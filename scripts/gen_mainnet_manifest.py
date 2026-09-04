#!/usr/bin/env python3
"""Generate and verify exact blockchain-fixture manifests, per lane.

The generator has no network behaviour.  It consumes a fixture tree already
verified against ``sources.json`` by ``env_doctor.py --<lane>-deep`` and emits
the complete static-fork, transition, and exclusion inventories.  A fixed
lexicographic rule over a pinned seed derives the smoke suite; no path is
hand-selected.

``--lane`` selects which release the manifest describes:

- ``mainnet`` (the default) inventories the current-mainnet release over the
  forks whose rules this build implements: Prague, Osaka, BPO1, BPO2;
- ``amsterdam`` inventories the Glamsterdam devnet-8 prerelease over those plus
  the *declared* fork ``Amsterdam``.

A label is *in a lane* when every fork it names is one that lane covers, which
for a transition is the same rule ``ForkTransition.ofString?`` applies in Lean.
Nothing here is a hand-kept list: the archive's labels are parsed, and a label
naming a fork outside the lane is excluded with that fork as its reason.

**Being in a lane is not being runnable.** The Amsterdam lane deliberately
covers a fork ``Fork.rules?`` answers ``none`` for, because the inventory's job
is to say exactly what the corpus holds -- including what it holds that this
build cannot yet execute.  Which suites may actually run is decided by
``check-mainnet.sh``, which refuses this lane's suites outright.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

import env_doctor


ROOT = Path(__file__).resolve().parent
DEFAULT_SOURCES = ROOT / "sources.json"
DEFAULT_OUTPUT = ROOT / "mainnet" / "manifests.json"
SUPPORTED_STATIC = ("Prague", "Osaka", "BPO1", "BPO2")
AMSTERDAM_STATIC = SUPPORTED_STATIC + ("Amsterdam",)
SMOKE_FILE_COUNT = 16
GAS_PER_BLOB = 2 ** 17
BLOB_SCHEDULE_FIELDS = ("target", "max", "baseFeeUpdateFraction")


class InventoryError(Exception):
    pass


@dataclass(frozen=True)
class LaneSpec:
    """One release this generator can inventory.

    `statics` is the set of static labels the lane covers, and therefore also
    the endpoints a transition label may name.  `smoke_network` is the static
    label the small reproducible sample is drawn from.  `sources_key` names the
    manifest section holding the release identity that seeds that sample.
    """

    name: str
    sources_key: str
    statics: tuple[str, ...]
    suite_statics: tuple[str, ...]
    smoke_network: str
    suite_prefix: str
    report_label: str
    output: Path

    def suite(self, kind: str) -> str:
        """The name of one of this lane's derived suites.

        Static suites keep their label's own lowercase spelling; the three
        derived suites are lane-prefixed so that the two lanes' suite
        namespaces are disjoint and a mistyped `--suite` can never select the
        other lane's corpus.
        """
        return f"{self.suite_prefix}{kind}"


LANES = {
    "mainnet": LaneSpec(
        name="mainnet",
        sources_key="current_mainnet",
        statics=SUPPORTED_STATIC,
        suite_statics=SUPPORTED_STATIC,
        smoke_network="Prague",
        suite_prefix="",
        report_label="current-mainnet",
        output=ROOT / "mainnet" / "manifests.json",
    ),
    # The devnet lane *covers* every fork a devnet label can name -- otherwise
    # `BPO2ToAmsterdamAtTime15k` would be excluded for naming BPO2 -- but it
    # raises a suite only over Amsterdam itself. The Prague-BPO2 fixtures this
    # prerelease also carries are the mainnet lane's subject at the mainnet
    # lane's own pin, and running them here would test the same rules against a
    # second, weaker corpus while reporting it as Amsterdam coverage.
    "amsterdam": LaneSpec(
        name="amsterdam",
        sources_key="glamsterdam_devnet",
        statics=AMSTERDAM_STATIC,
        suite_statics=("Amsterdam",),
        smoke_network="Amsterdam",
        suite_prefix="amsterdam-",
        report_label="glamsterdam-devnet",
        output=ROOT / "amsterdam" / "manifests.json",
    ),
}
DEFAULT_LANE = LANES["mainnet"]


def parse_transition(label: str) -> tuple[str, str, int] | None:
    """Split ``<before>To<after>AtTime<n>`` exactly as the Lean parser does.

    Returns ``None`` for any label that is not of that shape; whether the forks
    it names are supported is a separate question, answered by the caller.
    """
    parts = label.split("AtTime")
    if len(parts) != 2:
        return None
    forks, time = parts
    if time.endswith("k"):
        digits, scale = time[:-1], 1000
    else:
        digits, scale = time, 1
    if not digits.isdigit():
        return None
    endpoints = forks.split("To")
    if len(endpoints) != 2:
        return None
    return endpoints[0], endpoints[1], int(digits) * scale


def label_forks(label: str, statics: tuple[str, ...] = SUPPORTED_STATIC) -> tuple[str, ...] | None:
    """The forks a label can select, or ``None`` if it is outside this lane."""
    if label in statics:
        return (label,)
    transition = parse_transition(label)
    if transition is None:
        return None
    before, after, _ = transition
    if before not in statics or after not in statics:
        return None
    return (before, after)


def exclusion_reason(label: str, statics: tuple[str, ...] = SUPPORTED_STATIC) -> str:
    """Why a label is not in this lane, named precisely enough to be reviewable."""
    transition = parse_transition(label)
    if transition is None:
        return f"unsupported historical fork: {label} is not in the supported chain"
    before, after, _ = transition
    outside = [f for f in (before, after) if f not in statics]
    verb = "is" if len(outside) == 1 else "are"
    return f"unsupported transition: {', '.join(outside)} {verb} not in the supported chain"


def file_digest(names: list[str]) -> str:
    """Stable compact witness for the exact cases in one fixture file."""
    payload = "\n".join(names).encode()
    return hashlib.sha256(payload).hexdigest()


def smoke_rank(release_commit: str, entry: dict) -> str:
    """Pinned seed plus path makes the small smoke sample reproducible."""
    return hashlib.sha256(f"{release_commit}:{entry['path']}".encode()).hexdigest()


def declared_blob_schedule(path: Path, name: str, case: dict, forks: tuple[str, ...]) -> dict:
    """The blob schedule a runnable case states about the forks it uses.

    A supported case must declare one, and must declare it for every fork it can
    select: these numbers are the entire content of a BPO fork, and they are what
    the fixture runner checks its own rule data against.  A missing declaration is
    an inventory error rather than a case that quietly goes unchecked.
    """
    declared = ((case.get("config") or {}).get("blobSchedule") or {})
    if not isinstance(declared, dict):
        raise InventoryError(f"unknown JSON form in {path}: case {name!r} has a non-object blobSchedule")
    schedules: dict[str, dict[str, int]] = {}
    for fork in forks:
        entry = declared.get(fork)
        if not isinstance(entry, dict):
            raise InventoryError(
                f"{path}: case {name!r} runs {fork} but declares no blob schedule for it"
            )
        values: dict[str, int] = {}
        for field in BLOB_SCHEDULE_FIELDS:
            raw = entry.get(field)
            if not isinstance(raw, str):
                raise InventoryError(f"{path}: case {name!r} has no {fork} blob {field}")
            try:
                values[field] = int(raw, 16)
            except ValueError as error:
                raise InventoryError(
                    f"{path}: case {name!r} has an unreadable {fork} blob {field}: {raw!r}"
                ) from error
        schedules[fork] = values
    return schedules


def read_cases(path: Path, statics: tuple[str, ...] = SUPPORTED_STATIC) -> tuple[str, list[str], dict]:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise InventoryError(f"unreadable JSON fixture {path}: {error}") from error
    if not isinstance(value, dict) or not value:
        raise InventoryError(f"unknown JSON form in {path}: expected nonempty object")

    network: str | None = None
    names: list[str] = []
    schedules: dict[str, dict[str, int]] = {}
    for name, case in value.items():
        if not isinstance(name, str) or not isinstance(case, dict):
            raise InventoryError(f"unknown JSON form in {path}: case map expected")
        label = case.get("network")
        if not isinstance(label, str):
            raise InventoryError(f"unknown JSON form in {path}: case {name!r} has no string network")
        if network is None:
            network = label
        elif network != label:
            raise InventoryError(f"mixed network labels in one fixture file: {path}")
        forks = label_forks(label, statics)
        if forks is not None:
            for fork, values in declared_blob_schedule(path, name, case, forks).items():
                if schedules.setdefault(fork, values) != values:
                    raise InventoryError(
                        f"{path}: cases disagree about the {fork} blob schedule"
                    )
        names.append(name)
    assert network is not None
    return network, sorted(names), schedules


def inventory(fixtures_root: Path, sources: dict, lane: LaneSpec = DEFAULT_LANE) -> dict:
    statics = lane.statics
    release = sources[lane.sources_key]
    blockchain = fixtures_root / "blockchain_tests"
    if not blockchain.is_dir():
        raise InventoryError(f"missing blockchain_tests root: {blockchain}")
    expected_top = set(release["expected_top_level_dirs"])
    actual_top = {
        path.name for path in fixtures_root.iterdir() if path.is_dir() and path.name != ".meta"
    }
    if actual_top != expected_top:
        raise InventoryError(
            "unexpected fixture top-level directory set: "
            f"expected {sorted(expected_top)}, got {sorted(actual_top)}"
        )

    grouped: dict[str, list[dict]] = defaultdict(list)
    label_cases: Counter[str] = Counter()
    all_files: set[str] = set()
    blob_schedules: dict[str, dict[str, int]] = {}
    for path in sorted(blockchain.rglob("*.json")):
        relative = path.relative_to(blockchain).as_posix()
        label, names, schedules = read_cases(path, statics)
        grouped[label].append(
            {
                "path": relative,
                "network": label,
                "case_count": len(names),
                "case_names": names,
                "case_names_sha256": file_digest(names),
            }
        )
        for fork, values in schedules.items():
            if blob_schedules.setdefault(fork, values) != values:
                raise InventoryError(
                    f"fixtures disagree about the {fork} blob schedule at {relative}"
                )
        label_cases[label] += len(names)
        all_files.add(relative)

    if not all_files:
        raise InventoryError("zero blockchain fixture files")
    suites = {
        label.lower(): {
            "network": label,
            "files": grouped.get(label, []),
            "file_count": len(grouped.get(label, [])),
            "case_count": label_cases[label],
        }
        for label in lane.suite_statics
    }
    smoke_source = suites[lane.smoke_network.lower()]["files"]
    smoke_files = sorted(
        smoke_source,
        key=lambda entry: smoke_rank(release["release_commit"], entry),
    )[:SMOKE_FILE_COUNT]
    suites[lane.suite("smoke")] = {
        "network": lane.smoke_network,
        "selection_rule": f"lowest {SMOKE_FILE_COUNT} SHA-256 ranks of release_commit:path",
        "files": smoke_files,
        "file_count": len(smoke_files),
        "case_count": sum(entry["case_count"] for entry in smoke_files),
    }

    transition_labels = sorted(
        label for label in grouped if parse_transition(label) is not None
    )
    # A transition belongs to this lane's suite when it is in the lane *and*
    # at least one endpoint is a fork this lane raises a suite over. Without
    # the second condition the devnet lane's transitions suite would carry the
    # three Prague-BPO2 transitions the mainnet lane already owns, at a second
    # pin, and report them as Amsterdam coverage. For the mainnet lane the two
    # conditions coincide, because it raises a suite over every fork it covers.
    supported_transitions = [
        label
        for label in transition_labels
        if (forks := label_forks(label, statics)) is not None
        and any(fork in lane.suite_statics for fork in forks)
    ]
    transition_files = sorted(
        (entry for label in supported_transitions for entry in grouped[label]),
        key=lambda entry: entry["path"],
    )
    suites[lane.suite("transitions")] = {
        "networks": supported_transitions,
        "selection_rule": "every fixture whose transition label names two supported forks",
        "files": transition_files,
        "file_count": len(transition_files),
        "case_count": sum(entry["case_count"] for entry in transition_files),
    }
    # The union suite names its components instead of repeating their entries:
    # every file's case evidence is already stated exactly once, under the suite
    # that selects it, and duplicating it here would make the two copies
    # something that could disagree.
    components = [
        label.lower() for label in lane.suite_statics if grouped.get(label)
    ] + [lane.suite("transitions")]
    suites[lane.suite("full")] = {
        "networks": [label for label in lane.suite_statics if grouped.get(label)]
        + supported_transitions,
        "selection_rule": "union of every supported static and transition suite",
        "component_suites": components,
        "file_count": sum(suites[name]["file_count"] for name in components),
        "case_count": sum(suites[name]["case_count"] for name in components),
    }

    excluded = {
        label: {
            "reason": exclusion_reason(label, statics),
            "file_count": len(entries),
            "case_count": label_cases[label],
            "files": entries,
        }
        for label, entries in sorted(grouped.items())
        if label_forks(label, statics) is None
    }

    # A label may be inside the lane and still raise no suite of its own -- the
    # devnet corpus carries the whole Prague-BPO2 history alongside Amsterdam,
    # and that history is the mainnet lane's subject at the mainnet lane's pin.
    # Such a label is neither run here nor excluded, so it is stated outright
    # rather than left to be inferred from the difference of two other lists.
    suite_networks = {
        network
        for suite in suites.values()
        for network in ([suite["network"]] if "network" in suite else suite.get("networks", []))
    }
    covered_without_suite = {
        label: {
            "reason": "in this lane's fork coverage, but this lane raises no "
            "suite over it: it is another lane's subject at that lane's pin",
            "file_count": len(entries),
            "case_count": label_cases[label],
        }
        for label, entries in sorted(grouped.items())
        if label_forks(label, statics) is not None and label not in suite_networks
    }
    label_inventory = {
        label: {
            "file_count": len(entries),
            "case_count": label_cases[label],
            "in_lane": label_forks(label, statics) is not None,
            "in_suite": label in suite_networks,
        }
        for label, entries in sorted(grouped.items())
    }

    result = {
        "schema_version": 2,
        "source": {
            "release_tag": release["release_tag"],
            "release_commit": release["release_commit"],
            "archive_sha256": release["archive_sha256"],
            "metadata_json_expected": release["metadata_json_expected"],
        },
        "fixture_root": "fixtures",
        "blockchain_root": "blockchain_tests",
        "suites": suites,
        # The blob parameters the fixtures themselves declare for every fork
        # this build runs, in gas as well as in the blob counts they are written
        # in.  Recording them here makes the archive, and not this repository,
        # the source of the numbers a BPO fork consists of; the fixture runner
        # checks its own rule data against the same declarations as it runs.
        "declared_blob_schedules": {
            fork: dict(
                values,
                target_gas=values["target"] * GAS_PER_BLOB,
                max_gas=values["max"] * GAS_PER_BLOB,
            )
            for fork, values in sorted(blob_schedules.items())
        },
        "transition_inventory": {
            label: {
                "supported": label_forks(label, statics) is not None,
                "activation": parse_transition(label)[2],
                "file_count": len(grouped[label]),
                "case_count": label_cases[label],
                "files": grouped[label],
            }
            for label in transition_labels
        },
        "excluded": excluded,
        "non_blockchain_fixture_families": sorted(
            expected_top - {"blockchain_tests"}
        ),
    }
    if lane.name != DEFAULT_LANE.name:
        # Lane-local sections. The current-mainnet manifest is a tracked
        # artifact with a fixed shape and a gate that compares it exactly, so a
        # second lane adds keys to its own manifest and never to that one.
        result["lane"] = lane.name
        result["covered_without_suite"] = covered_without_suite
        result["label_inventory"] = label_inventory
        result["runnable"] = False
        result["refusal_reason"] = (
            "this lane's fixtures target Amsterdam, whose execution rules "
            "Fork.rules? answers none for; every suite here is refused until "
            "the goal that owns those semantics activates it"
        )
    return result


def load_sources(path: Path) -> dict:
    return env_doctor.load_manifest(path)


def write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures-root", type=Path, required=True)
    parser.add_argument("--sources", type=Path, default=DEFAULT_SOURCES)
    parser.add_argument(
        "--lane",
        choices=sorted(LANES),
        default=DEFAULT_LANE.name,
        help="which release to inventory (default: %(default)s). The lane fixes "
        "the sources.json section, the fork coverage, the suite names, and the "
        "default output path.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="manifest path (default: the lane's own, scripts/<lane>/manifests.json)",
    )
    parser.add_argument("--check", action="store_true", help="fail unless output is exact")
    parser.add_argument(
        "--emit-suite",
        help="after optional --check, print manifest file paths and network labels as TSV",
    )
    args = parser.parse_args(argv)
    lane = LANES[args.lane]
    output = args.output if args.output is not None else lane.output
    try:
        sources = load_sources(args.sources)
        actual = inventory(args.fixtures_root, sources, lane)
    except (env_doctor.ManifestError, InventoryError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    if args.check:
        try:
            expected = json.loads(output.read_text())
        except (OSError, json.JSONDecodeError) as error:
            print(f"error: cannot read generated manifest {output}: {error}", file=sys.stderr)
            return 2
        if expected != actual:
            print(
                f"RED — {lane.report_label} manifest is stale or fixture input differs",
                file=sys.stderr,
            )
            return 1
        if args.emit_suite is None:
            print(
                f"OK — {lane.report_label} manifest exactly matches the pinned fixture tree"
            )
            return 0
    if args.emit_suite is not None:
        suite = actual["suites"].get(args.emit_suite)
        if not isinstance(suite, dict):
            print(f"error: unknown suite {args.emit_suite!r}", file=sys.stderr)
            return 2
        files = suite.get("files")
        if files is None:
            # A union suite states its components rather than their entries.
            files = sorted(
                (
                    entry
                    for name in suite.get("component_suites", [])
                    for entry in actual["suites"][name]["files"]
                ),
                key=lambda entry: entry["path"],
            )
        if not isinstance(files, list) or not files:
            print(f"error: suite {args.emit_suite!r} has zero selected files", file=sys.stderr)
            return 2
        # Every entry names its own network, so a suite spanning several labels
        # -- a transition suite, or the union -- needs no second lookup and no
        # per-suite special case downstream.
        for entry in files:
            print(f"{entry['path']}\t{entry['network']}")
        return 0
    write_json(output, actual)
    print(f"Wrote {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
