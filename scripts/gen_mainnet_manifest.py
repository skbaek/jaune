#!/usr/bin/env python3
"""Generate and verify exact current-mainnet blockchain-fixture manifests.

The generator has no network behaviour.  It consumes a fixture tree already
verified against ``sources.json`` by ``env_doctor.py --mainnet-deep`` and emits
the complete static-fork, transition, and exclusion inventories.  A fixed
lexicographic first-32 Prague-file rule derives the smoke suite; no path is
hand-selected.

A transition label is supported when both of its endpoints are forks this build
implements, which is the same rule ``ForkTransition.ofString?`` applies in Lean.
Nothing here is a hand-kept list of supported transitions: the archive's labels
are parsed, and a label naming a fork outside the supported chain is excluded
with that fork as its reason.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

import env_doctor


ROOT = Path(__file__).resolve().parent
DEFAULT_SOURCES = ROOT / "sources.json"
DEFAULT_OUTPUT = ROOT / "mainnet" / "manifests.json"
SUPPORTED_STATIC = ("Prague", "Osaka", "BPO1", "BPO2")
SMOKE_FILE_COUNT = 16
GAS_PER_BLOB = 2 ** 17
BLOB_SCHEDULE_FIELDS = ("target", "max", "baseFeeUpdateFraction")


class InventoryError(Exception):
    pass


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


def label_forks(label: str) -> tuple[str, ...] | None:
    """The forks a label can select, or ``None`` if this build cannot run it."""
    if label in SUPPORTED_STATIC:
        return (label,)
    transition = parse_transition(label)
    if transition is None:
        return None
    before, after, _ = transition
    if before not in SUPPORTED_STATIC or after not in SUPPORTED_STATIC:
        return None
    return (before, after)


def exclusion_reason(label: str) -> str:
    """Why a label is not run, named precisely enough to be reviewable."""
    transition = parse_transition(label)
    if transition is None:
        return f"unsupported historical fork: {label} is not in the supported chain"
    before, after, _ = transition
    outside = [f for f in (before, after) if f not in SUPPORTED_STATIC]
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


def read_cases(path: Path) -> tuple[str, list[str], dict]:
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
        forks = label_forks(label)
        if forks is not None:
            for fork, values in declared_blob_schedule(path, name, case, forks).items():
                if schedules.setdefault(fork, values) != values:
                    raise InventoryError(
                        f"{path}: cases disagree about the {fork} blob schedule"
                    )
        names.append(name)
    assert network is not None
    return network, sorted(names), schedules


def inventory(fixtures_root: Path, sources: dict) -> dict:
    blockchain = fixtures_root / "blockchain_tests"
    if not blockchain.is_dir():
        raise InventoryError(f"missing blockchain_tests root: {blockchain}")
    expected_top = set(sources["current_mainnet"]["expected_top_level_dirs"])
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
        label, names, schedules = read_cases(path)
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
        for label in SUPPORTED_STATIC
    }
    prague_files = suites["prague"]["files"]
    smoke_files = sorted(
        prague_files,
        key=lambda entry: smoke_rank(sources["current_mainnet"]["release_commit"], entry),
    )[:SMOKE_FILE_COUNT]
    suites["smoke"] = {
        "network": "Prague",
        "selection_rule": f"lowest {SMOKE_FILE_COUNT} SHA-256 ranks of release_commit:path",
        "files": smoke_files,
        "file_count": len(smoke_files),
        "case_count": sum(entry["case_count"] for entry in smoke_files),
    }

    transition_labels = sorted(
        label for label in grouped if parse_transition(label) is not None
    )
    supported_transitions = [
        label for label in transition_labels if label_forks(label) is not None
    ]
    transition_files = sorted(
        (entry for label in supported_transitions for entry in grouped[label]),
        key=lambda entry: entry["path"],
    )
    suites["transitions"] = {
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
        label.lower() for label in SUPPORTED_STATIC if grouped.get(label)
    ] + ["transitions"]
    suites["full"] = {
        "networks": [label for label in SUPPORTED_STATIC if grouped.get(label)]
        + supported_transitions,
        "selection_rule": "union of every supported static and transition suite",
        "component_suites": components,
        "file_count": sum(suites[name]["file_count"] for name in components),
        "case_count": sum(suites[name]["case_count"] for name in components),
    }

    excluded = {
        label: {
            "reason": exclusion_reason(label),
            "file_count": len(entries),
            "case_count": label_cases[label],
            "files": entries,
        }
        for label, entries in sorted(grouped.items())
        if label_forks(label) is None
    }
    return {
        "schema_version": 2,
        "source": {
            "release_tag": sources["current_mainnet"]["release_tag"],
            "release_commit": sources["current_mainnet"]["release_commit"],
            "archive_sha256": sources["current_mainnet"]["archive_sha256"],
            "metadata_json_expected": sources["current_mainnet"]["metadata_json_expected"],
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
                "supported": label_forks(label) is not None,
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


def load_sources(path: Path) -> dict:
    return env_doctor.load_manifest(path)


def write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures-root", type=Path, required=True)
    parser.add_argument("--sources", type=Path, default=DEFAULT_SOURCES)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true", help="fail unless output is exact")
    parser.add_argument(
        "--emit-suite",
        help="after optional --check, print manifest file paths and network labels as TSV",
    )
    args = parser.parse_args(argv)
    try:
        sources = load_sources(args.sources)
        actual = inventory(args.fixtures_root, sources)
    except (env_doctor.ManifestError, InventoryError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    if args.check:
        try:
            expected = json.loads(args.output.read_text())
        except (OSError, json.JSONDecodeError) as error:
            print(f"error: cannot read generated manifest {args.output}: {error}", file=sys.stderr)
            return 2
        if expected != actual:
            print("RED — current-mainnet manifest is stale or fixture input differs", file=sys.stderr)
            return 1
        if args.emit_suite is None:
            print("OK — current-mainnet manifest exactly matches the pinned fixture tree")
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
    write_json(args.output, actual)
    print(f"Wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
