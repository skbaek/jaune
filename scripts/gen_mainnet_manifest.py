#!/usr/bin/env python3
"""Generate and verify exact current-mainnet blockchain-fixture manifests.

The generator has no network behaviour.  It consumes a fixture tree already
verified against ``sources.json`` by ``env_doctor.py --mainnet-deep`` and emits
the complete static-fork, transition, and exclusion inventories.  A fixed
lexicographic first-32 Prague-file rule derives the smoke suite; no path is
hand-selected.
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
SMOKE_FILE_COUNT = 32


class InventoryError(Exception):
    pass


def file_digest(names: list[str]) -> str:
    """Stable compact witness for the exact cases in one fixture file."""
    payload = "\n".join(names).encode()
    return hashlib.sha256(payload).hexdigest()


def read_cases(path: Path) -> tuple[str, list[str]]:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise InventoryError(f"unreadable JSON fixture {path}: {error}") from error
    if not isinstance(value, dict) or not value:
        raise InventoryError(f"unknown JSON form in {path}: expected nonempty object")

    network: str | None = None
    names: list[str] = []
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
        names.append(name)
    assert network is not None
    return network, sorted(names)


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
    for path in sorted(blockchain.rglob("*.json")):
        relative = path.relative_to(blockchain).as_posix()
        label, names = read_cases(path)
        grouped[label].append(
            {
                "path": relative,
                "case_count": len(names),
                "case_names": names,
                "case_names_sha256": file_digest(names),
            }
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
    suites["smoke"] = {
        "network": "Prague",
        "selection_rule": f"first {SMOKE_FILE_COUNT} Prague files in bytewise path order",
        "files": prague_files[:SMOKE_FILE_COUNT],
        "file_count": min(SMOKE_FILE_COUNT, len(prague_files)),
        "case_count": sum(entry["case_count"] for entry in prague_files[:SMOKE_FILE_COUNT]),
    }

    transition_labels = {label: grouped[label] for label in sorted(grouped) if "To" in label}
    excluded = {
        label: {
            "reason": (
                "future supported transition; inventory only until Step 6"
                if label in {"PragueToOsakaAtTime15k", "OsakaToBPO1AtTime15k", "BPO1ToBPO2AtTime15k"}
                else "unsupported historical fork or transition"
            ),
            "file_count": len(entries),
            "case_count": label_cases[label],
            "files": entries,
        }
        for label, entries in sorted(grouped.items())
        if label not in SUPPORTED_STATIC
    }
    return {
        "schema_version": 1,
        "source": {
            "release_tag": sources["current_mainnet"]["release_tag"],
            "release_commit": sources["current_mainnet"]["release_commit"],
            "archive_sha256": sources["current_mainnet"]["archive_sha256"],
            "metadata_json_expected": sources["current_mainnet"]["metadata_json_expected"],
        },
        "fixture_root": "fixtures",
        "blockchain_root": "blockchain_tests",
        "suites": suites,
        "transition_inventory": {
            label: {
                "file_count": len(entries),
                "case_count": label_cases[label],
                "files": entries,
            }
            for label, entries in transition_labels.items()
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
        network = suite.get("network")
        if not isinstance(files, list) or not isinstance(network, str) or not files:
            print(f"error: suite {args.emit_suite!r} has zero selected files", file=sys.stderr)
            return 2
        for entry in files:
            print(f"{entry['path']}\t{network}")
        return 0
    write_json(args.output, actual)
    print(f"Wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
