#!/usr/bin/env python3
"""Network-free tests for the vector shard generator.

The generator exists to make one property checkable: the shards a gate runs are
an exact partition of the source file they replace. These tests exercise that
property directly — a partition that silently drops, duplicates, or invents a
case must fail, because a shard set that runs less than it claims still reports
every case it did run as passing.
"""
from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parents[1]

_spec = importlib.util.spec_from_file_location(
    "gen_vector_shards", SCRIPTS_DIR / "gen-vector-shards.py"
)
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)


def case(name: str, pairs: int = 1) -> dict:
    """A vector case whose Input length stands in for its cost."""
    return {"Name": name, "Input": "ab" * (384 * pairs), "Expected": "01", "Gas": 100}


class PartitionTests(unittest.TestCase):
    def test_partition_is_exact_for_many_shard_counts(self):
        cases = [case(f"c{i}", pairs=(i % 10) + 1) for i in range(106)]
        for count in (1, 2, 3, 7, 8, 24, 53, 106):
            with self.subTest(shards=count):
                shards = gen.partition(cases, count)
                self.assertEqual(len(shards), count)
                flat = [c for s in shards for c in s]
                self.assertEqual(len(flat), len(cases))
                # Exact multiset equality: no drops, no duplicates, no inventions.
                self.assertEqual(
                    sorted(map(gen.canonical, flat)),
                    sorted(map(gen.canonical, cases)),
                )

    def test_shards_are_balanced_by_cost_not_by_count(self):
        # Sorted ascending by cost, which is the shape that makes contiguous
        # slicing pathological: the last slice would hold every heavy case.
        cases = [case(f"c{i}", pairs=1 + i // 10) for i in range(100)]
        shards = gen.partition(cases, 8)
        loads = [sum(gen.cost(c) for c in s) for s in shards]
        self.assertLess((max(loads) - min(loads)) / max(loads), 0.05)

    def test_partition_is_deterministic(self):
        cases = [case(f"c{i}", pairs=(i % 7) + 1) for i in range(50)]
        first = gen.partition(cases, 6)
        second = gen.partition(cases, 6)
        self.assertEqual(
            [[gen.canonical(c) for c in s] for s in first],
            [[gen.canonical(c) for c in s] for s in second],
        )

    def test_more_shards_than_cases_is_refused(self):
        with self.assertRaises(SystemExit):
            gen.partition([case("only")], 4)

    def test_verify_rejects_a_dropped_case(self):
        cases = [case(f"c{i}") for i in range(10)]
        shards = gen.partition(cases, 2)
        shards[0] = shards[0][1:]
        with self.assertRaises(SystemExit):
            gen.verify(Path("src.json"), cases, shards, "test")

    def test_verify_rejects_a_duplicated_case(self):
        cases = [case(f"c{i}") for i in range(10)]
        shards = gen.partition(cases, 2)
        shards[1] = shards[1] + [shards[0][0]]
        with self.assertRaises(SystemExit):
            gen.verify(Path("src.json"), cases, shards, "test")

    def test_verify_rejects_an_invented_case(self):
        cases = [case(f"c{i}") for i in range(10)]
        shards = gen.partition(cases, 2)
        shards[0] = shards[0] + [case("not-from-the-source")]
        with self.assertRaises(SystemExit):
            gen.verify(Path("src.json"), cases, shards, "test")

    def test_verify_accepts_the_generated_partition(self):
        cases = [case(f"c{i}", pairs=(i % 4) + 1) for i in range(40)]
        gen.verify(Path("src.json"), cases, gen.partition(cases, 5), "test")

    def test_empty_source_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "empty.json"
            path.write_text("[]\n")
            with self.assertRaises(SystemExit):
                gen.load_cases(path)

    def test_round_trip_through_written_shards(self):
        """Write shards, then --check them, exactly as the repository does."""
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / "src.json"
            cases = [case(f"c{i}", pairs=(i % 5) + 1) for i in range(37)]
            source.write_text(json.dumps(cases, indent=2) + "\n")
            self.assertEqual(gen.main(["--source", str(source), "--shards", "6"]), 0)
            self.assertEqual(
                gen.main(["--source", str(source), "--shards", "6", "--check"]), 0
            )
            # A tampered shard must fail the same check.
            victim = gen.shard_path(source, 3)
            kept = json.loads(victim.read_text())[1:]
            victim.write_text(json.dumps(kept, indent=2) + "\n")
            with self.assertRaises(SystemExit):
                gen.main(["--source", str(source), "--shards", "6", "--check"])

    def test_committed_shards_partition_the_committed_source(self):
        """The repository's own shards, checked as the gate's provenance step."""
        source = SCRIPTS_DIR / "vectors" / "blsPairing.json"
        if not source.exists():
            self.skipTest("blsPairing.json not present")
        self.assertEqual(gen.main(["--check"]), 0)


if __name__ == "__main__":
    unittest.main()
