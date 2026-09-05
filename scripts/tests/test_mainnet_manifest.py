"""Synthetic tests for the strict current-mainnet manifest generator."""
from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import gen_mainnet_manifest as generator


def sources(path: Path) -> None:
    path.write_text(json.dumps({
        "schema_version": 1,
        "execution_specs": {"repo_url": "x", "commit": "0" * 40},
        "ethereum_tests": {"repo_url": "x", "commit": "1" * 40, "relative_path_from_execution_specs": "x"},
        "legacy_tests_submodule": {"commit": "2" * 40, "relative_path_from_ethereum_tests": "x"},
        "eest": {"release_tag": "v", "archive_url": "x", "archive_filename": "x", "archive_sha256": "0" * 64, "fixtures_subpath": "fixtures", "expected_top_level_dirs": ["x"]},
        "current_mainnet": {
            "release_tag": "tests@v0", "release_commit": "3" * 40, "release_url": "x",
            "archive_url": "x", "archive_filename": "fixtures.tar.gz", "archive_sha256": "4" * 64,
            "fixtures_subpath": "fixtures",
            "expected_top_level_dirs": ["blockchain_tests", "blockchain_tests_engine", "blockchain_tests_engine_x", "blockchain_tests_sync", "state_tests", "transaction_tests"],
            "metadata_json_expected": {"root_hash": "0xsynthetic"},
        },
        "python_oracle": {"intended_version": "3", "patch_policy": "exact", "package_manager": "uv", "requirements_lock": "x", "requirements_lock_sha256": "0" * 64, "known_packages": {}, "full_lock_status": "locked"},
    }))


SCHEDULES = {
    "Prague": {"target": "0x06", "max": "0x09", "baseFeeUpdateFraction": "0x4c6964"},
    "Osaka": {"target": "0x06", "max": "0x09", "baseFeeUpdateFraction": "0x4c6964"},
    "BPO1": {"target": "0x0a", "max": "0x0f", "baseFeeUpdateFraction": "0x7f5a51"},
    "BPO2": {"target": "0x0e", "max": "0x15", "baseFeeUpdateFraction": "0xb24b3f"},
}


def fixture(root: Path, relative: str, network: str, schedule: dict | None = None) -> None:
    path = root / "blockchain_tests" / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    forks = generator.label_forks(network)
    if schedule is None:
        schedule = {fork: SCHEDULES[fork] for fork in (forks or ())}
    case: dict = {"network": network}
    if forks is not None or schedule:
        case["config"] = {"network": network, "chainid": "0x01", "blobSchedule": schedule}
    path.write_text(json.dumps({f"{network}-{relative}": case}))


class ManifestTests(unittest.TestCase):
    def make_root(self, tmp: Path) -> tuple[Path, Path]:
        fixtures = tmp / "fixtures"
        for name in ["blockchain_tests", "blockchain_tests_engine", "blockchain_tests_engine_x", "blockchain_tests_sync", "state_tests", "transaction_tests"]:
            (fixtures / name).mkdir(parents=True, exist_ok=True)
        fixture(fixtures, "z.json", "Prague")
        fixture(fixtures, "a.json", "Prague")
        fixture(fixtures, "osaka.json", "Osaka")
        fixture(fixtures, "old.json", "Cancun")
        fixture(fixtures, "to_osaka.json", "PragueToOsakaAtTime15k")
        fixture(fixtures, "to_bpo1.json", "OsakaToBPO1AtTime15k")
        fixture(fixtures, "to_bpo3.json", "BPO2ToBPO3AtTime15k")
        manifest = tmp / "sources.json"
        sources(manifest)
        return fixtures, manifest

    def test_exact_static_and_exclusion_inventory(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            actual = generator.inventory(fixtures, generator.load_sources(manifest))
            self.assertEqual([f["path"] for f in actual["suites"]["prague"]["files"]], ["a.json", "z.json"])
            self.assertEqual(actual["suites"]["smoke"]["case_count"], 2)
            self.assertEqual(actual["suites"]["bpo1"]["file_count"], 0)
            self.assertEqual(
                actual["excluded"]["Cancun"]["reason"],
                "unsupported historical fork: Cancun is not in the supported chain",
            )

    def test_transition_labels_are_parsed_not_listed(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            actual = generator.inventory(fixtures, generator.load_sources(manifest))
            transitions = actual["suites"]["transitions"]
            self.assertEqual(
                [entry["path"] for entry in transitions["files"]],
                ["to_bpo1.json", "to_osaka.json"],
            )
            self.assertEqual(
                [entry["network"] for entry in transitions["files"]],
                ["OsakaToBPO1AtTime15k", "PragueToOsakaAtTime15k"],
            )
            # A transition with an endpoint outside the supported chain is
            # excluded by naming that endpoint, not by a hand-kept list.
            self.assertNotIn("BPO2ToBPO3AtTime15k", transitions["networks"])
            self.assertEqual(
                actual["excluded"]["BPO2ToBPO3AtTime15k"]["reason"],
                "unsupported transition: BPO3 is not in the supported chain",
            )
            self.assertFalse(actual["transition_inventory"]["BPO2ToBPO3AtTime15k"]["supported"])
            self.assertTrue(actual["transition_inventory"]["PragueToOsakaAtTime15k"]["supported"])
            self.assertEqual(
                actual["transition_inventory"]["PragueToOsakaAtTime15k"]["activation"], 15000
            )

    def test_transition_activation_parsing(self):
        self.assertEqual(generator.parse_transition("PragueToOsakaAtTime15k"), ("Prague", "Osaka", 15000))
        self.assertEqual(generator.parse_transition("PragueToOsakaAtTime900"), ("Prague", "Osaka", 900))
        for bad in ["Prague", "PragueToOsaka", "PragueToOsakaAtTime", "PragueToOsakaAtTimek",
                    "PragueToOsakaToBPO1AtTime15k", "PragueToOsakaAtTime15kAtTime2k"]:
            self.assertIsNone(generator.parse_transition(bad), bad)
        self.assertIsNone(generator.label_forks("CancunToPragueAtTime15k"))
        self.assertEqual(generator.label_forks("BPO1ToBPO2AtTime15k"), ("BPO1", "BPO2"))

    def test_union_suite_is_its_components(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            actual = generator.inventory(fixtures, generator.load_sources(manifest))
            full = actual["suites"]["full"]
            self.assertNotIn("files", full)
            self.assertEqual(full["component_suites"], ["prague", "osaka", "transitions"])
            self.assertEqual(full["file_count"], 2 + 1 + 2)

    def test_declared_blob_schedules_are_recorded(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            actual = generator.inventory(fixtures, generator.load_sources(manifest))
            self.assertEqual(
                actual["declared_blob_schedules"]["BPO1"],
                {"target": 10, "max": 15, "baseFeeUpdateFraction": 8346193,
                 "target_gas": 10 * 131072, "max_gas": 15 * 131072},
            )

    def test_missing_blob_schedule_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            fixture(fixtures, "silent.json", "Osaka", schedule={})
            with self.assertRaises(generator.InventoryError):
                generator.inventory(fixtures, generator.load_sources(manifest))

    def test_disagreeing_blob_schedule_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            fixture(fixtures, "moved.json", "Osaka", schedule={
                "Osaka": {"target": "0x07", "max": "0x09", "baseFeeUpdateFraction": "0x4c6964"},
            })
            with self.assertRaises(generator.InventoryError):
                generator.inventory(fixtures, generator.load_sources(manifest))

    def test_unknown_shape_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            (fixtures / "blockchain_tests" / "bad.json").write_text("[]")
            with self.assertRaises(generator.InventoryError):
                generator.inventory(fixtures, generator.load_sources(manifest))

    def test_check_detects_stale_generated_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            output = Path(tmp) / "out.json"
            self.assertEqual(generator.main(["--fixtures-root", str(fixtures), "--sources", str(manifest), "--output", str(output)]), 0)
            self.assertEqual(generator.main(["--fixtures-root", str(fixtures), "--sources", str(manifest), "--output", str(output), "--check"]), 0)
            fixture(fixtures, "new.json", "Prague")
            self.assertEqual(generator.main(["--fixtures-root", str(fixtures), "--sources", str(manifest), "--output", str(output), "--check"]), 1)

    def test_emit_suite_names_every_network(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            output = Path(tmp) / "out.json"
            argv = ["--fixtures-root", str(fixtures), "--sources", str(manifest), "--output", str(output)]
            self.assertEqual(generator.main(argv), 0)
            for suite, expected in [("transitions", 2), ("full", 5), ("prague", 2)]:
                buffer = io.StringIO()
                with contextlib.redirect_stdout(buffer):
                    self.assertEqual(generator.main(argv + ["--check", "--emit-suite", suite]), 0)
                rows = [line.split("\t") for line in buffer.getvalue().splitlines()]
                self.assertEqual(len(rows), expected, suite)
                self.assertTrue(all(len(row) == 2 and row[1] for row in rows), suite)

    def test_the_default_lane_states_no_runnability(self):
        """The devnet lane annotates every suite with `runnable` and defers the
        two that select `BPO2ToAmsterdamAtTime15k` by name. The current-mainnet
        manifest is a tracked artifact its gate compares byte for byte, so none
        of that may reach it through the shared code path: this lane defers
        nothing, and every suite it raises is one this build runs."""
        self.assertEqual(generator.LANES["mainnet"].deferred_labels, ())
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            actual = generator.inventory(fixtures, generator.load_sources(manifest))
        for key in ("runnable", "refusal_reason", "lane", "label_inventory"):
            self.assertNotIn(key, actual, key)
        for name, suite in actual["suites"].items():
            with self.subTest(suite=name):
                self.assertNotIn("runnable", suite)
                self.assertNotIn("refusal_reason", suite)

    def test_emit_rejects_an_empty_suite(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            output = Path(tmp) / "out.json"
            argv = ["--fixtures-root", str(fixtures), "--sources", str(manifest), "--output", str(output)]
            self.assertEqual(generator.main(argv), 0)
            self.assertEqual(generator.main(argv + ["--check", "--emit-suite", "bpo1"]), 2)
            self.assertEqual(generator.main(argv + ["--check", "--emit-suite", "amsterdam"]), 2)


if __name__ == "__main__":
    unittest.main()
