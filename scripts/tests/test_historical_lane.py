"""Synthetic tests for the historical manifest lane and dormant table (goal U10)."""
from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import gen_mainnet_manifest as generator
import importlib.util


def _load_hyphenated(name: str):
    # scripts/gen-fork-constants.py is hyphenated like its gate sibling, so
    # it is loaded from its path rather than imported. Its top level only
    # binds constants and defines functions, so executing it is side-effect
    # free.
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


constants = _load_hyphenated("gen-fork-constants")


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


def fixture(root: Path, relative: str, network: str) -> None:
    """A historical case declares no blob schedule: there was none to declare."""
    path = root / "blockchain_tests" / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({f"{network}-{relative}": {"network": network}}))


HISTORICAL = generator.LANES["historical"]


class HistoricalLaneTests(unittest.TestCase):
    def make_root(self, tmp: Path) -> tuple[Path, Path]:
        fixtures = tmp / "fixtures"
        for name in ["blockchain_tests", "blockchain_tests_engine", "blockchain_tests_engine_x", "blockchain_tests_sync", "state_tests", "transaction_tests"]:
            (fixtures / name).mkdir(parents=True, exist_ok=True)
        fixture(fixtures, "b1.json", "Byzantium")
        fixture(fixtures, "b2.json", "Byzantium")
        fixture(fixtures, "cfix.json", "ConstantinopleFix")
        fixture(fixtures, "cancun.json", "Cancun")
        fixture(fixtures, "paris_shanghai.json", "ParisToShanghaiAtTime15k")
        fixture(fixtures, "cancun_prague.json", "CancunToPragueAtTime15k")
        fixture(fixtures, "prague.json", "Prague")
        fixture(fixtures, "osaka.json", "Osaka")
        manifest = tmp / "sources.json"
        sources(manifest)
        return fixtures, manifest

    def inventory(self, fixtures: Path, manifest: Path) -> dict:
        return generator.inventory(fixtures, generator.load_sources(manifest), HISTORICAL)

    def test_one_suite_per_fork_plus_transitions(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            actual = self.inventory(fixtures, manifest)
            self.assertEqual(
                [f["path"] for f in actual["suites"]["byzantium"]["files"]],
                ["b1.json", "b2.json"],
            )
            self.assertEqual(
                [f["path"] for f in actual["suites"]["constantinoplefix"]["files"]],
                ["cfix.json"],
            )
            # EIP-1283 Constantinople selects nothing, but its suite exists.
            self.assertEqual(actual["suites"]["constantinople"]["file_count"], 0)
            transitions = actual["suites"]["hist-transitions"]
            self.assertEqual(
                transitions["networks"],
                ["CancunToPragueAtTime15k", "ParisToShanghaiAtTime15k"],
            )
            self.assertEqual(
                [e["path"] for e in transitions["files"]],
                ["cancun_prague.json", "paris_shanghai.json"],
            )

    def test_prague_is_covered_without_a_suite_and_osaka_is_excluded(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            actual = self.inventory(fixtures, manifest)
            self.assertIn("Prague", actual["covered_without_suite"])
            self.assertNotIn("Prague", actual["excluded"])
            self.assertIn("Osaka", actual["excluded"])
            self.assertEqual(
                actual["suites"]["hist-full"]["component_suites"],
                ["byzantium", "constantinoplefix", "cancun", "hist-transitions"],
            )

    def test_smoke_is_drawn_from_cancun(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            actual = self.inventory(fixtures, manifest)
            smoke = actual["suites"]["hist-smoke"]
            self.assertEqual(smoke["network"], "Cancun")
            self.assertEqual([f["path"] for f in smoke["files"]], ["cancun.json"])

    def test_emit_refuses_the_empty_constantinople_suite(self):
        with tempfile.TemporaryDirectory() as tmp:
            fixtures, manifest = self.make_root(Path(tmp))
            output = Path(tmp) / "manifests.json"
            argv = ["--fixtures-root", str(fixtures), "--sources", str(manifest),
                    "--lane", "historical", "--output", str(output)]
            self.assertEqual(generator.main(argv), 0)
            self.assertEqual(generator.main(argv + ["--check"]), 0)
            self.assertEqual(
                generator.main(argv + ["--check", "--emit-suite", "constantinople"]), 2
            )
            buffer = io.StringIO()
            with contextlib.redirect_stdout(buffer):
                self.assertEqual(
                    generator.main(argv + ["--check", "--emit-suite", "byzantium"]), 0
                )
            rows = [line.split("\t") for line in buffer.getvalue().splitlines()]
            self.assertEqual(len(rows), 2)
            self.assertTrue(all(len(row) == 2 and row[1] for row in rows))


class DormantTableTests(unittest.TestCase):
    def test_runnable_forks_carry_no_dormant_cells(self):
        for label in ("Prague", "Osaka", "BPO1", "BPO2", "Amsterdam"):
            self.assertEqual(constants.dormant_for(label), {}, label)

    def test_era_dormants_stack(self):
        byzantium = constants.dormant_for("Byzantium")
        for field in ("blob.target", "blob.max", "blob.baseFeeUpdateFraction",
                      "code.maxInitCodeSize", "tx.maxGas", "tx.maxTotalGas",
                      "block.maxRlpSize", "gas.floorTokenCost",
                      "gas.perAuthIntrinsic", "gas.coldAccountAccess",
                      "gas.txAccessListAddress", "gas.txAccessListStorageKey"):
            self.assertIn(field, byzantium, field)
        # Berlin prices access warm/cold, so the flat prices are dormant;
        # Byzantium prices flat, so they are live -- except EXTCODEHASH,
        # which is undefined before EIP-1052.
        for field in ("access.balance", "access.extCode", "access.sload",
                      "access.call"):
            self.assertIn(field, constants.dormant_for("Berlin"), field)
            self.assertNotIn(field, byzantium, field)
        self.assertIn("access.extCodeHash", byzantium)
        self.assertNotIn("access.extCodeHash",
                         constants.dormant_for("Petersburg"))
        # Cancun has a live blob schedule: nothing blob-dormant.
        cancun = constants.dormant_for("Cancun")
        for field in ("blob.target", "blob.max", "blob.baseFeeUpdateFraction"):
            self.assertNotIn(field, cancun, field)

    def test_every_dormant_key_is_a_checked_field(self):
        checked = {path for path, status in constants.COVERAGE.items()
                   if status == "checked"}
        for label in ("Byzantium", "Constantinople", "Petersburg",
                      "Istanbul", "MuirGlacier", "Berlin", "London",
                      "ArrowGlacier", "GrayGlacier", "Paris", "Shanghai",
                      "Cancun"):
            self.assertTrue(set(constants.dormant_for(label)) <= checked, label)

    def test_constantinople_is_all_dormant(self):
        checked = {path for path, status in constants.COVERAGE.items()
                   if status == "checked"}
        self.assertEqual(set(constants.dormant_for("Constantinople")), checked)
        entry = constants.constantinople_entry()
        self.assertIsNone(entry["module"])
        self.assertEqual(set(entry["constants"]), checked)


if __name__ == "__main__":
    unittest.main()
