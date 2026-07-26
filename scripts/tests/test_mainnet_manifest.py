"""Synthetic tests for the strict current-mainnet manifest generator."""
from __future__ import annotations

import importlib.util
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


def fixture(root: Path, relative: str, network: str) -> None:
    path = root / "blockchain_tests" / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({f"{network}-{relative}": {"network": network}}))


class ManifestTests(unittest.TestCase):
    def make_root(self, tmp: Path) -> tuple[Path, Path]:
        fixtures = tmp / "fixtures"
        for name in ["blockchain_tests", "blockchain_tests_engine", "blockchain_tests_engine_x", "blockchain_tests_sync", "state_tests", "transaction_tests"]:
            (fixtures / name).mkdir(parents=True, exist_ok=True)
        fixture(fixtures, "z.json", "Prague")
        fixture(fixtures, "a.json", "Prague")
        fixture(fixtures, "osaka.json", "Osaka")
        fixture(fixtures, "old.json", "Cancun")
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
            self.assertEqual(actual["excluded"]["Cancun"]["reason"], "unsupported historical fork or transition")

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


if __name__ == "__main__":
    unittest.main()
