#!/usr/bin/env python3
"""Synthetic tests for scripts/bootstrap_mainnet.py.

Every archive is a tiny locally-built tar.gz served over a file:// URL. The
suite never contacts the network or reads/writes the user's real CURRENT MAINNET
destination.
"""
from __future__ import annotations

import importlib.util
import io
import json
import os
import sys
import tarfile
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS_DIR / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


env_doctor = _load("env_doctor")
bootstrap = _load("bootstrap_mainnet")


_BLS_G1 = "fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_valid.json"
_BLS_BLOB = "fixtures/blockchain_tests/cancun/eip4844_blobs/test_valid_inputs.json"

VALID_FILES = {
    "fixtures/.meta/index.json": b'{"root_hash":"0xsynthetic","test_count":4}\n',
    "fixtures/.meta/fixtures.ini": (
        b"; a comment\n[fixtures]\nref = refs/tags/tests-v0\nbuild = stable\n"
    ),
    _BLS_G1: b'{"valid": true}\n',
    _BLS_BLOB: b"{}\n",
    "fixtures/state_tests/example/test_state.json": b"{}\n",
}


def write_archive(
    path: Path,
    regular_files: dict[str, bytes],
    extra_members: list[tuple[tarfile.TarInfo, bytes | None]] | None = None,
) -> str:
    with tarfile.open(path, "w:gz") as tar:
        for name, data in regular_files.items():
            info = tarfile.TarInfo(name)
            info.size = len(data)
            info.mtime = 0
            tar.addfile(info, io.BytesIO(data))
        for info, data in extra_members or []:
            if data is None:
                tar.addfile(info)
            else:
                info.size = len(data)
                tar.addfile(info, io.BytesIO(data))
    return env_doctor.sha256_file(path)


def base_manifest(archive_url: str, archive_sha: str) -> dict:
    return {
        "schema_version": 1,
        "execution_specs": {
            "repo_url": "https://example.invalid/execution-specs.git",
            "commit": "0" * 40,
            "default_env_var": "EELS_ROOT",
            "default_subpath_from_home": "execution-specs",
        },
        "ethereum_tests": {
            "repo_url": "https://example.invalid/tests.git",
            "commit": "1" * 40,
            "relative_path_from_execution_specs": "tests/fixtures/ethereum_tests",
        },
        "legacy_tests_submodule": {
            "commit": "2" * 40,
            "relative_path_from_ethereum_tests": "LegacyTests",
        },
        "eest": {
            "release_tag": "v0",
            "archive_url": archive_url,
            "archive_filename": "fixtures_stable.tar.gz",
            "archive_sha256": archive_sha,
            "default_env_var": "EEST_ROOT",
            "default_subpath_from_home": "eest-fixtures",
            "fixtures_subpath": "fixtures",
            "expected_top_level_dirs": ["blockchain_tests"],
        },
        "current_mainnet": {
            "release_tag": "tests@v0.0.0",
            "release_commit": "3" * 40,
            "release_url": "https://example.invalid/tests@v0.0.0",
            "archive_url": archive_url,
            "archive_filename": "fixtures.tar.gz",
            "archive_sha256": archive_sha,
            "default_env_var": "EEST_MAINNET_ROOT",
            "default_subpath_from_home": "eest-mainnet-v0.0.0",
            "fixtures_subpath": "fixtures",
            "expected_top_level_dirs": ["blockchain_tests", "state_tests"],
            "bls_tier_subpaths": [
                "blockchain_tests/prague/eip2537_bls_12_381_precompiles",
                "blockchain_tests/cancun/eip4844_blobs",
            ],
            "metadata_file_subpath": ".meta/fixtures.ini",
            "metadata_expected": {"ref": "refs/tags/tests-v0", "build": "stable"},
            "metadata_json_file_subpath": ".meta/index.json",
            "metadata_json_expected": {"root_hash": "0xsynthetic", "test_count": 4},
        },
        "python_oracle": {
            "intended_version": "3.11.9",
            "patch_policy": "exact",
            "package_manager": "uv",
            "requirements_lock": "oracle/requirements.lock",
            "requirements_lock_sha256": "0" * 64,
            "known_packages": {"py-ecc": "8.0.0", "coincurve": "20.0.0"},
            "full_lock_status": "locked",
        },
    }


class Scenario:
    """A temp root holding a synthetic archive and a manifest pointing at it."""

    def __init__(
        self,
        root: Path,
        regular_files: dict[str, bytes] | None = None,
        extra_members: list[tuple[tarfile.TarInfo, bytes | None]] | None = None,
        sha_override: str | None = None,
    ):
        self.root = root
        self.archive_source = root / "download source" / "fixtures.tar.gz"
        self.archive_source.parent.mkdir(parents=True)
        real_sha = write_archive(
            self.archive_source,
            regular_files if regular_files is not None else VALID_FILES,
            extra_members,
        )
        self.archive_sha = sha_override or real_sha
        self.manifest_path = root / "sources.json"
        self.manifest_data = base_manifest(
            self.archive_source.as_uri(), self.archive_sha
        )
        self.manifest_path.write_text(json.dumps(self.manifest_data))
        self.mainnet_root = root / "eest-mainnet-v0.0.0"

    def write_manifest(self, data: dict) -> None:
        self.manifest_data = data
        self.manifest_path.write_text(json.dumps(data))

    def truncate_source(self, keep_bytes: int) -> None:
        data = self.archive_source.read_bytes()[:keep_bytes]
        self.archive_source.write_bytes(data)


class BootstrapMainnetTests(unittest.TestCase):
    def run_cli(self, scenario: Scenario, *extra: str) -> tuple[int, str, str]:
        stdout, stderr = io.StringIO(), io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            rc = bootstrap.main(
                [
                    "--manifest",
                    str(scenario.manifest_path),
                    "--mainnet-root",
                    str(scenario.mainnet_root),
                    *extra,
                ]
            )
        return rc, stdout.getvalue(), stderr.getvalue()

    def assert_no_staging_or_part(self, scenario: Scenario) -> None:
        if scenario.mainnet_root.exists():
            self.assertEqual(
                list(scenario.mainnet_root.glob(".fixtures.bootstrap-*")), []
            )
            self.assertEqual(list(scenario.mainnet_root.glob("*.part")), [])

    # ----- correct extraction & idempotence -------------------------------

    def test_fresh_install_extracts_and_verifies(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp))
            rc, stdout, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 0, stderr)
            self.assertIn("OK — installed", stdout)

            fixtures = scenario.mainnet_root / "fixtures"
            self.assertTrue(
                (
                    fixtures
                    / "blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_valid.json"
                ).is_file()
            )
            self.assertTrue((scenario.mainnet_root / "fixtures.tar.gz").is_file())
            self.assert_no_staging_or_part(scenario)

            # The doctor recognises the produced tree, fast checks and deep.
            checks = env_doctor.check_current_mainnet(scenario.manifest_data, scenario.mainnet_root)
            deep = env_doctor.deep_compare_current_mainnet(
                scenario.manifest_data, scenario.mainnet_root
            )
            self.assertTrue(all(c.status == "ok" for c in checks), checks)
            self.assertTrue(all(c.status == "ok" for c in deep), deep)

    def test_idempotent_rerun_is_offline_no_op(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp))
            self.assertEqual(self.run_cli(scenario)[0], 0)

            # Remove the download source to prove the rerun is fully offline.
            scenario.archive_source.unlink()

            rc, stdout, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 0, stderr)
            self.assertIn("NO-OP", stdout)
            self.assertIn("No network or filesystem changes", stdout)

            rc, stdout, _ = self.run_cli(scenario, "--dry-run")
            self.assertEqual(rc, 0)
            self.assertIn("NO-OP", stdout)

    def test_reuses_prepositioned_verified_archive_offline(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp))
            scenario.mainnet_root.mkdir()
            # Pre-place the verified archive; then break the URL entirely.
            (scenario.mainnet_root / "fixtures.tar.gz").write_bytes(
                scenario.archive_source.read_bytes()
            )
            manifest = json.loads(scenario.manifest_path.read_text())
            manifest["current_mainnet"]["archive_url"] = "http://example.invalid/nope.tar.gz"
            scenario.write_manifest(manifest)

            rc, stdout, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 0, stderr)
            self.assertIn("OK — installed", stdout)
            self.assertIn("reused verified cached archive", stdout)

    def test_dry_run_makes_no_changes(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp))
            rc, stdout, stderr = self.run_cli(scenario, "--dry-run")
            self.assertEqual(rc, 0, stderr)
            self.assertIn("DRY RUN", stdout)
            self.assertIn("Would download", stdout)
            self.assertFalse(scenario.mainnet_root.exists())

    def test_paths_with_spaces(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp))
            scenario.mainnet_root = Path(tmp) / "mainnet fixtures with spaces"
            rc, stdout, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 0, stderr)
            self.assertTrue(
                (scenario.mainnet_root / "fixtures/state_tests/example/test_state.json").is_file()
            )

    # ----- checksum & transport failures ----------------------------------

    def test_download_checksum_mismatch_refuses_and_cleans_up(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp), sha_override="a" * 64)
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 1)
            self.assertIn("checksum verification", stderr)
            self.assertFalse((scenario.mainnet_root / "fixtures").exists())
            self.assert_no_staging_or_part(scenario)

    def test_truncated_download_refuses(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp))
            scenario.truncate_source(32)  # manifest sha still names the full file
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 1)
            self.assertIn("bootstrap failed safely", stderr)
            self.assertFalse((scenario.mainnet_root / "fixtures").exists())
            self.assert_no_staging_or_part(scenario)

    def test_corrupt_cached_archive_is_refused_not_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp))
            scenario.mainnet_root.mkdir()
            corrupt = scenario.mainnet_root / "fixtures.tar.gz"
            corrupt.write_bytes(b"not the real archive")
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 1)
            self.assertIn("does not verify", stderr)
            self.assertEqual(corrupt.read_bytes(), b"not the real archive")
            self.assertFalse((scenario.mainnet_root / "fixtures").exists())

    # ----- malicious archive members --------------------------------------

    def _malicious_scenario(self, tmp, member, data=b"payload"):
        return Scenario(Path(tmp), VALID_FILES, extra_members=[(member, data)])

    def test_absolute_path_member_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            member = tarfile.TarInfo("/etc/evil")
            scenario = self._malicious_scenario(tmp, member)
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 1)
            self.assertIn("unsafe archive", stderr)
            self.assertFalse(Path("/etc/evil").exists())
            self.assertFalse((scenario.mainnet_root / "fixtures").exists())
            self.assert_no_staging_or_part(scenario)

    def test_traversal_member_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            member = tarfile.TarInfo("fixtures/../../evil.json")
            scenario = self._malicious_scenario(tmp, member)
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 1)
            self.assertIn("unsafe archive", stderr)
            self.assertFalse((scenario.root / "evil.json").exists())
            self.assert_no_staging_or_part(scenario)

    def test_prefix_escaping_member_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            member = tarfile.TarInfo("outside/evil.json")
            scenario = self._malicious_scenario(tmp, member)
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 1)
            self.assertIn("escapes", stderr)
            self.assert_no_staging_or_part(scenario)

    def test_symlink_member_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            member = tarfile.TarInfo("fixtures/link")
            member.type = tarfile.SYMTYPE
            member.linkname = "../../../../etc/passwd"
            scenario = self._malicious_scenario(tmp, member, data=None)
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 1)
            self.assertIn("link", stderr)
            self.assertFalse((scenario.mainnet_root / "fixtures").exists())

    def test_hardlink_member_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            member = tarfile.TarInfo("fixtures/hard")
            member.type = tarfile.LNKTYPE
            member.linkname = "fixtures/.meta/fixtures.ini"
            scenario = self._malicious_scenario(tmp, member, data=None)
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 1)
            self.assertIn("link", stderr)

    def test_special_device_member_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            member = tarfile.TarInfo("fixtures/dev")
            member.type = tarfile.CHRTYPE
            member.devmajor = 1
            member.devminor = 3
            scenario = self._malicious_scenario(tmp, member, data=None)
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 1)
            self.assertIn("special", stderr)

    # ----- existing-tree refusals -----------------------------------------

    def test_partial_existing_tree_is_refused_not_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp))
            # A structurally incomplete tree: only one top-level dir, no metadata.
            partial = scenario.mainnet_root / "fixtures" / "blockchain_tests"
            partial.mkdir(parents=True)
            marker = scenario.mainnet_root / "fixtures" / "keep.txt"
            marker.write_text("do not touch\n")
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 1)
            self.assertIn("refusing existing fixture tree", stderr)
            self.assertIn("will not repair", stderr)
            self.assertEqual(marker.read_text(), "do not touch\n")

    def test_wrong_provenance_tree_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp))
            self.assertEqual(self.run_cli(scenario)[0], 0)
            # Corrupt the provenance file; a rerun must refuse, not "fix" it.
            meta = scenario.mainnet_root / "fixtures/.meta/index.json"
            meta.write_text('{"root_hash":"0xtampered","test_count":4}\n')
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 1)
            self.assertIn("refusing existing fixture tree", stderr)

    # ----- manifest validation --------------------------------------------

    def test_bad_sha_in_manifest_is_usage_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp))
            manifest = json.loads(scenario.manifest_path.read_text())
            manifest["current_mainnet"]["archive_sha256"] = "xyz"
            scenario.write_manifest(manifest)
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 2)
            self.assertIn("archive_sha256", stderr)

    def test_archive_filename_traversal_is_usage_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp))
            manifest = json.loads(scenario.manifest_path.read_text())
            manifest["current_mainnet"]["archive_filename"] = "../escape.tar.gz"
            scenario.write_manifest(manifest)
            rc, _, stderr = self.run_cli(scenario)
            self.assertEqual(rc, 2)
            self.assertIn("archive_filename", stderr)

    def test_explicit_archive_cache_precedes_default(self):
        with tempfile.TemporaryDirectory() as tmp:
            scenario = Scenario(Path(tmp))
            cache = Path(tmp) / "shared cache" / "fixtures.tar.gz"
            with mock.patch.dict(os.environ, {"EEST_MAINNET_ROOT": str(scenario.mainnet_root)}, clear=False):
                self.assertEqual(
                    bootstrap.archive_cache_from_args(cache, scenario.mainnet_root, scenario.manifest_data),
                    Path(os.path.abspath(cache)),
                )
                self.assertEqual(
                    bootstrap.archive_cache_from_args(None, scenario.mainnet_root, scenario.manifest_data),
                    scenario.mainnet_root / "fixtures.tar.gz",
                )


if __name__ == "__main__":
    unittest.main()
