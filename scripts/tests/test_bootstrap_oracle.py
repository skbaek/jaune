#!/usr/bin/env python3
"""Focused, network-free tests for scripts/bootstrap_oracle.py."""
from __future__ import annotations

import hashlib
import importlib.util
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS_DIR))

import env_doctor


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


bootstrap = load_module("bootstrap_oracle", SCRIPTS_DIR / "bootstrap_oracle.py")


def git(path: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(path), *args],
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def make_checkout(path: Path) -> str:
    subprocess.run(["git", "init", "-q", str(path)], check=True)
    git(path, "config", "user.email", "test@example.com")
    git(path, "config", "user.name", "Test")
    git(path, "config", "commit.gpgsign", "false")
    # bootstrap_oracle only checks that these exist, so inert files suffice
    # here; the layout itself comes from env_doctor so it cannot drift from
    # what the generators require.
    for relative in env_doctor.GENERATOR_SOURCE_LAYOUT:
        target = path / "src" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("# synthetic source\n")
    git(path, "add", ".")
    git(path, "commit", "-q", "-m", "synthetic execution-specs")
    git(path, "remote", "add", "origin", "https://example.invalid/execution-specs.git")
    return git(path, "rev-parse", "HEAD")


def make_lock(path: Path) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "coincurve==20.0.0 \\\n"
        f"    --hash=sha256:{'1' * 64}\n"
        "py-ecc==8.0.0 \\\n"
        f"    --hash=sha256:{'2' * 64}\n"
    )
    return hashlib.sha256(path.read_bytes()).hexdigest()


def make_manifest(path: Path, checkout_commit: str) -> None:
    lock_hash = make_lock(path.parent / "oracle/requirements.lock")
    data = {
        "schema_version": 1,
        "execution_specs": {
            "repo_url": "https://example.invalid/execution-specs.git",
            "commit": checkout_commit,
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
            "archive_url": "https://example.invalid/fixtures.tar.gz",
            "archive_filename": "fixtures.tar.gz",
            "archive_sha256": "3" * 64,
            "fixtures_subpath": "fixtures",
            "expected_top_level_dirs": ["blockchain_tests"],
        },
        "python_oracle": {
            "intended_version": "3.11.9",
            "patch_policy": "exact",
            "package_manager": "uv",
            "package_manager_tested_version": "0.11.3",
            "requirements_input": "oracle/requirements.in",
            "requirements_lock": "oracle/requirements.lock",
            "requirements_lock_sha256": lock_hash,
            "known_packages": {"py-ecc": "8.0.0", "coincurve": "20.0.0"},
            "full_lock_status": "locked",
        },
    }
    path.write_text(json.dumps(data))


def fake_python(venv: Path, version: str, packages: dict[str, str]) -> None:
    bin_dir = venv / "bin"
    bin_dir.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(
        {
            "python_version": version,
            "packages": packages,
            "imports": {"coincurve": None, "Crypto": None, "py_ecc": None},
        }
    )
    python = bin_dir / "python"
    python.write_text(f"#!/bin/sh\ncat <<'EOF'\n{payload}\nEOF\n")
    python.chmod(0o755)


def make_fake_uv(path: Path) -> None:
    payload = json.dumps(
        {
            "python_version": "3.11.9",
            "packages": {"coincurve": "20.0.0", "py-ecc": "8.0.0"},
            "imports": {"coincurve": None, "Crypto": None, "py_ecc": None},
        }
    )
    path.write_text(
        "#!/usr/bin/env python3\n"
        "import pathlib, sys\n"
        f"payload = {payload!r}\n"
        "if len(sys.argv) > 1 and sys.argv[1] == 'venv':\n"
        "    root = pathlib.Path(sys.argv[-1])\n"
        "    (root / 'bin').mkdir(parents=True)\n"
        "    python = root / 'bin' / 'python'\n"
        "    python.write_text(\"#!/bin/sh\\ncat <<'EOF'\\n\" + payload + \"\\nEOF\\n\")\n"
        "    python.chmod(0o755)\n"
        "sys.exit(0)\n"
    )
    path.chmod(0o755)


class BootstrapOracleTests(unittest.TestCase):
    def fixture(self, root: Path) -> tuple[Path, Path, Path]:
        checkout = root / "execution specs"
        commit = make_checkout(checkout)
        manifest = root / "config with spaces" / "sources.json"
        manifest.parent.mkdir()
        make_manifest(manifest, commit)
        uv = root / "fake uv"
        make_fake_uv(uv)
        return checkout, manifest, uv

    def run_cli(
        self, checkout: Path, manifest: Path, uv: Path, venv: Path, *extra: str
    ) -> tuple[int, str, str]:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            rc = bootstrap.main(
                [
                    "--manifest",
                    str(manifest),
                    "--execution-specs",
                    str(checkout),
                    "--venv",
                    str(venv),
                    "--uv",
                    str(uv),
                    *extra,
                ]
            )
        return rc, stdout.getvalue(), stderr.getvalue()

    def test_fresh_install_with_spaces_and_idempotent_rerun(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            checkout, manifest, uv = self.fixture(root)
            venv = checkout / "oracle venv"
            rc, stdout, stderr = self.run_cli(checkout, manifest, uv, venv)
            self.assertEqual(rc, 0, stderr)
            self.assertIn("installed frozen", stdout)
            self.assertTrue((venv / "bin/python").is_file())
            self.assertEqual(list(checkout.glob(".oracle venv.bootstrap-*")), [])

            uv.rename(root / "fake uv.offline")
            rc, stdout, stderr = self.run_cli(checkout, manifest, uv, venv)
            self.assertEqual(rc, 0, stderr)
            self.assertIn("NO-OP", stdout)

    def test_refuses_wrong_python_missing_and_wrong_package(self):
        scenarios = {
            "wrong-python": (
                "3.11.8",
                {"coincurve": "20.0.0", "py-ecc": "8.0.0"},
            ),
            "missing-package": ("3.11.9", {"coincurve": "20.0.0"}),
            "wrong-package": (
                "3.11.9",
                {"coincurve": "20.0.0", "py-ecc": "7.0.0"},
            ),
        }
        for name, (python_version, packages) in scenarios.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                checkout, manifest, uv = self.fixture(root)
                venv = checkout / "venv"
                fake_python(venv, python_version, packages)
                marker = venv / "keep.txt"
                marker.write_text("untouched\n")
                rc, _, stderr = self.run_cli(checkout, manifest, uv, venv)
                self.assertEqual(rc, 1)
                self.assertIn("refusing existing venv", stderr)
                self.assertEqual(marker.read_text(), "untouched\n")

    def test_wrong_checkout_revision_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            checkout, manifest, uv = self.fixture(root)
            (checkout / "second.txt").write_text("new\n")
            git(checkout, "add", "second.txt")
            git(checkout, "commit", "-q", "-m", "wrong revision")
            rc, _, stderr = self.run_cli(
                checkout, manifest, uv, checkout / "venv"
            )
            self.assertEqual(rc, 2)
            self.assertIn("execution-specs is not", stderr)
            self.assertFalse((checkout / "venv").exists())

    def test_path_precedence_option_then_environment_then_home(self):
        manifest = {
            "execution_specs": {
                "default_env_var": "EELS_ROOT",
                "default_subpath_from_home": "execution-specs",
            }
        }
        with patch.dict(os.environ, {"EELS_ROOT": "/environment/root"}):
            self.assertEqual(
                bootstrap.execution_specs_from_args(Path("/explicit/root"), manifest),
                Path("/explicit/root"),
            )
            self.assertEqual(
                bootstrap.execution_specs_from_args(None, manifest),
                Path("/environment/root"),
            )
        with patch.dict(os.environ, {}, clear=True), patch.object(
            Path, "home", return_value=Path("/synthetic/home")
        ):
            self.assertEqual(
                bootstrap.execution_specs_from_args(None, manifest),
                Path("/synthetic/home/execution-specs"),
            )

    def test_offline_dry_run_makes_no_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            checkout, manifest, uv = self.fixture(root)
            venv = checkout / "venv"
            rc, stdout, stderr = self.run_cli(
                checkout, manifest, uv, venv, "--offline", "--dry-run"
            )
            self.assertEqual(rc, 0, stderr)
            self.assertIn("offline/cache-only", stdout)
            self.assertFalse(venv.exists())


if __name__ == "__main__":
    unittest.main()
