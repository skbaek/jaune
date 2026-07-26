#!/usr/bin/env python3
"""Network-free tests for shared generator configuration and U256 output."""
from __future__ import annotations

import argparse
import functools
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS_DIR))

import bootstrap_oracle
import env_doctor

# Most files in the synthetic checkout only have to exist, so an inert comment
# is an honest stand-in.  ethereum/crypto/hash.py is different: the generator
# imports keccak256 from it and hashes real byte strings, so this one has to
# compute genuine Keccak-256 or the generator cannot run.  It wraps pycryptodome
# exactly as the pinned EELS module does instead of reimplementing the
# permutation, so the fixture cannot become a second, independent opinion about
# what Keccak-256 is.  The digests it produces are never shipped: the checked-in
# vectors come from the real pinned checkout.
SYNTHETIC_STUB = "# synthetic pinned source\n"
SYNTHETIC_HASH_MODULE = '''\
"""Synthetic stand-in for the pinned EELS ethereum.crypto.hash module."""
from Crypto.Hash import keccak
from ethereum_types.bytes import Bytes, Bytes32


def keccak256(buffer: Bytes | bytearray) -> Bytes32:
    return Bytes32(keccak.new(digest_bits=256).update(buffer).digest())
'''

# The frozen oracle closure the generator run path needs: the manifest package
# pins it enforces via require_known_packages, plus the modules the pinned EELS
# hash module imports.  The whole lock is the unit here, exactly as
# scripts/oracle/requirements.lock treats it, so these tests ask for all of it
# rather than for a per-test subset.
ORACLE_PACKAGES = {"py-ecc": "8.0.0", "coincurve": "20.0.0"}
ORACLE_MODULES = ("Crypto.Hash.keccak", "ethereum_types.bytes")

ORACLE_PROBE = """\
import json
import sys
from importlib import import_module
from importlib.metadata import version

modules, packages = json.loads(sys.argv[1])
for name in modules:
    import_module(name)
for name, expected in packages.items():
    actual = version(name)
    if actual != expected:
        raise SystemExit(f"{name} {actual} != {expected}")
"""

# Imported off the checkout's src root under the frozen oracle interpreter,
# which is the same code path the generator itself uses.
SYNTHETIC_KECCAK_PROBE = """\
import json
import sys

sys.path.insert(0, sys.argv[1])
from ethereum.crypto.hash import keccak256

print(json.dumps([keccak256(b"").hex(), keccak256(bytes(32)).hex()]))
"""


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


common = load_module("generator_common", SCRIPTS_DIR / "generator_common.py")


def interpreter_has_oracle_closure(python: str) -> bool:
    expectations = json.dumps([list(ORACLE_MODULES), ORACLE_PACKAGES])
    try:
        result = subprocess.run(
            [python, "-c", ORACLE_PROBE, expectations],
            capture_output=True,
            text=True,
        )
    except OSError:
        return False
    return result.returncode == 0


@functools.lru_cache(maxsize=None)
def find_oracle_interpreter() -> tuple[str | None, str]:
    """Locate an interpreter with the frozen oracle closure.

    Returns ``(interpreter, "")`` or ``(None, skip_reason)``.  The interpreter
    running this suite is preferred, so the documented
    ``<execution-specs>/venv/bin/python -m unittest ...`` form needs no lookup;
    otherwise the manifest-default oracle venv is used, which is the same
    checkout-and-venv resolution bootstrap_oracle.py performs.
    """
    if interpreter_has_oracle_closure(sys.executable):
        return sys.executable, ""
    # Only the venv lookup needs the real manifest.  Manifest validity is
    # test_env_doctor's assertion, not this module's, so a broken manifest is
    # reported there and skips here instead of failing the same defect twice.
    try:
        manifest = env_doctor.load_manifest(SCRIPTS_DIR / "sources.json")
    except env_doctor.ManifestError as error:
        return None, (
            f"cannot locate the frozen oracle venv because the manifest is "
            f"unreadable ({error}); this suite's interpreter "
            f"({sys.executable}) does not provide the oracle closure either"
        )
    execution_specs = bootstrap_oracle.execution_specs_from_args(None, manifest)
    venv_python = (
        bootstrap_oracle.venv_from_args(None, execution_specs) / "bin" / "python"
    )
    if interpreter_has_oracle_closure(str(venv_python)):
        return str(venv_python), ""
    wanted = ", ".join(
        [f"{name} {expected}" for name, expected in ORACLE_PACKAGES.items()]
        + list(ORACLE_MODULES)
    )
    return None, (
        f"no frozen oracle interpreter: neither this suite's interpreter "
        f"({sys.executable}) nor the manifest-default oracle venv "
        f"({venv_python}) provides {wanted}. Create the venv with "
        f"scripts/bootstrap_oracle.py, or run this suite as "
        f"'<execution-specs>/venv/bin/python -m unittest discover -s "
        f"scripts/tests'."
    )


def require_oracle_interpreter(test: unittest.TestCase) -> str:
    interpreter, reason = find_oracle_interpreter()
    if interpreter is None:
        test.skipTest(reason)
    return interpreter


def git(path: Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(path), *args],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def make_checkout(path: Path) -> str:
    subprocess.run(["git", "init", "-q", str(path)], check=True)
    git(path, "config", "user.email", "test@example.com")
    git(path, "config", "user.name", "Test")
    git(path, "config", "commit.gpgsign", "false")
    for relative in env_doctor.GENERATOR_SOURCE_LAYOUT:
        target = path / "src" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(
            SYNTHETIC_HASH_MODULE
            if relative == "ethereum/crypto/hash.py"
            else SYNTHETIC_STUB
        )
    git(path, "add", ".")
    git(path, "commit", "-q", "-m", "pinned")
    return git(path, "rev-parse", "HEAD")


def make_manifest(path: Path, commit: str) -> None:
    data = {
        "schema_version": 1,
        "execution_specs": {
            "repo_url": "https://example.invalid/execution-specs.git",
            "commit": commit,
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
            "archive_url": "https://example.invalid/eest.tar.gz",
            "archive_filename": "eest.tar.gz",
            "archive_sha256": "3" * 64,
            "fixtures_subpath": "fixtures",
            "expected_top_level_dirs": ["blockchain_tests"],
        },
        "python_oracle": {
            "intended_version": "3.11.9",
            "patch_policy": "exact",
            "package_manager": "uv",
            "requirements_lock": "oracle/requirements.lock",
            "requirements_lock_sha256": "4" * 64,
            "known_packages": dict(ORACLE_PACKAGES),
            "full_lock_status": "locked",
        },
    }
    path.write_text(json.dumps(data))


class GeneratorTests(unittest.TestCase):
    def test_u256_explicit_path_with_spaces_is_deterministic(self):
        # A full generator run, so it needs the frozen oracle closure: the
        # manifest package gate and the pinned keccak256 import both come after
        # the checkout is validated.
        python = require_oracle_interpreter(self)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            checkout = root / "execution specs"
            commit = make_checkout(checkout)
            manifest = root / "sources.json"
            make_manifest(manifest, commit)
            output_one = root / "output one.json"
            output_two = root / "output two.json"

            for output in (output_one, output_two):
                subprocess.run(
                    [
                        python,
                        str(SCRIPTS_DIR / "gen-u256-vectors.py"),
                        "--manifest",
                        str(manifest),
                        "--execution-specs",
                        str(checkout),
                        "--output",
                        str(output),
                    ],
                    check=True,
                    capture_output=True,
                    text=True,
                )
            self.assertEqual(output_one.read_bytes(), output_two.read_bytes())
            payload = json.loads(output_one.read_text())
            self.assertEqual(payload["header"]["eels_revision"], commit)

    def test_explicit_generator_path_precedes_eels_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            good = root / "good"
            commit = make_checkout(good)
            manifest_path = root / "sources.json"
            make_manifest(manifest_path, commit)
            parser = argparse.ArgumentParser()
            with patch.dict(os.environ, {"EELS_ROOT": str(root / "wrong")}):
                _, selected, _ = common.load_generator_source(
                    parser, manifest_path, good
                )
            self.assertEqual(selected, good)

    def test_eels_root_is_used_without_explicit_path(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            checkout = root / "from environment"
            commit = make_checkout(checkout)
            manifest_path = root / "sources.json"
            make_manifest(manifest_path, commit)
            parser = argparse.ArgumentParser()
            with patch.dict(os.environ, {"EELS_ROOT": str(checkout)}):
                _, selected, _ = common.load_generator_source(
                    parser, manifest_path, None
                )
            self.assertEqual(selected, checkout)

    def test_wrong_checkout_revision_is_clear_failure(self):
        # Checkout validation precedes the package gate and the pinned import,
        # so this failure mode is interpreter-independent: run it under whatever
        # interpreter runs the suite rather than requiring the oracle venv.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            checkout = root / "checkout"
            old_commit = make_checkout(checkout)
            manifest_path = root / "sources.json"
            make_manifest(manifest_path, old_commit)
            (checkout / "new.txt").write_text("new commit\n")
            git(checkout, "add", "new.txt")
            git(checkout, "commit", "-q", "-m", "new")
            result = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPTS_DIR / "gen-u256-vectors.py"),
                    "--manifest",
                    str(manifest_path),
                    "--execution-specs",
                    str(checkout),
                    "--output",
                    str(root / "must-not-exist.json"),
                ],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("revision mismatch", result.stderr)
            self.assertFalse((root / "must-not-exist.json").exists())

    def test_checkout_missing_a_generator_source_is_clear_failure(self):
        # The generator imports ethereum.crypto.hash at run time, well after the
        # checkout is validated.  It has to be part of the declared layout, or a
        # checkout missing it is reported as an opaque ModuleNotFoundError from
        # the middle of generation rather than as a checkout problem.  That
        # rejection is also interpreter-independent, for the reason above.
        self.assertIn("ethereum/crypto/hash.py", env_doctor.GENERATOR_SOURCE_LAYOUT)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            checkout = root / "checkout"
            commit = make_checkout(checkout)
            manifest_path = root / "sources.json"
            make_manifest(manifest_path, commit)
            (checkout / "src" / "ethereum" / "crypto" / "hash.py").unlink()
            result = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPTS_DIR / "gen-u256-vectors.py"),
                    "--manifest",
                    str(manifest_path),
                    "--execution-specs",
                    str(checkout),
                    "--output",
                    str(root / "must-not-exist.json"),
                ],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("expected Prague generator sources", result.stderr)
            self.assertIn("ethereum/crypto/hash.py", result.stderr)
            self.assertNotIn("ModuleNotFoundError", result.stderr)
            self.assertFalse((root / "must-not-exist.json").exists())

    def test_synthetic_checkout_keccak_matches_the_pinned_formula(self):
        # The synthetic ethereum.crypto.hash has to agree with the pinned EELS
        # module, not merely satisfy the import: these are the standard
        # Keccak-256 digests (not SHA3-256) the generator also hardcodes.  The
        # fixture wraps pycryptodome, so this needs the frozen oracle closure
        # too, and it is imported the way the generator imports it.
        python = require_oracle_interpreter(self)
        with tempfile.TemporaryDirectory() as tmp:
            checkout = Path(tmp) / "checkout"
            make_checkout(checkout)
            digests = json.loads(
                subprocess.run(
                    [python, "-c", SYNTHETIC_KECCAK_PROBE, str(checkout / "src")],
                    check=True,
                    capture_output=True,
                    text=True,
                ).stdout
            )
        self.assertEqual(
            digests,
            [
                "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
                "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
            ],
        )

    def test_bls_package_checks_report_missing_and_wrong_versions(self):
        manifest = {
            "python_oracle": {
                "known_packages": {"py-ecc": "8.0.0", "coincurve": "20.0.0"}
            }
        }
        parser = argparse.ArgumentParser()
        with patch.object(
            common,
            "version",
            side_effect=common.PackageNotFoundError("py-ecc"),
        ), self.assertRaises(SystemExit):
            common.require_known_packages(parser, manifest)

        parser = argparse.ArgumentParser()
        with patch.object(common, "version", return_value="7.0.0"), self.assertRaises(
            SystemExit
        ):
            common.require_known_packages(parser, manifest)


if __name__ == "__main__":
    unittest.main()
