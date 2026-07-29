#!/usr/bin/env python3
"""Create Jaune's frozen Python 3.11.9 generator/oracle environment.

The command consumes scripts/sources.json and the hash-locked requirements
file referenced by it.  It never installs the execution-specs checkout as a
machine-local path dependency; generators import source from the independently
manifest-pinned checkout.

A correct existing venv is an offline no-op.  Any other existing destination
is refused without mutation.  A fresh venv is built in a relocatable temporary
sibling, validated with env_doctor.py, and atomically placed at the requested
destination.  Interrupted staging directories are left with an obvious
``.bootstrap-`` name for manual inspection.
"""
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

import env_doctor

DEFAULT_MANIFEST = Path(__file__).resolve().parent / "sources.json"


class BootstrapError(Exception):
    """A safe refusal or failed bootstrap action."""


@dataclass(frozen=True)
class EnvironmentState:
    exists: bool
    correct: bool
    problems: tuple[str, ...]


def _path_exists(path: Path) -> bool:
    return os.path.lexists(path)


def execution_specs_from_args(explicit: Path | None, manifest: dict) -> Path:
    spec = manifest["execution_specs"]
    if explicit is not None:
        selected = explicit.expanduser()
    elif os.environ.get(spec["default_env_var"]):
        selected = Path(os.environ[spec["default_env_var"]]).expanduser()
    else:
        selected = Path.home() / spec["default_subpath_from_home"]
    return Path(os.path.abspath(os.fspath(selected)))


def venv_from_args(explicit: Path | None, execution_specs: Path) -> Path:
    selected = explicit.expanduser() if explicit is not None else execution_specs / "venv"
    return Path(os.path.abspath(os.fspath(selected)))


def validate_inputs(manifest: dict, manifest_path: Path, execution_specs: Path) -> Path:
    spec = manifest["python_oracle"]
    if spec["patch_policy"] != "exact":
        raise BootstrapError(
            "python_oracle.patch_policy must be 'exact' for reproducible generators"
        )
    if spec["package_manager"] != "uv":
        raise BootstrapError("python_oracle.package_manager must be 'uv'")
    if spec["full_lock_status"] != "locked":
        raise BootstrapError("python_oracle.full_lock_status must be 'locked'")

    checkout_problems = [
        f"{check.name}: {check.detail}"
        for check in env_doctor.check_execution_specs(manifest, execution_specs)
        if check.status != env_doctor.STATUS_OK
    ]
    missing_layout = [
        f"src/{relative}"
        for relative in env_doctor.GENERATOR_SOURCE_LAYOUT
        if not (execution_specs / "src" / relative).is_file()
    ]
    if missing_layout:
        checkout_problems.append(
            "execution-specs layout missing: " + ", ".join(missing_layout)
        )
    if checkout_problems:
        raise BootstrapError(
            "execution-specs is not the clean manifest-pinned generator source:\n  - "
            + "\n  - ".join(checkout_problems)
        )

    try:
        lock_path = env_doctor.oracle_lock_path(manifest, manifest_path)
    except env_doctor.ManifestError as error:
        raise BootstrapError(str(error)) from error
    if not lock_path.is_file():
        raise BootstrapError(f"requirements lock not found: {lock_path}")
    actual_hash = env_doctor.sha256_file(lock_path)
    expected_hash = spec["requirements_lock_sha256"]
    if actual_hash != expected_hash:
        raise BootstrapError(
            f"requirements lock hash mismatch: expected {expected_hash}, got {actual_hash}"
        )
    try:
        env_doctor.parse_requirements_lock(lock_path)
    except env_doctor.ManifestError as error:
        raise BootstrapError(str(error)) from error
    return lock_path


def inspect_environment(
    manifest: dict, manifest_path: Path, venv: Path
) -> EnvironmentState:
    if not _path_exists(venv):
        return EnvironmentState(False, False, ())
    if venv.is_symlink():
        return EnvironmentState(
            True, False, (f"destination is a symbolic link: {venv}",)
        )
    if not venv.is_dir():
        return EnvironmentState(
            True, False, (f"destination exists but is not a directory: {venv}",)
        )
    checks = env_doctor.check_python_oracle(manifest, venv, manifest_path)
    problems = tuple(
        f"{check.name}: {check.detail}"
        for check in checks
        if check.status != env_doctor.STATUS_OK
    )
    return EnvironmentState(True, not problems, problems)


def _run(command: list[str], *, offline: bool) -> str:
    environment = os.environ.copy()
    environment["UV_NO_PROGRESS"] = "1"
    if offline:
        environment["UV_OFFLINE"] = "1"
    try:
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=False,
            env=environment,
        )
    except OSError as error:
        raise BootstrapError(f"could not execute {command[0]}: {error}") from error
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip() or "no diagnostic"
        if offline:
            detail += (
                "\nOffline mode uses only already-cached Python/package artifacts; "
                "rerun without --offline after arranging network access, or prefill "
                "uv's cache on this machine."
            )
        raise BootstrapError(f"command failed ({' '.join(command)}): {detail}")
    return result.stdout.strip()


def install_fresh(
    manifest: dict,
    manifest_path: Path,
    lock_path: Path,
    venv: Path,
    uv: str,
    *,
    offline: bool,
) -> None:
    if not venv.parent.is_dir():
        raise BootstrapError(
            f"venv parent directory does not exist: {venv.parent}; create or "
            "select the execution-specs checkout first"
        )

    staging = Path(
        tempfile.mkdtemp(prefix=f".{venv.name}.bootstrap-", dir=str(venv.parent))
    )
    staging.rmdir()
    try:
        venv_command = [
            uv,
            "venv",
            "--relocatable",
            "--python",
            manifest["python_oracle"]["intended_version"],
        ]
        if offline:
            venv_command.extend(["--offline", "--no-python-downloads"])
        venv_command.append(str(staging))
        _run(venv_command, offline=offline)

        sync_command = [
            uv,
            "pip",
            "sync",
            "--python",
            str(staging / "bin" / "python"),
            "--require-hashes",
        ]
        if offline:
            sync_command.append("--offline")
        sync_command.append(str(lock_path))
        _run(sync_command, offline=offline)

        state = inspect_environment(manifest, manifest_path, staging)
        if not state.correct:
            raise BootstrapError(
                "staged venv failed frozen-environment validation:\n  - "
                + "\n  - ".join(state.problems)
            )
        if _path_exists(venv):
            raise BootstrapError(
                f"destination appeared during installation; refusing to overwrite: {venv}"
            )
        os.replace(staging, venv)
    except Exception:
        if _path_exists(staging):
            print(
                f"warning: preserved incomplete staging directory for inspection: {staging}",
                file=sys.stderr,
            )
        raise


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=DEFAULT_MANIFEST,
        help=f"path to the external-source manifest (default: {DEFAULT_MANIFEST})",
    )
    parser.add_argument(
        "--execution-specs",
        type=Path,
        default=None,
        help="pinned checkout root (default: $EELS_ROOT or ~/execution-specs)",
    )
    parser.add_argument(
        "--venv",
        type=Path,
        default=None,
        help="venv destination (default: <execution-specs>/venv)",
    )
    parser.add_argument(
        "--uv",
        default="uv",
        help="uv executable name or path (default: uv)",
    )
    parser.add_argument(
        "--offline",
        action="store_true",
        help="forbid Python/package downloads and use only uv's local cache",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="validate inputs and report actions without creating a venv",
    )
    return parser


def main(argv: list[str]) -> int:
    args = build_parser().parse_args(argv)
    try:
        manifest = env_doctor.load_manifest(args.manifest)
        execution_specs = execution_specs_from_args(args.execution_specs, manifest)
        venv = venv_from_args(args.venv, execution_specs)
        lock_path = validate_inputs(
            manifest, args.manifest, execution_specs
        )
    except (env_doctor.ManifestError, BootstrapError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    state = inspect_environment(manifest, args.manifest, venv)
    if state.correct:
        print("NO-OP — the existing Python oracle venv exactly matches the frozen lock.")
        print(f"Verified destination: {venv}")
        print("No network or filesystem changes were made.")
        return 0
    if state.exists:
        print(
            f"error: refusing existing venv because it does not exactly match "
            f"Python {manifest['python_oracle']['intended_version']} and the frozen "
            f"package lock: {venv}",
            file=sys.stderr,
        )
        for problem in state.problems:
            print(f"  - {problem}", file=sys.stderr)
        print(
            "Recovery: inspect the venv, then manually remove or move it only if "
            "you are certain it is disposable; alternatively choose a different "
            "--venv destination. This command never mutates an unexpected venv.",
            file=sys.stderr,
        )
        return 1

    uv_path = shutil.which(args.uv)
    if uv_path is None:
        print(f"error: uv executable not found: {args.uv}", file=sys.stderr)
        return 1

    if args.dry_run:
        mode = "offline/cache-only" if args.offline else "frozen network/cache"
        print(f"Would create relocatable Python {manifest['python_oracle']['intended_version']} venv")
        print(f"Would sync only hash-verified packages from: {lock_path}")
        print(f"Mode: {mode}")
        print(f"Would atomically place the verified venv at: {venv}")
        print("No network or filesystem changes were made.")
        return 0

    try:
        install_fresh(
            manifest,
            args.manifest,
            lock_path,
            venv,
            uv_path,
            offline=args.offline,
        )
    except BootstrapError as error:
        print(f"error: bootstrap failed safely: {error}", file=sys.stderr)
        return 1

    print(f"OK — installed frozen Python oracle venv at {venv}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
