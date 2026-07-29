#!/usr/bin/env python3
"""Safely bootstrap Jaune's Git-backed legacy fixture sources.

The command consumes scripts/sources.json, installs execution-specs plus the
ignored nested ethereum/tests checkout and its required LegacyTests submodule,
and leaves the final execution-specs checkout detached at the locked commit.

An existing installation is accepted only when every source is already at the
locked origin and revision with no tracked changes. Any other existing target
is refused: this command never repairs, resets, deletes, or overwrites it.

Python-standard-library only. Python environment and EEST installation are
deliberately deferred to later portability steps.
"""
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

import env_doctor

DEFAULT_MANIFEST = Path(__file__).resolve().parent / "sources.json"


class BootstrapError(Exception):
    """A safe refusal or failed bootstrap action."""


@dataclass(frozen=True)
class InstallationState:
    exists: bool
    correct: bool
    problems: tuple[str, ...]


def _path_exists(path: Path) -> bool:
    """Like Path.exists(), but also true for a broken symlink."""
    return os.path.lexists(path)


def _safe_relative_path(value: object, field: str) -> Path:
    if not isinstance(value, str) or not value:
        raise BootstrapError(f"manifest field {field} must be a nonempty string")
    pure = PurePosixPath(value)
    if pure.is_absolute() or any(part in ("", ".", "..") for part in pure.parts):
        raise BootstrapError(
            f"manifest field {field} must be a safe relative path, got {value!r}"
        )
    return Path(*pure.parts)


def validate_bootstrap_manifest(manifest: dict) -> None:
    """Validate the lock fields that can influence filesystem or Git actions."""
    if manifest.get("schema_version") != 1:
        raise BootstrapError(
            f"unsupported manifest schema_version {manifest.get('schema_version')!r}; "
            "expected 1"
        )

    for section in ("execution_specs", "ethereum_tests", "legacy_tests_submodule"):
        commit = manifest[section].get("commit")
        if (
            not isinstance(commit, str)
            or len(commit) != 40
            or any(char not in "0123456789abcdefABCDEF" for char in commit)
        ):
            raise BootstrapError(
                f"manifest field {section}.commit must be an exact 40-character "
                "hexadecimal commit"
            )

    for section in ("execution_specs", "ethereum_tests"):
        repo_url = manifest[section].get("repo_url")
        if not isinstance(repo_url, str) or not repo_url.strip():
            raise BootstrapError(
                f"manifest field {section}.repo_url must be a nonempty string"
            )

    environment_name = manifest["execution_specs"].get("default_env_var")
    if environment_name != "EELS_ROOT":
        raise BootstrapError(
            "manifest field execution_specs.default_env_var must preserve the "
            "EELS_ROOT convention"
        )
    _safe_relative_path(
        manifest["execution_specs"].get("default_subpath_from_home"),
        "execution_specs.default_subpath_from_home",
    )
    _safe_relative_path(
        manifest["ethereum_tests"]["relative_path_from_execution_specs"],
        "ethereum_tests.relative_path_from_execution_specs",
    )
    _safe_relative_path(
        manifest["legacy_tests_submodule"]["relative_path_from_ethereum_tests"],
        "legacy_tests_submodule.relative_path_from_ethereum_tests",
    )


def destination_from_args(explicit: Path | None, manifest: dict) -> Path:
    environment_name = manifest["execution_specs"]["default_env_var"]
    if explicit is not None:
        selected = explicit.expanduser()
    elif os.environ.get(environment_name):
        selected = Path(os.environ[environment_name]).expanduser()
    else:
        selected = (
            Path.home()
            / manifest["execution_specs"]["default_subpath_from_home"]
        )
    return Path(os.path.abspath(os.fspath(selected)))


def inspect_installation(manifest: dict, destination: Path) -> InstallationState:
    if not _path_exists(destination):
        return InstallationState(False, False, ())
    if destination.is_symlink():
        return InstallationState(
            True,
            False,
            (f"destination is a symbolic link, which is not accepted: {destination}",),
        )
    if not destination.is_dir():
        return InstallationState(
            True,
            False,
            (f"destination exists but is not a directory: {destination}",),
        )

    checks = [
        *env_doctor.check_execution_specs(manifest, destination),
        *env_doctor.check_ethereum_tests(manifest, destination),
    ]
    problems = tuple(
        f"{check.name}: {check.detail}"
        for check in checks
        if check.status != env_doctor.STATUS_OK
    )
    return InstallationState(True, not problems, problems)


def _run_git(
    args: list[str],
    *,
    cwd: Path | None = None,
    allow_file_protocol: bool = False,
) -> str:
    command = ["git"]
    if allow_file_protocol:
        # A command-scoped setting is needed by the synthetic file:// tests and
        # is not persisted in local or global Git configuration.
        command.extend(["-c", "protocol.file.allow=always"])
    command.extend(args)

    environment = os.environ.copy()
    environment["GIT_TERMINAL_PROMPT"] = "0"
    try:
        result = subprocess.run(
            command,
            cwd=None if cwd is None else str(cwd),
            capture_output=True,
            text=True,
            check=False,
            env=environment,
        )
    except OSError as error:
        raise BootstrapError(f"could not execute git: {error}") from error
    if result.returncode != 0:
        rendered = " ".join(command)
        detail = result.stderr.strip() or result.stdout.strip() or "no diagnostic"
        raise BootstrapError(
            f"Git command failed ({rendered}) in {cwd or Path.cwd()}: {detail}"
        )
    return result.stdout.strip()


def _clone_detached(repo_url: str, commit: str, destination: Path) -> None:
    _run_git(
        [
            "clone",
            "--no-checkout",
            "--no-recurse-submodules",
            "--origin",
            "origin",
            "--",
            repo_url,
            str(destination),
        ],
        allow_file_protocol=repo_url.startswith("file://"),
    )
    _run_git(["checkout", "--detach", commit], cwd=destination)


def _verify_legacy_gitlink(
    ethereum_tests_root: Path, relative_path: Path, expected_commit: str
) -> None:
    entry = _run_git(
        ["ls-tree", "HEAD", "--", relative_path.as_posix()],
        cwd=ethereum_tests_root,
    )
    expected = f"160000 commit {expected_commit}\t{relative_path.as_posix()}"
    if entry != expected:
        actual = entry or "no gitlink entry"
        raise BootstrapError(
            "the pinned ethereum/tests checkout does not record the required "
            f"{relative_path.as_posix()} gitlink at {expected_commit}; got {actual}"
        )


def _remove_owned_temporary(path: Path) -> None:
    """Best-effort cleanup, limited to the exact directory created by mkdtemp."""
    try:
        shutil.rmtree(path)
    except OSError as error:
        print(
            f"warning: could not remove incomplete temporary checkout {path}: {error}",
            file=sys.stderr,
        )


def install_fresh(manifest: dict, destination: Path) -> None:
    if _path_exists(destination):
        raise BootstrapError(
            f"destination appeared during bootstrap and was not touched: {destination}"
        )

    try:
        destination.parent.mkdir(parents=True, exist_ok=True)
    except OSError as error:
        raise BootstrapError(
            f"cannot create destination parent {destination.parent}: {error}"
        ) from error

    try:
        temporary = Path(
            tempfile.mkdtemp(
                prefix=f".{destination.name}.bootstrap-",
                dir=destination.parent,
            )
        )
    except OSError as error:
        raise BootstrapError(
            f"cannot create a temporary sibling of {destination}: {error}"
        ) from error

    keep_temporary = True
    try:
        execution_specs = manifest["execution_specs"]
        print(
            "Cloning execution-specs at "
            f"{execution_specs['commit']} into temporary destination..."
        )
        _clone_detached(
            execution_specs["repo_url"],
            execution_specs["commit"],
            temporary,
        )

        ethereum_tests = manifest["ethereum_tests"]
        ethereum_rel = _safe_relative_path(
            ethereum_tests["relative_path_from_execution_specs"],
            "ethereum_tests.relative_path_from_execution_specs",
        )
        ethereum_root = temporary / ethereum_rel
        ethereum_root.parent.mkdir(parents=True, exist_ok=True)
        print(
            "Cloning ethereum/tests at "
            f"{ethereum_tests['commit']} into its ignored nested destination..."
        )
        _clone_detached(
            ethereum_tests["repo_url"],
            ethereum_tests["commit"],
            ethereum_root,
        )

        legacy = manifest["legacy_tests_submodule"]
        legacy_rel = _safe_relative_path(
            legacy["relative_path_from_ethereum_tests"],
            "legacy_tests_submodule.relative_path_from_ethereum_tests",
        )
        _verify_legacy_gitlink(ethereum_root, legacy_rel, legacy["commit"])
        print(
            f"Initializing only {legacy_rel.as_posix()} at {legacy['commit']}..."
        )
        _run_git(
            ["submodule", "update", "--init", "--", legacy_rel.as_posix()],
            cwd=ethereum_root,
            allow_file_protocol=True,
        )

        installed = inspect_installation(manifest, temporary)
        if not installed.correct:
            raise BootstrapError(
                "temporary installation failed final verification:\n  - "
                + "\n  - ".join(installed.problems)
            )

        if _path_exists(destination):
            raise BootstrapError(
                "destination appeared during bootstrap; leaving it untouched: "
                f"{destination}"
            )
        try:
            temporary.rename(destination)
        except OSError as error:
            raise BootstrapError(
                f"could not atomically place verified checkout at {destination}: {error}"
            ) from error
        keep_temporary = False
    finally:
        if keep_temporary:
            _remove_owned_temporary(temporary)


def print_dry_run(manifest: dict, destination: Path) -> None:
    execution_specs = manifest["execution_specs"]
    ethereum_tests = manifest["ethereum_tests"]
    legacy = manifest["legacy_tests_submodule"]
    ethereum_rel = ethereum_tests["relative_path_from_execution_specs"]
    legacy_rel = legacy["relative_path_from_ethereum_tests"]

    print(f"DRY RUN — destination is absent: {destination}")
    if not destination.parent.exists():
        print(f"Would create destination parent: {destination.parent}")
    print(f"Would create a temporary sibling of: {destination}")
    print(
        f"Would clone {execution_specs['repo_url']} and detach at "
        f"{execution_specs['commit']}"
    )
    print(
        f"Would clone {ethereum_tests['repo_url']} into {ethereum_rel} and detach "
        f"at {ethereum_tests['commit']}"
    )
    print(
        f"Would initialize only {ethereum_rel}/{legacy_rel} at {legacy['commit']}"
    )
    print("Would verify all origins, revisions, tracked cleanliness, and fixture layout")
    print(f"Would atomically place the verified tree at: {destination}")
    print("No network or filesystem changes were made.")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
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
        help="destination root (default: $EELS_ROOT or ~/execution-specs)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="report network/filesystem actions without making changes",
    )
    return parser


def main(argv: list[str]) -> int:
    args = build_parser().parse_args(argv)
    try:
        manifest = env_doctor.load_manifest(args.manifest)
        validate_bootstrap_manifest(manifest)
    except (env_doctor.ManifestError, BootstrapError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    if shutil.which("git") is None:
        print("error: git is required but was not found on PATH", file=sys.stderr)
        return 1

    destination = destination_from_args(args.execution_specs, manifest)
    state = inspect_installation(manifest, destination)

    if state.correct:
        print(
            "NO-OP — the existing execution-specs, ethereum/tests, and "
            "LegacyTests checkouts already match the manifest."
        )
        print(f"Verified destination: {destination}")
        print("No network or filesystem changes were made.")
        return 0

    if state.exists:
        print(
            f"error: refusing existing destination because it is not a complete, "
            f"clean manifest-matching installation: {destination}",
            file=sys.stderr,
        )
        for problem in state.problems:
            print(f"  - {problem}", file=sys.stderr)
        print(
            "Recovery: inspect the destination, then manually move or remove it "
            "only if you are certain it is disposable; alternatively choose a "
            "different --execution-specs destination. This command will not "
            "repair or overwrite it.",
            file=sys.stderr,
        )
        return 1

    if args.dry_run:
        print_dry_run(manifest, destination)
        return 0

    try:
        install_fresh(manifest, destination)
    except BootstrapError as error:
        print(f"error: bootstrap failed safely: {error}", file=sys.stderr)
        print(
            "The final destination was not installed. Inspect any warning-named "
            "temporary sibling before removing it manually.",
            file=sys.stderr,
        )
        return 1

    print(f"OK — installed verified legacy fixture sources at {destination}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
