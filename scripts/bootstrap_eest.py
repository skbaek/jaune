#!/usr/bin/env python3
"""Safely bootstrap Jaune's EEST consensus-fixture release.

The command consumes the EEST fields of scripts/sources.json, obtains the
pinned execution-spec-tests archive (reusing an already-verified copy or
downloading it once), verifies its SHA-256 *before* extraction, extracts it
through a safe member-by-member validator, checks the expected layout and
release provenance, and places the fixture tree atomically at the install
root.

Safety invariants (mirroring scripts/bootstrap_legacy.py):

- an existing installation is accepted only when the cached archive verifies
  and the extracted tree matches the manifest layout and provenance;
- any other existing fixture tree is refused, never repaired, reset, deleted,
  or overwritten;
- the checksum is verified before a single byte is extracted;
- absolute, traversal, link, and special archive members are rejected;
- a partially downloaded archive or partially extracted tree can never
  masquerade as a complete installation.

Python-standard-library only. Network download is only attempted when no
verified archive is already present; deep tree/archive comparison lives in
scripts/env_doctor.py (--eest-deep).
"""
from __future__ import annotations

import argparse
import hashlib
import os
import shutil
import sys
import tarfile
import tempfile
import urllib.request
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

import env_doctor
from env_doctor import (
    UnsafeArchiveMember,
    classify_member,
    safe_member_relpath,
)

DEFAULT_MANIFEST = Path(__file__).resolve().parent / "sources.json"
_STREAM_CHUNK = 1024 * 1024


class EestBootstrapError(Exception):
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
        raise EestBootstrapError(f"manifest field {field} must be a nonempty string")
    pure = PurePosixPath(value)
    if pure.is_absolute() or any(part in ("", ".", "..") for part in pure.parts):
        raise EestBootstrapError(
            f"manifest field {field} must be a safe relative path, got {value!r}"
        )
    return Path(*pure.parts)


def _safe_filename(value: object, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise EestBootstrapError(f"manifest field {field} must be a nonempty string")
    if "/" in value or "\\" in value or value in (".", ".."):
        raise EestBootstrapError(
            f"manifest field {field} must be a bare filename, got {value!r}"
        )
    return value


def validate_eest_manifest(manifest: dict) -> None:
    """Validate the EEST lock fields that influence download/extraction."""
    if manifest.get("schema_version") != 1:
        raise EestBootstrapError(
            f"unsupported manifest schema_version {manifest.get('schema_version')!r}; "
            "expected 1"
        )
    spec = manifest["eest"]

    sha = spec.get("archive_sha256")
    if (
        not isinstance(sha, str)
        or len(sha) != 64
        or any(char not in "0123456789abcdefABCDEF" for char in sha)
    ):
        raise EestBootstrapError(
            "manifest field eest.archive_sha256 must be an exact 64-character "
            "hexadecimal digest"
        )

    url = spec.get("archive_url")
    if not isinstance(url, str) or not url.strip():
        raise EestBootstrapError("manifest field eest.archive_url must be a nonempty string")

    _safe_filename(spec.get("archive_filename"), "eest.archive_filename")
    _safe_relative_path(spec.get("fixtures_subpath"), "eest.fixtures_subpath")

    if spec.get("default_env_var") != "EEST_ROOT":
        raise EestBootstrapError(
            "manifest field eest.default_env_var must preserve the EEST_ROOT convention"
        )
    _safe_relative_path(
        spec.get("default_subpath_from_home"), "eest.default_subpath_from_home"
    )

    top = spec.get("expected_top_level_dirs")
    if not isinstance(top, list) or not top:
        raise EestBootstrapError(
            "manifest field eest.expected_top_level_dirs must be a nonempty list"
        )
    for entry in top:
        _safe_relative_path(entry, "eest.expected_top_level_dirs[]")


def eest_root_from_args(explicit: Path | None, manifest: dict) -> Path:
    spec = manifest["eest"]
    if explicit is not None:
        selected = explicit.expanduser()
    elif os.environ.get(spec["default_env_var"]):
        selected = Path(os.environ[spec["default_env_var"]]).expanduser()
    else:
        selected = Path.home() / spec["default_subpath_from_home"]
    return Path(os.path.abspath(os.fspath(selected)))


def archive_cache_from_args(
    explicit: Path | None, eest_root: Path, manifest: dict
) -> Path:
    if explicit is not None:
        selected = explicit.expanduser()
    else:
        selected = eest_root / manifest["eest"]["archive_filename"]
    return Path(os.path.abspath(os.fspath(selected)))


def _verify_archive_hash(archive_path: Path, expected_sha: str) -> str | None:
    """Return None when the archive matches, else a human-readable problem."""
    if not archive_path.is_file():
        return f"archive not found: {archive_path}"
    actual = env_doctor.sha256_file(archive_path)
    if actual.lower() != expected_sha.lower():
        return f"archive sha256 mismatch: expected {expected_sha}, got {actual}"
    return None


def _verify_fixtures_tree(manifest: dict, fixtures_root: Path) -> list[str]:
    """Fast structural + provenance verification of an extracted tree."""
    spec = manifest["eest"]
    if not fixtures_root.is_dir():
        return [f"extracted fixtures not found: {fixtures_root}"]

    problems: list[str] = []
    missing = [
        d for d in spec["expected_top_level_dirs"] if not (fixtures_root / d).is_dir()
    ]
    if missing:
        problems.append(f"missing expected subdirectories: {', '.join(missing)}")

    for check in env_doctor._check_eest_metadata(spec, fixtures_root):
        if check.status != env_doctor.STATUS_OK:
            problems.append(f"{check.name}: {check.detail}")
    for check in env_doctor._check_eest_bls_tier(spec, fixtures_root):
        if check.status != env_doctor.STATUS_OK:
            problems.append(f"{check.name}: {check.detail}")
    return problems


def inspect_installation(
    manifest: dict, eest_root: Path, archive_cache: Path
) -> InstallationState:
    spec = manifest["eest"]
    fixtures_root = eest_root / spec["fixtures_subpath"]

    archive_present = archive_cache.is_file()
    fixtures_present = fixtures_root.exists()

    if eest_root.is_symlink():
        return InstallationState(
            True,
            False,
            (f"install root is a symbolic link, which is not accepted: {eest_root}",),
        )
    if _path_exists(eest_root) and not eest_root.is_dir():
        return InstallationState(
            True,
            False,
            (f"install root exists but is not a directory: {eest_root}",),
        )

    problems: list[str] = []
    archive_problem = _verify_archive_hash(archive_cache, spec["archive_sha256"])
    if archive_problem is not None:
        problems.append(archive_problem)
    problems.extend(_verify_fixtures_tree(manifest, fixtures_root))

    exists = archive_present or fixtures_present
    return InstallationState(exists, not problems, tuple(problems))


def _download_archive(url: str, part_path: Path, expected_sha: str) -> None:
    """Stream a download to a .part file, verifying the checksum before it is
    promoted. Removes the partial file on any failure."""
    digest = hashlib.sha256()
    try:
        request = urllib.request.Request(url, headers={"User-Agent": "jaune-bootstrap"})
        with urllib.request.urlopen(request) as response, part_path.open("wb") as out:
            while True:
                chunk = response.read(_STREAM_CHUNK)
                if not chunk:
                    break
                out.write(chunk)
                digest.update(chunk)
    except OSError as error:
        _remove_quietly(part_path)
        raise EestBootstrapError(f"could not download archive from {url}: {error}") from error

    actual = digest.hexdigest()
    if actual.lower() != expected_sha.lower():
        _remove_quietly(part_path)
        raise EestBootstrapError(
            f"downloaded archive from {url} failed checksum verification: "
            f"expected {expected_sha}, got {actual}. The partial download was removed."
        )


def _obtain_archive(manifest: dict, url: str, archive_cache: Path) -> str:
    """Ensure a checksum-verified archive exists at archive_cache. Returns a
    one-line description of what happened."""
    expected_sha = manifest["eest"]["archive_sha256"]

    if archive_cache.is_file():
        problem = _verify_archive_hash(archive_cache, expected_sha)
        if problem is not None:
            raise EestBootstrapError(
                f"refusing existing cached archive because it does not verify: {problem}. "
                "Remove it manually if you are certain it is disposable, or choose a "
                "different --archive-cache path; this command will not overwrite it."
            )
        return f"reused verified cached archive (offline): {archive_cache}"

    if _path_exists(archive_cache):
        raise EestBootstrapError(
            f"archive cache path exists but is not a regular file: {archive_cache}"
        )

    try:
        archive_cache.parent.mkdir(parents=True, exist_ok=True)
    except OSError as error:
        raise EestBootstrapError(
            f"cannot create archive cache directory {archive_cache.parent}: {error}"
        ) from error

    part_path = archive_cache.with_name(archive_cache.name + ".part")
    if _path_exists(part_path):
        raise EestBootstrapError(
            f"a previous partial download is present: {part_path}. Inspect and remove "
            "it manually before retrying; this command will not overwrite it."
        )
    _download_archive(url, part_path, expected_sha)
    try:
        os.replace(part_path, archive_cache)
    except OSError as error:
        _remove_quietly(part_path)
        raise EestBootstrapError(
            f"could not place verified archive at {archive_cache}: {error}"
        ) from error
    return f"downloaded and verified archive: {archive_cache}"


def _extract_archive(manifest: dict, archive_path: Path, staging_dir: Path) -> int:
    """Extract the archive's fixtures/ subtree into staging_dir (which becomes
    the fixtures tree), rejecting any unsafe member. Returns the file count."""
    prefix = manifest["eest"]["fixtures_subpath"].rstrip("/") + "/"
    prefix_dir = prefix.rstrip("/")
    file_count = 0

    with tarfile.open(archive_path, mode="r|gz") as archive:
        for member in archive:
            try:
                kind = classify_member(member)
                relative = safe_member_relpath(member.name)
            except UnsafeArchiveMember as error:
                raise EestBootstrapError(f"refusing unsafe archive: {error}") from error

            posix = relative.as_posix()
            if kind == "dir":
                if posix == prefix_dir:
                    continue
                if not posix.startswith(prefix):
                    raise EestBootstrapError(
                        f"refusing archive: directory member escapes {prefix!r}: {posix}"
                    )
                sub = posix[len(prefix):]
                if sub:
                    (staging_dir / Path(*PurePosixPath(sub).parts)).mkdir(
                        parents=True, exist_ok=True
                    )
                continue

            if not posix.startswith(prefix):
                raise EestBootstrapError(
                    f"refusing archive: member escapes {prefix!r}: {posix}"
                )
            sub = posix[len(prefix):]
            if not sub:
                raise EestBootstrapError(
                    f"refusing archive: file member has no path under {prefix!r}: {posix}"
                )
            target = staging_dir / Path(*PurePosixPath(sub).parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            source = archive.extractfile(member)
            if source is None:
                raise EestBootstrapError(
                    f"refusing archive: unreadable file member: {posix}"
                )
            with source, target.open("wb") as out:
                shutil.copyfileobj(source, out, length=_STREAM_CHUNK)
            file_count += 1

    if file_count == 0:
        raise EestBootstrapError(
            "refusing archive: it contained no regular fixture files under "
            f"{prefix!r}"
        )
    return file_count


def _remove_quietly(path: Path) -> None:
    try:
        if path.is_dir() and not path.is_symlink():
            shutil.rmtree(path)
        elif _path_exists(path):
            path.unlink()
    except OSError as error:
        print(
            f"warning: could not remove temporary path {path}: {error}",
            file=sys.stderr,
        )


def install_fresh(manifest: dict, eest_root: Path, archive_cache: Path) -> None:
    spec = manifest["eest"]
    fixtures_root = eest_root / spec["fixtures_subpath"]
    if _path_exists(fixtures_root):
        raise EestBootstrapError(
            f"fixtures tree appeared during bootstrap; leaving it untouched: {fixtures_root}"
        )

    try:
        eest_root.mkdir(parents=True, exist_ok=True)
    except OSError as error:
        raise EestBootstrapError(
            f"cannot create install root {eest_root}: {error}"
        ) from error

    print(_obtain_archive(manifest, spec["archive_url"], archive_cache))

    try:
        staging = Path(
            tempfile.mkdtemp(prefix=f".{fixtures_root.name}.bootstrap-", dir=eest_root)
        )
    except OSError as error:
        raise EestBootstrapError(
            f"cannot create a temporary staging directory in {eest_root}: {error}"
        ) from error

    keep_staging = True
    try:
        print("Extracting verified archive into a temporary staging directory...")
        count = _extract_archive(manifest, archive_cache, staging)

        problems = _verify_fixtures_tree(manifest, staging)
        if problems:
            raise EestBootstrapError(
                "extracted tree failed layout/provenance verification:\n  - "
                + "\n  - ".join(problems)
            )

        if _path_exists(fixtures_root):
            raise EestBootstrapError(
                "fixtures tree appeared during bootstrap; leaving it untouched: "
                f"{fixtures_root}"
            )
        try:
            os.rename(staging, fixtures_root)
        except OSError as error:
            raise EestBootstrapError(
                f"could not atomically place verified fixtures at {fixtures_root}: {error}"
            ) from error
        keep_staging = False
        print(f"Placed {count} verified fixture files at {fixtures_root}")
    finally:
        if keep_staging:
            _remove_quietly(staging)


def print_dry_run(
    manifest: dict, eest_root: Path, archive_cache: Path, state: InstallationState
) -> None:
    spec = manifest["eest"]
    fixtures_root = eest_root / spec["fixtures_subpath"]
    print(f"DRY RUN — planning EEST install at: {eest_root}")
    if not _path_exists(eest_root):
        print(f"Would create install root: {eest_root}")

    if archive_cache.is_file() and _verify_archive_hash(
        archive_cache, spec["archive_sha256"]
    ) is None:
        print(f"Would reuse the already-verified cached archive (offline): {archive_cache}")
    else:
        print(
            f"Would download {spec['archive_url']} to {archive_cache}.part, verify "
            f"sha256 {spec['archive_sha256']}, then place it at {archive_cache}"
        )
    print("Would extract through the safe member validator into a temporary staging dir")
    print(
        "Would verify expected top-level dirs, BLS tier dirs, and release provenance"
    )
    print(f"Would atomically place the verified fixture tree at: {fixtures_root}")
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
        "--eest-root",
        type=Path,
        default=None,
        help="EEST install root containing the archive and extracted fixtures/ "
        "(default: $EEST_ROOT or ~/eest-fixtures)",
    )
    parser.add_argument(
        "--archive-cache",
        type=Path,
        default=None,
        help="where the release archive is read from / stored "
        "(default: <eest-root>/<archive_filename>)",
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
        validate_eest_manifest(manifest)
    except (env_doctor.ManifestError, EestBootstrapError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    eest_root = eest_root_from_args(args.eest_root, manifest)
    archive_cache = archive_cache_from_args(args.archive_cache, eest_root, manifest)

    state = inspect_installation(manifest, eest_root, archive_cache)

    if state.correct:
        print(
            "NO-OP — the cached archive verifies and the extracted fixture tree "
            "already matches the manifest layout and provenance."
        )
        print(f"Verified install root: {eest_root}")
        print("No network or filesystem changes were made.")
        return 0

    fixtures_root = eest_root / manifest["eest"]["fixtures_subpath"]
    if fixtures_root.exists():
        print(
            "error: refusing existing fixture tree because it is not a complete, "
            f"verified manifest-matching installation: {fixtures_root}",
            file=sys.stderr,
        )
        for problem in state.problems:
            print(f"  - {problem}", file=sys.stderr)
        print(
            "Recovery: inspect the tree, then manually move or remove it only if you "
            "are certain it is disposable; alternatively choose a different "
            "--eest-root. This command will not repair, delete, or overwrite it.",
            file=sys.stderr,
        )
        return 1

    if args.dry_run:
        print_dry_run(manifest, eest_root, archive_cache, state)
        return 0

    try:
        install_fresh(manifest, eest_root, archive_cache)
    except EestBootstrapError as error:
        print(f"error: bootstrap failed safely: {error}", file=sys.stderr)
        print(
            "The fixture tree was not installed. Inspect any '.fixtures.bootstrap-*' "
            "staging sibling or '*.part' download before removing it manually.",
            file=sys.stderr,
        )
        return 1

    print(f"OK — installed verified EEST fixtures at {eest_root}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
