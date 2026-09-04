#!/usr/bin/env python3
"""Read-only diagnostic for Jaune's external-source environment.

Checks the manifest in scripts/sources.json against the local filesystem and
Git state: execution-specs, the nested ethereum/tests + LegacyTests checkout,
the frozen EEST and current-mainnet release archives/extractions, and the
Python oracle venv when present.
The EEST checks are fast by default (archive hash, expected layout, --bls tier
directories, and the release provenance in fixtures/.meta/fixtures.ini);
--eest-deep additionally streams the archive and compares it file-by-file
against the extracted tree to detect changed, missing, or extra fixtures.

This script never edits, fetches, clones, initializes, activates, or repairs
anything. It only reads. scripts/bootstrap_legacy.py can create a missing
Git-backed legacy-fixture installation and scripts/bootstrap_eest.py can create
a missing EEST installation. scripts/bootstrap_oracle.py can create the exact
Python 3.11.9 hash-locked oracle venv. All refuse to repair an existing
non-matching destination.

Python-standard-library only.

Exit codes:
  0  every checked component is present and matches the manifest
  1  at least one component is missing, dirty, or does not match the manifest
  2  usage error or a malformed manifest
"""
from __future__ import annotations

import argparse
import configparser
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
from dataclasses import dataclass, asdict
from pathlib import Path, PurePosixPath
from typing import Optional

DEFAULT_MANIFEST = Path(__file__).resolve().parent / "sources.json"

STATUS_OK = "ok"
STATUS_MISSING = "missing"
STATUS_FAIL = "fail"

# Paths under the execution-specs ``src/`` tree that Jaune's generators read or
# import.  bootstrap_oracle.py and generator_common.py both refuse a checkout
# missing any of them, and the synthetic checkouts in scripts/tests are built
# from this same tuple, so a new generator dependency is recorded in one place
# instead of drifting between the checks and the fixtures.
GENERATOR_SOURCE_LAYOUT = (
    "ethereum/crypto/hash.py",
    "ethereum/crypto/kzg.py",
    "ethereum/prague/vm/instructions/arithmetic.py",
    "ethereum/prague/vm/instructions/comparison.py",
    "ethereum/prague/vm/instructions/bitwise.py",
    "ethereum/prague/vm/instructions/keccak.py",
    "ethereum/prague/vm/gas.py",
)


@dataclass
class Check:
    name: str
    status: str
    detail: str


def load_manifest(path: Path) -> dict:
    try:
        text = path.read_text()
    except OSError as error:
        raise ManifestError(f"cannot read manifest {path}: {error}") from error
    try:
        data = json.loads(text)
    except json.JSONDecodeError as error:
        raise ManifestError(f"manifest {path} is not valid JSON: {error}") from error

    if not isinstance(data, dict):
        raise ManifestError(f"manifest {path} root must be a JSON object")
    if data.get("schema_version") != 1:
        raise ManifestError(
            f"manifest {path} has unsupported schema_version "
            f"{data.get('schema_version')!r}; expected 1"
        )

    required_top = (
        "execution_specs",
        "ethereum_tests",
        "legacy_tests_submodule",
        "eest",
        "python_oracle",
    )
    for key in required_top:
        if key not in data:
            raise ManifestError(f"manifest {path} is missing required key {key!r}")

    required_fields = {
        "execution_specs": ("repo_url", "commit"),
        "ethereum_tests": ("repo_url", "commit", "relative_path_from_execution_specs"),
        "legacy_tests_submodule": ("commit", "relative_path_from_ethereum_tests"),
        "eest": (
            "release_tag",
            "archive_url",
            "archive_filename",
            "archive_sha256",
            "fixtures_subpath",
            "expected_top_level_dirs",
        ),
        "python_oracle": (
            "intended_version",
            "patch_policy",
            "package_manager",
            "requirements_lock",
            "requirements_lock_sha256",
            "known_packages",
            "full_lock_status",
        ),
    }
    for section, fields in required_fields.items():
        if not isinstance(data[section], dict):
            raise ManifestError(
                f"manifest {path} section {section!r} must be a JSON object"
            )
        for field in fields:
            if field not in data[section]:
                raise ManifestError(
                    f"manifest {path} section {section!r} is missing field {field!r}"
                )
    return data


class ManifestError(Exception):
    pass


_LOCKED_REQUIREMENT = re.compile(
    r"^([A-Za-z0-9][A-Za-z0-9_.-]*)==([^;\\\s]+)\s*\\?\s*$"
)


def normalize_package_name(name: str) -> str:
    return re.sub(r"[-_.]+", "-", name).lower()


def oracle_lock_path(manifest: dict, manifest_path: Path) -> Path:
    value = manifest["python_oracle"]["requirements_lock"]
    if not isinstance(value, str) or not value:
        raise ManifestError(
            "manifest field python_oracle.requirements_lock must be a nonempty "
            "path relative to the manifest"
        )
    pure = PurePosixPath(value)
    if pure.is_absolute() or any(part in ("", ".", "..") for part in pure.parts):
        raise ManifestError(
            "manifest field python_oracle.requirements_lock must be a safe "
            f"relative path, got {value!r}"
        )
    return manifest_path.resolve().parent.joinpath(*pure.parts)


def parse_requirements_lock(path: Path) -> dict[str, str]:
    """Parse uv's exact, hash-locked requirements output."""
    try:
        lines = path.read_text().splitlines()
    except OSError as error:
        raise ManifestError(f"cannot read Python requirements lock {path}: {error}") from error

    packages: dict[str, str] = {}
    current_name: str | None = None
    current_has_hash = False

    def finish_current() -> None:
        if current_name is not None and not current_has_hash:
            raise ManifestError(
                f"Python requirements lock entry {current_name!r} has no SHA-256 hash"
            )

    for line in lines:
        match = _LOCKED_REQUIREMENT.match(line)
        if match:
            finish_current()
            raw_name, package_version = match.groups()
            package_name = normalize_package_name(raw_name)
            if package_name in packages:
                raise ManifestError(
                    f"Python requirements lock contains duplicate package {package_name!r}"
                )
            packages[package_name] = package_version
            current_name = package_name
            current_has_hash = False
        elif current_name is not None and "--hash=sha256:" in line:
            current_has_hash = True

    finish_current()
    if not packages:
        raise ManifestError(f"Python requirements lock {path} contains no exact packages")
    return packages


def run_git(args: list[str], cwd: Path) -> Optional[str]:
    """Run a read-only git command; None on any failure (never raises)."""
    environment = os.environ.copy()
    environment["GIT_OPTIONAL_LOCKS"] = "0"
    try:
        result = subprocess.run(
            ["git", *args],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            check=False,
            env=environment,
        )
    except OSError:
        return None
    if result.returncode != 0:
        return None
    return result.stdout.strip()


def check_git_checkout(
    label: str, path: Path, expected_url: Optional[str], expected_commit: str
) -> list[Check]:
    checks: list[Check] = []
    if not path.is_dir():
        checks.append(Check(f"{label}: directory", STATUS_MISSING, f"not found: {path}"))
        return checks
    if not (path / ".git").exists():
        checks.append(
            Check(f"{label}: git repo", STATUS_FAIL, f"{path} is not a Git checkout")
        )
        return checks

    head = run_git(["rev-parse", "HEAD"], path)
    if head is None:
        checks.append(Check(f"{label}: HEAD", STATUS_FAIL, f"could not read HEAD in {path}"))
    elif head != expected_commit:
        checks.append(
            Check(
                f"{label}: HEAD",
                STATUS_FAIL,
                f"expected {expected_commit}, got {head}",
            )
        )
    else:
        checks.append(Check(f"{label}: HEAD", STATUS_OK, head))

    if expected_url is not None:
        origin = run_git(["remote", "get-url", "origin"], path)
        if origin is None:
            checks.append(
                Check(f"{label}: origin", STATUS_FAIL, "no 'origin' remote configured")
            )
        elif _normalize_git_url(origin) != _normalize_git_url(expected_url):
            checks.append(
                Check(
                    f"{label}: origin",
                    STATUS_FAIL,
                    f"expected {expected_url}, got {origin}",
                )
            )
        else:
            checks.append(Check(f"{label}: origin", STATUS_OK, origin))

    status = run_git(["status", "--porcelain"], path)
    if status is None:
        checks.append(Check(f"{label}: tracked dirtiness", STATUS_FAIL, "git status failed"))
    else:
        # "??" lines are untracked files (e.g. an unrelated stray
        # .python-version); they are not modifications to tracked source and
        # must not be reported as dirty. Every other porcelain line reflects a
        # change to a tracked file (modified/added/deleted/renamed/staged).
        dirty_lines = [
            line for line in status.splitlines() if line and not line.startswith("??")
        ]
        untracked_count = sum(1 for line in status.splitlines() if line.startswith("??"))
        if dirty_lines:
            checks.append(
                Check(
                    f"{label}: tracked dirtiness",
                    STATUS_FAIL,
                    f"{len(dirty_lines)} tracked change(s): "
                    + "; ".join(dirty_lines[:5]),
                )
            )
        else:
            detail = "clean"
            if untracked_count:
                detail += f" ({untracked_count} untracked file(s) ignored by this check)"
            checks.append(Check(f"{label}: tracked dirtiness", STATUS_OK, detail))

    return checks


def _normalize_git_url(url: str) -> str:
    url = url.strip()
    if url.endswith("/"):
        url = url[:-1]
    if url.endswith(".git"):
        url = url[: -len(".git")]
    return url.lower()


def check_execution_specs(manifest: dict, root: Path) -> list[Check]:
    spec = manifest["execution_specs"]
    return check_git_checkout("execution-specs", root, spec["repo_url"], spec["commit"])


def check_ethereum_tests(manifest: dict, execution_specs_root: Path) -> list[Check]:
    spec = manifest["ethereum_tests"]
    path = execution_specs_root / spec["relative_path_from_execution_specs"]
    checks = check_git_checkout("ethereum/tests", path, spec["repo_url"], spec["commit"])

    legacy = manifest["legacy_tests_submodule"]
    legacy_path = path / legacy["relative_path_from_ethereum_tests"]
    gitlink = run_git(
        ["ls-tree", "HEAD", "--", legacy["relative_path_from_ethereum_tests"]],
        path,
    )
    expected_gitlink = (
        f"160000 commit {legacy['commit']}\t"
        f"{legacy['relative_path_from_ethereum_tests']}"
    )
    if gitlink is None:
        checks.append(
            Check(
                "ethereum/tests: LegacyTests gitlink",
                STATUS_FAIL,
                f"could not read gitlink in {path}",
            )
        )
    elif gitlink != expected_gitlink:
        checks.append(
            Check(
                "ethereum/tests: LegacyTests gitlink",
                STATUS_FAIL,
                f"expected {expected_gitlink}, got {gitlink or 'no entry'}",
            )
        )
    else:
        checks.append(
            Check("ethereum/tests: LegacyTests gitlink", STATUS_OK, legacy["commit"])
        )

    # The submodule has no independent 'origin' expectation in the manifest
    # (only its pinned commit); its remote is whatever ethereum/tests'
    # .gitmodules declares.
    checks.extend(
        check_git_checkout(
            f"ethereum/tests/{legacy['relative_path_from_ethereum_tests']}",
            legacy_path,
            None,
            legacy["commit"],
        )
    )

    blockchain_tests = path / "BlockchainTests"
    if blockchain_tests.is_dir():
        checks.append(
            Check(
                "legacy fixtures: BlockchainTests",
                STATUS_OK,
                str(blockchain_tests),
            )
        )
    else:
        checks.append(
            Check(
                "legacy fixtures: BlockchainTests",
                STATUS_MISSING,
                f"not found: {blockchain_tests}",
            )
        )
    return checks


_STREAM_CHUNK = 1024 * 1024


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(_STREAM_CHUNK), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_stream(handle) -> str:
    """SHA-256 of a binary file-like object, read in bounded-size chunks."""
    digest = hashlib.sha256()
    for chunk in iter(lambda: handle.read(_STREAM_CHUNK), b""):
        digest.update(chunk)
    return digest.hexdigest()


class UnsafeArchiveMember(Exception):
    """An archive member whose name or type is not safe to extract or trust."""


def safe_member_relpath(name: str) -> PurePosixPath:
    """Return a normalized, guaranteed-safe relative POSIX path for an archive
    member name, or raise UnsafeArchiveMember.

    Rejects empty names, Windows drive/UNC forms, absolute paths, and any '.'
    or '..' component. The result never escapes the extraction root.
    """
    if not name:
        raise UnsafeArchiveMember("archive member has an empty name")
    # Reject Windows drive letters and backslash separators outright rather
    # than trying to normalize them; the fixture archive is POSIX-only.
    if "\\" in name or (len(name) >= 2 and name[1] == ":"):
        raise UnsafeArchiveMember(f"archive member is not a POSIX path: {name!r}")
    pure = PurePosixPath(name)
    if pure.is_absolute():
        raise UnsafeArchiveMember(f"archive member has an absolute path: {name!r}")
    parts = pure.parts
    if not parts or any(part in ("", ".", "..") for part in parts):
        raise UnsafeArchiveMember(
            f"archive member has an unsafe path component: {name!r}"
        )
    return PurePosixPath(*parts)


def classify_member(member: tarfile.TarInfo) -> str:
    """Return 'file' or 'dir' for a safe member, else raise UnsafeArchiveMember.

    Regular files and directories are the only member types the fixture
    archive is expected to contain. Symlinks, hardlinks, character/block
    devices, FIFOs, and any other special members are refused so that a
    tampered archive cannot write or link outside the extraction root.
    """
    if member.isreg():
        return "file"
    if member.isdir():
        return "dir"
    if member.issym() or member.islnk():
        raise UnsafeArchiveMember(
            f"archive member is a link, which is not accepted: {member.name!r}"
        )
    raise UnsafeArchiveMember(
        f"archive member has an unsupported special type: {member.name!r}"
    )


def check_eest(manifest: dict, eest_root: Path) -> list[Check]:
    spec = manifest["eest"]
    checks: list[Check] = []

    if not eest_root.is_dir():
        checks.append(
            Check("eest: root directory", STATUS_MISSING, f"not found: {eest_root}")
        )
        return checks
    checks.append(Check("eest: root directory", STATUS_OK, str(eest_root)))

    archive_path = eest_root / spec["archive_filename"]
    if not archive_path.is_file():
        checks.append(
            Check("eest: archive", STATUS_MISSING, f"not found: {archive_path}")
        )
    else:
        actual_hash = sha256_file(archive_path)
        if actual_hash != spec["archive_sha256"]:
            checks.append(
                Check(
                    "eest: archive sha256",
                    STATUS_FAIL,
                    f"expected {spec['archive_sha256']}, got {actual_hash}",
                )
            )
        else:
            checks.append(Check("eest: archive sha256", STATUS_OK, actual_hash))

    fixtures_root = eest_root / spec["fixtures_subpath"]
    if not fixtures_root.is_dir():
        checks.append(
            Check(
                "eest: extracted fixtures",
                STATUS_MISSING,
                f"not found: {fixtures_root}",
            )
        )
        return checks

    missing_dirs = [
        d for d in spec["expected_top_level_dirs"] if not (fixtures_root / d).is_dir()
    ]
    if missing_dirs:
        checks.append(
            Check(
                "eest: extracted fixtures",
                STATUS_FAIL,
                f"missing expected subdirectories: {', '.join(missing_dirs)}",
            )
        )
    else:
        checks.append(
            Check(
                "eest: extracted fixtures",
                STATUS_OK,
                f"{len(spec['expected_top_level_dirs'])} expected top-level dirs present",
            )
        )

    checks.extend(_check_eest_metadata(spec, fixtures_root))
    checks.extend(_check_eest_bls_tier(spec, fixtures_root))
    return checks


def _check_eest_metadata(spec: dict, fixtures_root: Path) -> list[Check]:
    """Confirm the extracted tree carries the pinned release provenance from
    its own .meta/fixtures.ini. Skipped when the manifest omits the fields."""
    subpath = spec.get("metadata_file_subpath")
    expected = spec.get("metadata_expected")
    if not subpath or not isinstance(expected, dict):
        return []

    try:
        relative = safe_member_relpath(subpath)
    except UnsafeArchiveMember as error:
        return [Check("eest: fixture metadata", STATUS_FAIL, str(error))]
    metadata_path = fixtures_root / Path(*relative.parts)
    if not metadata_path.is_file():
        return [
            Check(
                "eest: fixture metadata",
                STATUS_MISSING,
                f"not found: {metadata_path}",
            )
        ]

    parser = configparser.ConfigParser(interpolation=None)
    try:
        parser.read_string(metadata_path.read_text(), source=str(metadata_path))
    except (OSError, configparser.Error) as error:
        return [
            Check(
                "eest: fixture metadata",
                STATUS_FAIL,
                f"could not parse {metadata_path}: {error}",
            )
        ]

    mismatches = []
    for key, want in expected.items():
        got = parser.get("fixtures", key, fallback=None)
        if got != want:
            mismatches.append(f"{key}: expected {want!r}, got {got!r}")
    if mismatches:
        return [
            Check("eest: fixture metadata", STATUS_FAIL, "; ".join(mismatches))
        ]
    return [
        Check(
            "eest: fixture metadata",
            STATUS_OK,
            ", ".join(f"{key}={want}" for key, want in expected.items()),
        )
    ]


def _check_eest_bls_tier(spec: dict, fixtures_root: Path) -> list[Check]:
    """Confirm the exact leaf directories consumed by scripts/bls-tests.txt via
    scripts/check-legacy.sh --bls exist. Skipped when the manifest omits the field."""
    subpaths = spec.get("bls_tier_subpaths")
    if not subpaths:
        return []
    missing = []
    for sub in subpaths:
        try:
            relative = safe_member_relpath(sub)
        except UnsafeArchiveMember as error:
            return [Check("eest: bls tier fixtures", STATUS_FAIL, str(error))]
        if not (fixtures_root / Path(*relative.parts)).is_dir():
            missing.append(sub)
    if missing:
        return [
            Check(
                "eest: bls tier fixtures",
                STATUS_FAIL,
                f"missing BLS tier directories: {', '.join(missing)}",
            )
        ]
    return [
        Check(
            "eest: bls tier fixtures",
            STATUS_OK,
            f"{len(subpaths)} BLS tier director(ies) present",
        )
    ]


def check_release_index_metadata(
    spec: dict, fixtures_root: Path, label: str = "current-mainnet"
) -> list[Check]:
    """Verify the release index fields emitted by the current fixture publisher.

    `label` names the lane in the check's own name, so a doctor run covering
    two lanes reports two distinguishable rows rather than the same row twice.
    """
    name = f"{label}: fixture metadata"
    subpath = spec.get("metadata_json_file_subpath")
    expected = spec.get("metadata_json_expected")
    if not subpath or not isinstance(expected, dict):
        return []
    try:
        relative = safe_member_relpath(subpath)
    except UnsafeArchiveMember as error:
        return [Check(name, STATUS_FAIL, str(error))]
    path = fixtures_root / Path(*relative.parts)
    if not path.is_file():
        return [Check(name, STATUS_MISSING, f"not found: {path}")]
    try:
        actual = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        return [Check(name, STATUS_FAIL, f"could not parse {path}: {error}")]
    if not isinstance(actual, dict):
        return [Check(name, STATUS_FAIL, "release index is not a JSON object")]
    mismatches = [
        f"{key}: expected {want!r}, got {actual.get(key)!r}"
        for key, want in expected.items()
        if actual.get(key) != want
    ]
    if mismatches:
        return [Check(name, STATUS_FAIL, "; ".join(mismatches))]
    return [
        Check(
            name,
            STATUS_OK,
            ", ".join(f"{key}={value}" for key, value in expected.items()),
        )
    ]


# The pre-rename spelling, kept for any caller that still asks for it by name.
check_current_mainnet_metadata = check_release_index_metadata


def deep_compare_eest(manifest: dict, eest_root: Path) -> list[Check]:
    """Read-only deep verification: compare the extracted fixture tree against
    the verified release archive strongly enough to detect changed, missing,
    and extra files.

    The archive is streamed once (bounded memory); each regular member's
    content hash is compared with the on-disk file, and the extracted tree is
    then walked to find files absent from the archive. Nothing is modified.
    """
    spec = manifest["eest"]
    checks: list[Check] = []

    archive_path = eest_root / spec["archive_filename"]
    fixtures_subpath = spec["fixtures_subpath"]
    fixtures_root = eest_root / fixtures_subpath

    if not archive_path.is_file():
        return [
            Check(
                "eest deep: archive",
                STATUS_MISSING,
                f"cannot deep-verify without the release archive: {archive_path}",
            )
        ]
    if not fixtures_root.is_dir():
        return [
            Check(
                "eest deep: extracted fixtures",
                STATUS_MISSING,
                f"cannot deep-verify without the extracted tree: {fixtures_root}",
            )
        ]

    # Deep comparison is only meaningful against the pinned archive, so confirm
    # its checksum first rather than trusting whatever bytes are on disk.
    actual_hash = sha256_file(archive_path)
    if actual_hash != spec["archive_sha256"]:
        return [
            Check(
                "eest deep: archive sha256",
                STATUS_FAIL,
                f"expected {spec['archive_sha256']}, got {actual_hash}; "
                "refusing to deep-verify against an unverified archive",
            )
        ]

    prefix = fixtures_subpath.rstrip("/") + "/"
    archive_files: set[str] = set()
    changed: list[str] = []
    missing: list[str] = []
    unsafe: list[str] = []
    member_count = 0

    try:
        with tarfile.open(archive_path, mode="r|gz") as archive:
            for member in archive:
                try:
                    kind = classify_member(member)
                    relative = safe_member_relpath(member.name)
                except UnsafeArchiveMember as error:
                    unsafe.append(str(error))
                    continue
                if kind == "dir":
                    continue
                member_count += 1
                posix = relative.as_posix()
                if not posix.startswith(prefix):
                    unsafe.append(
                        f"archive member escapes the {prefix!r} prefix: {posix}"
                    )
                    continue
                archive_files.add(posix)
                on_disk = eest_root / Path(*relative.parts)
                if not on_disk.is_file():
                    missing.append(posix)
                    continue
                source = archive.extractfile(member)
                expected_digest = (
                    sha256_stream(source) if source is not None else None
                )
                try:
                    with on_disk.open("rb") as handle:
                        actual_digest = sha256_stream(handle)
                except OSError as error:
                    changed.append(f"{posix} (unreadable: {error})")
                    continue
                if expected_digest != actual_digest:
                    changed.append(posix)
    except (tarfile.TarError, OSError) as error:
        return [
            Check(
                "eest deep: archive read",
                STATUS_FAIL,
                f"could not stream {archive_path}: {error}",
            )
        ]

    extra: list[str] = []
    for path in fixtures_root.rglob("*"):
        if path.is_dir():
            continue
        try:
            relative_posix = path.relative_to(eest_root).as_posix()
        except ValueError:
            continue
        if relative_posix not in archive_files:
            extra.append(relative_posix)

    if unsafe:
        checks.append(
            Check(
                "eest deep: archive safety",
                STATUS_FAIL,
                f"{len(unsafe)} unsafe/misplaced member(s): "
                + "; ".join(unsafe[:5]),
            )
        )
    else:
        checks.append(
            Check(
                "eest deep: archive safety",
                STATUS_OK,
                f"{member_count} regular file member(s), all safe",
            )
        )

    disk_count = member_count - len(missing) + len(extra)
    summary = (
        f"{member_count} archive files; {len(missing)} missing, "
        f"{len(changed)} changed, {len(extra)} extra "
        f"({disk_count} files on disk)"
    )
    if missing or changed or extra:
        detail_bits = []
        if missing:
            detail_bits.append(f"missing: {', '.join(missing[:5])}")
        if changed:
            detail_bits.append(f"changed: {', '.join(changed[:5])}")
        if extra:
            detail_bits.append(f"extra: {', '.join(extra[:5])}")
        checks.append(
            Check(
                "eest deep: tree vs archive",
                STATUS_FAIL,
                summary + " — " + "; ".join(detail_bits),
            )
        )
    else:
        checks.append(Check("eest deep: tree vs archive", STATUS_OK, summary))

    return checks


def _renamed_checks(checks: list[Check], old: str, new: str) -> list[Check]:
    """Reuse the release-archive verifier while keeping doctor output precise."""
    return [Check(check.name.replace(old, new), check.status, check.detail) for check in checks]


def check_release_lane(manifest: dict, root: Path, key: str, label: str) -> list[Check]:
    """Check one separately installed fixture-release lane.

    Both lanes carry the same fields under their own manifest key, so this is
    the mainnet check with the key and the reported label supplied rather than
    assumed. Nothing here knows which fork a lane's fixtures target: a lane is
    installed and verified the same way whether or not this build can run what
    it holds, and which suites are runnable is the manifest generator's
    question, not the doctor's.
    """
    spec = manifest[key]
    checks = check_eest({"eest": spec}, root)
    checks = _renamed_checks(checks, "eest", label)
    fixtures_root = root / spec["fixtures_subpath"]
    if fixtures_root.is_dir():
        checks.extend(check_release_index_metadata(spec, fixtures_root, label))
    return checks


def deep_compare_release_lane(
    manifest: dict, root: Path, key: str, label: str
) -> list[Check]:
    """Deep-check one lane's tree against its pinned release asset."""
    checks = deep_compare_eest({"eest": manifest[key]}, root)
    return _renamed_checks(checks, "eest", label)


def check_current_mainnet(manifest: dict, mainnet_root: Path) -> list[Check]:
    """Check the separately installed canonical current-mainnet fixture lane."""
    return check_release_lane(manifest, mainnet_root, "current_mainnet", "current-mainnet")


def deep_compare_current_mainnet(manifest: dict, mainnet_root: Path) -> list[Check]:
    """Deep-check the current-mainnet tree against its pinned release asset."""
    return deep_compare_release_lane(
        manifest, mainnet_root, "current_mainnet", "current-mainnet"
    )


def check_amsterdam(manifest: dict, amsterdam_root: Path) -> list[Check]:
    """Check the separately installed Glamsterdam devnet fixture lane."""
    return check_release_lane(
        manifest, amsterdam_root, "glamsterdam_devnet", "glamsterdam-devnet"
    )


def deep_compare_amsterdam(manifest: dict, amsterdam_root: Path) -> list[Check]:
    """Deep-check the Glamsterdam devnet tree against its pinned release asset."""
    return deep_compare_release_lane(
        manifest, amsterdam_root, "glamsterdam_devnet", "glamsterdam-devnet"
    )


def check_python_oracle(
    manifest: dict, venv_path: Path, manifest_path: Path = DEFAULT_MANIFEST
) -> list[Check]:
    spec = manifest["python_oracle"]
    checks: list[Check] = []

    try:
        lock_path = oracle_lock_path(manifest, manifest_path)
    except ManifestError as error:
        checks.append(Check("python-oracle: lock path", STATUS_FAIL, str(error)))
        return checks
    if not lock_path.is_file():
        checks.append(
            Check("python-oracle: lock", STATUS_MISSING, f"not found: {lock_path}")
        )
        return checks

    actual_lock_hash = sha256_file(lock_path)
    expected_lock_hash = spec["requirements_lock_sha256"]
    if actual_lock_hash != expected_lock_hash:
        checks.append(
            Check(
                "python-oracle: lock hash",
                STATUS_FAIL,
                f"expected {expected_lock_hash}, got {actual_lock_hash}",
            )
        )
        return checks
    checks.append(Check("python-oracle: lock hash", STATUS_OK, actual_lock_hash))

    try:
        locked_packages = parse_requirements_lock(lock_path)
    except ManifestError as error:
        checks.append(Check("python-oracle: lock contents", STATUS_FAIL, str(error)))
        return checks

    known_packages = {
        normalize_package_name(name): package_version
        for name, package_version in spec["known_packages"].items()
    }
    inconsistent = [
        f"{name}: manifest {package_version}, lock {locked_packages.get(name, 'missing')}"
        for name, package_version in known_packages.items()
        if locked_packages.get(name) != package_version
    ]
    if inconsistent:
        checks.append(
            Check(
                "python-oracle: lock contents",
                STATUS_FAIL,
                "known-package mismatch — " + "; ".join(inconsistent),
            )
        )
        return checks
    checks.append(
        Check(
            "python-oracle: lock contents",
            STATUS_OK,
            f"{len(locked_packages)} exact package(s), each with SHA-256 hashes",
        )
    )

    python_bin = venv_path / "bin" / "python"
    if not python_bin.is_file():
        checks.append(
            Check("python-oracle: venv", STATUS_MISSING, f"not found: {python_bin}")
        )
        return checks
    checks.append(Check("python-oracle: venv", STATUS_OK, str(python_bin)))

    probe = (
        "import json, sys\n"
        "from importlib.metadata import distributions\n"
        "info = {'python_version': '%d.%d.%d' % sys.version_info[:3]}\n"
        "def norm(name):\n"
        "    import re\n"
        "    return re.sub(r'[-_.]+', '-', name).lower()\n"
        "packages = {norm(d.metadata['Name']): d.version for d in distributions()}\n"
        "info['packages'] = packages\n"
        "imports = {}\n"
        "for module in ('coincurve', 'Crypto', 'py_ecc'):\n"
        "    try:\n"
        "        __import__(module)\n"
        "        imports[module] = None\n"
        "    except Exception as error:\n"
        "        imports[module] = '%s: %s' % (type(error).__name__, error)\n"
        "info['imports'] = imports\n"
        "print(json.dumps(info))\n"
    )
    try:
        result = subprocess.run(
            [str(python_bin), "-c", probe],
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as error:
        checks.append(
            Check("python-oracle: interpreter", STATUS_FAIL, f"could not run venv python: {error}")
        )
        return checks
    if result.returncode != 0:
        checks.append(
            Check(
                "python-oracle: interpreter",
                STATUS_FAIL,
                f"venv python exited {result.returncode}: {result.stderr.strip()}",
            )
        )
        return checks
    try:
        info = json.loads(result.stdout.strip())
    except json.JSONDecodeError:
        checks.append(
            Check("python-oracle: interpreter", STATUS_FAIL, "could not parse venv probe output")
        )
        return checks

    actual_version = info["python_version"]
    if actual_version != spec["intended_version"]:
        checks.append(
            Check(
                "python-oracle: version",
                STATUS_FAIL,
                f"expected {spec['intended_version']}, got {actual_version}",
            )
        )
    else:
        checks.append(Check("python-oracle: version", STATUS_OK, actual_version))

    actual_packages = info["packages"]
    for name, expected_version in locked_packages.items():
        actual = actual_packages.get(name)
        if actual is None:
            checks.append(Check(f"python-oracle: {name}", STATUS_MISSING, "not installed"))
        elif actual != expected_version:
            checks.append(
                Check(
                    f"python-oracle: {name}",
                    STATUS_FAIL,
                    f"expected {expected_version}, got {actual}",
                )
            )
        else:
            checks.append(Check(f"python-oracle: {name}", STATUS_OK, actual))

    extras = sorted(set(actual_packages) - set(locked_packages))
    if extras:
        checks.append(
            Check(
                "python-oracle: extra packages",
                STATUS_FAIL,
                f"{len(extras)} package(s) not in the frozen lock: "
                + ", ".join(extras[:10]),
            )
        )
    else:
        checks.append(Check("python-oracle: extra packages", STATUS_OK, "none"))

    import_errors = {
        module: detail for module, detail in info.get("imports", {}).items() if detail
    }
    if import_errors:
        checks.append(
            Check(
                "python-oracle: imports",
                STATUS_FAIL,
                "; ".join(
                    f"{module}: {detail}" for module, detail in import_errors.items()
                ),
            )
        )
    else:
        checks.append(
            Check("python-oracle: imports", STATUS_OK, "coincurve, Crypto, py_ecc")
        )

    return checks


def check_required_commands() -> list[Check]:
    checks = []
    git_path = shutil.which("git")
    if git_path is None:
        checks.append(Check("command: git", STATUS_MISSING, "git not found on PATH"))
    else:
        checks.append(Check("command: git", STATUS_OK, git_path))
    return checks


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=DEFAULT_MANIFEST,
        help=f"path to the source manifest (default: {DEFAULT_MANIFEST})",
    )
    parser.add_argument(
        "--execution-specs",
        type=Path,
        default=None,
        help="execution-specs checkout root (default: $EELS_ROOT or ~/execution-specs)",
    )
    parser.add_argument(
        "--eest-root",
        type=Path,
        default=None,
        help="EEST install root containing the archive and extracted fixtures/ "
        "(default: $EEST_ROOT or ~/eest-fixtures; distinct from check-legacy.sh's "
        "JAUNE_FIXTURES, which points directly at a tier's leaf fixture dir)",
    )
    parser.add_argument(
        "--mainnet-root",
        type=Path,
        default=None,
        help="current-mainnet install root containing fixtures.tar.gz and extracted "
        "fixtures/ (default: $EEST_MAINNET_ROOT or ~/eest-mainnet-v20.0.1)",
    )
    parser.add_argument(
        "--amsterdam-root",
        type=Path,
        default=None,
        help="Glamsterdam devnet install root containing the release archive and "
        "extracted fixtures/ (default: $EEST_AMSTERDAM_ROOT or "
        "~/eest-glamsterdam-devnet-v8.1.4). This lane holds fixtures for a fork "
        "whose rules this build does not implement; installing it claims nothing "
        "about running it.",
    )
    parser.add_argument(
        "--venv",
        type=Path,
        default=None,
        help="Python oracle venv path (default: <execution-specs root>/venv)",
    )
    parser.add_argument(
        "--legacy-only",
        action="store_true",
        help="check only Git-backed legacy fixture sources; skip EEST and Python "
        "(the components deliberately not installed by bootstrap_legacy.py)",
    )
    parser.add_argument(
        "--eest-deep",
        action="store_true",
        help="additionally deep-verify the extracted EEST tree against the "
        "release archive (hashes every file; slower but detects changed, "
        "missing, and extra fixtures). Ignored with --legacy-only.",
    )
    parser.add_argument(
        "--mainnet-deep",
        action="store_true",
        help="additionally deep-verify the current-mainnet fixture tree against "
        "its release archive. Ignored with --legacy-only.",
    )
    parser.add_argument(
        "--amsterdam-deep",
        action="store_true",
        help="additionally deep-verify the Glamsterdam devnet fixture tree "
        "against its release archive. Ignored with --legacy-only.",
    )
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    return parser


def main(argv: list[str]) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    try:
        manifest = load_manifest(args.manifest)
    except ManifestError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    if args.execution_specs is not None:
        execution_specs_root = args.execution_specs.expanduser()
    elif os.environ.get("EELS_ROOT"):
        execution_specs_root = Path(os.environ["EELS_ROOT"]).expanduser()
    else:
        execution_specs_root = Path.home() / manifest["execution_specs"]["default_subpath_from_home"]

    if args.eest_root is not None:
        eest_root = args.eest_root.expanduser()
    elif os.environ.get("EEST_ROOT"):
        eest_root = Path(os.environ["EEST_ROOT"]).expanduser()
    else:
        eest_root = Path.home() / manifest["eest"]["default_subpath_from_home"]

    if args.mainnet_root is not None and "current_mainnet" not in manifest:
        print("error: --mainnet-root requires a current_mainnet manifest section", file=sys.stderr)
        return 2
    if args.mainnet_root is not None:
        mainnet_root = args.mainnet_root.expanduser()
    elif os.environ.get("EEST_MAINNET_ROOT"):
        mainnet_root = Path(os.environ["EEST_MAINNET_ROOT"]).expanduser()
    elif "current_mainnet" in manifest:
        mainnet_root = Path.home() / manifest["current_mainnet"]["default_subpath_from_home"]
    else:
        mainnet_root = None

    if args.amsterdam_root is not None and "glamsterdam_devnet" not in manifest:
        print(
            "error: --amsterdam-root requires a glamsterdam_devnet manifest section",
            file=sys.stderr,
        )
        return 2
    if args.amsterdam_root is not None:
        amsterdam_root = args.amsterdam_root.expanduser()
    elif os.environ.get("EEST_AMSTERDAM_ROOT"):
        amsterdam_root = Path(os.environ["EEST_AMSTERDAM_ROOT"]).expanduser()
    elif "glamsterdam_devnet" in manifest:
        amsterdam_root = Path.home() / manifest["glamsterdam_devnet"]["default_subpath_from_home"]
    else:
        amsterdam_root = None

    # The devnet lane is optional in a way the mainnet lane is not: it is a
    # prerelease corpus no in-tree gate runs today, so an installation that is
    # simply absent is not a failure. It is checked when it is asked for
    # explicitly, and when it is actually installed.
    check_amsterdam_lane = amsterdam_root is not None and (
        args.amsterdam_root is not None
        or args.amsterdam_deep
        or bool(os.environ.get("EEST_AMSTERDAM_ROOT"))
        or amsterdam_root.is_dir()
    )

    venv_path = args.venv or (execution_specs_root / "venv")

    checks: list[Check] = []
    checks.extend(check_required_commands())
    checks.extend(check_execution_specs(manifest, execution_specs_root))
    checks.extend(check_ethereum_tests(manifest, execution_specs_root))
    if not args.legacy_only:
        checks.extend(check_eest(manifest, eest_root))
        if args.eest_deep:
            checks.extend(deep_compare_eest(manifest, eest_root))
        if mainnet_root is not None:
            checks.extend(check_current_mainnet(manifest, mainnet_root))
        if args.mainnet_deep and mainnet_root is not None:
            checks.extend(deep_compare_current_mainnet(manifest, mainnet_root))
        if check_amsterdam_lane:
            checks.extend(check_amsterdam(manifest, amsterdam_root))
        if args.amsterdam_deep and amsterdam_root is not None:
            checks.extend(deep_compare_amsterdam(manifest, amsterdam_root))
        checks.extend(check_python_oracle(manifest, venv_path, args.manifest))

    ok = all(check.status == STATUS_OK for check in checks)

    if args.json:
        payload = {
            "ok": ok,
            "checks": [asdict(check) for check in checks],
        }
        print(json.dumps(payload, indent=2))
    else:
        for check in checks:
            marker = {"ok": "OK", "missing": "MISSING", "fail": "FAIL"}[check.status]
            print(f"{marker:8} {check.name}: {check.detail}")
        print()
        print("OK — all checks passed" if ok else "NOT OK — see failures/missing components above")

    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
