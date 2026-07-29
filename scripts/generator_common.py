"""Shared manifest-backed configuration for Jaune's Python generators."""
from __future__ import annotations

import argparse
import os
import subprocess
from importlib.metadata import PackageNotFoundError, version
from pathlib import Path

import env_doctor

DEFAULT_MANIFEST = Path(__file__).resolve().parent / "sources.json"


def add_source_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--manifest",
        type=Path,
        default=DEFAULT_MANIFEST,
        help=f"external-source manifest (default: {DEFAULT_MANIFEST})",
    )
    parser.add_argument(
        "--execution-specs",
        type=Path,
        default=None,
        help="path to the pinned execution-specs checkout "
        "(precedence: option, $EELS_ROOT, manifest home-relative default)",
    )


def load_generator_source(
    parser: argparse.ArgumentParser,
    manifest_path: Path,
    explicit_execution_specs: Path | None,
) -> tuple[dict, Path, Path]:
    try:
        manifest = env_doctor.load_manifest(manifest_path)
    except env_doctor.ManifestError as error:
        parser.error(str(error))

    spec = manifest["execution_specs"]
    if explicit_execution_specs is not None:
        selected = explicit_execution_specs.expanduser()
    elif os.environ.get(spec["default_env_var"]):
        selected = Path(os.environ[spec["default_env_var"]]).expanduser()
    else:
        selected = Path.home() / spec["default_subpath_from_home"]
    execution_specs = Path(os.path.abspath(os.fspath(selected)))
    source_root = execution_specs / "src"

    missing = [
        relative
        for relative in env_doctor.GENERATOR_SOURCE_LAYOUT
        if not (source_root / relative).is_file()
    ]
    if missing:
        parser.error(
            f"{execution_specs} is not an execution-specs checkout with the "
            f"expected Prague generator sources; missing: {', '.join(missing)}"
        )

    try:
        revision = subprocess.run(
            ["git", "-C", str(execution_specs), "rev-parse", "HEAD"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as error:
        parser.error(f"could not read the execution-specs Git revision: {error}")
    if revision != spec["commit"]:
        parser.error(
            f"execution-specs revision mismatch: expected {spec['commit']}, "
            f"got {revision}"
        )
    return manifest, execution_specs, source_root


def require_known_packages(parser: argparse.ArgumentParser, manifest: dict) -> None:
    for package_name, expected in manifest["python_oracle"]["known_packages"].items():
        try:
            actual = version(package_name)
        except PackageNotFoundError:
            parser.error(
                f"{package_name} is not installed; run this generator with the "
                "frozen oracle venv created by scripts/bootstrap_oracle.py"
            )
        if actual != expected:
            parser.error(
                f"{package_name} version mismatch: expected {expected}, got {actual}"
            )
