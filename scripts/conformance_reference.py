"""Read-only identity verification for the conformance EELS checkout.

The semantic base and legacy four-path wrapper allowance remain unchanged.
A CLI adapter is a separate exact-content identity, never a path allowance.
No function here imports EELS, changes a checkout, or executes its tools.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path, PurePosixPath

WRAPPER_PATHS = {
    "packages/testing/src/execution_testing/client_clis/__init__.py",
    "packages/testing/src/execution_testing/client_clis/clis/jaune.py",
    "packages/testing/src/execution_testing/client_clis/tests/test_jaune.py",
    "packages/testing/src/execution_testing/client_clis/transition_tool.py",
}
CLI_PATH = "packages/testing/src/execution_testing/evm_tools/t8n/cli.py"


class ReferenceError(ValueError):
    pass


def git(root: Path, *args: str) -> bytes:
    try:
        run = subprocess.run(
            ["git", "-C", str(root), *args], capture_output=True,
            env={**os.environ, "GIT_OPTIONAL_LOCKS": "0"},
        )
    except OSError as error:
        raise ReferenceError(f"cannot inspect reference checkout: {error}") from error
    if run.returncode:
        raise ReferenceError(f"reference git {' '.join(args)}: {run.stderr.decode().strip()}")
    return run.stdout


def target_root(entry: dict) -> Path:
    return Path(os.environ.get(entry["default_env_var"]) or
                Path.home() / entry["default_subpath_from_home"]).expanduser()


def adapter_registration(entry: dict, scripts: Path) -> dict | None:
    adapter = entry.get("cli_adapter")
    if adapter is None:
        return None
    keys = {"id", "path", "base_git_blob", "adapted_git_blob", "adapted_sha256",
            "mode", "patch_subpath", "patch_sha256"}
    if not isinstance(adapter, dict) or set(adapter) != keys:
        raise ReferenceError("invalid conformance_target.cli_adapter fields")
    if adapter["id"] != "ommer-reward-summary-cli-v1" or adapter["path"] != CLI_PATH:
        raise ReferenceError("unknown reference CLI adapter identity")
    for key, width in [("base_git_blob", 40), ("adapted_git_blob", 40),
                       ("adapted_sha256", 64), ("patch_sha256", 64)]:
        if not isinstance(adapter[key], str) or not re.fullmatch(rf"[0-9a-f]{{{width}}}", adapter[key]):
            raise ReferenceError(f"invalid CLI adapter {key}")
    if adapter["mode"] != "100644":
        raise ReferenceError("reference CLI adapter must remain a regular non-executable file")
    rel = PurePosixPath(adapter["patch_subpath"])
    if rel.is_absolute() or ".." in rel.parts:
        raise ReferenceError("unsafe reference patch path")
    patch = scripts / str(rel)
    if not patch.resolve().is_relative_to(scripts.resolve()):
        raise ReferenceError("reference patch escapes scripts directory")
    try:
        actual = hashlib.sha256(patch.read_bytes()).hexdigest()
    except OSError as error:
        raise ReferenceError(f"cannot read registered CLI patch: {error}") from error
    if actual != adapter["patch_sha256"]:
        raise ReferenceError("registered CLI patch digest differs")
    return adapter


def verify_reference(root: Path, entry: dict, scripts: Path) -> dict:
    base = entry["commit"]
    if not isinstance(base, str) or not re.fullmatch(r"[0-9a-f]{40}", base):
        raise ReferenceError("reference semantic base is not a full commit ID")
    adapter = adapter_registration(entry, scripts)
    head = git(root, "rev-parse", "HEAD").decode().strip()
    if git(root, "status", "--porcelain"):
        raise ReferenceError(f"reference checkout {root} has uncommitted changes")
    if head == base:
        return {"semantic_base": base, "checkout_head": head, "kind": "base"}
    git(root, "merge-base", "--is-ancestor", base, "HEAD")
    changed = set(filter(None, git(root, "diff", "--name-only", "--no-renames", "-z", base, "HEAD").decode().split("\0")))
    if changed <= WRAPPER_PATHS:
        return {"semantic_base": base, "checkout_head": head, "kind": "jaune-wrapper"}
    # The adapter checkout must contain ONLY this exact adapter relative to
    # the base. It cannot combine arbitrary wrapper changes with CLI changes.
    if adapter is None or changed != {CLI_PATH}:
        raise ReferenceError(f"unregistered reference changes: {sorted(changed)}")
    for revision, expected_blob in [(base, adapter["base_git_blob"]),
                                    ("HEAD", adapter["adapted_git_blob"])]:
        wanted = f'{adapter["mode"]} blob {expected_blob}\t{CLI_PATH}\n'.encode()
        if git(root, "ls-tree", revision, "--", CLI_PATH) != wanted:
            raise ReferenceError(f"reference CLI mode/blob differs at {revision}")
    committed = git(root, "show", f"HEAD:{CLI_PATH}")
    wanted_sha = adapter["adapted_sha256"]
    if hashlib.sha256(committed).hexdigest() != wanted_sha:
        raise ReferenceError("committed reference CLI digest differs")
    if hashlib.sha256((root / CLI_PATH).read_bytes()).hexdigest() != wanted_sha:
        raise ReferenceError("working reference CLI digest differs")
    return {"semantic_base": base, "checkout_head": head, "kind": "cli-adapter",
            "cli_adapter": adapter}


def check_reference_records(provenance: dict, entry: dict, scripts: Path, cases: Path) -> None:
    """Check stored reference identities without a target checkout or venv."""
    adapter = adapter_registration(entry, scripts)
    records = provenance.get("reference_identities", {})
    if not isinstance(records, dict) or set(records) - set(provenance["cases"]):
        raise ReferenceError("invalid per-case reference identity registry")
    for name in provenance["cases"]:
        env = json.loads((cases / name / "env.json").read_text())
        identity = records.get(name)
        if identity is None:
            if env.get("ommers"):
                raise ReferenceError(f"{name}: nonempty ommers require recorded adapter identity")
            continue  # Historical base-only entries remain byte-identical.
        if not isinstance(identity, dict):
            raise ReferenceError(f"{name}: reference identity must be an object")
        kind = identity.get("kind")
        expected = {"semantic_base", "checkout_head", "kind"}
        if kind == "cli-adapter":
            expected.add("cli_adapter")
        if set(identity) != expected or identity.get("semantic_base") != entry["commit"]:
            raise ReferenceError(f"{name}: malformed reference identity")
        if not re.fullmatch(r"[0-9a-f]{40}", identity.get("checkout_head", "")):
            raise ReferenceError(f"{name}: missing actual reference HEAD")
        if kind == "base":
            if identity["checkout_head"] != entry["commit"]:
                raise ReferenceError(f"{name}: base reference HEAD differs")
        elif kind == "cli-adapter":
            if adapter is None or identity.get("cli_adapter") != adapter:
                raise ReferenceError(f"{name}: unregistered reference CLI adapter")
            if identity["checkout_head"] == entry["commit"]:
                raise ReferenceError(f"{name}: adapter identity names the unmodified base")
        elif kind != "jaune-wrapper":
            raise ReferenceError(f"{name}: unknown reference kind")
        if env.get("ommers") and kind != "cli-adapter":
            raise ReferenceError(f"{name}: nonempty ommers require CLI adapter reference")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=Path(__file__).with_name("sources.json"))
    parser.add_argument("--root", type=Path)
    parser.add_argument("--require-cli-adapter", action="store_true")
    args = parser.parse_args()
    try:
        entry = json.loads(args.manifest.read_text())["conformance_target"]
        identity = verify_reference(args.root or target_root(entry), entry, args.manifest.parent)
        if args.require_cli_adapter and identity["kind"] != "cli-adapter":
            raise ReferenceError("this operation requires the registered CLI adapter checkout")
    except (ReferenceError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        parser.exit(1, f"error: {error}\n")
    print(json.dumps(identity, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
