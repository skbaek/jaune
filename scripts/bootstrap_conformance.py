#!/usr/bin/env python3
"""Provision a fresh conformance checkout; never repair an existing one.

Default mode installs the semantic base, as the former inline CI step did.
--with-cli-adapter requires an explicit dedicated --root. The adapter is
applied only to a fresh checkout, committed locally, then verified by exact
blob/hash identity. This script does not create a venv or run EELS.
"""
from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

from conformance_reference import (
    ReferenceError, adapter_registration, git, target_root, verify_reference,
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=Path(__file__).with_name("sources.json"))
    parser.add_argument("--root", type=Path)
    parser.add_argument("--with-cli-adapter", action="store_true")
    args = parser.parse_args()
    try:
        entry = json.loads(args.manifest.read_text())["conformance_target"]
        scripts = args.manifest.resolve().parent
        if args.with_cli_adapter and args.root is None:
            raise ReferenceError("--with-cli-adapter requires an explicit dedicated --root")
        dest = (args.root or target_root(entry)).expanduser()
        if args.with_cli_adapter and dest.resolve() == (Path.home() / entry["default_subpath_from_home"]).resolve():
            raise ReferenceError("the CLI adapter must not replace the default base checkout")
        adapter = adapter_registration(entry, scripts)
        if args.with_cli_adapter and adapter is None:
            raise ReferenceError("no CLI adapter is registered")
        if dest.exists() or dest.is_symlink():
            identity = verify_reference(dest, entry, scripts)
            if (identity["kind"] == "cli-adapter") != args.with_cli_adapter:
                raise ReferenceError("existing target has different adapter mode; never repaired")
            print(f"NO-OP — verified conformance checkout: {dest}")
        else:
            subprocess.run(["git", "clone", "--no-checkout", "--origin", "origin", "--",
                            entry["repo_url"], str(dest)], check=True)
            git(dest, "checkout", "--detach", entry["commit"])
            if args.with_cli_adapter:
                patch = scripts / adapter["patch_subpath"]
                git(dest, "apply", "--check", str(patch))
                git(dest, "apply", str(patch))
                git(dest, "add", "--", adapter["path"])
                git(dest, "-c", "user.name=Jaune reference bootstrap",
                    "-c", "user.email=reference-bootstrap@example.invalid",
                    "-c", "commit.gpgsign=false", "commit", "-m",
                    "Adapt t8n reward summaries before typed environment validation")
            identity = verify_reference(dest, entry, scripts)
        print(json.dumps(identity, indent=2, sort_keys=True))
    except (ReferenceError, OSError, KeyError, TypeError, subprocess.CalledProcessError,
            json.JSONDecodeError) as error:
        parser.exit(1, f"error: {error}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
