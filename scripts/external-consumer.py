#!/usr/bin/env python3
"""Prepare a disposable Git consumer, or verify its resolved dependency identity.

Compilation is deliberately separate: CI uses lean-action, and coordinated local
hosts use their admitted build launcher. This script never invokes a Lean build.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
from urllib.parse import urlparse


def git(path, *args):
    return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()


def prepare(args):
    root = Path(__file__).resolve().parent.parent
    destination = Path(args.directory).resolve()
    if destination.exists():
        raise ValueError("destination must not exist")
    if not re.fullmatch(r"[0-9a-f]{40}", args.revision):
        raise ValueError("revision must be a full lowercase Git commit ID")
    parsed = urlparse(args.url)
    if parsed.scheme not in {"https", "file"} or not parsed.path or parsed.query or parsed.fragment:
        raise ValueError("expected an HTTPS Git URL (or file:// bare Git mirror for local rehearsal)")
    if parsed.username or parsed.password:
        raise ValueError("credentials must not be embedded in the dependency URL")
    # TOML strings use JSON-compatible escaping for these scalar values.
    lakefile = f'''name = "jaune-consumer"
version = "0.1.0"
defaultTargets = ["Consumer"]

[[require]]
name = "jaune"
git = {json.dumps(args.url)}
rev = {json.dumps(args.revision)}

[[lean_lib]]
name = "Consumer"
'''
    toolchain = (root / "lean-toolchain").read_text()
    consumer = (root / "scripts/consumer/Consumer.lean").read_bytes()
    destination.mkdir(parents=True)
    (destination / "lakefile.toml").write_text(lakefile)
    (destination / "lean-toolchain").write_text(toolchain)
    (destination / "Consumer.lean").write_bytes(consumer)
    (destination / "expected.json").write_text(json.dumps({
        "url": args.url, "revision": args.revision, "toolchain": toolchain.strip(),
    }, indent=2) + "\n")
    shutil.copyfile(__file__, destination / "verify-consumer.py")
    print(f"PREPARED — external consumer at {destination}; revision {args.revision}")


def verify(args):
    root = Path(args.directory).resolve()
    expected = json.loads((root / "expected.json").read_text())
    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = manifest["packages"]
    matches = [p for p in packages if p["name"] == "jaune"]
    if len(matches) != 1:
        raise ValueError("expected exactly one resolved jaune dependency")
    jaune = matches[0]
    if jaune.get("type") != "git" or jaune.get("url") != expected["url"] or jaune.get("rev") != expected["revision"]:
        raise ValueError("resolved Jaune Git identity differs from the requested candidate")
    if any(p.get("type") != "git" for p in packages):
        raise ValueError("consumer contains a non-Git dependency")
    if any(p["name"].lower() in {"blanc", "creme"} for p in packages):
        raise ValueError("consumer unexpectedly depends on Blanc/Creme")
    package = root / manifest["packagesDir"] / "jaune"
    if package.is_symlink() or root not in package.resolve().parents:
        raise ValueError("Jaune package escapes the disposable consumer")
    if git(package, "rev-parse", "HEAD") != expected["revision"]:
        raise ValueError("installed Jaune checkout is at the wrong commit")
    if git(package, "status", "--porcelain", "--untracked-files=no"):
        raise ValueError("installed Jaune checkout has modified tracked files")
    if (package / "lean-toolchain").read_text().strip() != expected["toolchain"]:
        raise ValueError("consumer and candidate toolchains differ")
    if not (root / ".lake/build/lib/lean/Consumer.olean").is_file():
        raise ValueError("consumer was not built")
    print(f"OK — external consumer built against Git candidate {expected['revision']}; "
          f"{len(packages)} Git dependencies; no Blanc/Creme package")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    create = commands.add_parser("prepare")
    create.add_argument("directory")
    create.add_argument("--url", required=True)
    create.add_argument("--revision", required=True)
    check = commands.add_parser("verify")
    check.add_argument("directory")
    args = parser.parse_args()
    try:
        (prepare if args.command == "prepare" else verify)(args)
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"REGRESSION — external consumer: {error}\n")
