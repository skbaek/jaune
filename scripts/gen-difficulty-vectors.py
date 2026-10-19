#!/usr/bin/env python3
"""Fill and check the bomb-boundary difficulty vectors (goal U10).

`scripts/difficulty-vectors.json` carries authored inputs at, below, and
above each bomb-only fork's delay, with `expected` left `null`. This script
runs the pinned conformance target's `calculate_block_difficulty` for each
fork module and either fills `expected` (generate mode) or compares the
committed values against the target's current output (`--check`).

Inputs are bound to the target function by parameter name, so a renamed
parameter fails loudly instead of binding positionally to the wrong value.
The shared verifier accepts the semantic pin, the existing four-path
framework wrapper, or the exact registered CLI adapter. All specification
files remain byte-identical to the semantic base in every accepted form.

Usage:
  python3 scripts/gen-difficulty-vectors.py [--check]
"""

from __future__ import annotations

import argparse
import inspect
import json
import subprocess
import sys
from pathlib import Path

from conformance_reference import ReferenceError, verify_reference

SCRIPTS = Path(__file__).resolve().parent
SOURCES = SCRIPTS / "sources.json"
OUTPUT = SCRIPTS / "difficulty-vectors.json"

# Reference admission is shared in conformance_reference.py.


MODULES = {
    "MuirGlacier": "muir_glacier",
    "ArrowGlacier": "arrow_glacier",
    "GrayGlacier": "gray_glacier",
}


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)
    raise SystemExit(2)


def git(root: Path, *args: str) -> "subprocess.CompletedProcess[str]":
    return subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True)


def verify_revision(root: Path, pinned: str) -> None:
    """Verify the semantic base, legacy wrapper, or exact registered adapter."""
    entry = json.loads(SOURCES.read_text())["conformance_target"]
    if pinned != entry["commit"]:
        fail("reference verifier received a different semantic pin")
    try:
        verify_reference(root, entry, SCRIPTS)
    except (ReferenceError, OSError) as error:
        fail(str(error))


SNIPPET = r"""
import importlib, inspect, json, sys

vectors = json.load(open(sys.argv[1]))
modules = json.loads(sys.argv[2])
out = {}
for label, module_name in modules.items():
    fork = importlib.import_module(f"ethereum.forks.{module_name}.fork")
    fn = getattr(fork, "calculate_block_difficulty", None)
    if fn is None:
        print(f"error: {module_name}.fork has no calculate_block_difficulty",
              file=sys.stderr)
        raise SystemExit(2)
    params = inspect.signature(fn).parameters
    results = []
    for vector in vectors[label]:
        inputs = {k: v for k, v in vector.items() if k != "expected"}
        missing = [k for k in inputs if k not in params]
        if missing:
            print(f"error: {label}.calculate_block_difficulty takes no "
                  f"{missing}; signature is {sorted(params)}", file=sys.stderr)
            raise SystemExit(2)
        results.append(int(fn(**{k: inputs[k] for k in params if k in inputs})))
    out[label] = results
json.dump(out, sys.stdout)
"""


def target() -> "tuple[Path, Path, str]":
    sources = json.loads(SOURCES.read_text())
    try:
        entry = sources["conformance_target"]
    except KeyError:
        fail("scripts/sources.json has no conformance_target entry")
    import os

    root = Path(
        os.environ.get(
            entry["default_env_var"], Path.home() / entry["default_subpath_from_home"]
        )
    )
    if not root.is_dir():
        fail(f"conformance-target checkout not found at {root}")
    verify_revision(root, entry["commit"])
    python = root / entry["venv_subpath"] / "bin" / "python"
    if not python.exists():
        fail(f"{python} not found")
    return root, python, entry["commit"]


def compute(root: Path, python: Path) -> dict:
    run = subprocess.run(
        [str(python), "-c", SNIPPET, str(OUTPUT), json.dumps(MODULES)],
        capture_output=True,
        text=True,
        cwd=str(root),
        env={"PATH": "/usr/bin:/bin"},
    )
    if run.returncode != 0:
        fail(f"difficulty oracle failed in {root}:\n{run.stderr.strip()}")
    try:
        return json.loads(run.stdout)
    except json.JSONDecodeError as error:
        fail(f"difficulty oracle emitted unreadable JSON: {error}")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    root, python, commit = target()
    document = json.loads(OUTPUT.read_text())
    comment = document.pop("_comment", None)
    if sorted(document) != sorted(MODULES):
        fail(f"{OUTPUT} names {sorted(document)}, expected {sorted(MODULES)}")
    computed = compute(root, python)
    problems = []
    for label in sorted(MODULES):
        for index, vector in enumerate(document[label]):
            if args.check:
                if vector["expected"] != computed[label][index]:
                    problems.append(
                        f"{label}[{index}]: committed {vector['expected']!r}, "
                        f"target computes {computed[label][index]!r}"
                    )
            else:
                vector["expected"] = computed[label][index]
    if args.check:
        if problems:
            for problem in problems:
                print(f"  - {problem}", file=sys.stderr)
            print("RED — difficulty vectors: committed expectations differ "
                  "from the target", file=sys.stderr)
            return 1
        print(f"OK — difficulty vectors: 9 vector(s) match the target at {commit[:12]}")
        return 0
    if comment is not None:
        document = {"_comment": comment, **document}
    OUTPUT.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")
    print(f"Wrote {OUTPUT} from {commit[:12]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
