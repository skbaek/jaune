#!/usr/bin/env python3
"""Generate the `check-t8n.sh` corpus goldens from the conformance target.

The goldens this writes are the transition-tool outputs of the pinned
conformance target, verbatim. Nothing here is transcribed by hand and nothing
here reads Jaune: a golden that agreed with Jaune because it was copied from
Jaune would test nothing.

What it does, per case directory under `scripts/t8n/cases/`:

  1. signs `txs.src.json` into `txs.json`, using the target's own testing
     `Transaction.sign`, so that both tools consume one identical, fully
     signed transaction list rather than each signing its own;
  2. runs the target's `ethereum-spec-evm t8n` on the case's inputs;
  3. writes `expected/result.json`, `expected/alloc.json` and
     `expected/body.json` exactly as the target wrote them;
  4. records the generating revision and every golden's digest in
     `scripts/t8n/provenance.json`.

The target checkout and its venv are located from the `conformance_target`
entry of `scripts/sources.json`; its commit is verified before anything is
generated, so a moved checkout fails loudly instead of silently regenerating
against a different revision.

Usage:
  python3 scripts/gen-t8n-goldens.py [--case <name>] [--check]

  --check   regenerate into a temporary directory and report whether the
            committed goldens still match, without writing anything.
"""

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from t8n_inputs import T8nInputError, materialize_alloc, materialize_txs_source

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent
CASES_DIR = SCRIPTS / "t8n" / "cases"
PROVENANCE = SCRIPTS / "t8n" / "provenance.json"
SOURCES = SCRIPTS / "sources.json"

GOLDEN_FILES = ("result.json", "alloc.json", "body.json")


def fail(message: str) -> "NoReturn":  # type: ignore[valid-type]
    print(f"error: {message}", file=sys.stderr)
    raise SystemExit(2)


# The checkout also carries the local Jaune wrapper (see the goal's W-E and
# ~/plans/t8n-eest-jaune-wrapper.patch). That patch is framework-side only: it
# adds a client wrapper, its tests, and one opt-in flag on the transition-tool
# base class, none of which the `ethereum-spec-evm t8n` entry point reaches. So
# the generator accepts a checkout that is the anchor *plus exactly those
# files*, and refuses anything else -- a change under `src/ethereum/` would
# change the goldens and must never pass unnoticed.
WRAPPER_PATHS = {
    "packages/testing/src/execution_testing/client_clis/__init__.py",
    "packages/testing/src/execution_testing/client_clis/clis/jaune.py",
    "packages/testing/src/execution_testing/client_clis/tests/test_jaune.py",
    "packages/testing/src/execution_testing/client_clis/transition_tool.py",
}


def git(root: Path, *args: str) -> "subprocess.CompletedProcess[str]":
    return subprocess.run(
        ["git", "-C", str(root), *args], capture_output=True, text=True
    )


def verify_revision(root: Path, pinned: str) -> None:
    """Refuse a checkout that could generate against a different revision."""
    head = git(root, "rev-parse", "HEAD")
    if head.returncode != 0:
        fail(f"{root} is not a git checkout: {head.stderr.strip()}")
    dirty = git(root, "status", "--porcelain")
    if dirty.stdout.strip():
        fail(
            f"conformance-target checkout {root} has uncommitted changes; "
            "goldens are generated from a committed revision"
        )
    if head.stdout.strip() == pinned:
        return
    ancestry = git(root, "merge-base", "--is-ancestor", pinned, "HEAD")
    changed = git(root, "diff", "--name-only", pinned, "HEAD")
    unexpected = sorted(set(changed.stdout.split()) - WRAPPER_PATHS)
    if ancestry.returncode != 0 or unexpected:
        detail = (
            f"; it changes {unexpected}" if unexpected else ""
        )
        fail(
            f"conformance-target checkout {root} is at {head.stdout.strip()}, "
            f"which is not {pinned} nor that revision plus the local Jaune "
            f"wrapper{detail}; goldens and emission must come from one revision"
        )


def target_paths() -> "tuple[Path, Path, str]":
    """The conformance-target checkout, its interpreter, and its commit."""
    sources = json.loads(SOURCES.read_text())
    try:
        entry = sources["conformance_target"]
    except KeyError:
        fail("scripts/sources.json has no conformance_target entry")
    root = Path(
        os.environ.get(
            entry["default_env_var"],
            Path.home() / entry["default_subpath_from_home"],
        )
    )
    if not root.is_dir():
        fail(
            f"conformance-target checkout not found at {root}; set "
            f"{entry['default_env_var']} or clone "
            f"{entry['repo_url']} at {entry['commit']}"
        )
    verify_revision(root, entry["commit"])
    python = root / entry["venv_subpath"] / "bin" / "python"
    t8n = root / entry["venv_subpath"] / "bin" / entry["t8n_command"]
    if not t8n.exists():
        fail(
            f"{t8n} not found; create the target's venv with "
            f"`cd {root} && uv sync --no-default-groups --group test`"
        )
    return t8n, python, entry["commit"]


SIGN_SNIPPET = r"""
import json, sys
from execution_testing.test_types import Transaction

out = []
for raw in json.load(open(sys.argv[1])):
    tx = Transaction.model_validate(raw)
    if "v" not in tx.model_fields_set and tx.secret_key is not None:
        tx.sign()
    dumped = tx.model_dump(mode="json", by_alias=True, exclude_none=True)
    dumped.pop("secretKey", None)
    dumped.pop("sender", None)
    out.append(dumped)
json.dump(out, open(sys.argv[2], "w"), indent=2)
open(sys.argv[2], "a").write("\n")
"""


def sign_txs(python: Path, case: Path, out_dir: Path) -> None:
    src = out_dir / "txs.src.json"
    try:
        materialize_txs_source(case, SCRIPTS / "t8n", src)
    except T8nInputError as error:
        fail(str(error))
    with tempfile.NamedTemporaryFile("w", suffix=".py", delete=False) as f:
        f.write(SIGN_SNIPPET)
        snippet = f.name
    try:
        run = subprocess.run(
            [str(python), snippet, str(src), str(out_dir / "txs.json")],
            capture_output=True,
            text=True,
        )
    finally:
        os.unlink(snippet)
    if run.returncode != 0:
        fail(f"{case.name}: signing failed:\n{run.stderr}")


def run_target(t8n: Path, case: Path, work: Path) -> None:
    spec = json.loads((case / "case.json").read_text())
    try:
        materialize_alloc(case, SCRIPTS / "t8n", work / "input.alloc.json")
    except T8nInputError as error:
        fail(str(error))
    args = [
        str(t8n),
        "t8n",
        f"--input.alloc={work / 'input.alloc.json'}",
        f"--input.env={case / 'env.json'}",
        f"--input.txs={work / 'txs.json'}",
        "--output.result=result.json",
        "--output.alloc=alloc.json",
        "--output.body=body.json",
        f"--state.fork={spec['fork']}",
        f"--state.chainid={spec['chainid']}",
        f"--state.reward={spec['reward']}",
        f"--output.basedir={work}",
    ]
    if spec["mode"] == "state-test":
        args.append("--state-test")
    elif spec["mode"] != "blockchain":
        fail(f"{case.name}: unknown mode {spec['mode']!r}")
    run = subprocess.run(args, capture_output=True, text=True)
    if run.returncode != 0:
        fail(f"{case.name}: the conformance target failed:\n{run.stderr}")
    for name in GOLDEN_FILES:
        if not (work / name).exists():
            fail(f"{case.name}: the target wrote no {name}")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", help="regenerate only this case")
    parser.add_argument(
        "--check",
        action="store_true",
        help="report drift without writing anything",
    )
    options = parser.parse_args()

    t8n, python, commit = target_paths()
    names = sorted(p.name for p in CASES_DIR.iterdir() if p.is_dir())
    if options.case:
        if options.case not in names:
            fail(f"no case named {options.case!r} under {CASES_DIR}")
        names = [options.case]

    provenance = {"conformance_target_commit": commit, "cases": {}}
    if PROVENANCE.exists():
        previous = json.loads(PROVENANCE.read_text())
        if options.case:
            provenance["cases"] = previous.get("cases", {})

    drift = []
    with tempfile.TemporaryDirectory() as tmp:
        for name in names:
            case = CASES_DIR / name
            work = Path(tmp) / name
            work.mkdir()
            sign_txs(python, case, work)
            run_target(t8n, case, work)
            expected = case / "expected"
            expected.mkdir(exist_ok=True)
            produced = {"txs.json": work / "txs.json"}
            for golden in GOLDEN_FILES:
                produced[f"expected/{golden}"] = work / golden
            entry = {}
            for relative, path in produced.items():
                committed = case / relative
                if options.check:
                    if (
                        not committed.exists()
                        or committed.read_bytes() != path.read_bytes()
                    ):
                        drift.append(f"{name}/{relative}")
                else:
                    shutil.copyfile(path, committed)
                entry[relative] = digest(path)
            provenance["cases"][name] = entry
            print(f"  {name}: {len(produced)} file(s)")

    if options.check:
        if drift:
            print("DRIFT — t8n goldens differ from the target's current output:")
            for item in drift:
                print(f"  {item}")
            return 1
        print(f"OK — t8n goldens: {len(names)} case(s) match the target at {commit}")
        return 0

    PROVENANCE.write_text(json.dumps(provenance, indent=2, sort_keys=True) + "\n")
    print(f"OK — t8n goldens: {len(names)} case(s) generated from {commit}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
