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

from conformance_reference import ReferenceError, verify_reference

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


# Reference admission is shared in conformance_reference.py.



def git(root: Path, *args: str) -> "subprocess.CompletedProcess[str]":
    return subprocess.run(
        ["git", "-C", str(root), *args], capture_output=True, text=True
    )


def verify_revision(root: Path, pinned: str) -> None:
    """Verify the semantic base, legacy wrapper, or exact registered adapter."""
    entry = json.loads(SOURCES.read_text())["conformance_target"]
    if pinned != entry["commit"]:
        fail("reference verifier received a different semantic pin")
    try:
        verify_reference(root, entry, SCRIPTS)
    except (ReferenceError, OSError) as error:
        fail(str(error))


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
    entry = json.loads(SOURCES.read_text())["conformance_target"]
    try:
        identity = verify_reference(t8n.parents[2], entry, SCRIPTS)
    except (ReferenceError, OSError) as error:
        fail(str(error))
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
            if "reference_identities" in previous:
                provenance["reference_identities"] = previous["reference_identities"]

    drift = []
    with tempfile.TemporaryDirectory() as tmp:
        for name in names:
            case = CASES_DIR / name
            env = json.loads((case / "env.json").read_text())
            if env.get("ommers") and identity["kind"] != "cli-adapter":
                fail(f"{name}: nonempty ommers require the registered CLI adapter checkout")
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
            provenance.setdefault("reference_identities", {})[name] = identity
            print(f"  {name}: {len(produced)} file(s)")

    reference_label = commit
    if identity["kind"] == "cli-adapter":
        reference_label += (f' with CLI adapter {identity["cli_adapter"]["id"]}'
                            f' (checkout {identity["checkout_head"]})')
    if options.check:
        if drift:
            print("DRIFT — t8n goldens differ from the target's current output:")
            for item in drift:
                print(f"  {item}")
            return 1
        print(f"OK — t8n goldens: {len(names)} case(s) match the target at {reference_label}")
        return 0

    PROVENANCE.write_text(json.dumps(provenance, indent=2, sort_keys=True) + "\n")
    print(f"OK — t8n goldens: {len(names)} case(s) generated from {reference_label}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
