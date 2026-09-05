#!/usr/bin/env bash
# Transition-tool conformance gate for `jaune t8n`.
#
# Compares this build's `t8n` output against goldens generated from the pinned
# conformance target (`conformance_target` in scripts/sources.json) over the
# committed corpus in scripts/t8n/cases/. The goldens are that target's own
# output, verbatim; scripts/gen-t8n-goldens.py wrote them and
# scripts/t8n/provenance.json records the revision and every golden's digest.
#
# Three things are checked per case, and all three must hold:
#
#   1. DETERMINISM. The binary is run twice into separate directories and the
#      two runs must be byte-identical -- key order and hex casing included.
#   2. CONFORMANCE. `result`, `alloc` and `body` must equal the goldens
#      byte for byte, after the two declared canonicalisations and the
#      declared deviations in scripts/t8n/deviations.json are applied to the
#      *golden* side. Nothing is applied to Jaune's side: its bytes are
#      compared as written.
#   3. PROVENANCE. Every golden's digest must match provenance.json, and
#      provenance.json's revision must match the pin in sources.json. A
#      hand-edited golden fails here rather than passing quietly.
#
# The two canonicalisations exist because neither order is normative and no
# consumer reads either: the target emits `alloc` in Python dictionary
# insertion order, Jaune in ascending key order. Both sides are sorted --
# addresses lexically, storage keys numerically -- before comparison.
#
# The deviations file is a *registry*, not a mask. Each entry pins Jaune's
# exact expected bytes alongside the target's, so an unregistered difference
# and a changed registered one both fail. Its two entry kinds are the
# rejection/block-exception message strings, which carry no normative content
# and which the framework maps rather than compares, and a small number of
# per-case field exemptions with their justification.
#
# This gate needs the built binary and nothing else -- no conformance-target
# checkout, no venv, no corpus download.
#
# Usage: scripts/check-t8n.sh [--red-test] [--case <name>]
#
#   --red-test  additionally prove the gate can fail: corrupt one byte of one
#               expectation in a scratch copy and require a red verdict, then
#               prove the registry bites -- dropping a registered deviation
#               must surface the difference it declares, and moving the target
#               bytes it pins must fail rather than be applied.
#   --case      run one case only.
#
# CLI contract: exit 0 iff every selected case passes; the last line is a
# single unambiguous verdict. Exit 1 on a failure, 2 on a usage or setup error.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="${JAUNE_BIN:-$ROOT/.lake/build/bin/jaune}"

ONLY=""
RED=0
while [ $# -gt 0 ]; do
  case "$1" in
    --red-test) RED=1; shift ;;
    --case) shift; [ $# -gt 0 ] || { echo "usage: --case <name>" >&2; exit 2; }
            ONLY="$1"; shift ;;
    *) echo "usage: scripts/check-t8n.sh [--red-test] [--case <name>]" >&2; exit 2 ;;
  esac
done

if [ ! -x "$BIN" ]; then
  echo "REGRESSION — t8n: no jaune binary at $BIN; run \`lake build\` first"
  exit 2
fi

JAUNE_T8N_BIN="$BIN" JAUNE_T8N_ONLY="$ONLY" JAUNE_T8N_RED="$RED" \
  python3 - "$ROOT" <<'PY'
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(sys.argv[1])
sys.path.insert(0, str(ROOT / "scripts"))
from t8n_inputs import T8nInputError, materialize_alloc

BIN = Path(os.environ["JAUNE_T8N_BIN"])
ONLY = os.environ["JAUNE_T8N_ONLY"]
RED = os.environ["JAUNE_T8N_RED"] == "1"

CASES = ROOT / "scripts" / "t8n" / "cases"
PROVENANCE = ROOT / "scripts" / "t8n" / "provenance.json"
DEVIATIONS = ROOT / "scripts" / "t8n" / "deviations.json"
SOURCES = ROOT / "scripts" / "sources.json"

OUTPUTS = ("result.json", "alloc.json", "body.json")


def canonical(name, obj):
    """The declared canonical form of one output document.

    `result` keeps its emitted order -- that order is the target's own model
    declaration order and is part of what the gate pins. `alloc` is sorted:
    addresses lexically (they are fixed-width, so that is numeric order too)
    and storage keys numerically, because they are not.
    """
    if name != "alloc.json":
        return json.dumps(obj, indent=4)
    out = {}
    for address in sorted(obj):
        account = dict(obj[address])
        storage = account.get("storage", {})
        account["storage"] = {
            k: storage[k] for k in sorted(storage, key=lambda x: int(x, 16))
        }
        out[address] = account
    return json.dumps(out, indent=4)


def message_identity(row):
    """The canonical identity a `messages` row maps its free text to.

    A row is either that identity on its own or an object carrying it under
    `jaune` beside the owner and date of the goal that ruled on the row.
    """
    return row["jaune"] if isinstance(row, dict) else row


def apply_deviations(case, name, obj, deviations):
    """Patch the *golden* into what Jaune is expected to have written."""
    messages = deviations["messages"]
    unmapped = []
    if name == "result.json":
        for rejection in obj.get("rejected", []):
            text = rejection.get("error")
            if text in messages:
                rejection["error"] = message_identity(messages[text])
            else:
                unmapped.append(text)
        exception = obj.get("blockException")
        if exception is not None:
            if exception in messages:
                obj["blockException"] = message_identity(messages[exception])
            else:
                unmapped.append(exception)
    for entry in deviations["fields"]:
        if entry["case"] != case or entry["document"] != name:
            continue
        pointer = obj
        path = entry["path"]
        for step in path[:-1]:
            pointer = pointer[step]
        if pointer[path[-1]] != entry["target"]:
            unmapped.append(
                f"registered deviation {case}/{name}/{'.'.join(path)} expected "
                f"the target to write {entry['target']!r}, found "
                f"{pointer[path[-1]]!r}"
            )
        if entry.get("jauneAbsent") is True:
            del pointer[path[-1]]
        else:
            pointer[path[-1]] = entry["jaune"]
    return unmapped


def run_case(case_dir, work):
    spec = json.loads((case_dir / "case.json").read_text())
    try:
        materialize_alloc(case_dir, ROOT / "scripts" / "t8n", work / "input.alloc.json")
    except T8nInputError as error:
        return subprocess.CompletedProcess([], 2, "", str(error)), spec
    args = [
        str(BIN), "t8n",
        f"--input.alloc={work / 'input.alloc.json'}",
        f"--input.env={case_dir / 'env.json'}",
        f"--input.txs={case_dir / 'txs.json'}",
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
    run = subprocess.run(args, capture_output=True, text=True)
    return run, spec


def check_case(name, expected_root, deviations, failures):
    case_dir = CASES / name
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "a").mkdir()
        (Path(tmp) / "b").mkdir()
        first, spec = run_case(case_dir, Path(tmp) / "a")
        second, _ = run_case(case_dir, Path(tmp) / "b")
        for run, label in ((first, "run 1"), (second, "run 2")):
            if run.returncode != 0:
                failures.append(
                    f"{name}: jaune t8n exited {run.returncode} on {label}\n"
                    f"    {run.stderr.strip()}"
                )
                return
        for output in OUTPUTS:
            a = (Path(tmp) / "a" / output).read_bytes()
            b = (Path(tmp) / "b" / output).read_bytes()
            if a != b:
                failures.append(
                    f"{name}: {output} is not deterministic across two runs"
                )
                return
        for output in OUTPUTS:
            actual = (Path(tmp) / "a" / output).read_text()
            golden_path = expected_root / name / "expected" / output
            golden_text = golden_path.read_text()
            if output == "body.json":
                golden = json.loads(golden_text)
                unmapped = []
                for entry in deviations["fields"]:
                    if entry["case"] == name and entry["document"] == output:
                        if golden != entry["target"]:
                            unmapped.append(
                                f"registered deviation {name}/{output} expected "
                                f"{entry['target']!r}, found {golden!r}"
                            )
                        golden = entry["jaune"]
                expected = json.dumps(golden)
            else:
                golden = json.loads(golden_text)
                unmapped = apply_deviations(name, output, golden, deviations)
                expected = canonical(output, golden)
            if unmapped:
                for item in unmapped:
                    failures.append(f"{name}: {output}: unregistered: {item}")
                continue
            if actual != expected:
                failures.append(
                    f"{name}: {output} differs from the golden\n"
                    + diff_report(expected, actual)
                )


def diff_report(expected, actual):
    import difflib

    lines = list(
        difflib.unified_diff(
            expected.splitlines(),
            actual.splitlines(),
            fromfile="expected",
            tofile="jaune",
            lineterm="",
            n=1,
        )
    )
    return "\n".join("    " + line for line in lines[:40])


def check_provenance(failures):
    if not PROVENANCE.exists():
        failures.append("scripts/t8n/provenance.json is missing")
        return None
    provenance = json.loads(PROVENANCE.read_text())
    case_names = sorted(p.name for p in CASES.iterdir() if p.is_dir())
    if sorted(provenance.get("cases", {})) != case_names:
        failures.append(
            "provenance case registry differs from the case directories; "
            "regenerate with scripts/gen-t8n-goldens.py"
        )
    pinned = json.loads(SOURCES.read_text())["conformance_target"]["commit"]
    if provenance["conformance_target_commit"] != pinned:
        failures.append(
            "the goldens were generated from "
            f"{provenance['conformance_target_commit']} but sources.json pins "
            f"{pinned}; regenerate with scripts/gen-t8n-goldens.py"
        )
    for name, files in provenance["cases"].items():
        for relative, expected_digest in files.items():
            path = CASES / name / relative
            if not path.exists():
                failures.append(f"{name}: {relative} is missing")
                continue
            actual = hashlib.sha256(path.read_bytes()).hexdigest()
            if actual != expected_digest:
                failures.append(
                    f"{name}: {relative} does not match its recorded digest; "
                    "a golden is generated evidence and is never edited by hand"
                )
    return provenance


def select():
    names = sorted(p.name for p in CASES.iterdir() if p.is_dir())
    if ONLY:
        if ONLY not in names:
            print(f"REGRESSION — t8n: no case named {ONLY!r}")
            raise SystemExit(2)
        return [ONLY]
    return names


def main():
    names = select()
    failures = []
    deviations = json.loads(DEVIATIONS.read_text())
    provenance = check_provenance(failures)
    for name in names:
        check_case(name, CASES, deviations, failures)
    for failure in failures:
        print(f"T8N — {failure}")

    if RED:
        # The gate must be able to go red. Corrupt one byte of one expectation
        # in a scratch copy of the corpus and require a failure; a gate that
        # cannot fail is not evidence.
        with tempfile.TemporaryDirectory() as tmp:
            scratch = Path(tmp) / "cases"
            shutil.copytree(CASES, scratch)
            victim = scratch / names[0] / "expected" / "result.json"
            corrupted = json.loads(victim.read_text())
            root = corrupted["stateRoot"]
            corrupted["stateRoot"] = root[:-1] + ("0" if root[-1] != "0" else "1")
            victim.write_text(json.dumps(corrupted, indent=4))
            red_failures = []
            check_case(names[0], scratch, deviations, red_failures)
            if not red_failures:
                print(
                    "T8N — the red test did not fail: a corrupted stateRoot in "
                    f"{names[0]} was accepted"
                )
                failures.append("red test did not fail")
            else:
                print(
                    "OK — t8n red test: a corrupted stateRoot in "
                    f"{names[0]} is rejected"
                )

        # The registry must also be doing real work: a difference that is not
        # registered must fail, and a registered entry whose target side moved
        # must fail too. Both are proved on a surviving registered deviation.
        registered = [
            entry for entry in deviations["fields"] if entry.get("case") in names
        ]
        if registered:
            entry = registered[0]
            victim = entry["case"]
            label = (
                f"{victim}/{entry['document']}/"
                f"{'.'.join(entry['path']) or '(document)'}"
            )

            dropped = json.loads(json.dumps(deviations))
            dropped["fields"] = [
                other for other in dropped["fields"] if other != entry
            ]
            dropped_failures = []
            check_case(victim, CASES, dropped, dropped_failures)
            if not dropped_failures:
                print(
                    "T8N — the red test did not fail: the difference at "
                    f"{label} was accepted with no registered deviation"
                )
                failures.append("unregistered difference passed")
            else:
                print(
                    "OK — t8n red test: the unregistered difference at "
                    f"{label} is rejected"
                )

            moved = json.loads(json.dumps(deviations))
            for other in moved["fields"]:
                if other == entry:
                    target = other["target"]
                    other["target"] = target[:-1] + (
                        "0" if target[-1] != "0" else "1"
                    )
            moved_failures = []
            check_case(victim, CASES, moved, moved_failures)
            if not moved_failures:
                print(
                    "T8N — the red test did not fail: the registered deviation "
                    f"at {label} was applied to a target value it does not pin"
                )
                failures.append("registered deviation mismatch passed")
            else:
                print(
                    "OK — t8n red test: a registered deviation whose target "
                    f"side moved is rejected at {label}"
                )

    if failures:
        print(
            f"REGRESSION — t8n: {len(failures)} failure(s) over "
            f"{len(names)} case(s)"
        )
        return 1
    commit = provenance["conformance_target_commit"] if provenance else "?"
    print(
        f"OK — t8n: {len(names)} case(s) byte-identical to goldens generated "
        f"from execution-specs {commit[:12]}, deterministic over two runs"
    )
    return 0


raise SystemExit(main())
PY
