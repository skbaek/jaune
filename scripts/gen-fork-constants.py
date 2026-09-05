#!/usr/bin/env python3
"""Extract every declared fork's rule constants from the pinned EELS revision.

`scripts/check-fork-constants.sh` compares what this writes against what the
built binary prints for `--rules <fork>`, so that no number in
`Jaune/Fork.lean` is a transcription anybody has to re-read against a
specification by eye. This is decision D10 of the Amsterdam programme.

Provenance, in the order it is established:

  1. the conformance-target checkout named by `sources.json` is located, and
     its revision is verified exactly as `gen-t8n-goldens.py` verifies it --
     the pin, or the pin plus the framework-side Jaune wrapper, and nothing
     else;
  2. `git diff <pin> HEAD -- src/ethereum` is required to be empty, so the
     specification tree the probe imports is byte-identical to the pinned
     commit even though it is read through the working tree;
  3. the probe runs in that checkout's own virtual environment and reports
     each constant as a *value* together with the dotted upstream path it came
     from.

Step 2 is what makes importing legitimate. The constants are not all literals
-- Amsterdam's `CREATE_ACCESS` is a sum of two other costs and its
`REFUND_STORAGE_CLEAR` a state-gas product -- so reading them as text would
mean reimplementing those expressions here, in a second place that could
disagree with upstream. Importing evaluates the definitions upstream ships;
the git checks are what tie the import to the pin.

A moved, dirty, or otherwise unexpected checkout is refused rather than
silently generating against a different revision.

Usage:
  python3 scripts/gen-fork-constants.py [--check]

  --check   regenerate in memory and report whether the committed artifact
            still matches, without writing anything.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
SOURCES = SCRIPTS / "sources.json"
OUTPUT = SCRIPTS / "amsterdam" / "constants.json"
PROBE = SCRIPTS / "fork_constants_probe.py"

# The generator shares `gen-t8n-goldens.py`'s allowance verbatim: the anchor,
# or the anchor plus exactly the framework-side wrapper files. Naming it here
# rather than importing keeps the two gates independently readable, and the
# `src/ethereum` diff check below is the one that actually matters for this
# gate -- the wrapper lives entirely outside that tree.
WRAPPER_PATHS = {
    "packages/testing/src/execution_testing/client_clis/__init__.py",
    "packages/testing/src/execution_testing/client_clis/clis/jaune.py",
    "packages/testing/src/execution_testing/client_clis/tests/test_jaune.py",
    "packages/testing/src/execution_testing/client_clis/transition_tool.py",
}

# Every `ForkRules` field the printer emits must appear here, and
# `check-fork-constants.sh` fails when one does not. A field is either checked
# against upstream by this generator, or explicitly recorded as checked
# somewhere else with the gate that checks it named. The point is that a field
# added later cannot become silently unchecked: it has to be classified.
COVERAGE = {
    "blob.target": "checked",
    "blob.max": "checked",
    "blob.baseFeeUpdateFraction": "checked",
    "blob.reserveBaseCost": "checked",
    "code.maxCodeSize": "checked",
    "code.maxInitCodeSize": "checked",
    "tx.maxGas": "checked",
    "tx.maxBlobCount": "checked",
    "block.maxRlpSize": "checked",
    "op.clz": "checked",
    "op.slotnum": "checked",
    "op.stackAccess": "checked",
    "precompiles": "checked",
    "gas.coldAccountAccess": "checked",
    "gas.callValue": "checked",
    "gas.createAccess": "checked",
    "gas.storageClearRefund": "checked",
    "gas.txBase": "checked",
    "gas.txAccessListAddress": "checked",
    "gas.txAccessListStorageKey": "checked",
    "gas.floorTokenCost": "checked",
    "gas.perAuthIntrinsic": "checked",
    "gas.codeReadSurcharge": "checked",
    "header.blockAccessListHash": "checked",
    "header.slotNumber": "checked",
    "requests": "checked",
    # D13: the mainnet activation timestamp, from the pinned `FORK_CRITERIA`.
    # Not a `ForkRules` field -- the printer reads it from
    # `mainnetChainConfig` -- but a row of the same comparison, so that the
    # gate turns red the moment the pin schedules a fork this build's mainnet
    # schedule does not name (goal jaune-amsterdam-currency-v1, G5).
    "mainnetActivation": "checked",
    # EIP-8037's state-gas dimension. Every fork carries these rows; a fork
    # that meters in one dimension carries them as `null` with
    # `stateGas.present` false, exactly as `ForkRules.stateGas = none` prints.
    "stateGas.present": "checked",
    "stateGas.costPerStateByte": "checked",
    "stateGas.stateBytesPerNewAccount": "checked",
    "stateGas.stateBytesPerStorageSet": "checked",
    "stateGas.stateBytesPerAuthBase": "checked",
    "stateGas.storageWrite": "checked",
    "stateGas.accountWrite": "checked",
    "stateGas.txValueCost": "checked",
    "stateGas.accessListAddressFloorTokens": "checked",
    "stateGas.accessListStorageKeyFloorTokens": "checked",
    "stateGas.systemMaxSstoresPerCall": "checked",
    # EIP-7928's block-level access list, under the same Option convention as
    # the state-gas rows: every fork carries both, and a fork with no block
    # access list carries `bal.present` false and `bal.itemCost` null, exactly
    # as `ForkRules.bal = none` prints.
    "bal.present": "checked",
    "bal.itemCost": "checked",
    # The six MODEXP parameters are inline literals inside `complexity`,
    # `iterations` and `gas_cost` in the pinned modules -- upstream gives them
    # no names to read. Reading them would mean re-deriving each one from
    # probe inputs, which is a reimplementation of the pricing formula in this
    # script and exactly the second source of truth the gate exists to avoid.
    # They are covered as behaviour instead, by the differential oracle and the
    # repricing subtrees named below.
    "modexp.maxLength": "elsewhere",
    "modexp.flatComplexity": "elsewhere",
    "modexp.complexityCoeff": "elsewhere",
    "modexp.iterationCoeff": "elsewhere",
    "modexp.gasDivisor": "elsewhere",
    "modexp.minGas": "elsewhere",
}

ELSEWHERE_REASON = (
    "no named upstream constant: the value is an inline literal inside "
    "vm/precompiled_contracts/modexp.py's complexity/iterations/gas_cost. "
    "Checked as behaviour by scripts/check-vectors.sh and by the "
    "eip7823_modexp_upper_bounds and eip7883_modexp_gas_increase subtrees of "
    "scripts/check-mainnet.sh --suite osaka."
)


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)
    raise SystemExit(2)


def git(root: Path, *args: str) -> "subprocess.CompletedProcess[str]":
    return subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True)


def verify_revision(root: Path, pinned: str) -> None:
    """Refuse a checkout that could report a different revision's constants."""
    head = git(root, "rev-parse", "HEAD")
    if head.returncode != 0:
        fail(f"{root} is not a git checkout: {head.stderr.strip()}")
    dirty = git(root, "status", "--porcelain")
    if dirty.stdout.strip():
        fail(
            f"conformance-target checkout {root} has uncommitted changes; "
            "constants are extracted from a committed revision"
        )
    actual = head.stdout.strip()
    if actual != pinned:
        ancestry = git(root, "merge-base", "--is-ancestor", pinned, "HEAD")
        changed = git(root, "diff", "--name-only", pinned, "HEAD")
        unexpected = sorted(set(changed.stdout.split()) - WRAPPER_PATHS)
        if ancestry.returncode != 0 or unexpected:
            detail = f"; it changes {unexpected}" if unexpected else ""
            fail(
                f"conformance-target checkout {root} is at {actual}, which is "
                f"not {pinned} nor that revision plus the local Jaune "
                f"wrapper{detail}; constants must come from one revision"
            )
    # The check this gate actually rests on. The probe imports from the working
    # tree, so the working tree's specification sources must be the pin's.
    spec_diff = git(root, "diff", "--name-only", pinned, "HEAD", "--", "src/ethereum")
    if spec_diff.returncode != 0:
        fail(f"could not diff {root} against {pinned}: {spec_diff.stderr.strip()}")
    if spec_diff.stdout.strip():
        fail(
            f"conformance-target checkout {root} differs from {pinned} under "
            f"src/ethereum: {sorted(spec_diff.stdout.split())}. The extracted "
            "constants would not be the pinned revision's."
        )


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
        fail(
            f"conformance-target checkout not found at {root}; set "
            f"{entry['default_env_var']} or clone {entry['repo_url']} at "
            f"{entry['commit']}"
        )
    verify_revision(root, entry["commit"])
    python = root / entry["venv_subpath"] / "bin" / "python"
    if not python.exists():
        fail(
            f"{python} not found; create the target's venv with "
            f"`cd {root} && uv sync --no-default-groups --group test`"
        )
    return root, python, entry["commit"]


def build() -> dict:
    root, python, commit = target()
    run = subprocess.run(
        [str(python), str(PROBE)],
        capture_output=True,
        text=True,
        cwd=str(root),
        env={"PYTHONPATH": str(SCRIPTS), "PATH": "/usr/bin:/bin"},
    )
    if run.returncode != 0:
        fail(f"constant probe failed in {root}:\n{run.stderr.strip()}")
    try:
        forks = json.loads(run.stdout)
    except json.JSONDecodeError as error:
        fail(f"constant probe emitted unreadable JSON: {error}")

    extracted = {
        path for fork in forks.values() for path in fork["constants"]
    }
    declared = {path for path, status in COVERAGE.items() if status == "checked"}
    if extracted != declared:
        missing = sorted(declared - extracted)
        extra = sorted(extracted - declared)
        fail(
            "the probe and the coverage table disagree about which fields are "
            f"checked: missing {missing}, unexpected {extra}"
        )

    return {
        # 2: the metering vehicle's per-fork `fork_coverage` table is gone.
        # Every declared fork resolves, so every field of every fork's record
        # is compared or classified by the single `coverage` table above.
        "schema_version": 2,
        "_comment": (
            "Generated by scripts/gen-fork-constants.py from the pinned "
            "conformance target. Never hand-edited: scripts/check-fork-constants.sh "
            "compares it against `lake exe jaune --rules <fork>`, and "
            "`--check` fails if this file is stale."
        ),
        "conformance_target_commit": commit,
        "coverage": {
            path: (
                {"status": status}
                if status == "checked"
                else {"status": status, "reason": ELSEWHERE_REASON}
            )
            for path, status in sorted(COVERAGE.items())
        },
        "forks": forks,
    }


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check", action="store_true", help="fail unless the committed artifact is exact"
    )
    args = parser.parse_args(argv)
    actual = build()
    if args.check:
        try:
            expected = json.loads(OUTPUT.read_text())
        except (OSError, json.JSONDecodeError) as error:
            print(f"error: cannot read {OUTPUT}: {error}", file=sys.stderr)
            return 2
        if expected != actual:
            print(
                "RED — fork constants: the committed extraction is stale or the "
                "pinned revision's constants moved",
                file=sys.stderr,
            )
            return 1
        print(
            "OK — fork constants: the committed extraction matches "
            f"{actual['conformance_target_commit']}"
        )
        return 0
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(actual, indent=2, sort_keys=True) + "\n")
    print(f"Wrote {OUTPUT} from {actual['conformance_target_commit']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
