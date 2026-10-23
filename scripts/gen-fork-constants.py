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

from conformance_reference import ReferenceError, verify_reference

SCRIPTS = Path(__file__).resolve().parent
SOURCES = SCRIPTS / "sources.json"
OUTPUT = SCRIPTS / "amsterdam" / "constants.json"
PROBE = SCRIPTS / "fork_constants_probe.py"

# Reference admission is shared in conformance_reference.py.


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
    "tx.maxTotalGas": "checked",
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
    # The Byzantium..Cancun extension (goal U1, compared against the pinned
    # EELS revision by goal U1c). Every fork carries these rows. Numbers
    # upstream names (bn254 prices, the fifth-cap divisor, data costs) are
    # read as values with their dotted paths; shape facts (opcode and header
    # availability, the EIP-2929 shape, net metering, EIP-6780, the system
    # calls, the MODEXP formula) as source-presence facts; and fields a
    # post-merge fork cannot read (flat access prices, proof-of-work numbers)
    # as `null` with the absence stated, exactly as `stateGas`/`bal` do.
    # The historical forks' dormant values stay pinned by the `#guard`s in
    # `Jaune/Fork.lean`; per-fork historical extraction against the old EELS
    # modules is U10's per-fork generator extension.
    "op.shifts": "checked",
    "op.extCodeHash": "checked",
    "op.create2": "checked",
    "op.chainId": "checked",
    "op.selfBalance": "checked",
    "op.baseFee": "checked",
    "op.push0": "checked",
    "op.transient": "checked",
    "op.mcopy": "checked",
    "op.blobHash": "checked",
    "op.blobBaseFee": "checked",
    "header.baseFee": "checked",
    "header.withdrawalsRoot": "checked",
    "header.blobGas": "checked",
    "header.parentBeaconBlockRoot": "checked",
    "header.requestsHash": "checked",
    "access.shape": "checked",
    "access.balance": "checked",
    "access.extCode": "checked",
    "access.extCodeHash": "checked",
    "access.sload": "checked",
    "access.call": "checked",
    "sstore.netMetering": "checked",
    "sstore.stipendSentry": "checked",
    "settle.refundQuotient": "checked",
    "settle.selfdestructRefund": "checked",
    "settle.selfdestructOnlyCreated": "checked",
    "settle.touchedSweep": "checked",
    "settle.eraseEmptyOnModify": "checked",
    "txr.maxType": "checked",
    "txr.dataNonZero": "checked",
    "txr.calldataFloor": "checked",
    "txr.warmCoinbase": "checked",
    "creation.initCodeLimit": "checked",
    "creation.rejectEf": "checked",
    "pow.present": "checked",
    "pow.blockReward": "checked",
    "pow.bombDelay": "checked",
    "sys.beaconRoots": "checked",
    "sys.historyStorage": "checked",
    "bn254.add": "checked",
    "bn254.mul": "checked",
    "bn254.pairingBase": "checked",
    "bn254.pairingPerPair": "checked",
    "modexpComplexity": "checked",
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

def elsewhere_reason(path: str) -> str:
    return ELSEWHERE_REASON


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


def verify_descent(root: Path, entry: dict) -> None:
    """Refuse a target that does not descend from the fixture lanes' release.

    The fixture lanes and this target used to name one commit. Since goal
    devcon8-talk-v1 the target may run ahead of the release, but only along
    its history: `fixture_release_commit` must be an ancestor of the checkout.
    A shallow clone cannot answer that and is refused the same way.
    """
    release = entry.get("fixture_release_commit")
    if not release:
        fail("scripts/sources.json conformance_target has no fixture_release_commit")
    descent = git(root, "merge-base", "--is-ancestor", release, "HEAD")
    if descent.returncode != 0:
        fail(
            f"conformance-target checkout {root} does not descend from the "
            f"fixture release commit {release} (or is too shallow to show it); "
            "the target must not leave the fixture lanes' history"
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
    verify_descent(root, entry)
    python = root / entry["venv_subpath"] / "bin" / "python"
    if not python.exists():
        fail(
            f"{python} not found; create the target's venv with "
            f"`cd {root} && uv sync --no-default-groups --group test`"
        )
    return root, python, entry["commit"]


def probe(root: Path, python: Path, *args: str) -> dict:
    run = subprocess.run(
        [str(python), str(PROBE), *args],
        capture_output=True,
        text=True,
        cwd=str(root),
        env={"PYTHONPATH": str(SCRIPTS), "PATH": "/usr/bin:/bin"},
    )
    if run.returncode != 0:
        fail(f"constant probe failed in {root}:\n{run.stderr.strip()}")
    try:
        return json.loads(run.stdout)
    except json.JSONDecodeError as error:
        fail(f"constant probe emitted unreadable JSON: {error}")


# A cell is dormant for a fork when Jaune's literal carries a value that
# fork's rules never read: the first-activation carryover that keeps the
# `Valid` predicates well-formed (goal U10). Dormant cells are classified
# here, not compared by `check-fork-constants.sh`. Absence facts (`null`,
# `false`, `[]` on both sides, e.g. `stateGas.*` or `bal.*`) stay compared:
# they pin that the fork lacks the feature, exactly as the modern gate does.
_DORMANT_BLOB_PRE_CANCUN = (
    "no blob schedule before Cancun (EIP-4844); carries Prague's schedule "
    "so BlobSchedule.Valid holds"
)
_DORMANT_INITCODE_PRE_SHANGHAI = (
    "no initcode limit before Shanghai (EIP-3860); carries Prague's limit"
)
_DORMANT_PRE_PRAGUE = {
    "tx.maxGas": "no whole-transaction cap before Osaka (EIP-7825)",
    "tx.maxTotalGas": "no total-transaction cap before Amsterdam (EIP-8037)",
    "block.maxRlpSize": "no RLP envelope cap before Osaka (EIP-7934)",
    "gas.floorTokenCost": (
        "no calldata floor before Prague (EIP-7623); carries Prague's"
    ),
    "gas.perAuthIntrinsic": (
        "no EIP-7702 authorisations before Prague; carries Prague's"
    ),
}
_DORMANT_PRE_BERLIN = {
    "gas.coldAccountAccess": (
        "no warm/cold pricing before Berlin (EIP-2929); carries Prague's"
    ),
    "gas.txAccessListAddress": (
        "no access-list pricing before Berlin (EIP-2930); carries Prague's"
    ),
    "gas.txAccessListStorageKey": (
        "no access-list pricing before Berlin (EIP-2930); carries Prague's"
    ),
}
_DORMANT_BYZANTIUM_ONLY = {
    "access.extCodeHash": (
        "EXTCODEHASH (EIP-1052) is undefined at Byzantium; carries the "
        "Constantinople price so AccessPrices.Valid holds"
    ),
}
_DORMANT_FLAT_POST_BERLIN = (
    "EIP-2929 warm/cold pricing from Berlin; no flat prices to print"
)

_PRE_CANCUN_LABELS = (
    "Byzantium", "Petersburg", "Istanbul", "MuirGlacier", "Berlin",
    "London", "ArrowGlacier", "GrayGlacier", "Paris", "Shanghai",
)
_PRE_SHANGHAI_LABELS = (
    "Byzantium", "Petersburg", "Istanbul", "MuirGlacier", "Berlin",
    "London", "ArrowGlacier", "GrayGlacier", "Paris",
)
_PRE_BERLIN_LABELS = (
    "Byzantium", "Constantinople", "Petersburg", "Istanbul", "MuirGlacier",
)
_BERLIN_PLUS_LABELS = (
    "Berlin", "London", "ArrowGlacier", "GrayGlacier", "Paris",
    "Shanghai", "Cancun",
)
_HISTORICAL_LABELS = (
    "Byzantium", "Constantinople", "Petersburg", "Istanbul", "MuirGlacier",
    "Berlin", "London", "ArrowGlacier", "GrayGlacier", "Paris",
    "Shanghai", "Cancun",
)

_NO_MODULE_REASON = (
    "no EELS fork module carries EIP-1283 Constantinople (it never "
    "activated; mainnet went Byzantium straight to Petersburg): the literal "
    "is a record update of petersburgRules differing only in sstore, and is "
    "fixture-grounded by the legacy corpus, not by a module extraction"
)


def dormant_for(label: str) -> "dict[str, str]":
    """The classified dormant cells of one historical fork (goal U10)."""
    if label not in _HISTORICAL_LABELS:
        return {}
    dormant: dict[str, str] = dict(_DORMANT_PRE_PRAGUE)
    if label in _PRE_CANCUN_LABELS or label == "Constantinople":
        for field in (
            "blob.target", "blob.max", "blob.baseFeeUpdateFraction",
        ):
            dormant[field] = _DORMANT_BLOB_PRE_CANCUN
    if label in _PRE_SHANGHAI_LABELS or label == "Constantinople":
        dormant["code.maxInitCodeSize"] = _DORMANT_INITCODE_PRE_SHANGHAI
    if label in _PRE_BERLIN_LABELS:
        dormant.update(_DORMANT_PRE_BERLIN)
    if label == "Byzantium":
        dormant.update(_DORMANT_BYZANTIUM_ONLY)
    if label in _BERLIN_PLUS_LABELS:
        for field in (
            "access.balance", "access.extCode", "access.extCodeHash",
            "access.sload", "access.call",
        ):
            dormant[field] = _DORMANT_FLAT_POST_BERLIN
    if label == "Constantinople":
        for field in [f for f in COVERAGE if COVERAGE[f] == "checked"]:
            dormant.setdefault(field, _NO_MODULE_REASON)
    return dormant


def constantinople_entry() -> dict:
    """The fixture-only fork's entry: no module, every cell dormant.

    The generator knows nothing about Jaune, so there are no values to
    carry: every checked field is present with a `null` value and a dormant
    classification, which is exactly what keeps the coverage key set uniform
    and the comparison skipping it.
    """
    constants = {
        field: {"value": None, "source": _NO_MODULE_REASON}
        for field, status in COVERAGE.items()
        if status == "checked"
    }
    return {
        "label": "Constantinople",
        "module": None,
        "fork_criteria": {"kind": "NoModule", "timestamp": None},
        "header_field_count": None,
        "constants": constants,
    }


def build() -> dict:
    root, python, commit = target()
    forks = probe(root, python)
    historical = probe(root, python, "--historical")
    forks.update(historical)
    forks["Constantinople"] = constantinople_entry()
    # The mainnet schedule from Byzantium (goal jaune-historical-forks-v1,
    # design §4): every fork module's `FORK_CRITERIA`, compared by
    # `check-fork-constants.sh` against `jaune --mainnet-schedule` for every
    # declared fork, refused ones included -- the per-fork `mainnetActivation`
    # row covers only the forks `--rules` prints.
    mainnet_schedule = probe(root, python, "--schedule")

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
    elsewhere = {path for path, status in COVERAGE.items() if status == "elsewhere"}
    modexp_elsewhere = {
        "modexp.maxLength", "modexp.flatComplexity", "modexp.complexityCoeff",
        "modexp.iterationCoeff", "modexp.gasDivisor", "modexp.minGas",
    }
    if elsewhere != modexp_elsewhere:
        fail(
            "elsewhere keys with no assigned reason: "
            f"{sorted(elsewhere - modexp_elsewhere)}; "
            "extend elsewhere_reason"
        )

    # Goal U10: every historical fork carries its dormant classification.
    # A dormant key outside the checked set is a generator bug, not a quiet
    # skip, and a fork the table does not know stays fully compared.
    checked = {path for path, status in COVERAGE.items() if status == "checked"}
    for label in sorted(forks):
        dormant = dormant_for(label)
        unknown = sorted(set(dormant) - checked)
        if unknown:
            fail(
                f"dormant keys of {label} are outside the coverage table: "
                f"{unknown}"
            )
        forks[label]["dormant"] = dormant

    return {
        # 3: goal U10 adds the pre-Prague forks. Every fork entry carries a
        # `dormant` map (empty for the runnable forks): cells Jaune's literal
        # carries but the fork never reads, classified here and skipped by
        # the comparison. Constantinople has no EELS module, so its entry is
        # synthesised with every cell dormant.
        "schema_version": 3,
        "_comment": (
            "Generated by scripts/gen-fork-constants.py from the pinned "
            "conformance target. Never hand-edited: scripts/check-fork-constants.sh "
            "compares it against `lake exe jaune --rules <fork>` (runnable "
            "forks) and `lake exe jaune --rules-literal <fork>` (refused "
            "forks, dormant cells classified, not compared), and "
            "`--check` fails if this file is stale."
        ),
        "conformance_target_commit": commit,
        "coverage": {
            path: (
                {"status": status}
                if status == "checked"
                else {"status": status, "reason": elsewhere_reason(path)}
            )
            for path, status in sorted(COVERAGE.items())
        },
        "forks": forks,
        "mainnet_schedule": mainnet_schedule,
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
