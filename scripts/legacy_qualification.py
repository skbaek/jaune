#!/usr/bin/env python3
"""CI qualification for the owner-amended legacy Prague delta.

The raw ``check-legacy.sh`` regression gate stays RED: it passes iff every
file's classification equals the tracked correctness baseline, and the owner
amendment (``scripts/GATES.md``) accepts exactly five stale Prague files
turning PASS->FAIL. This module adds the aggregate verdict on top without
touching the harness, the baseline, the fixtures, or ``scripts/sources.json``:

  1. strict classifier: the report population must equal the baseline
     population, and the only delta must be the exact owner-qualified set
     (2 files on smoke, 5 on full), with the raw harness exit still 1;
  2. live replay: the ten Prague cases in those five files are replayed
     against BOTH the current jaune binary and the manifest-pinned
     conformance EELS. No saved expected outputs are consulted.

Only the aggregate verdict is ever QUALIFIED, never all-PASS, and any
extra, missing, malformed, or duplicate classification -- or any exit other
than the raw 1 -- fails. There is no continue-on-error blanket and no new
exemption: the first replay mismatch fails the run.

Every run writes its evidence into a fresh output directory (refused when it
already exists) so a stale acceptance can never be re-read as a new one.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
ROOT = SCRIPTS_DIR.parent
sys.path.insert(0, str(SCRIPTS_DIR))
from conformance_reference import ReferenceError, verify_reference

# Exact baselines and delta accepted by the GATES.md owner amendment (2026-10-11).
# The baseline hashes pin the unchanged owner-reviewed baselines; changing a
# baseline byte fails here rather than qualifying something else.
BASELINE_HASHES = {
    "smoke": "1636865463a17055397da7752ebe62e75a988be7dcb8d85bde89ad3bc90c3755",
    "full": "3d2ed9a7d20c9beba1c908377a18319881f1772ce508b6264c4a8be3a4b598ef",
}
QUALIFIED_PATHS = {
    "GeneralStateTests/stCreate2/RevertInCreateInInitCreate2Paris.json",
    "GeneralStateTests/stCreate2/create2collisionStorageParis.json",
    "GeneralStateTests/stExtCodeHash/dynamicAccountOverwriteEmpty_Paris.json",
    "GeneralStateTests/stRevertTest/RevertInCreateInInit_Paris.json",
    "GeneralStateTests/stSStoreTest/InitCollisionParis.json",
}
# Per-file Prague case counts: 1 + 3 + 1 + 1 + 4 = 10.
FIXTURE_CASE_COUNTS = (
    ("GeneralStateTests/stCreate2/RevertInCreateInInitCreate2Paris.json", 1),
    ("GeneralStateTests/stCreate2/create2collisionStorageParis.json", 3),
    ("GeneralStateTests/stExtCodeHash/dynamicAccountOverwriteEmpty_Paris.json", 1),
    ("GeneralStateTests/stRevertTest/RevertInCreateInInit_Paris.json", 1),
    ("GeneralStateTests/stSStoreTest/InitCollisionParis.json", 4),
)
EXPECTED_PRAGUE_TOTAL = 10

QUALIFICATION_BOUNDARY = (
    "Not an all-PASS result; the retained ten-case pinned-EELS replay is a "
    "separate required condition."
)

# t8n output documents compared whole-document per case.
T8N_OUTPUTS = ("result.json", "alloc.json", "body.json")

# Exact legacy transaction fields the replay accepts. Anything else fails
# closed: an unknown field could carry value the normalizer would drop.
LEGACY_TX_FIELDS = frozenset(
    {"data", "gasLimit", "gasPrice", "nonce", "r", "s", "sender", "to", "v", "value"}
)


class QualificationError(ValueError):
    """A strict-classifier or replay refusal."""


def parse_rows(data: bytes, columns: int) -> dict[str, str]:
    """Parse STATUS rows into {path: status}, failing closed on any defect."""
    result: dict[str, str] = {}
    for line in data.decode().splitlines():
        fields = line.split("\t")
        if len(fields) != columns or fields[0] not in {"PASS", "FAIL"} or not fields[-1]:
            raise QualificationError("malformed classification row")
        if fields[-1] in result:
            raise QualificationError("duplicate fixture path")
        result[fields[-1]] = fields[0]
    if not result:
        raise QualificationError("empty classification population")
    return result


def qualify(tier: str, baseline: bytes, report: bytes, raw_exit: int) -> dict:
    """Exact strict classifier from the owner-reviewed draft.

    The verdict is QUALIFIED only for the exact owner-qualified delta with
    the raw harness still RED at exit 1. Anything else raises.
    """
    if hashlib.sha256(baseline).hexdigest() != BASELINE_HASHES[tier]:
        raise QualificationError("baseline is not the unchanged owner-reviewed baseline")
    before, after = parse_rows(baseline, 2), parse_rows(report, 3)
    if before.keys() != after.keys():
        raise QualificationError("report population differs from the complete baseline")
    expected = QUALIFIED_PATHS & before.keys()
    if len(expected) != {"smoke": 2, "full": 5}[tier]:
        raise QualificationError("qualified population mismatch")
    changes = {p: (before[p], after[p]) for p in before if before[p] != after[p]}
    if changes != {p: ("PASS", "FAIL") for p in expected}:
        raise QualificationError(
            "classification delta differs from the exact owner qualification"
        )
    if raw_exit != 1:
        raise QualificationError("raw harness must retain its RED exit1")
    return {
        "verdict": "QUALIFIED",
        "raw_verdict": "RED",
        "raw_exit": raw_exit,
        "files": len(after),
        "changes": dict(sorted(changes.items())),
        "boundary": QUALIFICATION_BOUNDARY,
    }


def _hex_int(value: object, label: str) -> int:
    if not isinstance(value, str) or not value.startswith("0x"):
        raise QualificationError(f"{label} is not a 0x-hex string: {value!r}")
    try:
        return int(value, 16)
    except ValueError as error:
        raise QualificationError(f"{label} is not a 0x-hex string: {value!r}") from error


@dataclass(frozen=True)
class CaseInputs:
    """One replayable Prague case extracted from a legacy fixture file."""

    fixture_rel: str
    case_key: str
    alloc: dict
    env: dict
    txs: list
    frozen_gas_used: str
    genesis_hash: str


def normalize_legacy_tx(tx: object) -> dict:
    """Spell one legacy signed transaction as t8n input without re-signing.

    Field renames only (``data`` -> ``input``, ``gasLimit`` -> ``gas``,
    empty ``to`` -> null, drop ``sender``, add ``type``/``chainId``). Every
    signed value -- ``v``, ``r``, ``s`` and all payload fields -- is
    preserved byte for byte; signature bytes are unchanged.
    """
    if not isinstance(tx, dict):
        raise QualificationError(f"transaction is not an object: {tx!r}")
    if set(tx) != LEGACY_TX_FIELDS:
        raise QualificationError(
            "transaction schema mismatch: expected exactly "
            f"{sorted(LEGACY_TX_FIELDS)}, got {sorted(tx)}"
        )
    for key in ("data", "gasLimit", "gasPrice", "nonce", "r", "s", "v", "value"):
        if not isinstance(tx[key], str) or not tx[key].startswith("0x"):
            raise QualificationError(f"transaction field {key} is not a 0x string")
    to = tx["to"]
    if not isinstance(to, str):
        raise QualificationError("transaction field to is not a string")
    return {
        "type": "0x0",
        "chainId": "0x1",
        "nonce": tx["nonce"],
        "gasPrice": tx["gasPrice"],
        "gas": tx["gasLimit"],
        "to": None if to == "" else to,
        "value": tx["value"],
        "input": tx["data"],
        "v": tx["v"],
        "r": tx["r"],
        "s": tx["s"],
    }


def build_t8n_env(block: dict, genesis: dict) -> dict:
    """Build the t8n env document from one block and the genesis header."""
    header = block.get("blockHeader")
    if not isinstance(header, dict):
        raise QualificationError("block has no blockHeader object")
    for key in (
        "coinbase",
        "gasLimit",
        "number",
        "timestamp",
        "mixHash",
        "baseFeePerGas",
        "excessBlobGas",
        "parentBeaconBlockRoot",
    ):
        if key not in header:
            raise QualificationError(f"blockHeader lacks required field {key}")
    withdrawals = block.get("withdrawals")
    if not isinstance(withdrawals, list):
        raise QualificationError("block withdrawals are not a list")
    genesis_number = genesis.get("number")
    genesis_hash = genesis.get("hash")
    if not isinstance(genesis_hash, str) or not genesis_hash.startswith("0x"):
        raise QualificationError("genesis header lacks a 0x hash")
    block_hashes = {hex(_hex_int(genesis_number, "genesis number")): genesis_hash}
    return {
        "currentCoinbase": header["coinbase"],
        "currentGasLimit": header["gasLimit"],
        "currentNumber": header["number"],
        "currentTimestamp": header["timestamp"],
        "currentRandom": header["mixHash"],
        "currentBaseFee": header["baseFeePerGas"],
        "currentExcessBlobGas": header["excessBlobGas"],
        "parentBeaconBlockRoot": header["parentBeaconBlockRoot"],
        "blockHashes": block_hashes,
        "withdrawals": withdrawals,
    }


def extract_prague_cases(fixture_rel: str, doc: object) -> list[CaseInputs]:
    """Extract and validate every Prague case in one fixture file.

    Fails closed on any schema mismatch: exactly one block, block number 1,
    genesis number 0, no uncles, empty withdrawals, chainid 1, one legacy
    signed transaction, Prague network, and the supported field schema.
    Alloc is the fixture ``pre`` taken directly.
    """
    if not isinstance(doc, dict) or not doc:
        raise QualificationError(f"{fixture_rel}: fixture is not a nonempty object")
    cases: list[CaseInputs] = []
    for case_key, case in doc.items():
        if not isinstance(case_key, str) or "-fork_Prague-" not in case_key:
            continue
        if not isinstance(case, dict):
            raise QualificationError(f"{fixture_rel}::{case_key}: case is not an object")
        if case.get("network") != "Prague":
            raise QualificationError(f"{fixture_rel}::{case_key}: network is not Prague")
        config = case.get("config")
        if not isinstance(config, dict) or config.get("chainid") != "0x01":
            raise QualificationError(f"{fixture_rel}::{case_key}: chainid is not 0x01")
        if case.get("sealEngine") != "NoProof":
            raise QualificationError(
                f"{fixture_rel}::{case_key}: sealEngine is not NoProof"
            )
        genesis = case.get("genesisBlockHeader")
        if not isinstance(genesis, dict):
            raise QualificationError(
                f"{fixture_rel}::{case_key}: missing genesisBlockHeader"
            )
        if _hex_int(genesis.get("number"), "genesis number") != 0:
            raise QualificationError(
                f"{fixture_rel}::{case_key}: genesis number is not 0"
            )
        blocks = case.get("blocks")
        if not isinstance(blocks, list) or len(blocks) != 1:
            raise QualificationError(
                f"{fixture_rel}::{case_key}: expected exactly one block"
            )
        block = blocks[0]
        if not isinstance(block, dict):
            raise QualificationError(f"{fixture_rel}::{case_key}: block is not an object")
        header = block.get("blockHeader")
        if not isinstance(header, dict) or _hex_int(
            header.get("number"), "block number"
        ) != 1:
            raise QualificationError(f"{fixture_rel}::{case_key}: block number is not 1")
        if block.get("uncleHeaders") != []:
            raise QualificationError(f"{fixture_rel}::{case_key}: uncles are not empty")
        if block.get("withdrawals") != []:
            raise QualificationError(
                f"{fixture_rel}::{case_key}: withdrawals are not empty"
            )
        txs = block.get("transactions")
        if not isinstance(txs, list) or len(txs) != 1:
            raise QualificationError(
                f"{fixture_rel}::{case_key}: expected one legacy signed transaction"
            )
        pre = case.get("pre")
        if not isinstance(pre, dict):
            raise QualificationError(f"{fixture_rel}::{case_key}: pre is not an object")
        frozen_gas = header.get("gasUsed")
        if not isinstance(frozen_gas, str) or not frozen_gas.startswith("0x"):
            raise QualificationError(
                f"{fixture_rel}::{case_key}: frozen gasUsed is not a 0x string"
            )
        cases.append(
            CaseInputs(
                fixture_rel=fixture_rel,
                case_key=case_key,
                alloc=pre,
                env=build_t8n_env(block, genesis),
                txs=[normalize_legacy_tx(txs[0])],
                frozen_gas_used=frozen_gas,
                genesis_hash=genesis["hash"],
            )
        )
    return cases


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def require_fresh_dir(path: Path) -> Path:
    """Create a directory that must not already exist (no stale acceptance)."""
    if os.path.lexists(path):
        raise QualificationError(f"output directory already exists: {path}")
    path.mkdir(parents=True)
    return path


def load_gen_goldens_module():
    """Import gen-t8n-goldens.py for its target paths, never for generation."""
    spec = importlib.util.spec_from_file_location(
        "jaune_gen_t8n_goldens", SCRIPTS_DIR / "gen-t8n-goldens.py"
    )
    if spec is None or spec.loader is None:
        raise QualificationError("cannot load scripts/gen-t8n-goldens.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    sys.path.insert(0, str(SCRIPTS_DIR))
    try:
        spec.loader.exec_module(module)
    finally:
        with contextlib.suppress(ValueError):
            sys.path.remove(str(SCRIPTS_DIR))
    return module


def resolve_conformance_target() -> tuple[Path, Path, str]:
    """Return the (t8n, python, commit) of the manifest-pinned EELS target.

    Reuses ``target_paths`` (which verifies the checkout revision) via
    importlib; nothing here generates goldens.
    """
    module = load_gen_goldens_module()
    return module.target_paths()


def _git(repo: Path, *args: str) -> str:
    try:
        run = subprocess.run(
            ["git", "-C", str(repo), *args],
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as error:
        raise QualificationError(f"cannot execute git: {error}") from error
    if run.returncode != 0:
        raise QualificationError(
            f"git {' '.join(args)} failed in {repo}: "
            f"{run.stderr.strip() or run.stdout.strip() or 'no diagnostic'}"
        )
    return run.stdout.strip()


def verify_fixture_provenance(fixtures_root: Path, manifest: dict) -> dict:
    """Check the five fixture files against the pinned ethereum_tests commit.

    The fixtures root must be the ``BlockchainTests`` directory of the nested
    ethereum/tests checkout; its HEAD must equal the manifest pin, and every
    fixture file's bytes must hash (``git hash-object``) to the blob committed
    at that revision. Returns per-file blob hashes for the evidence record.
    """
    try:
        eth_commit = manifest["ethereum_tests"]["commit"]
    except KeyError as error:
        raise QualificationError(f"sources.json lacks ethereum_tests field: {error}")
    if fixtures_root.name != "BlockchainTests":
        raise QualificationError(
            f"fixtures root is not a BlockchainTests directory: {fixtures_root}"
        )
    eth_root = fixtures_root.parent
    head = _git(eth_root, "rev-parse", "HEAD")
    if head != eth_commit:
        raise QualificationError(
            f"ethereum/tests checkout is at {head}, not the manifest pin {eth_commit}"
        )
    if _git(eth_root, "status", "--porcelain"):
        raise QualificationError(
            f"ethereum/tests checkout {eth_root} has uncommitted changes"
        )
    blobs: dict[str, str] = {}
    for rel in QUALIFIED_PATHS:
        blob_rel = f"BlockchainTests/{rel}"
        committed = _git(eth_root, "rev-parse", f"HEAD:{blob_rel}")
        working = _git(eth_root, "hash-object", str(fixtures_root / rel))
        if working != committed:
            raise QualificationError(
                f"{rel}: working bytes {working} differ from the committed "
                f"blob {committed} at {eth_commit}"
            )
        blobs[rel] = committed
    return {"ethereum_tests_commit": eth_commit, "blobs": blobs}


@dataclass
class ToolRun:
    argv: list[str]
    exit: int
    stdout: str = ""
    stderr: str = ""


def run_command(argv: list[str]) -> ToolRun:
    run = subprocess.run(argv, capture_output=True, text=True, check=False)
    return ToolRun(
        argv=argv, exit=run.returncode, stdout=run.stdout, stderr=run.stderr
    )


INPUT_FILES = ("alloc.json", "env.json", "txs.json")


def write_shared_inputs(case_inputs: CaseInputs, work_dir: Path) -> dict[str, str]:
    """Write the one shared input triple both tools read; hash the actual files."""
    if os.path.lexists(work_dir):
        raise QualificationError(f"input directory is not fresh: {work_dir}")
    work_dir.mkdir(parents=True)
    docs = {
        "alloc.json": case_inputs.alloc,
        "env.json": case_inputs.env,
        "txs.json": case_inputs.txs,
    }
    digests: dict[str, str] = {}
    for name in INPUT_FILES:
        path = work_dir / name
        path.write_text(json.dumps(docs[name], indent=2) + "\n")
        digests[name] = sha256_file(path)
    return digests


def run_t8n(
    binary: Path,
    case_key: str,
    work_dir: Path,
    out_dir: Path,
    reward: str = "-1",
    runner=run_command,
) -> ToolRun:
    """Run one t8n tool on the shared input triple; nonzero exits fail."""
    missing = [name for name in INPUT_FILES if not (work_dir / name).is_file()]
    if missing:
        raise QualificationError(
            f"{case_key}: shared inputs missing {', '.join(missing)}; "
            "both tools read one triple written once"
        )
    if os.path.lexists(out_dir):
        raise QualificationError(f"tool output directory is not fresh: {out_dir}")
    out_dir.mkdir(parents=True)
    argv = [
        str(binary),
        "t8n",
        f"--input.alloc={work_dir / 'alloc.json'}",
        f"--input.env={work_dir / 'env.json'}",
        f"--input.txs={work_dir / 'txs.json'}",
        "--output.result=result.json",
        "--output.alloc=alloc.json",
        "--output.body=body.json",
        "--state.fork=Prague",
        "--state.chainid=1",
        f"--state.reward={reward}",
        f"--output.basedir={out_dir}",
    ]
    result = runner(argv)
    (out_dir / "stdout.log").write_text(result.stdout)
    (out_dir / "stderr.log").write_text(result.stderr)
    (out_dir / "command.json").write_text(json.dumps(
        {"argv": result.argv, "exit": result.exit}, indent=2) + "\n")
    if result.exit != 0:
        raise QualificationError(
            f"{case_key}: {binary} exited {result.exit}: "
            f"{result.stderr.strip()[-2000:]}"
        )
    missing = [name for name in T8N_OUTPUTS if not (out_dir / name).is_file()]
    if missing:
        raise QualificationError(
            f"{case_key}: {binary} wrote no {', '.join(missing)} "
            f"(exit {result.exit}); partial output is not compared"
        )
    return result


def compare_case_outputs(
    case_key: str, jaune_dir: Path, ref_dir: Path
) -> dict[str, str]:
    """Compare whole result/body/alloc documents; any mismatch fails."""
    digests: dict[str, str] = {}
    for name in T8N_OUTPUTS:
        try:
            jaune_doc = json.loads((jaune_dir / name).read_text())
        except (OSError, json.JSONDecodeError) as error:
            raise QualificationError(
                f"{case_key}: cannot read jaune {name}: {error}"
            ) from error
        try:
            ref_doc = json.loads((ref_dir / name).read_text())
        except (OSError, json.JSONDecodeError) as error:
            raise QualificationError(
                f"{case_key}: cannot read reference {name}: {error}"
            ) from error
        if jaune_doc != ref_doc:
            raise QualificationError(
                f"{case_key}: {name} differs between jaune and the pinned EELS"
            )
        digests[f"jaune_{name}"] = sha256_file(jaune_dir / name)
        digests[f"ref_{name}"] = sha256_file(ref_dir / name)
    return digests


def reference_gas_used(result_doc: object) -> str:
    """Extract the reference result's top-level gasUsed, failing closed otherwise.

    The t8n result specifies gasUsed as a top-level field. No value is ever
    inferred from receipts or other nested fields.
    """
    if isinstance(result_doc, dict) and isinstance(result_doc.get("gasUsed"), str):
        return result_doc["gasUsed"]
    raise QualificationError(
        "reference result has no top-level gasUsed for the divergence check"
    )


def assert_gas_divergence(case_key: str, ref_dir: Path, frozen_gas_used: str) -> str:
    """Require the reference gasUsed to differ from the frozen header value.

    The amendment's claim is that the old header gas values disagree with the
    live replay; a replay that reproduced the frozen value would prove nothing.
    """
    try:
        ref_doc = json.loads((ref_dir / "result.json").read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise QualificationError(
            f"{case_key}: cannot read reference result.json: {error}"
        ) from error
    live = reference_gas_used(ref_doc)
    if _hex_int(live, "reference gasUsed") == _hex_int(frozen_gas_used, "frozen gasUsed"):
        raise QualificationError(
            f"{case_key}: reference gasUsed {live} reproduces the frozen header; "
            "the replay is vacuous"
        )
    return live


@dataclass
class ReplayEvidence:
    case_key: str
    fixture_rel: str
    input_files: dict[str, str]
    fixture_sha256: str
    jaune_argv: list[str]
    jaune_exit: int
    jaune_stdout: str
    jaune_stderr: str
    ref_argv: list[str]
    ref_exit: int
    ref_stdout: str
    ref_stderr: str
    output_digests: dict[str, str] = field(default_factory=dict)
    live_gas_used: str = ""


def replay_case(
    case_inputs: CaseInputs,
    fixture_sha256: str,
    jaune_bin: Path,
    ref_t8n: Path,
    case_dir: Path,
    reward: str = "-1",
    runner=run_command,
) -> ReplayEvidence:
    """Replay one case: one shared triple read by both tools, compared whole."""
    if os.path.lexists(case_dir):
        raise QualificationError(f"case directory is not fresh: {case_dir}")
    case_dir.mkdir(parents=True)
    work = case_dir / "work"
    out_jaune = case_dir / "out-jaune"
    out_ref = case_dir / "out-ref"
    input_files = write_shared_inputs(case_inputs, work)
    jaune_run = run_t8n(
        jaune_bin, case_inputs.case_key, work, out_jaune, reward, runner
    )
    ref_run = run_t8n(ref_t8n, case_inputs.case_key, work, out_ref, reward, runner)
    digests = compare_case_outputs(case_inputs.case_key, out_jaune, out_ref)
    live_gas = assert_gas_divergence(
        case_inputs.case_key, out_ref, case_inputs.frozen_gas_used
    )
    return ReplayEvidence(
        case_key=case_inputs.case_key,
        fixture_rel=case_inputs.fixture_rel,
        input_files=input_files,
        fixture_sha256=fixture_sha256,
        jaune_argv=jaune_run.argv,
        jaune_exit=jaune_run.exit,
        jaune_stdout=jaune_run.stdout,
        jaune_stderr=jaune_run.stderr,
        ref_argv=ref_run.argv,
        ref_exit=ref_run.exit,
        ref_stdout=ref_run.stdout,
        ref_stderr=ref_run.stderr,
        output_digests=digests,
        live_gas_used=live_gas,
    )


def record_candidate_provenance(repo_root: Path) -> dict[str, str]:
    """Record the candidate checkout's git HEAD and tracked source-diff digest."""
    if Path(_git(repo_root, "rev-parse", "--show-toplevel")).resolve() != repo_root.resolve():
        raise QualificationError("candidate root is not the Git checkout root")
    head = _git(repo_root, "rev-parse", "HEAD")
    try:
        diff = subprocess.run(
            ["git", "-C", str(repo_root), "diff", "HEAD", "--"],
            capture_output=True,
            check=False,
        )
    except OSError as error:
        raise QualificationError(f"cannot execute git: {error}") from error
    if diff.returncode != 0:
        raise QualificationError(
            f"git diff HEAD failed in {repo_root}: "
            f"{diff.stderr.decode().strip() or 'no diagnostic'}"
        )
    return {"head": head, "tracked_diff_sha256": sha256_bytes(diff.stdout)}


def read_reference_head(ref_t8n: Path) -> tuple[str, str]:
    """Return the (checkout root, git HEAD) holding the reference t8n binary.

    The binary lives at <root>/.venv/bin/<command> per the manifest layout,
    so the root is two levels above its parent directory.
    """
    root = ref_t8n.parents[2]
    if not os.path.lexists(root / ".git"):
        raise QualificationError(
            f"reference checkout has no git state at {root}"
        )
    return str(root), _git(root, "rev-parse", "HEAD")


def collect_prague_cases(fixtures_root: Path) -> list[tuple[CaseInputs, str]]:
    """Extract all ten Prague cases in fixture order with file hashes."""
    collected: list[tuple[CaseInputs, str]] = []
    for rel, expected_count in FIXTURE_CASE_COUNTS:
        path = fixtures_root / rel
        try:
            raw = path.read_bytes()
            doc = json.loads(raw.decode())
        except (OSError, json.JSONDecodeError) as error:
            raise QualificationError(f"{rel}: cannot read fixture: {error}") from error
        cases = extract_prague_cases(rel, doc)
        if len(cases) != expected_count:
            raise QualificationError(
                f"{rel}: expected {expected_count} Prague case(s), found {len(cases)}"
            )
        file_hash = sha256_bytes(raw)
        collected.extend((case, file_hash) for case in cases)
    if len(collected) != EXPECTED_PRAGUE_TOTAL:
        raise QualificationError(
            f"expected {EXPECTED_PRAGUE_TOTAL} Prague cases, found {len(collected)}"
        )
    return collected


def run_qualification(
    tier: str,
    baseline: bytes,
    report: bytes,
    raw_exit: int,
    fixtures_root: Path,
    jaune_bin: Path,
    ref_t8n: Path,
    reference_commit: str,
    output_dir: Path,
    manifest: dict,
    reward: str = "-1",
    runner=run_command,
    reference_identity: dict | None = None,
) -> dict:
    """Strict-classify, live-replay all ten cases, and write JSON evidence."""
    verdict = qualify(tier, baseline, report, raw_exit)
    if not jaune_bin.is_file():
        raise QualificationError(f"jaune binary not found: {jaune_bin}")
    candidate = record_candidate_provenance(ROOT)
    provenance = verify_fixture_provenance(fixtures_root, manifest)
    collected = collect_prague_cases(fixtures_root)
    ref_root, ref_head = read_reference_head(ref_t8n)
    require_fresh_dir(output_dir)
    runs_dir = output_dir / "runs"
    runs_dir.mkdir()
    replays: list[dict] = []
    for index, (case_inputs, file_hash) in enumerate(collected):
        case_dir = runs_dir / f"{index:02d}"
        evidence = replay_case(
            case_inputs, file_hash, jaune_bin, ref_t8n, case_dir, reward, runner
        )
        replays.append(
            {
                "case": evidence.case_key,
                "fixture": evidence.fixture_rel,
                "fixture_sha256": evidence.fixture_sha256,
                "input_files": evidence.input_files,
                "jaune_argv": evidence.jaune_argv,
                "jaune_exit": evidence.jaune_exit,
                "jaune_stdout": evidence.jaune_stdout,
                "jaune_stderr": evidence.jaune_stderr,
                "ref_argv": evidence.ref_argv,
                "ref_exit": evidence.ref_exit,
                "ref_stdout": evidence.ref_stdout,
                "ref_stderr": evidence.ref_stderr,
                "output_digests": evidence.output_digests,
                "frozen_gas_used": case_inputs.frozen_gas_used,
                "live_gas_used": evidence.live_gas_used,
            }
        )
    record = {
        **verdict,
        "tier": tier,
        "candidate_head": candidate["head"],
        "qualifier_sha256": sha256_file(Path(__file__)),
        "candidate_tracked_diff_sha256": candidate["tracked_diff_sha256"],
        "reference_root": ref_root,
        "reference_head": ref_head,
        "reference_pin": reference_commit,
        "ethereum_tests_commit": provenance["ethereum_tests_commit"],
        "fixture_blobs": provenance["blobs"],
        "jaune_binary": str(jaune_bin),
        "jaune_binary_sha256": sha256_file(jaune_bin),
        "replays": replays,
    }
    if reference_identity is not None:
        record["reference_identity"] = reference_identity
    (output_dir / "evidence.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tier", choices=sorted(BASELINE_HASHES), required=True)
    parser.add_argument("--raw-exit", type=int, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, default=None)
    parser.add_argument("--fixtures", type=Path, required=True)
    parser.add_argument("--jaune-bin", type=Path, default=None)
    parser.add_argument("--output", type=Path, required=True)
    return parser


def load_manifest() -> dict:
    """Load the canonical manifest; target_paths reads this same file."""
    try:
        return json.loads((SCRIPTS_DIR / "sources.json").read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise QualificationError(f"cannot read scripts/sources.json: {error}") from error


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    baseline_path = args.baseline or (SCRIPTS_DIR / f"baseline-{args.tier}.txt")
    jaune_bin = args.jaune_bin or (ROOT / ".lake" / "build" / "bin" / "jaune")
    try:
        manifest = load_manifest()
        baseline = baseline_path.read_bytes()
        report = args.report.read_bytes()
        ref_t8n, _, reference_commit = resolve_conformance_target()
        reference_identity = verify_reference(ref_t8n.parents[2], manifest["conformance_target"], SCRIPTS_DIR)
        record = run_qualification(
            args.tier,
            baseline,
            report,
            args.raw_exit,
            args.fixtures,
            jaune_bin,
            ref_t8n,
            reference_commit,
            args.output,
            manifest,
            reference_identity=reference_identity,
        )
    except (QualificationError, ReferenceError, OSError) as error:
        print(json.dumps({"verdict": "REJECTED", "detail": str(error)}))
        return 1
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
