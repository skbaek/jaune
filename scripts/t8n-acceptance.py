#!/usr/bin/env python3
"""Three-way `t8n` agreement over the `check-t8n.sh` corpus.

Sends every case in `scripts/t8n/cases/` to three transition tools -- Jaune,
the pinned conformance target, and one further tool -- and reports agreement
field by field. This is the goal's G12 evidence; it is *not* a gate, because
it needs two external tools that `scripts/check-t8n.sh` deliberately does not.

Agreement is checked on **semantic content**, not on bytes. The three tools
spell the same values differently on purpose:

  * numbers -- minimal, zero-padded, and full-width hex all appear, so every
    quantity is compared as an integer;
  * `alloc` -- key order differs, and a tool may omit a zero `nonce` or an
    empty `code`, so accounts are compared field by field with defaults
    applied;
  * `receipts` -- geth carries `contractAddress`, `blockHash`,
    `transactionIndex` and friends that the other two do not, so only the
    fields all three define are compared, and `logs: null` reads as `[]`;
  * `rejected[].error` and `blockException` -- free text with no normative
    content, mapped rather than compared by the framework that consumes them.
    What is compared is the *set of rejected indices* and the presence of a
    block exception. The texts are printed so a reader can see all three.

Usage:
  python3 scripts/t8n-acceptance.py --third <path-to-evm> [--third-name geth]
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
CASES = SCRIPTS / "t8n" / "cases"
SOURCES = SCRIPTS / "sources.json"
DIVERGENCES = SCRIPTS / "t8n" / "acceptance-divergences.json"
ROOT = SCRIPTS.parent

RESULT_SCALARS = [
    "stateRoot",
    "txRoot",
    "receiptsRoot",
    "logsHash",
    "logsBloom",
    "gasUsed",
    "currentBaseFee",
    "withdrawalsRoot",
    "currentExcessBlobGas",
    "blobGasUsed",
    "requestsHash",
]

def fail(message: str) -> "NoReturn":  # type: ignore[valid-type]
    print(f"error: {message}", file=sys.stderr)
    raise SystemExit(2)


def num(value):
    """Any hex quantity, as an integer. `None` stays `None`."""
    if value is None:
        return None
    if isinstance(value, int):
        return value
    return int(value, 16)


def canonical_result(raw):
    """The part of a `result` all three tools define, spelled one way."""
    out = {k: (num(raw[k]) if k in raw and raw[k] is not None else None)
           for k in RESULT_SCALARS}
    out["requests"] = [r.lower() for r in (raw.get("requests") or [])]
    receipts = []
    for r in raw.get("receipts") or []:
        bloom = r.get("bloom", r.get("logsBloom"))
        logs = []
        for log in r.get("logs") or []:
            logs.append(
                (
                    log["address"].lower(),
                    tuple(t.lower() for t in (log.get("topics") or [])),
                    (log.get("data") or "0x").lower(),
                )
            )
        receipts.append(
            (
                r["transactionHash"].lower(),
                num(r.get("status")),
                num(r.get("cumulativeGasUsed")),
                num(bloom),
                tuple(logs),
            )
        )
    out["receipts"] = receipts
    out["rejectedIndices"] = sorted(
        num(r["index"]) for r in (raw.get("rejected") or [])
    )
    out["hasBlockException"] = raw.get("blockException") is not None
    return out


def canonical_alloc(raw):
    """Post-state accounts, with each tool's omissions filled in."""
    out = {}
    for address, account in raw.items():
        storage = {
            int(k, 16): int(v, 16)
            for k, v in (account.get("storage") or {}).items()
            if int(v, 16) != 0
        }
        out[address.lower()] = (
            num(account.get("nonce")) or 0,
            num(account.get("balance")) or 0,
            (account.get("code") or "0x").lower(),
            tuple(sorted(storage.items())),
        )
    return out


def target_tool():
    entry = json.loads(SOURCES.read_text())["conformance_target"]
    root = Path(
        os.environ.get(
            entry["default_env_var"],
            Path.home() / entry["default_subpath_from_home"],
        )
    )
    binary = root / entry["venv_subpath"] / "bin" / entry["t8n_command"]
    if not binary.exists():
        fail(f"conformance target not found at {binary}")
    head = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"],
        capture_output=True,
        text=True,
    )
    return binary, head.stdout.strip(), entry["commit"]


def run(binary, subcommand, case, work, spec):
    """One tool, one case. Blockchain mode only -- see the caller."""
    args = [str(binary)]
    if subcommand:
        args.append(subcommand)
    args += [
        f"--input.alloc={case / 'alloc.json'}",
        f"--input.env={case / 'env.json'}",
        f"--input.txs={case / 'txs.json'}",
        "--output.result=result.json",
        "--output.alloc=alloc.json",
        f"--state.fork={spec['fork']}",
        f"--state.chainid={spec['chainid']}",
        f"--state.reward={spec['reward']}",
        f"--output.basedir={work}",
    ]
    return subprocess.run(args, capture_output=True, text=True)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--third", required=True, help="path to the third tool")
    parser.add_argument("--third-name", default="third")
    parser.add_argument("--third-version", default="")
    options = parser.parse_args()

    jaune = ROOT / ".lake" / "build" / "bin" / "jaune"
    if not jaune.exists():
        fail(f"no jaune binary at {jaune}; run `lake build`")
    target, target_head, target_pin = target_tool()
    third = Path(options.third)
    if not third.exists():
        fail(f"third tool not found at {third}")

    print("sides:")
    print(f"  jaune   {jaune}")
    print(f"          {subprocess.run([str(jaune), '-v'], capture_output=True, text=True).stdout.strip()}")
    print(f"  target  {target}")
    print(f"          execution-specs {target_head} (pinned {target_pin})")
    print(f"  {options.third_name:<7} {third}")
    version = options.third_version or subprocess.run(
        [str(third), "-v"], capture_output=True, text=True
    ).stdout.strip()
    print(f"          {version}")
    print()

    registry = {}
    for entry in json.loads(DIVERGENCES.read_text())["divergences"]:
        registry[entry["case"]] = set(entry["fields"])

    names = sorted(p.name for p in CASES.iterdir() if p.is_dir())
    disagreements = []
    registered = 0
    for name in names:
        case = CASES / name
        spec = json.loads((case / "case.json").read_text())
        # Only the blockchain mode is three-way comparable: `--state-test` is
        # this target's flag and the third tool has no equivalent.
        if spec["mode"] != "blockchain":
            print(f"{name}: SKIPPED (state-test mode is not a three-way surface)")
            continue
        results, allocs, texts = {}, {}, {}
        with tempfile.TemporaryDirectory() as tmp:
            for label, binary, subcommand in (
                ("jaune", jaune, "t8n"),
                ("target", target, "t8n"),
                (options.third_name, third, "t8n"),
            ):
                work = Path(tmp) / label
                work.mkdir()
                completed = run(binary, subcommand, case, work, spec)
                if completed.returncode != 0:
                    detail = (
                        f"{label} exited {completed.returncode}: "
                        f"{(completed.stderr.strip() or completed.stdout.strip())[:400]}"
                    )
                    if "*" in registry.get(name, set()):
                        registered += 1
                        print(f"{name}: REGISTERED DIVERGENCE — {detail}")
                    else:
                        disagreements.append(f"{name}: {detail}")
                    break
                raw_result = json.loads((work / "result.json").read_text())
                results[label] = canonical_result(raw_result)
                allocs[label] = canonical_alloc(
                    json.loads((work / "alloc.json").read_text())
                )
                texts[label] = (
                    [r.get("error") for r in (raw_result.get("rejected") or [])],
                    raw_result.get("blockException"),
                )
        if len(results) != 3:
            continue
        labels = list(results)
        fields = RESULT_SCALARS + [
            "requests",
            "receipts",
            "rejectedIndices",
            "hasBlockException",
        ]
        bad = []
        for field in fields:
            values = {label: results[label][field] for label in labels}
            if len(set(map(repr, values.values()))) != 1:
                bad.append((field, values))
        alloc_values = {
            label: tuple(sorted(allocs[label].items())) for label in labels
        }
        if len({repr(v) for v in alloc_values.values()}) != 1:
            differing = set()
            for label in labels:
                for address, account in allocs[label].items():
                    if any(
                        allocs[other].get(address) != account for other in labels
                    ):
                        differing.add(address)
            bad.append(
                (
                    "alloc",
                    {
                        label: {a: allocs[label].get(a) for a in sorted(differing)}
                        for label in labels
                    },
                )
            )
        if bad:
            allowed = registry.get(name, set())
            unregistered = [f for f, _ in bad if f not in allowed]
            label_word = "DISAGREE" if unregistered else "REGISTERED DIVERGENCE"
            print(f"{name}: {label_word} on {[b[0] for b in bad]}")
            for field, values in bad:
                for label, value in values.items():
                    print(f"    {field:<22} {label:<8} {str(value)[:160]}")
            if unregistered:
                disagreements.append(f"{name}: unregistered {unregistered}")
            else:
                registered += 1
        else:
            print(f"{name}: AGREE on {len(fields)} result fields and the post-state")
        for label in labels:
            rejected, exception = texts[label]
            if rejected or exception:
                print(f"    text {label:<8} rejected={rejected} blockException={exception}")

    compared = len(
        [
            n
            for n in names
            if json.loads((CASES / n / "case.json").read_text())["mode"]
            == "blockchain"
        ]
    )
    print()
    if disagreements:
        for item in disagreements:
            print(f"T8N-ACCEPTANCE — {item}")
        print(
            f"RED — t8n acceptance: {len(disagreements)} unregistered "
            f"disagreement(s) over {compared} blockchain-mode case(s)"
        )
        return 1
    print(
        f"OK — t8n acceptance: {compared} blockchain-mode case(s) compared "
        f"three ways; {compared - registered} unanimous and {registered} with "
        f"registered divergences, and jaune agrees with the conformance target "
        f"in every one"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
