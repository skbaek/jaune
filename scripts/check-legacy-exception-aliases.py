#!/usr/bin/env python3
"""Check `FixtureException.legacyAliases` against upstream's own renames.

The historical lane's legacy side runs the `legacytests` restoration tree
(ethereum/tests at 41404287), whose `expectException` values are retesteth
tokens (`TR_IntrinsicGas`, ...). `Jaune/FixtureException.lean` expands each
token to a canonical expectation through `legacyAliases`. This gate re-derives
that table from upstream instead of trusting it: the later ethereum/tests tree
under `execution-specs` carries the same tests with canonical identities, so
for every case of the restoration tree whose block expects a retesteth token,
the same test, case (`dNgNvN` indices) and block in the later tree names what
upstream renamed the token to. The later tree runs Cancun (and Prague) only,
so a case at another fork is paired with the later tree's Cancun case of the
same test and indices ("sibling" evidence) only when no same-fork pair exists
for that token.

It fails when
  - a table row has no attesting pair;
  - a pair contradicts a row (the token was renamed to a different
    expectation somewhere);
  - the table cannot be read between its BEGIN/END markers.
A token that upstream never converted has no pair at all (the later tree keeps
the test only under its LegacyTests tree, still spelled with the retesteth
token). Such a row is *definitional* and must be listed in DEFINITIONAL below,
with the reason, instead of being attested by a pair: the gate then requires the
canonical value to equal the listed one, requires every block that expects the
token to carry the marker the fixture itself uses for that cause, and fails the
moment an upstream pair appears (the pair then governs, and the listing is
stale). Goal U11c: `TR_RLP_WRONGVALUE`.

It reports, without failing, the restoration tree's retesteth tokens with no
row: a fixture expecting one fails at parse in the runner, which is where an
unattested token belongs (goal U11a).

Usage: scripts/check-legacy-exception-aliases.py [--old ROOT] [--new ROOT]
Needs no build and takes no lock; it reads two fixture trees and one source
file and writes nothing.
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Jaune" / "FixtureException.lean"
CANONICAL = ("TransactionException.", "BlockException.")

# Rows no upstream pair can attest, each with the canonical identity, the
# per-block fixture marker every block expecting the token must carry, and the
# reason. Anything not listed here must be attested by a pair.
DEFINITIONAL = {
    "TR_RLP_WRONGVALUE": {
        "canonical": "BlockException.RLP_STRUCTURES_ENCODING",
        "marker": ("hasBigInt", "true"),
        "reason": (
            "stTransactionTest/ValueOverflow{,Paris} send a legacy transaction whose "
            "value is a 33-byte integer (> 2**256-1) inside a well-formed block RLP; "
            "upstream ported only the transaction-test siblings "
            "(TransactionException.VALUE_OVERFLOW, tests/frontier/validation/"
            "test_transaction_rlp.py::test_field_overflow) and left these block tests "
            "unconverted (src/InvalidRLP/ConvertThisTestValueOverflowParis.txt). "
            "The pinned EELS rejects the block in rlp.decode_to(Block) at every fork "
            "(DecodingError on the transaction's U256 value), which is the class "
            "packages/testing/.../exceptions/block.py defines as "
            "RLP_STRUCTURES_ENCODING: the block's rlp encoding is valid but the "
            "ethereum structures in it are invalid."
        ),
    },
}

MARKERS = sorted({spec["marker"][0] for spec in DEFINITIONAL.values()})


def read_table(text: str) -> dict[str, str]:
    m = re.search(r"-- BEGIN legacyAliases.*?\n(.*?)-- END legacyAliases", text, re.S)
    if not m:
        raise SystemExit("HARNESS ERROR — legacy-aliases: no BEGIN/END legacyAliases block in "
                         f"{SOURCE}")
    rows = re.findall(r'\("([^"]+)",\s*"([^"]+)"\)', m.group(1))
    table: dict[str, str] = {}
    for tok, canon in rows:
        if tok in table:
            raise SystemExit(f"REGRESSION — legacy-aliases: duplicate row {tok}")
        table[tok] = canon
    return table


def case_key(name: str) -> tuple[str, str | None]:
    name = name.split("::")[-1]
    m = re.match(r"(.*)_(d\d+g\d+v\d+)_(\w+)$", name)
    if m:
        return m.group(1), m.group(2)
    m = re.match(r"(.*)-fork_(\w+)-(d\d+g\d+v\d+)$", name)
    if m:
        return m.group(1), m.group(3)
    m = re.match(r"(.*)_(\w+)$", name)
    return (m.group(1), None) if m else (name, None)


def load(path: Path):
    try:
        with open(path) as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--old", default=os.path.expanduser(
        os.environ.get("JAUNE_LEGACY_RESTORATION_ROOT", "~/legacytests-41404287")))
    ap.add_argument("--new", default=os.path.expanduser(
        "~/execution-specs/tests/fixtures/ethereum_tests"))
    args = ap.parse_args()
    table = read_table(SOURCE.read_text())

    same = collections.defaultdict(collections.Counter)
    sibling = collections.defaultdict(collections.Counter)
    seen = collections.Counter()
    marks = collections.defaultdict(collections.Counter)
    for tree in ("Cancun", "Constantinople"):
        old_root = Path(args.old) / tree / "BlockchainTests"
        if not old_root.is_dir():
            continue
        for dirpath, _, files in os.walk(old_root):
            for fname in files:
                if not fname.endswith(".json"):
                    continue
                op = Path(dirpath) / fname
                od = load(op)
                if not isinstance(od, dict):
                    continue
                nd = load(Path(args.new) / "BlockchainTests" / op.relative_to(old_root))
                ncases = {}
                if isinstance(nd, dict):
                    for k, c in nd.items():
                        ncases[(case_key(k), c.get("network"))] = c
                for k, c in od.items():
                    net = c.get("network")
                    key = case_key(k)
                    for i, b in enumerate(c.get("blocks", [])):
                        e = b.get("expectException")
                        if not e or e.startswith(CANONICAL):
                            continue
                        seen[e] += 1
                        for mk in MARKERS:
                            marks[e][(mk, b.get(mk))] += 1
                        nc = ncases.get((key, net))
                        target = same
                        if nc is None and net != "Cancun":
                            nc = ncases.get((key, "Cancun"))
                            target = sibling
                        if nc is not None and i < len(nc.get("blocks", [])):
                            ne = nc["blocks"][i].get("expectException")
                            if ne:
                                target[e][ne] += 1

    problems = []
    definitional = 0
    for tok in sorted(DEFINITIONAL):
        if tok not in table:
            problems.append(f"{tok}: listed in DEFINITIONAL but has no row in {SOURCE.name}")
    for tok, canon in sorted(table.items()):
        ev = same.get(tok) or sibling.get(tok)
        kind = "same-fork" if same.get(tok) else "sibling"
        if tok in DEFINITIONAL:
            spec = DEFINITIONAL[tok]
            if ev:
                problems.append(f"{tok}: upstream now has pairs {dict(ev)}; "
                                f"drop it from DEFINITIONAL and let the pair govern")
            elif canon != spec["canonical"]:
                problems.append(f"{tok}: the row says {canon!r}, the definitional listing "
                                f"says {spec['canonical']!r}")
            elif not seen[tok]:
                problems.append(f"{tok}: no block in the restoration tree expects it")
            else:
                mk, want = spec["marker"]
                bad = {k: v for k, v in marks[tok].items() if k != (mk, want)}
                if bad:
                    problems.append(f"{tok}: {sum(bad.values())} block(s) expecting it lack "
                                    f"the fixture marker {mk}={want!r}: {bad}")
                else:
                    definitional += 1
            continue
        if not ev:
            problems.append(f"{tok}: no pair in the two trees attests the row {canon!r}")
            continue
        other = {k: v for k, v in ev.items() if k != canon}
        if other:
            problems.append(f"{tok}: the row says {canon!r}, but {kind} pairs say {dict(ev)}")
    for tok, ev in sorted(same.items()):
        if tok in table and table[tok] not in ev:
            problems.append(f"{tok}: same-fork pairs {dict(ev)} contradict the row {table[tok]!r}")

    unmapped = sorted(t for t in seen if t not in table)
    for tok in unmapped:
        print(f"NOTE — legacy-aliases: {tok} ({seen[tok]} block(s)) has no row; "
              f"same-fork pairs {dict(same.get(tok, {}))}, sibling pairs {dict(sibling.get(tok, {}))}")
    if problems:
        for p in problems:
            print(f"  - {p}")
        print(f"REGRESSION — legacy-aliases: {len(problems)} row problem(s) in {SOURCE.name}")
        return 1
    print(f"OK — legacy-aliases: {len(table)} row(s), {len(table) - definitional} attested by "
          f"upstream's own rename (same-fork or Cancun-sibling pairs) and contradicted by none, "
          f"{definitional} definitional (no upstream pair; DEFINITIONAL); "
          f"{len(unmapped)} unmapped token(s) noted")
    return 0


if __name__ == "__main__":
    sys.exit(main())
