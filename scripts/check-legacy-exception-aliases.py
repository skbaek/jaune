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
same test and indices ("sibling" evidence) only when that case has no
same-fork pair.

It fails when
  - a table row has no agreeing pair (an explained pair attests nothing);
  - a pair of either kind contradicts a row: a same-fork pair naming another
    expectation, or a Cancun-sibling pair whose different reason no fork
    difference explains (U11d: sibling pairs are judged too, never shadowed by
    same-fork agreement; a sibling naming a post-merge identity for a
    pre-Paris case, or the fee-market identity for a pre-London case, is
    explained, and one whose set contains the row's is a widening);
  - a row's target names a token the vocabulary does not parse (the
    `toString` and `ofString?` arms of the source, read here; U11d);
  - the table or the vocabulary cannot be read.
The verdict counts the rows attested by sibling pairs only: such a row rests
on the Cancun rename of the same case, not on a same-fork rename.
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


# The restoration tree's network labels in activation order, for judging a
# Cancun-sibling pair: a case's own fork decides which rules the Cancun run
# applies that the case's run did not. A label missing here explains nothing.
NETWORK_ORDER = [
    "Frontier", "Homestead", "EIP150", "EIP158", "Byzantium", "Constantinople",
    "ConstantinopleFix", "Istanbul", "MuirGlacier", "Berlin", "London",
    "ArrowGlacier", "GrayGlacier", "Paris", "Shanghai", "Cancun", "Prague",
]
# Identities only a post-merge block import can produce: a pre-Paris block
# carrying ommers or a nonzero difficulty is rejected for them at Cancun before
# the rule its own fork's case tests (EELS validate_header, paris on).
POST_MERGE = {"BlockException.IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS",
              "BlockException.IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS"}
# The fee-market identity: a pre-London transaction whose gas price is below
# the Cancun base fee is rejected for it first (EELS london check_transaction).
FEE_MARKET = "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS"


def sibling_verdict(canon: str, ne: str, net: str) -> str | None:
    """"agree" when the sibling names the row's expectation, or one member of a
    set-valued row (the row then needs every member attested, see `main`); a
    named fork explanation when the sibling's reason is one Cancun applies
    first and the case's own fork lacks; "widened" when the sibling's set
    contains the row's; None (a contradiction) otherwise."""
    want, got = set(canon.split("|")), set(ne.split("|"))
    if got <= want:
        return "agree"
    if want <= got:
        return "widened"
    if net not in NETWORK_ORDER:
        return None
    pos = NETWORK_ORDER.index(net)
    if got & POST_MERGE and pos < NETWORK_ORDER.index("Paris"):
        return "pre-Paris"
    if FEE_MARKET in got and pos < NETWORK_ORDER.index("London"):
        return "pre-London"
    return None


def read_vocabulary(text: str) -> set[str]:
    """The canonical spellings `FixtureException.ofString?` accepts: every
    `toString` arm's token and every extra `ofString?` arm's literal."""
    m = re.search(r"def toString : FixtureException → String\n(.*?)\ninstance", text, re.S)
    o = re.search(r"def ofString\? \(s : String\) : Option FixtureException :=\n(.*?)\n  \| _ =>", text, re.S)
    if not m or not o:
        raise SystemExit("HARNESS ERROR — legacy-aliases: cannot read toString/ofString? in "
                         f"{SOURCE}")
    vocab = set(re.findall(r'=> *\n? *"((?:Transaction|Block)Exception\.[A-Z0-9_]+)"', m.group(1)))
    vocab |= set(re.findall(r'\| "((?:Transaction|Block)Exception\.[A-Z0-9_]+)" =>', o.group(1)))
    if not vocab:
        raise SystemExit("HARNESS ERROR — legacy-aliases: empty vocabulary read from "
                         f"{SOURCE}")
    return vocab


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
    sibling_nets = collections.defaultdict(collections.Counter)
    seen = collections.Counter()
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
                        nc = ncases.get((key, net))
                        target = same
                        if nc is None and net != "Cancun":
                            nc = ncases.get((key, "Cancun"))
                            target = sibling
                        if nc is not None and i < len(nc.get("blocks", [])):
                            ne = nc["blocks"][i].get("expectException")
                            if ne:
                                target[e][ne] += 1
                                if target is sibling:
                                    sibling_nets[e][(ne, net)] += 1

    vocab = read_vocabulary(SOURCE.read_text())
    problems = []
    kinds = collections.Counter()
    explained = collections.Counter()
    for tok, canon in sorted(table.items()):
        # Review U11a #1 (fixed in U11d): every pair of either kind is judged.
        # A same-fork pair must name the row's expectation. A Cancun-sibling
        # pair names the reason the *Cancun* run of the case rejects for, which
        # may legitimately differ when the case's own fork predates a rule
        # Cancun applies first (`sibling_verdict`); any other disagreement is a
        # contradiction, and same-fork agreement never shadows it. A row is
        # attested only by agreeing pairs, never by explained ones.
        # A set-valued row (a token upstream split across blocks, each block
        # renamed to one reason) agrees with a pair naming a subset of it, and
        # is attested only when the agreeing pairs together name every member.
        want = set(canon.split("|"))
        named: set[str] = set()
        agree_same = 0
        for ne, n in same.get(tok, {}).items():
            if ne == canon or set(ne.split("|")) <= want:
                agree_same += n
                named |= set(ne.split("|"))
            else:
                problems.append(f"{tok}: the row says {canon!r}, but {n} same-fork pair(s) say {ne!r}")
        agree_sib = 0
        for (ne, net), n in sibling_nets.get(tok, {}).items():
            verdict = sibling_verdict(canon, ne, net)
            if verdict == "agree":
                agree_sib += n
                named |= set(ne.split("|"))
            elif verdict is None:
                problems.append(f"{tok}: the row says {canon!r}, but {n} Cancun-sibling pair(s) of "
                                f"{net} cases say {ne!r}, which no fork difference explains")
            else:
                explained[verdict] += n
        if not agree_same and not agree_sib:
            problems.append(f"{tok}: no agreeing pair in the two trees attests the row {canon!r}")
        elif named != want:
            problems.append(f"{tok}: the row says {canon!r}, but agreeing pairs name only "
                            f"{sorted(named)}; {sorted(want - named)} is unattested")
        else:
            kinds["same-fork" if agree_same else "sibling"] += 1
        unparsed = [t for t in canon.split("|") if t not in vocab]
        if unparsed:
            problems.append(f"{tok}: the row's target names {unparsed}, which "
                            f"{SOURCE.name}'s vocabulary does not parse")

    unmapped = sorted(t for t in seen if t not in table)
    for tok in unmapped:
        print(f"NOTE — legacy-aliases: {tok} ({seen[tok]} block(s)) has no row; "
              f"same-fork pairs {dict(same.get(tok, {}))}, sibling pairs {dict(sibling.get(tok, {}))}")
    if problems:
        for p in problems:
            print(f"  - {p}")
        print(f"REGRESSION — legacy-aliases: {len(problems)} row problem(s) in {SOURCE.name}")
        return 1
    print(f"OK — legacy-aliases: {len(table)} row(s), each attested by upstream's own rename "
          f"({kinds['same-fork']} by same-fork pairs, {kinds['sibling']} by Cancun-sibling pairs "
          f"only), contradicted by no pair of either kind, and parsed by the vocabulary "
          f"({sum(explained.values())} sibling pair(s) explained by a fork difference: "
          f"{dict(sorted(explained.items()))}); {len(unmapped)} unmapped token(s) noted")
    return 0


if __name__ == "__main__":
    sys.exit(main())
