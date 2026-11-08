#!/usr/bin/env python3
"""Inventory the pinned consensus-spec-tests tarballs, case by case.

Reads the ``general``, ``minimal`` and ``mainnet`` tarballs of one
``ethereum/consensus-specs`` release, checks each against the size and SHA-256
recorded in ``scripts/consensus-vectors.json``, and counts every test case by
preset, fork, runner, handler and suite. Nothing is extracted: the archives
are streamed and only member names are read, so the tarballs stay untrusted
data.

A case is the directory ``tests/<preset>/<fork>/<runner>/<handler>/<suite>/<case>``
of any regular file below it. That is the layout ``tests/formats/README.md``
defines at the pin.

Usage (run with ``python3 -I``)::

    python3 -I scripts/consensus-vector-inventory.py \\
        --tarballs DIR [--provenance scripts/consensus-vectors.json] \\
        [--json OUT.json] [--markdown OUT.md] [--expect OUT.json]

``--expect`` compares the fresh counts with a recorded inventory and fails on
any difference. ``--unpinned`` skips the digest check; it exists only for the
negative control, which must show that a tarball with one case removed yields
different counts, and its output is marked unpinned so it can never stand in
for the pinned inventory.

Exit status: 0 on success, 1 on a digest, size, layout or count mismatch.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import tarfile
from collections import Counter, defaultdict

PRESETS = ("general", "minimal", "mainnet")
# Forks whose cases the goal must pass on minimal and mainnet. The general
# preset is in scope whole: every general case lives under a fork directory
# that names where the format was introduced, not where it is used.
SCOPE_FORKS = ("electra", "fulu")
# Fork-independent runners the goal names outright (O1 names `shuffling` on
# both presets). Their only cases sit under the fork that introduced them.
SCOPE_EXTRA = {("phase0", "shuffling")}


def fail(msg: str) -> "NoReturn":  # type: ignore[name-defined]
    print(f"consensus-vector-inventory: FAIL: {msg}", file=sys.stderr)
    sys.exit(1)


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def check_tarball(path: str, want: dict) -> None:
    size = os.path.getsize(path)
    if size != want["size"]:
        fail(f"{path}: size {size} != pinned {want['size']}")
    got = sha256_file(path)
    if got != want["sha256"]:
        fail(f"{path}: sha256 {got} != pinned {want['sha256']}")


def scan(path: str, preset: str) -> tuple[Counter, int]:
    """Return a counter of case keys (fork, runner, handler, suite) and the
    number of regular files seen."""
    cases: set[tuple[str, ...]] = set()
    files = 0
    with tarfile.open(path, mode="r|gz") as tar:
        for m in tar:
            if not m.isfile():
                continue
            parts = [p for p in m.name.split("/") if p not in ("", ".")]
            if ".." in parts:
                fail(f"{path}: member with '..': {m.name!r}")
            if len(parts) < 8 or parts[0] != "tests":
                fail(f"{path}: unexpected member layout: {m.name!r}")
            if parts[1] != preset:
                fail(f"{path}: member outside preset {preset!r}: {m.name!r}")
            files += 1
            cases.add(tuple(parts[2:7]))
    per_suite: Counter = Counter()
    for fork, runner, handler, suite, _case in cases:
        per_suite[(fork, runner, handler, suite)] += 1
    return per_suite, files


def build_inventory(tar_dir: str, prov: dict, pinned: bool) -> dict:
    out: dict = {
        "release": prov["release"],
        "tag_commit": prov["tag_commit"],
        "pinned": pinned,
        "presets": {},
    }
    for preset in PRESETS:
        meta = prov["tarballs"][preset]
        path = os.path.join(tar_dir, meta["name"])
        if not os.path.isfile(path):
            fail(f"missing tarball {path}")
        if pinned:
            check_tarball(path, meta)
        per_suite, files = scan(path, preset)
        if not per_suite:
            fail(f"{path}: no cases")
        tree: dict = defaultdict(lambda: defaultdict(lambda: defaultdict(dict)))
        for (fork, runner, handler, suite), n in sorted(per_suite.items()):
            tree[fork][runner][handler][suite] = n
        out["presets"][preset] = {
            "files": files,
            "cases": sum(per_suite.values()),
            "forks": json.loads(json.dumps(tree)),
        }
    return out


def handler_rows(inv: dict):
    """Yield (preset, fork, runner, handler, suites, cases)."""
    for preset, p in inv["presets"].items():
        for fork, runners in sorted(p["forks"].items()):
            for runner, handlers in sorted(runners.items()):
                for handler, suites in sorted(handlers.items()):
                    yield preset, fork, runner, handler, suites, sum(suites.values())


def in_scope(preset: str, fork: str, runner: str) -> bool:
    return preset == "general" or fork in SCOPE_FORKS or (fork, runner) in SCOPE_EXTRA


def markdown(inv: dict) -> str:
    L: list[str] = []
    L.append(f"# Consensus vector inventory, {inv['release']}")
    L.append("")
    L.append("Generated by `scripts/consensus-vector-inventory.py`. Do not edit by hand.")
    L.append("")
    L.append(f"Release `{inv['release']}`, tag commit `{inv['tag_commit']}`, "
             f"digests {'checked' if inv['pinned'] else 'NOT CHECKED (unpinned run)'}.")
    L.append("In scope: every `general` case, and every `minimal` and `mainnet` case "
             "whose fork is `electra` or `fulu`, plus `phase0/shuffling` on both presets "
             "(O1 names it; it has no cases under a later fork).")
    L.append("")
    L.append("## Totals")
    L.append("")
    L.append("| preset | all cases | in-scope cases | files |")
    L.append("|---|---:|---:|---:|")
    grand_all = grand_scope = 0
    for preset, p in inv["presets"].items():
        scope = sum(n for pr, f, r, _h, _s, n in handler_rows(inv)
                    if pr == preset and in_scope(pr, f, r))
        grand_all += p["cases"]
        grand_scope += scope
        L.append(f"| {preset} | {p['cases']} | {scope} | {p['files']} |")
    L.append(f"| **total** | {grand_all} | {grand_scope} | |")
    L.append("")
    L.append("## In-scope cases by preset, fork and runner")
    L.append("")
    agg: Counter = Counter()
    for pr, f, r, _h, _s, n in handler_rows(inv):
        if in_scope(pr, f, r):
            agg[(pr, f, r)] += n
    L.append("| preset | fork | runner | cases |")
    L.append("|---|---|---|---:|")
    for (pr, f, r), n in sorted(agg.items(), key=lambda kv: (PRESETS.index(kv[0][0]), kv[0][1], kv[0][2])):
        L.append(f"| {pr} | {f} | {r} | {n} |")
    L.append("")
    L.append("## In-scope cases by handler")
    L.append("")
    L.append("Suites are listed as `name:count`.")
    L.append("")
    L.append("| preset | fork | runner | handler | cases | suites |")
    L.append("|---|---|---|---|---:|---|")
    for pr, f, r, h, suites, n in handler_rows(inv):
        if in_scope(pr, f, r):
            s = ", ".join(f"{k}:{v}" for k, v in sorted(suites.items()))
            L.append(f"| {pr} | {f} | {r} | {h} | {n} | {s} |")
    L.append("")
    L.append("## Out-of-scope forks, for context")
    L.append("")
    L.append("| preset | fork | cases outside scope |")
    L.append("|---|---|---:|")
    ctx: Counter = Counter()
    for pr, f, r, _h, _s, n in handler_rows(inv):
        if not in_scope(pr, f, r):
            ctx[(pr, f)] += n
    for (pr, f), n in sorted(ctx.items(), key=lambda kv: (PRESETS.index(kv[0][0]), kv[0][1])):
        L.append(f"| {pr} | {f} | {n} |")
    L.append("")
    return "\n".join(L)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("--tarballs", required=True, help="directory holding the three tarballs")
    ap.add_argument("--provenance", default=os.path.join(here, "consensus-vectors.json"))
    ap.add_argument("--json", help="write the inventory JSON here")
    ap.add_argument("--markdown", help="write the Markdown tables here")
    ap.add_argument("--expect", help="recorded inventory JSON; fail on any count difference")
    ap.add_argument("--unpinned", action="store_true",
                    help="skip the digest check (negative control only)")
    a = ap.parse_args()

    with open(a.provenance, encoding="utf-8") as f:
        prov = json.load(f)
    inv = build_inventory(a.tarballs, prov, pinned=not a.unpinned)

    if a.json:
        with open(a.json, "w", encoding="utf-8") as f:
            json.dump(inv, f, indent=1, sort_keys=True)
            f.write("\n")
    if a.markdown:
        with open(a.markdown, "w", encoding="utf-8") as f:
            f.write(markdown(inv))
    for preset, p in inv["presets"].items():
        print(f"{preset}: {p['cases']} cases, {p['files']} files")

    if a.expect:
        with open(a.expect, encoding="utf-8") as f:
            want = json.load(f)
        if want["presets"] != inv["presets"]:
            got_rows = {(pr, fo, r, h): n for pr, fo, r, h, _s, n in handler_rows(inv)}
            want_rows = {(pr, fo, r, h): n for pr, fo, r, h, _s, n in handler_rows(want)}
            for k in sorted(set(got_rows) | set(want_rows)):
                if got_rows.get(k) != want_rows.get(k):
                    print(f"count mismatch {'/'.join(k)}: got {got_rows.get(k)} "
                          f"recorded {want_rows.get(k)}", file=sys.stderr)
            fail("inventory differs from " + a.expect)
        print("inventory matches " + a.expect)
    return 0


if __name__ == "__main__":
    sys.exit(main())
