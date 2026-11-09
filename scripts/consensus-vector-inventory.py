#!/usr/bin/env python3
"""Inventory the pinned consensus-spec-tests tarballs, case by case.

Reads the ``minimal``, ``mainnet`` and ``comptests`` tarballs of the pinned
``ethereum/consensus-specs`` release and the ``general`` tarball of the
general-only provenance entry (``general`` in ``scripts/consensus-vectors.json``:
the pinned release's own general tarball has no ``ssz_generic`` or ``kzg``
cases, so the general rows stay on an earlier release), checks each against
the size and SHA-256 recorded there, and counts every test case by tarball,
fork, runner, handler and suite. Nothing is extracted: the archives are
streamed and only member names are read, so the tarballs stay untrusted data.

A case is the directory ``tests/<preset>/<fork>/<runner>/<handler>/<suite>/<case>``
of any regular file below it. That is the layout ``tests/formats/README.md``
defines at the pin. The ``comptests`` tarball uses the same layout under the
``minimal`` preset (``tests/minimal/<fork>/fork_choice_compliance/...``); it also
ships the pyspec sources, the format descriptions and the compliance generators
(``tests/core/``, ``tests/formats/``, ``tests/generators/``), which are not
cases: they are skipped and their regular-file count per prefix is recorded
(``skipped_source_members``).

Usage (run with ``python3 -I``)::

    python3 -I scripts/consensus-vector-inventory.py \\
        --tarballs DIR [--general-tarballs DIR] \\
        [--provenance scripts/consensus-vectors.json] \\
        [--json OUT.json] [--markdown OUT.md] [--expect OUT.json]

``--general-tarballs`` defaults to ``~/consensus-spec-tests-<general release>/tarballs``.

``--expect`` compares the fresh counts with a recorded inventory and fails on
any difference. ``--unpinned`` skips the digest check; it exists only for the
negative control, which must show that a tarball with one case removed yields
different counts, and its output is marked unpinned so it can never stand in
for the pinned inventory.

For every in-scope suite the inventory also records, under ``suites``, what the
conformance runner (``lake exe jaune-consensus``) pins case by case:

* ``names_sha256``: SHA-256 of the sorted case directory names, one per line,
  each line ending in ``\n``. A missing, extra or renamed case changes it.
* ``files_sha256``: SHA-256 of the sorted ``<case>/<file>`` paths, same
  framing. A missing, extra or renamed file (for example a Fulu fork-choice
  ``column_<hex>.ssz_snappy``) changes it.
* ``bls_setting``: a histogram of each case's ``meta.yaml`` ``bls_setting``
  (``absent`` when the case has no ``meta.yaml`` or the key is not present).
* ``config_overrides``: the sorted names of cases carrying a ``config.yaml``.

These are read from the verified tarball, never from an extracted tree.

Exit status: 0 on success, 1 on a digest, size, layout or count mismatch.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import tarfile
from collections import Counter, defaultdict

# The tarballs the inventory reads, by key. Each key is also the extraction
# directory (``<root>/<key>/tests/<preset>/...``); ``TARBALL_PRESET`` maps it to
# the preset directory inside the tarball.
PRESETS = ("general", "minimal", "mainnet", "comptests")
TARBALL_PRESET = {"general": "general", "minimal": "minimal", "mainnet": "mainnet",
                  "comptests": "minimal"}
# Member prefixes of the non-case files in the comptests tarball: the pyspec
# sources, the test-format descriptions and the compliance generators.
SOURCE_PREFIX = {"comptests": ("tests/core/", "tests/formats/", "tests/generators/")}
# Forks whose cases the goal must pass on minimal and mainnet (and comptests).
# The general preset is in scope whole: every general case lives under a fork
# directory that names where the format was introduced, not where it is used.
SCOPE_FORKS = ("electra", "fulu", "gloas")
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


BLS_RE = re.compile(rb"(?:^|[{,\s])bls_setting:\s*([0-9]+)\s*(?:[,}\n]|$)")


def bls_setting_of(data: bytes, where: str) -> str:
    """The ``bls_setting`` of one ``meta.yaml``, as a histogram key. Fails
    closed on a mention the pattern does not account for."""
    hits = BLS_RE.findall(data)
    if len(hits) != data.count(b"bls_setting"):
        fail(f"{where}: unrecognised bls_setting form")
    if len(hits) > 1:
        fail(f"{where}: repeated bls_setting")
    if not hits:
        return "absent"
    v = hits[0].decode()
    if v not in ("0", "1", "2"):
        fail(f"{where}: bls_setting {v} outside 0, 1, 2")
    return v


def tarball_meta(prov: dict, key: str) -> tuple[dict, str, str]:
    """The pin of tarball ``key``: its record, release and tag commit. The
    general tarball comes from the general-only provenance entry."""
    if key == "general":
        g = prov["general"]
        return g["tarballs"]["general"], g["release"], g["tag_commit"]
    return prov["tarballs"][key], prov["release"], prov["tag_commit"]


def scan(path: str, tkey: str, details: dict | None = None,
         skipped: list | None = None) -> tuple[Counter, int]:
    """Return a counter of case keys (fork, runner, handler, suite) and the
    number of regular files seen in tarball ``tkey``. When ``details`` is a dict,
    fill it with the per-suite records described in the module docstring, for
    in-scope suites. Source members (``SOURCE_PREFIX``) are skipped and counted
    per prefix in the dict ``skipped[0]``."""
    preset = TARBALL_PRESET[tkey]
    skip = SOURCE_PREFIX.get(tkey, ())
    cases: set[tuple[str, ...]] = set()
    files = 0
    nskip: Counter = Counter()
    case_files: dict = defaultdict(list)
    case_bls: dict = {}
    with tarfile.open(path, mode="r|gz") as tar:
        for m in tar:
            if not m.isfile():
                continue
            parts = [p for p in m.name.split("/") if p not in ("", ".")]
            if ".." in parts:
                fail(f"{path}: member with '..': {m.name!r}")
            pre = next((q for q in skip if "/".join(parts).startswith(q)), None)
            if pre is not None:
                nskip[pre] += 1
                continue
            if len(parts) < 8 or parts[0] != "tests":
                fail(f"{path}: unexpected member layout: {m.name!r}")
            if parts[1] != preset:
                fail(f"{path}: member outside preset {preset!r}: {m.name!r}")
            files += 1
            key = tuple(parts[2:7])
            cases.add(key)
            if details is not None and in_scope(tkey, parts[2], parts[3]):
                rel = "/".join(parts[7:])
                case_files[key].append(rel)
                if rel == "meta.yaml":
                    fh = tar.extractfile(m)
                    if fh is None:
                        fail(f"{path}: unreadable {m.name!r}")
                    case_bls[key] = bls_setting_of(fh.read(), m.name)
    per_suite: Counter = Counter()
    for fork, runner, handler, suite, _case in cases:
        per_suite[(fork, runner, handler, suite)] += 1
    if details is not None:
        grouped: dict = defaultdict(list)
        for key in case_files:
            grouped[key[:4]].append(key)
        for skey, ckeys in sorted(grouped.items()):
            names = sorted(k[4] for k in ckeys)
            paths = sorted(f"{k[4]}/{rel}" for k in ckeys for rel in case_files[k])
            hist: Counter = Counter(case_bls.get(k, "absent") for k in ckeys)
            details["/".join(skey)] = {
                "cases": len(names),
                "names_sha256": hashlib.sha256("".join(n + "\n" for n in names).encode()).hexdigest(),
                "files_sha256": hashlib.sha256("".join(q + "\n" for q in paths).encode()).hexdigest(),
                "bls_setting": dict(sorted(hist.items())),
                "config_overrides": sorted(k[4] for k in ckeys if "config.yaml" in case_files[k]),
            }
    if skipped is not None:
        skipped.append(dict(sorted(nskip.items())))
    return per_suite, files


def build_inventory(tar_dir: str, general_dir: str, prov: dict, pinned: bool) -> dict:
    out: dict = {
        "release": prov["release"],
        "tag_commit": prov["tag_commit"],
        "general_release": {"release": prov["general"]["release"],
                            "tag_commit": prov["general"]["tag_commit"]},
        "pinned": pinned,
        "presets": {},
        "suites": {},
    }
    for key in PRESETS:
        meta, _rel, _tag = tarball_meta(prov, key)
        path = os.path.join(general_dir if key == "general" else tar_dir, meta["name"])
        if not os.path.isfile(path):
            fail(f"missing tarball {path}")
        if pinned:
            check_tarball(path, meta)
        details: dict = {}
        skipped: list = []
        per_suite, files = scan(path, key, details, skipped)
        out["suites"][key] = details
        if not per_suite:
            fail(f"{path}: no cases")
        if key not in SOURCE_PREFIX and skipped[0]:
            fail(f"{path}: {skipped[0]} skipped members in a tarball with no source prefix")
        tree: dict = defaultdict(lambda: defaultdict(lambda: defaultdict(dict)))
        for (fork, runner, handler, suite), n in sorted(per_suite.items()):
            tree[fork][runner][handler][suite] = n
        rec: dict = {
            "files": files,
            "cases": sum(per_suite.values()),
            "forks": json.loads(json.dumps(tree)),
        }
        if TARBALL_PRESET[key] != key:
            rec["preset"] = TARBALL_PRESET[key]
        if key in SOURCE_PREFIX:
            rec["skipped_source_members"] = skipped[0]
        out["presets"][key] = rec
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
    g = inv["general_release"]
    L.append(f"Release `{inv['release']}`, tag commit `{inv['tag_commit']}`, for the `minimal`, "
             f"`mainnet` and `comptests` tarballs; the `general` tarball is release "
             f"`{g['release']}` (tag commit `{g['tag_commit']}`), because the pinned release's "
             f"general tarball has no `ssz_generic` or `kzg` cases. "
             f"Digests {'checked' if inv['pinned'] else 'NOT CHECKED (unpinned run)'}.")
    L.append("In scope: every `general` case, and every `minimal`, `mainnet` and `comptests` "
             "case whose fork is `electra`, `fulu` or `gloas`, plus `phase0/shuffling` on both "
             "presets (O1 names it; it has no cases under a later fork). The `comptests` tarball "
             "holds `minimal`-preset `fork_choice_compliance` cases.")
    L.append("")
    L.append("## Totals")
    L.append("")
    L.append("| tarball | all cases | in-scope cases | files | skipped source members |")
    L.append("|---|---:|---:|---:|---:|")
    grand_all = grand_scope = 0
    for preset, p in inv["presets"].items():
        scope = sum(n for pr, f, r, _h, _s, n in handler_rows(inv)
                    if pr == preset and in_scope(pr, f, r))
        grand_all += p["cases"]
        grand_scope += scope
        L.append(f"| {preset} | {p['cases']} | {scope} | {p['files']} | "
                 f"{sum(p.get('skipped_source_members', {}).values())} |")
    L.append(f"| **total** | {grand_all} | {grand_scope} | | |")
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
    L.append("## bls_setting and per-case config overrides (in scope)")
    L.append("")
    L.append("Histogram of `meta.yaml` `bls_setting` per preset (`absent`: no `meta.yaml` or no key), "
             "and cases carrying a `config.yaml`. Per-suite values, with the case-name and file-path "
             "digests the runner checks, are in the JSON under `suites`.")
    L.append("")
    L.append("| preset | absent | 0 | 1 | 2 | config overrides |")
    L.append("|---|---:|---:|---:|---:|---:|")
    for pr, recs in inv.get("suites", {}).items():
        h: Counter = Counter()
        nover = 0
        for r_ in recs.values():
            h.update(r_["bls_setting"])
            nover += len(r_["config_overrides"])
        L.append(f"| {pr} | {h['absent']} | {h['0']} | {h['1']} | {h['2']} | {nover} |")
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
    ap.add_argument("--tarballs", required=True,
                    help="directory holding the pinned release's minimal, mainnet and comptests tarballs")
    ap.add_argument("--general-tarballs",
                    help="directory holding the general-only entry's general tarball "
                         "(default ~/consensus-spec-tests-<general release>/tarballs)")
    ap.add_argument("--provenance", default=os.path.join(here, "consensus-vectors.json"))
    ap.add_argument("--json", help="write the inventory JSON here")
    ap.add_argument("--markdown", help="write the Markdown tables here")
    ap.add_argument("--expect", help="recorded inventory JSON; fail on any count difference")
    ap.add_argument("--unpinned", action="store_true",
                    help="skip the digest check (negative control only)")
    a = ap.parse_args()

    with open(a.provenance, encoding="utf-8") as f:
        prov = json.load(f)
    general_dir = a.general_tarballs or os.path.expanduser(
        f"~/consensus-spec-tests-{prov['general']['release']}/tarballs")
    inv = build_inventory(a.tarballs, general_dir, prov, pinned=not a.unpinned)

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
        if want.get("suites") != inv["suites"]:
            ws, gs = want.get("suites") or {}, inv["suites"]
            for pr in sorted(set(ws) | set(gs)):
                a_, b_ = ws.get(pr, {}), gs.get(pr, {})
                for k in sorted(set(a_) | set(b_)):
                    if a_.get(k) != b_.get(k):
                        print(f"suite record mismatch {pr}/{k}", file=sys.stderr)
            fail("suite records differ from " + a.expect)
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
