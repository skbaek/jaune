#!/usr/bin/env python3
"""jsn-s6d: per-theorem table from the Lean count/timing output and the sources.

usage: metrics.py COUNT_TXT TIMING_DIR

COUNT_TXT: the S6D_COUNT lines (Experiments/S6d/Report.lean build output).
TIMING_DIR: files run*-B.txt / run*-V.txt holding S6D_TIME lines (one file per run per side).

Proof-size metrics are read from the declaration's source range (from S6D_COUNT):
  lines   - source lines of the declaration (statement and proof), comments excluded
  ptoks   - tokens of the proof only (after the first ':=' at depth 0), comments excluded
  conv    - conversion obligations in the proof: references to conversion lemmas (the regexes
            below, the same on both sides) plus explicit `< 2 ^ N` bound side goals.
"""
import json, re, statistics, sys, glob, os

ROOT = os.path.dirname(os.path.abspath(__file__))
FILES = {"Experiments.S6d.B256Words": os.path.join(ROOT, "B256Words.lean"),
         "Experiments.S6d.BitVecWords": os.path.join(ROOT, "BitVecWords.lean")}

# Conversion lemmas: the representation-to-Nat bridge and its inverses, on either side.
CONV = re.compile(r"""(?x)
   \b(?:[A-Za-z0-9_.]*\.)?toNat_[A-Za-z0-9_']*   # B256.toNat_add, BitVec.toNat_sub, toNat_toB128 ...
 | \b(?:[A-Za-z0-9_.]*\.)?to(?:B128|B256)_[A-Za-z0-9_']*   # toB256_toNat, toB128_or ...
 | \bNat\.lo_eq_of_lt\b | \bNat\.mod_eq_of_lt\b | \bNat\.lo\b
 | \b[A-Za-z0-9_.]*lt_iff_toNat_lt_toNat\b | \b[A-Za-z0-9_.]*le_iff_toNat_le_toNat\b
 | \bBitVec\.(?:lt_def|le_def|eq_of_toNat_eq|isLt|toNat_inj)\b | \.isLt\b
 | \bB(?:128|256)\.toNat_lt\b
""")
BOUND = re.compile(r"<\s*2\s*\^\s*(?:64|128|256)\b")
TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_.'!?]*|\d+|[^\sA-Za-z0-9_]")


def strip_comments(s):
    s = re.sub(r"/-.*?-/", "", s, flags=re.S)
    return "\n".join(l.split("--")[0] for l in s.splitlines())


def source(rng):
    mod, span = rng.rsplit(":", 1)
    a, b = map(int, span.split("-"))
    lines = open(FILES[mod]).read().splitlines()[a - 1:b]
    return strip_comments("\n".join(lines))


def proof_part(src):
    i = src.find(":=")
    return src[i + 2:] if i >= 0 else ""


def main():
    count_txt, tdir = sys.argv[1], sys.argv[2]
    counts = {}
    for l in open(count_txt):
        m = re.match(r"S6D_COUNT (\S+) axioms=\[(.*?)\] helpers=(\d+) helper_lines=(\d+) range=(\S+)", l)
        if m:
            counts[m[1]] = dict(axioms=m[2], helpers=int(m[3]), hlines=int(m[4]), range=m[5])
    times = {}
    for f in sorted(glob.glob(os.path.join(tdir, "run*-*.txt"))):
        for l in open(f):
            m = re.search(r"S6D_TIME (\S+) total_ms=([\d.]+) kernel_ms=([\d.]+) heartbeats=(\d+)", l)
            if m:
                times.setdefault(m[1], []).append((float(m[2]), float(m[3]), int(m[4])))
    pairs = json.load(open(os.path.join(ROOT, "pairs.json")))
    rows = []
    for g, orig, b, v in pairs:
        row = dict(group=g, name=orig)
        for side, n in (("B", "Jaune." + b), ("V", "S6d.V." + v)):
            c = counts[n]
            src = source(c["range"])
            pf = proof_part(src)
            t = times.get(n, [])
            row[side] = dict(
                decl=n,
                lines=len([x for x in src.splitlines() if x.strip()]),
                ptoks=len(TOK.findall(pf)),
                conv=len(CONV.findall(pf)) + len(BOUND.findall(pf)),
                helpers=c["helpers"], hlines=c["hlines"], axioms=c["axioms"],
                total_ms=statistics.median([x[0] for x in t]) if t else None,
                kernel_ms=statistics.median([x[1] for x in t]) if t else None,
                khb=statistics.median([x[2] for x in t]) if t else None,
                runs=len(t))
        rows.append(row)
    json.dump(rows, open(os.path.join(tdir, "table.json"), "w"), indent=1)
    keys = ["lines", "ptoks", "conv", "helpers", "hlines", "total_ms", "kernel_ms", "khb"]
    hdr = "| grp | theorem | " + " | ".join(f"{k} B / V" for k in keys) + " |"
    print(hdr)
    print("|" + "---|" * (len(keys) + 2))
    fmt = lambda x: "-" if x is None else (f"{x:.2f}" if isinstance(x, float) else str(x))
    for r in rows:
        print(f"| {r['group']} | `{r['name']}` | " +
              " | ".join(f"{fmt(r['B'][k])} / {fmt(r['V'][k])}" for k in keys) + " |")
    print()
    print("Group medians (B256 / BitVec):")
    print("| grp | n | " + " | ".join(keys) + " |")
    print("|" + "---|" * (len(keys) + 2))
    for g in sorted(set(r["group"] for r in rows)) + ["all"]:
        rs = [r for r in rows if g == "all" or r["group"] == g]
        med = lambda side, k: statistics.median([r[side][k] for r in rs if r[side][k] is not None])
        print(f"| {g} | {len(rs)} | " + " | ".join(f"{fmt(float(med('B', k)))} / {fmt(float(med('V', k)))}" for k in keys) + " |")
    print()
    print("Totals (B256 / BitVec):")
    for k in keys:
        tb = sum(r["B"][k] or 0 for r in rows); tv = sum(r["V"][k] or 0 for r in rows)
        print(f"- {k}: {fmt(float(tb))} / {fmt(float(tv))}")
    ax = set()
    for r in rows:
        for s in ("B", "V"):
            ax |= set(a for a in r[s]["axioms"].split(",") if a)
    print(f"\nAxiom union over all 64 declarations: {sorted(ax)}")


if __name__ == "__main__":
    main()
