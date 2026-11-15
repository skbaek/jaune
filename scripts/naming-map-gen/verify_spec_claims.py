#!/usr/bin/env python3
"""Re-read every pyspec citation of classification.tsv in the checkouts and confirm that the cited
line contains the claimed pyspec name.  usage: verify_spec_claims.py classification.tsv HOME_DIR"""
import re
import sys
from pathlib import Path

tsv, home = sys.argv[1], Path(sys.argv[2])
ok = bad = 0
samples = []
for l in open(tsv):
    grp, cls, mod, line, kind, q, new, cite = l.rstrip("\n").split("\t")
    if cls != "spec" or not cite.startswith("consensus-specs"):
        continue
    m = re.match(r"(consensus-specs-v[\w.\-]+)/(.+?):(\d+) \((\S+), (.+)\)$", cite)
    if not m:
        bad += 1
        print("UNPARSED", cite)
        continue
    co, path, n, name, how = m.groups()
    text = (home / co / path).read_text().split("\n")[int(n) - 1]
    if name in text:
        ok += 1
        samples.append((q.replace("JauneConsensus.", ""), co.replace("consensus-specs-", ""), path, n, text.strip()[:90]))
    else:
        bad += 1
        print("MISMATCH", q, cite, "|", text.strip()[:80])
print(f"verified {ok} pyspec citations, {bad} failures")
if len(sys.argv) > 3:
    step = max(1, len(samples) // int(sys.argv[3]))
    for s in samples[::step]:
        print(" | ".join(s))
