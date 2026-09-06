#!/usr/bin/env bash
# Semantic-integrity gate for Jaune (CI lint tier).
#
# Jaune owns this gate; scripts/GATES.md is its current usage and pass-criterion
# authority. Its design and closure history are recorded in
# `~/plans/integrity.md`. This is a STATIC gate: it reads source only, runs no
# Lean toolchain, and is expected to finish well under five seconds. Semantic
# negative regressions live in the fixture tiers and in Lean #guards, not here.
#
# The inventory is computed over the EXACT LOCAL MODULE IMPORT CLOSURE of
# Jaune.lean, traversed transitively from `import Jaune.*` lines rather than
# hardcoded. At the time of writing that closure is
#
#   Basic Types Fork Hash EC BLSConst BLS Machine Precompiles Execution
#   Sufficiency Transaction
#
# and Jaune/ChainStore.lean and Jaune/FixtureException.lean are OUTSIDE it.
# If a module joins or leaves the closure the inventory changes with it, which
# is the point: the gate can never be satisfied by moving code out of reach.
#
# Four rules, all fail-closed:
#
#   R1  ABSENCE, no allowlist. No `partial def`, `implemented_by`, or
#       `dbg_trace` anywhere under Jaune/, in Main.lean, or in MemoryProbe.lean.
#       The historical
#       `~/plans/silence.md` record documents removal of the last of each from
#       the library, and this gate keeps them out. There is deliberately no
#       carve-out and no allowlist row for these.
#
#   R2  No `panic` / `panic!` in the closure, except exact allowlist rows.
#
#   R3  No raw bang operation (`get!`, `set!`, `modify!`, `xs[i]!`, ...) in the
#       closure, except exact allowlist rows.
#
#   R4  No stringly-typed semantic error carrier or string-driven semantic
#       branch, except exact allowlist rows. Since Step 10 completed the
#       typed-error migration, R4's scope is the closure PLUS the runner
#       boundary (Jaune/ChainStore.lean, Jaune/FixtureException.lean,
#       Main.lean) and the bounded memory probe (MemoryProbe.lean), every
#       remaining row is a reviewed KEEP -- a named legacy
#       renderer adapter or an external parser/JSON boundary -- and the gate
#       refuses an R4 PENDING row outright: a new stringly semantic carrier
#       can no longer be deferred, only reviewed in or rejected.
#
# An allowlist row is matched line-number-independently: each occurrence is
# normalised to
#
#   <rule> <relpath> <source line, trimmed, whitespace runs collapsed>
#
# and compared as a whole line against scripts/integrity-allow.txt. That
# survives edits above the line but forces re-review if the matched text
# itself changes.
#
# Rows carry a disposition in a trailing comment on their own allowlist line:
#
#   KEEP     a retained private optimized kernel operation. Its row must name
#            the declaration, its checked/fixed-size public wrapper, and the
#            bounds/size theorem that discharges it.
#   PENDING  a known defect this arc removes, with the owning step named. A
#            PENDING row is reported as a WARNING on every run so it cannot be
#            forgotten, and the gate refuses to let the PENDING set grow.
#
# The allowlist is a budget that only shrinks. New occurrences fail. This is
# mechanically enforceable and does not pretend that grep proves reachability.
#
# Usage: scripts/check-integrity.sh [--list|--pending]
#
#   --list     print the current normalised occurrence inventory and exit 0.
#              Use it to author allowlist rows; never pipe it into the
#              allowlist without reading every line.
#   --pending  print every PENDING row in full. The plain run prints only a
#              per-step count, so that a green run stays readable.
#
# CLI contract: exit 0 iff every occurrence is allowlisted and no PENDING row
# was added; the last line of output is a single unambiguous verdict. Exit 1 on
# a violation, 2 on a usage or setup error.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
ALLOW="$SCRIPT_DIR/integrity-allow.txt"

MODE="check"
if [ $# -eq 1 ] && [ "$1" = "--list" ]; then
  MODE="list"
elif [ $# -eq 1 ] && [ "$1" = "--pending" ]; then
  MODE="pending"
elif [ $# -ne 0 ]; then
  echo "usage: scripts/check-integrity.sh [--list|--pending]" >&2
  exit 2
fi

if [ "$MODE" = "pending" ]; then
  if [ ! -f "$ALLOW" ]; then
    echo "REGRESSION — integrity: allowlist not found: $ALLOW"
    exit 2
  fi
  grep -vE '^[[:space:]]*(#|$)' "$ALLOW" | grep '## *PENDING' \
    | while IFS= read -r p; do echo "PENDING — $p"; done
  NP="$(grep -vE '^[[:space:]]*(#|$)' "$ALLOW" | grep -c '## *PENDING')"
  echo "OK — integrity: $NP pending row(s) listed"
  exit 0
fi

if [ ! -f "$ROOT/Jaune.lean" ]; then
  echo "REGRESSION — integrity: root module not found: $ROOT/Jaune.lean"
  exit 2
fi

INVENTORY="$(cd "$ROOT" && python3 - <<'PY'
import os, re, sys

# ---- the exact local module import closure of Jaune.lean -------------------
def path_of(mod):
    return "Jaune.lean" if mod == "Jaune" else mod.replace(".", "/") + ".lean"

IMPORT = re.compile(r'\s*import\s+(Jaune(?:\.[A-Za-z0-9_]+)*)\s*$')
closure, stack = set(), ["Jaune"]
while stack:
    mod = stack.pop()
    if mod in closure:
        continue
    closure.add(mod)
    p = path_of(mod)
    if not os.path.exists(p):
        print("SETUP missing module file for %s (%s)" % (mod, p), file=sys.stderr)
        sys.exit(2)
    for line in open(p, encoding="utf-8"):
        m = IMPORT.match(line)
        if m:
            stack.append(m.group(1))

closure_files = sorted(path_of(m) for m in closure)

# The post-Step-10 scope of R4: the closure plus the runner boundary, where
# the fixture parser and the CLI renderer live. Strings there are legitimate
# only at exact-listed parser/renderer lines.
# MemoryProbe.lean is the second tracked Lean executable in this repository:
# a bounded native probe built by the ordinary `lake build` and asserted by
# scripts/check-memory-probe.sh. It was outside every static gate until the
# memory-closure repair; an anti-regression instrument that no gate reads is
# one that rots. It carries a typed ProbeError rather than an `Except String`,
# so it enters this scope with no allowlist row.
r4_files = sorted(set(closure_files)
                  | {"Jaune/ChainStore.lean", "Jaune/FixtureException.lean",
                     "Main.lean", "MemoryProbe.lean"})

# R1 is scoped to the whole library plus Main.lean, not just the closure:
# silence.md removed these from every Jaune source file and this gate keeps
# them out of all of them. scripts/*.lean are Lean metaprograms over `Expr`
# and are deliberately not in scope.
r1_files = sorted(
    ["Jaune/" + f for f in os.listdir("Jaune") if f.endswith(".lean")]
    + ["Jaune.lean", "Main.lean", "MemoryProbe.lean"]
)

RULES = [
    # rule, scope, compiled pattern
    ("R1", r1_files, re.compile(r'partial\s+def|implemented_by|dbg_trace')),
    ("R2", closure_files,
     re.compile(r'(?<![A-Za-z0-9_])panic!?(?![A-Za-z0-9_])')),
    ("R3", closure_files,
     re.compile(r'(?<![A-Za-z0-9_])'
                r'(get!|set!|modify!|getLast!|head!|back!|swap!|uget!|getElem!)'
                r'(?![A-Za-z0-9_])'
                r'|\]!')),
    # R4: stringly-typed semantic carriers and string-driven semantic branches.
    # `String × Devm` is the VM carrier; `Option String` catches Meta.error and
    # MsgCallOutput.error; hasErrorType/isExceptionalHalt/isBlockException are
    # the prefix-match branch primitives; String.isPrefixOf and an exact
    # comparison against a quoted literal cover the hand-rolled variants.
    ("R4", r4_files,
     re.compile(r'Except\s+String'
                r'|Except\s*\(\s*String\s*×'
                r'|String\s*×\s*Devm'
                r'|Option\s+String'
                r'|(?<![A-Za-z0-9_])hasErrorType(?![A-Za-z0-9_])'
                r'|(?<![A-Za-z0-9_])isExceptionalHalt(?![A-Za-z0-9_])'
                r'|(?<![A-Za-z0-9_])isBlockException(?![A-Za-z0-9_])'
                r'|String\.isPrefixOf')),
]

def normalise(s):
    return " ".join(s.split())

rows = []
for rule, files, pat in RULES:
    for f in files:
        if not os.path.exists(f):
            continue
        for line in open(f, encoding="utf-8"):
            if pat.search(line):
                rows.append("%s %s %s" % (rule, f, normalise(line)))

for r in sorted(set(rows)):
    print(r)
PY
)"
PYSTATUS=$?
if [ $PYSTATUS -ne 0 ]; then
  echo "REGRESSION — integrity: could not build the inventory (python exit $PYSTATUS)"
  exit 2
fi

HITS="$(printf '%s\n' "$INVENTORY" | grep -v '^$' | sort -u)"

if [ "$MODE" = "list" ]; then
  printf '%s\n' "$HITS"
  NLIST="$(printf '%s\n' "$HITS" | grep -c .)"
  echo "OK — integrity: $NLIST normalised occurrence(s) in the current inventory"
  exit 0
fi

if [ ! -f "$ALLOW" ]; then
  echo "REGRESSION — integrity: allowlist not found: $ALLOW"
  exit 2
fi

# Allowlist data lines: strip the trailing disposition comment and normalise
# identically, so authoring is forgiving about incidental whitespace.
ALLOWED="$(grep -vE '^[[:space:]]*(#|$)' "$ALLOW" \
  | sed -E 's/[[:space:]]*##.*$//' \
  | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//; s/[[:space:]]+/ /g' \
  | grep -v '^$' | sort -u)"

VIOLATIONS="$(comm -23 <(printf '%s\n' "$HITS") <(printf '%s\n' "$ALLOWED"))"
STALE="$(comm -13 <(printf '%s\n' "$HITS") <(printf '%s\n' "$ALLOWED"))"

# Every R1 occurrence is a violation by construction: R1 admits no rows. Guard
# the allowlist itself against ever acquiring one.
BADR1="$(printf '%s\n' "$ALLOWED" | grep -c '^R1 ' || true)"
if [ "$BADR1" -ne 0 ]; then
  echo "INTEGRITY — the allowlist carries $BADR1 R1 row(s); R1 admits no carve-out"
  echo "REGRESSION — integrity: R1 (no partial def / implemented_by / dbg_trace) has no allowlist"
  exit 1
fi

# Step 10 completed the typed-error migration: every remaining R4 row is a
# reviewed KEEP (a named legacy renderer adapter or an external parser
# boundary). An R4 PENDING row would mean a new stringly semantic carrier was
# deferred rather than reviewed; the gate refuses it outright.
BADR4="$(grep -vE '^[[:space:]]*(#|$)' "$ALLOW" | grep '^R4 ' | grep -c '## *PENDING' || true)"
if [ "$BADR4" -ne 0 ]; then
  echo "INTEGRITY — the allowlist carries $BADR4 R4 PENDING row(s); since Step 10 a stringly semantic carrier is KEEP-reviewed or removed, never deferred"
  echo "REGRESSION — integrity: R4 (typed error carriers) admits no PENDING disposition"
  exit 1
fi

PENDING="$(grep -vE '^[[:space:]]*(#|$)' "$ALLOW" | grep -c '## *PENDING' || true)"
PENDING_MAX="$(grep -E '^# *pending-budget:' "$ALLOW" | head -1 \
  | sed -E 's/^# *pending-budget:[[:space:]]*//')"
if [ -z "${PENDING_MAX:-}" ]; then
  echo "REGRESSION — integrity: the allowlist declares no '# pending-budget: <n>' line"
  exit 2
fi

if [ -n "$STALE" ]; then
  printf '%s\n' "$STALE" | while IFS= read -r s; do
    [ -n "$s" ] && echo "WARNING — integrity: stale allowlist row no longer in source: $s"
  done
fi

# Summarise the pending set by owning step rather than printing every row: the
# full list is `--pending`. A cheap gate that prints hundreds of lines on a
# green run stops being read, and this one must stay readable to stay useful.
grep -vE '^[[:space:]]*(#|$)' "$ALLOW" | grep -oE '## *PENDING\(step[0-9]+' \
  | sed -E 's/.*\(//' | sort | uniq -c \
  | while read -r n s; do
      echo "PENDING — integrity: $n row(s) owned by ${s}"
    done

if [ -n "$VIOLATIONS" ]; then
  printf '%s\n' "$VIOLATIONS" | while IFS= read -r v; do
    [ -n "$v" ] && echo "INTEGRITY — un-allowlisted occurrence: $v"
  done
  NVIO="$(printf '%s\n' "$VIOLATIONS" | grep -c .)"
  echo "REGRESSION — integrity: $NVIO occurrence(s) not in $(basename "$ALLOW"); remove them or add a justified allowlist row"
  exit 1
fi

if [ "$PENDING" -gt "$PENDING_MAX" ]; then
  echo "REGRESSION — integrity: $PENDING PENDING row(s) exceeds the declared budget of $PENDING_MAX; the pending set may only shrink"
  exit 1
fi

NHITS="$(printf '%s\n' "$HITS" | grep -c .)"
echo "OK — integrity: all $NHITS occurrence(s) in the audited scope (Jaune.lean closure + runner boundary and MemoryProbe.lean for R4) are allowlisted; $PENDING pending (budget $PENDING_MAX); no new ones"
exit 0
