#!/usr/bin/env bash
# Elaboration-time gate for Jaune.
#
# Measures how long each of our own modules takes to re-elaborate against
# already-built dependencies — the cost an interactive session pays to open or
# touch a file, and the cost that sits on `lake build`'s critical path. Compares
# every file against the committed reference times in scripts/baseline-elab.txt
# and fails when one has become materially slower.
#
# This gate exists because nothing else measures this axis. check-hygiene.sh,
# check-integrity.sh, and the conformance tiers all say nothing about
# elaboration cost, and CI's only ceilings are coarse job timeouts, so a module
# drifting from 4s to 60s would land unnoticed until a timeout fired. Runtime
# EVM performance is measured continuously; build-time performance was not
# measured at all before this script.
#
# Usage:
#   scripts/check-elab.sh [--rebase] [--list] [--no-build] [--force]
#                         [--report <path>]
#
#   --rebase      accept the current times as the new committed baseline.
#                 Refused if any file failed to elaborate — a baseline must
#                 only ever record a green tree.
#   --list        measure and print, compare nothing, write no baseline. Use
#                 when investigating rather than gating.
#   --no-build    skip the `lake build` precondition. Permitted only when the
#                 tree is already built at this exact source revision;
#                 otherwise the first file measured pays for everything stale
#                 beneath it and every number is wrong.
#   --force       run even though Lean language servers are alive. See below.
#   --report      write the per-file report here instead of
#                 scripts/report-elab.txt.
#
# CLI contract: exit 0 iff the gate passed; the last line of output is a single
# unambiguous verdict. Exit 1 on a violation, 2 on a usage or setup error — a
# refusal to run under contention, including the lock refusal below, is that
# second kind.
#
# WHY THIS GATE IS SEQUENTIAL AND HAS NO --jobs
#
# check-legacy.sh, check-mainnet.sh, and check-vectors.sh take --jobs because their
# gate is the STATUS column and their TIME column is merely reference data, so a
# contended run still decides the real question. Here TIME *is* the gate. There
# is no meaningful parallel mode: concurrent elaborations contend for cores and
# memory, and the resulting times would measure the scheduler rather than the
# code. So this script always runs one file at a time, and there is no flag to
# change that.
#
# For the same reason it refuses to run while Lean language servers are holding
# large environments. A pair of them holding mathlib has previously driven this
# host deep into swap and inflated wall times several-fold — timings taken under
# that contention are unusable, while classification-style results would have
# been unaffected. A gate whose only output is a timing must refuse that
# condition rather than annotate it.
#
# It keys on resident size, not on the mere presence of a server, and the
# distinction matters. lean-lsp-mcp is mandated tooling here, so idle servers
# are this project's normal steady state: one that has opened no file sits near
# 40MB and burns no CPU, while one holding a mathlib environment sits near
# 900MB. Refusing on presence would therefore refuse nearly every legitimate
# run and train everyone to pass --force by reflex, which would hollow the gate
# out completely. So a small server is noted and tolerated; a large one is
# refused. --force overrides for a deliberate investigation; a --force run may
# not be rebased.
#
# THRESHOLD
#
# A file fails when its time exceeds both 2x its baseline and its baseline plus
# 1.0s. The 2x factor mirrors the DRIFT convention already used by check-legacy.sh; the
# absolute floor keeps a sub-second file from tripping on ordinary scheduler
# noise, where a half-second blip is a large ratio and no real change. A file
# that has become much *faster* is reported as IMPROVED rather than passed over
# in silence, because a stale over-generous baseline is how this gate would
# quietly stop gating.
#
# SCOPE: THIS IS A LOCAL GATE, NOT A CI GATE
#
# The committed times are wall-clock measurements from one machine, so they are
# machine-dependent in exactly the way `notimeout.md` objected to when it
# abolished TIMEOUT as a fixture classification: a slower or noisier runner
# would fail files that are in no way worse. Do not wire this into CI against a
# baseline measured elsewhere. Either keep it a local pre-push check, or give CI
# its own baseline measured on its own runner and rebased when that runner
# changes. The 1.0s absolute floor and the 2x factor together absorb ordinary
# same-machine variance, not cross-machine variance.
#
# BASELINE FORMAT
#
# STATUS<TAB>TIME<TAB>path, sorted by path, matching the check-legacy.sh baselines.
# STATUS is OK or ERROR. A source file with no baseline row is a configuration
# error, not an unmeasured file: that is what forces a newly added module to
# state its cost. A baseline row whose file no longer exists is reported as a
# warning, never a failure.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

# Captured before the argument loop consumes them; the lock records the whole
# command line so a refusal can name what is holding it.
GATE_CMDLINE="$0 $*"
. "$SCRIPT_DIR/gate-lock.sh"

# One cleanup function, one EXIT trap, installed once: a second `trap ... EXIT`
# would silently replace this one and leak RCFILE.
RCFILE=""
cleanup() {
  gate_lock_release_all
  if [ -n "$RCFILE" ]; then rm -f "$RCFILE"; fi
  return 0
}
trap cleanup EXIT

SRC_DIR="Jaune"
ROOT_MODULES="Jaune.lean Main.lean"
BASELINE="$SCRIPT_DIR/baseline-elab.txt"
REPORT="$SCRIPT_DIR/report-elab.txt"

DRIFT_FACTOR="2.0"
DRIFT_FLOOR="1.0"
IMPROVE_FACTOR="0.5"

# Language-server contention thresholds, in MB of resident size. A server that
# has opened no file sits near 40MB and cannot contend for anything; one holding
# a mathlib environment sits near 900MB and is the case on record for driving
# this host into swap. These sit well above the former and well below the
# latter, so the ordinary always-connected MCP server passes and a live editing
# session does not.
LSP_RSS_MAX_MB=250
LSP_RSS_TOTAL_MB=600

REBASE=0
LIST_ONLY=0
NO_BUILD=0
FORCE=0

while [ $# -gt 0 ]; do
  case "$1" in
    --rebase)   REBASE=1; shift ;;
    --list)     LIST_ONLY=1; shift ;;
    --no-build) NO_BUILD=1; shift ;;
    --force)    FORCE=1; shift ;;
    --report)
      if [ $# -lt 2 ]; then
        echo "usage error: --report needs a path" >&2
        exit 2
      fi
      REPORT="$2"; shift 2 ;;
    *)
      echo "usage: scripts/check-elab.sh [--rebase] [--list] [--no-build] [--force] [--report <path>]" >&2
      exit 2 ;;
  esac
done

if [ "$REBASE" -eq 1 ] && [ "$LIST_ONLY" -eq 1 ]; then
  echo "usage error: --rebase and --list are mutually exclusive" >&2
  exit 2
fi

cd "$ROOT" || exit 2

if [ ! -d "$SRC_DIR" ]; then
  echo "REGRESSION — elab: source tree not found: $ROOT/$SRC_DIR"
  exit 2
fi

# --- contention guard -------------------------------------------------------
# Only our own toolchain's servers matter; match the binary invocation rather
# than any command line mentioning the word "lean".
LSP_PIDS="$(pgrep -f 'bin/lean --server' 2>/dev/null | tr '\n' ' ' | sed 's/ *$//')"
LSP_MAX_MB=0
LSP_SUM_MB=0
if [ -n "$LSP_PIDS" ]; then
  LSP_MAX_MB="$(ps -o rss= -p "$(printf '%s' "$LSP_PIDS" | tr ' ' ',')" 2>/dev/null \
    | awk 'BEGIN{m=0} {v=$1/1024; if (v>m) m=v} END {printf "%.0f", m}')"
  LSP_SUM_MB="$(ps -o rss= -p "$(printf '%s' "$LSP_PIDS" | tr ' ' ',')" 2>/dev/null \
    | awk '{s+=$1/1024} END {printf "%.0f", s}')"
  : "${LSP_MAX_MB:=0}" "${LSP_SUM_MB:=0}"
fi

if [ "${LSP_MAX_MB:-0}" -gt "$LSP_RSS_MAX_MB" ] || [ "${LSP_SUM_MB:-0}" -gt "$LSP_RSS_TOTAL_MB" ]; then
  if [ "$FORCE" -eq 0 ]; then
    echo "SETUP — elab: Lean language server(s) holding large environments (pid(s): $LSP_PIDS;"
    echo "SETUP — elab: largest ${LSP_MAX_MB}MB, total ${LSP_SUM_MB}MB, limits ${LSP_RSS_MAX_MB}MB/${LSP_RSS_TOTAL_MB}MB)."
    echo "SETUP — elab: these contend for memory and cores, and this gate's only output is a timing."
    echo "SETUP — elab: Close the editing session and re-run, or pass --force to measure anyway"
    echo "SETUP — elab: (a --force run may not be rebased)."
    echo "REGRESSION — elab: refusing to measure under language-server contention"
    exit 2
  fi
  if [ "$REBASE" -eq 1 ]; then
    echo "usage error: --force may not be combined with --rebase; a contended run must never become the committed reference" >&2
    exit 2
  fi
  echo "WARNING — elab: measuring under language-server contention (--force); times are indicative only"
elif [ -n "$LSP_PIDS" ]; then
  # Present but idle: report it so a surprising number has this context attached,
  # and proceed. See the header on why presence alone must not refuse.
  echo "NOTE — elab: $(printf '%s' "$LSP_PIDS" | wc -w | tr -d ' ') idle language server(s) present (largest ${LSP_MAX_MB}MB, total ${LSP_SUM_MB}MB); below the ${LSP_RSS_MAX_MB}MB/${LSP_RSS_TOTAL_MB}MB contention limits, proceeding"
fi

# --- concurrency guard ------------------------------------------------------
# Canonicalised first, because the report lock is keyed on this string: two
# spellings of one path would otherwise take two locks and share a file.
mkdir -p "$(dirname "$REPORT")"
REPORT="$(cd "$(dirname "$REPORT")" && pwd)/$(basename "$REPORT")"

# The same argument as the language-server guard above, applied to the other
# thing that contends on this host: another gate run. This gate's only output
# is a timing, so a fixture tier dispatching ten workers alongside it does not
# degrade a reference column — it decides the verdict. So this gate takes the
# shared heavy-gate lock, and unlike the language-server guard there is no
# --force for it: a server can be idle and harmless, whereas a heavy gate
# holding that lock is by construction running. It also locks its report.
gate_lock_acquire "$SCRIPT_DIR/.gate-heavy.lock" "elab" \
  "the heavy-gate lock" \
  "wait for that run to finish; measuring elaboration time beside it would measure the scheduler" \
  || exit 2
gate_lock_acquire "$REPORT.lock" "elab" "$REPORT" \
  "wait for that run to finish, or pass --report <path> to write elsewhere" \
  || exit 2

# --- build precondition -----------------------------------------------------
# Every measurement below elaborates one file against its dependencies' oleans.
# If those are stale the first file to need them pays for rebuilding them and
# its number is meaningless, so the tree must be current before we start.
if [ "$NO_BUILD" -eq 0 ]; then
  if ! lake build >/dev/null 2>&1; then
    echo "SETUP — elab: 'lake build' failed; this gate measures a green tree only."
    echo "REGRESSION — elab: build precondition failed"
    exit 2
  fi
fi

# --- file discovery ---------------------------------------------------------
# Discovered, never hardcoded: a new module is measured the moment it exists,
# and then fails the gate until it has a baseline row.
FILES="$( { find "$SRC_DIR" -name '*.lean' -type f | sed 's|^\./||'
            for r in $ROOT_MODULES; do [ -f "$r" ] && echo "$r"; done
          } | sort )"

if [ -z "$FILES" ]; then
  echo "REGRESSION — elab: no source files selected under $SRC_DIR"
  exit 2
fi

# --- measure ----------------------------------------------------------------
RESULTS=""
RCFILE="$(mktemp)"

for f in $FILES; do
  TIMEFORMAT='%R'
  ELAPSED="$( { time { lake env lean "$f" >/dev/null 2>&1; echo $? >"$RCFILE"; } ; } 2>&1 )"
  RC="$(cat "$RCFILE")"
  if [ "$RC" -eq 0 ]; then STATUS="OK"; else STATUS="ERROR"; fi
  printf '%s\t%s\t%s\n' "$STATUS" "$ELAPSED" "$f"
  RESULTS="$RESULTS$STATUS	$ELAPSED	$f
"
done

printf '%s' "$RESULTS" > "$REPORT"

TOTAL="$(printf '%s' "$RESULTS" | awk -F'\t' 'NF{s+=$2} END {printf "%.1f", s}')"
NFILES="$(printf '%s' "$RESULTS" | grep -c .)"
NERR="$(printf '%s' "$RESULTS" | awk -F'\t' '$1=="ERROR"' | grep -c .)"

echo "---"
echo "elab: $NFILES file(s), $TOTAL s total, report: ${REPORT#$ROOT/}"

# --- list mode --------------------------------------------------------------
if [ "$LIST_ONLY" -eq 1 ]; then
  # --list compares no times, but a file that does not elaborate at all is a
  # fact rather than a comparison, and the exit code must stay honest.
  if [ "$NERR" -gt 0 ]; then
    printf '%s' "$RESULTS" | awk -F'\t' '$1=="ERROR" {print "ELAB — does not elaborate: " $3}'
    echo "REGRESSION — elab: $NERR file(s) failed to elaborate (--list compared no times)"
    exit 1
  fi
  echo "OK — elab: listed $NFILES file(s) in $TOTAL s (--list compares nothing)"
  exit 0
fi

# --- rebase -----------------------------------------------------------------
if [ "$REBASE" -eq 1 ]; then
  if [ "$NERR" -gt 0 ]; then
    printf '%s' "$RESULTS" | awk -F'\t' '$1=="ERROR" {print "ELAB — does not elaborate: " $3}'
    echo "REGRESSION — elab: refusing to rebase with $NERR file(s) failing to elaborate"
    exit 1
  fi
  {
    echo "# Elaboration-time baseline for Jaune — scripts/check-elab.sh"
    echo "#"
    echo "# STATUS<TAB>TIME<TAB>path. TIME is seconds to re-elaborate that file against"
    echo "# already-built dependencies, measured sequentially with no language server"
    echo "# alive. A file fails the gate above both ${DRIFT_FACTOR}x its time here and that time"
    echo "# plus ${DRIFT_FLOOR}s. Rewrite with: scripts/check-elab.sh --rebase"
    printf '%s' "$RESULTS"
  } > "$BASELINE"
  echo "OK — elab: baseline rebased with $NFILES file(s), $TOTAL s total"
  exit 0
fi

# --- compare ----------------------------------------------------------------
if [ ! -f "$BASELINE" ]; then
  echo "SETUP — elab: no baseline at ${BASELINE#$ROOT/}; create one with scripts/check-elab.sh --rebase"
  echo "REGRESSION — elab: baseline not found"
  exit 2
fi

BASE_ROWS="$(grep -vE '^[[:space:]]*(#|$)' "$BASELINE")"

VIOLATIONS=""
NOTES=""

for f in $FILES; do
  CUR_ROW="$(printf '%s' "$RESULTS" | awk -F'\t' -v p="$f" '$3==p {print; exit}')"
  CUR_STATUS="$(printf '%s' "$CUR_ROW" | cut -f1)"
  CUR_TIME="$(printf '%s' "$CUR_ROW" | cut -f2)"

  if [ "$CUR_STATUS" = "ERROR" ]; then
    VIOLATIONS="${VIOLATIONS}ELAB — does not elaborate: $f
"
    continue
  fi

  BASE_ROW="$(printf '%s' "$BASE_ROWS" | awk -F'\t' -v p="$f" '$3==p {print; exit}')"
  if [ -z "$BASE_ROW" ]; then
    VIOLATIONS="${VIOLATIONS}ELAB — no baseline row (new module must state its cost): $f
"
    continue
  fi
  BASE_TIME="$(printf '%s' "$BASE_ROW" | cut -f2)"

  VERDICT="$(awk -v c="$CUR_TIME" -v b="$BASE_TIME" -v k="$DRIFT_FACTOR" \
                 -v fl="$DRIFT_FLOOR" -v imp="$IMPROVE_FACTOR" 'BEGIN {
    if (c > b * k && c > b + fl) print "DRIFT"
    else if (b > fl && c < b * imp) print "IMPROVED"
    else print "OK"
  }')"

  case "$VERDICT" in
    DRIFT)
      VIOLATIONS="${VIOLATIONS}ELAB — $f: ${CUR_TIME}s vs baseline ${BASE_TIME}s
"
      ;;
    IMPROVED)
      NOTES="${NOTES}IMPROVED — elab: $f: ${CUR_TIME}s vs baseline ${BASE_TIME}s; refresh with --rebase
"
      ;;
  esac
done

# Stale rows are a warning, never a failure — same policy as check-hygiene.sh.
# Note the '%s\n': command substitution stripped BASE_ROWS' trailing newline, and
# `while read` drops a final line that lacks one, which silently skipped the last
# row in the baseline.
printf '%s\n' "$BASE_ROWS" | while IFS= read -r row; do
  [ -z "$row" ] && continue
  p="$(printf '%s' "$row" | cut -f3)"
  [ -f "$ROOT/$p" ] || echo "WARNING — elab: stale baseline row, file no longer in source: $p"
done

[ -n "$NOTES" ] && printf '%s' "$NOTES"

if [ -n "$VIOLATIONS" ]; then
  printf '%s' "$VIOLATIONS"
  NVIO="$(printf '%s' "$VIOLATIONS" | grep -c .)"
  BASE_TOTAL="$(printf '%s' "$BASE_ROWS" | awk -F'\t' 'NF{s+=$2} END {printf "%.1f", s}')"
  echo "REGRESSION — elab: $NVIO file(s) slower than ${DRIFT_FACTOR}x baseline (or newly failing); $TOTAL s total vs $BASE_TOTAL s baseline"
  exit 1
fi

BASE_TOTAL="$(printf '%s' "$BASE_ROWS" | awk -F'\t' 'NF{s+=$2} END {printf "%.1f", s}')"
echo "OK — elab: all $NFILES file(s) within ${DRIFT_FACTOR}x baseline; $TOTAL s total vs $BASE_TOTAL s baseline"
exit 0
