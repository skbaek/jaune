#!/usr/bin/env bash
# The jump-destination control for EIP-8024 (goal C, G4; programme D8 and R3).
#
# `Jaune/Machine.lean` proves `pinnedJumpDestsFrom_eq_legacy`: the pinned
# Amsterdam `get_valid_jump_destinations` walk, which skips the immediate of an
# accepted `DUPN`/`SWAPN`/`EXCHANGE`, computes the same destinations as the
# pre-Amsterdam walk on every byte array. This gate is the falsifier for that
# theorem's *statement* and for the interpreter's backward scan `jumpable`
# agreeing with both: `jaune --jumpdest-control` generates a reproducible
# pseudo-random blob per seed at EIP-7954's 64 KiB code ceiling and compares
# the three computations position by position, printing per-phase times.
#
# The seeds are an explicit list, and that is deliberate: on this host a
# 64 KiB blob at seeds 20260906, 20260910, 20260911, 20260912, 20260916,
# 20260917 and 20260920 does not finish within 45 s (measured 2026-09-06), so
# a gate over consecutive seeds would not terminate inside the catalogue's
# runtime rule. Those seeds are programme R3's measurement -- the cost of the
# jump-destination analysis at the raised code ceiling -- and are recorded in
# goal C's evidence; they are not evidence about the theorem, whose statement
# this gate falsifies on the blobs it runs. Pass `--seeds` to run others.
#
# Usage: scripts/check-jumpdest.sh [--seeds "s1 s2 ..."] [--size N]
#   defaults: seeds 20260905 20260907 20260908 20260909 20260913 20260914
#             20260915 20260918 20260919; size 65536.
#
# CLI contract: exit 0 iff the control held on every seed; the last line is a
# single verdict. Light: no corpus, no Lean elaboration, no lock. Reads the
# built binary and never builds it.

set -uo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/jaune"
SEEDS="20260905 20260907 20260908 20260909 20260913 20260914 20260915 20260918 20260919"
SIZE=65536
while [ $# -gt 0 ]; do
  case "$1" in
    --seeds) SEEDS="$2"; shift 2 ;;
    --size) SIZE="$2"; shift 2 ;;
    *) echo "usage: scripts/check-jumpdest.sh [--seeds \"s1 s2 ...\"] [--size N]" >&2; exit 2 ;;
  esac
done
if [ ! -x "$BIN" ]; then
  echo "REGRESSION — jumpdest: jaune binary not found at $BIN; build the executable first"
  exit 2
fi
FAILS=0; RUNS=0; SLOWEST=0; SLOWSEED=""
for s in $SEEDS; do
  RUNS=$((RUNS + 1))
  START=$(date +%s%N)
  OUT="$("$BIN" --jumpdest-control "$s" 1 "$SIZE" 2>&1)"; RC=$?
  END=$(date +%s%N)
  MS=$(( (END - START) / 1000000 ))
  printf '%s\n' "$OUT" | grep -E '^blob' | sed "s/^blob 0/seed $s/"
  if [ "$RC" -ne 0 ] || ! printf '%s\n' "$OUT" | grep -q '^OK'; then
    FAILS=$((FAILS + 1)); printf '%s\n' "$OUT" | grep -E '^RED|error' | head -3
  fi
  if [ "$MS" -gt "$SLOWEST" ]; then SLOWEST=$MS; SLOWSEED=$s; fi
done
if [ "$FAILS" -ne 0 ]; then
  echo "RED — jumpdest: $FAILS of $RUNS seed(s) disagreed at $SIZE bytes; see the lines above"
  exit 1
fi
echo "OK — jumpdest: pinned walk = legacy walk = jumpable on $RUNS blob(s) × $SIZE bytes (seeds $SEEDS); slowest blob $SLOWEST ms (seed $SLOWSEED)"
exit 0
