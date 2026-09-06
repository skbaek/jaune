#!/usr/bin/env bash
# Bounded call-depth memory regression for Jaune (CI lint tier).
#
# Runs the native `jaune-memory-probe` at two fixed points and fails if either
# exceeds an asserted peak resident set. This is the gate that makes the
# 2026-09 calldata-retention fix a property the repository defends rather than
# a property somebody once measured.
#
# WHAT IT ASSERTS. Both points drive a 1,000,000-byte call input through a
# 1,024-deep call path — the shape of the fixture that once needed more than
# 9 GiB — one point per call family:
#
#   jaune-memory-probe --staticcall 1024 1000000
#   jaune-memory-probe --call       1024 1000000
#
# Both must stay within BUDGET_BYTES (256 MiB by default). On the candidate
# each runs in about 0.05 s at roughly 104 MiB, so the budget carries about
# 2.5x margin — wide enough that ordinary allocator and toolchain variation
# does not move it, narrow enough that ONE retained calldata copy per frame
# cannot fit: that regression costs about 32 MB per live frame, so it crosses
# 256 MiB by depth 8 and would reach tens of gigabytes at depth 1024.
#
# BOTH FAMILIES ARE THE POINT. Until 2026-09-06 only STATICCALL was
# specialized, and the CALL analogue retained exactly as the pre-fix code did:
# the pinned corpus file `call1_mb1024_calldepth` peaked at 2.08 GiB in
# isolation and stayed under its 3 GiB row only because its gas limit bounded
# the recursion at roughly 65 frames. A single-family gate would have kept
# missing that. CALLCODE and DELEGATECALL share the same specialization; they
# are not separate points here because they share `genericCall.stepCached` with
# the two that are.
#
# WHICH MECHANISM, ON WHICH PLATFORM. The peak is the child's high-water
# resident set from `getrusage(RUSAGE_CHILDREN).ru_maxrss` — POSIX, present on
# Linux and macOS alike, needing no cgroup, container or privilege — converted
# from its platform's unit by `scripts/memory_probe_budget.py`. A sampling
# watchdog additionally kills a child that crosses the budget while running
# (`/proc/<pid>/statm` on Linux, `ps -o rss=` elsewhere), which is what lets a
# lost-property run be reported instead of taking the machine down. **This row
# therefore has no Linux, cgroup or 16 GB dependency**: it is the portable form
# of the assertion, and the cgroup-based `scripts/measure-resource.py` remains
# the instrument for the resource-acceptance rows, which do need Linux.
#
# It needs the built binary and no corpus, exactly as `scripts/check-cli.sh`
# does, and it never builds one itself — `jaune-memory-probe` is a Lake
# default target, so an ordinary `lake build` produces it.
#
# Usage: scripts/check-memory-probe.sh [--budget-bytes N] [--json-dir DIR]
#
#   --budget-bytes N  override the asserted peak (accepts K/M/G suffixes).
#                     Raising it is a change to the gate, not a way past it.
#   --json-dir DIR    write one JSON record per point into DIR.
#
# CLI contract: exit 0 iff every point stayed within the budget and exited 0;
# the last line of output is a single unambiguous verdict. Exit 1 on a
# violation, 2 on a usage or setup error. It writes nothing under the
# repository and takes no lock: it is a single short-lived process per point.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
PROBE="$ROOT/.lake/build/bin/jaune-memory-probe"
RUNNER="$SCRIPT_DIR/memory_probe_budget.py"

BUDGET="268435456"   # 256 MiB
JSON_DIR=""

while [ $# -gt 0 ]; do
  case "$1" in
    --budget-bytes)
      [ $# -ge 2 ] || { echo "usage: scripts/check-memory-probe.sh [--budget-bytes N] [--json-dir DIR]" >&2; exit 2; }
      BUDGET="$2"; shift 2 ;;
    --json-dir)
      [ $# -ge 2 ] || { echo "usage: scripts/check-memory-probe.sh [--budget-bytes N] [--json-dir DIR]" >&2; exit 2; }
      JSON_DIR="$2"; shift 2 ;;
    *)
      echo "usage: scripts/check-memory-probe.sh [--budget-bytes N] [--json-dir DIR]" >&2
      exit 2 ;;
  esac
done

if [ ! -x "$PROBE" ]; then
  echo "REGRESSION — memory probe: built probe not found: $PROBE"
  echo "  run \`lake build\` first; jaune-memory-probe is a default target"
  exit 2
fi
if [ ! -f "$RUNNER" ]; then
  echo "REGRESSION — memory probe: runner not found: $RUNNER"
  exit 2
fi

DEPTH=1024
INPUT=1000000
FAILURES=0
SUMMARY=""

for FAMILY in staticcall call; do
  ARGS=(--budget-bytes "$BUDGET" --timeout-seconds 120)
  if [ -n "$JSON_DIR" ]; then
    ARGS+=(--json-out "$JSON_DIR/memory-probe-$FAMILY-d$DEPTH-i$INPUT.json")
  fi
  OUTPUT="$(python3 "$RUNNER" "${ARGS[@]}" -- "$PROBE" "--$FAMILY" "$DEPTH" "$INPUT" 2>&1)"
  STATUS=$?
  RECORD="$(printf '%s\n' "$OUTPUT" | grep '^PROBE ' | head -1 | cut -c7-)"
  if [ -z "$RECORD" ]; then
    echo "REGRESSION — memory probe: $FAMILY produced no record"
    printf '%s\n' "$OUTPUT"
    exit 2
  fi
  READING="$(printf '%s' "$RECORD" | python3 -c '
import json, sys
r = json.load(sys.stdin)
print("%s %d %d %.3f" % (r["status"], r["peak_bytes"], r["budget_bytes"], r["elapsed_seconds"]))
')"
  set -- $READING
  VERDICT="$1"; PEAK="$2"; LIMIT="$3"; ELAPSED="$4"
  MIB="$(python3 -c "print('%.1f' % ($PEAK / 1048576.0))")"
  LIMIT_MIB="$(python3 -c "print('%.1f' % ($LIMIT / 1048576.0))")"
  if [ "$VERDICT" = "OK" ] && [ $STATUS -eq 0 ]; then
    echo "OK   $FAMILY depth=$DEPTH input=$INPUT peak=${MIB} MiB <= ${LIMIT_MIB} MiB in ${ELAPSED}s"
  else
    echo "MEMORY PROBE — $FAMILY depth=$DEPTH input=$INPUT: $VERDICT at peak=${MIB} MiB against ${LIMIT_MIB} MiB"
    printf '%s\n' "$OUTPUT" | grep -v '^PROBE '
    FAILURES=$((FAILURES + 1))
  fi
  SUMMARY="$SUMMARY $FAMILY=${MIB}MiB"
done

if [ "$FAILURES" -ne 0 ]; then
  echo "REGRESSION — memory probe: $FAILURES of 2 point(s) exceeded the asserted peak or failed"
  exit 1
fi

echo "OK — memory probe: 2/2 points at depth $DEPTH, input $INPUT within $(python3 -c "print('%.0f' % ($BUDGET / 1048576.0))") MiB;$SUMMARY"
exit 0
