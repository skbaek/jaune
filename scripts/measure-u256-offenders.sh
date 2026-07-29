#!/usr/bin/env bash
# Record the four Step-1/Step-7 U256-plan offender measurements without
# overwriting an earlier run.  The opt.md arc this served is closed, but the
# script remains a working instrument for timing these files.
#
# Each report line is check.sh's PASS/FAIL classification plus the wall time,
# which is the measurement of interest here; every offender runs to completion
# under the uniform wall-clock guard, so a guard trip is not measurement data
# but a harness error — check.sh aborts and exits nonzero, and this script
# propagates that rather than recording anything.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
FIXTURES="${JAUNE_FIXTURES:-$HOME/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests}"

usage() {
  echo "usage: scripts/measure-u256-offenders.sh <label> [--no-build]" >&2
  echo "example: scripts/measure-u256-offenders.sh step1" >&2
  exit 2
}

[ $# -ge 1 ] && [ $# -le 2 ] || usage
LABEL="$1"
case "$LABEL" in
  *[!A-Za-z0-9._-]*|'')
    echo "label may contain only letters, digits, dot, underscore, and hyphen" >&2
    exit 2
    ;;
esac

NO_BUILD=0
if [ $# -eq 2 ]; then
  [ "$2" = "--no-build" ] || usage
  NO_BUILD=1
fi

OUT_DIR="${JAUNE_REPORT_DIR:-$SCRIPT_DIR}"
mkdir -p "$OUT_DIR"

run_measurement() {
  local name="$1"
  local path="$2"
  local build_flag="$3"
  local report="$OUT_DIR/report-$LABEL-$name.txt"
  local args=(--dir "$path" --report "$report")
  if [ "$build_flag" -eq 0 ]; then
    args+=(--no-build)
  fi

  echo "--- Measuring $name ---"
  local out rc verdict
  # `local out=$(...)` would mask the exit status, so declare first.
  out="$("$SCRIPT_DIR/check.sh" "${args[@]}")"
  rc=$?
  printf '%s\n' "$out"
  verdict="$(printf '%s\n' "$out" | tail -1)"
  # A guard trip aborts the tier mid-list, so a partially written report is
  # not evidence of a completed measurement: fail loudly instead.
  case "$verdict" in
    "HARNESS ERROR"*)
      echo "RED — $name: harness error, measurement discarded — $verdict" >&2
      return 1
      ;;
  esac
  if [ ! -s "$report" ]; then
    echo "RED — measurement did not produce $report" >&2
    return "$rc"
  fi
  echo "RECORDED — $report (check.sh exit $rc; PASS/FAIL classifications and wall times are retained for review)"
  return 0
}

BUILD_FIRST=$((1 - NO_BUILD))
run_measurement \
  vmPerformance \
  "$FIXTURES/GeneralStateTests/VMTests/vmPerformance" \
  "$BUILD_FIRST" || exit $?

run_measurement \
  CALLBlake2f_MaxRounds \
  "$FIXTURES/GeneralStateTests/stTimeConsuming/CALLBlake2f_MaxRounds.json" \
  0 || exit $?

run_measurement \
  static_Call50000_sha256 \
  "$FIXTURES/GeneralStateTests/stTimeConsuming/static_Call50000_sha256.json" \
  0 || exit $?

echo "OK — offender measurements recorded with label $LABEL"
