#!/usr/bin/env bash
# Generated-vector conformance gate: every file in the manifest below is run at
# its precompile address under the fork whose rules it is stated against, and
# the gate passes iff every one of them passes.
#
# Coverage is a separate question from correctness, and this gate checks both.
# `jaune --vectors` reports whatever a file happens to hold, so a file that
# quietly lost cases would still go green while testing less than it claims. Two
# things stop that: get_cases below declares how many cases each file must
# contribute and the run is cross-checked against it, and the binary refuses a
# file with no cases at all rather than reporting a vacuous 0/0 pass.
#
# Usage: scripts/check-vectors.sh [--jobs <n>|auto]
#
#   --jobs <n>  run <n> vector files concurrently (default 1 = sequential).
#               `auto` resolves to the machine's logical-core count.
#
# Parallel dispatch (--jobs)
# --------------------------
# Vector files are independent, so --jobs <n> dispatches them across <n>
# concurrent processes. Sequential (--jobs 1) is the default and its behaviour is
# untouched: same manifest, same ordering, same authoritative timings.
#
# What parallel mode changes:
#
#   * Timings become reference-only. A contended run's wall time reflects
#     scheduling, not the vectors, so the verdict line says so. The gate itself
#     is unaffected — it only ever compared per-file pass/fail.
#   * Dispatch order becomes longest-first (see get_weight). This matters more
#     here than in the fixture harnesses: this suite is dominated by a handful of
#     pairing-heavy files, and starting one of them late adds its full runtime to
#     the tail.
#   * A per-file wall-clock guard applies. The sequential path streams each
#     runner's output as it goes, so a hang there is visible immediately; a
#     parallel run assembles its output at the end, where a hang would otherwise
#     be indistinguishable from slow progress. The guard is what restores that,
#     and it is a "this should never fire" hang detector, never a performance
#     budget: the slowest file in the manifest runs ~370s, so the 3600s default
#     clears it by nearly 10x. An explicit JAUNE_TIMEOUT wins.
#
# What parallel mode does NOT change: the report and stdout are assembled in
# manifest order, not completion order. Two runs of the same manifest therefore
# produce byte-identical output whatever the job count, so any two reports diff
# cleanly against each other.
#
# One run at a time: this suite takes an exclusive lock on its report and on the
# shared heavy-gate lock, and a second run that would contend is REFUSED
# immediately rather than queued. See scripts/gate-lock.sh.
#
# CLI contract: exit 0 if and only if the gate passes; the last line of output
# is a single unambiguous verdict line. A refusal exits 2 — the gate did not
# fail, it did not run.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/jaune"

# Captured before the argument loop consumes them; the lock records the whole
# command line so a refusal can name what is holding it.
GATE_CMDLINE="$0 $*"
. "$SCRIPT_DIR/gate-lock.sh"

usage() {
  echo "usage: scripts/check-vectors.sh [--jobs <n>|auto]" >&2
  exit 2
}

# Logical-core count. Sizing the pool below this only idles cores the scheduler
# would otherwise use: efficiency cores are slow but not worthless, and no cap
# can steer work away from them anyway — there is no affinity API and the
# scheduler migrates rather than pins.
all_cores() {
  N="$(sysctl -n hw.ncpu 2>/dev/null || true)"
  if [ -z "$N" ]; then N="$(getconf _NPROCESSORS_ONLN 2>/dev/null || true)"; fi
  if [ -z "$N" ]; then N=4; fi
  echo "$N"
}

JOBS=1
while [ "$#" -gt 0 ]; do
  case "$1" in
    --jobs) shift; [ "$#" -gt 0 ] || usage; JOBS="$1" ;;
    *) echo "error: unknown argument $1" >&2; usage ;;
  esac
  shift
done

if [ "$JOBS" = "auto" ]; then
  JOBS="$(all_cores)"
fi
case "$JOBS" in
  ''|*[!0-9]*)
    echo "error: --jobs takes a positive integer or 'auto', not $JOBS" >&2
    exit 2
    ;;
esac
[ "$JOBS" -ge 1 ] || { echo "error: --jobs must be at least 1" >&2; exit 2; }

# Hang detector for the parallel path only; see the header note. The slowest file
# in the manifest runs ~370s, so 3600s clears it by nearly 10x while still
# tripping long before anything pathological.
GUARD="${JAUNE_TIMEOUT:-3600}"
[ "$GUARD" -gt 0 ] 2>/dev/null || { echo "error: JAUNE_TIMEOUT must be positive" >&2; exit 2; }

if [ ! -x "$BIN" ]; then
  echo "ERROR: jaune binary not found. Run 'lake build' first."
  exit 1
fi

REPORT="$SCRIPT_DIR/report-vectors.txt"

# One cleanup function, one EXIT trap, installed once: a second `trap ... EXIT`
# would silently replace this one and leak the scratch directory. TMPD is the
# scratch for both modes — the parallel pool's chunks and the case-count
# cross-check both live there.
TMPD=""
cleanup() {
  gate_lock_release_all
  if [ -n "$TMPD" ]; then rm -rf "$TMPD"; fi
  return 0
}
trap cleanup EXIT

# This suite is a Medium gate in every mode (~7.8 min sequential, ~1.5 min at
# --jobs auto), so it always takes the heavy-gate lock as well as its report
# lock. See scripts/gate-lock.sh.
gate_lock_heavy_acquire "vectors" \
  "the heavy-gate lock" \
  "wait for that run to finish" \
  || exit 2
gate_lock_acquire "$REPORT.lock" "vectors" "$REPORT" \
  "wait for that run to finish" \
  || exit 2

: > "$REPORT"

TMPD="$(mktemp -d)"

VECTORS_DIR="$SCRIPT_DIR/vectors"
CONTROL_FILES=(
  bn256Add.json
  bn256ScalarMul.json
  bn256Pairing.json
  blake2F.json
  modexp_eip2565.json
)

# Hash precompiles, generated against the pinned EELS oracle by
# scripts/gen-hash-precompile-vectors.py. They are their own group rather than
# additions to either group above: the controls are a fixed five-file
# anti-vacuity set whose denominator is quoted in scripts/GATES.md and is more
# useful held constant, and the group below it is BLS and point-evaluation, which
# these are not. Their boundary-length sweeps sit at the 55/56 padding seam, the
# 63/64/65 block seam and the 31/32/33 gas-word seam; see the generator.
HASH_FILES=(
  sha256.json
  ripemd160.json
)

# This is a target manifest, not a directory scan: deleting a vector file must
# make the gate fail rather than silently reducing the tested set.
PRECOMPILE_FILES=(
  pointEvaluation.json
  add_G1_bls.json
  fail-add_G1_bls.json
  blsG1Add.json
  fail-blsG1Add.json
  mul_G1_bls.json
  fail-mul_G1_bls.json
  msm_G1_bls.head.json
  fail-msm_G1_bls.json
  blsG1Mul.json
  fail-blsG1Mul.json
  blsG1MultiExp.head.json
  fail-blsG1MultiExp.json
  add_G2_bls.json
  fail-add_G2_bls.json
  blsG2Add.json
  fail-blsG2Add.json
  mul_G2_bls.json
  fail-mul_G2_bls.json
  msm_G2_bls.head.json
  fail-msm_G2_bls.json
  blsG2Mul.json
  fail-blsG2Mul.json
  blsG2MultiExp.head.json
  fail-blsG2MultiExp.json
  pairing_check_bls.json
  fail-pairing_check_bls.json
  blsPairing.shard1.json
  blsPairing.shard2.json
  blsPairing.shard3.json
  blsPairing.shard4.json
  blsPairing.shard5.json
  blsPairing.shard6.json
  blsPairing.shard7.json
  blsPairing.shard8.json
  fail-blsPairing.json
  map_fp_to_G1_bls.json
  fail-map_fp_to_G1_bls.json
  blsMapG1.json
  fail-blsMapG1.json
  map_fp2_to_G2_bls.json
  fail-map_fp2_to_G2_bls.json
  blsMapG2.json
  fail-blsMapG2.json
)

# Vectors that only hold under Osaka rules.  They are a separate group because
# each one is run with an explicit --network and could not run under Prague:
# modexp_eip7883.json reprices MODEXP, and p256Verify.json is at an address
# Prague does not activate at all.
OSAKA_FILES=(
  modexp_eip7883.json
  p256Verify.json
)

EXPECTED_FILES=("${CONTROL_FILES[@]}" "${HASH_FILES[@]}" "${PRECOMPILE_FILES[@]}" "${OSAKA_FILES[@]}")

# Files that live in the vector directory but are deliberately not dispatched by
# this gate.  Listing them keeps the stray-file scan below able to reject a
# genuinely unlisted JSON file without also rejecting these.
#
#   u256.json       run by check-u256.sh, not through the precompile dispatch.
#   fake-exp.json   run by check-fake-exp.sh, likewise: a differential grid
#                   against the pinned EELS `taylor_exponential`, not a
#                   precompile vector file this gate could dispatch.
#   blsPairing.json the shard source.  Its 106 cases run as the eight
#                   blsPairing.shardN.json entries above, which are an exact
#                   partition of it — verified by
#                   `python3 scripts/gen-vector-shards.py --check`, not assumed.
#                   Running the source as well would only duplicate that work,
#                   but it stays committed so the partition remains checkable.
AUXILIARY_FILES=(
  u256.json
  fake-exp.json
  blsPairing.json
)

# Regenerate compact MSM samples from the pinned full files in
# scripts/vectors/SOURCES.md:
#   jq '.[0:32]' msm_G1_bls.json > scripts/vectors/msm_G1_bls.head.json
#   jq '.[0:32]' msm_G2_bls.json > scripts/vectors/msm_G2_bls.head.json
#   jq '.[0:32]' blsG1MultiExp.json > scripts/vectors/blsG1MultiExp.head.json
#   jq '.[0:32]' blsG2MultiExp.json > scripts/vectors/blsG2MultiExp.head.json
#
# The blsPairing shards are a different thing and must not be hand-cut: they are
# a *partition* of blsPairing.json, not a sample of it, so regenerate and verify
# them with the generator, which checks that property rather than assuming it:
#   python3 scripts/gen-vector-shards.py            # rewrite the shards
#   python3 scripts/gen-vector-shards.py --check     # verify the committed ones

# The fork whose rules each file is stated against.  Every file is run with an
# explicit --network so that a repriced or newly activated precompile is tested
# under the rules that define it, never under whatever the binary defaults to.
# sha256.json and ripemd160.json take the Prague default deliberately: both
# precompiles are Frontier-era and neither has ever been repriced, so Prague is
# the latest fork whose rules define them unchanged and no separate row is right.
get_fork() {
  case "$1" in
    modexp_eip7883.json|p256Verify.json) echo "Osaka" ;;
    *) echo "Prague" ;;
  esac
}

get_addr() {
  case "$1" in
    bn256Add.json) echo "06" ;;
    bn256ScalarMul.json) echo "07" ;;
    bn256Pairing.json) echo "08" ;;
    blake2F.json) echo "09" ;;
    modexp_eip2565.json) echo "05" ;;
    sha256.json) echo "02" ;;
    ripemd160.json) echo "03" ;;
    modexp_eip7883.json) echo "05" ;;
    p256Verify.json) echo "0100" ;;
    pointEvaluation.json) echo "0a" ;;
    add_G1_bls.json|fail-add_G1_bls.json|blsG1Add.json|fail-blsG1Add.json) echo "0b" ;;
    mul_G1_bls.json|fail-mul_G1_bls.json|msm_G1_bls.head.json|fail-msm_G1_bls.json|blsG1Mul.json|fail-blsG1Mul.json|blsG1MultiExp.head.json|fail-blsG1MultiExp.json) echo "0c" ;;
    add_G2_bls.json|fail-add_G2_bls.json|blsG2Add.json|fail-blsG2Add.json) echo "0d" ;;
    mul_G2_bls.json|fail-mul_G2_bls.json|msm_G2_bls.head.json|fail-msm_G2_bls.json|blsG2Mul.json|fail-blsG2Mul.json|blsG2MultiExp.head.json|fail-blsG2MultiExp.json) echo "0e" ;;
    pairing_check_bls.json|fail-pairing_check_bls.json|blsPairing.json|fail-blsPairing.json) echo "0f" ;;
    blsPairing.shard*.json) echo "0f" ;;
    map_fp_to_G1_bls.json|fail-map_fp_to_G1_bls.json|blsMapG1.json|fail-blsMapG1.json) echo "10" ;;
    map_fp2_to_G2_bls.json|fail-map_fp2_to_G2_bls.json|blsMapG2.json|fail-blsMapG2.json) echo "11" ;;
    *) echo "" ;;
  esac
}

# Dispatch weight in seconds, used only to order the parallel pool longest-first
# and never as gate input: a stale weight costs makespan, never correctness.
#
# Only files that are not near-instant need an entry. The other 34 files in the
# manifest run in under a second each and about 2.5s between them, so naming
# them would be noise. An unnamed file weighs 0 and dispatches last, which is
# also the right default for a newly added vector whose cost is unknown.
#
# Reference times measured sequentially on a 10-core Apple M5. The eight
# blsPairing shards are balanced by construction (see gen-vector-shards.py), so
# they share one weight; before it was sharded, that file alone was ~80% of this
# suite's sequential wall time and set its parallel makespan single-handedly.
# See scripts/GATES.md.
get_weight() {
  case "$1" in
    blsPairing.shard*.json) echo 46 ;;
    bn256Pairing.json) echo 26 ;;
    p256Verify.json) echo 20 ;;
    pairing_check_bls.json) echo 20 ;;
    blsG2MultiExp.head.json) echo 13 ;;
    fail-blsPairing.json) echo 6 ;;
    blsMapG2.json) echo 4 ;;
    blsG1MultiExp.head.json) echo 2 ;;
    blake2F.json) echo 1.5 ;;
    pointEvaluation.json) echo 1 ;;
    *) echo 0 ;;
  esac
}

# The number of cases each file must contribute, cross-checked after the run
# against the `n/n` count the runner itself reports.
#
# Without this the gate is blind to coverage. `jaune --vectors` reports whatever
# the file happens to hold and passes if all of it passes, so a file that lost
# cases — a bad shard slice, a truncated regeneration, a jq mistake — still goes
# green while testing less than it claims. The address and fork tables above pin
# *how* each file is run; this pins *how much* is there to run.
#
# An entry is therefore mandatory: a file with no declared count is a
# configuration error, not a file that skips the check. That is what forces a
# newly added vector to state its size.
#
# These counts are facts about the committed files (`jq length`), not targets, so
# a deliberate corpus change updates them in the same commit that changes the
# vectors.
get_cases() {
  case "$1" in
    bn256Add.json) echo 16 ;;
    bn256ScalarMul.json) echo 19 ;;
    bn256Pairing.json) echo 14 ;;
    blake2F.json) echo 5 ;;
    modexp_eip2565.json) echo 47 ;;
    sha256.json) echo 81 ;;
    ripemd160.json) echo 85 ;;
    modexp_eip7883.json) echo 45 ;;
    p256Verify.json) echo 782 ;;
    pointEvaluation.json) echo 1 ;;
    add_G1_bls.json) echo 9 ;;
    fail-add_G1_bls.json) echo 7 ;;
    blsG1Add.json) echo 112 ;;
    fail-blsG1Add.json) echo 6 ;;
    mul_G1_bls.json) echo 11 ;;
    fail-mul_G1_bls.json) echo 8 ;;
    msm_G1_bls.head.json) echo 32 ;;
    fail-msm_G1_bls.json) echo 8 ;;
    blsG1Mul.json) echo 11 ;;
    fail-blsG1Mul.json) echo 7 ;;
    blsG1MultiExp.head.json) echo 32 ;;
    fail-blsG1MultiExp.json) echo 7 ;;
    add_G2_bls.json) echo 9 ;;
    fail-add_G2_bls.json) echo 7 ;;
    blsG2Add.json) echo 112 ;;
    fail-blsG2Add.json) echo 6 ;;
    mul_G2_bls.json) echo 11 ;;
    fail-mul_G2_bls.json) echo 8 ;;
    msm_G2_bls.head.json) echo 32 ;;
    fail-msm_G2_bls.json) echo 8 ;;
    blsG2Mul.json) echo 11 ;;
    fail-blsG2Mul.json) echo 7 ;;
    blsG2MultiExp.head.json) echo 32 ;;
    fail-blsG2MultiExp.json) echo 7 ;;
    pairing_check_bls.json) echo 15 ;;
    fail-pairing_check_bls.json) echo 25 ;;
    blsPairing.shard1.json) echo 14 ;;
    blsPairing.shard2.json) echo 14 ;;
    blsPairing.shard3.json) echo 13 ;;
    blsPairing.shard4.json) echo 13 ;;
    blsPairing.shard5.json) echo 13 ;;
    blsPairing.shard6.json) echo 13 ;;
    blsPairing.shard7.json) echo 13 ;;
    blsPairing.shard8.json) echo 13 ;;
    fail-blsPairing.json) echo 9 ;;
    map_fp_to_G1_bls.json) echo 5 ;;
    fail-map_fp_to_G1_bls.json) echo 5 ;;
    blsMapG1.json) echo 105 ;;
    fail-blsMapG1.json) echo 5 ;;
    map_fp2_to_G2_bls.json) echo 5 ;;
    fail-map_fp2_to_G2_bls.json) echo 5 ;;
    blsMapG2.json) echo 105 ;;
    fail-blsMapG2.json) echo 5 ;;
    *) echo "" ;;
  esac
}

is_control_file() {
  local file="$1"
  local control
  for control in "${CONTROL_FILES[@]}"; do
    [ "$file" = "$control" ] && return 0
  done
  return 1
}

is_hash_file() {
  local file="$1"
  local hash
  for hash in "${HASH_FILES[@]}"; do
    [ "$file" = "$hash" ] && return 0
  done
  return 1
}

is_osaka_file() {
  local file="$1"
  local osaka
  for osaka in "${OSAKA_FILES[@]}"; do
    [ "$file" = "$osaka" ] && return 0
  done
  return 1
}

is_expected_file() {
  local file="$1"
  local expected
  for expected in "${EXPECTED_FILES[@]}"; do
    [ "$file" = "$expected" ] && return 0
  done
  for expected in "${AUXILIARY_FILES[@]}"; do
    [ "$file" = "$expected" ] && return 0
  done
  return 1
}

# The three group banners, named once so that the sequential path and the
# parallel path's reassembly cannot drift apart.
HDR_CONTROL='--- Running control files ---'
HDR_HASH='--- Running hash-precompile files ---'
HDR_PRECOMPILE='--- Running BLS and point-evaluation files ---'
HDR_OSAKA='--- Running Osaka files ---'

group_header() {
  case "$1" in
    control) printf '%s\n' "$HDR_CONTROL" ;;
    hash) printf '%s\n' "$HDR_HASH" ;;
    osaka) printf '%s\n' "$HDR_OSAKA" ;;
    *) printf '%s\n' "$HDR_PRECOMPILE" ;;
  esac
}

control_passes=0
passed_files=0
failed_files=0
missing_files=0
configuration_errors=0

START_ALL="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"

run_vector_file() {
  local file="$1"
  local addr
  local fork
  local path
  local runner_status
  local verdict
  local group

  addr="$(get_addr "$file")"
  fork="$(get_fork "$file")"
  path="$VECTORS_DIR/$file"
  if [ ! -f "$path" ]; then
    printf 'MISSING\t%s\n' "$file" | tee -a "$REPORT"
    missing_files=$((missing_files + 1))
    return
  fi
  if [ -z "$addr" ]; then
    printf 'CONFIGURATION ERROR: unknown address for %s\n' "$file" | tee -a "$REPORT"
    configuration_errors=$((configuration_errors + 1))
    return
  fi

  if is_control_file "$file"; then
    group="control"
  elif is_hash_file "$file"; then
    group="hash"
  elif is_osaka_file "$file"; then
    group="osaka"
  else
    group="BLS/point-eval"
  fi
  printf 'Running %s at address %s under %s\n' "$file" "$addr" "$fork" | tee -a "$REPORT"
  "$BIN" --vectors "$addr" "$path" --network "$fork" | tee -a "$REPORT"
  runner_status=${PIPESTATUS[0]}
  if [ "$runner_status" -eq 0 ]; then
    verdict="OK"
    passed_files=$((passed_files + 1))
  else
    verdict="RED"
    failed_files=$((failed_files + 1))
  fi
  printf 'MATRIX\t%s\t%s\t%s\n' "$group" "$verdict" "$file" | tee -a "$REPORT"
  if [ "$group" = "control" ] && [ "$runner_status" -eq 0 ]; then
    control_passes=$((control_passes + 1))
  fi
}

if [ "$JOBS" -gt 1 ]; then
  RUNNER="$SCRIPT_DIR/run-vector.sh"
  [ -x "$RUNNER" ] || {
    echo "error: parallel runner not found or not executable: $RUNNER" >&2
    exit 2
  }
  WORK="$TMPD/work"
  CHUNKS="$WORK/chunks"
  mkdir -p "$CHUNKS"

  # Number the whole manifest in *report* order, group by group. Dispatch order
  # is chosen separately below; keeping the two apart is what lets a parallel
  # report be reassembled in the order a sequential run would have produced.
  : > "$WORK/plan"
  plan_idx=0
  for file in "${CONTROL_FILES[@]}"; do
    plan_idx=$((plan_idx + 1))
    printf '%d\t%s\t%s\n' "$plan_idx" 'control' "$file" >> "$WORK/plan"
  done
  for file in "${HASH_FILES[@]}"; do
    plan_idx=$((plan_idx + 1))
    printf '%d\t%s\t%s\n' "$plan_idx" 'hash' "$file" >> "$WORK/plan"
  done
  for file in "${PRECOMPILE_FILES[@]}"; do
    plan_idx=$((plan_idx + 1))
    printf '%d\t%s\t%s\n' "$plan_idx" 'BLS/point-eval' "$file" >> "$WORK/plan"
  done
  for file in "${OSAKA_FILES[@]}"; do
    plan_idx=$((plan_idx + 1))
    printf '%d\t%s\t%s\n' "$plan_idx" 'osaka' "$file" >> "$WORK/plan"
  done

  # A missing file and an unknown address are gate classifications here, not
  # harness errors, so they are recorded exactly as the sequential path records
  # them — as this file's whole report chunk — and no worker is dispatched for
  # them. The two checks stay in the sequential path's order: a file that is
  # absent is reported absent even if its address is also unknown.
  : > "$WORK/weighted"
  while IFS=$'\t' read -r idx group file; do
    if [ ! -f "$VECTORS_DIR/$file" ]; then
      printf 'MISSING\t%s\n' "$file" > "$CHUNKS/$idx.out"
      missing_files=$((missing_files + 1))
      continue
    fi
    addr="$(get_addr "$file")"
    if [ -z "$addr" ]; then
      printf 'CONFIGURATION ERROR: unknown address for %s\n' "$file" > "$CHUNKS/$idx.out"
      configuration_errors=$((configuration_errors + 1))
      continue
    fi
    printf '%s %s %s %s %s %s\n' \
      "$(get_weight "$file")" "$idx" "$group" "$addr" "$(get_fork "$file")" "$file" \
      >> "$WORK/weighted"
  done < "$WORK/plan"

  # Heaviest first, manifest order breaking ties, so that the dispatch order is
  # itself reproducible rather than merely sorted.
  sort -k1,1gr -k2,2n "$WORK/weighted" | cut -d' ' -f2-6 > "$WORK/dispatch"
  DISPATCHED="$(grep -c . "$WORK/dispatch" || true)"
  echo "dispatching $DISPATCHED of ${#EXPECTED_FILES[@]} vector files across $JOBS workers (guard ${GUARD}s, longest-first)" >&2

  if [ "$DISPATCHED" -gt 0 ]; then
    RV_BIN="$BIN"; RV_GUARD="$GUARD"; RV_OUT="$CHUNKS"; RV_DIR="$VECTORS_DIR"
    export RV_BIN RV_GUARD RV_OUT RV_DIR
    # `{}` carries the whole "idx group addr fork file" line as one argument; the
    # shim re-splits it and execs the runner. No manifest entry contains
    # whitespace — a group label and a vector filename are both single words.
    xargs -P "$JOBS" -I{} bash -c '
      set -- $1
      exec "$0" "$RV_BIN" "$RV_GUARD" "$RV_OUT" "$1" "$RV_DIR/$5" "$3" "$4" "$2" "$5"
    ' "$RUNNER" {} < "$WORK/dispatch"
  fi

  # A guard trip aborts the pool via exit 255 and leaves this sentinel. It is a
  # harness event, not a classification: no report may absorb it.
  if [ -f "$CHUNKS/.guard-tripped" ]; then
    TRIPPED="$(cut -f1 "$CHUNKS/.guard-tripped")"
    DONE="$(find "$CHUNKS" -name '*.out' | grep -c . || true)"
    echo "HARNESS ERROR — vectors: wall-clock guard tripped on $TRIPPED (guard ${GUARD}s); run aborted after $DONE/$DISPATCHED classifications, none recorded for that file"
    exit 1
  fi

  # Reassemble in manifest order. A chunk missing here means a worker died
  # without classifying, which must not silently shrink the report.
  missing_chunks=0
  prev_group=""
  while IFS=$'\t' read -r idx group file; do
    if [ "$group" != "$prev_group" ]; then
      group_header "$group" >> "$REPORT"
      prev_group="$group"
    fi
    if [ -f "$CHUNKS/$idx.out" ]; then
      cat "$CHUNKS/$idx.out" >> "$REPORT"
    else
      missing_chunks=$((missing_chunks + 1))
      printf 'MISSING — no classification recorded for %s\n' "$file" >&2
    fi
  done < "$WORK/plan"
  if [ "$missing_chunks" -ne 0 ]; then
    echo "HARNESS ERROR — vectors: $missing_chunks/$DISPATCHED dispatched files produced no classification; see $REPORT"
    exit 1
  fi

  # Recount from the assembled report rather than from the workers: a counter
  # incremented inside a worker could not survive its process, and the report is
  # the only artifact that is known to be complete at this point.
  read -r passed_files failed_files control_passes < <(awk -F'\t' '
    $1 == "MATRIX" && $3 == "OK"  { p++ }
    $1 == "MATRIX" && $3 == "RED" { f++ }
    $1 == "MATRIX" && $2 == "control" && $3 == "OK" { c++ }
    END { printf "%d %d %d\n", p, f, c }
  ' "$REPORT")

  # The sequential path streams the report as it runs; this path has nothing to
  # stream until every chunk is in, so it prints the assembled report in one go.
  cat "$REPORT"
else
# Sequential path — deliberately left unindented so that its diff against the
# pre-parallel harness is this line, the closing `fi`, and the three banners
# becoming named constants. Nothing about default-mode behaviour changes.
printf '%s\n' "$HDR_CONTROL" | tee -a "$REPORT"
for file in "${CONTROL_FILES[@]}"; do
  run_vector_file "$file"
done

printf '%s\n' "$HDR_HASH" | tee -a "$REPORT"
for file in "${HASH_FILES[@]}"; do
  run_vector_file "$file"
done

printf '%s\n' "$HDR_PRECOMPILE" | tee -a "$REPORT"
for file in "${PRECOMPILE_FILES[@]}"; do
  run_vector_file "$file"
done

printf '%s\n' "$HDR_OSAKA" | tee -a "$REPORT"
for file in "${OSAKA_FILES[@]}"; do
  run_vector_file "$file"
done
fi

# An unlisted JSON file is also a configuration error: otherwise a newly
# added vector could sit in the directory without ever being executed.
shopt -s nullglob
for path in "$VECTORS_DIR"/*.json; do
  file="$(basename "$path")"
  if ! is_expected_file "$file"; then
    printf 'CONFIGURATION ERROR: unexpected vector file %s\n' "$file" | tee -a "$REPORT"
    configuration_errors=$((configuration_errors + 1))
  fi
done

# Coverage cross-check: every file must have run the number of cases get_cases
# declares. The report is identical in both modes, so this reads the report
# rather than the runners, and one code path serves sequential and parallel.
#
# Pull each file's reported total out of its `OK|RED — vectors: n/m PASS` line.
# A file with no such line — absent, no address, or a run that died before
# reporting — is skipped here and already accounted for by its own
# classification; a file whose block reports the wrong total is what this exists
# to catch.
awk '
  /^Running / { split($0, p, " "); cur = p[2]; next }
  /^(OK|RED) — vectors: [0-9]+\/[0-9]+ PASS/ {
    if (cur == "") next
    split($0, p, " "); split(p[4], q, "/")
    print cur "\t" q[2]
    cur = ""
  }
' "$REPORT" > "$TMPD/actual-cases"

for file in "${EXPECTED_FILES[@]}"; do
  want="$(get_cases "$file")"
  got="$(awk -F'\t' -v f="$file" '$1 == f { print $2; exit }' "$TMPD/actual-cases")"
  if [ -z "$want" ]; then
    printf 'CONFIGURATION ERROR: no expected case count declared for %s\n' "$file" \
      | tee -a "$REPORT"
    configuration_errors=$((configuration_errors + 1))
  elif [ -n "$got" ] && [ "$got" -ne "$want" ]; then
    printf 'CONFIGURATION ERROR: %s ran %s cases, expected %s\n' "$file" "$got" "$want" \
      | tee -a "$REPORT"
    configuration_errors=$((configuration_errors + 1))
  fi
done

control_total="${#CONTROL_FILES[@]}"
expected_total="${#EXPECTED_FILES[@]}"
END_ALL="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"
ELAPSED="$(perl -e 'printf "%.2f", $ARGV[1] - $ARGV[0]' "$START_ALL" "$END_ALL")"
# Mark a parallel verdict so its wall time is never mistaken for a measurement
# of the vectors rather than of the scheduler.
if [ "$JOBS" -gt 1 ]; then
  TIMING=" in ${ELAPSED}s (--jobs $JOBS, timings reference-only)"
else
  TIMING=" in ${ELAPSED}s"
fi
if [ "$passed_files" -eq "$expected_total" ] && \
   [ "$failed_files" -eq 0 ] && \
   [ "$missing_files" -eq 0 ] && \
   [ "$configuration_errors" -eq 0 ]; then
  printf 'OK — vectors: %s/%s files PASS; controls %s/%s PASS%s; full matrix in %s\n' \
    "$passed_files" "$expected_total" "$control_passes" "$control_total" "$TIMING" "$REPORT"
  exit 0
fi
printf 'RED — vectors: %s/%s files PASS; %s failed, %s missing, %s configuration errors; controls %s/%s PASS%s; see %s\n' \
  "$passed_files" "$expected_total" "$failed_files" "$missing_files" \
  "$configuration_errors" "$control_passes" "$control_total" "$TIMING" "$REPORT"
exit 1
