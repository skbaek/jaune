#!/usr/bin/env bash

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/elevm"

if [ ! -x "$BIN" ]; then
  echo "ERROR: elevm binary not found. Run 'lake build' first."
  exit 1
fi

REPORT="$SCRIPT_DIR/report-vectors.txt"
: > "$REPORT"

VECTORS_DIR="$SCRIPT_DIR/vectors"
CONTROL_FILES=(
  bn256Add.json
  bn256ScalarMul.json
  bn256Pairing.json
  blake2F.json
  modexp_eip2565.json
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
  blsPairing.json
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

EXPECTED_FILES=("${CONTROL_FILES[@]}" "${PRECOMPILE_FILES[@]}" "${OSAKA_FILES[@]}")

# The word-operation oracle is deliberately run by check-u256.sh, not through
# the precompile address dispatch above.  Keep it listed here so this manifest
# still rejects genuinely stray JSON files while the two gates remain separate.
AUXILIARY_FILES=(
  u256.json
)

# Regenerate compact MSM samples from the pinned full files in
# scripts/vectors/SOURCES.md:
#   jq '.[0:32]' msm_G1_bls.json > scripts/vectors/msm_G1_bls.head.json
#   jq '.[0:32]' msm_G2_bls.json > scripts/vectors/msm_G2_bls.head.json
#   jq '.[0:32]' blsG1MultiExp.json > scripts/vectors/blsG1MultiExp.head.json
#   jq '.[0:32]' blsG2MultiExp.json > scripts/vectors/blsG2MultiExp.head.json

# The fork whose rules each file is stated against.  Every file is run with an
# explicit --network so that a repriced or newly activated precompile is tested
# under the rules that define it, never under whatever the binary defaults to.
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
    modexp_eip7883.json) echo "05" ;;
    p256Verify.json) echo "0100" ;;
    pointEvaluation.json) echo "0a" ;;
    add_G1_bls.json|fail-add_G1_bls.json|blsG1Add.json|fail-blsG1Add.json) echo "0b" ;;
    mul_G1_bls.json|fail-mul_G1_bls.json|msm_G1_bls.head.json|fail-msm_G1_bls.json|blsG1Mul.json|fail-blsG1Mul.json|blsG1MultiExp.head.json|fail-blsG1MultiExp.json) echo "0c" ;;
    add_G2_bls.json|fail-add_G2_bls.json|blsG2Add.json|fail-blsG2Add.json) echo "0d" ;;
    mul_G2_bls.json|fail-mul_G2_bls.json|msm_G2_bls.head.json|fail-msm_G2_bls.json|blsG2Mul.json|fail-blsG2Mul.json|blsG2MultiExp.head.json|fail-blsG2MultiExp.json) echo "0e" ;;
    pairing_check_bls.json|fail-pairing_check_bls.json|blsPairing.json|fail-blsPairing.json) echo "0f" ;;
    map_fp_to_G1_bls.json|fail-map_fp_to_G1_bls.json|blsMapG1.json|fail-blsMapG1.json) echo "10" ;;
    map_fp2_to_G2_bls.json|fail-map_fp2_to_G2_bls.json|blsMapG2.json|fail-blsMapG2.json) echo "11" ;;
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

control_passes=0
passed_files=0
failed_files=0
missing_files=0
configuration_errors=0

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

printf '%s\n' '--- Running control files ---' | tee -a "$REPORT"
for file in "${CONTROL_FILES[@]}"; do
  run_vector_file "$file"
done

printf '%s\n' '--- Running BLS and point-evaluation files ---' | tee -a "$REPORT"
for file in "${PRECOMPILE_FILES[@]}"; do
  run_vector_file "$file"
done

printf '%s\n' '--- Running Osaka files ---' | tee -a "$REPORT"
for file in "${OSAKA_FILES[@]}"; do
  run_vector_file "$file"
done

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

control_total="${#CONTROL_FILES[@]}"
expected_total="${#EXPECTED_FILES[@]}"
if [ "$passed_files" -eq "$expected_total" ] && \
   [ "$failed_files" -eq 0 ] && \
   [ "$missing_files" -eq 0 ] && \
   [ "$configuration_errors" -eq 0 ]; then
  printf 'OK — vectors: %s/%s files PASS; controls %s/%s PASS; full matrix in %s\n' \
    "$passed_files" "$expected_total" "$control_passes" "$control_total" "$REPORT"
  exit 0
fi
printf 'RED — vectors: %s/%s files PASS; %s failed, %s missing, %s configuration errors; controls %s/%s PASS; see %s\n' \
  "$passed_files" "$expected_total" "$failed_files" "$missing_files" \
  "$configuration_errors" "$control_passes" "$control_total" "$REPORT"
exit 1
