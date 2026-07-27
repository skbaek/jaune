#!/usr/bin/env bash
# Strict all-PASS harness for the generated current-mainnet fixture manifests.
# Future suite names are recognised explicitly and refused until their protocol
# step activates them. This is intentionally not a permissive selector.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/elevm"
FIXTURES_ROOT="${EEST_MAINNET_ROOT:-$HOME/eest-mainnet-v20.0.1}/fixtures"
SUITE=""
SUBDIR=""
BUILD=1
START_AT=1
GUARD="${ELEVM_TIMEOUT:-1800}"

usage() {
  echo "usage: scripts/check-mainnet.sh (--suite (prague|osaka|transitions|smoke|full) | --dir REL --suite SUITE) [--fixtures-root PATH] [--no-build] [--start-at N]" >&2
  exit 2
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --suite) shift; [ "$#" -gt 0 ] || usage; SUITE="$1" ;;
    --dir) shift; [ "$#" -gt 0 ] || usage; SUBDIR="$1" ;;
    --fixtures-root) shift; [ "$#" -gt 0 ] || usage; FIXTURES_ROOT="$1" ;;
    --no-build) BUILD=0 ;;
    --start-at) shift; [ "$#" -gt 0 ] || usage; START_AT="$1" ;;
    *) echo "error: unknown argument $1" >&2; usage ;;
  esac
  shift
done
[ -n "$SUITE" ] || usage
[ "$START_AT" -ge 1 ] 2>/dev/null || {
  echo "error: --start-at must be a positive manifest index" >&2; exit 2;
}

# The pinned release publishes no fixture whose `network` is a bare `BPO1` or
# `BPO2`: every BPO case in it is a transition case, and those are the
# `transitions` suite.  Refusing the two static BPO suites is therefore not a
# step that has yet to happen -- it is the archive's shape.  Reporting an
# all-PASS verdict over zero selected files would be exactly the permissive
# oracle this harness exists to prevent.
bpo_refusal() {
  LABEL="$(printf '%s' "$1" | tr '[:lower:]' '[:upper:]')"
  echo "error: suite $1 selects no file: the pinned release publishes no fixture whose network is $LABEL." >&2
  echo "       $LABEL rules are exercised by --suite transitions (OsakaToBPO1AtTime15k, BPO1ToBPO2AtTime15k)." >&2
  exit 2
}

# `--dir` restricts a suite to one subtree of the pinned archive.  It is a
# targeted instrument for landing one semantic change at a time: the entries
# still come from the generated manifest, every one of them still has to PASS,
# and an empty or unlisted selection is an error.
if [ -n "$SUBDIR" ]; then
  case "$SUITE" in
    prague|smoke|osaka|transitions) ;;
    bpo1|bpo2) bpo_refusal "$SUITE" ;;
    full)
      echo "error: suite full has no per-directory form; name the component suite" >&2
      exit 2 ;;
    *) echo "error: unknown suite $SUITE" >&2; exit 2 ;;
  esac
  case "$SUBDIR" in
    /*|*..*) echo "error: --dir must be a relative path inside blockchain_tests" >&2; exit 2 ;;
  esac
else
  case "$SUITE" in
    prague|osaka|transitions|smoke|full) ;;
    bpo1|bpo2) bpo_refusal "$SUITE" ;;
    *) echo "error: unknown suite $SUITE" >&2; exit 2 ;;
  esac
fi

[ -d "$FIXTURES_ROOT/blockchain_tests" ] || {
  echo "error: current-mainnet blockchain fixture root not found: $FIXTURES_ROOT/blockchain_tests" >&2
  exit 2
}
[ "$GUARD" -gt 0 ] 2>/dev/null || { echo "error: ELEVM_TIMEOUT must be positive" >&2; exit 2; }

if [ "$BUILD" -eq 1 ]; then
  (cd "$ROOT" && lake build elevm)
fi
[ -x "$BIN" ] || { echo "error: elevm binary not found: $BIN" >&2; exit 2; }

LIST="$(mktemp)"
trap 'rm -f "$LIST"' EXIT
python3 "$SCRIPT_DIR/gen_mainnet_manifest.py" \
  --fixtures-root "$FIXTURES_ROOT" --check --emit-suite "$SUITE" > "$LIST"
[ -s "$LIST" ] || { echo "error: zero selected manifest entries for $SUITE" >&2; exit 2; }

if [ -n "$SUBDIR" ]; then
  [ -d "$FIXTURES_ROOT/blockchain_tests/$SUBDIR" ] || {
    echo "error: --dir subtree not found: blockchain_tests/$SUBDIR" >&2; exit 2;
  }
  SELECTED="$(mktemp)"
  trap 'rm -f "$LIST" "$SELECTED"' EXIT
  grep -E "^${SUBDIR%/}/" "$LIST" > "$SELECTED" || true
  [ -s "$SELECTED" ] || {
    echo "error: zero $SUITE manifest entries under blockchain_tests/$SUBDIR" >&2
    exit 2
  }
  # An unlisted .json inside the subtree means the subtree mixes fork labels or
  # the manifest is stale; either way it must not be skipped silently.
  ON_DISK="$(find "$FIXTURES_ROOT/blockchain_tests/${SUBDIR%/}" -name '*.json' | wc -l | tr -d ' ')"
  IN_MANIFEST="$(wc -l < "$SELECTED" | tr -d ' ')"
  [ "$ON_DISK" -eq "$IN_MANIFEST" ] || {
    echo "error: blockchain_tests/$SUBDIR holds $ON_DISK fixture files but the $SUITE manifest lists $IN_MANIFEST" >&2
    exit 2
  }
  mv "$SELECTED" "$LIST"
  trap 'rm -f "$LIST"' EXIT
  SUITE="$SUITE:$SUBDIR"
fi

TOTAL="$(wc -l < "$LIST" | tr -d ' ')"
[ "$START_AT" -le "$TOTAL" ] || {
  echo "error: --start-at $START_AT exceeds $SUITE manifest size $TOTAL" >&2; exit 2;
}
PASS=$((START_AT - 1))
START_ALL="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"
while IFS=$'\t' read -r REL NETWORK; do
  [ -n "$REL" ] && [ -n "$NETWORK" ] || {
    echo "error: malformed generated manifest entry" >&2; exit 2;
  }
  # The static forks and the transition labels whose endpoints are both
  # supported.  A label this list does not name must never reach the binary:
  # the binary would refuse it, but the manifest is what is meant to be exact.
  case "$NETWORK" in
    Prague|Osaka|BPO1|BPO2) ;;
    PragueToOsakaAtTime15k|OsakaToBPO1AtTime15k|BPO1ToBPO2AtTime15k) ;;
    *) echo "error: unknown manifest network $NETWORK" >&2; exit 2;;
  esac
  FILE="$FIXTURES_ROOT/blockchain_tests/$REL"
  [ -f "$FILE" ] || { echo "error: missing manifest fixture file: $FILE" >&2; exit 2; }
  set +e
  perl -e '
    my $t = shift @ARGV;
    my $pid = fork(); die "fork failed: $!" unless defined $pid;
    if (!$pid) { exec @ARGV; exit 127 }
    $SIG{ALRM} = sub { kill "KILL", $pid; waitpid($pid, 0); exit 142 };
    alarm $t; waitpid($pid, 0); alarm 0;
    my $st = $?; exit($st & 127 ? 128 + ($st & 127) : $st >> 8);
  ' "$GUARD" "$BIN" "$FILE" --network "$NETWORK" > /dev/null 2>&1
  RC=$?
  set -e
  if [ "$RC" -eq 142 ]; then
    echo "HARNESS ERROR — $REL exceeded ${GUARD}s; no classification was recorded" >&2
    exit 1
  fi
  if [ "$RC" -ne 0 ]; then
    echo "RED — $SUITE: non-PASS fixture $REL (network $NETWORK, exit $RC)" >&2
    exit 1
  fi
  PASS=$((PASS + 1))
  printf '[%d/%d] PASS %s\n' "$PASS" "$TOTAL" "$REL" >&2
done < <(tail -n +"$START_AT" "$LIST")
END_ALL="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"
ELAPSED="$(perl -e 'printf "%.2f", $ARGV[1] - $ARGV[0]' "$START_ALL" "$END_ALL")"
echo "OK — $SUITE: $PASS/$TOTAL manifest files PASS in ${ELAPSED}s"
