#!/usr/bin/env bash
# Compile the standalone benchmark through Lean C generation and leanc -O2,
# then save its table under a stable step label.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

if [ $# -ne 1 ]; then
  echo "usage: scripts/run-bench-u256.sh <label>" >&2
  echo "example: scripts/run-bench-u256.sh step1" >&2
  exit 2
fi
LABEL="$1"
case "$LABEL" in
  *[!A-Za-z0-9._-]*|'')
    echo "label may contain only letters, digits, dot, underscore, and hyphen" >&2
    exit 2
    ;;
esac

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

cd "$ROOT"
lake env lean -c "$TMP/bench-u256.c" -o "$TMP/bench-u256.olean" scripts/bench-u256.lean

if ! scripts/native-link-objects.sh scripts/bench-u256.lean "$TMP/objects.rsp"; then
  echo "could not recover the native objects of scripts/bench-u256.lean's import closure" >&2
  exit 1
fi

lake env leanc -O2 -o "$TMP/bench-u256" "$TMP/bench-u256.c" @"$TMP/objects.rsp"
REPORT="${JAUNE_REPORT_DIR:-$SCRIPT_DIR}/report-$LABEL-bench-u256.txt"
mkdir -p "$(dirname "$REPORT")"
"$TMP/bench-u256" | tee "$REPORT"
echo "OK — U256 benchmark recorded in $REPORT"
