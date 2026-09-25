#!/usr/bin/env bash
# Compile the standalone elliptic-curve benchmark through Lean C generation and
# leanc -O2, then save its table under a stable step label.
#
# Same native-link discipline as scripts/run-bench-u256.sh: the benchmark is not
# a Lake target, so it reuses the dependency objects recorded by Lake's most
# recent `jaune` executable link.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

if [ $# -ne 1 ]; then
  echo "usage: scripts/run-bench-ec.sh <label>" >&2
  echo "example: scripts/run-bench-ec.sh ec-baseline-1" >&2
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
lake env lean -c "$TMP/bench-ec.c" -o "$TMP/bench-ec.olean" scripts/bench-ec.lean

if ! scripts/native-link-objects.sh scripts/bench-ec.lean "$TMP/objects.rsp"; then
  echo "could not recover the native objects of scripts/bench-ec.lean's import closure" >&2
  exit 1
fi

lake env leanc -O2 -o "$TMP/bench-ec" "$TMP/bench-ec.c" @"$TMP/objects.rsp"
REPORT="${JAUNE_REPORT_DIR:-$SCRIPT_DIR}/report-$LABEL-bench-ec.txt"
mkdir -p "$(dirname "$REPORT")"
"$TMP/bench-ec" | tee "$REPORT"
echo "OK — EC benchmark recorded in $REPORT"
