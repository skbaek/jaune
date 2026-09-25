#!/usr/bin/env bash
# Elliptic-curve differential-oracle gate.
#
# Compiles scripts/check-ec.lean through Lean C generation and leanc -O2 and
# links it against the built native objects of its import closure
# (scripts/native-link-objects.sh), as scripts/run-bench-ec.sh does.  The
# imported modules must be built first.  The checker exits 0
# if and only if every pinned, differential, and identity case passes; there is
# no skip or unknown outcome.  The last line of output is the verdict.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
REPORT="${JAUNE_REPORT_DIR:-$SCRIPT_DIR}/report-ec.txt"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

cd "$ROOT"
if ! lake env lean -c "$TMP/check-ec.c" -o "$TMP/check-ec.olean" scripts/check-ec.lean; then
  echo "RED — ec: scripts/check-ec.lean failed to elaborate"
  exit 1
fi

if ! scripts/native-link-objects.sh scripts/check-ec.lean "$TMP/objects.rsp"; then
  echo "RED — ec: could not recover the native objects of scripts/check-ec.lean's import closure"
  exit 1
fi

if ! lake env leanc -O2 -o "$TMP/check-ec" "$TMP/check-ec.c" @"$TMP/objects.rsp"; then
  echo "RED — ec: native link of the checker failed"
  exit 1
fi

mkdir -p "$(dirname "$REPORT")"
"$TMP/check-ec" | tee "$REPORT"
STATUS="${PIPESTATUS[0]}"
if [ "$STATUS" -ne 0 ]; then
  echo "RED — ec: differential oracle failed; full case list in $REPORT"
  exit 1
fi
echo "OK — ec: differential oracle passed; full case list in $REPORT"
exit 0
