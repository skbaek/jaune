#!/usr/bin/env bash
# Elliptic-curve differential-oracle gate.
#
# Compiles scripts/check-ec.lean through Lean C generation and leanc -O2 and
# links it against the native objects Lake already recorded for the `jaune`
# executable, the same way scripts/run-bench-ec.sh does.  The checker exits 0
# if and only if every pinned, differential, and identity case passes; there is
# no skip or unknown outcome.  The last line of output is the verdict.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
REPORT="${JAUNE_REPORT_DIR:-$SCRIPT_DIR}/report-ec.txt"

TRACE="$ROOT/.lake/build/bin/jaune.trace"
if [ ! -f "$TRACE" ]; then
  echo "RED — ec: needs the existing jaune native dependency objects; run 'lake build' or a check.sh gate first"
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

cd "$ROOT"
if ! lake env lean -c "$TMP/check-ec.c" -o "$TMP/check-ec.olean" scripts/check-ec.lean; then
  echo "RED — ec: scripts/check-ec.lean failed to elaborate"
  exit 1
fi

python3 - "$TRACE" "$TMP/objects.rsp" <<'PY'
import json, shlex, sys
trace = json.load(open(sys.argv[1]))
command = next(item["message"] for item in trace["log"] if ".c.o.export" in item.get("message", ""))
objects = [arg for arg in shlex.split(command)
           if ".c.o" in arg and not arg.endswith("/ir/Main.c.o.export")]
if not objects:
    raise SystemExit("no native dependency objects found in jaune trace")
with open(sys.argv[2], "w") as out:
    for obj in objects:
        out.write(shlex.quote(obj) + "\n")
PY

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
