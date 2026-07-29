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

TRACE="$ROOT/.lake/build/bin/jaune.trace"
if [ ! -f "$TRACE" ]; then
  echo "benchmark needs the existing jaune native dependency objects; run a normal check.sh gate first" >&2
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

cd "$ROOT"
lake env lean -c "$TMP/bench-ec.c" -o "$TMP/bench-ec.olean" scripts/bench-ec.lean

# Reuse the native import objects recorded by Lake's most recent executable
# link, omitting Main itself.  A response file avoids command-line size limits.
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

lake env leanc -O2 -o "$TMP/bench-ec" "$TMP/bench-ec.c" @"$TMP/objects.rsp"
REPORT="${JAUNE_REPORT_DIR:-$SCRIPT_DIR}/report-$LABEL-bench-ec.txt"
mkdir -p "$(dirname "$REPORT")"
"$TMP/bench-ec" | tee "$REPORT"
echo "OK — EC benchmark recorded in $REPORT"
