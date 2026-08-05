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

TRACE="$ROOT/.lake/build/bin/jaune.trace"
if [ ! -f "$TRACE" ]; then
  echo "benchmark needs the existing jaune native dependency objects; run a normal check-legacy.sh gate first" >&2
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

cd "$ROOT"
lake env lean -c "$TMP/bench-u256.c" -o "$TMP/bench-u256.olean" scripts/bench-u256.lean

# Reuse the native import objects recorded by Lake's most recent executable
# link, omitting Main itself.  A response file avoids command-line size limits.
python3 - "$TRACE" "$TMP/objects.rsp" <<'PY'
import json, shlex, sys
trace = json.load(open(sys.argv[1]))


def from_inputs(trace):
    """Lake >= 5.0 (trace schema 2025-09-10) records the link inputs
    structurally and passes the linker a response file, so the object paths are
    no longer present in the logged command line."""
    for entry in trace.get("inputs", []):
        if isinstance(entry, list) and len(entry) == 2 and entry[0] == "linkObjs":
            return [path for path, _hash in entry[1]]
    return []


def from_log(trace):
    """Older Lake spelled the whole linker invocation into the build log."""
    for item in trace.get("log", []):
        message = item.get("message", "")
        if ".c.o.export" in message:
            return [arg for arg in shlex.split(message) if ".c.o" in arg]
    return []


objects = [obj for obj in (from_inputs(trace) or from_log(trace))
           if obj.endswith(".c.o") or obj.endswith(".c.o.export")]
objects = [obj for obj in objects if not obj.endswith("/ir/Main.c.o.export")]
if not objects:
    raise SystemExit("no native dependency objects found in jaune trace")
with open(sys.argv[2], "w") as out:
    for obj in objects:
        out.write(shlex.quote(obj) + "\n")
PY

lake env leanc -O2 -o "$TMP/bench-u256" "$TMP/bench-u256.c" @"$TMP/objects.rsp"
REPORT="${JAUNE_REPORT_DIR:-$SCRIPT_DIR}/report-$LABEL-bench-u256.txt"
mkdir -p "$(dirname "$REPORT")"
"$TMP/bench-u256" | tee "$REPORT"
echo "OK — U256 benchmark recorded in $REPORT"
