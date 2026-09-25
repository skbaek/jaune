#!/usr/bin/env bash
# Write a leanc response file listing the native objects a standalone Lean
# program needs: one compiled object per non-toolchain module in the import
# closure of FILE.  Toolchain modules (Init, Std, Lean) come from the runtime
# libraries leanc links by default.
#
#   scripts/native-link-objects.sh FILE OUT.rsp
#
# Used by check-ec.sh, run-bench-ec.sh and run-bench-u256.sh.  Run it from the
# repository root after the modules FILE imports are built.  It fails closed:
# a closure module whose object is missing is an error, never a skipped line.

set -uo pipefail

if [ "$#" -ne 2 ]; then
  echo "usage: scripts/native-link-objects.sh FILE OUT.rsp" >&2
  exit 2
fi
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if ! CLOSURE="$(lake env lean --run "$SCRIPT_DIR/ImportClosure.lean" "$1")"; then
  echo "could not compute the import closure of $1" >&2
  exit 1
fi

printf '%s\n' "$CLOSURE" | python3 -c '
import os, shlex, sys

TOOLCHAIN = os.path.realpath(sys.argv[2])
LIB = "/.lake/build/lib/lean/"
objects, missing = [], []
for line in sys.stdin:
    module, olean = line.rstrip("\n").split("\t")
    if os.path.realpath(olean).startswith(TOOLCHAIN + os.sep):
        continue
    root, sep, rel = olean.rpartition(LIB)
    if not sep or not rel.endswith(".olean"):
        raise SystemExit("unexpected olean location for %s: %s" % (module, olean))
    obj = root + "/.lake/build/ir/" + rel[: -len(".olean")] + ".c.o.export"
    (objects if os.path.isfile(obj) else missing).append(obj)
if missing:
    raise SystemExit("%d closure object(s) missing, e.g. %s; build the imported modules first"
                     % (len(missing), missing[0]))
if not objects:
    raise SystemExit("no native objects in the import closure")
with open(sys.argv[1], "w") as out:
    for obj in objects:
        out.write(shlex.quote(obj) + "\n")
' "$2" "$(lean --print-prefix)"
