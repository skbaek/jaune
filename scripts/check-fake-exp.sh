#!/usr/bin/env bash
# Step-7 fake-exponential differential-oracle gate.  The committed vectors in
# scripts/vectors/fake-exp.json carry expected values computed by the pinned
# EELS `taylor_exponential` itself (see scripts/gen-fake-exp-vectors.py); the
# binary evaluates Jaune's total `fakeExp` on every case.  The final line
# follows check-legacy.sh's verdict convention: exit 0 exactly when every vector
# passes.
set -uo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/jaune"
VECTORS="$SCRIPT_DIR/vectors/fake-exp.json"
if [ ! -x "$BIN" ]; then
  echo "RED — fake-exp: jaune binary not found; build the executable first"
  exit 1
fi
if [ ! -f "$VECTORS" ]; then
  echo "RED — fake-exp: generated vector file not found: $VECTORS"
  exit 1
fi
"$BIN" --fake-exp "$VECTORS"
