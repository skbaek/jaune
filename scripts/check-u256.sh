#!/usr/bin/env bash
# Step-1 U256 differential-oracle gate.  The final line follows check-legacy.sh's
# verdict convention: exit 0 exactly when every generated vector passes.
set -uo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/jaune"
VECTORS="$SCRIPT_DIR/vectors/u256.json"
if [ ! -x "$BIN" ]; then
  echo "RED — u256: jaune binary not found; build the executable first"
  exit 1
fi
if [ ! -f "$VECTORS" ]; then
  echo "RED — u256: generated vector file not found: $VECTORS"
  exit 1
fi
"$BIN" --u256 "$VECTORS"
