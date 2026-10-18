#!/usr/bin/env bash
# Difficulty-bomb boundary gate (goal U10, bomb-only forks).
#
# Compares the committed expectations in scripts/difficulty-vectors.json --
# authored inputs at, below, and above each bomb-only fork's delay -- against
# the pinned conformance target's `calculate_block_difficulty`, one fork
# module at a time. No theorem states that function, so these nine vectors
# are finite evidence a theorem does not cover.
#
# CLI contract: exit 0 iff every committed expectation matches the target's
# current output; the last line is a single unambiguous verdict. Exit 1 on a
# mismatch, 2 on a usage or setup error. Needs the conformance-target
# checkout and its venv; writes nothing, takes no lock.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/gen-difficulty-vectors.py" --check
