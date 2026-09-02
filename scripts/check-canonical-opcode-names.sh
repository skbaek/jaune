#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Retired constructor names, derived declaration fragments, and the three old
# renderer strings. `dest` is intentionally syntax-qualified: ordinary values
# named `dest` are destinations, not SELFDESTRUCT aliases.
PATTERN='(?<![A-Za-z0-9])kec(?![a-z])|retdatasize|retdatacopy|delcall|statcall|(?<![A-Za-z0-9])ret(?![a-z])|retdata(?=[A-Z_])|(?<![A-Za-z0-9])rev(?![a-z])|\.dest\b|\bcase[[:space:]]+dest\b|^[[:space:]]*\|[[:space:]]*dest[[:space:]]*(?:=>|--)|"KEC"|"RETDATASIZE"|"RETDATACOPY"'

set +e
matches="$(LC_ALL=C rg -n --pcre2 "$PATTERN" "$ROOT/Jaune" --glob '*.lean')"
status=$?
set -e

if (( status == 0 )); then
  printf '%s\n' 'canonical opcode names: FAIL (retired live spelling)' >&2
  printf '%s\n' "$matches" >&2
  exit 1
fi
if (( status != 1 )); then
  printf '%s\n' "canonical opcode names: FAIL (rg exited $status)" >&2
  exit "$status"
fi

printf '%s\n' 'canonical opcode names: OK'
