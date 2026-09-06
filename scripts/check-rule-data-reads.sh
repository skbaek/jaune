#!/usr/bin/env bash
# Rule-data reads: the interpreter reads a repriced gas number from the
# selected `ForkRules.gas` record, never from the global that shadows it.
#
# See scripts/rule-data-allow.txt for what this inventories and why. The gate
# is structural on purpose: with `BenvStat` carrying a `Fork`, every machine a
# fixture or a proof can build runs the legacy lane under `pragueGasSchedule`,
# whose three repriced numbers equal these globals by `rfl`, so no evaluation
# guard can distinguish a site that reads the record from one that reads the
# global. Goal `jaune-forks-by-construction-v1`, D-F6 (iii).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ALLOW="$ROOT/scripts/rule-data-allow.txt"

NAMES='gasColdAccountAccess|gasCallValue|gasCreate'

if [ ! -f "$ALLOW" ]; then
  printf '%s\n' "SETUP — rule-data: missing allowlist $ALLOW" >&2
  exit 1
fi

if [ "${1-}" = "--list" ]; then
  LIST=1
elif [ -n "${1-}" ]; then
  printf '%s\n' "usage: scripts/check-rule-data-reads.sh [--list]" >&2
  exit 2
else
  LIST=0
fi

cd "$ROOT"

# Normalised inventory: "<relpath> <trimmed line, whitespace runs collapsed>".
inventory() {
  local files
  files="$(find Jaune -name '*.lean' | LC_ALL=C sort) Main.lean"
  # shellcheck disable=SC2086
  grep -nE "(^|[^A-Za-z0-9_])($NAMES)([^A-Za-z0-9_]|\$)" $files \
    | sed 's/^\([^:]*\):[0-9]*:[[:space:]]*/\1 /' \
    | sed 's/[[:space:]]\{1,\}/ /g' \
    | sed 's/[[:space:]]*$//' \
    | LC_ALL=C sort
}

if (( LIST )); then
  inventory
  exit 0
fi

# Allowlist rows, normalised the same way, with multiplicity.
allowed="$(grep -v '^[[:space:]]*#' "$ALLOW" | grep -v '^[[:space:]]*$' \
  | sed 's/^[[:space:]]*//; s/[[:space:]]\{1,\}/ /g; s/[[:space:]]*$//' \
  | LC_ALL=C sort)"

found="$(inventory)"

unlisted="$(LC_ALL=C comm -23 <(printf '%s\n' "$found" | uniq) \
                              <(printf '%s\n' "$allowed" | uniq))"
stale="$(LC_ALL=C comm -13 <(printf '%s\n' "$found" | uniq) \
                           <(printf '%s\n' "$allowed" | uniq))"

fail=0
if [ -n "$unlisted" ]; then
  printf '%s\n' 'rule-data: FAIL — occurrence(s) of a repriced gas global that the allowlist does not classify:' >&2
  printf '%s\n' "$unlisted" >&2
  fail=1
fi
if [ -n "$stale" ]; then
  printf '%s\n' 'rule-data: FAIL — allowlist row(s) with no occurrence (stale; remove them):' >&2
  printf '%s\n' "$stale" >&2
  fail=1
fi
if (( fail )); then
  printf '%s\n' 'FAIL — rule-data: the inventory and the allowlist disagree' >&2
  exit 1
fi

count="$(printf '%s\n' "$found" | grep -c . || true)"
rows="$(printf '%s\n' "$allowed" | grep -c . || true)"
printf 'OK — rule-data: all %s occurrence(s) of {gasColdAccountAccess, gasCallValue, gasCreate} under Jaune/ and in Main.lean match one of %s allowlist row(s); no interpreter site reads a repriced global instead of the selected rules.gas\n' "$count" "$rows"
