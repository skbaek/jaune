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

# The three repriced globals, as the G0a rename spells them (`Gas.` namespace;
# every source spelling is qualified, and the left boundary excludes record
# fields such as `pragueGas.callValue` and `rules.gas.callValue`), and their
# former names (gasColdAccountAccess, gasCallValue, gasCreate), which comments
# still mention and which no new code may reintroduce.
NAMES='Gas\.coldAccountAccessCost|Gas\.callValue|Gas\.create|gasColdAccountAccess|gasCallValue|gasCreate'

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

# Source view the greps read, one record per line: "<relpath>:<line>:<text>".
# `lines` keeps every line with Lean's spelling variants folded to the plain
# spelling (`«Gas».«callValue»` -> `Gas.callValue`, `_root_.Jaune.Gas` ->
# `Jaune.Gas`), so an escaped or root-anchored read is still inventoried.
# `scope` lists, outside comments, every `open`/`export` command joined
# across its continuation lines, every `namespace` line, and every bare
# short-name read (`callValue`, `create`, `coldAccountAccessCost`) inside a
# declaration whose name is `Gas.`-qualified: Lean elaborates such a body
# inside the `Gas` namespace, so a short name there resolves to the global.
source_view() {
  # shellcheck disable=SC2046
  python3 - "$1" $(find Jaune -name '*.lean' | LC_ALL=C sort) Main.lean <<'PY'
import re
import sys

mode, paths = sys.argv[1], sys.argv[2:]
ESCAPED = re.compile(r'«([A-Za-z_][A-Za-z0-9_\'!?]*)»')
ROOTED = re.compile(r'(?<![A-Za-z0-9_.])_root_\.')


def fold(line):
    return ROOTED.sub('', ESCAPED.sub(r'\1', line))


def code(lines):
    """Lines with comments and strings blanked (line structure kept)."""
    out, depth, text = [], 0, '\n'.join(lines)
    chars, i = list(text), 0
    while i < len(text):
        if depth == 0 and text.startswith('--', i):
            j = text.find('\n', i)
            j = len(text) if j < 0 else j
            chars[i:j] = ' ' * (j - i)
            i = j
        elif text.startswith('/-', i):
            depth += 1
            chars[i:i + 2] = '  '
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            chars[i:i + 2] = '  '
            i += 2
        elif depth:
            if chars[i] != '\n':
                chars[i] = ' '
            i += 1
        elif text[i] == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            for k in range(i, min(j + 1, len(text))):
                if chars[k] != '\n':
                    chars[k] = ' '
            i = j + 1
        else:
            i += 1
    return ''.join(chars).split('\n')


DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
                  r"(?:def|abbrev|theorem|lemma|instance|opaque|structure|inductive|class|axiom)\s+"
                  r"(?:Jaune\.)?Gas\.")
SHORT = re.compile(r"(?<![A-Za-z0-9_.'!?])(callValue|create|coldAccountAccessCost)(?![A-Za-z0-9_'!?])")
CONT = re.compile(r"^\s+[A-Za-z_(][A-Za-z0-9_.'!?()\s]*$")

for path in paths:
    with open(path, encoding='utf-8') as handle:
        raw = handle.read().split('\n')
    folded = [fold(line) for line in raw]
    if mode == 'lines':
        for n, line in enumerate(folded, 1):
            print(f'{path}:{n}:{line}')
        continue
    lines = code(folded)
    in_gas_decl = False
    for n, line in enumerate(lines, 1):
        stripped = line.strip()
        if line[:1] not in ('', ' ', '\t'):
            in_gas_decl = bool(DECL.match(line))
        if in_gas_decl:
            for m in SHORT.finditer(line):
                print(f'{path}:{n}:short read {m.group(1)} inside a Gas.-qualified declaration: {stripped}')
        if re.match(r'(open|export)(\s|$)', stripped):
            joined, k = stripped, n
            while k < len(lines) and CONT.match(lines[k]) and not re.match(
                    r'\s*(in|def|theorem|abbrev|open|export|namespace|section|end|variable)\b', lines[k]):
                joined += ' ' + lines[k].strip()
                k += 1
            print(f'{path}:{n}:{joined}')
        elif re.match(r'namespace(\s|$)', stripped):
            print(f'{path}:{n}:{stripped}')
PY
}

# Normalised inventory: "<relpath> <trimmed line, whitespace runs collapsed>".
inventory() {
  source_view lines \
    | grep -E "^[^:]*:[0-9]*:(.*[^A-Za-z0-9_])?($NAMES)([^A-Za-z0-9_]|\$)" \
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

# The three globals live in the `Gas` namespace, and their short names
# (`callValue`, `create`, `coldAccountAccessCost`) are not unique tokens: a read
# spelled under `open Gas` or inside `namespace Gas` would escape the qualified
# grep above. Absence rule, no allowlist: nothing under Jaune/ or in Main.lean
# opens or exports `Gas`/`Jaune.Gas` or declares `namespace Gas`/`Jaune.Gas`,
# so every spelling of the three is qualified and inventoried.
# The view folds `«»` escapes and `_root_.`, joins multi-line `open`/`export`,
# and also catches `namespace Gas.Sub` (inside it `callValue` resolves to
# `Gas.callValue` too) and short reads inside `Gas.`-qualified declarations.
gas_scope="$(source_view scope | grep -E '^[^:]*:[0-9]*:((open|export)[[:space:]](.*[[:space:](])?(Jaune\.)?Gas([^A-Za-z0-9_.]|$)|namespace[[:space:]]+(Jaune\.)?Gas([^A-Za-z0-9_]|$)|short read )' || true)"
if [ -n "$gas_scope" ]; then
  printf '%s\n' 'rule-data: FAIL — the Gas namespace is opened, exported or reopened, so a short-name read could escape the inventory:' >&2
  printf '%s\n' "$gas_scope" >&2
  printf '%s\n' 'FAIL — rule-data: Gas namespace scope outside qualified spellings' >&2
  exit 1
fi

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
printf 'OK — rule-data: all %s occurrence(s) of {Gas.coldAccountAccessCost, Gas.callValue, Gas.create} under Jaune/ and in Main.lean match one of %s allowlist row(s); no interpreter site reads a repriced global instead of the selected rules.gas\n' "$count" "$rows"
