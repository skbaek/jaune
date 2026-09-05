#!/usr/bin/env bash
# Fork-constant gate (cheap tier).
#
# Every number in `Jaune/Fork.lean` that a fork carries as rule data is
# supposed to be the pinned `execution-specs` revision's number. Nothing else
# checks that directly: the conformance tiers would catch a wrong *gas* value
# through a failing fixture, eventually and expensively, but they say nothing
# about a fork whose fixtures are not installed, and nothing at all about a
# value no fixture happens to exercise. This gate compares the two sides
# outright.
#
#   left  — `scripts/amsterdam/constants.json`, written by
#           `scripts/gen-fork-constants.py` from the pinned revision;
#   right — `lake exe jaune --rules <fork>`, this build's own record.
#
# Neither side reads the other. The generator imports upstream and knows
# nothing about Jaune; the printer reads `ForkRules` and knows nothing about
# upstream; this script is the only place they meet.
#
# Three things are checked, and the third is the one that keeps the gate
# honest over time:
#
#   1. every constant the extraction marks `checked` matches, for every fork
#      this build runs;
#   2. the extraction was taken at the commit `sources.json` currently pins;
#   3. the *key set* the printer emits is exactly the key set the coverage
#      table classifies — so a `ForkRules` field added later cannot slip
#      through unchecked, it has to be classified first.
#
# A fork this build declares but does not implement is expected to be refused
# by `--rules`; that is checked too, so the gate's fork list and
# `Fork.supported` cannot drift apart. Every fork the extraction names resolves
# today, so that branch is unreachable through a declared label; it stays for
# the next declared-but-unimplemented fork, which is precisely when it bites.
#
# Usage: scripts/check-fork-constants.sh [--table]
#
#   --table  additionally print the extracted Amsterdam column in full, for a
#            report. Every row of it is checked by rule 1; printing it is a
#            convenience for the report, not a further check.
#
# CLI contract: exit 0 iff every check holds; the last line is a single
# unambiguous verdict. Exit 1 on a violation, 2 on a usage or setup error.
# Reads the built binary and never builds it. Writes nothing, takes no lock.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/jaune"
EXTRACTION="$SCRIPT_DIR/amsterdam/constants.json"
SOURCES="$SCRIPT_DIR/sources.json"

TABLE=0
while [ "$#" -gt 0 ]; do
  case "$1" in
    --table) TABLE=1 ;;
    *) echo "usage: scripts/check-fork-constants.sh [--table]" >&2; exit 2 ;;
  esac
  shift
done

if [ ! -x "$BIN" ]; then
  echo "REGRESSION — fork-constants: jaune binary not found at $BIN; build the executable first"
  exit 2
fi
if [ ! -f "$EXTRACTION" ]; then
  echo "REGRESSION — fork-constants: no extraction at $EXTRACTION; run scripts/gen-fork-constants.py"
  exit 2
fi

TMP="$(mktemp -d)" || { echo "REGRESSION — fork-constants: could not create a temp dir"; exit 2; }
trap 'rm -rf "$TMP"' EXIT

# The extraction names the forks. Printing each one's record is the only thing
# the shell does; the comparison is one Python pass over the results.
FORKS="$(python3 -c '
import json, sys
print(" ".join(sorted(json.load(open(sys.argv[1]))["forks"])))' "$EXTRACTION")" || {
  echo "REGRESSION — fork-constants: could not read $EXTRACTION"; exit 2; }

for FORK in $FORKS; do
  if "$BIN" --rules "$FORK" > "$TMP/$FORK.json" 2> "$TMP/$FORK.err"; then
    : > "$TMP/$FORK.refused"
  else
    printf 'refused\n' > "$TMP/$FORK.refused"
  fi
done

python3 - "$EXTRACTION" "$SOURCES" "$TMP" "$TABLE" <<'PYEOF'
import json, sys
from pathlib import Path

extraction_path, sources_path, tmp, want_table = sys.argv[1:5]
extraction = json.loads(Path(extraction_path).read_text())
sources = json.loads(Path(sources_path).read_text())
tmp = Path(tmp)
problems = []

pinned = sources["conformance_target"]["commit"]
taken = extraction["conformance_target_commit"]
if taken != pinned:
    problems.append(
        f"the extraction was taken at {taken} but sources.json pins {pinned}; "
        "regenerate with scripts/gen-fork-constants.py"
    )

coverage = extraction["coverage"]
checked = {k for k, v in coverage.items() if v["status"] == "checked"}
compared = 0
runnable = []


def compare_fields(fork, entry, printed, fields):
    """Compare one fork's printed record against the extraction, field by field."""
    n = 0
    for field in fields:
        if field not in printed:
            problems.append(f"{fork}: the printer emits no {field}")
            continue
        upstream = entry["constants"][field]
        want, source = upstream["value"], upstream["source"]
        got = printed[field]
        # The extractor reports precompiles sorted; the record carries them in
        # activation order, which is a different fact and is guarded in Lean.
        if field == "precompiles":
            got = sorted(got)
        if got != want:
            problems.append(
                f"{fork}.{field}: this build has {got!r}, {taken[:12]} has "
                f"{want!r} (from {source})"
            )
        n += 1
    return n

for fork, entry in sorted(extraction["forks"].items()):
    refused = (tmp / f"{fork}.refused").read_text().strip() == "refused"
    if refused:
        # A declared-but-unimplemented fork. `--rules` must refuse it, and
        # must refuse it for the stated reason rather than by falling over.
        err = (tmp / f"{fork}.err").read_text()
        if "UnsupportedForkError" not in err:
            problems.append(
                f"{fork}: --rules failed, but not with UnsupportedForkError: "
                f"{err.strip()[:200]}"
            )

        # Nothing of a refused fork is compared: there is no record to
        # compare. The refusal itself is the whole check.
        continue
    runnable.append(fork)
    try:
        printed = json.loads((tmp / f"{fork}.json").read_text())
    except json.JSONDecodeError as error:
        problems.append(f"{fork}: --rules did not print JSON: {error}")
        continue

    # Check 3, the one that keeps this gate from quietly shrinking.
    if set(printed) != set(coverage):
        missing = sorted(set(printed) - set(coverage))
        extra = sorted(set(coverage) - set(printed))
        problems.append(
            f"{fork}: the printer's fields and the coverage table disagree — "
            f"unclassified {missing}, classified-but-absent {extra}. A new "
            "ForkRules field must be classified in scripts/gen-fork-constants.py "
            "before this gate can pass."
        )

    compared += compare_fields(fork, entry, printed, sorted(checked))

if want_table == "1":
    amsterdam = extraction["forks"].get("Amsterdam")
    if amsterdam is not None:
        print(f"Amsterdam extraction at {taken}")
        print(f"  FORK_CRITERIA: {amsterdam['fork_criteria']}")
        print(f"  header fields: {amsterdam['header_field_count']}")
        for field, v in sorted(amsterdam["constants"].items()):
            print(f"  {field:34s} {json.dumps(v['value'])}")
        print()

if problems:
    for problem in problems:
        print(f"  - {problem}", file=sys.stderr)
    print(
        f"RED — fork-constants: {len(problems)} disagreement(s) with "
        f"execution-specs {taken[:12]}",
        file=sys.stderr,
    )
    raise SystemExit(1)

declared_refused = len(extraction["forks"]) - len(runnable)
print(
    f"OK — fork-constants: {compared} comparison(s) across {len(runnable)} "
    f"runnable fork(s) ({', '.join(runnable)}) match execution-specs "
    f"{taken[:12]}; {declared_refused} declared fork(s) refused"
)
PYEOF
exit $?
