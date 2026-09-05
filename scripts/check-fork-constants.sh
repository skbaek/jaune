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
# `Fork.supported` cannot drift apart.
#
# A refused fork may nonetheless carry a *metering vehicle*: a partial record
# whose numbers this build does implement, printed by `--rules-partial` and
# resolved only through the transition tool's own lane table. For such a fork
# three further things are checked, and together they are what keeps a partial
# claim honest:
#
#   4. the per-fork coverage table classifies *every* field of the record --
#      compared, covered elsewhere, or deferred with the owning goal named;
#   5. the metering printer's key set is exactly the compared set, so the lane
#      cannot quietly shrink or quietly widen; and
#   6. every compared field matches the pinned revision, exactly as for a fork
#      this build runs.
#
# Usage: scripts/check-fork-constants.sh [--table]
#
#   --table  additionally print the extracted Amsterdam column in full, for a
#            report. The rows outside the metering vehicle are inventory, not a
#            check; the rows inside it are checked by rule 6 above.
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
  # A refused fork may still carry a metering vehicle -- a partial record whose
  # numbers this build does implement. Ask for it unconditionally; the Python
  # pass decides whether one was expected.
  if "$BIN" --rules-partial "$FORK" > "$TMP/$FORK.partial.json" \
      2> "$TMP/$FORK.partial.err"; then
    : > "$TMP/$FORK.partial.ok"
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
fork_coverage = extraction.get("fork_coverage", {})
compared = 0
metered = []
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

        # A refused fork may still be metered. When it is, every field of the
        # record has to be classified for it -- compared against upstream
        # because the vehicle claims it, covered by behaviour elsewhere, or
        # deferred with the goal that owns it named -- and the partial
        # printer's key set has to be exactly the compared set. That is what
        # stops the metering lane from quietly shrinking, and what makes the
        # deferral a recorded fact rather than an omission.
        per_fork = fork_coverage.get(fork)
        has_partial = (tmp / f"{fork}.partial.ok").exists()
        if per_fork is None:
            if has_partial:
                problems.append(
                    f"{fork}: --rules-partial prints a metering record, but "
                    "the extraction classifies no fields for this fork; "
                    "classify them in scripts/gen-fork-constants.py"
                )
            continue
        if not has_partial:
            partial_err = (tmp / f"{fork}.partial.err").read_text()
            problems.append(
                f"{fork}: the extraction classifies fields for a metering "
                f"vehicle, but --rules-partial refused: {partial_err.strip()[:200]}"
            )
            continue
        if set(per_fork) != set(coverage):
            missing = sorted(set(coverage) - set(per_fork))
            extra = sorted(set(per_fork) - set(coverage))
            problems.append(
                f"{fork}: the per-fork coverage table is not the whole record "
                f"— unclassified {missing}, classified-but-absent {extra}"
            )
        for field, entry_status in sorted(per_fork.items()):
            if entry_status["status"] == "deferred" and not entry_status.get("owner"):
                problems.append(
                    f"{fork}.{field}: deferred with no owning goal named"
                )
        metering_checked = {
            k for k, v in per_fork.items() if v["status"] == "checked"
        }
        try:
            partial = json.loads((tmp / f"{fork}.partial.json").read_text())
        except json.JSONDecodeError as error:
            problems.append(f"{fork}: --rules-partial did not print JSON: {error}")
            continue
        if set(partial) != metering_checked:
            missing = sorted(metering_checked - set(partial))
            extra = sorted(set(partial) - metering_checked)
            problems.append(
                f"{fork}: the metering printer's fields and the per-fork "
                f"coverage table disagree — not printed {missing}, printed but "
                f"not checked {extra}"
            )
        metered.append(fork)
        compared += compare_fields(fork, entry, partial, sorted(metering_checked))
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

metering_note = ""
if metered:
    deferred = sum(
        1
        for f in metered
        for v in fork_coverage[f].values()
        if v["status"] == "deferred"
    )
    metering_note = (
        f"; {len(metered)} metering vehicle(s) ({', '.join(metered)}) compared "
        f"on their claimed fields, {deferred} field(s) deferred to a named goal"
    )

print(
    f"OK — fork-constants: {compared} constant(s) across {len(runnable)} fork(s) "
    f"({', '.join(runnable)}) match execution-specs {taken[:12]}; "
    f"{len(extraction['forks']) - len(runnable)} declared fork(s) refused"
    f"{metering_note}"
)
PYEOF
exit $?
