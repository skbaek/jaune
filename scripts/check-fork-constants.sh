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
# One row of check 1 is not rule data but schedule data: `mainnetActivation`,
# the pinned `FORK_CRITERIA` timestamp against `mainnetChainConfig`'s
# activation for the fork (D13 of the Amsterdam programme; goal
# jaune-amsterdam-currency-v1). Today Amsterdam is `Unscheduled` upstream and
# absent from the mainnet schedule, so the row agrees on `null`. The day the
# pin says `ByTimestamp`, this gate turns red at `Amsterdam.mainnetActivation`
# and names the constant to write; an activation the build carries that the
# pin does not, or at a different second, is red the same way. Before this
# goal the criterion was only *printed*, under `--table`, and compared to
# nothing.
#
# The same schedule fact is also compared for every declared fork, refused ones
# included: `jaune --mainnet-schedule` prints `mainnetChainConfig`'s criterion
# for each fork, and the extraction's `mainnet_schedule` carries every EELS
# fork module's `FORK_CRITERIA` from Byzantium on (goal
# jaune-historical-forks-v1, design §4). A timestamp is a bare number, a block
# number `{"block": n}`, no activation `null`; a declared fork with no EELS
# module (Jaune's EIP-1283 `Constantinople`) must print `null`. These rows are
# counted apart from the rule comparisons.
#
# A fork this build declares but does not implement is expected to be refused
# by `--rules`; that is checked too, so the gate's fork list and
# `Fork.supported` cannot drift apart. Refusal is not the end of the story
# for such a fork (goal U10): its committed literal is still compared against
# the pinned `execution-specs` module through `--rules-literal`, which prints
# `Fork.ruleSet` without resolving it. Dormant cells -- fields the fork never
# reads, classified in the extraction's per-fork `dormant` map -- are skipped,
# never compared; everything else is compared exactly as for a runnable fork.
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

if ! "$BIN" --mainnet-schedule > "$TMP/schedule.json" 2> "$TMP/schedule.err"; then
  echo "REGRESSION — fork-constants: jaune --mainnet-schedule failed: $(head -c 200 "$TMP/schedule.err")"
  exit 2
fi

for FORK in $FORKS; do
  if "$BIN" --rules "$FORK" > "$TMP/$FORK.json" 2> "$TMP/$FORK.err"; then
    : > "$TMP/$FORK.refused"
  else
    printf 'refused\n' > "$TMP/$FORK.refused"
  fi
  if "$BIN" --rules-literal "$FORK" > "$TMP/$FORK.literal.json" 2> "$TMP/$FORK.literal.err"; then
    : > "$TMP/$FORK.literal.ok"
  else
    printf 'failed\n' > "$TMP/$FORK.literal.ok"
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
literal_compared = 0
dormant_skipped = 0
runnable = []
literal_forks = []


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
            if field == "mainnetActivation" and got is None:
                # D13: the pin schedules the fork and this build does not.
                problems.append(
                    f"{fork}.mainnetActivation: {taken[:12]} schedules {fork} "
                    f"on mainnet at timestamp {want} ({source}), but "
                    f"mainnetChainConfig carries no {fork} activation. Write "
                    f"`mainnet{fork}Timestamp : Nat := {want}` in Jaune/Fork.lean "
                    f"and append ⟨.{fork.lower()}, mainnet{fork}Timestamp⟩ to "
                    "mainnetChainConfig.activations."
                )
            elif field == "mainnetActivation" and want is None:
                problems.append(
                    f"{fork}.mainnetActivation: this build activates {fork} on "
                    f"mainnet at timestamp {got}, but {taken[:12]}'s FORK_CRITERIA "
                    f"for it is unscheduled ({source})."
                )
            elif field == "mainnetActivation":
                problems.append(
                    f"{fork}.mainnetActivation: this build activates {fork} on "
                    f"mainnet at {got}, {taken[:12]} at {want} ({source})."
                )
            else:
                problems.append(
                    f"{fork}.{field}: this build has {got!r}, {taken[:12]} has "
                    f"{want!r} (from {source})"
                )
        n += 1
    return n

def check_key_set(fork, printed, printer):
    if set(printed) != set(coverage):
        missing = sorted(set(printed) - set(coverage))
        extra = sorted(set(coverage) - set(printed))
        problems.append(
            f"{fork}: the {printer} fields and the coverage table disagree — "
            f"unclassified {missing}, classified-but-absent {extra}. A new "
            "ForkRules field must be classified in scripts/gen-fork-constants.py "
            "before this gate can pass."
        )


for fork, entry in sorted(extraction["forks"].items()):
    refused = (tmp / f"{fork}.refused").read_text().strip() == "refused"
    dormant = entry.get("dormant", {})
    unknown_dormant = sorted(set(dormant) - set(checked))
    if unknown_dormant:
        problems.append(
            f"{fork}: the extraction classifies dormant cells outside the "
            f"coverage table: {unknown_dormant}"
        )
    live = sorted(checked - set(dormant))
    if refused:
        # A declared-but-unimplemented fork. `--rules` must refuse it, and
        # must refuse it for the stated reason rather than by falling over.
        err = (tmp / f"{fork}.err").read_text()
        if "UnsupportedForkError" not in err:
            problems.append(
                f"{fork}: --rules failed, but not with UnsupportedForkError: "
                f"{err.strip()[:200]}"
            )

        # Goal U10: the refusal is the execution check, and the literal is
        # the constants check. `--rules-literal` prints the committed
        # record without resolving it; every live cell is compared, every
        # dormant cell is classified, not compared.
        if (tmp / f"{fork}.literal.ok").read_text().strip() != "":
            lit_err = (tmp / f"{fork}.literal.err").read_text()
            problems.append(
                f"{fork}: --rules-literal failed: {lit_err.strip()[:200]}"
            )
            continue
        try:
            printed = json.loads((tmp / f"{fork}.literal.json").read_text())
        except json.JSONDecodeError as error:
            problems.append(f"{fork}: --rules-literal did not print JSON: {error}")
            continue
        check_key_set(fork, printed, "--rules-literal printer's")
        literal_forks.append(fork)
        literal_compared += compare_fields(fork, entry, printed, live)
        dormant_skipped += len(dormant)
        continue
    runnable.append(fork)
    try:
        printed = json.loads((tmp / f"{fork}.json").read_text())
    except json.JSONDecodeError as error:
        problems.append(f"{fork}: --rules did not print JSON: {error}")
        continue

    # Check 3, the one that keeps this gate from quietly shrinking.
    check_key_set(fork, printed, "printer's")

    compared += compare_fields(fork, entry, printed, sorted(checked))

# The mainnet schedule, every declared fork.
schedule_rows = 0
want_schedule = extraction.get("mainnet_schedule")
if want_schedule is None:
    problems.append(
        "the extraction has no mainnet_schedule; regenerate with "
        "scripts/gen-fork-constants.py"
    )
else:
    try:
        got_schedule = json.loads((tmp / "schedule.json").read_text())
    except json.JSONDecodeError as error:
        problems.append(f"--mainnet-schedule did not print JSON: {error}")
        got_schedule = {}
    for fork, upstream in sorted(want_schedule.items()):
        if fork not in got_schedule:
            problems.append(
                f"{fork}.mainnetSchedule: the printer names no fork {fork}"
            )
            continue
        if got_schedule[fork] != upstream["value"]:
            problems.append(
                f"{fork}.mainnetSchedule: mainnetChainConfig activates {fork} "
                f"at {got_schedule[fork]!r}, {taken[:12]} at "
                f"{upstream['value']!r} ({upstream['source']})"
            )
        schedule_rows += 1
    for fork in sorted(set(got_schedule) - set(want_schedule)):
        if got_schedule[fork] is not None:
            problems.append(
                f"{fork}.mainnetSchedule: mainnetChainConfig activates {fork} "
                f"at {got_schedule[fork]!r}, but no {taken[:12]} fork module "
                "names it"
            )
        schedule_rows += 1

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
    f"{taken[:12]}; {literal_compared} literal comparison(s) across "
    f"{len(literal_forks)} refused fork(s) ({', '.join(literal_forks)}), "
    f"{dormant_skipped} dormant cell(s) classified, not compared; "
    f"{declared_refused} declared fork(s) refused; mainnet "
    f"schedule: {schedule_rows} fork(s) match FORK_CRITERIA"
)
PYEOF
exit $?
