#!/usr/bin/env bash
# Fixture-test harness for Jaune (REFACTOR.md Phase 0, step 0.1).
#
# Usage: scripts/check.sh (--depth | --smoke | --full | --patch | --rlp4 | --bls | --dir <path>) [--report <path>] [--rebase] [--no-build]
#
#   --depth       run the fuel/call-depth stress set (scripts/depth-tests.txt)
#   --smoke       run the smoke set (scripts/smoke-tests.txt)
#   --full        run every .json fixture under the fixture root
#   --patch       run the patch-plan target set (scripts/patch-tests.txt): the
#                 ten historical FAIL files
#   --rlp4        run the four invalid-RLP/header files (scripts/rlp4-tests.txt),
#                 a subset of --patch
#   --bls         run the EEST consensus set for the BLS12-381 and
#                 point-evaluation precompiles (scripts/bls-tests.txt) against
#                 the committed hand-authored target baseline
#                 scripts/baseline-bls.txt (precomps.md Step 9); the fixture
#                 root differs — see Environment
#   --dir <path>  run one .json fixture, or every .json fixture under a
#                 directory (the path must be inside the fixture root); ad hoc
#                 — if no baseline-dir.txt exists, the gate passes iff every
#                 selected file PASSes
#   --report <p>  write this run's report to <p> instead of overwriting the
#                 default scripts/report-<tier>.txt
#   --rebase      accept the current results as the new committed baseline
#                 (rejected for --patch/--rlp4: their desired result is fixed)
#   --no-build    skip `lake build jaune`
#
# --patch and --rlp4 are target gates, not baseline-comparison tiers: each
# succeeds if and only if every listed file is PASS. They have no baseline and
# never rebase.
#
# --bls compares against a committed baseline like the ordinary tiers, but the
# baseline is a hand-authored target (all PASS unless an entry carries a
# written justification), so --rebase is rejected; edit baseline-bls.txt
# directly instead. `#` comment lines in it document exclusions and
# justifications.
#
# Environment:
#   JAUNE_FIXTURES  fixture root (default:
#                   ~/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests;
#                   for --bls: ~/eest-fixtures/fixtures/blockchain_tests, the
#                   pinned EEST release snapshot — see scripts/vectors/SOURCES.md)
#   JAUNE_TIMEOUT   per-file wall-clock GUARD in seconds (default: 1800). Not a
#                   classifier — see below.
#
# Classification contract
# -----------------------
# Every fixture file must run to completion, and the only classifications are
# PASS and FAIL. Correctness is the sole pass/fail axis; wall time is never
# one. A failing test makes jaune throw and abort the whole invocation, so
# each fixture file runs in its own process.
#
# That process runs under a per-file wall-clock GUARD (a perl alarm; macOS has
# no coreutils timeout). The guard is not a classification: it is a
# "this should never fire" hang detector. The slowest fixture in the corpus
# runs ~763 s, so the 1800 s default has better than 2x headroom. If the guard
# ever trips, the run prints a HARNESS ERROR, aborts the tier immediately, and
# exits nonzero — no classification is recorded for that file, and no report
# or baseline can absorb the event.
#
# Per-file lines are `STATUS<TAB>TIME<TAB>path` in both the report
# (scripts/report-<tier>.txt, gitignored) and the committed baseline
# (scripts/baseline-<tier>.txt). The gate compares the STATUS column only; the
# TIME column is informational reference data recorded on the machine that ran
# --rebase (stated in each baseline's header) and never gate input. A run
# whose per-file time exceeds 2x its baseline reference prints a DRIFT note —
# informational, never a verdict.
#
# The gate passes iff every file's classification equals the committed
# baseline's — NOT iff every file passes. Any classification change is a
# regression.
#
# CLI contract: exit 0 if and only if the gate passes; the last line of
# output is a single unambiguous verdict line.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/jaune"

usage() {
  echo "usage: scripts/check.sh (--depth | --smoke | --full | --patch | --rlp4 | --bls | --dir <path>) [--report <path>] [--rebase] [--no-build]" >&2
  exit 2
}

TIER=""
DIR_PATH=""
REBASE=0
BUILD=1
REPORT_PATH=""
while [ $# -gt 0 ]; do
  case "$1" in
    --depth|--smoke|--full|--patch|--rlp4|--bls) TIER="${1#--}" ;;
    --dir)
      TIER="dir"
      shift
      [ $# -gt 0 ] || usage
      DIR_PATH="$1"
      ;;
    --report)
      shift
      [ $# -gt 0 ] || usage
      REPORT_PATH="$1"
      ;;
    --rebase) REBASE=1 ;;
    --no-build) BUILD=0 ;;
    *) echo "unknown argument: $1" >&2; usage ;;
  esac
  shift
done
[ -n "$TIER" ] || usage

# The bls tier runs the pinned EEST release snapshot, which lives outside the
# default fixture root. The wall-clock guard is uniform across tiers: it is a
# hang detector, not a per-tier performance budget.
if [ "$TIER" = "bls" ]; then
  FIXTURES="${JAUNE_FIXTURES:-$HOME/eest-fixtures/fixtures/blockchain_tests}"
else
  FIXTURES="${JAUNE_FIXTURES:-$HOME/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests}"
fi
GUARD="${JAUNE_TIMEOUT:-1800}"

# Target-gate tiers succeed iff every listed file is PASS; they have no
# baseline and never rebase.
case "$TIER" in
  patch|rlp4) IS_TARGET=1 ;;
  *)          IS_TARGET=0 ;;
esac
if [ "$IS_TARGET" -eq 1 ] && [ "$REBASE" -eq 1 ]; then
  echo "usage error: --rebase is not supported for the $TIER target gate; its desired result is fixed at all-PASS" >&2
  exit 2
fi

# The bls tier compares against a committed hand-authored target baseline;
# accepting observed results wholesale would defeat it.
if [ "$TIER" = "bls" ] && [ "$REBASE" -eq 1 ]; then
  echo "usage error: --rebase is not supported for the bls tier; its baseline is a hand-maintained target — edit scripts/baseline-bls.txt directly" >&2
  exit 2
fi

if [ ! -d "$FIXTURES" ]; then
  echo "REGRESSION — $TIER: fixture root not found: $FIXTURES"
  exit 1
fi

# Assemble the file list (paths relative to the fixture root, sorted).
case "$TIER" in
  depth|smoke|patch|rlp4|bls)
    LIST_FILE="$SCRIPT_DIR/$TIER-tests.txt"
    if [ ! -f "$LIST_FILE" ]; then
      echo "REGRESSION — $TIER: file list not found: $LIST_FILE"
      exit 1
    fi
    FILES="$(grep -v '^[[:space:]]*$' "$LIST_FILE")"
    ;;
  full)
    # .meta/ holds fixture-index metadata, not tests.
    FILES="$(find "$FIXTURES" -name '*.json' | sed "s|^$FIXTURES/||" \
      | grep -v -e '^\.meta/' -e '/\.meta/' | sort)"
    ;;
  dir)
    if [ ! -e "$DIR_PATH" ]; then
      echo "REGRESSION — dir: path not found: $DIR_PATH"
      exit 1
    fi
    if [ -d "$DIR_PATH" ]; then
      ABS="$(cd "$DIR_PATH" && pwd)"
    elif [ -f "$DIR_PATH" ]; then
      ABS="$(cd "$(dirname "$DIR_PATH")" && pwd)/$(basename "$DIR_PATH")"
      case "$ABS" in
        *.json) : ;;
        *) echo "REGRESSION — dir: selected file is not JSON: $ABS"; exit 1 ;;
      esac
    else
      echo "REGRESSION — dir: path is not a regular file or directory: $DIR_PATH"
      exit 1
    fi
    case "$ABS" in
      "$FIXTURES"|"$FIXTURES"/*) : ;;
      *)
        echo "REGRESSION — dir: $ABS is not under the fixture root $FIXTURES"
        exit 1
        ;;
    esac
    if [ -d "$ABS" ]; then
      FILES="$(find "$ABS" -name '*.json' | sed "s|^$FIXTURES/||" | sort)"
    else
      FILES="${ABS#"$FIXTURES"/}"
    fi
    ;;
esac

TOTAL="$(printf '%s\n' "$FILES" | grep -c .)"
if [ "$TOTAL" -eq 0 ]; then
  echo "REGRESSION — $TIER: no fixture files selected"
  exit 1
fi

if [ "$BUILD" -eq 1 ]; then
  if ! (cd "$ROOT" && lake build jaune); then
    echo "REGRESSION — $TIER: lake build jaune failed"
    exit 1
  fi
fi
if [ ! -x "$BIN" ]; then
  echo "REGRESSION — $TIER: jaune binary not found: $BIN"
  exit 1
fi

REPORT="${REPORT_PATH:-$SCRIPT_DIR/report-$TIER.txt}"
BASELINE="$SCRIPT_DIR/baseline-$TIER.txt"
mkdir -p "$(dirname "$REPORT")"
: > "$REPORT"

NPASS=0
NFAIL=0
I=0
while IFS= read -r REL; do
  [ -n "$REL" ] || continue
  I=$((I + 1))
  START="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"
  # Guard runner (macOS has no coreutils timeout): fork jaune, alarm the
  # parent, SIGKILL the child on trip and exit 142 *normally* — exiting rather
  # than dying by SIGALRM keeps bash's "Alarm clock" job-control notice off
  # this script's stderr, so a guard trip is announced only by the HARNESS
  # ERROR path below. A child killed by the guard reports 128+9 = 137, so it
  # can never be confused with the 142 the guard itself returns.
  perl -e '
    my $t = shift @ARGV;
    my $pid = fork();
    die "fork failed: $!" unless defined $pid;
    if (!$pid) { exec @ARGV; exit 127 }
    $SIG{ALRM} = sub { kill "KILL", $pid; waitpid($pid, 0); exit 142 };
    alarm $t;
    waitpid($pid, 0);
    alarm 0;
    my $st = $?;
    exit($st & 127 ? 128 + ($st & 127) : $st >> 8);
  ' "$GUARD" "$BIN" "$FIXTURES/$REL" --network Prague \
    > /dev/null 2>&1
  RC=$?
  ELAPSED="$(perl -e 'printf "%.2f", $ARGV[1] - $ARGV[0]' \
    "$START" "$(perl -MTime::HiRes=time -e 'printf "%.3f", time')")"
  if [ "$RC" -eq 142 ]; then
    # The guard is a hang detector, never a classification. Nothing is written
    # to the report for this file and the tier stops here.
    printf 'HARNESS ERROR — %s exceeded the %ss guard; no fixture legitimately runs this long — investigate before rerunning\n' \
      "$REL" "$GUARD" >&2
    echo "HARNESS ERROR — $TIER: wall-clock guard tripped on $REL after ${ELAPSED}s (guard ${GUARD}s); tier aborted at file $I/$TOTAL, no classification recorded; partial report: $REPORT"
    exit 1
  fi
  if [ "$RC" -eq 0 ]; then
    CLS=PASS; NPASS=$((NPASS + 1))
  else
    CLS=FAIL; NFAIL=$((NFAIL + 1))
  fi
  printf '%s\t%ss\t%s\n' "$CLS" "$ELAPSED" "$REL" >> "$REPORT"
  printf '[%d/%d] %s %ss %s\n' "$I" "$TOTAL" "$CLS" "$ELAPSED" "$REL" >&2
done <<EOF
$FILES
EOF

SUMMARY="$NPASS PASS, $NFAIL FAIL"

# Target gates: fixed all-PASS end condition, no baseline, no rebase.
if [ "$IS_TARGET" -eq 1 ]; then
  if [ "$NFAIL" -eq 0 ]; then
    echo "OK — $TIER: $NPASS/$TOTAL PASS ($SUMMARY)"
    exit 0
  fi
  echo "RED — $TIER: $NPASS/$TOTAL PASS, target not met ($SUMMARY); see $REPORT"
  exit 1
fi

if [ "$REBASE" -eq 1 ]; then
  # STATUS and TIME are regenerated together; the times become this machine's
  # reference data.
  cp "$REPORT" "$BASELINE"
  echo "OK — $TIER: baseline rebased with $TOTAL files ($SUMMARY)"
  exit 0
fi

if [ ! -f "$BASELINE" ]; then
  if [ "$TIER" = "dir" ]; then
    if [ "$NFAIL" -eq 0 ]; then
      echo "OK — dir: $TOTAL files, all PASS, no baseline ($SUMMARY)"
      exit 0
    fi
    echo "REGRESSION — dir: $NFAIL FAIL with no baseline; see $REPORT"
    exit 1
  fi
  if [ "$TIER" = "bls" ]; then
    echo "REGRESSION — bls: no target baseline at $BASELINE (it is committed and hand-maintained, never rebased)"
    exit 1
  fi
  echo "REGRESSION — $TIER: no baseline at $BASELINE (run once with --rebase)"
  exit 1
fi

# Baselines are STATUS<TAB>TIME<TAB>path, plus (in the hand-authored bls
# baseline) `#` comment lines carrying exclusions and justifications. Strip
# comments, then reject anything that is not a well-formed timed line rather
# than letting a stale two-column baseline compare as a truncated field.
CMP_DIR="$(mktemp -d)"
grep -v -e '^[[:space:]]*#' -e '^[[:space:]]*$' "$BASELINE" > "$CMP_DIR/baseline-raw"
MALFORMED="$(awk -F'\t' 'NF != 3 { print FILENAME ":" FNR ": " $0 }' "$CMP_DIR/baseline-raw")"
if [ -n "$MALFORMED" ]; then
  printf '%s\n' "$MALFORMED" >&2
  if [ "$TIER" = "bls" ]; then
    HINT="it is hand-maintained, never rebased — add the missing TIME column by hand"
  else
    HINT="regenerate it with --rebase"
  fi
  echo "REGRESSION — $TIER: $BASELINE is not in STATUS<TAB>TIME<TAB>path form ($HINT)"
  exit 1
fi

# The gate compares STATUS only; TIME is reference data, never gate input.
cut -f1,3 "$CMP_DIR/baseline-raw" > "$CMP_DIR/baseline"
cut -f1,3 "$REPORT" > "$CMP_DIR/report"

# Informational: a file taking more than 2x its baseline reference time. Never
# a verdict — the reference times come from whatever machine last rebased.
awk -F'\t' '
  function secs(v) { sub(/s$/, "", v); return v + 0 }
  NR == FNR { bt[$3] = secs($2); next }
  ($3 in bt) && bt[$3] >= 1.0 && secs($2) > 2 * bt[$3] {
    printf "DRIFT — %s: %ss vs %.2fs baseline reference (%.1fx); informational only\n", \
      $3, secs($2), bt[$3], secs($2) / bt[$3]
  }
' "$CMP_DIR/baseline-raw" "$REPORT"

CHANGES="$(awk -F'\t' '
  NR == FNR { base[$2] = $1; next }
  {
    old = ($2 in base) ? base[$2] : "MISSING"
    if (old != $1) print old "\t" $1 "\t" $2
    delete base[$2]
  }
  END { for (file in base) print base[file] "\tMISSING\t" file }
' "$CMP_DIR/baseline" "$CMP_DIR/report")"

if [ -z "$CHANGES" ]; then
  echo "OK — $TIER: $TOTAL files match baseline ($SUMMARY)"
  exit 0
fi

NCHANGED="$(printf '%s\n' "$CHANGES" | grep -c .)"
printf '%s\n' "$CHANGES" | while IFS="$(printf '\t')" read -r OLD NEW REL; do
  printf 'CHANGE — %s: %s -> %s\n' "$REL" "$OLD" "$NEW"
done
echo "REGRESSION — $NCHANGED classification changes vs baseline; see $REPORT"
exit 1
