#!/usr/bin/env bash
# Fixture-test harness for Jaune (REFACTOR.md Phase 0, step 0.1).
#
# Usage: scripts/check-legacy.sh (--depth | --smoke | --full | --patch | --rlp4 | --bls | --dir <path>) [--report <path>] [--rebase | --refresh-times] [--no-build] [--jobs <n>|auto]
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
#   --rebase      accept the current classifications as the new tracked
#                 correctness baseline, printing the delta it absorbs; also
#                 refresh this host's ignored timing baseline
#                 (rejected for --patch/--rlp4: their desired result is fixed)
#   --refresh-times
#                 refresh only this host's ignored timing baseline: run the
#                 tier, require every STATUS to match the tracked correctness
#                 baseline, and refuse to write anything if it does not
#   --no-build    skip `lake build jaune`
#   --jobs <n>    run <n> fixtures concurrently (default 1 = sequential).
#                 `auto` resolves from effective memory and CPU capacity. See
#                 "Parallel dispatch" below; sequential remains the default and
#                 is the only mode whose timings are ever authoritative.
#
# --patch and --rlp4 are target gates, not baseline-comparison tiers: each
# succeeds if and only if every listed file is PASS. They have no baseline and
# never rebase.
#
# --bls compares against a tracked baseline like the ordinary tiers, but that
# baseline is a hand-authored target (all PASS unless an entry carries a
# written justification), so --rebase is rejected; edit baseline-bls.txt
# directly instead. Its host-local times may still be refreshed safely with
# --refresh-times. `#` comment lines document exclusions and justifications.
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
# runs ~373 s (loopMul, as of 2026-07-31; it was ~763 s until the BLAKE2b
# unboxing), so the 1800 s default has better than 4x headroom. If the guard
# ever trips, the run prints a HARNESS ERROR, aborts the tier immediately, and
# exits nonzero — no classification is recorded for that file, and no report
# or baseline can absorb the event.
#
# Per-file reports are `STATUS<TAB>TIME<TAB>path`. Tracked correctness
# baselines (`scripts/baseline-<tier>.txt`) are `STATUS<TAB>path`; ignored
# host-local timing baselines (`scripts/baseline-<tier>-times.txt`) are
# `TIME<TAB>path`. A host's first complete sequential run initializes its
# timing baseline and performs no timing comparison. Later runs print a DRIFT
# note above 2x that same host's reference — informational, never a verdict.
#
# The gate passes iff every file's classification equals the committed
# baseline's — NOT iff every file passes. Any classification change is a
# regression.
#
# Writing the baseline: two verbs, deliberately separate
# ------------------------------------------------------
# Correctness and timing have different authority, so the two reasons to
# rewrite their separate files deserve different answers.
#
#   --rebase        "the classifications legitimately changed; accept them."
#                   Rare and consequential. It absorbs whatever it is given, so
#                   it now prints the classification delta it is about to
#                   absorb; a reviewer sees exactly what was accepted, and the
#                   commit message writes itself.
#   --refresh-times "the classifications are identical, the code got faster,
#                   refresh this host's reference times." Safe and mechanical.
#                   It compares STATUS first and writes nothing unless every
#                   file matches, so it cannot absorb a regression.
#
# Refreshing TIME is not cosmetic: parallel dispatch is longest-first, seeded
# from this host's timing baseline when present, so a stale local baseline
# schedules the wrong fixture first. Both verbs are sequential-only, for the
# reason given under Parallel dispatch, and both are rejected for target gates.
# The hand-maintained bls tier rejects --rebase but accepts --refresh-times.
#
# Parallel dispatch (--jobs)
# --------------------------
# Fixture runs are independent, so --jobs <n> dispatches them across <n>
# concurrent processes. Sequential (--jobs 1) is the default and its behaviour
# is untouched: same guard, same ordering, same authoritative timings.
#
# What parallel mode changes:
#
#   * Timings become reference-only. A contended run's TIME column reflects
#     scheduling, not the fixture, so --rebase and --refresh-times are both
#     rejected outright and the DRIFT comparison is skipped entirely rather
#     than computed and suppressed. The gate itself is unaffected — it only
#     ever compared STATUS.
#   * The guard rises to 2000s (from 1800s). This is the sole thing a parallel
#     run still decides for real. Measured contention on this class of machine
#     is 1.16x at 4 concurrent and 1.65x at 8, so the slowest fixture lands
#     near 430s and 615s respectively; 2000s clears both with room to spare
#     while still tripping long before anything pathological. (The 2000s figure
#     was set when the slowest fixture was 766s and landed near 875s/1250s; it
#     is left as-is — a hang detector wants headroom, not tightness.)
#   * Dispatch order becomes longest-first, seeded from the host-local timing
#     baseline when one exists. This matters: the corpus is
#     dominated by a single indivisible fixture, and starting it late adds its
#     full runtime to the tail.
#
# What parallel mode does NOT change: the report is reassembled in the
# sequential order, not completion order, so a report from either mode diffs
# cleanly against the same baseline.
#
# `auto` is shared with the mainnet and vector harnesses. It takes the smaller
# of effective logical CPU capacity and a memory pool with 1 GiB reserved plus
# 2.4 GiB per worker. Linux detection follows finite cgroup-v2 ancestors as
# well as host MemAvailable; macOS uses reclaimable `vm_stat` pages. Missing
# trustworthy memory information falls back to one worker, and an UNREADABLE
# boundary file counts as missing rather than as absent: a leaf whose own
# `memory.max` is refused resolves to one worker even when a permissive
# ancestor is readable. A numeric `--jobs` remains an explicit override and
# bypasses this sizing policy.
#
# What the job count is worth depends on which bound a tier is under:
#
#   - Latency-bound (--full: one 373s fixture, loopMul, is 33% of the serial
#     total) is flat in the job count. The makespan is that one fixture
#     finishing alone, and no number of workers changes it: 462s at 10 jobs
#     measured 2026-07-31. Before the BLAKE2b unboxing the holder of that
#     position was a 766s fixture at 41% of the total, and the makespan was
#     886s at 4 jobs and 899s at 8 — same shape, different file.
#
#     "Serial total" means the sum of the per-file TIME column: 1145.8s as of
#     2026-07-31, down from 3337.9s. That is a LOWER BOUND on sequential wall
#     time, not a measurement of it — a sequential run also pays 2983 process
#     spawns and harness overhead. A sequential --full therefore still sits
#     above the 1000s deferral threshold and still needs explicit
#     authorization; only the parallel run is under it, as it already was
#     before the unboxing.
#   - Throughput-bound (the current-mainnet suites: 90% of files run under
#     0.15s, so process spawn dominates) improves substantially: 435s at 4
#     jobs, 299s at 10.
#
# One default therefore serves both — the throughput-bound case gains a lot and
# the latency-bound case is indifferent to within 1.4%.
#
# One run at a time
# -----------------
# A run takes an exclusive lock on its report file, and the Medium/Long tiers
# and every parallel run also take a shared heavy-gate lock. A second run that
# would contend is REFUSED immediately, naming the holder; it does not queue and
# writes nothing. See scripts/gate-lock.sh for the mechanism and the incident.
#
# Independently of the lock, a report or baseline that repeats a path is a
# HARNESS ERROR rather than a classification verdict: the comparison treats path
# as a primary key, and a doubled report would otherwise be scored as one
# spurious `MISSING -> <status>` per file.
#
# CLI contract: exit 0 if and only if the gate passes; the last line of
# output is a single unambiguous verdict line. A refusal exits 2 — the gate did
# not fail, it did not run.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/jaune"
BASELINE_HELPER="$SCRIPT_DIR/check-legacy-baseline.py"

# Captured before the argument loop consumes them, so a lock records the whole
# command line and a refusal can name what is holding it.
GATE_CMDLINE="$0 $*"
. "$SCRIPT_DIR/gate-lock.sh"

# One cleanup function, one EXIT trap, installed once. A second `trap ... EXIT`
# silently replaces the first, so every scratch path this script removes has to
# live here.
WORK=""
cleanup() {
  gate_lock_release_all
  if [ -n "$WORK" ]; then rm -rf "$WORK"; fi
  return 0
}
trap cleanup EXIT

usage() {
  echo "usage: scripts/check-legacy.sh (--depth | --smoke | --full | --patch | --rlp4 | --bls | --dir <path>) [--report <path>] [--rebase | --refresh-times] [--no-build] [--jobs <n>|auto]" >&2
  exit 2
}

TIER=""
DIR_PATH=""
REBASE=0
REFRESH=0
BUILD=1
REPORT_PATH=""
JOBS=1
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
    --jobs)
      shift
      [ $# -gt 0 ] || usage
      JOBS="$1"
      ;;
    --rebase) REBASE=1 ;;
    --refresh-times) REFRESH=1 ;;
    --no-build) BUILD=0 ;;
    *) echo "unknown argument: $1" >&2; usage ;;
  esac
  shift
done
[ -n "$TIER" ] || usage

if [ "$JOBS" = "auto" ]; then
  if ! JOBS="$(python3 "$SCRIPT_DIR/fixture_jobs.py" --explain)"; then
    echo "usage error: could not resolve resource-aware automatic job count" >&2
    exit 2
  fi
fi
case "$JOBS" in
  ''|*[!0-9]*)
    echo "usage error: --jobs takes a positive integer or 'auto', not $JOBS" >&2
    exit 2
    ;;
esac
if [ "$JOBS" -lt 1 ]; then
  echo "usage error: --jobs must be at least 1" >&2
  exit 2
fi

# The bls tier runs the pinned EEST release snapshot, which lives outside the
# default fixture root. The wall-clock guard is uniform across tiers: it is a
# hang detector, not a per-tier performance budget.
if [ "$TIER" = "bls" ]; then
  FIXTURES="${JAUNE_FIXTURES:-$HOME/eest-fixtures/fixtures/blockchain_tests}"
else
  FIXTURES="${JAUNE_FIXTURES:-$HOME/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests}"
fi
# A parallel run's workers contend, so the guard rises to 2000s there. It stays
# a hang detector in both modes, never a performance budget. An explicit
# JAUNE_TIMEOUT still wins in either mode.
if [ "$JOBS" -gt 1 ]; then
  GUARD="${JAUNE_TIMEOUT:-2000}"
else
  GUARD="${JAUNE_TIMEOUT:-1800}"
fi

# Target-gate tiers succeed iff every listed file is PASS; they have no
# baseline and never rebase.
case "$TIER" in
  patch|rlp4) IS_TARGET=1 ;;
  *)          IS_TARGET=0 ;;
esac
if [ "$REBASE" -eq 1 ] && [ "$REFRESH" -eq 1 ]; then
  echo "usage error: --rebase and --refresh-times are mutually exclusive; --rebase accepts new classifications, --refresh-times refuses them" >&2
  exit 2
fi

# Name the verb in the usage errors below, so a --refresh-times refusal is never
# reported as though --rebase had been asked for.
if [ "$REFRESH" -eq 1 ]; then WRITE_FLAG="--refresh-times"; else WRITE_FLAG="--rebase"; fi
WRITES=$((REBASE + REFRESH))

if [ "$IS_TARGET" -eq 1 ] && [ "$WRITES" -eq 1 ]; then
  echo "usage error: $WRITE_FLAG is not supported for the $TIER target gate; its desired result is fixed at all-PASS" >&2
  exit 2
fi

# The bls tier compares against a tracked hand-authored target baseline;
# accepting observed classifications wholesale would defeat it. Its separate
# host-local timing state can be refreshed without touching that target.
if [ "$TIER" = "bls" ] && [ "$REBASE" -eq 1 ]; then
  echo "usage error: --rebase is not supported for the bls tier; its correctness baseline is a hand-maintained target — edit scripts/baseline-bls.txt directly" >&2
  exit 2
fi

# Timings from a contended run describe the scheduler, not the fixture, so they
# must never become host-local reference data. Rejecting outright rather than
# ignoring: a silently-dropped --rebase would leave the operator believing the
# baseline had been refreshed.
if [ "$JOBS" -gt 1 ] && [ "$WRITES" -eq 1 ]; then
  echo "usage error: $WRITE_FLAG is not supported with --jobs > 1; a parallel run's TIME column is contended and would corrupt this host's timing baseline — run it sequentially" >&2
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

# Path is a primary key on the selection, and the comparison downstream depends
# on it: its lookup table is destructive, so a repeated path finds nothing on
# its second occurrence and is scored `MISSING -> <status>` — a fabricated
# classification change. --full derives its list from `find | sort` and cannot
# repeat, but the tier lists are hand-edited, so this is reachable there. Fail
# before running anything rather than after.
SEL_DUPS="$(printf '%s\n' "$FILES" | grep -v '^[[:space:]]*$' | sort | uniq -d)"
if [ -n "$SEL_DUPS" ]; then
  printf '%s\n' "$SEL_DUPS" | while IFS= read -r D; do
    echo "DUPLICATE — $TIER: selected more than once: $D" >&2
  done
  NSEL_DUPS="$(printf '%s\n' "$SEL_DUPS" | grep -c .)"
  echo "HARNESS ERROR — $TIER: the selection names $NSEL_DUPS path(s) more than once; no fixture was run"
  exit 1
fi

REPORT="${REPORT_PATH:-$SCRIPT_DIR/report-$TIER.txt}"
BASELINE="$SCRIPT_DIR/baseline-$TIER.txt"
TIMING_BASELINE="$SCRIPT_DIR/baseline-$TIER-times.txt"
mkdir -p "$(dirname "$REPORT")"
# Canonicalised, because the lock below is keyed on this string: two spellings
# of one path would otherwise take two locks and share a file. Same idiom as
# the --dir resolution above.
REPORT="$(cd "$(dirname "$REPORT")" && pwd)/$(basename "$REPORT")"

# Locks before the build, so a refusal costs nothing and two runs cannot even
# contend over `lake build`. Heavy first, then the report: a consistent order,
# though rejection rather than queuing already makes deadlock impossible.
#
# The heavy lock is held by the catalogue's Medium and Long tiers and by any
# run that dispatches a worker pool. Two of those on one host contend whatever
# they write — the 2026-07-31 pair inflated fixture time ~7x — and a contended
# run's TIME column describes the scheduler rather than the fixture. The
# sub-second target gates and a sequential --depth or --dir stay outside it, so
# the cheap check you run while iterating is never hostage to a --full.
case "$TIER" in
  smoke|bls|full) HEAVY=1 ;;
  *)              HEAVY=0 ;;
esac
if [ "$JOBS" -gt 1 ]; then HEAVY=1; fi
if [ "$HEAVY" -eq 1 ]; then
  gate_lock_heavy_acquire "$TIER" \
    "the heavy-gate lock" \
    "wait for that run to finish; --patch, --rlp4 and a sequential --depth or --dir do not take this lock" \
    || exit 2
fi
gate_lock_acquire "$REPORT.lock" "$TIER" "$REPORT" \
  "wait for that run to finish, or pass --report <path> to write elsewhere" \
  || exit 2

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

: > "$REPORT"

NPASS=0
NFAIL=0

if [ "$JOBS" -gt 1 ]; then
  RUNNER="$SCRIPT_DIR/run-fixture.sh"
  if [ ! -x "$RUNNER" ]; then
    echo "REGRESSION — $TIER: parallel runner not found or not executable: $RUNNER"
    exit 1
  fi
  WORK="$(mktemp -d)"
  LINES="$WORK/lines"
  mkdir -p "$LINES"

  # Number the selection in *report* order. Dispatch order is chosen separately
  # below; keeping the two apart is what lets a parallel report be reassembled
  # byte-for-byte in the order a sequential run would have produced.
  printf '%s\n' "$FILES" | grep -v '^[[:space:]]*$' \
    | awk '{ printf "%d %s\n", NR, $0 }' > "$WORK/numbered"

  # Longest-first dispatch is seeded only from this host's ignored timing
  # baseline. A fresh clone has no weights yet and therefore preserves report
  # order; its first complete sequential run creates the local reference.
  if ! python3 "$BASELINE_HELPER" dispatch --timings "$TIMING_BASELINE" \
      --numbered "$WORK/numbered" --output "$WORK/dispatch"; then
    echo "HARNESS ERROR — $TIER: could not construct fixture dispatch order"
    exit 2
  fi

  echo "dispatching $TOTAL files across $JOBS workers (guard ${GUARD}s, longest-first)" >&2

  RF_BIN="$BIN"; RF_GUARD="$GUARD"; RF_OUT="$LINES"
  RF_FIX="$FIXTURES"; RF_NET="Prague"
  export RF_BIN RF_GUARD RF_OUT RF_FIX RF_NET
  # `{}` carries the whole "idx rel" line as one argument; the shim re-splits it
  # and execs the runner. No fixture path in either corpus contains whitespace.
  xargs -P "$JOBS" -I{} bash -c '
    set -- $1
    exec "$0" "$RF_BIN" "$RF_GUARD" "$RF_OUT" "$1" "$RF_FIX/$2" "$RF_NET" "$2"
  ' "$RUNNER" {} < "$WORK/dispatch"

  # A guard trip aborts the pool via exit 255 and leaves this sentinel. It is a
  # harness event, not a classification: no report or baseline may absorb it.
  if [ -f "$LINES/.guard-tripped" ]; then
    TRIPPED="$(cut -f1 "$LINES/.guard-tripped")"
    DONE="$(find "$LINES" -name '*.line' | grep -c . || true)"
    echo "HARNESS ERROR — $TIER: wall-clock guard tripped on $TRIPPED (guard ${GUARD}s); tier aborted after $DONE/$TOTAL classifications, none recorded for that file"
    exit 1
  fi

  # Reassemble in report order. A missing line means a worker died without
  # classifying, which must not silently shrink the report.
  MISSING=0
  while read -r IDX REL; do
    if [ -f "$LINES/$IDX.line" ]; then
      cat "$LINES/$IDX.line" >> "$REPORT"
    else
      MISSING=$((MISSING + 1))
      echo "MISSING — no classification recorded for $REL" >&2
    fi
  done < "$WORK/numbered"
  if [ "$MISSING" -ne 0 ]; then
    echo "HARNESS ERROR — $TIER: $MISSING/$TOTAL files produced no classification; see $REPORT"
    exit 1
  fi

  NPASS="$(cut -f1 "$REPORT" | grep -c '^PASS' || true)"
  NFAIL="$(cut -f1 "$REPORT" | grep -c '^FAIL' || true)"
else
# Sequential path — deliberately left unindented so that its diff against the
# pre-parallel harness is exactly this line and the closing `fi`. Nothing about
# default-mode behaviour changes.
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
fi

# The report holds one line per selected file and nothing else. A count that
# disagrees with the selection means something other than this run wrote to it:
# on 2026-07-31 two concurrent --full runs each appended their 2,983 lines to
# one report, and the comparison scored the resulting doubling as 2,983
# classification changes against an untouched baseline. That is a harness
# event, and no report or baseline may absorb it — the same rule the wall-clock
# guard already follows. The lock above prevents this cause; this check refuses
# the shape whatever the cause.
NLINES="$(grep -c . "$REPORT" || true)"
if [ "$NLINES" -ne "$TOTAL" ]; then
  echo "HARNESS ERROR — $TIER: $REPORT holds $NLINES line(s) for a $TOTAL-file selection; it was not written by this run alone. No classification comparison was performed."
  exit 1
fi

SUMMARY="$NPASS PASS, $NFAIL FAIL"
# Mark parallel verdicts so a report is never mistaken for one whose TIME column
# carries authority.
if [ "$JOBS" -gt 1 ]; then
  SUMMARY="$SUMMARY; --jobs $JOBS, timings reference-only"
fi

# Target gates: fixed all-PASS end condition, no baseline, no rebase.
if [ "$IS_TARGET" -eq 1 ]; then
  if [ "$NFAIL" -eq 0 ]; then
    echo "OK — $TIER: $NPASS/$TOTAL PASS ($SUMMARY)"
    exit 0
  fi
  echo "RED — $TIER: $NPASS/$TOTAL PASS, target not met ($SUMMARY); see $REPORT"
  exit 1
fi

# Portable classification comparison and host-local timing state are handled
# together by the tested helper so a write path cannot accidentally put wall
# time back into the tracked correctness baseline.
HELPER_ARGS=""
if [ "$REBASE" -eq 1 ]; then HELPER_ARGS="--rebase"; fi
if [ "$REFRESH" -eq 1 ]; then HELPER_ARGS="--refresh-times"; fi
python3 "$BASELINE_HELPER" evaluate \
  --tier "$TIER" --report "$REPORT" --baseline "$BASELINE" \
  --timings "$TIMING_BASELINE" --total "$TOTAL" --npass "$NPASS" \
  --nfail "$NFAIL" --jobs "$JOBS" --summary "$SUMMARY" $HELPER_ARGS
exit $?
