#!/usr/bin/env bash
# Strict all-PASS harness for the generated fixture manifests.
# Future suite names are recognised explicitly and refused until their protocol
# step activates them. This is intentionally not a permissive selector.
#
# --lane selects the corpus. `mainnet` (the default) is the current-mainnet
# release and every suite over it runs. `amsterdam` is the Glamsterdam devnet-8
# prerelease, whose fixtures target a fork `Fork.rules?` answers `none` for:
# its four suite names are recognised here and every one of them is refused,
# naming the goal that owns the semantics they would need. A refusal is the
# point, not a gap -- the alternative is a suite that reports failures about a
# fork this build has never claimed to run.
#
# The two lanes' suite namespaces are disjoint by construction (the devnet
# lane's derived suites are `amsterdam-` prefixed), so a suite name is never
# ambiguous and a mistyped --lane cannot silently select the other corpus.
#
# --jobs <n>|auto runs <n> fixtures concurrently; sequential (the default) is
# unchanged. The two modes differ in one deliberate way: sequential stops at the
# first non-PASS fixture, while parallel runs the whole selection and reports
# every failure. Stopping early saves little once the suite is parallel, and the
# complete failure list is the more useful artifact. Parallel mode also writes
# scripts/report-mainnet-<suite>.txt; sequential keeps its progress-only output.
#
# `--start-at N` selects manifest entries at or after position N in both modes.
# It is a selection over the manifest, applied before any dispatch ordering —
# never a claim about the order in which the selected entries then run.
#
# One run at a time: the osaka/prague/full suites and every parallel run take
# the shared heavy-gate lock, and a parallel run also locks its report file. A
# second run that would contend is REFUSED immediately rather than queued, and
# exits 2 — it did not fail, it did not run. See scripts/gate-lock.sh.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/jaune"

# Captured before the argument loop consumes them; the lock records the whole
# command line so a refusal can name what is holding it.
GATE_CMDLINE="$0 $*"
. "$SCRIPT_DIR/gate-lock.sh"

# One cleanup function, one EXIT trap, installed once. This script previously
# installed four EXIT traps, each silently replacing the last as the selection
# narrowed; every scratch path now lives here instead, and the variables are
# initialised so the trap is safe from the first line onwards.
LIST=""
SELECTED=""
WORK=""
cleanup() {
  gate_lock_release_all
  if [ -n "$LIST" ]; then rm -f "$LIST"; fi
  if [ -n "$SELECTED" ]; then rm -f "$SELECTED"; fi
  if [ -n "$WORK" ]; then rm -rf "$WORK"; fi
  return 0
}
trap cleanup EXIT

LANE="mainnet"
FIXTURES_ROOT=""
SUITE=""
SUBDIR=""
BUILD=1
START_AT=1
JOBS=1

usage() {
  echo "usage: scripts/check-mainnet.sh [--lane (mainnet|amsterdam)] (--suite SUITE | --dir REL --suite SUITE) [--fixtures-root PATH] [--no-build] [--start-at N] [--jobs <n>|auto]" >&2
  echo "  --lane mainnet   suites: prague osaka transitions smoke full" >&2
  echo "  --lane amsterdam suites: amsterdam amsterdam-transitions amsterdam-smoke amsterdam-full (all refused)" >&2
  exit 2
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --lane) shift; [ "$#" -gt 0 ] || usage; LANE="$1" ;;
    --suite) shift; [ "$#" -gt 0 ] || usage; SUITE="$1" ;;
    --dir) shift; [ "$#" -gt 0 ] || usage; SUBDIR="$1" ;;
    --fixtures-root) shift; [ "$#" -gt 0 ] || usage; FIXTURES_ROOT="$1" ;;
    --no-build) BUILD=0 ;;
    --start-at) shift; [ "$#" -gt 0 ] || usage; START_AT="$1" ;;
    --jobs) shift; [ "$#" -gt 0 ] || usage; JOBS="$1" ;;
    *) echo "error: unknown argument $1" >&2; usage ;;
  esac
  shift
done
[ -n "$SUITE" ] || usage

case "$LANE" in
  mainnet)
    LANE_ROOT_DEFAULT="${EEST_MAINNET_ROOT:-$HOME/eest-mainnet-v20.0.1}/fixtures"
    LANE_BOOTSTRAP="python3 scripts/bootstrap_mainnet.py"
    LANE_ROOT_ENV="EEST_MAINNET_ROOT"
    LANE_NAME="current-mainnet" ;;
  amsterdam)
    LANE_ROOT_DEFAULT="${EEST_AMSTERDAM_ROOT:-$HOME/eest-glamsterdam-devnet-v8.1.3}/fixtures"
    LANE_BOOTSTRAP="python3 scripts/bootstrap_mainnet.py --lane amsterdam"
    LANE_ROOT_ENV="EEST_AMSTERDAM_ROOT"
    LANE_NAME="glamsterdam-devnet" ;;
  *) echo "error: unknown lane $LANE; expected mainnet or amsterdam" >&2; exit 2 ;;
esac
[ -n "$FIXTURES_ROOT" ] || FIXTURES_ROOT="$LANE_ROOT_DEFAULT"

# The devnet lane's suites are recognised and refused, one message per suite,
# naming the goal that owns the semantics each would need. The refusal fires
# before the fixture root is looked at, so it is the same answer on a host that
# has never installed the corpus as on one that has: whether the archive is
# present is not what makes this lane unrunnable.
amsterdam_refusal() { # <suite> <owning goal> <what it would need>
  echo "error: suite $1 is installed but refused: this build declares Fork.amsterdam and Fork.rules? answers none for it, so no Amsterdam fixture can be run or judged." >&2
  echo "       Activating it belongs to $2, which implements $3." >&2
  echo "       The lane is inventoried, not exercised: see scripts/amsterdam/manifests.json for its exact contents." >&2
  exit 2
}

AMSTERDAM_BLOCK_GOAL="goal jaune-amsterdam-block-v1"
AMSTERDAM_CURRENCY_GOAL="goal jaune-amsterdam-currency-v1"

if [ "$LANE" = "amsterdam" ]; then
  if [ -n "$SUBDIR" ]; then
    echo "error: --dir is refused on --lane amsterdam: a subtree of a corpus this build cannot run is still a corpus this build cannot run." >&2
    echo "       Per-subtree landing is $AMSTERDAM_BLOCK_GOAL's instrument, and it becomes available when that goal activates the suite." >&2
    exit 2
  fi
  case "$SUITE" in
    amsterdam)
      amsterdam_refusal "$SUITE" "$AMSTERDAM_BLOCK_GOAL" \
        "the two-dimensional gas meter, the block-level access list, and the four new opcodes" ;;
    amsterdam-smoke)
      amsterdam_refusal "$SUITE" "$AMSTERDAM_BLOCK_GOAL" \
        "the two-dimensional gas meter, the block-level access list, and the four new opcodes" ;;
    amsterdam-full)
      amsterdam_refusal "$SUITE" "$AMSTERDAM_BLOCK_GOAL" \
        "the two-dimensional gas meter, the block-level access list, and the four new opcodes" ;;
    amsterdam-transitions)
      amsterdam_refusal "$SUITE" "$AMSTERDAM_CURRENCY_GOAL" \
        "the BPO2-to-Amsterdam transition lane on top of that metering core" ;;
    prague|osaka|transitions|smoke|full)
      echo "error: suite $SUITE is a --lane mainnet suite; the devnet lane's suites are amsterdam, amsterdam-transitions, amsterdam-smoke, amsterdam-full" >&2
      exit 2 ;;
    *) echo "error: unknown suite $SUITE for lane amsterdam" >&2; exit 2 ;;
  esac
fi

if [ "$JOBS" = "auto" ]; then
  if ! JOBS="$(python3 "$SCRIPT_DIR/fixture_jobs.py" --explain)"; then
    echo "error: could not resolve resource-aware automatic job count" >&2
    exit 2
  fi
fi
case "$JOBS" in
  ''|*[!0-9]*) echo "error: --jobs takes a positive integer or 'auto', not $JOBS" >&2; exit 2 ;;
esac
[ "$JOBS" -ge 1 ] || { echo "error: --jobs must be at least 1" >&2; exit 2; }

# Workers contend, so the guard rises in parallel mode. It stays a hang
# detector in both, never a performance budget; an explicit JAUNE_TIMEOUT wins.
if [ "$JOBS" -gt 1 ]; then
  GUARD="${JAUNE_TIMEOUT:-2000}"
else
  GUARD="${JAUNE_TIMEOUT:-1800}"
fi
[ "$START_AT" -ge 1 ] 2>/dev/null || {
  echo "error: --start-at must be a positive manifest index" >&2; exit 2;
}

# The pinned release publishes no fixture whose `network` is a bare `BPO1` or
# `BPO2`: every BPO case in it is a transition case, and those are the
# `transitions` suite.  Refusing the two static BPO suites is therefore not a
# step that has yet to happen -- it is the archive's shape.  Reporting an
# all-PASS verdict over zero selected files would be exactly the permissive
# oracle this harness exists to prevent.
lane_mismatch() {
  echo "error: suite $1 is a --lane amsterdam suite and this run is on --lane $LANE" >&2
  echo "       Run it as: scripts/check-mainnet.sh --lane amsterdam --suite $1 (which refuses it, by design)" >&2
  exit 2
}

bpo_refusal() {
  LABEL="$(printf '%s' "$1" | tr '[:lower:]' '[:upper:]')"
  echo "error: suite $1 selects no file: the pinned release publishes no fixture whose network is $LABEL." >&2
  echo "       $LABEL rules are exercised by --suite transitions (OsakaToBPO1AtTime15k, BPO1ToBPO2AtTime15k)." >&2
  exit 2
}

# `--dir` restricts a suite to one subtree of the pinned archive.  It is a
# targeted instrument for landing one semantic change at a time: the entries
# still come from the generated manifest, every one of them still has to PASS,
# and an empty or unlisted selection is an error.
if [ -n "$SUBDIR" ]; then
  case "$SUITE" in
    prague|smoke|osaka|transitions) ;;
    bpo1|bpo2) bpo_refusal "$SUITE" ;;
    amsterdam|amsterdam-*) lane_mismatch "$SUITE" ;;
    full)
      echo "error: suite full has no per-directory form; name the component suite" >&2
      exit 2 ;;
    *) echo "error: unknown suite $SUITE" >&2; exit 2 ;;
  esac
  case "$SUBDIR" in
    /*|*..*) echo "error: --dir must be a relative path inside blockchain_tests" >&2; exit 2 ;;
  esac
else
  case "$SUITE" in
    prague|osaka|transitions|smoke|full) ;;
    bpo1|bpo2) bpo_refusal "$SUITE" ;;
    amsterdam|amsterdam-*) lane_mismatch "$SUITE" ;;
    *) echo "error: unknown suite $SUITE" >&2; exit 2 ;;
  esac
fi

# The corpus is provisioned separately and is not in the repository, so on a
# fresh clone this is the first thing that fires. The missing path alone is only
# actionable to someone who already knows the bootstrap exists, so name the
# command that creates it and the two ways to point at an existing copy.
[ -d "$FIXTURES_ROOT/blockchain_tests" ] || {
  echo "error: $LANE_NAME blockchain fixture root not found: $FIXTURES_ROOT/blockchain_tests" >&2
  echo "  the corpus is provisioned separately; install it with:" >&2
  echo "    $LANE_BOOTSTRAP" >&2
  echo "  then re-run. Use --fixtures-root PATH or $LANE_ROOT_ENV for an existing copy" >&2
  echo "  elsewhere. Provenance, disk and runtime: scripts/vectors/SOURCES.md" >&2
  exit 2
}
[ "$GUARD" -gt 0 ] 2>/dev/null || { echo "error: JAUNE_TIMEOUT must be positive" >&2; exit 2; }

# The heavy-gate lock, taken before the build so a refusal costs nothing and two
# runs cannot contend over `lake build` either. The suites that hold it are the
# catalogue's Long rows plus any run dispatching a worker pool; smoke and
# transitions stay outside it, so the cheap suites you run while iterating are
# never hostage to a long one. See scripts/gate-lock.sh.
case "$SUITE" in
  osaka|prague|full) HEAVY=1 ;;
  *)                 HEAVY=0 ;;
esac
if [ "$JOBS" -gt 1 ]; then HEAVY=1; fi
if [ "$HEAVY" -eq 1 ]; then
  gate_lock_heavy_acquire "$SUITE" \
    "the heavy-gate lock" \
    "wait for that run to finish; --suite smoke and --suite transitions do not take this lock when sequential" \
    || exit 2
fi

if [ "$BUILD" -eq 1 ]; then
  (cd "$ROOT" && lake build jaune)
fi
[ -x "$BIN" ] || { echo "error: jaune binary not found: $BIN" >&2; exit 2; }

LIST="$(mktemp)"
python3 "$SCRIPT_DIR/gen_mainnet_manifest.py" --lane "$LANE" \
  --fixtures-root "$FIXTURES_ROOT" --check --emit-suite "$SUITE" > "$LIST"
[ -s "$LIST" ] || { echo "error: zero selected manifest entries for $SUITE" >&2; exit 2; }

if [ -n "$SUBDIR" ]; then
  [ -d "$FIXTURES_ROOT/blockchain_tests/$SUBDIR" ] || {
    echo "error: --dir subtree not found: blockchain_tests/$SUBDIR" >&2; exit 2;
  }
  SELECTED="$(mktemp)"
  grep -E "^${SUBDIR%/}/" "$LIST" > "$SELECTED" || true
  [ -s "$SELECTED" ] || {
    echo "error: zero $SUITE manifest entries under blockchain_tests/$SUBDIR" >&2
    exit 2
  }
  # An unlisted .json inside the subtree means the subtree mixes fork labels or
  # the manifest is stale; either way it must not be skipped silently.
  ON_DISK="$(find "$FIXTURES_ROOT/blockchain_tests/${SUBDIR%/}" -name '*.json' | wc -l | tr -d ' ')"
  IN_MANIFEST="$(wc -l < "$SELECTED" | tr -d ' ')"
  [ "$ON_DISK" -eq "$IN_MANIFEST" ] || {
    echo "error: blockchain_tests/$SUBDIR holds $ON_DISK fixture files but the $SUITE manifest lists $IN_MANIFEST" >&2
    exit 2
  }
  mv "$SELECTED" "$LIST"
  SELECTED=""
  SUITE="$SUITE:$SUBDIR"
fi

# The report path is settled once the suite name is — the --dir form appends its
# subtree to that name — so resolve it here and lock it before anything is
# dispatched. Only the parallel path writes a report; the sequential path
# streams progress and writes none, so only it needs the lock.
REPORT="$SCRIPT_DIR/report-mainnet-$(printf '%s' "$SUITE" | tr '/:' '__').txt"
if [ "$JOBS" -gt 1 ]; then
  gate_lock_acquire "$REPORT.lock" "$SUITE" "$REPORT" \
    "wait for that run to finish" \
    || exit 2
fi

TOTAL="$(wc -l < "$LIST" | tr -d ' ')"
[ "$START_AT" -le "$TOTAL" ] || {
  echo "error: --start-at $START_AT exceeds $SUITE manifest size $TOTAL" >&2; exit 2;
}
PASS=$((START_AT - 1))
START_ALL="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"

if [ "$JOBS" -gt 1 ]; then
  RUNNER="$SCRIPT_DIR/run-fixture.sh"
  [ -x "$RUNNER" ] || {
    echo "error: parallel runner not found or not executable: $RUNNER" >&2; exit 2;
  }
  WORK="$(mktemp -d)"
  LINES="$WORK/lines"
  mkdir -p "$LINES"

  # Validate the whole selection up front rather than per-iteration. The
  # sequential path can afford to check as it goes because it stops at the first
  # problem; a pool cannot, and a malformed entry or missing file is a harness
  # error that must never be reachable as a fixture classification.
  tail -n +"$START_AT" "$LIST" \
    | awk -F'\t' -v root="$FIXTURES_ROOT/blockchain_tests" -v start="$START_AT" '
        {
          if (NF != 2 || $1 == "" || $2 == "") {
            printf "error: malformed generated manifest entry at line %d\n", FNR > "/dev/stderr"; bad = 1; exit 1
          }
          n = $2
          if (n != "Prague" && n != "Osaka" && n != "BPO1" && n != "BPO2" &&
              n != "PragueToOsakaAtTime15k" && n != "OsakaToBPO1AtTime15k" &&
              n != "BPO1ToBPO2AtTime15k") {
            printf "error: unknown manifest network %s\n", n > "/dev/stderr"; bad = 1; exit 1
          }
          printf "%d %s %s\n", FNR + start - 1, $1, n
        }
        END { if (bad) exit 1 }' > "$WORK/dispatch" || exit 2

  while read -r _IDX REL _NET; do
    [ -f "$FIXTURES_ROOT/blockchain_tests/$REL" ] || {
      echo "error: missing manifest fixture file: $FIXTURES_ROOT/blockchain_tests/$REL" >&2
      exit 2
    }
  done < "$WORK/dispatch"

  SELECTED_N="$(wc -l < "$WORK/dispatch" | tr -d ' ')"
  echo "dispatching $SELECTED_N of $TOTAL manifest files across $JOBS workers (guard ${GUARD}s)" >&2

  RF_BIN="$BIN"; RF_GUARD="$GUARD"; RF_OUT="$LINES"
  RF_FIX="$FIXTURES_ROOT/blockchain_tests"
  export RF_BIN RF_GUARD RF_OUT RF_FIX
  set +e
  xargs -P "$JOBS" -I{} bash -c '
    set -- $1
    exec "$0" "$RF_BIN" "$RF_GUARD" "$RF_OUT" "$1" "$RF_FIX/$2" "$3" "$2"
  ' "$RUNNER" {} < "$WORK/dispatch"
  set -e

  if [ -f "$LINES/.guard-tripped" ]; then
    TRIPPED="$(cut -f1 "$LINES/.guard-tripped")"
    echo "HARNESS ERROR — $TRIPPED exceeded ${GUARD}s; no classification was recorded" >&2
    exit 1
  fi

  : > "$REPORT"
  MISSING=0
  while read -r IDX REL _NET; do
    if [ -f "$LINES/$IDX.line" ]; then
      cat "$LINES/$IDX.line" >> "$REPORT"
    else
      MISSING=$((MISSING + 1))
      echo "MISSING — no classification recorded for $REL" >&2
    fi
  done < "$WORK/dispatch"
  if [ "$MISSING" -ne 0 ]; then
    echo "HARNESS ERROR — $SUITE: $MISSING/$SELECTED_N files produced no classification; see $REPORT"
    exit 1
  fi

  END_ALL="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"
  ELAPSED="$(perl -e 'printf "%.2f", $ARGV[1] - $ARGV[0]' "$START_ALL" "$END_ALL")"
  NFAIL="$(cut -f1 "$REPORT" | grep -c '^FAIL' || true)"
  if [ "$NFAIL" -ne 0 ]; then
    grep '^FAIL' "$REPORT" | cut -f3 | while IFS= read -r F; do
      echo "RED — $SUITE: non-PASS fixture $F"
    done
    echo "RED — $SUITE: $NFAIL of $SELECTED_N manifest files non-PASS in ${ELAPSED}s (--jobs $JOBS, timings reference-only); see $REPORT"
    exit 1
  fi
  # Name the skip rather than folding it into the numerator. The sequential path
  # seeds PASS with START_AT-1 and so reports every skipped entry as passing;
  # counting files that never ran as PASS is the permissive oracle this harness
  # exists to prevent, so parallel mode reports only what it actually verified.
  if [ "$START_AT" -gt 1 ]; then
    echo "OK — $SUITE: $SELECTED_N/$SELECTED_N selected manifest files PASS in ${ELAPSED}s (entries $START_AT-$TOTAL; $((START_AT - 1)) skipped by --start-at and NOT verified) (--jobs $JOBS, timings reference-only)"
  else
    echo "OK — $SUITE: $SELECTED_N/$TOTAL manifest files PASS in ${ELAPSED}s (--jobs $JOBS, timings reference-only)"
  fi
  exit 0
fi

while IFS=$'\t' read -r REL NETWORK; do
  [ -n "$REL" ] && [ -n "$NETWORK" ] || {
    echo "error: malformed generated manifest entry" >&2; exit 2;
  }
  # The static forks and the transition labels whose endpoints are both
  # supported.  A label this list does not name must never reach the binary:
  # the binary would refuse it, but the manifest is what is meant to be exact.
  case "$NETWORK" in
    Prague|Osaka|BPO1|BPO2) ;;
    PragueToOsakaAtTime15k|OsakaToBPO1AtTime15k|BPO1ToBPO2AtTime15k) ;;
    *) echo "error: unknown manifest network $NETWORK" >&2; exit 2;;
  esac
  FILE="$FIXTURES_ROOT/blockchain_tests/$REL"
  [ -f "$FILE" ] || { echo "error: missing manifest fixture file: $FILE" >&2; exit 2; }
  set +e
  perl -e '
    my $t = shift @ARGV;
    my $pid = fork(); die "fork failed: $!" unless defined $pid;
    if (!$pid) { exec @ARGV; exit 127 }
    $SIG{ALRM} = sub { kill "KILL", $pid; waitpid($pid, 0); exit 142 };
    alarm $t; waitpid($pid, 0); alarm 0;
    my $st = $?; exit($st & 127 ? 128 + ($st & 127) : $st >> 8);
  ' "$GUARD" "$BIN" "$FILE" --network "$NETWORK" > /dev/null 2>&1
  RC=$?
  set -e
  if [ "$RC" -eq 142 ]; then
    echo "HARNESS ERROR — $REL exceeded ${GUARD}s; no classification was recorded" >&2
    exit 1
  fi
  if [ "$RC" -ne 0 ]; then
    echo "RED — $SUITE: non-PASS fixture $REL (network $NETWORK, exit $RC)" >&2
    exit 1
  fi
  PASS=$((PASS + 1))
  printf '[%d/%d] PASS %s\n' "$PASS" "$TOTAL" "$REL" >&2
done < <(tail -n +"$START_AT" "$LIST")
END_ALL="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"
ELAPSED="$(perl -e 'printf "%.2f", $ARGV[1] - $ARGV[0]' "$START_ALL" "$END_ALL")"
echo "OK — $SUITE: $PASS/$TOTAL manifest files PASS in ${ELAPSED}s"
