#!/usr/bin/env bash
# Exclusive gate locks, shared by the report-writing harnesses.
#
# Source this file; it defines functions and never runs anything on its own.
#
# WHY
#
# On 2026-07-31 two `scripts/check.sh --full` runs overlapped. Both truncated
# scripts/report-full.txt at start and both then appended their 2,983 per-file
# lines to it, leaving a 5,966-line report holding every path exactly twice.
# The comparison's lookup table is destructive, so each path's second
# occurrence found nothing and scored `MISSING -> <status>`: the harness
# reported 2,983 classification changes against a baseline nobody had touched,
# and a session HALTed on it. Both runs were in fact green.
#
# The two runs also summed ~8,400s of fixture time against a ~1,146s
# sequential baseline — roughly thirty workers on ten cores. Contention alone
# is reason enough to refuse: even had the reports not collided, the timings
# would have been worthless and both runs needlessly slow.
#
# WHAT THIS DOES
#
# A run takes an exclusive lock and a second run that would contend is
# REFUSED — immediately, with the holder named. It does not queue, does not
# wait, does not fall back to a different path, and does not run. Rejection is
# the contract: two gate runs on one host is the thing being prevented, not a
# scheduling problem to be smoothed over.
#
# WHY mkdir
#
# `flock(1)` does not exist on macOS, which is the same reason check.sh guards
# fixtures with a perl alarm rather than timeout(1). `mkdir` is atomic on every
# filesystem in play, needs no helper binary, and works identically on the CI
# runners. Only mkdir, kill -0, ps and trap are used.
#
# STALE LOCKS
#
# A run killed with SIGKILL leaves its lock directory behind, so a lock whose
# recorded PID is no longer running is reclaimed — and the reclaim is
# announced, never silent. A guard that cleans up quietly stops being evidence.
# There is deliberately no timeout-based reclaim: a legitimate --full run holds
# its lock for minutes, so any duration threshold either breaks that or fails
# to help.
#
# USE
#
#   GATE_CMDLINE="$0 $*"                     # before the argument loop eats them
#   . "$SCRIPT_DIR/gate-lock.sh"
#   gate_lock_acquire "$LOCKDIR" "$TIER" "$WHAT" "$HINT" || exit 2
#   ...
#   cleanup() { gate_lock_release_all; rm -rf "$WORK"; }
#   trap cleanup EXIT
#
# Install exactly one EXIT trap per script: a second `trap ... EXIT` silently
# replaces the first, and that is how the scratch-directory removals these
# harnesses already depend on would be lost.

# Lock directories held by this process, space separated. Paths must not
# contain whitespace; every caller here builds them from its own script
# directory or from a --report path.
GATE_LOCKS=""

# gate_lock_acquire <lockdir> <label> <what> [hint]
#
#   lockdir  directory to create, e.g. scripts/report-full.txt.lock
#   label    short name for the verdict lines, e.g. "full"
#   what     what is being protected, named as the operator sees it
#   hint     optional escape-hatch sentence for the refusal message
#
# Returns 0 holding the lock, or 1 having printed a REFUSED verdict. Callers
# exit 2 on a refusal: the gate did not fail, it did not run.
gate_lock_acquire() {
  gl_dir="$1"
  gl_label="$2"
  gl_what="$3"
  gl_hint="${4:-}"
  gl_reclaimed=0

  while : ; do
    if mkdir "$gl_dir" 2>/dev/null; then
      printf '%s\n%s\n%s\n' \
        "$$" "$(date '+%F %T')" "${GATE_CMDLINE:-unknown command}" \
        > "$gl_dir/owner"
      GATE_LOCKS="$GATE_LOCKS $gl_dir"
      return 0
    fi

    # Held. The holder stamps its metadata immediately after creating the
    # directory, but not atomically with it, so allow one second for that
    # write before concluding the lock has no owner.
    if [ ! -s "$gl_dir/owner" ]; then
      sleep 1
    fi
    if [ ! -s "$gl_dir/owner" ]; then
      echo "REFUSED — $gl_label: $gl_what is locked by $gl_dir, which carries no owner metadata"
      echo "REFUSED — $gl_label: a run may have died between creating and stamping it; if no gate is running, remove that directory by hand"
      echo "REFUSED — $gl_label: nothing was run and nothing was written"
      return 1
    fi

    gl_pid="$(awk 'NR == 1' "$gl_dir/owner")"
    gl_when="$(awk 'NR == 2' "$gl_dir/owner")"
    gl_cmd="$(awk 'NR == 3' "$gl_dir/owner")"

    # kill -0 fails with EPERM for a live process owned by someone else, so a
    # ps lookup backs it up. Refusing a lock whose holder is alive is the safe
    # direction; reclaiming one that is still running is not.
    if [ -n "$gl_pid" ] && { kill -0 "$gl_pid" 2>/dev/null || ps -p "$gl_pid" >/dev/null 2>&1; }; then
      echo "REFUSED — $gl_label: $gl_what is locked by PID $gl_pid, started $gl_when"
      echo "REFUSED — $gl_label: holder: $gl_cmd"
      if [ -n "$gl_hint" ]; then echo "REFUSED — $gl_label: $gl_hint"; fi
      echo "REFUSED — $gl_label: nothing was run and nothing was written"
      return 1
    fi

    # Stale. Reclaim once; a second failure means someone else won the race
    # for it, and that someone is now a live holder.
    if [ "$gl_reclaimed" -ne 0 ]; then
      echo "REFUSED — $gl_label: $gl_what is locked by $gl_dir and could not be reclaimed"
      echo "REFUSED — $gl_label: nothing was run and nothing was written"
      return 1
    fi
    gl_reclaimed=1
    echo "RECLAIMED — $gl_label: stale lock $gl_dir left by PID $gl_pid ($gl_cmd, started $gl_when); that process is no longer running"
    rm -f "$gl_dir/owner"
    rmdir "$gl_dir" 2>/dev/null || true
  done
}

# Release every lock this process holds. Idempotent, and safe to call from an
# EXIT trap that also runs on the refusal path, where nothing was acquired.
gate_lock_release_all() {
  for gl_held in $GATE_LOCKS; do
    rm -f "$gl_held/owner"
    rmdir "$gl_held" 2>/dev/null || true
  done
  GATE_LOCKS=""
}
