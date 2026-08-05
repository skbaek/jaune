#!/usr/bin/env bash
# Internal helper: run exactly one fixture under the wall-clock guard and
# record its classification. Used only by the parallel dispatch path of
# check-legacy.sh and check-mainnet.sh — both sequential paths keep their own inline
# runner so that default-mode behaviour stays byte-identical.
#
# usage: run-fixture.sh <bin> <guard> <outdir> <idx> <file> <network> <label>
#
# Writes `STATUS<TAB>TIME<TAB>label` to <outdir>/<idx>.line. Numbering the
# output by the caller's report index — not by completion order — is what lets
# the caller reassemble a report identical in order to a sequential run.
#
# Exit 0 for both PASS and FAIL: they are classifications, not harness events.
# Exit 255 on a guard trip, which makes xargs abort the whole pool immediately
# (BSD and GNU xargs both treat 255 as "stop now"). A guard trip also drops a
# sentinel so the caller can distinguish it from any other nonzero exit.
set -u

BIN="$1"; GUARD="$2"; OUTDIR="$3"; IDX="$4"; FILE="$5"; NETWORK="$6"; LABEL="$7"

START="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"
# Same guard runner as the sequential paths: fork the binary, alarm the parent,
# SIGKILL the child on trip and exit 142 *normally* so bash prints no "Alarm
# clock" notice. A child killed by the guard reports 128+9 = 137, so it can
# never be confused with the 142 the guard itself returns.
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
' "$GUARD" "$BIN" "$FILE" --network "$NETWORK" > /dev/null 2>&1
RC=$?
ELAPSED="$(perl -e 'printf "%.2f", $ARGV[1] - $ARGV[0]' \
  "$START" "$(perl -MTime::HiRes=time -e 'printf "%.3f", time')")"

if [ "$RC" -eq 142 ]; then
  printf '%s\t%ss\n' "$LABEL" "$ELAPSED" > "$OUTDIR/.guard-tripped"
  printf 'HARNESS ERROR — %s exceeded the %ss guard after %ss; no fixture legitimately runs this long — investigate before rerunning\n' \
    "$LABEL" "$GUARD" "$ELAPSED" >&2
  exit 255
fi

if [ "$RC" -eq 0 ]; then
  CLS=PASS
else
  CLS=FAIL
fi
printf '%s\t%ss\t%s\n' "$CLS" "$ELAPSED" "$LABEL" > "$OUTDIR/$IDX.line"
printf '%s %ss %s\n' "$CLS" "$ELAPSED" "$LABEL" >&2
exit 0
