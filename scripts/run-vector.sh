#!/usr/bin/env bash
# Internal helper: run exactly one vector file and record the report chunk it
# contributes. Used only by the parallel dispatch path of check-vectors.sh; the
# sequential path keeps its own inline runner so that default-mode behaviour
# stays byte-identical.
#
# usage: run-vector.sh <bin> <guard> <outdir> <idx> <path> <addr> <fork> <group> <label>
#
# Writes the file's whole contribution to the report — its `Running ...` banner,
# the runner's own stdout, and the trailing MATRIX line — to <outdir>/<idx>.out.
# A vector file contributes many lines, not one classification line, so the unit
# reassembled by the caller is this chunk. Numbering it by the caller's report
# index rather than by completion order is what lets the caller rebuild a report
# ordered exactly as a sequential run would have produced it.
#
# The chunk is assembled under a .part name and moved into place only once the
# classification is known: a partially written chunk must never be reachable as
# a classification, and `mv` within one directory is atomic.
#
# Exit 0 for both OK and RED: they are classifications, not harness events.
# Exit 255 on a guard trip, which makes xargs abort the whole pool immediately
# (BSD and GNU xargs both treat 255 as "stop now"). A guard trip also drops a
# sentinel so the caller can distinguish it from any other nonzero exit.
set -u

BIN="$1"; GUARD="$2"; OUTDIR="$3"; IDX="$4"; FILE="$5"
ADDR="$6"; FORK="$7"; GROUP="$8"; LABEL="$9"

PART="$OUTDIR/$IDX.part"
printf 'Running %s at address %s under %s\n' "$LABEL" "$ADDR" "$FORK" > "$PART"

START="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"
# Guard runner (macOS has no coreutils timeout): fork the binary, alarm the
# parent, SIGKILL the child on trip and exit 142 *normally* so bash prints no
# "Alarm clock" notice. A child killed by the guard reports 128+9 = 137, so it
# can never be confused with the 142 the guard itself returns. Only stdout is
# captured into the chunk, matching what the sequential path tees; stderr stays
# on the terminal.
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
' "$GUARD" "$BIN" --vectors "$ADDR" "$FILE" --network "$FORK" >> "$PART"
RC=$?
ELAPSED="$(perl -e 'printf "%.2f", $ARGV[1] - $ARGV[0]' \
  "$START" "$(perl -MTime::HiRes=time -e 'printf "%.3f", time')")"

if [ "$RC" -eq 142 ]; then
  rm -f "$PART"
  printf '%s\t%ss\n' "$LABEL" "$ELAPSED" > "$OUTDIR/.guard-tripped"
  printf 'HARNESS ERROR — %s exceeded the %ss guard after %ss; no vector file legitimately runs this long — investigate before rerunning\n' \
    "$LABEL" "$GUARD" "$ELAPSED" >&2
  exit 255
fi

if [ "$RC" -eq 0 ]; then
  VERDICT=OK
else
  VERDICT=RED
fi
printf 'MATRIX\t%s\t%s\t%s\n' "$GROUP" "$VERDICT" "$LABEL" >> "$PART"
mv "$PART" "$OUTDIR/$IDX.out"
printf '%s %ss %s\n' "$VERDICT" "$ELAPSED" "$LABEL" >&2
exit 0
