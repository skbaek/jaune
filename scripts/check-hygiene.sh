#!/usr/bin/env bash
# Source-hygiene gate for Jaune (CI lint tier).
#
# Fails if any forbidden pattern appears in the scanned source that is not
# recorded in the committed allowlist scripts/hygiene-allow.txt. The scanned
# source is every `*.lean` under Jaune/ plus the root-level MemoryProbe.lean,
# which is a tracked Lean executable built by the ordinary `lake build` and is
# therefore part of the surface this gate defends; it was outside the scan
# until the memory-closure repair brought it in. Forbidden patterns:
#
#   dbg_trace       stray debug tracing left on a code path
#   sorry           an incomplete proof / axiomatized hole
#   axiom           a proposition asserted rather than proved
#   opaque          a constant with no defining equation
#   @[extern]       a body supplied outside Lean
#   @[implemented_by]  ditto, by substitution at compile time
#   @[csimp]        a compiled-code substitution: the kernel keeps seeing the
#                   original definition while every compiled artifact runs the
#                   replacement, so this is the attribute that makes the binary
#                   differ from what was elaborated. It demands a kernel-checked
#                   equality proof, so it is not a hole in the trust surface —
#                   it is a fact about the trust surface that must be visible
#                   rather than silent, and every fixture gate measures the
#                   compiled binary
#   partial def     a definition whose termination is not established
#   unsafe          a declaration exempted from the kernel's checks
#   native_decide   a goal closed by running compiled code outside the kernel
#
# The first two are hygiene; the rest are the trust surface. TRUSTED.md
# describes Jaune as having no axiom, sorry, extern or native_decide in the
# protected path, and until this gate covered them that was a property of the
# source at a moment rather than a property CI defends. A claim that is only a
# fact can be lost by one commit; a claim that is a gate cannot be lost
# quietly. Every trust-surface pattern but one has no occurrence at all, and
# any first occurrence must be argued for in writing. The one exception is the
# single proved `@[csimp]` substitution, which carries a written allowlist row
# naming the equality it proves.
#
# The trust-surface patterns are anchored to declaration and attribute
# positions rather than matched as bare words, so prose that merely discusses
# an opaque scrutinee or an external binary does not trip the gate.
#
# Anchoring is not comment-awareness, and this gate deliberately does not try
# to be a Lean parser. Two prose shapes still trip it, both by design:
#
#   * a wrapped comment whose continuation line happens to begin with `axiom`
#     or `opaque` — reflow the comment (this is how the one occurrence under
#     Jaune/ was resolved, in Jaune/Hash.lean's `vec_eta` docstring);
#   * any comment containing `native_decide`, which cannot be anchored because
#     it is a tactic and legitimately appears mid-line after `by`.
#
# That direction is chosen on purpose. A false positive is a loud failure a
# human clears in seconds by rewording or by adding one justified allowlist
# entry; a false negative silently admits an axiom into the trusted path. For a
# gate whose whole job is the trust surface, fail loud. Prefer rewording the
# prose over adding an entry, so the allowlist stays empty and keeps meaning
# something.
#
# The gate is fail-closed: every currently-committed occurrence must be either
# removed from the source or listed in the allowlist with a written
# justification, and any NEW occurrence fails the gate. This needs no Lean
# toolchain, so CI runs it on a bare runner.
#
# Matching is line-number independent. Each occurrence is normalised to
#   <relpath> <source line, leading/trailing space trimmed, runs collapsed>
# and compared as a whole line against the allowlist. That survives edits above
# the line, but forces re-review if the matched text itself changes. Paths
# under Jaune/ contain no spaces, so the single-space join is unambiguous.
#
# Usage: scripts/check-hygiene.sh
#
# CLI contract: exit 0 iff no un-allowlisted occurrence exists; the last line
# of output is a single unambiguous verdict. Exit 1 on a violation, 2 on a
# usage or setup error. A stale allowlist entry (listed but no longer present
# in the source) is reported as a warning, never a failure.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
SRC_DIR="Jaune"
# Tracked Lean sources outside SRC_DIR that are nonetheless part of the scanned
# surface. MemoryProbe.lean is the bounded memory regression's executable: it is
# built by `lake build` and asserted by scripts/check-memory-probe.sh, so it is
# scanned here rather than left as the one Lean file nothing looks at.
EXTRA_SRC="MemoryProbe.lean"
SCAN_LABEL="$SRC_DIR/ + $EXTRA_SRC"
ALLOW="$SCRIPT_DIR/hygiene-allow.txt"

# Hygiene proper: unanchored, since these are never legitimate anywhere.
P_DEBUG='dbg_trace'
P_SORRY='\bsorry\b'

# Trust surface. Each is anchored to the position the construct actually
# occupies, so prose about an opaque scrutinee or an external binary is not a
# hit. `axiom` and `opaque` head a declaration, after any leading modifiers.
P_DECL='^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+|unsafe[[:space:]]+|scoped[[:space:]]+|local[[:space:]]+)*(axiom|opaque)[[:space:]]'
# `@[extern ...]` / `@[implemented_by ...]` supply a body from outside Lean.
P_ATTR='@\[[^]]*(extern|implemented_by)\b'
# `partial def` defines without establishing termination.
P_PARTIAL='^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+|unsafe[[:space:]]+)*partial[[:space:]]+def\b'
# `unsafe` heads a declaration exempted from the kernel's checks.
P_UNSAFE='^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)*unsafe[[:space:]]'
# `native_decide` closes a goal by running compiled code outside the kernel.
P_NATIVE='\bnative_decide\b'
# `@[csimp]` substitutes a different function into compiled code. Anchored to
# the attribute position for the same reason as @[extern]: prose about csimp
# lemmas must not trip the gate, an actual attribute must.
P_CSIMP='@\[[^]]*csimp\b'

PATTERN="$P_DEBUG|$P_SORRY|$P_DECL|$P_ATTR|$P_PARTIAL|$P_UNSAFE|$P_NATIVE|$P_CSIMP"
FORBIDDEN='{dbg_trace, sorry, axiom, opaque, @[extern], @[implemented_by], @[csimp], partial def, unsafe, native_decide}'

if [ $# -ne 0 ]; then
  echo "usage: scripts/check-hygiene.sh" >&2
  exit 2
fi
if [ ! -d "$ROOT/$SRC_DIR" ]; then
  echo "REGRESSION — hygiene: source tree not found: $ROOT/$SRC_DIR"
  exit 2
fi
for extra in $EXTRA_SRC; do
  if [ ! -f "$ROOT/$extra" ]; then
    echo "REGRESSION — hygiene: scanned source not found: $ROOT/$extra"
    exit 2
  fi
done

normalise() { sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//; s/[[:space:]]+/ /g'; }

# Current occurrences, normalised to "<relpath> <collapsed source line>".
HITS="$(cd "$ROOT" && grep -rEn "$PATTERN" "$SRC_DIR" --include='*.lean' $EXTRA_SRC 2>/dev/null \
  | awk '{
      path = $0; sub(/:[0-9]+:.*$/, "", path)
      line = $0; sub(/^[^:]+:[0-9]+:/, "", line)
      print path "\t" line
    }' \
  | awk -F'\t' '{
      c = $2
      gsub(/^[ \t]+|[ \t]+$/, "", c); gsub(/[ \t]+/, " ", c)
      print $1 " " c
    }' \
  | sort -u)"

# Allowlist data lines (drop comments / blanks), normalised identically so
# authoring is forgiving about incidental whitespace.
ALLOWED=""
if [ -f "$ALLOW" ]; then
  ALLOWED="$(grep -vE '^[[:space:]]*(#|$)' "$ALLOW" | normalise | sort -u)"
fi

VIOLATIONS="$(comm -23 <(printf '%s\n' "$HITS" | grep -v '^$' | sort -u) \
                        <(printf '%s\n' "$ALLOWED" | grep -v '^$' | sort -u))"
STALE="$(comm -13 <(printf '%s\n' "$HITS" | grep -v '^$' | sort -u) \
                   <(printf '%s\n' "$ALLOWED" | grep -v '^$' | sort -u))"

if [ -n "$STALE" ]; then
  printf '%s\n' "$STALE" | while IFS= read -r s; do
    [ -n "$s" ] && echo "WARNING — hygiene: stale allowlist entry no longer in source: $s"
  done
fi

NHITS="$(printf '%s\n' "$HITS" | grep -c .)"
if [ -n "$VIOLATIONS" ]; then
  printf '%s\n' "$VIOLATIONS" | while IFS= read -r v; do
    [ -n "$v" ] && echo "HYGIENE — un-allowlisted occurrence: $v"
  done
  NVIO="$(printf '%s\n' "$VIOLATIONS" | grep -c .)"
  echo "REGRESSION — hygiene: $NVIO forbidden occurrence(s) in $SCAN_LABEL not in $(basename "$ALLOW"); remove them or add a justified allowlist entry"
  exit 1
fi

echo "OK — hygiene: all $NHITS occurrence(s) of $FORBIDDEN in $SCAN_LABEL are allowlisted; no new ones"
exit 0
