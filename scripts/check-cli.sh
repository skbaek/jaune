#!/usr/bin/env bash
# CLI refusal gate for the fixture runner (cheap tier).
#
# `runTestFile` in Main.lean refuses a fixture file on four counts, and each
# refusal is a diagnostic a user reads before anything else:
#
#   1. the file holds cases from another EEST sibling tree (state_tests,
#      blockchain_tests_engine, blockchain_tests_engine_x, transaction_tests),
#      named by their `_info.fixture-format`;
#   2. the file holds no cases at all;
#   3. no case in it runs at a network this build supports;
#   4. the command line's filters select none of the cases that do.
#
# A fifth refusal joined them when `Fork.amsterdam` was declared: a case whose
# network label this build *parses* but whose rules it does not implement. It
# is a different refusal from rule 3 and must stay different -- `Cancun` is a
# label this build does not know, while `Amsterdam` is one it knows and
# deliberately cannot run -- so both are asserted here, on files that differ
# only in that label.
#
# Nothing else pinned them. The conformance tiers only ever run well-formed
# corpus files, `scripts/golden-messages.txt` covers block-rejection reasons
# observed *inside* a run, and the Python tests under `scripts/tests/` cover the
# bootstrap and generator scripts. So all four messages were verified by hand
# once and could rot silently. This gate is the falsifier: it builds synthetic
# fixtures in a temp dir, runs the built binary against each, and asserts both
# the nonzero exit and a substring of the message.
#
# Rule 1 is permissive by design — a case declaring no `fixture-format` at all
# is passed through, since the field is EEST's and a hand-written fixture may
# omit it. That half is checked as an A/B pair: two files identical but for the
# `_info` block, both of which must reach the per-case run. The undeclared one
# then fails on the synthetic fixture's absent block data, which is expected and
# deliberately not asserted — this gate pins the guard, not the runner beneath
# it.
#
# Usage: scripts/check-cli.sh
#
# CLI contract: exit 0 iff every check holds; the last line of output is a
# single unambiguous verdict. Exit 1 on a violation, 2 on a usage or setup
# error. This gate reads the built binary and never builds it — run `lake build`
# first, exactly as the `--no-build` tiers require.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/jaune"

if [ $# -ne 0 ]; then
  echo "usage: scripts/check-cli.sh" >&2
  exit 2
fi
if [ ! -x "$BIN" ]; then
  echo "REGRESSION — cli: jaune binary not found at $BIN; build the executable first"
  exit 2
fi

TMP="$(mktemp -d)" || { echo "REGRESSION — cli: could not create a temp dir"; exit 2; }
trap 'rm -rf "$TMP"' EXIT

CHECKS=0
FAILS=0

fail() {
  printf 'CLI — %s\n' "$1"
  FAILS=$((FAILS + 1))
}

detail() { printf '       %s\n' "$1"; }

has() { printf '%s\n' "$2" | grep -qF -- "$1"; }

# Run the binary, capturing stdout, stderr and exit status separately: the
# refusals go to stderr as uncaught exceptions, the progress lines to stdout.
run_jaune() {
  RUN_OUT="$("$BIN" "$@" 2>"$TMP/.stderr")"
  RUN_RC=$?
  RUN_ERR="$(cat "$TMP/.stderr")"
}

# Assert that the given argv is refused with exit 1 and a message containing
# <needle>. Leaves RUN_OUT/RUN_ERR in place for a follow-up assertion.
expect_refusal() { # <label> <needle> <argv...>
  label="$1"; needle="$2"; shift 2
  CHECKS=$((CHECKS + 1))
  run_jaune "$@"
  if [ "$RUN_RC" -ne 1 ]; then
    fail "$label: expected exit 1, got $RUN_RC"
    return
  fi
  if ! has "$needle" "$RUN_ERR"; then
    fail "$label: refusal message does not contain: $needle"
    detail "got: ${RUN_ERR:-<empty stderr>}"
  fi
}

expect_last_has() { # <label> <needle>
  CHECKS=$((CHECKS + 1))
  if ! has "$2" "$RUN_ERR"; then
    fail "$1: refusal message does not contain: $2"
    detail "got: ${RUN_ERR:-<empty stderr>}"
  fi
}

expect_last_lacks() { # <label> <needle>
  CHECKS=$((CHECKS + 1))
  if has "$2" "$RUN_ERR"; then
    fail "$1: refusal message unexpectedly contains: $2"
    detail "got: ${RUN_ERR:-<empty stderr>}"
  fi
}

# ---------------------------------------------------------------- fixtures --
#
# Case keys and `fixture-format` values are the ones EEST actually writes. Only
# the fields a guard reads are filled in: every one of these files is refused,
# or refused-adjacent, before the runner reads a block.

mkdir -p "$TMP/state_tests/nested" "$TMP/loose"

cat > "$TMP/state_tests/nested/dup.json" <<'EOF'
{
  "tests/frontier/opcodes/test_dup.py::test_dup[fork_Prague-state_test]": {
    "network": "Prague",
    "_info": { "fixture-format": "state_test" }
  }
}
EOF

# The same mistake made the commonest way: the file copied out of its tree, so
# no path component names a sibling and there is nothing to rewrite.
cat > "$TMP/loose/dup.json" <<'EOF'
{
  "tests/frontier/opcodes/test_dup.py::test_dup[fork_Prague-transaction_test]": {
    "network": "Prague",
    "_info": { "fixture-format": "transaction_test" }
  }
}
EOF

# A file mixing formats is refused for the foreign ones only.
cat > "$TMP/loose/mixed.json" <<'EOF'
{
  "tests/frontier/opcodes/test_dup.py::test_dup[fork_Prague-blockchain_test]": {
    "network": "Prague",
    "_info": { "fixture-format": "blockchain_test" }
  },
  "tests/frontier/opcodes/test_dup.py::test_dup[fork_Prague-blockchain_test_engine]": {
    "network": "Prague",
    "_info": { "fixture-format": "blockchain_test_engine" }
  }
}
EOF

echo '{}' > "$TMP/loose/empty.json"

cat > "$TMP/loose/unsupported.json" <<'EOF'
{
  "tests/frontier/opcodes/test_dup.py::test_dup[fork_Cancun-blockchain_test]": {
    "network": "Cancun",
    "_info": { "fixture-format": "blockchain_test" }
  }
}
EOF

# The declared-but-unimplemented twin of unsupported.json: identical but for
# the label. This is the shape every fixture in the installed Glamsterdam
# devnet corpus has, and the refusal below is the one that corpus meets.
cat > "$TMP/loose/declared_unimplemented.json" <<'EOF'
{
  "tests/amsterdam/eip7843_slotnum/test_slotnum.py::test_slotnum[fork_Amsterdam-blockchain_test]": {
    "network": "Amsterdam",
    "_info": { "fixture-format": "blockchain_test" }
  }
}
EOF

# A transition into an unimplemented fork. Its pre-fork blocks would run
# perfectly well under BPO2, which is exactly why the refusal has to come
# before the first block rather than partway through the case.
cat > "$TMP/loose/declared_transition.json" <<'EOF'
{
  "tests/amsterdam/eip7843_slotnum/test_slotnum.py::test_slotnum[fork_BPO2ToAmsterdamAtTime15k-blockchain_test]": {
    "network": "BPO2ToAmsterdamAtTime15k",
    "_info": { "fixture-format": "blockchain_test" }
  }
}
EOF

cat > "$TMP/loose/declared.json" <<'EOF'
{
  "tests/frontier/opcodes/test_dup.py::test_dup[fork_Prague-blockchain_test]": {
    "network": "Prague",
    "_info": { "fixture-format": "blockchain_test" }
  }
}
EOF

# The A/B twin of declared.json: identical but for the absent `_info`.
cat > "$TMP/loose/undeclared.json" <<'EOF'
{
  "tests/frontier/opcodes/test_dup.py::test_dup[fork_Prague-blockchain_test]": {
    "network": "Prague"
  }
}
EOF

# ------------------------------------------------------------------ checks --

# 1. Wrong tree, still in it: refuse, and name the blockchain_tests copy.
expect_refusal "wrong-tree (in state_tests)" \
  "holds [state_test] cases, and jaune runs blockchain_test fixtures" \
  "$TMP/state_tests/nested/dup.json"
expect_last_has "wrong-tree (in state_tests)" \
  "-- here, $TMP/blockchain_tests/nested/dup.json"

# 2. Wrong tree, copied out of it: same refusal, and no sibling to name.
expect_refusal "wrong-tree (copied out)" \
  "holds [transaction_test] cases, and jaune runs blockchain_test fixtures" \
  "$TMP/loose/dup.json"
expect_last_lacks "wrong-tree (copied out)" " -- here, "

# 3. Mixed formats: the runnable format is not reported as foreign.
expect_refusal "mixed formats" \
  "holds [blockchain_test_engine] cases" \
  "$TMP/loose/mixed.json"

# 4. No cases at all is a corpus error, never a vacuous pass.
expect_refusal "empty file" \
  "holds no cases; an empty fixture file is a corpus error, never a vacuous pass" \
  "$TMP/loose/empty.json"

# 5. Out of this build's fork range: report the labels, both sides.
expect_refusal "unsupported network" \
  "runs at a network this build supports; the file's labels are [Cancun]" \
  "$TMP/loose/unsupported.json"

# 5b. A label this build parses but cannot run is refused as *unimplemented*,
#     not as unknown, and refused before any block is read. `SELECTED CASES`
#     must not appear: reaching the per-case run and only then refusing would
#     mean the refusal had already been reported as a block verdict.
expect_refusal "declared but unimplemented network" \
  "UnsupportedForkError : fork Amsterdam is a declared protocol fork" \
  "$TMP/loose/declared_unimplemented.json"
expect_last_lacks "declared but unimplemented network" \
  "runs at a network this build supports"

# 5c. The same, through a transition label whose other endpoint this build
#     does run. Checking only the static label would leave the case where the
#     first blocks are runnable and the later ones are not.
expect_refusal "transition into an unimplemented network" \
  "UnsupportedForkError : fork Amsterdam is a declared protocol fork" \
  "$TMP/loose/declared_transition.json"

# 6. An empty selection the command line caused is a command-line error, and
#    says how much it filtered away.
expect_refusal "filters select nothing" \
  "the filters select no case in" \
  "$TMP/loose/declared.json" --name nosuchcase
expect_last_has "filters select nothing" \
  "1 of its 1 cases run at a supported network, with labels [Prague]"

# 7. The permissive half of rule 1: a case declaring no format is passed
#    through and reaches the per-case run, exactly as its declared twin does.
for variant in declared undeclared; do
  CHECKS=$((CHECKS + 1))
  run_jaune "$TMP/loose/$variant.json"
  if has "jaune runs blockchain_test fixtures" "$RUN_ERR"; then
    fail "pass-through ($variant): refused a file that declares no foreign format"
    detail "got: $RUN_ERR"
  elif ! has "SELECTED CASES : 1" "$RUN_OUT" \
    || ! has "TEST NAME : tests/frontier/opcodes/test_dup.py::test_dup[fork_Prague-blockchain_test]" "$RUN_OUT"; then
    fail "pass-through ($variant): did not reach the per-case run"
    detail "stdout: ${RUN_OUT:-<empty stdout>}"
  fi
done

# 8. The rule-data printers. `--rules` answers for a fork this build runs and
#    refuses one it does not, which is what makes the constants gate's fork
#    list and `Fork.supported` the same list. `--rules-partial` is the mirror
#    image: it answers only for a fork carrying a metering vehicle, so a
#    partial record can never be mistaken for a complete one.
CHECKS=$((CHECKS + 1))
run_jaune --rules Prague
if [ "$RUN_RC" -ne 0 ] || ! has '"gas.txBase": 21000' "$RUN_OUT"; then
  fail "--rules Prague: expected the Prague record on stdout"
  detail "rc=$RUN_RC stdout: ${RUN_OUT:-<empty stdout>}"
fi
expect_refusal "--rules on an unimplemented fork" \
  "UnsupportedForkError : fork Amsterdam is a declared protocol fork" \
  --rules Amsterdam
expect_refusal "--rules-partial on an implemented fork" \
  "has no metering vehicle" \
  --rules-partial Prague
CHECKS=$((CHECKS + 1))
run_jaune --rules-partial Amsterdam
if [ "$RUN_RC" -ne 0 ] \
  || ! has '"stateGas.costPerStateByte": 1530' "$RUN_OUT" \
  || ! has '"gas.txBase": 12000' "$RUN_OUT"; then
  fail "--rules-partial Amsterdam: expected the metering vehicle's rows"
  detail "rc=$RUN_RC stdout: ${RUN_OUT:-<empty stdout>}"
fi
CHECKS=$((CHECKS + 1))
if has "code.maxCodeSize" "$RUN_OUT" || has "header.blockAccessListHash" "$RUN_OUT"; then
  fail "--rules-partial Amsterdam: printed a field the vehicle does not claim"
  detail "stdout: $RUN_OUT"
fi

# ----------------------------------------------------------------- verdict --

if [ "$FAILS" -ne 0 ]; then
  echo "REGRESSION — cli: $FAILS of $CHECKS check(s) failed; the runner's refusal paths no longer match this gate"
  exit 1
fi

echo "OK — cli: $CHECKS checks; the four fixture-file refusals and the unimplemented-fork refusal hold, an undeclared format is still passed through, and the two rule-data printers answer for exactly the forks they should"
exit 0
