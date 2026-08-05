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

# ----------------------------------------------------------------- verdict --

if [ "$FAILS" -ne 0 ]; then
  echo "REGRESSION — cli: $FAILS of $CHECKS check(s) failed; the runner's refusal paths no longer match this gate"
  exit 1
fi

echo "OK — cli: $CHECKS checks; the four fixture-file refusals hold and an undeclared format is still passed through"
exit 0
