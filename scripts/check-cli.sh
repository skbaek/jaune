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
# A fifth refusal joined them when `Fork.amsterdam` was declared -- a case whose
# network label this build *parses* but whose rules it does not implement --
# and left again when goal C composed `amsterdamRules`: every declared label
# now resolves. The two files that pinned that refusal (an Amsterdam static
# case and a BPO2-to-Amsterdam transition, each differing from unsupported.json
# only in the label) are kept and asserted the other way round: they pass rule
# resolution, are never refused as unsupported, and fail only on the synthetic
# fixture's absent block data. `Cancun` (rule 3) is still a label this build
# does not know, so the distinction between "unknown" and "declared" survives
# as the difference between rule 3 and these two admissions.
#
# Nothing else pinned them. The conformance tiers only ever run well-formed
# corpus files, `scripts/golden-messages.txt` covers block-rejection reasons
# observed *inside* a run, and the Python tests under `scripts/tests/` cover the
# bootstrap and generator scripts. The t8n handshake also needs a small
# boundary here: `t8n --forks` must name exactly the runnable lane -- the five
# supported forks, Amsterdam included since goal jaune-amsterdam-currency-v1
# took the owner-consulted step goal C surfaced -- and agree with
# `sources.json`'s `conformance_target.fork_lane`; `--info` must state the lane
# and its basis and no longer call Amsterdam pending; and an Amsterdam
# invocation must pass rule resolution before it reaches its inputs. So all of these surfaces are kept by this falsifier: it builds
# synthetic fixtures in a temp dir, runs the built binary against each, and
# asserts both the exit status and a substring of the message.
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

# The declared twin of unsupported.json: identical but for the label. This is
# the shape every fixture in the installed Glamsterdam devnet corpus has; it
# was refused as unimplemented until goal C, and is admitted below.
cat > "$TMP/loose/declared_unimplemented.json" <<'EOF'
{
  "tests/amsterdam/eip7843_slotnum/test_slotnum.py::test_slotnum[fork_Amsterdam-blockchain_test]": {
    "network": "Amsterdam",
    "_info": { "fixture-format": "blockchain_test" }
  }
}
EOF

# A transition into Amsterdam. Both endpoints resolve since goal C, so the
# label passes rule resolution; the harness-level `amsterdam-transitions`
# suite runs under `check-mainnet.sh` since goal jaune-amsterdam-currency-v1
# gated the activation boundary (goal C's harness refused it until then).
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

# 5b. Amsterdam is a label this build parses *and* runs (goal C). The case is
#     admitted past both fork guards -- neither "unsupported" (rule 3) nor
#     "unimplemented" (the retired fifth refusal) -- and fails only on the
#     synthetic fixture's absent block data, exactly like undeclared.json.
#     (Goal A asserted the UnsupportedForkError refusal here; rewritten.)
expect_admitted_past_fork_guards() { # <label> <argv...>
  label="$1"; shift
  CHECKS=$((CHECKS + 1))
  run_jaune "$@"
  if [ "$RUN_RC" -eq 0 ]; then
    fail "$label: a synthetic fixture with no block data cannot pass"
    return
  fi
  if has "UnsupportedForkError" "$RUN_ERR"; then
    fail "$label: refused as an unimplemented fork, but Amsterdam resolves"
    detail "got: ${RUN_ERR:-<empty stderr>}"
  fi
  if has "runs at a network this build supports" "$RUN_ERR"; then
    fail "$label: refused as an unknown network, but Amsterdam is declared and runs"
    detail "got: ${RUN_ERR:-<empty stderr>}"
  fi
}
expect_admitted_past_fork_guards "declared and implemented network (Amsterdam)" \
  "$TMP/loose/declared_unimplemented.json"

# 5c. The same, through a transition label into Amsterdam whose other endpoint
#     this build also runs: the label passes rule resolution for both
#     endpoints. (Goal A asserted the UnsupportedForkError refusal here.)
expect_admitted_past_fork_guards "transition into Amsterdam" \
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

# 8. The rule-data printer. `--rules` answers for every fork this build runs,
#    which since goal C is every declared fork, and that is what makes the
#    constants gate's fork list and `Fork.supported` the same list. Goal B's
#    `--rules-partial` (the metering vehicle's partial view) is retired with
#    the vehicle: the flag is unknown, and Amsterdam is printed whole.
#    (Goal A asserted `--rules Amsterdam` was refused with UnsupportedForkError,
#    and goal B asserted `--rules-partial Amsterdam` printed the vehicle's rows
#    and none of the block-level fields; both are rewritten here.)
CHECKS=$((CHECKS + 1))
run_jaune --rules Prague
if [ "$RUN_RC" -ne 0 ] || ! has '"gas.txBase": 21000' "$RUN_OUT"; then
  fail "--rules Prague: expected the Prague record on stdout"
  detail "rc=$RUN_RC stdout: ${RUN_OUT:-<empty stdout>}"
fi
CHECKS=$((CHECKS + 1))
run_jaune --rules Amsterdam
if [ "$RUN_RC" -ne 0 ] \
  || ! has '"gas.txBase": 12000' "$RUN_OUT" \
  || ! has '"stateGas.costPerStateByte": 1530' "$RUN_OUT" \
  || ! has '"code.maxCodeSize": 65536' "$RUN_OUT" \
  || ! has '"header.blockAccessListHash": true' "$RUN_OUT" \
  || ! has '"bal.itemCost": 2000' "$RUN_OUT" \
  || ! has '"op.slotnum": true' "$RUN_OUT" \
  || ! has '"op.stackAccess": true' "$RUN_OUT"; then
  fail "--rules Amsterdam: expected the whole Amsterdam record on stdout"
  detail "rc=$RUN_RC stdout: ${RUN_OUT:-<empty stdout>}"
fi
CHECKS=$((CHECKS + 1))
run_jaune --rules-partial Amsterdam
if [ "$RUN_RC" -eq 0 ] || has '"gas.txBase"' "$RUN_OUT"; then
  fail "--rules-partial: the retired metering-vehicle printer still answers"
  detail "rc=$RUN_RC stdout: ${RUN_OUT:-<empty stdout>}"
fi

# 9. The t8n handshake. The advertised lane is the runnable lane: `--forks`
#    names the five supported forks, Amsterdam included, and is byte-equal to
#    `sources.json`'s `conformance_target.fork_lane`, so a fork cannot be
#    advertised in one place and not the other; `--info` states the lane, its
#    basis, and the resolved list, and no longer says Amsterdam is pending.
#    (Goal C asserted here that `--forks` stayed the four-fork lane and that
#    `--info` said Amsterdam was "not yet advertised on --forks, pending goal
#    jaune-amsterdam-currency-v1"; goal B, before it, that `--info` named a
#    separate "metering lane" omitting block semantics. Each is rewritten to
#    the statement that replaced it.)
CHECKS=$((CHECKS + 1))
run_jaune t8n --forks
LANE_FROM_SOURCES="$(python3 -c '
import json, sys
print(" ".join(json.load(open(sys.argv[1]))["conformance_target"]["fork_lane"]))' "$ROOT/scripts/sources.json")"
if [ "$RUN_RC" -ne 0 ] || [ "$RUN_OUT" != "Prague Osaka BPO1 BPO2 Amsterdam" ]; then
  fail "t8n --forks: expected the five-fork lane, Amsterdam included"
  detail "rc=$RUN_RC stdout: ${RUN_OUT:-<empty stdout>}"
fi

CHECKS=$((CHECKS + 1))
if [ "$RUN_OUT" != "$LANE_FROM_SOURCES" ]; then
  fail "t8n --forks: the advertised lane and sources.json conformance_target.fork_lane disagree"
  detail "binary: ${RUN_OUT:-<empty>}; sources.json: $LANE_FROM_SOURCES"
fi

CHECKS=$((CHECKS + 1))
run_jaune t8n --info
if [ "$RUN_RC" -ne 0 ] \
  || ! has "t8n fork lane: Prague Osaka BPO1 BPO2 Amsterdam" "$RUN_OUT" \
  || ! has "t8n lane basis: the advertised lane is every fork this build runs" "$RUN_OUT" \
  || ! has "t8n resolves: Prague Osaka BPO1 BPO2 Amsterdam" "$RUN_OUT"; then
  fail "t8n --info: expected the five-fork lane, its basis, and the resolved fork list"
  detail "rc=$RUN_RC stdout: ${RUN_OUT:-<empty stdout>}"
fi

CHECKS=$((CHECKS + 1))
if has "not yet advertised" "$RUN_OUT" \
  || has "pending goal jaune-amsterdam-currency-v1" "$RUN_OUT" \
  || has "omits EIP-7928/8282/7843/8024/7954 block semantics" "$RUN_OUT"; then
  fail "t8n --info: a retired lane statement (pending-goal note or block-semantics omission) is still printed"
  detail "stdout: ${RUN_OUT:-<empty stdout>}"
fi

CHECKS=$((CHECKS + 1))
run_jaune t8n --state.fork Amsterdam \
  --input.alloc "$TMP/absent-amsterdam-alloc.json"
if [ "$RUN_RC" -ne 1 ] || has "UnsupportedForkError" "$RUN_ERR"; then
  fail "t8n Amsterdam: expected rule resolution before the missing input"
  detail "rc=$RUN_RC stderr: ${RUN_ERR:-<empty stderr>}"
fi

# ----------------------------------------------------------------- verdict --

if [ "$FAILS" -ne 0 ]; then
  echo "REGRESSION — cli: $FAILS of $CHECKS check(s) failed; the runner's refusal paths no longer match this gate"
  exit 1
fi

echo "OK — cli: $CHECKS checks; fixture refusals, the Amsterdam admissions, the rule-data printer, and the t8n handshake hold"
exit 0
