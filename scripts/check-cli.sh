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
# fixture's absent block data. Since goal jaune-historical-forks-v1 (U1)
# declared the pre-Prague forks, earlier candidates parsed Istanbul but
# refused it per case with UnsupportedForkError. U9/U10 used Cancun
# for that check; U11a moved it to Paris, U11b to Berlin, and U11d to Istanbul.
# This experimental candidate admits the remaining records: the Istanbul file
# now pins admission (5d), while Frontier retains the unknown-network refusal.
#
# Nothing else pinned them. The conformance tiers only ever run well-formed
# corpus files, `scripts/golden-messages.txt` covers block-rejection reasons
# observed *inside* a run, and the Python tests under `scripts/tests/` cover the
# bootstrap and generator scripts. The t8n handshake also needs a small
# boundary here: `t8n --forks` must name the canonical target projection of
# the runnable lane and agree with
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
  "tests/frontier/opcodes/test_dup.py::test_dup[fork_Frontier-blockchain_test]": {
    "network": "Frontier",
    "_info": { "fixture-format": "blockchain_test" }
  }
}
EOF

# A declared fork whose rules this build does not implement (U1's twelve).
cat > "$TMP/loose/declared_refused.json" <<'EOF'
{
  "tests/frontier/opcodes/test_dup.py::test_dup[fork_Istanbul-blockchain_test]": {
    "network": "Istanbul",
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
  "runs at a network this build supports; the file's labels are [Frontier]" \
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
    fail "$label: refused as an unimplemented fork, but this declared fork resolves"
    detail "got: ${RUN_ERR:-<empty stderr>}"
  fi
  if has "runs at a network this build supports" "$RUN_ERR"; then
    fail "$label: refused as an unknown network, but this label is declared and runnable"
    detail "got: ${RUN_ERR:-<empty stderr>}"
  fi
}
# 5d. The formerly refused Istanbul case now passes both fork guards.
# The unknown-network refusal remains pinned by the Frontier case above.
expect_admitted_past_fork_guards "declared and implemented network (Istanbul)" \
  "$TMP/loose/declared_refused.json"

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

# 9. The t8n handshake. `--forks` names the runnable target projection,
#    with Petersburg as ConstantinopleFix and synthetic Constantinople
#    omitted. Its output is byte-equal to
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
if [ "$RUN_RC" -ne 0 ] || [ "$RUN_OUT" != "Byzantium ConstantinopleFix Istanbul MuirGlacier Berlin London ArrowGlacier GrayGlacier Paris Shanghai Cancun Prague Osaka BPO1 BPO2 Amsterdam" ]; then
  fail "t8n --forks: expected the canonical target-name lane"
  detail "rc=$RUN_RC stdout: ${RUN_OUT:-<empty stdout>}"
fi

CHECKS=$((CHECKS + 1))
if [ "$RUN_OUT" != "$LANE_FROM_SOURCES" ]; then
  fail "t8n --forks: the advertised lane and sources.json conformance_target.fork_lane disagree"
  detail "binary: ${RUN_OUT:-<empty>}; sources.json: $LANE_FROM_SOURCES"
fi

# Every advertised target name resolves before any input is read. This also
# rejects advertising a general-only spelling such as Petersburg.
for name in $LANE_FROM_SOURCES; do
  CHECKS=$((CHECKS + 1))
  run_jaune t8n --state.fork "$name" --input.alloc "$TMP/absent-target-label-alloc.json"
  if [ "$RUN_RC" -ne 1 ] || ! has "$TMP/absent-target-label-alloc.json" "$RUN_ERR" \
      || has "UnsupportedForkError" "$RUN_ERR" || has "does not support the fork" "$RUN_ERR"; then
    fail "t8n $name: advertised target name did not reach the missing input"
    detail "rc=$RUN_RC stderr: ${RUN_ERR:-<empty stderr>}"
  fi
done


CHECKS=$((CHECKS + 1))
run_jaune t8n --info
if [ "$RUN_RC" -ne 0 ] \
  || ! has "t8n fork lane: Byzantium ConstantinopleFix Istanbul MuirGlacier Berlin London ArrowGlacier GrayGlacier Paris Shanghai Cancun Prague Osaka BPO1 BPO2 Amsterdam" "$RUN_OUT" \
  || ! has "t8n lane basis: runnable forks with a pinned-target transition-tool" "$RUN_OUT" \
  || ! has "t8n resolves: Byzantium ConstantinopleFix Istanbul MuirGlacier Berlin London ArrowGlacier GrayGlacier Paris Shanghai Cancun Prague Osaka BPO1 BPO2 Amsterdam" "$RUN_OUT"; then
  fail "t8n --info: expected the canonical target-name lane, its basis, and the resolved fork list"
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

# The canonical Petersburg target name and historical transition now pass
# rule lookup before input loading. General-only Petersburg and synthetic
# Constantinople remain unknown t8n names below.
for name in ConstantinopleFix ByzantiumToConstantinopleAt5; do
  CHECKS=$((CHECKS + 1))
  run_jaune t8n --state.fork "$name" --input.alloc "$TMP/absent-amsterdam-alloc.json"
  if [ "$RUN_RC" -ne 1 ] || has "UnsupportedForkError" "$RUN_ERR" \
      || ! has "$TMP/absent-amsterdam-alloc.json" "$RUN_ERR"; then
    fail "t8n $name: expected rule resolution before the missing input"
    detail "rc=$RUN_RC stderr: ${RUN_ERR:-<empty stderr>}"
  fi
done
for name in Berlin London ArrowGlacier GrayGlacier Merge Shanghai Cancun BerlinToLondonAt5; do
  CHECKS=$((CHECKS + 1))
  run_jaune t8n --state.fork "$name" --input.alloc "$TMP/absent-amsterdam-alloc.json"
  if [ "$RUN_RC" -ne 1 ] || has "UnsupportedForkError" "$RUN_ERR"; then
    fail "t8n $name: expected rule resolution before the missing input"
    detail "rc=$RUN_RC stderr: ${RUN_ERR:-<empty stderr>}"
  fi
done
for name in Petersburg Constantinople; do
  CHECKS=$((CHECKS + 1))
  run_jaune t8n --state.fork "$name" --input.alloc "$TMP/absent-amsterdam-alloc.json"
  if [ "$RUN_RC" -ne 1 ] || ! has "t8n does not support the fork" "$RUN_ERR"; then
    fail "t8n $name: expected the unknown-fork refusal the target gives"
    detail "rc=$RUN_RC stderr: ${RUN_ERR:-<empty stderr>}"
  fi
done
# `--state.reward` is read: a non-integer is refused, not ignored.
CHECKS=$((CHECKS + 1))
run_jaune t8n --state.fork Prague --state.reward abc
if [ "$RUN_RC" -ne 1 ] || ! has "--state.reward expects an integer" "$RUN_ERR"; then
  fail "t8n --state.reward abc: expected the integer refusal"
  detail "rc=$RUN_RC stderr: ${RUN_ERR:-<empty stderr>}"
fi

# Historical allocations retain explicit empty accounts. The fork-aware
# blockchain-prestate policy rejects the same empty fields from Paris on,
# including nonempty storage. The t8n MaterializedAlloc path stays permissive.
cat > "$TMP/empty-alloc.json" <<'EOF_ALLOC'
{"0x1111111111111111111111111111111111111111":
 {"nonce":"0x00","balance":"0x00","code":"0x","storage":{"0x00":"0x00"}}}
EOF_ALLOC
cat > "$TMP/storage-only-alloc.json" <<'EOF_ALLOC'
{"0x1111111111111111111111111111111111111111":
 {"nonce":"0x00","balance":"0x00","code":"0x","storage":{"0x00":"0x01"}}}
EOF_ALLOC
printf '[]\n' > "$TMP/empty-txs.json"
for fork in Berlin Merge; do
  case "$fork" in Berlin) environment=berlin ;; Merge) environment=merge ;; esac
  mkdir -p "$TMP/empty-$fork"
CHECKS=$((CHECKS + 1))
run_jaune t8n --state.fork "$fork" --state.reward=-1 \
  --input.alloc "$TMP/empty-alloc.json" \
  --input.env "$ROOT/scripts/t8n/cases/hist-transfer-$environment/env.json" \
  --input.txs "$TMP/empty-txs.json" --output.basedir "$TMP/empty-$fork" \
  --output.alloc alloc.json --output.result result.json --output.body body.json
if [ "$RUN_RC" -ne 0 ]; then
  fail "$fork t8n empty allocation: expected a successful transition"
  detail "rc=$RUN_RC stderr: ${RUN_ERR:-<empty stderr>}"
elif ! python3 - "$TMP/empty-$fork/alloc.json" <<'EOF_CHECK'
import json
import sys
from pathlib import Path
allocation = json.loads(Path(sys.argv[1]).read_text())
assert set(allocation) == {"0x1111111111111111111111111111111111111111"}, allocation
account = next(iter(allocation.values()))
assert int(account["nonce"], 16) == 0 and int(account["balance"], 16) == 0, account
assert account["code"] == "0x" and account["storage"] == {}, account
EOF_CHECK
then
  fail "$fork t8n empty allocation: empty account was lost or zero storage retained"
fi
done
# A fixed canonical Paris genesis envelope lets these synthetic cases reach
# the blockchain prestate policy. Header/RLP source: legacy restoration
# 41404287, NonZeroValue_TransactionCALL_ToEmpty_Paris_d0g0v0_Paris.
# Neither case has a valid root for its altered prestate: if the policy is
# removed, it must fail at a different boundary and this control turns red.
python3 - "$TMP" <<'EOF_FIXTURES'
import json
import sys
from pathlib import Path
root = Path(sys.argv[1])
base = json.loads(r'''{"network":"Paris","genesisBlockHeader":{"baseFeePerGas":"0x0b","bloom":"0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000","coinbase":"0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba","difficulty":"0x00","extraData":"0x00","gasLimit":"0x989680","gasUsed":"0x00","hash":"0x416404aa6551fdeb78e92b675ae8b70f3637fdbc3c7706baf4313381786ef85b","mixHash":"0x0000000000000000000000000000000000000000000000000000000000020000","nonce":"0x0000000000000000","number":"0x00","parentHash":"0x0000000000000000000000000000000000000000000000000000000000000000","receiptTrie":"0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421","stateRoot":"0xa1f80a72f40cdf16c2a64b31f74d9cc75a77d74061b7963c128417693e520056","timestamp":"0x00","transactionsTrie":"0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421","uncleHash":"0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"},"genesisRLP":"0xf901f6f901f1a00000000000000000000000000000000000000000000000000000000000000000a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347942adc25665018aa1fe0e6bc666dac8fc2697ff9baa0a1f80a72f40cdf16c2a64b31f74d9cc75a77d74061b7963c128417693e520056a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421b9010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000808083989680808000a000000000000000000000000000000000000000000000000000000000000200008800000000000000000bc0c0"}''')
for variant in ("empty", "storage-only"):
    case = dict(base, pre=json.loads((root / f"{variant}-alloc.json").read_text()))
    (root / f"paris-{variant}.json").write_text(json.dumps({f"empty-policy-{variant}": case}))
EOF_FIXTURES
for allocation in empty storage-only; do
  CHECKS=$((CHECKS + 1))
  run_jaune "$TMP/paris-$allocation.json"
  if [ "$RUN_RC" -ne 1 ] \
    || ! has "empty account in proof-of-stake prestate" "$RUN_ERR"; then
    fail "Paris $allocation blockchain allocation: expected the empty-prestate refusal"
    detail "rc=$RUN_RC stdout: ${RUN_OUT:-<empty stdout>} stderr: ${RUN_ERR:-<empty stderr>}"
  fi
done

# Explicit original-identity diagnostics require a full network selection and
# a new absolute report path. These controls exercise only the new CLI/report
# boundary; the existing synthetic case deliberately has no genesis data.
expect_refusal "identity closure missing report" "--identity-closure takes a report path" \
  "$TMP/loose/undeclared.json" --network Prague --identity-closure
expect_refusal "identity closure duplicate report" "--identity-closure given more than once" \
  "$TMP/loose/undeclared.json" --network Prague \
  --identity-closure "$TMP/closure.json" --identity-closure "$TMP/other.json"
expect_refusal "identity closure missing network" "--identity-closure requires explicit --network" \
  "$TMP/loose/undeclared.json" --identity-closure "$TMP/closure.json"
for option in --name --notName --index; do
  expect_refusal "identity closure $option filter" \
    "--identity-closure forbids --name, --notName and --index" \
    "$TMP/loose/undeclared.json" --network Prague \
    --identity-closure "$TMP/closure.json" "$option" 0
done
expect_refusal "identity closure relative report" \
  "--identity-closure requires absolute input and report paths" \
  "$TMP/loose/undeclared.json" --network Prague --identity-closure relative-report.json
expect_refusal "identity closure relative input" \
  "--identity-closure requires absolute input and report paths" \
  relative-input.json --network Prague --identity-closure "$TMP/closure.json"
expect_refusal "identity closure vector mode" "--identity-closure is only available in fixture mode" \
  --vectors 00 "$TMP/loose/undeclared.json" --identity-closure "$TMP/closure.json"

cp "$TMP/loose/undeclared.json" "$TMP/input-before.json"
expect_refusal "identity closure input collision" "--identity-closure report must differ from input" \
  "$TMP/loose/undeclared.json" --network Prague --identity-closure "$TMP/loose/undeclared.json"
CHECKS=$((CHECKS + 1))
if ! cmp -s "$TMP/input-before.json" "$TMP/loose/undeclared.json"; then
  fail "identity closure input collision: input bytes changed"
fi
printf 'retained report sentinel\n' > "$TMP/existing-report.json"
cp "$TMP/existing-report.json" "$TMP/report-before.json"
expect_refusal "identity closure existing report" "--identity-closure report must not already exist" \
  "$TMP/loose/undeclared.json" --network Prague --identity-closure "$TMP/existing-report.json"
CHECKS=$((CHECKS + 1))
if ! cmp -s "$TMP/report-before.json" "$TMP/existing-report.json"; then
  fail "identity closure existing report: report bytes changed"
fi

CHECKS=$((CHECKS + 1))
run_jaune "$TMP/loose/undeclared.json" --network Prague --identity-closure "$TMP/closure.json"
if [ "$RUN_RC" -ne 1 ] \
  || ! has "SELECTED CASES : 1" "$RUN_OUT" \
  || ! has "TEST NAME : tests/frontier/opcodes/test_dup.py::test_dup[fork_Prague-blockchain_test]" "$RUN_OUT" \
  || ! has "TEST INDEX : 0" "$RUN_OUT"; then
  fail "identity closure fatal genesis: expected raw failure and original case markers"
  detail "rc=$RUN_RC stdout: ${RUN_OUT:-<empty stdout>} stderr: ${RUN_ERR:-<empty stderr>}"
elif ! python3 - "$TMP/closure.json" "$TMP/loose/undeclared.json" <<'EOF_CLOSURE'
import json
import sys
from pathlib import Path
report_path, input_path = map(Path, sys.argv[1:])
report = json.loads(report_path.read_text())
assert report["schema"] == "jaune-original-identity-closure-v1", report
assert report["input_path"] == str(input_path) and report["network_filter"] == "Prague", report
assert len(report["cases"]) == 1, report
case = report["cases"][0]
assert case["case_key"] == next(iter(json.loads(input_path.read_text()))), case
assert case["original_case_index_sorted_keys"] == 0 and case["network"] == "Prague", case
assert case["genesis_checks_complete"] is False and case["case_complete"] is False, case
assert case["candidates"] == [] and case["final_assertions"] is None, case
assert not list(report_path.parent.glob(report_path.name + ".tmp-*")), report_path
EOF_CLOSURE
then
  fail "identity closure fatal genesis: missing/incorrect partial report or leaked temporary file"
fi
CHECKS=$((CHECKS + 1))
if ! cmp -s "$TMP/input-before.json" "$TMP/loose/undeclared.json"; then
  fail "identity closure fatal genesis: input bytes changed"
fi

# ----------------------------------------------------------------- verdict --

if [ "$FAILS" -ne 0 ]; then
  echo "REGRESSION — cli: $FAILS of $CHECKS check(s) failed; the runner's refusal paths no longer match this gate"
  exit 1
fi

echo "OK — cli: $CHECKS checks; fixture refusals, the Amsterdam and Berlin-through-Cancun admissions, the rule-data printer, and the t8n handshake hold"
exit 0
