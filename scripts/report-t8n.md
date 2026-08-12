# `t8n` frontend — completion report

**Date:** 2026-08-10
**Goal:** `~/plans/t8n-goal.md`
**Jaune branch:** `codex/t8n-frontend`, from `main` `4ec33de`
**Conformance target:** `execution-specs` `forks/amsterdam`
`9d6e6f8352a0f76e7e8803722d1a2798fa4f0a96`, at
`~/execution-specs-t8n-amsterdam`
**Wrapper patch:** `~/plans/t8n-eest-jaune-wrapper.patch`, also committed on
that checkout's `jaune-wrapper` branch
**Third tool:** go-ethereum `evm`, `evm version 1.15.6-stable-19d2b4c8`, at
`~/geth-evm-1.15.6/`
**Status:** every definition-of-done row is satisfied.

## What was built

`jaune t8n` reads a pre-state, an environment and a transaction list under a
named fork, executes one state transition outside any block-validation
context, and emits `result` and the post-state `alloc` in the shapes the
conformance target emits.

The seam is the one the goal named. `stateTransitionE` validates a sealed
header, builds a `Benv` from a chain and a header, runs the body, computes six
values, and *compares* them against the header. `Jaune/T8n.lean` drops
`validateHeader` and `stateTransitionChecks`, builds the `Benv` from `env`,
runs the same body functions, computes the same six values with the same
functions, and emits. `processTransaction`, `processWithdrawals`,
`processGeneralPurposeRequests` and `processUncheckedSystemTransaction` are
called unchanged; the only new control flow is the reject-and-continue fold.

**The library root's import closure is untouched.** `git diff main` over
`Jaune.lean` and its twelve closure modules is empty. The whole change is a
new runner-side module, a 128-line deletion from `Main.lean` where its JSON
decoder block moved into that module, and script/documentation additions.

## Definition of done

| ID | Verdict | Evidence |
|---|---|---|
| G1 | **met** | `~/execution-specs-t8n-amsterdam`, `git rev-parse HEAD` = `9d6e6f8352a0f76e7e8803722d1a2798fa4f0a96`, outside `/private/tmp`; own venv at `.venv` (Python 3.11.9, `uv sync --no-default-groups --group test`); `conformance_target` entry in `scripts/sources.json` (commit `3d0bcce`); `~/execution-specs` untouched, still `4198b9c5996713b268aed602739d5aa40e277694`, never repointed |
| G2 | **met** | Every `env` / `txs` / `alloc` field of the design report's Prague–BPO2 table is accepted (`envKnownFields`, `txKnownFields`), and an unrecognised one is refused by name. `currentExcessBlobGas` is derived from the parent fields through `calculateExcessBlobGas` when absent, and `currentBaseFee` through `calculateBaseFeePerGas`. The RLP-string `txs` form is refused with the target's own reason. Measured exits: out-of-lane `--state.fork Cancun` → 1; missing `--state.fork` → 1; RLP `txs` → 1; unknown flag → 1; unknown `env` field → 1; a good run → 0. No fallback to Prague anywhere |
| G3 | **met** | The split is typed: `TxParse Tx = Except TxParseError Tx`, and `RejectReason` is `parse` or `execution`, rendered once at the emission boundary. Corpus case `reject-parse`: transaction 0 never becomes a `Tx`, is reported in `rejected` at index `0x0`, and transaction 1 still executes and produces a receipt |
| G4 | **met** | `--state-test` applies `txs[0]` only, through `runStateTest`, with no system operations, no withdrawals and no requests. Rollback is not threading the new state. Corpus case `transfer-state-test` is byte-identical to the target's `--state-test` output |
| G5 | **met** | `runBlockchain` runs the history-storage and beacon-roots system transactions, the reject-and-continue fold, withdrawals and general-purpose requests, in the target's order. Corpus cases `transfer-blockchain`, `withdrawals`, `requests`, `reject-middle`, `block-exception`; the last of these lands a failing checked system transaction in `blockException` and still emits a complete result |
| G6 | **met** | Every always-emitted key is present in the target's declaration order, `blockException` appears only under block rejection, `currentDifficulty` and the Amsterdam-only block-access-list pair are absent as `exclude_none` drops them, receipts carry `transactionHash` / `status` / cumulative `gasUsed` / `bloom` / `logs`, and `blobGasUsed` is emitted. Nine corpus cases agree byte for byte |
| G7 | **met** | `scripts/check-t8n.sh` runs every case twice into separate directories and requires the two runs to be byte-identical, including key order and hex casing. The document is built as a value and rendered once, so order is fixed by construction |
| G8 | **met** | `jaune t8n --info` prints the version, the Lean toolchain (`4.32.1`), the fork lane, the modes, the tracing claim, and the conformance-target, oracle, legacy-corpus, EEST and current-mainnet pins — every pin read from `scripts/sources.json`, none restated. `jaune t8n --forks` prints the lane alone; `jaune -v` prints the banner |
| G9 | **met** | `scripts/check-t8n.sh` over nine committed cases — plain transfer, contract call with logs, parse rejection, execution rejection, multi-transaction rejection-in-the-middle with a later success, withdrawals, requests, block exception, and both modes. Goldens produced by `scripts/gen-t8n-goldens.py` driving the target, never transcribed; digests recorded in `scripts/t8n/provenance.json` and checked on every run; the generating revision printed in the verdict. `--red-test` corrupts one `stateRoot` in a scratch copy and requires the failure — recorded below |
| G10 | **met** | `JauneTransitionTool` + `JauneExceptionMapper` in the local checkout's `client_clis/clis/jaune.py`, registered through `client_clis/__init__.py`. The mapper declares all 43 identities Jaune can emit and matches each anchored against its own spelling. `test_jaune.py`, 18 tests, all passing, including six unmapped-reason cases that must surface as `UndefinedException`. The whole diff is one commit against the anchor |
| G11 | **met** | `fill --evm-bin ~/jaune/.lake/build/bin/jaune tests/frontier/opcodes/test_calldatasize.py --fork Prague` fills 30 of 30 cases, and the three fixture files it writes are **identical, outside `_info`, to the same module filled by the target's own in-process EELS** — 30 of 30 cases equal, field for field |
| G12 | **met** | `scripts/t8n-acceptance.py` sends the eight blockchain-mode corpus cases to Jaune, the conformance target and go-ethereum's `evm`, and compares field by field with all three versions recorded. Three cases unanimous; five carry registered divergences, and **Jaune agrees with the conformance target in every one**. Output at `scripts/report-t8n-acceptance.txt`, registry at `scripts/t8n/acceptance-divergences.json` |
| G13 | **met** | `Jaune/T8n.lean` is imported by `Main.lean` only, never from `Jaune.lean`; `git diff --name-only main` over `Jaune.lean` and its twelve closure modules is empty; `check-integrity.sh` reports 58 occurrences and 0 pending, unchanged from `main`; Blanc untouched, its pin unmoved |
| G14 | **met** | The full battery is green on the candidate, both `--full` tiers at `--jobs auto`, on an uncontended host — verdicts below |
| G15 | **met** | README carries a `t8n` section naming the subcommand, the lane, the handshake and the fail-closed rule; `scripts/GATES.md` carries a cheap-tier row and a selection row for it; this report maps every G-row |

## Gate verdicts on the candidate

Run at `lake build` = 1,778 jobs, clean tree, uncontended host, no Lean
language server alive. The heavy tiers were measured at `1d16791`; the final
commit differs from it only in `scripts/GATES.md` and
`scripts/t8n-acceptance.py`, neither of which is an input to any gate, and the
cheap gates were re-run on the final tip.

```
OK — hygiene: all 0 occurrence(s) of {dbg_trace, sorry} under Jaune/ are allowlisted
OK — integrity: all 58 occurrence(s) ... are allowlisted; 0 pending (budget 0)
OK — cli: 11 checks; the four fixture-file refusals hold
OK — u256: 21593/21593 PASS
OK — fake-exp: 240/240 PASS
OK — ec: 573/573 cases PASS
OK — patch: 10/10 PASS
OK — rlp4: 4/4 PASS
OK — depth: 67 files match baseline (--jobs 10)
OK — smoke: 174 files match baseline (173 PASS, 1 FAIL; --jobs 10)
OK — bls: 29 files match baseline (29 PASS, 0 FAIL; --jobs 10)
OK — vectors: 51/51 files PASS; controls 5/5 PASS in 87.81s (--jobs 10)
OK — elab: all 18 file(s) within 2.0x baseline; 53.2 s total vs 50.5 s baseline
OK — smoke (mainnet): 16/16 manifest files PASS
OK — transitions: 13/13 manifest files PASS (--jobs 10)
OK — full (mainnet): 5100/5100 manifest files PASS in 279.39s (--jobs 10)
OK — full (legacy): 2983 files match baseline (2978 PASS, 5 FAIL; --jobs 10)
OK — t8n red test: a corrupted stateRoot in block-exception is rejected
OK — t8n: 9 case(s) byte-identical to goldens generated from execution-specs
     9d6e6f8352a0, deterministic over two runs
Ran 121 tests ... OK          (python3 -m unittest discover -s scripts/tests)
```

Both legacy tiers are baseline-identical, which is the contract: their five
known FAILs are still FAILs and nothing turned into a PASS. `scripts/check-t8n.sh
--red-test` measured at 0.53 s.

**`check-elab.sh` needed a second run, and the first one was the gate's own
trap rather than a regression.** With `--no-build` it reported
`Jaune.lean: 3.075s vs baseline 1.230s` and went red. That measurement cannot
have been caused by this change: `Jaune.lean` and its entire import closure are
byte-identical to `main`, and `Jaune/T8n.lean` is outside that closure. The
cause is that `--no-build` skips the `lake build` that also warms the page
cache, so the first file measured — `Jaune.lean`, which sorts first — pays the
cold read alone. Run as documented, without the flag, the same tree gives
`Jaune.lean` at 1.290 s and a green verdict, and nothing else in the run moves.
`scripts/GATES.md` now records the trap and both numbers.

`Jaune/T8n.lean` itself measured 1.658 s against its 1.690 s baseline.

## The field table as implemented

`result`, in the target's declaration order, which is what `model_dump` emits:

| key | source | spelling |
|---|---|---|
| `stateRoot` | `State.root` of the post-state | 32-byte hash |
| `txRoot` | `getTransactionsRoot` | 32-byte hash |
| `receiptsRoot` | `getReceiptRoot` | 32-byte hash |
| `logsHash` | `keccak(rlp(blockLogs))` | 32-byte hash |
| `logsBloom` | `logsBloom blockLogs` | 256-byte string |
| `receipts` | `receiptKeys`, in order | array |
| `rejected` | the fold's rejections, in index order | array |
| `gasUsed` | `blockGasUsed` | minimal hex |
| `currentBaseFee` | the resolved `env` base fee | minimal hex |
| `withdrawalsRoot` | `getWithdrawalsRoot` | 32-byte hash |
| `currentExcessBlobGas` | the resolved `env` excess blob gas | minimal hex |
| `blobGasUsed` | `blobGasUsed` | minimal hex |
| `requestsHash` | `computeRequestsHash` | 32-byte hash |
| `requests` | `bout.requests` | array of byte strings |
| `blockException` | present only under block rejection | string |

`currentDifficulty` is absent because the lane is proof-of-stake and the
target's `exclude_none` drops it; `blockAccessList` / `blockAccessListHash`
are absent because they are Amsterdam-only; `sha3Uncles`, `traces` and
`opcodeCount` are absent for the same reason.

Two number spellings, and confusing them is the easiest way to produce output
that parses and still differs. `result` numbers are the target's `HexNumber`:
minimal, zero is `0x0`. `alloc` numbers — account `nonce`, `balance`, and
storage keys and values — are its `ZeroPaddedHexNumber`: an even number of
digits, zero is `0x00`. Both are reproduced exactly.

The whole document is written the way Python's `json.dump(..., indent=4)`
writes it, down to `\uXXXX` for anything outside printable ASCII.

## Deliberate divergences, and why

Every one is registered in `scripts/t8n/deviations.json`, which
`scripts/check-t8n.sh` applies to the *golden* side. Nothing is applied to
Jaune's side: its bytes are compared as written, and each entry pins Jaune's
exact expected bytes as well as the target's, so an unregistered difference
and a changed registered one both fail.

**1. `rejected[].error` and `blockException` carry Jaune's own vocabulary.**
The target writes a Python `repr` — `Failed transaction:
NonceMismatchError('nonce too high')`. Jaune writes
`TransactionException.NONCE_MISMATCH_TOO_HIGH`.

This field has no normative content: every transition tool writes its own text
and the framework maps it to a canonical identity through the *registered
wrapper's* exception mapper rather than comparing it
(`exceptions/exception_mapper.py`, `cli_types.py`). The goal's invariant 8
settles the direction — Jaune retains canonical typed reasons to the boundary
— and invariant 12's rationale for rejecting the Geth facade settles it again:
imitating another tool's error vocabulary "collides with invariant 8 and
degrades precisely on the tests that check error behavior". Imitating EELS's
`repr` strings would be the same mistake with a different tool.

What Jaune writes instead is the official identity that
`Jaune/FixtureException.lean` already assigns to each typed reason. So the two
sides differ in bytes and agree in meaning: every registered pair maps to the
same `TransactionException` / `BlockException` member. A reason Jaune cannot
classify renders as `JauneT8n.UNMAPPED_*`, which the mapper deliberately does
not recognise.

**2. `alloc` key order.** The target emits Python dictionary insertion order —
the input allocation's order, then whatever its block diff touched. Jaune's
state is a `Std.TreeMap`, so it emits ascending key order. Neither is
normative and no consumer reads either, so the gate sorts both sides
(addresses lexically, storage keys numerically) before comparing. Reproducing
the target's order would mean reproducing the order its diff happened to touch
accounts in, which is an internal detail and not deterministic by
construction.

**3 and 4. `reject-parse`'s `txRoot` and `body`.** The case's first
transaction is a type-3 blob transaction with no receiver — a shape every fork
on this lane rejects, and one `TxType.three` cannot represent at all because
its receiver is a mandatory `Adr`. The target builds the object anyway and
rejects it a step later inside `check_transaction`; because `process_transaction`
writes into the shared `block_output.transactions_trie` *before* validating,
the unexecutable transaction is still counted by `txRoot` and still encoded
into `body`. Jaune classifies the same shape at decode with the same official
identity, so `rejected` agrees; it simply has no transaction object to put in
the trie or the body. The framework consumes neither field —
`specs/blockchain.py` excludes `transactions_trie` from the fixture header and
recomputes it — and widening the type to represent an invalid shape would
weaken Jaune, not the tool.

**5. An empty `blockHashes` window in blockchain mode.** The target reads
`block_hashes[-1]` for the history-storage system transaction and raises
`IndexError` out of the whole tool when the window is empty. There is no
reference behaviour to match, so Jaune records the zero hash and continues. On
every input the target can process, the window is non-empty and Jaune uses its
last entry.

**6. A checked system contract that holds no code.** The target raises
`InvalidBlock` and reports it in `blockException`; Jaune's
`processCheckedSystemTransaction` types this reason `internal` — deliberately,
because the official identity `SYSTEM_CONTRACT_EMPTY` is outside its reviewed
vocabulary — so `jaune t8n` fails the run instead. Correcting this would mean
changing a declaration inside the library root's import closure, which the
goal reserves for the user. Not reachable from any corpus case or any `fill`
run recorded here: the `block-exception` case uses a predeploy that *has* code
and reverts, which both tools classify as a block exception.

## Upstream findings

**F1. `--state-test` never reaches an external binary.**
`TransitionToolData.state_test` is honoured by the in-process tool and dropped
by both external paths: `_evaluate_filesystem` does not pass it and
`construct_args_stream` does not either. A state test's pre-allocation is
`fork.pre_allocation()`, which carries no system contracts, so an external
tool told to run a *block* over it performs the fork's checked system
transactions against addresses holding no code — and reports an invalid block
for a test that is not about blocks at all. Measured: without the flag, ten of
the thirty `test_calldatasize` cases fail for exactly that reason; with it,
all thirty pass and match the reference fill.

The wrapper patch therefore adds `TransitionTool.supports_state_test`,
defaulting to `False`, and passes `--state-test` only for a tool that opts in.
Nothing changes for any existing tool.

**F2. `ExecutionSpecsTransitionTool` cannot be driven as an external binary.**
`fill --evm-bin .venv/bin/ethereum-spec-evm` fails with
`UnknownCLIError: ... type object 'ExecutionSpecsTransitionTool' has no
attribute 'detect_binary_pattern'`. So the target cannot be used as its own
external cross-check, which is why G11's comparison is against the in-process
fill.

**F3. An empty `env.blockHashes` crashes the tool in blockchain mode.**
`IndexError: list index out of range` out of `_run_blockchain_test`, from
`block_env.block_hashes[-1]`. Reachable from any hand-written `env` that omits
the map.

**F4. There is no reachable parse-rejection path on this lane.**
`convert_transaction` raises `UnsupportedTxError` only through
`unsupported_tx_type`, which needs a fork that does not support the type —
and Prague through BPO2 support types 0 to 4. Every other malformed input
either raises a `ValueError` out of `get_parameters` (uncaught, so the whole
run dies) or is rejected by the pydantic model before `T8N` is constructed.
So the target's `rejected` list, on this lane, only ever holds execution
rejections.

**F5. A transaction rejected during execution stays in the transactions
trie — and go-ethereum disagrees.** `process_transaction` writes it there
before validating, on a block output it mutates in place, so the entry
survives the exception and contributes to `txRoot`. When the rejection is in
the middle of a list, the surviving receipts also keep their original indices,
so `receiptsRoot` is taken over a trie keyed 0 and 2.

Jaune reproduces both deliberately, under the goal's "match the reference"
invariant, and `txRoot` in the `reject-execution` and `reject-middle` goldens
is what pins it. The three-way comparison then showed geth doing neither: it
counts only the accepted transactions and re-indexes their receipts. Geth's is
the root the block that would be built actually has, so **this looks like an
upstream defect in the conformance target, not a difference of opinion.** It
has plausibly gone unnoticed because the framework does not consume `txRoot`
at all — `specs/blockchain.py` excludes `transactions_trie` from the fixture
header and recomputes it.

**F6. The target's `body` output is not the canonical transactions-list
encoding for legacy transactions.** It writes `rlp.encode([tx.rlp() for tx in
txs])`, which wraps every member as an RLP byte string. That is right for
typed transactions, which are opaque byte strings under EIP-2718, and wrong
for legacy ones, which appear inline. Measured on the corpus: for the type-2
case all three tools agree, and for the legacy case the target and Jaune emit
`0xf864b862f860…` where geth emits `0xf862f860…`. Jaune matches the target,
again by invariant.

None of F1–F6 is a Jaune defect and none is disclosed anywhere by this goal;
whether to report them upstream is the user's call. F5 and F6 are the two
worth an upstream issue on their own.

**Disclosure addendum (2026-08-12).** Both were subsequently filed upstream
on 2026-08-11 — F6 as pull request
[ethereum/execution-specs#3361](https://github.com/ethereum/execution-specs/pull/3361)
(the body encoding, with a regression test) and F5 as issue
[ethereum/execution-specs#3362](https://github.com/ethereum/execution-specs/issues/3362)
(the indexing behaviour, framed as the tool's design decision, with two
candidate designs) — together with a public case study,
<https://skbaek.github.io/jaune/t8n-case-study.html>. Nothing on Jaune's side
moves: "match the reference" stands, the goldens pin the target's behaviour
at the anchor, and the `reject-execution`, `reject-middle` and `reject-parse`
cases are the regression detectors for the day the anchor is re-pinned past
an upstream fix. The registries carry the filings row by row — see
`scripts/t8n/deviations.json` and `scripts/t8n/acceptance-divergences.json`.

## Three-way agreement (G12)

| side | binary | revision |
|---|---|---|
| Jaune | `~/jaune/.lake/build/bin/jaune` | `codex/t8n-frontend`, `jaune version 0.1.0`, Lean 4.32.1 |
| conformance target | `~/execution-specs-t8n-amsterdam/.venv/bin/ethereum-spec-evm` | `execution-specs` `9d6e6f8352a0f76e7e8803722d1a2798fa4f0a96` (checkout HEAD `827a1cad`, that revision plus the wrapper patch, which the CLI path does not reach) |
| third tool | `~/geth-evm-1.15.6/geth-alltools-darwin-arm64-1.15.6-19d2b4c8/evm` | `evm version 1.15.6-stable-19d2b4c8`, from `geth-alltools-darwin-arm64-1.15.6-19d2b4c8.tar.gz`, 55,994,330 bytes, MD5 `eab13dc07679afd9b03c25a8ff5b8fe6` as published by the store, SHA-256 `1f90eb6752443ecac1e4853ee01891dd297c81e547b4141c7aba1fadfa14d85a`. This is the newest darwin-arm64 build go-ethereum publishes; the project's current releases carry no macOS binary |

The acceptance corpus is the committed nine-case corpus. Eight of the nine are
blockchain-mode and therefore three-way comparable; `transfer-state-test` is
not, because `--state-test` is this target's flag and geth has no equivalent.

`scripts/t8n-acceptance.py` compares semantic content rather than bytes,
because the three spell the same values differently on purpose — minimal,
zero-padded and full-width hex all appear, `alloc` key order differs, a tool
may omit a zero `nonce`, and geth's receipts carry five fields the other two
do not. Fifteen `result` fields plus the whole post-state are compared per
case. Full output: `scripts/report-t8n-acceptance.txt`.

**Result: three cases unanimous, five with registered divergences, and Jaune
agrees with the conformance target in every one.** Every divergence has geth
on one side and Jaune-with-the-target on the other, which is what reproducing
the target faithfully looks like when the target and another client genuinely
differ. Each is registered in `scripts/t8n/acceptance-divergences.json`:

| case | field(s) | what geth does differently |
|---|---|---|
| `reject-execution` | `txRoot` | counts only the accepted transactions |
| `reject-middle` | `txRoot`, `receiptsRoot` | counts only the accepted transactions, and re-indexes their receipts to 0 and 1 rather than leaving the gap at 1 |
| `reject-parse` | the whole run | refuses the input file rather than the one malformed member |
| `requests` | `requests` | omits the EIP-7685 type byte from the request payload, while computing the same `requestsHash` — so it hashes with the prefix and reports without it |
| `block-exception` | `blockException` | reports none at all when the withdrawal-request predeploy is an INVALID opcode |

The first two are the same upstream defect seen from two sides, and they are
the most consequential thing this comparison found — see F5 below.

## The EIP-3155 note

The goal asks, as a note only, whether a stepping entry point could wrap the
existing driver without threading an accumulator through `exec`.

**It could, and it should not be done by touching `exec`.** `Evm.step : Evm →
Step` is total and pure, and every field EIP-3155 reports is readable around
it without instrumentation: `pc`, the opcode and its name from `Evm.getInst`,
`gas` from `dyna.mach.gasLeft` before the step and `gasCost` as the difference
after, `stack`, `memSize`, `depth` from `sta.depth`, and `refund` from
`dyna.meta.refundCounter`. Nothing is hidden inside the step.

The cost is elsewhere. `execFueled` is the sole recursion over `Evm.step`, and
its `.spawn` arm is where child frames are entered and settled — which is
exactly what a trace has to interleave. A tracing driver in the runner-side
module would therefore be a **second copy of that recursion**, and its
fidelity to `exec` would need its own gate. That gate is cheap and would be a
real falsifier: run both drivers on the same `Evm` and require the traced
run's final `Devm` to equal `exec`'s.

The alternative — making `execFueled` polymorphic over an accumulator — is a
change to a declaration inside the library root's import closure, and every
sufficiency theorem is stated over that declaration. It would perturb the
proofs for a diagnostic feature. Do not choose it.

So: feasible, at the cost of one duplicated driver plus one equality gate, and
strictly a successor. Nothing in the frontend as built forecloses it.

## Autonomous decisions

1. **A fresh branch name.** `codex/t8n` already exists on the remote as the
   merged Step-1 branch, so the work is on `codex/t8n-frontend` rather than
   resetting an existing ref.
2. **Where the shared decoder lives.** `Main.lean`'s `Lean.Json.toIo*`,
   `toAcct`, `toWorld` and the two `find` accessors moved *into*
   `Jaune/T8n.lean` rather than into a third module, and the three
   declarations `check-integrity.sh`'s allowlist names by line
   (`Option.remove0x`, `Lean.Json.toString?`, `Except.toIO`) stayed in
   `Main.lean`. Moving those out would have relocated audited occurrences into
   a module R4 does not scope, which is the one thing that gate's own header
   warns against; leaving them keeps the inventory at 58 rows with no stale
   warnings.
3. **`--forks` as a separate probe.** `--info` reads `scripts/sources.json`
   and fails closed without it, which is right for a handshake and wrong for
   the question a framework wrapper asks from a temporary directory. Two
   flags, each fully answerable in its own context.
4. **`--state.reward` accepted and not consumed.** The target pays block
   rewards only when the fork is not proof-of-stake, and every fork on this
   lane is, so the value cannot change the transition. `fill` always passes
   it.
5. **`--input.blobParams` refused rather than ignored.** Jaune names its BPO
   forks directly, so a schedule override is not needed; accepting and
   ignoring one would silently run a different schedule than the caller asked
   for.
6. **The corpus omits the deposit contract.** 6.3 KB of bytecode that nothing
   reads unless a transaction logs a deposit, and no case does. The other four
   Prague system contracts are present, taken from the target's own
   `pre_allocation_blockchain()`.
7. **go-ethereum 1.15.6 as the third tool.** The project publishes no macOS
   binary for its current releases; 1.15.6 (2025-03-25) is the newest
   darwin-arm64 build in its store. Downloaded with the user's explicit
   approval and verified against the store's published MD5.
8. **The wrapper patch touches `transition_tool.py`.** Two lines and one
   opt-in class variable, without which no external tool can be told to use
   state-test mode (finding F1). Shaped as an upstreamable change; default
   `False`, so nothing else moves.

## Remaining risk

- **The third tool is a year old.** `evm 1.15.6` is the newest darwin-arm64
  build go-ethereum publishes, so the `requests` prefix divergence in
  particular may already be fixed upstream. It does not weaken the two
  findings that matter, which are about the *target*, not about geth.
- **The corpus is all Prague.** The lane's other three forks differ from
  Prague in their blob schedule, and no case exercises blob transactions. A
  BPO case is a fair successor.
- **An empty account in the input `alloc`** would be dropped by `toWorld`'s
  canonicalisation and kept by the target's, so the two `alloc` documents
  would differ. EEST's pre-allocations never contain one — `make_state_test_fixture`
  raises on `pre_alloc.empty_accounts()` — and no corpus case has one, so this
  is untested rather than known-divergent.
- **Divergence 6** stands: a missing checked system contract fails the run
  rather than reporting `blockException`. Fixing it needs a change inside the
  library root's import closure.
