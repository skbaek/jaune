# `t8n` Step 1 design report

**Date:** 2026-08-02
**Jaune candidate:** `codex/t8n` from merged `main`,
`5d16ebac180ee36776994ef232a7ae65e672d10d`
**Pinned oracle (unchanged):** `~/execution-specs`,
`4198b9c5996713b268aed602739d5aa40e277694`
**Current upstream, read-only:** `/private/tmp/execution-specs-t8n-20260802`,
`forks/amsterdam`, `9d6e6f8352a0f76e7e8803722d1a2798fa4f0a96`
**Comparison, read-only:** `/private/tmp/execution-specs-t8n-mainnet-20260802`,
`mainnet`, `7b8124a77280edaaad877128937b71a1e3a7ebc5`.
**Plan:** `~/plans/t8n.md`, Step 1 ("Rebind, reconnoitre, and re-decide").
**Status:** Step 1 complete, technical verdict GO. The arc is **paused after
Step 1** by user decision; Steps 2–6 are not started, so no `t8n` frontend
exists in this repository. This report was written on `codex/t8n` and merged to
`main` on 2026-08-04 so that it lives with its sibling reports; the branch
carried nothing else.

**These coordinates are historical.** Every line number and gate figure below
was measured at `5d16eba`; `main` has moved since. Re-measure the baseline per
`~/plans/t8n.md`, *Baseline gates*, rather than inheriting the numbers here.

Re-checked against `main` on 2026-08-04: the semantic-core pointers all still
land exactly — `processTransaction`, `applyTransactions`, `applyBody`,
`stateTransitionChecks`, `stateTransitionE`, `TransitionError`, `logsBloom`,
`ErrorDetail` — and `DecodeError` has shifted four lines. **The CLI row is the
one that rotted:** `bda92bc` ("cli: make every fixture option a filter") deleted
`getTestIndex` and `getNetworkSpec` outright and moved `getFork` to
`Main.lean:630`. Everything this report concludes about the seam, the typed-error
routing, and the upstream `t8n` surface is unaffected — those are anchored to
Jaune's architecture and to upstream `9d6e6f83`, neither of which moves when
Jaune's `main` does.

The fresh checkouts were fetched separately and made read-only. The pinned
oracle was neither repointed nor modified.

## Baseline and branch

`codex/t8n` was created from merged `main`. All prescribed Step 1 baseline
gates passed at `5d16eba`: `lake build` (1,774 jobs; one existing
unused-simp linter warning), hygiene, integrity (56 allowlisted / 0 pending),
U256 (21,593/21,593), PATCH (10/10), RLP4 (4/4), DEPTH
(67 baseline-identical), Python unit tests (121), mainnet smoke (16/16), and
mainnet transitions (13/13). Commands used `--no-build --jobs auto` after
the successful build where applicable.

## Rebound Jaune pointers

Signatures were verified with `lean_local_search` and Lean LSP hover. Line
numbers are coordinates for `5d16eba`, not future contracts.

| Declaration | Location | Exact current signature |
|---|---:|---|
| `processTransaction` | `Transaction.lean:1033` | `Benv -> BlockOutput -> Tx -> Nat -> Except TransitionError (State × BlockOutput)` |
| `applyTransactions` | `:1625` | `List (Nat × Tx) -> Benv -> BlockOutput -> Except TransitionError (Benv × BlockOutput)` |
| `applyBody` | `:1632` | `Benv -> List (Bytes ⊕ Tx) -> List Withdrawal -> Except TransitionError (State × BlockOutput)` |
| `computeRequestsHash` | `:1931` | `List Bytes -> B256` |
| `State.root` | `:1938` | `State -> B256` |
| `stateTransitionChecks` | `:2113` | `BlockOutput -> Header -> B256 -> B256 -> B256 -> Bytes -> B256 -> B256 -> Except BlockValidationError Unit` |
| `initBenvStat` | `:2149` | `ForkRules -> BlockChain -> Header -> BenvStat` |
| `initBenv` | `:2166` | `ForkRules -> BlockChain -> Header -> Benv` |
| `getTransactionsRoot` | `:2173` | `BlockOutput -> B256` |
| `getReceiptRoot` | `:2185` | `BlockOutput -> B256` |
| `getWithdrawalsRoot` | `:2190` | `BlockOutput -> B256` |
| `stateTransitionE` | `:2284` | `ForkRules -> BlockChain -> Block -> Except TransitionError BlockChain` |
| `stateTransitionWith` | `:2305` | `ForkRules -> BlockChain -> Block -> Except String BlockChain` |
| `logsBloom` | `Jaune/Execution.lean:876` | `List Log -> Bytes` |
| `Lean.Json.toAcct` | `Main.lean:96` | `Json -> IO Acct` |
| `Lean.Json.toWorld` | `:122` | `Json -> IO State` |
| `Lean.Json.toHeader` | `:147` | `Json -> IO Header` |
| `getTestIndex` / `getFork` / `getNetworkSpec` | `:504/525/548` | `List String -> Option Nat` / `List String -> IO Fork` / `List String -> IO NetworkSpec` |

### Seam verdict: clean

`stateTransitionE` (`Transaction.lean:2284-2301`) validates the sealed
header and ommers, creates `Benv`, calls `applyBody`, computes
`State.root`, transaction/receipt/withdrawal roots, `logsBloom`, and
`computeRequestsHash`, then calls `stateTransitionChecks`. `applyBody`
never receives a header. Step 10 changed the error carrier but did not fuse
the seam. The t8n design remains: construct the environment from `env`, use
the existing body, compute the same six values, and emit rather than compare.
No new EVM semantics is needed.

## Typed-error inventory and routing

| Type and constructors | Renderer | t8n classification |
|---|---|---|
| `ErrorDetail` (`Fork.lean:536`): `none`, `text String` | `renderTagged` | diagnostic payload only |
| `DecodeError` (`Machine.lean:1002`): `rlpStructure`, `fixedWidth`, `fieldOverflow64`, `fieldOverflow256`, `leadingZeros`, `withdrawalsNotRead`, `roundTrip` | `DecodeError.render` | `TransitionError.decode` -> candidate/block rejection |
| `TxValidationError` (`Transaction.lean:46`): `gasPriceProductOverflow`, `gasAllowanceExceeded`, `initcodeSizeExceeded`, `insufficientAccountFunds`, `insufficientMaxFeePerGas`, `insufficientMaxFeePerBlobGas`, `transactionGasLimitExceeded`, `intrinsicGasTooLow`, `invalidChainId`, `nonceIsMax`, `nonceMismatchTooHigh`, `nonceMismatchTooLow`, `priorityGreaterThanMaxFee`, `senderNotEoa`, `type3BlobCountExceeded`, `type3BlobCountLimitExceeded`, `type3ContractCreation`, `type3InvalidBlobVersionedHash`, `type3ZeroBlobs`, `type4ContractCreation`, `emptyAuthorizationList` | `TxValidationError.render` | transaction-level reject-and-continue |
| `BlockValidationError` (`:132`): `gasLimitTooBig`, `gasLimitAdjustment`, `gasUsedOverflow`, `gasUsedMismatch`, `timestampOlderThanParent`, `blockNumber`, `baseFeePerGas`, `difficultyOverParis`, `ommersOverParis`, `extraDataTooBig`, `unknownParent`, `unknownParentZero`, `stateRoot`, `transactionsRoot`, `receiptsRoot`, `logBloom`, `withdrawalsRoot`, `headerNonce`, `excessBlobGas`, `blobGasUsed`, `requestsHash`, `depositEventLayout`, `systemContractCallFailed`, `blockRlpSizeExceeded` | `BlockValidationError.render` | block-level `blockException` |
| `CryptoError` (`Machine.lean:1129`): `invalidSignature`, `pointCompression`, `value`; `ExceptionalHalt` (`:1055`): `stackUnderflow`, `stackOverflow`, `outOfGas`, `modexpInputLimit`, `invalidOpcode`, `invalidJumpDest`, `stackDepthLimit`, `writeInStaticContext`, `outOfBoundsRead`, `invalidParameter`, `invalidContractPrefix`, `addressCollision`, `kzgProof` | respective `.render` functions | sender recovery is candidate rejection; a settled VM halt is not |
| `InternalError` (`:1150`): `assertion`, `invariant`; `EvmError` (`:1169`): `halt`, `revert`, `crypto`, `internal` | respective `.render` functions | operational only |
| `ChainContextError` (`Fork.lean:602`): `emptySchedule`, `nonIncreasingActivations`, `nonForwardActivations`, `chainIdMismatch`, `invalidForkRules`; `SupportError` (`:648`): `unsupportedFork`, `unsupportedEra`; `RulesLookupError` (`:714`): `context`, `support` | respective `.render` functions | operational only |

`TransitionError` (`Transaction.lean:315-369`) has exactly
`decode DecodeError | transaction TxValidationError | block
BlockValidationError | senderRecovery CryptoError | vm EvmError | internal
InternalError`. Its renderer delegates. Its `split` is definitive:
`decode`, `transaction`, `block`, and `senderRecovery` become
`BlockRejection`; `vm` and `internal` become `ImportFailure`.

`ImportFailure` (`:220`) has `context`, `support`, `harness`,
`internal`, and `vm`; `BlockRejection` (`:263`) has `transaction`,
`block`, `decode`, and `senderRecovery`; `ImportOutcome chain` (`:290`)
is `chain ⊕ BlockRejection`; and `RawImportFailure` (`:296`) is
`strictDecode DecodeError | operational ImportFailure`. Each has the named
sole renderer at the adjacent definition.

Consequently, parse failures are recorded pre-execution, `TxValidationError`
is the normal reject-and-continue set, `BlockValidationError` is the separate
block exception, and operational failures fail closed. Step 3 must preserve
this constructor-based split, never parse its own strings.

## Current EEST / `fill` contract

The current checkout's default branch is `forks/amsterdam`. Its default
`fill` tool is the in-process `ExecutionSpecsTransitionTool`, set in
`packages/testing/src/execution_testing/client_clis/__init__.py:52` and
instantiated in `.../filler/filler.py:804-818`; it calls `T8N.run()`
(`client_clis/clis/execution_specs.py:87-150`). Therefore the actual default
reference revision in this checkout is **`forks/amsterdam`
`9d6e6f8352a0f76e7e8803722d1a2798fa4f0a96`**.

For an external binary, the framework does this:

```
fill --evm-bin /absolute/path/to/jaune …
/absolute/path/to/jaune -v
/absolute/path/to/jaune t8n \
  --input.alloc=stdin --input.txs=stdin --input.env=stdin \
  --output.result=output/result.json --output.alloc=output/alloc.json \
  --output.body=output/txs.rlp --state.fork=<Fork> \
  --state.chainid=<positive-int> --state.reward=<nonnegative-int> \
  --output.basedir=<temporary-directory>
```

Evidence: `filler.py:463-472,804-818`, `ethereum_cli.py:83-204`,
`transition_tool.py:790-868`, and `clis/geth.py:261-293`. Detection invokes
`binary -v` and requires a registered wrapper. The compatible existing
wrapper is Geth: banner regex `^evm(.exe)? version\\b`
(`geth.py:181-186`) and successful `binary t8n --help` advertising each
fork. Thus `jaune t8n` alone will not be recognized: Steps 4/5 need a
documented Geth-protocol facade (banner and help/fork surface) or an upstream
EEST Jaune wrapper. The facade is lower cost and must be confined to this
protocol compatibility surface.

When requested, the framework also supplies `--trace`; an opcode-count-capable
tool gets `--opcode.count opcodes.json`. The planned no-tracing tool should
not claim that capability.

### `rejected[].error`

Current EEST validates both `RejectedTransaction.error` and
`Result.blockException` through `ExceptionMapperValidator`
(`cli_types.py:71-79,381-420`). Verification uses
`TransactionExceptionInfo.verify(strict_match=…)` and its block analogue
(`specs/helpers.py:344-393`), not literal EELS Python-`repr` equality. The
selected Geth wrapper's mapper is substring-based (`clis/geth.py:31-178`), so
Jaune's canonical renderings are not automatically identities EEST knows.

**Decision:** retain typed Jaune reasons to the boundary; do not make Python
`repr` the semantic model. Step 5 must provide a Jaune/EEST mapping strategy
(a small EEST adapter/mapper or deliberately mapped Geth-compatible wire
phrases) and test it. This is extra Step 5 scope, not a semantic NO-GO or
Step 1 HALT.

## Current target surface, Prague through BPO2

Sources: CLI bridge `src/ethereum_spec_tools/evm_tools/t8n/cli.py:39-76,298-383`;
environment `test_types/block_types.py:81-209`; transactions
`transaction_types.py:196-380`; result `client_clis/cli_types.py:381-420`;
result construction `t8n/result.py:54-121`.

| Surface | Prague | Osaka | BPO1 | BPO2 |
|---|---|---|---|---|
| Required/current `env` semantics | `currentCoinbase,currentGasLimit,currentNumber,currentTimestamp,currentRandom,currentDifficulty,currentBaseFee,currentExcessBlobGas,parentBeaconBlockRoot,blockHashes,withdrawals`; parent derivation inputs `parentTimestamp,parentDifficulty,parentBaseFee,parentGasUsed,parentGasLimit,parentUncleHash,parentBlobGasUsed,parentExcessBlobGas` | same | same; fork/blob schedule applies | same |
| Additional accepted `env` fields | `currentBlobGasUsed,slotNumber,ommers,extraData,blockAccessListHash,blockAccessLists`; only in-lane features are consumed | same | same | same |
| `txs` JSON | signed type 0/1/2/3/4 objects: common `type,chainId,nonce`, fee fields, `gas,to,value,input,v,r,s`; type-1 access list, type-2 fee caps, type-3 blob fields, type-4 authorization list | same | same | same |
| `txs` RLP string | **not accepted** by this target (`cli.py:151-166`) | same | same | same |
| Always-emitted `result` | `stateRoot,txRoot,receiptsRoot,logsHash,logsBloom,receipts,rejected,gasUsed,currentBaseFee,withdrawalsRoot,currentExcessBlobGas,blobGasUsed,requests,requestsHash` | same | same | same |
| Conditional `result` | `blockException` on block rejection; PoS lane omits `currentDifficulty`; `blockAccessList` and `blockAccessListHash` are Amsterdam-only; traces/opcode count are opt-in extensions | same | same | same |

Current receipts emit `transactionHash`, `status` (or pre-Byzantium
`postState`), cumulative `gasUsed`, `bloom`, and `logs`
(`t8n/result.py:28-52`). This is broader than the pinned oracle: it emits
`blobGasUsed`, receipt logs, and status; its CLI rejects RLP `txs`.

### Emitted versus consumed

The framework builds the fixture header from `result.model_dump` while
explicitly excluding `blob_gas_used` and `transactions_trie`, and
independently computes them (`specs/blockchain.py:890-1042`). It consumes
post-state allocation, roots/header fields, accepted receipts, rejected
index/errors through the mapper, and requests/requests hash. It does **not**
consume `blobGasUsed` or `txRoot`. Block access lists are consumed only
outside this lane.

The comparison `mainnet` checkout has the same Prague–BPO2 consumed surface
and the same explicit blob/trie exclusions
(`specs/blockchain.py:664-682`). Hence no identified consumed surfaces
conflict. The pinned oracle predates EEST, so it has no competing `fill`
consumer surface; it remains an emission-only target and omits `blobGasUsed`.

## Anchor, cost, and decision

**Recommended gate anchor:** `forks/amsterdam`
**`9d6e6f8352a0f76e7e8803722d1a2798fa4f0a96`**, because current `fill`
actually defaults to that checkout's EELS implementation.

**Compatibility set:** that anchor and `mainnet`
`7b8124a77280edaaad877128937b71a1e3a7ebc5` simultaneously, for the consumed
Prague–BPO2 surface. There is no real either/or conflict.

Selecting this non-pinned anchor costs: a separately pinned checkout and venv;
a conformance-target entry in `scripts/sources.json`; target-generated
Step 4 goldens; implementation of the current field table
(`blobGasUsed`, receipt logs/status, no RLP tx list); and the EEST
detection/exception-mapper work above. The pinned oracle is cheaper for
goldens but does not anchor the current `fill` workflow.

## NO-GO refresh and Step 5 candidates

**Technical verdict: GO.** The seam remains intact and typed errors express the
required split; all gaps are frontend/orchestration work, not EVM semantics.

**Arc status: HALT for the user’s anchor decision.** The recommended anchor is
not `4198b9c5`, exactly the plan's explicit stop condition. Do not start
Step 2 until the user selects this anchor or directs another one.

Proposed Step 5 corpus: Prague plain state-test transfer; contract call with
logs; parse and execution rejections; multi-transaction rejection-in-the-middle
with a later success; withdrawals; requests; and one each of Osaka, BPO1, and
BPO2 schedule behavior. Drive it through current EELS
`fill --evm-bin <jaune>` and cross-check with a Geth `evm t8n` build that
advertises Prague, Osaka, BPO1, and BPO2. If no such build is available,
choose another registered transition tool and record its exact version.
