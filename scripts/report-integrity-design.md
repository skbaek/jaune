# Integrity arc — Step 1 design report

Re-audit and freeze of the semantic-integrity architecture. Plan: `~/plans/integrity.md`. Executed 2026-07-31 (Asia/Seoul).

This report is the frozen design contract for Steps 2–12. Where it contradicts the plan's planning-time snapshot, **this report wins**; every divergence is in §11. Two Step-1 deliverables landed as committed machine-checkable artifacts and are normative in their own right: `scripts/check-integrity.sh` and `scripts/integrity-allow.txt`.

## 1. Branch point, verified

| Repository | Branch | Created from | Tree |
| --- | --- | --- | --- |
| Jaune | `codex/integrity` | `b0dc4eee6d82e0309321b2350071b20c0e3984a3` | clean |
| Blanc | `codex/integrity` | `5aff61505d02a942fa525ff1bd593f4708f9778d` | clean |

Both are the documentation-only commits on the restructure arc's semantic candidates (`ad7f47ec…` / `ecad8192…`), which remain ancestors. Both on `leanprover/lean4:v4.32.1`. Blanc pins Jaune `ad7f47ec4bd1fa3cd1c4a315174b7361f7960518` in `lakefile.lean`, `lake-manifest.json`, and the Lake checkout — all three agreeing, an ordinary clone, not a symlink. `silence.md`, `blake2f.md`, `restructure.md` all closed green and merged; the sequencing stop condition does not fire.

Baseline gates, each run alone before any edit, all matching the restructure closure scale for scale: `env_doctor` PASS; `env_doctor --mainnet-deep` PASS; `gen_mainnet_manifest --check` PASS; `gen-vector-shards --check` PASS (106/106); `check-hygiene.sh` PASS (0); Python **121 tests** OK; Jaune `lake build` **1,768 jobs**; `check-u256.sh` 21,593/21,593; `--patch` 10/10; `--rlp4` 4/4; `--depth` 67/67 vs baseline; mainnet `smoke` 16/16; `transitions` 13/13 files, 109 cases; Blanc `lake build` **913 jobs**; Blanc `check.sh --no-build` 4/4 exact axiom sets. Sole build diagnostic in either repo is the inherited `Jaune/Types.lean:462` unused-simp warning.

## 2. Post-restructure module layout, re-derived

Closure computed mechanically from `Jaune.lean` by transitive `import Jaune.*` traversal — the same traversal `check-integrity.sh` performs every run. **13 modules**: `Jaune` plus `Basic`, `Types`, `Fork`, `Hash`, `EC`, `BLSConst`, `BLS`, `Machine`, `Precompiles`, `Execution`, `Sufficiency`, `Transaction`. **`ChainStore` and `FixtureException` are outside it**, confirming fixed decision 11 and fixing the P0.6 gate's scope. `ChainStore` → `FixtureException` → `Transaction`; `Main.lean` imports `ChainStore`.

| Module | Imports | Lines |
| --- | --- | ---: |
| `Basic` | Mathlib + `Std.Tactic.BVDecide` | 1,493 |
| `Types` | `Basic`, `Std.Data.TreeMap.Lemmas` | 1,270 |
| `Fork` | `Types` | 891 |
| `Hash` | `Basic` | 560 |
| `EC` | `Types`, `Hash` | 941 |
| `BLSConst` | — | 56 |
| `BLS` | `EC`, `BLSConst` | 574 |
| `Machine` | `Types`, `Fork`, `EC`, `BLS`, `Hash` | 2,602 |
| `Precompiles` | `Machine` | 820 |
| `Execution` | `Precompiles` | 1,296 |
| `Sufficiency` | `Execution` | 3,026 |
| `Transaction` | `Sufficiency` | 1,928 |
| *(outside)* `FixtureException` | `Transaction` | 710 |
| *(outside)* `ChainStore` | `FixtureException` | 263 |

Linear chain from `Machine` onward — that is what makes §6's layering cycle-free. No drift; line counts match the restructure closure exactly.

## 3. Entry points, construction paths, validation order

### 3.1 Entry points — all in `Jaune/Transaction.lean`

`Sufficiency.lean` references none of them.

| Entry point | Line | Private | Signature tail | Delegates to |
| --- | ---: | :---: | --- | --- |
| `stateTransitionWith` | 1225 | no | `ForkRules → BlockChain → Block → Except String BlockChain` | *(implementation)* |
| `stateTransitionAt` | 1247 | no | `Fork → …` | `f.rules` then `…With` |
| `stateTransitionUsing` | 1253 | no | `ChainConfig → …` | `cfg.rulesAt hdr.timestamp` then `…With` |
| `stateTransition` | 1262 | no | `BlockChain → Block → …` | `…With pragueRules` |
| `rlpToBlock` | 1366 | no | `Bytes → Except String (Block × B256)` | — |
| `checkBlockRlpSize` | 1383 | no | `BlockLimits → Nat → Except String Unit` | — |
| `addBlockToChain.go` | 1634 | **yes** | `ForkRules → BlockChain → Block → B256 → Nat → Except String (BlockChain ⊕ String)` | — |
| `addBlockToChainWith` | 1652 | no | `ForkRules → BlockChain → Bytes → …` | `rlpToBlock` then `.go` |
| `addBlockToChainAt` | 1662 | no | `Fork → …` | `f.rules` then `…With` |
| `addBlockToChainUsing` | 1668 | no | `ChainConfig → …` | `rlpToBlock`, `cfg.rulesAt`, `.go` |
| `addBlockToChain` | 1678 | no | `BlockChain → Bytes → …` | `…With pragueRules` |

Four `rfl` identities Steps 2 and 10 must preserve: `stateTransition = stateTransitionWith pragueRules` (1689); `stateTransitionAt .prague = stateTransition` (1692); `addBlockToChain = addBlockToChainWith pragueRules` (1695); `addBlockToChain = addBlockToChainAt .prague` (1699).

### 3.2 P0.1 confirmed — the configured chain ID is inert

Neither `…Using` reads `cfg.chainId`. **`ChainConfig.chainId` (`Fork.lean:415`) has zero non-`#guard` readers in the repository** — only mentions are `Fork.lean:799` and `:863`. Execution's chain ID comes from `BlockChain.chainId`:

```
fixture JSON genesisBlockHeader.chainId (default 1)   Main.lean:302-305
  → BlockChain.chainId                                Main.lean:313
  → carried forward unchanged by every transition     Transaction.lean:1240
  → BenvStat.chainId                                  Transaction.lean:1170
  → legacy EIP-155 sender recovery                    Transaction.lean:259
  → typed-transaction chain-ID check                  Transaction.lean:265
  → EIP-7702 authorization applicability              Execution.lean:1242
  → CHAINID opcode                                    Machine.lean:1988
```

### 3.3 Validation order — FROZEN

`addBlockToChainWith` / `…At` / `addBlockToChain`: (1) *(`…At` only)* `f.rules`, **before** decode; (2) `rlpToBlock` — outer RLP structure (1367) → `BLT.toExStrBlock` (1369) → canonical re-encode byte comparison (1371); (3) header-hash evidence check (1637), **`.error` channel**; (4) `checkBlockRlpSize` EIP-7934 (1642), `.inr`; (5) `stateTransitionWith` (1646), `.inr`; (6) `.ok (.inl chain')` (1649).

`addBlockToChainUsing`: decode (1670) → `cfg.rulesAt` (1671) → steps 3–6. Rules lookup is **after** decode here and **before** it in `…At`; the asymmetry is forced — the timestamp lives in the decoded header.

`stateTransitionWith` (1225): `validateHeader` (1227) → ommers (1228) → `initBenv` (1229) → `applyBody`, where `decodeTx` runs on `.inl` entries (1230 → 1104) → computed roots/bloom/requests (1231–1236) → `stateTransitionChecks` (1237) → `appendBlock` carrying `ch.chainId` (1240).

`validateHeader` (`Execution.lean:1010`): parent lookup → parentHash (all-zero separate) → `calculateBaseFeePerGas` (runs `checkGasLimit` internally) → excessBlobGas → gasUsed ≤ gasLimit → baseFeePerGas → timestamp → number → extraData → difficulty → header nonce → ommersHash.

`stateTransitionChecks` (1130): blockGasUsed → txsRoot → stateRoot → receiptRoot → bloom → withdrawalsRoot → blobGasUsed → requestsHash.

**Frozen.** Step 2 inserts the config/context check strictly before step 1 of the import path. Step 5's unsupported-era check runs after full canonical decode but before step 4. Nothing else moves.

### 3.4 The `.go` shape and its tautological check

`.go` takes decoded block, header hash, and original RLP length as **three independent arguments**, as P0.3 describes. Its first act (1637) rejects a block whose recomputed header hash differs from the supplied one. **That check is tautological at every in-tree call site**: both callers pass exactly the hash `rlpToBlock` just computed from the same block, so the inequality is never true. The independent-evidence design its docstring describes is not realised. Step 5 replaces the three arguments with the canonical envelope and derives both values from it, removing the tautology rather than preserving it.

### 3.5 Construction paths

| Type | Line | Shape |
| --- | ---: | --- |
| `Withdrawal` | `Machine:85` | `globalIndex`/`validatorIndex : UInt64`, `recipient : Adr`, `amount : B256` |
| `Header` | `:91` | 21 fields; `bloom : Bytes` **unconstrained**; `requestsHash : Option B256` |
| `Tx` | `:141` | `r`/`s` raw `Bytes`; `v : Nat`; `type : TxType` |
| `Block` | `:151` | `txs : List (Bytes ⊕ Tx)` |
| `BlockChain` | `:157` | `blocks : List Block`, `state : State`, `chainId : UInt64` |
| `ForkRules` | `Fork:161` | 8 fields; `Inhabited := ⟨pragueRules⟩` at 264 |
| `ChainConfig` | `Fork:414` | `chainId : UInt64`, `activations : List ForkActivation` |

**No smart constructor, `default`, or `Inhabited` instance exists for `Header`, `Block`, `Tx`, `Withdrawal`, or `BlockChain`.** Every value comes from a decoder or an explicit record literal — so Step 5 has no constructor surface to deprecate, only one to add.

Decoder-produced: `BLT.toExStrHeader` (`Execution:810`), `BLT.toExStrWithdrawal` (`Transaction:1266`), `BLT.toExStrTx` (1292), `Bytes.toExStrTx` (757), `BLT.toExStrBlock` (1330). Hand-built non-test: `Main.lean:137–159` (genesis `Header` from JSON, **not** decoder-validated), `:291` (genesis `Block`), `:309–314` (genesis `BlockChain`), `:459` (`BenvStat`). All else is `private` guard material. `scripts/*.lean` construct none of these.

### 3.6 The retained-history window, measured

```lean
def appendBlock (blks : List Block) (blk : Block) : List Block :=
  (blk :: blks.reverse.take 254).reverse            -- Transaction.lean:1218
```
**Retention is exactly 255**: the 254 newest plus the new one.

```lean
def getLast256BlockHashes (chain : BlockChain) : List B256 :=
  match chain.blocks.reverse.take 255 with          -- Transaction.lean:1109
  | [] => []
  | block :: blocks =>
    let hash : B256 := (Header.toBLT block.header).toBytes.keccak
    let hashes : List B256 := (block :: blocks).map (fun x => x.header.parentHash)
    (hash :: hashes).reverse
```

Result, oldest-first: `[oldest.parentHash, …, tip.parentHash, keccak(tipHeader)]`. Length `1 + min 255 n`; maximum **256**; `[]` on an empty chain. **Only the tip's hash is recomputed; every other entry is a trusted `parentHash` field.** The list reaches 256 from 255 retained blocks precisely because the oldest retained block contributes its `parentHash` as well as being in the map — confirming the plan's suspicion exactly.

Consumers: `applyBody:1096–1101` takes `blockHashes.getLast?` for the EIP-2935 history system transaction, failing `"ERROR : block hashes is empty"` on an empty chain; `BLOCKHASH` (`Machine:2150–2162`), window `blockNumber < number ≤ blockNumber + 256`, index `blockHashes.length - (number - blockNumber)`, default `0`.

### 3.7 `ChainStore`

`init` (`:53`) and `insert` (`:67`) both take a **caller-supplied key**; `insert` never calls `tipHash?` and never compares. Claimed invariant 1 (key = keccak of tip header) is a comment, enforced only by a `#guard` at `:217–218` and externally by `Main.lean:295–297` happening to verify the genesis hash first. Invariants 2 and 3 *are* structurally enforced: `addResult`'s `.error` branch (`:99`) is literally `store`, and `findParent` takes only a `B256`. `findParent` yields `unknownParentZeroTag` for the all-zero hash and `unknownParentTag` otherwise; `findLast` deliberately carries **no** canonical tag so a miss cannot score as an expected block exception. Step 6 preserves both.

### 3.8 `Main.lean` genesis and JSON prestate

**The genesis prestate root is never checked.** `Main.lean` verifies the genesis header hash (295–297), compares `genesisRLP` against a re-encoding of a hand-built block (299–301), then installs `preState` unchecked (307–314). No `preState.root = gbh.stateRoot` guard exists. **`genesisRLP` is never decoded** — only compared against a self-re-encoding, exactly the weakness P0.2 item 6 names.

**A second independent chain ID** at `Main.lean:433`: `(t.chainConfig 1).validate` uses literal `1` while the run uses the fixture's ID (302–305, 313, 318, 192). Benign only because `validate` ignores `chainId`. Step 2 removes it.

| Quantity | Site | Converter | Behaviour |
| --- | --- | --- | --- |
| storage key | `Main:71–74` | `Bytes.toB256` (`Basic:974`) | shift-fold, keeps low 256 bits |
| storage value | `:73–74` | `Bytes.toB256` | same |
| balance | `:79` via `toIoB256P` | `Bytes.toB256` | same |
| nonce | `:80` via `toIoB64P` | `Bytes.toUInt64` (`Basic:598`) | `pack 8`, keeps **rightmost 8 bytes** |
| code | `:81` | `toIoBytes` | none |

Strict `toIoB64` (exactly 8) and `toIoB256` (exactly 32) already exist and already reject. The `P` pair exists to accept *short* values and accepts over-long ones by truncation as a side effect. Step 3 adds width-checked decoders keeping short-value acceptance and rejecting over-long. JSON quantity syntax is not RLP minimal-scalar syntax — share the width conversion only, **no leading-zero rule**. Storage normalisation at `:86` already folds through `Stor.set`, so zero `pre` slots are not noncanonical today; what is missing is the predicate and theorem, not the behaviour.

### 3.9 Fork configuration and divisors

`ChainConfig.validate` (`Fork:446`) rejects an empty schedule and requires `first.timestamp = 0` (**451–454**, the rule P0.5 removes); `validateSteps` (428) requires strictly forward timestamp (432) and fork index (437). `validate` reads only `activations`. `forkAt?` (459) does not validate and takes the *last* activation at or before the timestamp, so the activation block runs the new rules. `forkAt` (465) validates then selects; given `validate`, its `none` branch is currently **unreachable** — exactly the branch P0.5 turns into `unsupportedEra`.

`mainnetChainConfig` (509) puts `⟨.prague, 0⟩` first while `mainnetPragueTimestamp = 1746612311` (491) is kept for provenance and cross-checked at `:801`. **Documented, not accidental**, and the only place the schedule deliberately disagrees with mainnet history. No in-tree consumer outside `#guard`s.

| Constant | Site | Role |
| --- | --- | --- |
| `baseFeeUpdateFraction` | `Fork:87` | **divisor** in `fakeExp` (`Machine:1430`); no zero guard |
| `elasticityMultiplier` = 2 | `Machine:565` | divisor, `Execution:989` |
| `gasLimitAdjustmentFactor` = 1024 | `Machine:566` | divisor, `Execution:946` |
| `baseFeeMaxChangeDenominator` = 8 | `Machine:568` | divisor, `Execution:1000, 1007` |
| `blob.max` | `Fork:85` | divisor on the EIP-7918 branch, `Execution:920` |
| `blob.max - blob.target` | — | `Nat` subtraction; inverted schedule silently yields 0 |
| `gasPerBlob` = 2^17 | `Machine:513` | multiplier |
| `gasLimitMaximum` = 2^63 | `Execution:931` | absolute bound, tested first |

**`BlobSchedule.Valid` must require at minimum `baseFeeUpdateFraction > 0`, `target ≤ max`, and `max > 0`.** The latter two are additional to the plan's stated minimum, recorded as an in-scope refinement: both are already assumed by the EIP-7918 branch's arithmetic.

## 4. State, storage, canonicality

`State`/`Stor` are `Std.TreeMap` aliases. `State.set` erases an exact `Acct.nil`; `Stor.set` erases a zero slot. Both canonicalise normal writes; direct map construction bypasses both. `Acct.Empty` exists and is **not** the right predicate — an account with storage is not the representational default even at zero code/nonce/balance. **Step 3 uses `account ≠ Acct.nil`, never `¬ account.Empty`.** `State.root` serialises the stored entry, so identical EVM-level reads can give different roots — which is why canonicality is a commitment-level property and why **`State.root` may not be changed to conceal noncanonical data**.

```lean
def Stor.Canonical (s : Stor) : Prop :=
  s.toList.All (fun entry => entry.2 ≠ 0)

def State.Canonical (st : State) : Prop :=
  st.toList.All (fun entry => entry.2 ≠ Acct.nil ∧ entry.2.stor.Canonical)
```

Finite `toList` traversal, hence decidable without quantifying over the key type. Step 3 proves equivalence to the lookup characterisations proofs use. Do not obtain "decidability" by quantifying over every `B256`/`Adr` and hoping Lean infers finiteness.

Preservation ladder owed by Steps 3–4, with real premises: empty maps; `State.set` (assuming the inserted account's storage is canonical); `State.setStor` (assuming its storage input is canonical); destruction, balance, nonce, code, storage, transient helpers; a frame invariant covering current state, `BenvStat.origState`, and **every saved parent/rollback state**; step/frame/message execution including restoration; transaction processing and `applyBody`; successful block transition. **`Blanc.State.Inv` must not absorb this** — carry it as the orthogonal checked-chain invariant (fixed decision 10, P0.4 item 5).

## 5. Frozen checked wrappers and `ValidContext`

```
ValidContext ch := ch.blocks ≠ [] ∧ ch.state.Canonical
                 ∧ ch.RetainedHistoryValid ∧ ch.TipStateAgrees
```

**`RetainedHistoryValid`, settled against §3.6.** Because `getLast256BlockHashes` recomputes only the tip and reads everything else from trusted `parentHash` fields, the predicate states the linkage as a hypothesis about those fields: (1) consecutive block numbers across the retained suffix; (2) `next.header.parentHash = keccak (Header.toBLT prev.header).toBytes` for every adjacent retained pair; (3) wire-representable retained headers (§7); (4) retention of at least `min 255 n`, so §3.6's window formula holds. Without (2) the BLOCKHASH theorem is unprovable — which is why the plan makes history mandatory. Step 6 owes: for `blockNumber < number ≤ blockNumber + 256`, `getLast256BlockHashes` returns that block's true header keccak, **including early-chain and truncated-window cases**.

```lean
structure CheckedBlockChain where
  val   : BlockChain
  tip   : Block
  tip_is_last     : val.blocks.getLast? = some tip
  retainedHistory : val.RetainedHistoryValid
  canonicalState  : val.state.Canonical
  tipStateRoot    : val.state.root = tip.header.stateRoot

structure ConfiguredChain where
  config        : ChainConfig
  chain         : CheckedBlockChain
  validSchedule : config.Valid
  chainId_eq    : config.chainId = chain.val.chainId

structure CanonicalBlock where
  raw       : Bytes
  block     : Block
  decoded   : strictDecodeBlock raw = .ok block
  canonical : block.toBLT.toBytes = raw
```

Explicit `tip` + `tip_is_last` resolves the nonempty-tip dependency: **no partial projection, no `get!`, no `Fin` juggling**. Nonemptiness is implied, so it needs no separate field. `CanonicalBlock` constructors stay private/opaque — only the strict decoder and checked smart constructors are exported. `raw` is retained because EIP-7934 depends on the **supplied** size; re-encoding is evidence of canonicality, never a substitute.

`BlockChain.check` defensive order, frozen: nonempty → state canonicality → retained-history validity → compute the canonical state's root and compare with the tip. Empty-chain agreement must **not** be vacuously true and then executed.

## 6. Frozen error-layer placement

| Layer | Frozen module | Justification |
| --- | --- | --- |
| `ChainContextError`, `SupportError` | **`Fork.lean`** | first producers `validate`/`forkAt`/`rulesAt` at `Fork:446/465/475`; `Fork` imports only `Types` |
| `DecodeError` | **`Machine.lean`** | strict field decoders at `Machine:985–1050`, tag vocabulary `:954–981`; `BLT` is `Basic:1325` but no `Basic` declaration produces a decode *error* |
| `ExceptionalHalt`, revert, `InternalError` | **`Machine.lean`** | carrier `abbrev Execution := Except (String × Devm) Devm` at `:1174`; `Meta.error` `:1069`; `isExceptionalHalt` `:757` |
| **precompile/crypto reasons** | **`Machine.lean`** — *not* `Precompiles.lean` | **corrects the plan** |
| `TxValidationError` | **`Transaction.lean`** | producers there; `transactionExceptionTags` (`Machine:806`) is a string table that moves with the type |
| `BlockValidationError` | **`Transaction.lean`** | ditto `blockExceptionTags` (`Machine:913`) |
| `ImportFailure`, `BlockRejection`, `ImportOutcome`, `RawImportFailure` | **`Transaction.lean`** | entry points all there |

**Why precompile reasons cannot live in `Precompiles.lean`.** Import order is `Machine ← Precompiles ← Execution`. `PrecompResult` (`Precompiles:7`) carries its failure as a `String`, and that failure must inhabit the VM carrier declared **upstream** at `Machine:1174`. A typed precompile reason declared in `Precompiles.lean` could not be a constructor of the Machine-level halt type without a cycle. Resolution: the *reason type* is a constructor family of the Machine-level halt error; `Precompiles.lean` keeps only precompile-specific helpers and renderer arms. **The plan's Step-1 prompt says "precompile errors in `Precompiles.lean`" — that is the one placement instruction this report overrides.** It is a placement correction, not the cycle the plan lists as a stop condition: the dependency graph is exactly what `restructure.md` produced. No layer needs a type from a module that imports it. **No cycle exists.**

## 7. Structural predicates and the staged typed-tx rule

A *lift* of existing decoder checks, not new policy:

- **`Header.WireWellFormed`** — `bloom.length = 256`; every `Nat` scalar in U256 range; `blobGasUsed`/`excessBlobGas` in U64 range.
- **`Tx.WireWellFormed`** — fee/gas/value/parity fields in wire ranges; canonical signature scalar bytes (`r`/`s` are raw `Bytes`, so minimality is a real obligation); type/envelope agreement; recursively well-formed authorisations and access-list material.
- **`Withdrawal.WireWellFormed`** — notably `amount < 2^64`, though the field is `B256`.
- **`Block.RlpCanonical`** — header, ommers, withdrawals, outer-list structure.

Kept **distinct** from fork/context validity (fixed decision 3). **Staged rule, frozen:** a canonical outer block may contain *opaque malformed typed-tx bytes* until the existing decode stage inside `applyBody`. Step 5 must **not** eagerly decode typed transactions before EIP-7934 or header checks — that changes which error wins. The envelope ADT's legacy-list constructor carries strict wire/decode evidence plus the decoded `Tx`; its typed constructor carries opaque bytes. **No direct trusted `.inr Tx` survives** — the bypass is `decodeTx (.inr tx) := .ok tx` at `Transaction:937`.

## 8. Producer/channel matrix

**Scale.** `Except String` by module: `Transaction` 55, `BLS` 12, `Execution` 11, `Machine` 9, `Fork` 7, `ChainStore` 4, `Precompiles` 3, `Main` 2, `FixtureException` 2; zero in `Types`, `Sufficiency`, `Hash`, `EC`, `Basic`, `BLSConst`. The gate's R4 counts **169 normalised rows**.

**The vocabulary is already one-producer-per-reason** — the most consequential finding for Steps 9–10:

| Vocabulary | Site | Size |
| --- | --- | ---: |
| `isExceptionalHalt` list | `Machine:757–772` | 13 |
| `transactionExceptionTags` | `Machine:806–819` | 20 (`#guard`ed distinct) |
| `blockExceptionTags` | `Machine:913` | ~17, documented `:836–911` |
| `rlpTags` | `Execution:8–22` | 7, `#guard`ed prefix-free |
| `invalidChainConfigTag` | `Fork:420` | 1 |

**The typed ADTs are a mechanical lift of these lists, not a redesign.** `#guard`s at `Execution:15–22` already assert the strict tags are distinct, prefix-free, and unreadable as the old generic categories — those become constructor-distinctness facts for free.

```lean
def hasErrorType (err errType : String) : Bool :=
  err = errType || String.isPrefixOf (errType ++ " : ") err   -- Machine.lean:747
```
Every semantic string branch reads through this, `isExceptionalHalt` (`:757`), or `isBlockException` (`:924`), plus private `errOf`/`hasTag` (`Execution:24/28`, `Transaction:27`) and `importErrOf`. Direct prefix matching also at `Precompiles:735/738/767/770`. These control exactly what P0.7 names: zero-gas/rollback, revert semantics, EIP-7702 invalidation, precompile conversion, fixture classification.

**The channel invariant is already violated.** `addBlockToChain*` returns `Except String (BlockChain ⊕ String)`, intended as *outer = context/support, inner-right = candidate rejection*. **That does not hold.** All seven strict RLP failures and the header-hash check reach the **outer `.error`** channel via `rlpToBlock` (`Transaction:1367–1374`, `:1637`), yet the runner classifies them as invalid-candidate outcomes. Two tx-validation checks ride the same outer channel. `checkBlockRlpSize` and all of `stateTransitionWith` correctly use `.inr`. `Main.lean:191` then **collapses both channels**, which is why this never produced a visible misclassification — the runner recovers the distinction from the *string*, precisely the defect P0.7 exists to remove. **Binding on Step 10:** move each strict-decode reason deliberately per EELS semantics, reason by reason, recording the decision — never preserve today's accidental nesting. Preserve final verdict and precedence. No producer moves across the boundary by intuition.

**Template census — REGENERATE, DO NOT TRANSCRIBE.** ~67 distinct templates exist. Per plan §5, Step 9/10 must regenerate mechanically from source immediately before changing producers, capture every fixture-observed *actual* message from a full legacy + current-mainnet run, and commit those as golden strings. A hand-copied list would be stale by use. `check-integrity.sh --list` already emits the per-site R4 inventory those goldens must cover. `FixtureException.classify` parses **two** things: the fixture's external `expectException` (legitimate, stays) and *our own* rendered messages (the defect, goes). After Step 10 typed reasons map directly, and unknown/internal/support/context errors **fail closed**.

## 9. Partiality inventory and residual policy

Machine-checked as `scripts/integrity-allow.txt`; counts generated, not transcribed.

**Absence checks all hold.** `partial def`, `implemented_by`, `dbg_trace`: **zero** in `Jaune/*.lean`, `Jaune.lean`, `Main.lean`. `silence.md` held. The only two `partial def`s in the repo are `exprSize` and `zetaAll` in `scripts/flatten-pilot.lean`, a Lean metaprogram over `Expr` — neither library code nor in any closure, correctly out of scope. R1 asserts this **outright, no allowlist**; the gate refuses an allowlist carrying an R1 row.

**Panics — exactly two, both in the closure:** `Machine:1424` `fakeExpAux` `panic! "error : fuel exhausted in fake exponentiation"` (Step 7); `Hash:259` `KECCAK.Array.modify!` `panic "Array.modify! out of bounds"` (Step 8). Nothing outside the closure panics.

**Bang operations — 294 raw, 158 normalised.** By module: `Hash` 139, `Precompiles` 129, `BLS` 8, `EC` 4, `Basic` 5, `Machine` 3, `Execution` 2, `Transaction` 2. The twelve non-crypto sites are exactly P0.6's sub-items:

| Site | Declaration | P0.6 item |
| --- | --- | --- |
| `Machine:2393` | `jumpable`, `cd.get! k` | 2 |
| `Machine:2384` | `noPushBefore`, `cd.get! k` | 2 |
| `Machine:1405` | `ByteArray.getInst`, `code.get! pc` | 2 |
| `Execution:108` | delegation address, `.toAdr?.get!` | 3 |
| `Execution:742` | first byte of fixed hash, `h.toBytes[0]!` | 3 |
| `Transaction:227` | versioned hash, `bvh.toBytes[0]!` | 3 |
| `Transaction:1053` | system-call error, `systemTxOutput.error.get!` | 3 |
| `EC:616` | `twist`, four coefficient reads from a possibly short list | 4 |
| `Basic:588–589` | `Bytes.toUInt16`, `v[0]!`/`v[1]!` after `pack 2` | 4 |
| `Basic:1261` | `ByteArray.sliceD`, guarded by `m < xs.size` | 4 |
| `Basic:1254` | `Array.copyD`, `Array.set!` | 4 |
| `Basic:1458` | `List.splitToArray.aux`, `Array.set!` | 4 |

**Two refuted plan premises.** **(a) Nothing is `private`.** No bang-op site sits inside a `private` declaration. `Precompiles.lean` and `BLS.lean` have **zero** `private` declarations; `Hash.lean`'s only two (`rolc`, `round1600`) contain none. The keccak/SHA-256/RIPEMD-160/Blake2 kernels are public `Jaune.KECCAK.*`, `Jaune.SHA256.*`, `Jaune.Blake2.*`, reachable by any importer — internal by convention only. P0.6 item 4 permits "a **private** optimized array kernel behind a checked wrapper", so **Step 8 must privatise these or give them fixed-size inputs.** A wrapper over an exported raw kernel is not compliant — that is exactly the "public helper accepting an arbitrary short array" the plan requires rejected or totalized. **(b) `Blake2.g` retains four `Array.set!`.** `Blake2.Vec` is a sixteen-field scalar structure and `Blake2.roundVec_toArray` / `Blake2.roundsVec_toArray` exist with axiom set exactly `[propext, Quot.sound]`, as promised. But `Blake2.g` still has four `Array.set!`. They are **off the execution path** and retained because the equivalence theorems mention them — not dead code, as the plan says. The plan's stronger claim that `blake2f.md` "replaces `Blake2.g`'s four `Array.set!` calls" is **false as stated**. Not a hazard, not a stop condition: `Array.set!` is `Array.setIfInBounds`, hence **total**. Step 8 must not reopen the kernel.

**Severity triage.** `Array.set!` = `setIfInBounds`: **total**; the objection is allocation cost and an unexpressed invariant, not partiality. `a[i]!`, `ByteArray.get!`, `Option.get!`: **do panic** (stderr + `default`). `Jaune.List.slice!` (`Basic:410`): total despite the name; zero-pads via `takeD`. **The single genuinely unguarded, reachable, attacker-influenced site is `jumpable` (`Machine:2393`)**: `cd.get! k` where `k` is a popped stack value with no bound relative to `cd.size`. An out-of-range `JUMP` emits a real panic line on stderr and returns `default = 0`; the *verdict* stays correct (0 is not `JUMPDEST`, so `InvalidJumpDestError`), but a partial read is live on a consensus path. `noPushBefore` and `ByteArray.getInst` are guarded by explicit `< size` tests; both `Option.get!` sites are guarded by validity/`isSome` tests immediately above.

**Residual-partiality policy, FROZEN.** (1) A valid checked input reaches **no** panic/default branch. (2) An optimized kernel may retain a low-level operation only behind a formal size/bounds interface **and** an exact allowlist row naming its declaration, its checked/fixed-size wrapper, and its bounds/size theorem — both real declarations. (3) No carve-out for `partial def` or `implemented_by`, ever. (4) The allowlist is a **shrink-only budget**, `# pending-budget: 329` today; a step discharging a row deletes it (or rewrites it `KEEP`) and lowers the budget in the same commit. That is what makes "the list cannot grow without the static gate failing" mechanical. (5) Full reference-algorithm equivalence for keccak is a **separate** target; `~/plans/keccak-proof-proposal.md` records that `f1600` does **not** yield to Blake2's unfolding recipe. Step 8 must not assume otherwise.

## 10. Blanc, the downstream proof client

**Present** in `Blanc/Solvent.lean`: `BlockChain.ReachUsing`, `stateTransitionUsing_preserves_solvent`, `addBlockToChainWith_preserves_solvent`. **Absent**, as expected: `BlockChain.Reach.toReachUsing`, `chainUsing_inv_solvent`, `addBlockToChainUsing_inv_solvent` — recorded history from blanc `692224c`, **not drift**, a finding rather than a stop condition; Step 11 owns the response. **`ReachUsing.refl` imposes no relationship between config and chain**, so a zero-step mismatched reach exists — confirming P0.1 item 6 exactly; the inductive is additionally **dead** (nothing constructs or eliminates it). **Blanc inspects no error string anywhere** — the VM error's `String` component is always quantified over or preserved opaquely, and Blanc has zero `Except String`, so retyping the carrier breaks Blanc only on the type, which is the mechanical part. The four protected theorems audit under their `Blanc.`-prefixed names with exactly `[propext, Classical.choice, Quot.sound]`. Step 11 adds a fifth audited row, `stateTransitionUsing_preserves_solvent`; growing the audited set is sanctioned, shrinking is not, and the original four keep the stronger textual guarantee. Blanc unfolds Jaune transition/import definitions in its solvency proof, so **Jaune owes inversion lemmas** (fixed decision 10); adding them is in scope, relocating declarations is not.

## 11. Divergences from the plan's snapshot

Each overrides the plan text; none is a stop condition.

1. **Precompile error placement** — `Machine.lean`, not `Precompiles.lean` (§6).
2. **No kernel is `private`** (§9) — constrains how Step 8 discharges 152 rows.
3. **`Blake2.g` retains four `Array.set!`** (§9) — harmless, off-path, but the plan says they were removed.
4. **`.go`'s hash check is tautological** (§3.4).
5. **The outer/inner channel invariant is already violated** (§8) — all seven strict RLP failures use the outer channel; `Main.lean:191` collapses both.
6. **`BlobSchedule.Valid` needs `target ≤ max` and `max > 0`** beyond the plan's `baseFeeUpdateFraction > 0` (§3.9).
7. **`ChainConfig.chainId` has zero non-`#guard` readers** (§3.2) — the P0.1 defect is cleaner than described; no partial use to preserve.
8. **GATES.md's Python test count was stale** (110 → 121), corrected while registering the new gate.

## 12. Scope check

No semantic change. No opcode behaviour, gas constant, gas charge timing, fork activation fact, trie commitment, cryptographic algorithm, error text, or validation order altered. No baseline, exclusion list, manifest, timeout, or protected theorem weakened or rebased. No `sorry`, `admit`, new axiom, or `ofReduce*`. No history rewrite, force-push, local-path Blanc dependency, or protected-branch merge. `~/plans/todo.md` was neither read as instruction, staged, committed, nor modified.
