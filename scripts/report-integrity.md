# Integrity arc — closure report

Plan: `~/plans/integrity.md`. Step 12 (closure, reports, and merge handoff),
executed 2026-08-01 (Asia/Seoul) by the auto-mode relay (Claude Code / Sonnet 5
/ high). Synthesizes `scripts/report-integrity-design.md` (Step 1) and
`~/plans/reports/integrity-step3.md` through `integrity-step11.md`.

**Exact candidates, verified clean and pushed at report time:**

| Repository | Branch | Tip | Tree |
| --- | --- | --- | --- |
| Jaune | `codex/integrity` | `739fa42d23c91d3add313437dde5648cf182428b` | clean |
| Blanc | `codex/integrity` | `98376a274e57914e647cb6288060459a42b24324` | clean, pins Jaune `739fa42d…` in all three locations |

**This report documents these tips. Neither branch is merged into `main` by
this report; merge is the user's decision alone (Global stop conditions /
Final closure checklist).**

## 1. Final checked/wire/raw API and validation-order diagram

Entry points are unchanged in name and type from the design report's §3.1
inventory — this was a deliberate constraint (see §11, Deviations) — but the
checked layer added around them is now the recommended path.

```
Wire bytes (untrusted)
  │
  │  rlpToCanonicalBlock : Bytes → Except DecodeError CanonicalBlock
  │    proves: strict-decoder image AND block.toBLT.toBytes = raw
  ▼
CanonicalBlock { raw, block, decoded, canonical }  (private ctor, checked smart-constructor only)
  │
  │  BlockChain.check : BlockChain → Except ChainContextError CheckedBlockChain
  │    order: nonempty → canonicality of state → retained-history validity →
  │           canonical-state-root vs tip header comparison
  ▼
CheckedBlockChain { val, tip, tip_is_last, retainedHistory, canonicalState, tipStateRoot }
  │
  │  ChainConfig.checkChainId : ChainConfig → BlockChain → Except ChainContextError Unit
  │    (runs BEFORE decode on the import path; context/config failure, never
  │    an inner invalid-block result)
  ▼
ConfiguredChain { config, chain, validSchedule, chainId_eq }
  │
  │  repeated execution: addBlockToChainCanonicalE / stateTransitionE / …
  │    reuse the CheckedBlockChain witness; no redundant trie-root recompute
  ▼
CheckedBlockChain'  (successor snapshot, canonicality + tip-root re-derived
                      from the existing child-root check, not recomputed)

Raw compatibility layer (unchanged names, Blanc's protected-theorem surface):
  stateTransitionWith/At/Using, stateTransition,
  addBlockToChainWith/At/Using, addBlockToChain, rlpToBlock
    — each validates chain-ID/schedule context up front (P0.1) but does
      NOT itself call BlockChain.check per call (see §11.2); build and
      store a CheckedBlockChain once instead of repeating raw calls.
```

Validation order at the raw import entry points, frozen since design report
§3.3 and re-confirmed unchanged this arc: `(…At only)` `f.rules`/`cfg`
context+schedule before decode → `rlpToBlock`/`rlpToCanonicalBlock` structural
decode → header-hash evidence → `checkBlockRlpSize` (EIP-7934) → transition →
`.ok`. `ChainConfig.checkChainId` was inserted at the very front of both
configured entry points (P0.1), strictly before decode, so a contradictory
caller context is reported as a context failure rather than a candidate-block
verdict.

## 2. The seven P0 findings and their exact fixes

| # | Finding | Fix | Evidence |
| --- | --- | --- | --- |
| P0.1 | `ChainConfig.chainId`/`BlockChain.chainId` could silently disagree | `ChainConfig.checkChainId` runs first at both configured entry points, before decode; `ConfiguredChain` bundles a validated schedule + checked snapshot + ID-equality witness once; `BlockChain.ReachUsing.refl` now requires `cfg.Valid ∧ ch.ValidContext ∧ cfg.chainId = ch.chainId` — no zero-step mismatched reach exists | Steps 2, 11 |
| P0.2 | A `BlockChain` could pair a tip with an unrelated state | `BlockChain.Canonical`/`RetainedHistoryValid`/`TipStateAgrees` → `BlockChain.check` → `CheckedBlockChain`; `ChainStore` derives its key from `checked.tipHash`, cannot be seeded with an independent pair; genesis is strictly decoded and its prestate root checked | Steps 3, 6 |
| P0.3 | Wire-decoded and freely constructed transactions shared one path | `CanonicalBlock` envelope (private ctor) proves the strict-decoder image and exact round trip; `decodeTx (.inr tx) := .ok tx`'s unconditional bypass removed by `TxEnvelope` checked constructors; a direct typed `.inr Tx` cannot be certified through the checked path | Step 5 |
| P0.4 | Canonical state/structural well-formedness were informal | `Stor.Canonical`/`State.Canonical`/`Tra.Canonical` as finite decidable predicates (`≠ Acct.nil`, never `¬ Acct.Empty`) with lookup-characterisation theorems; checked-width JSON prestate decoders (`Bytes.toQuantityB64?`/`B256?`) reject overwide nonce/balance/storage before conversion; `BlobSchedule.Valid`/`ForkRules.Valid` for every named and arbitrary rule record | Step 3 |
| P0.5 | Configured execution did not fail closed before a chain's earliest era | `ChainConfig.validate`'s buggy "first activation must be timestamp 0" branch deleted; `ChainConfig.forkAt` reports typed `SupportError.unsupportedEra (timestamp, floor)` before an unimplemented era; `mainnetChainConfig`'s first activation moved to the real Prague timestamp | Step 2 |
| P0.6 | Non-fuel panic/partial paths existed | `Machine:1424` panic (fakeExp) replaced by well-founded recursion with existence/uniqueness theorems; `Hash:259` (the sole remaining library panic before Step 8) replaced — Keccak/SHA-256/RIPEMD-160 take fixed-size `Vector` inputs, BLAKE2b kernel made private behind a rejecting checked wrapper (`bCompress`); EC twist coefficient extraction corrected (a real bug, not only totalized); library-wide `panic`/`panic!` count is **0** | Steps 7, 8 |
| P0.7 | Strings used as internal semantic discriminants | `ChainContextError`/`SupportError`/`RuleDefect`/`RulesLookupError`/`DecodeError`/`ExceptionalHalt`/`CryptoError`/`InternalError`/`EvmError`/`SettledHalt`/`TxValidationError`/`BlockValidationError`/`ImportFailure`/`BlockRejection`/`RawImportFailure`/`TransitionError` — every core producer constructs one of these directly; `String` remains only at the 56-row external parsing/rendering/compatibility allowlist, shrink-only-gated | Steps 1, 9, 10 |

## 3. Canonicality and preservation theorem census

Bottom-up, each layer discharging its premise from the one below rather than
assuming it:

- **Map layer** (Step 3, `Machine.lean`): `Stor.canonical_iff`, `State.canonical_iff`, `Tra.canonical_iff` (finite lookup characterisations, no key-type quantification); `get_eq_zero_iff`/`get_eq_nil_iff` (on a canonical map, "reads the default" and "is absent" coincide); a preservation theorem per named mutator — `Stor.Canonical.set/.erase`, `State.Canonical.set` (premise: inserted account's storage canonical), `.setStor` (premise: its storage argument canonical), and the *derived* mutators (`destroyAccount`, `setCode`, `setBal`, `addBal`, `subBal`, `incrNonce`, `setStorVal`) discharge that premise automatically from `State.Canonical.stor`; smart constructors `Stor.ofList`/`State.ofList` with canonicality + read-agreement soundness.
- **Result-carrier layer** (Step 4, `Machine.lean`): `Except.CanonicalOn` (generic over the error component), `Execution.Canonical`, `Except.CanonicalSettle` for frame settlement (error channel's saved state *and* transient storage both canonical); compositional bind/map/imp lemmas; instances for every VM primitive (`chargeGas`, `push`/`pop`, `memWrite`/`memRead`, `addLog`, `applyUnary/Binary/Ternary`, …) and every world-changing `Devm`/`Benv`/`Tenv`/`Msg` mutator.
- **Frame/interpreter layer** (Step 4, `Machine.lean`+`Execution.lean`+`Precompiles.lean`): `Rinst.runCore_canonical` (~70 arms), `Jinst`/`Linst.run_canonical`, `applyPrecompResult_canonical`, `Frame.settleMsg`/`Frame.settle` canonical for **both** restoration targets (inner message at `processMessage.settle`, outer message when a create fails its code-deposit charge), `execFueled_run_canonical` by induction on fuel.
- **Transaction/block layer** (Step 4, `Sufficiency.lean`+`Transaction.lean`): `exec_canonical`, `processMessageCall`/`prepareMessage`/`processTransaction`/`processWithdrawalsState`/`applyBody`/`stateTransitionWith_canonical` — axioms exactly `[propext, Classical.choice, Quot.sound]`.
- **Snapshot layer** (Step 6, `Machine.lean`+`Transaction.lean`): `BlockChain.validContext_of_transition` (successful checked transition ⇒ output canonical ∧ tip-root agreement), `getLast256BlockHashes_window`/`_of_mem_retained` (BLOCKHASH correctness from `RetainedHistoryValid`, including the honest depth-256/255-retained boundary case), `validateHeader_links`.
- **Wire layer** (Step 5, `Transaction.lean`): `rlpToBlock_canonical`/`CanonicalBlock.canonical` (`block.toBLT.toBytes = raw`), `CanonicalBlock.decodeTx_inr` (a direct typed `.inr Tx` cannot be certified), `addBlockToChainWith_eq_ok_inl` (import bridge, consumed by Blanc without unfolding the core).

## 4. Error constructor/producer/channel/classification matrix

Read directly from the exact candidate's source (`Jaune/Fork.lean`,
`Jaune/Machine.lean`, `Jaune/Transaction.lean`), constructor-by-constructor,
2026-08-01:

| Type | Constructors | Role |
| --- | ---: | --- |
| `RuleDefect` | 4 | why a fork-rule record is unusable (zero divisor/ceiling, target > max) |
| `ChainContextError` | 5 | schedule/config/ID-agreement failure (`emptySchedule`, `nonIncreasingActivations`, `nonForwardActivations`, `chainIdMismatch`, `invalidForkRules`) |
| `SupportError` | 2 | domain-unimplemented (`unsupportedFork`, `unsupportedEra`) |
| `RulesLookupError` | 2 | sum of the two above, for `forkAt`/`rulesAt` |
| `DecodeError` | 7 | strict-decoder failure reasons (structure, fixed-width, ×2 overflow, leading zeros, withdrawals-not-read, round-trip) |
| `ExceptionalHalt` | 13 | VM halt reasons (stack under/overflow, OOG, modexp limit, invalid opcode/jump-dest, depth limit, static write, OOB read, invalid parameter/contract-prefix, address collision, KZG proof) |
| `CryptoError` | 3 | signature/point/pairing-value failure |
| `InternalError` | 2 | broken implementation invariant (assertion, invariant) — fails closed, never a settled halt, never an expected rejection |
| `EvmError` | 4 | the VM's whole error carrier: `halt`/`revert`/`crypto`/`internal` |
| `SettledHalt` | 2 | what `Meta.error`/`MsgCallOutput.error` can store: `halt`/`revert` (crypto/internal are unrepresentable as a settled halt by construction) |
| `TxValidationError` | 21 | transaction admissibility |
| `BlockValidationError` | 24 | header/post-transition consensus checks |
| `ImportFailure` | 5 | outer/operational import channel (`context`, `support`, `harness`, `internal`, `vm`) |
| `BlockRejection` | 4 | inner/candidate-verdict channel (`transaction`, `block`, `decode`, `senderRecovery`) |
| `RawImportFailure` | 2 | raw-bytes ingress split (`strictDecode`, `operational`) |
| `TransitionError` | 6 | the transition body's working union, later split by `TransitionError.split` into the outer/inner channels above |

Every type has exactly one renderer (`X.render`), and every renderer bottoms
out in `renderTagged tag detail` — the single rendering primitive, so a tag
cannot acquire a second spelling. Golden `#guard`s pin one representative
render per constructor against literal text. `ImportOutcome (chain) := chain
⊕ BlockRejection` is parameterised so the raw-`BlockChain` compatibility path
and the `CheckedBlockChain` checked core share the same shape.

## 5. Renderer compatibility verdicts

Every renderer is byte-identical to its pre-migration text — this is the
central claim Steps 9–10 exist to prove, and it is the reason
`JAUNE_MSG_LOG`/`golden-messages.txt` exist. At Step-10 closure (`4b2171d8`),
both full tiers were run with the capture hook active and their
**distinct observed-message sets were byte-identical to the committed
golden set**: legacy 177/177 (from 296 observations), current-mainnet 648/648
(from 3337 observations) — observation *counts* equal to the pre-migration
multisets, so nothing silently stopped triggering either. Checkpoint 1 of
this step re-ran both full tiers again on the final exact candidate
(`739fa42d`) without the capture hook, since no further producer changed
after Step 10: **2983/2983 legacy classifications and 5100/5100 mainnet
classifications remained baseline-identical**, which is the transitive
confirmation that no renderer regressed between Step 10's golden capture and
the final candidate. No consensus branch compares or prefix-matches a
rendered string anywhere in the closure (`hasErrorType`/`isBlockException`
deleted at Step 10; `FixtureException`'s `matchesSet` classifies on typed
constructors, `parseExpectation` is the sole external-string parser).

## 6. Totality inventory: before/after and every residual allowlist item

`check-integrity.sh`'s pending budget (a shrink-only defect count) over the
arc:

`329 → 322 (Step 7) → 321 (Step 7) → 230 (Step 8) → 218 (Step 8) → 169 (Step 8) → 153 (Step 9) → 92 (Step 9) → 80 (Step 9) → 41 (Step 10) → 10 (Step 10) → 0 (Step 10, held through Steps 11–12)`.

**56 rows remain, all permanent `KEEP` (0 pending), each naming a real
declaration and a real theorem in `scripts/integrity-allow.txt`:**

| Rule | File | Rows | Disposition |
| --- | --- | ---: | --- |
| R3 (raw bang op) | `Jaune/Precompiles.lean` | 43 | `KEEP(wrapper=bCompress, theorem=…)` — the private BLAKE2b compression kernel (`Blake2.g/round/rounds/roundVec/roundsVec`), reachable only through the checked `bCompress` wrapper which rejects `h.length ≠ 8 ∨ m.length ≠ 16`; theorems named per row include `Blake2.roundVec_toArray`, `size_blake2Sigma_get`, `blake2Sigma_lt` |
| R4 (stringly carrier) | `Jaune/Transaction.lean` | 7 | Legacy renderer adapters over the typed cores (`stateTransitionE`, `addBlockToChainCanonicalE`/`…AtE`/`…UsingE`, `rlpToBlockE`) plus one guard-only golden-text probe (`errorText?`) — retained by exact name/type because Blanc's protected `addBlockToChain_preserves_solvent`/`stateTransition_preserves_solvent` quantify over these equations |
| R4 | `Main.lean` | 5 | CLI/JSON/harness string boundaries (`Except.toIO`, `Lean.Json.toString?`, `Option.remove0x`, `getNetwork`, `getTxExMap`) — none is a consensus error channel |
| R4 | `Jaune/FixtureException.lean` | 1 | `parseExpectation` — the sole external-string parser, reads the fixture's own `expectException` label, never a rendered diagnostic |

No R1 row exists or may exist: absence of `partial def`/`implemented_by`/
`dbg_trace` is asserted outright (confirmed 0 occurrences today, independent
of the gate). Library-wide `panic`/`panic!` count is 0 (Step 8; `grep -c
panic` over `Jaune/*.lean` + `Jaune.lean` + `Main.lean`).

## 7. Fake-exponential: definition, theorems, differential evidence

`fakeExpAux` is well-founded recursion on `(num + 1 - i, numAcc)`, replacing
the deleted `Machine:1424` panic. `fakeExpAux_zero`/`_succ` give the
recurrence; `FakeExpSpec` existence and uniqueness
(`fakeExpAux_spec`/`fakeExpAux_spec_unique`, via `fakeExpAux.induct`); public
equations `calculateBlobGasPrice_eq`/`_spec` plus non-evaluating instantiations
at `UInt64.max` and the corpus max `0xfffffffffffe0000`. Axioms of
`fakeExpAux_spec_unique`/`calculateBlobGasPrice_spec`: exactly `[propext,
Quot.sound]` — no `Classical.choice`. The old fuelled worker survives only as
`Option`-valued `fakeExpAuxRef?` with bridge theorems to the new total
definition.

**Differential evidence:** `scripts/check-fake-exp.sh`, 240 generated cases
against the pinned EELS `taylor_exponential` (verified byte-identical to the
implementation at current-mainnet source commit `87aba1a3`), PASS today.
**Corpus scan** (all 5100 full-manifest files): the maximum feasible
`excessBlobGas` reachable by a valid, priced block is `0xe760000` (1851
blobs), covered directly by the 240-case grid against all three canonical
blob-fee fractions; the theoretical maximum `0xfffffffffffe0000` occurs only
in fixtures that are rejected before pricing (invalid-header fixtures),
covered by the non-evaluating theorem instantiation rather than execution.
`baseFeeUpdateFraction = 0` is rejected before calculation by Step 3's
`ForkRules.Valid` machinery, so `RuleDefect.zeroBlobBaseFeeUpdateFraction`
fails closed rather than needing a totality escape hatch in `fakeExpAux`
itself.

## 8. State-root-check count and performance evidence

**Root-computation instrumentation** on the runner path (Step 6, unchanged
since): `preState.root` computed exactly once per fixture case, at genesis
ingress (bound to a local, reused by the fixture comparison, the diagnostic,
and the checked-snapshot proof); `st.root` computed exactly once per block,
inside `stateTransitionWith` — the same child-root value `stateTransitionChecks`
already compares against the header. `BlockChain.check` is never called on
the repeated execution path. **No parent-state root is recomputed for any
checked block.**

**Comparable four-family sweep** (sequential `--no-build`, same machine, LSP
reaped, before `97c0e777` vs after `857f62a8`):

| gate | before | after |
| --- | --- | --- |
| `check.sh --depth` | 12s | 11s |
| `check-mainnet.sh --suite transitions` | 20s | 18s |
| `check-mainnet.sh --suite smoke` | 5s | 4s |
| `check.sh --smoke` | 91s | 92s |
| **total** | **128s** | **125s** |

−2.3%: no regression, far from the 20% remedy threshold — the checked path
does not pay for its own guarantees. Checkpoint 1 of this step re-confirmed
the same relative shape at `--jobs auto` on the final candidate (see §9).

## 9. Fixture and vector verdicts, tied to exact commits/binaries

The Step-12 checkpoint-1 battery (jaune `739fa42d`, blanc `98376a27`) is the
authoritative fixture/vector verdict for these exact candidates: legacy
`--full` 2983/2983 (2978 PASS/5 known FAIL, 485.3s at `--jobs auto`);
mainnet `--suite full` 5100/5100 (320.2s); `--suite prague` 2573/2573;
`--suite osaka` 2514/2514; `--suite transitions` 13/13 (109 cases);
`--suite smoke` 16/16; legacy `--smoke` 174 (173/1); `--bls` 29/29;
`check-ec.sh` 573/573; `check-vectors.sh` 51/51 files + 5/5 controls +
782/782 declared cases; `check-fake-exp.sh` 240/240; `check-u256.sh`
21593/21593; `--patch` 10/10; `--rlp4` 4/4; `--depth` 67/67; Python
unittest 121/121. Every classification matches its committed baseline
exactly — none rebased, none weakened. Environment doctors and the mainnet
manifest check also passed on the exact candidates (`env_doctor`,
`env_doctor --mainnet-deep` over 34,909 archive files, `gen_mainnet_manifest
--check` exact identity, `gen-vector-shards --check` 106/106).

## 10. Blanc pin, protected theorem statements, and the five-row axiom audit

Blanc `98376a274e57914e647cb6288060459a42b24324` pins Jaune
`739fa42d23c91d3add313437dde5648cf182428b` through Lake (all three locations
agreeing, re-verified today). `lake build` 916 jobs green. All five audited
theorems verified today, exactly `[propext, Classical.choice, Quot.sound]`:

```lean
theorem weth_preserves_solvent (wa : Adr) :
    ∀ sevm pre post,
      Exec 0 sevm pre (.ok post) →
      (sevm.currentTarget = wa → some sevm.code.toList = Prog.compile weth) →
      Precond wa sevm pre → Postcond wa sevm post

theorem stateTransition_preserves_solvent (wa : Adr)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state

theorem chain_preserves_solvent (wa : Adr) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state

theorem addBlockToChain_preserves_solvent (wa : Adr)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChain ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state

theorem stateTransitionUsing_preserves_solvent (wa : Adr) (cfg : ChainConfig)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionUsing cfg ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state
```

The first four are textually unchanged from before this arc. The fifth,
`stateTransitionUsing_preserves_solvent`, was added at Step 11 — the
per-transition **configured-chain** solvency result, protecting exactly the
declaration whose absence let the style arc classify
`chainUsing_inv_solvent`/`addBlockToChainUsing_inv_solvent` as dead code and
delete them (`692224c`). Its axiom set was verified with `lean_verify`
**before** wiring (per the plan's HALT gate on this exact point); wiring
landed in `AxiomCheck.lean`, `scripts/check.sh`'s `THEOREMS` list, the
README's audited list, and `.github/workflows/canary.yml`'s comment. A
negative meta-test (temporary copy with the fifth target renamed to a
nonexistent theorem) failed `4/5` exit 1, confirming the row is load-bearing
rather than merely listed — re-confirmed at Step 11 closure, not re-run
today since checkpoint 1 makes no source change to the audit script.

## 11. Deviations from the plan sketch, recorded per step

1. **Step 5** — `rlpToBlock` keeps its exact name/type/behaviour rather than
   returning the `CanonicalBlock` envelope directly: its type appears inside
   the *protected* Blanc theorem `addBlockToChain_preserves_solvent`
   (hypothesis `h_wds`), and changing it would change a protected statement —
   a declared HALT. The envelope is layered on top; `CanonicalBlock.decoded`
   is stated in terms of `rlpToBlock`. Correspondingly, the raw
   `stateTransition`/`…With`/`…At`/`…Using` family was **not** renamed to a
   `…Unchecked`/`…Trusted` spelling (P0.3 item 4's naming half): those names
   are load-bearing in Blanc's protected statements and the four frozen `rfl`
   identities. `stateTransitionCanonical` was added beside them instead.
2. **Step 6** — P0.2 prescribed-fix item 4 ("raw compatibility entry points
   call `BlockChain.check` first") was **deliberately not implemented**.
   Doing so would recompute a trie root on every raw import (the exact
   regression the plan's own fixed decision 9 forbids as a remedy), change
   the observable behaviour of names in Blanc's protected statements, and
   move the frozen validation order of design report §3.3. The checked
   ingress is provided instead and the runner uses it exclusively; the
   closure checklist's actual wording ("normal repeated execution uses
   checked values without redundant root computation") is satisfied by this
   route, which is the one measured in §8.
3. **Step 8** — the EC twist-coordinate fix (`Jaune/EC.lean`, reading through
   `takeRightV` instead of `List.ekat`) is a genuine **mathematical
   correction**, not merely a totalization: the old unpadded right-slice
   returned a trimmed coordinate's low coefficient in the high position and
   defaulted the low one to zero. No old/new kernel *equivalence* theorem was
   stated — a deliberate judgment call, since the old behaviour was simply
   wrong on the affected input class, not an alternative total
   implementation worth relating. The Step-7 vector-gate configuration red
   (fake-exp misregistered) was repaired as part of Step 8's closure.
4. **Step 9** — 20 allowlist rows were re-owned `PENDING(step10)` mid-step
   rather than discharged in place (strict-decoder guards and the
   `hasErrorType`/`isBlockException` classifier primitives still had live
   readers until Step 10's fixture-boundary rewrite); 2 renderer respellings
   were unobserved by any fixture in either full tier (recorded, not a golden
   violation since goldens are fixture-observed sets); the BLS decoder
   relocation moved 12 declarations out of `BLS.lean` into `Precompiles.lean`
   alongside the retyped precompile carriers.
5. **Step 10** — 3 vocabulary extensions beyond the Step-1 skeleton
   (`insufficientMaxFeePerBlobGasTag`, the `senderRecovery`/`vm` arms on
   `BlockRejection`/`ImportFailure`); a channel-nesting change in the legacy
   import adapters (`ImportOutcome.renderLegacy` collapses the typed result
   onto the pre-existing legacy channels rather than adding a new one); 2
   further unobserved respellings; the `toExStr*` → `toEx*` decoder rename
   completed across `Precompiles.lean`/`BLS.lean`.
6. **Step 11** — the fifth audited Blanc theorem
   (`stateTransitionUsing_preserves_solvent`) was added to the protected set
   *after* its axiom set was pre-verified, per §10 above; `BlockChain.Reach.
   toReachUsing` — absent since the style arc's dead-code purge deleted it in
   `692224c`, not itself a P0 defect — was re-introduced in corrected form
   (targeting `ChainConfig.pragueOnly ch.chainId`, taking `ValidContext` as a
   hypothesis rather than re-deriving it, which would rebuild the P0.1 defect
   one level up); `~/plans/restore-chain-using-proposal.md`'s two
   style-arc-deleted solvency theorems were **not** restored, per that step's
   explicit boundary — the shape Step 11 lands (evidence-carrying `refl`,
   corrected `toReachUsing`, `Reach.chainId_eq`) is what that successor arc
   will consume. The upstream-candidate inventory (22 + 18 rows) is
   consolidated in §14 below, nothing moved.

## 12. Full commit ledger

All jaune/blanc commits, chronological, all pushed unless flagged:

| Step | Repo | Commit | Purpose |
| --- | --- | --- | --- |
| 1 | jaune | `c9c39af3` | integrity-gate (`check-integrity.sh` + allowlist, branch point) |
| 1 | jaune | `2dc5dbaf` | design report installed |
| 1 | jaune | `e3d02aea` | error-vocabulary skeleton, pure insertion |
| 2 | jaune | `5d032c62` | fork-schedule: P0.5 fail-closed era floor |
| 2 | jaune | `39baca82` | configured-boundary: P0.1 `checkChainId` |
| 3 | jaune | `db522a6c` | finite canonicality predicates |
| 3 | jaune | `b3de1d1e` | checked-width JSON prestate parser |
| 3 | jaune | `40d2e068` | fork-rules validity + invariant vocabulary |
| 4 | jaune | `d5a3a05f` | result-carrier canonicality helpers |
| 4 | jaune | `4d9c1732` | frame/interpreter canonicality |
| 4 | jaune | `8ce70b0a` | transaction/block canonicality |
| 5 cp1 | jaune | `e29aa664` | wire-structural predicates + decoder soundness |
| 5 cp2 | jaune | `473a83d4` | `CanonicalBlock` envelope |
| 5 cp3 | jaune | `97c0e777` | checked constructors, `TxEnvelope`, bypass discharged |
| 6 | jaune | `598c7764` | retained-history validity |
| 6 | jaune | `b4c522c0` | checked-transition cores |
| 6 | jaune | `857f62a8` | genesis/`ChainStore` checked ingress |
| 7 | jaune | `72e6fd8d` | simple-projection totalization |
| 7 | jaune | `ad52cadc` | fake-exp totalization |
| 8 | jaune | `8a86eb9` | Keccak/SHA-256/RIPEMD-160 fixed-size |
| 8 | jaune | `13eb09c` | EC twist correction |
| 8 | jaune | `8b59012` | BLAKE2b checked wrapper |
| 8 | jaune | `9ad65ec` | BLAKE2b kernel privatized |
| 9 | jaune | `6d81f31` | golden-message capture + decoder relocation |
| 9 | jaune | `f64a421` | typed VM/frame/precompile carrier |
| 9 | jaune | `0e4647bd` | halt-field typing, allowlist closure to 80 |
| 10 | jaune | `d59a5cb` | codec/transaction typed retype |
| 10 | jaune | `dc318c2` | header/block/config/import typed retype |
| 10 | jaune | `4b2171d8` | fixture-boundary closure, allowlist to 0, both golden verdicts |
| 11 cp1 | blanc | `cee817e` | pin bump (diagnostic, flagged red by design) |
| 11 cp2 | blanc | `8284543` | execution-error carrier repair |
| 11 cp4 | jaune | `739fa42d` | `pragueOnly` bridge lemmas upstreamed |
| 11 cp3 | blanc | `98376a27` | transition/import repair, 5-row audit, tip |
| 12 cp1 | both | (none) | verification-only; no source changes |

`~/plans` ledger commits: `cae3ae8`, `75759c3`, `9720a00`, `1500f5a` (Step 11)
and `40d10f6` (Step 12 checkpoint 1) — none pushed, consistent with this
repo's existing convention.

**Recovery state:** both repos clean, pushed, green at the tips above. Prior
Blanc greens: `8284543`↦`4b2171d8`; `5aff6150`↦`ad7f47ec`.

## 13. Deferred, non-P0 work

- **`Blanc/Common.lean`/`Solvent.lean` split** (`restructure.md` Steps 3–4):
  the tactic re-rooting closed; the module split itself was explicitly
  deferrable in that plan and is not part of this arc's scope.
- **16 zero-reference `@[simp]` lemmas** noted during `restructure.md` Step 3,
  carried forward, not touched here.
- **`stateTransitionConfigured`'s residual double-validate**: it still calls
  `cfg.rulesAt`, which re-runs `cfg.validate` internally (a five-element list
  walk, no root recomputation) — noted at Step 6, not addressed; a cheap
  target for a future step alongside the error-carrier work that already
  touched this function.
- **`~/plans/restore-chain-using-proposal.md`**: the two style-arc-deleted
  solvency theorems remain unrestored; Step 11 explicitly prepared the ground
  (`ReachUsing.refl`'s evidence, corrected `toReachUsing`, `Reach.chainId_eq`)
  for that successor arc to consume.
- **Production-client capabilities** were never in scope (mempool, networking,
  RPC, database, throughput) — Jaune remains an executable specification, not
  a competitive client, per the plan's non-goals.
- **BLAKE2b kernel equivalence**: the private `Blake2.g/round/rounds` kernel
  keeps its original (unfixed-size) form behind the checked `bCompress`
  wrapper rather than being restated at fixed size, because restating it
  would require re-deriving its existing equivalence theorems from scratch —
  a deliberate cost/benefit call recorded at Step 8, not a defect.
- **Consolidated upstream-candidate worklist** — see §14. Nothing moved.

## 14. Consolidated upstream-candidate worklist

Every Blanc declaration noticed, across `restructure.md` (Step 3) and this
arc (Step 11), that states a fact about a Jaune-shaped type with no Blanc
concept in it, and so is a genuine candidate to relocate to Jaune in a future
sweep. **Nothing has been moved** — relocating a declaration changes Jaune's
public API and is out of scope for both arcs. All are currently declared in
Blanc (`Blanc.` qualified); "Kind" `definition` entries additionally change
Jaune's API surface if moved and need more deliberation than a lemma.

**From `restructure.md` (`scripts/report-restructure-step-3.md`), 22 rows:**

| Candidate | Kind | Hits/uses | Cone |
| --- | --- | ---: | :---: |
| `B128.sub_self` | lemma | 2/1 | yes |
| `B256.sub_self` | lemma | 4/3 | yes |
| `Adr.max` | **definition** | 5/4 | yes |
| `Nat.add_sub_mod_eq_sub` | lemma | 2/1 | yes |
| `B128.zero_eq` | lemma | 2/1 | no |
| `B128.sub_zero` | lemma | 1/0 | no |
| `B256.toNat_zero` | lemma | 11/10 | yes |
| `B256.Nof` | **definition** | 17/16 | yes |
| `B256.toNat_add_eq_of_nof` | lemma | 7/6 | yes |
| `B256.toNat_sub_eq_of_le` | theorem | 8/7 | yes |
| `B256.zero_ne_one` | lemma | 5/4 | yes |
| `of_bind_eq_ok` | lemma | 150/149 | yes |
| `of_bind_eq_some` | lemma | 16/15 | yes |
| `of_pure_eq_some` | lemma | 2/1 | yes |
| `Except.IsOk` | inductive/API | 2/0 external | no |
| `B128.and_eq_and_prod_and` | lemma | 4/3 | yes |
| `B256.and_eq_and_prod_and` | lemma | 3/2 | yes |
| `B128.zero_and` | lemma | 2/1 | yes |
| `Adr.toNat_lt_size` | lemma | 7/6 | yes |
| `Adr.toNat_inj` | lemma | 2/1 | yes |
| `B256.le_add_right` | lemma | 1/0 | no |
| `adr_toNat_lt_size_local` | lemma | 2/1 | yes |

The marked `B128`/`B256` block still carries the unacted-on banner
`-- B(2^n) lemmas (transfer to Jaune later) --` at `Blanc/Basic.lean:247`;
carried forward, not silently dropped or prefixed away.

**From this arc's Step 11 (`~/plans/reports/integrity-step11.md`), 18 further
rows — all lemmas (no new definitions), all in the protected-theorem cone,
surfaced while repairing Blanc against the typed carrier:**

| Candidate | Kind | Hits/uses | Cone | Note |
| --- | --- | ---: | :---: | --- |
| `ByteArray.getElem_of_getElem?_eq_some` | lemma | 7/6 | yes | new this step; proof-indexed reads |
| `ByteArray.of_getElem?_eq_some` | lemma | 2/1 | yes | |
| `ByteArray.lt_size_of_getElem?_eq_some` | lemma | 12/11 | yes | |
| `ByteArray.toList_eq_toList_data` | lemma | 7/6 | yes | |
| `ByteArray.sliceD_eq` | lemma | 2/1 | yes | about Jaune's `sliceD` |
| `ByteArray.sliceD_eq_replicate` | lemma | 2/1 | yes | |
| `List.toUInt16_pair` | lemma | 2/1 | yes | about `Bytes.toUInt16` |
| `List.toUInt32_pair` | lemma | 2/1 | yes | |
| `List.toUInt64_pair` | lemma | 2/1 | yes | |
| `List.toB256_pair` | lemma | 4/3 | yes | |
| `accessDelegation_state` | lemma | 2/1 | yes | |
| `accessDelegation_code_of_not` | lemma | 2/1 | yes | |
| `accessDelegation_of_not_delegation` | lemma | 3/2 | yes | |
| `of_handleError_err` | lemma | 6/5 | yes | about `executeCode.handleError` |
| `of_benvAfterTransfer` | lemma | 9/8 | yes | about `Msg.benvAfterTransfer` |
| `processCheckedSystemTransaction_to_unchecked` | lemma | 3/2 | yes | |
| `setDelegationStep_bal_eq` | lemma | 2/1 | yes | |
| `setDelegationLoop_bal_eq` | lemma | 2/1 | yes | |

**40 total candidates**, the complete input to a future upstream sweep. The
discriminator used throughout: not namespace shape (most of Blanc's ~482
declarations in Jaune-shaped namespaces legitimately belong to Blanc — e.g.
`Devm.Pop`, `Ninst.pushB256`), but whether the *statement* is a fact about
Jaune types with no Blanc concept in it.

## Verification and handoff

All catalogue gates green on the exact candidates (§1, §9); both `--full`
verdicts recorded inline at `--jobs auto` (§1); trees clean; pins agree; no
baseline/exclusion/manifest weakened; ledger complete (§12). Handoff is the
exact pair of branch tips: jaune `codex/integrity` @ `739fa42d…`, blanc
`codex/integrity` @ `98376a27…`, proposed for user integration into `main` in
both repositories. **No merge, rebase, or squash has been performed.**
