import Jaune.Run.Block
import Jaune.Bridge.G2a.Body
import Jaune.Bridge.G2a.Decode

/-!
# W2 cut E: bridges for the block run (goal `jaune-shape-and-names-v1`, gate G2a, bridge)

Old side = cut D's `Staging.stateTransitionCoreE` (`Jaune.Run.Body`), whose own old side is
`stateTransitionCoreE` at `ba15f397` (`Jaune.Transaction`), unedited. New side = `Jaune.Run.Block`.

* `Block.check_ofPrefix`: `Block.check` over a prefix's commitments is today's
  `stateTransitionChecks` followed by `blockAccessListCheck`, on the whole result, so the same
  check fails first with the same reason and text.
* `E.stateTransitionCoreE_eq`: **the bridge.** The staged block transition equals cut D's, for every
  error embedding, fork, chain, block and ommer check, on the whole result.
* `E.stateTransitionCoreE_difference`: cut E composed with cut D's difference theorem (decode
  before the system calls, decision 14) and W2-T's (an unknown type byte is an invalid block,
  decision 16), against `ba15f397`'s `stateTransitionCoreE`: equal except on
  `BlockDecodeOrderSplit` and on `TransitionDiffers`, with the exact results on each.
-/

namespace Jaune.Bridge.G2a

open Jaune Jaune.Staging

/-! ### The check -/

/-- **`Block.check` is today's two checks.** Over a body prefix's commitments, `Block.check` is
`stateTransitionChecks` with the transition's computed values, then `blockAccessListCheck`: the
whole result, so the first failing comparison and its text are today's. -/
theorem Block.check_ofPrefix (rules : ForkRules) (q : Body.Prefix) (header : Header) :
    Block.check header (Block.Commitments.ofPrefix rules q) =
      (stateTransitionChecks q.toBlockOutput header (getTransactionsRoot q.toBlockOutput)
          q.state.root (getReceiptRoot q.toBlockOutput) (logsBloom q.toBlockOutput.blockLogs)
          (getWithdrawalsRoot q.toBlockOutput)
          (if rules.header.requestsHash then some (computeRequestsHash q.toBlockOutput.requests)
            else none) >>= fun _ =>
        blockAccessListCheck rules q.toBlockOutput header) := by
  unfold Block.check
  refine congrArg₂ (fun a k => Bind.bind a k) ?_ ?_
  · rfl
  funext _
  unfold Block.checkAccessListHash blockAccessListCheck Block.Commitments.ofPrefix
  cases rules.blockAccessListRules <;> rfl

/-! ### The bridge -/

/-- **Bridge, cut E.** The staged block transition is cut D's, on the whole result: the same
header failure, the same ommer failure, the same body failure, the same first failing commitment
check with the same text, and the same chain. -/
theorem E.stateTransitionCoreE_eq {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) :
    E.stateTransitionCoreE embed f ch block checkOmmers =
      Staging.stateTransitionCoreE embed f ch block checkOmmers := by
  rw [staged_stateTransitionCoreE_eq_with]
  unfold E.stateTransitionCoreE stateTransitionCoreWith Staging.applyBody
  cases hv : validateHeader f.ruleSet ch block.header with
  | error e => rfl
  | ok u =>
    cases ho : checkOmmers () with
    | error e => simp only [bind, Except.bind, Except.mapError]
    | ok u' =>
      cases hq : Body.importer (initBlockEnvironment f ch block.header) block.transactions block.ommers
          block.withdrawals with
      | error e => simp only [bind, Except.bind, Except.mapError, Functor.map, Except.map]
      | ok q =>
        simp only [bind, Except.bind, Except.mapError, Functor.map, Except.map,
          Body.Prefix.output]
        rw [Block.check_ofPrefix]
        cases stateTransitionChecks q.toBlockOutput block.header _ _ _ _ _ _ <;>
          simp only [bind, Except.bind]

/-- The whole result, through `ba15f397`'s `stateTransitionCoreE` off the decode-order split. -/
theorem E.stateTransitionCoreE_eq_of_not_split {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit)
    (h : ¬ BlockDecodeOrderSplit f ch block checkOmmers) :
    E.stateTransitionCoreE embed f ch block checkOmmers =
      stateTransitionCoreE embed f ch block checkOmmers := by
  rw [E.stateTransitionCoreE_eq,
    Jaune.Bridge.G2a.stateTransitionCoreE_eq_of_not_split embed f ch block checkOmmers h]

/-! ### The composed difference theorem against `ba15f397` -/

/-- The importer's body with the slot decoder as a parameter (bridge only). -/
def Body.importerDecoding
    (decode : ForkRules → Bytes ⊕ Transaction → Except TransitionError Transaction)
    (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
    (wds : List Withdrawal) : Except TransitionError Body.Prefix := do
  let decoded ← txs.mapM (decode benv.stat.rules)
  Body.fold benv (Body.Prefix.init benv.state) (Body.ops benv decoded ommers wds)

/-- The staged block transition with the slot decoder as a parameter (bridge only). At
`decodeTransaction` it is `E.stateTransitionCoreE`; at `Staging.decodeTransaction` it is the
transition after the switch, which composes cuts D, E and W2-T. -/
def E.stateTransitionCoreEDecoding
    (decode : ForkRules → Bytes ⊕ Transaction → Except TransitionError Transaction)
    {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except ε Unit) : Except ε BlockChain := do
  Except.mapError embed (validateHeader f.ruleSet ch block.header)
  checkOmmers ()
  let q ← Except.mapError embed
    (Body.importerDecoding decode (initBlockEnvironment f ch block.header) block.transactions block.ommers
      block.withdrawals)
  Except.mapError (embed ∘ TransitionError.block) <|
    Block.check block.header (Block.Commitments.ofPrefix f.ruleSet q)
  .ok ⟨appendBlock ch.blocks block, q.state, ch.chainId⟩

theorem E.stateTransitionCoreE_eq_decoding {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) :
    E.stateTransitionCoreE embed f ch block checkOmmers =
      E.stateTransitionCoreEDecoding decodeTransaction embed f ch block checkOmmers := rfl

/-- **The composed difference theorem.** The block transition after cuts D, E and W2-T (decode the
whole list first with the staged decoder, then the block run and its checks) against `ba15f397`'s
`stateTransitionCoreE`, for every error embedding, fork, chain, block and ommer check. Exactly one
of:

1. off both sets, the whole result is equal;
2. on the decode-order split (the header and ommers pass, the pre-execution system calls fail with
   `eSys`, the decode fails): the old transition reports `eSys`, the new one the staged decoder's
   error `eNew`;
3. on `TransitionDiffers x` (the header and ommers pass, the system calls succeed, the first
   failing slot has the unknown type byte `x`): the old transition reports the internal error, the
   new one the rejection `transactionTypeNotSupported x`. -/
theorem E.stateTransitionCoreE_difference {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) :
    (E.stateTransitionCoreEDecoding Staging.decodeTransaction embed f ch block checkOmmers =
          stateTransitionCoreE embed f ch block checkOmmers ∧
        ¬ BlockDecodeOrderSplit f ch block checkOmmers ∧
        ∀ x, ¬ TransitionDiffers f ch block checkOmmers x) ∨
      (BlockDecodeOrderSplit f ch block checkOmmers ∧
        ∃ eSys eNew, preCalls (initBlockEnvironment f ch block.header) = .error eSys ∧
          block.transactions.mapM
              (Staging.decodeTransaction (initBlockEnvironment f ch block.header).stat.rules) = .error eNew ∧
          stateTransitionCoreE embed f ch block checkOmmers = .error (embed eSys) ∧
          E.stateTransitionCoreEDecoding Staging.decodeTransaction embed f ch block checkOmmers =
            .error (embed eNew)) ∨
      (∃ x, TransitionDiffers f ch block checkOmmers x ∧
        stateTransitionCoreE embed f ch block checkOmmers = .error (embed (oldUnknownTypeError x)) ∧
        E.stateTransitionCoreEDecoding Staging.decodeTransaction embed f ch block checkOmmers =
          .error (embed (Staging.transactionTypeNotSupported x))) := by
  have hrules : (initBlockEnvironment f ch block.header).stat.rules = f.ruleSet := rfl
  rcases mapM_decodeTransaction_difference (initBlockEnvironment f ch block.header).stat.rules
      block.transactions with ⟨hm, hmn⟩ | ⟨x, hx, hold, hnew⟩
  · -- The staged decoder agrees: cut E's bridge and cut D's difference theorem.
    have hE :
        E.stateTransitionCoreEDecoding Staging.decodeTransaction embed f ch block checkOmmers =
        Staging.stateTransitionCoreE embed f ch block checkOmmers := by
      rw [← E.stateTransitionCoreE_eq, E.stateTransitionCoreE_eq_decoding]
      unfold E.stateTransitionCoreEDecoding Body.importerDecoding
      rw [hm]
    have hnd : ∀ x, ¬ TransitionDiffers f ch block checkOmmers x := by
      rintro x ⟨-, -, _, _, _, _, -, -, h3⟩
      exact hmn x h3
    by_cases hs : BlockDecodeOrderSplit f ch block checkOmmers
    · obtain ⟨hv, ho, ⟨eSys, hsys⟩, eDec, hd⟩ := hs
      obtain ⟨h1, h2⟩ :=
        Jaune.Bridge.G2a.stateTransitionCoreE_of_split embed f ch block checkOmmers hv ho hsys hd
      refine .inr (.inl ⟨⟨hv, ho, ⟨eSys, hsys⟩, eDec, hd⟩, eSys, eDec, hsys, ?_, h1, ?_⟩)
      · rw [hm]; exact hd
      · rw [hE, h2]
    · refine .inl ⟨?_, hs, hnd⟩
      rw [hE, Jaune.Bridge.G2a.stateTransitionCoreE_eq_of_not_split embed f ch block checkOmmers hs]
  · -- The staged decoder rejects at an unknown type byte `x`.
    have hnew' : E.stateTransitionCoreEDecoding Staging.decodeTransaction embed f ch block
        checkOmmers = (do
          Except.mapError embed (validateHeader f.ruleSet ch block.header)
          checkOmmers ()
          Except.error (embed (Staging.transactionTypeNotSupported x))) := by
      unfold E.stateTransitionCoreEDecoding Body.importerDecoding
      rw [hnew]; rfl
    cases hv : validateHeader f.ruleSet ch block.header with
    | error e =>
      refine .inl ⟨?_, ?_, ?_⟩
      rotate_left
      · intro h; rw [h.1] at hv; cases hv
      · intro x h; rw [h.1] at hv; cases hv
      rw [hnew', Jaune.Bridge.G2a.stateTransitionCoreE_eq_decoding]
      unfold Jaune.Bridge.G2a.stateTransitionCoreEDecoding
      simp only [hv, bind, Except.bind, Except.mapError]
    | ok u =>
      cases ho : checkOmmers () with
      | error e =>
        refine .inl ⟨?_, ?_, ?_⟩
        rotate_left
        · intro h; rw [h.2.1] at ho; cases ho
        · intro x h; rw [h.2.1] at ho; cases ho
        rw [hnew', Jaune.Bridge.G2a.stateTransitionCoreE_eq_decoding]
        unfold Jaune.Bridge.G2a.stateTransitionCoreEDecoding
        simp only [hv, ho, bind, Except.bind, Except.mapError]
      | ok u' =>
        have hu : u = () := rfl
        have hu' : u' = () := rfl
        subst hu hu'
        have hE : E.stateTransitionCoreEDecoding Staging.decodeTransaction embed f ch block
            checkOmmers = .error (embed (Staging.transactionTypeNotSupported x)) := by
          rw [hnew']; simp only [hv, ho, bind, Except.bind, Except.mapError]
        cases hp : preCalls (initBlockEnvironment f ch block.header) with
        | error eSys =>
          have hd : decodeAll (initBlockEnvironment f ch block.header) block.transactions =
              .error (oldUnknownTypeError x) := hold
          obtain ⟨h1, -⟩ :=
            Jaune.Bridge.G2a.stateTransitionCoreE_of_split embed f ch block checkOmmers hv ho hp hd
          exact .inr (.inl ⟨⟨hv, ho, ⟨eSys, hp⟩, _, hd⟩, eSys, _, rfl, hnew, h1, hE⟩)
        | ok sb =>
          revert hp; unfold preCalls
          cases hb : beaconRootsCall (initBlockEnvironment f ch block.header).stat.rules
              (initBlockEnvironment f ch block.header) with
          | error e => intro hp; cases hp
          | ok pb =>
            obtain ⟨stB, bal⟩ := pb
            simp only [bind, Except.bind]
            cases hh : historyStorageCall (initBlockEnvironment f ch block.header).stat.rules
                ((initBlockEnvironment f ch block.header).withState stB) bal with
            | error e => intro hp; cases hp
            | ok ph =>
              intro _
              obtain ⟨stH, bal'⟩ := ph
              refine .inr (.inr ⟨x, ⟨hv, ho, stB, bal, stH, bal', hb, hh, hx⟩, ?_, hE⟩)
              rw [Jaune.Bridge.G2a.stateTransitionCoreE_eq_decoding]
              unfold Jaune.Bridge.G2a.stateTransitionCoreEDecoding applyBodyDecoding
              have hr : (((initBlockEnvironment f ch block.header).withState stB).withState stH).stat.rules =
                  (initBlockEnvironment f ch block.header).stat.rules := rfl
              simp only [hv, ho, hb, hh, hr, hold, bind, Except.bind, Except.mapError]

end Jaune.Bridge.G2a
