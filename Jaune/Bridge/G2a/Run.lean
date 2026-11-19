import Jaune.Bridge.G2a.Old.Transaction
import Jaune.Bridge.G2a.Phased
import Jaune.MessageCall.SpawnFacts
import Jaune.Run.Transaction

/-!
# W2 cuts A and B1: bridges (goal `jaune-shape-and-names-v1`, gate G2a, bridge)

Old side = the definitions at `ba15f397` (`Jaune.Transaction`), unedited. New side = the staged
definitions of `Jaune.Run.Message` and `Jaune.Run.Transaction`. Each bridge quantifies over every
input and observes the whole result. The original preparation helpers now live in
`Jaune.Transaction.Parts`. This module is deleted with the old side after the gate's tag.
-/

namespace Jaune.Bridge.G2a

/-! ### B1: the message run at `processMessageCall` -/

theorem processMessageCall_of_frame {msg : Msg} {f : Frame} {a : Nat}
    (hp : TopLevel.prepare msg = .ok (.frame f a)) :
    Bridge.G2a.Phased.processMessageCall msg = (do
      let r ← (Frame.runTop f).mapError Fault.toEvmError
      match msg.benv.stat.rules.stateGas with
      | none => Bridge.G2a.Old.Frame.output f a r
      | some _ => Bridge.G2a.Old.Frame.outputAmsterdam f r) := by
  unfold Bridge.G2a.Phased.processMessageCall TopLevel.run Frame.runTop
  rw [hp]
  simp only [bind, Except.bind]
  cases enterWith f f.checkpoint.toDevm with
  | run evm =>
    dsimp only
    cases settle f (exec evm) <;> rfl
  | done result => cases result <;> rfl

theorem processMessageCall_of_refused {msg : Msg} {reason : ExceptionalHalt} {halted : Devm}
    (hp : TopLevel.prepare msg = .ok (.refused reason halted)) :
    Bridge.G2a.Phased.processMessageCall msg = (match msg.benv.stat.rules.stateGas with
      | none =>
        .ok ⟨msg.benv.state,
          { gasLeft := 0, refundCounter := 0, logs := [],
            accountsToDelete := .emptyWithCapacity,
            error := .some (.halt reason), returnData := [] }⟩
      | some _ => Bridge.G2a.Old.settleTopLevelPreparationFailure msg (.halt reason) halted) := by
  unfold Bridge.G2a.Phased.processMessageCall TopLevel.run
  rw [hp]
  rfl

theorem processMessageCall_of_fault {msg : Msg} {e : Fault}
    (hp : TopLevel.prepare msg = .error e) :
    Bridge.G2a.Phased.processMessageCall msg = .error e.toEvmError := by
  unfold Bridge.G2a.Phased.processMessageCall TopLevel.run
  rw [hp]
  rfl

theorem processMessageCall_amsterdam {msg : Msg} {state : StateGasRules} {isCreate : Bool}
    (hs : msg.benv.stat.rules.stateGas = some state)
    (hp : TopLevel.prepare msg = TopLevel.prepare.amsterdam state msg isCreate) :
    Bridge.G2a.Phased.processMessageCall msg = Bridge.G2a.Old.processTopLevelAmsterdam state msg isCreate := by
  unfold TopLevel.prepare.amsterdam at hp
  unfold Bridge.G2a.Old.processTopLevelAmsterdam
  split at hp
  · rename_i reason devm h
    rw [processMessageCall_of_refused hp, hs]
    rw [h]
  · rename_i devm h
    exact absurd h (prepareTopLevelAmsterdam_error_ne_revert state msg devm)
  · rename_i reason devm h
    rw [processMessageCall_of_fault hp, h]
    rfl
  · rename_i reason devm h
    rw [processMessageCall_of_fault hp, h]
    rfl
  · rename_i prepared devm h
    rw [processMessageCall_of_frame hp, hs, h]

/-- **Bridge B1.** For every message, under every fork, the staged message run renders exactly
today's `processMessageCall` result, faults included. -/
theorem processMessageCall_eq (msg : Msg) :
    Bridge.G2a.Phased.processMessageCall msg = Bridge.G2a.Old.processMessageCall msg := by
  unfold Bridge.G2a.Old.processMessageCall
  by_cases ht : msg.target.isNone
  · simp only [ht, ↓reduceIte]
    unfold Bridge.G2a.Old.processMessageCall.create
    cases hs : msg.benv.stat.rules.stateGas with
    | none =>
      by_cases hc : accountHasCodeOrNonce msg.benv.state msg.currentTarget
      · rw [processMessageCall_of_refused (reason := .addressCollision .none)
          (halted := initDevm msg) (by
            simp [TopLevel.prepare, TopLevel.prepare.create, ht, hs, hc])]
        simp [hs, hc]
        rfl
      · rw [processMessageCall_of_frame (f := Frame.ofTop msg true) (a := 0) (by
            simp [TopLevel.prepare, TopLevel.prepare.create, ht, hs, hc])]
        simp [hs, hc]
    | some state =>
      exact processMessageCall_amsterdam hs (by
        simp [TopLevel.prepare, TopLevel.prepare.create, ht, hs])
  · simp only [ht, Bool.false_eq_true, ↓reduceIte]
    unfold Bridge.G2a.Old.processMessageCall.call
    cases hs : msg.benv.stat.rules.stateGas with
    | none =>
      cases ha : TopLevel.applyAuthorizations msg with
      | error e =>
        rw [processMessageCall_of_fault (e := EvmError.toFault e
          (TopLevel.applyAuthorizations_error_isFault ha)) (by
            simp only [TopLevel.prepare, TopLevel.prepare.call, ht, hs,
              Bool.false_eq_true, ↓reduceIte]
            split
            · rename_i e' h
              rw [ha] at h
              cases h
              rfl
            · simp_all)]
        simp [bind, Except.bind]
      | ok q =>
        obtain ⟨delegated, refund⟩ := q
        rw [processMessageCall_of_frame (f := Frame.ofTop (TopLevel.resolveCodeDelegation delegated) false)
          (a := refund) (by
            simp only [TopLevel.prepare, TopLevel.prepare.call, ht, hs,
              Bool.false_eq_true, ↓reduceIte]
            split <;> simp_all)]
        simp [hs, bind, Except.bind]
    | some state =>
      exact processMessageCall_amsterdam hs (by
        simp [TopLevel.prepare, TopLevel.prepare.call, ht, hs])

/-! ### A: the transaction in phases at `processTransaction` -/

/-- **Bridge A.** For every block environment, block output, transaction and index, the staged
phases compute exactly today's `processTransaction` result, rejection text included. -/
theorem processTransaction_eq (benv : Benv) (bout : BlockOutput) (tx : Transaction)
    (index : Nat) :
    Bridge.G2a.Phased.processTransaction benv bout tx index = Bridge.G2a.Old.processTransaction benv bout tx index := by
  have hm : Bridge.G2a.Phased.processMessageCall = Bridge.G2a.Old.processMessageCall := funext processMessageCall_eq
  simp only [Bridge.G2a.Phased.processTransaction, hm, Transaction.admit,
    Transaction.prepare, Bridge.G2a.Phased.Transaction.settle, Bridge.G2a.Old.processTransaction, bind_assoc,
    pure_bind]
  rfl

end Jaune.Bridge.G2a
