import Jaune.Bridge.G2a.Old.Transaction
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
    (hp : Staging.TopLevel.prepare msg = .ok (.frame f a)) :
    Staging.processMessageCall msg = (do
      let r ← (Frame.runTop f).mapError Fault.toEvmError
      match msg.benv.stat.rules.stateGas with
      | none => f.output a r
      | some _ => f.outputAmsterdam r) := by
  unfold Staging.processMessageCall Staging.Message.run Frame.runTop
  rw [hp]
  simp only [bind, Except.bind]
  cases enterWith f f.checkpoint.toDevm with
  | run evm =>
    dsimp only
    cases settle f (exec evm) <;> rfl
  | done result => cases result <;> rfl

theorem processMessageCall_of_refused {msg : Msg} {reason : ExceptionalHalt} {halted : Devm}
    (hp : Staging.TopLevel.prepare msg = .ok (.refused reason halted)) :
    Staging.processMessageCall msg = (match msg.benv.stat.rules.stateGas with
      | none =>
        .ok ⟨msg.benv.state,
          { gasLeft := 0, refundCounter := 0, logs := [],
            accountsToDelete := .emptyWithCapacity,
            error := .some (.halt reason), returnData := [] }⟩
      | some _ => settleTopLevelPreparationFailure msg (.halt reason) halted) := by
  unfold Staging.processMessageCall Staging.Message.run
  rw [hp]
  rfl

theorem processMessageCall_of_fault {msg : Msg} {e : Fault}
    (hp : Staging.TopLevel.prepare msg = .error e) :
    Staging.processMessageCall msg = .error e.toEvmError := by
  unfold Staging.processMessageCall Staging.Message.run
  rw [hp]
  rfl

theorem processMessageCall_amsterdam {msg : Msg} {state : StateGasRules} {isCreate : Bool}
    (hs : msg.benv.stat.rules.stateGas = some state)
    (hp : Staging.TopLevel.prepare msg = Staging.TopLevel.prepare.amsterdam state msg isCreate) :
    Staging.processMessageCall msg = processTopLevelAmsterdam state msg isCreate := by
  unfold Staging.TopLevel.prepare.amsterdam at hp
  unfold processTopLevelAmsterdam
  split at hp
  · rename_i reason devm h
    rw [processMessageCall_of_refused hp, hs]
    rw [h]
  · rename_i devm h
    exact absurd h (Staging.prepareTopLevelAmsterdam_error_ne_revert state msg devm)
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
    Staging.processMessageCall msg = processMessageCall msg := by
  unfold processMessageCall
  by_cases ht : msg.target.isNone
  · simp only [ht, ↓reduceIte]
    unfold processMessageCall.create
    cases hs : msg.benv.stat.rules.stateGas with
    | none =>
      by_cases hc : accountHasCodeOrNonce msg.benv.state msg.currentTarget
      · rw [processMessageCall_of_refused (reason := .addressCollision .none)
          (halted := initDevm msg) (by
            simp [Staging.TopLevel.prepare, Staging.TopLevel.prepare.create, ht, hs, hc])]
        simp [hs, hc]
        rfl
      · rw [processMessageCall_of_frame (f := Frame.ofTop msg true) (a := 0) (by
            simp [Staging.TopLevel.prepare, Staging.TopLevel.prepare.create, ht, hs, hc])]
        simp [hs, hc]
    | some state =>
      exact processMessageCall_amsterdam hs (by
        simp [Staging.TopLevel.prepare, Staging.TopLevel.prepare.create, ht, hs])
  · simp only [ht, Bool.false_eq_true, ↓reduceIte]
    unfold processMessageCall.call
    cases hs : msg.benv.stat.rules.stateGas with
    | none =>
      cases ha : processMessageCall.authorize msg with
      | error e =>
        rw [processMessageCall_of_fault (e := Staging.EvmError.toFault e
          (Staging.processMessageCall.authorize_error_isFault ha)) (by
            simp only [Staging.TopLevel.prepare, Staging.TopLevel.prepare.call, ht, hs,
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
            simp only [Staging.TopLevel.prepare, Staging.TopLevel.prepare.call, ht, hs,
              Bool.false_eq_true, ↓reduceIte]
            split <;> simp_all)]
        simp [hs, bind, Except.bind]
    | some state =>
      exact processMessageCall_amsterdam hs (by
        simp [Staging.TopLevel.prepare, Staging.TopLevel.prepare.call, ht, hs])

/-! ### Every frame a top-level message call runs is a `processMessageCall.TopFrame`

This closes the gap left at W1 (u36). It is stated over the staged run, whose frame is the one
`TopLevel.prepare` returns; its Amsterdam case is the public preparation itself. Once
`processMessageCall.TopFrame` names the staged preparation (the switch), the theorem needs no
bridge and moves to a proof module. -/

theorem Staging.TopLevel.prepare.amsterdam_topFrame {state : StateGasRules} {msg : Msg}
    (hs : msg.benv.stat.rules.stateGas = some state) {f : Frame} {a : Nat}
    (h : Staging.TopLevel.prepare.amsterdam state msg msg.target.isNone = .ok (.frame f a)) :
    processMessageCall.TopFrame msg f := by
  unfold Staging.TopLevel.prepare.amsterdam at h
  split at h
  · cases h
  · rename_i devm hp
    exact absurd hp (Staging.prepareTopLevelAmsterdam_error_ne_revert state msg devm)
  · cases h
  · cases h
  · rename_i prepared devm hp
    cases h
    exact .amsterdam hs (p := (prepared, devm)) hp

/-- **Every frame the top-level preparation returns is a `processMessageCall.TopFrame`.** -/
theorem Staging.TopLevel.prepare_topFrame {msg : Msg} {f : Frame} {a : Nat}
    (h : Staging.TopLevel.prepare msg = .ok (.frame f a)) : processMessageCall.TopFrame msg f := by
  unfold Staging.TopLevel.prepare at h
  by_cases ht : msg.target.isNone
  · simp only [ht, ↓reduceIte] at h
    unfold Staging.TopLevel.prepare.create at h
    cases hs : msg.benv.stat.rules.stateGas with
    | none =>
      rw [hs] at h
      dsimp only at h
      split at h
      · cases h
      · cases h
        exact .create (Option.isNone_iff_eq_none.mp ht) hs
    | some state =>
      rw [hs] at h
      dsimp only at h
      rw [← ht] at h
      exact Staging.TopLevel.prepare.amsterdam_topFrame hs h
  · simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
    unfold Staging.TopLevel.prepare.call at h
    have ht' : msg.target ≠ none := fun e => ht (by simp [e])
    cases hs : msg.benv.stat.rules.stateGas with
    | none =>
      rw [hs] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i delegated refund ha
        cases h
        exact .call ht' hs ha
    | some state =>
      rw [hs] at h
      dsimp only at h
      have hf : msg.target.isNone = false := by cases hmt : msg.target <;> simp_all
      rw [← hf] at h
      exact Staging.TopLevel.prepare.amsterdam_topFrame hs h

/-- **Every frame a top-level message run runs is a `processMessageCall.TopFrame`.** This closes
the gap left at W1 (u36): `processMessageCall` runs only frames the relation names. -/
theorem Staging.Message.run_topFrame {msg : Msg} {run : Staging.MessageRun} (h : Staging.Message.run msg = .ok run)
    {f : Frame} {a : Nat} (hf : run.preparation = .frame f a) :
    processMessageCall.TopFrame msg f := by
  unfold Staging.Message.run at h
  obtain ⟨p, hp, h⟩ := Except.bind_eq_ok h
  have : p = .frame f a := by
    cases p with
    | refused reason halted => cases h; cases hf
    | frame f' a' =>
      dsimp only at h
      split at h
      · obtain ⟨r, -, h⟩ := Except.bind_eq_ok h
        cases h; exact hf
      · obtain ⟨r, -, h⟩ := Except.bind_eq_ok h
        cases h; exact hf
  subst this
  exact Staging.TopLevel.prepare_topFrame hp

/-! ### A: the transaction in phases at `processTransaction` -/

/-- **Bridge A.** For every block environment, block output, transaction and index, the staged
phases compute exactly today's `processTransaction` result, rejection text included. -/
theorem processTransaction_eq (benv : Benv) (bout : BlockOutput) (tx : Transaction)
    (index : Nat) :
    Staging.processTransaction benv bout tx index = processTransaction benv bout tx index := by
  have hm : Staging.processMessageCall = processMessageCall := funext processMessageCall_eq
  simp only [Staging.processTransaction, hm, Staging.Transaction.check,
    Staging.Transaction.prepare, Staging.Transaction.settle, processTransaction, bind_assoc,
    pure_bind]
  rfl

end Jaune.Bridge.G2a
