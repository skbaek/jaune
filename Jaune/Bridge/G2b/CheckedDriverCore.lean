import Jaune.Bridge.G2b.CheckedOutcomes

/-! Fuel induction for erasure of the complete checked call tree. -/

namespace Jaune.Checked

section Simulation
variable
    (hstep : ∀ r : Frame.Running, Staging.step r.toLegacy = (step r).map Step.toLegacy)
    (henter : ∀ f : Frame, Staging.enter f.toLegacy = (enter f).toLegacy)
    (hsettle : ∀ (f : Frame) (e : Frame.Exit), Staging.settle f.toLegacy e.toLegacy = settle f e)
    (hresume : ∀ rules p (s : Frame.State) r,
      Staging.resume rules p s.toLegacy r = (resume rules p s r).map ResumeResult.toLegacy)

include hstep henter hsettle hresume

theorem execFueled_toLegacy_of_parts (fuel : Nat) (r : Frame.Running) :
    (Staging.execFueled r.toLegacy fuel).run =
      (execFueled r fuel).run.map (Except.map Frame.Exit.toLegacy) := by
  induction fuel generalizing r with
  | zero => rfl
  | succ fuel ih =>
    rw [Staging.execFueled, execFueled, hstep]
    cases hs : step r with
    | error f => rfl
    | ok next =>
      cases next with
      | exit e => rfl
      | next pc s => exact ih ⟨pc, r.context, s⟩
      | spawn child p pc =>
        simp only [Except.map, Step.toLegacy, henter]
        have tail (result : Frame.Result) :
            (match Staging.resume r.context.block.rules p child.checkpoint.toLegacy result with
              | .error fault => Fueled.ofExcept (.error fault)
              | .ok (.error (reason, s)) => Fueled.ofExcept (.ok (Jaune.Frame.Exit.halted reason s))
              | .ok (.ok s) => Staging.execFueled ⟨pc, r.context, s⟩ fuel).run =
              (match resume r.context.block.rules p child.checkpoint result with
                | .error fault => Fueled.ofExcept (.error fault)
                | .ok (.error (reason, s)) => Fueled.ofExcept (.ok (Frame.Exit.halted reason s))
                | .ok (.ok s) => execFueled ⟨pc, r.context, s⟩ fuel).run.map (Except.map Frame.Exit.toLegacy) := by
          rw [hresume]
          rcases resume r.context.block.rules p child.checkpoint result with fault | (⟨reason, s⟩ | s)
          · rfl
          · rfl
          · exact ih ⟨pc, r.context, s⟩
        cases he : enter child with
        | done value =>
          cases value with
          | error fault => rfl
          | ok result => exact tail result
        | run cr =>
          simp only [Frame.Entry.toLegacy, ih]
          cases hc : (execFueled cr fuel).run with
          | none => rfl
          | some raw =>
            cases raw with
            | error fault => rfl
            | ok e =>
              simp only [Option.map, Except.map, bind, Except.bind, hsettle]
              cases hs : settle child e with
              | error fault => rfl
              | ok result => exact tail result

theorem exec_toLegacy_of_parts (r : Frame.Running) :
    Staging.exec r.toLegacy = (exec r).map Frame.Exit.toLegacy := by
  unfold Staging.exec exec
  change (match (Staging.execFueled r.toLegacy (sufficientFuel r.state.machine.gasMeasure)).run with
    | some x => x | none => _) = _
  rw [execFueled_toLegacy_of_parts hstep henter hsettle hresume]
  cases (execFueled r (sufficientFuel r.state.machine.gasMeasure)).run <;> rfl

variable (henterWith : ∀ (f : Frame) (s : Frame.State),
    Staging.enterWith f.toLegacy s.toLegacy = (enterWith f s).toLegacy)

include henterWith

theorem Frame.runTop_toLegacy_of_parts (f : Frame) :
    Staging.Frame.runTop f.toLegacy = Frame.runTop f := by
  rw [Frame.runTop_eq]
  unfold Staging.Frame.runTop
  rw [show f.toLegacy.checkpoint = f.checkpoint.toLegacy from rfl, henterWith]
  cases enterWith f f.checkpoint with
  | done x => rfl
  | run r =>
    simp only [Frame.Entry.toLegacy, exec_toLegacy_of_parts hstep henter hsettle hresume]
    cases exec r with
    | error e => rfl
    | ok e => exact hsettle f e

end Simulation

end Jaune.Checked
