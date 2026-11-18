import Jaune.Bridge.G2b.MessageOps
import Jaune.MessageCall.StepGas

/-!
# Bridge: the message operations' gas obligations, transported (G2b, unit W3-2c)

`Jaune.MessageCall.StepGas` proves the two step-level obligations of `MessageOp.step`
(`MessageOp.step_gasDecreasing`, `MessageOp.step_halt`). The squares of
`Jaune.Bridge.G2b.MessageOps` carry both to the staged `Staging.MessageOp.step`, for every running
state (one whose RIPEMD-160 flag is down) and every context. The restated obligations
(`Staging.MessageOp.Outcome.GasDecreasing`, `Halt`) are what W3-3's driver totality reads.

These proofs go through the old step, so the module is a bridge artifact; a native proof replaces
it when the `Devm` interpreter is deleted.
-/

namespace Jaune

open Jaune

/-- An old outcome's call-family obligation carries to a new outcome it observes as. -/
theorem Staging.MessageOp.Outcome.gasDecreasing_of_observe {o : Jaune.MessageOp.Outcome}
    {o' : Staging.MessageOp.Outcome} {sevm : Sevm} {n : Nat} (h : o'.observe = o.observe)
    (hg : o.GasDecreasing sevm n) : o'.GasDecreasing (CallContext.ofSevm sevm) n := by
  cases o' with
  | done r =>
    cases o with
    | done ex =>
      intro s hr
      subst hr
      simp only [observe, Jaune.MessageOp.Outcome.observe, Except.ofHalt,
        MessageOp.Observation.done.injEq] at h
      rcases ex with ⟨e, d⟩ | d
      · simp [Frame.State.ofExecution, Except.mapResultState] at h
      · simp only [Frame.State.ofExecution, Except.mapResultState, Except.ok.injEq] at h
        subst h
        exact hg d rfl
    | spawn => simp [observe, Jaune.MessageOp.Outcome.observe] at h
  | spawn c p =>
    cases o with
    | done => simp [observe, Jaune.MessageOp.Outcome.observe] at h
    | spawn c' p' =>
      simp only [observe, Jaune.MessageOp.Outcome.observe, MessageOp.Observation.spawn.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hg

/-- An old outcome's halt obligation carries to a new outcome it observes as. -/
theorem Staging.MessageOp.Outcome.halt_of_observe {o : Jaune.MessageOp.Outcome}
    {o' : Staging.MessageOp.Outcome} {n : Nat} (h : o'.observe = o.observe) (hh : o.Halt n) :
    o'.Halt n := by
  cases o' with
  | done r =>
    cases o with
    | done ex =>
      rintro ⟨hr, s⟩ hp
      subst hp
      simp only [observe, Jaune.MessageOp.Outcome.observe, Except.ofHalt,
        MessageOp.Observation.done.injEq] at h
      rcases ex with ⟨e, d⟩ | d
      · simp only [Frame.State.ofExecution, Except.mapResultState, Except.error.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact (hh _ rfl).2
      · simp [Frame.State.ofExecution, Except.mapResultState] at h
    | spawn => simp [observe, Jaune.MessageOp.Outcome.observe] at h
  | spawn => trivial

/-- Every context is the image of a static machine. -/
theorem CallContext.exists_ofSevm (ctx : CallContext) : ∃ sevm, CallContext.ofSevm sevm = ctx :=
  ⟨({ context := ctx, kind := .call, codeAddress := none, target := none, gas := 0
      stateGasGrant := 0, transfersValue := false, disablePrecompiles := false } : Message).sevm,
    rfl⟩

/-- The call-family obligation of the staged step (`MessageOp.step_gasDecreasing`). -/
theorem Staging.MessageOp.step_gasDecreasing (ctx : CallContext) (s : Frame.State)
    (hflag : s.trail.touchedRIPEMD160 = false) (x : MessageOp) :
    (Staging.MessageOp.step ctx s x).GasDecreasing ctx s.machine.gasMeasure := by
  obtain ⟨sevm, rfl⟩ := CallContext.exists_ofSevm ctx
  rw [← Frame.State.ofDevm_toDevm hflag]
  exact Staging.MessageOp.Outcome.gasDecreasing_of_observe (Staging.MessageOp.step_ofDevm _ _ x)
    (Jaune.MessageOp.step_gasDecreasing sevm s.toDevm x)

/-- The halt obligation of the staged step (`MessageOp.step_halt`). -/
theorem Staging.MessageOp.step_halt (ctx : CallContext) (s : Frame.State)
    (hflag : s.trail.touchedRIPEMD160 = false) (x : MessageOp) {n : Nat} (hsn : s.spill ≤ n)
    (hn : s.machine.gasMeasure ≤ n) : (Staging.MessageOp.step ctx s x).Halt n := by
  obtain ⟨sevm, rfl⟩ := CallContext.exists_ofSevm ctx
  rw [← Frame.State.ofDevm_toDevm hflag]
  exact Staging.MessageOp.Outcome.halt_of_observe (Staging.MessageOp.step_ofDevm _ _ x)
    (Jaune.MessageOp.step_halt sevm s.toDevm x rfl hsn hn)

end Jaune
