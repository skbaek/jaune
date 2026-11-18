import Jaune.MessageCall.FinalStep
import Jaune.Bridge.G2b.Plain
import Jaune.Bridge.G2b.Control
import Jaune.Bridge.G2b.MessageOps

/-!
# Bridge: the staged `step` against `Evm.step` (G2b, unit W3-3)

Old side: `Jaune.Evm.step` and `Jaune.NextOp.step` (`Jaune/MessageCall/Step.lean`) at `bba27e95`,
unedited. New side: `Jaune.Staging.step` and `Jaune.Staging.NextOp.step`
(`Jaune.MessageCall.FinalStep`).

An old step is observed as a new one (`Step.observe`): a raw result through
`Frame.Exit.ofExecution` (a fault leaves on the fault channel), a continuing state through
`Frame.State.ofDevm`, a spawn's `Pending` without its two residue fields
(`Staging.Pending.ofLegacy`). The square `Staging.step_ofEvm` holds for every running machine whose
`Devm` carries no output, which every running frame satisfies (`Jaune.Bridge.G2b.FinalDriver`
proves that the driver only ever runs such machines); the premise is the one of W3-2b's halt
square, which the halt arm uses.

Everything here goes with `Devm` after G2b's tag.
-/

namespace Jaune

open Frame.State Jaune.Bridge.G2b

/-- An old step, observed as a new one. -/
def Step.observe : Step → Except Fault Staging.Step
  | .halt ex => (Frame.Exit.ofExecution ex).map .exit
  | .next pc d => .ok (.next pc (ofDevm d))
  | .spawn child pending pc => .ok (.spawn child (Staging.Pending.ofLegacy pending) pc)

/-- A frame-local result whose square holds is observed as the new frame-local step. -/
theorem Step.observe_ofExecution {pc : Nat} {ex : Execution}
    {y : Except (ExceptionalHalt × Frame.State) Frame.State}
    (h : Frame.State.ofExecution ex = Except.ofHalt y) :
    (Jaune.Step.ofExecution pc ex).observe = .ok (Staging.Step.ofHalt pc y) := by
  rcases ex with ⟨e, d⟩ | d <;> rcases y with ⟨r, s⟩ | s <;>
    simp only [Frame.State.ofExecution, Except.mapResultState, Except.ofHalt, reduceCtorEq,
      Except.error.injEq, Except.ok.injEq, Prod.mk.injEq] at h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · subst h; rfl

/-- A message operation's outcome that observes as a new one steps as it. -/
theorem Step.observe_toStep {pc : Nat} {o : MessageOp.Outcome} {o' : Staging.MessageOp.Outcome}
    (h : o'.observe = o.observe) : (Jaune.MessageOp.Outcome.toStep pc o).observe = .ok (o'.toStep pc) := by
  cases o' with
  | done r =>
    cases o with
    | done ex =>
      simp only [Staging.MessageOp.Outcome.observe, MessageOp.Outcome.observe,
        MessageOp.Observation.done.injEq] at h
      exact Step.observe_ofExecution h.symm
    | spawn => simp [Staging.MessageOp.Outcome.observe, MessageOp.Outcome.observe] at h
  | spawn c p =>
    cases o with
    | done => simp [Staging.MessageOp.Outcome.observe, MessageOp.Outcome.observe] at h
    | spawn c' p' =>
      simp only [Staging.MessageOp.Outcome.observe, MessageOp.Outcome.observe,
        MessageOp.Observation.spawn.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-- A jump steps as the staged jump. -/
theorem Step.observe_ofJump (evm : Evm) (j : JumpOp) :
    (Jaune.Step.ofJump (j.run evm)).observe =
      .ok (Staging.Step.ofJump (Staging.JumpOp.run (Frame.Running.ofEvm evm) j)) := by
  have h := Frame.Running.ofJumpOutcome_run evm j
  revert h
  generalize j.run evm = o
  generalize Staging.JumpOp.run (Frame.Running.ofEvm evm) j = n
  intro h
  rcases o with ⟨e, d⟩ | ⟨pc, d⟩ <;> rcases n with ⟨r, s⟩ | r <;>
    simp only [Frame.Running.ofJumpOutcome, Except.ofHalt, reduceCtorEq, Except.error.injEq,
      Except.ok.injEq, Prod.mk.injEq] at h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · subst h; rfl

/-- `DUPN`, `SWAPN` and `EXCHANGE`'s shared shape: the availability check, the charge, then a
continuation that commutes. -/
private theorem sq_stackAccess {c : Bool} {d : Devm} {f : Devm → Execution}
    {g : Frame.State → Except (ExceptionalHalt × Frame.State) Frame.State}
    (hf : ∀ d, ofExecution (f d) = Except.ofHalt (g (ofDevm d))) :
    ofExecution (if c = true then Jaune.chargeGas Gas.veryLow d >>= f
      else .error ⟨.halt (.invalidOpcode .none), d⟩) =
      Except.ofHalt (if c = true then (ofDevm d).chargeGas Gas.veryLow >>= g
      else .error (.invalidOpcode .none, ofDevm d)) :=
  sq_ite (fun _ => sq_bind (ofExecution_chargeGas _ d) hf) (fun _ => rfl)

/-- The square for the operations that go on to the next instruction. -/
theorem Staging.NextOp.step_ofEvm (evm : Evm) (n : NextOp) :
    (Jaune.NextOp.step evm n).observe = .ok (Staging.NextOp.step (Frame.Running.ofEvm evm) n) := by
  cases n with
  | plain op => exact Step.observe_ofExecution (PlainOp.run_square evm op)
  | message x => exact Step.observe_toStep (Staging.MessageOp.step_ofEvm evm x)
  | push xs hxs =>
    unfold Jaune.NextOp.step Staging.NextOp.step
    dsimp only [Frame.Running.ofEvm, CallContext.ofSevm]
    split
    · exact Step.observe_ofExecution rfl
    · exact Step.observe_ofExecution
        (sq_bind (ofExecution_chargeGas _ evm.dyna) (fun d => ofExecution_push _ d))
  | dupn imm =>
    refine Step.observe_ofExecution (sq_stackAccess fun d => ?_)
    cases decodeSingle imm with
    | none => rfl
    | some k =>
      show ofExecution (match d.stack[k - 1]? with
        | none => .error ⟨.halt (.stackUnderflow .none), d⟩
        | some word => d.push word) = Except.ofHalt (match (ofDevm d).stack[k - 1]? with
        | none => .error (.stackUnderflow .none, ofDevm d)
        | some word => (ofDevm d).push word)
      rw [ofDevm_stack]
      cases d.stack[k - 1]? with
      | none => rfl
      | some word => exact ofExecution_push word d
  | swapn imm =>
    refine Step.observe_ofExecution (sq_stackAccess fun d => ?_)
    cases decodeSingle imm with
    | none => rfl
    | some k =>
      show ofExecution (match List.swap d.stack (k - 1) with
        | none => .error ⟨.halt (.stackUnderflow .none), d⟩
        | some stack => .ok (d.withStack stack)) = _
      show _ = Except.ofHalt (match List.swap (ofDevm d).stack (k - 1) with
        | none => .error (.stackUnderflow .none, ofDevm d)
        | some stack => .ok ((ofDevm d).withStack stack))
      rw [ofDevm_stack]
      cases List.swap d.stack (k - 1) with
      | none => rfl
      | some stack => rfl
  | exchange imm =>
    refine Step.observe_ofExecution (sq_stackAccess fun d => ?_)
    cases decodePair imm with
    | none => rfl
    | some p =>
      rcases p with ⟨a, b⟩
      show ofExecution (match List.exchange d.stack a b with
        | none => .error ⟨.halt (.stackUnderflow .none), d⟩
        | some stack => .ok (d.withStack stack)) = _
      show _ = Except.ofHalt (match List.exchange (ofDevm d).stack a b with
        | none => .error (.stackUnderflow .none, ofDevm d)
        | some stack => .ok ((ofDevm d).withStack stack))
      rw [ofDevm_stack]
      cases List.exchange d.stack a b with
      | none => rfl
      | some stack => rfl

/-- The square for one step: the staged step of the running frame is the old step, observed. It
holds for every running machine with no output, every fork. -/
theorem Staging.step_ofEvm (evm : Evm) (ho : evm.dyna.output = []) :
    Staging.step (Frame.Running.ofEvm evm) = (Jaune.Evm.step evm).observe := by
  unfold Staging.step Jaune.Evm.step
  rw [Frame.Running.getOp_ofEvm]
  cases evm.getInst with
  | none => rfl
  | some op =>
    cases op with
    | next n => exact (Staging.NextOp.step_ofEvm evm n).symm
    | jump j => exact (Step.observe_ofJump evm j).symm
    | halt l =>
      show _ = (Frame.Exit.ofExecution (l.run evm.sta evm.dyna)).map _
      rw [Frame.Running.ofExecution_haltRun evm ho l]

end Jaune
