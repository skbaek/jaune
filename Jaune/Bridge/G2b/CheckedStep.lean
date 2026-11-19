import Jaune.Bridge.G2b.CheckedControl
import Jaune.Bridge.G2b.CheckedPlain
import Jaune.Bridge.G2b.CheckedMessageOps
import Jaune.Bridge.G2b.CheckedOutcomes
import Jaune.MessageCall.FinalStep

namespace Jaune.MemorySimulation

instance eraseStep : Erases Checked.Step Staging.Step := ⟨Checked.Step.toLegacy⟩

private theorem Step.ofHalt (pc : Nat) {x : Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State}
    {y : Except (ExceptionalHalt × Frame.State) Frame.State} (h : Square x y) :
    Square (Checked.Step.ofHalt pc x) (Staging.Step.ofHalt pc y) := by
  change erase x = y at h
  subst y
  cases x with
  | error p => cases p; rfl
  | ok s => rfl

private theorem Step.ofJump {x : Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.Running}
    {y : Except (ExceptionalHalt × Frame.State) Frame.Running} (h : Square x y) :
    Square (Checked.Step.ofJump x) (Staging.Step.ofJump y) := by
  change erase x = y at h
  subst y
  cases x with
  | error p => cases p; rfl
  | ok r => rfl

private theorem MessageOp.Outcome.toStep (pc : Nat) (x : Checked.MessageOp.Outcome) :
    Square (x.toStep pc) (x.toLegacy.toStep pc) := by
  cases x with
  | done z => cases z with
    | error p => cases p; rfl
    | ok s => rfl
  | spawn f p => rfl

theorem NextOp.step (r : Checked.Frame.Running) (op : Jaune.NextOp) :
    Square (Checked.NextOp.step r op) (Staging.NextOp.step r.toLegacy op) := by
  rw [Checked.NextOp.step_arms]
  cases op <;> simp only [Checked.Arms.NextOp.step, Staging.NextOp.step]
  case message m =>
    change erase _ = (Staging.MessageOp.step r.context r.state.toLegacy m).toStep _
    rw [← (show (Checked.MessageOp.step r.context r.state m).toLegacy = _ from MessageOp.step ..)]
    apply MessageOp.Outcome.toStep
  case plain op =>
    apply Step.ofHalt
    rw [← Checked.PlainOp.run_arms]
    exact PlainOp.runCore r.pc r.context r.state op
  all_goals repeat' first | apply Step.ofHalt | checked_sq_one

theorem step (r : Checked.Frame.Running) :
    Staging.step r.toLegacy = (Checked.step r).map Checked.Step.toLegacy := by
  unfold Staging.step Checked.step
  change (match r.getOp with | none => _ | some (.next n) => _ | some (.jump j) => _ | some (.halt h) => _) = _
  cases r.getOp with
  | none => rfl
  | some op =>
    cases op with
    | next n => exact congrArg Except.ok (NextOp.step r n).symm
    | jump j => exact congrArg Except.ok (Step.ofJump (JumpOp.run r j)).symm
    | halt h =>
      dsimp only
      rw [show r.toLegacy.context = r.context from rfl, show r.toLegacy.state = r.state.toLegacy from rfl,
        ← (show erase (Checked.HaltOp.run r.context r.state h) = _ from HaltOp.run ..)]
      cases Checked.HaltOp.run r.context r.state h <;> rfl

end Jaune.MemorySimulation
