import Jaune.Bridge.G2b.CheckedOutcomes
import Jaune.Bridge.G2b.FinalStep
import Jaune.Bridge.G2b.MemoryReachability

namespace Jaune.MemoryReachability

private def RunningPost : Step → Prop
  | .halt _ => True
  | .next _ d => d.memory.Wf
  | .spawn f _ _ => f.checkpoint.machine.memory.Wf

private def StagedRunningPost : Except Fault Staging.Step → Prop
  | .ok (.next _ s) => s.machine.memory.Wf
  | .ok (.spawn f _ _) => f.checkpoint.machine.memory.Wf
  | _ => True

private theorem post_erase (x : Except Fault Checked.Step) :
    StagedRunningPost (x.map Checked.Step.toLegacy) := by
  cases x with
  | error f => trivial
  | ok st =>
    cases st with
    | exit e => trivial
    | next pc s => exact s.machine.memory.wf_toMem
    | spawn f p pc => exact f.checkpoint.machine.memory.wf_toMem

private theorem post_of_observe (x : Step) (h : StagedRunningPost x.observe) :
    RunningPost x := by
  cases x with
  | halt _ => trivial
  | next _ _ => exact h
  | spawn _ _ _ => exact h

variable (hstep : ∀ r : Checked.Frame.Running,
    Staging.step r.toLegacy = (Checked.step r).map Checked.Step.toLegacy)
include hstep

private theorem step_post (evm : Evm) (h : evm.dyna.memory.Wf) :
    RunningPost (Evm.step evm) := by
  let r := Checked.Frame.Running.ofLegacy (Frame.Running.ofEvm evm) h
  have hp : StagedRunningPost (Staging.step (Frame.Running.ofEvm evm)) := by
    change StagedRunningPost (Staging.step r.toLegacy)
    rw [hstep]
    exact post_erase _
  unfold Staging.step at hp
  rw [Frame.Running.getOp_ofEvm] at hp
  unfold Evm.step
  cases hi : evm.getInst with
  | none => trivial
  | some op =>
    cases op with
    | halt _ => trivial
    | next n =>
      rw [hi] at hp
      apply post_of_observe
      rw [Staging.NextOp.step_ofEvm]
      exact hp
    | jump j =>
      rw [hi] at hp
      apply post_of_observe
      rw [Step.observe_ofJump]
      exact hp

theorem reaches_memory_wf_of_step {start evm : Evm} (hw : start.dyna.memory.Wf)
    (h : start.Reaches evm) : evm.dyna.memory.Wf := by
  induction h with
  | refl => exact hw
  | next _ hs ih => have hp := step_post hstep _ ih; rwa [hs] at hp
  | enter _ _ he _ => exact enter_run he
  | resume _ hs _ hr ih =>
    have hp := step_post hstep _ ih
    rw [hs] at hp
    exact resume_post hp hr

theorem checkpoint_memory_wf_of_step {start evm : Evm} (hw : start.dyna.memory.Wf)
    (h : start.Reaches evm) {child : Frame} {p : Pending} {pc : Nat}
    (hs : Evm.step evm = .spawn child p pc) : child.checkpoint.machine.memory.Wf := by
  have hp := step_post hstep _ (reaches_memory_wf_of_step hstep hw h)
  rwa [hs] at hp

end Jaune.MemoryReachability
