import Jaune.MessageCall.DriverInvariants
import Jaune.Bridge.Memory

namespace Jaune.MemoryReachability

def StepPost : Step → Prop
  | .halt (.ok d) | .halt (.error (_, d)) | .next _ d => d.memory.Wf
  | .spawn child _ _ => child.checkpoint.machine.memory.Wf

/-- Entry from a chosen start preserves its memory in the returned running machine. -/
theorem enterWith_run {f : Frame} {start : Devm} {evm : Evm}
    (hw : start.memory.Wf) (he : enterWith f start = .run evm) : evm.dyna.memory.Wf := by
  unfold enterWith at he
  dsimp only at he
  split at he
  · cases he
  · split at he
    · split at he
      · cases he
      · cases he; exact hw
    · cases he; exact hw

/-- A spawned child runs with freshly empty, well-formed memory. -/
theorem enter_run {f : Frame} {evm : Evm}
    (he : enter f = .run evm) : evm.dyna.memory.Wf :=
  enterWith_run (start := f.start) Mem.wf_empty he

private theorem resume_shape {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Devm) Devm}
    (h : resume rules p saved r = .ok x) :
    ∃ s : Frame.State, s.machine = absorbMeters rules p saved.machine r ∧
      (x = .ok (p.restore { s with machine := p.target.finish r s.machine }) ∨
        x = .error (.stackOverflow .none, p.restore s)) := by
  unfold resume at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨⟨_, _, _, _⟩, rfl, Or.inl rfl⟩)
    | (cases h; exact ⟨⟨_, _, _, _⟩, rfl, Or.inr rfl⟩)
    | cases h

private theorem absorbMeters_memory (rules : ForkRules) (p : Pending) (m : Machine)
    (r : Frame.Result) : (absorbMeters rules p m r).memory = m.memory := by
  unfold absorbMeters Machine.creditStateGasRefund Machine.repayStateGasSpill
  repeat' split
  all_goals rfl

private theorem finish_memory (target : ReturnTarget) (r : Frame.Result) (m : Machine) :
    (target.finish r m).memory = match target with
      | .call outputIndex outputSize => m.memory.write outputIndex (r.output.take outputSize)
      | .create _ => m.memory := by
  cases target <;> rfl

/-- Both the pushed caller and a caller halted on a full stack keep a well-formed memory. -/
theorem resume_post {rules : ForkRules}
    {p : Pending} {saved : Frame.State} {r : Frame.Result} {x : Except (ExceptionalHalt × Devm) Devm}
    (hw : saved.machine.memory.Wf) (h : resume rules p saved r = .ok x) :
    match x with | .ok d | .error (_,d) => d.memory.Wf := by
  obtain ⟨s, hs, hx | hx⟩ := resume_shape h <;> subst x
  · change (p.target.finish r s.machine).memory.Wf
    rw [finish_memory, hs, absorbMeters_memory]
    cases p.target with
    | call i n => exact hw.write _ _
    | create a => exact hw
  · change s.machine.memory.Wf
    rwa [hs, absorbMeters_memory]

end Jaune.MemoryReachability
