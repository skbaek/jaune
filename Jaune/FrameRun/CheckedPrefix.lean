import Jaune.FrameRun.CheckedAdequacy

namespace Jaune.Checked

/-- The child result supplied to the caller, either at entry or after the completed child run. -/
inductive Frame.ChildResult (child : Frame) : Except Fault Frame.Result → Prop
  | done {res} (h : enter child = .done res) : Frame.ChildResult child res
  | ran {cr} (h : enter child = .run cr) : Frame.ChildResult child (exec cr >>= settle child)

/-- A successful instruction continuation strictly decreases the running machine's gas measure. -/
theorem Frame.Running.step_cont_gasMeasure_lt {r : Frame.Running} {pc s}
    (h : step r = .ok (.next pc s)) : s.machine.gasMeasure < r.state.machine.gasMeasure :=
  step_gasBound r _ h

/-- Returning from a spawned child strictly decreases the caller's gas measure. -/
theorem Frame.Running.call_gasMeasure_lt {r : Frame.Running} {child pending pc result s}
    (hs : step r = .ok (.spawn child pending pc)) (hc : Frame.ChildResult child result)
    (hr : resumeCaller r.context.block.rules child pending result = .ok s) :
    s.machine.gasMeasure < r.state.machine.gasMeasure := by
  have hb := (step_gasBound r _ hs).1
  have resultBound : ∀ v, result = .ok v → v.gasMeasure ≤ child.message.gas := by
    cases hc with
    | done he => rintro v rfl; exact enter_done_gasLe he
    | @ran cr he =>
      intro v hv
      cases hx : exec cr with
      | error fault => rw [hx] at hv; contradiction
      | ok exit =>
        rw [hx] at hv
        have bound := execFueled_settledGasLe _ cr ((execFueled_run_sufficientFuel cr).trans (congrArg some hx))
        rw [enter_run_gasMeasure he] at bound
        exact settle_gasLe bound hv
  cases result with
  | error fault => cases hr
  | ok v =>
    have hv := resultBound v rfl
    simp only [resumeCaller] at hr
    rcases he : resume r.context.block.rules pending child.checkpoint v with f | ⟨reason, state⟩ | state <;>
      rw [he] at hr
    · contradiction
    · contradiction
    · cases hr
      have bound := resume_gasLe he
      change s.machine.gasMeasure ≤ child.checkpoint.machine.gasMeasure + v.gasMeasure at bound
      omega

namespace Frame.Run

/-- Induct forward over same-frame steps. A call premise supplies the child's actual returned result. -/
theorem prefix_induction {P : Frame.Running → Prop}
    (next : ∀ {r pc s}, step r = .ok (.next pc s) → P r → P ⟨pc, r.context, s⟩)
    (call : ∀ {r child pending pc res s}, step r = .ok (.spawn child pending pc) →
      Frame.ChildResult child res → resumeCaller r.context.block.rules child pending res = .ok s →
      P r → P ⟨pc, r.context, s⟩) {r s} (p : Prefix r s) (initial : P r) : P s := by
  cases p with
  | stop => exact initial
  | next hs rest => exact prefix_induction next call rest (next hs initial)
  | callDone hs he hr rest => exact prefix_induction next call rest (call hs (.done he) hr initial)
  | callRan hs he child hr rest =>
    have hout := (exec_iff ..).mp ⟨child⟩
    exact prefix_induction next call rest (call hs (.ran he) (by simpa only [hout] using hr) initial)
termination_by sizeOf p

/-- A prefix's end has at most the starting amount of gas. -/
theorem Prefix.gasMeasure_le {r s} (p : Prefix r s) :
    s.state.machine.gasMeasure ≤ r.state.machine.gasMeasure :=
  prefix_induction (P := fun x => x.state.machine.gasMeasure ≤ r.state.machine.gasMeasure)
    (fun hs ih => (Frame.Running.step_cont_gasMeasure_lt hs).le.trans ih)
    (fun hs hc hr ih => (Frame.Running.call_gasMeasure_lt hs hc hr).le.trans ih) p (Nat.le_refl _)

end Frame.Run
end Jaune.Checked
