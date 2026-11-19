import Jaune.MessageCall.Totality
import Jaune.MessageCall.FinalParts
import Jaune.MessageCall.FinalStepGasBound

/-! Gas at frame entry, settlement, and resumption. -/
namespace Jaune.Staging

open Jaune

theorem _root_.Jaune.Frame.Exit.SettledGasLe.mono {e : Frame.Exit} {m n : Nat}
    (h : e.SettledGasLe m) (hle : m ≤ n) : e.SettledGasLe n := by
  cases e <;> exact Nat.le_trans h hle

theorem _root_.Jaune.Frame.Exit.settledGasLe_of_measure {e : Frame.Exit} {n : Nat}
    (h : e.state.machine.gasMeasure ≤ n) : e.SettledGasLe n := by
  cases e with
  | finished _ s | reverted _ s => exact h
  | halted _ s =>
    change s.machine.gasLeft + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill ≤ n at h
    change s.machine.stateGas.spilled + s.machine.stateGas.committedSpill ≤ n
    omega

private theorem chargeDeposit_gas (rules : ForkRules) (code : Bytes) (s : Frame.State) {n : Nat}
    (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure ≤ n) (chargeDeposit rules code s) := by
  have chargeSize (c : Bytes) : Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure ≤ n) (do
      let t ← s.chargeGas (c.length * Gas.codeDeposit)
      if rules.code.maxCodeSize < c.length then .error (.outOfGas .none, t) else .ok t) := by
    apply Walk.bind (Frame.State.chargeGas_gas _ h)
    intro t ht
    change t.machine.gasMeasure + _ = s.machine.gasMeasure at ht
    split <;> change t.machine.gasMeasure ≤ n <;> omega
  unfold chargeDeposit
  dsimp only
  repeat' (first | exact h | apply chargeSize | split)
  all_goals
    apply Walk.bind (Frame.State.chargeGas_gas _ h)
    intro t ht
    change t.machine.gasMeasure + _ = s.machine.gasMeasure at ht
    apply Walk.mono (Frame.State.chargeStateGas_gas _ (by omega))
    intro u hu
    change u.machine.gasMeasure = t.machine.gasMeasure at hu
    omega

private theorem depositCode_gas (rules : ForkRules) (recipient : Address) (code : Bytes)
    (s : Frame.State) {n : Nat} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure ≤ n) (depositCode rules recipient code s) := by
  have hc := chargeDeposit_gas rules code s h
  unfold depositCode
  cases he : chargeDeposit rules code s with
  | error p => rw [he] at hc; exact hc
  | ok t => rw [he] at hc; exact hc

private theorem haltedResult_gas (rules : ForkRules) (s : Frame.State) (reason : ExceptionalHalt)
    (trail : Trail) {n : Nat} (h : s.spill ≤ n) :
    (Frame.Result.halt reason (match rules.stateGas with
      | none => s.machine.forfeitRemainingGas
      | some _ => s.machine.restoreStateGas.forfeitRemainingGas).stateGas trail).gasMeasure ≤ n := by
  change s.machine.stateGas.spilled + s.machine.stateGas.committedSpill ≤ n at h
  cases rules.stateGas
  · change 0 + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill ≤ n
    omega
  · change 0 + 0 + s.machine.stateGas.committedSpill ≤ n
    omega

/-- Settlement returns at most the gas covered by an exit, including a failed creation deposit. -/
theorem settle_gasLe {f : Frame} {raw : Frame.Exit} {n : Nat} {r : Frame.Result}
    (hraw : raw.SettledGasLe n) (h : settle f raw = .ok r) : r.gasMeasure ≤ n := by
  cases raw with
  | halted reason s =>
    cases h
    exact haltedResult_gas _ _ _ _ hraw
  | reverted bytes s =>
    cases h
    cases hs : f.message.context.block.rules.stateGas
    · exact hraw
    · change s.machine.restoreStateGas.gasMeasure ≤ n
      rw [Machine.restoreStateGas_gasMeasure]
      exact hraw
  | finished bytes s =>
    simp only [settle] at h
    split at h
    · cases h; exact hraw
    · rename_i hk
      have dep := depositCode_gas f.message.context.block.rules f.message.context.recipient bytes
        (s.recordTouch f.message.context.block.rules true f.message.context.recipient) (n := n) hraw
      split at h
      · rename_i t ht; rw [ht] at dep; cases h; exact dep
      · rename_i reason t ht
        rw [ht] at dep
        cases h
        apply haltedResult_gas
        change t.machine.gasLeft + t.machine.stateGas.spilled + t.machine.stateGas.committedSpill ≤ n at dep
        change t.machine.stateGas.spilled + t.machine.stateGas.committedSpill ≤ n
        omega

theorem enter_run_gasMeasure {f : Frame} {r : Frame.Running} (h : enter f = .run r) :
    r.state.machine.gasMeasure = f.message.gas := by
  unfold enter enterWith at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · split at h
      · contradiction
      · cases h; rfl
    · cases h; rfl

private theorem runPrecompile_gas (r : Frame.Running) (a : Address) {e : Frame.Exit}
    (h : runPrecompile r a = .ok e) : e.SettledGasLe r.state.machine.gasMeasure := by
  apply Frame.Exit.settledGasLe_of_measure
  unfold runPrecompile Frame.Exit.ofPrecompileResult at h
  split at h
  · cases h
    apply Nat.add_le_add_right
    apply Nat.add_le_add_right
    exact Nat.sub_le _ _
  · split at h <;> cases h <;>
      exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.sub_le _ _) _) _

/-- A child completing during entry stays within its message's gas grant. -/
theorem enter_done_gasLe {f : Frame} {r : Frame.Result} (h : enter f = .done (.ok r)) :
    r.gasMeasure ≤ f.message.gas := by
  unfold enter enterWith at h
  dsimp only at h
  cases hw : f.message.transfer f.enteredWorld with
  | error fault => rw [hw] at h; cases h
  | ok world =>
    rw [hw] at h
    cases ha : f.message.codeAddress with
    | none => rw [ha] at h; contradiction
    | some a =>
      rw [ha] at h
      dsimp only at h
      split at h
      · simp only [Frame.Entry.done.injEq] at h
        cases hp : runPrecompile (Frame.entered f f.startState world) a with
        | error fault => rw [hp] at h; contradiction
        | ok e =>
          rw [hp] at h
          exact settle_gasLe (runPrecompile_gas _ _ hp) h
      · contradiction

private theorem absorbMeters_gas (rules : ForkRules) (p : Pending) (saved : Machine) (r : Frame.Result) :
    (absorbMeters rules p saved r).gasMeasure ≤ saved.gasMeasure + r.gasMeasure := by
  unfold absorbMeters
  dsimp only
  split
  · simp only [Jaune.Machine.gasMeasure, Frame.Result.gasMeasure]; omega
  · split
    · split <;> try rw [Machine.creditStateGasRefund_gasMeasure]
      all_goals simp only [Jaune.Machine.gasMeasure, Frame.Result.gasMeasure]; omega
    · rw [Machine.repayStateGasSpill_gasMeasure]
      simp only [Jaune.Machine.gasMeasure, Frame.Result.gasMeasure]
      omega

private theorem finish_gas (target : ReturnTarget) (r : Frame.Result) (m : Machine) :
    (target.finish r m).gasMeasure = m.gasMeasure := by cases target <;> rfl

/-- Resuming or halting the caller uses at most the checkpoint measure plus the child result. -/
theorem resume_gasLe {rules : ForkRules} {p : Pending} {saved : Frame.State} {r : Frame.Result}
    {x : Except (ExceptionalHalt × Frame.State) Frame.State} (h : resume rules p saved r = .ok x) :
    Walk (·.machine.gasMeasure ≤ saved.machine.gasMeasure + r.gasMeasure)
      (·.machine.gasMeasure ≤ saved.machine.gasMeasure + r.gasMeasure) x := by
  have hm := absorbMeters_gas rules p saved.machine r
  unfold resume at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; exact hm)
    | (cases h; apply Nat.le_trans (Nat.le_of_eq (finish_gas _ _ _)) hm)
    | cases h

end Jaune.Staging
