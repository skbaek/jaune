import Jaune.MessageCall.CheckedGasFacts
import Jaune.MessageCall.CheckedPlainGasFacts
import Jaune.MessageCall.CheckedMessageGasFacts
import Jaune.Instructions.PushFacts

/-! Gas bounds at the boundary between one grouped frame step and the driver. -/
namespace Jaune.Checked

open Jaune

/-- A halt forfeits its execution gas. A finished or reverted frame retains its measure. -/
def Frame.Exit.SettledGasLe (n : Nat) : Frame.Exit → Prop
  | .finished _ s | .reverted _ s => s.machine.gasMeasure ≤ n
  | .halted _ s => s.spill ≤ n

/-- The spill bound accounts for exceptional settlement under either state-gas regime. -/
theorem Frame.Exit.halted_settledGasLe_iff (reason : ExceptionalHalt) (s : Frame.State)
    (n : Nat) : (Frame.Exit.halted reason s).SettledGasLe n ↔
      (s.withGasLeft 0).machine.gasMeasure ≤ n ∧
      s.machine.restoreStateGas.forfeitRemainingGas.gasMeasure ≤ n := by
  change s.machine.stateGas.spilled + s.machine.stateGas.committedSpill ≤ n ↔
    0 + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill ≤ n ∧
      0 + 0 + s.machine.stateGas.committedSpill ≤ n
  omega

/-- Restoring a reverted frame's meter preserves its measure. -/
theorem Frame.Exit.reverted_settledGasLe_iff (bytes : Bytes) (s : Frame.State)
    (n : Nat) : (Frame.Exit.reverted bytes s).SettledGasLe n ↔
      s.machine.gasMeasure ≤ n ∧ s.machine.restoreStateGas.gasMeasure ≤ n := by
  rw [Machine.restoreStateGas_gasMeasure]
  exact ⟨fun h => ⟨h, h⟩, And.left⟩

/-- An exit can settle, a continuation spends gas, and a child plus its checkpoint costs
strictly less than the calling frame's starting measure. -/
def Step.GasBound (ctx : Jaune.CallContext) (n : Nat) : Step → Prop
  | .exit e => e.SettledGasLe n
  | .next _ s => s.machine.gasMeasure < n
  | .spawn child _ _ => child.message.gas + child.checkpoint.machine.gasMeasure < n ∧
      child.message.context.block.rules = ctx.block.rules

private theorem spill_le (s : Frame.State) : s.spill ≤ s.machine.gasMeasure := by
  change s.machine.stateGas.spilled + s.machine.stateGas.committedSpill ≤
    s.machine.gasLeft + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill
  omega

private theorem ofHalt_bound {ctx : Jaune.CallContext} {pc n : Nat}
    {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (h : Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure < n) x) :
    (Step.ofHalt pc x).GasBound ctx n := by
  cases x with
  | error p => exact (spill_le p.2).trans h
  | ok s => exact h

private theorem messageStep_bound {ctx : Jaune.CallContext} {n pc : Nat} (o : MessageOp.Outcome)
    (h : o.GasDecreasing ctx n ∧ o.Halt n) : (o.toStep pc).GasBound ctx n := by
  cases o with
  | done result =>
    cases result with
    | error p => exact h.2 p rfl
    | ok s => exact h.1 s rfl
  | spawn child pending => exact h.1

theorem NextOp.step_gasBound (r : Frame.Running) (n : Jaune.NextOp) :
    (NextOp.step r n).GasBound r.context r.state.machine.gasMeasure := by
  cases n with
  | plain op => exact ofHalt_bound (PlainOp.runCore_gas r.pc r.context r.state op (Nat.le_refl _))
  | message op => exact messageStep_bound _ (MessageOp.step_gas r.context r.state op)
  | push xs _ => exact ofHalt_bound (WordRow.run_gas _ (NextOp.pushRow_cost_pos xs) r (Nat.le_refl _))
  | dupn imm =>
    exact ofHalt_bound (ShuffleRow.run_gas _ (by simp [NextOp.dupnRow, Gas.veryLow]) r (Nat.le_refl _))
  | swapn imm =>
    exact ofHalt_bound (ShuffleRow.run_gas _ (by simp [NextOp.swapnRow, Gas.veryLow]) r (Nat.le_refl _))
  | exchange imm =>
    exact ofHalt_bound (ShuffleRow.run_gas _ (by simp [NextOp.exchangeRow, Gas.veryLow]) r (Nat.le_refl _))

/-- Every successful driver step obeys the budget of the frame at its program counter. -/
theorem step_gasBound (r : Frame.Running) (out : Step) (h : step r = .ok out) :
    out.GasBound r.context r.state.machine.gasMeasure := by
  unfold step at h
  split at h
  · cases h
    exact spill_le r.state
  · cases h
    exact NextOp.step_gasBound _ _
  · rename_i j _
    have law := JumpOp.runCore_gas r.pc r.context r.state j (Nat.le_refl _)
    unfold JumpOp.run at h
    cases he : JumpOp.runCore r.pc r.context r.state j with
    | error p => rw [he] at law h; cases h; exact (spill_le p.2).trans law
    | ok p => rcases p with ⟨pc, s⟩; rw [he] at law h; cases h; exact law
  · rename_i l _
    cases he : HaltOp.run r.context r.state l with
    | error f => rw [he] at h; contradiction
    | ok e =>
      rw [he] at h
      cases h
      have law := HaltOp.run_gas _ _ _ e he
      cases e with
      | finished _ s | reverted _ s => exact law
      | halted _ s => exact (spill_le s).trans law

end Jaune.Checked
