import Jaune.SufficiencyWalk

/-! Gas bounds for instructions over the lifetime-grouped running state. -/

namespace Jaune

open Jaune

/-- Jumps charge execution gas on every continuation. A rejected jump stays within
the same upper bound as its input, including failures while popping its operands. -/
theorem JumpOp.runCore_gas (pc : Nat) (ctx : CallContext) (s : Frame.State) (op : Jaune.JumpOp)
    {n : Nat} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (fun p => p.2.machine.gasMeasure < s.machine.gasMeasure)
      (JumpOp.runCore pc ctx s op) := by
  cases op with
  | jumpdest =>
    apply Walk.bind (Frame.State.chargeGas_gas Gas.jumpdest h)
    intro t ht
    change t.machine.gasMeasure + 1 = s.machine.gasMeasure at ht
    change t.machine.gasMeasure < s.machine.gasMeasure
    omega
  | jump =>
    apply Walk.bind (Frame.State.pop_gas h)
    rintro ⟨dest, t⟩ ht
    change t.machine.gasMeasure = s.machine.gasMeasure at ht
    apply Walk.bind (Frame.State.chargeGas_gas Gas.mid (ht.trans_le h))
    intro u hu
    change u.machine.gasMeasure + 8 = t.machine.gasMeasure at hu
    apply Walk.bind (Walk.assert (by omega : u.machine.gasMeasure ≤ n))
    intro _ _
    change u.machine.gasMeasure < s.machine.gasMeasure
    omega
  | jumpi =>
    apply Walk.bind (Frame.State.pop_gas h)
    rintro ⟨dest, t⟩ ht
    change t.machine.gasMeasure = s.machine.gasMeasure at ht
    apply Walk.bind (Frame.State.pop_gas (ht.trans_le h))
    rintro ⟨cond, u⟩ hu
    change u.machine.gasMeasure = t.machine.gasMeasure at hu
    apply Walk.bind (Frame.State.chargeGas_gas Gas.high ((hu.trans ht).trans_le h))
    intro v hv
    change v.machine.gasMeasure + 10 = u.machine.gasMeasure at hv
    by_cases hz : cond = 0
    · simp only [hz, ite_true, bind, Except.bind, Walk.ok_iff]
      omega
    · simp only [hz, ite_false]
      unfold Except.assert
      split <;> simp only [bind, Except.bind, Walk.ok_iff, Walk.error_iff] <;> omega


private abbrev ExitGas (n : Nat) (result : Except Fault Frame.Exit) : Prop :=
  ∀ e, result = .ok e → e.state.machine.gasMeasure ≤ n

private theorem catchHalt_gas {n : Nat}
    {body : Except (ExceptionalHalt × Frame.State) (Except Fault Frame.Exit)}
    (h : Walk (·.machine.gasMeasure ≤ n) (ExitGas n) body) :
    ExitGas n (Frame.Exit.catchHalt body) := by
  cases body with
  | error e =>
    obtain ⟨reason, s⟩ := e
    intro exit he
    cases he
    exact h
  | ok res => exact h

private theorem return_gas (ctx : CallContext) (s : Frame.State) (isRevert : Bool) :
    ExitGas s.machine.gasMeasure
      (HaltOp.run ctx s (if isRevert then .revert else .return_)) := by
  cases isRevert <;> simp only [Bool.false_eq_true, ↓reduceIte, HaltOp.run] <;>
    apply catchHalt_gas <;>
    apply Walk.bind (Frame.State.popToNat_gas (Nat.le_refl _)) <;>
    rintro ⟨start, t⟩ ht <;>
    change t.machine.gasMeasure = s.machine.gasMeasure at ht <;>
    apply Walk.bind (Frame.State.popToNat_gas ht.le) <;>
    rintro ⟨size, u⟩ hu <;>
    change u.machine.gasMeasure = t.machine.gasMeasure at hu <;>
    apply Walk.bind (Frame.State.chargeGas_gas _ (hu.trans ht).le) <;>
    intro v hv <;> intro exit he <;> cases he <;>
    change (v.machine.readMemory start size).2.gasMeasure ≤ s.machine.gasMeasure <;>
    rw [Machine.readMemory_gasMeasure] <;>
    change v.machine.gasMeasure + _ = u.machine.gasMeasure at hv <;> omega


private theorem creditBeneficiary_machine (s : Frame.State) (rules : ForkRules) (a : Address) (v : U256) :
    (s.creditBeneficiary rules a v).machine = s.machine := by
  unfold Frame.State.creditBeneficiary
  split <;> rfl

private theorem emitTransferLog_machine (s : Frame.State) (a b : Address) (v : U256) :
    (s.emitTransferLog a b v).machine = s.machine := by
  unfold Frame.State.emitTransferLog
  split <;> rfl

private theorem selfdestructRefund_machine (s : Frame.State) (rules : ForkRules) (p : Prop)
    [Decidable p] : (s.creditSelfdestructRefund rules p).machine = s.machine := by
  unfold Frame.State.creditSelfdestructRefund
  split <;> rfl

private theorem subtractBalance_machine {s t : Frame.State} {a : Address} {v : U256}
    (h : s.subtractBalance a v = some t) : t.machine = s.machine := by
  unfold Frame.State.subtractBalance at h
  cases eqn : s.world.subtractBalance a v <;> rw [eqn] at h
  case none => contradiction
  case some w => cases h; rfl

private theorem selfdestruct_gas (ctx : CallContext) (s : Frame.State) :
    ExitGas s.machine.gasMeasure (HaltOp.run ctx s .selfdestruct) := by
  cases hs : ctx.block.rules.stateGas with
  | none =>
    simp only [HaltOp.run, hs]
    apply catchHalt_gas
    apply Walk.bind (Frame.State.popToAddress_gas (Nat.le_refl _))
    rintro ⟨donee, t⟩ ht
    change t.machine.gasMeasure = s.machine.gasMeasure at ht
    cases ha : ctx.block.rules.access <;> simp only [ha]
    all_goals
      repeat' split
      all_goals
        apply Walk.bind (Frame.State.chargeGas_gas _ (by
          simpa only [Frame.State.recordAccountRead, Frame.State.withTrail_machine,
            Frame.State.addAccessedAddress, Frame.State.withSubstate_machine] using ht.le))
        intro u hu
        simp only [Frame.State.recordAccountRead, Frame.State.withTrail_machine,
          Frame.State.addAccessedAddress, Frame.State.withSubstate_machine] at hu
        apply Walk.bind (Frame.State.assertDynamic_gas _ (by omega))
        intro _ _
        split
        · intro exit he; cases he
        · rename_i w hw
          have hwu := subtractBalance_machine hw
          split <;> intro exit he <;> cases he <;>
            simp only [Frame.Exit.state, selfdestructRefund_machine, Frame.State.addSelfDestruct,
              Frame.State.withSelfDestructs, Frame.State.withSubstate_machine, Frame.State.setBalance,
              Frame.State.clearStorageWritesIfEmpty, Frame.State.withState, Frame.State.withWorld_machine,
              creditBeneficiary_machine, hwu] <;> omega
  | some state =>
    simp only [HaltOp.run, hs]
    apply catchHalt_gas
    apply Walk.bind (Frame.State.assertDynamic_gas ctx (Nat.le_refl _))
    intro _ _
    apply Walk.bind (Frame.State.popToAddress_gas (Nat.le_refl _))
    rintro ⟨donee, t⟩ ht
    change t.machine.gasMeasure = s.machine.gasMeasure at ht
    apply Walk.bind (Walk.assert ht.le)
    intro _ _
    split <;>
      apply Walk.bind (Frame.State.chargeGas_gas _ (by
        simpa only [Frame.State.recordAccountRead, Frame.State.withTrail_machine,
          Frame.State.addAccessedAddress, Frame.State.withSubstate_machine] using ht.le)) <;>
      intro u hu <;>
      simp only [Frame.State.recordAccountRead, Frame.State.withTrail_machine,
        Frame.State.addAccessedAddress, Frame.State.withSubstate_machine] at hu <;>
      apply Walk.bind (Frame.State.chargeStateGas_gas _ (by omega)) <;>
      intro v hv
    all_goals
      split
      · intro exit he; cases he
      · rename_i w hw
        have hwv := subtractBalance_machine hw
        split <;> intro exit he <;> cases he <;>
          simp only [Frame.Exit.state, Frame.State.addSelfDestruct, Frame.State.withSelfDestructs,
            Frame.State.withSubstate_machine, emitTransferLog_machine, Frame.State.addBalance,
            Frame.State.withWorld_machine, hwv] <;> omega

/-- Every exit from a halting instruction stays within the starting gas measure. -/
theorem HaltOp.run_gas (ctx : CallContext) (s : Frame.State) (op : Jaune.HaltOp)
    (exit : Frame.Exit) (h : HaltOp.run ctx s op = .ok exit) :
    exit.state.machine.gasMeasure ≤ s.machine.gasMeasure := by
  cases op with
  | stop => cases h; exact Nat.le_refl _
  | revert => exact return_gas ctx s true exit h
  | return_ => exact return_gas ctx s false exit h
  | selfdestruct => exact selfdestruct_gas ctx s exit h

end Jaune
