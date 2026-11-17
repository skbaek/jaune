import Jaune.Sufficiency
import Jaune.MessageCall.Step

/-!
# Totality of the staged driver: the step-level obligation (goal `jaune-shape-and-names-v1`, W1 unit G)

The staged `Evm.step` (`Jaune.MessageCall.Step`) keeps today's call-family bodies and changes
only what a spawn carries: the child's `Frame` (its message and its caller's checkpoint) and the
caller's `Pending` continuation. This module ports today's step-level gas corpus from
`Jaune.Sufficiency` to it: `MessageOp.Outcome.GasDecreasing` (today's `XStep.GasDecreasing`), the
`Halt` obligation of the call-family halt branch, and `Step.GasBound` with
`Evm.step_gasBound`.

The measure a spawn leaves its caller is now its checkpoint's (`Frame.parentGas`, today's
`Resume.parentGas`). Everything that does not mention the step type -- the pricing walks, the
`HaltLe` combinators, the non-call instruction corpus -- is reused from `Jaune.Sufficiency`
unchanged. Staged under `Jaune.Staging`; nothing outside the staged chain reads it.
-/

namespace Jaune

open Jaune

namespace Staging

/-! ## The measures a spawn and a result carry -/

/-- A lifetime-grouped state's gas measure: today's `Devm.gasMeasure` on its machine. -/
def Frame.State.gasMeasure (s : Frame.State) : Nat :=
  s.machine.gasLeft + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill

@[simp] theorem Frame.State.gasMeasure_ofDevm (d : Devm) :
    (Frame.State.ofDevm d).gasMeasure = d.gasMeasure := rfl

@[simp] theorem Frame.State.toDevm_gasMeasure (s : Frame.State) :
    s.toDevm.gasMeasure = s.gasMeasure := rfl

/-- The measure a spawn retains for its caller, before the child's leftover is added back:
the checkpoint's (today's `Resume.parentGas`, the saved caller's measure). -/
def Frame.parentGas (f : Frame) : Nat := f.checkpoint.gasMeasure

/-! ## The call-family obligation -/

/-- The step-level obligation for a call-type instruction, measured against the frame's gas at
the start of the step (today's `XStep.GasDecreasing`).

The spawn case is the single arithmetic fact `child.message.gas + child.parentGas < n`, with
the child running under the spawning frame's rules. The driver's other spawn obligations follow
from it generically: `enter` hands a running child exactly `child.message.gas`, neither the child
nor `settle` can increase that, and `resume` returns at most the checkpoint's measure plus the
result's (`Jaune.MessageCall.Totality`). -/
def MessageOp.Outcome.GasDecreasing (sevm : Sevm) (n : Nat) : MessageOp.Outcome → Prop
  | .done ex => ∀ devm', ex = .ok devm' → devm'.gasMeasure < n
  | .spawn child _ =>
      child.message.gas + child.parentGas < n ∧
        child.message.context.block.rules = sevm.benvStat.rules

theorem MessageOp.Outcome.ofExcept_gasDecreasing {sevm : Sevm} {n : Nat}
    {x : Except (EvmError × Devm) MessageOp.Outcome}
    (h : ∀ step, x = .ok step → step.GasDecreasing sevm n) :
    (MessageOp.Outcome.ofExcept x).GasDecreasing sevm n := by
  cases x with
  | error e => intro devm' hd; exact absurd hd (by simp)
  | ok step => exact h step rfl

/-- The call-family spawn, stated once for all six dispatch sites. The single
hypothesis is what each `Xinst` constructor has to establish: the gas the parent
keeps, plus the whole budget handed to the child, is still strictly less than
what the parent had when the step began. The depth-0 refund branch hands the
budget straight back, so it needs exactly the same inequality. -/
theorem genericCall.step_gasDecreasing
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) {n : Nat}
    (hn : devm.gasMeasure + gas < n) :
    (genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles).GasDecreasing sevm n := by
  unfold genericCall.step
  split
  · apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨d1, p1, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    intro devm' hd
    simp only [Except.ok.injEq] at hd
    rw [← hd, Devm.push_gasMeasure p1]
    simp only [Devm.withGasLeft_gasMeasure, Devm.withReturnData_gasLeft,
      Devm.withReturnData_spill]
    have hm := Devm.gasMeasure_eq devm
    omega
  · -- The spawn owes two things now: the arithmetic, and that the child runs
    -- under the spawning frame's rules -- which holds by construction, since
    -- `callMessage` copies `sevm.benvStat` verbatim.
    refine ⟨?_, rfl⟩
    show Message.gas _ + Frame.parentGas _ < n
    simp only [callMessage, Frame.parentGas, Frame.State.gasMeasure_ofDevm, Devm.withReturnData_gasMeasure]
    omega

theorem genericCallAmsterdam.step_gasDecreasing
    (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    (gas reservoir : Nat) (value : U256)
    (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray)
    (disablePrecompiles newAccountCharged insufficientBalance : Bool) {n : Nat}
    (hn : devm.gasMeasure + gas < n) :
    (genericCallAmsterdam.step sevm state devm gas reservoir value caller target
      codeAddress shouldTransferValue isStaticcall inputIndex inputSize
      outputIndex outputSize code disablePrecompiles newAccountCharged
      insufficientBalance).GasDecreasing sevm n := by
  unfold genericCallAmsterdam.step
  split
  · apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨d1, p1, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    intro devm' hd
    simp only [Except.ok.injEq] at hd
    rw [← hd, Devm.push_gasMeasure p1]
    split <;>
      simp only [Devm.withReturnData_gasMeasure, Devm.restoreChildGas_gasMeasure,
        Devm.creditStateGasRefund_gasMeasure] <;>
      omega
  · refine ⟨?_, rfl⟩
    show Message.gas _ + Frame.parentGas _ < n
    simp only [callMessage, Frame.parentGas, Frame.State.gasMeasure_ofDevm,
      Devm.withReturnData_gasMeasure]
    omega

theorem MessageOp.step_call_gasDecreasing_legacy (sevm : Sevm) (devm : Devm)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    (MessageOp.step sevm devm .call).GasDecreasing sevm devm.gasMeasure := by
  have hv := Sevm.rules_valid sevm
  have hacc := hv.access
  -- The access step, of either shape: the arms reduce by `match` on the
  -- schedule, and both leave a positive price `pre` and a gas-neutral `dA`.
  rcases hA : sevm.benvStat.rules.access with g | _ <;> rw [hA] at hacc
  all_goals
    simp only [MessageOp.step, hstate, hA]
    apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨callee, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨value, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputIndex, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputSize, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputIndex, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputSize, d7⟩, p7, hstep⟩ := Except.bind_eq_ok hstep
    dsimp only at hstep
    have e1 := Devm.pop_gasMeasure p1
    have e2 := Devm.popToAdr_gasMeasure p2
    have e3 := Devm.pop_gasMeasure p3
    have e4 := Devm.popToNat_gasMeasure p4
    have e5 := Devm.popToNat_gasMeasure p5
    have e6 := Devm.popToNat_gasMeasure p6
    have e7 := Devm.popToNat_gasMeasure p7
    dsimp only at e2 e3 e4 e5 e6 e7
  on_goal 1 =>
    have hpre : 0 < g.call := by
      simp only [AccessSchedule.Valid, FlatAccessGas.Valid] at hacc
      omega
    generalize g.call = pre at hpre hstep
    let dA := d7
    have hdA : dA.gasMeasure = d7.gasMeasure := rfl
  on_goal 2 =>
    have hpre := GasSchedule.access_cost_pos hv.gas callee d7.accessedAddresses
    have hdA := addAccessedAddress_gasMeasure d7 callee
    generalize sevm.benvStat.rules.gas.accessCost callee d7.accessedAddresses = pre at hpre hstep
    generalize addAccessedAddress d7 callee = dA at hdA hstep
  all_goals
    -- The delegation lookup can warm one more address but never touches gas.
    have eA : (sevm.benvStat.rules.accessDelegation
        dA callee).2.2.2.2.gasMeasure = devm.gasMeasure := by
      rw [ForkRules.accessDelegation_gasMeasure, hdA]
      omega
    -- `extra_gas` strictly covers the stipend: a warm access alone costs 100, and
    -- a value-bearing call pays `gasCallValue` against a `gCallStipend` stipend.
    have hstip :
        (if value.toNat = 0 then 0 else Gas.callStipend) <
          ((pre +
                (sevm.benvStat.rules.accessDelegation
                  dA callee).2.2.2.1 +
              if ¬((sevm.benvStat.rules.accessDelegation
                      dA callee).2.2.2.2.getAcct
                      callee).isEmpty ∨ value = 0 then 0 else Gas.newAccount) +
            if value = 0 then 0 else sevm.benvStat.rules.gas.callValue) +
          d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
      have hcall := GasSchedule.Valid.stipend_le_callValue hv.gas
      by_cases hv : value = 0
      · have : value.toNat = 0 := by rw [hv]; rfl
        rw [ite_eq_left this]
        omega
      · rw [ite_eq_right hv]
        split <;> omega
    obtain ⟨d8, pcharge, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨-, -, hstep⟩ := Except.bind_eq_ok hstep
    have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
    split at hstep
    · -- Insufficient sender balance: the stipend is refunded, nothing is spawned.
      obtain ⟨d9, ppush, hstep⟩ := Except.bind_eq_ok hstep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      intro devm' hd
      simp only [Except.ok.injEq] at hd
      rw [← hd]
      simp only [Devm.withGasLeft_gasMeasure, Devm.withReturnData_spill]
      rw [Nat.add_right_comm, ← Devm.gasMeasure_eq, Devm.push_gasMeasure ppush,
        Devm.memExtends_gasMeasure]
      exact key
    · -- The spawn: the child's whole budget is the stipend.
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      apply genericCall.step_gasDecreasing
      rw [Devm.memExtends_gasMeasure]
      exact key

theorem MessageOp.step_call_gasDecreasing (sevm : Sevm) (devm : Devm) :
    (MessageOp.step sevm devm .call).GasDecreasing sevm devm.gasMeasure := by
  have hv := Sevm.rules_valid sevm
  simp only [MessageOp.step]
  split
  · simpa only [MessageOp.step, *] using
      MessageOp.step_call_gasDecreasing_legacy sevm devm (by assumption)
  · rename_i state hstate
    apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨callee, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨value, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputIndex, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputSize, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputIndex, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputSize, d7⟩, p7, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hstatic, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hpre, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hfull, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d8, pcharge, hstep⟩ := Except.bind_eq_ok hstep
    have e1 := Devm.pop_gasMeasure p1
    have e2 := Devm.popToAdr_gasMeasure p2
    have e3 := Devm.pop_gasMeasure p3
    have e4 := Devm.popToNat_gasMeasure p4
    have e5 := Devm.popToNat_gasMeasure p5
    have e6 := Devm.popToNat_gasMeasure p6
    have e7 := Devm.popToNat_gasMeasure p7
    dsimp only at e1 e2 e3 e4 e5 e6 e7
    have eA :
        (completeDelegationAccess
          (Devm.balReadAccount sevm.benvStat.rules
            (sevm.benvStat.rules.delegationCost
              (addAccessedAddress d7 callee) callee).2.1
            (Devm.balReadAccount sevm.benvStat.rules callee (addAccessedAddress d7 callee)))
          (sevm.benvStat.rules.delegationCost
            (addAccessedAddress d7 callee) callee).1
          (sevm.benvStat.rules.delegationCost
            (addAccessedAddress d7 callee) callee).2.1).2.gasMeasure =
          devm.gasMeasure := by
      rw [completeDelegationAccess_gasMeasure]
      simp only [Devm.balReadAccount_gasMeasure, addAccessedAddress_gasMeasure]
      omega
    have hstip :
        (if value.toNat = 0 then 0 else Gas.callStipend) <
          (sevm.benvStat.rules.gas.accessCost callee d7.accessedAddresses +
              (if value = 0 then 0 else sevm.benvStat.rules.gas.callValue) +
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d7 callee) callee).2.2) +
            d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
      have hac := GasSchedule.access_cost_pos hv.gas callee d7.accessedAddresses
      have hcall := GasSchedule.Valid.stipend_le_callValue hv.gas
      by_cases hvalue : value = 0
      · have : value.toNat = 0 := by rw [hvalue]; rfl
        rw [ite_eq_left this, ite_eq_left hvalue]
        omega
      · have hto : value.toNat ≠ 0 := by
          intro hz
          exact hvalue (U256.toNat_inj value 0 (by rw [hz, U256.toNat_zero]))
        rw [ite_eq_right hto, ite_eq_right hvalue]
        omega
    have echarge := chargeGas_gasMeasure pcharge
    dsimp only at echarge hstep
    have hchargeCost :
        d8.gasMeasure +
            ((sevm.benvStat.rules.gas.accessCost callee d7.accessedAddresses +
                (if value = 0 then 0 else sevm.benvStat.rules.gas.callValue) +
                (sevm.benvStat.rules.delegationCost
                  (addAccessedAddress d7 callee) callee).2.2) +
              d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) =
          devm.gasMeasure := by
      calc
        _ = (completeDelegationAccess
              (Devm.balReadAccount sevm.benvStat.rules
                (sevm.benvStat.rules.delegationCost
                  (addAccessedAddress d7 callee) callee).2.1
                (Devm.balReadAccount sevm.benvStat.rules callee (addAccessedAddress d7 callee)))
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d7 callee) callee).1
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d7 callee) callee).2.1).2.gasMeasure := echarge
        _ = devm.gasMeasure := eA
    have hpaid :
        d8.gasMeasure + (if value.toNat = 0 then 0 else Gas.callStipend) <
          devm.gasMeasure := by
      calc
        _ < d8.gasMeasure +
              ((sevm.benvStat.rules.gas.accessCost callee d7.accessedAddresses +
                  (if value = 0 then 0 else sevm.benvStat.rules.gas.callValue) +
                  (sevm.benvStat.rules.delegationCost
                    (addAccessedAddress d7 callee) callee).2.2) +
                d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) :=
            Nat.add_lt_add_left hstip _
        _ = devm.gasMeasure := hchargeCost
    split at hstep
    · obtain ⟨d9, pstate, hstep⟩ := Except.bind_eq_ok hstep
      obtain ⟨d10, pcall, hstep⟩ := Except.bind_eq_ok hstep
      have estate := chargeStateGas_gasMeasure pstate
      have ecall := chargeGas_gasMeasure pcall
      have hcalc := calculateMsgCallGas_zero_cost value.toNat gas.toNat d9.gasLeft
        Gas.callStipend
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      apply genericCallAmsterdam.step_gasDecreasing
      rw [Devm.memExtends_gasMeasure,
        Devm.drainStateGasReservoir_gasMeasure]
      omega
    · simp only [bind, Except.bind] at hstep
      obtain ⟨d9, pcall, hstep⟩ := Except.bind_eq_ok hstep
      have ecall := chargeGas_gasMeasure pcall
      have hcalc := calculateMsgCallGas_zero_cost value.toNat gas.toNat d8.gasLeft
        Gas.callStipend
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      apply genericCallAmsterdam.step_gasDecreasing
      rw [Devm.memExtends_gasMeasure,
        Devm.drainStateGasReservoir_gasMeasure]
      omega

theorem genericCreate.step_gasDecreasing
    (sevm : Sevm) (devm : Devm) (endowment : U256)
    (newAddress : Address) (memoryIndex memorySize : Nat) {n : Nat}
    (hn : devm.gasMeasure < n) :
    MessageOp.Outcome.GasDecreasing sevm n
      (genericCreate.step sevm devm endowment newAddress memoryIndex memorySize) := by
  unfold genericCreate.step
  apply MessageOp.Outcome.ofExcept_gasDecreasing
  intro step hstep
  obtain ⟨_, _hsize, hstep⟩ := Except.bind_eq_ok hstep
  dsimp only at hstep
  obtain ⟨_, _hdynamic, hstep⟩ := Except.bind_eq_ok hstep
  split at hstep
  · obtain ⟨d1, hpush, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    intro devm' hd
    simp only [Except.ok.injEq] at hd
    rw [← hd, Devm.push_gasMeasure hpush]
    simp only [Devm.withGasLeft_gasMeasure, Devm.withGasLeft_gasLeft,
      Devm.withReturnData_gasLeft, Devm.withReturnData_spill,
      Devm.withGasLeft_spill]
    have hle := except64th_le devm.gasLeft
    have hm := Devm.gasMeasure_eq devm
    omega
  · split at hstep
    · obtain ⟨d1, hpush, hstep⟩ := Except.bind_eq_ok hstep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      intro devm' hd
      simp only [Except.ok.injEq] at hd
      rw [← hd, Devm.push_gasMeasure hpush, addAccessedAddress_gasMeasure,
        Devm.incrNonce_gasMeasure, Devm.withReturnData_gasMeasure,
        Devm.withGasLeft_gasMeasure]
      have hm := Devm.gasMeasure_eq devm
      omega
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      refine ⟨?_, rfl⟩
      show Message.gas _ + Frame.parentGas _ < n
      simp only [createMessage, Frame.parentGas, Frame.State.gasMeasure_ofDevm,
        addAccessedAddress_gasMeasure,
        Devm.incrNonce_gasMeasure, Devm.withReturnData_gasMeasure,
        Devm.withGasLeft_gasMeasure]
      have hle := except64th_le devm.gasLeft
      have hm := Devm.gasMeasure_eq devm
      omega

theorem genericCreateAmsterdam.step_gasDecreasing
    (sevm : Sevm) (state : StateGasRules) (devm : Devm) (endowment : U256)
    (newAddress : Address) (memoryIndex memorySize : Nat) {n : Nat}
    (hn : devm.gasMeasure < n) :
    (genericCreateAmsterdam.step sevm state devm endowment newAddress
      memoryIndex memorySize).GasDecreasing sevm n := by
  unfold genericCreateAmsterdam.step
  apply MessageOp.Outcome.ofExcept_gasDecreasing
  intro step hstep
  dsimp only at hstep
  split at hstep
  · obtain ⟨d1, hpush, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    intro devm' hd
    simp only [Except.ok.injEq] at hd
    rw [← hd, Devm.push_gasMeasure hpush]
    simpa only [Devm.balReadAccount_gasMeasure, Devm.withReturnData_gasMeasure] using hn
  · have eaccess :
        (Devm.balReadAccount sevm.benvStat.rules newAddress
          (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
            (devm.withReturnData [])) newAddress)).gasMeasure =
          devm.gasMeasure := by simp
    split at hstep
    · obtain ⟨d1, hstate, hstep⟩ := Except.bind_eq_ok hstep
      have estate := chargeStateGas_gasMeasure hstate
      have hwith := Devm.withholdCreateGas_gasMeasure d1
      split at hstep
      · obtain ⟨d2, hpush, hstep⟩ := Except.bind_eq_ok hstep
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
        rw [← hstep]
        intro devm' hd
        simp only [Except.ok.injEq] at hd
        rw [← hd, Devm.push_gasMeasure hpush,
          Devm.incrNonce_gasMeasure]
        omega
      · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
        rw [← hstep]
        refine ⟨?_, rfl⟩
        show Message.gas _ + Frame.parentGas _ < n
        simp only [createMessage, Frame.parentGas, Frame.State.gasMeasure_ofDevm,
          Devm.incrNonce_gasMeasure,
          Devm.drainStateGasReservoir_gasMeasure]
        omega
    · simp only [bind, Except.bind] at hstep
      have hwith := Devm.withholdCreateGas_gasMeasure
        (Devm.balReadAccount sevm.benvStat.rules newAddress
          (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
            (devm.withReturnData [])) newAddress))
      split at hstep
      · obtain ⟨d1, hpush, hstep⟩ := Except.bind_eq_ok hstep
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
        rw [← hstep]
        intro devm' hd
        simp only [Except.ok.injEq] at hd
        rw [← hd, Devm.push_gasMeasure hpush,
          Devm.incrNonce_gasMeasure]
        omega
      · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
        rw [← hstep]
        refine ⟨?_, rfl⟩
        show Message.gas _ + Frame.parentGas _ < n
        simp only [createMessage, Frame.parentGas, Frame.State.gasMeasure_ofDevm,
          Devm.incrNonce_gasMeasure,
          Devm.drainStateGasReservoir_gasMeasure]
        omega

theorem MessageOp.step_create_gasDecreasing (sevm : Sevm) (devm : Devm) :
    (MessageOp.step sevm devm .create).GasDecreasing sevm devm.gasMeasure := by
  have hv := Sevm.rules_valid sevm
  simp only [MessageOp.step]
  split
  · apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨endowment, d1⟩, h1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨memoryIndex, d2⟩, h2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨memorySize, d3⟩, h3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d4, h4, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCreate.step_gasDecreasing
    have e1 := Devm.pop_gasMeasure h1
    have e2 := Devm.popToNat_gasMeasure h2
    have e3 := Devm.popToNat_gasMeasure h3
    have e4 := chargeGas_gasMeasure h4
    dsimp only at e1 e2 e3 e4
    rw [Devm.memExtends_gasMeasure]
    have hpos := hv.gas.createAccess_pos
    omega
  · apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨_, hstatic, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨endowment, d1⟩, h1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨memoryIndex, d2⟩, h2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨memorySize, d3⟩, h3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d4, h4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hsize, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCreateAmsterdam.step_gasDecreasing
    have e1 := Devm.pop_gasMeasure h1
    have e2 := Devm.popToNat_gasMeasure h2
    have e3 := Devm.popToNat_gasMeasure h3
    have e4 := chargeGas_gasMeasure h4
    have hpos := hv.gas.createAccess_pos
    dsimp only at e1 e2 e3 e4
    rw [Devm.memExtends_gasMeasure]
    omega

theorem MessageOp.step_create2_gasDecreasing (sevm : Sevm) (devm : Devm) :
    (MessageOp.step sevm devm .create2).GasDecreasing sevm devm.gasMeasure := by
  have hv := Sevm.rules_valid sevm
  simp only [MessageOp.step]
  split
  · split
    · apply MessageOp.Outcome.ofExcept_gasDecreasing
      intro step hstep
      obtain ⟨⟨endowment, d1⟩, h1, hstep⟩ := Except.bind_eq_ok hstep
      obtain ⟨⟨memoryIndex, d2⟩, h2, hstep⟩ := Except.bind_eq_ok hstep
      obtain ⟨⟨memorySize, d3⟩, h3, hstep⟩ := Except.bind_eq_ok hstep
      obtain ⟨⟨salt, d4⟩, h4, hstep⟩ := Except.bind_eq_ok hstep
      obtain ⟨d5, h5, hstep⟩ := Except.bind_eq_ok hstep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      apply genericCreate.step_gasDecreasing
      have e1 := Devm.pop_gasMeasure h1
      have e2 := Devm.popToNat_gasMeasure h2
      have e3 := Devm.popToNat_gasMeasure h3
      have e4 := Devm.pop_gasMeasure h4
      have e5 := chargeGas_gasMeasure h5
      dsimp only at e1 e2 e3 e4 e5
      rw [Devm.memExtends_gasMeasure]
      have hpos := hv.gas.createAccess_pos
      omega
    · apply MessageOp.Outcome.ofExcept_gasDecreasing
      intro step hstep
      obtain ⟨_, hstatic, hstep⟩ := Except.bind_eq_ok hstep
      obtain ⟨⟨endowment, d1⟩, h1, hstep⟩ := Except.bind_eq_ok hstep
      obtain ⟨⟨memoryIndex, d2⟩, h2, hstep⟩ := Except.bind_eq_ok hstep
      obtain ⟨⟨memorySize, d3⟩, h3, hstep⟩ := Except.bind_eq_ok hstep
      obtain ⟨⟨salt, d4⟩, h4, hstep⟩ := Except.bind_eq_ok hstep
      obtain ⟨d5, h5, hstep⟩ := Except.bind_eq_ok hstep
      obtain ⟨_, hsize, hstep⟩ := Except.bind_eq_ok hstep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      apply genericCreateAmsterdam.step_gasDecreasing
      have e1 := Devm.pop_gasMeasure h1
      have e2 := Devm.popToNat_gasMeasure h2
      have e3 := Devm.popToNat_gasMeasure h3
      have e4 := Devm.pop_gasMeasure h4
      have e5 := chargeGas_gasMeasure h5
      have hpos := hv.gas.createAccess_pos
      dsimp only at e1 e2 e3 e4 e5
      rw [Devm.memExtends_gasMeasure]
      omega
  · -- Gate off: no `.ok` step exists to be decreasing for.
    apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    nomatch hstep

theorem MessageOp.step_callcode_gasDecreasing_legacy (sevm : Sevm) (devm : Devm)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    (MessageOp.step sevm devm .callcode).GasDecreasing sevm devm.gasMeasure := by
  have hv := Sevm.rules_valid sevm
  have hacc := hv.access
  -- The access step, of either shape: the arms reduce by `match` on the
  -- schedule, and both leave a positive price `pre` and a gas-neutral `dA`.
  rcases hA : sevm.benvStat.rules.access with g | _ <;> rw [hA] at hacc
  all_goals
    simp only [MessageOp.step, hstate, hA]
    apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨codeAddress, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨value, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputIndex, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputSize, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputIndex, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputSize, d7⟩, p7, hstep⟩ := Except.bind_eq_ok hstep
    dsimp only at hstep
    have e1 := Devm.pop_gasMeasure p1
    have e2 := Devm.popToAdr_gasMeasure p2
    have e3 := Devm.pop_gasMeasure p3
    have e4 := Devm.popToNat_gasMeasure p4
    have e5 := Devm.popToNat_gasMeasure p5
    have e6 := Devm.popToNat_gasMeasure p6
    have e7 := Devm.popToNat_gasMeasure p7
    dsimp only at e2 e3 e4 e5 e6 e7
  on_goal 1 =>
    have hpre : 0 < g.call := by
      simp only [AccessSchedule.Valid, FlatAccessGas.Valid] at hacc
      omega
    generalize g.call = pre at hpre hstep
    let dA := d7
    have hdA : dA.gasMeasure = d7.gasMeasure := rfl
  on_goal 2 =>
    have hpre := GasSchedule.access_cost_pos hv.gas codeAddress d7.accessedAddresses
    have hdA := addAccessedAddress_gasMeasure d7 codeAddress
    generalize sevm.benvStat.rules.gas.accessCost codeAddress d7.accessedAddresses = pre at hpre hstep
    generalize addAccessedAddress d7 codeAddress = dA at hdA hstep
  all_goals
    have eA :
        (sevm.benvStat.rules.accessDelegation
          dA codeAddress).2.2.2.2.gasMeasure
          = devm.gasMeasure := by
      rw [ForkRules.accessDelegation_gasMeasure, hdA]
      omega
    have hstip :
        (if value.toNat = 0 then 0 else Gas.callStipend) <
          ((pre +
              (sevm.benvStat.rules.accessDelegation dA
                codeAddress).2.2.2.1) +
            if value = 0 then 0 else sevm.benvStat.rules.gas.callValue) +
          d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
      have hcall := GasSchedule.Valid.stipend_le_callValue hv.gas
      by_cases hv : value = 0
      · have : value.toNat = 0 := by rw [hv]; rfl
        rw [ite_eq_left this]
        omega
      · rw [ite_eq_right hv]
        split <;> omega
    obtain ⟨d8, pcharge, hstep⟩ := Except.bind_eq_ok hstep
    have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
    split at hstep
    · obtain ⟨d9, ppush, hstep⟩ := Except.bind_eq_ok hstep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      intro devm' hd
      simp only [Except.ok.injEq] at hd
      rw [← hd]
      simp only [Devm.withGasLeft_gasMeasure, Devm.withReturnData_gasMeasure]
      rw [Nat.add_right_comm, ← Devm.gasMeasure_eq, Devm.push_gasMeasure ppush,
        Devm.memExtends_gasMeasure]
      exact key
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      apply genericCall.step_gasDecreasing
      rw [Devm.memExtends_gasMeasure]
      exact key

theorem MessageOp.step_callcode_gasDecreasing (sevm : Sevm) (devm : Devm) :
    (MessageOp.step sevm devm .callcode).GasDecreasing sevm devm.gasMeasure := by
  have hv := Sevm.rules_valid sevm
  simp only [MessageOp.step]
  split
  · simpa only [MessageOp.step, *] using
      MessageOp.step_callcode_gasDecreasing_legacy sevm devm (by assumption)
  · rename_i state hstate
    apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨codeAddress, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨value, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputIndex, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputSize, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputIndex, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputSize, d7⟩, p7, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hpre, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hfull, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d8, pcharge, hstep⟩ := Except.bind_eq_ok hstep
    have e1 := Devm.pop_gasMeasure p1
    have e2 := Devm.popToAdr_gasMeasure p2
    have e3 := Devm.pop_gasMeasure p3
    have e4 := Devm.popToNat_gasMeasure p4
    have e5 := Devm.popToNat_gasMeasure p5
    have e6 := Devm.popToNat_gasMeasure p6
    have e7 := Devm.popToNat_gasMeasure p7
    dsimp only at e1 e2 e3 e4 e5 e6 e7 hstep
    have eA :
        (completeDelegationAccess
          (Devm.balReadAccount sevm.benvStat.rules
            (sevm.benvStat.rules.delegationCost
              (addAccessedAddress d7 codeAddress) codeAddress).2.1
            (Devm.balReadAccount sevm.benvStat.rules codeAddress (addAccessedAddress d7 codeAddress)))
          (sevm.benvStat.rules.delegationCost
            (addAccessedAddress d7 codeAddress) codeAddress).1
          (sevm.benvStat.rules.delegationCost
            (addAccessedAddress d7 codeAddress) codeAddress).2.1).2.gasMeasure =
          devm.gasMeasure := by
      rw [completeDelegationAccess_gasMeasure]
      simp only [Devm.balReadAccount_gasMeasure, addAccessedAddress_gasMeasure]
      omega
    have hstip :
        (if value.toNat = 0 then 0 else Gas.callStipend) <
          ((sevm.benvStat.rules.gas.accessCost codeAddress d7.accessedAddresses +
              (if value = 0 then 0 else sevm.benvStat.rules.gas.callValue) +
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d7 codeAddress) codeAddress).2.2) +
            d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) := by
      have hac := GasSchedule.access_cost_pos hv.gas codeAddress d7.accessedAddresses
      have hcall := GasSchedule.Valid.stipend_le_callValue hv.gas
      by_cases hvalue : value = 0
      · have hto : value.toNat = 0 := by rw [hvalue]; rfl
        rw [ite_eq_left hto, ite_eq_left hvalue]
        omega
      · have hto : value.toNat ≠ 0 := by
          intro hz
          exact hvalue (U256.toNat_inj value 0 (by rw [hz, U256.toNat_zero]))
        rw [ite_eq_right hto, ite_eq_right hvalue]
        omega
    have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCallAmsterdam.step_gasDecreasing
    rw [Devm.memExtends_gasMeasure,
      Devm.drainStateGasReservoir_gasMeasure]
    exact key

theorem MessageOp.step_delegatecall_gasDecreasing_legacy (sevm : Sevm) (devm : Devm)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    (MessageOp.step sevm devm .delegatecall).GasDecreasing sevm devm.gasMeasure := by
  have hv := Sevm.rules_valid sevm
  have hacc := hv.access
  -- The access step, of either shape: the arms reduce by `match` on the
  -- schedule, and both leave a positive price `pre` and a gas-neutral `dA`.
  rcases hA : sevm.benvStat.rules.access with g | _ <;> rw [hA] at hacc
  all_goals
    simp only [MessageOp.step, hstate, hA]
    apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨codeAddress, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputIndex, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputSize, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputIndex, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputSize, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
    dsimp only at hstep
    have e1 := Devm.pop_gasMeasure p1
    have e2 := Devm.popToAdr_gasMeasure p2
    have e3 := Devm.popToNat_gasMeasure p3
    have e4 := Devm.popToNat_gasMeasure p4
    have e5 := Devm.popToNat_gasMeasure p5
    have e6 := Devm.popToNat_gasMeasure p6
    dsimp only at e2 e3 e4 e5 e6
  on_goal 1 =>
    have hpre : 0 < g.call := by
      simp only [AccessSchedule.Valid, FlatAccessGas.Valid] at hacc
      omega
    generalize g.call = pre at hpre hstep
    let dA := d6
    have hdA : dA.gasMeasure = d6.gasMeasure := rfl
  on_goal 2 =>
    have hpre := GasSchedule.access_cost_pos hv.gas codeAddress d6.accessedAddresses
    have hdA := addAccessedAddress_gasMeasure d6 codeAddress
    generalize sevm.benvStat.rules.gas.accessCost codeAddress d6.accessedAddresses = pre at hpre hstep
    generalize addAccessedAddress d6 codeAddress = dA at hdA hstep
  all_goals
    have eA :
        (sevm.benvStat.rules.accessDelegation
          dA codeAddress).2.2.2.2.gasMeasure
          = devm.gasMeasure := by
      rw [ForkRules.accessDelegation_gasMeasure, hdA]
      omega
    have hstip :
        (if (0 : Nat) = 0 then 0 else Gas.callStipend) <
          (pre +
            (sevm.benvStat.rules.accessDelegation dA
              codeAddress).2.2.2.1) +
          d6.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
      simp only [ite_eq_left]
      omega
    obtain ⟨d7, pcharge, hstep⟩ := Except.bind_eq_ok hstep
    have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCall.step_gasDecreasing
    rw [Devm.memExtends_gasMeasure]
    exact key

theorem MessageOp.step_delegatecall_gasDecreasing (sevm : Sevm) (devm : Devm) :
    (MessageOp.step sevm devm .delegatecall).GasDecreasing sevm devm.gasMeasure := by
  have hv := Sevm.rules_valid sevm
  simp only [MessageOp.step]
  split
  · simpa only [MessageOp.step, *] using
      MessageOp.step_delegatecall_gasDecreasing_legacy sevm devm (by assumption)
  · rename_i state hstate
    apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨codeAddress, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputIndex, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputSize, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputIndex, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputSize, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hpre, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hfull, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d7, pcharge, hstep⟩ := Except.bind_eq_ok hstep
    have e1 := Devm.pop_gasMeasure p1
    have e2 := Devm.popToAdr_gasMeasure p2
    have e3 := Devm.popToNat_gasMeasure p3
    have e4 := Devm.popToNat_gasMeasure p4
    have e5 := Devm.popToNat_gasMeasure p5
    have e6 := Devm.popToNat_gasMeasure p6
    dsimp only at e1 e2 e3 e4 e5 e6 hstep
    have eA :
        (completeDelegationAccess
          (Devm.balReadAccount sevm.benvStat.rules
            (sevm.benvStat.rules.delegationCost
              (addAccessedAddress d6 codeAddress) codeAddress).2.1
            (Devm.balReadAccount sevm.benvStat.rules codeAddress (addAccessedAddress d6 codeAddress)))
          (sevm.benvStat.rules.delegationCost
            (addAccessedAddress d6 codeAddress) codeAddress).1
          (sevm.benvStat.rules.delegationCost
            (addAccessedAddress d6 codeAddress) codeAddress).2.1).2.gasMeasure =
          devm.gasMeasure := by
      rw [completeDelegationAccess_gasMeasure]
      simp only [Devm.balReadAccount_gasMeasure, addAccessedAddress_gasMeasure]
      omega
    have hstip :
        (if (0 : Nat) = 0 then 0 else Gas.callStipend) <
          (sevm.benvStat.rules.gas.accessCost codeAddress d6.accessedAddresses +
              0 +
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d6 codeAddress) codeAddress).2.2) +
            d6.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
      simp only [ite_eq_left]
      have hac := GasSchedule.access_cost_pos hv.gas codeAddress d6.accessedAddresses
      omega
    have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCallAmsterdam.step_gasDecreasing
    rw [Devm.memExtends_gasMeasure,
      Devm.drainStateGasReservoir_gasMeasure]
    exact key

theorem MessageOp.step_staticcall_gasDecreasing_legacy (sevm : Sevm) (devm : Devm)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    (MessageOp.step sevm devm .staticcall).GasDecreasing sevm devm.gasMeasure := by
  have hv := Sevm.rules_valid sevm
  have hacc := hv.access
  -- The access step, of either shape: the arms reduce by `match` on the
  -- schedule, and both leave a positive price `pre` and a gas-neutral `dA`.
  rcases hA : sevm.benvStat.rules.access with g | _ <;> rw [hA] at hacc
  all_goals
    simp only [MessageOp.step, hstate, hA]
    apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨target, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputIndex, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputSize, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputIndex, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputSize, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
    dsimp only at hstep
    have e1 := Devm.pop_gasMeasure p1
    have e2 := Devm.popToAdr_gasMeasure p2
    have e3 := Devm.popToNat_gasMeasure p3
    have e4 := Devm.popToNat_gasMeasure p4
    have e5 := Devm.popToNat_gasMeasure p5
    have e6 := Devm.popToNat_gasMeasure p6
    dsimp only at e2 e3 e4 e5 e6
  on_goal 1 =>
    have hpre : 0 < g.call := by
      simp only [AccessSchedule.Valid, FlatAccessGas.Valid] at hacc
      omega
    generalize g.call = pre at hpre hstep
    let dA := d6
    have hdA : dA.gasMeasure = d6.gasMeasure := rfl
  on_goal 2 =>
    have hpre := GasSchedule.access_cost_pos hv.gas target d6.accessedAddresses
    have hdA := addAccessedAddress_gasMeasure d6 target
    generalize sevm.benvStat.rules.gas.accessCost target d6.accessedAddresses = pre at hpre hstep
    generalize addAccessedAddress d6 target = dA at hdA hstep
  all_goals
    have eA :
        (sevm.benvStat.rules.accessDelegation
          dA target).2.2.2.2.gasMeasure
          = devm.gasMeasure := by
      rw [ForkRules.accessDelegation_gasMeasure, hdA]
      omega
    have hstip :
        (if (0 : Nat) = 0 then 0 else Gas.callStipend) <
          (pre +
            (sevm.benvStat.rules.accessDelegation
              dA target).2.2.2.1) +
          d6.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
      simp only [ite_eq_left]
      omega
    obtain ⟨d7, pcharge, hstep⟩ := Except.bind_eq_ok hstep
    have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCall.step_gasDecreasing
    rw [Devm.memExtends_gasMeasure]
    exact key

theorem MessageOp.step_staticcall_gasDecreasing (sevm : Sevm) (devm : Devm) :
    (MessageOp.step sevm devm .staticcall).GasDecreasing sevm devm.gasMeasure := by
  have hv := Sevm.rules_valid sevm
  simp only [MessageOp.step]
  split
  · simpa only [MessageOp.step, *] using
      MessageOp.step_staticcall_gasDecreasing_legacy sevm devm (by assumption)
  · rename_i state hstate
    apply MessageOp.Outcome.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨codeAddress, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputIndex, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputSize, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputIndex, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputSize, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hpre, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hfull, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d7, pcharge, hstep⟩ := Except.bind_eq_ok hstep
    have e1 := Devm.pop_gasMeasure p1
    have e2 := Devm.popToAdr_gasMeasure p2
    have e3 := Devm.popToNat_gasMeasure p3
    have e4 := Devm.popToNat_gasMeasure p4
    have e5 := Devm.popToNat_gasMeasure p5
    have e6 := Devm.popToNat_gasMeasure p6
    dsimp only at e1 e2 e3 e4 e5 e6 hstep
    have eA :
        (completeDelegationAccess
          (Devm.balReadAccount sevm.benvStat.rules
            (sevm.benvStat.rules.delegationCost
              (addAccessedAddress d6 codeAddress) codeAddress).2.1
            (Devm.balReadAccount sevm.benvStat.rules codeAddress (addAccessedAddress d6 codeAddress)))
          (sevm.benvStat.rules.delegationCost
            (addAccessedAddress d6 codeAddress) codeAddress).1
          (sevm.benvStat.rules.delegationCost
            (addAccessedAddress d6 codeAddress) codeAddress).2.1).2.gasMeasure =
          devm.gasMeasure := by
      rw [completeDelegationAccess_gasMeasure]
      simp only [Devm.balReadAccount_gasMeasure, addAccessedAddress_gasMeasure]
      omega
    have hstip :
        (if (0 : Nat) = 0 then 0 else Gas.callStipend) <
          (sevm.benvStat.rules.gas.accessCost codeAddress d6.accessedAddresses +
              0 +
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d6 codeAddress) codeAddress).2.2) +
            d6.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
      simp only [ite_eq_left]
      have hac := GasSchedule.access_cost_pos hv.gas codeAddress d6.accessedAddresses
      omega
    have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCallAmsterdam.step_gasDecreasing
    rw [Devm.memExtends_gasMeasure,
      Devm.drainStateGasReservoir_gasMeasure]
    exact key

theorem MessageOp.step_gasDecreasing (sevm : Sevm) (devm : Devm) (x : MessageOp) :
    (MessageOp.step sevm devm x).GasDecreasing sevm devm.gasMeasure := by
  cases x
  case create => exact MessageOp.step_create_gasDecreasing sevm devm
  case create2 => exact MessageOp.step_create2_gasDecreasing sevm devm
  case call => exact MessageOp.step_call_gasDecreasing sevm devm
  case callcode => exact MessageOp.step_callcode_gasDecreasing sevm devm
  case delegatecall => exact MessageOp.step_delegatecall_gasDecreasing sevm devm
  case staticcall => exact MessageOp.step_staticcall_gasDecreasing sevm devm

/-- What the `Xinst` route owes on its halt branch, against the measure `n`
the step began with: no `"Revert"` tag, and a spill `n` still covers, because
the spill is what an exceptional halt keeps. A spawn carries no outcome of its
own, so it owes nothing. -/
def MessageOp.Outcome.Halt (n : Nat) : MessageOp.Outcome → Prop
  | .done ex => ∀ p, ex = .error p → p.1 ≠ .revert ∧ p.2.spill ≤ n
  | .spawn _ _ => True

theorem MessageOp.Outcome.done_ok_halt (d : Devm) (n : Nat) : (MessageOp.Outcome.done (.ok d)).Halt n := by
  intro p hp
  exact absurd hp (by simp)

/-- The obligation on an `MessageOp.Outcome`-valued body, before `MessageOp.Outcome.ofExcept` collapses
its error branch into a `.done`: an error is a non-`Revert` halt still carrying
the meter `s`, and a step owes `Halt n`. -/
def outcomeHalt (s : StateGasMeter) (n : Nat) : Except (EvmError × Devm) MessageOp.Outcome → Prop
  | .error p => p.1 ≠ .revert ∧ p.2.mach.stateGas = s
  | .ok step => step.Halt n

/-- Collapsing the error branch: a halt still holding the meter `s` spills at
most what `s` spills, which is the one arithmetic fact in this corpus. -/
theorem MessageOp.Outcome.ofExcept_halt {s : StateGasMeter} {n : Nat}
    {x : Except (EvmError × Devm) MessageOp.Outcome}
    (hsn : s.spilled + s.committedSpill ≤ n) (h : outcomeHalt s n x) :
    (MessageOp.Outcome.ofExcept x).Halt n := by
  cases x with
  | error p =>
    have h' : p.1 ≠ .revert ∧ p.2.mach.stateGas = s := h
    intro q hq
    cases hq
    refine ⟨h'.1, ?_⟩
    unfold Devm.spill
    rw [h'.2]
    exact hsn
  | ok step => exact h

theorem outcomeHalt_bind {α : Type} {proj : α → Devm} {s : StateGasMeter} {n : Nat}
    {e : Except (EvmError × Devm) α} {f : α → Except (EvmError × Devm) MessageOp.Outcome}
    (he : HaltOut proj s e)
    (hf : ∀ a, (proj a).mach.stateGas = s → outcomeHalt s n (f a)) :
    outcomeHalt s n (e >>= f) := by
  cases e with
  | error p => exact he
  | ok a => exact hf a he

theorem MessageOp.Outcome.ofExcept_haltLe {n : Nat}
    {e : Except (EvmError × Devm) MessageOp.Outcome}
    (h : HaltLe n (fun step => step.Halt n) e) :
    (MessageOp.Outcome.ofExcept e).Halt n := by
  cases e with
  | error p =>
    intro q hq
    cases hq
    exact h
  | ok step => exact h

theorem genericCall.step_halt
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) {s : StateGasMeter} {n : Nat}
    (hs : devm.mach.stateGas = s) (hsn : s.spilled + s.committedSpill ≤ n) :
    (genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles).Halt n := by
  unfold genericCall.step
  split
  · exact MessageOp.Outcome.ofExcept_halt hsn
      (outcomeHalt_bind (Devm.push_haltOut (by simpa using hs))
        (fun _ _ => MessageOp.Outcome.done_ok_halt _ _))
  · trivial

theorem genericCallAmsterdam.step_halt
    (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    (gas reservoir : Nat) (value : U256)
    (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray)
    (disablePrecompiles newAccountCharged insufficientBalance : Bool) {n : Nat}
    (hn : devm.spill ≤ n) :
    (genericCallAmsterdam.step sevm state devm gas reservoir value caller target
      codeAddress shouldTransferValue isStaticcall inputIndex inputSize
      outputIndex outputSize code disablePrecompiles newAccountCharged
      insufficientBalance).Halt n := by
  unfold genericCallAmsterdam.step
  split
  · apply MessageOp.Outcome.ofExcept_haltLe
    refine HaltLe.bind (Devm.push_haltLe_spill 0 ?_) ?_
    · split
      · exact Nat.le_trans (Devm.creditStateGasRefund_spill_le _ _) (by simpa using hn)
      · simpa using hn
    · intro d hd
      exact MessageOp.Outcome.done_ok_halt d n
  · trivial

theorem genericCreate.step_halt
    (sevm : Sevm) (devm : Devm) (endowment : U256) (newAddress : Address)
    (memoryIndex memorySize : Nat) {s : StateGasMeter} {n : Nat}
    (hs : devm.mach.stateGas = s) (hsn : s.spilled + s.committedSpill ≤ n) :
    (genericCreate.step sevm devm endowment newAddress memoryIndex
      memorySize).Halt n := by
  unfold genericCreate.step
  apply MessageOp.Outcome.ofExcept_halt hsn
  refine outcomeHalt_bind (assert_haltOut (by decide) hs) ?_
  intro _ _
  refine outcomeHalt_bind (assertDynamic_haltOut _ (by simpa using hs)) ?_
  intro _ _
  dsimp only
  split
  · exact outcomeHalt_bind (Devm.push_haltOut (by simpa using hs))
      (fun _ _ => MessageOp.Outcome.done_ok_halt _ _)
  · split
    · exact outcomeHalt_bind (Devm.push_haltOut (by simpa using hs))
        (fun _ _ => MessageOp.Outcome.done_ok_halt _ _)
    · trivial

theorem genericCreateAmsterdam.step_halt
    (sevm : Sevm) (state : StateGasRules) (devm : Devm) (endowment : U256)
    (newAddress : Address) (memoryIndex memorySize : Nat) {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    (genericCreateAmsterdam.step sevm state devm endowment newAddress
      memoryIndex memorySize).Halt n := by
  unfold genericCreateAmsterdam.step
  apply MessageOp.Outcome.ofExcept_haltLe
  dsimp only
  split
  · refine HaltLe.bind (Devm.push_haltLe 0 ?_) ?_
    · simpa only [Devm.balReadAccount_gasMeasure, Devm.withReturnData_gasMeasure] using hn
    · intro d hd
      exact MessageOp.Outcome.done_ok_halt d n
  · have haccess :
        (Devm.balReadAccount sevm.benvStat.rules newAddress
          (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
            (devm.withReturnData [])) newAddress)).gasMeasure ≤ n := by
      simpa only [Devm.balReadAccount_gasMeasure, addAccessedAddress_gasMeasure,
        Devm.withReturnData_gasMeasure] using hn
    split
    · refine HaltLe.bind (chargeStateGas_haltLe state.newAccount haccess) ?_
      intro d1 hd
      have hwith := Devm.withholdCreateGas_gasMeasure d1
      split
      · refine HaltLe.bind (Devm.push_haltLe 0 ?_) ?_
        · simp only [Devm.incrNonce_gasMeasure]
          omega
        · intro d2 hd2
          exact MessageOp.Outcome.done_ok_halt d2 n
      · trivial
    · simp only [bind, Except.bind]
      have hwith := Devm.withholdCreateGas_gasMeasure
        (Devm.balReadAccount sevm.benvStat.rules newAddress
          (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
            (devm.withReturnData [])) newAddress))
      split
      · refine HaltLe.bind (Devm.push_haltLe 0 ?_) ?_
        · simp only [Devm.incrNonce_gasMeasure]
          omega
        · intro d2 hd2
          exact MessageOp.Outcome.done_ok_halt d2 n
      · trivial

theorem MessageOp.step_halt_legacy (sevm : Sevm) (devm : Devm) (x : MessageOp)
    {s : StateGasMeter} {n : Nat}
    (hs : devm.mach.stateGas = s) (hsn : s.spilled + s.committedSpill ≤ n)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    (MessageOp.step sevm devm x).Halt n := by
  cases x <;> simp only [MessageOp.step, hstate]
  case create2 =>
    split
    · apply MessageOp.Outcome.ofExcept_halt hsn
      refine outcomeHalt_bind (Devm.pop_haltOut hs) ?_
      rintro ⟨endowment, d1⟩ h1
      refine outcomeHalt_bind (Devm.popToNat_haltOut h1) ?_
      rintro ⟨memoryIndex, d2⟩ h2
      refine outcomeHalt_bind (Devm.popToNat_haltOut h2) ?_
      rintro ⟨memorySize, d3⟩ h3
      refine outcomeHalt_bind (Devm.pop_haltOut h3) ?_
      rintro ⟨salt, d4⟩ h4
      refine outcomeHalt_bind (chargeGas_haltOut h4) ?_
      intro d5 h5
      exact genericCreate.step_halt _ _ _ _ _ _ (by simpa using h5) hsn
    · -- Gate off: the invalid-opcode error is non-`Revert` and keeps the meter.
      apply MessageOp.Outcome.ofExcept_halt hsn
      refine ⟨?_, ?_⟩
      · simp
      · exact hs
  all_goals apply MessageOp.Outcome.ofExcept_halt hsn
  case create =>
    refine outcomeHalt_bind (Devm.pop_haltOut hs) ?_
    rintro ⟨endowment, d1⟩ h1
    refine outcomeHalt_bind (Devm.popToNat_haltOut h1) ?_
    rintro ⟨memoryIndex, d2⟩ h2
    refine outcomeHalt_bind (Devm.popToNat_haltOut h2) ?_
    rintro ⟨memorySize, d3⟩ h3
    refine outcomeHalt_bind (chargeGas_haltOut h3) ?_
    intro d4 h4
    exact genericCreate.step_halt _ _ _ _ _ _ (by simpa using h4) hsn
  case call =>
    refine outcomeHalt_bind (Devm.pop_haltOut hs) ?_
    rintro ⟨gas, d1⟩ h1
    refine outcomeHalt_bind (Devm.popToAdr_haltOut h1) ?_
    rintro ⟨callee, d2⟩ h2
    refine outcomeHalt_bind (Devm.pop_haltOut h2) ?_
    rintro ⟨value, d3⟩ h3
    refine outcomeHalt_bind (Devm.popToNat_haltOut h3) ?_
    rintro ⟨inputIndex, d4⟩ h4
    refine outcomeHalt_bind (Devm.popToNat_haltOut h4) ?_
    rintro ⟨inputSize, d5⟩ h5
    refine outcomeHalt_bind (Devm.popToNat_haltOut h5) ?_
    rintro ⟨outputIndex, d6⟩ h6
    refine outcomeHalt_bind (Devm.popToNat_haltOut h6) ?_
    rintro ⟨outputSize, d7⟩ h7
    refine outcomeHalt_bind (chargeGas_haltOut (by
      simp only [ForkRules.accessDelegation_stateGas]
      split <;> simpa only [addAccessedAddress_stateGas] using h7)) ?_
    intro d8 h8
    refine outcomeHalt_bind (assert_haltOut (by decide) h8) ?_
    intro _ _
    split
    · exact outcomeHalt_bind (Devm.push_haltOut (by simpa using h8))
        (fun _ _ => MessageOp.Outcome.done_ok_halt _ _)
    · exact genericCall.step_halt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using h8) hsn
  case callcode =>
    refine outcomeHalt_bind (Devm.pop_haltOut hs) ?_
    rintro ⟨gas, d1⟩ h1
    refine outcomeHalt_bind (Devm.popToAdr_haltOut h1) ?_
    rintro ⟨codeAddress, d2⟩ h2
    refine outcomeHalt_bind (Devm.pop_haltOut h2) ?_
    rintro ⟨value, d3⟩ h3
    refine outcomeHalt_bind (Devm.popToNat_haltOut h3) ?_
    rintro ⟨inputIndex, d4⟩ h4
    refine outcomeHalt_bind (Devm.popToNat_haltOut h4) ?_
    rintro ⟨inputSize, d5⟩ h5
    refine outcomeHalt_bind (Devm.popToNat_haltOut h5) ?_
    rintro ⟨outputIndex, d6⟩ h6
    refine outcomeHalt_bind (Devm.popToNat_haltOut h6) ?_
    rintro ⟨outputSize, d7⟩ h7
    refine outcomeHalt_bind (chargeGas_haltOut (by
      simp only [ForkRules.accessDelegation_stateGas]
      split <;> simpa only [addAccessedAddress_stateGas] using h7)) ?_
    intro d8 h8
    split
    · exact outcomeHalt_bind (Devm.push_haltOut (by simpa using h8))
        (fun _ _ => MessageOp.Outcome.done_ok_halt _ _)
    · exact genericCall.step_halt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using h8) hsn
  case delegatecall =>
    refine outcomeHalt_bind (Devm.pop_haltOut hs) ?_
    rintro ⟨gas, d1⟩ h1
    refine outcomeHalt_bind (Devm.popToAdr_haltOut h1) ?_
    rintro ⟨codeAddress, d2⟩ h2
    refine outcomeHalt_bind (Devm.popToNat_haltOut h2) ?_
    rintro ⟨inputIndex, d3⟩ h3
    refine outcomeHalt_bind (Devm.popToNat_haltOut h3) ?_
    rintro ⟨inputSize, d4⟩ h4
    refine outcomeHalt_bind (Devm.popToNat_haltOut h4) ?_
    rintro ⟨outputIndex, d5⟩ h5
    refine outcomeHalt_bind (Devm.popToNat_haltOut h5) ?_
    rintro ⟨outputSize, d6⟩ h6
    refine outcomeHalt_bind (chargeGas_haltOut (by
      simp only [ForkRules.accessDelegation_stateGas]
      split <;> simpa only [addAccessedAddress_stateGas] using h6)) ?_
    intro d7 h7
    exact genericCall.step_halt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using h7) hsn
  case staticcall =>
    refine outcomeHalt_bind (Devm.pop_haltOut hs) ?_
    rintro ⟨gas, d1⟩ h1
    refine outcomeHalt_bind (Devm.popToAdr_haltOut h1) ?_
    rintro ⟨target, d2⟩ h2
    refine outcomeHalt_bind (Devm.popToNat_haltOut h2) ?_
    rintro ⟨inputIndex, d3⟩ h3
    refine outcomeHalt_bind (Devm.popToNat_haltOut h3) ?_
    rintro ⟨inputSize, d4⟩ h4
    refine outcomeHalt_bind (Devm.popToNat_haltOut h4) ?_
    rintro ⟨outputIndex, d5⟩ h5
    refine outcomeHalt_bind (Devm.popToNat_haltOut h5) ?_
    rintro ⟨outputSize, d6⟩ h6
    refine outcomeHalt_bind (chargeGas_haltOut (by
      simp only [ForkRules.accessDelegation_stateGas]
      split <;> simpa only [addAccessedAddress_stateGas] using h6)) ?_
    intro d7 h7
    exact genericCall.step_halt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using h7) hsn

theorem MessageOp.step_halt (sevm : Sevm) (devm : Devm) (x : MessageOp)
    {s : StateGasMeter} {n : Nat}
    (hs : devm.mach.stateGas = s) (hsn : s.spilled + s.committedSpill ≤ n)
    (hn : devm.gasMeasure ≤ n) :
    (MessageOp.step sevm devm x).Halt n := by
  cases hstate : sevm.benvStat.rules.stateGas with
  | none =>
    exact MessageOp.step_halt_legacy sevm devm x hs hsn hstate
  | some state =>
    cases x <;> simp only [MessageOp.step, hstate]
    case create2 =>
      split
      · apply MessageOp.Outcome.ofExcept_haltLe
        refine HaltLe.bind (assertDynamic_haltLe sevm hn) ?_
        intro _ h0
        refine HaltLe.bind (Devm.pop_haltLe h0) ?_
        rintro ⟨endowment, d1⟩ h1
        refine HaltLe.bind (Devm.popToNat_haltLe h1) ?_
        rintro ⟨memoryIndex, d2⟩ h2
        refine HaltLe.bind (Devm.popToNat_haltLe h2) ?_
        rintro ⟨memorySize, d3⟩ h3
        refine HaltLe.bind (Devm.pop_haltLe h3) ?_
        rintro ⟨salt, d4⟩ h4
        refine HaltLe.bind (chargeGas_haltLe _ h4) ?_
        intro d5 h5
        refine HaltLe.bind (assert_haltLe _ (by decide) h5) ?_
        intro _ _
        apply genericCreateAmsterdam.step_halt
        simpa only [Devm.memExtends_gasMeasure] using h5
      · -- Gate off: the invalid-opcode error is non-`Revert` and
        -- spill-bounded.
        apply MessageOp.Outcome.ofExcept_haltLe
        refine ⟨?_, ?_⟩
        · simp
        · exact Nat.le_trans (Devm.spill_le_gasMeasure _) hn
    all_goals apply MessageOp.Outcome.ofExcept_haltLe
    case create =>
      refine HaltLe.bind (assertDynamic_haltLe sevm hn) ?_
      intro _ h0
      refine HaltLe.bind (Devm.pop_haltLe h0) ?_
      rintro ⟨endowment, d1⟩ h1
      refine HaltLe.bind (Devm.popToNat_haltLe h1) ?_
      rintro ⟨memoryIndex, d2⟩ h2
      refine HaltLe.bind (Devm.popToNat_haltLe h2) ?_
      rintro ⟨memorySize, d3⟩ h3
      refine HaltLe.bind (chargeGas_haltLe _ h3) ?_
      intro d4 h4
      refine HaltLe.bind (assert_haltLe _ (by decide) h4) ?_
      intro _ _
      apply genericCreateAmsterdam.step_halt
      simpa only [Devm.memExtends_gasMeasure] using h4
    case call =>
      refine HaltLe.bind (Devm.pop_haltLe hn) ?_
      rintro ⟨gas, d1⟩ h1
      refine HaltLe.bind (Devm.popToAdr_haltLe h1) ?_
      rintro ⟨callee, d2⟩ h2
      refine HaltLe.bind (Devm.pop_haltLe h2) ?_
      rintro ⟨value, d3⟩ h3
      refine HaltLe.bind (Devm.popToNat_haltLe h3) ?_
      rintro ⟨inputIndex, d4⟩ h4
      refine HaltLe.bind (Devm.popToNat_haltLe h4) ?_
      rintro ⟨inputSize, d5⟩ h5
      refine HaltLe.bind (Devm.popToNat_haltLe h5) ?_
      rintro ⟨outputIndex, d6⟩ h6
      refine HaltLe.bind (Devm.popToNat_haltLe h6) ?_
      rintro ⟨outputSize, d7⟩ h7
      refine HaltLe.bind (assert_haltLe _ (by decide) h7) ?_
      intro _ hstatic
      refine HaltLe.bind (assert_haltLe _ (by decide) hstatic) ?_
      intro _ hpre
      refine HaltLe.bind (assert_haltLe _ (by decide) ?_) ?_
      · simpa only [Devm.balReadAccount_gasMeasure, addAccessedAddress_gasMeasure] using hpre
      · intro _ hfull
        have haccess :
            (completeDelegationAccess
              (Devm.balReadAccount sevm.benvStat.rules
                (sevm.benvStat.rules.delegationCost
                  (addAccessedAddress d7 callee) callee).2.1
                (Devm.balReadAccount sevm.benvStat.rules callee (addAccessedAddress d7 callee)))
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d7 callee) callee).1
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d7 callee) callee).2.1).2.gasMeasure ≤ n := by
          simpa only [completeDelegationAccess_gasMeasure, Devm.balReadAccount_gasMeasure]
            using hfull
        refine HaltLe.bind (chargeGas_haltLe _ haccess) ?_
        intro d8 h8
        split
        · refine HaltLe.bind (chargeStateGas_haltLe _ h8) ?_
          intro d9 h9
          refine HaltLe.bind (chargeGas_haltLe _ h9) ?_
          intro d10 h10
          apply genericCallAmsterdam.step_halt
          exact Nat.le_trans (Devm.spill_le_gasMeasure _)
            (by simpa only [Devm.drainStateGasReservoir_gasMeasure,
              Devm.memExtends_gasMeasure] using h10)
        · simp only [bind, Except.bind]
          refine HaltLe.bind (chargeGas_haltLe _ h8) ?_
          intro d9 h9
          apply genericCallAmsterdam.step_halt
          exact Nat.le_trans (Devm.spill_le_gasMeasure _)
            (by simpa only [Devm.drainStateGasReservoir_gasMeasure,
              Devm.memExtends_gasMeasure] using h9)
    case callcode =>
      refine HaltLe.bind (Devm.pop_haltLe hn) ?_
      rintro ⟨gas, d1⟩ h1
      refine HaltLe.bind (Devm.popToAdr_haltLe h1) ?_
      rintro ⟨codeAddress, d2⟩ h2
      refine HaltLe.bind (Devm.pop_haltLe h2) ?_
      rintro ⟨value, d3⟩ h3
      refine HaltLe.bind (Devm.popToNat_haltLe h3) ?_
      rintro ⟨inputIndex, d4⟩ h4
      refine HaltLe.bind (Devm.popToNat_haltLe h4) ?_
      rintro ⟨inputSize, d5⟩ h5
      refine HaltLe.bind (Devm.popToNat_haltLe h5) ?_
      rintro ⟨outputIndex, d6⟩ h6
      refine HaltLe.bind (Devm.popToNat_haltLe h6) ?_
      rintro ⟨outputSize, d7⟩ h7
      refine HaltLe.bind (assert_haltLe _ (by decide) h7) ?_
      intro _ hpre
      refine HaltLe.bind (assert_haltLe _ (by decide) ?_) ?_
      · simpa only [Devm.balReadAccount_gasMeasure, addAccessedAddress_gasMeasure] using hpre
      · intro _ hfull
        have haccess :
            (completeDelegationAccess
              (Devm.balReadAccount sevm.benvStat.rules
                (sevm.benvStat.rules.delegationCost
                  (addAccessedAddress d7 codeAddress) codeAddress).2.1
                (Devm.balReadAccount sevm.benvStat.rules codeAddress (addAccessedAddress d7 codeAddress)))
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d7 codeAddress) codeAddress).1
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d7 codeAddress) codeAddress).2.1).2.gasMeasure ≤ n := by
          simpa only [completeDelegationAccess_gasMeasure, Devm.balReadAccount_gasMeasure]
            using hfull
        refine HaltLe.bind (chargeGas_haltLe _ haccess) ?_
        intro d8 h8
        apply genericCallAmsterdam.step_halt
        exact Nat.le_trans (Devm.spill_le_gasMeasure _)
          (by simpa only [Devm.drainStateGasReservoir_gasMeasure,
            Devm.memExtends_gasMeasure] using h8)
    case delegatecall =>
      refine HaltLe.bind (Devm.pop_haltLe hn) ?_
      rintro ⟨gas, d1⟩ h1
      refine HaltLe.bind (Devm.popToAdr_haltLe h1) ?_
      rintro ⟨codeAddress, d2⟩ h2
      refine HaltLe.bind (Devm.popToNat_haltLe h2) ?_
      rintro ⟨inputIndex, d3⟩ h3
      refine HaltLe.bind (Devm.popToNat_haltLe h3) ?_
      rintro ⟨inputSize, d4⟩ h4
      refine HaltLe.bind (Devm.popToNat_haltLe h4) ?_
      rintro ⟨outputIndex, d5⟩ h5
      refine HaltLe.bind (Devm.popToNat_haltLe h5) ?_
      rintro ⟨outputSize, d6⟩ h6
      refine HaltLe.bind (assert_haltLe _ (by decide) h6) ?_
      intro _ hpre
      refine HaltLe.bind (assert_haltLe _ (by decide) ?_) ?_
      · simpa only [Devm.balReadAccount_gasMeasure, addAccessedAddress_gasMeasure] using hpre
      · intro _ hfull
        have haccess :
            (completeDelegationAccess
              (Devm.balReadAccount sevm.benvStat.rules
                (sevm.benvStat.rules.delegationCost
                  (addAccessedAddress d6 codeAddress) codeAddress).2.1
                (Devm.balReadAccount sevm.benvStat.rules codeAddress (addAccessedAddress d6 codeAddress)))
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d6 codeAddress) codeAddress).1
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d6 codeAddress) codeAddress).2.1).2.gasMeasure ≤ n := by
          simpa only [completeDelegationAccess_gasMeasure, Devm.balReadAccount_gasMeasure]
            using hfull
        refine HaltLe.bind (chargeGas_haltLe _ haccess) ?_
        intro d7 h7
        apply genericCallAmsterdam.step_halt
        exact Nat.le_trans (Devm.spill_le_gasMeasure _)
          (by simpa only [Devm.drainStateGasReservoir_gasMeasure,
            Devm.memExtends_gasMeasure] using h7)
    case staticcall =>
      refine HaltLe.bind (Devm.pop_haltLe hn) ?_
      rintro ⟨gas, d1⟩ h1
      refine HaltLe.bind (Devm.popToAdr_haltLe h1) ?_
      rintro ⟨codeAddress, d2⟩ h2
      refine HaltLe.bind (Devm.popToNat_haltLe h2) ?_
      rintro ⟨inputIndex, d3⟩ h3
      refine HaltLe.bind (Devm.popToNat_haltLe h3) ?_
      rintro ⟨inputSize, d4⟩ h4
      refine HaltLe.bind (Devm.popToNat_haltLe h4) ?_
      rintro ⟨outputIndex, d5⟩ h5
      refine HaltLe.bind (Devm.popToNat_haltLe h5) ?_
      rintro ⟨outputSize, d6⟩ h6
      refine HaltLe.bind (assert_haltLe _ (by decide) h6) ?_
      intro _ hpre
      refine HaltLe.bind (assert_haltLe _ (by decide) ?_) ?_
      · simpa only [Devm.balReadAccount_gasMeasure, addAccessedAddress_gasMeasure] using hpre
      · intro _ hfull
        have haccess :
            (completeDelegationAccess
              (Devm.balReadAccount sevm.benvStat.rules
                (sevm.benvStat.rules.delegationCost
                  (addAccessedAddress d6 codeAddress) codeAddress).2.1
                (Devm.balReadAccount sevm.benvStat.rules codeAddress (addAccessedAddress d6 codeAddress)))
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d6 codeAddress) codeAddress).1
              (sevm.benvStat.rules.delegationCost
                (addAccessedAddress d6 codeAddress) codeAddress).2.1).2.gasMeasure ≤ n := by
          simpa only [completeDelegationAccess_gasMeasure, Devm.balReadAccount_gasMeasure]
            using hfull
        refine HaltLe.bind (chargeGas_haltLe _ haccess) ?_
        intro d7 h7
        apply genericCallAmsterdam.step_halt
        exact Nat.le_trans (Devm.spill_le_gasMeasure _)
          (by simpa only [Devm.drainStateGasReservoir_gasMeasure,
            Devm.memExtends_gasMeasure] using h7)


/-- What one step of the driver owes, measured against the frame's gas at the
start of the step. -/
def Step.GasBound (sevm : Sevm) (n : Nat) : Step → Prop
  | .halt ex => ex.SettledGasLe n
  | .next _ devm => devm.gasMeasure < n
  | .spawn child _ _ =>
      child.message.gas + child.parentGas < n ∧
        child.message.context.block.rules = sevm.benvStat.rules

theorem Step.ofExecution_gasBound {sevm : Sevm} {pc n : Nat} {ex : Execution}
    (hok : ∀ d, ex = .ok d → d.gasMeasure < n) (hset : ex.SettledGasLe n) :
    (Step.ofExecution pc ex).GasBound sevm n := by
  cases ex with
  | error e => exact hset
  | ok d => exact hok d rfl

theorem Step.ofJump_gasBound {sevm : Sevm} {n : Nat}
    {x : Except (EvmError × Devm) (Nat × Devm)}
    (hok : ∀ p, x = .ok p → p.2.gasMeasure < n) (hle : resultGas Prod.snd x ≤ n) :
    (Step.ofJump x).GasBound sevm n := by
  cases x with
  | error e => exact Execution.settledGasLe_of_gasLe hle
  | ok p => exact hok p rfl


theorem MessageOp.Outcome.toStep_gasBound {sevm : Sevm} {pc n : Nat} {step : MessageOp.Outcome}
    (hdec : step.GasDecreasing sevm n) (hh : step.Halt n) :
    (MessageOp.Outcome.toStep pc step).GasBound sevm n := by
  cases step with
  | done ex =>
    refine Step.ofExecution_gasBound hdec ?_
    exact Execution.settledGasLe_of_halt
      (fun d hd => Nat.le_of_lt (hdec d hd)) hh
  | spawn child pending => exact hdec

theorem NextOp.step_gasBound (evm : Evm) (n : NextOp) :
    (NextOp.step evm n).GasBound evm.sta evm.dyna.gasMeasure := by
  cases n with
  | push xs b =>
    simp only [NextOp.step]
    split
    · -- Gate off: the error is non-`Revert` and spill-bounded.
      refine Step.ofExecution_gasBound (fun d hd => by nomatch hd) ?_
      refine Execution.settledGasLe_of_halt (fun d hd => by nomatch hd) ?_
      intro p hp
      simp only [Except.error.injEq] at hp
      subst hp
      refine ⟨?_, ?_⟩
      · simp
      · exact Devm.spill_le_gasMeasure _
    · refine Step.ofExecution_gasBound (fun d hd => NextOp.step_push_gasLt hd) ?_
      refine Execution.settledGasLe_of_gasLe ?_
      exact gasLe_bind_id (chargeGas_result_gasLe _ _)
        (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
  | plain r =>
    refine Step.ofExecution_gasBound
      (fun d hd => PlainOp.runCore_gasLt evm.pc evm.dyna evm.sta r hd) ?_
    exact Execution.settledGasLe_of_gasLe
      (PlainOp.runCore_gasLe evm.pc evm.dyna evm.sta r)
  | message x =>
    exact MessageOp.Outcome.toStep_gasBound (MessageOp.step_gasDecreasing evm.sta evm.dyna x)
      (MessageOp.step_halt evm.sta evm.dyna x rfl
        (Devm.spill_le_gasMeasure _) (Nat.le_refl _))
  -- EIP-8024: `VERY_LOW` is charged before anything else can succeed, so a
  -- successful step strictly lowers the measure; every outcome keeps it
  -- bounded by the entry measure.
  | dupn imm =>
    refine Step.ofExecution_gasBound (fun d hd => ?_) ?_
    · split at hd
      · obtain ⟨d1, h1, hd⟩ := Except.bind_eq_ok hd
        have e1 := chargeGas_gasMeasure h1
        split at hd
        · nomatch hd
        · split at hd
          · nomatch hd
          · have e2 := Devm.push_gasMeasure hd
            unfold Gas.veryLow at e1
            omega
      · nomatch hd
    · refine Execution.settledGasLe_of_gasLe ?_
      split
      · refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
        intro d1
        split
        · simp
        · split
          · simp
          · exact Nat.le_of_eq (Devm.push_gasLe _ _)
      · simp
  | swapn imm =>
    refine Step.ofExecution_gasBound (fun d hd => ?_) ?_
    · split at hd
      · obtain ⟨d1, h1, hd⟩ := Except.bind_eq_ok hd
        have e1 := chargeGas_gasMeasure h1
        split at hd
        · nomatch hd
        · split at hd
          · nomatch hd
          · simp only [Except.ok.injEq] at hd
            rw [← hd, Devm.withStack_gasMeasure]
            unfold Gas.veryLow at e1
            omega
      · nomatch hd
    · refine Execution.settledGasLe_of_gasLe ?_
      split
      · refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
        intro d1
        split
        · simp
        · split <;> simp
      · simp
  | exchange imm =>
    refine Step.ofExecution_gasBound (fun d hd => ?_) ?_
    · split at hd
      · obtain ⟨d1, h1, hd⟩ := Except.bind_eq_ok hd
        have e1 := chargeGas_gasMeasure h1
        split at hd
        · nomatch hd
        · split at hd
          · nomatch hd
          · simp only [Except.ok.injEq] at hd
            rw [← hd, Devm.withStack_gasMeasure]
            unfold Gas.veryLow at e1
            omega
      · nomatch hd
    · refine Execution.settledGasLe_of_gasLe ?_
      split
      · refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
        intro d1
        split
        · simp
        · split <;> simp
      · simp

theorem Evm.step_gasBound (evm : Evm) :
    (Staging.Evm.step evm).GasBound evm.sta evm.dyna.gasMeasure := by
  unfold Evm.step
  split
  · exact Execution.settledGasLe_of_gasLe (Nat.le_of_eq rfl)
  · exact NextOp.step_gasBound evm _
  · rename_i j _
    exact Step.ofJump_gasBound
      (fun p hp => JumpOp.runCore_gasLt evm.pc evm.dyna evm.sta j hp)
      (JumpOp.runCore_gasLe evm.pc evm.dyna evm.sta j)
  · rename_i l _
    exact Execution.settledGasLe_of_gasLe (HaltOp.run_gasLe evm.sta evm.dyna l)

end Staging

end Jaune
