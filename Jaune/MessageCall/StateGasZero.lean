import Jaune.MessageCall.Totality

/-!
# The zero-meter invariant on the four-part chain (goal `jaune-shape-and-names-v1`, W1 unit L)

Under rules without state gas (`rules.stateGas = none`) every frame runs with the disabled
state-gas meter `StateGasMeter.zero`. The machine layer (`Jaune.Machine`) proves that every
instruction preserves `Devm.StateGasZero`; this module adds the frame structure of the
four-part message call: `step`'s spawns, `enter`, `settle`, `resume` and the driver.

Two points of its shape:

* a frame has one message, so `Frame.StateGasZero` has one rules clause; the saved caller is
  the frame's checkpoint, so its zero meter is a clause of the frame;
* `resume` under rules without state gas leaves the caller's meter as saved, so its lemma needs
  nothing about the child's result, and the driver needs neither the `enter` nor the `settle`
  lemma: they are kept as facts in their own right.
-/

namespace Jaune

open Jaune

/-! ### The predicates -/

/-- A frame runs under rules without state gas, with no state-gas grant, and falls back to a
caller whose meter is zero. -/
def Frame.StateGasZero (f : Frame) : Prop :=
  f.message.context.block.rules.stateGas = none ∧ f.message.stateGasGrant = 0 ∧
    f.checkpoint.machine.stateGas = .zero

/-- A message opcode's outcome keeps the zero meter: its result on both channels, or the frame it
spawns. -/
def MessageOp.Outcome.StateGasZero : MessageOp.Outcome → Prop
  | .done ex => ex.StateGasZero
  | .spawn child _ => child.StateGasZero

/-- A step keeps the zero meter. -/
def Step.StateGasZero : Step → Prop
  | .halt ex => ex.StateGasZero
  | .next _ devm => devm.StateGasZero
  | .spawn child _ _ => child.StateGasZero

/-- A frame's result hands back the zero meter. -/
def Frame.Result.StateGasZero (r : Frame.Result) : Prop := r.stateGas = .zero

/-- An entry keeps the zero meter: the machine it runs, or the result it settled at once (a
fault carries no meter). -/
def Frame.Entry.StateGasZero : Frame.Entry → Prop
  | .done result => ∀ r, result = .ok r → r.StateGasZero
  | .run evm => evm.StateGasZero

/-! ### Results of a step -/

theorem MessageOp.Outcome.ofExcept_stateGasZero
    {x : Except (EvmError × Devm) MessageOp.Outcome}
    (h : x.StateGasZeroOn MessageOp.Outcome.StateGasZero) :
    (MessageOp.Outcome.ofExcept x).StateGasZero := by
  cases x with
  | error e => exact h
  | ok step => exact h

theorem Step.ofExecution_stateGasZero (pc : Nat) {x : Execution}
    (h : x.StateGasZero) : (Step.ofExecution pc x).StateGasZero := by
  cases x with
  | error e => exact h
  | ok devm => exact h

theorem Step.ofJump_stateGasZero {x : Except (EvmError × Devm) (Nat × Devm)}
    (h : x.StateGasZeroOn (fun a => a.2.StateGasZero)) :
    (Step.ofJump x).StateGasZero := by
  cases x with
  | error e => exact h
  | ok a => exact h

theorem MessageOp.Outcome.toStep_stateGasZero (pc : Nat) {x : MessageOp.Outcome}
    (h : x.StateGasZero) : (x.toStep pc).StateGasZero := by
  cases x with
  | done ex => exact Step.ofExecution_stateGasZero pc h
  | spawn child pending => exact h

/-! ### The four tails and the step -/

theorem genericCall.step_stateGasZero {sevm : Sevm} {devm : Devm}
    (hrules : sevm.benvStat.rules.stateGas = none)
    (h : devm.StateGasZero)
    (gas : Nat) (value : U256) (caller target codeAddress : Address)
    (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) :
    (genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles).StateGasZero := by
  unfold genericCall.step
  dsimp only
  split
  · refine MessageOp.Outcome.ofExcept_stateGasZero ?_
    refine Except.StateGasZeroOn.bind
      (Devm.push_stateGasZero _ (Devm.stateGasZero_withGasLeft h)) ?_
    intro d hd
    exact Except.stateGasZeroOn_ok hd
  · exact ⟨hrules, rfl, h⟩

theorem genericCreate.step_stateGasZero {sevm : Sevm} {devm : Devm}
    (hrules : sevm.benvStat.rules.stateGas = none)
    (h : devm.StateGasZero) (endowment : U256) (newAddress : Address)
    (memoryIndex memorySize : Nat) :
    (genericCreate.step sevm devm endowment newAddress memoryIndex memorySize).StateGasZero := by
  unfold genericCreate.step
  refine MessageOp.Outcome.ofExcept_stateGasZero ?_
  refine Except.StateGasZeroOn.bind (Except.stateGasZeroOn_assert h) ?_
  intro _ _
  refine Except.StateGasZeroOn.bind
    (Except.stateGasZeroOn_assert (Devm.stateGasZero_withGasLeft h)) ?_
  intro _ _
  dsimp only
  split
  · refine Except.StateGasZeroOn.bind
      (Devm.push_stateGasZero _ (Devm.stateGasZero_withGasLeft h)) ?_
    intro d hd
    exact Except.stateGasZeroOn_ok hd
  · split
    · refine Except.StateGasZeroOn.bind
        (Devm.push_stateGasZero _ (Devm.stateGasZero_withGasLeft h)) ?_
      intro d hd
      exact Except.stateGasZeroOn_ok hd
    · exact Except.stateGasZeroOn_ok
        (show Frame.StateGasZero _ from ⟨hrules, rfl,
          Devm.stateGasZero_withGasLeft (n := devm.gasLeft - except64th devm.gasLeft) h⟩)

theorem MessageOp.step_stateGasZero {sevm : Sevm} {devm : Devm}
    (hrules : sevm.benvStat.rules.stateGas = none)
    (h : devm.StateGasZero) (x : MessageOp) :
    (MessageOp.step sevm devm x).StateGasZero := by
  cases x <;> simp only [MessageOp.step, hrules]
  case create =>
    refine MessageOp.Outcome.ofExcept_stateGasZero ?_
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero ha) fun b hb => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hb) fun c hc => ?_
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hc) fun d hd => ?_
    exact Except.stateGasZeroOn_ok
      (genericCreate.step_stateGasZero hrules (by exact hd) _ _ _ _)
  case create2 =>
    split
    · refine MessageOp.Outcome.ofExcept_stateGasZero ?_
      refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
      refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero ha) fun b hb => ?_
      refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hb) fun c hc => ?_
      refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero hc) fun e he => ?_
      refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ he) fun d hd => ?_
      exact Except.stateGasZeroOn_ok
        (genericCreate.step_stateGasZero hrules (by exact hd) _ _ _ _)
    · -- Gate off: the undefined-opcode error keeps the machine.
      refine MessageOp.Outcome.ofExcept_stateGasZero ?_
      exact h
  case call =>
    refine MessageOp.Outcome.ofExcept_stateGasZero ?_
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToAdr_stateGasZero ha) fun b hb => ?_
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero hb) fun c hc => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hc) fun d hd => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hd) fun e he => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero he) fun f hf => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hf) fun g hg => ?_
    have haccess := ForkRules.accessDelegation_stateGasZero
      (rules := sevm.benvStat.rules) (devm := match sevm.benvStat.rules.access with
              | .eip2929 => addAccessedAddress g.2 b.1
              | .flat _ => g.2)
      (by split <;> exact hg) b.1
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ haccess) fun d2 hd2 => ?_
    refine Except.StateGasZeroOn.bind (Except.stateGasZeroOn_assert hd2) fun _ _ => ?_
    split
    · refine Except.StateGasZeroOn.bind (Devm.push_stateGasZero _ hd2) fun d3 hd3 => ?_
      exact Except.stateGasZeroOn_ok hd3
    · exact Except.stateGasZeroOn_ok
        (genericCall.step_stateGasZero hrules (by exact hd2)
          _ _ _ _ _ _ _ _ _ _ _ _ _)
  case callcode =>
    refine MessageOp.Outcome.ofExcept_stateGasZero ?_
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToAdr_stateGasZero ha) fun b hb => ?_
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero hb) fun c hc => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hc) fun d hd => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hd) fun e he => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero he) fun f hf => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hf) fun g hg => ?_
    have haccess := ForkRules.accessDelegation_stateGasZero
      (rules := sevm.benvStat.rules) (devm := match sevm.benvStat.rules.access with
              | .eip2929 => addAccessedAddress g.2 b.1
              | .flat _ => g.2)
      (by split <;> exact hg) b.1
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ haccess) fun d2 hd2 => ?_
    split
    · refine Except.StateGasZeroOn.bind (Devm.push_stateGasZero _ hd2) fun d3 hd3 => ?_
      exact Except.stateGasZeroOn_ok hd3
    · exact Except.stateGasZeroOn_ok
        (genericCall.step_stateGasZero hrules (by exact hd2)
          _ _ _ _ _ _ _ _ _ _ _ _ _)
  case delegatecall =>
    refine MessageOp.Outcome.ofExcept_stateGasZero ?_
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToAdr_stateGasZero ha) fun b hb => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hb) fun c hc => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hc) fun d hd => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hd) fun e he => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero he) fun f hf => ?_
    have haccess := ForkRules.accessDelegation_stateGasZero
      (rules := sevm.benvStat.rules) (devm := match sevm.benvStat.rules.access with
              | .eip2929 => addAccessedAddress f.2 b.1
              | .flat _ => f.2)
      (by split <;> exact hf) b.1
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ haccess) fun d2 hd2 => ?_
    exact Except.stateGasZeroOn_ok
      (genericCall.step_stateGasZero hrules (by exact hd2)
        _ _ _ _ _ _ _ _ _ _ _ _ _)
  case staticcall =>
    refine MessageOp.Outcome.ofExcept_stateGasZero ?_
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToAdr_stateGasZero ha) fun b hb => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hb) fun c hc => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hc) fun d hd => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hd) fun e he => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero he) fun f hf => ?_
    have haccess := ForkRules.accessDelegation_stateGasZero
      (rules := sevm.benvStat.rules) (devm := match sevm.benvStat.rules.access with
              | .eip2929 => addAccessedAddress f.2 b.1
              | .flat _ => f.2)
      (by split <;> exact hf) b.1
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ haccess) fun d2 hd2 => ?_
    exact Except.stateGasZeroOn_ok
      (genericCall.step_stateGasZero hrules (by exact hd2)
        _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem NextOp.step_stateGasZero {evm : Evm} (h : evm.StateGasZero)
    (n : NextOp) : (NextOp.step evm n).StateGasZero := by
  cases n with
  | push xs prf =>
      simp only [NextOp.step]
      split
      · -- Gate off: the undefined-opcode error keeps the machine.
        refine Step.ofExecution_stateGasZero _ ?_
        exact Except.stateGasZeroOn_error h.2
      · refine Step.ofExecution_stateGasZero _ ?_
        refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h.2) ?_
        intro d hd
        exact Devm.push_stateGasZero _ hd
  | plain r =>
      exact Step.ofExecution_stateGasZero _
        (PlainOp.run_stateGasZero h.2 h.1 r)
  | message x =>
      exact MessageOp.Outcome.toStep_stateGasZero _
        (MessageOp.step_stateGasZero h.1 h.2 x)
  | dupn imm =>
      refine Step.ofExecution_stateGasZero _ ?_
      split
      · refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h.2) fun d hd => ?_
        split
        · exact Except.stateGasZeroOn_error hd
        · split
          · exact Except.stateGasZeroOn_error hd
          · exact Devm.push_stateGasZero _ hd
      · exact Except.stateGasZeroOn_error h.2
  | swapn imm =>
      refine Step.ofExecution_stateGasZero _ ?_
      split
      · refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h.2) fun d hd => ?_
        split
        · exact Except.stateGasZeroOn_error hd
        · split
          · exact Except.stateGasZeroOn_error hd
          · exact Except.stateGasZeroOn_ok hd
      · exact Except.stateGasZeroOn_error h.2
  | exchange imm =>
      refine Step.ofExecution_stateGasZero _ ?_
      split
      · refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h.2) fun d hd => ?_
        split
        · exact Except.stateGasZeroOn_error hd
        · split
          · exact Except.stateGasZeroOn_error hd
          · exact Except.stateGasZeroOn_ok hd
      · exact Except.stateGasZeroOn_error h.2

theorem Evm.step_stateGasZero {evm : Evm} (h : evm.StateGasZero) :
    (Evm.step evm).StateGasZero := by
  unfold Evm.step
  split
  · exact h.2
  · exact NextOp.step_stateGasZero h _
  · exact Step.ofJump_stateGasZero (JumpOp.run_stateGasZero h.2 _)
  · exact HaltOp.run_stateGasZero h.2 h.1 _

/-! ### `settle`, `enter`, `resume` -/

/-- The code-deposit charge keeps the zero meter under rules without state gas, on both
channels: the counterpart of `processCreateMessage.chargeCodeGas_stateGasZero`. -/
theorem chargeDeposit_stateGasZero {rules : ForkRules} {code : Bytes} {d : Devm}
    (hrules : rules.stateGas = none) (h : d.StateGasZero) :
    (chargeDeposit rules code d).StateGasZeroOn Devm.StateGasZero := by
  have hcharge : ∀ (c : Nat) (d : Devm), d.StateGasZero →
      (Devm.chargeGas c d).StateGasZeroOn Devm.StateGasZero := by
    intro c d hd
    unfold Devm.chargeGas
    split
    · exact hd
    · exact Devm.stateGasZero_withGasLeft hd
  have hthen : (do
      let d ← Devm.chargeGas (code.length * Gas.codeDeposit) d
      if rules.code.maxCodeSize < code.length then
        (.error (.outOfGas .none, d) : Except (ExceptionalHalt × Devm) Devm)
      else .ok d).StateGasZeroOn Devm.StateGasZero := by
    refine Except.StateGasZeroOn.bind (hcharge _ d h) fun d' hd' => ?_
    split
    · exact hd'
    · exact hd'
  unfold chargeDeposit
  rw [hrules]
  dsimp only
  split
  · split
    · exact h
    · exact hthen
  · exact hthen

/-- A settled result keeps the zero meter. -/
theorem settle_stateGasZero {f : Frame}
    (hrules : f.message.context.block.rules.stateGas = none)
    {raw : Execution} (h : raw.StateGasZero) {r : Frame.Result}
    (hs : settle f raw = .ok r) : r.StateGasZero := by
  unfold settle at hs
  simp only [hrules] at hs
  rcases raw with ⟨⟨reason⟩ | ⟨⟩ | ⟨reason⟩ | ⟨reason⟩, d⟩ | d
  · cases hs
    exact Devm.stateGasZero_withGasLeft h
  · cases hs
    exact h
  · cases hs
  · cases hs
  · dsimp only at hs
    have ht : (d.recordTouch f.message.context.block.rules true
        f.message.context.recipient).StateGasZero := by
      unfold Devm.recordTouch
      split <;> exact h
    split at hs
    · cases hs
      exact ht
    · split at hs
      · next s hd =>
          cases hs
          have hc := chargeDeposit_stateGasZero (code := (d.recordTouch f.message.context.block.rules true f.message.context.recipient).output)
            hrules ht
          unfold depositCode at hd
          rcases hcd : chargeDeposit f.message.context.block.rules
              (d.recordTouch f.message.context.block.rules true
                f.message.context.recipient).output
              (d.recordTouch f.message.context.block.rules true
                f.message.context.recipient) with e | s'
          · rw [hcd] at hd
            cases hd
          · rw [hcd] at hd hc
            simp only [Except.map, Except.ok.injEq] at hd
            rw [← hd]
            exact hc
      · next reason s hd =>
          cases hs
          have hc := chargeDeposit_stateGasZero (code := (d.recordTouch f.message.context.block.rules true f.message.context.recipient).output)
            hrules ht
          unfold depositCode at hd
          rcases hcd : chargeDeposit f.message.context.block.rules
              (d.recordTouch f.message.context.block.rules true
                f.message.context.recipient).output
              (d.recordTouch f.message.context.block.rules true
                f.message.context.recipient) with e | s'
          · rw [hcd] at hd hc
            simp only [Except.map, Except.error.injEq] at hd
            subst hd
            exact Devm.stateGasZero_withGasLeft hc
          · rw [hcd] at hd
            cases hd

/-- Entering a frame keeps the zero meter. Only the rules and the grant are needed: a child
starts from the message's grant, not from its checkpoint's meter. -/
theorem enter_stateGasZero {f : Frame}
    (hrules : f.message.context.block.rules.stateGas = none)
    (hgrant : f.message.stateGasGrant = 0) :
    (enter f).StateGasZero := by
  have hstart : f.start.StateGasZero := by
    simp only [Devm.StateGasZero, Frame.start, Frame.startState, Frame.State.toDevm, hgrant]
    rfl
  unfold enter enterWith
  dsimp only
  split
  · intro r hr
    cases hr
  · next world _ =>
      have hd : ((f.start.setWorld world).withCreatedAccounts
          f.enteredCreatedAccounts).StateGasZero := hstart
      have hevm : Evm.StateGasZero
          ⟨0, f.message.sevm, (f.start.setWorld world).withCreatedAccounts
            f.enteredCreatedAccounts⟩ := ⟨hrules, hd⟩
      split
      · split
        · intro r hr
          exact settle_stateGasZero hrules (executePrecompile_stateGasZero hd _) hr
        · exact hevm
      · exact hevm

/-- Resuming a caller keeps its zero meter. Under rules without state gas `resume` hands the
caller's meter back as saved, so nothing about the child's result is needed. -/
theorem resume_stateGasZero {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Devm) Devm}
    (hrules : rules.stateGas = none) (hsaved : saved.machine.stateGas = .zero)
    (h : resume rules p saved r = .ok x) : x.StateGasZeroOn Devm.StateGasZero := by
  unfold resume at h
  simp only [hrules, Option.isSome_none, Bool.false_eq_true, ite_false] at h
  split at h <;> cases h <;>
    simp only [Except.StateGasZeroOn, Devm.StateGasZero, Pending.restore,
      Frame.State.toDevm, absorbMeters, hrules] <;>
    cases p.target <;> simpa [ReturnTarget.finish] using hsaved

/-! ### The driver -/

/-- A run started with the disabled state-gas meter returns with that meter still zero, on
both channels. -/
theorem execFueled_run_stateGasZero :
    ∀ (fuel : Nat) (evm : Evm), evm.StateGasZero →
      ∀ {raw : Execution}, (execFueled evm fuel).run = some raw →
        raw.StateGasZero := by
  intro fuel
  induction fuel with
  | zero =>
      intro evm _ raw hrun
      rw [execFueled] at hrun
      simp only [Fueled.exhausted_run] at hrun
      nomatch hrun
  | succ fuel ih =>
      intro evm hevm raw hrun
      have hstep := Evm.step_stateGasZero hevm
      rw [execFueled] at hrun
      rcases hs : Evm.step evm with ex | ⟨pc, devm⟩ | ⟨child, pending, pc⟩ <;>
        rw [hs] at hrun hstep <;> dsimp only at hrun
      · simp only [Fueled.ofExcept_run, Option.some.injEq] at hrun
        rw [← hrun]
        exact hstep
      · exact ih ⟨pc, evm.sta, devm⟩ ⟨hevm.1, hstep⟩ hrun
      · have hcheck : child.checkpoint.toDevm.StateGasZero := hstep.2.2
        split at hrun
        · simp only [Fueled.exhausted_run] at hrun
          nomatch hrun
        · simp only [Fueled.ofExcept_run, Option.some.injEq] at hrun
          rw [← hrun]
          exact hcheck
        · split at hrun
          · simp only [Fueled.ofExcept_run, Option.some.injEq] at hrun
            rw [← hrun]
            exact hcheck
          · next reason devm hres =>
              simp only [Fueled.ofExcept_run, Option.some.injEq] at hrun
              rw [← hrun]
              exact resume_stateGasZero hevm.1 hstep.2.2 hres
          · next devm hres =>
              exact ih ⟨pc, evm.sta, devm⟩
                ⟨hevm.1, resume_stateGasZero hevm.1 hstep.2.2 hres⟩ hrun

theorem execFueled_run_gasMeasure_eq_gasLeft {fuel : Nat} {evm : Evm}
    (h : evm.StateGasZero) {devm : Devm}
    (hrun : (execFueled evm fuel).run = some (.ok devm)) :
    devm.gasMeasure = devm.gasLeft :=
  Devm.stateGasZero_gasMeasure (execFueled_run_stateGasZero fuel evm h hrun)

/-- The total interpreter keeps the zero meter, on both channels. -/
theorem exec_stateGasZero {evm : Evm} (h : evm.StateGasZero) :
    Execution.StateGasZero (exec evm) :=
  execFueled_run_stateGasZero _ evm h (execFueled_run_sufficientFuel evm)

end Jaune
