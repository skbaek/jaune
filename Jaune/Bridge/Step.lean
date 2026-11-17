import Jaune.Bridge.Settle
import Jaune.ExecFrame
import Jaune.MessageCall.Step

/-!
# `step`, today's and the staged one (W1 unit E, bridge)

Today's `Evm.step` hands the driver a child as two messages and a `Resume`; the staged one hands
it a `Frame` (a `Message` and the saved caller as its checkpoint) and a `Pending`. `Step.ofLegacy`
reads the first as the second, and `step_legacy` says the two steps agree on every machine.
`step_spawn_coherent` states what a spawn of today establishes about the child it hands over: the
premise `Legacy.Frame.Coherent` that the bridges of `enter` and `resume` take, the static records,
and that its `Resume` is the one the rules select (`Resume.Matches`).

About today's definitions, and deleted with them after the gate's tag (the W1 design note, third
revision, section 3.2, unit E).
-/

namespace Jaune

/-- A `Resume` is the one the rules select: an Amsterdam constructor exactly when the rules have
state gas, carrying those rules' state-gas record. -/
def Resume.Matches : Resume → ForkRules → Prop
  | .create .., rules => rules.stateGas = none
  | .call .., rules => rules.stateGas = none
  | .createAmsterdam state .., rules => rules.stateGas = some state
  | .callAmsterdam state .., rules => rules.stateGas = some state

end Jaune

namespace Jaune.Staging

/-! ### Reading today's results as staged ones -/

/-- Today's message-opcode result as a staged one. -/
def MessageOp.Outcome.ofLegacy : XStep → MessageOp.Outcome
  | .done ex => .done ex
  | .spawn f rsm => .spawn (Frame.ofLegacy f rsm) (Pending.ofLegacy rsm)

/-- Today's step as a staged one. -/
def Step.ofLegacy : Jaune.Step → Step
  | .halt ex => .halt ex
  | .cont pc devm => .next pc devm
  | .spawn f rsm pc => .spawn (Frame.ofLegacy f rsm) (Pending.ofLegacy rsm) pc

@[simp] theorem MessageOp.Outcome.ofLegacy_done (ex : Execution) :
    MessageOp.Outcome.ofLegacy (.done ex) = .done ex := rfl

theorem MessageOp.Outcome.ofLegacy_ofExcept (x : Except (EvmError × Devm) XStep) :
    MessageOp.Outcome.ofLegacy (XStep.ofExcept x)
      = MessageOp.Outcome.ofExcept (MessageOp.Outcome.ofLegacy <$> x) := by
  cases x <;> rfl

theorem Step.ofLegacy_ofExecution (pc : Nat) (ex : Execution) :
    Step.ofLegacy (Jaune.Step.ofExecution pc ex) = Step.ofExecution pc ex := by
  cases ex <;> rfl

theorem Step.ofLegacy_ofJump (x : Except (EvmError × Devm) (Nat × Devm)) :
    Step.ofLegacy (Jaune.Step.ofJump x) = Step.ofJump x := by
  rcases x with _ | ⟨_, _⟩ <;> rfl

theorem Step.ofLegacy_toStep (pc : Nat) (s : XStep) :
    Step.ofLegacy (XStep.toStep pc s)
      = MessageOp.Outcome.toStep pc (MessageOp.Outcome.ofLegacy s) := by
  cases s with
  | done ex => exact Step.ofLegacy_ofExecution pc ex
  | spawn f rsm => rfl

theorem map_ite' {ε α β : Type} {f : α → β} (c : Prop) [Decidable c] (a b : Except ε α) :
    f <$> (if c then a else b) = if c then f <$> a else f <$> b := by
  split <;> rfl

/-! ### The four tails -/

theorem genericCreate.step_legacy (sevm : Sevm) (devm : Devm) (endowment : U256)
    (newAddress : Address) (memoryIndex memorySize : Nat) :
    MessageOp.Outcome.ofLegacy
        (Jaune.genericCreate.step sevm devm endowment newAddress memoryIndex memorySize)
      = genericCreate.step sevm devm endowment newAddress memoryIndex memorySize := by
  unfold Jaune.genericCreate.step genericCreate.step
  rw [MessageOp.Outcome.ofLegacy_ofExcept]
  congr 1
  simp only [map_bind, map_pure, map_ite', MessageOp.Outcome.ofLegacy_done]
  rfl

theorem genericCall.step_legacy (sevm : Sevm) (devm : Devm) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat) (code : ByteArray)
    (disablePrecompiles : Bool) :
    MessageOp.Outcome.ofLegacy
        (Jaune.genericCall.step sevm devm gas value caller target codeAddress
          shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize code
          disablePrecompiles)
      = genericCall.step sevm devm gas value caller target codeAddress
          shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize code
          disablePrecompiles := by
  unfold Jaune.genericCall.step genericCall.step
  split
  · rw [MessageOp.Outcome.ofLegacy_ofExcept]
    congr 1
    simp only [map_bind, map_pure, MessageOp.Outcome.ofLegacy_done]
  · rfl

theorem genericCallAmsterdam.step_legacy (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    (gas reservoir : Nat) (value : U256) (caller target codeAddress : Address)
    (shouldTransferValue isStaticcall : Bool) (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles newAccountCharged insufficientBalance : Bool) :
    MessageOp.Outcome.ofLegacy
        (Jaune.genericCallAmsterdam.step sevm state devm gas reservoir value caller target
          codeAddress shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
          code disablePrecompiles newAccountCharged insufficientBalance)
      = genericCallAmsterdam.step sevm state devm gas reservoir value caller target
          codeAddress shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
          code disablePrecompiles newAccountCharged insufficientBalance := by
  unfold Jaune.genericCallAmsterdam.step genericCallAmsterdam.step
  split
  · rw [MessageOp.Outcome.ofLegacy_ofExcept]
    congr 1
    simp only [map_bind, map_pure, MessageOp.Outcome.ofLegacy_done]
  · rfl

theorem genericCreateAmsterdam.step_legacy (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    (endowment : U256) (newAddress : Address) (memoryIndex memorySize : Nat) :
    MessageOp.Outcome.ofLegacy
        (Jaune.genericCreateAmsterdam.step sevm state devm endowment newAddress memoryIndex
          memorySize)
      = genericCreateAmsterdam.step sevm state devm endowment newAddress memoryIndex
          memorySize := by
  unfold Jaune.genericCreateAmsterdam.step genericCreateAmsterdam.step
  rw [MessageOp.Outcome.ofLegacy_ofExcept]
  congr 1
  simp only [map_bind, map_pure, map_ite', MessageOp.Outcome.ofLegacy_done]
  rfl

/-! ### The message opcodes, one lemma per opcode -/

set_option hygiene false in
/-- The walk shared by the message opcodes: split on the rules' state gas, then push the reading
through the do-block to the tails. -/
macro "message_step_legacy" : tactic => `(tactic| (
  cases hsg : sevm.benvStat.rules.stateGas <;>
    simp only [Jaune.MessageOp.step, MessageOp.step, hsg] <;>
    rw [MessageOp.Outcome.ofLegacy_ofExcept] <;>
    congr 1 <;>
    simp only [map_bind, map_pure, map_ite', MessageOp.Outcome.ofLegacy_done,
      genericCreate.step_legacy, genericCall.step_legacy, genericCallAmsterdam.step_legacy,
      genericCreateAmsterdam.step_legacy] <;>
    try rfl))

theorem MessageOp.step_legacy_create (sevm : Sevm) (devm : Devm) :
    MessageOp.Outcome.ofLegacy (Jaune.MessageOp.step sevm devm .create)
      = MessageOp.step sevm devm .create := by
  message_step_legacy

theorem MessageOp.step_legacy_create2 (sevm : Sevm) (devm : Devm) :
    MessageOp.Outcome.ofLegacy (Jaune.MessageOp.step sevm devm .create2)
      = MessageOp.step sevm devm .create2 := by
  by_cases h2 : sevm.benvStat.rules.opcodes.create2
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Jaune.MessageOp.step, MessageOp.step, hsg, h2, ite_true] <;>
      rw [MessageOp.Outcome.ofLegacy_ofExcept] <;>
      congr 1 <;>
      simp only [map_bind, map_pure, genericCreate.step_legacy,
        genericCreateAmsterdam.step_legacy]
  · simp only [Jaune.MessageOp.step, MessageOp.step, h2, Bool.false_eq_true, ite_false]
    rfl

theorem MessageOp.step_legacy_call (sevm : Sevm) (devm : Devm) :
    MessageOp.Outcome.ofLegacy (Jaune.MessageOp.step sevm devm .call)
      = MessageOp.step sevm devm .call := by
  message_step_legacy

theorem MessageOp.step_legacy_callcode (sevm : Sevm) (devm : Devm) :
    MessageOp.Outcome.ofLegacy (Jaune.MessageOp.step sevm devm .callcode)
      = MessageOp.step sevm devm .callcode := by
  message_step_legacy

theorem MessageOp.step_legacy_delegatecall (sevm : Sevm) (devm : Devm) :
    MessageOp.Outcome.ofLegacy (Jaune.MessageOp.step sevm devm .delegatecall)
      = MessageOp.step sevm devm .delegatecall := by
  message_step_legacy

theorem MessageOp.step_legacy_staticcall (sevm : Sevm) (devm : Devm) :
    MessageOp.Outcome.ofLegacy (Jaune.MessageOp.step sevm devm .staticcall)
      = MessageOp.step sevm devm .staticcall := by
  message_step_legacy

theorem MessageOp.step_legacy (sevm : Sevm) (devm : Devm) (op : MessageOp) :
    MessageOp.Outcome.ofLegacy (Jaune.MessageOp.step sevm devm op)
      = MessageOp.step sevm devm op := by
  cases op
  · exact MessageOp.step_legacy_create sevm devm
  · exact MessageOp.step_legacy_call sevm devm
  · exact MessageOp.step_legacy_callcode sevm devm
  · exact MessageOp.step_legacy_delegatecall sevm devm
  · exact MessageOp.step_legacy_create2 sevm devm
  · exact MessageOp.step_legacy_staticcall sevm devm

/-! ### The step -/

theorem NextOp.step_legacy (evm : Evm) (n : NextOp) :
    Step.ofLegacy (Jaune.NextOp.step evm n) = NextOp.step evm n := by
  cases n <;> simp only [Jaune.NextOp.step, NextOp.step] <;>
    first
      | (simp only [Step.ofLegacy_ofExecution, Step.ofLegacy_toStep, MessageOp.step_legacy]; done)
      | (rw [Step.ofLegacy_ofExecution]; rfl)
      | (split <;> simp only [Step.ofLegacy_ofExecution])

/-- **Step.** Today's step, read as a staged one, is the staged step, on every machine. -/
theorem step_legacy (evm : Evm) : Step.ofLegacy (Jaune.Evm.step evm) = Evm.step evm := by
  unfold Jaune.Evm.step Evm.step
  rcases h : evm.getInst with _ | (l | n | j) <;> simp only []
  · rfl
  · rfl
  · exact NextOp.step_legacy evm n
  · exact Step.ofLegacy_ofJump _

/-! ### What a spawn of today establishes -/

/-- What a spawn hands over, about the spawning machine's static record: the child is coherent
with the saved caller, carries the caller's static records, and its `Resume` matches the rules. -/
def SpawnCoherent (sevm : Sevm) (f : Jaune.Frame) (rsm : Resume) : Prop :=
  Legacy.Frame.Coherent f rsm.parent ∧ f.outer.benv.stat = sevm.benvStat ∧
    f.outer.tenv.stat = sevm.tenvStat ∧ rsm.Matches sevm.benvStat.rules

set_option hygiene false in
/-- The walk that inverts a tail's spawn, on the hypothesis `hs`. -/
macro "spawn_walk" : tactic => `(tactic| (
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, rfl⟩ := hs))

theorem genericCreate.step_spawn_coherent {sevm : Sevm} {devm : Devm} {endowment : U256}
    {newAddress : Address} {memoryIndex memorySize : Nat} {f : Jaune.Frame} {rsm : Resume}
    (hs : Jaune.genericCreate.step sevm devm endowment newAddress memoryIndex memorySize
      = .spawn f rsm) (hsg : sevm.benvStat.rules.stateGas = none) :
    SpawnCoherent sevm f rsm := by
  unfold Jaune.genericCreate.step at hs
  spawn_walk
  all_goals exact ⟨⟨⟨by simp [Jaune.Frame.ofCreate], rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, hsg⟩

theorem genericCall.step_spawn_coherent {sevm : Sevm} {devm : Devm} {gas : Nat} {value : U256}
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {f : Jaune.Frame} {rsm : Resume}
    (hs : Jaune.genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize code
      disablePrecompiles = .spawn f rsm) (hsg : sevm.benvStat.rules.stateGas = none) :
    SpawnCoherent sevm f rsm := by
  unfold Jaune.genericCall.step at hs
  spawn_walk
  all_goals exact ⟨⟨⟨by simp [Jaune.Frame.ofCall], rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, hsg⟩

theorem genericCallAmsterdam.step_spawn_coherent {sevm : Sevm} {state : StateGasRules}
    {devm : Devm} {gas reservoir : Nat} {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool} {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles newAccountCharged insufficientBalance : Bool}
    {f : Jaune.Frame} {rsm : Resume}
    (hs : Jaune.genericCallAmsterdam.step sevm state devm gas reservoir value caller target
      codeAddress shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles newAccountCharged insufficientBalance = .spawn f rsm)
    (hsg : sevm.benvStat.rules.stateGas = some state) :
    SpawnCoherent sevm f rsm := by
  unfold Jaune.genericCallAmsterdam.step at hs
  spawn_walk
  all_goals exact ⟨⟨⟨by simp [Jaune.Frame.ofCall], rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, hsg⟩

theorem genericCreateAmsterdam.step_spawn_coherent {sevm : Sevm} {state : StateGasRules}
    {devm : Devm} {endowment : U256} {newAddress : Address} {memoryIndex memorySize : Nat}
    {f : Jaune.Frame} {rsm : Resume}
    (hs : Jaune.genericCreateAmsterdam.step sevm state devm endowment newAddress memoryIndex
      memorySize = .spawn f rsm) (hsg : sevm.benvStat.rules.stateGas = some state) :
    SpawnCoherent sevm f rsm := by
  unfold Jaune.genericCreateAmsterdam.step at hs
  spawn_walk
  all_goals exact ⟨⟨⟨by simp [Jaune.Frame.ofCreate], rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, hsg⟩

theorem MessageOp.step_spawn_coherent {sevm : Sevm} {devm : Devm} {x : MessageOp}
    {f : Jaune.Frame} {rsm : Resume} (hs : Jaune.MessageOp.step sevm devm x = .spawn f rsm) :
    SpawnCoherent sevm f rsm := by
  cases x <;>
    simp only [Jaune.MessageOp.step, Bind.bind, Except.bind, Except.assert,
      Pure.pure, Except.pure] at hs <;>
    repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals
    first
      | exact genericCreate.step_spawn_coherent hs (by assumption)
      | exact genericCall.step_spawn_coherent hs (by assumption)
      | exact genericCreateAmsterdam.step_spawn_coherent hs (by assumption)
      | exact genericCallAmsterdam.step_spawn_coherent hs (by assumption)

/-- **Spawn coherence.** A spawn of today hands over a child coherent with its saved caller, with
the spawning machine's static records, and a `Resume` that matches the rules. -/
theorem step_spawn_coherent {evm : Evm} {f : Jaune.Frame} {rsm : Resume} {pc : Nat}
    (h : Jaune.Evm.step evm = .spawn f rsm pc) :
    Legacy.Frame.Coherent f rsm.parent ∧ f.outer.benv.stat = evm.sta.benvStat ∧
      f.outer.tenv.stat = evm.sta.tenvStat ∧ rsm.Matches evm.sta.benvStat.rules := by
  rcases evm with ⟨pc0, sevm, devm⟩
  obtain ⟨x, -, hx, -⟩ := Evm.step_spawn_inv h
  exact MessageOp.step_spawn_coherent hx

end Jaune.Staging

