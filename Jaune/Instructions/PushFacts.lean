import Jaune.Instructions.Push
import Jaune.Instructions.WordFacts
import Jaune.MessageCall.CheckedStep

/-! The push rows' table lemmas and the lemma that `Checked.NextOp.step` reads them, for every
input and every `Fork`. The effect law is the Word family's (`WordRow.step_ok`,
`WordRow.step_error`). The rows' agreement with the per-opcode arms is in
`Jaune.Bridge.G2b.CheckedRowAgreement`. -/

namespace Jaune.Checked

open Jaune

theorem NextOp.pushRow?_isSome_iff (n : Jaune.NextOp) :
    (NextOp.pushRow? n).isSome = true ↔ ∃ xs h, n = .push xs h := by
  cases n <;> simp_all [NextOp.pushRow?]

theorem NextOp.pushRow_cost_pos (xs : Bytes) (args : Words (NextOp.pushRow xs).arity) :
    0 < (NextOp.pushRow xs).cost args := by
  simp only [NextOp.pushRow]
  split <;> simp [Gas.base, Gas.veryLow]

/-- A push reads neither the gas left nor the program counter nor anything else of its view. -/
theorem NextOp.pushRow_result (xs : Bytes) (args : Words (NextOp.pushRow xs).arity)
    (v : Word.View) :
    (NextOp.pushRow xs).result.map (· args v) = some xs.toU256 := rfl

/-- The only rule field a push reads: `opcodes.push0`, and only for `PUSH0`. -/
theorem NextOp.pushRow_available (xs : Bytes) (opcodes : OpcodeRules) :
    (NextOp.pushRow xs).available opcodes = (!xs.isEmpty || opcodes.push0) := rfl

/-- A push row's step depends on the opcode rules only through `push0`, and not on its
environment. -/
theorem NextOp.pushRow_step_irrel (xs : Bytes) (o o' : OpcodeRules) (e e' : Word.Env)
    (h : o.push0 = o'.push0) :
    (NextOp.pushRow xs).step o e = (NextOp.pushRow xs).step o' e' := by
  funext m
  simp only [WordRow.step, NextOp.pushRow, h]
  rfl

/-- `PUSH0`–`PUSH32` are the push row, stepped by `WordRow.step`, lifted by `liftMachine` and
turned into a step at the next program counter, by the definition of `NextOp.step`. -/
theorem NextOp.pushRow_step_eq (xs : Bytes) (hxs : xs.length ≤ 32) (r : Frame.Running) :
    Step.ofHalt (r.pc + (NextOp.push xs hxs).size)
        (r.state.liftMachine ((NextOp.pushRow xs).step r.context.block.rules.opcodes
          ⟨r.pc, r.context⟩)) =
      NextOp.step r (.push xs hxs) := rfl

theorem NextOp.pushRow?_step_eq {n : Jaune.NextOp} {row : WordRow}
    (hrow : NextOp.pushRow? n = some row) (r : Frame.Running) :
    Step.ofHalt (r.pc + n.size)
        (r.state.liftMachine (row.step r.context.block.rules.opcodes ⟨r.pc, r.context⟩)) =
      NextOp.step r n := by
  cases n <;> simp only [NextOp.pushRow?, Option.some.injEq, reduceCtorEq] at hrow
  subst hrow
  exact NextOp.pushRow_step_eq _ _ r

/-- A push keeps the world, the substate and the trail, on both channels. -/
theorem NextOp.pushRow_lift_keeps (xs : Bytes) (r : Frame.Running) :
    (match r.state.liftMachine ((NextOp.pushRow xs).step r.context.block.rules.opcodes
        ⟨r.pc, r.context⟩) with
      | .ok s' | .error (_, s') =>
        s'.world = r.state.world ∧ s'.substate = r.state.substate ∧ s'.trail = r.state.trail) := by
  unfold Frame.State.liftMachine
  cases (NextOp.pushRow xs).step r.context.block.rules.opcodes ⟨r.pc, r.context⟩ r.state.machine <;>
    exact ⟨rfl, rfl, rfl⟩

/-- A push depends on the fork only through `opcodes.push0`. -/
theorem NextOp.push_step_congr_fork (xs : Bytes) (hxs : xs.length ≤ 32) (r : Frame.Running)
    (f' : Fork)
    (h : (Fork.ruleSet r.context.block.fork).opcodes.push0 = (Fork.ruleSet f').opcodes.push0) :
    NextOp.step { r with context := { r.context with block := { r.context.block with fork := f' } } }
        (.push xs hxs) =
      NextOp.step r (.push xs hxs) := by
  rw [← NextOp.pushRow_step_eq xs hxs, ← NextOp.pushRow_step_eq xs hxs]
  simp only [BlockContext.rules] at h ⊢
  rw [NextOp.pushRow_step_irrel xs (Fork.ruleSet f').opcodes
    (Fork.ruleSet r.context.block.fork).opcodes _ ⟨r.pc, r.context⟩ h.symm]

end Jaune.Checked
