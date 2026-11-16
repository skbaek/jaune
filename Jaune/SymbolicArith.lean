import Jaune.Exec

/-!
Symbolic rules for the binary arithmetic family `ADD`, `SUB` and `MUL`, with
explicit decoding, gas and stack premises. Both operand words, the rest of the
stack, the state, the fork and the program counter remain variable.

The family is deliberately selected, not exhaustive: other binary opcodes that
share `applyBinary` (`DIV`, `MOD`, shifts, comparisons) are not members of `Op`,
so these rules cannot be instantiated at them.
-/

namespace Jaune.SymbolicArith

/-- The covered opcodes. -/
inductive Op
  | add
  | sub
  | mul
  deriving DecidableEq, Repr

/-- The decoded register instruction of each covered opcode. -/
def Op.rinst : Op → Rinst
  | .add => .add
  | .sub => .sub
  | .mul => .mul

/-- The word function, applied to the top of the stack first. -/
def Op.eval : Op → B256 → B256 → B256
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- The static gas charge: `gVerylow` (3) for `ADD`/`SUB`, `gLow` (5) for `MUL`. -/
def Op.cost : Op → Nat
  | .add => gVerylow
  | .sub => gVerylow
  | .mul => gLow

/-- The state after success: the two operands are replaced by the result and
the static cost is charged. Memory, state gas, metadata and world are unchanged. -/
def post (op : Op) (x y : B256) (rest : List B256) (pre : Devm) : Devm :=
  pre.setMach { pre.mach with
    stack := op.eval x y :: rest
    gasLeft := pre.gasLeft - op.cost }

/-- The state carried by a raw error raised after both operands were popped. -/
def popped (rest : List B256) (pre : Devm) : Devm :=
  pre.setMach { pre.mach with stack := rest }

/-- Every covered opcode steps through `applyBinary` with its own function and cost. -/
theorem step_eq (evm : Evm) (op : Op) :
    Ninst.step evm (.reg op.rinst) =
      Step.ofExecution (evm.pc + 1) (applyBinary op.eval op.cost evm.dyna) := by
  cases op <;> rfl

/-- Success pops `x` (top) and `y`, pushes `op.eval x y`, and charges `op.cost`. -/
theorem step_success (evm : Evm) (op : Op) (x y : B256) (rest : List B256)
    (stack : evm.dyna.stack = x :: y :: rest)
    (gas : op.cost ≤ evm.dyna.gasLeft)
    (room : rest.length < 1024) :
    Ninst.step evm (.reg op.rinst) =
      .cont (evm.pc + 1) (post op x y rest evm.dyna) := by
  rw [step_eq, applyBinary_def]
  dsimp [Devm.stack] at stack
  dsimp [Devm.gasLeft] at gas
  simp [Devm.pop_def, Devm.stack, stack, pushItem_def, chargeGas_def, safeSub, gas,
    Devm.push_def, Except.assert, Devm.setMach, room, post, bind, Except.bind,
    Step.ofExecution, Devm.gasLeft]

/-- With two operands but too little gas, the raw error carries the popped stack. -/
theorem step_outOfGas (evm : Evm) (op : Op) (x y : B256) (rest : List B256)
    (stack : evm.dyna.stack = x :: y :: rest)
    (gas : evm.dyna.gasLeft < op.cost) :
    Ninst.step evm (.reg op.rinst) =
      .halt (.error ⟨.halt (.outOfGas .none), popped rest evm.dyna⟩) := by
  rw [step_eq, applyBinary_def]
  dsimp [Devm.stack] at stack
  dsimp [Devm.gasLeft] at gas
  simp [Devm.pop_def, Devm.stack, stack, pushItem_def, chargeGas_def, safeSub,
    Nat.not_le_of_lt gas, Devm.setMach, popped, bind, Except.bind,
    Step.ofExecution, Devm.gasLeft]

/-- Fewer than two operands underflow before any gas is charged; the raw error
carries the emptied stack and the input gas. -/
theorem step_stackUnderflow (evm : Evm) (op : Op)
    (short : evm.dyna.stack.length < 2) :
    Ninst.step evm (.reg op.rinst) =
      .halt (.error ⟨.halt (.stackUnderflow .none), popped [] evm.dyna⟩) := by
  rw [step_eq, applyBinary_def]
  rcases evm with ⟨pc, sevm, ⟨⟨stk, memory, gasLeft, stateGas⟩, view, world⟩⟩
  dsimp [Devm.stack] at short
  match stk, short with
  | [], _ => rfl
  | [_], _ => rfl

/-- Prepend a decoded covered opcode to a complete continuation, preserving its outcome. -/
def prepend {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (op : Op) (x y : B256) (rest : List B256)
    (decoded : Rinst.At sevm.code pc op.rinst)
    (stack : pre.stack = x :: y :: rest)
    (gas : op.cost ≤ pre.gasLeft) (room : rest.length < 1024)
    (next : Exec (pc + 1) sevm (post op x y rest pre) out) :
    Exec pc sevm pre out :=
  .cont ((Evm.step_next (n := .reg op.rinst) decoded).trans
    (step_success ⟨pc, sevm, pre⟩ op x y rest stack gas room)) next

end Jaune.SymbolicArith
