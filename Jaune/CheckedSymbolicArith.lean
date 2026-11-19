import Jaune.CheckedSymbolicPush
import Jaune.Instructions.WordFacts

/-!
# Symbolic arithmetic rules over the checked interpreter (goal `jaune-shape-and-names-v1`, G2b, F1f)

The audited rows of `Jaune.SymbolicArith`, restated with the same names under `Jaune.Checked` over
`Checked.NextOp.step` and `Checked.Frame.Run`, for the binary family `ADD`, `SUB` and `MUL`. Both
operand words, the rest of the stack, the state, the fork and the program counter remain variable.
-/

namespace Jaune.Checked.SymbolicArith

/-- The covered opcodes. -/
inductive Op
  | add
  | sub
  | mul
  deriving DecidableEq, Repr

/-- The decoded instruction of each covered opcode. -/
def Op.rinst : Op → PlainOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul

/-- The word function, applied to the top of the stack first. -/
def Op.eval : Op → U256 → U256 → U256
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- The static gas charge: `gVerylow` (3) for `ADD`/`SUB`, `gLow` (5) for `MUL`. -/
def Op.cost : Op → Nat
  | .add => Gas.veryLow
  | .sub => Gas.veryLow
  | .mul => Gas.low

/-- The state after success: the two operands are replaced by the result and the static cost is
charged. Memory, state gas, world, substate and trail are unchanged. -/
def post (op : Op) (x y : U256) (rest : List U256) (pre : Frame.State) : Frame.State :=
  { pre with machine := { pre.machine with
      stack := op.eval x y :: rest
      gasLeft := pre.machine.gasLeft - op.cost } }

/-- The state carried by a halt raised after both operands were popped. -/
def popped (rest : List U256) (pre : Frame.State) : Frame.State :=
  { pre with machine := { pre.machine with stack := rest } }

/-- Every covered opcode steps through `applyBinary` with its own function and cost. -/
theorem step_eq (r : Frame.Running) (op : Op) :
    NextOp.step r (.plain op.rinst) =
      Step.ofHalt (r.pc + 1) (r.state.applyBinary op.eval op.cost) := by
  -- The table gives each a binary Word row; the Word family's step on a binary row is
  -- `applyBinary` (`WordRow.binary_step`).
  cases op <;>
    exact congrArg (Step.ofHalt (r.pc + 1))
      (Frame.State.liftMachine_congr r.state (WordRow.binary_step _ _ _ _ _))

/-- Success pops `x` (top) and `y`, pushes `op.eval x y`, and charges `op.cost`. -/
theorem step_success (r : Frame.Running) (op : Op) (x y : U256) (rest : List U256)
    (stack : r.state.machine.stack = x :: y :: rest)
    (gas : op.cost ≤ r.state.machine.gasLeft)
    (room : rest.length < 1024) :
    NextOp.step r (.plain op.rinst) = .next (r.pc + 1) (post op x y rest r.state) := by
  rw [step_eq]
  simp [Frame.State.applyBinary, Frame.State.liftMachine, Machine.applyBinary, Machine.pop, stack,
    Machine.pushItem, Machine.chargeGas, safeSub, gas, Machine.push, room, Step.ofHalt, post,
    Frame.State.withMachine]

/-- With two operands but too little gas, the halted state carries the popped stack. -/
theorem step_outOfGas (r : Frame.Running) (op : Op) (x y : U256) (rest : List U256)
    (stack : r.state.machine.stack = x :: y :: rest)
    (gas : r.state.machine.gasLeft < op.cost) :
    NextOp.step r (.plain op.rinst) = .exit (.halted (.outOfGas .none) (popped rest r.state)) := by
  rw [step_eq]
  simp [Frame.State.applyBinary, Frame.State.liftMachine, Machine.applyBinary, Machine.pop, stack,
    Machine.pushItem, Machine.chargeGas, safeSub, Nat.not_le_of_lt gas, Step.ofHalt, popped,
    Frame.State.withMachine]

/-- Fewer than two operands underflow before any gas is charged; the halted state carries the
emptied stack and the input gas. -/
theorem step_stackUnderflow (r : Frame.Running) (op : Op)
    (short : r.state.machine.stack.length < 2) :
    NextOp.step r (.plain op.rinst) = .exit (.halted (.stackUnderflow .none) (popped [] r.state)) := by
  rw [step_eq]
  rcases r with ⟨pc, ctx, ⟨⟨stk, memory, gasLeft, stateGas, returnData⟩, world, substate, trail⟩⟩
  dsimp only at short
  match stk, short with
  | [], _ => rfl
  | [_], _ => rfl

/-- Prepend a covered binary operation to a run from its successor, preserving its end. -/
def prepend {pc : Nat} {ctx : Jaune.CallContext} {pre : Frame.State} {e : Frame.Run.End}
    (op : Op) (x y : U256) (rest : List U256)
    (decoded : PlainOp.At ctx.code pc op.rinst)
    (stack : pre.machine.stack = x :: y :: rest)
    (gas : op.cost ≤ pre.machine.gasLeft) (room : rest.length < 1024)
    (next : Frame.Run ⟨pc + 1, ctx, post op x y rest pre⟩ e) :
    Frame.Run ⟨pc, ctx, pre⟩ e :=
  .next ((step_of_next (r := ⟨pc, ctx, pre⟩) (n := .plain op.rinst) decoded).trans
    (congrArg Except.ok (step_success ⟨pc, ctx, pre⟩ op x y rest stack gas room))) next

end Jaune.Checked.SymbolicArith
