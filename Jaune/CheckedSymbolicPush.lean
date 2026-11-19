import Jaune.FrameRun.CheckedBasic
import Jaune.ExecFrame

/-!
# Symbolic PUSH rules over the checked interpreter (goal `jaune-shape-and-names-v1`, G2b, F1f)

The audited rows of `Jaune.SymbolicPush`, restated with the same names under `Jaune.Checked` over
`Checked.NextOp.step` and `Checked.Frame.Run`. The state, operand bytes, fork and program counter
remain variable.
-/

namespace Jaune.Checked

/-- A decoded next-op instruction steps through `NextOp.step`. -/
theorem step_of_next {r : Frame.Running} {n : NextOp} (h : NextOp.At r.context.code r.pc n) :
    step r = .ok (NextOp.step r n) := by
  unfold step
  rw [show r.getOp = some (.next n) from h]

/-- A decoded halting instruction exits with its own result. -/
theorem step_of_halt {r : Frame.Running} {l : HaltOp} (h : HaltOp.At r.context.code r.pc l) :
    step r = (HaltOp.run r.context r.state l).map Step.exit := by
  unfold step
  rw [show r.getOp = some (.halt l) from h]

namespace SymbolicPush

def cost (bytes : Bytes) : Nat := if bytes = [] then Gas.base else Gas.veryLow

def afterCharge (bytes : Bytes) (pre : Frame.State) : Frame.State :=
  { pre with machine := { pre.machine with gasLeft := pre.machine.gasLeft - cost bytes } }

def post (bytes : Bytes) (pre : Frame.State) : Frame.State :=
  { pre with machine := { pre.machine with
      stack := bytes.toU256 :: pre.machine.stack
      gasLeft := pre.machine.gasLeft - cost bytes } }

private theorem pushAvail (r : Frame.Running) (bytes : Bytes)
    (hgate : bytes ≠ [] ∨ r.context.block.rules.opcodes.push0) :
    (!bytes.isEmpty || r.context.block.rules.opcodes.push0) = true := by
  rcases hgate with hne | hon
  · simp [List.isEmpty_iff, hne]
  · simp [hon]

/-- Success charges the selected PUSH cost and prepends the operand word. -/
theorem step_success (r : Frame.Running) (bytes : Bytes) (width : bytes.length ≤ 32)
    (gas : cost bytes ≤ r.state.machine.gasLeft)
    (room : r.state.machine.stack.length < 1024)
    (hgate : bytes ≠ [] ∨ r.context.block.rules.opcodes.push0) :
    NextOp.step r (.push bytes width) = .next (r.pc + bytes.length + 1) (post bytes r.state) := by
  dsimp [cost] at gas
  simp only [NextOp.step, Family.run]
  unfold WordRow.step
  simp only [NextOp.pushRow, pushAvail r bytes hgate, ↓reduceIte, Machine.popWords]
  simp [List.isEmpty_iff, pure, Except.pure, Frame.State.chargeGas, Frame.State.push, Frame.State.liftMachine, Machine.chargeGas,
    Machine.push, safeSub, gas, room, bind, Except.bind, Step.ofHalt, post, cost, NextOp.size,
    Frame.State.withMachine, Nat.add_assoc]

/-- Gas exhaustion is checked before stack capacity and leaves the input state. -/
theorem step_outOfGas (r : Frame.Running) (bytes : Bytes) (width : bytes.length ≤ 32)
    (gas : r.state.machine.gasLeft < cost bytes)
    (hgate : bytes ≠ [] ∨ r.context.block.rules.opcodes.push0) :
    NextOp.step r (.push bytes width) = .exit (.halted (.outOfGas .none) r.state) := by
  dsimp [cost] at gas
  simp only [NextOp.step, Family.run]
  unfold WordRow.step
  simp only [NextOp.pushRow, pushAvail r bytes hgate, ↓reduceIte, Machine.popWords]
  simp [List.isEmpty_iff, pure, Except.pure, Frame.State.chargeGas, Frame.State.liftMachine, Machine.chargeGas, safeSub,
    Nat.not_le_of_lt gas, bind, Except.bind, Step.ofHalt, Frame.State.withMachine]

/-- With gas available, stack overflow retains the gas charge in the halted state. -/
theorem step_stackOverflow (r : Frame.Running) (bytes : Bytes) (width : bytes.length ≤ 32)
    (gas : cost bytes ≤ r.state.machine.gasLeft)
    (full : 1024 ≤ r.state.machine.stack.length)
    (hgate : bytes ≠ [] ∨ r.context.block.rules.opcodes.push0) :
    NextOp.step r (.push bytes width) =
      .exit (.halted (.stackOverflow .none) (afterCharge bytes r.state)) := by
  dsimp [cost] at gas
  simp only [NextOp.step, Family.run]
  unfold WordRow.step
  simp only [NextOp.pushRow, pushAvail r bytes hgate, ↓reduceIte, Machine.popWords]
  simp [List.isEmpty_iff, pure, Except.pure, Frame.State.chargeGas, Frame.State.push, Frame.State.liftMachine, Machine.chargeGas,
    Machine.push, safeSub, gas, Nat.not_lt_of_ge full, bind, Except.bind, Step.ofHalt, afterCharge,
    cost, Frame.State.withMachine]

/-- Prepend a decoded PUSH to a run from its successor, preserving its end. -/
def prepend {pc : Nat} {ctx : CallContext} {pre : Frame.State} {e : Frame.Run.End}
    (bytes : Bytes) (width : bytes.length ≤ 32)
    (decoded : NextOp.At ctx.code pc (.push bytes width))
    (gas : cost bytes ≤ pre.machine.gasLeft) (room : pre.machine.stack.length < 1024)
    (hgate : bytes ≠ [] ∨ ctx.block.rules.opcodes.push0)
    (next : Frame.Run ⟨pc + bytes.length + 1, ctx, post bytes pre⟩ e) :
    Frame.Run ⟨pc, ctx, pre⟩ e :=
  .next ((step_of_next (r := ⟨pc, ctx, pre⟩) decoded).trans
    (congrArg Except.ok (step_success ⟨pc, ctx, pre⟩ bytes width gas room hgate))) next

end SymbolicPush

end Jaune.Checked
