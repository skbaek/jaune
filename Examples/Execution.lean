import Jaune.SymbolicPush
import Jaune.FrameRun.Adequacy

/-!
A complete symbolic execution of PUSH1 a; PUSH1 b; STOP on the checked interpreter: the audited rows
of `Examples.Execution` restated over `Checked.Frame.Run` and `Checked.exec`. Both operand bytes,
the call context, the world, the substate and the trail remain variable. Six gas and an empty
initial stack make every premise satisfiable.
-/
namespace Examples.Execution

open Jaune

abbrev code (a b : UInt8) : ByteArray := ⟨#[0x60, a, 0x60, b, 0x00]⟩

theorem first (a b : UInt8) :
    Jaune.NextOp.At (code a b) 0 (.push [a] (by simp)) := by
  simp [Jaune.NextOp.At, code, ByteArray.getOp,
    ← ByteArray.size_data, ByteArray.getElem_eq_getElem_data,
    UInt8.toOpClass, UInt8.highs, UInt8.lows, ByteArray.sliceD, UInt8.toHaltOp]
  rfl

theorem second (a b : UInt8) :
    Jaune.NextOp.At (code a b) 2 (.push [b] (by simp)) := by
  simp [Jaune.NextOp.At, code, ByteArray.getOp,
    ← ByteArray.size_data, ByteArray.getElem_eq_getElem_data,
    UInt8.toOpClass, UInt8.highs, UInt8.lows, ByteArray.sliceD, UInt8.toHaltOp]
  rfl

theorem last (a b : UInt8) : Jaune.HaltOp.At (code a b) 4 .stop := by
  simp [Jaune.HaltOp.At, code, ByteArray.getOp,
    ← ByteArray.size_data, ByteArray.getElem_eq_getElem_data,
    UInt8.toOpClass, UInt8.highs, UInt8.lows, UInt8.toHaltOp]
  rfl

def initial (base : Frame.State) : Frame.State :=
  { base with machine := { base.machine with stack := [], gasLeft := 6 } }

def finalState (base : Frame.State) (a b : UInt8) : Frame.State :=
  SymbolicPush.post [b] (SymbolicPush.post [a] (initial base))

theorem final_stack (base : Frame.State) (a b : UInt8) :
    (finalState base a b).machine.stack = [Bytes.toU256 [b], Bytes.toU256 [a]] := rfl

theorem final_gas (base : Frame.State) (a b : UInt8) :
    (finalState base a b).machine.gasLeft = 0 := rfl

theorem final_world (base : Frame.State) (a b : UInt8) :
    (finalState base a b).world = base.world := rfl

/-- Proposed replacement of `Examples.Execution.final_meta` (row 65): the checked state has no
`meta`; its substate and trail are what `meta` grouped, and both are unchanged. -/
theorem final_substate_trail (base : Frame.State) (a b : UInt8) :
    (finalState base a b).substate = base.substate ∧ (finalState base a b).trail = base.trail :=
  ⟨rfl, rfl⟩

/-- A data-valued run on the checked interpreter, from `Checked.SymbolicPush.prepend`. -/
def execution (ctx : CallContext) (base : Frame.State) (a b : UInt8) :
    Frame.Run ⟨0, { ctx with code := code a b }, initial base⟩
      (.exit (.ok (.finished [] (finalState base a b)))) := by
  apply SymbolicPush.prepend [a] (by simp) (first a b)
  · simp [SymbolicPush.cost, initial, Gas.veryLow]
  · simp [initial]
  · exact Or.inl (by simp)
  apply SymbolicPush.prepend [b] (by simp) (second a b)
  · simp [SymbolicPush.cost, SymbolicPush.post, initial, Gas.veryLow]
  · simp [SymbolicPush.post, initial]
  · exact Or.inl (by simp)
  exact .halt (step_of_halt (r := ⟨4, { ctx with code := code a b }, finalState base a b⟩)
    (l := .stop) (last a b))

/-- Adequacy connects the run to the checked total interpreter. -/
theorem interpreter (ctx : CallContext) (base : Frame.State) (a b : UInt8) :
    exec ⟨0, { ctx with code := code a b }, initial base⟩ =
      .ok (.finished [] (finalState base a b)) :=
  (Frame.Run.exec_iff _ _).mp ⟨execution ctx base a b⟩

end Examples.Execution
