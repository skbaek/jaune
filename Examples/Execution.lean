import Jaune.SymbolicPush

/-!
A complete symbolic execution of PUSH1 a; PUSH1 b; STOP.
Both operand bytes, the environment, metadata and world remain variable.
Six gas and an empty initial stack make every premise satisfiable.
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

def initial (base : Devm) : Devm :=
  base.setMach { base.mach with stack := [], gasLeft := 6 }

def finalState (base : Devm) (a b : UInt8) : Devm :=
  SymbolicPush.post [b] (SymbolicPush.post [a] (initial base))

theorem final_stack (base : Devm) (a b : UInt8) :
    (finalState base a b).stack = [Bytes.toU256 [b], Bytes.toU256 [a]] := rfl

theorem final_gas (base : Devm) (a b : UInt8) :
    (finalState base a b).gasLeft = 0 := rfl

theorem final_world (base : Devm) (a b : UInt8) :
    (finalState base a b).world = base.world := rfl

theorem final_meta (base : Devm) (a b : UInt8) :
    (finalState base a b).meta = base.meta := rfl

/-! ## The derivation and its adequacy

The derivation over `Exec` and `exec` of the four-part message call. -/

/-- A data-valued derivation on the four-part chain, from `SymbolicPush.prepend`. -/
def execution (env : Sevm) (base : Devm) (a b : UInt8) :
    Jaune.Exec 0 { env with code := code a b } (initial base) (.ok (finalState base a b)) := by
  apply SymbolicPush.prepend [a] (by simp) (first a b)
  · simp [SymbolicPush.cost, initial, Devm.gasLeft, Devm.setMach, Gas.veryLow]
  · simp [initial, Devm.stack, Devm.setMach]
  · exact Or.inl (by simp)
  apply SymbolicPush.prepend [b] (by simp) (second a b)
  · simp [SymbolicPush.cost, SymbolicPush.post, initial, Devm.gasLeft,
      Devm.setMach, Gas.veryLow]
  · simp [SymbolicPush.post, initial, Devm.stack, Devm.setMach]
  · exact Or.inl (by simp)
  exact .halt (Jaune.Evm.step_of_halt (devm := finalState base a b) (l := .stop) (last a b))

/-- Adequacy on the four-part chain connects the derivation to `exec`. -/
theorem interpreter (env : Sevm) (base : Devm) (a b : UInt8) :
    exec ⟨0, { env with code := code a b }, initial base⟩ = .ok (finalState base a b) :=
  (Jaune.exec_iff_exec_eq _ _ _ _).mp ⟨execution env base a b⟩

end Examples.Execution
