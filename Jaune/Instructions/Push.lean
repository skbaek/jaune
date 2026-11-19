import Jaune.Instructions.Word

/-! The push family (S4): `PUSH0`–`PUSH32` as Word rows.

A push is a Word row of arity zero whose result is its immediate: it is stepped by
`WordRow.step` and obeys `WordRow.step_ok` and `WordRow.step_error`, so it needs no step or law of
its own. -/

namespace Jaune.Checked

open Jaune

/-- `PUSH0` (EIP-3855: available only under `opcodes.push0`, charged `Gas.base`) and
`PUSH1`–`PUSH32` (always available, charged `Gas.veryLow`): push the immediate. -/
def NextOp.pushRow (xs : Bytes) : WordRow where
  available := fun opcodes => !xs.isEmpty || opcodes.push0
  arity := 0
  cost := fun _ => if xs.isEmpty then Gas.base else Gas.veryLow
  result := some fun _ _ => xs.toU256

/-- The push rows of the non-message operations. -/
def NextOp.pushRow? : Jaune.NextOp → Option WordRow
  | .push xs _ => some (NextOp.pushRow xs)
  | _ => none

end Jaune.Checked
