import Batteries.Tactic.OpenPrivate
import Jaune.Instructions.Word

/-! The Memory family as rows (goal `jaune-shape-and-names-v1`, S4).

`MLOAD`, `MSTORE`, `MSTORE8`, `CALLDATACOPY`, `CODECOPY`, `RETURNDATACOPY`, `MCOPY` and
`KECCAK256` pop their operands, pay a base price plus the extension of the ranges their effect
touches, and then move bytes. A row holds no function on the machine: the effect is one
constructor of `MemoryEffect`, and `MemoryEffect.apply` is the only place bytes move. The step
returns a `Machine`, so lifted through `Frame.State.liftMachine` it cannot touch the world, the
substate or the trail. -/

open private keccakReadRun from Jaune.Machine

namespace Jaune.Checked

open Jaune

/-- A source a copy reads. Call data is zero-filled, code is `STOP`-filled, and return data is
strict: reading past its end halts (EIP-211). -/
inductive MemoryBuffer where
  | calldata
  | code
  | returnData
deriving DecidableEq, Repr

/-- What a Memory row does with its operands, in pop order. The index is the number of operands.
No constructor reads the world or writes outside memory and the stack. -/
inductive MemoryEffect : Fin 4 → Type where
  /-- Copy from a buffer: destination, offset, size. -/
  | copy (source : MemoryBuffer) : MemoryEffect 3
  /-- `MCOPY`: destination, source, size. -/
  | move : MemoryEffect 3
  /-- `MSTORE`: offset, word (32 bytes). -/
  | storeWord : MemoryEffect 2
  /-- `MSTORE8`: offset, word (its low byte). -/
  | storeByte : MemoryEffect 2
  /-- `MLOAD`: offset; pushes the word read. -/
  | load : MemoryEffect 1
  /-- `KECCAK256`: offset, size; pushes the digest of the range, read in place. -/
  | digest : MemoryEffect 2

/-- The ranges whose extension a row pays for, a function of the effect alone, in today's
order (`MCOPY` extends over the source, then the destination). -/
def MemoryEffect.ranges : {a : Fin 4} → MemoryEffect a → Words a → List (Nat × Nat)
  | _, .copy _, (d, _, n) => [(d.toNat, n.toNat)]
  | _, .move, (d, s, n) => [(s.toNat, n.toNat), (d.toNat, n.toNat)]
  | _, .storeWord, (i, _) => [(i.toNat, 32)]
  | _, .storeByte, (i, _) => [(i.toNat, 1)]
  | _, .load, i => [(i.toNat, 32)]
  | _, .digest, (i, n) => [(i.toNat, n.toNat)]

/-- What an effect does after the charge, from the frame's three buffers (call data, code, return
data), the operands and the memory: the new memory and the word to push, if any. `none` is the
strict return-data bound (`outOfBoundsRead`). An effect reads nothing else of the call context. -/
def MemoryEffect.apply : {a : Fin 4} → MemoryEffect a → (calldata : Bytes) → (code : ByteArray) →
    (returnData : Bytes) → Words a → Memory → Option (Memory × Option U256)
  | _, .copy .calldata, calldata, _, _, (d, o, n), memory =>
    some (memory.write d.toNat (calldata.sliceD o.toNat n.toNat 0), none)
  | _, .copy .code, _, code, _, (d, o, n), memory =>
    some (memory.write d.toNat (code.sliceD o.toNat n.toNat (HaltOp.toUInt8 .stop)), none)
  | _, .copy .returnData, _, _, returnData, (d, o, n), memory =>
    if returnData.length < o.toNat + n.toNat then none
    else some (memory.write d.toNat (returnData.sliceD o.toNat n.toNat 0), none)
  | _, .move, _, _, _, (d, s, n), memory =>
    let (value, memory) := memory.read s.toNat n.toNat
    some (memory.write d.toNat value, none)
  | _, .storeWord, _, _, _, (i, x), memory => some (memory.write i.toNat x.toBytes, none)
  | _, .storeByte, _, _, _, (i, x), memory => some (memory.write i.toNat [x.2.2.toUInt8], none)
  | _, .load, _, _, _, i, memory =>
    let (value, memory) := memory.read i.toNat 32
    some (memory, some (Bytes.toU256 value))
  | _, .digest, _, _, _, (i, n), memory =>
    some (memory.extend i.toNat n.toNat,
      some (keccakReadRun (fun j => memory.data.getD j 0) i.toNat n.toNat 0 (.replicate 25 0)))

/-- A Memory row: availability, arity, effect and base price (static plus per-word part). The
extension price is not data: it is the extension of `effect.ranges`. -/
structure MemoryRow where
  available : OpcodeRules → Bool := fun _ => true
  arity : Fin 4
  effect : MemoryEffect arity
  base : Words arity → Nat

/-- The one step of the Memory family: availability, pops, the charge (base plus extension),
then the effect, with the strict return-data bound after the charge and a push last. -/
def MemoryRow.step (row : MemoryRow) (opcodes : OpcodeRules) (ctx : CallContext) (m : Machine) :
    Except (ExceptionalHalt × Machine) Machine := do
  unless row.available opcodes do throw (.invalidOpcode .none, m)
  let (args, m) ← m.popWords row.arity
  let m ← m.chargeGas (row.base args + m.extCost (row.effect.ranges args))
  match row.effect.apply ctx.calldata ctx.code m.returnData args m.memory with
  | none => throw (.outOfBoundsRead .none, m)
  | some (memory, none) => pure { m with memory }
  | some (memory, some x) => Machine.push x { m with memory }

end Jaune.Checked
