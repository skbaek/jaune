import Jaune.MessageCall.CheckedState

/-! The Shuffle family (S4): `DUP`, `SWAP`, and EIP-8024's `DUPN`, `SWAPN` and `EXCHANGE`.

A row is data: an availability flag, a fixed charge and a stack shuffle, or `none` for an
immediate that does not decode. The family step runs over the frame-local `Machine` alone, so a
row cannot reach the world, the substate or the trail; and `Shuffle` has no constructor that
reads or writes memory, the return data or the state-gas meter. -/

namespace Jaune.Checked

open Jaune

/-- A stack shuffle, indices counted from the top (zero-based). -/
inductive Shuffle where
  /-- Push a copy of the word at `index`. -/
  | dup (index : Nat)
  /-- Swap the top word with the word at `index + 1`. -/
  | swap (index : Nat)
  /-- Exchange the words at `i` and `j`. -/
  | exchange (i j : Nat)
deriving DecidableEq, Repr

/-- The stack a shuffle makes, or `none` when the stack is too short (`stackUnderflow`). -/
def Shuffle.apply : Shuffle → List U256 → Option (List U256)
  | .dup index, stack => stack[index]?.map (· :: stack)
  | .swap index, stack => List.swap stack index
  | .exchange i j, stack => List.exchange stack i j

/-- Whether a shuffle can grow the stack (`DUP`), and so halt with `stackOverflow`. -/
def Shuffle.grows : Shuffle → Bool
  | .dup _ => true
  | _ => false

structure ShuffleRow where
  available : OpcodeRules → Bool := fun _ => true
  cost : Nat := Gas.veryLow
  /-- `none`: an immediate that does not decode, an invalid instruction after the charge. -/
  shuffle : Option Shuffle

/-- Run one shuffle on a charged machine: underflow, then (for `DUP`) overflow. -/
def Shuffle.run (sh : Shuffle) (m : Machine) : Except (ExceptionalHalt × Machine) Machine :=
  match sh with
  | .dup index =>
    match m.stack[index]? with
    | none => .error (.stackUnderflow .none, m)
    | some word => m.push word
  | .swap index =>
    match List.swap m.stack index with
    | none => .error (.stackUnderflow .none, m)
    | some stack => .ok { m with stack }
  | .exchange i j =>
    match List.exchange m.stack i j with
    | none => .error (.stackUnderflow .none, m)
    | some stack => .ok { m with stack }

/-- The family step: availability, the charge, the decode, the shuffle. -/
def ShuffleRow.step (row : ShuffleRow) (opcodes : OpcodeRules) (m : Machine) :
    Except (ExceptionalHalt × Machine) Machine := do
  unless row.available opcodes do throw (.invalidOpcode .none, m)
  let m ← m.chargeGas row.cost
  match row.shuffle with
  | none => throw (.invalidOpcode .none, m)
  | some sh => sh.run m

/-- `DUP1`–`DUP16` and `SWAP1`–`SWAP16`. -/
def PlainOp.shuffleRow? : Jaune.PlainOp → Option ShuffleRow
  | .dup n => some { shuffle := some (.dup n.val) }
  | .swap n => some { shuffle := some (.swap n.val) }
  | _ => none

/-- EIP-8024's `DUPN`, `SWAPN` and `EXCHANGE`: the immediate decodes to the shuffle. -/
def NextOp.shuffleRow? : Jaune.NextOp → Option ShuffleRow
  | .dupn imm => some
    { available := OpcodeRules.stackAccess
      shuffle := (decodeSingle imm).map (fun n => .dup (n - 1)) }
  | .swapn imm => some
    { available := OpcodeRules.stackAccess
      shuffle := (decodeSingle imm).map (fun n => .swap (n - 1)) }
  | .exchange imm => some
    { available := OpcodeRules.stackAccess
      shuffle := (decodePair imm).map (fun pair => .exchange pair.1 pair.2) }
  | _ => none

end Jaune.Checked
