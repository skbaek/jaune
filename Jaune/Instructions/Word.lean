import Jaune.MessageCall.CheckedState

namespace Jaune.Checked

/-- Operands in EVM pop order, with one type for each supported arity. -/
def Words : Fin 4 → Type
  | 0 => Unit
  | 1 => U256
  | 2 => U256 × U256
  | 3 => U256 × U256 × U256

def Machine.popWords (m : Machine) : (arity : Fin 4) →
    Except (ExceptionalHalt × Machine) (Words arity × Machine)
  | 0 => .ok ((), m)
  | 1 => m.pop
  | 2 => do
    let (x, m) ← m.pop
    let (y, m) ← m.pop
    return ((x, y), m)
  | 3 => do
    let (x, m) ← m.pop
    let (y, m) ← m.pop
    let (z, m) ← m.pop
    return ((x, y, z), m)

structure Word.Env where
  pc : Nat
  context : CallContext
deriving Inhabited

/-- A result can read these observations after the charge succeeds. -/
structure Word.View extends Word.Env where
  memorySize : Nat
  returnData : Bytes
  gasLeft : Nat

structure WordRow where
  available : OpcodeRules → Bool := fun _ => true
  arity : Fin 4
  cost : Words arity → Nat
  result : Option (Words arity → Word.View → U256)

def WordRow.context (cost : Nat) (read : Word.View → U256) : WordRow where
  arity := 0
  cost := fun _ => cost
  result := some fun _ v => read v

def WordRow.unary (f : U256 → U256) (cost : Nat) : WordRow where
  arity := 1
  cost := fun _ => cost
  result := some fun x _ => f x

def WordRow.binary (f : U256 → U256 → U256) (cost : Nat) : WordRow where
  arity := 2
  cost := fun _ => cost
  result := some fun (x, y) _ => f x y

def WordRow.ternary (f : U256 → U256 → U256 → U256) (cost : Nat) : WordRow where
  arity := 3
  cost := fun _ => cost
  result := some fun (x, y, z) _ => f x y z

def WordRow.step (row : WordRow) (opcodes : OpcodeRules) (env : Word.Env) (m : Machine) :
    Except (ExceptionalHalt × Machine) Machine := do
  unless row.available opcodes do throw (.invalidOpcode .none, m)
  let (args, m) ← m.popWords row.arity
  let m ← m.chargeGas (row.cost args)
  match row.result with
  | none => return m
  | some f => m.push (f args ⟨env, m.memory.size, m.returnData, m.gasLeft⟩)

end Jaune.Checked
