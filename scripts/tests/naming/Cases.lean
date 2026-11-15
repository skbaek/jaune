import Lean

namespace CasesPilot

structure Tx where
  gas : Nat

inductive Op where
  | gas
  | stop

def valid : Op → Prop
  | .gas => True
  | .stop => True

theorem allValid (op : Op) : valid op := by
  cases op <;> change True
  case gas => trivial
  case stop => trivial

def transaction : Tx := { gas := 11 }
#guard transaction.gas == 11

end CasesPilot
