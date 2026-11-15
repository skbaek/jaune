import Lean

namespace Fidelity

structure Tx where
  gas : Nat

structure Msg where
  gas : Nat

def work (n : Nat) : Nat := n + 1
def fast (n : Nat) : Nat := n + 1

@[csimp] theorem work_eq_fast : @work = @fast := rfl
@[simp] theorem work_zero : work 0 = 1 := rfl
@[inline] def value : Nat := 7
@[irreducible] def hidden : Nat := 9

instance : Inhabited Tx := ⟨⟨3⟩⟩

def transaction : Tx := { gas := 11 }
def message : Msg := { gas := 17 }
def update (t : Tx) : Tx := { t with gas := t.gas + 1 }

example : transaction.gas = 11 := by simp [transaction]
#guard transaction.gas == 11
#guard transaction.gas = 11
#guard (some transaction.gas : Option Nat) matches some _
#guard message.gas == 17

end Fidelity

#guard (3 : Nat) == 3
