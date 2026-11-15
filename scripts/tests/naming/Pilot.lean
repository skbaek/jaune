import Lean

namespace Pilot

structure Tx where
  gas : Nat

structure Msg where
  gas : Nat

def transaction : Tx := { gas := 11 }
def message : Msg := { gas := 17 }
def update (tx : Tx) : Tx := { tx with gas := tx.gas + 1 }
def transactionGas (tx : Tx) := tx.gas
def messageGas (msg : Msg) := msg.gas

example : transactionGas (update transaction) = 12 := by
  simp [transactionGas, update, transaction]

example : messageGas message = 17 := by
  simp [messageGas, message]

#guard message.gas == 17
#guard transaction.gas == 11

end Pilot
