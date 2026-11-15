import Jaune.Machine

/-! A downstream client of Jaune's actual transaction and message fields.
The rename pilot applies the same semantic map to this file and Machine.
-/

namespace NamingRealField

open Jaune

def transaction : Tx := {
  nonce := 0, gas := 11, value := 0, data := [], v := 0, r := [], s := []
  type := .zero 0 none }

def transactionGas (tx : Tx) : Nat := tx.gas
def messageGas (msg : Msg) : Nat := msg.gas
def updateTransaction (tx : Tx) : Tx := { tx with gas := tx.gas + 1 }
def updateMessage (msg : Msg) : Msg := { msg with gas := msg.gas + 2 }

theorem transaction_update : transactionGas (updateTransaction transaction) = 12 := by
  simp [transactionGas, updateTransaction, transaction]

theorem message_update (msg : Msg) : messageGas (updateMessage msg) = msg.gas + 2 := by
  simp [messageGas, updateMessage]

end NamingRealField
