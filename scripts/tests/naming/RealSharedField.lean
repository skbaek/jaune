import Jaune.Machine

/-! A downstream client of Jaune's actual transaction and message fields.
The rename pilot applies the same semantic map to this file and Machine.
-/

namespace NamingRealField

open Jaune

def transaction : Transaction := {
  nonce := 0, gasLimit := 11, value := 0, data := [], v := 0, r := [], s := []
  type := .legacy 0 none }

def transactionGas (tx : Transaction) : Nat := tx.gasLimit
def messageGas (msg : Msg) : Nat := msg.gas
def updateTransaction (tx : Transaction) : Transaction := { tx with gasLimit := tx.gasLimit + 1 }
def updateMessage (msg : Msg) : Msg := { msg with gas := msg.gas + 2 }

theorem transaction_update : transactionGas (updateTransaction transaction) = 12 := by
  simp [transactionGas, updateTransaction, transaction]

theorem message_update (msg : Msg) : messageGas (updateMessage msg) = msg.gas + 2 := by
  simp [messageGas, updateMessage]

end NamingRealField
