import Jaune.Run.PrepareFacts
import Jaune.Run.Transaction

/-!
# Kind coherence of the built top-level inputs (goal `jaune-shape-and-names-v1`, G2b, U103)

`TopLevel.prepare_kindCoherent` carries a creation kind exactly when the code address is absent
from the input message to the prepared one. The two builders of a top-level input satisfy its
premise: a transaction's input is a creation exactly when the transaction has no destination,
and then its code address is the absent destination; a system call's input is a call with its
recipient as code address.
-/

namespace Jaune

open Jaune

/-- A transaction's top-level input is a creation exactly when it has no code address. -/
theorem Transaction.prepare_kindCoherent {block : BlockContext} {state : State}
    {admitted : Transaction.Admitted} {tx : Jaune.Transaction} {prepared : Transaction.Prepared}
    (h : Transaction.prepare block state admitted tx = .ok prepared) :
    prepared.input.message.KindCoherent := by
  unfold Transaction.prepare at h
  obtain ⟨st, _, h⟩ := Except.bind_eq_ok h
  cases h
  unfold Message.KindCoherent
  dsimp only
  cases tx.type.to? <;> simp

/-- A system call's top-level input is a call with a code address. -/
theorem TopLevel.systemInput_kindCoherent (block : BlockContext) (state : State) (recipient : Address)
    (code : ByteArray) (calldata : Bytes) :
    (TopLevel.systemInput block state recipient code calldata).message.KindCoherent :=
  Message.kindCoherent_call rfl recipient rfl

end Jaune
