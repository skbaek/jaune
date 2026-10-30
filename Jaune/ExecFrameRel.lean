import Jaune.ExecFrame

/-!
# Order on `Devm.Rels` and monotonicity of `Devm.Rel`

`Devm.Rel r` is assembled field by field from the 19 relations of `r`. A
consumer that weakens one field (a burn that becomes a `≥`, an equality that
becomes a preorder) otherwise rebuilds all 19 fields by hand, and every new
`Devm.Rels` field is then repaired at each such site. `Devm.Rels.Le r r'` is the
fieldwise implication; each field defaults to the identity, so a literal names
only the fields that differ, and `Devm.Rel.mono` transports a relation along it.
-/

namespace Jaune

open Jaune

/-- `r` is fieldwise at least as strong as `r'`. A field left out of a literal
is discharged by `intro _ _ h; exact h`, so only fields where `r` and `r'`
differ need to be written. -/
structure Devm.Rels.Le (r r' : Devm.Rels) : Prop where
  (stack : ∀ ⦃a b⦄, r.stack a b → r'.stack a b := by intro _ _ h; exact h)
  (memory : ∀ ⦃a b⦄, r.memory a b → r'.memory a b := by intro _ _ h; exact h)
  (gasLeft : ∀ ⦃a b⦄, r.gasLeft a b → r'.gasLeft a b := by intro _ _ h; exact h)
  (logs : ∀ ⦃a b⦄, r.logs a b → r'.logs a b := by intro _ _ h; exact h)
  (refundCounter : ∀ ⦃a b⦄, r.refundCounter a b → r'.refundCounter a b := by intro _ _ h; exact h)
  (output : ∀ ⦃a b⦄, r.output a b → r'.output a b := by intro _ _ h; exact h)
  (accountsToDelete : ∀ ⦃a b⦄, r.accountsToDelete a b → r'.accountsToDelete a b := by intro _ _ h; exact h)
  (returnData : ∀ ⦃a b⦄, r.returnData a b → r'.returnData a b := by intro _ _ h; exact h)
  (error : ∀ ⦃a b⦄, r.error a b → r'.error a b := by intro _ _ h; exact h)
  (accessedAddresses : ∀ ⦃a b⦄, r.accessedAddresses a b → r'.accessedAddresses a b := by intro _ _ h; exact h)
  (accessedStorageKeys : ∀ ⦃a b⦄, r.accessedStorageKeys a b → r'.accessedStorageKeys a b := by intro _ _ h; exact h)
  (state : ∀ ⦃a b⦄, r.state a b → r'.state a b := by intro _ _ h; exact h)
  (createdAccounts : ∀ ⦃a b⦄, r.createdAccounts a b → r'.createdAccounts a b := by intro _ _ h; exact h)
  (transientStorage : ∀ ⦃a b⦄, r.transientStorage a b → r'.transientStorage a b := by intro _ _ h; exact h)
  (stateGas : ∀ ⦃a b⦄, r.stateGas a b → r'.stateGas a b := by intro _ _ h; exact h)
  (accountReads : ∀ ⦃a b⦄, r.accountReads a b → r'.accountReads a b := by intro _ _ h; exact h)
  (storageReads : ∀ ⦃a b⦄, r.storageReads a b → r'.storageReads a b := by intro _ _ h; exact h)
  (storageWrites : ∀ ⦃a b⦄, r.storageWrites a b → r'.storageWrites a b := by intro _ _ h; exact h)
  (touchedAccounts : ∀ ⦃a b⦄, r.touchedAccounts a b → r'.touchedAccounts a b := by intro _ _ h; exact h)

/-- A relation is transported along a fieldwise weakening. -/
theorem Devm.Rel.mono {r r' : Devm.Rels} {devm devm' : Devm} (h : r.Le r')
    (hr : Devm.Rel r devm devm') : Devm.Rel r' devm devm' :=
  { stack := h.stack hr.stack, memory := h.memory hr.memory, gasLeft := h.gasLeft hr.gasLeft, logs := h.logs hr.logs, refundCounter := h.refundCounter hr.refundCounter, output := h.output hr.output, accountsToDelete := h.accountsToDelete hr.accountsToDelete, returnData := h.returnData hr.returnData, error := h.error hr.error, accessedAddresses := h.accessedAddresses hr.accessedAddresses, accessedStorageKeys := h.accessedStorageKeys hr.accessedStorageKeys, state := h.state hr.state, createdAccounts := h.createdAccounts hr.createdAccounts, transientStorage := h.transientStorage hr.transientStorage, stateGas := h.stateGas hr.stateGas, accountReads := h.accountReads hr.accountReads, storageReads := h.storageReads hr.storageReads, storageWrites := h.storageWrites hr.storageWrites, touchedAccounts := h.touchedAccounts hr.touchedAccounts }

theorem Devm.Rels.Le.refl (r : Devm.Rels) : r.Le r :=
  { stack := fun _ _ h => h, memory := fun _ _ h => h, gasLeft := fun _ _ h => h, logs := fun _ _ h => h, refundCounter := fun _ _ h => h, output := fun _ _ h => h, accountsToDelete := fun _ _ h => h, returnData := fun _ _ h => h, error := fun _ _ h => h, accessedAddresses := fun _ _ h => h, accessedStorageKeys := fun _ _ h => h, state := fun _ _ h => h, createdAccounts := fun _ _ h => h, transientStorage := fun _ _ h => h, stateGas := fun _ _ h => h, accountReads := fun _ _ h => h, storageReads := fun _ _ h => h, storageWrites := fun _ _ h => h, touchedAccounts := fun _ _ h => h }

theorem Devm.Rels.Le.trans {r r' r'' : Devm.Rels} (h : r.Le r') (h' : r'.Le r'') : r.Le r'' :=
  { stack := fun _ _ x => h'.stack (h.stack x), memory := fun _ _ x => h'.memory (h.memory x), gasLeft := fun _ _ x => h'.gasLeft (h.gasLeft x), logs := fun _ _ x => h'.logs (h.logs x), refundCounter := fun _ _ x => h'.refundCounter (h.refundCounter x), output := fun _ _ x => h'.output (h.output x), accountsToDelete := fun _ _ x => h'.accountsToDelete (h.accountsToDelete x), returnData := fun _ _ x => h'.returnData (h.returnData x), error := fun _ _ x => h'.error (h.error x), accessedAddresses := fun _ _ x => h'.accessedAddresses (h.accessedAddresses x), accessedStorageKeys := fun _ _ x => h'.accessedStorageKeys (h.accessedStorageKeys x), state := fun _ _ x => h'.state (h.state x), createdAccounts := fun _ _ x => h'.createdAccounts (h.createdAccounts x), transientStorage := fun _ _ x => h'.transientStorage (h.transientStorage x), stateGas := fun _ _ x => h'.stateGas (h.stateGas x), accountReads := fun _ _ x => h'.accountReads (h.accountReads x), storageReads := fun _ _ x => h'.storageReads (h.storageReads x), storageWrites := fun _ _ x => h'.storageWrites (h.storageWrites x), touchedAccounts := fun _ _ x => h'.touchedAccounts (h.touchedAccounts x) }

/-- Every state is `Devm.Rels.eq`-related to itself. -/
theorem Devm.Rel.eq_refl (devm : Devm) : Devm.Rel Devm.Rels.eq devm devm :=
  { stack := rfl, memory := rfl, gasLeft := rfl, logs := rfl, refundCounter := rfl, output := rfl, accountsToDelete := rfl, returnData := rfl, error := rfl, accessedAddresses := rfl, accessedStorageKeys := rfl, state := rfl, createdAccounts := rfl, transientStorage := rfl, stateGas := rfl, accountReads := rfl, storageReads := rfl, storageWrites := rfl, touchedAccounts := rfl }

/-- A relation that every field's equality implies relates a state to itself. -/
theorem Devm.Rel.of_eq_le {r : Devm.Rels} (h : Devm.Rels.eq.Le r) (devm : Devm) :
    Devm.Rel r devm devm :=
  (Devm.Rel.eq_refl devm).mono h

-- A literal names only the field that differs: equality implies the `Burn` frame.
example (devm : Devm) : Devm.Burn devm devm :=
  (Devm.Rel.eq_refl devm).mono { gasLeft := by intro _ _ h; subst h; exact Nat.le_refl _ }

end Jaune
