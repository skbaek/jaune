import Jaune.MessageCall.FrameRelations
import Jaune.Bridge.G2b.CheckedFrame
import Jaune.ExecFrame

namespace Jaune.Checked

/-- Translate every observable legacy column. A raw machine has no RIPEMD-160 trail flag. -/
def Frame.State.Rels.ofLegacy (r : Jaune.Devm.Rels) : Frame.State.Rels where
  machine := {
    stack := r.stack, memory := fun a b => r.memory a.toMem b.toMem,
    gasLeft := r.gasLeft, stateGas := r.stateGas, returnData := r.returnData }
  world := {state := r.state, transientStorage := r.transientStorage, storageWrites := r.storageWrites}
  substate := {
    logs := r.logs, refund := r.refundCounter, selfDestructs := r.accountsToDelete,
    accessedAddresses := r.accessedAddresses, accessedStorageKeys := r.accessedStorageKeys,
    touchedAccounts := r.touchedAccounts }
  trail := {
    createdAccounts := r.createdAccounts, accountReads := r.accountReads,
    storageReads := r.storageReads, touchedRIPEMD160 := fun _ _ => True }

/-- Erasing the typed memories preserves the field relation. The two obsolete
machine columns are exactly the empty output and absent stored error. -/
theorem Frame.State.rel_legacy_iff (r : Jaune.Devm.Rels) (a b : Frame.State) :
    Jaune.Devm.Rel r a.toLegacy.toDevm b.toLegacy.toDevm ↔
      Frame.State.Rel (.ofLegacy r) a b ∧ r.output [] [] ∧ r.error none none := by
  constructor
  · intro h
    exact ⟨⟨⟨h.stack, h.memory, h.gasLeft, h.stateGas, h.returnData⟩,
      ⟨h.state, h.transientStorage, h.storageWrites⟩,
      ⟨h.logs, h.refundCounter, h.accountsToDelete, h.accessedAddresses, h.accessedStorageKeys,
        h.touchedAccounts⟩,
      ⟨h.createdAccounts, h.accountReads, h.storageReads, trivial⟩⟩, h.output, h.error⟩
  · rintro ⟨h, output, err⟩
    exact ⟨h.machine.stack, h.machine.memory, h.machine.gasLeft, h.substate.logs,
      h.substate.refund, output, h.substate.selfDestructs, h.machine.returnData, err,
      h.substate.accessedAddresses, h.substate.accessedStorageKeys, h.world.state,
      h.trail.createdAccounts, h.world.transientStorage, h.machine.stateGas, h.trail.accountReads,
      h.trail.storageReads, h.world.storageWrites, h.substate.touchedAccounts⟩

end Jaune.Checked
