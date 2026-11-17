import Jaune.Execution
import Jaune.MessageCall

/-!
# The four-part message call: maps from today's definitions (W1 unit B, bridge)

The maps between today's message-call types and the staged ones of `Jaune.MessageCall`, used
only in bridges. They live in this bridge module with the old side and are deleted with it
after the gate's tag (goal 3.1).

Also here, about today's definitions: `Resume.parent`, the saved caller every `Resume` carries,
and `Execution.Clean`, the premise that a raw result stores no settled error (`note-rev3-delta.md`
section 3.1).
-/

namespace Jaune

/-- The saved caller a `Resume` carries. -/
def Resume.parent : Resume → Devm
  | .create parent _ => parent
  | .call parent _ _ => parent
  | .createAmsterdam _ parent _ _ => parent
  | .callAmsterdam _ parent _ _ _ => parent

/-- A raw result that stores no settled error. The error channel is unconstrained. -/
def Execution.Clean : Execution → Prop
  | .ok d => d.error = none
  | .error _ => True

namespace Staging

/-- Today's dynamic state grouped by lifetime. It forgets `output` and `error`; the trail's
RIPEMD-160 flag is `false`, as in every running frame. -/
def Frame.State.ofDevm (d : Devm) : Frame.State :=
  { machine :=
      { stack := d.stack, memory := d.memory, gasLeft := d.gasLeft, stateGas := d.stateGas
        returnData := d.returnData }
    world := d.world
    substate :=
      { logs := d.logs, refund := d.refundCounter, selfDestructs := d.accountsToDelete
        accessedAddresses := d.accessedAddresses, accessedStorageKeys := d.accessedStorageKeys
        touchedAccounts := d.meta.touchedAccounts }
    trail :=
      { createdAccounts := d.createdAccounts, accountReads := d.meta.accountReads
        storageReads := d.meta.storageReads, touchedRIPEMD160 := false } }

/-- A lifetime-grouped state as today's dynamic state, with no output and no stored error. -/
def Frame.State.toDevm (s : Frame.State) : Devm :=
  { mach :=
      { stack := s.machine.stack, memory := s.machine.memory, gasLeft := s.machine.gasLeft
        stateGas := s.machine.stateGas }
    «meta» :=
      { logs := s.substate.logs, refundCounter := s.substate.refund, output := []
        accountsToDelete := s.substate.selfDestructs, returnData := s.machine.returnData
        error := none, accessedAddresses := s.substate.accessedAddresses
        accessedStorageKeys := s.substate.accessedStorageKeys
        createdAccounts := s.trail.createdAccounts, accountReads := s.trail.accountReads
        storageReads := s.trail.storageReads, touchedAccounts := s.substate.touchedAccounts }
    world := s.world }

/-- Grouping by lifetime and back loses nothing of a state with no output and no stored error. -/
theorem Frame.State.toDevm_ofDevm (d : Devm) (hout : d.output = []) (herr : d.error = none) :
    (Frame.State.ofDevm d).toDevm = d := by
  rcases d with ⟨⟨stack, memory, gasLeft, stateGas⟩, ⟨logs, refund, output, deletions,
    returnData, error, accessed, keys, created, accountReads, storageReads, touched⟩, world⟩
  simp only [Devm.output, Devm.error] at hout herr
  subst hout herr
  rfl

/-- Today's message as a staged one. `isCreate` gives the kind; today it is the frame's flag,
not the message's. -/
def Message.ofLegacy (msg : Msg) (isCreate : Bool) : Message :=
  { context :=
      { caller := msg.caller, recipient := msg.currentTarget, value := msg.value
        calldata := msg.data, code := msg.code, depthLeft := msg.depth
        isStatic := msg.isStatic, tx := msg.tenv.stat, block := msg.benv.stat }
    kind := if isCreate then .create else .call
    codeAddress := msg.codeAddress
    target := msg.target
    gas := msg.gas
    stateGasGrant := msg.stateGasGrant
    transfersValue := msg.shouldTransferValue
    disablePrecompiles := msg.disablePrecompiles }

/-- What a `Resume` waits with besides its saved caller. -/
def Pending.ofLegacy : Resume → Pending
  | .create parent newAddress =>
    ⟨.create newAddress, false, parent.output, parent.error⟩
  | .call parent outputIndex outputSize =>
    ⟨.call outputIndex outputSize, false, parent.output, parent.error⟩
  | .createAmsterdam _ parent newAddress charged =>
    ⟨.create newAddress, charged, parent.output, parent.error⟩
  | .callAmsterdam _ parent outputIndex outputSize charged =>
    ⟨.call outputIndex outputSize, charged, parent.output, parent.error⟩

/-- A spawned child frame of today, with the `Resume` it was spawned with: the message is the
outer one (before a creation's set-up), the checkpoint is the saved caller. -/
def Frame.ofLegacy (f : Jaune.Frame) (rsm : Resume) : Frame :=
  ⟨Message.ofLegacy f.outer f.isCreate, Frame.State.ofDevm rsm.parent⟩

/-- A top-level frame of today: the checkpoint is the state its message starts on. -/
def Frame.ofTop (msg : Msg) (isCreate : Bool) : Frame :=
  ⟨Message.ofLegacy msg isCreate, Frame.State.ofDevm (initDevm msg)⟩

end Staging

end Jaune
