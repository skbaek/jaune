import Jaune.MessageCall.Frame

/-! Field-wise relations over the four lifetime groups. -/

namespace Jaune

/-- Select how each machine field is compared. -/
structure Machine.FieldRelations where
  stack : List U256 → List U256 → Prop := Eq
  memory : Memory → Memory → Prop := Eq
  gasLeft : Nat → Nat → Prop := Eq
  stateGas : StateGasMeter → StateGasMeter → Prop := Eq
  returnData : Bytes → Bytes → Prop := Eq

structure Machine.Related (relations : Machine.FieldRelations) (before after : Machine) : Prop where
  stack : relations.stack before.stack after.stack
  memory : relations.memory before.memory after.memory
  gasLeft : relations.gasLeft before.gasLeft after.gasLeft
  stateGas : relations.stateGas before.stateGas after.stateGas
  returnData : relations.returnData before.returnData after.returnData

/-- Select how each world field is compared. -/
structure World.FieldRelations where
  state : State → State → Prop := Eq
  transientStorage : TransientStorage → TransientStorage → Prop := Eq
  storageWrites : KeySet → KeySet → Prop := Eq

structure World.Related (relations : World.FieldRelations) (before after : World) : Prop where
  state : relations.state before.state after.state
  transientStorage : relations.transientStorage before.transientStorage after.transientStorage
  storageWrites : relations.storageWrites before.storageWrites after.storageWrites

/-- Select how each substate field is compared. -/
structure Substate.FieldRelations where
  logs : List Log → List Log → Prop := Eq
  refund : Int → Int → Prop := Eq
  selfDestructs : AddressSet → AddressSet → Prop := Eq
  accessedAddresses : AddressSet → AddressSet → Prop := Eq
  accessedStorageKeys : KeySet → KeySet → Prop := Eq
  touchedAccounts : AddressSet → AddressSet → Prop := Eq

structure Substate.Related (relations : Substate.FieldRelations) (before after : Substate) : Prop where
  logs : relations.logs before.logs after.logs
  refund : relations.refund before.refund after.refund
  selfDestructs : relations.selfDestructs before.selfDestructs after.selfDestructs
  accessedAddresses : relations.accessedAddresses before.accessedAddresses after.accessedAddresses
  accessedStorageKeys : relations.accessedStorageKeys before.accessedStorageKeys after.accessedStorageKeys
  touchedAccounts : relations.touchedAccounts before.touchedAccounts after.touchedAccounts

/-- Select how each trail field is compared. -/
structure Trail.FieldRelations where
  createdAccounts : AddressSet → AddressSet → Prop := Eq
  accountReads : AddressSet → AddressSet → Prop := Eq
  storageReads : KeySet → KeySet → Prop := Eq
  touchedRIPEMD160 : Bool → Bool → Prop := Eq

structure Trail.Related (relations : Trail.FieldRelations) (before after : Trail) : Prop where
  createdAccounts : relations.createdAccounts before.createdAccounts after.createdAccounts
  accountReads : relations.accountReads before.accountReads after.accountReads
  storageReads : relations.storageReads before.storageReads after.storageReads
  touchedRIPEMD160 : relations.touchedRIPEMD160 before.touchedRIPEMD160 after.touchedRIPEMD160

/-- Each component defaults to comparing its fields for equality. -/
structure Frame.State.FieldRelations where
  machine : Machine.FieldRelations := {}
  world : World.FieldRelations := {}
  substate : Substate.FieldRelations := {}
  trail : Trail.FieldRelations := {}

structure Frame.State.Related (relations : Frame.State.FieldRelations) (before after : Frame.State) : Prop where
  machine : Machine.Related relations.machine before.machine after.machine
  world : World.Related relations.world before.world after.world
  substate : Substate.Related relations.substate before.substate after.substate
  trail : Trail.Related relations.trail before.trail after.trail

/-- The four legacy machine fields may change. Returned child data still agrees. -/
def Frame.State.FieldRelations.machineFrame : Frame.State.FieldRelations where
  machine := {
    stack := fun _ _ => True
    memory := fun _ _ => True
    gasLeft := fun _ _ => True
    stateGas := fun _ _ => True }

/-- The gas-erasure relation retains the memory size and the full state-gas meter. -/
def Frame.State.FieldRelations.eqModGas : Frame.State.FieldRelations where
  machine := {
    gasLeft := fun _ _ => True }

/-- Instructions in this class leave the world, self-destruct set and created accounts fixed. -/
def Frame.State.FieldRelations.instructionFrame : Frame.State.FieldRelations where
  machine := {
    stack := fun _ _ => True
    memory := fun _ _ => True
    gasLeft := fun _ _ => True
    stateGas := fun _ _ => True
    returnData := fun _ _ => True }
  substate := {
    logs := fun _ _ => True
    refund := fun _ _ => True
    accessedAddresses := fun _ _ => True
    accessedStorageKeys := fun _ _ => True
    touchedAccounts := fun _ _ => True }
  trail := {
    accountReads := fun _ _ => True
    storageReads := fun _ _ => True
    touchedRIPEMD160 := fun _ _ => True }

/-- A persistent storage instruction preserves account balances and code.
Its caller records the written storage key. -/
def Frame.State.FieldRelations.stateWriteFrame : Frame.State.FieldRelations :=
  { instructionFrame with world := {
      state := fun pre post => ∀ address,
        (pre.get address).balance = (post.get address).balance ∧
        (pre.get address).code = (post.get address).code,
      storageWrites := fun _ _ => True } }

def Frame.State.FieldRelations.transientWriteFrame : Frame.State.FieldRelations :=
  { instructionFrame with world := {transientStorage := fun _ _ => True} }

theorem Frame.State.Related.eq_iff {a b : Frame.State} :
    Frame.State.Related {} a b ↔ a = b := by
  constructor
  · rintro ⟨⟨_, _, _, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _, _, _, _⟩, ⟨_, _, _, _⟩⟩
    rcases a with ⟨⟨_, _, _, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _, _, _, _⟩, ⟨_, _, _, _⟩⟩
    rcases b with ⟨⟨_, _, _, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _, _, _, _⟩, ⟨_, _, _, _⟩⟩
    congr
  · rintro rfl
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

end Jaune
