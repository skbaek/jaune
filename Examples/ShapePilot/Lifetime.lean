import Jaune.Execution

/-! WP lifetime prototype. These records are not a replacement specification.
The interpreter adapter is separate; the equations here concern resume alone.
-/
namespace Examples.ShapePilot.Prototype
open Jaune

@[ext] structure Machine where
  stack : List U256
  memory : Mem
  gasLeft : Nat
  stateGas : StateGasMeter
  returnData : Bytes

@[ext] structure Substate where
  logs : List Log
  refund : Int
  selfDestructs : AdrSet
  accessedAddresses : AdrSet
  accessedStorageKeys : KeySet
  touchedAccounts : AdrSet

@[ext] structure Trail where
  createdAccounts : AdrSet
  accountReads : AdrSet
  storageReads : KeySet
  ripemd160Touched : Bool

@[ext] structure Dynamic where
  machine : Machine
  world : Jaune.World
  substate : Substate
  trail : Trail

/-- The boundary to existing instruction primitives. Output and error belong
in a step outcome, not in the dynamic state. -/
def Dynamic.ofLegacy (d : Devm) : Dynamic := {
  machine := ⟨d.stack, d.memory, d.gasLeft, d.stateGas, d.returnData⟩
  world := d.world
  substate := ⟨d.logs, d.refundCounter, d.accountsToDelete, d.accessedAddresses,
    d.accessedStorageKeys, d.meta.touchedAccounts⟩
  trail := ⟨d.createdAccounts, d.meta.accountReads, d.meta.storageReads,
    d.meta.touchedAccounts.contains ripemd160Address⟩ }

def Dynamic.toLegacy (d : Dynamic) : Devm := {
  mach := ⟨d.machine.stack, d.machine.memory, d.machine.gasLeft, d.machine.stateGas⟩
  world := d.world
  «meta» := {
    logs := d.substate.logs
    refundCounter := d.substate.refund
    accountsToDelete := d.substate.selfDestructs
    accessedAddresses := d.substate.accessedAddresses
    accessedStorageKeys := d.substate.accessedStorageKeys
    touchedAccounts := d.substate.touchedAccounts
    createdAccounts := d.trail.createdAccounts
    accountReads := d.trail.accountReads
    storageReads := d.trail.storageReads
    returnData := d.machine.returnData
    output := []
    error := none } }

/-- The only substate effect a failed child may retain. -/
def Substate.keepTouch (s : Substate) (trail : Trail) : Substate :=
  { s with touchedAccounts := if trail.ripemd160Touched
      then s.touchedAccounts.insert ripemd160Address else s.touchedAccounts }

namespace Frame
/-- Neither failed constructor can carry a world or substate. -/
inductive Result where
  | success (output : Bytes) (gasLeft : Nat) (stateGas : StateGasMeter)
      (world : Jaune.World) (substate : Substate) (trail : Trail)
  | revert (output : Bytes) (gasLeft : Nat) (stateGas : StateGasMeter) (trail : Trail)
  | halt (reason : ExceptionalHalt) (stateGas : StateGasMeter) (trail : Trail)

def Result.trail : Result → Trail
  | .success _ _ _ _ _ t | .revert _ _ _ t | .halt _ _ t => t

def Result.failed : Result → Bool
  | .success .. => false
  | .revert .. | .halt .. => true

def Result.output : Result → Bytes
  | .success o .. | .revert o .. => o
  | .halt .. => []

def Result.gasLeft : Result → Nat
  | .success _ g .. | .revert _ g .. => g
  | .halt .. => 0

def Result.stateGas : Result → StateGasMeter
  | .success _ _ m .. | .revert _ _ m .. | .halt _ m _ => m
end Frame

inductive ReturnTarget where
  | call (outputIndex outputSize : Nat)
  | create (address : Address)

/-- Opcode preparation supplies the saved caller and the charge to refund.
The latter is zero for the one-dimensional rules and uncharged creations. -/
structure Continuation where
  target : ReturnTarget
  stateGas : Bool
  newAccountRefund : Nat

/-- The meter calculation is independent of world and substate. -/
def returnedMeter (c : Continuation) (parent : Machine) (r : Frame.Result) : Mach :=
  let m : Mach := {
    stack := parent.stack
    memory := parent.memory
    gasLeft := parent.gasLeft + r.gasLeft
    stateGas := if c.stateGas then
      { parent.stateGas with
        left := parent.stateGas.left + r.stateGas.left
        spilled := parent.stateGas.spilled + r.stateGas.spilled }
      else parent.stateGas }
  if c.stateGas then
    if r.failed then m.creditStateGasRefund c.newAccountRefund
    else m.repayStateGasSpill
  else m

/-- The exact calling-opcode effect. The stack capacity check belongs to
`resume`; this function merely describes the successful return. -/
def returnedMachine (c : Continuation) (parent : Machine) (r : Frame.Result) : Machine :=
  let m := returnedMeter c parent r
  let value : U256 := if r.failed then 0 else match c.target with
    | .call .. => 1
    | .create address => address.toU256
  let memory := match c.target with
    | .call index size => parent.memory.write index (r.output.take size)
    | .create _ => parent.memory
  let returnData := if r.failed then r.output else match c.target with
    | .call .. => r.output
    | .create _ => []
  ⟨value :: parent.stack, memory, m.gasLeft, m.stateGas, returnData⟩

/-- One world/substate choice, with no child machine state to roll back. -/
def returnedState (c : Continuation) (saved : Dynamic) (r : Frame.Result) : Dynamic :=
  let (world, substate) := match r with
    | .success _ _ _ world substate _ => (world, substate)
    | .revert .. | .halt .. => (saved.world, saved.substate.keepTouch r.trail)
  ⟨returnedMachine c saved.machine r, world, substate, r.trail⟩

def resume (c : Continuation) (saved : Dynamic) (r : Frame.Result) :
    Except ExceptionalHalt Dynamic :=
  if saved.machine.stack.length < 1024 then .ok (returnedState c saved r)
  else .error (.stackOverflow .none)

/-- No rollback, settlement, interpreter or private-helper premise. The sole
precondition is the calling opcode's ordinary stack-capacity check. -/
theorem resume_revert (c : Continuation) (saved : Dynamic)
    (output : Bytes) (gasLeft : Nat) (stateGas : StateGasMeter) (trail : Trail)
    (room : saved.machine.stack.length < 1024) :
    resume c saved (.revert output gasLeft stateGas trail) = .ok {
      machine := returnedMachine c saved.machine (.revert output gasLeft stateGas trail)
      world := saved.world
      substate := saved.substate.keepTouch trail
      trail := trail } := by
  simp only [resume, room, ↓reduceIte, returnedState, Frame.Result.trail]

theorem resume_halt (c : Continuation) (saved : Dynamic)
    (reason : ExceptionalHalt) (stateGas : StateGasMeter) (trail : Trail)
    (room : saved.machine.stack.length < 1024) :
    resume c saved (.halt reason stateGas trail) = .ok {
      machine := returnedMachine c saved.machine (.halt reason stateGas trail)
      world := saved.world
      substate := saved.substate.keepTouch trail
      trail := trail } := by
  simp only [resume, room, ↓reduceIte, returnedState, Frame.Result.trail]

end Examples.ShapePilot.Prototype
