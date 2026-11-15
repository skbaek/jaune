import Jaune.Execution

/-! WP lifetime prototype. These records are not a replacement specification.
The interpreter adapter is separate; the equations here concern resume alone.

The design followed is the accepted W1/W3 note (sections 2.1-2.4): a child is
seeded as today (logs empty except the EIP-7708 transfer log, refund zero,
deletions inherited or none by rule, empty touched and read sets), and the
caller absorbs a successful child's substate with today's `HashSet.union`
merges, behind one `Substate.absorb`. The caller's trail is
`checkpoint.trail.absorb result.trail` in every outcome.
-/
namespace Examples.ShapePilot.Prototype
open Jaune

/-- Frame-local: discarded when the frame ends. -/
@[ext] structure Machine where
  stack : List B256
  memory : Mem
  gasLeft : Nat
  stateGas : StateGasMeter
  returnData : Bytes

/-- Dropped when the frame fails. -/
@[ext] structure Substate where
  logs : List Log
  refund : Int
  selfDestructs : AdrSet
  accessedAddresses : AdrSet
  accessedStorageKeys : KeySet
  touchedAccounts : AdrSet

/-- Kept when the frame fails. `ripemd160Touched` is `false` in a running
frame; only settlement sets it, in a failed result, and only `resume` reads it. -/
@[ext] structure Trail where
  createdAccounts : AdrSet
  accountReads : AdrSet
  storageReads : KeySet
  ripemd160Touched : Bool

/-- What a frame is entered from and falls back to. It has no machine: the
caller's machine travels in the continuation. -/
@[ext] structure Checkpoint where
  world : Jaune.World
  substate : Substate
  trail : Trail

/-- A running frame's dynamic state, the four lifetime groups. -/
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
  trail := ⟨d.createdAccounts, d.meta.accountReads, d.meta.storageReads, false⟩ }

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

def Checkpoint.ofLegacy (d : Devm) : Checkpoint :=
  let v := Dynamic.ofLegacy d
  ⟨v.world, v.substate, v.trail⟩

/-- A failed legacy frame's trail: the touch of RIPEMD-160 it keeps is read
off its settled touched set, as `incorporateChildOnError` does. -/
def Trail.ofFailedLegacy (d : Devm) : Trail :=
  { (Dynamic.ofLegacy d).trail with
    ripemd160Touched := d.meta.touchedAccounts.contains ripemd160Address }

/-- The only substate effect a failed child may retain (`Machine.lean:6200`). -/
def Substate.keepTouch (s : Substate) (trail : Trail) : Substate :=
  { s with touchedAccounts := if trail.ripemd160Touched
      then s.touchedAccounts.insert ripemd160Address else s.touchedAccounts }

/-- Today's successful merge (`incorporateChildOnSuccess`,
`incorporateChildAmsterdamOnSuccess`), one rule branch on touched accounts. -/
def Substate.absorb (stateGas : Bool) (saved child : Substate) : Substate :=
  { logs := saved.logs ++ child.logs
    refund := saved.refund + child.refund
    selfDestructs := saved.selfDestructs.union child.selfDestructs
    accessedAddresses := saved.accessedAddresses.union child.accessedAddresses
    accessedStorageKeys := saved.accessedStorageKeys.union child.accessedStorageKeys
    touchedAccounts := if stateGas then saved.touchedAccounts
      else saved.touchedAccounts.union child.touchedAccounts }

/-- The caller's trail after any child outcome (all four `incorporateChild*`). -/
def Trail.absorb (saved child : Trail) : Trail :=
  { createdAccounts := child.createdAccounts
    accountReads := saved.accountReads.union child.accountReads
    storageReads := saved.storageReads.union child.storageReads
    ripemd160Touched := saved.ripemd160Touched }

/-- Cryptographic and internal errors are not frame results. They end the run;
every consumer of today's fault payload drops it, so a fault carries none. -/
inductive Fault where
  | crypto (reason : CryptoError)
  | internal (reason : InternalError)

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

/-- The meter facts Amsterdam's merge asserts (`Devm.AmsterdamChildUncommitted`,
and `Devm.AmsterdamFailedChildSettled` less its refund conjunct, which a failed
result cannot carry). -/
def Result.meterSettled (r : Result) : Bool :=
  let m := r.stateGas
  if r.failed then m.committedSpill == 0 && m.spilled == 0 && m.left == m.baseline
  else m.committedSpill == 0
end Frame

inductive ReturnTarget where
  | call (outputIndex outputSize : Nat)
  | create (address : Adr)

/-- What the calling opcode leaves for `resume`: the caller's machine after
call preparation, where the status goes, and the charge to refund. The refund
is zero under the one-dimensional rules and for uncharged creations. -/
structure Continuation where
  machine : Machine
  target : ReturnTarget
  stateGas : Bool
  newAccountRefund : Nat

/-- The meter calculation is independent of world and substate. -/
def returnedMeter (c : Continuation) (r : Frame.Result) : Mach :=
  let parent := c.machine
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

def returnedData (c : Continuation) (r : Frame.Result) : Bytes :=
  if r.failed then r.output else match c.target with
    | .call .. => r.output
    | .create _ => []

/-- The caller's machine after the child is absorbed and before the status
push: what a stack overflow at the push halts the caller with. -/
def mergedMachine (c : Continuation) (r : Frame.Result) : Machine :=
  let m := returnedMeter c r
  ⟨c.machine.stack, c.machine.memory, m.gasLeft, m.stateGas, returnedData c r⟩

def statusWord (c : Continuation) (r : Frame.Result) : B256 :=
  if r.failed then 0 else match c.target with
    | .call .. => 1
    | .create address => address.toB256

/-- The exact calling-opcode effect on the caller's machine. -/
def returnedMachine (c : Continuation) (r : Frame.Result) : Machine :=
  let m := mergedMachine c r
  { m with
    stack := statusWord c r :: m.stack
    memory := match c.target with
      | .call index size => m.memory.write index (r.output.take size)
      | .create _ => m.memory }

/-- The world and substate the caller continues with. -/
def returnedWorld (c : Continuation) (cp : Checkpoint) : Frame.Result →
    Jaune.World × Substate
  | .success _ _ _ world substate _ => (world, cp.substate.absorb c.stateGas substate)
  | r => (cp.world, if c.stateGas then cp.substate else cp.substate.keepTouch r.trail)

/-- The caller's state after absorbing the child, before the status push. -/
def mergedState (c : Continuation) (cp : Checkpoint) (r : Frame.Result) : Dynamic :=
  let (world, substate) := returnedWorld c cp r
  ⟨mergedMachine c r, world, substate, cp.trail.absorb r.trail⟩

/-- `Resume.run`: Amsterdam's two assertions, then the merge, then the push
with its capacity check. A failed push halts the caller with the merged state
(`execFueled`, `Execution.lean:1936`). -/
def resume (c : Continuation) (cp : Checkpoint) (r : Frame.Result) :
    Except Fault (Except (ExceptionalHalt × Dynamic) Dynamic) :=
  if c.stateGas && !r.meterSettled then
    .error (.internal (.invariant (.text (if r.failed
      then "failed Amsterdam child is not settled"
      else "Amsterdam child has committed state-gas spill"))))
  else
    let merged := mergedState c cp r
    if c.machine.stack.length < 1024 then
      .ok (.ok { merged with machine := returnedMachine c r })
    else .ok (.error (.stackOverflow .none, merged))

/-! ### S3 over `resume` alone

No theorem below unfolds an interpreter definition or opens a private helper.
The premises are the calling opcode's stack capacity and, under Amsterdam,
the meter facts the merge asserts (W1 note 2.3 and 6.3). -/

/-- (a) and (c): a failed child leaves the caller's world and substate as
saved, except the one touch a rule keeps, and the caller absorbs its trail. -/
theorem resume_failed (c : Continuation) (cp : Checkpoint) (r : Frame.Result)
    (failed : r.failed = true)
    (meter : c.stateGas = true → r.meterSettled = true)
    (room : c.machine.stack.length < 1024) :
    resume c cp r = .ok (.ok {
      machine := returnedMachine c r
      world := cp.world
      substate := if c.stateGas then cp.substate else cp.substate.keepTouch r.trail
      trail := cp.trail.absorb r.trail }) := by
  have guard : (c.stateGas && !r.meterSettled) = false := by
    cases h : c.stateGas <;> simp_all
  cases r with
  | success => simp [Frame.Result.failed] at failed
  | revert => simp only [resume, guard, room, mergedState, returnedWorld,
      Bool.false_eq_true, ↓reduceIte]
  | halt => simp only [resume, guard, room, mergedState, returnedWorld,
      Bool.false_eq_true, ↓reduceIte]

/-- A successful child hands back its world; its substate is absorbed. -/
theorem resume_success (c : Continuation) (cp : Checkpoint)
    (output : Bytes) (gasLeft : Nat) (stateGas : StateGasMeter)
    (world : Jaune.World) (substate : Substate) (trail : Trail)
    (meter : c.stateGas = true → stateGas.committedSpill = 0)
    (room : c.machine.stack.length < 1024) :
    resume c cp (.success output gasLeft stateGas world substate trail) = .ok (.ok {
      machine := returnedMachine c (.success output gasLeft stateGas world substate trail)
      world := world
      substate := cp.substate.absorb c.stateGas substate
      trail := cp.trail.absorb trail }) := by
  have guard : (c.stateGas &&
      !(Frame.Result.success output gasLeft stateGas world substate trail).meterSettled)
      = false := by
    cases h : c.stateGas <;> simp_all [Frame.Result.meterSettled, Frame.Result.failed,
      Frame.Result.stateGas]
  simp only [resume, guard, room, mergedState, returnedWorld, Bool.false_eq_true, ↓reduceIte,
    Frame.Result.trail]

/-- A failed push halts the caller at its own merged state, never at the
child's checkpoint. -/
theorem resume_overflow (c : Continuation) (cp : Checkpoint) (r : Frame.Result)
    (meter : c.stateGas = true → r.meterSettled = true)
    (full : ¬ c.machine.stack.length < 1024) :
    resume c cp r = .ok (.error (.stackOverflow .none, mergedState c cp r)) := by
  have guard : (c.stateGas && !r.meterSettled) = false := by
    cases h : c.stateGas <;> simp_all
  simp only [resume, guard, full, Bool.false_eq_true, ↓reduceIte]

/-- Amsterdam's assertion is kept: an unsettled meter is a fault. -/
theorem resume_unsettled (c : Continuation) (cp : Checkpoint) (r : Frame.Result)
    (amsterdam : c.stateGas = true) (unsettled : r.meterSettled = false) :
    ∃ reason, resume c cp r = .error (.internal reason) := by
  simp only [resume, amsterdam, unsettled, Bool.not_false, Bool.and_self, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- Specializations used by the worked example's clients. -/
theorem resume_revert (c : Continuation) (cp : Checkpoint)
    (output : Bytes) (gasLeft : Nat) (stateGas : StateGasMeter) (trail : Trail)
    (meter : c.stateGas = true → (Frame.Result.revert output gasLeft stateGas trail).meterSettled = true)
    (room : c.machine.stack.length < 1024) :
    resume c cp (.revert output gasLeft stateGas trail) = .ok (.ok {
      machine := returnedMachine c (.revert output gasLeft stateGas trail)
      world := cp.world
      substate := if c.stateGas then cp.substate else cp.substate.keepTouch trail
      trail := cp.trail.absorb trail }) :=
  resume_failed c cp _ rfl meter room

theorem resume_halt (c : Continuation) (cp : Checkpoint)
    (reason : ExceptionalHalt) (stateGas : StateGasMeter) (trail : Trail)
    (meter : c.stateGas = true → (Frame.Result.halt reason stateGas trail).meterSettled = true)
    (room : c.machine.stack.length < 1024) :
    resume c cp (.halt reason stateGas trail) = .ok (.ok {
      machine := returnedMachine c (.halt reason stateGas trail)
      world := cp.world
      substate := if c.stateGas then cp.substate else cp.substate.keepTouch trail
      trail := cp.trail.absorb trail }) :=
  resume_failed c cp _ rfl meter room

/-! ### S3(b): the calling opcode's effect on the caller's machine -/

theorem returnedMachine_stack_failed (c : Continuation) (r : Frame.Result)
    (failed : r.failed = true) :
    (returnedMachine c r).stack = 0 :: c.machine.stack := by
  simp only [returnedMachine, statusWord, failed, ↓reduceIte, mergedMachine]

theorem returnedMachine_memory_call (c : Continuation) (r : Frame.Result)
    (index size : Nat) (target : c.target = .call index size) :
    (returnedMachine c r).memory = c.machine.memory.write index (r.output.take size) := by
  simp only [returnedMachine, target, mergedMachine]

theorem returnedMachine_memory_create (c : Continuation) (r : Frame.Result)
    (address : Adr) (target : c.target = .create address) :
    (returnedMachine c r).memory = c.machine.memory := by
  simp only [returnedMachine, target, mergedMachine]

theorem returnedMachine_returnData_failed (c : Continuation) (r : Frame.Result)
    (failed : r.failed = true) :
    (returnedMachine c r).returnData = r.output := by
  simp only [returnedMachine, mergedMachine, returnedData, failed, ↓reduceIte]

/-- One-dimensional rules: the child's execution gas comes back, the state-gas
meter is the caller's. -/
theorem returnedMachine_meters_oneDim (c : Continuation) (r : Frame.Result)
    (oneDim : c.stateGas = false) :
    (returnedMachine c r).gasLeft = c.machine.gasLeft + r.gasLeft ∧
    (returnedMachine c r).stateGas = c.machine.stateGas := by
  simp only [returnedMachine, mergedMachine, returnedMeter, oneDim, Bool.false_eq_true,
    ↓reduceIte, and_self]

/-- Amsterdam, failed child: both meters come back, then the new-account charge
the caller paid before the child ran is refunded. -/
theorem returnedMachine_meters_failed_amsterdam (c : Continuation) (r : Frame.Result)
    (amsterdam : c.stateGas = true) (failed : r.failed = true) :
    let m : Mach := {
      stack := c.machine.stack, memory := c.machine.memory
      gasLeft := c.machine.gasLeft + r.gasLeft
      stateGas := { c.machine.stateGas with
        left := c.machine.stateGas.left + r.stateGas.left
        spilled := c.machine.stateGas.spilled + r.stateGas.spilled } }
    (returnedMachine c r).gasLeft = (m.creditStateGasRefund c.newAccountRefund).gasLeft ∧
    (returnedMachine c r).stateGas = (m.creditStateGasRefund c.newAccountRefund).stateGas := by
  simp only [returnedMachine, mergedMachine, returnedMeter, amsterdam, failed, ↓reduceIte,
    and_self]

end Examples.ShapePilot.Prototype
