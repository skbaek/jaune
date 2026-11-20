import Jaune.Transaction
import Jaune.MessageCall.ResumeFacts
import Jaune.MessageCall.DriverInvariants
import Jaune.Run.Canonical

/-!
# The shape pilot's two executions, on the four-part message call

The pilot of goal `jaune-shape-and-names-v1` (WP) ran two programs on a prototype that never
landed (`Examples/ShapePilot/` on `wsl/jsn-pilot`). Here they run on the landed definitions:
`enter`, `exec`, `Frame.runTop` and `Message.run`, with the pilot's expected values.

* A Prague caller CALLs a child that writes storage and a log, then reverts with the byte
  `0xAA`. The caller pushes 42 and goes on; it receives the byte in its output window and its
  return data, and keeps neither the child's slot nor its log.
* An Amsterdam caller CREATEs a child whose initcode returns one STOP byte; the code deposit
  runs out of gas. The caller pushes 42 and goes on, keeps its incremented nonce and the warmed
  new address, loses the deployment and receives the new-account state-gas refund.

The observations name the raw child (before settlement) apart from the settled result, so a
preflight refusal cannot pass for either execution. The caller's final stack comes from its
raw result, since a settled result carries no machine.
-/

namespace Examples.ShapePilot

open Jaune

def parentAddress : Address := 0x1000
def childAddress : Address := 0x20

/-- Write slot zero and a log, then revert with the byte 0xAA. -/
def revertingChild : ByteArray := ⟨#[
  0x60, 0x07, 0x60, 0x00, 0x55,
  0x60, 0x00, 0x60, 0x00, 0xA0,
  0x60, 0xAA, 0x60, 0x00, 0x53,
  0x60, 0x01, 0x60, 0x00, 0xFD]⟩

/-- CALL with a one-byte output window, then push 42 to witness continuation. -/
def callingParent : ByteArray := ⟨#[
  0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00,
  0x60, 0x00, 0x60, 0x20, 0x61, 0xFF, 0xFF, 0xF1,
  0x60, 0x2A, 0x00]⟩

/-- Initcode returns one STOP byte. It does not revert or halt exceptionally. -/
def initcode : ByteArray := ⟨#[
  0x60, 0x00, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xF3]⟩

/-- Copy the trailing initcode into memory, CREATE, then continue. -/
def creatingParent : ByteArray := ⟨#[
  0x60, 0x0A, 0x60, 0x11, 0x60, 0x00, 0x39,
  0x60, 0x0A, 0x60, 0x00, 0x60, 0x00, 0xF0,
  0x60, 0x2A, 0x00] ++ initcode.data⟩

def message (fork : Fork) (code : ByteArray) (gas stateGas : Nat)
    (extraState : State := .empty) : Msg :=
  let state := (extraState.set parentAddress
    { nonce := 1, balance := 0, storage := .empty, code := code })
  { (default : Msg) with
    benv := { (default : Benv) with
      state := state
      stat := { (default : BenvStat) with fork := fork, origState := state } }
    caller := parentAddress
    target := some parentAddress
    currentTarget := parentAddress
    codeAddress := some parentAddress
    code := code
    gas := gas
    stateGasGrant := stateGas
    depth := 8 }

def callMessage : Msg :=
  message .prague callingParent 100000 0
    (State.setCode .empty childAddress revertingChild)

def createMessage : Msg :=
  message .amsterdam creatingParent 13000 amsterdamStateGasRules.newAccount

def newAddress : Address := computeContractAddress parentAddress 1

/-- The top-level frame of a pilot message: a call to the parent. -/
def topFrame (msg : Msg) : Frame := Frame.ofTop msg false

/-- The machine a frame's code is entered with. -/
def entered (f : Frame) : Option Evm :=
  match enterWith f f.checkpoint.toDevm with
  | .run evm => some evm
  | .done _ => none

/-- Inspect a finite prefix up to the first spawned frame. No child is skipped. -/
def firstSpawn : Nat → Evm → Option (Evm × Frame × Pending × Nat)
  | 0, _ => none
  | n + 1, evm =>
    match Evm.step evm with
    | .next pc devm => firstSpawn n ⟨pc, evm.sta, devm⟩
    | .spawn child pending pc => some (evm, child, pending, pc)
    | .halt _ => none

/-- The raw machine a raw result carries. -/
def rawMachine : Execution → Devm
  | .ok d | .error (_, d) => d

structure CallObservation where
  isCall : Bool
  codeAddress : Option Nat
  childReverted : Bool
  childOutput : Bytes
  childSlot : Nat
  childLogs : Nat
  resultReverted : Bool
  resultOutput : Bytes
  callerStack : List Nat
  callerOutputWindow : Bytes
  callerReturnData : Bytes
  settledSlot : Nat
  settledLogs : Nat
  topLevelSlot : Nat
  topLevelLogs : Nat
  deriving Repr, BEq

def observeCall : Option CallObservation := do
  let f := topFrame callMessage
  let start ← entered f
  let (_, child, _, _) ← firstSpawn 100 start
  let .run childStart := enter child | none
  let raw := exec childStart
  let .ok result := settle child raw | none
  let callerRaw := exec start
  let .ok (.success _ _ _ world substate _) := Frame.runTop f | none
  let .ok run := TopLevel.run callMessage | none
  pure {
    isCall := child.message.kind == .call
    codeAddress := child.message.codeAddress.map Address.toNat
    childReverted := match raw with | .error (.revert, _) => true | _ => false
    childOutput := (rawMachine raw).output
    childSlot := ((rawMachine raw).getStorVal childAddress 0).toNat
    childLogs := (rawMachine raw).logs.length
    resultReverted := match result with | .revert .. => true | _ => false
    resultOutput := result.output
    callerStack := (rawMachine callerRaw).stack.map U256.toNat
    callerOutputWindow := ((rawMachine callerRaw).memory.read 0 1).1
    callerReturnData := (rawMachine callerRaw).returnData
    settledSlot := ((world.state.get childAddress).storage.get 0).toNat
    settledLogs := substate.logs.length
    topLevelSlot := ((run.state.get childAddress).storage.get 0).toNat
    topLevelLogs := run.logs.length }

structure CreateObservation where
  isCreate : Bool
  codeAddress : Option Nat
  childFinished : Bool
  childOutput : Bytes
  childNonce : Nat
  depositHalted : Bool
  callerStack : List Nat
  creatorNonce : Nat
  destinationWarm : Bool
  deployedNonce : Nat
  deployedCodeSize : Nat
  refundedStateGas : Nat
  topLevelCreatorNonce : Nat
  topLevelDeployedCodeSize : Nat
  deriving Repr, BEq

def observeCreate : Option CreateObservation := do
  let f := topFrame createMessage
  let start ← entered f
  let (_, child, _, _) ← firstSpawn 100 start
  let .run childStart := enter child | none
  let raw := exec childStart
  let .ok result := settle child raw | none
  let callerRaw := exec start
  let .ok (.success _ _ meter world substate _) := Frame.runTop f | none
  let .ok run := TopLevel.run createMessage | none
  let state := run.state
  pure {
    isCreate := child.message.kind == .create
    codeAddress := child.message.codeAddress.map Address.toNat
    childFinished := match raw with | .ok _ => true | _ => false
    childOutput := (rawMachine raw).output
    childNonce := ((rawMachine raw).state.get newAddress).nonce.toNat
    depositHalted := match result with | .halt (.outOfGas _) .. => true | _ => false
    callerStack := (rawMachine callerRaw).stack.map U256.toNat
    creatorNonce := (world.state.get parentAddress).nonce.toNat
    destinationWarm := substate.accessedAddresses.contains newAddress
    deployedNonce := (world.state.get newAddress).nonce.toNat
    deployedCodeSize := (world.state.get newAddress).code.size
    refundedStateGas := meter.left
    topLevelCreatorNonce := (state.get parentAddress).nonce.toNat
    topLevelDeployedCodeSize := (state.get newAddress).code.size }

-- The expected values are the pilot's (`Examples/ShapePilot/Programs.lean` and `Runs.lean` on
-- `wsl/jsn-pilot`), read off the landed definitions.
#guard observeCall == some {
  isCall := true, codeAddress := some 32, childReverted := true, childOutput := [170],
  childSlot := 7, childLogs := 1, resultReverted := true, resultOutput := [170],
  callerStack := [42, 0], callerOutputWindow := [170], callerReturnData := [170],
  settledSlot := 0, settledLogs := 0, topLevelSlot := 0, topLevelLogs := 0 }

#guard observeCreate == some {
  isCreate := true, codeAddress := none, childFinished := true, childOutput := [0],
  childNonce := 1, depositHalted := true, callerStack := [42, 0], creatorNonce := 2,
  destinationWarm := true, deployedNonce := 0, deployedCodeSize := 0,
  refundedStateGas := 183600, topLevelCreatorNonce := 2, topLevelDeployedCodeSize := 0 }

/-! ## The two runs as applications of the S3 lemmas

The pilot's `Runs.lean` applied the resume equation to a result returned by its driver. Here
the same two steps are applications of `resume_failed` (through `Evm.Reaches.resume_failed`) and
the (b) equations (`returnedMachine_failed_call`, `returnedMachine_failed_create`) to a result
named by a driver premise (`Frame.Returns`), at any spawn the run of a top frame reaches.
`room`, and for the Amsterdam creation `settled`, are discharged by the run invariants
(`Jaune.MessageCall.DriverInvariants`), not by these theorems' premises; no concrete state is
unfolded. -/

/-- A top frame is entered with an empty stack. -/
theorem entered_stack {msg : Msg} {isCreate : Bool} {start : Evm}
    (h : entered (Frame.ofTop msg isCreate) = some start) : start.dyna.stack.length ≤ 1024 := by
  unfold entered at h
  split at h
  · rename_i evm he
    cases h
    have hm := RunInvariants.enterWith_run_mach he
    show start.dyna.mach.stack.length ≤ 1024
    rw [hm]
    exact Nat.zero_le _
  · cases h

/-- The call execution's return: a Prague caller resumed after a reverted child keeps its own
world and substate (with the child's RIPEMD-160 touch), pushes 0, receives the output in its
window and its return data, and takes back the child's remaining gas. -/
theorem call_return_survival {msg : Msg} {start evm : Evm}
    (hstart : entered (Frame.ofTop msg false) = some start) (hrun : start.Reaches evm)
    {child : Frame} {p : Pending} {pc : Nat} (hspawn : Evm.step evm = .spawn child p pc)
    {outputIndex outputSize : Nat} (target : p.target = .call outputIndex outputSize)
    (prague : evm.sta.benvStat.rules.stateGas = none)
    {output : Bytes} {gasLeft : Nat} {meter : StateGasMeter} {trail : Trail}
    (childRan : Frame.Returns child (.revert output gasLeft meter trail)) :
    resume evm.sta.benvStat.rules p child.checkpoint (.revert output gasLeft meter trail) =
      .ok (.ok (p.restore
        { machine :=
            { stack := 0 :: child.checkpoint.machine.stack
              memory := child.checkpoint.machine.memory.write outputIndex (output.take outputSize)
              gasLeft := child.checkpoint.machine.gasLeft + gasLeft
              stateGas := child.checkpoint.machine.stateGas
              returnData := output }
          world := child.checkpoint.world
          substate := child.checkpoint.substate.keepTouch trail
          trail := child.checkpoint.trail.absorb trail })) := by
  rw [Evm.Reaches.resume_failed (entered_stack hstart) hrun hspawn childRan rfl,
    returnedMachine_failed_call _ _ _ _ target rfl]
  simp only [prague]
  rfl

/-- The creation execution's return: an Amsterdam caller resumed after a child whose deposit
halted keeps its own world and substate, pushes 0, keeps its memory, takes the child's output
as return data, takes back the child's reservoir and spill, and is refunded a charged new
account's state gas. -/
theorem create_return_survival {msg : Msg} {start evm : Evm}
    (hstart : entered (Frame.ofTop msg false) = some start) (hrun : start.Reaches evm)
    {child : Frame} {p : Pending} {pc : Nat} (hspawn : Evm.step evm = .spawn child p pc)
    {address : Address} (target : p.target = .create address)
    {state : StateGasRules} (amsterdam : evm.sta.benvStat.rules.stateGas = some state)
    {reason : ExceptionalHalt} {meter : StateGasMeter} {trail : Trail}
    (childRan : Frame.Returns child (.halt reason meter trail)) :
    resume evm.sta.benvStat.rules p child.checkpoint (.halt reason meter trail) =
      .ok (.ok (p.restore
        { machine :=
            let m : Machine :=
              { stack := 0 :: child.checkpoint.machine.stack
                memory := child.checkpoint.machine.memory
                gasLeft := child.checkpoint.machine.gasLeft
                stateGas :=
                  { child.checkpoint.machine.stateGas with
                    left := child.checkpoint.machine.stateGas.left + meter.left
                    spilled := child.checkpoint.machine.stateGas.spilled + meter.spilled }
                returnData := [] }
            if p.newAccountCharged then m.creditStateGasRefund state.newAccount else m
          world := child.checkpoint.world
          substate := child.checkpoint.substate
          trail := child.checkpoint.trail.absorb trail })) := by
  rw [Evm.Reaches.resume_failed (entered_stack hstart) hrun hspawn childRan rfl,
    returnedMachine_failed_create _ _ _ _ target rfl]
  simp only [amsterdam]
  rfl

end Examples.ShapePilot
