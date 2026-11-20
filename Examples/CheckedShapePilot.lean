import Jaune.MessageCall.CheckedDriverInvariants
import Jaune.Run.CheckedMessage

/-!
# The shape pilot's two executions, on the landed Checked definitions

The pilot of goal `jaune-shape-and-names-v1` (WP) ran two programs on a prototype that never
landed (`Examples/ShapePilot/` on `wsl/jsn-pilot`). Here they run natively on the Checked
message call: `Checked.enter`, `Checked.exec`, `Checked.settle`, `Checked.Frame.runTop`, and the
top-level run `TopLevel.runNative` with its settlement, from a `TopLevel.Input` built directly
(no `Msg`, no `Frame.ofTop`), with the pilot's expected values (S1 and S3: "the pilot's two
executions restated over the landed definitions").

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
namespace Examples.ShapePilot.Checked

open Jaune
open Jaune.Checked

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

/-- The top-level input of a pilot program: a call of the parent at depth left 8, with the
parent's account (nonce 1, the program as code) added to `extraState`, which is also the
transaction's original state. Nothing is warm and no value moves. -/
def input (fork : Fork) (code : ByteArray) (gas stateGas : Nat)
    (extraState : State := .empty) : TopLevel.Input :=
  let state := extraState.set parentAddress
    { nonce := 1, balance := 0, storage := .empty, code := code }
  let message : Checked.Message := {
    context := {
      caller := parentAddress, recipient := parentAddress, value := 0, calldata := [], code
      depthLeft := 8, isStatic := false
      tx := { origin := 0, gasPrice := 0, blobVersionedHashes := [], originalState := state }
      block := { (default : BlockContext) with fork } }
    kind := .call
    codeAddress := some parentAddress
    target := some parentAddress
    gas
    stateGasGrant := stateGas
    transfersValue := false
    disablePrecompiles := false }
  ⟨message, message.initialCheckpoint ⟨state, .empty, .emptyWithCapacity⟩ .emptyWithCapacity
    .emptyWithCapacity .emptyWithCapacity .emptyWithCapacity, []⟩

def callInput : TopLevel.Input :=
  input .prague callingParent 100000 0 (State.setCode .empty childAddress revertingChild)

def createInput : TopLevel.Input :=
  input .amsterdam creatingParent 13000 amsterdamStateGasRules.newAccount

def newAddress : Address := computeContractAddress parentAddress 1

/-- The top-level frame of an input: its message on the checkpoint it is prepared from. -/
def topFrame (input : TopLevel.Input) : Checked.Frame := ⟨input.message, input.checkpoint⟩

/-- A frame whose checkpoint is the one a top-level message starts on. -/
def IsTop (f : Checked.Frame) : Prop :=
  ∃ world accessedAddresses accessedStorageKeys createdAccounts selfDestructs,
    f.checkpoint = f.message.initialCheckpoint world accessedAddresses accessedStorageKeys
      createdAccounts selfDestructs

theorem topFrame_isTop (fork : Fork) (code : ByteArray) (gas stateGas : Nat) (extraState : State) :
    IsTop (topFrame (input fork code gas stateGas extraState)) :=
  ⟨_, _, _, _, _, rfl⟩

def entered (f : Checked.Frame) : Option Checked.Frame.Running :=
  match Checked.enterWith f f.checkpoint with
  | .run r => some r
  | .done _ => none

/-- Follow the caller's local steps until it hands the first child to the driver. -/
private def firstSpawn : Nat → Checked.Frame.Running → Option (Checked.Frame × Staging.Pending)
  | 0, _ => none
  | n + 1, r =>
    match Checked.step r with
    | .ok (.next pc s) => firstSpawn n ⟨pc, r.context, s⟩
    | .ok (.spawn child pending _) => some (child, pending)
    | _ => none

/-- What the transaction reads of the native top-level run: the world after it and the logs it
keeps (a failed frame keeps none), from the top-level settlement. Both pilot preparations are
frames. -/
private def rendered (input : TopLevel.Input) : Option (State × List Log) := do
  let .ok run := TopLevel.runNative input | none
  let .frame .. := run | none
  let settled := run.settlement input
  pure (settled.state, settled.logs)

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

def observeCall : Option CallObservation := do
  let f := topFrame callInput
  let start ← entered f
  let (child, _) ← firstSpawn 100 start
  let .run childStart := Checked.enter child | none
  let .ok raw := Checked.exec childStart | none
  let .ok result := Checked.settle child raw | none
  let .ok callerRaw := Checked.exec start | none
  let .ok (.success _ _ _ world substate _) := Checked.Frame.runTop f | none
  let (state, logs) ← rendered callInput
  pure {
    isCall := child.message.kind == .call
    codeAddress := child.message.codeAddress.map Address.toNat
    childReverted := match raw with | .reverted .. => true | _ => false
    childOutput := raw.output
    childSlot := (raw.state.storageValue childAddress 0).toNat
    childLogs := raw.state.substate.logs.length
    resultReverted := match result with | .revert .. => true | _ => false
    resultOutput := result.output
    callerStack := callerRaw.state.stack.map U256.toNat
    callerOutputWindow := (callerRaw.state.memory.read 0 1).1
    callerReturnData := callerRaw.state.returnData
    settledSlot := ((world.state.get childAddress).storage.get 0).toNat
    settledLogs := substate.logs.length
    topLevelSlot := ((state.get childAddress).storage.get 0).toNat
    topLevelLogs := logs.length }

def observeCreate : Option CreateObservation := do
  let f := topFrame createInput
  let start ← entered f
  let (child, _) ← firstSpawn 100 start
  let .run childStart := Checked.enter child | none
  let .ok raw := Checked.exec childStart | none
  let .ok result := Checked.settle child raw | none
  let .ok callerRaw := Checked.exec start | none
  let .ok (.success _ _ meter world substate _) := Checked.Frame.runTop f | none
  let (state, _) ← rendered createInput
  pure {
    isCreate := child.message.kind == .create
    codeAddress := child.message.codeAddress.map Address.toNat
    childFinished := match raw with | .finished .. => true | _ => false
    childOutput := raw.output
    childNonce := (raw.state.world.state.get newAddress).nonce.toNat
    depositHalted := match result with | .halt (.outOfGas _) .. => true | _ => false
    callerStack := callerRaw.state.stack.map U256.toNat
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

/-- A top-level frame starts with an empty stack. -/
theorem entered_stack {f : Checked.Frame} (top : IsTop f) {start : Checked.Frame.Running}
    (h : entered f = some start) : start.state.stack.length ≤ 1024 := by
  unfold entered at h
  split at h
  · rename_i r he
    cases h
    obtain ⟨_, _, _, _, _, hc⟩ := top
    have hi := Checked.RunInvariants.enterWith_run_inv (c := 0) (f := f)
      (start := f.checkpoint) (h := he)
    refine (hi ⟨?_, ?_⟩).2
    · rw [hc]; rfl
    · rw [hc]; exact Nat.zero_le _
  · cases h

/-- The call execution's return: a Prague caller resumed after a reverted child keeps its own
world and substate (with the child's RIPEMD-160 touch), pushes 0, receives the output in its
window and its return data, and takes back the child's remaining gas. -/
theorem call_return_survival {f : Checked.Frame} (top : IsTop f) {start run : Checked.Frame.Running}
    (hstart : entered f = some start) (hrun : Checked.Frame.Running.Reaches start run)
    {child : Checked.Frame} {p : Staging.Pending} {pc : Nat} (hspawn : Checked.step run = .ok (.spawn child p pc))
    {outputIndex outputSize : Nat} (target : p.target = .call outputIndex outputSize)
    (prague : run.context.block.rules.stateGas = none)
    {output : Bytes} {gasLeft : Nat} {meter : StateGasMeter} {trail : Trail}
    (childRan : Checked.Frame.Returns child (.revert output gasLeft meter trail)) :
    Checked.resume run.context.block.rules p child.checkpoint (.revert output gasLeft meter trail) =
      .ok (.ok
        { machine :=
            { stack := 0 :: child.checkpoint.machine.stack
              memory := child.checkpoint.machine.memory.write outputIndex (output.take outputSize)
              gasLeft := child.checkpoint.machine.gasLeft + gasLeft
              stateGas := child.checkpoint.machine.stateGas
              returnData := output }
          world := child.checkpoint.world
          substate := child.checkpoint.substate.keepTouch trail
          trail := child.checkpoint.trail.absorb trail }) := by
  rw [Checked.Frame.Running.Reaches.resume_failed (entered_stack top hstart) hrun hspawn childRan rfl,
    Checked.returnedMachine_failed_call _ _ _ _ target rfl]
  simp only [prague]
  rfl

/-- The creation execution's return: an Amsterdam caller resumed after a child whose deposit
halted keeps its own world and substate, pushes 0, keeps its memory, takes the child's output
as return data, takes back the child's reservoir and spill, and is refunded a charged new
account's state gas. -/
theorem create_return_survival {f : Checked.Frame} (top : IsTop f) {start run : Checked.Frame.Running}
    (hstart : entered f = some start) (hrun : Checked.Frame.Running.Reaches start run)
    {child : Checked.Frame} {p : Staging.Pending} {pc : Nat} (hspawn : Checked.step run = .ok (.spawn child p pc))
    {address : Address} (target : p.target = .create address)
    {state : StateGasRules} (amsterdam : run.context.block.rules.stateGas = some state)
    {reason : ExceptionalHalt} {meter : StateGasMeter} {trail : Trail}
    (childRan : Checked.Frame.Returns child (.halt reason meter trail)) :
    Checked.resume run.context.block.rules p child.checkpoint (.halt reason meter trail) =
      .ok (.ok
        { machine :=
            let m : Checked.Machine :=
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
          trail := child.checkpoint.trail.absorb trail }) := by
  rw [Checked.Frame.Running.Reaches.resume_failed (entered_stack top hstart) hrun hspawn childRan rfl,
    Checked.returnedMachine_failed_create _ _ _ _ target rfl]
  simp only [amsterdam]
  rfl

end Examples.ShapePilot.Checked
