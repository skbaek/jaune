import Jaune.Sufficiency

/-! Concrete WP executions, kept outside the specification import closure.
These run the current interpreter; the prototype will consume the same inputs.
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

/-- Inspect a finite prefix up to the first spawned frame. No child is skipped. -/
def firstSpawn : Nat → Evm → Option (Frame × Resume × Nat)
  | 0, _ => none
  | n + 1, evm =>
    match evm.step with
    | .cont pc devm => firstSpawn n ⟨pc, evm.sta, devm⟩
    | .spawn frame resume pc => some (frame, resume, pc)
    | .halt _ => none

structure CallObservation where
  isCall : Bool
  codeAddress : Option Nat
  childOutput : Bytes
  childSlot : Nat
  childLogs : Nat
  callerStack : List Nat
  callerOutputWindow : Bytes
  callerReturnData : Bytes
  settledSlot : Nat
  settledLogs : Nat
  deriving Repr, BEq

def observeCall : Option CallObservation := do
  let (frame, _, _) ← firstSpawn 100 (initEvm callMessage)
  let .run childStart := frame.enter | none
  let .error (.revert, child) := exec childStart | none
  let .ok caller := processMessage callMessage | none
  pure {
    isCall := !frame.isCreate
    codeAddress := frame.inner.codeAddress.map Address.toNat
    childOutput := child.output
    childSlot := (child.getStorVal childAddress 0).toNat
    childLogs := child.logs.length
    callerStack := caller.stack.map U256.toNat
    callerOutputWindow := (caller.memory.read 0 1).1
    callerReturnData := caller.returnData
    settledSlot := (caller.getStorVal childAddress 0).toNat
    settledLogs := caller.logs.length }

structure CreateObservation where
  isCreate : Bool
  codeAddress : Option Nat
  output : Bytes
  depositOutOfGas : Bool
  initcodeGasLeft : Nat
  initcodeStateGasLeft : Nat
  childNonce : Nat
  callerStack : List Nat
  creatorNonce : Nat
  destinationWarm : Bool
  deployedNonce : Nat
  deployedCodeSize : Nat
  refundedStateGas : Nat
  deriving Repr, BEq

def observeCreate : Option CreateObservation := do
  let (frame, _, _) ← firstSpawn 100 (initEvm createMessage)
  let .run childStart := frame.enter | none
  let .ok child := exec childStart | none
  let .ok caller := processMessage createMessage | none
  pure {
    isCreate := frame.isCreate
    codeAddress := frame.inner.codeAddress.map Address.toNat
    output := child.output
    depositOutOfGas := match processCreateMessage.chargeCodeGas amsterdamRules child with
      | .error (.halt (.outOfGas _), _) => true
      | _ => false
    initcodeGasLeft := child.gasLeft
    initcodeStateGasLeft := child.stateGasLeft
    childNonce := (child.state.get newAddress).nonce.toNat
    callerStack := caller.stack.map U256.toNat
    creatorNonce := (caller.state.get parentAddress).nonce.toNat
    destinationWarm := caller.accessedAddresses.contains newAddress
    deployedNonce := (caller.state.get newAddress).nonce.toNat
    deployedCodeSize := (caller.state.get newAddress).code.size
    refundedStateGas := caller.stateGasLeft }

-- These observations include the raw child, so a preflight refusal cannot
-- masquerade as either of the required executions.
#guard observeCall == some {
  isCall := true, codeAddress := some 32, childOutput := [170],
  childSlot := 7, childLogs := 1, callerStack := [42, 0],
  callerOutputWindow := [170], callerReturnData := [170],
  settledSlot := 0, settledLogs := 0 }

#guard observeCreate == some {
  isCreate := true, codeAddress := none, output := [0], depositOutOfGas := true,
  initcodeGasLeft := 938, initcodeStateGasLeft := 0, childNonce := 1,
  callerStack := [42, 0], creatorNonce := 2, destinationWarm := true,
  deployedNonce := 0, deployedCodeSize := 0, refundedStateGas := 183600 }

end Examples.ShapePilot
