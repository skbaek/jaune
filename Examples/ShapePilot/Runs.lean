import Examples.ShapePilot.Driver
import Examples.ShapePilot.Programs

namespace Examples.ShapePilot
open Jaune

namespace Prototype

def firstChild : Nat → Runtime → Option (Frame × Continuation × Nat)
  | 0, _ => none
  | n + 1, runtime => match step runtime with
    | .ok (.next runtime) => firstChild n runtime
    | .ok (.spawn frame continuation pc) => some (frame, continuation, pc)
    | _ => none

/-- Observe the pilot child's actual terminal instruction before settlement.
The two child programs have no nested calls; a spawn fails this observation. -/
def rawChild : Nat → Runtime → Option Execution
  | 0, _ => none
  | n + 1, runtime => match step runtime with
    | .ok (.next runtime) => rawChild n runtime
    | .ok (.finish raw) => some raw
    | _ => none

/-- The first child of a top-level message: its frame, the continuation the
calling opcode left, and the result the driver returned for it. -/
def firstSpawnResult (msg : Msg) : Option (Frame × Continuation × Frame.Result) := do
  let frame ← topFrame msg
  let .run initial := enter frame | none
  let (child, continuation, _) ← firstChild 100 initial
  let .ok report := drive 100 child none | none
  pure (child, continuation, report.result)

structure Observation where
  childIsCreate : Bool
  childCodeAddress : Option Nat
  childReverted : Bool
  childDepositHalted : Bool
  childOutput : Bytes
  rawChildOutput : Bytes
  rawChildSlot : Nat
  rawChildLogs : Nat
  callerStack : List Nat
  callerOutputWindow : Bytes
  callerReturnData : Bytes
  childSlot : Nat
  logs : Nat
  creatorNonce : Nat
  destinationWarm : Bool
  deployedNonce : Nat
  deployedCodeSize : Nat
  stateGas : Nat
  deriving Repr, BEq

def observe (msg : Msg) : Option Observation := do
  let frame ← topFrame msg
  let .run initial := enter frame | none
  let (child, _, _) ← firstChild 100 initial
  let .run childInitial := enter child | none
  let raw ← rawChild 100 childInitial
  let rawState := match raw with | .ok d | .error (_, d) => d
  let .ok childReport := drive 100 child none | none
  let .ok parentReport := drive 100 frame none | none
  let .success _ _ meter world substate _ := parentReport.result | none
  let terminal ← parentReport.terminalMachine
  pure {
    childIsCreate := child.message.isCreate
    childCodeAddress := child.message.codeAccount.map Adr.toNat
    childReverted := match childReport.result with | .revert .. => true | _ => false
    childDepositHalted := match raw, childReport.result with
      | .ok _, .halt (.outOfGas _) _ _ => child.message.isCreate
      | _, _ => false
    childOutput := childReport.result.output
    rawChildOutput := rawState.output
    rawChildSlot := (rawState.getStorVal childAddress 0).toNat
    rawChildLogs := rawState.logs.length
    callerStack := terminal.stack.map B256.toNat
    callerOutputWindow := (terminal.memory.read 0 1).1
    callerReturnData := terminal.returnData
    childSlot := ((world.state.get childAddress).stor.get 0).toNat
    logs := substate.logs.length
    creatorNonce := (world.state.get parentAddress).nonce.toNat
    destinationWarm := substate.accessedAddresses.contains newAddress
    deployedNonce := (world.state.get newAddress).nonce.toNat
    deployedCodeSize := (world.state.get newAddress).code.size
    stateGas := meter.left }

#guard observe callMessage == some {
  childIsCreate := false, childCodeAddress := some 32,
  childReverted := true, childDepositHalted := false,
  childOutput := [170], rawChildOutput := [170], rawChildSlot := 7, rawChildLogs := 1,
  callerStack := [42, 0], callerOutputWindow := [170], callerReturnData := [170],
  childSlot := 0, logs := 0, creatorNonce := 1, destinationWarm := false,
  deployedNonce := 0, deployedCodeSize := 0, stateGas := 0 }

#guard observe createMessage == some {
  childIsCreate := true, childCodeAddress := none,
  childReverted := false, childDepositHalted := true,
  childOutput := [], rawChildOutput := [0], rawChildSlot := 0, rawChildLogs := 0,
  callerStack := [42, 0], callerOutputWindow := [96], callerReturnData := [],
  childSlot := 0, logs := 0, creatorNonce := 2, destinationWarm := true,
  deployedNonce := 0, deployedCodeSize := 0, stateGas := 183600 }

/-! ### S3 over the worked example

The two child results and continuations are those the driver actually
produced; the guards below check every premise the theorems take. Concrete
memory and storage images are not evaluated in the kernel. -/

/-- The call: a reverting child with output `0xAA` under one-dimensional
rules. Its continuation writes one byte at offset 0. -/
def CallShape (c : Continuation) (r : Frame.Result) : Bool :=
  (match c.target with | .call 0 1 => true | _ => false) && !c.stateGas &&
  c.machine.stack.length < 1024 &&
  (match r with | .revert [0xAA] _ _ _ => true | _ => false)

/-- The create: a child whose deposit ran out of gas under Amsterdam, with a
settled zero meter, and a caller that paid the new-account charge from a
reservoir its child grant then drained. -/
def CreateShape (c : Continuation) (r : Frame.Result) : Bool :=
  (match c.target with | .create a => a == newAddress | _ => false) && c.stateGas &&
  c.newAccountRefund == amsterdamStateGasRules.newAccount &&
  c.machine.stateGas == ⟨0, amsterdamStateGasRules.newAccount, 0, 0⟩ &&
  c.machine.stack.length < 1024 &&
  (match r with | .halt (.outOfGas _) ⟨0, 0, 0, 0⟩ _ => true | _ => false)

#guard (firstSpawnResult callMessage).any fun (_, c, r) => CallShape c r
#guard (firstSpawnResult createMessage).any fun (_, c, r) => CreateShape c r
#guard amsterdamStateGasRules.newAccount == 183600

/-- S3(a)-(c) for the call: the caller keeps its saved world and substate
(with only a kept RIPEMD-160 touch), absorbs the child's trail, pushes 0,
receives `0xAA` in its output window and as return data, and gets the child's
execution gas back. -/
theorem call_example (cp : Checkpoint) (c : Continuation)
    (gasLeft : Nat) (meter : StateGasMeter) (trail : Trail)
    (target : c.target = .call 0 1) (oneDim : c.stateGas = false)
    (room : c.machine.stack.length < 1024) :
    resume c cp (.revert [0xAA] gasLeft meter trail) = .ok (.ok {
      machine := {
        stack := 0 :: c.machine.stack
        memory := c.machine.memory.write 0 [0xAA]
        gasLeft := c.machine.gasLeft + gasLeft
        stateGas := c.machine.stateGas
        returnData := [0xAA] }
      world := cp.world
      substate := cp.substate.keepTouch trail
      trail := cp.trail.absorb trail }) := by
  rw [resume_revert c cp _ _ _ _ (by simp [oneDim]) room]
  have stack := returnedMachine_stack_failed c (.revert [0xAA] gasLeft meter trail) rfl
  have memory := returnedMachine_memory_call c (.revert [0xAA] gasLeft meter trail) 0 1 target
  have data := returnedMachine_returnData_failed c (.revert [0xAA] gasLeft meter trail) rfl
  have meters := returnedMachine_meters_oneDim c (.revert [0xAA] gasLeft meter trail) oneDim
  simp only [oneDim, Bool.false_eq_true, ↓reduceIte]
  simp only [Frame.Result.output, Frame.Result.gasLeft, List.take] at memory data meters
  have hm : returnedMachine c (.revert [0xAA] gasLeft meter trail) =
      { stack := 0 :: c.machine.stack, memory := c.machine.memory.write 0 [0xAA]
        gasLeft := c.machine.gasLeft + gasLeft, stateGas := c.machine.stateGas
        returnData := [0xAA] } :=
    Machine.ext stack memory meters.1 meters.2 data
  rw [hm]

/-- S3(a)-(c) for the create: the caller keeps its saved world and substate,
which already hold its nonce increment and the warmed destination; it pushes
0, its memory is unchanged, its return data is empty, and the 183600 the
caller paid for the new account comes back to its reservoir. -/
theorem create_example (cp : Checkpoint) (c : Continuation)
    (reason : ExceptionalHalt) (trail : Trail)
    (target : c.target = .create newAddress) (amsterdam : c.stateGas = true)
    (refund : c.newAccountRefund = 183600)
    (parentMeter : c.machine.stateGas = ⟨0, 183600, 0, 0⟩)
    (room : c.machine.stack.length < 1024) :
    resume c cp (.halt reason ⟨0, 0, 0, 0⟩ trail) = .ok (.ok {
      machine := {
        stack := 0 :: c.machine.stack
        memory := c.machine.memory
        gasLeft := c.machine.gasLeft
        stateGas := ⟨183600, 183600, 0, 0⟩
        returnData := [] }
      world := cp.world
      substate := cp.substate
      trail := cp.trail.absorb trail }) := by
  rw [resume_halt c cp _ _ _ (fun _ => rfl) room]
  have stack := returnedMachine_stack_failed c (.halt reason ⟨0, 0, 0, 0⟩ trail) rfl
  have memory := returnedMachine_memory_create c (.halt reason ⟨0, 0, 0, 0⟩ trail) _ target
  have data := returnedMachine_returnData_failed c (.halt reason ⟨0, 0, 0, 0⟩ trail) rfl
  have meters := returnedMachine_meters_failed_amsterdam c
    (.halt reason ⟨0, 0, 0, 0⟩ trail) amsterdam rfl
  simp only [amsterdam, ↓reduceIte]
  simp only [Frame.Result.output, Frame.Result.gasLeft, Frame.Result.stateGas,
    Mach.creditStateGasRefund, parentMeter, refund] at data meters
  simp only [Nat.add_zero, Nat.zero_add, Nat.min_zero, Nat.sub_zero] at meters
  have hm : returnedMachine c (.halt reason ⟨0, 0, 0, 0⟩ trail) =
      { stack := 0 :: c.machine.stack, memory := c.machine.memory
        gasLeft := c.machine.gasLeft, stateGas := ⟨183600, 183600, 0, 0⟩
        returnData := [] } :=
    Machine.ext stack memory meters.1 meters.2 data
  rw [hm]

/-- Apply the resume equation to a result returned by the driver. The actual
execution remains a premise: no concrete state is unfolded in the kernel. -/
theorem call_return_survival (fuel : Nat) (child : Frame) (c : Continuation)
    (terminal : Option Machine) (gasLeft : Nat) (meter : StateGasMeter) (trail : Trail)
    (childRan : drive fuel child none = .ok ⟨.revert [0xAA] gasLeft meter trail, terminal⟩)
    (target : c.target = .call 0 1) (oneDim : c.stateGas = false)
    (room : c.machine.stack.length < 1024) :
    (drive fuel child none).map (fun report => resume c child.checkpoint report.result) =
      .ok (.ok (.ok {
        machine := {
          stack := 0 :: c.machine.stack
          memory := c.machine.memory.write 0 [0xAA]
          gasLeft := c.machine.gasLeft + gasLeft
          stateGas := c.machine.stateGas
          returnData := [0xAA] }
        world := child.checkpoint.world
        substate := child.checkpoint.substate.keepTouch trail
        trail := child.checkpoint.trail.absorb trail })) := by
  rw [childRan]
  exact congrArg Except.ok (call_example child.checkpoint c gasLeft meter trail target oneDim room)

/-- A deposit failure uses the same equation, without an account-rollback
premise. The caller checkpoint already includes its nonce and warm address. -/
theorem create_return_survival (fuel : Nat) (child : Frame) (c : Continuation)
    (terminal : Option Machine) (reason : ExceptionalHalt) (trail : Trail)
    (childRan : drive fuel child none = .ok ⟨.halt reason ⟨0, 0, 0, 0⟩ trail, terminal⟩)
    (target : c.target = .create newAddress) (amsterdam : c.stateGas = true)
    (refund : c.newAccountRefund = 183600)
    (parentMeter : c.machine.stateGas = ⟨0, 183600, 0, 0⟩)
    (room : c.machine.stack.length < 1024) :
    (drive fuel child none).map (fun report => resume c child.checkpoint report.result) =
      .ok (.ok (.ok {
        machine := {
          stack := 0 :: c.machine.stack
          memory := c.machine.memory
          gasLeft := c.machine.gasLeft
          stateGas := ⟨183600, 183600, 0, 0⟩
          returnData := [] }
        world := child.checkpoint.world
        substate := child.checkpoint.substate
        trail := child.checkpoint.trail.absorb trail })) := by
  rw [childRan]
  exact congrArg Except.ok
    (create_example child.checkpoint c reason trail target amsterdam refund parentMeter room)

/-! ### A top-level creation is a creation

`topFrame` derives the kind from the legacy message, so a top-level creation
runs the creation set-up, pays the code deposit and installs its code. -/

def topCreateAddress : Adr := 0x3000

def topCreateMessage : Msg :=
  { message .prague initcode 100000 0 with
    target := none, currentTarget := topCreateAddress, codeAddress := none }

structure TopCreate where
  isCreate : Bool
  succeeded : Bool
  gasLeft : Nat
  code : List UInt8
  nonce : Nat
  deriving Repr, BEq

def legacyTopCreate : Option TopCreate := do
  let .ok d := processCreateMessage topCreateMessage | none
  pure ⟨true, d.error.isNone, d.gasLeft, (d.state.get topCreateAddress).code.data.toList,
    (d.state.get topCreateAddress).nonce.toNat⟩

def prototypeTopCreate : Option TopCreate := do
  let frame ← topFrame topCreateMessage
  let .ok report := drive 100 frame none | none
  let .success _ gasLeft _ world _ _ := report.result | none
  pure ⟨frame.message.isCreate, true, gasLeft,
    (world.state.get topCreateAddress).code.data.toList,
    (world.state.get topCreateAddress).nonce.toNat⟩

#guard legacyTopCreate.isSome && legacyTopCreate == prototypeTopCreate
#guard legacyTopCreate.any fun r => r.code == [0] && r.nonce == 1

/-! ### RIPEMD-160's surviving touch, evaluated where production evaluates it

Under a rule set with the touched-account sweep, 0x03 exists and is empty. A
failed creation whose target is 0x03 does not keep a touch: the creation
set-up has already given it a nonce. A failed call to 0x03 does. -/

def ripemdState : State :=
  State.setPresent .empty ripemd160Address { nonce := 0, bal := 0, stor := .empty, code := .empty }

def failedRipemdCreate : Msg :=
  { message .berlin ⟨#[0x60, 0x00, 0x60, 0x00, 0xFD]⟩ 100000 0 ripemdState with
    target := none, currentTarget := ripemd160Address, codeAddress := none }

def failedRipemdCall : Msg :=
  { message .berlin .empty 10 0 ripemdState with
    data := List.replicate 64 0,
    target := some ripemd160Address, currentTarget := ripemd160Address,
    codeAddress := some ripemd160Address }

def legacyKeepsTouch (run : Msg → Except (EvmError × State × AdrSet × Tra) Devm)
    (msg : Msg) : Option Bool := do
  let .ok d := run msg | none
  guard d.error.isSome
  pure (d.meta.touchedAccounts.contains ripemd160Address)

def prototypeKeepsTouch (msg : Msg) : Option Bool := do
  let frame ← topFrame msg
  let .ok report := drive 100 frame none | none
  guard report.result.failed
  pure report.result.trail.ripemd160Touched

#guard legacyKeepsTouch processCreateMessage failedRipemdCreate == some false
#guard prototypeKeepsTouch failedRipemdCreate == some false
#guard legacyKeepsTouch processMessage failedRipemdCall == some true
#guard prototypeKeepsTouch failedRipemdCall == some true

end Prototype
end Examples.ShapePilot
