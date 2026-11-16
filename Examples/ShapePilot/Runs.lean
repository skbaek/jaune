import Examples.ShapePilot.Driver
import Examples.ShapePilot.Programs

namespace Examples.ShapePilot
open Jaune

namespace Prototype

def firstChild : Nat → Runtime → Option (Frame × Continuation × Nat)
  | 0, _ => none
  | n + 1, runtime => match step runtime with
    | .next runtime => firstChild n runtime
    | .spawn frame continuation pc => some (frame, continuation, pc)
    | .finish _ => none

/-- Observe the pilot child's actual terminal instruction before settlement.
The two child programs have no nested calls; a spawn fails this observation. -/
def rawChild : Nat → Runtime → Option Execution
  | 0, _ => none
  | n + 1, runtime => match step runtime with
    | .next runtime => rawChild n runtime
    | .finish raw => some raw
    | .spawn .. => none

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
  let frame := topFrame msg
  let .run initial := enter frame | none
  let (child, _, _) ← firstChild 100 initial
  let .run childInitial := enter child | none
  let raw ← rawChild 100 childInitial
  let rawState := match raw with | .ok d | .error (_, d) => d
  let .ok childReport := drive 100 child none | none
  let .ok parentReport := drive 100 frame none | none
  let .success _ _ meter world substate _ := parentReport.result | none
  pure {
    childIsCreate := child.message.isCreate
    childCodeAddress := child.message.codeAddress.map Address.toNat
    childReverted := match childReport.result with | .revert .. => true | _ => false
    childDepositHalted := match raw, childReport.result with
      | .ok _, .halt (.outOfGas _) _ _ => child.message.isCreate
      | _, _ => false
    childOutput := childReport.result.output
    rawChildOutput := rawState.output
    rawChildSlot := (rawState.getStorVal childAddress 0).toNat
    rawChildLogs := rawState.logs.length
    callerStack := parentReport.terminalMachine.stack.map U256.toNat
    callerOutputWindow := (parentReport.terminalMachine.memory.read 0 1).1
    callerReturnData := parentReport.terminalMachine.returnData
    childSlot := ((world.state.get childAddress).storage.get 0).toNat
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

/-- Apply the resume equation to a result returned by the driver. The actual
execution remains a premise: no concrete state is unfolded in the kernel. -/
theorem call_return_survival (fuel : Nat) (child : Frame) (continuation : Continuation)
    (terminalMachine : Machine) (output : Bytes) (gasLeft : Nat) (meter : StateGasMeter)
    (trail : Trail) (childRan : drive fuel child none =
      .ok ⟨.revert output gasLeft meter trail, terminalMachine⟩)
    (room : child.checkpoint.machine.stack.length < 1024) :
    (drive fuel child none).map (fun report =>
      resume continuation child.checkpoint report.result) = .ok (.ok {
        machine := returnedMachine continuation child.checkpoint.machine
          (.revert output gasLeft meter trail)
        world := child.checkpoint.world
        substate := child.checkpoint.substate.keepTouch trail
        trail := trail }) := by
  rw [childRan]
  exact congrArg Except.ok
    (resume_revert continuation child.checkpoint output gasLeft meter trail room)

/-- A deposit failure uses the same equation, without an account-rollback
premise. The caller checkpoint already includes its nonce and warm address. -/
theorem create_return_survival (fuel : Nat) (child : Frame) (continuation : Continuation)
    (terminalMachine : Machine) (reason : ExceptionalHalt) (meter : StateGasMeter)
    (trail : Trail) (childRan : drive fuel child none =
      .ok ⟨.halt reason meter trail, terminalMachine⟩)
    (room : child.checkpoint.machine.stack.length < 1024) :
    (drive fuel child none).map (fun report =>
      resume continuation child.checkpoint report.result) = .ok (.ok {
        machine := returnedMachine continuation child.checkpoint.machine
          (.halt reason meter trail)
        world := child.checkpoint.world
        substate := child.checkpoint.substate.keepTouch trail
        trail := trail }) := by
  rw [childRan]
  exact congrArg Except.ok
    (resume_halt continuation child.checkpoint reason meter trail room)

end Prototype
end Examples.ShapePilot
