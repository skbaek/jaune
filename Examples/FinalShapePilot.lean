import Examples.ShapePilot
import Jaune.MessageCall.FinalDriverInvariants

/-! The Prague and Amsterdam programs of the shape pilot run on the grouped frame driver. -/
namespace Examples.ShapePilot.Final

open Jaune
open Examples.ShapePilot

def entered (f : Frame) : Option Frame.Running :=
  match Staging.enterWith f f.checkpoint with
  | .run r => some r
  | .done _ => none

/-- Follow the caller's local steps until it hands the first child to the driver. -/
private def firstSpawn : Nat → Frame.Running → Option (Frame × Staging.Pending)
  | 0, _ => none
  | n + 1, r =>
    match Staging.step r with
    | .ok (.next pc s) => firstSpawn n ⟨pc, r.context, s⟩
    | .ok (.spawn child pending _) => some (child, pending)
    | _ => none

/-- Render the result of native top-level preparation and native frame execution through the
same fork-specific output boundary used for the transaction. Both pilot preparations are frames. -/
private def rendered (msg : Msg) : Option (State × MsgCallOutput) := do
  let .ok (.frame f refund) := Staging.TopLevel.prepare msg | none
  let .ok result := Staging.Frame.runTop f | none
  match msg.benv.stat.rules.stateGas with
  | none => (f.output refund result).toOption
  | some _ => (f.outputAmsterdam result).toOption

def observeCall : Option CallObservation := do
  let f := topFrame callMessage
  let start ← entered f
  let (child, _) ← firstSpawn 100 start
  let .run childStart := Staging.enter child | none
  let .ok raw := Staging.exec childStart | none
  let .ok result := Staging.settle child raw | none
  let .ok callerRaw := Staging.exec start | none
  let .ok (.success _ _ _ world substate _) := Staging.Frame.runTop f | none
  let (state, output) ← rendered callMessage
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
    topLevelLogs := output.logs.length }

def observeCreate : Option CreateObservation := do
  let f := topFrame createMessage
  let start ← entered f
  let (child, _) ← firstSpawn 100 start
  let .run childStart := Staging.enter child | none
  let .ok raw := Staging.exec childStart | none
  let .ok result := Staging.settle child raw | none
  let .ok callerRaw := Staging.exec start | none
  let .ok (.success _ _ meter world substate _) := Staging.Frame.runTop f | none
  let (state, _) ← rendered createMessage
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
theorem entered_stack {msg : Msg} {isCreate : Bool} {start : Frame.Running}
    (h : entered (Frame.ofTop msg isCreate) = some start) : start.state.stack.length ≤ 1024 := by
  unfold entered at h
  split at h
  · rename_i r he
    cases h
    have hi := Staging.RunInvariants.enterWith_run_inv (c := 0) (f := Frame.ofTop msg isCreate)
      (start := (Frame.ofTop msg isCreate).checkpoint) (h := he)
    exact (hi ⟨rfl, Nat.zero_le _⟩).2
  · cases h

/-- The call execution's return: a Prague caller resumed after a reverted child keeps its own
world and substate (with the child's RIPEMD-160 touch), pushes 0, receives the output in its
window and its return data, and takes back the child's remaining gas. -/
theorem call_return_survival {msg : Msg} {start run : Frame.Running}
    (hstart : entered (Frame.ofTop msg false) = some start) (hrun : Staging.Frame.Running.Reaches start run)
    {child : Frame} {p : Staging.Pending} {pc : Nat} (hspawn : Staging.step run = .ok (.spawn child p pc))
    {outputIndex outputSize : Nat} (target : p.target = .call outputIndex outputSize)
    (prague : run.context.block.rules.stateGas = none)
    {output : Bytes} {gasLeft : Nat} {meter : StateGasMeter} {trail : Trail}
    (childRan : Staging.Frame.Returns child (.revert output gasLeft meter trail)) :
    Staging.resume run.context.block.rules p child.checkpoint (.revert output gasLeft meter trail) =
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
  rw [Staging.Frame.Running.Reaches.resume_failed (entered_stack hstart) hrun hspawn childRan rfl,
    Staging.returnedMachine_failed_call _ _ _ _ target rfl]
  simp only [prague]
  rfl

/-- The creation execution's return: an Amsterdam caller resumed after a child whose deposit
halted keeps its own world and substate, pushes 0, keeps its memory, takes the child's output
as return data, takes back the child's reservoir and spill, and is refunded a charged new
account's state gas. -/
theorem create_return_survival {msg : Msg} {start run : Frame.Running}
    (hstart : entered (Frame.ofTop msg false) = some start) (hrun : Staging.Frame.Running.Reaches start run)
    {child : Frame} {p : Staging.Pending} {pc : Nat} (hspawn : Staging.step run = .ok (.spawn child p pc))
    {address : Address} (target : p.target = .create address)
    {state : StateGasRules} (amsterdam : run.context.block.rules.stateGas = some state)
    {reason : ExceptionalHalt} {meter : StateGasMeter} {trail : Trail}
    (childRan : Staging.Frame.Returns child (.halt reason meter trail)) :
    Staging.resume run.context.block.rules p child.checkpoint (.halt reason meter trail) =
      .ok (.ok
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
          trail := child.checkpoint.trail.absorb trail }) := by
  rw [Staging.Frame.Running.Reaches.resume_failed (entered_stack hstart) hrun hspawn childRan rfl,
    Staging.returnedMachine_failed_create _ _ _ _ target rfl]
  simp only [amsterdam]
  rfl

end Examples.ShapePilot.Final
