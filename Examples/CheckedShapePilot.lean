import Examples.ShapePilot
import Jaune.MessageCall.CheckedDriverInvariants
import Jaune.Run.Message

/-! The Prague and Amsterdam programs of the shape pilot run on the checked frame driver. -/
namespace Examples.ShapePilot.Checked

open Jaune
open Examples.ShapePilot

/-- A frame built by the shared top-level constructors (`Jaune.Frame.ofTop`, the run layer's
`TopLevel.prepare`) on the checked machine: the same message and checkpoint, with the
checkpoint's memory carried over when its backing array lies within its logical size, and
refused otherwise. -/
def checkedFrame (f : Jaune.Frame) : Option Checked.Frame :=
  let m := f.checkpoint.machine
  if h : m.memory.data.size ≤ m.memory.size then
    some ⟨f.message,
      { machine :=
          { stack := m.stack, memory := ⟨m.memory.data, m.memory.size, h⟩, gasLeft := m.gasLeft
            stateGas := m.stateGas, returnData := m.returnData }
        world := f.checkpoint.world
        substate := f.checkpoint.substate
        trail := f.checkpoint.trail }⟩
  else none

/-- A frame whose checkpoint memory is empty converts. -/
theorem checkedFrame_isSome_of_empty {f : Jaune.Frame} (h : f.checkpoint.machine.memory = Mem.empty) :
    (checkedFrame f).isSome := by
  unfold checkedFrame
  dsimp only
  split
  · rfl
  · rename_i hn; exact absurd (by rw [h]; exact Nat.le_refl 0) hn

/-- The top-level frame always converts: its checkpoint starts with empty memory. -/
theorem checkedFrame_ofTop_isSome (msg : Msg) (isCreate : Bool) :
    (checkedFrame (Jaune.Frame.ofTop msg isCreate)).isSome :=
  checkedFrame_isSome_of_empty rfl

theorem checkedFrame_machine {f : Jaune.Frame} {g : Checked.Frame} (h : checkedFrame f = some g) :
    g.checkpoint.machine.stack = f.checkpoint.machine.stack ∧
      g.checkpoint.machine.stateGas = f.checkpoint.machine.stateGas := by
  unfold checkedFrame at h
  dsimp only at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- A top-level frame on the checked machine (`Jaune.Frame.ofTop` with its empty memory). -/
def ofTop (msg : Msg) (isCreate : Bool) : Checked.Frame :=
  (checkedFrame (Jaune.Frame.ofTop msg isCreate)).get (checkedFrame_ofTop_isSome msg isCreate)

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

/-- What the transaction reads of the native top-level frame: the world after it and the logs it
keeps (a failed frame keeps none). Both pilot preparations are frames. -/
private def rendered (msg : Msg) : Option (State × List Log) := do
  let .ok (.frame f _) := TopLevel.prepare msg | none
  let cf ← checkedFrame f
  let .ok result := Checked.Frame.runTop cf | none
  let logs := match result with
    | .success _ _ _ _ substate _ => substate.logs
    | _ => []
  pure ((f.worldAfter result).state, logs)

def observeCall : Option CallObservation := do
  let f := ofTop callMessage false
  let start ← entered f
  let (child, _) ← firstSpawn 100 start
  let .run childStart := Checked.enter child | none
  let .ok raw := Checked.exec childStart | none
  let .ok result := Checked.settle child raw | none
  let .ok callerRaw := Checked.exec start | none
  let .ok (.success _ _ _ world substate _) := Checked.Frame.runTop f | none
  let (state, logs) ← rendered callMessage
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
  let f := ofTop createMessage false
  let start ← entered f
  let (child, _) ← firstSpawn 100 start
  let .run childStart := Checked.enter child | none
  let .ok raw := Checked.exec childStart | none
  let .ok result := Checked.settle child raw | none
  let .ok callerRaw := Checked.exec start | none
  let .ok (.success _ _ meter world substate _) := Checked.Frame.runTop f | none
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
theorem entered_stack {msg : Msg} {isCreate : Bool} {start : Checked.Frame.Running}
    (h : entered (ofTop msg isCreate) = some start) : start.state.stack.length ≤ 1024 := by
  unfold entered at h
  split at h
  · rename_i r he
    cases h
    have hi := Checked.RunInvariants.enterWith_run_inv (c := 0) (f := ofTop msg isCreate)
      (start := (ofTop msg isCreate).checkpoint) (h := he)
    have hm : (ofTop msg isCreate).checkpoint.machine.stack =
          (Jaune.Frame.ofTop msg isCreate).checkpoint.machine.stack ∧
        (ofTop msg isCreate).checkpoint.machine.stateGas =
          (Jaune.Frame.ofTop msg isCreate).checkpoint.machine.stateGas :=
      checkedFrame_machine (Option.some_get (checkedFrame_ofTop_isSome msg isCreate)).symm
    refine (hi ⟨?_, ?_⟩).2
    · rw [hm.2]; rfl
    · rw [hm.1]; exact Nat.zero_le _
  · cases h

/-- The call execution's return: a Prague caller resumed after a reverted child keeps its own
world and substate (with the child's RIPEMD-160 touch), pushes 0, receives the output in its
window and its return data, and takes back the child's remaining gas. -/
theorem call_return_survival {msg : Msg} {start run : Checked.Frame.Running}
    (hstart : entered (ofTop msg false) = some start) (hrun : Checked.Frame.Running.Reaches start run)
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
  rw [Checked.Frame.Running.Reaches.resume_failed (entered_stack hstart) hrun hspawn childRan rfl,
    Checked.returnedMachine_failed_call _ _ _ _ target rfl]
  simp only [prague]
  rfl

/-- The creation execution's return: an Amsterdam caller resumed after a child whose deposit
halted keeps its own world and substate, pushes 0, keeps its memory, takes the child's output
as return data, takes back the child's reservoir and spill, and is refunded a charged new
account's state gas. -/
theorem create_return_survival {msg : Msg} {start run : Checked.Frame.Running}
    (hstart : entered (ofTop msg false) = some start) (hrun : Checked.Frame.Running.Reaches start run)
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
  rw [Checked.Frame.Running.Reaches.resume_failed (entered_stack hstart) hrun hspawn childRan rfl,
    Checked.returnedMachine_failed_create _ _ _ _ target rfl]
  simp only [amsterdam]
  rfl

end Examples.ShapePilot.Checked
