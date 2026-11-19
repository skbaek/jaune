import Jaune.MessageCall.CheckedControl
import Jaune.MessageCall.CheckedMessageOps

/-! Entry, settlement and resumption of checked frames. -/
namespace Jaune.Checked

open Jaune

def Frame.enteredWorld (f : Frame) : World :=
  match f.message.kind with
  | .call => f.checkpoint.world
  | .create => f.checkpoint.world.createSetUp f.message.context.recipient

def Frame.startState (f : Frame) : Frame.State :=
  let m := f.message
  let cp := f.checkpoint
  let rules := m.context.block.rules
  { machine :=
      { stack := [], memory := .empty, gasLeft := m.gas
        stateGas :=
          { left := m.stateGasGrant, baseline := m.stateGasGrant, spilled := 0
            committedSpill := 0 }
        returnData := [] }
    world := cp.world
    substate :=
      { logs := m.transferLogs
        refund := 0
        selfDestructs :=
          if rules.settlement.selfdestructRefund = 0 then .emptyWithCapacity
          else cp.substate.selfDestructs
        accessedAddresses := cp.substate.accessedAddresses
        accessedStorageKeys := cp.substate.accessedStorageKeys
        touchedAccounts := .emptyWithCapacity }
    trail := { createdAccounts := cp.trail.createdAccounts } }


def Frame.enteredCreatedAccounts (f : Frame) : AdrSet :=
  match f.message.kind with
  | .call => f.checkpoint.trail.createdAccounts
  | .create => f.checkpoint.trail.createdAccounts.insert f.message.context.recipient


def finishTarget (target : ReturnTarget) (r : Frame.Result) (m : Machine) : Machine :=
  let m := { m with stack := target.status r :: m.stack }
  match target with
  | .call outputIndex outputSize =>
    { m with memory := m.memory.write outputIndex (r.output.take outputSize) }
  | .create _ => m


/-! ### `enter` -/

/-- What entering a frame gives: a running frame, or a result already (a precompile, or a failed
value transfer). -/
inductive Frame.Entry : Type
  /-- Run this frame. -/
  | run (r : Frame.Running)
  /-- The frame finished at entry, or faulted. -/
  | done (result : Except Fault Frame.Result)

/-- The running frame `enterWith` builds from a start state and the world after the value
transfer: the world and the created accounts come from the checkpoint, the rest from the start
state; the RIPEMD-160 flag is down. -/
def Frame.entered (f : Frame) (start : Frame.State) (world : World) : Frame.Running :=
  ⟨0, f.message.context,
    { start with
      world
      trail := { start.trail with
        createdAccounts := f.enteredCreatedAccounts, touchedRIPEMD160 := false } }⟩

/-! ### `settle` -/

/-- Charge a creation's code deposit, failing only by a halt. Without state gas the code is
charged per byte before its size is checked, so a size failure carries the charged state; with
state gas the prefix and the size are checked before either charge. -/
def chargeDeposit (rules : ForkRules) (code : Bytes) (s : Frame.State) :
    Except (ExceptionalHalt × Frame.State) Frame.State :=
  match rules.stateGas with
  | none =>
    let chargeThenSize : Except (ExceptionalHalt × Frame.State) Frame.State := do
      let s ← s.chargeGas (code.length * Gas.codeDeposit)
      if rules.code.maxCodeSize < code.length then .error (.outOfGas .none, s) else .ok s
    match code with
    | 0xEF :: _ =>
      if rules.creation.rejectEf then .error (.invalidContractPrefix .none, s)
      else chargeThenSize
    | _ => chargeThenSize
  | some state =>
    match code with
    | 0xEF :: _ => .error (.invalidContractPrefix .none, s)
    | _ =>
      if rules.code.maxCodeSize < code.length then .error (.outOfGas .none, s)
      else do
        let s ← s.chargeGas (Gas.keccak256Word * ceilDiv code.length 32)
        s.chargeStateGas (code.length * state.costPerStateByte)

/-- A creation's code deposit: the charge, then the code set at the new address (which also
forgets an empty account's storage writes). -/
def depositCode (rules : ForkRules) (recipient : Address) (code : Bytes) (s : Frame.State) :
    Except (ExceptionalHalt × Frame.State) Frame.State :=
  (chargeDeposit rules code s).map fun s => s.setCode recipient ⟨⟨code⟩⟩

/-- A successful frame's result, from its output and final state. -/
def Frame.Result.ofSuccess (output : Bytes) (s : Frame.State) : Frame.Result :=
  .success output s.machine.gasLeft s.machine.stateGas s.world s.substate s.trail

/-- Settle how a frame stopped.

* A revert keeps its output and gas; under state gas its meter is refilled to the baseline.
* A halt forfeits its gas; under state gas its meter is refilled first.
* A failed frame's trail records whether RIPEMD-160's address was touched: by a child, or by the
  frame itself when it targets that address and it exists and is empty in the world the frame
  was entered on.
* A finished frame records its own touch, then a creation deposits its code; a failed deposit
  is a halt whose trail records only the touches already made. -/
def settle (f : Frame) (exit : Frame.Exit) : Except Fault Frame.Result :=
  let m := f.message
  let rules := m.context.block.rules
  let failedTrail (s : Frame.State) : Trail :=
    let selfTouch := rules.settlement.touchedSweep && (m.context.recipient == ripemd160Address) &&
      decide (accountExistsAndIsEmpty f.enteredWorld.state m.context.recipient)
    { s.trail with
      touchedRIPEMD160 := selfTouch || s.substate.touchedAccounts.contains ripemd160Address }
  let depositTrail (s : Frame.State) : Trail :=
    { s.trail with touchedRIPEMD160 := s.substate.touchedAccounts.contains ripemd160Address }
  let reverted (s : Frame.State) : Machine :=
    match rules.stateGas with
    | none => s.machine
    | some _ => s.machine.restoreStateGas
  let halted (s : Frame.State) : Machine :=
    match rules.stateGas with
    | none => s.machine.forfeitRemainingGas
    | some _ => s.machine.restoreStateGas.forfeitRemainingGas
  match exit with
  | .reverted output s =>
    .ok (.revert output (reverted s).gasLeft (reverted s).stateGas (failedTrail s))
  | .halted reason s => .ok (.halt reason (halted s).stateGas (failedTrail s))
  | .finished output s =>
    let s := s.recordTouch rules true m.context.recipient
    match m.kind with
    | .call => .ok (Frame.Result.ofSuccess output s)
    | .create =>
      match depositCode rules m.context.recipient output s with
      | .ok s => .ok (Frame.Result.ofSuccess output s)
      | .error (reason, s) => .ok (.halt reason (halted s).stateGas (depositTrail s))

/-! ### `enter`, continued -/

/-- Enter a frame from a given start state. The value moves on the world the frame is entered on
(the checkpoint's, set up for a creation); a creation's new address joins the created accounts. A
precompile target is run and settled at once, its fault propagating; any other target hands back
its running frame. -/
def enterWith (f : Frame) (start : Frame.State) : Frame.Entry :=
  let m := f.message
  match m.transfer f.enteredWorld with
  | .error fault => .done (.error fault)
  | .ok world =>
    let running := Frame.entered f start world
    match m.codeAddress with
    | some address =>
      if !m.disablePrecompiles && m.context.block.rules.isPrecompile address then
        .done (runPrecompile running address >>= settle f)
      else .run running
    | none => .run running

/-- Enter a spawned child frame, from `Frame.startState`. -/
def enter (f : Frame) : Frame.Entry := enterWith f f.startState

/-! ### `resume` -/

/-- The caller's machine after its child returns. Execution gas comes back whatever the child's
fate; under state gas so do the reservoir and the spill, after which a failed child refunds a
charged new account and a successful one repays spill. The return data is the child's output,
except after a successful creation, which returns none. -/
def absorbMeters (rules : ForkRules) (p : Staging.Pending) (saved : Machine) (r : Frame.Result) :
    Machine :=
  let returnData := match p.target, r.failed with
    | .create _, false => []
    | _, _ => r.output
  match rules.stateGas with
  | none => { saved with gasLeft := saved.gasLeft + r.gasLeft, returnData := returnData }
  | some state =>
    let m : Machine :=
      { saved with
        gasLeft := saved.gasLeft + r.gasLeft
        stateGas := { saved.stateGas with
          left := saved.stateGas.left + r.stateGas.left
          spilled := saved.stateGas.spilled + r.stateGas.spilled }
        returnData := returnData }
    if r.failed then
      if p.newAccountCharged then m.creditStateGasRefund state.newAccount else m
    else m.repayStateGasSpill

/-- Resume the caller `saved` with its child's result `r`.

Under state gas a failed result must be settled (no committed or outstanding spill, the
reservoir at its baseline) and a successful one must have no committed spill; otherwise the run
faults. The merged caller is then pushed the status; a full stack halts it with the merged
state. -/
def resume (rules : ForkRules) (p : Staging.Pending) (saved : Frame.State) (r : Frame.Result) :
    Except Fault (Except (ExceptionalHalt × Frame.State) Frame.State) := do
  if rules.stateGas.isSome then
    if r.failed then
      unless r.stateGas.committedSpill = 0 ∧ r.stateGas.spilled = 0 ∧
          r.stateGas.left = r.stateGas.baseline do
        throw (.internal (.invariant (.text "failed Amsterdam child is not settled")))
    else unless r.stateGas.committedSpill = 0 do
      throw (.internal (.invariant (.text "Amsterdam child has committed state-gas spill")))
  let (world, substate) := match r with
    | .success _ _ _ world sub _ => (world, saved.substate.absorb rules sub)
    | _ => (saved.world, match rules.stateGas with
                         | none => saved.substate.keepTouch r.trail
                         | some _ => saved.substate)
  let merged : Frame.State :=
    ⟨absorbMeters rules p saved.machine r, world, substate, saved.trail.absorb r.trail⟩
  if merged.machine.stack.length < 1024 then
    pure (.ok { merged with machine := finishTarget p.target r merged.machine })
  else pure (.error (.stackOverflow .none, merged))
end Jaune.Checked
