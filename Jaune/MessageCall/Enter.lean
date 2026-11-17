import Jaune.MessageCall.Settle
import Jaune.Precompiles

/-!
# The four-part message call: `enter` (goal `jaune-shape-and-names-v1`, W1 unit D)

`enter` starts a frame: it moves the value, and either hands back a machine to run or, for a
precompile or a failed value transfer, the frame's result at once. Staged under a namespace of its own until the switch commit, which gave it its final names; nothing in today's interpreter reads it until the switch commit.

This is the W1 form: the running machine is still today's `Evm`, built through
`Message.sevm` and `Frame.State.toDevm`.

The world and the created accounts a frame runs on always come from its checkpoint; only the
machine, the substate and the trail's read sets come from the start state. A spawned child starts
from `Frame.start`, which seeds its deletions from its caller's only under rules that pay a
self-destruct refund; a top-level frame starts from its checkpoint, ungated.
-/

namespace Jaune

/-- A spawned child's initial state: today's `initDevm` of the child's message. The machine is
empty with the message's gas and state-gas grant; the world is the checkpoint's; the logs are the
entry's transfer log; the deletions are the caller's under rules that pay a self-destruct
refund; the accessed sets and created accounts are the caller's. -/
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
      { logs := transferLogs rules m
        refund := 0
        selfDestructs :=
          if rules.settlement.selfdestructRefund = 0 then .emptyWithCapacity
          else cp.substate.selfDestructs
        accessedAddresses := cp.substate.accessedAddresses
        accessedStorageKeys := cp.substate.accessedStorageKeys
        touchedAccounts := .emptyWithCapacity }
    trail := { createdAccounts := cp.trail.createdAccounts } }

/-- A spawned child's initial state as today's `Devm`. -/
def Frame.start (f : Frame) : Devm := (Frame.startState f).toDevm

/-- The created accounts a frame runs with: the checkpoint's, and for a creation its new
address. -/
def Frame.enteredCreatedAccounts (f : Frame) : AdrSet :=
  match f.message.kind with
  | .call => f.checkpoint.trail.createdAccounts
  | .create => f.checkpoint.trail.createdAccounts.insert f.message.context.recipient

/-- Enter a frame from a given start state. The value moves on the world the frame is entered on
(the checkpoint's, set up for a creation); a creation's new address joins the created accounts.
A precompile target is run and settled at once; any other target hands back its machine. -/
def enterWith (f : Frame) (start : Devm) : Frame.Entry :=
  let m := f.message
  match m.transfer f.enteredWorld with
  | .error fault => .done (.error fault)
  | .ok world =>
    let evm : Evm :=
      ⟨0, m.sevm, (start.setWorld world).withCreatedAccounts f.enteredCreatedAccounts⟩
    match m.codeAddress with
    | some address =>
      if !m.disablePrecompiles && m.context.block.rules.isPrecompile address then
        .done (settle f (executePrecompile evm address))
      else .run evm
    | none => .run evm

/-- Enter a spawned child frame. -/
def enter (f : Frame) : Frame.Entry := enterWith f f.start

end Jaune

