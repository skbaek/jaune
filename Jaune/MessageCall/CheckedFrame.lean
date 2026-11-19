import Jaune.Memory
import Jaune.MessageCall.CheckedContext

/-! Frame-local machine state with a backing-array bound in the memory field. -/

namespace Jaune.Checked

/-- The execution state local to one frame. -/
structure Machine where
  stack : List U256
  memory : Memory
  gasLeft : Nat
  stateGas : StateGasMeter := .zero
  returnData : Bytes

/-- The dynamic state, grouped by the lifetime of its fields. -/
structure Frame.State where
  machine : Machine
  world : World
  substate : Substate
  trail : Trail

/-- The checkpoint is the caller state after preparing the child. -/
structure Frame where
  message : Message
  checkpoint : Frame.State

/-- The program counter, context and local state before a step. -/
structure Frame.Running where
  pc : Nat
  context : CallContext
  state : Frame.State

/-- The execution result before settlement. -/
inductive Frame.Exit
  | finished (output : Bytes) (state : Frame.State)
  | reverted (output : Bytes) (state : Frame.State)
  | halted (reason : ExceptionalHalt) (state : Frame.State)

/-- The machine and lifetime groups when top-level preparation begins. -/
def Message.initialCheckpoint (message : Message) (world : World)
    (accessedAddresses : AdrSet) (accessedStorageKeys : KeySet) (createdAccounts selfDestructs : AdrSet) :
    Frame.State :=
  let context := message.context
  let logs := match context.block.rules.stateGas with
    | none => []
    | some _ =>
      if message.transfersValue then
        if context.caller = context.recipient ∨ context.value = 0 then []
        else [transferLog context.caller context.recipient context.value]
      else []
  { machine := {
      stack := [], memory := .empty, gasLeft := message.gas, returnData := []
      stateGas := ⟨message.stateGasGrant, message.stateGasGrant, 0, 0⟩ }
    world
    substate := { logs, refund := 0, selfDestructs, accessedAddresses, accessedStorageKeys }
    trail := { createdAccounts } }

/-- Input to top-level preparation. Authorization tuples are consumed before the frame runs. -/
structure TopLevel.Input where
  message : Message
  checkpoint : Frame.State
  authorizationList : List Authorization

end Jaune.Checked
