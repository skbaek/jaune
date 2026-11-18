import Jaune.Memory
import Jaune.MessageCall

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

end Jaune.Checked
