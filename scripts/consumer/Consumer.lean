import Jaune.SymbolicPush
import Jaune.FrameRun.Adequacy

/- A disposable external consumer: build a complete out-of-gas run and connect
it to the interpreter. No Blanc package or example imports are used. -/
namespace Consumer
open Jaune Jaune

def outOfGasRun {r : Frame.Running}
    (bytes : Bytes) (width : bytes.length ≤ 32)
    (decoded : NextOp.At r.context.code r.pc (.push bytes width))
    (gas : r.state.machine.gasLeft < SymbolicPush.cost bytes)
    (hgate : bytes ≠ [] ∨ r.context.block.rules.opcodes.push0) :
    Frame.Run r (.exit (.ok (.halted (.outOfGas .none) r.state))) :=
  .halt (by rw [step_of_next decoded, SymbolicPush.step_outOfGas r bytes width gas hgate]; rfl)

theorem interpreter_outOfGasRun {r : Frame.Running}
    (bytes : Bytes) (width : bytes.length ≤ 32)
    (decoded : NextOp.At r.context.code r.pc (.push bytes width))
    (gas : r.state.machine.gasLeft < SymbolicPush.cost bytes)
    (hgate : bytes ≠ [] ∨ r.context.block.rules.opcodes.push0) :
    exec r = .ok (.halted (.outOfGas .none) r.state) :=
  (Frame.Run.exec_iff _ _).mp ⟨outOfGasRun bytes width decoded gas hgate⟩

end Consumer
