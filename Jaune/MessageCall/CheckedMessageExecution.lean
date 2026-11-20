import Jaune.MessageCall.CheckedExec
import Jaune.MessageCall.CheckedCanonical

/-!
# From checked code execution to settled message results (goal `jaune-shape-and-names-v1`, G2b,
unit jsn-u97)

Contract-neutral adapters between `Checked.exec` and a top-level frame run by
`Checked.Frame.runTop`: its entry, its settlement and its results. The checked counterparts of the
original-run `Jaune.MessageExecution` forms, beside `Checked.Frame.runTop_eq`.

A failed frame's result carries no world, logs or substate (S3): these name the result, its
output, gas and meter; the world after it is the checkpoint's (`Checked.Frame.worldAfter`).
-/

namespace Jaune.Checked

open Jaune

namespace MessageExecution

/-- A frame entered into the interpreter settles the total execution selected by that entry. -/
theorem runTop_eq_settle_exec_of_enter (f : Frame) (r : Frame.Running)
    (henter : enterWith f f.checkpoint = .run r) :
    Frame.runTop f = exec r >>= settle f := by
  rw [Frame.runTop_eq, henter]

/-- After a successful transfer, a frame whose code address is not a precompile under its
rules enters the interpreter on the transferred world. -/
theorem enterWith_eq_run_of_notPrecompile (f : Frame) (start : Frame.State) (world : World)
    (codeAddress : Address)
    (htransfer : f.message.transfer f.enteredWorld = .ok world)
    (hcode : f.message.codeAddress = some codeAddress)
    (hnotPrecompile : ¬ f.message.context.block.rules.isPrecompile codeAddress) :
    enterWith f start = .run (Frame.entered f start world) := by
  unfold enterWith
  simp only [htransfer, hcode, hnotPrecompile, decide_false, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]

/-- After a successful transfer, a frame with no code address (a creation) enters its code. -/
theorem enterWith_eq_run_of_noCodeAddress (f : Frame) (start : Frame.State) (world : World)
    (htransfer : f.message.transfer f.enteredWorld = .ok world)
    (hcode : f.message.codeAddress = none) :
    enterWith f start = .run (Frame.entered f start world) := by
  unfold enterWith
  simp only [htransfer, hcode]

/-- After a successful transfer, a frame with precompiles disabled enters its code. -/
theorem enterWith_eq_run_of_disablePrecompiles (f : Frame) (start : Frame.State) (world : World)
    (htransfer : f.message.transfer f.enteredWorld = .ok world)
    (hdisable : f.message.disablePrecompiles = true) :
    enterWith f start = .run (Frame.entered f start world) := by
  unfold enterWith
  simp only [htransfer, hdisable]
  split <;> simp

/-- A call frame's clean finish settles to a success carrying its output and its state after
its own touch. -/
theorem settle_ok_call (f : Frame) (output : Bytes) (s : Frame.State)
    (hkind : f.message.kind = .call) :
    settle f (.finished output s) =
      let s' := s.recordTouch f.message.context.block.rules true f.message.context.recipient
      .ok (Frame.Result.ofSuccess output s') := by
  unfold settle
  simp only [hkind]

/-- Without state gas, a REVERT exit settles to a revert with its output, gas and meter. -/
theorem settle_revert (f : Frame) (output : Bytes) (s : Frame.State)
    (hgas : f.message.context.block.rules.stateGas = none) :
    ∃ trail, settle f (.reverted output s) =
      .ok (.revert output s.machine.gasLeft s.machine.stateGas trail) := by
  unfold settle
  simp only [hgas]
  exact ⟨_, rfl⟩

/-- Without state gas, an exceptional halt settles to a halt with the frame's meter. -/
theorem settle_halt (f : Frame) (reason : ExceptionalHalt) (s : Frame.State)
    (hgas : f.message.context.block.rules.stateGas = none) :
    ∃ trail, settle f (.halted reason s) = .ok (.halt reason s.machine.stateGas trail) := by
  unfold settle
  simp only [hgas]
  exact ⟨_, rfl⟩

/-- A failed result leaves the frame's world as its checkpoint's. -/
theorem worldAfter_of_failed (f : Frame) (r : Frame.Result) (hfailed : r.failed = true) :
    f.worldAfter r = f.checkpoint.world := by
  cases r with
  | success => simp [Frame.Result.failed] at hfailed
  | revert => rfl
  | halt => rfl

end MessageExecution

end Jaune.Checked
