import Jaune.Exec
import Jaune.MessageCall.Top

/-!
# From raw code execution to settled message results

Contract-neutral adapters between `exec` and a top-level frame run by `Frame.runTop`: its
entry, its settlement and its results.
-/

namespace Jaune

-- `ByteArray.getInst` and other extensions of root types live in `Jaune`;
-- opening it lets generalized field notation (`code.getInst`) find them.
open Jaune

/-! ## Canonical message-entry projections -/

@[simp] theorem Msg.initDevm_stack (msg : Msg) :
    (initDevm msg).stack = [] := rfl

@[simp] theorem Msg.initDevm_memory (msg : Msg) :
    (initDevm msg).memory = Mem.empty := rfl

@[simp] theorem Msg.initDevm_accessedStorageKeys (msg : Msg) :
    (initDevm msg).accessedStorageKeys = msg.accessedStorageKeys := rfl

@[simp] theorem Msg.initSevm_data (msg : Msg) :
    (initSevm msg).data = msg.data := rfl

@[simp] theorem Msg.initSevm_currentTarget (msg : Msg) :
    (initSevm msg).currentTarget = msg.currentTarget := rfl

/-! ## Adapters for `Frame.runTop`, `enterWith` and `settle`

A failed frame's result carries no world, logs or substate (S3): these name the result, its
output, gas and meter; the world after it is the checkpoint's (`Frame.worldAfter`). -/

namespace MessageExecution

/-- A frame entered into the interpreter settles the total execution selected by that entry. -/
theorem runTop_eq_settle_exec_of_enter (f : Frame) (evm : Evm)
    (henter : enterWith f f.checkpoint.toDevm = .run evm) :
    Frame.runTop f = settle f (exec evm) := by
  unfold Frame.runTop
  rw [henter]

/-- After a successful transfer, a frame whose code address is not a precompile under its
rules enters the interpreter on the transferred world. -/
theorem enterWith_eq_run_of_notPrecompile (f : Frame) (start : Devm) (world : World)
    (codeAddress : Address)
    (htransfer : f.message.transfer f.enteredWorld = .ok world)
    (hcode : f.message.codeAddress = some codeAddress)
    (hnotPrecompile : ¬ f.message.context.block.rules.isPrecompile codeAddress) :
    enterWith f start =
      .run ⟨0, f.message.sevm, (start.setWorld world).withCreatedAccounts
        f.enteredCreatedAccounts⟩ := by
  unfold enterWith
  simp only [htransfer, hcode, hnotPrecompile, decide_false, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]

/-- After a successful transfer, a frame with no code address (a creation) enters its code. -/
theorem enterWith_eq_run_of_noCodeAddress (f : Frame) (start : Devm) (world : World)
    (htransfer : f.message.transfer f.enteredWorld = .ok world)
    (hcode : f.message.codeAddress = none) :
    enterWith f start =
      .run ⟨0, f.message.sevm, (start.setWorld world).withCreatedAccounts
        f.enteredCreatedAccounts⟩ := by
  unfold enterWith
  simp only [htransfer, hcode]

/-- After a successful transfer, a frame with precompiles disabled enters its code. -/
theorem enterWith_eq_run_of_disablePrecompiles (f : Frame) (start : Devm) (world : World)
    (htransfer : f.message.transfer f.enteredWorld = .ok world)
    (hdisable : f.message.disablePrecompiles = true) :
    enterWith f start =
      .run ⟨0, f.message.sevm, (start.setWorld world).withCreatedAccounts
        f.enteredCreatedAccounts⟩ := by
  unfold enterWith
  simp only [htransfer, hdisable]
  split <;> simp

/-- A call frame's clean finish settles to a success carrying its output and its machine after
its own touch. -/
theorem settle_ok_call (f : Frame) (d : Devm) (hkind : f.message.kind = .call) :
    settle f (.ok d) =
      let d' := d.recordTouch f.message.context.block.rules true f.message.context.recipient
      .ok (Frame.Result.ofSuccess d'.output d') := by
  unfold settle
  simp only [hkind]

/-- Without state gas, a raw REVERT settles to a revert with the raw output, gas and meter. -/
theorem settle_revert (f : Frame) (d : Devm)
    (hgas : f.message.context.block.rules.stateGas = none) :
    ∃ trail, settle f (.error (.revert, d)) = .ok (.revert d.output d.gasLeft d.mach.stateGas trail) := by
  unfold settle
  simp only [hgas]
  exact ⟨_, rfl⟩

/-- Without state gas, a raw exceptional halt settles to a halt with the raw meter. -/
theorem settle_halt (f : Frame) (reason : ExceptionalHalt) (d : Devm)
    (hgas : f.message.context.block.rules.stateGas = none) :
    ∃ trail, settle f (.error (.halt reason, d)) = .ok (.halt reason d.mach.stateGas trail) := by
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

end Jaune
