import Jaune.Bridge.G2b.CheckedDriver
import Jaune.Bridge.G2b.CheckedIngress
import Jaune.Bridge.G2b.CheckedReached
import Jaune.Implementation.CheckedCachedDriver
import Jaune.Bridge.G2b.FinalDriver
import Jaune.Bridge.G2a.Run

namespace Jaune.Checked

/-- A raw running machine can be grouped exactly when its backing memory lies within its logical size. -/
def Frame.Running.ofEvm (evm : Evm) (hw : evm.dyna.memory.Wf) : Frame.Running :=
  Frame.Running.ofLegacy (Jaune.Frame.Running.ofEvm evm) hw

theorem step_ofEvm (evm : Evm) (hw : evm.dyna.memory.Wf) (ho : evm.dyna.output = []) :
    (step (Frame.Running.ofEvm evm hw)).map Step.toLegacy = (Jaune.Evm.step evm).observe := by
  rw [← MemorySimulation.step]
  exact Staging.step_ofEvm evm ho

theorem execFueled_square (fuel : Nat) (evm : Evm) (hw : evm.dyna.memory.Wf) (ho : evm.dyna.output = []) :
    (execFueled (Frame.Running.ofEvm evm hw) fuel).run.map (Except.map Frame.Exit.toLegacy) =
      (Jaune.execFueled evm fuel).run.map Jaune.Frame.Exit.ofExecution := by
  rw [← execFueled_toLegacy]
  exact Jaune.execFueled_square fuel evm ho

theorem exec_square (evm : Evm) (hw : evm.dyna.memory.Wf) (ho : evm.dyna.output = []) :
    (exec (Frame.Running.ofEvm evm hw)).map Frame.Exit.toLegacy = Jaune.Frame.Exit.ofExecution (Jaune.exec evm) := by
  rw [← exec_toLegacy]
  exact Jaune.exec_square evm ho

theorem execFueledCached_square (fuel : Nat) (evm : Evm) (hw : evm.dyna.memory.Wf) (ho : evm.dyna.output = []) :
    (execFueledCached (Frame.Running.ofEvm evm hw) fuel).run.map (Except.map Frame.Exit.toLegacy) =
      (Jaune.execFueled evm fuel).run.map Jaune.Frame.Exit.ofExecution := by
  rw [← execFueled_eq_cached]
  exact execFueled_square fuel evm hw ho

/-- Full outward result, for every checked frame and every fork. -/
theorem Frame.runTop_square (f : Frame) : Frame.runTop f = Jaune.Frame.runTop f.toLegacy := by
  rw [← Jaune.Frame.runTop_square, ← Frame.runTop_toLegacy]

/-- A top-level preparation always supplies the evidence to convert its checkpoint exactly. -/
theorem Frame.runTop_prepared {msg : Msg} {f : Jaune.Frame} {refund : Nat}
    (hp : Staging.TopLevel.prepare msg = .ok (.frame f refund)) :
    Frame.runTop (Frame.ofLegacy f (Staging.TopLevel.prepare_frame_memory_wf hp)) = Jaune.Frame.runTop f := by
  rw [Frame.runTop_square, Frame.toLegacy_ofLegacy]

/-- The checked frame entered by transaction preparation names its kind and code address
coherently, including after authorization and delegation resolution. -/
theorem Frame.ofLegacy_prepared_kindCoherent {benv : Benv} {tenv : Tenv} {tx : Transaction}
    {msg : Msg} (hm : prepareMessage benv tenv tx = .ok msg) {f : Jaune.Frame} {refund : Nat}
    (hp : Staging.TopLevel.prepare msg = .ok (.frame f refund)) :
    (Frame.ofLegacy f (Staging.TopLevel.prepare_frame_memory_wf hp)).message.KindCoherent :=
  processMessageCall.topFrame_kindCoherent hm (Jaune.Bridge.G2a.Staging.TopLevel.prepare_topFrame hp)

/-- Raw execution from a prepared frame keeps every reached current machine well formed. -/
theorem prepared_reached_memory_wf {msg : Msg} {f : Jaune.Frame} {refund : Nat} {root evm : Evm}
    (hp : Staging.TopLevel.prepare msg = .ok (.frame f refund))
    (he : Jaune.enterWith f f.checkpoint.toDevm = .run root) (hr : root.Reaches evm) : evm.dyna.memory.Wf :=
  hr.memory_wf (MemoryReachability.enterWith_run (start := f.checkpoint.toDevm)
    (Staging.TopLevel.prepare_frame_memory_wf hp) he)

/-- Every caller checkpoint saved by that execution has well-formed memory. -/
theorem prepared_checkpoint_memory_wf {msg : Msg} {f : Jaune.Frame} {refund : Nat} {root evm : Evm}
    (hp : Staging.TopLevel.prepare msg = .ok (.frame f refund))
    (he : Jaune.enterWith f f.checkpoint.toDevm = .run root) (hr : root.Reaches evm)
    {child : Jaune.Frame} {p : Pending} {pc : Nat} (hs : evm.step = .spawn child p pc) :
    child.checkpoint.machine.memory.Wf :=
  hr.checkpoint_memory_wf (MemoryReachability.enterWith_run (start := f.checkpoint.toDevm)
    (Staging.TopLevel.prepare_frame_memory_wf hp) he) hs

/-- The complete transaction-visible output of checked execution, using the proven preparation
and rendering functions for the bridge candidate. -/
def preparedMessageOutput (msg : Msg) : Except EvmError (Jaune.State × MsgCallOutput) :=
  match hp : Staging.TopLevel.prepare msg with
  | .error fault => .error fault.toEvmError
  | .ok (.refused h d) => (Staging.MessageRun.mk msg (.refused h d) none none).output
  | .ok (.frame f refund) => do
    let r ← (Frame.runTop (Frame.ofLegacy f (Staging.TopLevel.prepare_frame_memory_wf hp))).mapError Fault.toEvmError
    match msg.benv.stat.rules.stateGas with
    | none => f.output refund r
    | some _ => f.outputAmsterdam r

/-- The transaction-visible output agrees for every top-level message, including preparation faults. -/
theorem preparedMessageOutput_square (msg : Msg) : preparedMessageOutput msg = Jaune.processMessageCall msg := by
  rw [← Jaune.Bridge.G2a.processMessageCall_eq]
  unfold preparedMessageOutput
  split
  · rename_i fault hp
    rw [Jaune.Bridge.G2a.processMessageCall_of_fault hp]
  · rename_i reason d hp
    rw [Jaune.Bridge.G2a.processMessageCall_of_refused hp]
    rfl
  · rename_i f refund hp
    rw [Jaune.Bridge.G2a.processMessageCall_of_frame hp, Frame.runTop_prepared hp]
    rfl

end Jaune.Checked
