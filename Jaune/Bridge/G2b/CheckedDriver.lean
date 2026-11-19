import Jaune.Bridge.G2b.CheckedDriverCore
import Jaune.Bridge.G2b.CheckedParts
import Jaune.Bridge.G2b.CheckedStep
import Jaune.MessageCall.FinalExec

/-! The recursive frame simulation, including exhaustion, faults, immediate entries and nested runs. -/

namespace Jaune.Checked



theorem execFueled_toLegacy (fuel : Nat) (r : Frame.Running) :
    (Staging.execFueled r.toLegacy fuel).run =
      (execFueled r fuel).run.map (Except.map Frame.Exit.toLegacy) :=
  execFueled_toLegacy_of_parts MemorySimulation.step enter_toLegacy settle_toLegacy resume_toLegacy fuel r

theorem exec_toLegacy (r : Frame.Running) :
    Staging.exec r.toLegacy = (exec r).map Frame.Exit.toLegacy :=
  exec_toLegacy_of_parts MemorySimulation.step enter_toLegacy settle_toLegacy resume_toLegacy r

theorem Frame.runTop_toLegacy (f : Frame) : Staging.Frame.runTop f.toLegacy = Frame.runTop f :=
  Frame.runTop_toLegacy_of_parts MemorySimulation.step enter_toLegacy settle_toLegacy resume_toLegacy
    enterWith_toLegacy f

end Jaune.Checked
