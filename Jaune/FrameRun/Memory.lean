import Jaune.MessageCall.MemoryAccounting
import Jaune.FrameRun.Adequacy

/-!
# Gas and memory bounds of a checked frame sequence (goal `jaune-shape-and-names-v1`, G2b)

`Checked.Exec.settledGasLe` and `Checked.Exec.memory_accounting_output` restated over
`Checked.Frame.Run`, with the same conclusions.
-/

namespace Jaune.Frame.Run
open Jaune

/-- The completed frame described by a run settles within its initial gas measure. -/
theorem settledGasLe {r : Frame.Running} {out : Except Fault Frame.Exit} (t : Frame.Run r (.exit out)) :
    match out with
    | .error _ => True
    | .ok e => e.SettledGasLe r.state.machine.gasMeasure := by
  have he := (exec_iff r out).mp ⟨t⟩
  cases out with
  | error _ => trivial
  | ok e =>
    have hs := execFueled_run_sufficientFuel r
    rw [he] at hs
    exact execFueled_settledGasLe _ r hs

/-- Every frame exit of a closed run satisfies the gas and memory output bound. -/
theorem memory_accounting_output {r : Frame.Running} {out : Except Fault Frame.Exit}
    (t : Frame.Run r (.exit out)) (hn : r.context.block.rules.stateGas = none) :
    match out with
    | .error _ => True
    | .ok e => Frame.Exit.MemoryAccounted (Machine.memoryPotential r.state.machine) e := by
  have he := (exec_iff r out).mp ⟨t⟩
  cases out with
  | error _ => trivial
  | ok e => exact exec_memory_accounting_output r hn he

end Jaune.Frame.Run
