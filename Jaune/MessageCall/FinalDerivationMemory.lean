import Jaune.MessageCall.FinalMemoryAccounting
import Jaune.MessageCall.FinalAdequacy

/-! # Gas and memory bounds of an execution derivation -/

namespace Jaune.Staging
open Jaune

/-- The completed frame described by a derivation settles within its initial gas measure. -/
theorem Exec.settledGasLe {r : Frame.Running} {out : Except Fault Frame.Exit} (h : Exec r out) :
    match out with
    | .error _ => True
    | .ok e => e.SettledGasLe r.state.machine.gasMeasure := by
  have he := (exec_iff_exec_eq r out).mp ⟨h⟩
  cases out with
  | error _ => trivial
  | ok e =>
    have hs := execFueled_run_sufficientFuel r
    rw [he] at hs
    exact execFueled_settledGasLe _ r hs

/-- Every frame exit in a closed derivation satisfies the gas and memory output bound. -/
theorem Exec.memory_accounting_output {r : Frame.Running} {out : Except Fault Frame.Exit}
    (h : Exec r out) (hn : r.context.block.rules.stateGas = none) :
    match out with
    | .error _ => True
    | .ok e => Frame.Exit.MemoryAccounted (Machine.memoryPotential r.state.machine) e := by
  have he := (exec_iff_exec_eq r out).mp ⟨h⟩
  cases out with
  | error _ => trivial
  | ok e => exact exec_memory_accounting_output r hn he

end Jaune.Staging
