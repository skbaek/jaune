import Jaune.MessageCall.FinalAdequacy
import Jaune.Bridge.G2b.FinalDriver
import Jaune.Exec

namespace Jaune

/-- An output-free running machine has the same closed executions after mapping both its
input and its terminal observation. A legacy fault may carry an unobservable machine. -/
theorem Staging.Exec.ofEvm_iff (evm : Evm) (clean : evm.dyna.output = [])
    (out : Except Fault Frame.Exit) :
    Nonempty (Staging.Exec (Frame.Running.ofEvm evm) out) ↔
      ∃ old, Nonempty (Jaune.Exec evm.pc evm.sta evm.dyna old) ∧ Frame.Exit.ofExecution old = out := by
  rw [Staging.exec_iff_exec_eq, exec_square evm clean]
  constructor
  · intro h
    exact ⟨Jaune.exec evm, Jaune.Exec.nonempty evm, h⟩
  · rintro ⟨old, hold, eq⟩
    have he : Jaune.exec evm = old := (Jaune.exec_iff_exec_eq ..).mp hold
    rw [he, eq]

end Jaune
