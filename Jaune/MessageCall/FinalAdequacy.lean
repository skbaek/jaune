import Jaune.MessageCall.FinalDerivation
import Jaune.MessageCall.FinalTotality

/-! A derivation characterises the fuel-independent result of the frame interpreter. -/

namespace Jaune.Staging

theorem exec_iff_exec_eq (r : Frame.Running) (out : Except Fault Frame.Exit) :
    Nonempty (Exec r out) ↔ exec r = out := by
  constructor
  · rintro ⟨run⟩
    obtain ⟨height, enough⟩ := run.sufficient
    let budget := max height (r.state.machine.gasMeasure + 1)
    have hr : execFueled r budget = Fueled.ofExcept out := enough budget (Nat.le_max_left ..)
    apply exec_eq_of_run (fuel := budget) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right ..))
    rw [hr, Fueled.ofExcept_run]
  · intro h
    have hr := execFueled_run_sufficientFuel r
    rw [h] at hr
    exact Exec.of_fueled _ _ _ (Fueled.ext hr)

theorem Exec.nonempty (r : Frame.Running) : Nonempty (Exec r (exec r)) :=
  (exec_iff_exec_eq r (exec r)).mpr rfl

end Jaune.Staging
