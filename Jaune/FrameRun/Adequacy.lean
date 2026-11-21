import Jaune.FrameRun.Basic
import Jaune.MessageCall.Totality

namespace Jaune.Frame.Run

theorem sufficient {r out} (run : Frame.Run r (.exit out)) :
    ∃ height, ∀ fuel ≥ height, execFueled r fuel = Fueled.ofExcept out := by
  cases run with
  | halt hs =>
    refine ⟨1, ?_⟩
    intro fuel large
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    cases out <;> simp [execFueled, hs, Except.map]
  | next hs rest =>
    obtain ⟨height, ih⟩ := sufficient rest
    refine ⟨height + 1, ?_⟩
    intro fuel large
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    simpa only [execFueled, hs] using ih fuel (by omega)
  | callDoneEnd hs he hr =>
    refine ⟨1, ?_⟩
    intro fuel large
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [execFueled_spawn_done hs he, hr]
  | callDone hs he hr rest =>
    obtain ⟨height, ih⟩ := sufficient rest
    refine ⟨height + 1, ?_⟩
    intro fuel large
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [execFueled_spawn_done hs he, hr]
    exact ih fuel (by omega)
  | callRanEnd hs he child hr =>
    obtain ⟨height, ih⟩ := sufficient child
    refine ⟨height + 1, ?_⟩
    intro fuel large
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [execFueled_spawn_run hs he, ih fuel (by omega), Fueled.ofExcept_run]
    simp only [hr]
  | callRan hs he child hr rest =>
    obtain ⟨ch, ihChild⟩ := sufficient child
    obtain ⟨ph, ihParent⟩ := sufficient rest
    refine ⟨max ch ph + 1, ?_⟩
    intro fuel large
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [execFueled_spawn_run hs he, ihChild fuel (by omega), Fueled.ofExcept_run]
    simpa only [hr] using ihParent fuel (by omega)

termination_by sizeOf run

/-- Recover each subderivation from the driver, eliminating exhaustion at the root and at
each child. -/
def ofFueled (fuel : Nat) (r : Frame.Running) (out : Except Fault Frame.Exit)
    (h : execFueled r fuel = Fueled.ofExcept out) : Frame.Run r (.exit out) := by
  cases fuel with
  | zero => exact (Fueled.exhausted_ne_ofExcept h).elim
  | succ fuel =>
    rcases hs : step r with f | exit | ⟨pc, state⟩ | ⟨child, pending, pc⟩
    · simp only [execFueled, hs] at h
      cases Fueled.ofExcept_inj.mp h
      exact .halt hs
    · simp only [execFueled, hs] at h
      cases Fueled.ofExcept_inj.mp h
      exact .halt hs
    · simp only [execFueled, hs] at h
      let next := ofFueled fuel _ _ h
      exact .next hs next
    · cases he : enter child with
      | done result =>
        rw [execFueled_spawn_done hs he] at h
        cases hr : resumeCaller r.context.block.rules child pending result with
        | error terminal =>
          rw [hr] at h
          cases Fueled.ofExcept_inj.mp h
          exact .callDoneEnd hs he hr
        | ok state =>
          rw [hr] at h
          let next := ofFueled fuel _ _ h
          exact .callDone hs he hr next
      | run cr =>
        rw [execFueled_spawn_run hs he] at h
        cases hc : (execFueled cr fuel).run with
        | none =>
          rw [hc] at h
          exact (Fueled.exhausted_ne_ofExcept h).elim
        | some raw =>
          let childRun := ofFueled fuel cr raw (Fueled.ext hc)
          rw [hc] at h
          dsimp only at h
          cases hr : resumeCaller r.context.block.rules child pending (raw >>= settle child) with
          | error terminal =>
            rw [hr] at h
            cases Fueled.ofExcept_inj.mp h
            exact .callRanEnd hs he childRun hr
          | ok state =>
            rw [hr] at h
            let next := ofFueled fuel _ _ h
            exact .callRan hs he childRun hr next
termination_by fuel


/-- A finite whole run at the interpreter's totality budget. -/
def canonical (r : Frame.Running) : Frame.Run r (.exit (exec r)) :=
  ofFueled _ r _ (Fueled.ext (execFueled_run_sufficientFuel r))

/-- Whole runs describe exactly the total interpreter's result, including semantic faults. -/
theorem exec_iff (r : Frame.Running) (out : Except Fault Frame.Exit) :
    Nonempty (Frame.Run r (.exit out)) ↔ exec r = out := by
  constructor
  · rintro ⟨run⟩
    obtain ⟨height, enough⟩ := sufficient run
    let fuel := max height (r.state.machine.gasMeasure + 1)
    apply exec_eq_of_run (fuel := fuel) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right ..))
    rw [enough fuel (Nat.le_max_left ..), Fueled.ofExcept_run]
  · rintro rfl
    exact ⟨canonical r⟩

theorem exec_of_prefix {r s} (p : Prefix r s) : exec r = exec s :=
  (exec_iff ..).mp ⟨append p (canonical s)⟩

theorem exit_unique {r a b} (p : Frame.Run r (.exit a)) (q : Frame.Run r (.exit b)) : a = b :=
  ((exec_iff ..).mp ⟨p⟩).symm.trans ((exec_iff ..).mp ⟨q⟩)

end Jaune.Frame.Run
