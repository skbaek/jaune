import Jaune.MessageCall.CheckedDriver

/-! A complete execution derivation over the running frame. A child run and the
caller's continuation are separate subderivations. Faults carry no frame state. -/

namespace Jaune.Checked

/-- Finishing a call either gives the driver's final outcome or a caller state to resume. -/
def resumeCaller (rules : ForkRules) (child : Frame) (pending : Staging.Pending) :
    Except Fault Frame.Result → Except (Except Fault Frame.Exit) Frame.State
  | .error fault => .error (.error fault)
  | .ok result =>
    match resume rules pending child.checkpoint result with
    | .error fault => .error (.error fault)
    | .ok (.error (reason, state)) => .error (.ok (.halted reason state))
    | .ok (.ok state) => .ok state

/-- A derivation of the outcome of the four-part frame driver. -/
inductive Exec : Frame.Running → Except Fault Frame.Exit → Type
  | halt {r : Frame.Running} {out : Except Fault Frame.Exit} :
    step r = out.map Step.exit → Exec r out
  | cont {r pc state out} :
    step r = .ok (.next pc state) →
    Exec ⟨pc, r.context, state⟩ out →
    Exec r out
  | doneErr {r child pending pc result out} :
    step r = .ok (.spawn child pending pc) →
    enter child = .done result →
    resumeCaller r.context.block.rules child pending result = .error out →
    Exec r out
  | doneOk {r child pending pc result state out} :
    step r = .ok (.spawn child pending pc) →
    enter child = .done result →
    resumeCaller r.context.block.rules child pending result = .ok state →
    Exec ⟨pc, r.context, state⟩ out →
    Exec r out
  | runErr {r child pending pc cr raw out} :
    step r = .ok (.spawn child pending pc) →
    enter child = .run cr →
    Exec cr raw →
    resumeCaller r.context.block.rules child pending (raw >>= settle child) = .error out →
    Exec r out
  | runOk {r child pending pc cr raw state out} :
    step r = .ok (.spawn child pending pc) →
    enter child = .run cr →
    Exec cr raw →
    resumeCaller r.context.block.rules child pending (raw >>= settle child) = .ok state →
    Exec ⟨pc, r.context, state⟩ out →
    Exec r out

theorem execFueled_spawn_done {r : Frame.Running} {fuel : Nat} {child pending pc result}
    (hs : step r = .ok (.spawn child pending pc)) (he : enter child = .done result) :
    execFueled r (fuel + 1) =
      match resumeCaller r.context.block.rules child pending result with
      | .error out => Fueled.ofExcept out
      | .ok state => execFueled ⟨pc, r.context, state⟩ fuel := by
  rw [execFueled, hs]
  dsimp only
  rw [he]
  cases result with
  | error f => rfl
  | ok v =>
    dsimp only [resumeCaller]
    rcases resume r.context.block.rules pending child.checkpoint v with
      f | ⟨reason, state⟩ | state <;> rfl

theorem execFueled_spawn_run {r : Frame.Running} {fuel : Nat} {child pending pc cr}
    (hs : step r = .ok (.spawn child pending pc)) (he : enter child = .run cr) :
    execFueled r (fuel + 1) =
      match (execFueled cr fuel).run with
      | none => Fueled.exhausted
      | some raw =>
        match resumeCaller r.context.block.rules child pending (raw >>= settle child) with
        | .error out => Fueled.ofExcept out
        | .ok state => execFueled ⟨pc, r.context, state⟩ fuel := by
  rw [execFueled, hs]
  dsimp only
  rw [he]
  dsimp only
  cases hc : (execFueled cr fuel).run with
  | none => rfl
  | some raw =>
    dsimp only [Option.map]
    cases raw >>= settle child with
    | error f => rfl
    | ok v =>
      dsimp only [resumeCaller]
      rcases resume r.context.block.rules pending child.checkpoint v with
        f | ⟨reason, state⟩ | state <;> rfl

/-- Every budget at least the derivation's height suffices, including when the
driver uses the same remaining budget for a child and then for the caller. -/
theorem Exec.sufficient {r out} (run : Exec r out) :
    ∃ height, ∀ fuel ≥ height, execFueled r fuel = Fueled.ofExcept out := by
  induction run with
  | @halt r out hs =>
    refine ⟨1, ?_⟩
    intro fuel large
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    cases out <;> simp [execFueled, hs, Except.map]
  | cont hs _ ih =>
    obtain ⟨height, ih⟩ := ih
    refine ⟨height + 1, ?_⟩
    intro fuel large
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    simpa only [execFueled, hs] using ih fuel (by omega)
  | doneErr hs he hr =>
    refine ⟨1, ?_⟩
    intro fuel large
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [execFueled_spawn_done hs he, hr]
  | doneOk hs he hr _ ih =>
    obtain ⟨height, ih⟩ := ih
    refine ⟨height + 1, ?_⟩
    intro fuel large
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [execFueled_spawn_done hs he, hr]
    exact ih fuel (by omega)
  | runErr hs he _ hr ih =>
    obtain ⟨height, ih⟩ := ih
    refine ⟨height + 1, ?_⟩
    intro fuel large
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [execFueled_spawn_run hs he, ih fuel (by omega), Fueled.ofExcept_run]
    simp only [hr]
  | runOk hs he _ hr _ ihChild ihParent =>
    obtain ⟨ch, ihChild⟩ := ihChild
    obtain ⟨ph, ihParent⟩ := ihParent
    refine ⟨max ch ph + 1, ?_⟩
    intro fuel large
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [execFueled_spawn_run hs he, ihChild fuel (by omega), Fueled.ofExcept_run]
    simpa only [hr] using ihParent fuel (by omega)

/-- Recover each subderivation from the driver, eliminating exhaustion at the root and at
each child. -/
def Exec.ofFueled (fuel : Nat) (r : Frame.Running) (out : Except Fault Frame.Exit)
    (h : execFueled r fuel = Fueled.ofExcept out) : Exec r out := by
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
      let next := Exec.ofFueled fuel _ _ h
      exact .cont hs next
    · cases he : enter child with
      | done result =>
        rw [execFueled_spawn_done hs he] at h
        cases hr : resumeCaller r.context.block.rules child pending result with
        | error terminal =>
          rw [hr] at h
          cases Fueled.ofExcept_inj.mp h
          exact .doneErr hs he hr
        | ok state =>
          rw [hr] at h
          let next := Exec.ofFueled fuel _ _ h
          exact .doneOk hs he hr next
      | run cr =>
        rw [execFueled_spawn_run hs he] at h
        cases hc : (execFueled cr fuel).run with
        | none =>
          rw [hc] at h
          exact (Fueled.exhausted_ne_ofExcept h).elim
        | some raw =>
          let childRun := Exec.ofFueled fuel cr raw (Fueled.ext hc)
          rw [hc] at h
          dsimp only at h
          cases hr : resumeCaller r.context.block.rules child pending (raw >>= settle child) with
          | error terminal =>
            rw [hr] at h
            cases Fueled.ofExcept_inj.mp h
            exact .runErr hs he childRun hr
          | ok state =>
            rw [hr] at h
            let next := Exec.ofFueled fuel _ _ h
            exact .runOk hs he childRun hr next
termination_by fuel

theorem Exec.of_fueled (fuel : Nat) (r : Frame.Running) (out : Except Fault Frame.Exit)
    (h : execFueled r fuel = Fueled.ofExcept out) : Nonempty (Exec r out) := ⟨Exec.ofFueled fuel r out h⟩

end Jaune.Checked
