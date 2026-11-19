import Jaune.MessageCall.CheckedPartsGas
import Jaune.MessageCall.CheckedExec

/-! The grouped driver's fuel bound and independence of any extra fuel. -/
namespace Jaune.Checked

open Jaune

/-- The result of a run stays inside its frame's gas bound, and sufficient fuel always
produces an answer on the semantic result channel. -/
private structure RunBound (measure fuel : Nat) (x : Option (Except Fault Frame.Exit)) : Prop where
  settled : ∀ e, x = some (.ok e) → e.SettledGasLe measure
  enough : measure < fuel → x.isSome

private theorem fault_bound (n fuel : Nat) (fault : Fault) :
    RunBound n fuel (some (.error fault)) :=
  ⟨(fun _ h => nomatch h), fun _ => rfl⟩

private theorem exit_bound {n fuel : Nat} {e : Frame.Exit} (h : e.SettledGasLe n) :
    RunBound n fuel (some (.ok e)) :=
  ⟨fun _ he => by cases he; exact h, fun _ => rfl⟩

private theorem next_bound {n m fuel : Nat} {x : Option (Except Fault Frame.Exit)}
    (hlt : m < n) (h : RunBound m fuel x) : RunBound n (fuel + 1) x :=
  ⟨fun e he => (h.settled e he).mono hlt.le, fun _ => h.enough (by omega)⟩

/-- The continuation from a child's settled result in the driver's spawn branch. -/
private def afterChild (p : Staging.Pending) (saved : Frame.State) (pc : Nat)
    (ctx : CallContext) (fuel : Nat) : Option (Except Fault Frame.Result) → Fueled Fault Frame.Exit
  | none => Fueled.exhausted
  | some (.error fault) => Fueled.ofExcept (.error fault)
  | some (.ok result) =>
    match resume ctx.block.rules p saved result with
    | .error fault => Fueled.ofExcept (.error fault)
    | .ok (.error (reason, s)) => Fueled.ofExcept (.ok (.halted reason s))
    | .ok (.ok s) => execFueled ⟨pc, ctx, s⟩ fuel

private theorem afterChild_bound {n fuel : Nat} {r : Frame.Running} {child : Frame}
    {p : Staging.Pending} {pc : Nat} {x : Option (Except Fault Frame.Result)}
    (ih : ∀ run : Frame.Running, RunBound run.state.machine.gasMeasure fuel (execFueled run fuel).run)
    (hlt : child.message.gas + child.checkpoint.machine.gasMeasure < n)
    (hchild : ∀ c, x = some (.ok c) → c.gasMeasure ≤ child.message.gas)
    (hex : n < fuel + 1 → x.isSome) :
    RunBound n (fuel + 1)
      (afterChild p child.checkpoint pc r.context fuel x).run := by
  rcases x with _ | fault | result
  · exact ⟨fun _ h => by contradiction, hex⟩
  · exact fault_bound _ _ _
  · have hr := hchild result rfl
    simp only [afterChild]
    rcases he : resume r.context.block.rules p child.checkpoint result with fault | ⟨reason, s⟩ | s
    · exact fault_bound _ _ _
    · have hs := resume_gasLe he
      change s.machine.gasMeasure ≤ child.checkpoint.machine.gasMeasure + result.gasMeasure at hs
      apply exit_bound
      apply Frame.Exit.settledGasLe_of_measure
      change s.machine.gasMeasure ≤ n
      omega
    · have hs := resume_gasLe he
      change s.machine.gasMeasure ≤ child.checkpoint.machine.gasMeasure + result.gasMeasure at hs
      exact next_bound (show s.machine.gasMeasure < n by omega) (ih ⟨pc, r.context, s⟩)

private theorem execFueled_bound (fuel : Nat) (r : Frame.Running) :
    RunBound r.state.machine.gasMeasure fuel (execFueled r fuel).run := by
  induction fuel generalizing r with
  | zero => exact ⟨fun _ h => by contradiction, fun h => by omega⟩
  | succ fuel ih =>
    rw [execFueled]
    rcases hs : step r with fault | e | ⟨pc, s⟩ | ⟨child, p, pc⟩
    · exact fault_bound _ _ _
    · exact exit_bound (step_gasBound r _ hs)
    · exact next_bound (step_gasBound r _ hs) (ih ⟨pc, r.context, s⟩)
    · obtain ⟨budget, _⟩ := step_gasBound r _ hs
      apply afterChild_bound (r := r) ih budget
      · intro c hc
        cases he : enter child with
        | done result =>
          rw [he] at hc
          cases hc
          exact enter_done_gasLe he
        | run cr =>
          simp only [he] at hc
          cases hr : (execFueled cr fuel).run with
          | none => rw [hr] at hc; contradiction
          | some raw =>
            rw [hr] at hc
            cases raw with
            | error f => cases hc
            | ok e =>
              simp only [Option.map, Option.some.injEq, bind, Except.bind] at hc
              have hbound := (ih cr).settled e hr
              rw [enter_run_gasMeasure he] at hbound
              exact settle_gasLe hbound hc
      · intro h
        cases he : enter child with
        | done result => rfl
        | run cr =>
          dsimp only
          have start := enter_run_gasMeasure he
          have hsome := (ih cr).enough (by omega)
          cases hr : (execFueled cr fuel).run with
          | none => rw [hr] at hsome; contradiction
          | some raw => rfl

/-- An execution returning a frame exit stays within its initial settlement budget. -/
theorem execFueled_settledGasLe (fuel : Nat) (r : Frame.Running) {exit : Frame.Exit}
    (h : (execFueled r fuel).run = some (.ok exit)) : exit.SettledGasLe r.state.machine.gasMeasure :=
  (execFueled_bound fuel r).settled exit h

theorem execFueled_run_isSome (fuel : Nat) (r : Frame.Running) (h : r.state.machine.gasMeasure < fuel) :
    ∃ raw : Except Fault Frame.Exit, (execFueled r fuel).run = some raw :=
  Option.isSome_iff_exists.mp ((execFueled_bound fuel r).enough h)

theorem execFueled_ne_exhausted (r : Frame.Running) (fuel : Nat) (h : r.state.machine.gasMeasure < fuel) :
    execFueled r fuel ≠ Fueled.exhausted := by
  obtain ⟨raw, hraw⟩ := execFueled_run_isSome fuel r h
  intro he
  rw [he] at hraw
  contradiction

theorem execFueled_succ_ne_exhausted (r : Frame.Running) :
    execFueled r (r.state.machine.gasMeasure + 1) ≠ Fueled.exhausted :=
  execFueled_ne_exhausted _ _ (Nat.lt_succ_self _)

theorem execFueled_run_sufficientFuel_isSome (r : Frame.Running) :
    (execFueled r (sufficientFuel r.state.machine.gasMeasure)).run.isSome :=
  (execFueled_bound _ r).enough (Nat.lt_succ_self _)

/-- Running at the frame's seeded budget returns exactly the total interpreter's answer. -/
theorem execFueled_run_sufficientFuel (r : Frame.Running) :
    (execFueled r (sufficientFuel r.state.machine.gasMeasure)).run = some (exec r) := by
  obtain ⟨raw, h⟩ := execFueled_run_isSome (sufficientFuel r.state.machine.gasMeasure) r (Nat.lt_succ_self _)
  rw [h]
  unfold exec
  rw [h]

theorem exec_ok (r : Frame.Running) :
    ∃ raw, (execFueled r (sufficientFuel r.state.machine.gasMeasure)).run = some raw ∧ exec r = raw :=
  ⟨exec r, execFueled_run_sufficientFuel r, rfl⟩

private theorem afterChild_mono {fuel m : Nat} {r : Frame.Running} {child : Frame}
    {p : Staging.Pending} {pc : Nat} {x : Option (Except Fault Frame.Result)} {raw : Except Fault Frame.Exit}
    (ih : ∀ run : Frame.Running, (execFueled run fuel).run = some raw → (execFueled run m).run = some raw)
    (h : (afterChild p child.checkpoint pc r.context fuel x).run = some raw) :
    (afterChild p child.checkpoint pc r.context m x).run = some raw := by
  rcases x with _ | fault | result
  · contradiction
  · exact h
  · simp only [afterChild] at h ⊢
    rcases he : resume r.context.block.rules p child.checkpoint result with fault | ⟨reason, s⟩ | s <;> rw [he] at h
    · exact h
    · exact h
    · exact ih _ h

/-- Increasing fuel preserves the exact answer, including any propagated fault. -/
theorem execFueled_run_mono (fuel : Nat) (r : Frame.Running) {m : Nat} {raw : Except Fault Frame.Exit}
    (hle : fuel ≤ m) (h : (execFueled r fuel).run = some raw) : (execFueled r m).run = some raw := by
  induction fuel generalizing r m raw with
  | zero => contradiction
  | succ fuel ih =>
    cases m with
    | zero => omega
    | succ m =>
      have hm : fuel ≤ m := by omega
      rw [execFueled] at h ⊢
      rcases hs : step r with fault | e | ⟨pc, s⟩ | ⟨child, p, pc⟩ <;> rw [hs] at h
      · exact h
      · exact h
      · exact ih _ hm h
      · dsimp only at h ⊢
        cases he : enter child with
        | done result =>
          rw [he] at h
          exact afterChild_mono (r := r) (child := child) (p := p) (pc := pc)
            (x := some result) (fun run hx => ih run hm hx) h
        | run cr =>
          simp only [he] at h
          dsimp only
          cases hc : (execFueled cr fuel).run with
          | none => rw [hc] at h; contradiction
          | some c =>
            rw [hc] at h
            rw [ih cr hm hc]
            exact afterChild_mono (r := r) (child := child) (p := p) (pc := pc)
              (x := some (c >>= settle child)) (fun run hx => ih run hm hx) h

theorem execFueled_run_of_lt {r : Frame.Running} {fuel : Nat} (h : r.state.machine.gasMeasure < fuel) :
    (execFueled r fuel).run = some (exec r) :=
  execFueled_run_mono _ r h (execFueled_run_sufficientFuel r)

theorem exec_eq_of_run {r : Frame.Running} {fuel : Nat} {raw : Except Fault Frame.Exit}
    (h : r.state.machine.gasMeasure < fuel) (hr : (execFueled r fuel).run = some raw) : exec r = raw := by
  rw [execFueled_run_of_lt h] at hr
  exact Option.some.inj hr

end Jaune.Checked
