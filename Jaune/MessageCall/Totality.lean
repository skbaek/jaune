import Jaune.MessageCall.StepGas
import Jaune.MessageCall.Exec

/-!
# Totality of the staged driver (goal `jaune-shape-and-names-v1`, W1 unit G)

The staged `execFueled` (`Jaune.MessageCall.Driver`) never reports fuel exhaustion when it is
seeded with more fuel than the frame's gas measure, so the staged `exec`
(`Jaune.MessageCall.Exec`) never takes its invariant branch. This is today's argument from
`Jaune.Sufficiency` over the staged pieces:

* a step owes `Step.GasBound` (`Jaune.MessageCall.StepGas`);
* `enter` hands a running child exactly its message's gas, and a child settled at once reports
  at most that;
* `settle` turns a raw result that owes `Execution.SettledGasLe n` into a result measuring at
  most `n`;
* `resume` hands the caller back at most its checkpoint's measure plus the result's.

Staged under a namespace of its own until the switch commit, which gave it its final names.
-/

namespace Jaune

open Jaune

/-! ## Settling a finished frame -/

/-- A frame result's gas measure: what its caller can absorb, its execution gas and its
state-gas spill. -/
def Frame.Result.gasMeasure (r : Frame.Result) : Nat :=
  r.gasLeft + r.stateGas.spilled + r.stateGas.committedSpill

/-- The measure of the state a halt-typed computation ends in, on either branch. -/
def haltGas : Except (ExceptionalHalt × Devm) Devm → Nat
  | .ok d => d.gasMeasure
  | .error (_, d) => d.gasMeasure

private theorem chargeGas_haltGas (c : Nat) (d : Devm) :
    haltGas (Devm.chargeGas c d) ≤ d.gasMeasure := by
  have hm := Devm.gasMeasure_eq d
  by_cases hle : c ≤ d.gasLeft
  · simp only [Devm.chargeGas, safeSub, hle, ↓reduceIte, haltGas, Devm.withGasLeft_gasMeasure]
    omega
  · simp only [Devm.chargeGas, safeSub, hle, ↓reduceIte, haltGas]
    exact Nat.le_refl _

private theorem chargeStateGas_haltGas (a : Nat) (d : Devm) :
    haltGas (Devm.chargeStateGas a d) ≤ d.gasMeasure := by
  unfold Devm.chargeStateGas
  split
  · simp only [haltGas, Devm.gasMeasure, Mach.gasMeasure]
    exact Nat.le_refl _
  · split
    · simp only [haltGas, Devm.setMach_gasMeasure]
      simp only [Mach.gasMeasure, Devm.gasMeasure]
      omega
    · exact Nat.le_refl _

private theorem haltGas_bind {n : Nat} {e : Except (ExceptionalHalt × Devm) Devm}
    {f : Devm → Except (ExceptionalHalt × Devm) Devm} (he : haltGas e ≤ n)
    (hf : ∀ d, d.gasMeasure ≤ n → haltGas (f d) ≤ n) : haltGas (e >>= f) ≤ n := by
  cases e with
  | error p => exact he
  | ok d => exact hf d he

private theorem chargeDeposit_haltGas (rules : ForkRules) (code : Bytes) (d : Devm) :
    haltGas (chargeDeposit rules code d) ≤ d.gasMeasure := by
  have chargeThenSize : ∀ c : Bytes, haltGas
      (Devm.chargeGas (c.length * Gas.codeDeposit) d >>= fun d =>
        if rules.code.maxCodeSize < c.length then .error (.outOfGas .none, d)
        else .ok d) ≤ d.gasMeasure := by
    intro c
    refine haltGas_bind (chargeGas_haltGas _ _) (fun d' h' => ?_)
    split <;> exact h'
  unfold chargeDeposit
  dsimp only
  repeat' split
  all_goals first
    | exact Nat.le_refl d.gasMeasure
    | exact haltGas_bind (chargeGas_haltGas _ _) (fun d' h' => h')
    | exact haltGas_bind (chargeGas_haltGas _ _)
        (fun d' h' => Nat.le_trans (chargeStateGas_haltGas _ _) h')

private theorem depositCode_haltGas (rules : ForkRules) (recipient : Address) (code : Bytes)
    (d : Devm) : haltGas (depositCode rules recipient code d) ≤ d.gasMeasure := by
  have h := chargeDeposit_haltGas rules code d
  unfold depositCode
  cases hc : chargeDeposit rules code d with
  | error p => rw [hc] at h; exact h
  | ok s =>
    rw [hc] at h
    simp only [Except.map, haltGas, Devm.setCode_gasMeasure]
    exact h

/-- A state's spill is part of its measure. -/
private theorem stateGas_le (d : Devm) :
    0 + d.stateGas.spilled + d.stateGas.committedSpill ≤ d.gasMeasure := by
  have h := Devm.spill_le_gasMeasure d
  simp only [Devm.spill] at h
  show 0 + d.mach.stateGas.spilled + d.mach.stateGas.committedSpill ≤ d.gasMeasure
  omega

/-- A state's spill is part of its measure. -/
private theorem stateGas_spill_le (d : Devm) :
    d.mach.stateGas.spilled + d.mach.stateGas.committedSpill ≤ d.gasMeasure := by
  have := Devm.spill_le_gasMeasure d
  simpa only [Devm.spill] using this

/-- **Settlement bound.** A raw result that owes `SettledGasLe n` settles to a result measuring
at most `n`, whatever the frame. -/
theorem settle_gasLe {f : Frame} {raw : Execution} {n : Nat} {r : Frame.Result}
    (hraw : raw.SettledGasLe n) (h : settle f raw = .ok r) : r.gasMeasure ≤ n := by
  unfold settle at h
  dsimp only at h
  split at h
  · nomatch h
  · nomatch h
  · rename_i d
    simp only [Except.ok.injEq] at h
    subst h
    cases hs : f.message.context.block.rules.stateGas with
    | none =>
      have : d.gasMeasure ≤ n := hraw.1
      simp only [Devm.gasMeasure, Mach.gasMeasure] at this
      simp only [Frame.Result.gasMeasure, Frame.Result.gasLeft, Frame.Result.stateGas]
      exact this
    | some state =>
      have : d.restoreStateGas.gasMeasure ≤ n := hraw.2
      simp only [Devm.gasMeasure, Mach.gasMeasure] at this
      simp only [Frame.Result.gasMeasure, Frame.Result.gasLeft, Frame.Result.stateGas]
      exact this
  · rename_i reason d
    simp only [Except.ok.injEq] at h
    subst h
    cases hs : f.message.context.block.rules.stateGas with
    | none =>
      have : (d.withGasLeft 0).gasMeasure ≤ n := hraw.1
      simp only [Frame.Result.gasMeasure, Frame.Result.gasLeft, Frame.Result.stateGas]
      exact Nat.le_trans (stateGas_le _) this
    | some state =>
      have : d.restoreStateGas.forfeitRemainingGas.gasMeasure ≤ n := hraw.2
      simp only [Frame.Result.gasMeasure, Frame.Result.gasLeft, Frame.Result.stateGas]
      exact Nat.le_trans (stateGas_le _) this
  · rename_i d
    have hd : d.gasMeasure ≤ n := hraw
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact hd
    · have hdep := depositCode_haltGas f.message.context.block.rules
        f.message.context.recipient
        (d.recordTouch f.message.context.block.rules true f.message.context.recipient).output
        (d.recordTouch f.message.context.block.rules true f.message.context.recipient)
      rw [Devm.recordTouch_gasMeasure] at hdep
      split at h
      · rename_i s hs
        simp only [Except.ok.injEq] at h
        subst h
        rw [hs] at hdep
        exact Nat.le_trans hdep hd
      · rename_i reason s hs
        simp only [Except.ok.injEq] at h
        subst h
        rw [hs] at hdep
        simp only [haltGas] at hdep
        simp only [Frame.Result.gasMeasure, Frame.Result.gasLeft, Frame.Result.stateGas]
        refine Nat.le_trans ?_ (Nat.le_trans hdep hd)
        split
        · have h1 := stateGas_le (s.withGasLeft 0)
          rw [Devm.withGasLeft_gasMeasure] at h1
          have h2 := Devm.spill_le_gasMeasure s
          omega
        · have h1 := stateGas_le s.restoreStateGas.forfeitRemainingGas
          have h2 := Devm.restoreStateGas_forfeitRemainingGas_gasMeasure_le_spill s
          have h3 := Devm.spill_le_gasMeasure s
          omega

/-! ## Entering a frame -/

/-- A running child starts with exactly its message's gas. -/
theorem enter_run_gasMeasure {f : Frame} {evm : Evm} (h : enter f = .run evm) :
    evm.dyna.gasMeasure = f.message.gas := by
  unfold enter enterWith at h
  dsimp only at h
  split at h
  · nomatch h
  · split at h
    · split at h
      · nomatch h
      · simp only [Frame.Entry.run.injEq] at h
        subst h
        rfl
    · simp only [Frame.Entry.run.injEq] at h
      subst h
      rfl

/-- A child settled at once (a precompile) reports at most its message's gas. -/
theorem enter_done_gasLe {f : Frame} {r : Frame.Result} (h : enter f = .done (.ok r)) :
    r.gasMeasure ≤ f.message.gas := by
  unfold enter enterWith at h
  dsimp only at h
  split at h
  · simp only [Frame.Entry.done.injEq] at h
    nomatch h
  · split at h
    · split at h
      · rename_i world _ address _ _
        simp only [Frame.Entry.done.injEq] at h
        refine settle_gasLe (Execution.settledGasLe_of_gasLe ?_) h
        exact Nat.le_trans (executePrecompile_gasLe _ _) (Nat.le_of_eq rfl)
      · nomatch h
    · nomatch h

/-! ## Resuming the caller -/

private theorem creditStateGasRefund_measure (a : Nat) (m : Machine) :
    (m.creditStateGasRefund a).gasLeft + (m.creditStateGasRefund a).stateGas.spilled
        + (m.creditStateGasRefund a).stateGas.committedSpill
      = m.gasLeft + m.stateGas.spilled + m.stateGas.committedSpill := by
  simp only [Machine.creditStateGasRefund]
  omega

private theorem repayStateGasSpill_measure (m : Machine) :
    m.repayStateGasSpill.gasLeft + m.repayStateGasSpill.stateGas.spilled
        + m.repayStateGasSpill.stateGas.committedSpill
      = m.gasLeft + m.stateGas.spilled + m.stateGas.committedSpill := by
  simp only [Machine.repayStateGasSpill]
  omega

private theorem absorbMeters_measure (rules : ForkRules) (p : Pending) (saved : Machine)
    (r : Frame.Result) :
    (absorbMeters rules p saved r).gasLeft + (absorbMeters rules p saved r).stateGas.spilled
        + (absorbMeters rules p saved r).stateGas.committedSpill
      ≤ saved.gasLeft + saved.stateGas.spilled + saved.stateGas.committedSpill
          + r.gasMeasure := by
  unfold absorbMeters Frame.Result.gasMeasure
  dsimp only
  split
  · dsimp only
    omega
  · split
    · split
      · rw [creditStateGasRefund_measure]
        dsimp only
        omega
      · dsimp only
        omega
    · rw [repayStateGasSpill_measure]
      dsimp only
      omega

private theorem Pending.restore_gasMeasure (p : Pending) (s : Frame.State) :
    (p.restore s).gasMeasure = s.gasMeasure := rfl

private theorem ReturnTarget.finish_gasLeft (target : ReturnTarget) (r : Frame.Result)
    (m : Machine) : (target.finish r m).gasLeft = m.gasLeft := by
  cases target <;> rfl

private theorem ReturnTarget.finish_stateGas (target : ReturnTarget) (r : Frame.Result)
    (m : Machine) : (target.finish r m).stateGas = m.stateGas := by
  cases target <;> rfl

/-- **Resume bound.** The caller comes back, resumed or halted, with at most its checkpoint's
measure plus the result's. -/
theorem resume_gasLe {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Devm) Devm}
    (h : resume rules p saved r = .ok x) :
    haltGas x ≤ saved.gasMeasure + r.gasMeasure := by
  have hm := absorbMeters_measure rules p saved.machine r
  unfold resume at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (simp only [Except.ok.injEq] at h
       subst h
       simp only [haltGas, Pending.restore_gasMeasure, Frame.State.gasMeasure,
         ReturnTarget.finish_gasLeft, ReturnTarget.finish_stateGas]
       omega)
    | cases h

/-! ## The driver

As today: monotonicity first (a child that ran to completion hands back no more than it was
given), then sufficiency, both by structural induction on the fuel. -/

/-- The spawn branch of the driver, once the child's settled result `x` is known. -/
private theorem spawn_settledGasLe {fuel : Nat} {evm : Evm} {child : Frame}
    {pending : Pending} {pc : Nat} {x : Option (Except Fault Frame.Result)} {raw : Execution}
    (ih : ∀ (evm : Evm) {raw : Execution},
      (execFueled evm fuel).run = some raw → raw.SettledGasLe evm.dyna.gasMeasure)
    (hlt : child.message.gas + child.parentGas < evm.dyna.gasMeasure)
    (hx : ∀ r, x = some (.ok r) → r.gasMeasure ≤ child.message.gas)
    (h : (match x with
      | none => Fueled.exhausted
      | some (.error fault) =>
        Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
      | some (.ok result) =>
        match resume evm.sta.benvStat.rules pending child.checkpoint result with
        | .error fault =>
          Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
        | .ok (.error (reason, devm)) => Fueled.ofExcept (.error (.halt reason, devm))
        | .ok (.ok devm) => execFueled ⟨pc, evm.sta, devm⟩ fuel).run = some raw) :
    raw.SettledGasLe evm.dyna.gasMeasure := by
  have hcp : child.checkpoint.toDevm.gasMeasure < evm.dyna.gasMeasure := by
    rw [Frame.State.toDevm_gasMeasure]
    unfold Frame.parentGas at hlt
    omega
  rcases x with _ | fault | result
  · simp only [Fueled.exhausted_run] at h
    nomatch h
  · simp only [Fueled.ofExcept_run, Option.some.injEq] at h
    subst h
    exact Execution.settledGasLe_of_gasLe (Nat.le_of_lt hcp)
  · have hr := hx result rfl
    dsimp only at h
    rcases hres : resume evm.sta.benvStat.rules pending child.checkpoint result with
        fault | ⟨reason, devm⟩ | devm <;> rw [hres] at h <;> dsimp only at h
    · simp only [Fueled.ofExcept_run, Option.some.injEq] at h
      subst h
      exact Execution.settledGasLe_of_gasLe (Nat.le_of_lt hcp)
    · simp only [Fueled.ofExcept_run, Option.some.injEq] at h
      subst h
      have hg := resume_gasLe hres
      simp only [haltGas] at hg
      unfold Frame.parentGas at hlt
      exact Execution.settledGasLe_of_gasLe (by simp only [Execution.gasMeasure_error]; omega)
    · have hg := resume_gasLe hres
      simp only [haltGas] at hg
      unfold Frame.parentGas at hlt
      exact (ih _ h).mono (show devm.gasMeasure ≤ evm.dyna.gasMeasure by omega)

/-- Driver monotonicity, over the settlement obligation, as today. -/
theorem execFueled_settledGasLe : ∀ (fuel : Nat) (evm : Evm) {raw : Execution},
    (execFueled evm fuel).run = some raw →
      raw.SettledGasLe evm.dyna.gasMeasure := by
  intro fuel
  induction fuel with
  | zero =>
    intro evm raw h
    rw [execFueled] at h
    simp only [Fueled.exhausted_run] at h
    nomatch h
  | succ fuel ih =>
    intro evm raw h
    have hstep := Evm.step_gasBound evm
    rw [execFueled] at h
    rcases hs : Evm.step evm with ex | ⟨pc, devm⟩ | ⟨child, pending, pc⟩
    · rw [hs] at h hstep
      simp only [Fueled.ofExcept_run, Option.some.injEq] at h
      rw [← h]
      exact hstep
    · rw [hs] at h hstep
      simp only [Step.GasBound] at hstep
      exact (ih _ h).mono (Nat.le_of_lt hstep)
    · rw [hs] at h hstep
      simp only [Step.GasBound] at hstep
      obtain ⟨hstep, -⟩ := hstep
      dsimp only at h
      refine spawn_settledGasLe ih hstep ?_ h
      intro r hr
      rcases he : enter child with childEvm | result <;> rw [he] at hr <;> dsimp only at hr
      · rcases hc : (execFueled childEvm fuel).run with _ | raw' <;> rw [hc] at hr
        · nomatch hr
        · simp only [Option.map, Option.some.injEq] at hr
          have hchild := ih childEvm hc
          rw [enter_run_gasMeasure he] at hchild
          exact settle_gasLe hchild hr
      · simp only [Option.some.injEq] at hr
        subst hr
        exact enter_done_gasLe he

/-- The spawn branch of the driver reaches a result once the child's settled result is known. -/
private theorem spawn_isSome {fuel : Nat} {evm : Evm} {child : Frame}
    {pending : Pending} {pc : Nat} {x : Option (Except Fault Frame.Result)}
    (ih : ∀ evm : Evm, evm.dyna.gasMeasure < fuel →
      ∃ raw : Execution, (execFueled evm fuel).run = some raw)
    (hlt : child.message.gas + child.parentGas < fuel)
    (hsome : x.isSome)
    (hx : ∀ r, x = some (.ok r) → r.gasMeasure ≤ child.message.gas) :
    ∃ raw : Execution, (match x with
      | none => Fueled.exhausted
      | some (.error fault) =>
        Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
      | some (.ok result) =>
        match resume evm.sta.benvStat.rules pending child.checkpoint result with
        | .error fault =>
          Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
        | .ok (.error (reason, devm)) => Fueled.ofExcept (.error (.halt reason, devm))
        | .ok (.ok devm) => execFueled ⟨pc, evm.sta, devm⟩ fuel).run = some raw := by
  rcases x with _ | fault | result
  · nomatch hsome
  · exact ⟨_, rfl⟩
  · have hr := hx result rfl
    dsimp only
    rcases hres : resume evm.sta.benvStat.rules pending child.checkpoint result with
        fault | ⟨reason, devm⟩ | devm <;> dsimp only
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · have hg := resume_gasLe hres
      simp only [haltGas] at hg
      unfold Frame.parentGas at hlt
      exact ih _ (show devm.gasMeasure < fuel by omega)

/-- **Sufficiency.** Fuel strictly greater than the frame's measure always carries the staged
driver to a result. -/
theorem execFueled_run_isSome : ∀ (fuel : Nat) (evm : Evm),
    evm.dyna.gasMeasure < fuel →
      ∃ raw : Execution, (execFueled evm fuel).run = some raw := by
  intro fuel
  induction fuel with
  | zero =>
    intro evm h
    omega
  | succ fuel ih =>
    intro evm h
    have hstep := Evm.step_gasBound evm
    rw [execFueled]
    rcases hs : Evm.step evm with ex | ⟨pc, devm⟩ | ⟨child, pending, pc⟩ <;>
      rw [hs] at hstep <;> simp only [Step.GasBound] at hstep <;> dsimp only
    · exact ⟨ex, rfl⟩
    · exact ih _ (show devm.gasMeasure < fuel by omega)
    · obtain ⟨hstep, -⟩ := hstep
      have hlt : child.message.gas + child.parentGas < fuel := by omega
      rcases he : enter child with childEvm | result
      · have hgas := enter_run_gasMeasure he
        obtain ⟨raw', hraw'⟩ := ih childEvm (by unfold Frame.parentGas at hlt; omega)
        refine spawn_isSome ih hlt ?_ ?_
        · simp only [hraw', Option.map, Option.isSome]
        · intro r hr
          simp only [hraw', Option.map, Option.some.injEq] at hr
          have hchild := execFueled_settledGasLe fuel childEvm hraw'
          rw [hgas] at hchild
          exact settle_gasLe hchild hr
      · refine spawn_isSome ih hlt rfl ?_
        intro r hr
        simp only [Option.some.injEq] at hr
        subst hr
        exact enter_done_gasLe he

theorem execFueled_ne_exhausted (evm : Evm) (fuel : Nat)
    (h : evm.dyna.gasMeasure < fuel) :
    execFueled evm fuel ≠ Fueled.exhausted := by
  obtain ⟨raw, hraw⟩ := execFueled_run_isSome fuel evm h
  intro hcon
  rw [hcon] at hraw
  simp only [Fueled.exhausted_run] at hraw
  nomatch hraw

/-- Seeding the staged driver with `gasMeasure + 1` is always enough. -/
theorem execFueled_succ_ne_exhausted (evm : Evm) :
    execFueled evm (evm.dyna.gasMeasure + 1) ≠ Fueled.exhausted :=
  execFueled_ne_exhausted evm (evm.dyna.gasMeasure + 1) (Nat.lt_succ_self _)

/-! ## The total interpreter -/

theorem execFueled_run_sufficientFuel_isSome (evm : Evm) :
    ((execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run).isSome := by
  obtain ⟨raw, hraw⟩ :=
    execFueled_run_isSome (sufficientFuel evm.dyna.gasMeasure) evm
      (Nat.lt_succ_self _)
  rw [hraw]
  rfl

/-- **Bridge equation.** The staged driver at the seeded budget returns exactly the staged
total result. -/
theorem execFueled_run_sufficientFuel (evm : Evm) :
    (execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run = some (exec evm) := by
  obtain ⟨raw, hraw⟩ :=
    execFueled_run_isSome (sufficientFuel evm.dyna.gasMeasure) evm
      (Nat.lt_succ_self _)
  rw [hraw]
  unfold exec
  rw [hraw]

/-- The staged `exec`'s invariant branch is unreachable: it is the staged driver's own answer,
so it never returns the fuel-exhaustion fault. -/
theorem exec_ok (evm : Evm) :
    ∃ raw, (execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run = some raw
      ∧ exec evm = raw :=
  ⟨exec evm, execFueled_run_sufficientFuel evm, rfl⟩

/-- The spawn branch of the driver keeps its result under more fuel. -/
private theorem spawn_mono {fuel m : Nat} {evm : Evm} {child : Frame}
    {pending : Pending} {pc : Nat} {x : Option (Except Fault Frame.Result)} {raw : Execution}
    (ih : ∀ (evm : Evm) {raw : Execution},
      (execFueled evm fuel).run = some raw → (execFueled evm m).run = some raw)
    (h : (match x with
      | none => Fueled.exhausted
      | some (.error fault) =>
        Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
      | some (.ok result) =>
        match resume evm.sta.benvStat.rules pending child.checkpoint result with
        | .error fault =>
          Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
        | .ok (.error (reason, devm)) => Fueled.ofExcept (.error (.halt reason, devm))
        | .ok (.ok devm) => execFueled ⟨pc, evm.sta, devm⟩ fuel).run = some raw) :
    (match x with
      | none => Fueled.exhausted
      | some (.error fault) =>
        Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
      | some (.ok result) =>
        match resume evm.sta.benvStat.rules pending child.checkpoint result with
        | .error fault =>
          Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
        | .ok (.error (reason, devm)) => Fueled.ofExcept (.error (.halt reason, devm))
        | .ok (.ok devm) => execFueled ⟨pc, evm.sta, devm⟩ m).run = some raw := by
  rcases x with _ | fault | result
  · simp only [Fueled.exhausted_run] at h
    nomatch h
  · exact h
  · dsimp only at h ⊢
    rcases hres : resume evm.sta.benvStat.rules pending child.checkpoint result with
        fault | ⟨reason, devm⟩ | devm <;> rw [hres] at h <;> dsimp only at h ⊢
    · exact h
    · exact h
    · exact ih _ h

/-- More fuel never changes a result the staged driver already reached. -/
theorem execFueled_run_mono :
    ∀ (fuel : Nat) (evm : Evm) {fuel' : Nat} {raw : Execution}, fuel ≤ fuel' →
      (execFueled evm fuel).run = some raw → (execFueled evm fuel').run = some raw := by
  intro fuel
  induction fuel with
  | zero =>
    intro evm fuel' raw _ h
    rw [execFueled] at h
    simp only [Fueled.exhausted_run] at h
    nomatch h
  | succ fuel ih =>
    intro evm fuel' raw hle h
    obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := by
      cases fuel' with
      | zero => omega
      | succ m => exact ⟨m, rfl⟩
    have hle' : fuel ≤ m := by omega
    rw [execFueled] at h
    rw [execFueled]
    rcases hs : Evm.step evm with ex | ⟨pc, devm⟩ | ⟨child, pending, pc⟩ <;>
      rw [hs] at h <;> dsimp only at h ⊢
    · exact h
    · exact ih _ hle' h
    · rcases he : enter child with childEvm | result <;> rw [he] at h <;> dsimp only at h ⊢
      · rcases hc : (execFueled childEvm fuel).run with _ | raw'
        · rw [hc] at h
          simp only [Option.map, Fueled.exhausted_run] at h
          nomatch h
        · rw [hc] at h
          rw [ih _ hle' hc]
          exact spawn_mono (fun e _ he' => ih e hle' he') h
      · exact spawn_mono (fun e _ he' => ih e hle' he') h

/-- The staged driver at an arbitrary sufficient budget. -/
theorem execFueled_run_of_lt {evm : Evm} {fuel : Nat} (h : evm.dyna.gasMeasure < fuel) :
    (execFueled evm fuel).run = some (exec evm) :=
  execFueled_run_mono _ evm h (execFueled_run_sufficientFuel evm)

/-- Reading a fueled result off as the total one. -/
theorem exec_eq_of_run {evm : Evm} {fuel : Nat} {raw : Execution}
    (hlt : evm.dyna.gasMeasure < fuel)
    (h : (execFueled evm fuel).run = some raw) :
    exec evm = raw := by
  rw [execFueled_run_of_lt hlt] at h
  exact Option.some.inj h

end Jaune

