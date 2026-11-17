import Jaune.Bridge.Step
import Jaune.MessageCall.Resume

/-!
# `resume`, today's and the staged one (W1 unit E, bridge)

Today's `Resume.run` merges a settled child `Devm` into the saved caller; the staged `resume`
merges a `Frame.Result`. `resume_legacy` says the two agree, observed with a fault's state
erased, for every child coherent with its saved caller, every `Resume` the rules select, and
every clean raw result.

The proof goes through what today's settlement guarantees of its result
(`Legacy.SettledFacts`): it faults only with a cryptographic or internal reason; a failed result
has the saved caller's world, under state gas no refund, and after a halt no gas and no output.

About today's definitions, and deleted with them after the gate's tag (the W1 design note, third
revision, section 3.2, unit E).
-/

namespace Jaune

/-- Today's raw result with a fault's state erased: what the staged driver can reproduce. -/
def Execution.observe : Execution → Except Staging.Fault Execution
  | .error (.crypto reason, _) => .error (.crypto reason)
  | .error (.internal reason, _) => .error (.internal reason)
  | ex => .ok ex

namespace Legacy

/-- What today's settlement guarantees of a settled result, relative to the saved caller
`parent` and the rules. -/
structure SettledFacts (parent : Devm) (rules : ForkRules)
    (s : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm) : Prop where
  /-- It faults only with a cryptographic or internal reason. -/
  fault : ∀ {e st c t}, s = .error (e, st, c, t) → (∃ r, e = .crypto r) ∨ (∃ r, e = .internal r)
  /-- A failed result has the saved caller's world. -/
  world : ∀ {d}, s = .ok d → d.error.isSome → d.world = parent.world
  /-- Under state gas a failed result has no refund. -/
  refund : ∀ {d}, s = .ok d → d.error.isSome → rules.stateGas.isSome → d.refundCounter = 0
  /-- A halted result has no gas and no output. -/
  halted : ∀ {d reason}, s = .ok d → d.error = some (.halt reason) → d.gasLeft = 0 ∧ d.output = []

end Legacy

end Jaune

namespace Jaune.Staging
open Legacy

/-- `throw` in `Except`. -/
theorem throw_except {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl

set_option hygiene false in
/-- The simp set that evaluates both sides of a resume on concrete records. -/
macro "resume_simp" : tactic => `(tactic| simp [hst, throw_except, Devm.error, Resume.run,
      liftToExecution, Frame.Result.ofSettled, resume, hm, absorbMeters,
      Devm.push_def, Except.assert, bind, Except.bind, pure, Except.pure,
      Frame.Result.ofSuccess, Frame.State.ofDevm, Pending.ofLegacy, Frame.Result.failed,
      incorporateChildOnSuccess, incorporateChildOnError, Substate.keepTouch,
      incorporateChildAmsterdamOnSuccess, incorporateChildAmsterdamOnError,
      Devm.AmsterdamFailedChildSettled, Devm.AmsterdamChildUncommitted, Devm.stateGasLeft,
      Devm.creditStateGasRefund, Mach.creditStateGasRefund, Machine.creditStateGasRefund,
      Mach.repayStateGasSpill, Machine.repayStateGasSpill, Frame.Result.stateGas,
      Execution.observe, ofHalting, Except.map, Devm.setMach,
      Devm.setMeta, Devm.setWorld, Devm.stack, Devm.gasLeft, Devm.memWrite, liftMachPure,
      Mach.memWrite, ReturnTarget.finish, ReturnTarget.status, Pending.restore,
      Frame.State.toDevm, Substate.absorb, Trail.absorb, Devm.logs, Devm.refundCounter,
      Devm.accountsToDelete, Devm.accessedAddresses, Devm.accessedStorageKeys,
      Devm.createdAccounts, Devm.output, Devm.state, Devm.transientStorage, Devm.stateGas,
      Devm.memory, Frame.Result.output, Frame.Result.gasLeft, Frame.Result.trail])

set_option hygiene false in
/-- The same, with the three meter cases of the state-gas walk. -/
macro "resume_simp_ams" : tactic => `(tactic| simp [hst, h1, h2, h3, throw_except, Devm.error,
      Resume.run, liftToExecution, Frame.Result.ofSettled, resume, hm, absorbMeters,
      Devm.push_def, Except.assert, bind, Except.bind, pure, Except.pure,
      Frame.Result.ofSuccess, Frame.State.ofDevm, Pending.ofLegacy, Frame.Result.failed,
      incorporateChildOnSuccess, incorporateChildOnError, Substate.keepTouch,
      incorporateChildAmsterdamOnSuccess, incorporateChildAmsterdamOnError,
      Devm.AmsterdamFailedChildSettled, Devm.AmsterdamChildUncommitted, Devm.stateGasLeft,
      Devm.creditStateGasRefund, Mach.creditStateGasRefund, Machine.creditStateGasRefund,
      Mach.repayStateGasSpill, Machine.repayStateGasSpill, Frame.Result.stateGas,
      Execution.observe, ofHalting, Except.map, Devm.setMach,
      Devm.setMeta, Devm.setWorld, Devm.stack, Devm.gasLeft, Devm.memWrite, liftMachPure,
      Mach.memWrite, ReturnTarget.finish, ReturnTarget.status, Pending.restore,
      Frame.State.toDevm, Substate.absorb, Trail.absorb, Devm.logs, Devm.refundCounter,
      Devm.accountsToDelete, Devm.accessedAddresses, Devm.accessedStorageKeys,
      Devm.createdAccounts, Devm.output, Devm.state, Devm.transientStorage, Devm.stateGas,
      Devm.memory, Frame.Result.output, Frame.Result.gasLeft, Frame.Result.trail])

set_option hygiene false in
/-- The ok-case walk: destructure the saved caller and the child, take the settlement facts,
split on the child's stored error and the stack bound. -/
macro "resume_walk" hf:ident : tactic => `(tactic| (
  rcases s with ⟨e, st, c, t⟩ | d
  · obtain ⟨r, rfl⟩ | ⟨r, rfl⟩ := SettledFacts.fault $hf rfl <;> rfl
  · have hw := fun h => SettledFacts.world $hf (d := d) rfl h
    have hh := fun {reason} h => SettledFacts.halted $hf (d := d) (reason := reason) rfl h
    have hr := fun h => SettledFacts.refund $hf (d := d) rfl h
    clear $hf:ident
    rcases parent with ⟨⟨ps, pm, pg, psg⟩, ⟨pl, pr, po, pdel, prd, perr, paa, pak, pca, par, psr,
      pta⟩, pw⟩
    rcases d with ⟨⟨ds, dm, dg, dsg⟩, ⟨dl, dr, dout, ddel, drd, derr, daa, dak, dca, dar, dsr,
      dta⟩, dw⟩
    simp only [Devm.error, Devm.gasLeft, Devm.output, Devm.refundCounter] at hw hh hr
    rcases derr with _ | (reason | _)
    · by_cases hst : ps.length < 1024 <;> resume_simp
    · obtain ⟨rfl, rfl⟩ := hh rfl
      have := hw rfl; subst this
      by_cases hst : ps.length < 1024 <;> resume_simp
    · have := hw rfl; subst this
      by_cases hst : ps.length < 1024 <;> resume_simp))

set_option hygiene false in
/-- The ok-case walk under state gas: as `resume_walk`, also splitting on the spawn's charge
and on the three conditions of the settled-child assertions. -/
macro "resume_walk_ams" hf:ident : tactic => `(tactic| (
  rcases s with ⟨e, st, c, t⟩ | d
  · obtain ⟨r, rfl⟩ | ⟨r, rfl⟩ := SettledFacts.fault $hf rfl <;> rfl
  · have hw := fun h => SettledFacts.world $hf (d := d) rfl h
    have hh := fun {reason} h => SettledFacts.halted $hf (d := d) (reason := reason) rfl h
    have hr := fun h => SettledFacts.refund $hf (d := d) rfl h
    clear $hf:ident
    rcases parent with ⟨⟨ps, pm, pg, psg⟩, ⟨pl, pr, po, pdel, prd, perr, paa, pak, pca, par, psr,
      pta⟩, pw⟩
    rcases d with ⟨⟨ds, dm, dg, dsg⟩, ⟨dl, dr, dout, ddel, drd, derr, daa, dak, dca, dar, dsr,
      dta⟩, dw⟩
    simp only [Devm.error, Devm.gasLeft, Devm.output, Devm.refundCounter] at hw hh hr
    rcases dsg with ⟨sl, sb, ssp, scs⟩
    have hr' := fun h => hr h (by rw [hm]; rfl)
    cases charged <;> by_cases h1 : scs = 0 <;> by_cases h2 : ssp = 0 <;> by_cases h3 : sl = sb <;>
    rcases derr with _ | (reason | _)
    all_goals first
      | (have := hr' rfl; subst this; have := hw rfl; subst this; obtain ⟨rfl, rfl⟩ := hh rfl)
      | (have := hr' rfl; subst this; have := hw rfl; subst this)
      | skip
    all_goals by_cases hst : ps.length < 1024 <;> resume_simp_ams))

theorem resume_core_call (parent : Devm) (oi os : Nat) (rules : ForkRules)
    (hm : rules.stateGas = none)
    (s : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm)
    (hf : SettledFacts parent rules s) :
    ((Resume.call parent oi os).run s).observe
      = (Frame.Result.ofSettled s >>=
          resume rules (Pending.ofLegacy (.call parent oi os)) (Frame.State.ofDevm parent)).map
          ofHalting := by
  resume_walk hf

theorem resume_core_create (parent : Devm) (a : Address) (rules : ForkRules)
    (hm : rules.stateGas = none)
    (s : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm)
    (hf : SettledFacts parent rules s) :
    ((Resume.create parent a).run s).observe
      = (Frame.Result.ofSettled s >>=
          resume rules (Pending.ofLegacy (.create parent a)) (Frame.State.ofDevm parent)).map
          ofHalting := by
  resume_walk hf

theorem resume_core_callAmsterdam (state : StateGasRules) (parent : Devm) (oi os : Nat)
    (charged : Bool) (rules : ForkRules) (hm : rules.stateGas = some state)
    (s : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm)
    (hf : SettledFacts parent rules s) :
    ((Resume.callAmsterdam state parent oi os charged).run s).observe
      = (Frame.Result.ofSettled s >>=
          resume rules (Pending.ofLegacy (.callAmsterdam state parent oi os charged))
            (Frame.State.ofDevm parent)).map ofHalting := by
  resume_walk_ams hf

theorem resume_core_createAmsterdam (state : StateGasRules) (parent : Devm) (a : Address)
    (charged : Bool) (rules : ForkRules) (hm : rules.stateGas = some state)
    (s : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm)
    (hf : SettledFacts parent rules s) :
    ((Resume.createAmsterdam state parent a charged).run s).observe
      = (Frame.Result.ofSettled s >>=
          resume rules (Pending.ofLegacy (.createAmsterdam state parent a charged))
            (Frame.State.ofDevm parent)).map ofHalting := by
  resume_walk_ams hf

end Jaune.Staging

namespace Jaune.Legacy

/-- Today's raw settlement faults only with a cryptographic or internal reason. -/
theorem handleErrorWith_error {sg : Option StateGasRules} {raw : Execution} {e : EvmError}
    {st : Jaune.State} {c : AdrSet} {t : TransientStorage}
    (h : executeCode.handleErrorWith sg raw = .error (e, st, c, t)) :
    (∃ r, e = .crypto r) ∨ (∃ r, e = .internal r) := by
  unfold executeCode.handleErrorWith at h
  rcases raw with ⟨e0, d0⟩ | d0
  · cases sg <;> cases e0 <;>
      simp [executeCode.handleError, executeCode.handleErrorAmsterdam] at h <;>
      obtain ⟨rfl, -⟩ := h <;> simp
  · cases sg <;> simp [executeCode.handleError, executeCode.handleErrorAmsterdam] at h

/-- `processMessage.settle` passes a fault through. -/
theorem processMessage.settle_error {msg : Msg}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    {x : EvmError × Jaune.State × AdrSet × TransientStorage}
    (h : processMessage.settle msg r = .error x) : r = .error x := by
  cases r with
  | error y => simpa [processMessage.settle, bind, Except.bind] using h
  | ok evm =>
    simp only [processMessage.settle, bind, Except.bind] at h
    split at h <;> cases h

/-- `processCreateMessage.settle` passes a fault through, and adds none: the deposit charge
fails only by halting. -/
theorem processCreateMessage.settle_error {msg : Msg}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    {x : EvmError × Jaune.State × AdrSet × TransientStorage}
    (h : processCreateMessage.settle msg r = .error x) : r = .error x := by
  cases r with
  | error y => simpa [processCreateMessage.settle, bind, Except.bind] using h
  | ok evm =>
    simp only [processCreateMessage.settle, bind, Except.bind] at h
    split at h
    · rw [Staging.chargeCodeGas_legacy] at h
      rcases hc : Staging.chargeDeposit msg.benv.stat.rules evm.output evm with ⟨r, e⟩ | e <;>
        simp [hc, Staging.ofHalting] at h
    · cases h

/-- Today's settlement faults only with a cryptographic or internal reason. -/
theorem Frame.settle_error_isFault (f : Jaune.Frame) (raw : Execution) {e : EvmError}
    {st : Jaune.State} {c : AdrSet} {t : TransientStorage}
    (h : f.settle raw = .error (e, st, c, t)) :
    (∃ r, e = .crypto r) ∨ (∃ r, e = .internal r) := by
  simp only [Jaune.Frame.settle, Jaune.Frame.settleMsg] at h
  apply handleErrorWith_error (sg := f.inner.benv.stat.rules.stateGas) (raw := raw)
  split at h
  · exact processMessage.settle_error (processCreateMessage.settle_error h)
  · exact processMessage.settle_error h

/-- A halt settled by today's raw settlement has no gas and no output. -/
theorem handleErrorWith_ok_halt {sg : Option StateGasRules} {raw : Execution} (clean : raw.Clean)
    {x : Devm} {reason : ExceptionalHalt} (h : executeCode.handleErrorWith sg raw = .ok x)
    (he : x.error = some (.halt reason)) : x.gasLeft = 0 ∧ x.output = [] := by
  unfold executeCode.handleErrorWith at h
  rcases raw with ⟨e0, d0⟩ | d0
  · cases sg <;> cases e0 <;>
      simp [executeCode.handleError, executeCode.handleErrorAmsterdam] at h <;> subst h <;>
      simp_all [Devm.error, Devm.gasLeft, Devm.output, Devm.setMeta, Devm.withGasLeft,
        Devm.setMach, Devm.forfeitRemainingGas, Devm.restoreStateGas, Devm.withRefundCounter,
        Devm.withError, Mach.forfeitRemainingGas, Mach.restoreStateGas]
  · simp only [Execution.Clean] at clean
    cases sg <;> simp [executeCode.handleError, executeCode.handleErrorAmsterdam] at h <;>
      subst h <;> simp_all

/-- `processMessage.settle` keeps the stored error, the gas and the output. -/
theorem processMessage.settle_ok_fields {msg : Msg} {x d : Devm}
    (h : processMessage.settle msg (.ok x) = .ok d) :
    d.error = x.error ∧ d.gasLeft = x.gasLeft ∧ d.output = x.output := by
  simp only [processMessage.settle, bind, Except.bind] at h
  split at h <;> cases h <;> exact ⟨rfl, rfl, rfl⟩

/-- A halt out of `processCreateMessage.settle` is the input's, with its gas and output, or a
failed deposit's, with none. -/
theorem processCreateMessage.settle_ok_halt {msg : Msg} {x d : Devm} {reason : ExceptionalHalt}
    (h : processCreateMessage.settle msg (.ok x) = .ok d) (he : d.error = some (.halt reason)) :
    (x.error = some (.halt reason) ∧ d.gasLeft = x.gasLeft ∧ d.output = x.output) ∨
      (d.gasLeft = 0 ∧ d.output = []) := by
  simp only [processCreateMessage.settle, bind, Except.bind] at h
  split at h
  · rename_i hn
    rw [Staging.chargeCodeGas_legacy] at h
    rcases hc : Staging.chargeDeposit msg.benv.stat.rules x.output x with ⟨r, e⟩ | e
    · rw [hc] at h
      right
      cases hsg : msg.benv.stat.rules.stateGas <;> simp [Staging.ofHalting, hsg] at h <;>
        subst h <;> exact ⟨rfl, rfl⟩
    · rw [hc] at h
      cases h
      have hm := Staging.chargeDeposit_ok_meta hc
      simp only [Devm.error, Devm.setCode, Devm.clearStorageWritesIfEmpty, Devm.withState,
        Devm.withStorageWrites, Devm.setWorld, hm] at he
      simp [Devm.error, he] at hn
  · cases h
    left
    exact ⟨he, rfl, rfl⟩

/-- A halt settled by today's settlement has no gas and no output, given a clean raw result. -/
theorem Frame.settle_halted (f : Jaune.Frame) {raw : Execution} (clean : raw.Clean) {d : Devm}
    {reason : ExceptionalHalt} (hs : f.settle raw = .ok d) (he : d.error = some (.halt reason)) :
    d.gasLeft = 0 ∧ d.output = [] := by
  simp only [Jaune.Frame.settle, Jaune.Frame.settleMsg] at hs
  have inner : ∀ {y : Devm}, processMessage.settle f.inner
      (executeCode.handleErrorWith f.inner.benv.stat.rules.stateGas raw) = .ok y →
      y.error = some (.halt reason) → y.gasLeft = 0 ∧ y.output = [] := by
    intro y hy hye
    cases hx : executeCode.handleErrorWith f.inner.benv.stat.rules.stateGas raw with
    | error _ => rw [hx] at hy; simp [processMessage.settle, bind, Except.bind] at hy
    | ok x =>
      rw [hx] at hy
      obtain ⟨h1, h2, h3⟩ := processMessage.settle_ok_fields hy
      rw [h2, h3]
      exact handleErrorWith_ok_halt clean hx (h1 ▸ hye)
  split at hs
  · obtain ⟨y, hy⟩ := processCreateMessage.settle_ok_input hs
    rw [hy] at hs
    rcases processCreateMessage.settle_ok_halt hs he with ⟨hye, h2, h3⟩ | hfin
    · rw [h2, h3]; exact inner hy hye
    · exact hfin
  · exact inner hs he

/-- What today's settlement guarantees, for a child coherent with its saved caller. -/
theorem settledFacts {f : Jaune.Frame} {parent : Devm} {rules : ForkRules}
    (h : Frame.Coherent f parent) (hr : f.outer.benv.stat.rules = rules) {raw : Execution}
    (clean : raw.Clean) : SettledFacts parent rules (f.settle raw) where
  fault := Frame.settle_error_isFault f raw
  world := fun hs hf => by
    rw [Frame.settle_failed_world f h.paired hs hf, h.state, h.transient, h.storageWrites]
    rfl
  refund := fun hs hf hsg => Frame.settle_failed_refund f h.paired (hr ▸ hsg) clean hs hf
  halted := Frame.settle_halted f clean

end Jaune.Legacy

namespace Jaune.Staging

/-- Today's resumption, observed, is the staged `resume` of the result read by `ofSettled`, for
every settled result with today's settlement guarantees. -/
theorem resume_of_facts {rsm : Resume} {rules : ForkRules} (hm : rsm.Matches rules)
    {s : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    (hf : Legacy.SettledFacts rsm.parent rules s) :
    (rsm.run s).observe
      = (Frame.Result.ofSettled s >>=
          resume rules (Pending.ofLegacy rsm) (Frame.State.ofDevm rsm.parent)).map ofHalting := by
  cases rsm with
  | create parent a => exact resume_core_create parent a rules hm _ hf
  | call parent oi os => exact resume_core_call parent oi os rules hm _ hf
  | createAmsterdam state parent a charged =>
    exact resume_core_createAmsterdam state parent a charged rules hm _ hf
  | callAmsterdam state parent oi os charged =>
    exact resume_core_callAmsterdam state parent oi os charged rules hm _ hf

/-- **Resume.** Today's resumption of a settled child, observed with a fault's state erased, is the
staged `resume` of the child's result read by `ofSettled`, for every child coherent with its
saved caller, every `Resume` the rules select, and every clean raw result. -/
theorem resume_legacy {f : Jaune.Frame} {rsm : Resume} {rules : ForkRules}
    (h : Legacy.Frame.Coherent f rsm.parent) (hm : rsm.Matches rules)
    (hr : f.outer.benv.stat.rules = rules) (raw : Execution) (clean : raw.Clean) :
    (rsm.run (f.settle raw)).observe
      = (Frame.Result.ofSettled (f.settle raw) >>=
          resume rules (Pending.ofLegacy rsm) (Frame.State.ofDevm rsm.parent)).map ofHalting :=
  resume_of_facts hm (Legacy.settledFacts h hr clean)

end Jaune.Staging
