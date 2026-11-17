import Jaune.Bridge.Resume
import Jaune.Bridge.Enter
import Jaune.MessageCall.Exec

/-!
# The four-part message call: the driver bridge (goal `jaune-shape-and-names-v1`, W1 unit F)

Today's driver `execFueled` and the staged one agree on every machine and every fuel, observed
with a fault's state erased (`Execution.observe`). The proof is by induction on fuel from the
step bridge (`step_legacy`, `step_spawn_coherent`), the entry bridge (`enter_legacy`), the
settlement bridge (`settle_legacy`) and the resume bridge's core lemmas. A child's raw result is
clean because a child starts from `initDevm`, which stores no error, and today's driver keeps
the stored error (`Legacy.execFueled_ok_error`).

About today's definitions, and deleted with them after the gate's tag (the W1 design note,
third revision, section 3.2, unit F).
-/

namespace Jaune

namespace Legacy

/-- A child machine that today's entry hands back starts with no stored error. -/
theorem Frame.enter_run_error {f : Jaune.Legacy.Frame} {child : Evm} (h : f.enter = .run child) :
    child.dyna.error = none := by
  rw [Frame.enter_eq_enterFrom] at h
  unfold Frame.enterFrom at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h; rfl
    · split at h
      · cases h
      · cases h; rfl

/-- What today's settlement guarantees holds of every result today's entry settles at once:
a failed value transfer (an assertion fault) and a precompile's settled result. -/
theorem Frame.enter_done_facts {f : Jaune.Legacy.Frame} {parent : Devm} {rules : ForkRules}
    (h : Frame.Coherent f parent) (hr : f.outer.benv.stat.rules = rules)
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    (he : f.enter = .done r) : SettledFacts parent rules r := by
  rw [Frame.enter_eq_enterFrom] at he
  unfold Frame.enterFrom at he
  split at he
  · rename_i e hb
    cases he
    have hfault := Msg.benvAfterTransfer_error hb
    have hs : f.settleMsg (.error e) = .error e := by
      unfold Jaune.Legacy.Frame.settleMsg processMessage.settle processCreateMessage.settle
      split <;> rfl
    rw [hs]
    refine ⟨?_, fun hs _ => (nomatch hs), fun hs _ _ => (nomatch hs), fun hs _ => (nomatch hs)⟩
    intro e' st c t he'
    cases he'
    exact .inr ⟨_, hfault⟩
  · dsimp only at he
    split at he
    · cases he
    · split at he
      · cases he
        apply settledFacts h hr
        show Execution.Clean _
        cases hp : executePrecompile _ _ with
        | error _ => trivial
        | ok d => exact (executePrecompile_ok_error hp).trans rfl
      · cases he

end Legacy

end Jaune

namespace Jaune

open Legacy

/-- The observation forgets nothing settlement reads. -/
theorem settle_observe {f : Frame} {a b : Execution} (h : a.observe = b.observe) :
    settle f a = settle f b := by
  rcases a with ⟨ea, da⟩ | da <;> rcases b with ⟨eb, db⟩ | db
  · cases ea <;> cases eb <;> simp_all [Execution.observe, settle]
  · cases ea <;> simp_all [Execution.observe]
  · cases eb <;> simp_all [Execution.observe]
  · simp_all [Execution.observe]

/-- An observed fault is the staged fault. -/
theorem observe_eq_fault {x : Execution} {fault : Fault} {d : Devm} (h : x.observe = .error fault) :
    x.observe = Execution.observe (.error (fault.toEvmError, d)) := by
  rcases x with ⟨e, d'⟩ | d'
  · cases e <;> cases fault <;> simp_all [Execution.observe, Fault.toEvmError]
  · simp [Execution.observe] at h

/-- An observed result that is not a fault is the result itself. -/
theorem observe_eq_ok {x y : Execution} (h : x.observe = .ok y) : x = y := by
  rcases x with ⟨e, d'⟩ | d'
  · cases e <;> simp_all [Execution.observe]
  · simpa [Execution.observe] using h

/-- **The resume tail.** Once today's resumption and the staged one agree, observed, the two
drivers' continuations agree, given that they agree on every machine at the remaining fuel. -/
theorem execFueled_tail {fuel pc : Nat} {sta : Sevm}
    (ih : ∀ evm : Evm, ((Jaune.Legacy.execFueled evm fuel).run).map Execution.observe
      = ((execFueled evm fuel).run).map Execution.observe)
    (x : Execution) (X : Except Fault Frame.Result) (rules : ForkRules) (p : Pending)
    (saved : Frame.State) (cp : Devm)
    (h : x.observe = (X >>= resume rules p saved).map ofHalting) :
    ((match (generalizing := false) x with
      | .error e => Fueled.ofExcept (.error e)
      | .ok devm => Jaune.Legacy.execFueled ⟨pc, sta, devm⟩ fuel :
        Fueled (EvmError × Devm) Devm).run).map Execution.observe
    = ((match (generalizing := false) some X with
      | none => Fueled.exhausted
      | some (.error fault) => Fueled.ofExcept (.error (fault.toEvmError, cp))
      | some (.ok result) =>
        match (generalizing := false) resume rules p saved result with
        | .error fault => Fueled.ofExcept (.error (fault.toEvmError, cp))
        | .ok (.error (reason, devm)) => Fueled.ofExcept (.error (.halt reason, devm))
        | .ok (.ok devm) => execFueled ⟨pc, sta, devm⟩ fuel :
        Fueled (EvmError × Devm) Devm).run).map Execution.observe := by
  rcases X with fault | result
  · have hx : x.observe = .error fault := h
    rcases x with ⟨e, d⟩ | d
    · simp only [Fueled.ofExcept_run, Option.map_some]
      rw [observe_eq_fault (d := cp) hx]
    · simp [Execution.observe] at hx
  · cases hR : resume rules p saved result with
    | error fault =>
      have hx : x.observe = .error fault := by
        simp [h, hR, bind, Except.bind, Except.map]
      rcases x with ⟨e, d⟩ | d
      · simp only [hR, Fueled.ofExcept_run, Option.map_some]
        rw [observe_eq_fault (d := cp) hx]
      · simp [Execution.observe] at hx
    | ok R =>
      have hx : x.observe = .ok (ofHalting R) := by
        simp [h, hR, bind, Except.bind, Except.map]
      have hxe := observe_eq_ok hx
      subst hxe
      simp only [hR]
      rcases R with ⟨reason, devm⟩ | devm
      · rfl
      · exact ih _

/-- **The driver.** Today's driver and the staged one agree on every machine and every fuel,
observed with a fault's state erased. -/
theorem execFueled_legacy (fuel : Nat) (evm : Evm) :
    ((Jaune.Legacy.execFueled evm fuel).run).map Execution.observe
      = ((execFueled evm fuel).run).map Execution.observe := by
  induction fuel generalizing evm with
  | zero => rw [Jaune.Legacy.execFueled, execFueled]
  | succ fuel ih =>
    rw [Jaune.Legacy.execFueled, execFueled, ← step_legacy]
    rcases hs : Jaune.Legacy.Evm.step evm with ex | ⟨pc, devm⟩ | ⟨f, rsm, pc⟩
    · rfl
    · exact ih _
    · obtain ⟨hc, hb, -, hm⟩ := step_spawn_coherent hs
      simp only [Step.ofLegacy]
      rw [← enter_legacy f rsm hc]
      rcases he : f.enter with r | child
      · simp only [Frame.Entry.ofLegacy]
        exact execFueled_tail ih _ _ _ _ _ _
          (resume_of_facts hm (Frame.enter_done_facts hc (congrArg BenvStat.rules hb) he))
      · simp only [Frame.Entry.ofLegacy]
        have hih := ih child
        cases hL : (Jaune.Legacy.execFueled child fuel).run with
        | none =>
          rw [hL, Option.map_none, eq_comm, Option.map_eq_none_iff] at hih
          rw [hih]
          rfl
        | some raw =>
          rw [hL, Option.map_some, eq_comm, Option.map_eq_some_iff] at hih
          obtain ⟨raw', hN, hobs⟩ := hih
          have hclean : Execution.Clean raw := by
            rcases raw with _ | d
            · trivial
            · exact (execFueled_ok_error fuel child hL).trans (Frame.enter_run_error he)
          have hset : settle (Frame.ofLegacy f rsm) raw' = Frame.Result.ofSettled (f.settle raw) :=
            (settle_observe hobs).trans
              (settle_legacy f rsm.parent hc.toTopCoherent raw hclean).symm
          rw [hN, Option.map_some, hset]
          exact execFueled_tail ih _ _ _ _ _ _
            (resume_legacy hc hm (congrArg BenvStat.rules hb) raw hclean)

/-- **The total interpreter.** Today's `exec` and the staged one agree on every machine, observed
with a fault's state erased: both run their driver at the same seeded fuel. -/
theorem exec_legacy (evm : Evm) :
    Execution.observe (Jaune.Legacy.exec evm) = Execution.observe (exec evm) := by
  have h := execFueled_legacy (sufficientFuel evm.dyna.gasMeasure) evm
  unfold Jaune.Legacy.exec exec
  cases hL : (Jaune.Legacy.execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run with
  | none =>
    rw [hL, Option.map_none, eq_comm, Option.map_eq_none_iff] at h
    rw [h]
  | some r =>
    rw [hL, Option.map_some, eq_comm, Option.map_eq_some_iff] at h
    obtain ⟨r', hN, ho⟩ := h
    rw [hN]
    exact ho.symm

end Jaune

