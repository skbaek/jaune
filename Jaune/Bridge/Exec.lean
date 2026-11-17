import Jaune.Bridge.Top
import Jaune.ExecChronology

/-!
# The derivation, today's and the restated one (goal `jaune-shape-and-names-v1`, W1 unit J)

`Jaune.Exec` restates the derivation over the four-part message call; today's waits as
`Jaune.Legacy.Exec`. This module maps each to the other constructor by constructor, through the
step bridge (`step_legacy`, `step_spawn_coherent`), the entry bridge (`enter_legacy`) and the
resume bridge (`resume_of_facts`, `resume_legacy`). A child's raw result is clean (F0) because a
child starts from `initDevm`; the map reads the cleanliness off the child's derivation through
today's adequacy (`Legacy.exec_iff_exec_eq`, `Legacy.exec_clean`).

The observation is the raw result with a fault's state erased (`Execution.observe`); a result
that is not a fault is equal. The three views correspond node for node under the map: the raw
chronology, the same-frame continuation and its prefixes, and the retained chronology with the
retained frames.

About today's definitions, and deleted with them after the gate's tag (the W1 design note,
revision 2, section 3.2, unit J).
-/

namespace Jaune

/-! ### The caller's continuation, observed -/

/-- The caller's continuation, observed, is the resumption of the settled result. -/
theorem resumeCaller_observe (rules : ForkRules) (child : Jaune.Frame) (pending : Pending)
    (s : Except Fault Frame.Result) :
    (resumeCaller rules child pending s).observe
      = (s >>= resume rules pending child.checkpoint).map ofHalting := by
  rcases s with fault | result
  · cases fault <;> rfl
  · simp only [resumeCaller, Bind.bind, Except.bind]
    rcases resume rules pending child.checkpoint result with fault | ⟨reason, devm⟩ | devm
    · cases fault <;> rfl
    · rfl
    · rfl

/-- Two raw results observed alike are both errors or both not. -/
theorem observe_isOk {x y : Execution} (h : x.observe = y.observe) : x.isOk = y.isOk := by
  rcases x with ⟨e, d⟩ | d <;> rcases y with ⟨e', d'⟩ | d' <;>
    first
      | rfl
      | (cases e <;> simp [Execution.observe] at h)
      | (cases e' <;> simp [Execution.observe] at h)

/-- A raw result that is not a fault is observed as itself. -/
theorem observe_eq_self {x : Execution} (h : ∀ e, x.observe ≠ .error e) : x.observe = .ok x := by
  rcases x with ⟨e, d⟩ | d
  · cases e <;> first | rfl | exact absurd rfl (h _)
  · rfl

/-! ### One spawn of today, read as a restated one -/

theorem step_halt_of_legacy {evm : Evm} {ex : Execution} (h : Legacy.Evm.step evm = .halt ex) :
    Evm.step evm = .halt ex := by
  rw [← step_legacy, h]; rfl

theorem step_next_of_legacy {evm : Evm} {pc : Nat} {devm : Devm}
    (h : Legacy.Evm.step evm = .cont pc devm) : Evm.step evm = .next pc devm := by
  rw [← step_legacy, h]; rfl

theorem step_spawn_of_legacy {evm : Evm} {f : Legacy.Frame} {rsm : Resume} {pc : Nat}
    (h : Legacy.Evm.step evm = .spawn f rsm pc) :
    Evm.step evm = .spawn (Jaune.Frame.ofLegacy f rsm) (Pending.ofLegacy rsm) pc := by
  rw [← step_legacy, h]; rfl

theorem enter_done_of_legacy {evm : Evm} {f : Legacy.Frame} {rsm : Resume} {pc : Nat}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    (hs : Legacy.Evm.step evm = .spawn f rsm pc) (he : f.enter = .done r) :
    enter (Jaune.Frame.ofLegacy f rsm) = .done (Frame.Result.ofSettled r) := by
  rw [← enter_legacy f rsm (step_spawn_coherent hs).1, he]; rfl

theorem enter_run_of_legacy {evm : Evm} {f : Legacy.Frame} {rsm : Resume} {pc : Nat}
    {cevm : Evm} (hs : Legacy.Evm.step evm = .spawn f rsm pc) (he : f.enter = .run cevm) :
    enter (Jaune.Frame.ofLegacy f rsm) = .run cevm := by
  rw [← enter_legacy f rsm (step_spawn_coherent hs).1, he]; rfl

/-- A child settled at entry: today's resumption and the restated continuation agree, observed. -/
theorem resume_done_of_legacy {evm : Evm} {f : Legacy.Frame} {rsm : Resume} {pc : Nat}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    (hs : Legacy.Evm.step evm = .spawn f rsm pc) (he : f.enter = .done r) :
    (rsm.run r).observe
      = (resumeCaller evm.sta.benvStat.rules (Jaune.Frame.ofLegacy f rsm) (Pending.ofLegacy rsm)
          (Frame.Result.ofSettled r)).observe := by
  obtain ⟨hc, hb, -, hm⟩ := step_spawn_coherent hs
  rw [resumeCaller_observe]
  exact resume_of_facts hm (Legacy.Frame.enter_done_facts hc (congrArg BenvStat.rules hb) he)

/-- A child that runs: today's resumption of its settled clean result and the restated
continuation of a result observed alike agree, observed. -/
theorem resume_run_of_legacy {evm : Evm} {f : Legacy.Frame} {rsm : Resume} {pc : Nat}
    (hs : Legacy.Evm.step evm = .spawn f rsm pc) {raw raw' : Execution}
    (hobs : raw'.observe = raw.observe) (clean : raw.Clean) :
    (rsm.run (f.settle raw)).observe
      = (resumeCaller evm.sta.benvStat.rules (Jaune.Frame.ofLegacy f rsm) (Pending.ofLegacy rsm)
          (settle (Jaune.Frame.ofLegacy f rsm) raw')).observe := by
  obtain ⟨hc, hb, -, hm⟩ := step_spawn_coherent hs
  have hset : settle (Jaune.Frame.ofLegacy f rsm) raw' = Frame.Result.ofSettled (f.settle raw) :=
    (settle_observe hobs).trans (settle_legacy f rsm.parent hc.toTopCoherent raw clean).symm
  rw [resumeCaller_observe, hset]
  exact resume_legacy hc hm (congrArg BenvStat.rules hb) raw clean

/-- A child derivation of today has a clean result: the child starts from no stored error. -/
theorem Legacy.Exec.child_clean {f : Legacy.Frame} {cevm : Evm} {raw : Execution}
    (he : f.enter = .run cevm) (d : Jaune.Legacy.Exec cevm.pc cevm.sta cevm.dyna raw) :
    raw.Clean := by
  rw [← (Jaune.Legacy.exec_iff_exec_eq _ _ _ _).mp ⟨d⟩]
  exact Legacy.exec_clean (Legacy.Frame.enter_run_error he)

/-! ### From today's derivation to the restated one -/

/-- A restated `doneErr` node from a continuation known not to resume. -/
def Exec.ofDoneErr {pc : Nat} {sevm : Sevm} {devm : Devm} {child : Jaune.Frame}
    {pending : Pending} {pc' : Nat} {r : Except Fault Frame.Result}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn child pending pc') (he : enter child = .done r)
    (x : Execution) (hx : resumeCaller sevm.benvStat.rules child pending r = x)
    (hne : x.isOk = false) : Jaune.Exec pc sevm devm x :=
  match x, hx, hne with
  | .error _, hx, _ => .doneErr hs he hx

/-- A restated `runErr` node from a continuation known not to resume. -/
def Exec.ofRunErr {pc : Nat} {sevm : Sevm} {devm : Devm} {child : Jaune.Frame}
    {pending : Pending} {pc' : Nat} {cevm : Evm} {raw : Execution}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn child pending pc') (he : enter child = .run cevm)
    (run : Jaune.Exec cevm.pc cevm.sta cevm.dyna raw)
    (x : Execution) (hx : resumeCaller sevm.benvStat.rules child pending (settle child raw) = x)
    (hne : x.isOk = false) : Jaune.Exec pc sevm devm x :=
  match x, hx, hne with
  | .error _, hx, _ => .runErr hs he run hx

/-- **The map from today's derivation.** Constructor by constructor; the result is observed
alike. -/
def Exec.ofLegacy : {pc : Nat} → {sevm : Sevm} → {devm : Devm} → {ex : Execution} →
    Jaune.Legacy.Exec pc sevm devm ex →
      (Σ' ex' : Execution, Jaune.Exec pc sevm devm ex' ×' ex'.observe = ex.observe)
  | _, _, _, _, .halt h => ⟨_, .halt (step_halt_of_legacy h), rfl⟩
  | _, _, _, _, .cont h next =>
    ⟨(Exec.ofLegacy next).1, .cont (step_next_of_legacy h) (Exec.ofLegacy next).2.1,
      (Exec.ofLegacy next).2.2⟩
  | _, _, _, _, .doneErr hs he hr =>
    let ho := (resume_done_of_legacy hs he).symm.trans (congrArg Execution.observe hr)
    ⟨_, Exec.ofDoneErr (step_spawn_of_legacy hs) (enter_done_of_legacy hs he) _ rfl
        (observe_isOk ho), ho⟩
  | _, _, _, _, .doneOk hs he hr next =>
    ⟨(Exec.ofLegacy next).1,
      .doneOk (step_spawn_of_legacy hs) (enter_done_of_legacy hs he)
        (observe_eq_ok ((resume_done_of_legacy hs he).symm.trans (congrArg Execution.observe hr)))
        (Exec.ofLegacy next).2.1,
      (Exec.ofLegacy next).2.2⟩
  | _, _, _, _, .runErr hs he child hr =>
    let ho := (resume_run_of_legacy hs (Exec.ofLegacy child).2.2
      (Legacy.Exec.child_clean he child)).symm.trans (congrArg Execution.observe hr)
    ⟨_, Exec.ofRunErr (step_spawn_of_legacy hs) (enter_run_of_legacy hs he)
        (Exec.ofLegacy child).2.1 _ rfl (observe_isOk ho), ho⟩
  | _, _, _, _, .runOk hs he child hr next =>
    ⟨(Exec.ofLegacy next).1,
      .runOk (step_spawn_of_legacy hs) (enter_run_of_legacy hs he) (Exec.ofLegacy child).2.1
        (observe_eq_ok ((resume_run_of_legacy hs (Exec.ofLegacy child).2.2
          (Legacy.Exec.child_clean he child)).symm.trans (congrArg Execution.observe hr)))
        (Exec.ofLegacy next).2.1,
      (Exec.ofLegacy next).2.2⟩

/-- A result that is not a fault is mapped to itself. -/
theorem Exec.ofLegacy_eq {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution}
    (d : Jaune.Legacy.Exec pc sevm devm ex) (h : ∀ e, ex.observe ≠ .error e) :
    (Exec.ofLegacy d).1 = ex :=
  observe_eq_ok ((Exec.ofLegacy d).2.2.trans (observe_eq_self h))

/-! ### From the restated derivation back to today's -/

theorem legacy_of_step_halt {evm : Evm} {ex : Execution} (h : Evm.step evm = .halt ex) :
    Legacy.Evm.step evm = .halt ex := by
  rw [← step_legacy] at h
  rcases hL : Legacy.Evm.step evm with ex' | ⟨pc, d⟩ | ⟨f, rsm, pc⟩ <;> rw [hL] at h <;>
    simp only [Step.ofLegacy, reduceCtorEq, Step.halt.injEq] at h
  rw [h]

theorem legacy_of_step_next {evm : Evm} {pc : Nat} {devm : Devm}
    (h : Evm.step evm = .next pc devm) : Legacy.Evm.step evm = .cont pc devm := by
  rw [← step_legacy] at h
  rcases hL : Legacy.Evm.step evm with ex' | ⟨pc', d⟩ | ⟨f, rsm, pc'⟩ <;> rw [hL] at h <;>
    simp only [Step.ofLegacy, reduceCtorEq, Step.next.injEq] at h
  rw [h.1, h.2]

/-- A restated spawn comes from today's spawn of the same child, read by the maps. -/
def spawnOfLegacy {evm : Evm} {child : Jaune.Frame} {pending : Pending} {pc : Nat}
    (hs : Evm.step evm = .spawn child pending pc) :
    Σ' (f : Legacy.Frame) (rsm : Resume),
      Legacy.Evm.step evm = .spawn f rsm pc ∧ child = Jaune.Frame.ofLegacy f rsm ∧
        pending = Pending.ofLegacy rsm :=
  match hL : Legacy.Evm.step evm with
  | .spawn f rsm _ => ⟨f, rsm, by
      have h := hs
      rw [← step_legacy, hL] at h
      simp only [Step.ofLegacy, Step.spawn.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h3
      exact ⟨rfl, h1.symm, h2.symm⟩⟩
  | .halt _ => False.elim (by
      have h := hs
      rw [← step_legacy, hL] at h
      simp [Step.ofLegacy] at h)
  | .cont _ _ => False.elim (by
      have h := hs
      rw [← step_legacy, hL] at h
      simp [Step.ofLegacy] at h)

/-- A restated child settled at entry was settled at today's entry. -/
def enterDoneOfLegacy {f : Legacy.Frame} {rsm : Resume}
    (hc : Legacy.Frame.Coherent f rsm.parent) {r : Except Fault Frame.Result}
    (he : enter (Jaune.Frame.ofLegacy f rsm) = .done r) :
    Σ' r0 : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm,
      f.enter = .done r0 ∧ Frame.Result.ofSettled r0 = r :=
  match hE : f.enter with
  | .done r0 => ⟨r0, rfl, by
      have h := he
      rw [← enter_legacy f rsm hc, hE] at h
      simp only [Frame.Entry.ofLegacy, Frame.Entry.done.injEq] at h
      exact h⟩
  | .run _ => False.elim (by
      have h := he
      rw [← enter_legacy f rsm hc, hE] at h
      simp [Frame.Entry.ofLegacy] at h)

/-- A restated child that runs runs from today's entry. -/
theorem enterRunOfLegacy {f : Legacy.Frame} {rsm : Resume}
    (hc : Legacy.Frame.Coherent f rsm.parent) {cevm : Evm}
    (he : enter (Jaune.Frame.ofLegacy f rsm) = .run cevm) : f.enter = .run cevm := by
  rw [← enter_legacy f rsm hc] at he
  rcases hE : f.enter with r | c <;> rw [hE] at he <;>
    simp only [Frame.Entry.ofLegacy, reduceCtorEq, Frame.Entry.run.injEq] at he
  rw [he]

/-- Today's `doneErr` node from a resumption known to fail. -/
def Legacy.Exec.ofDoneErr {pc : Nat} {sevm : Sevm} {devm : Devm} {f : Legacy.Frame}
    {rsm : Resume} {pc' : Nat}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    (hs : Legacy.Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc') (he : f.enter = .done r)
    (x : Execution) (hx : rsm.run r = x) (hne : x.isOk = false) :
    Jaune.Legacy.Exec pc sevm devm x :=
  match x, hx, hne with
  | .error _, hx, _ => .doneErr hs he hx

/-- Today's `runErr` node from a resumption known to fail. -/
def Legacy.Exec.ofRunErr {pc : Nat} {sevm : Sevm} {devm : Devm} {f : Legacy.Frame}
    {rsm : Resume} {pc' : Nat} {cevm : Evm} {raw : Execution}
    (hs : Legacy.Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc') (he : f.enter = .run cevm)
    (run : Jaune.Legacy.Exec cevm.pc cevm.sta cevm.dyna raw)
    (x : Execution) (hx : rsm.run (f.settle raw) = x) (hne : x.isOk = false) :
    Jaune.Legacy.Exec pc sevm devm x :=
  match x, hx, hne with
  | .error _, hx, _ => .runErr hs he run hx

/-- **The map back to today's derivation.** Constructor by constructor; the result is observed
alike. -/
def Exec.toLegacy : {pc : Nat} → {sevm : Sevm} → {devm : Devm} → {ex : Execution} →
    Jaune.Exec pc sevm devm ex →
      (Σ' ex0 : Execution, Jaune.Legacy.Exec pc sevm devm ex0 ×' ex.observe = ex0.observe)
  | _, _, _, _, .halt h => ⟨_, .halt (legacy_of_step_halt h), rfl⟩
  | _, _, _, _, .cont h next =>
    ⟨(Exec.toLegacy next).1, .cont (legacy_of_step_next h) (Exec.toLegacy next).2.1,
      (Exec.toLegacy next).2.2⟩
  | _, _, _, _, .doneErr hs he hr => by
    obtain ⟨f, rsm, hL, rfl, rfl⟩ := spawnOfLegacy hs
    obtain ⟨r0, hE, rfl⟩ := enterDoneOfLegacy (step_spawn_coherent hL).1 he
    have ho := (resume_done_of_legacy hL hE).trans (congrArg Execution.observe hr)
    exact ⟨_, Legacy.Exec.ofDoneErr hL hE _ rfl (observe_isOk ho), ho.symm⟩
  | _, _, _, _, .doneOk hs he hr next => by
    obtain ⟨f, rsm, hL, rfl, rfl⟩ := spawnOfLegacy hs
    obtain ⟨r0, hE, rfl⟩ := enterDoneOfLegacy (step_spawn_coherent hL).1 he
    have ho := (resume_done_of_legacy hL hE).trans (congrArg Execution.observe hr)
    exact ⟨(Exec.toLegacy next).1,
      .doneOk hL hE (observe_eq_ok ho) (Exec.toLegacy next).2.1, (Exec.toLegacy next).2.2⟩
  | _, _, _, _, .runErr hs he child hr => by
    obtain ⟨f, rsm, hL, rfl, rfl⟩ := spawnOfLegacy hs
    have hE := enterRunOfLegacy (step_spawn_coherent hL).1 he
    have clean := Legacy.Exec.child_clean hE (Exec.toLegacy child).2.1
    have ho := (resume_run_of_legacy hL (Exec.toLegacy child).2.2 clean).trans
      (congrArg Execution.observe hr)
    exact ⟨_, Legacy.Exec.ofRunErr hL hE (Exec.toLegacy child).2.1 _ rfl (observe_isOk ho),
      ho.symm⟩
  | _, _, _, _, .runOk hs he child hr next => by
    obtain ⟨f, rsm, hL, rfl, rfl⟩ := spawnOfLegacy hs
    have hE := enterRunOfLegacy (step_spawn_coherent hL).1 he
    have clean := Legacy.Exec.child_clean hE (Exec.toLegacy child).2.1
    have ho := (resume_run_of_legacy hL (Exec.toLegacy child).2.2 clean).trans
      (congrArg Execution.observe hr)
    exact ⟨(Exec.toLegacy next).1,
      .runOk hL hE (Exec.toLegacy child).2.1 (observe_eq_ok ho) (Exec.toLegacy next).2.1,
      (Exec.toLegacy next).2.2⟩


/-! ### The views, node for node -/

/-- A node of today's derivation, mapped. -/
def Exec.Deriv.ofLegacy (n : Jaune.Legacy.Exec.Deriv) : Jaune.Exec.Deriv :=
  ⟨n.pc, n.sevm, n.devm, (Exec.ofLegacy n.exc).1, (Exec.ofLegacy n.exc).2.1⟩

theorem Exec.rawNodes_ofDoneErr {pc : Nat} {sevm : Sevm} {devm : Devm} {child : Jaune.Frame}
    {pending : Pending} {pc' : Nat} {r : Except Fault Frame.Result}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn child pending pc') (he : enter child = .done r)
    (x : Execution) (hx : resumeCaller sevm.benvStat.rules child pending r = x)
    (hne : x.isOk = false) :
    Jaune.Exec.rawNodes (Exec.ofDoneErr hs he x hx hne) =
      [⟨pc, sevm, devm, x, Exec.ofDoneErr hs he x hx hne⟩] := by
  cases x with
  | ok _ => cases hne
  | error _ => simp [Exec.ofDoneErr, Jaune.Exec.rawNodes]

theorem Exec.rawNodes_ofRunErr {pc : Nat} {sevm : Sevm} {devm : Devm} {child : Jaune.Frame}
    {pending : Pending} {pc' : Nat} {cevm : Evm} {raw : Execution}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn child pending pc') (he : enter child = .run cevm)
    (run : Jaune.Exec cevm.pc cevm.sta cevm.dyna raw)
    (x : Execution) (hx : resumeCaller sevm.benvStat.rules child pending (settle child raw) = x)
    (hne : x.isOk = false) :
    Jaune.Exec.rawNodes (Exec.ofRunErr hs he run x hx hne) =
      ⟨pc, sevm, devm, x, Exec.ofRunErr hs he run x hx hne⟩ :: Jaune.Exec.rawNodes run := by
  cases x with
  | ok _ => cases hne
  | error _ => simp [Exec.ofRunErr, Jaune.Exec.rawNodes]

/-- **The raw chronology, node for node.** -/
theorem Exec.rawNodes_ofLegacy {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution}
    (d : Jaune.Legacy.Exec pc sevm devm ex) :
    Jaune.Exec.rawNodes (Exec.ofLegacy d).2.1 =
      (Jaune.Legacy.Exec.rawNodes d).map Exec.Deriv.ofLegacy := by
  induction d with
  | halt h => simp [Exec.ofLegacy, Jaune.Exec.rawNodes, Jaune.Legacy.Exec.rawNodes,
      Exec.Deriv.ofLegacy]
  | cont h next ih =>
    simp only [Exec.ofLegacy, Jaune.Exec.rawNodes, Jaune.Legacy.Exec.rawNodes, List.map_cons, ih]
    rfl
  | doneErr hs he hr =>
    simp only [Exec.ofLegacy, Jaune.Legacy.Exec.rawNodes, List.map_cons, List.map_nil]
    exact Exec.rawNodes_ofDoneErr ..
  | doneOk hs he hr next ih =>
    simp only [Exec.ofLegacy, Jaune.Exec.rawNodes, Jaune.Legacy.Exec.rawNodes, List.map_cons, ih]
    rfl
  | runErr hs he child hr ihc =>
    simp only [Exec.ofLegacy, Jaune.Legacy.Exec.rawNodes, List.map_cons, ← ihc]
    exact Exec.rawNodes_ofRunErr ..
  | runOk hs he child hr next ihc ih =>
    simp only [Exec.ofLegacy, Jaune.Exec.rawNodes, Jaune.Legacy.Exec.rawNodes, List.map_cons,
      List.map_append, ihc, ih]
    rfl

/-- The same-frame continuation of a node, if it has one (restated). -/
def Exec.next? {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution} :
    Jaune.Exec pc sevm devm ex → Option Jaune.Exec.Deriv
  | .halt _ => none
  | .cont _ next => some ⟨_, _, _, _, next⟩
  | .doneErr _ _ _ => none
  | .doneOk _ _ _ next => some ⟨_, _, _, _, next⟩
  | .runErr _ _ _ _ => none
  | .runOk _ _ _ _ next => some ⟨_, _, _, _, next⟩

/-- The same-frame continuation of a node, if it has one (today's). -/
def Legacy.Exec.next? {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution} :
    Jaune.Legacy.Exec pc sevm devm ex → Option Jaune.Legacy.Exec.Deriv
  | .halt _ => none
  | .cont _ next => some ⟨_, _, _, _, next⟩
  | .doneErr _ _ _ => none
  | .doneOk _ _ _ next => some ⟨_, _, _, _, next⟩
  | .runErr _ _ _ _ => none
  | .runOk _ _ _ _ next => some ⟨_, _, _, _, next⟩

theorem Exec.Deriv.parentStep_iff {next root : Jaune.Exec.Deriv} :
    Jaune.Exec.Deriv.ParentStep next root ↔ Exec.next? root.exc = some next := by
  constructor
  · intro h; cases h <;> rfl
  · intro h
    rcases root with ⟨pc, sevm, devm, ex, d⟩
    cases d <;> simp only [Exec.next?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
      constructor

theorem Legacy.Exec.Deriv.parentStep_iff {next root : Jaune.Legacy.Exec.Deriv} :
    Jaune.Legacy.Exec.Deriv.ParentStep next root ↔ Legacy.Exec.next? root.exc = some next := by
  constructor
  · intro h; cases h <;> rfl
  · intro h
    rcases root with ⟨pc, sevm, devm, ex, d⟩
    cases d <;> simp only [Legacy.Exec.next?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
      constructor

theorem Exec.next?_ofDoneErr {pc : Nat} {sevm : Sevm} {devm : Devm} {child : Jaune.Frame}
    {pending : Pending} {pc' : Nat} {r : Except Fault Frame.Result}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn child pending pc') (he : enter child = .done r)
    (x : Execution) (hx : resumeCaller sevm.benvStat.rules child pending r = x)
    (hne : x.isOk = false) :
    Exec.next? (Exec.ofDoneErr hs he x hx hne) = none := by
  cases x with
  | ok _ => cases hne
  | error _ => rfl

theorem Exec.next?_ofRunErr {pc : Nat} {sevm : Sevm} {devm : Devm} {child : Jaune.Frame}
    {pending : Pending} {pc' : Nat} {cevm : Evm} {raw : Execution}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn child pending pc') (he : enter child = .run cevm)
    (run : Jaune.Exec cevm.pc cevm.sta cevm.dyna raw)
    (x : Execution) (hx : resumeCaller sevm.benvStat.rules child pending (settle child raw) = x)
    (hne : x.isOk = false) :
    Exec.next? (Exec.ofRunErr hs he run x hx hne) = none := by
  cases x with
  | ok _ => cases hne
  | error _ => rfl

theorem Exec.next?_ofLegacy {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution}
    (d : Jaune.Legacy.Exec pc sevm devm ex) :
    Exec.next? (Exec.ofLegacy d).2.1 = (Legacy.Exec.next? d).map Exec.Deriv.ofLegacy := by
  cases d with
  | halt h => rfl
  | cont h next => rfl
  | doneErr hs he hr =>
    simp only [Exec.ofLegacy, Legacy.Exec.next?, Option.map_none]
    exact Exec.next?_ofDoneErr ..
  | doneOk hs he hr next => rfl
  | runErr hs he child hr =>
    simp only [Exec.ofLegacy, Legacy.Exec.next?, Option.map_none]
    exact Exec.next?_ofRunErr ..
  | runOk hs he child hr next => rfl

/-- **The same-frame continuation, node for node.** -/
theorem Exec.Deriv.parentStep_ofLegacy_iff {next : Jaune.Exec.Deriv}
    {root : Jaune.Legacy.Exec.Deriv} :
    Jaune.Exec.Deriv.ParentStep next (Exec.Deriv.ofLegacy root) ↔
      ∃ n, Jaune.Legacy.Exec.Deriv.ParentStep n root ∧ next = Exec.Deriv.ofLegacy n := by
  rw [Exec.Deriv.parentStep_iff]
  simp only [Exec.Deriv.ofLegacy, Exec.next?_ofLegacy, Option.map_eq_some_iff,
    Legacy.Exec.Deriv.parentStep_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩

theorem Exec.Deriv.parentStep_ofLegacy {next root : Jaune.Legacy.Exec.Deriv}
    (h : Jaune.Legacy.Exec.Deriv.ParentStep next root) :
    Jaune.Exec.Deriv.ParentStep (Exec.Deriv.ofLegacy next) (Exec.Deriv.ofLegacy root) :=
  Exec.Deriv.parentStep_ofLegacy_iff.mpr ⟨next, h, rfl⟩

/-- **Same-frame prefixes, node for node.** -/
theorem Exec.Deriv.parentPrefix_ofLegacy {root tail : Jaune.Legacy.Exec.Deriv}
    (h : Jaune.Legacy.Exec.Deriv.ParentPrefix root tail) :
    Jaune.Exec.Deriv.ParentPrefix (Exec.Deriv.ofLegacy root) (Exec.Deriv.ofLegacy tail) := by
  induction h with
  | refl => exact .refl _
  | step head _ ih => exact .step (Exec.Deriv.parentStep_ofLegacy head) ih

theorem Exec.Deriv.parentPrefix_ofLegacy_inv {root : Jaune.Legacy.Exec.Deriv}
    {tail : Jaune.Exec.Deriv}
    (h : Jaune.Exec.Deriv.ParentPrefix (Exec.Deriv.ofLegacy root) tail) :
    ∃ t, Jaune.Legacy.Exec.Deriv.ParentPrefix root t ∧ tail = Exec.Deriv.ofLegacy t := by
  generalize hr : Exec.Deriv.ofLegacy root = r at h
  induction h generalizing root with
  | refl => exact ⟨root, .refl _, hr.symm⟩
  | step head _ ih =>
    subst hr
    obtain ⟨n, hn, rfl⟩ := Exec.Deriv.parentStep_ofLegacy_iff.mp head
    obtain ⟨t, ht, rfl⟩ := ih rfl
    exact ⟨t, .step hn ht, rfl⟩

/-! ### Settlement, node for node -/

/-- Settlement commits in today's sense exactly when it commits in the restated one. -/
theorem settlementCommits_ofSettled
    (s : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm) :
    (match Frame.Result.ofSettled s with | .ok (.success ..) => true | _ => false) =
      (match s with | .error _ => false | .ok post => post.error.isNone) := by
  rcases s with ⟨e, _⟩ | d
  · cases e <;> rfl
  · simp only [Frame.Result.ofSettled]
    rcases d.error with _ | (_ | _) <;> rfl

theorem settlementCommits_of_legacy {evm : Evm} {f : Legacy.Frame} {rsm : Resume} {pc : Nat}
    (hs : Legacy.Evm.step evm = .spawn f rsm pc) {raw raw' : Execution}
    (hobs : raw'.observe = raw.observe) (clean : raw.Clean) :
    Jaune.Frame.settlementCommits (Jaune.Frame.ofLegacy f rsm) raw' =
      Legacy.Frame.settlementCommits f raw := by
  have hc := (step_spawn_coherent hs).1
  have hset : settle (Jaune.Frame.ofLegacy f rsm) raw' = Frame.Result.ofSettled (f.settle raw) :=
    (settle_observe hobs).trans (settle_legacy f rsm.parent hc.toTopCoherent raw clean).symm
  unfold Jaune.Frame.settlementCommits Legacy.Frame.settlementCommits
  rw [hset]
  exact settlementCommits_ofSettled _

theorem Execution.isOk_of_commits {ex : Execution} (h : Execution.commits ex = true) :
    ex.isOk = true := by
  cases ex with
  | error _ => simp [Execution.commits] at h
  | ok _ => rfl

/-- A retained frame of today, mapped. -/
def Exec.Frame.ofLegacy (fr : Jaune.Legacy.Exec.Frame) : Jaune.Exec.Frame :=
  ⟨fr.pc, fr.sevm, fr.pre, (Exec.ofLegacy fr.run).1, (Exec.ofLegacy fr.run).2.1,
    (observe_isOk (Exec.ofLegacy fr.run).2.2).trans (Execution.isOk_of_commits fr.committed)⟩

/-- A derivation from a machine with no stored error has a clean result. -/
theorem Legacy.Exec.out_clean {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution}
    (d : Jaune.Legacy.Exec pc sevm devm ex) (h : devm.error = none) : ex.Clean := by
  rw [← (Jaune.Legacy.exec_iff_exec_eq _ _ _ _).mp ⟨d⟩]
  exact Legacy.exec_clean h

/-- From a machine with no stored error, today's commitment is the restated one. -/
theorem Exec.commits_ofLegacy {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution}
    (d : Jaune.Legacy.Exec pc sevm devm ex) (h : devm.error = none) :
    (Exec.ofLegacy d).1.isOk = Execution.commits ex := by
  rw [observe_isOk (Exec.ofLegacy d).2.2]
  have hc := Legacy.Exec.out_clean d h
  cases ex with
  | error _ => rfl
  | ok post =>
    simp only [Execution.Clean] at hc
    simp [Execution.commits, hc]
    rfl

theorem Exec.retainedNodesOfCommits_ofLegacy {pc : Nat} {sevm : Sevm} {devm : Devm}
    {ex : Execution} (d : Jaune.Legacy.Exec pc sevm devm ex) :
    ∀ (h : Execution.commits ex = true) (h' : (Exec.ofLegacy d).1.isOk = true),
      Jaune.Exec.retainedNodesOfCommits (Exec.ofLegacy d).2.1 h' =
        (Jaune.Legacy.Exec.retainedNodesOfCommits d h).map Exec.Deriv.ofLegacy := by
  induction d with
  | halt hs =>
    intro h h'
    simp [Exec.ofLegacy, Jaune.Exec.retainedNodesOfCommits,
      Jaune.Legacy.Exec.retainedNodesOfCommits, Exec.Deriv.ofLegacy]
  | cont hs next ih =>
    intro h h'
    simp only [Exec.ofLegacy, Jaune.Exec.retainedNodesOfCommits,
      Jaune.Legacy.Exec.retainedNodesOfCommits, List.map_cons, ih h h']
    rfl
  | doneErr => intro h; simp [Execution.commits] at h
  | doneOk hs he hr next ih =>
    intro h h'
    simp only [Exec.ofLegacy, Jaune.Exec.retainedNodesOfCommits,
      Jaune.Legacy.Exec.retainedNodesOfCommits, List.map_cons, ih h h']
    rfl
  | runErr => intro h; simp [Execution.commits] at h
  | @runOk pc sevm devm f rsm pc' cevm raw devm' ex hs he child hr next ihc ih =>
    intro h h'
    have heq := settlementCommits_of_legacy hs (Exec.ofLegacy child).2.2
      (Legacy.Exec.child_clean he child)
    simp only [Exec.ofLegacy, Jaune.Exec.retainedNodesOfCommits,
      Jaune.Legacy.Exec.retainedNodesOfCommits, List.map_cons, List.map_append, ih h h']
    by_cases hc : Legacy.Frame.settlementCommits f raw = true
    · rw [dite_eq_left (heq.trans hc), dite_eq_left hc, ihc]
      rfl
    · rw [dite_eq_right (by rw [heq]; exact hc), dite_eq_right hc]
      rfl

/-- **The retained chronology, node for node**, from a machine with no stored error. -/
theorem Exec.retainedNodes_ofLegacy {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution}
    (d : Jaune.Legacy.Exec pc sevm devm ex) (clean : devm.error = none) :
    Jaune.Exec.retainedNodes (Exec.ofLegacy d).2.1 =
      (Jaune.Legacy.Exec.retainedNodes d).map Exec.Deriv.ofLegacy := by
  have hc := Exec.commits_ofLegacy d clean
  unfold Jaune.Exec.retainedNodes Jaune.Legacy.Exec.retainedNodes
  by_cases hk : Execution.commits ex = true
  · rw [dite_eq_left hk, dite_eq_left (hc.trans hk)]
    exact Exec.retainedNodesOfCommits_ofLegacy d hk _
  · rw [dite_eq_right hk, dite_eq_right (by rw [hc]; exact hk)]
    rfl

theorem Exec.descendantFrames_ofDoneErr {pc : Nat} {sevm : Sevm} {devm : Devm}
    {child : Jaune.Frame} {pending : Pending} {pc' : Nat} {r : Except Fault Frame.Result}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn child pending pc') (he : enter child = .done r)
    (x : Execution) (hx : resumeCaller sevm.benvStat.rules child pending r = x)
    (hne : x.isOk = false) :
    Jaune.Exec.descendantFrames (Exec.ofDoneErr hs he x hx hne) = [] := by
  cases x with
  | ok _ => cases hne
  | error _ => simp [Exec.ofDoneErr, Jaune.Exec.descendantFrames]

theorem Exec.descendantFrames_ofRunErr {pc : Nat} {sevm : Sevm} {devm : Devm}
    {child : Jaune.Frame} {pending : Pending} {pc' : Nat} {cevm : Evm} {raw : Execution}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn child pending pc') (he : enter child = .run cevm)
    (run : Jaune.Exec cevm.pc cevm.sta cevm.dyna raw)
    (x : Execution) (hx : resumeCaller sevm.benvStat.rules child pending (settle child raw) = x)
    (hne : x.isOk = false) :
    Jaune.Exec.descendantFrames (Exec.ofRunErr hs he run x hx hne) = [] := by
  cases x with
  | ok _ => cases hne
  | error _ => simp [Exec.ofRunErr, Jaune.Exec.descendantFrames]

/-- **The retained frames below a node, frame for frame.** -/
theorem Exec.descendantFrames_ofLegacy {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution}
    (d : Jaune.Legacy.Exec pc sevm devm ex) :
    Jaune.Exec.descendantFrames (Exec.ofLegacy d).2.1 =
      (Jaune.Legacy.Exec.descendantFrames d).map Exec.Frame.ofLegacy := by
  induction d with
  | halt hs =>
    simp [Exec.ofLegacy, Jaune.Exec.descendantFrames, Jaune.Legacy.Exec.descendantFrames]
  | cont hs next ih =>
    simp only [Exec.ofLegacy, Jaune.Exec.descendantFrames, Jaune.Legacy.Exec.descendantFrames, ih]
  | doneErr hs he hr =>
    simp only [Exec.ofLegacy, Jaune.Legacy.Exec.descendantFrames, List.map_nil]
    exact Exec.descendantFrames_ofDoneErr ..
  | doneOk hs he hr next ih =>
    simp only [Exec.ofLegacy, Jaune.Exec.descendantFrames, Jaune.Legacy.Exec.descendantFrames, ih]
  | runErr hs he child hr ihc =>
    simp only [Exec.ofLegacy, Jaune.Legacy.Exec.descendantFrames, List.map_nil]
    exact Exec.descendantFrames_ofRunErr ..
  | @runOk pc sevm devm f rsm pc' cevm raw devm' ex hs he child hr next ihc ih =>
    have heq := settlementCommits_of_legacy hs (Exec.ofLegacy child).2.2
      (Legacy.Exec.child_clean he child)
    simp only [Exec.ofLegacy, Jaune.Exec.descendantFrames, Jaune.Legacy.Exec.descendantFrames,
      List.map_append, ih]
    by_cases hc : Legacy.Frame.settlementCommits f raw = true
    · rw [dite_eq_left (heq.trans hc), dite_eq_left hc, ihc]
      rfl
    · rw [dite_eq_right (by rw [heq]; exact hc), dite_eq_right hc]
      rfl

/-- **The retained frames, frame for frame**, from a machine with no stored error. -/
theorem Exec.committedFrames_ofLegacy {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution}
    (d : Jaune.Legacy.Exec pc sevm devm ex) (clean : devm.error = none) :
    Jaune.Exec.committedFrames (Exec.ofLegacy d).2.1 =
      (Jaune.Legacy.Exec.committedFrames d).map Exec.Frame.ofLegacy := by
  have hc := Exec.commits_ofLegacy d clean
  unfold Jaune.Exec.committedFrames Jaune.Legacy.Exec.committedFrames
  by_cases hk : Execution.commits ex = true
  · rw [dite_eq_left hk, dite_eq_left (hc.trans hk), Exec.descendantFrames_ofLegacy d]
    rfl
  · rw [dite_eq_right hk, dite_eq_right (by rw [hc]; exact hk)]
    rfl

/-! ### The retired relations, one equation each

Today's frame and step relations (`Jaune.ExecFrame`, `Jaune.Exec`) wait unchanged for the
delete commit. Each is read here through the four-part message call: a spawned child is entered,
run by `exec` when it has code, and settled (`Frame.runSpawned`); the caller continues by
`resumeCaller`. -/

/-- A spawned child run to its settled result: the body of `Frame.runTop`, entered as a child. -/
def Frame.runSpawned (child : Jaune.Frame) : Except Fault Frame.Result :=
  match enter child with
  | .done result => result
  | .run evm => settle child (exec evm)

/-- A message opcode's outcome, run to the caller's continuation. -/
def MessageOp.Outcome.runSpawned (rules : ForkRules) : MessageOp.Outcome → Execution
  | .done ex => ex
  | .spawn child pending => resumeCaller rules child pending (Frame.runSpawned child)

/-- A step's outcome, run to the caller's continuation. -/
def Step.runSpawned (rules : ForkRules) : Step → Execution
  | .halt ex => ex
  | .next _ devm => .ok devm
  | .spawn child pending _ => resumeCaller rules child pending (Frame.runSpawned child)

/-- A filled child slot holds today's total result. -/
theorem Xlot.Filled.eq_exec {evm : Evm} {exn : Execution}
    (h : Xlot.Filled (.some ⟨evm, exn⟩)) : exn = Legacy.exec evm :=
  ((Jaune.Legacy.exec_iff_exec_eq _ _ _ _).mp h).symm

/-- **`Xlot.Filled`.** A filled child slot holds the restated total result, observed; for a
result that is not a fault, a slot is filled exactly when the restated derivation exists. -/
theorem Xlot.Filled.legacy {evm : Evm} {exn : Execution}
    (h : Xlot.Filled (.some ⟨evm, exn⟩)) :
    Nonempty (Jaune.Exec evm.pc evm.sta evm.dyna (exec evm)) ∧
      Execution.observe (exec evm) = exn.observe :=
  ⟨Exec.nonempty evm, by rw [h.eq_exec, exec_legacy]⟩

theorem Xlot.filled_iff_legacy {evm : Evm} {exn : Execution}
    (hne : ∀ e, exn.observe ≠ .error e) :
    Xlot.Filled (.some ⟨evm, exn⟩) ↔ Nonempty (Jaune.Exec evm.pc evm.sta evm.dyna exn) := by
  constructor
  · intro h
    obtain ⟨d⟩ := h
    have := Exec.ofLegacy_eq d hne
    exact ⟨this ▸ (Exec.ofLegacy d).2.1⟩
  · intro ⟨d⟩
    have hx := (exec_iff_exec_eq _ _ _ _).mp ⟨d⟩
    have ho := exec_legacy ⟨evm.pc, evm.sta, evm.dyna⟩
    rw [hx] at ho
    have : Legacy.exec ⟨evm.pc, evm.sta, evm.dyna⟩ = exn :=
      observe_eq_ok (ho.trans (observe_eq_self hne))
    exact (Jaune.Legacy.exec_iff_exec_eq _ _ _ _).mpr this

/-- A frame relation with a filled slot settles today's total result. -/
theorem RunFrame.eq_runFrame {f : Legacy.Frame} {xl : Xlot}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    (hr : RunFrame f xl r) (hx : xl.Filled) : r = runFrame f := by
  unfold RunFrame at hr
  unfold runFrame
  split at hr
  · rename_i r' he
    rw [he]; exact hr.2
  · rename_i evm he
    obtain ⟨raw, rfl, rfl⟩ := hr
    rw [he, Xlot.Filled.eq_exec hx]

/-- **`RunFrame`.** A spawned child's settled result, read as a frame result, is the child run by
the four-part message call. -/
theorem RunFrame.legacy {f : Legacy.Frame} {rsm : Resume}
    (hc : Legacy.Frame.Coherent f rsm.parent) {xl : Xlot}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    (hr : RunFrame f xl r) (hx : xl.Filled) :
    Frame.Result.ofSettled r = Frame.runSpawned (Jaune.Frame.ofLegacy f rsm) := by
  rw [RunFrame.eq_runFrame hr hx]
  unfold runFrame Frame.runSpawned
  rw [← enter_legacy f rsm hc]
  rcases he : f.enter with r' | evm
  · rfl
  · simp only [Frame.Entry.ofLegacy]
    rw [settle_observe (exec_legacy evm).symm]
    exact settle_legacy f rsm.parent hc.toTopCoherent _
      (Legacy.exec_clean (Legacy.Frame.enter_run_error he))

/-- **`ProcessMessage`.** A top-level call's settled result is `Frame.runTop` of its frame. -/
theorem ProcessMessage.legacy {msg : Msg} {xl : Xlot}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    (hr : ProcessMessage msg xl r) (hx : xl.Filled) :
    Frame.Result.ofSettled r = Frame.runTop (Frame.ofTop msg false) := by
  rw [runTop_ofTop, RunFrame.eq_runFrame hr hx]
  rfl

/-- **`ProcessCreateMessage`.** A top-level creation's settled result is `Frame.runTop` of its
frame. -/
theorem ProcessCreateMessage.legacy {msg : Msg} {xl : Xlot}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    (hr : ProcessCreateMessage msg xl r) (hx : xl.Filled) :
    Frame.Result.ofSettled r = Frame.runTop (Frame.ofTop msg true) := by
  rw [runTop_ofTop, RunFrame.eq_runFrame hr hx]
  rfl

/-- **`ExecuteCode`.** Its raw result is the restated `exec`'s, observed; the handling around it
is `settle`'s (it waits with `executeCode.handleErrorWith`). -/
theorem ExecuteCode.legacy {msg : Msg} {xl : Xlot}
    {ex : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    (hr : ExecuteCode msg xl ex) (hx : xl.Filled) :
    ∃ raw : Execution, ex = executeCode.handleErrorWith msg.benv.stat.rules.stateGas raw ∧
      raw.observe =
        Execution.observe (match executeCode.enter msg with | .inl evm => exec evm | .inr raw => raw) := by
  unfold ExecuteCode at hr
  split at hr
  · rename_i evm he
    obtain ⟨raw, rfl, rfl⟩ := hr
    refine ⟨raw, rfl, ?_⟩
    rw [he]
    simp only []
    rw [Xlot.Filled.eq_exec hx, exec_legacy]
  · rename_i raw he
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨raw, rfl, by rw [he]⟩

/-- Today's settled child result keeps what today's settlement guarantees. -/
theorem runFrame_settledFacts {f : Legacy.Frame} {rsm : Resume}
    (hc : Legacy.Frame.Coherent f rsm.parent) :
    Legacy.SettledFacts rsm.parent f.outer.benv.stat.rules (runFrame f) := by
  unfold runFrame
  rcases he : f.enter with r | evm
  · exact Legacy.Frame.enter_done_facts hc rfl he
  · exact Legacy.settledFacts hc rfl (Legacy.exec_clean (Legacy.Frame.enter_run_error he))

/-- **`XStep.Run`.** A message opcode's outcome of today whose spawns are coherent, with a filled
slot, continues the caller as the restated outcome run to its continuation does, observed. -/
theorem XStep.Run.legacy {sevm : Sevm} {s : XStep}
    (hs : ∀ f rsm, s = .spawn f rsm → SpawnCoherent sevm f rsm) {xl : Xlot} {ex : Execution}
    (hr : XStep.Run s xl ex) (hx : xl.Filled) :
    ex.observe =
      (MessageOp.Outcome.runSpawned sevm.benvStat.rules (MessageOp.Outcome.ofLegacy s)).observe := by
  cases s with
  | done ex' =>
    obtain ⟨-, rfl⟩ := hr
    rfl
  | spawn f rsm =>
    obtain ⟨r, hrun, rfl⟩ := hr
    obtain ⟨hc, hb, -, hm⟩ := hs f rsm rfl
    simp only [MessageOp.Outcome.ofLegacy, MessageOp.Outcome.runSpawned]
    rw [resumeCaller_observe, ← RunFrame.legacy hc hrun hx, RunFrame.eq_runFrame hrun hx]
    have hf := runFrame_settledFacts hc
    rw [hb] at hf
    exact resume_of_facts hm hf

/-- **`MessageOp.Run`.** -/
theorem MessageOp.Run.legacy {sevm : Sevm} {devm : Devm} {x : MessageOp} {xl : Xlot}
    {ex : Execution} (hr : MessageOp.Run sevm devm x xl ex) (hx : xl.Filled) :
    ex.observe =
      (MessageOp.Outcome.runSpawned sevm.benvStat.rules (MessageOp.step sevm devm x)).observe := by
  rw [← MessageOp.step_legacy]
  exact XStep.Run.legacy (fun _ _ h => MessageOp.step_spawn_coherent h) hr hx

/-- **`GenericCreate`.** -/
theorem GenericCreate.legacy {sevm : Sevm} {devm : Devm} {endowment : U256}
    {newAddress : Address} {memoryIndex memorySize : Nat} {xl : Xlot} {ex : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hr : GenericCreate sevm devm endowment newAddress memoryIndex memorySize xl ex)
    (hx : xl.Filled) :
    ex.observe = (MessageOp.Outcome.runSpawned sevm.benvStat.rules
      (genericCreate.step sevm devm endowment newAddress memoryIndex memorySize)).observe := by
  rw [← genericCreate.step_legacy]
  exact XStep.Run.legacy (fun _ _ h => genericCreate.step_spawn_coherent h hsg) hr hx

/-- **`GenericCall`.** -/
theorem GenericCall.legacy {sevm : Sevm} {devm : Devm} {gas : Nat} {value : U256}
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {ex : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hr : GenericCall sevm devm gas value caller target codeAddress shouldTransferValue
      isStaticcall inputIndex inputSize outputIndex outputSize code disablePrecompiles xl ex)
    (hx : xl.Filled) :
    ex.observe = (MessageOp.Outcome.runSpawned sevm.benvStat.rules
      (genericCall.step sevm devm gas value caller target codeAddress shouldTransferValue
        isStaticcall inputIndex inputSize outputIndex outputSize code
        disablePrecompiles)).observe := by
  rw [← genericCall.step_legacy]
  exact XStep.Run.legacy (fun _ _ h => genericCall.step_spawn_coherent h hsg) hr hx

/-- **`GenericCreateAmsterdam`.** -/
theorem GenericCreateAmsterdam.legacy {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {endowment : U256} {newAddress : Address} {memoryIndex memorySize : Nat} {xl : Xlot}
    {ex : Execution} (hsg : sevm.benvStat.rules.stateGas = some state)
    (hr : GenericCreateAmsterdam sevm state devm endowment newAddress memoryIndex memorySize
      xl ex)
    (hx : xl.Filled) :
    ex.observe = (MessageOp.Outcome.runSpawned sevm.benvStat.rules
      (genericCreateAmsterdam.step sevm state devm endowment newAddress memoryIndex
        memorySize)).observe := by
  rw [← genericCreateAmsterdam.step_legacy]
  exact XStep.Run.legacy (fun _ _ h => genericCreateAmsterdam.step_spawn_coherent h hsg) hr hx

/-- **`GenericCallAmsterdam`.** -/
theorem GenericCallAmsterdam.legacy {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {gas reservoir : Nat} {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool} {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles newAccountCharged insufficientBalance : Bool}
    {xl : Xlot} {ex : Execution} (hsg : sevm.benvStat.rules.stateGas = some state)
    (hr : GenericCallAmsterdam sevm state devm gas reservoir value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize code
      disablePrecompiles newAccountCharged insufficientBalance xl ex)
    (hx : xl.Filled) :
    ex.observe = (MessageOp.Outcome.runSpawned sevm.benvStat.rules
      (genericCallAmsterdam.step sevm state devm gas reservoir value caller target codeAddress
        shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize code
        disablePrecompiles newAccountCharged insufficientBalance)).observe := by
  rw [← genericCallAmsterdam.step_legacy]
  exact XStep.Run.legacy (fun _ _ h => genericCallAmsterdam.step_spawn_coherent h hsg) hr hx

/-- **`Step.Run`.** A step of today whose spawns are coherent, with a filled slot, continues the
caller as the restated step run to its continuation does, observed. -/
theorem Legacy.Step.Run.legacy {sevm : Sevm} {s : Jaune.Legacy.Step}
    (hs : ∀ f rsm pc, s = .spawn f rsm pc → SpawnCoherent sevm f rsm) {xl : Xlot}
    {ex : Execution} (hr : Jaune.Legacy.Step.Run s xl ex) (hx : xl.Filled) :
    ex.observe = (Step.runSpawned sevm.benvStat.rules (Step.ofLegacy s)).observe := by
  cases s with
  | halt ex' => obtain ⟨-, rfl⟩ := hr; rfl
  | cont pc devm => obtain ⟨-, rfl⟩ := hr; rfl
  | spawn f rsm pc =>
    obtain ⟨r, hrun, rfl⟩ := hr
    obtain ⟨hc, hb, -, hm⟩ := hs f rsm pc rfl
    simp only [Step.ofLegacy, Step.runSpawned]
    rw [resumeCaller_observe, ← RunFrame.legacy hc hrun hx, RunFrame.eq_runFrame hrun hx]
    have hf := runFrame_settledFacts hc
    rw [hb] at hf
    exact resume_of_facts hm hf

/-- **`NextOp.StepRun`.** -/
theorem NextOp.StepRun.legacy {pc : Nat} {sevm : Sevm} {devm : Devm} {n : NextOp} {xl : Xlot}
    {ex : Execution} (hr : NextOp.StepRun pc sevm devm n xl ex) (hx : xl.Filled) :
    ex.observe =
      (Step.runSpawned sevm.benvStat.rules (NextOp.step ⟨pc, sevm, devm⟩ n)).observe := by
  rw [← NextOp.step_legacy]
  refine Legacy.Step.Run.legacy (fun f rsm pc' h => ?_) hr hx
  obtain ⟨x, _, hx'⟩ := Legacy.NextOp.step_spawn_inv h
  exact MessageOp.step_spawn_coherent hx'

/-- **`NextOp.Run`.** -/
theorem NextOp.Run.legacy {sevm : Sevm} {devm : Devm} {n : NextOp} {devm' : Devm}
    (hr : NextOp.Run sevm devm n devm') :
    ∃ pc, Step.runSpawned sevm.benvStat.rules (NextOp.step ⟨pc, sevm, devm⟩ n) = .ok devm' := by
  obtain ⟨xl, hx, pc, hs⟩ := hr
  exact ⟨pc, observe_eq_ok (NextOp.StepRun.legacy hs hx).symm⟩

end Jaune
