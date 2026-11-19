import Jaune.FrameRun.CheckedDecompose
import Jaune.FrameRun.CheckedFacts
import Jaune.MessageCall.CheckedDerivOrder
import Jaune.Bridge.G2b.CheckedDriver
import Jaune.Bridge.G2b.FinalRetained
import Jaune.Bridge.G2b.FinalPrefix
import Jaune.Bridge.G3.FrameViews
import Jaune.FrameRun.Unique
import Jaune.MessageCall.FinalAdequacy
import Jaune.Run.Root

/-!
# Checked view bridges (goal `jaune-shape-and-names-v1`, G2b, S5)

The checked frame sequence `Checked.Frame.Run` and the checked six-constructor derivation
`Checked.Exec` are the same data: `equivExec` relabels one as the other. The three views of S5 agree
across that relabelling: every reached node in execution order (`rawNodes_bridge`), the
continuation within one frame (`parentPrefix_bridge`, through `spine_bridge`), and the frames kept
after settlement (`retainedNodes_bridge`, `committedFrames_bridge`, `descendantFrames_bridge`).
-/

namespace Jaune.Checked.Frame.Run

/-- Relabel a complete six-constructor derivation at its original start and result indices. -/
def ofExec {r out} (d : Exec r out) : Frame.Run r (.exit out) :=
  match d with
  | .halt hs => .halt hs
  | .cont hs rest => .next hs (ofExec rest)
  | .doneErr hs he hr => .callDoneEnd hs he hr
  | .doneOk hs he hr rest => .callDone hs he hr (ofExec rest)
  | .runErr hs he child hr => .callRanEnd hs he (ofExec child) hr
  | .runOk hs he child hr rest => .callRan hs he (ofExec child) hr (ofExec rest)
termination_by structural d

/-- Forget the endpoint tag of a complete frame sequence. -/
def toExec {r out} (t : Frame.Run r (.exit out)) : Exec r out :=
  match t with
  | .halt hs => .halt hs
  | .next hs rest => .cont hs (toExec rest)
  | .callDoneEnd hs he hr => .doneErr hs he hr
  | .callDone hs he hr rest => .doneOk hs he hr (toExec rest)
  | .callRanEnd hs he child hr => .runErr hs he (toExec child) hr
  | .callRan hs he child hr rest => .runOk hs he (toExec child) hr (toExec rest)
termination_by sizeOf t

@[simp] theorem toExec_ofExec {r out} (d : Exec r out) : toExec (ofExec d) = d := by
  induction d <;> simp_all [ofExec, toExec]

@[simp] theorem ofExec_toExec {r out} (t : Frame.Run r (.exit out)) : ofExec (toExec t) = t := by
  cases t with
  | halt | callDoneEnd => simp [ofExec, toExec]
  | next hs rest | callDone _ _ hs rest => simp [ofExec, toExec, ofExec_toExec rest]
  | callRanEnd hs he child hr => simp [ofExec, toExec, ofExec_toExec child]
  | callRan hs he child hr rest => simp [ofExec, toExec, ofExec_toExec child, ofExec_toExec rest]
termination_by sizeOf t

def equivExec (r : Frame.Running) (out : Except Fault Frame.Exit) :
    Frame.Run r (.exit out) ≃ Exec r out :=
  ⟨toExec, ofExec, ofExec_toExec, toExec_ofExec⟩

def Node.ofDeriv (d : Exec.Deriv) : Node := ⟨d.running, d.outcome, ofExec d.run⟩

def Kept.ofFrame (f : Exec.Frame) : Kept := ⟨⟨f.running, _, ofExec f.run⟩, rfl⟩



private def observe {α} (f : Visit → Option α) (e : Event) : Option α := e.visit? >>= f

private theorem observe_visits {α} (f : Visit → Option α) (ev : List Event) :
    (ev.filterMap Event.visit?).filterMap f = ev.filterMap (observe f) := by
  induction ev with
  | nil => rfl
  | cons e es ih => cases e <;> simp [Event.visit?, observe, List.filterMap_cons, ih]

private theorem nodesFrom {r out} (d : Exec r out) (path k first enc idx) :
    (eventsFrom (ofExec d) path k first enc idx).filterMap (observe (fun v => some v.node)) =
      d.rawNodes.map Node.ofDeriv := by
  induction d generalizing path k first enc idx <;>
    simp [ofExec, eventsFrom, Exec.rawNodes, Node.ofDeriv, observe, Event.visit?,
      List.filterMap_cons, List.filterMap_append, *]

theorem rawNodes_bridge {r out} (d : Exec r out) : d.rawNodes.map Node.ofDeriv = rawNodes (ofExec d) := by
  conv_rhs => rw [rawNodes, visits, events, ← List.filterMap_eq_map', observe_visits, nodesFrom]

private def retained? (v : Visit) : Option Node := if v.kept then some v.node else none

private theorem retained_filter (vs : List Visit) :
    (vs.filter Visit.kept).map Visit.node = vs.filterMap retained? := by
  induction vs with
  | nil => rfl
  | cons v vs ih => cases h : v.kept <;> simp [retained?, h, ih]

private theorem filterMap_cons_opt {α β} (f : α → Option β) (x : α) (xs : List α) :
    (x :: xs).filterMap f = (f x).toList ++ xs.filterMap f := by
  rw [List.filterMap_cons]
  cases f x <;> rfl

private theorem observe_visit {α} (f : Visit → Option α) (v : Visit) : observe f (.visit v) = f v := rfl
private theorem observe_exit {α} (f : Visit → Option α) (v : Visit) : observe f (.exit v) = none := rfl
private theorem retained_visit_false (n path first enc) : retained? ⟨n, path, false, first, enc⟩ = none := rfl
private theorem retained_visit_true (n path first enc) : retained? ⟨n, path, true, first, enc⟩ = some n := rfl

private theorem retainedFrom {r out} (d : Exec r out) (path k first enc idx)
    (valid : k = true → Exec.finished out = true) :
    (eventsFrom (ofExec d) path k first enc idx).filterMap (observe retained?) =
      if k then d.retainedNodes.map Node.ofDeriv else [] := by
  induction d generalizing path k first enc idx with
  | halt | doneErr =>
    cases k
    · simp only [ofExec, eventsFrom, filterMap_cons_opt, observe_visit, retained_visit_false,
        Option.toList_none, List.filterMap_nil, List.nil_append, Bool.false_eq_true, ↓reduceIte]
    · have ho := valid rfl
      simp only [ofExec, eventsFrom, filterMap_cons_opt, observe_visit, retained_visit_true,
        Option.toList_some, List.filterMap_nil, List.append_nil,
        ↓reduceIte, Exec.retainedNodes, ho, List.map_cons, List.map_nil, Node.ofDeriv]
  | cont hs next ih | doneOk _ _ hs next ih =>
    cases k
    · simp only [ofExec, eventsFrom, filterMap_cons_opt, observe_visit, retained_visit_false,
        Option.toList_none, List.nil_append, Bool.false_eq_true, ↓reduceIte]
      exact ih path false false enc _ (fun h => by cases h)
    · have ho := valid rfl
      rw [Exec.retainedNodes]
      simp only [ofExec, eventsFrom, filterMap_cons_opt, observe_visit, retained_visit_true,
        Option.toList_some, List.cons_append, List.nil_append, ↓reduceIte, ho, List.map_cons,
        Node.ofDeriv]
      exact congrArg (List.cons _) (ih path true false enc _ valid)
  | runErr hs he child hr ih =>
    cases k
    · simp only [ofExec, eventsFrom, filterMap_cons_opt, List.filterMap_append, observe_visit,
        observe_exit, retained_visit_false, Option.toList_none, List.filterMap_nil, List.nil_append,
        List.append_nil, Bool.false_eq_true, ↓reduceIte]
      exact ih (path ++ [idx]) false true _ 0 (fun h => by cases h)
    · have ho := valid rfl
      rw [Exec.retainedNodes]
      simp only [ofExec, eventsFrom, filterMap_cons_opt, List.filterMap_append, observe_visit,
        observe_exit, retained_visit_true, Option.toList_some, Option.toList_none,
        List.filterMap_nil, List.nil_append, List.append_nil, List.cons_append, ↓reduceIte, ho,
        List.map_cons, List.map_nil, Node.ofDeriv]
      exact congrArg (List.cons _) (by simpa using ih (path ++ [idx]) false true _ 0 (fun h => by cases h))
  | @runOk r f pending pc cr raw state out hs he child hr next ihc ihn =>
    cases k <;> cases hc : Frame.settlementCommits f raw
    · simp only [ofExec, eventsFrom, filterMap_cons_opt, List.filterMap_append, observe_visit,
        observe_exit, retained_visit_false, Option.toList_none, List.nil_append,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [ihc _ false true _ 0 (fun h => by cases h), ihn path false false enc (idx + 1) (fun h => by cases h)]
      rfl
    · simp only [ofExec, eventsFrom, filterMap_cons_opt, List.filterMap_append, observe_visit,
        observe_exit, retained_visit_false, Option.toList_none, List.nil_append,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [ihc _ false true _ 0 (fun h => by cases h), ihn path false false enc (idx + 1) (fun h => by cases h)]
      rfl
    · have ho := valid rfl
      rw [Exec.retainedNodes]
      simp only [ofExec, eventsFrom, filterMap_cons_opt, List.filterMap_append, observe_visit,
        observe_exit, retained_visit_true, Option.toList_some, Option.toList_none,
        List.nil_append, List.cons_append, ↓reduceIte, ho, hc, Bool.true_and,
        List.map_cons, List.map_append, Node.ofDeriv]
      rw [ihc _ false true _ 0 (fun h => by cases h), ihn path true false enc (idx + 1) valid]
      rfl
    · have ho := valid rfl
      have hraw := Frame.finished_of_settlementCommits hc
      rw [Exec.retainedNodes]
      simp only [ofExec, eventsFrom, filterMap_cons_opt, List.filterMap_append, observe_visit,
        observe_exit, retained_visit_true, Option.toList_some, Option.toList_none,
        List.nil_append, List.cons_append, ↓reduceIte, ho, hc, Bool.true_and,
        List.map_cons, List.map_append, Node.ofDeriv]
      rw [ihc _ true true _ 0 (fun _ => hraw), ihn path true false enc (idx + 1) valid]
      rfl

theorem retainedNodes_bridge {r out} (d : Exec r out) :
    d.retainedNodes.map Node.ofDeriv = retainedNodes (ofExec d) := by
  cases h : Exec.finished out with
  | false => simp [Exec.retainedNodes_eq_nil_of_failed d h, retainedNodes, h]
  | true =>
    simp only [retainedNodes, h, ite_true, retained_filter, visits, events, observe_visits]
    simpa using (retainedFrom d [] true true [] 0 (fun _ => h)).symm

private def descendant? (v : Visit) : Option Kept := if v.path.isEmpty then none else v.toKept?

private theorem ofFrame_ofRun {r out} (d : Exec r out) (h : Exec.finished out = true) :
    Kept.ofFrame (Exec.Frame.ofRun d h) = ⟨⟨r, out, ofExec d⟩, h⟩ := by
  rcases out with fault | ⟨bytes, state⟩ | ⟨bytes, state⟩ | ⟨why, state⟩ <;> first | rfl | contradiction

private theorem descendant_not_frameStart (n path k enc) :
    descendant? ⟨n, path, k, false, enc⟩ = none := by
  simp [descendant?, Visit.toKept?]

private theorem descendant_not_kept (n path first enc) :
    descendant? ⟨n, path, false, first, enc⟩ = none := by
  simp [descendant?, Visit.toKept?]

private theorem descendant_child {r out} (d : Exec r out) (p i enc) (h : Exec.finished out = true) :
    descendant? ⟨⟨r, out, ofExec d⟩, p ++ [i], true, true, enc⟩ =
      some (Kept.ofFrame (Exec.Frame.ofRun d h)) := by
  simp [descendant?, Visit.toKept?, ofFrame_ofRun, h]

private theorem descendantsFrom {r out} (d : Exec r out) (path k first enc idx) :
    (eventsFrom (ofExec d) path k first enc idx).filterMap (observe descendant?) =
      (descendant? ⟨⟨r, out, ofExec d⟩, path, k, first, enc⟩).toList ++
        (if k then d.descendantFrames.map Kept.ofFrame else []) := by
  induction d generalizing path k first enc idx with
  | halt | doneErr =>
    simp only [ofExec, eventsFrom, filterMap_cons_opt, observe_visit, List.filterMap_nil,
      List.append_nil, Exec.descendantFrames, List.map_nil, ite_self]
  | cont hs next ih | doneOk _ _ hs next ih =>
    simp only [ofExec, eventsFrom, filterMap_cons_opt, observe_visit, ih,
      descendant_not_frameStart, Option.toList_none, List.nil_append, Exec.descendantFrames]
  | runErr hs he child hr ih =>
    simp only [ofExec, eventsFrom, filterMap_cons_opt, List.filterMap_append, observe_visit,
      observe_exit, List.filterMap_nil, Option.toList_none, List.append_nil, ih,
      descendant_not_kept, Bool.false_eq_true, ↓reduceIte, Exec.descendantFrames, List.map_nil,
      ite_self]
  | @runOk r f pending pc cr raw state out hs he child hr next ihc ihn =>
    cases k
    · simp only [ofExec, eventsFrom, filterMap_cons_opt, List.filterMap_append, observe_visit,
        observe_exit, Option.toList_none, List.nil_append, Bool.false_and, ihc,
        ihn, descendant_not_kept, descendant_not_frameStart, Bool.false_eq_true, ↓reduceIte]
    · cases hc : Frame.settlementCommits f raw
      · simp only [ofExec, eventsFrom, filterMap_cons_opt, List.filterMap_append, observe_visit,
          observe_exit, Option.toList_none, List.nil_append, Bool.true_and, hc,
          ihc, ihn, descendant_not_kept, descendant_not_frameStart, Bool.false_eq_true, ↓reduceIte,
          Exec.descendantFrames, dite_false]
      · simp only [ofExec, eventsFrom, filterMap_cons_opt, List.filterMap_append, observe_visit,
          observe_exit, Option.toList_none, List.nil_append, Bool.true_and, hc,
          ihc, ihn, descendant_not_frameStart,
          descendant_child child path idx _ (Frame.finished_of_settlementCommits hc),
          Option.toList_some, List.cons_append, ↓reduceIte, Exec.descendantFrames, dite_true,
          List.map_append, List.map_cons]

theorem descendantFrames_bridge {r out} (d : Exec r out) :
    d.descendantFrames.map Kept.ofFrame = descendantFrames (ofExec d) := by
  change _ = ((eventsFrom (ofExec d) [] true true [] 0).filterMap Event.visit?).filterMap descendant?
  rw [observe_visits, descendantsFrom]
  simp [descendant?]

theorem committedFrames_bridge {r out} (d : Exec r out) :
    d.committedFrames.map Kept.ofFrame = committedFrames (ofExec d) := by
  cases h : Exec.finished out <;> simp [Exec.committedFrames, committedFrames, h, ofFrame_ofRun, descendantFrames_bridge]

theorem spine_bridge {r out} (d : Exec r out) : d.parentNodes.map Node.ofDeriv = spine (ofExec d) := by
  induction d <;> simp [Exec.parentNodes, Node.ofDeriv, spine, ofExec, *]

/-- The old same-frame successor maps to the exact immediate successor in the surviving run. -/
theorem parentNext_bridge (d : Exec.Deriv) :
    d.parentNext.map Node.ofDeriv = (Node.ofDeriv d).parentNext := by
  rcases d with ⟨_, _, run⟩
  cases run <;> rfl

private theorem root_mem_parentNodes (root : Exec.Deriv) : root ∈ root.run.parentNodes := by
  rcases root with ⟨_, _, run⟩
  cases run <;> simp [Exec.parentNodes]

private theorem following {parent child : Exec.Deriv} (h : child.ParentStep parent) :
    parent.run.parentNodes = parent :: child.run.parentNodes := by
  rcases parent with ⟨r, out, run⟩
  cases run <;> simp [Exec.Deriv.ParentStep, Exec.Deriv.parentNext] at h <;> subst child <;> rfl

private theorem parentNodes_subset {a b : Exec.Deriv} (h : a.ParentPrefix b) :
    ∀ c ∈ b.run.parentNodes, c ∈ a.run.parentNodes := by
  induction h with
  | refl => exact fun _ h => h
  | tail _ edge ih =>
    intro c hc
    apply ih
    rw [following edge]
    exact List.mem_cons_of_mem _ hc

private theorem parentPrefix_of_mem {r out} (d : Exec r out) (b : Exec.Deriv) (h : b ∈ d.parentNodes) :
    Exec.Deriv.ParentPrefix ⟨r, out, d⟩ b := by
  cases d with
  | halt | doneErr | runErr => simp [Exec.parentNodes] at h; subst b; exact .refl
  | cont hs next | doneOk _ _ hs next | runOk _ _ _ hs next =>
    simp only [Exec.parentNodes, List.mem_cons] at h
    rcases h with rfl | h
    · exact .refl
    · exact Relation.ReflTransGen.head (show Exec.Deriv.ParentStep ⟨_, _, next⟩ _ from rfl)
        (parentPrefix_of_mem next b h)
termination_by sizeOf d

private theorem ofDeriv_injective : Function.Injective Node.ofDeriv := by
  let back (n : Node) : Exec.Deriv := ⟨n.start, n.exit, toExec n.run⟩
  intro ⟨ar, ao, arun⟩ ⟨br, bo, brun⟩ h
  have eq := congrArg back h
  simp only [back, Node.ofDeriv, toExec_ofExec] at eq
  exact eq

/-- The successor relation agrees in both directions on the surviving run. -/
theorem parentStep_bridge (root next : Exec.Deriv) :
    next.ParentStep root ↔ (Node.ofDeriv root).parentNext = some (Node.ofDeriv next) := by
  rw [Exec.Deriv.ParentStep, ← parentNext_bridge]
  cases root.parentNext with
  | none => simp
  | some node => simp only [Option.map_some, Option.some.injEq, ofDeriv_injective.eq_iff]

theorem parentPrefix_bridge (a b : Exec.Deriv) :
    a.ParentPrefix b ↔ (Node.ofDeriv a).Prefix (Node.ofDeriv b) := by
  rw [Node.prefix_iff_mem_spine]
  change _ ↔ Node.ofDeriv b ∈ spine (ofExec a.run)
  rw [← spine_bridge]
  constructor
  · intro h
    exact List.mem_map.mpr ⟨b, parentNodes_subset h b (root_mem_parentNodes b), rfl⟩
  · intro h
    obtain ⟨c, hc, eq⟩ := List.mem_map.mp h
    exact (ofDeriv_injective eq) ▸ parentPrefix_of_mem a.run c hc

end Jaune.Checked.Frame.Run

/-! ## Checked derivations forget memory into staged derivations

`Checked.Exec.toLegacy` maps a checked derivation node by node onto the staged derivation at the
forgotten start and outcome, through the driver squares `MemorySimulation.step`, `enter_toLegacy`,
`settle_toLegacy` and `resume_toLegacy`. Every view commutes with it. -/

namespace Jaune.Checked

/-- The staged form of a caller-resumption outcome. -/
def legacyResume : Except (Except Fault Frame.Exit) Frame.State →
    Except (Except Fault Jaune.Frame.Exit) Jaune.Frame.State
  | .error out => .error (out.map Frame.Exit.toLegacy)
  | .ok s => .ok s.toLegacy

variable [LegacyTransaction]

theorem resumeCaller_toLegacy (rules : ForkRules) (child : Frame) (p : Staging.Pending)
    (res : Except Fault Frame.Result) :
    Staging.resumeCaller rules child.toLegacy p res = legacyResume (resumeCaller rules child p res) := by
  cases res with
  | error f => rfl
  | ok result =>
    simp only [Staging.resumeCaller, resumeCaller,
      show child.toLegacy.checkpoint = child.checkpoint.toLegacy from rfl, resume_toLegacy]
    rcases resume rules p child.checkpoint result with f | (⟨reason, s⟩ | s) <;> rfl

theorem settle_bind_toLegacy (child : Frame) (raw : Except Fault Frame.Exit) :
    (raw.map Frame.Exit.toLegacy >>= Staging.settle child.toLegacy) = (raw >>= settle child) := by
  cases raw with
  | error f => rfl
  | ok e => exact settle_toLegacy child e

theorem Frame.settlementCommits_toLegacy (child : Frame) (raw : Except Fault Frame.Exit) :
    Staging.Frame.settlementCommits child.toLegacy (raw.map Frame.Exit.toLegacy) =
      Frame.settlementCommits child raw := by
  unfold Staging.Frame.settlementCommits Frame.settlementCommits
  rw [settle_bind_toLegacy]
  rcases raw >>= settle child with _ | res
  · rfl
  · cases res <;> rfl

omit [LegacyTransaction] in
theorem Exec.finished_toLegacy (out : Except Fault Frame.Exit) :
    Staging.Exec.finished (out.map Frame.Exit.toLegacy) = Exec.finished out := by
  rcases out with f | ⟨o, s⟩ | ⟨o, s⟩ | ⟨r, s⟩ <;> rfl

private theorem step_spawn_toLegacy {r : Frame.Running} {child pending pc}
    (hs : step r = .ok (.spawn child pending pc)) :
    Staging.step r.toLegacy = .ok (.spawn child.toLegacy pending pc) := by
  rw [MemorySimulation.step, hs]; rfl

private theorem enter_done_toLegacy {child : Frame} {result} (he : enter child = .done result) :
    Staging.enter child.toLegacy = .done result := by
  rw [enter_toLegacy, he]; rfl

private theorem enter_run_toLegacy {child : Frame} {cr} (he : enter child = .run cr) :
    Staging.enter child.toLegacy = .run cr.toLegacy := by
  rw [enter_toLegacy, he]; rfl

/-- Forget memory at every node of a checked derivation. -/
def Exec.toLegacy {r out} (run : Exec r out) :
    Staging.Exec r.toLegacy (out.map Frame.Exit.toLegacy) :=
  match run with
  | .halt hs => .halt (by rw [MemorySimulation.step, hs]; cases out <;> rfl)
  | .cont hs next => .cont (by rw [MemorySimulation.step, hs]; rfl) next.toLegacy
  | .doneErr hs he hr =>
    .doneErr (step_spawn_toLegacy hs) (enter_done_toLegacy he)
      (by rw [resumeCaller_toLegacy, show r.toLegacy.context.block.rules = r.context.block.rules from rfl, hr]; rfl)
  | .doneOk hs he hr next =>
    .doneOk (step_spawn_toLegacy hs) (enter_done_toLegacy he)
      (by rw [resumeCaller_toLegacy, show r.toLegacy.context.block.rules = r.context.block.rules from rfl, hr]; rfl)
      next.toLegacy
  | .runErr hs he child hr =>
    .runErr (step_spawn_toLegacy hs) (enter_run_toLegacy he) child.toLegacy
      (by rw [settle_bind_toLegacy, resumeCaller_toLegacy, show r.toLegacy.context.block.rules = r.context.block.rules from rfl, hr]; rfl)
  | .runOk hs he child hr next =>
    .runOk (step_spawn_toLegacy hs) (enter_run_toLegacy he) child.toLegacy
      (by rw [settle_bind_toLegacy, resumeCaller_toLegacy, show r.toLegacy.context.block.rules = r.context.block.rules from rfl, hr]; rfl)
      next.toLegacy
termination_by structural run

/-- A checked node, seen with its memory forgotten. -/
def Exec.Deriv.legacyObservation (node : Exec.Deriv) :
    Jaune.Frame.Running × Except Fault Jaune.Frame.Exit :=
  (node.running.toLegacy, node.outcome.map Frame.Exit.toLegacy)

/-- A checked retained frame, seen with its memory forgotten. -/
def Exec.Frame.legacyObservation (frame : Exec.Frame) : Jaune.Frame.Running × Bytes × Jaune.Frame.State :=
  (frame.running.toLegacy, frame.output, frame.post.toLegacy)

def Exec.Deriv.toLegacy (node : Exec.Deriv) : Staging.Exec.Deriv := ⟨_, _, node.run.toLegacy⟩

/-- Every reached node, in execution order, including nodes inside failed children. -/
theorem Exec.toLegacy_rawNodes {r out} (run : Exec r out) :
    run.toLegacy.rawNodes.map Staging.Exec.Deriv.observation =
      run.rawNodes.map Exec.Deriv.legacyObservation := by
  induction run with
  | halt | doneErr => rfl
  | cont hs next ih | doneOk _ _ hs next ih | runErr _ _ next hs ih =>
    exact congrArg (List.cons _) ih
  | runOk hs he child hr next ihc ihn =>
    simp only [Exec.toLegacy, Exec.rawNodes, Staging.Exec.rawNodes, List.map_cons, List.map_append]
    exact congrArg (List.cons _) (congrArg₂ List.append ihc ihn)

private theorem keptNodes {r out} (run : Exec r out) (commits : Exec.finished out = true) :
    run.toLegacy.retainedNodes.map Staging.Exec.Deriv.observation =
      run.retainedNodes.map Exec.Deriv.legacyObservation := by
  have fin : Staging.Exec.finished (out.map Frame.Exit.toLegacy) = true :=
    (Exec.finished_toLegacy out).trans commits
  induction run with
  | halt | doneErr | runErr =>
    rw [Staging.Exec.retainedNodes, Exec.retainedNodes]
    simp only [fin, commits, ite_true, List.map_cons, List.map_nil]
    rfl
  | cont hs next ih | doneOk _ _ hs next ih =>
    rw [Staging.Exec.retainedNodes, Exec.retainedNodes]
    simp only [fin, commits, ite_true, List.map_cons]
    exact congrArg (List.cons _) (ih commits fin)
  | @runOk r f pending pc cr raw state out hs he child hr next ihc ihn =>
    rw [Staging.Exec.retainedNodes, Exec.retainedNodes]
    simp only [fin, commits, ite_true, List.map_cons, List.map_append, Exec.toLegacy,
      Frame.settlementCommits_toLegacy]
    by_cases keep : Frame.settlementCommits f raw = true
    · have hraw := Frame.finished_of_settlementCommits keep
      simp only [keep, ite_true]
      exact congrArg (List.cons _) (congrArg₂ List.append
        (ihc hraw ((Exec.finished_toLegacy raw).trans hraw)) (ihn commits fin))
    · simp only [keep, Bool.false_eq_true, ite_false, List.map_nil, List.nil_append]
      exact congrArg (List.cons _) (ihn commits fin)

/-- The nodes whose effects survive settlement. -/
theorem Exec.toLegacy_retainedNodes {r out} (run : Exec r out) :
    run.toLegacy.retainedNodes.map Staging.Exec.Deriv.observation =
      run.retainedNodes.map Exec.Deriv.legacyObservation := by
  cases h : Exec.finished out with
  | true => exact keptNodes run h
  | false =>
    rw [Staging.Exec.retainedNodes_eq_nil_of_failed _ ((Exec.finished_toLegacy out).trans h),
      Exec.retainedNodes_eq_nil_of_failed _ h]
    rfl

private theorem frame_ofRun_toLegacy {r out} (run : Exec r out) (ok : Exec.finished out = true) :
    (Staging.Exec.Frame.ofRun run.toLegacy ((Exec.finished_toLegacy out).trans ok)).observation =
      (Exec.Frame.ofRun run ok).legacyObservation := by
  rcases out with f | ⟨o, s⟩ | ⟨o, s⟩ | ⟨reason, s⟩ <;> first | rfl | cases ok

private theorem descendants_toLegacy {r out} (run : Exec r out) :
    run.toLegacy.descendantFrames.map Staging.Exec.Frame.observation =
      run.descendantFrames.map Exec.Frame.legacyObservation := by
  induction run with
  | halt | doneErr | runErr => rfl
  | cont hs next ih | doneOk _ _ hs next ih => exact ih
  | @runOk r f pending pc cr raw state out hs he child hr next ihc ihn =>
    simp only [Exec.toLegacy, Staging.Exec.descendantFrames, Exec.descendantFrames]
    by_cases keep : Frame.settlementCommits f raw = true
    · have keep' : Staging.Frame.settlementCommits f.toLegacy (raw.map Frame.Exit.toLegacy) = true :=
        (Frame.settlementCommits_toLegacy f raw).trans keep
      simp only [keep, keep', dite_true, List.map_append, List.map_cons]
      exact congrArg₂ List.append
        (congrArg₂ List.cons (frame_ofRun_toLegacy child (Frame.finished_of_settlementCommits keep)) ihc) ihn
    · have keep' : ¬ Staging.Frame.settlementCommits f.toLegacy (raw.map Frame.Exit.toLegacy) = true := by
        rw [Frame.settlementCommits_toLegacy]; exact keep
      rw [dite_eq_right keep', dite_eq_right keep]
      exact ihn

/-- The frames kept after settlement, with output bytes and post-state. -/
theorem Exec.toLegacy_committedFrames {r out} (run : Exec r out) :
    run.toLegacy.committedFrames.map Staging.Exec.Frame.observation =
      run.committedFrames.map Exec.Frame.legacyObservation := by
  unfold Staging.Exec.committedFrames Exec.committedFrames
  by_cases ok : Exec.finished out = true
  · have fin := (Exec.finished_toLegacy out).trans ok
    simp only [fin, ok, dite_true, List.map_cons]
    exact congrArg₂ List.cons (frame_ofRun_toLegacy run ok) (descendants_toLegacy run)
  · have fin : ¬ Staging.Exec.finished (out.map Frame.Exit.toLegacy) = true := by
      rw [Exec.finished_toLegacy]; exact ok
    rw [dite_eq_right fin, dite_eq_right ok]
    rfl

theorem Exec.Deriv.ParentStep.toLegacy {next root : Exec.Deriv} (edge : next.ParentStep root) :
    next.toLegacy.ParentStep root.toLegacy := by
  rcases root with ⟨r, out, run⟩
  cases run <;> simp [Exec.Deriv.ParentStep, Exec.Deriv.parentNext] at edge <;> subst next <;> rfl

theorem Exec.Deriv.toLegacy_parentStep_iff (root : Exec.Deriv) (node : Staging.Exec.Deriv) :
    node.ParentStep root.toLegacy ↔ ∃ next : Exec.Deriv, next.ParentStep root ∧ next.toLegacy = node := by
  constructor
  · intro edge
    rcases root with ⟨r, out, run⟩
    cases run with
    | halt | doneErr | runErr => cases edge
    | cont hs next => exact ⟨_, rfl, Option.some.inj edge⟩
    | doneOk hs he hr next => exact ⟨_, rfl, Option.some.inj edge⟩
    | runOk hs he child hr next => exact ⟨_, rfl, Option.some.inj edge⟩
  · rintro ⟨next, edge, rfl⟩
    exact edge.toLegacy

/-- The continuation within one frame: a staged same-frame path is the image of a checked one. -/
theorem Exec.Deriv.toLegacy_parentPrefix_iff (start : Exec.Deriv) (node : Staging.Exec.Deriv) :
    start.toLegacy.ParentPrefix node ↔ ∃ tail : Exec.Deriv, start.ParentPrefix tail ∧ tail.toLegacy = node := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨_, .refl, rfl⟩
    | tail path edge ih =>
      obtain ⟨prior, prefixPath, rfl⟩ := ih
      obtain ⟨next, nextEdge, rfl⟩ := (toLegacy_parentStep_iff prior _).mp edge
      exact ⟨next, prefixPath.tail nextEdge, rfl⟩
  · rintro ⟨tail, path, rfl⟩
    induction path with
    | refl => exact .refl
    | tail path edge ih => exact ih.tail edge.toLegacy

end Jaune.Checked

/-! ## The composed bridges

The checked frame sequence reaches the staged frame sequence (`Staging.Frame.Run`) and W1's `Exec`
through `toExec`, `Exec.toLegacy`, the staged bridges of `Bridge/G3/FrameViews.lean` and the W1
bridges of `Bridge/G2b/FinalChronology.lean`, `FinalPrefix.lean` and `FinalRetained.lean`. -/

namespace Jaune.Staging.Exec.Deriv

/-- Two staged derivations from the same start are the same node: the outcome is the
interpreter's, and the derivation is unique. -/
theorem eq_of_running (a b : Staging.Exec.Deriv) (h : a.running = b.running) : a = b := by
  rcases a with ⟨r, o, d⟩
  rcases b with ⟨r', o', d'⟩
  dsimp only at h
  subst h
  have ho : o = o' :=
    ((Jaune.Staging.exec_iff_exec_eq r o).mp ⟨d⟩).symm.trans ((Jaune.Staging.exec_iff_exec_eq r o').mp ⟨d'⟩)
  subst ho
  rw [← Staging.Frame.Run.toExec_ofExec d, ← Staging.Frame.Run.toExec_ofExec d',
    Subsingleton.elim (Staging.Frame.Run.ofExec d) (Staging.Frame.Run.ofExec d')]

end Jaune.Staging.Exec.Deriv

namespace Jaune.Checked.Frame.Run

variable [LegacyTransaction]

/-- A checked node, seen with its memory forgotten. -/
def Node.legacyObservation (n : Node) : Jaune.Frame.Running × Except Fault Jaune.Frame.Exit :=
  (n.start.toLegacy, n.exit.map Frame.Exit.toLegacy)

/-- A kept checked frame, seen with its memory forgotten: start, output bytes and post-state. -/
def Kept.legacyObservation : Kept → Jaune.Frame.Running × Bytes × Jaune.Frame.State
  | ⟨⟨r, .ok (.finished output post), _⟩, _⟩ => (r.toLegacy, output, post.toLegacy)
  | ⟨⟨_, .error _, _⟩, h⟩ | ⟨⟨_, .ok (.reverted ..), _⟩, h⟩ | ⟨⟨_, .ok (.halted ..), _⟩, h⟩ =>
    absurd h Bool.false_ne_true

/-- A staged node's observation. -/
def _root_.Jaune.Staging.Frame.Run.Node.observation (n : Staging.Frame.Run.Node) :
    Jaune.Frame.Running × Except Fault Jaune.Frame.Exit := (n.start, n.exit)

/-- A staged kept frame's observation. -/
def _root_.Jaune.Staging.Frame.Run.Kept.observation : Staging.Frame.Run.Kept →
    Jaune.Frame.Running × Bytes × Jaune.Frame.State
  | ⟨⟨r, .ok (.finished output post), _⟩, _⟩ => (r, output, post)
  | ⟨⟨_, .error _, _⟩, h⟩ | ⟨⟨_, .ok (.reverted ..), _⟩, h⟩ | ⟨⟨_, .ok (.halted ..), _⟩, h⟩ =>
    absurd h Bool.false_ne_true

/-- The staged frame sequence of a checked one, memory forgotten. -/
def toLegacy {r out} (t : Frame.Run r (.exit out)) :
    Staging.Frame.Run r.toLegacy (.exit (out.map Frame.Exit.toLegacy)) :=
  Staging.Frame.Run.ofExec (toExec t).toLegacy

private theorem rawNodes_exec {r out} (t : Frame.Run r (.exit out)) :
    (rawNodes t).map Node.legacyObservation = (toExec t).rawNodes.map Exec.Deriv.legacyObservation := by
  conv_lhs => rw [← ofExec_toExec t, ← rawNodes_bridge, List.map_map]
  rfl

private theorem retainedNodes_exec {r out} (t : Frame.Run r (.exit out)) :
    (retainedNodes t).map Node.legacyObservation =
      (toExec t).retainedNodes.map Exec.Deriv.legacyObservation := by
  conv_lhs => rw [← ofExec_toExec t, ← retainedNodes_bridge, List.map_map]
  rfl

private theorem kept_ofFrame (f : Exec.Frame) :
    (Kept.ofFrame f).legacyObservation = f.legacyObservation := rfl

private theorem committedFrames_exec {r out} (t : Frame.Run r (.exit out)) :
    (committedFrames t).map Kept.legacyObservation =
      (toExec t).committedFrames.map Exec.Frame.legacyObservation := by
  conv_lhs => rw [← ofExec_toExec t, ← committedFrames_bridge, List.map_map]
  rfl

/-- S5, every reached node in execution order: the checked view is the staged view. -/
theorem rawNodes_toLegacy {r out} (t : Frame.Run r (.exit out)) :
    (rawNodes t).map Node.legacyObservation = (Staging.Frame.Run.rawNodes (toLegacy t)).map
      Staging.Frame.Run.Node.observation := by
  rw [rawNodes_exec, ← Exec.toLegacy_rawNodes, toLegacy, ← Staging.Frame.Run.rawNodes_bridge, List.map_map]
  rfl

/-- S5, the frames kept after settlement, as nodes: the checked view is the staged view. -/
theorem retainedNodes_toLegacy {r out} (t : Frame.Run r (.exit out)) :
    (retainedNodes t).map Node.legacyObservation = (Staging.Frame.Run.retainedNodes (toLegacy t)).map
      Staging.Frame.Run.Node.observation := by
  rw [retainedNodes_exec, ← Exec.toLegacy_retainedNodes, toLegacy,
    ← Staging.Frame.Run.retainedNodes_bridge, List.map_map]
  rfl

/-- S5, the frames kept after settlement, with output and post-state: checked equals staged. -/
theorem committedFrames_toLegacy {r out} (t : Frame.Run r (.exit out)) :
    (committedFrames t).map Kept.legacyObservation = (Staging.Frame.Run.committedFrames (toLegacy t)).map
      Staging.Frame.Run.Kept.observation := by
  rw [committedFrames_exec, ← Exec.toLegacy_committedFrames, toLegacy,
    ← Staging.Frame.Run.committedFrames_bridge, List.map_map]
  congr 1

private theorem rootFrames_toLegacy (frame : Frame) {running raw old}
    (run : Frame.Run running (.exit raw)) (waiting : Staging.Exec running.toLegacy old)
    (outcome : old = raw.map Frame.Exit.toLegacy) :
    (Root.frames ⟨frame, running, raw, run⟩).map Kept.legacyObservation =
      (Staging.Root.frames ⟨frame.toLegacy, running.toLegacy, _, waiting⟩).map
        Staging.Exec.Frame.observation := by
  subst old
  dsimp only [Root.frames, Staging.Root.frames]
  rw [Frame.settlementCommits_toLegacy]
  split
  · rw [committedFrames_toLegacy, Subsingleton.elim (toLegacy run) (Staging.Frame.Run.ofExec waiting),
      ← Staging.Frame.Run.committedFrames_bridge, List.map_map]
    rfl
  · rfl

/-- A checked root retains exactly the same ordered frames and post-states as its staged entry. -/
theorem _root_.Jaune.Checked.Root.ofEntry_frames_toLegacy
    (frame : Frame) (running : Frame.Running) :
    ((Root.ofEntry frame running).frames.map Kept.legacyObservation) =
      ((Staging.Root.ofEntry frame.toLegacy running.toLegacy).frames.map Staging.Exec.Frame.observation) := by
  exact rootFrames_toLegacy frame _ _ (exec_toLegacy running)

/-- The staged node of a checked one. -/
def Node.toLegacy (n : Node) : Staging.Frame.Run.Node := ⟨_, _, Checked.Frame.Run.toLegacy n.run⟩

omit [LegacyTransaction] in
theorem Node.ofDeriv_surjective (n : Node) : ∃ d, Node.ofDeriv d = n :=
  ⟨⟨_, _, toExec n.run⟩, by rcases n with ⟨s, o, t⟩; simp [Node.ofDeriv]⟩

omit [LegacyTransaction] in
private theorem staging_ofDeriv_surjective (n : Staging.Frame.Run.Node) :
    ∃ d, Staging.Frame.Run.Node.ofDeriv d = n :=
  ⟨⟨_, _, Staging.Frame.Run.toExec n.run⟩, by rcases n with ⟨s, o, t⟩; simp [Staging.Frame.Run.Node.ofDeriv]⟩

omit [LegacyTransaction] in
private theorem staging_ofDeriv_injective {a b : Staging.Exec.Deriv}
    (h : Staging.Frame.Run.Node.ofDeriv a = Staging.Frame.Run.Node.ofDeriv b) : a = b := by
  have eq := congrArg (fun n : Staging.Frame.Run.Node =>
    (⟨n.start, n.exit, Staging.Frame.Run.toExec n.run⟩ : Staging.Exec.Deriv)) h
  rcases a with ⟨ar, ao, arun⟩
  rcases b with ⟨br, bo, brun⟩
  simpa [Staging.Frame.Run.Node.ofDeriv] using eq

theorem Node.ofDeriv_toLegacy (d : Exec.Deriv) :
    (Node.ofDeriv d).toLegacy = Staging.Frame.Run.Node.ofDeriv d.toLegacy := by
  simp [Node.toLegacy, Checked.Frame.Run.toLegacy, Node.ofDeriv, Exec.Deriv.toLegacy,
    Staging.Frame.Run.Node.ofDeriv]

/-- S5, the continuation within one frame: a staged same-frame prefix from a checked node's image
ends exactly at the image of a checked same-frame prefix. -/
theorem prefix_toLegacy_iff (a : Node) (n : Staging.Frame.Run.Node) :
    a.toLegacy.Prefix n ↔ ∃ b : Node, a.Prefix b ∧ b.toLegacy = n := by
  obtain ⟨da, rfl⟩ := Node.ofDeriv_surjective a
  obtain ⟨dn, rfl⟩ := staging_ofDeriv_surjective n
  rw [Node.ofDeriv_toLegacy, ← Staging.Frame.Run.parentPrefix_bridge, Exec.Deriv.toLegacy_parentPrefix_iff]
  constructor
  · rintro ⟨tail, path, rfl⟩
    exact ⟨Node.ofDeriv tail, (parentPrefix_bridge _ _).mp path, Node.ofDeriv_toLegacy tail⟩
  · rintro ⟨b, path, eq⟩
    obtain ⟨db, rfl⟩ := Node.ofDeriv_surjective b
    rw [Node.ofDeriv_toLegacy] at eq
    exact ⟨db, (parentPrefix_bridge _ _).mpr path, staging_ofDeriv_injective eq⟩

section W1

variable {pc : Nat} {sevm : Sevm} {devm : Devm} {out' : Execution}

private theorem deriv_eq {r out} (t : Frame.Run r (.exit out)) (run : _root_.Jaune.Exec pc sevm devm out')
    (clean : devm.output = []) (hs : Jaune.Frame.Running.ofEvm ⟨pc, sevm, devm⟩ = r.toLegacy) :
    (⟨_, _, (toExec t).toLegacy⟩ : Staging.Exec.Deriv) = ⟨_, _, run.observe clean⟩ :=
  Staging.Exec.Deriv.eq_of_running _ _ hs.symm

/-- S5 composed to W1, every reached node in execution order: the checked view of a run equals
W1's `Exec.rawNodes` of the W1 derivation from the same start, node by node. -/
theorem rawNodes_w1 {r out} (t : Frame.Run r (.exit out)) (run : _root_.Jaune.Exec pc sevm devm out')
    (clean : devm.output = []) (hs : Jaune.Frame.Running.ofEvm ⟨pc, sevm, devm⟩ = r.toLegacy) :
    (rawNodes t).map Node.legacyObservation = run.rawNodes.map _root_.Jaune.Exec.Deriv.frameObservation := by
  rw [rawNodes_exec, ← Exec.toLegacy_rawNodes, ← run.observe_rawNodes clean]
  exact congrArg (fun d : Staging.Exec.Deriv => d.run.rawNodes.map Staging.Exec.Deriv.observation)
    (deriv_eq t run clean hs)

/-- S5 composed to W1, the frames kept after settlement, as nodes: W1's `Exec.retainedNodes`. -/
theorem retainedNodes_w1 {r out} (t : Frame.Run r (.exit out)) (run : _root_.Jaune.Exec pc sevm devm out')
    (clean : devm.output = []) (hs : Jaune.Frame.Running.ofEvm ⟨pc, sevm, devm⟩ = r.toLegacy) :
    (retainedNodes t).map Node.legacyObservation =
      run.retainedNodes.map _root_.Jaune.Exec.Deriv.frameObservation := by
  rw [retainedNodes_exec, ← Exec.toLegacy_retainedNodes, ← run.observe_retainedNodes clean]
  exact congrArg (fun d : Staging.Exec.Deriv => d.run.retainedNodes.map Staging.Exec.Deriv.observation)
    (deriv_eq t run clean hs)

/-- S5 composed to W1, the frames kept after settlement with output bytes and complete post-state:
W1's `Exec.committedFrames`. -/
theorem committedFrames_w1 {r out} (t : Frame.Run r (.exit out)) (run : _root_.Jaune.Exec pc sevm devm out')
    (clean : devm.output = []) (hs : Jaune.Frame.Running.ofEvm ⟨pc, sevm, devm⟩ = r.toLegacy) :
    (committedFrames t).map Kept.legacyObservation =
      run.committedFrames.map _root_.Jaune.Exec.Frame.frameObservation := by
  rw [committedFrames_exec, ← Exec.toLegacy_committedFrames, ← run.observe_committedFrames clean]
  exact congrArg (fun d : Staging.Exec.Deriv => d.run.committedFrames.map Staging.Exec.Frame.observation)
    (deriv_eq t run clean hs)

/-- S5 composed to W1, the continuation within one frame: from a checked node whose image is the
image of a W1 node, the staged same-frame prefixes reached through checked prefixes are exactly
those reached through W1's `Exec.Deriv.ParentPrefix`. -/
theorem prefix_w1_iff (a : Exec.Deriv) (start : _root_.Jaune.Exec.Deriv) (clean : start.devm.output = [])
    (hs : Jaune.Frame.Running.ofEvm ⟨start.pc, start.sevm, start.devm⟩ = a.running.toLegacy)
    (n : Staging.Exec.Deriv) :
    (∃ b : Exec.Deriv, (Node.ofDeriv a).Prefix (Node.ofDeriv b) ∧ b.toLegacy = n) ↔
      ∃ tail : _root_.Jaune.Exec.Deriv, start.ParentPrefix tail ∧ ∃ hc, tail.observe hc = n := by
  have eq : a.toLegacy = start.observe clean := Staging.Exec.Deriv.eq_of_running _ _ hs.symm
  rw [← _root_.Jaune.Exec.Deriv.observe_parentPrefix_iff clean, ← eq, Exec.Deriv.toLegacy_parentPrefix_iff]
  simp only [← parentPrefix_bridge]

end W1

end Jaune.Checked.Frame.Run
