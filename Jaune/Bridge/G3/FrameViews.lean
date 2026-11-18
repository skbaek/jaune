import Jaune.Bridge.G3.FrameRun
import Jaune.FrameRun.Decompose
import Jaune.MessageCall.FinalDerivOrder

namespace Jaune.Staging.Frame.Run

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

end Jaune.Staging.Frame.Run
