import Jaune.FrameRun.Views
import Jaune.FrameRun.Prefix

/-!
# The calls of a frame run (goal `jaune-shape-and-names-v1`, G2b, U102)

`calls t` lists every message a run sent, at every depth and in execution order, with the child
frame and the result the caller resumed with. A child that finished at entry (a precompile, a
failed value transfer) is a call with no run of its own. `keptCalls t` keeps the calls whose
caller step survives every enclosing settlement, with the propagation `eventsFrom` uses.

The traversal is `eventsFrom`'s: the same path, kept flag and child counter. `Event` carries no
child result, so the calls have their own recursion instead of a projection of `events`.
-/

namespace Jaune.Frame.Run

/-- A message a running frame sent, and what came back. -/
structure Call where
  /-- The caller's visit at the call step: its node, path, kept flag and enclosing contexts. -/
  site : Visit
  /-- The child counter at the call step: the number of calls the caller frame made before it. -/
  index : Nat
  /-- The frame opened. `child.message` is the message sent. -/
  child : Frame
  /-- What the caller's resumption consumed: handed back at entry, or after the child settled. -/
  result : Except Fault Frame.Result
  /-- The child's own run, when it ran code. -/
  ran : Option Node

/-- The path of the child frame: the caller's path extended by the call's index. -/
def Call.path (c : Call) : List Nat := c.site.path ++ [c.index]

/-- The calls of a run, with `eventsFrom`'s path, kept flag, enclosing contexts and counter. -/
def callsFrom {r out} (t : Frame.Run r (.exit out)) (path : List Nat)
    (kept frameStart : Bool) (enclosing : List CallContext) (counter : Nat) : List Call :=
  let here : Visit := ⟨⟨r, out, t⟩, path, kept, frameStart, enclosing⟩
  match t with
  | .halt _ => []
  | .next _ rest => callsFrom rest path kept false enclosing counter
  | .callDone (child := f) (result := v) _ _ _ rest =>
    ⟨here, counter, f, v, none⟩ :: callsFrom rest path kept false enclosing (counter + 1)
  | .callRan (child := f) (cr := cr) (raw := raw) _ _ child _ rest =>
    ⟨here, counter, f, raw >>= settle f, some ⟨cr, raw, child⟩⟩ ::
      (callsFrom child (path ++ [counter]) (kept && Frame.settlementCommits f raw) true
        (r.context :: enclosing) 0 ++ callsFrom rest path kept false enclosing (counter + 1))
  | .callDoneEnd (child := f) (result := v) .. => [⟨here, counter, f, v, none⟩]
  | .callRanEnd (child := f) (cr := cr) (raw := raw) _ _ child _ =>
    [⟨here, counter, f, raw >>= settle f, some ⟨cr, raw, child⟩⟩] ++
      callsFrom child (path ++ [counter]) false true (r.context :: enclosing) 0
termination_by sizeOf t

/-- Every call of a run, in execution order, at every depth, including children that finished
at entry. Reverted calls are included. -/
def calls {r out} (t : Frame.Run r (.exit out)) : List Call := callsFrom t [] true true [] 0

/-- The calls whose caller step survives every enclosing settlement. A root that does not finish
keeps none, as for `retainedNodes`. -/
def keptCalls {r out} (t : Frame.Run r (.exit out)) : List Call :=
  if Frame.rawFinished out then (calls t).filter (·.site.kept) else []

/-! ### What each call records -/

/-- What a call step establishes: the caller stepped to the spawn, and the child either finished
at entry with the result, or ran from its entered state and settled to it. -/
def Call.Valid (c : Call) : Prop :=
  (∃ pending pc, step c.site.node.start = .ok (.spawn c.child pending pc)) ∧
    match c.ran with
    | none => enter c.child = .done c.result
    | some n => enter c.child = .run n.start ∧ c.result = n.exit >>= settle c.child

theorem callsFrom_valid {r out} (t : Frame.Run r (.exit out)) (path kept frameStart enclosing counter) :
    ∀ c ∈ callsFrom t path kept frameStart enclosing counter, c.Valid := by
  cases t with
  | halt => simp [callsFrom]
  | next hs rest =>
    rw [callsFrom]
    exact callsFrom_valid rest _ _ _ _ _
  | callDone hs he hr rest =>
    rw [callsFrom]
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨⟨_, _, hs⟩, he⟩
    · exact callsFrom_valid rest _ _ _ _ _ c hc
  | callRan hs he child hr rest =>
    rw [callsFrom]
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨⟨_, _, hs⟩, he, rfl⟩
    · rcases List.mem_append.mp hc with hc | hc
      · exact callsFrom_valid child _ _ _ _ _ c hc
      · exact callsFrom_valid rest _ _ _ _ _ c hc
  | callDoneEnd hs he hr =>
    rw [callsFrom]
    intro c hc
    rcases List.mem_singleton.mp hc with rfl
    exact ⟨⟨_, _, hs⟩, he⟩
  | callRanEnd hs he child hr =>
    rw [callsFrom]
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_singleton.mp hc with rfl
      exact ⟨⟨_, _, hs⟩, he, rfl⟩
    · exact callsFrom_valid child _ _ _ _ _ c hc
termination_by sizeOf t

theorem calls_valid {r out} {t : Frame.Run r (.exit out)} {c : Call} (h : c ∈ calls t) : c.Valid :=
  callsFrom_valid t _ _ _ _ _ c h

/-- The caller of every call stepped to that call's spawn. -/
theorem calls_step_spawn {r out} {t : Frame.Run r (.exit out)} {c : Call} (h : c ∈ calls t) :
    ∃ pending pc, step c.site.node.start = .ok (.spawn c.child pending pc) :=
  (calls_valid h).1

/-- Every call's result is the one its child hands back, at entry or after its run. -/
theorem calls_childResult {r out} {t : Frame.Run r (.exit out)} {c : Call} (h : c ∈ calls t) :
    Frame.ChildResult c.child c.result := by
  obtain ⟨_, hv⟩ := calls_valid h
  cases hran : c.ran with
  | none => rw [hran] at hv; exact .done hv
  | some n =>
    rw [hran] at hv
    obtain ⟨he, hres⟩ := hv
    have hexec : exec n.start = n.exit := (exec_iff ..).mp ⟨n.run⟩
    rw [hres, ← hexec]
    exact .ran he

/-- A call has no run exactly when its child finished at entry with the call's result. -/
theorem calls_ran_eq_none_iff {r out} {t : Frame.Run r (.exit out)} {c : Call} (h : c ∈ calls t) :
    c.ran = none ↔ enter c.child = .done c.result := by
  obtain ⟨_, hv⟩ := calls_valid h
  cases hran : c.ran with
  | none => rw [hran] at hv; exact ⟨(fun _ => hv), (fun _ => rfl)⟩
  | some n =>
    rw [hran] at hv
    refine ⟨(fun h => by cases h), (fun hd => ?_)⟩
    rw [hv.1] at hd
    cases hd

/-- A call that ran entered its child at the run's start and settled the run's raw outcome. -/
theorem calls_ran_eq_some {r out} {t : Frame.Run r (.exit out)} {c : Call} {n : Node}
    (h : c ∈ calls t) (hran : c.ran = some n) :
    enter c.child = .run n.start ∧ c.result = n.exit >>= settle c.child := by
  obtain ⟨_, hv⟩ := calls_valid h
  rw [hran] at hv
  exact hv

/-! ### Completeness and agreement with the existing views -/

/-- Whether a visit's node is a call step. -/
def Visit.spawned? (v : Visit) : Option Frame := v.node.head.spawned?

@[simp] private theorem filterMap_visit_exit (v : Visit) (es : List Event) :
    (Event.exit v :: es).filterMap Event.visit? = es.filterMap Event.visit? := rfl

private theorem callsFrom_sites {r out} (t : Frame.Run r (.exit out)) (path kept frameStart enclosing counter) :
    (callsFrom t path kept frameStart enclosing counter).map (fun c => (c.site, c.child)) =
      ((eventsFrom t path kept frameStart enclosing counter).filterMap Event.visit?).filterMap
        (fun v => v.spawned?.map (v, ·)) := by
  cases t with
  | halt => simp [callsFrom, eventsFrom, Event.visit?, Visit.spawned?, Node.head, Head.spawned?]
  | next hs rest =>
    rw [callsFrom, eventsFrom, callsFrom_sites rest]
    simp [Event.visit?, Visit.spawned?, Node.head, Head.spawned?]
  | callDone hs he hr rest =>
    rw [callsFrom, eventsFrom, List.map_cons, callsFrom_sites rest]
    simp [Event.visit?, Visit.spawned?, Node.head, Head.spawned?]
  | callRan hs he child hr rest =>
    rw [callsFrom, eventsFrom, List.map_cons, List.map_append, callsFrom_sites child, callsFrom_sites rest]
    simp [Event.visit?, Visit.spawned?, Node.head, Head.spawned?, List.filterMap_append]
  | callDoneEnd hs he hr =>
    rw [callsFrom, eventsFrom]
    simp [Event.visit?, Visit.spawned?, Node.head, Head.spawned?]
  | callRanEnd hs he child hr =>
    rw [callsFrom, eventsFrom, List.map_append, callsFrom_sites child]
    simp [Event.visit?, Visit.spawned?, Node.head, Head.spawned?, List.filterMap_append]
termination_by sizeOf t

/-- Completeness: the calls are exactly the call steps among the visits, in order, each with the
child its step spawned. Children that finished at entry are included. -/
theorem calls_complete {r out} (t : Frame.Run r (.exit out)) :
    (calls t).map (fun c => (c.site, c.child)) = (visits t).filterMap (fun v => v.spawned?.map (v, ·)) :=
  callsFrom_sites t _ _ _ _ _

/-- The number of calls is the number of call steps, the count `eventsFrom`'s child counters keep. -/
theorem calls_length {r out} (t : Frame.Run r (.exit out)) :
    (calls t).length = ((visits t).filter (fun v => v.spawned?.isSome)).length := by
  have h := congrArg List.length (calls_complete t)
  rw [List.length_map] at h
  rw [h]
  clear h
  induction visits t with
  | nil => rfl
  | cons v vs ih =>
    cases hv : v.spawned? <;> simp [hv, ih]

/-- Every call's site is one of the run's visits. -/
theorem calls_site_mem {r out} {t : Frame.Run r (.exit out)} {c : Call} (h : c ∈ calls t) :
    c.site ∈ visits t := by
  have hm : (c.site, c.child) ∈ (calls t).map (fun c => (c.site, c.child)) := List.mem_map_of_mem h
  rw [calls_complete] at hm
  obtain ⟨v, hv, hx⟩ := List.mem_filterMap.mp hm
  cases hs : v.spawned? with
  | none => rw [hs] at hx; cases hx
  | some f =>
    rw [hs] at hx
    cases hx
    exact hv

private def framePair (v : Visit) : List Nat × Node := (v.path, v.node)

private def Call.ranPair (c : Call) : Option (List Nat × Node) := c.ran.map (c.path, ·)

private theorem callsFrom_frames {r out} (t : Frame.Run r (.exit out)) (path kept frameStart enclosing counter) :
    (((eventsFrom t path kept frameStart enclosing counter).filterMap Event.visit?).filter
        Visit.frameStart).map framePair =
      (if frameStart then [(path, ⟨r, out, t⟩)] else []) ++
        (callsFrom t path kept frameStart enclosing counter).filterMap Call.ranPair := by
  cases t with
  | halt => cases frameStart <;> simp [callsFrom, eventsFrom, Event.visit?, framePair]
  | next hs rest =>
    rw [callsFrom, eventsFrom, List.filterMap_cons]
    cases frameStart <;> simp [Event.visit?, framePair, callsFrom_frames rest]
  | callDone hs he hr rest =>
    rw [callsFrom, eventsFrom, List.filterMap_cons, List.filterMap_cons]
    cases frameStart <;>
      simp [Event.visit?, framePair, Call.ranPair, callsFrom_frames rest]
  | callRan hs he child hr rest =>
    rw [callsFrom, eventsFrom, List.filterMap_cons, List.filterMap_cons, List.filterMap_append,
      List.filterMap_append]
    cases frameStart <;>
      simp [Event.visit?, List.filter_append, framePair, Call.ranPair, Call.path,
        callsFrom_frames child, callsFrom_frames rest]
  | callDoneEnd hs he hr =>
    rw [callsFrom, eventsFrom]
    cases frameStart <;> simp [Event.visit?, framePair, Call.ranPair]
  | callRanEnd hs he child hr =>
    rw [callsFrom, eventsFrom, List.filterMap_cons, List.filterMap_append, List.filterMap_append]
    cases frameStart <;>
      simp [Event.visit?, framePair, Call.ranPair, Call.path,
        callsFrom_frames child]
termination_by sizeOf t

/-- Agreement with `visits`: the frame starts of a run are its root and, at the same paths and in
the same order, the runs of its calls. -/
theorem calls_frameStarts {r out} (t : Frame.Run r (.exit out)) :
    ((visits t).filter Visit.frameStart).map (fun v => (v.path, v.node)) =
      ([], ⟨r, out, t⟩) :: (calls t).filterMap (fun c => c.ran.map (c.path, ·)) := by
  exact callsFrom_frames t [] true true [] 0

/-- Agreement with `frames`: the frames of a run are its root and the runs of its calls. -/
theorem frames_eq_calls {r out} (t : Frame.Run r (.exit out)) :
    frames t = ⟨r, out, t⟩ :: (calls t).filterMap Call.ran := by
  have h := congrArg (List.map Prod.snd) (calls_frameStarts t)
  simp only [List.map_map, List.map_cons, List.map_filterMap] at h
  simpa [frames, Function.comp_def, Option.map_map] using h

/-- Agreement with `rawNodes`: every call that ran lists its run among the run's nodes. -/
theorem calls_ran_mem_rawNodes {r out} {t : Frame.Run r (.exit out)} {c : Call} {n : Node}
    (h : c ∈ calls t) (hran : c.ran = some n) : n ∈ rawNodes t := by
  have hf : n ∈ frames t := by
    rw [frames_eq_calls]
    exact List.mem_cons_of_mem _ (List.mem_filterMap.mpr ⟨c, h, hran⟩)
  simp only [frames, List.mem_map, List.mem_filter] at hf
  obtain ⟨v, ⟨hv, _⟩, rfl⟩ := hf
  exact List.mem_map_of_mem hv

/-! ### Kept calls -/

theorem keptCalls_eq_nil_of_failed {r out} (t : Frame.Run r (.exit out))
    (h : Frame.rawFinished out = false) : keptCalls t = [] := by
  simp [keptCalls, h]

theorem keptCalls_of_finished {r out} (t : Frame.Run r (.exit out))
    (h : Frame.rawFinished out = true) : keptCalls t = (calls t).filter (·.site.kept) := by
  simp [keptCalls, h]

theorem keptCalls_sublist {r out} (t : Frame.Run r (.exit out)) : (keptCalls t).Sublist (calls t) := by
  unfold keptCalls
  split
  · exact List.filter_sublist
  · exact List.nil_sublist _

theorem mem_keptCalls {r out} {t : Frame.Run r (.exit out)} {c : Call} :
    c ∈ keptCalls t ↔ Frame.rawFinished out = true ∧ c ∈ calls t ∧ c.site.kept = true := by
  unfold keptCalls
  split <;> simp_all

/-- Agreement with `retainedNodes`: a kept call's caller node is retained. -/
theorem keptCalls_site_mem_retainedNodes {r out} {t : Frame.Run r (.exit out)} {c : Call}
    (h : c ∈ keptCalls t) : c.site.node ∈ retainedNodes t := by
  obtain ⟨hf, hc, hk⟩ := mem_keptCalls.mp h
  simp only [retainedNodes, hf, ite_true, List.mem_map, List.mem_filter]
  exact ⟨c.site, ⟨calls_site_mem hc, hk⟩, rfl⟩

end Jaune.Frame.Run
