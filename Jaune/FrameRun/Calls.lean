import Jaune.FrameRun.Views
import Jaune.FrameRun.Prefix

/-!
# The calls of a frame run (goal `jaune-shape-and-names-v1`, G2b, U102)

`calls t` lists every message a run sent, at every depth and in execution order, with the child
frame and the result the caller resumed with. A child that finished at entry (a precompile, a
failed value transfer) is a call with no run of its own. `keptCalls t` keeps the calls whose
caller step survives the settlements of the run's enclosing frames, with the propagation
`eventsFrom` uses. It filters on the caller's survival only: a kept call's own child may have
reverted, halted or failed its code deposit. The root frame of `t` is not a call.

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

/-- The calls whose caller step survives the settlements of the frames enclosing it inside `t`,
when the root `t` itself finishes. A root that does not finish keeps none, as for `retainedNodes`.

This filters on the caller's survival only (`c.site.kept`), not on the call's own outcome: a kept
call's own child may have reverted, halted or failed its code deposit, and `c.result` says which.
For calls whose effects persist, filter further on `c.result`; unlike `committedFrames` and
`descendantFrames`, this view does not check the child's settlement. The root's own
settlement, such as a top-level creation's code deposit, is not applied here; `Root.keptCalls`
applies it. -/
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

/-- A node's first step spawns exactly the child its head records. -/
theorem Node.spawned?_eq_some_iff (n : Node) {f : Frame} :
    n.head.spawned? = some f ↔ ∃ pending pc, step n.start = .ok (.spawn f pending pc) := by
  obtain ⟨start, exit, run⟩ := n
  cases run with
  | halt hs =>
    simp only [Node.head, Head.spawned?, reduceCtorEq, false_iff]
    rintro ⟨pending, pc, h⟩
    rw [hs] at h
    cases exit <;> simp [Except.map] at h
  | next hs rest =>
    simp only [Node.head, Head.spawned?, reduceCtorEq, false_iff]
    rintro ⟨pending, pc, h⟩
    rw [hs] at h
    cases h
  | callDone hs he hr rest =>
    simp only [Node.head, Head.spawned?, Option.some.injEq]
    refine ⟨fun h => h ▸ ⟨_, _, hs⟩, fun ⟨_, _, h⟩ => ?_⟩
    rw [hs] at h
    cases h; rfl
  | callRan hs he child hr rest =>
    simp only [Node.head, Head.spawned?, Option.some.injEq]
    refine ⟨fun h => h ▸ ⟨_, _, hs⟩, fun ⟨_, _, h⟩ => ?_⟩
    rw [hs] at h
    cases h; rfl
  | callDoneEnd hs he hr =>
    simp only [Node.head, Head.spawned?, Option.some.injEq]
    refine ⟨fun h => h ▸ ⟨_, _, hs⟩, fun ⟨_, _, h⟩ => ?_⟩
    rw [hs] at h
    cases h; rfl
  | callRanEnd hs he child hr =>
    simp only [Node.head, Head.spawned?, Option.some.injEq]
    refine ⟨fun h => h ▸ ⟨_, _, hs⟩, fun ⟨_, _, h⟩ => ?_⟩
    rw [hs] at h
    cases h; rfl

/-- A visit is a call step spawning `f` exactly when its first step spawns `f`. -/
theorem Visit.spawned?_eq_some_iff (v : Visit) {f : Frame} :
    v.spawned? = some f ↔ ∃ pending pc, step v.node.start = .ok (.spawn f pending pc) :=
  Node.spawned?_eq_some_iff v.node

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

/-- A visit whose first step spawns a child is the site of a call of the run with that child,
with no matching on the run's constructors. -/
theorem calls_of_visit_spawn {r out} {t : Frame.Run r (.exit out)} {v : Visit} {f : Frame}
    {pending : Pending} {pc : Nat} (hv : v ∈ visits t) (hs : step v.node.start = .ok (.spawn f pending pc)) :
    ∃ c ∈ calls t, c.site = v ∧ c.child = f := by
  have hsp : v.spawned? = some f := (Visit.spawned?_eq_some_iff v).mpr ⟨pending, pc, hs⟩
  have hm : (v, f) ∈ (visits t).filterMap (fun v => v.spawned?.map (v, ·)) :=
    List.mem_filterMap.mpr ⟨v, hv, by rw [hsp]; rfl⟩
  rw [← calls_complete] at hm
  obtain ⟨c, hc, hx⟩ := List.mem_map.mp hm
  exact ⟨c, hc, (Prod.mk.inj hx).1, (Prod.mk.inj hx).2⟩

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

/-! ### Call indices -/

private theorem callsFrom_path {r out} (t : Frame.Run r (.exit out)) (path kept frameStart enclosing counter) :
    ∀ c ∈ callsFrom t path kept frameStart enclosing counter,
      c.site.path = path ∨ ∃ k, counter ≤ k ∧ path ++ [k] <+: c.site.path := by
  have child : ∀ (l : List Call) (k : Nat),
      (∀ c ∈ l, c.site.path = path ++ [k] ∨ ∃ j, 0 ≤ j ∧ path ++ [k] ++ [j] <+: c.site.path) →
      ∀ c ∈ l, path ++ [k] <+: c.site.path := by
    intro l k h c hc
    rcases h c hc with h | ⟨j, _, hj⟩
    · rw [h]
    · exact (List.prefix_append _ _).trans hj
  have later : ∀ (l : List Call),
      (∀ c ∈ l, c.site.path = path ∨ ∃ k, counter + 1 ≤ k ∧ path ++ [k] <+: c.site.path) →
      ∀ c ∈ l, c.site.path = path ∨ ∃ k, counter ≤ k ∧ path ++ [k] <+: c.site.path := by
    intro l h c hc
    rcases h c hc with h | ⟨k, hk, hp⟩
    · exact .inl h
    · exact .inr ⟨k, by omega, hp⟩
  cases t with
  | halt => simp [callsFrom]
  | next hs rest =>
    rw [callsFrom]
    exact callsFrom_path rest _ _ _ _ _
  | callDone hs he hr rest =>
    rw [callsFrom]
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact .inl rfl
    · exact later _ (callsFrom_path rest _ _ _ _ _) c hc
  | callRan hs he ch hr rest =>
    rw [callsFrom]
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact .inl rfl
    · rcases List.mem_append.mp hc with hc | hc
      · exact .inr ⟨counter, Nat.le_refl _, child _ _ (callsFrom_path ch _ _ _ _ _) c hc⟩
      · exact later _ (callsFrom_path rest _ _ _ _ _) c hc
  | callDoneEnd hs he hr =>
    rw [callsFrom]
    intro c hc
    rcases List.mem_singleton.mp hc with rfl
    exact .inl rfl
  | callRanEnd hs he ch hr =>
    rw [callsFrom]
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_singleton.mp hc with rfl
      exact .inl rfl
    · exact .inr ⟨counter, Nat.le_refl _, child _ _ (callsFrom_path ch _ _ _ _ _) c hc⟩
termination_by sizeOf t

private theorem ne_of_child_prefix {path p : List Nat} {k : Nat} (h : path ++ [k] <+: p) : p ≠ path := by
  intro hp
  have := h.length_le
  simp [hp] at this

private theorem prefix_counter_eq {path p : List Nat} {j k : Nat} (hj : path ++ [j] <+: p)
    (hk : path ++ [k] <+: p) : j = k := by
  have hle : (path ++ [j]).length ≤ (path ++ [k]).length := by simp
  have h := (List.prefix_of_prefix_length_le hj hk hle).eq_of_length (by simp)
  simpa using h

private theorem callsFrom_index {r out} (t : Frame.Run r (.exit out)) (path kept frameStart enclosing counter)
    (p : List Nat) :
    ((callsFrom t path kept frameStart enclosing counter).filter (fun c => c.site.path = p)).map
        Call.index =
      List.range' (if p = path then counter else 0)
        ((callsFrom t path kept frameStart enclosing counter).filter (fun c => c.site.path = p)).length := by
  -- The calls of a child frame never sit at the caller's path.
  have childNil : ∀ (l : List Call) (k : Nat), (∀ c ∈ l, c.site.path = path ++ [k] ∨
      ∃ j, 0 ≤ j ∧ path ++ [k] ++ [j] <+: c.site.path) → l.filter (fun c => c.site.path = path) = [] := by
    intro l k h
    refine List.filter_eq_nil_iff.mpr fun c hc => ?_
    have hp : path ++ [k] <+: c.site.path := by
      rcases h c hc with h | ⟨j, _, hj⟩
      · rw [h]
      · exact (List.prefix_append _ _).trans hj
    simpa using ne_of_child_prefix hp
  -- Below the caller's path, a child's calls and the later calls never share a path.
  have disjoint : ∀ (l m : List Call) (k : Nat), p ≠ path →
      (∀ c ∈ l, c.site.path = path ++ [k] ∨ ∃ j, 0 ≤ j ∧ path ++ [k] ++ [j] <+: c.site.path) →
      (∀ c ∈ m, c.site.path = path ∨ ∃ j, k + 1 ≤ j ∧ path ++ [j] <+: c.site.path) →
      l.filter (fun c => c.site.path = p) = [] ∨ m.filter (fun c => c.site.path = p) = [] := by
    intro l m k hne hl hm
    by_cases hl0 : l.filter (fun c => c.site.path = p) = []
    · exact .inl hl0
    right
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hl0
    rw [List.mem_filter, decide_eq_true_eq] at hc
    obtain ⟨hc, hcp⟩ := hc
    have h1 : path ++ [k] <+: p := by
      rcases hl c hc with h | ⟨j, _, hj⟩
      · rw [← hcp, h]
      · rw [← hcp]; exact (List.prefix_append _ _).trans hj
    refine List.filter_eq_nil_iff.mpr fun d hd hdp => ?_
    rw [decide_eq_true_eq] at hdp
    rcases hm d hd with h | ⟨j, hj, hjp⟩
    · exact hne (hdp ▸ h)
    · have := prefix_counter_eq h1 (hdp ▸ hjp)
      omega
  have range_append : ∀ l1 l2 : Nat, l1 = 0 ∨ l2 = 0 →
      List.range' 0 l1 ++ List.range' 0 l2 = List.range' 0 (l1 + l2) := by
    intro l1 l2 h
    rcases h with rfl | rfl <;> simp
  cases t with
  | halt => simp [callsFrom]
  | next hs rest =>
    rw [callsFrom]
    exact callsFrom_index rest _ _ _ _ _ p
  | callDone hs he hr rest =>
    rw [callsFrom]
    have ih := callsFrom_index rest path kept false enclosing (counter + 1) p
    by_cases hp : p = path
    · subst hp
      simp only [List.filter_cons, decide_true, ite_true, List.map_cons, List.length_cons] at ih ⊢
      rw [ih]
      simp [List.range'_succ]
    · have hne : ¬ path = p := fun h => hp h.symm
      simp only [List.filter_cons, hne, decide_false, Bool.false_eq_true, ite_false] at ih ⊢
      simpa [hp] using ih
  | @callRan _ f _ _ _ raw _ _ hs he ch hr rest =>
    rw [callsFrom]
    have ihc := callsFrom_index ch (path ++ [counter]) (kept && Frame.settlementCommits f raw) true
      (r.context :: enclosing) 0 p
    have ihr := callsFrom_index rest path kept false enclosing (counter + 1) p
    have pc := callsFrom_path ch (path ++ [counter]) (kept && Frame.settlementCommits f raw) true
      (r.context :: enclosing) 0
    have pr := callsFrom_path rest path kept false enclosing (counter + 1)
    by_cases hp : p = path
    · subst hp
      simp only [List.filter_cons, List.filter_append, decide_true, ite_true, childNil _ _ pc,
        List.nil_append, List.map_cons, List.length_cons] at ihr ⊢
      rw [ihr]
      simp [List.range'_succ]
    · have hne : ¬ path = p := fun h => hp h.symm
      simp only [List.filter_cons, hne, decide_false, Bool.false_eq_true, ite_false, List.filter_append,
        List.map_append, List.length_append]
      simp only [hp, ite_false, ite_self] at ihc ihr ⊢
      rw [ihc, ihr]
      exact range_append _ _ ((disjoint _ _ counter hp pc pr).imp (fun h => by rw [h]; rfl)
        (fun h => by rw [h]; rfl))
  | callDoneEnd hs he hr =>
    rw [callsFrom]
    by_cases hp : p = path
    · subst hp; simp
    · have hne : ¬ path = p := fun h => hp h.symm
      simp [hne]
  | callRanEnd hs he ch hr =>
    rw [callsFrom]
    have ihc := callsFrom_index ch (path ++ [counter]) false true (r.context :: enclosing) 0 p
    have pc := callsFrom_path ch (path ++ [counter]) false true (r.context :: enclosing) 0
    by_cases hp : p = path
    · subst hp
      simp only [List.singleton_append, List.filter_cons, decide_true, ite_true, List.map_cons,
        List.length_cons]
      rw [childNil _ _ pc]
      simp
    · have hne : ¬ path = p := fun h => hp h.symm
      simp only [List.singleton_append, List.filter_cons, hne, decide_false, Bool.false_eq_true,
        ite_false]
      simpa [hp] using ihc
termination_by sizeOf t

/-- Every call's index, entry-finished calls included, is the caller's child counter at the call
step: the calls a run makes at one path, in execution order, have the indices `0, 1, 2, …`. So a
call's index is the number of calls its caller frame made before it. -/
theorem calls_index {r out} (t : Frame.Run r (.exit out)) (p : List Nat) :
    ((calls t).filter (fun c => c.site.path = p)).map Call.index =
      List.range ((calls t).filter (fun c => c.site.path = p)).length := by
  have h := callsFrom_index t [] true true [] 0 p
  simp only [ite_self] at h
  rw [calls, h, List.range_eq_range']

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
