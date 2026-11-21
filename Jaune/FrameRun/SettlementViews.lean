import Jaune.FrameRun.Views

namespace Jaune.Frame.Run

/-- A single projection describes retained driver nodes or surviving frame starts. -/
private structure Projection (α : Type) where
  everyNode : Bool
  emit : Node → Option α

private def Projection.event (p : Projection α) : Event → Option α
  | .exit _ => none
  | .visit v =>
    if v.kept && (p.everyNode || (v.frameStart && !v.path.isEmpty)) then p.emit v.node else none

private def Projection.tail (p : Projection α) {r out} (t : Frame.Run r (.exit out)) : List α :=
  match t with
  | .halt _ | .callDoneEnd .. | .callRanEnd .. => []
  | .next _ n | .callDone _ _ _ n =>
    (if p.everyNode then (p.emit ⟨_, _, n⟩).toList else []) ++ p.tail n
  | .callRan (child := f) (raw := raw) _ _ c _ n =>
    (if Frame.settlementCommits f raw then (p.emit ⟨_, _, c⟩).toList ++ p.tail c else []) ++
      ((if p.everyNode then (p.emit ⟨_, _, n⟩).toList else []) ++ p.tail n)
termination_by sizeOf t

private theorem Projection.project (p : Projection α) {r out} (t : Frame.Run r (.exit out))
    (path k first enc counter) :
    (eventsFrom t path k first enc counter).filterMap p.event =
      (p.event (.visit ⟨⟨r, out, t⟩, path, k, first, enc⟩)).toList ++ (if k then p.tail t else []) := by
  cases t with
  | halt | callDoneEnd =>
    simp [eventsFrom, Projection.tail, List.filterMap_cons, Option.toList]
    cases p.event (.visit ⟨⟨r, out, _⟩, path, k, first, enc⟩) <;> rfl
  | next hs n | callDone _ _ hs n =>
    rw [eventsFrom, List.filterMap_cons, p.project n]
    cases k <;> cases hp : p.everyNode <;>
      simp [Projection.event, Projection.tail, hp, Option.toList] <;> split <;> simp_all
  | callRanEnd hs he c hr =>
    rw [eventsFrom, List.filterMap_cons, List.filterMap_append, p.project c]
    cases k <;> simp [Projection.event, Projection.tail, List.filterMap_cons, Option.toList];
      split <;> simp_all
  | @callRan r f pending pc cr raw state _ hs he c hr n =>
    rw [eventsFrom, List.filterMap_cons, List.filterMap_append, p.project c]
    simp only [List.filterMap_cons, Projection.event]
    rw [p.project n]
    cases k <;> cases hp : p.everyNode <;> cases hidden : Frame.settlementCommits f raw <;>
      simp [Projection.event, Projection.tail, hp, hidden, Option.toList] <;> split <;> simp_all
termination_by sizeOf t

private def nodes : Projection Node := ⟨true, some⟩

private def asKept (n : Node) : Option Kept := if h : Frame.rawFinished n.exit then some ⟨n, h⟩ else none

private def descendants : Projection Kept := ⟨false, asKept⟩

private theorem filterNodes (es : List Event) :
    ((es.filterMap Event.visit?).filter Visit.kept).map Visit.node = es.filterMap nodes.event := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e with
    | exit v => simp [Event.visit?, Projection.event, List.filterMap_cons, ih]
    | visit v => cases h : v.kept <;> simp [Event.visit?, Projection.event, nodes, h, ih]

private theorem filterFrames (es : List Event) :
    (es.filterMap Event.visit?).filterMap (fun v => if v.path.isEmpty then none else v.toKept?) =
      es.filterMap descendants.event := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e with
    | exit v => simp only [Event.visit?, Projection.event, List.filterMap_cons, ih]
    | visit v =>
      cases hp : v.path <;> cases hk : v.kept <;> cases hf : v.frameStart <;>
        simp [Event.visit?, Projection.event, descendants, Visit.toKept?, asKept, hp, hk, hf,
          List.filterMap_cons] at ih ⊢ <;>
        first
        | exact ih
        | (by_cases hex : Frame.rawFinished v.node.exit = true <;> simp [hex, ih])

private theorem retained_eq {r out} (t : Frame.Run r (.exit out)) (h : Frame.rawFinished out = true) :
    retainedNodes t = ⟨r, out, t⟩ :: nodes.tail t := by
  simp [retainedNodes, h, visits, filterNodes, events, Projection.project, Projection.event, nodes]

private theorem descendants_eq {r out} (t : Frame.Run r (.exit out)) :
    descendantFrames t = descendants.tail t := by
  rw [descendantFrames, visits, filterFrames, events, Projection.project]
  simp [Projection.event, descendants, Option.toList]

variable {r : Frame.Running} {f : Frame} {p : Pending} {pc : Nat}
  {cr : Frame.Running} {raw out : Except Fault Frame.Exit} {s : Frame.State}
  (hs : step r = .ok (.spawn f p pc)) (he : enter f = .run cr) (child : Frame.Run cr (.exit raw))
  (hr : resumeCaller r.context.block.rules f p (raw >>= settle f) = .ok s)
  (next : Frame.Run ⟨pc, r.context, s⟩ (.exit out))

theorem descendantFrames_callRan_of_settles (h : Frame.settlementCommits f raw = true) :
    descendantFrames (.callRan hs he child hr next) =
      (⟨⟨cr, raw, child⟩, Frame.finished_of_settlementCommits h⟩ :: descendantFrames child) ++ descendantFrames next := by
  simp [descendants_eq, Projection.tail, descendants, asKept, h, Frame.finished_of_settlementCommits h]

theorem descendantFrames_callRan_of_not_settles (h : Frame.settlementCommits f raw ≠ true) :
    descendantFrames (.callRan hs he child hr next) = descendantFrames next := by
  simp [descendants_eq, Projection.tail, descendants, h]

theorem descendantFrames_callRan_create_codeDepositRollback {res : Frame.Result}
    (_ : Frame.rawFinished raw = true) (_ : f.message.kind = .create)
    (h : (raw >>= settle f) = .ok res) (failed : res.failed = true) :
    descendantFrames (.callRan hs he child hr next) = descendantFrames next := by
  apply descendantFrames_callRan_of_not_settles
  intro keep
  obtain ⟨_, _, _, _, _, _, ok⟩ := Frame.settlementCommits_iff.mp keep
  rw [h] at ok
  cases ok
  cases failed

theorem committedFrames_eq_nil_of_not_commits {r out} (t : Frame.Run r (.exit out)) (h : Frame.rawFinished out ≠ true) :
    committedFrames t = [] := by simp [committedFrames, h]

theorem retainedNodes_callRan_of_settles (root : Frame.rawFinished out = true) (h : Frame.settlementCommits f raw = true) :
    retainedNodes (.callRan hs he child hr next) = ⟨_, _, .callRan hs he child hr next⟩ ::
      (retainedNodes child ++ retainedNodes next) := by
  simp [retained_eq, root, Frame.finished_of_settlementCommits h, Projection.tail, nodes, h]

theorem retainedNodes_callRan_of_not_settles (root : Frame.rawFinished out = true) (h : Frame.settlementCommits f raw ≠ true) :
    retainedNodes (.callRan hs he child hr next) = ⟨_, _, .callRan hs he child hr next⟩ :: retainedNodes next := by
  simp [retained_eq, root, Projection.tail, nodes, h]

end Jaune.Frame.Run
