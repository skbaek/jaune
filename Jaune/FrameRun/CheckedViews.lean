import Jaune.FrameRun.CheckedBasic

namespace Jaune.Checked.Frame.Run

structure Visit where
  node : Node
  path : List Nat
  kept : Bool
  frameStart : Bool
  enclosing : List Jaune.CallContext

inductive Event where
  | visit (v : Visit)
  | exit (caller : Visit)

/-- Pre-order visits and matching return boundaries. The child counter includes children
that finished at entry. The caller's continuation stays inside the same frame. -/
def eventsFrom {r out} (t : Frame.Run r (.exit out)) (path : List Nat)
    (kept frameStart : Bool) (enclosing : List Jaune.CallContext) (counter : Nat) : List Event :=
  let here : Visit := ⟨⟨r, out, t⟩, path, kept, frameStart, enclosing⟩
  match t with
  | .halt _ | .callDoneEnd .. => [.visit here]
  | .next _ rest => .visit here :: eventsFrom rest path kept false enclosing counter
  | .callDone _ _ _ rest => .visit here :: eventsFrom rest path kept false enclosing (counter + 1)
  | .callRan (child := f) (raw := raw) _ _ child _ rest =>
    .visit here :: (eventsFrom child (path ++ [counter]) (kept && Frame.settlementCommits f raw)
      true (r.context :: enclosing) 0 ++ .exit here :: eventsFrom rest path kept false enclosing (counter + 1))
  | .callRanEnd _ _ child _ =>
    .visit here :: (eventsFrom child (path ++ [counter]) false true (r.context :: enclosing) 0 ++ [.exit here])
termination_by sizeOf t

def events {r out} (t : Frame.Run r (.exit out)) : List Event := eventsFrom t [] true true [] 0

def Event.visit? : Event → Option Visit
  | .visit v => some v
  | .exit _ => none

def visits {r out} (t : Frame.Run r (.exit out)) : List Visit := (events t).filterMap Event.visit?

def rawNodes {r out} (t : Frame.Run r (.exit out)) : List Node := (visits t).map Visit.node

def spine {r out} (t : Frame.Run r (.exit out)) : List Node :=
  let here : Node := ⟨r, out, t⟩
  match t with
  | .halt _ | .callDoneEnd .. | .callRanEnd .. => [here]
  | .next _ rest | .callDone _ _ _ rest | .callRan _ _ _ _ rest => here :: spine rest
termination_by sizeOf t

/-- A failed root has no retained nodes, even if a child settled successfully before its rollback. -/
def retainedNodes {r out} (t : Frame.Run r (.exit out)) : List Node :=
  if Exec.finished out then ((visits t).filter Visit.kept).map Visit.node else []

def Visit.toKept? (v : Visit) : Option Kept :=
  if h : v.kept = true ∧ v.frameStart = true ∧ Exec.finished v.node.exit = true then
    some ⟨v.node, h.2.2⟩ else none

/-- Descendant survival is relative to the root; it is observable even when the root reverts. -/
def descendantFrames {r out} (t : Frame.Run r (.exit out)) : List Kept :=
  (visits t).filterMap fun v => if v.path.isEmpty then none else v.toKept?

def committedFrames {r out} (t : Frame.Run r (.exit out)) : List Kept :=
  if h : Exec.finished out then ⟨⟨r, out, t⟩, h⟩ :: descendantFrames t else []

def frames {r out} (t : Frame.Run r (.exit out)) : List Node :=
  ((visits t).filter Visit.frameStart).map Visit.node

def Visit.inside (p : Jaune.CallContext → Bool) (v : Visit) : Bool :=
  p v.node.start.context || v.enclosing.any p

theorem Visit.inside_iff (p : Jaune.CallContext → Bool) (v : Visit) :
    v.inside p = true ↔ p v.node.start.context = true ∨ ∃ c ∈ v.enclosing, p c = true := by
  simp [inside]

def Visit.selected (p : Jaune.CallContext → Bool) (withRoot : Bool) (v : Visit) : Bool :=
  v.frameStart && (withRoot || !v.path.isEmpty) && p v.node.start.context &&
    (if withRoot then v.enclosing else v.enclosing.dropLast).all (fun c => !p c)

theorem Visit.inside_of_selected {p withRoot v} (h : Visit.selected p withRoot v = true) :
    Visit.inside p v = true := by
  simp only [selected, Bool.and_eq_true] at h
  simp [inside, h.1.2]

def outermostBelow {r out} (p : Jaune.CallContext → Bool) (t : Frame.Run r (.exit out)) : List Kept :=
  (visits t).filterMap fun v => if v.selected p false then v.toKept? else none

def keptAt {r out} (a : Address) (t : Frame.Run r (.exit out)) : List Kept :=
  outermostBelow (fun c => c.recipient == a) t

def descendantFramePaths {r out} (t : Frame.Run r (.exit out)) : List Located :=
  (visits t).filterMap fun v => if v.path.isEmpty then none else (v.toKept?).map (⟨v.path, ·⟩)

end Jaune.Checked.Frame.Run
