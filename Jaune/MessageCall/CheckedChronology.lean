import Jaune.MessageCall.CheckedDerivation

/-! Execution order, same-frame continuations and the frames whose settlement commits. -/

namespace Jaune.Checked

/-- One reached driver node, carrying its full derivation. -/
structure Exec.Deriv where
  running : Frame.Running
  outcome : Except Fault Frame.Exit
  run : Exec running outcome

/-- Every driver node, including nodes inside rolled-back children. -/
def Exec.rawNodes {r out} (run : Exec r out) : List Exec.Deriv :=
  let root : Exec.Deriv := ⟨r, out, run⟩
  match run with
  | .halt _ | .doneErr .. => [root]
  | .cont _ next | .doneOk _ _ _ next => root :: next.rawNodes
  | .runErr _ _ child _ => root :: child.rawNodes
  | .runOk _ _ child _ next => root :: (child.rawNodes ++ next.rawNodes)
termination_by structural run

/-- Same-frame continuation, in driver order. Entering a child has no effect on this list. -/
def Exec.parentNodes {r out} (run : Exec r out) : List Exec.Deriv :=
  let root : Exec.Deriv := ⟨r, out, run⟩
  match run with
  | .halt _ | .doneErr .. | .runErr .. => [root]
  | .cont _ next | .doneOk _ _ _ next | .runOk _ _ _ _ next => root :: next.parentNodes
termination_by structural run

/-- The immediate continuation within the same frame. -/
def Exec.Deriv.parentNext (d : Exec.Deriv) : Option Exec.Deriv :=
  match d.run with
  | .cont _ next | .doneOk _ _ _ next | .runOk _ _ _ _ next => some ⟨_, _, next⟩
  | _ => none

/-- A same-frame prefix ends after zero or more continuation edges. -/
def Exec.Deriv.ParentStep (next root : Exec.Deriv) : Prop := root.parentNext = some next

abbrev Exec.Deriv.ParentPrefix (root tail : Exec.Deriv) : Prop :=
  Relation.ReflTransGen (fun current next => Exec.Deriv.ParentStep next current) root tail

theorem Exec.Deriv.ParentStep.unique {root left right : Exec.Deriv}
    (hl : Exec.Deriv.ParentStep left root) (hr : Exec.Deriv.ParentStep right root) :
    left = right := Option.some.inj (hl.symm.trans hr)

/-- A retained frame's indexed outcome exposes its output and post-state directly. -/
structure Exec.Frame where
  running : Frame.Running
  output : Bytes
  post : Frame.State
  run : Exec running (.ok (.finished output post))

def Exec.Frame.ofRun {r out} (run : Exec r out) (h : Exec.finished out = true) : Exec.Frame :=
  match out, run, h with
  | .ok (.finished output state), run, _ => ⟨r, output, state, run⟩

/-- Descendants that survive their own settlement and every intervening ancestor's. -/
def Exec.descendantFrames {r out} (run : Exec r out) : List Exec.Frame :=
  match run with
  | .halt _ | .doneErr .. | .runErr .. => []
  | .cont _ next | .doneOk _ _ _ next => next.descendantFrames
  | .runOk (child := frame) (raw := raw) _ _ child _ next =>
    (if h : Frame.settlementCommits frame raw then
       Exec.Frame.ofRun child (Frame.finished_of_settlementCommits h) :: child.descendantFrames
     else []) ++ next.descendantFrames
termination_by structural run

def Exec.committedFrames {r out} (run : Exec r out) : List Exec.Frame :=
  if h : Exec.finished out then Exec.Frame.ofRun run h :: run.descendantFrames else []

/-- Driver chronology restricted to work whose effects survive settlement. -/
def Exec.retainedNodes {r out} (run : Exec r out) : List Exec.Deriv :=
  if Exec.finished out then
    let root : Exec.Deriv := ⟨r, out, run⟩
    match run with
    | .halt _ | .doneErr .. | .runErr .. => [root]
    | .cont _ next | .doneOk _ _ _ next => root :: next.retainedNodes
    | .runOk (child := frame) (raw := raw) _ _ child _ next =>
      root :: ((if Frame.settlementCommits frame raw then child.retainedNodes else []) ++ next.retainedNodes)
  else []
termination_by structural run

theorem Exec.committedFrames_eq_nil_of_failed {r out} (run : Exec r out)
    (h : Exec.finished out = false) : run.committedFrames = [] := by
  simp [Exec.committedFrames, h]

theorem Exec.retainedNodes_eq_nil_of_failed {r out} (run : Exec r out)
    (h : Exec.finished out = false) : run.retainedNodes = [] := by
  cases run <;> simp [Exec.retainedNodes, h]

end Jaune.Checked
