import Jaune.MessageCall.FinalAdequacy
import Jaune.MessageCall.FinalChronology

namespace Jaune.Staging

/-- The one top-level frame whose code was entered, with its complete execution. -/
structure Root where
  frame : Jaune.Frame
  running : Frame.Running
  outcome : Except Fault Frame.Exit
  run : Exec running outcome

def Root.ofEntry (frame : Jaune.Frame) (running : Frame.Running) : Root :=
  ⟨frame, running, exec running, Exec.ofRun running⟩

/-- Observe the result after settling this frame. Code deposit can fail after initcode succeeds. -/
def Root.settled (root : Root) : Except Fault Frame.Result :=
  root.outcome >>= settle root.frame

/-- A top-level rollback removes all work beneath it. -/
def Root.frames (root : Root) : List Exec.Frame :=
  if Frame.settlementCommits root.frame root.outcome then root.run.committedFrames else []

theorem Root.frames_of_failed {root : Root} (h : Frame.settlementCommits root.frame root.outcome = false) :
    root.frames = [] := by simp [Root.frames, h]

theorem Root.frames_of_success {root : Root} (h : Frame.settlementCommits root.frame root.outcome = true) :
    root.frames = root.run.committedFrames := by simp [Root.frames, h]

end Jaune.Staging
