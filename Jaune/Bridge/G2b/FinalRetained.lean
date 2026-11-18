import Jaune.Bridge.G2b.FinalChronology

namespace Jaune

private theorem keptNodes {pc sevm devm out} (run : Exec pc sevm devm out)
    (clean : devm.output = []) (commits : out.isOk = true) :
    (run.observe clean).retainedNodes.map Staging.Exec.Deriv.observation =
      (run.retainedNodesOfCommits commits).map Exec.Deriv.frameObservation := by
  induction run with
  | halt hs =>
    simp only [Exec.observe, Staging.Exec.retainedNodes, Exec.finished_observe, commits, ite_true,
      Exec.retainedNodesOfCommits, List.map_cons, List.map_nil]
    rfl
  | cont hs next ih =>
    simp only [Exec.observe, Staging.Exec.retainedNodes, Exec.finished_observe, commits, ite_true,
      Exec.retainedNodesOfCommits, List.map_cons]
    exact congrArg (List.cons _) (ih (Evm.next_output_eq_nil hs clean) commits)
  | doneErr hs he hr => cases commits
  | doneOk hs he hr next ih =>
    simp only [Exec.observe, Staging.Exec.retainedNodes, Exec.finished_observe, commits, ite_true,
      Exec.retainedNodesOfCommits, List.map_cons]
    exact congrArg (List.cons _) (ih (resumeCaller_output_eq_nil (Evm.spawn_legacyOutput_eq_nil hs clean) hr) commits)
  | runErr hs he child hr ih => cases commits
  | @runOk pc sevm d frame p pc' cr raw state out hs he child hr next ihChild ihNext =>
    have resumed := ihNext (resumeCaller_output_eq_nil (Evm.spawn_legacyOutput_eq_nil hs clean) hr) commits
    by_cases keep : Frame.settlementCommits frame raw = true
    · have nested := ihChild (enter_run_output he) (Frame.raw_commits_of_settlementCommits keep)
      rw [Staging.Exec.retainedNodes, Exec.retainedNodesOfCommits]
      simp only [Exec.observe, Exec.finished_observe, commits, ite_true,
        Frame.settlementCommits_observe, keep, dite_true,
        List.map_cons, List.map_append]
      exact congrArg (List.cons _) (congrArg₂ List.append nested resumed)
    · rw [Staging.Exec.retainedNodes, Exec.retainedNodesOfCommits]
      simp only [Exec.observe, Exec.finished_observe, commits, ite_true,
        Frame.settlementCommits_observe, keep, List.map_cons]
      exact congrArg (List.cons _) resumed

/-- Every surviving node agrees, with failed settlement pruning an entire child subtree. -/
theorem Exec.observe_retainedNodes {pc sevm devm out} (run : Exec pc sevm devm out)
    (clean : devm.output = []) :
    (run.observe clean).retainedNodes.map Staging.Exec.Deriv.observation =
      run.retainedNodes.map Exec.Deriv.frameObservation := by
  cases ok : out.isOk with
  | true => simpa only [Exec.retainedNodes_eq_of_commits run ok] using keptNodes run clean ok
  | false =>
    rw [Staging.Exec.retainedNodes_eq_nil_of_failed _ ((Exec.finished_observe out).trans ok),
      Exec.retainedNodes_eq_nil_of_not_commits _ (by simp [ok])]
    rfl

/-- A retained legacy frame, including the actual output and post-state after conversion. -/
def Exec.Frame.frameObservation (frame : Exec.Frame) : Frame.Running × Bytes × Frame.State :=
  (.ofEvm ⟨frame.pc, frame.sevm, frame.pre⟩, frame.post.output, .ofDevm frame.post)

def Staging.Exec.Frame.observation (frame : Staging.Exec.Frame) : Frame.Running × Bytes × Frame.State :=
  (frame.running, frame.output, frame.post)

private theorem observeFrame_ofRun {pc sevm devm out} (run : Exec pc sevm devm out)
    (clean : devm.output = []) (ok : out.isOk = true) :
    (Staging.Exec.Frame.ofRun (run.observe clean) ((Exec.finished_observe out).trans ok)).observation =
      (Exec.Frame.ofRun run ok).frameObservation := by
  cases out with
  | error err => cases ok
  | ok state => rfl

private theorem observe_descendants {pc sevm devm out} (run : Exec pc sevm devm out)
    (clean : devm.output = []) :
    (run.observe clean).descendantFrames.map Staging.Exec.Frame.observation =
      run.descendantFrames.map Exec.Frame.frameObservation := by
  induction run with
  | halt hs => rfl
  | cont hs next ih => exact ih (Evm.next_output_eq_nil hs clean)
  | doneErr hs he hr => rfl
  | doneOk hs he hr next ih => exact ih (resumeCaller_output_eq_nil (Evm.spawn_legacyOutput_eq_nil hs clean) hr)
  | runErr hs he child hr ih => rfl
  | @runOk pc sevm d frame p pc' cr raw state out hs he child hr next ihChild ihNext =>
    have resumed := ihNext (resumeCaller_output_eq_nil (Evm.spawn_legacyOutput_eq_nil hs clean) hr)
    have entered := enter_run_output he
    simp only [Exec.observe, Staging.Exec.descendantFrames, Exec.descendantFrames]
    by_cases keep : Frame.settlementCommits frame raw = true
    · simp only [Frame.settlementCommits_observe, keep, dite_true, List.map_append,
        List.map_cons]
      exact congrArg₂ List.append
        (congrArg₂ List.cons (observeFrame_ofRun child entered (Frame.raw_commits_of_settlementCommits keep))
          (ihChild entered)) resumed
    · simp [Frame.settlementCommits_observe, keep]
      exact resumed

/-- Retention keeps precisely the same frames, output bytes and complete post-state. -/
theorem Exec.observe_committedFrames {pc sevm devm out} (run : Exec pc sevm devm out)
    (clean : devm.output = []) :
    (run.observe clean).committedFrames.map Staging.Exec.Frame.observation =
      run.committedFrames.map Exec.Frame.frameObservation := by
  unfold Staging.Exec.committedFrames Exec.committedFrames
  by_cases ok : out.isOk = true
  · have finished := (Exec.finished_observe out).trans ok
    simp only [finished, ok, dite_true, List.map_cons]
    exact congrArg₂ List.cons (observeFrame_ofRun run clean ok) (observe_descendants run clean)
  · simp [Exec.finished_observe, ok]

end Jaune
