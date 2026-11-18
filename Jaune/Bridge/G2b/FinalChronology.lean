import Jaune.Bridge.G2b.FinalDerivation

namespace Jaune

def Exec.Deriv.frameObservation (node : Exec.Deriv) : Frame.Running × Except Fault Frame.Exit :=
  (.ofEvm ⟨node.pc, node.sevm, node.devm⟩, Frame.Exit.ofExecution node.exn)

def Staging.Exec.Deriv.observation (node : Staging.Exec.Deriv) : Frame.Running × Except Fault Frame.Exit :=
  (node.running, node.outcome)

/-- Conversion preserves every node observation in driver order, including failed children. -/
theorem Exec.observe_rawNodes {pc sevm devm out} (run : Exec pc sevm devm out)
    (clean : devm.output = []) :
    ((run.observe clean).rawNodes.map Staging.Exec.Deriv.observation) = run.rawNodes.map Exec.Deriv.frameObservation := by
  induction run with
  | halt hs => rfl
  | @cont pc sevm devm pc' devm' out hs next ih =>
    have cleanNext := OutputWalk.Evm.step_post (⟨pc, sevm, devm⟩ : Evm) clean
    rw [hs] at cleanNext
    exact congrArg (List.cons _) (ih cleanNext)
  | doneErr hs he hr => rfl
  | @doneOk pc sevm devm child p pc' res devm' out hs he hr next ih =>
    have saved := OutputWalk.Evm.step_post (⟨pc, sevm, devm⟩ : Evm) clean
    rw [hs] at saved
    exact congrArg (List.cons _) (ih (resumeCaller_output_eq_nil saved.1 hr))
  | runErr hs he child hr ih => exact congrArg (List.cons _) (ih (enter_run_output he))
  | @runOk pc sevm devm frame p pc' cr raw resumed out hs he child hr next ihChild ihNext =>
    have saved := OutputWalk.Evm.step_post (⟨pc, sevm, devm⟩ : Evm) clean
    rw [hs] at saved
    simp only [Exec.observe, Exec.rawNodes, Staging.Exec.rawNodes, List.map_cons, List.map_append]
    exact congrArg (List.cons _) (congrArg₂ List.append (ihChild (enter_run_output he))
      (ihNext (resumeCaller_output_eq_nil saved.1 hr)))

theorem Frame.settlementCommits_observe (f : Frame) (raw : Execution) :
    Staging.Frame.settlementCommits f (Frame.Exit.ofExecution raw) = Frame.settlementCommits f raw := by
  unfold Staging.Frame.settlementCommits Frame.settlementCommits
  rw [← settle_eq]
  cases settle f raw with
  | error e => rfl
  | ok result => cases result <;> rfl

theorem Exec.finished_observe (out : Execution) :
    Staging.Exec.finished (Frame.Exit.ofExecution out) = out.isOk := by
  rcases out with ⟨reason, state⟩ | state
  · cases reason <;> rfl
  · rfl

end Jaune
