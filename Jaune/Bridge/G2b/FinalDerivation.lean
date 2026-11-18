import Jaune.MessageCall.FinalChronology
import Jaune.Bridge.G2b.FinalDriver
import Jaune.ExecChronology

namespace Jaune

private def observeResume :
    Execution → Except (Except Fault Frame.Exit) Frame.State
  | .error e => .error (Frame.Exit.ofExecution (.error e))
  | .ok d => .ok (.ofDevm d)

private theorem observe_resumeCaller (rules : ForkRules) (child : Frame) (p : Pending)
    (result : Except Fault Frame.Result) (flag : child.checkpoint.trail.touchedRIPEMD160 = false) :
    Staging.resumeCaller rules child (.ofLegacy p) result =
      observeResume (resumeCaller rules child p result) := by
  cases result with
  | error fault =>
    change Except.error (.error fault) = Except.error (Frame.Exit.ofExecution _)
    rw [ofExecution_fault]
  | ok result =>
    unfold Staging.resumeCaller resumeCaller
    dsimp only
    rw [← resume_ofDevm rules p child.checkpoint result flag]
    rcases resume rules p child.checkpoint result with fault | ⟨reason, state⟩ | state
    · change Except.error (.error fault) = Except.error (Frame.Exit.ofExecution _)
      rw [ofExecution_fault]
    · rfl
    · rfl

theorem resumeCaller_output_eq_nil {rules : ForkRules} {child : Frame} {p : Pending}
    {result : Except Fault Frame.Result} {state : Devm} (clean : p.legacyOutput = [])
    (h : resumeCaller rules child p result = .ok state) : state.output = [] := by
  cases result with
  | error fault => cases h
  | ok result =>
    unfold resumeCaller at h
    dsimp only at h
    rw [resume_eq] at h
    revert h
    cases Staging.resume rules (.ofLegacy p) child.checkpoint result with
    | error fault => intro h; cases h
    | ok resumed =>
      rcases resumed with ⟨reason, state'⟩ | state'
      · intro h; cases h
      · intro h; cases h; exact clean

private theorem observeSpawn {e : Evm} {child p pc} (ho : e.dyna.output = [])
    (hs : Evm.step e = .spawn child p pc) :
    Staging.step (.ofEvm e) = .ok (.spawn child (.ofLegacy p) pc) ∧
    p.legacyOutput = [] ∧ child.checkpoint.trail.touchedRIPEMD160 = false := by
  constructor
  · rw [Staging.step_ofEvm e ho, hs]
    rfl
  · have h := OutputWalk.Evm.step_post e ho
    rwa [hs] at h

private theorem observeDone {f : Frame} {out} (h : enter f = .done out) :
    Staging.enter f = .done out := by
  rw [← Frame.Entry.observe_enter, h]
  rfl

private theorem observeRun {f : Frame} {e : Evm} (h : enter f = .run e) :
    Staging.enter f = .run (.ofEvm e) := by
  rw [← Frame.Entry.observe_enter, h]
  rfl

/-- Relabel the indices of every node while preserving both subderivations of a running child. -/
noncomputable def Exec.observe {pc sevm devm out} (run : Exec pc sevm devm out)
    (clean : devm.output = []) :
    Staging.Exec (.ofEvm ⟨pc, sevm, devm⟩) (Frame.Exit.ofExecution out) := by
  induction run with
  | halt hs => exact .halt (by rw [Staging.step_ofEvm _ clean, hs]; rfl)
  | @cont pc sevm devm pcNext devmNext out hs next ih =>
    have hc := OutputWalk.Evm.step_post (⟨pc, sevm, devm⟩ : Evm) clean
    rw [hs] at hc
    exact .cont (by rw [Staging.step_ofEvm _ clean, hs]; rfl) (ih hc)
  | doneErr hs he hr =>
    obtain ⟨step, _, flag⟩ := observeSpawn clean hs
    exact .doneErr step (observeDone he) (by rw [observe_resumeCaller _ _ _ _ flag]; exact congrArg observeResume hr)
  | doneOk hs he hr next ih =>
    obtain ⟨step, po, flag⟩ := observeSpawn clean hs
    exact .doneOk step (observeDone he) (by rw [observe_resumeCaller _ _ _ _ flag]; exact congrArg observeResume hr)
      (ih (resumeCaller_output_eq_nil po hr))
  | runErr hs he child hr ih =>
    obtain ⟨step, _, flag⟩ := observeSpawn clean hs
    exact .runErr step (observeRun he) (ih (enter_run_output he))
      (by rw [← settle_eq, observe_resumeCaller _ _ _ _ flag]; exact congrArg observeResume hr)
  | runOk hs he child hr next ihChild ihNext =>
    obtain ⟨step, po, flag⟩ := observeSpawn clean hs
    exact .runOk step (observeRun he) (ihChild (enter_run_output he))
      (by rw [← settle_eq, observe_resumeCaller _ _ _ _ flag]; exact congrArg observeResume hr)
      (ihNext (resumeCaller_output_eq_nil po hr))

end Jaune
