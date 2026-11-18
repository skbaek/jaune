import Jaune.MessageCall.FinalExec
import Jaune.MessageCall.Top
import Jaune.Bridge.G2b.FinalStep
import Jaune.Bridge.G2b.FinalParts
import Jaune.Bridge.G2b.FinalOutput
import Jaune.Implementation.FinalCachedDriver

/-!
# Bridge: the staged driver, `exec` and `Frame.runTop` against the `Devm` ones (G2b, unit W3-3)

Old side: `Jaune.execFueled`, `Jaune.exec` and `Jaune.Frame.runTop` (`Jaune/MessageCall/Driver.lean`,
`Exec.lean`, `Top.lean`) at `bba27e95`, unedited. New side: `Jaune.Staging.execFueled`,
`Staging.exec`, `Staging.Frame.runTop`.

* `execFueled_square`: for every fuel and every running machine with no output, the new driver's
  result is the old one's, observed through `Frame.Exit.ofExecution` (faults, exhaustion and every
  exit included). The premise is the only cleanliness premise the wave-2 squares use (W3-2b+d's
  halt and precompile squares); W3-2a's and W3-2c's squares have none. Every machine the old
  driver runs from such a machine satisfies it: a continuing step keeps the output
  (`OutputWalk.Evm.step_post`), an entered child starts with none (`enter_run_output`), and a
  resumed caller gets back the output its spawn passed through, which is the caller's.
* `exec_square`: the same for `exec`.
* `execFueledCached_square`: the cached twin of the staged driver
  (`Jaune.Implementation.FinalCachedDriver`) against the old driver, through the twin's equation.
  This import is also what puts the twin in the default build until the switch moves the
  compiled-code substitution to it.
* `Frame.runTop_square`: **the anchor**, for every frame, plain equality of the whole
  `Except Fault Frame.Result`. A top-level frame starts from `f.checkpoint.toDevm`, which has no
  output.

Everything here goes with `Devm` after G2b's tag.
-/

namespace Jaune

open Frame.State OutputWalk

/-- A frame entered to run from a start state with no output starts with no output. -/
theorem enterWith_run_output {f : Frame} {start : Devm} {cevm : Evm}
    (ho : start.output = []) (h : enterWith f start = .run cevm) : cevm.dyna.output = [] := by
  unfold enterWith at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h; exact ho
    · cases h; exact ho

/-- A child entered to run starts with no output. -/
theorem enter_run_output {f : Frame} {cevm : Evm} (h : enter f = .run cevm) :
    cevm.dyna.output = [] := by
  unfold enter enterWith at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h; rfl
    · cases h; rfl

/-- The old driver's fault payload, observed, is the fault. -/
theorem ofExecution_fault (fault : Fault) (d : Devm) :
    Frame.Exit.ofExecution (.error (fault.toEvmError, d)) = .error fault := by
  cases fault <;> rfl

/-- The square for the driver: from a running machine with no output, the staged driver's
result is the old driver's, observed through `Frame.Exit.ofExecution`, at every fuel. -/
theorem execFueled_square (fuel : Nat) :
    ∀ evm : Evm, evm.dyna.output = [] →
      (Staging.execFueled (Frame.Running.ofEvm evm) fuel).run =
        (Jaune.execFueled evm fuel).run.map Frame.Exit.ofExecution := by
  induction fuel with
  | zero => intro evm _; rfl
  | succ fuel ih =>
    intro evm ho
    have hp := Evm.step_post evm ho
    rw [Staging.execFueled, Jaune.execFueled, Staging.step_ofEvm evm ho]
    revert hp
    cases Evm.step evm with
    | halt ex =>
      intro _
      simp only [Step.observe]
      show _ = some (Frame.Exit.ofExecution ex)
      cases Frame.Exit.ofExecution ex <;> rfl
    | next pc d =>
      intro hd
      exact ih ⟨pc, evm.sta, d⟩ hd
    | spawn child p pc =>
      intro ⟨hpo, hflag⟩
      simp only [Step.observe]
      rw [← Frame.Entry.observe_enter child]
      have hr := fun result => resume_ofDevm evm.sta.benvStat.rules p child.checkpoint result hflag
      have hro := fun result => resume_eq evm.sta.benvStat.rules p child.checkpoint result
      cases he : enter child with
      | done res =>
        simp only [Frame.Entry.observe]
        rcases res with fault | result
        · exact congrArg some (ofExecution_fault fault _).symm
        · dsimp only
          rw [show (Frame.Running.ofEvm evm).context.block.rules = evm.sta.benvStat.rules from rfl,
            ← hr result]
          rcases hres : resume evm.sta.benvStat.rules p child.checkpoint result with
            fault | (⟨reason, d⟩ | d)
          · exact congrArg some (ofExecution_fault fault _).symm
          · rfl
          · have hd : d.output = [] := by
              rw [hro result] at hres
              revert hres
              cases Staging.resume evm.sta.benvStat.rules (.ofLegacy p) child.checkpoint result with
              | error e => intro h; cases h
              | ok x =>
                rcases x with ⟨r', s'⟩ | s'
                · intro h; cases h
                · intro h; cases h; exact hpo
            exact ih ⟨pc, evm.sta, d⟩ hd
      | run cevm =>
        simp only [Frame.Entry.observe]
        rw [ih cevm (enter_run_output he), Option.map_map]
        cases (Jaune.execFueled cevm fuel).run with
        | none => rfl
        | some raw =>
          simp only [Option.map, Function.comp]
          rw [← settle_eq]
          rcases settle child raw with fault | result
          · exact congrArg some (ofExecution_fault fault _).symm
          · dsimp only
            rw [show (Frame.Running.ofEvm evm).context.block.rules = evm.sta.benvStat.rules from rfl,
              ← hr result]
            rcases hres : resume evm.sta.benvStat.rules p child.checkpoint result with
              fault | (⟨reason, d⟩ | d)
            · exact congrArg some (ofExecution_fault fault _).symm
            · rfl
            · have hd : d.output = [] := by
                rw [hro result] at hres
                revert hres
                cases Staging.resume evm.sta.benvStat.rules (.ofLegacy p) child.checkpoint result with
                | error e => intro h; cases h
                | ok x =>
                  rcases x with ⟨r', s'⟩ | s'
                  · intro h; cases h
                  · intro h; cases h; exact hpo
              exact ih ⟨pc, evm.sta, d⟩ hd

/-- The square for `exec`: from a running machine with no output, the staged `exec` is the old one,
observed through `Frame.Exit.ofExecution`. -/
theorem exec_square (evm : Evm) (ho : evm.dyna.output = []) :
    Staging.exec (Frame.Running.ofEvm evm) = Frame.Exit.ofExecution (exec evm) := by
  unfold Staging.exec exec
  rw [show (Frame.Running.ofEvm evm).state.machine.gasMeasure = evm.dyna.gasMeasure from rfl,
    execFueled_square _ evm ho]
  cases (execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run <;> rfl

/-- The cached twin of the staged driver against the old driver. -/
theorem execFueledCached_square (fuel : Nat) (evm : Evm) (ho : evm.dyna.output = []) :
    (Staging.execFueledCached (Frame.Running.ofEvm evm) fuel).run =
      (Jaune.execFueled evm fuel).run.map Frame.Exit.ofExecution := by
  rw [← Staging.execFueled_eq_cached]
  exact execFueled_square fuel evm ho

/-- **The anchor.** For every frame, the staged top-level run is the old one: the whole
`Except Fault Frame.Result`. -/
theorem Frame.runTop_square (f : Frame) : Staging.Frame.runTop f = Frame.runTop f := by
  unfold Staging.Frame.runTop Frame.runTop
  have ho : f.checkpoint.toDevm.output = [] := rfl
  rw [← Staging.enterWith_ofDevm_toDevm f f.checkpoint, ← Frame.Entry.observe_enterWith f ho]
  cases he : enterWith f f.checkpoint.toDevm with
  | done r => rfl
  | run evm =>
    simp only [Frame.Entry.observe]
    rw [exec_square evm (enterWith_run_output ho he), settle_eq]

end Jaune
