import Jaune.ExecFrame
import Jaune.Sufficiency

/-!
The canonical complete execution derivation and its adequacy theorem.
The first natural-number index is the initial program counter. The six
constructors preserve child execution, settlement and parent resumption.
The historical `Blanc.Exec` name is retained for downstream compatibility.
-/

namespace Blanc

open Jaune

/- Exec pc sevm devm ex is provable iff
    exec ⟨pc, sevm, devm⟩ = ex
   holds (`exec_iff_exec_eq`): with sufficiency proved in Jaune, the total
   `exec` is the executable side of the adequacy bridge, and no fuel appears
   in it.  The relation is the generic derivation tree over the flattened
   driver's step outcomes: every premise other than a sub-derivation is an
   equation about a non-recursive function. -/
inductive Exec : Nat → Sevm → Devm → Execution → Type
  | halt {pc sevm devm ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .halt ex →
    Exec pc sevm devm ex
  | cont {pc sevm devm pc' devm' ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .cont pc' devm' →
    Exec pc' sevm devm' ex →
    Exec pc sevm devm ex
  | doneErr {pc sevm devm f rsm pc' r e} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .done r →
    rsm.run r = .error e →
    Exec pc sevm devm (.error e)
  | doneOk {pc sevm devm f rsm pc' r devm' ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .done r →
    rsm.run r = .ok devm' →
    Exec pc' sevm devm' ex →
    Exec pc sevm devm ex
  | runErr {pc sevm devm f rsm pc' cevm raw e} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .run cevm →
    Exec cevm.pc cevm.sta cevm.dyna raw →
    rsm.run (f.settle raw) = .error e →
    Exec pc sevm devm (.error e)
  | runOk {pc sevm devm f rsm pc' cevm raw devm' ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .run cevm →
    Exec cevm.pc cevm.sta cevm.dyna raw →
    rsm.run (f.settle raw) = .ok devm' →
    Exec pc' sevm devm' ex →
    Exec pc sevm devm ex

def Xlot.Filled : Xlot → Prop
  | .none => True
  | .some ⟨evm, exn⟩ => Nonempty (Exec evm.pc evm.sta evm.dyna exn)

/-! ### Inversion against the step outcome.

A derivation is determined at its root by the step outcome, so an equation
pinning that outcome collapses the six-way case analysis.  `halt_inv` is what
replaces the old "wrong instruction kind" branches of every `cases` on `Exec`:
where a proof knows the instruction at `pc` halts, the derivation's result is
that halt value. -/

lemma Exec.halt_inv {pc sevm devm exn ex}
    (cr : Exec pc sevm devm exn)
    (h : Evm.step ⟨pc, sevm, devm⟩ = .halt ex) : exn = ex := by
  cases cr with
  | halt h' => cases h.symm.trans h'; rfl
  | cont h' _ => cases h.symm.trans h'
  | doneErr h' _ _ => cases h.symm.trans h'
  | doneOk h' _ _ _ => cases h.symm.trans h'
  | runErr h' _ _ _ => cases h.symm.trans h'
  | runOk h' _ _ _ _ => cases h.symm.trans h'

/-- A `Linst` at the program counter settles the whole derivation. -/
lemma Exec.last_inv {pc sevm devm exn l}
    (cr : Exec pc sevm devm exn) (h : Linst.At sevm.code pc l) :
    exn = l.run sevm devm :=
  cr.halt_inv (Evm.step_last h)

/-- A nonterminal instruction together with any required child derivation. -/
def Ninst.Run (sevm : Sevm) (devm : Devm) (n : Ninst) (devm' : Devm) : Prop :=
  ∃ xl : Xlot, xl.Filled ∧ ∃ pc, Ninst.StepRun pc sevm devm n xl (.ok devm')

/- The residue of the fuel-bounded (`Fueled`) reasoning layer.  With
   sufficiency proved in Jaune, fuel never reaches a Blanc statement: these
   three lemmas exist only so that the adequacy bridge between `Exec` and the
   total `exec` can be proved by induction over `execFueled`. -/

namespace Fueled

variable {ε : Type} {α : Type}

lemma ext {x y : Fueled ε α} (h : x.run = y.run) : x = y := h

lemma exhausted_ne_ofExcept {x : Except ε α} :
    (Fueled.exhausted : Fueled ε α) ≠ Fueled.ofExcept x :=
  fun h => nomatch congrArg ExceptT.run h

@[simp] lemma ofExcept_inj {x y : Except ε α} :
    (Fueled.ofExcept x : Fueled ε α) = Fueled.ofExcept y ↔ x = y :=
  ⟨fun h => Option.some.inj (congrArg ExceptT.run h), fun h => by rw [h]⟩

end Fueled

/-! ### Depth side conditions for the strong induction of `Common.lean`.

Every `.spawn` produced by the step functions is depth-guarded, so a child
frame always sits strictly below its parent, and entering a frame preserves
the frame's own depth. -/

lemma genericCall.step_spawn_depth
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {f : Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Frame.ofCall, callMsg]
  all_goals omega

lemma genericCreate.step_spawn_depth
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {f : Frame} {rsm : Resume}
    (hs : genericCreate.step sevm devm endowment newAddress memoryIndex
      memorySize = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals
    simp only [Frame.ofCreate, processCreateMessage.msg, Msg.withBenv,
      createMsg, not_or] at *
  all_goals omega

lemma genericCallAmsterdam.step_spawn_depth
    {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {gas reservoir : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles newAccountCharged insufficientBalance : Bool}
    {f : Frame} {rsm : Resume}
    (hs : genericCallAmsterdam.step sevm state devm gas reservoir value
      caller target codeAddress shouldTransferValue isStaticcall inputIndex
      inputSize outputIndex outputSize code disablePrecompiles
      newAccountCharged insufficientBalance = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  simp only [genericCallAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Frame.ofCall, callMsg]
  all_goals omega

lemma genericCreateAmsterdam.step_spawn_depth
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : B256}
    {newAddress : Adr} {memoryIndex memorySize : Nat} {f : Frame} {rsm : Resume}
    (hs : genericCreateAmsterdam.step sevm state devm endowment newAddress
      memoryIndex memorySize = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals
    simp only [Frame.ofCreate, processCreateMessage.msg, Msg.withBenv,
      createMsg, not_or] at *
  all_goals omega

lemma Xinst.step_spawn_depth {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  cases x <;>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert,
      Pure.pure, Except.pure] at hs <;>
    repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals
    first
      | exact genericCreate.step_spawn_depth hs
      | exact genericCall.step_spawn_depth hs
      | exact genericCreateAmsterdam.step_spawn_depth hs
      | exact genericCallAmsterdam.step_spawn_depth hs

/-- A CALL-family spawn hands the parent's block statics to the child frame. -/
lemma genericCall.step_spawn_benvStat
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {f : Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles = .spawn f rsm) :
    f.inner.benv.stat = sevm.benvStat := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  rfl

/-- A CREATE-family spawn hands the parent's block statics to the child frame. -/
lemma genericCreate.step_spawn_benvStat
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {f : Frame} {rsm : Resume}
    (hs : genericCreate.step sevm devm endowment newAddress memoryIndex memorySize
      = .spawn f rsm) :
    f.inner.benv.stat = sevm.benvStat := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  rfl

/-- An Amsterdam CALL-family spawn hands the parent's block statics to the child. -/
lemma genericCallAmsterdam.step_spawn_benvStat
    {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {gas reservoir : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles newAccountCharged insufficientBalance : Bool}
    {f : Frame} {rsm : Resume}
    (hs : genericCallAmsterdam.step sevm state devm gas reservoir value
      caller target codeAddress shouldTransferValue isStaticcall inputIndex
      inputSize outputIndex outputSize code disablePrecompiles
      newAccountCharged insufficientBalance = .spawn f rsm) :
    f.inner.benv.stat = sevm.benvStat := by
  simp only [genericCallAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  rfl

/-- An Amsterdam CREATE-family spawn hands the parent's block statics to the child. -/
lemma genericCreateAmsterdam.step_spawn_benvStat
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : B256}
    {newAddress : Adr} {memoryIndex memorySize : Nat} {f : Frame} {rsm : Resume}
    (hs : genericCreateAmsterdam.step sevm state devm endowment newAddress
      memoryIndex memorySize = .spawn f rsm) :
    f.inner.benv.stat = sevm.benvStat := by
  simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals rfl

/-- Every spawning instruction hands the parent's block statics to the child. -/
lemma Xinst.step_spawn_benvStat {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} (hs : Xinst.step sevm devm x = .spawn f rsm) :
    f.inner.benv.stat = sevm.benvStat := by
  cases x <;>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert,
      Pure.pure, Except.pure] at hs <;>
    repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals
    first
      | exact genericCreate.step_spawn_benvStat hs
      | exact genericCall.step_spawn_benvStat hs
      | exact genericCreateAmsterdam.step_spawn_benvStat hs
      | exact genericCallAmsterdam.step_spawn_benvStat hs

lemma Ninst.step_spawn_depth {evm : Evm} {n : Ninst}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (h : Ninst.step evm n = .spawn f rsm pc') : f.inner.depth < evm.sta.depth := by
  obtain ⟨x, _, hx⟩ := Ninst.step_spawn_inv h
  exact Xinst.step_spawn_depth hx

/-- A spawned child frame sits strictly below its parent's depth. -/
lemma Step.spawn_depth_lt {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc') :
    f.inner.depth < sevm.depth := by
  unfold Evm.step at hs
  split at hs
  · cases hs
  · rename_i n hgi
    rcases n with r | x | ⟨xs, hxs⟩ | a | a | a <;> simp only [Ninst.step] at hs
    · cases Step.ofExecution_ne_spawn hs
    · exact Xinst.step_spawn_depth (XStep.toStep_spawn hs)
    · cases Step.ofExecution_ne_spawn hs
    · cases Step.ofExecution_ne_spawn hs
    · cases Step.ofExecution_ne_spawn hs
    · cases Step.ofExecution_ne_spawn hs
  · cases Step.ofJump_ne_spawn hs
  · cases hs

/-! ### Adequacy: the relational and executable semantics agree. -/

lemma of_exec' :
    ∀ (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      Exec pc sevm devm exn →
      ∃ fuel, ∀ fuel' > fuel, (execFueled ⟨pc, sevm, devm⟩ fuel' = Fueled.ofExcept exn) := by
  apply Exec.rec
  · intro pc sevm devm ex hstep
    refine ⟨0, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    simp only [execFueled, hstep]
  · intro pc sevm devm pc' devm' ex hstep _ ih
    rcases ih with ⟨fuel, ih⟩
    refine ⟨fuel + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    simp only [execFueled, hstep]
    exact ih fuel' (by omega)
  · intro pc sevm devm f rsm pc' r e hstep henter hr
    refine ⟨0, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    simp only [execFueled, hstep, henter, hr]
  · intro pc sevm devm f rsm pc' r devm' ex hstep henter hr _ ih
    rcases ih with ⟨fuel, ih⟩
    refine ⟨fuel + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    simp only [execFueled, hstep, henter, hr]
    exact ih fuel' (by omega)
  · intro pc sevm devm f rsm pc' cevm raw e hstep henter _ hr ihc
    rcases ihc with ⟨fuelc, ihc⟩
    refine ⟨fuelc + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    have hc : execFueled cevm fuel' = Fueled.ofExcept raw := ihc fuel' (by omega)
    simp only [execFueled, hstep, henter]
    rw [hc]
    simp only [Fueled.ofExcept_run, hr]
  · intro pc sevm devm f rsm pc' cevm raw devm' ex hstep henter _ hr _ ihc ih
    rcases ihc with ⟨fuelc, ihc⟩
    rcases ih with ⟨fuelp, ih⟩
    refine ⟨max fuelc fuelp + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    have hc : execFueled cevm fuel' = Fueled.ofExcept raw := ihc fuel' (by omega)
    simp only [execFueled, hstep, henter]
    rw [hc]
    simp only [Fueled.ofExcept_run, hr]
    exact ih fuel' (by omega)

set_option linter.defProp false in
@[reducible] def of_exec :
    ∀ (fuel : Nat) (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      (execFueled ⟨pc, sevm, devm⟩ fuel = Fueled.ofExcept exn) →
      Nonempty (Exec pc sevm devm exn) := by
  apply Nat.strongRec
  intro fuel ih pc sevm devm exn exec_eq
  cases fuel with
  | zero =>
    simp only [execFueled] at exec_eq
    cases Fueled.exhausted_ne_ofExcept exec_eq
  | succ fuel =>
    simp only [execFueled] at exec_eq
    rcases hstep : Evm.step ⟨pc, sevm, devm⟩ with ex | ⟨pc', devm'⟩ | ⟨f, rsm, pc'⟩ <;>
      rw [hstep] at exec_eq <;> simp only [] at exec_eq
    · rw [← Fueled.ofExcept_inj.mp exec_eq]
      exact ⟨Exec.halt hstep⟩
    · rcases ih fuel (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
      exact ⟨Exec.cont hstep exc⟩
    · rcases henter : f.enter with r | cevm <;>
        rw [henter] at exec_eq <;> simp only [] at exec_eq
      · rcases hr : rsm.run r with e | devm' <;>
          rw [hr] at exec_eq <;> simp only [] at exec_eq
        · rw [← Fueled.ofExcept_inj.mp exec_eq]
          exact ⟨Exec.doneErr hstep henter hr⟩
        · rcases ih fuel (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
          exact ⟨Exec.doneOk hstep henter hr exc⟩
      · rcases hrun : (execFueled cevm fuel).run with _ | raw <;>
          rw [hrun] at exec_eq <;> simp only [] at exec_eq
        · cases Fueled.exhausted_ne_ofExcept exec_eq
        · have hc : execFueled cevm fuel = Fueled.ofExcept raw := Fueled.ext hrun
          rcases ih fuel (Nat.lt_succ_self _) cevm.pc cevm.sta cevm.dyna raw hc with
            ⟨excChild⟩
          rcases hr : rsm.run (f.settle raw) with e | devm' <;>
            rw [hr] at exec_eq <;> simp only [] at exec_eq
          · rw [← Fueled.ofExcept_inj.mp exec_eq]
            exact ⟨Exec.runErr hstep henter excChild hr⟩
          · rcases ih fuel (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
            exact ⟨Exec.runOk hstep henter excChild hr exc⟩

/-- **Adequacy, fuel-free.**  A closed derivation is exactly a total-`exec`
equation.  Forward: `of_exec'` produces the driver equation at every budget
past some threshold, and Jaune's `exec_eq_of_run` reads it off at a budget
that also exceeds the frame's gas measure.  Backward: the sufficiency bridge
`execFueled_run_sufficientFuel` turns the total result into the driver equation
`of_exec` recurses over. -/
lemma exec_iff_exec_eq (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution) :
    Nonempty (Exec pc sevm devm exn) ↔ exec ⟨pc, sevm, devm⟩ = exn := by
  constructor
  · intro ⟨exc⟩
    rcases of_exec' _ _ _ _ exc with ⟨fuel, eq⟩
    have hlt : devm.gasMeasure < max (fuel + 1) (devm.gasMeasure + 1) :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
    refine exec_eq_of_run hlt ?_
    rw [eq _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _))]
    rfl
  · intro heq
    have h := execFueled_run_sufficientFuel ⟨pc, sevm, devm⟩
    rw [heq] at h
    exact of_exec _ _ _ _ _ (Fueled.ext h)

/-- The driver at the child's seeded budget reaches exactly the total `exec`
result, so every entered frame carries a closed derivation for it.  This is the
bridge from the total wrappers to the relational layer: no threshold obligation
survives, because sufficiency discharges it once and for all. -/
lemma Xlot.filled_exec (evm : Evm) : Xlot.Filled (.some ⟨evm, exec evm⟩) :=
  of_exec (sufficientFuel evm.dyna.gasMeasure) evm.pc evm.sta evm.dyna (exec evm)
    (Fueled.ext (execFueled_run_sufficientFuel evm))

lemma of_runFrame {f : Frame}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (eq : runFrame f = r) :
    ∃ xl : Xlot, xl.Filled ∧ RunFrame f xl r := by
  unfold runFrame at eq
  rcases henter : f.enter with r' | evm <;> rw [henter] at eq
  · refine ⟨.none, trivial, ?_⟩
    unfold RunFrame
    rw [henter]
    exact ⟨rfl, eq.symm⟩
  · refine ⟨.some ⟨evm, exec evm⟩, Xlot.filled_exec evm, ?_⟩
    unfold RunFrame
    rw [henter]
    exact ⟨exec evm, rfl, eq.symm⟩

lemma of_processMessage (msg : Msg)
    (ex : Except (EvmError × State × AdrSet × Tra) Devm)
    (eq : processMessage msg = ex) :
    ∃ xl : Xlot, xl.Filled ∧ ProcessMessage msg xl ex :=
  of_runFrame eq

lemma of_processCreateMessage (msg : Msg)
    (ex : Except (EvmError × State × AdrSet × Tra) Devm)
    (eq : processCreateMessage msg = ex) :
    ∃ xl : Xlot,
      xl.Filled ∧
      ProcessCreateMessage msg xl ex :=
  of_runFrame eq


end Blanc
