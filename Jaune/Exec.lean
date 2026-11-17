import Jaune.ExecFrame
import Jaune.Sufficiency
import Jaune.MessageCall.Totality

/-!
The canonical complete execution derivation and its adequacy theorem.
The first natural-number index is the initial program counter. The six
constructors preserve child execution, settlement and parent resumption.
-/

namespace Jaune

-- `ByteArray.getInst` and other extensions of root types live in `Jaune`;
-- opening it lets generalized field notation (`code.getInst`) find them.
open Jaune

/- Exec pc sevm devm ex is provable iff
    exec ⟨pc, sevm, devm⟩ = ex
   holds (`exec_iff_exec_eq`): with sufficiency proved in Jaune, the total
   `exec` is the executable side of the adequacy bridge, and no fuel appears
   in it.  The relation is the generic derivation tree over the flattened
   driver's step outcomes: every premise other than a sub-derivation is an
   equation about a non-recursive function. -/
inductive Legacy.Exec : Nat → Sevm → Devm → Execution → Type
  | halt {pc sevm devm ex} :
    Legacy.Evm.step ⟨pc, sevm, devm⟩ = .halt ex →
    Legacy.Exec pc sevm devm ex
  | cont {pc sevm devm pc' devm' ex} :
    Legacy.Evm.step ⟨pc, sevm, devm⟩ = .cont pc' devm' →
    Legacy.Exec pc' sevm devm' ex →
    Legacy.Exec pc sevm devm ex
  | doneErr {pc sevm devm f rsm pc' r e} :
    Legacy.Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .done r →
    rsm.run r = .error e →
    Legacy.Exec pc sevm devm (.error e)
  | doneOk {pc sevm devm f rsm pc' r devm' ex} :
    Legacy.Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .done r →
    rsm.run r = .ok devm' →
    Legacy.Exec pc' sevm devm' ex →
    Legacy.Exec pc sevm devm ex
  | runErr {pc sevm devm f rsm pc' cevm raw e} :
    Legacy.Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .run cevm →
    Legacy.Exec cevm.pc cevm.sta cevm.dyna raw →
    rsm.run (f.settle raw) = .error e →
    Legacy.Exec pc sevm devm (.error e)
  | runOk {pc sevm devm f rsm pc' cevm raw devm' ex} :
    Legacy.Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .run cevm →
    Legacy.Exec cevm.pc cevm.sta cevm.dyna raw →
    rsm.run (f.settle raw) = .ok devm' →
    Legacy.Exec pc' sevm devm' ex →
    Legacy.Exec pc sevm devm ex

def Xlot.Filled : Xlot → Prop
  | .none => True
  | .some ⟨evm, exn⟩ => Nonempty (Legacy.Exec evm.pc evm.sta evm.dyna exn)

/-! ### Inversion against the step outcome.

A derivation is determined at its root by the step outcome, so an equation
pinning that outcome collapses the six-way case analysis.  `halt_inv` is what
replaces the old "wrong instruction kind" branches of every `cases` on `Exec`:
where a proof knows the instruction at `pc` halts, the derivation's result is
that halt value. -/

lemma Legacy.Exec.halt_inv {pc sevm devm exn ex}
    (cr : Legacy.Exec pc sevm devm exn)
    (h : Legacy.Evm.step ⟨pc, sevm, devm⟩ = .halt ex) : exn = ex := by
  cases cr with
  | halt h' => cases h.symm.trans h'; rfl
  | cont h' _ => cases h.symm.trans h'
  | doneErr h' _ _ => cases h.symm.trans h'
  | doneOk h' _ _ _ => cases h.symm.trans h'
  | runErr h' _ _ _ => cases h.symm.trans h'
  | runOk h' _ _ _ _ => cases h.symm.trans h'

/-- A `Linst` at the program counter settles the whole derivation. -/
lemma Legacy.Exec.last_inv {pc sevm devm exn l}
    (cr : Legacy.Exec pc sevm devm exn) (h : HaltOp.At sevm.code pc l) :
    exn = l.run sevm devm :=
  cr.halt_inv (Legacy.Evm.step_last h)

/-- A nonterminal instruction together with any required child derivation. -/
def NextOp.Run (sevm : Sevm) (devm : Devm) (n : NextOp) (devm' : Devm) : Prop :=
  ∃ xl : Xlot, xl.Filled ∧ ∃ pc, NextOp.StepRun pc sevm devm n xl (.ok devm')

/-! ### Depth side conditions for the strong induction of `Common.lean`.

Every `.spawn` produced by the step functions is depth-guarded, so a child
frame always sits strictly below its parent, and entering a frame preserves
the frame's own depth. -/

lemma Legacy.genericCall.step_spawn_depth
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : U256}
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {f : Legacy.Frame} {rsm : Resume}
    (hs : Legacy.genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  simp only [Legacy.genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Legacy.Frame.ofCall, callMsg]
  all_goals omega

lemma Legacy.genericCreate.step_spawn_depth
    {sevm : Sevm} {devm : Devm} {endowment : U256} {newAddress : Address}
    {memoryIndex memorySize : Nat} {f : Legacy.Frame} {rsm : Resume}
    (hs : Legacy.genericCreate.step sevm devm endowment newAddress memoryIndex
      memorySize = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  simp only [Legacy.genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals
    simp only [Legacy.Frame.ofCreate, processCreateMessage.msg, Msg.withBenv,
      createMsg, not_or] at *
  all_goals omega

lemma Legacy.genericCallAmsterdam.step_spawn_depth
    {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {gas reservoir : Nat} {value : U256}
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles newAccountCharged insufficientBalance : Bool}
    {f : Legacy.Frame} {rsm : Resume}
    (hs : Legacy.genericCallAmsterdam.step sevm state devm gas reservoir value
      caller target codeAddress shouldTransferValue isStaticcall inputIndex
      inputSize outputIndex outputSize code disablePrecompiles
      newAccountCharged insufficientBalance = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  simp only [Legacy.genericCallAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Legacy.Frame.ofCall, callMsg]
  all_goals omega

lemma Legacy.genericCreateAmsterdam.step_spawn_depth
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : U256}
    {newAddress : Address} {memoryIndex memorySize : Nat} {f : Legacy.Frame} {rsm : Resume}
    (hs : Legacy.genericCreateAmsterdam.step sevm state devm endowment newAddress
      memoryIndex memorySize = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  simp only [Legacy.genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals
    simp only [Legacy.Frame.ofCreate, processCreateMessage.msg, Msg.withBenv,
      createMsg, not_or] at *
  all_goals omega

lemma Legacy.MessageOp.step_spawn_depth {sevm : Sevm} {devm : Devm} {x : MessageOp}
    {f : Legacy.Frame} {rsm : Resume}
    (hs : Legacy.MessageOp.step sevm devm x = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  cases x <;>
    simp only [Legacy.MessageOp.step, Bind.bind, Except.bind, Except.assert,
      Pure.pure, Except.pure] at hs <;>
    repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals
    first
      | exact Legacy.genericCreate.step_spawn_depth hs
      | exact Legacy.genericCall.step_spawn_depth hs
      | exact Legacy.genericCreateAmsterdam.step_spawn_depth hs
      | exact Legacy.genericCallAmsterdam.step_spawn_depth hs

/-- A CALL-family spawn hands the parent's block statics to the child frame. -/
lemma Legacy.genericCall.step_spawn_benvStat
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : U256}
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {f : Legacy.Frame} {rsm : Resume}
    (hs : Legacy.genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles = .spawn f rsm) :
    f.inner.benv.stat = sevm.benvStat := by
  simp only [Legacy.genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  rfl

/-- A CREATE-family spawn hands the parent's block statics to the child frame. -/
lemma Legacy.genericCreate.step_spawn_benvStat
    {sevm : Sevm} {devm : Devm} {endowment : U256} {newAddress : Address}
    {memoryIndex memorySize : Nat} {f : Legacy.Frame} {rsm : Resume}
    (hs : Legacy.genericCreate.step sevm devm endowment newAddress memoryIndex memorySize
      = .spawn f rsm) :
    f.inner.benv.stat = sevm.benvStat := by
  simp only [Legacy.genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  rfl

/-- An Amsterdam CALL-family spawn hands the parent's block statics to the child. -/
lemma Legacy.genericCallAmsterdam.step_spawn_benvStat
    {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {gas reservoir : Nat} {value : U256}
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles newAccountCharged insufficientBalance : Bool}
    {f : Legacy.Frame} {rsm : Resume}
    (hs : Legacy.genericCallAmsterdam.step sevm state devm gas reservoir value
      caller target codeAddress shouldTransferValue isStaticcall inputIndex
      inputSize outputIndex outputSize code disablePrecompiles
      newAccountCharged insufficientBalance = .spawn f rsm) :
    f.inner.benv.stat = sevm.benvStat := by
  simp only [Legacy.genericCallAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  rfl

/-- An Amsterdam CREATE-family spawn hands the parent's block statics to the child. -/
lemma Legacy.genericCreateAmsterdam.step_spawn_benvStat
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : U256}
    {newAddress : Address} {memoryIndex memorySize : Nat} {f : Legacy.Frame} {rsm : Resume}
    (hs : Legacy.genericCreateAmsterdam.step sevm state devm endowment newAddress
      memoryIndex memorySize = .spawn f rsm) :
    f.inner.benv.stat = sevm.benvStat := by
  simp only [Legacy.genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals rfl

/-- Every spawning instruction hands the parent's block statics to the child. -/
lemma Legacy.MessageOp.step_spawn_benvStat {sevm : Sevm} {devm : Devm} {x : MessageOp}
    {f : Legacy.Frame} {rsm : Resume} (hs : Legacy.MessageOp.step sevm devm x = .spawn f rsm) :
    f.inner.benv.stat = sevm.benvStat := by
  cases x <;>
    simp only [Legacy.MessageOp.step, Bind.bind, Except.bind, Except.assert,
      Pure.pure, Except.pure] at hs <;>
    repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals
    first
      | exact Legacy.genericCreate.step_spawn_benvStat hs
      | exact Legacy.genericCall.step_spawn_benvStat hs
      | exact Legacy.genericCreateAmsterdam.step_spawn_benvStat hs
      | exact Legacy.genericCallAmsterdam.step_spawn_benvStat hs

lemma Legacy.NextOp.step_spawn_depth {evm : Evm} {n : NextOp}
    {f : Legacy.Frame} {rsm : Resume} {pc' : Nat}
    (h : Legacy.NextOp.step evm n = .spawn f rsm pc') : f.inner.depth < evm.sta.depth := by
  obtain ⟨x, _, hx⟩ := Legacy.NextOp.step_spawn_inv h
  exact Legacy.MessageOp.step_spawn_depth hx

/-- A spawned child frame sits strictly below its parent's depth. -/
lemma Legacy.Step.spawn_depth_lt {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Legacy.Frame} {rsm : Resume} {pc' : Nat}
    (hs : Legacy.Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc') :
    f.inner.depth < sevm.depth := by
  unfold Legacy.Evm.step at hs
  split at hs
  · cases hs
  · rename_i n hgi
    rcases n with r | x | ⟨xs, hxs⟩ | a | a | a <;> simp only [Legacy.NextOp.step] at hs
    · cases Legacy.Step.ofExecution_ne_spawn hs
    · exact Legacy.MessageOp.step_spawn_depth (XStep.toStep_spawn hs)
    · split at hs <;> cases Legacy.Step.ofExecution_ne_spawn hs
    · cases Legacy.Step.ofExecution_ne_spawn hs
    · cases Legacy.Step.ofExecution_ne_spawn hs
    · cases Legacy.Step.ofExecution_ne_spawn hs
  · cases Legacy.Step.ofJump_ne_spawn hs
  · cases hs

/-! ### Adequacy: the relational and executable semantics agree. -/

lemma Legacy.of_exec' :
    ∀ (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      Legacy.Exec pc sevm devm exn →
      ∃ fuel, ∀ fuel' > fuel, (Legacy.execFueled ⟨pc, sevm, devm⟩ fuel' = Fueled.ofExcept exn) := by
  apply Legacy.Exec.rec
  · intro pc sevm devm ex hstep
    refine ⟨0, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    simp only [Legacy.execFueled, hstep]
  · intro pc sevm devm pc' devm' ex hstep _ ih
    rcases ih with ⟨fuel, ih⟩
    refine ⟨fuel + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    simp only [Legacy.execFueled, hstep]
    exact ih fuel' (by omega)
  · intro pc sevm devm f rsm pc' r e hstep henter hr
    refine ⟨0, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    simp only [Legacy.execFueled, hstep, henter, hr]
  · intro pc sevm devm f rsm pc' r devm' ex hstep henter hr _ ih
    rcases ih with ⟨fuel, ih⟩
    refine ⟨fuel + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    simp only [Legacy.execFueled, hstep, henter, hr]
    exact ih fuel' (by omega)
  · intro pc sevm devm f rsm pc' cevm raw e hstep henter _ hr ihc
    rcases ihc with ⟨fuelc, ihc⟩
    refine ⟨fuelc + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    have hc : Legacy.execFueled cevm fuel' = Fueled.ofExcept raw := ihc fuel' (by omega)
    simp only [Legacy.execFueled, hstep, henter]
    rw [hc]
    simp only [Fueled.ofExcept_run, hr]
  · intro pc sevm devm f rsm pc' cevm raw devm' ex hstep henter _ hr _ ihc ih
    rcases ihc with ⟨fuelc, ihc⟩
    rcases ih with ⟨fuelp, ih⟩
    refine ⟨max fuelc fuelp + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    have hc : Legacy.execFueled cevm fuel' = Fueled.ofExcept raw := ihc fuel' (by omega)
    simp only [Legacy.execFueled, hstep, henter]
    rw [hc]
    simp only [Fueled.ofExcept_run, hr]
    exact ih fuel' (by omega)

set_option linter.defProp false in
@[reducible] def Legacy.of_exec :
    ∀ (fuel : Nat) (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      (Legacy.execFueled ⟨pc, sevm, devm⟩ fuel = Fueled.ofExcept exn) →
      Nonempty (Legacy.Exec pc sevm devm exn) := by
  apply Nat.strongRec
  intro fuel ih pc sevm devm exn exec_eq
  cases fuel with
  | zero =>
    simp only [Legacy.execFueled] at exec_eq
    cases Fueled.exhausted_ne_ofExcept exec_eq
  | succ fuel =>
    simp only [Legacy.execFueled] at exec_eq
    rcases hstep : Legacy.Evm.step ⟨pc, sevm, devm⟩ with ex | ⟨pc', devm'⟩ | ⟨f, rsm, pc'⟩ <;>
      rw [hstep] at exec_eq <;> simp only [] at exec_eq
    · rw [← Fueled.ofExcept_inj.mp exec_eq]
      exact ⟨Legacy.Exec.halt hstep⟩
    · rcases ih fuel (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
      exact ⟨Legacy.Exec.cont hstep exc⟩
    · rcases henter : f.enter with r | cevm <;>
        rw [henter] at exec_eq <;> simp only [] at exec_eq
      · rcases hr : rsm.run r with e | devm' <;>
          rw [hr] at exec_eq <;> simp only [] at exec_eq
        · rw [← Fueled.ofExcept_inj.mp exec_eq]
          exact ⟨Legacy.Exec.doneErr hstep henter hr⟩
        · rcases ih fuel (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
          exact ⟨Legacy.Exec.doneOk hstep henter hr exc⟩
      · rcases hrun : (Legacy.execFueled cevm fuel).run with _ | raw <;>
          rw [hrun] at exec_eq <;> simp only [] at exec_eq
        · cases Fueled.exhausted_ne_ofExcept exec_eq
        · have hc : Legacy.execFueled cevm fuel = Fueled.ofExcept raw := Fueled.ext hrun
          rcases ih fuel (Nat.lt_succ_self _) cevm.pc cevm.sta cevm.dyna raw hc with
            ⟨excChild⟩
          rcases hr : rsm.run (f.settle raw) with e | devm' <;>
            rw [hr] at exec_eq <;> simp only [] at exec_eq
          · rw [← Fueled.ofExcept_inj.mp exec_eq]
            exact ⟨Legacy.Exec.runErr hstep henter excChild hr⟩
          · rcases ih fuel (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
            exact ⟨Legacy.Exec.runOk hstep henter excChild hr exc⟩

/-- **Adequacy, fuel-free.**  A closed derivation is exactly a total-`exec`
equation.  Forward: `of_exec'` produces the driver equation at every budget
past some threshold, and Jaune's `exec_eq_of_run` reads it off at a budget
that also exceeds the frame's gas measure.  Backward: the sufficiency bridge
`execFueled_run_sufficientFuel` turns the total result into the driver equation
`of_exec` recurses over. -/
lemma Legacy.exec_iff_exec_eq (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution) :
    Nonempty (Legacy.Exec pc sevm devm exn) ↔ Legacy.exec ⟨pc, sevm, devm⟩ = exn := by
  constructor
  · intro ⟨exc⟩
    rcases Legacy.of_exec' _ _ _ _ exc with ⟨fuel, eq⟩
    have hlt : devm.gasMeasure < max (fuel + 1) (devm.gasMeasure + 1) :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
    refine Legacy.exec_eq_of_run hlt ?_
    rw [eq _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _))]
    rfl
  · intro heq
    have h := Legacy.execFueled_run_sufficientFuel ⟨pc, sevm, devm⟩
    rw [heq] at h
    exact Legacy.of_exec _ _ _ _ _ (Fueled.ext h)

/-- The driver at the child's seeded budget reaches exactly the total `exec`
result, so every entered frame carries a closed derivation for it.  This is the
bridge from the total wrappers to the relational layer: no threshold obligation
survives, because sufficiency discharges it once and for all. -/
lemma Xlot.filled_exec (evm : Evm) : Xlot.Filled (.some ⟨evm, Legacy.exec evm⟩) :=
  Legacy.of_exec (sufficientFuel evm.dyna.gasMeasure) evm.pc evm.sta evm.dyna (Legacy.exec evm)
    (Fueled.ext (Legacy.execFueled_run_sufficientFuel evm))

lemma of_runFrame {f : Legacy.Frame}
    {r : Except (EvmError × State × AdrSet × TransientStorage) Devm}
    (eq : runFrame f = r) :
    ∃ xl : Xlot, xl.Filled ∧ RunFrame f xl r := by
  unfold runFrame at eq
  rcases henter : f.enter with r' | evm <;> rw [henter] at eq
  · refine ⟨.none, trivial, ?_⟩
    unfold RunFrame
    rw [henter]
    exact ⟨rfl, eq.symm⟩
  · refine ⟨.some ⟨evm, Legacy.exec evm⟩, Xlot.filled_exec evm, ?_⟩
    unfold RunFrame
    rw [henter]
    exact ⟨Legacy.exec evm, rfl, eq.symm⟩

lemma of_processMessage (msg : Msg)
    (ex : Except (EvmError × State × AdrSet × TransientStorage) Devm)
    (eq : processMessage msg = ex) :
    ∃ xl : Xlot, xl.Filled ∧ ProcessMessage msg xl ex :=
  of_runFrame eq

lemma of_processCreateMessage (msg : Msg)
    (ex : Except (EvmError × State × AdrSet × TransientStorage) Devm)
    (eq : processCreateMessage msg = ex) :
    ∃ xl : Xlot,
      xl.Filled ∧
      ProcessCreateMessage msg xl ex :=
  of_runFrame eq


/-! ## The derivation over the four-part message call

`Exec` restated over the four-part message call (goal `jaune-shape-and-names-v1`, W1 unit J): its
premises are equations about `Evm.step`, `enter`, `settle` and `resume`. The shape is
`Legacy.Exec`'s: six constructors, the same recursive premises. -/

/-- The caller's continuation after a spawned child, as the driver takes it: a fault ends the
run, a halted caller ends it with the halt, and a resumed caller goes on. A fault carries the
child's checkpoint, which nothing reads (W1). -/
def resumeCaller (rules : ForkRules) (child : Frame) (pending : Pending) :
    Except Fault Frame.Result → Execution
  | .error fault => .error (fault.toEvmError, child.checkpoint.toDevm)
  | .ok result =>
    match resume rules pending child.checkpoint result with
    | .error fault => .error (fault.toEvmError, child.checkpoint.toDevm)
    | .ok (.error (reason, devm)) => .error (.halt reason, devm)
    | .ok (.ok devm) => .ok devm

/- Exec pc sevm devm ex is provable iff
    exec ⟨pc, sevm, devm⟩ = ex
   holds (`exec_iff_exec_eq`). The relation is the derivation tree over the driver's step
   outcomes: every premise other than a sub-derivation is an equation about a non-recursive
   function of the four-part message call. -/
inductive Exec : Nat → Sevm → Devm → Execution → Type
  | halt {pc sevm devm ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .halt ex →
    Exec pc sevm devm ex
  | cont {pc sevm devm pc' devm' ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .next pc' devm' →
    Exec pc' sevm devm' ex →
    Exec pc sevm devm ex
  | doneErr {pc sevm devm child pending pc' r e} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn child pending pc' →
    enter child = .done r →
    resumeCaller sevm.benvStat.rules child pending r = .error e →
    Exec pc sevm devm (.error e)
  | doneOk {pc sevm devm child pending pc' r devm' ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn child pending pc' →
    enter child = .done r →
    resumeCaller sevm.benvStat.rules child pending r = .ok devm' →
    Exec pc' sevm devm' ex →
    Exec pc sevm devm ex
  | runErr {pc sevm devm child pending pc' cevm raw e} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn child pending pc' →
    enter child = .run cevm →
    Exec cevm.pc cevm.sta cevm.dyna raw →
    resumeCaller sevm.benvStat.rules child pending (settle child raw) = .error e →
    Exec pc sevm devm (.error e)
  | runOk {pc sevm devm child pending pc' cevm raw devm' ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn child pending pc' →
    enter child = .run cevm →
    Exec cevm.pc cevm.sta cevm.dyna raw →
    resumeCaller sevm.benvStat.rules child pending (settle child raw) = .ok devm' →
    Exec pc' sevm devm' ex →
    Exec pc sevm devm ex

/-- A derivation is determined at its root by the step outcome: where the step halts, the
derivation's result is that halt value. -/
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

/-- A halting instruction at the program counter settles the whole derivation. -/
lemma Exec.last_inv {pc sevm devm exn l}
    (cr : Exec pc sevm devm exn) (h : HaltOp.At sevm.code pc l) :
    exn = l.run sevm devm :=
  cr.halt_inv (by
    unfold Evm.step
    rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = some (.halt l) from h])

/-! ### Adequacy -/

/-- The driver at a spawn whose child is settled at entry. -/
theorem execFueled_spawn_done {evm : Evm} {fuel : Nat} {child : Frame} {pending : Pending}
    {pc : Nat} {r : Except Fault Frame.Result}
    (hs : Evm.step evm = .spawn child pending pc) (he : enter child = .done r) :
    execFueled evm (fuel + 1) =
      match resumeCaller evm.sta.benvStat.rules child pending r with
      | .error e => Fueled.ofExcept (.error e)
      | .ok devm => execFueled ⟨pc, evm.sta, devm⟩ fuel := by
  rw [execFueled, hs]
  dsimp only
  rw [he]
  dsimp only
  rcases r with fault | result
  · rfl
  · dsimp only [resumeCaller]
    rcases resume evm.sta.benvStat.rules pending child.checkpoint result with
      fault | ⟨reason, devm⟩ | devm <;> rfl

/-- The driver at a spawn whose child runs. -/
theorem execFueled_spawn_run {evm : Evm} {fuel : Nat} {child : Frame} {pending : Pending}
    {pc : Nat} {cevm : Evm}
    (hs : Evm.step evm = .spawn child pending pc) (he : enter child = .run cevm) :
    execFueled evm (fuel + 1) =
      match (execFueled cevm fuel).run with
      | none => Fueled.exhausted
      | some raw =>
        match resumeCaller evm.sta.benvStat.rules child pending (settle child raw) with
        | .error e => Fueled.ofExcept (.error e)
        | .ok devm => execFueled ⟨pc, evm.sta, devm⟩ fuel := by
  rw [execFueled, hs]
  dsimp only
  rw [he]
  dsimp only
  rcases (execFueled cevm fuel).run with _ | raw
  · rfl
  · dsimp only [Option.map]
    rcases settle child raw with fault | result
    · rfl
    · dsimp only [resumeCaller]
      rcases resume evm.sta.benvStat.rules pending child.checkpoint result with
        fault | ⟨reason, devm⟩ | devm <;> rfl

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
  · intro pc sevm devm child pending pc' r e hstep henter hr
    refine ⟨0, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    rw [execFueled_spawn_done hstep henter]
    simp only [hr]
  · intro pc sevm devm child pending pc' r devm' ex hstep henter hr _ ih
    rcases ih with ⟨fuel, ih⟩
    refine ⟨fuel + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    rw [execFueled_spawn_done hstep henter]
    simp only [hr]
    exact ih fuel' (by omega)
  · intro pc sevm devm child pending pc' cevm raw e hstep henter _ hr ihc
    rcases ihc with ⟨fuelc, ihc⟩
    refine ⟨fuelc + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    have hc : execFueled cevm fuel' = Fueled.ofExcept raw := ihc fuel' (by omega)
    rw [execFueled_spawn_run hstep henter, hc]
    simp only [Fueled.ofExcept_run, hr]
  · intro pc sevm devm child pending pc' cevm raw devm' ex hstep henter _ hr _ ihc ih
    rcases ihc with ⟨fuelc, ihc⟩
    rcases ih with ⟨fuelp, ih⟩
    refine ⟨max fuelc fuelp + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    have hc : execFueled cevm fuel' = Fueled.ofExcept raw := ihc fuel' (by omega)
    rw [execFueled_spawn_run hstep henter, hc]
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
    rcases hstep : Evm.step ⟨pc, sevm, devm⟩ with ex | ⟨pc', devm'⟩ | ⟨child, pending, pc'⟩
    · simp only [execFueled, hstep] at exec_eq
      rw [← Fueled.ofExcept_inj.mp exec_eq]
      exact ⟨Exec.halt hstep⟩
    · simp only [execFueled, hstep] at exec_eq
      rcases ih fuel (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
      exact ⟨Exec.cont hstep exc⟩
    · rcases henter : enter child with cevm | r
      · rw [execFueled_spawn_run hstep henter] at exec_eq
        rcases hrun : (execFueled cevm fuel).run with _ | raw <;>
          rw [hrun] at exec_eq <;> simp only [] at exec_eq
        · cases Fueled.exhausted_ne_ofExcept exec_eq
        · have hc : execFueled cevm fuel = Fueled.ofExcept raw := Fueled.ext hrun
          rcases ih fuel (Nat.lt_succ_self _) cevm.pc cevm.sta cevm.dyna raw hc with
            ⟨excChild⟩
          rcases hr : resumeCaller sevm.benvStat.rules child pending (settle child raw) with
              e | devm' <;>
            rw [hr] at exec_eq <;> simp only [] at exec_eq
          · rw [← Fueled.ofExcept_inj.mp exec_eq]
            exact ⟨Exec.runErr hstep henter excChild hr⟩
          · rcases ih fuel (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
            exact ⟨Exec.runOk hstep henter excChild hr exc⟩
      · rw [execFueled_spawn_done hstep henter] at exec_eq
        rcases hr : resumeCaller sevm.benvStat.rules child pending r with e | devm' <;>
          rw [hr] at exec_eq <;> simp only [] at exec_eq
        · rw [← Fueled.ofExcept_inj.mp exec_eq]
          exact ⟨Exec.doneErr hstep henter hr⟩
        · rcases ih fuel (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
          exact ⟨Exec.doneOk hstep henter hr exc⟩

/-- **Adequacy, fuel-free.** A closed derivation is exactly a total-`exec` equation. Forward:
`of_exec'` gives the driver equation at every budget past some threshold, and
`exec_eq_of_run` reads it off at a budget past the frame's gas measure. Backward:
`execFueled_run_sufficientFuel` turns the total result into the driver equation `of_exec`
recurses over. -/
theorem exec_iff_exec_eq (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution) :
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

/-- Every machine has a closed derivation of its total result. -/
theorem Exec.nonempty (evm : Evm) : Nonempty (Exec evm.pc evm.sta evm.dyna (exec evm)) :=
  (exec_iff_exec_eq evm.pc evm.sta evm.dyna (exec evm)).mpr rfl

end Jaune
