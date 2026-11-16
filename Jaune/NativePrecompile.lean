import Jaune.Execution

/-!
# Enabled native STATICCALLs do not enter an interpreter child

The conclusion concerns the actual spawn and Frame.enter equations, including
native failure outcomes. It neither constructs a call nor asserts native success.
-/

namespace Jaune

private theorem accessDelegation_direct {rules : ForkRules} {d : Devm} {target : Adr}
    (direct : rules.delegatedCodeAddress (d.getCode target) = none) :
    rules.accessDelegation d target = ⟨false, target, d.getCode target, 0, d⟩ := by
  cases enabled : rules.delegationEnabled with
  | false =>
      simpa only [Devm.getCode_state] using
        (ForkRules.accessDelegation_disabled enabled d target)
  | true =>
      have nodeleg : getDelegatedCodeAddress (d.getCode target) = none :=
        (ForkRules.delegatedCodeAddress_enabled enabled _).symm.trans direct
      rw [ForkRules.accessDelegation_enabled enabled]
      simp only [GasSchedule.accessDelegation, ← Devm.getCode_state, nodeleg]

private theorem genericCall_native_not_run
    {sevm : Sevm} {d : Devm} {target : Adr} {gas ii isz oi osz : Nat} {code : ByteArray}
    {frame : Frame} {resume : Resume} {child : Evm}
    (active : decide (sevm.benvStat.rules.isPrecomp target) = true)
    (spawn : genericCall.step sevm d gas 0 sevm.currentTarget target target true true
      ii isz oi osz code false = .spawn frame resume)
    (enter : frame.enter = .run child) : False := by
  unfold genericCall.step at spawn
  split at spawn
  · simp only [bind, Except.bind, pure, Except.pure] at spawn
    repeat' split at spawn
    all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  · simp only [XStep.spawn.injEq] at spawn
    obtain ⟨rfl, -⟩ := spawn
    let msg := callMsg sevm (d.withReturnData []) gas 0 sevm.currentTarget target target true true
      (Array.sliceD d.memory.data ii isz 0) code false
    change (Frame.ofCall msg).enter = .run child at enter
    unfold Frame.enter at enter
    dsimp only [Frame.ofCall] at enter
    rw [Msg.benvAfterTransfer_of_value_zero (show msg.value = 0 from rfl)] at enter
    simp only [executeCode.enter, msg, Msg.withBenv, callMsg, Bool.not_false,
      Bool.true_and, active, ↓reduceIte] at enter
    cases enter

/-- The actual six-operand STATICCALL to an enabled, effectively direct native
precompile cannot enter an interpreter child. The original no-state-gas lane,
real spawn and real entry equations remain explicit; native errors are included. -/
theorem Xinst.step_staticcall_not_run_of_precompile
    {sevm : Sevm} {pre : Devm} {frame : Frame} {resume : Resume} {child : Evm}
    {g t ii size oi outSize : B256} {rest : List B256}
    (operands : pre.stack = g :: t :: ii :: size :: oi :: outSize :: rest)
    (stateGas : sevm.benvStat.rules.stateGas = none)
    (active : decide (sevm.benvStat.rules.isPrecomp t.toAdr) = true)
    (direct : sevm.benvStat.rules.delegatedCodeAddress (pre.getCode t.toAdr) = none)
    (spawn : Xinst.step sevm pre .staticcall = .spawn frame resume)
    (enter : frame.enter = .run child) : False := by
  rcases pre with ⟨⟨stack, memory, gasLeft, stateGasLeft⟩, metadata, world⟩
  change stack = _ at operands
  subst stack
  simp only [Xinst.step, stateGas, bind, Except.bind, Devm.popToNat_def,
    Devm.popToAdr_def, Devm.pop_def, Prod.mapFst, Devm.stack, Devm.setMach,
    Functor.mapRev, Except.map_ok, Prod.map, id_eq] at spawn
  let d : Devm := ⟨⟨rest, memory, gasLeft, stateGasLeft⟩, metadata, world⟩
  let accessed : Devm := match sevm.benvStat.rules.access with
    | .eip2929 => addAccessedAddress d t.toAdr
    | .flat _ => d
  have directAccessed :
      sevm.benvStat.rules.delegatedCodeAddress (accessed.getCode t.toAdr) = none := by
    dsimp only [accessed, d]
    cases sevm.benvStat.rules.access <;> exact direct
  have route := accessDelegation_direct directAccessed
  dsimp only [accessed, d] at route
  cases schedule : sevm.benvStat.rules.access <;> simp only [schedule] at route spawn
  all_goals
    rw [route] at spawn
    simp only [Nat.add_zero] at spawn
    split at spawn
    · simp only [XStep.ofExcept, reduceCtorEq] at spawn
    · simp only [pure, Except.pure, XStep.ofExcept] at spawn
      exact genericCall_native_not_run active spawn enter

end Jaune
