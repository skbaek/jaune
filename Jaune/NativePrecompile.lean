import Jaune.Execution
import Jaune.MessageCall.Enter
import Jaune.MessageCall.Step

/-!
# Enabled native STATICCALLs do not enter an interpreter child

The conclusion concerns the actual spawn and `enter` equations, including
native failure outcomes. It neither constructs a call nor asserts native success.
-/

namespace Jaune

private theorem accessDelegation_direct {rules : ForkRules} {d : Devm} {target : Address}
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

/-! ## On the four-part message call -/

private theorem genericCall_native_not_run
    {sevm : Sevm} {d : Devm} {target : Address} {gas ii isz oi osz : Nat} {code : ByteArray}
    {child : Frame} {pending : Pending} {c : Evm}
    (active : decide (sevm.benvStat.rules.isPrecompile target) = true)
    (spawn : genericCall.step sevm d gas 0 sevm.currentTarget target target true true
      ii isz oi osz code false = .spawn child pending)
    (entered : enter child = .run c) : False := by
  unfold genericCall.step at spawn
  split at spawn
  · simp only [bind, Except.bind, pure, Except.pure] at spawn
    repeat' split at spawn
    all_goals simp only [MessageOp.Outcome.ofExcept, reduceCtorEq] at spawn
  · simp only [MessageOp.Outcome.spawn.injEq] at spawn
    obtain ⟨rfl, -⟩ := spawn
    simp only [enter, enterWith, Message.transfer, callMessage, ne_eq,
      not_true_eq_false, and_false, ↓reduceIte, Bool.not_false, Bool.true_and] at entered
    split at entered
    · cases entered
    · rename_i h
      exact h (decide_eq_true (of_decide_eq_true active))

/-- The six-operand STATICCALL to an enabled, effectively direct native precompile cannot
enter an interpreter child, over `MessageOp.step` and `enter`. -/
theorem MessageOp.step_staticcall_not_run_of_precompile
    {sevm : Sevm} {pre : Devm} {child : Frame} {pending : Pending} {c : Evm}
    {g t ii size oi outSize : U256} {rest : List U256}
    (operands : pre.stack = g :: t :: ii :: size :: oi :: outSize :: rest)
    (stateGas : sevm.benvStat.rules.stateGas = none)
    (active : decide (sevm.benvStat.rules.isPrecompile t.toAddress) = true)
    (direct : sevm.benvStat.rules.delegatedCodeAddress (pre.getCode t.toAddress) = none)
    (spawn : MessageOp.step sevm pre .staticcall = .spawn child pending)
    (entered : enter child = .run c) : False := by
  rcases pre with ⟨⟨stack, memory, gasLeft, stateGasLeft⟩, metadata, world⟩
  change stack = _ at operands
  subst stack
  simp only [MessageOp.step, stateGas, bind, Except.bind, Devm.popToNat_def,
    Devm.popToAdr_def, Devm.pop_def, Prod.mapFst, Devm.stack, Devm.setMach,
    Functor.mapRev, Except.map_ok, Prod.map, id_eq] at spawn
  let d : Devm := ⟨⟨rest, memory, gasLeft, stateGasLeft⟩, metadata, world⟩
  let accessed : Devm := match sevm.benvStat.rules.access with
    | .eip2929 => addAccessedAddress d t.toAddress
    | .flat _ => d
  have directAccessed :
      sevm.benvStat.rules.delegatedCodeAddress (accessed.getCode t.toAddress) = none := by
    dsimp only [accessed, d]
    cases sevm.benvStat.rules.access <;> exact direct
  have route := accessDelegation_direct directAccessed
  dsimp only [accessed, d] at route
  cases schedule : sevm.benvStat.rules.access <;> simp only [schedule] at route spawn
  all_goals
    rw [route] at spawn
    simp only [Nat.add_zero] at spawn
    split at spawn
    · simp only [MessageOp.Outcome.ofExcept, reduceCtorEq] at spawn
    · simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at spawn
      exact genericCall_native_not_run active spawn entered

end Jaune
