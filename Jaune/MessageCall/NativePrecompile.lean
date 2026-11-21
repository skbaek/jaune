import Jaune.Execution
import Jaune.MessageCall.Parts

/-!
# Enabled native STATICCALLs do not enter an interpreter child (checked frame)

Goal `jaune-shape-and-names-v1`, G2b, unit jsn-u97: the checked counterpart of the original-run
`Jaune.MessageOp.step_staticcall_not_run_of_precompile`. The conclusion concerns the actual
`Checked.MessageOp.step` spawn and `Checked.enter` equations, including native failure outcomes.
It neither constructs a call nor asserts native success.
-/

namespace Jaune

open Jaune

private theorem accessDelegation_direct {rules : ForkRules} {s : Frame.State} {target : Address}
    (direct : rules.delegatedCodeAddress (s.code target) = none) :
    ForkRules.accessDelegation rules s target = ⟨false, target, s.code target, 0, s⟩ := by
  unfold ForkRules.accessDelegation
  cases enabled : rules.delegationEnabled with
  | false => rfl
  | true =>
      have nodeleg : getDelegatedCodeAddress (s.code target) = none :=
        (ForkRules.delegatedCodeAddress_enabled enabled _).symm.trans direct
      simp only [↓reduceIte, GasSchedule.accessDelegation, nodeleg]

private theorem prepareCall_native_not_run
    {ctx : CallContext} {s : Frame.State} {target : Address} {gas ii isz oi osz : Nat}
    {code : ByteArray} {child : Frame} {pending : Pending} {c : Frame.Running}
    (active : decide (ctx.block.rules.isPrecompile target) = true)
    (spawn : prepareCall.step ctx s gas 0 ctx.recipient target target true true
      ii isz oi osz code false = .spawn child pending)
    (entered : enter child = .run c) : False := by
  unfold prepareCall.step at spawn
  split at spawn
  · simp only [bind, Except.bind, pure, Except.pure] at spawn
    repeat' split at spawn
    all_goals simp only [MessageOp.Outcome.ofExcept, reduceCtorEq] at spawn
  · simp only [MessageOp.Outcome.spawn.injEq] at spawn
    obtain ⟨rfl, -⟩ := spawn
    simp only [enter, enterWith, callMessage, Bool.not_false, Bool.true_and] at entered
    split at entered
    · cases entered
    · rename_i h
      simp only [of_decide_eq_true active, decide_true, ↓reduceIte, reduceCtorEq] at entered

/-- The six-operand STATICCALL to an enabled, effectively direct native precompile cannot enter
an interpreter child, over `Checked.MessageOp.step` and `Checked.enter`. The checked counterpart
of `Jaune.MessageOp.step_staticcall_not_run_of_precompile`. -/
theorem MessageOp.step_staticcall_not_run_of_precompile
    {ctx : CallContext} {pre : Frame.State} {child : Frame} {pending : Pending}
    {c : Frame.Running} {g t ii size oi outSize : U256} {rest : List U256}
    (operands : pre.stack = g :: t :: ii :: size :: oi :: outSize :: rest)
    (stateGas : ctx.block.rules.stateGas = none)
    (active : decide (ctx.block.rules.isPrecompile t.toAddress) = true)
    (direct : ctx.block.rules.delegatedCodeAddress (pre.code t.toAddress) = none)
    (spawn : MessageOp.step ctx pre .staticcall = .spawn child pending)
    (entered : enter child = .run c) : False := by
  rcases pre with ⟨⟨stack, memory, gasLeft, stateGasMeter, returnData⟩, world, substate, trail⟩
  change stack = _ at operands
  subst stack
  simp only [MessageOp.step, stateGas, bind, Except.bind, Frame.State.pop, Frame.State.popToNat,
    Frame.State.popToAddress, Frame.State.liftMachineValue, Machine.popToNat,
    Machine.popToAddress, Machine.pop, Frame.State.withMachine] at spawn
  let d : Frame.State :=
    ⟨⟨rest, memory, gasLeft, stateGasMeter, returnData⟩, world, substate, trail⟩
  let accessed : Frame.State := match ctx.block.rules.access with
    | .eip2929 => d.addAccessedAddress t.toAddress
    | .flat _ => d
  have directAccessed :
      ctx.block.rules.delegatedCodeAddress (accessed.code t.toAddress) = none := by
    dsimp only [accessed, d]
    cases ctx.block.rules.access <;> exact direct
  have route := accessDelegation_direct directAccessed
  dsimp only [accessed, d] at route
  cases schedule : ctx.block.rules.access <;> simp only [schedule] at route spawn
  all_goals
    rw [route] at spawn
    simp only [Nat.add_zero] at spawn
    split at spawn
    · simp only [MessageOp.Outcome.ofExcept, reduceCtorEq] at spawn
    · simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at spawn
      exact prepareCall_native_not_run active spawn entered

end Jaune
