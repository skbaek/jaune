import Jaune.MessageCall.Top

/-!
# Canonicality through the four-part message call

Every state the four parts hand on is canonical when the state they start from is: `step` (a
port of `Execution`'s canonical family over the new `Step`, whose spawn carries a `Frame`),
`enter`, `settle`, `resume`, the driver, `exec` and the top-level frame. The transaction layer
reads `Frame.runTop_canonical`, so the block transition's checked snapshot keeps its proof.
-/

namespace Jaune

open Jaune

/-- A frame's checkpoint world and its block's original state are canonical. -/
def Frame.Canonical (f : Frame) : Prop :=
  World.Canonical f.checkpoint.world ∧ BenvStat.Canonical f.message.context.block

/-- A spawned frame over a canonical saved caller and the caller's block is canonical. -/
theorem Frame.canonical_mk {m : Message} {d : Devm} (hd : d.Canonical)
    (hb : BenvStat.Canonical m.context.block) : Frame.Canonical ⟨m, Frame.State.ofDevm d⟩ :=
  ⟨hd, hb⟩

/-- What one extended step must preserve. The spawn arm carries only the
frame: `Resume.run_canonical` shows the parent machine is not needed. -/
def MessageOp.Outcome.Canonical : MessageOp.Outcome → Prop
  | .done ex => Execution.Canonical ex
  | .spawn child _ => child.Canonical

/-- What one step must preserve. -/
def Step.Canonical : Step → Prop
  | .halt ex => Execution.Canonical ex
  | .next _ devm => devm.Canonical
  | .spawn child _ _ => child.Canonical

theorem MessageOp.Outcome.ofExcept_canonical {x} (hx : x.CanonicalOn MessageOp.Outcome.Canonical) :
    (MessageOp.Outcome.ofExcept x).Canonical := by
  cases x with
  | error e => exact hx
  | ok s => exact hx

theorem Step.ofExecution_canonical (pc : Nat) {x}
    (hx : Execution.Canonical x) : (Step.ofExecution pc x).Canonical := by
  cases x with
  | error e => exact hx
  | ok devm => exact hx

theorem Step.ofJump_canonical {x}
    (hx : x.CanonicalOn (fun a => a.2.Canonical)) :
    (Step.ofJump x).Canonical := by
  cases x with
  | error e => exact hx
  | ok a => exact hx

theorem MessageOp.Outcome.toStep_canonical (pc : Nat) {s : MessageOp.Outcome} (hs : s.Canonical) :
    (MessageOp.Outcome.toStep pc s).Canonical := by
  cases s with
  | done ex => exact Step.ofExecution_canonical pc hs
  | spawn child pending => exact hs

/-- The CREATE-family step: the only world change on the parent's side is the
sender nonce increment, through its named mutator; the child frame is built
over the parent's world and the frame's original state. -/
theorem genericCreate.step_canonical {sevm : Sevm} {devm : Devm}
    (hs : sevm.Canonical) (hd : devm.Canonical) (endowment : U256)
    (newAddress : Address) (memoryIndex memorySize : Nat) :
    (genericCreate.step sevm devm endowment newAddress memoryIndex
      memorySize).Canonical := by
  unfold genericCreate.step
  refine MessageOp.Outcome.ofExcept_canonical ?_
  refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd) fun _ _ => ?_
  refine Except.CanonicalOn.bind
    (Except.canonicalOn_assert (by exact hd)) fun _ _ => ?_
  dsimp only
  split
  · refine Except.CanonicalOn.bind
      (liftMachExecution_canonical (by exact hd)) fun d hd1 => ?_
    exact hd1
  · split
    · refine Except.CanonicalOn.bind
        (liftMachExecution_canonical
          (by exact Devm.Canonical.of_world_eq (Devm.Canonical.incrNonce hd _) rfl))
        fun d hd1 => ?_
      exact hd1
    · refine Except.canonicalOn_ok ?_
      exact Frame.canonical_mk
        (by exact Devm.Canonical.of_world_eq (Devm.Canonical.incrNonce hd _) rfl) hs

/-- The CALL-family step never changes the parent world: it either refunds
the stipend at depth zero or spawns the child frame. -/
theorem genericCall.step_canonical {sevm : Sevm} {devm : Devm}
    (hs : sevm.Canonical) (hd : devm.Canonical) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) :
    (genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles).Canonical := by
  unfold genericCall.step
  dsimp only
  split
  · refine MessageOp.Outcome.ofExcept_canonical ?_
    refine Except.CanonicalOn.bind
      (liftMachExecution_canonical (by exact hd)) fun d hd1 => ?_
    exact hd1
  · exact Frame.canonical_mk (by exact hd) hs

theorem genericCallAmsterdam.step_canonical {sevm : Sevm} {state : StateGasRules}
    {devm : Devm} (hs : sevm.Canonical) (hd : devm.Canonical)
    (gas reservoir : Nat) (value : U256) (caller target codeAddress : Address)
    (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat) (code : ByteArray)
    (disablePrecompiles newAccountCharged insufficientBalance : Bool) :
    (genericCallAmsterdam.step sevm state devm gas reservoir value caller target
      codeAddress shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles newAccountCharged insufficientBalance).Canonical := by
  unfold genericCallAmsterdam.step
  dsimp only
  split
  · refine MessageOp.Outcome.ofExcept_canonical ?_
    have hp :
        (if newAccountCharged = true then
            (devm.withReturnData []).restoreChildGas gas reservoir |>
              Devm.creditStateGasRefund state.newAccount
          else (devm.withReturnData []).restoreChildGas gas reservoir).Canonical := by
      split
      · exact Devm.Canonical.of_world_eq hd rfl
      · exact Devm.Canonical.of_world_eq hd rfl
    refine Except.CanonicalOn.bind
      (liftMachExecution_canonical hp) fun d hd1 => ?_
    exact hd1
  · exact Frame.canonical_mk (Devm.Canonical.of_world_eq hd rfl) hs

theorem genericCreateAmsterdam.step_canonical {sevm : Sevm} {state : StateGasRules}
    {devm : Devm} (hs : sevm.Canonical) (hd : devm.Canonical)
    (endowment : U256) (newAddress : Address) (memoryIndex memorySize : Nat) :
    (genericCreateAmsterdam.step sevm state devm endowment newAddress memoryIndex
      memorySize).Canonical := by
  unfold genericCreateAmsterdam.step
  refine MessageOp.Outcome.ofExcept_canonical ?_
  dsimp only
  split
  · refine Except.CanonicalOn.bind
      (liftMachExecution_canonical (Devm.Canonical.of_world_eq hd rfl)) fun d hd1 => ?_
    exact Except.canonicalOn_ok hd1
  · split
    · refine Except.CanonicalOn.bind
        (liftMachExecution_canonical (Devm.Canonical.of_world_eq hd rfl))
        fun d hd1 => ?_
      split
      · refine Except.CanonicalOn.bind
          (liftMachExecution_canonical
            (Devm.Canonical.of_world_eq (Devm.Canonical.incrNonce hd1 _) rfl))
          fun d2 hd2 => ?_
        exact Except.canonicalOn_ok hd2
      · exact Except.canonicalOn_ok <| Frame.canonical_mk
          (Devm.Canonical.of_world_eq (Devm.Canonical.incrNonce hd1 _) rfl) hs
    · refine Except.CanonicalOn.bind
        (Except.canonicalOn_ok (Devm.Canonical.of_world_eq hd rfl))
        fun d hd1 => ?_
      split
      · refine Except.CanonicalOn.bind
          (liftMachExecution_canonical
            (Devm.Canonical.of_world_eq (Devm.Canonical.incrNonce hd1 _) rfl))
          fun d2 hd2 => ?_
        exact Except.canonicalOn_ok hd2
      · exact Except.canonicalOn_ok <| Frame.canonical_mk
          (Devm.Canonical.of_world_eq (Devm.Canonical.incrNonce hd1 _) rfl) hs

theorem MessageOp.step_canonical {sevm : Sevm} {devm : Devm}
    (hs : sevm.Canonical) (hd : devm.Canonical) (x : MessageOp) :
    (MessageOp.step sevm devm x).Canonical := by
  cases x <;> simp only [MessageOp.step]
  case create =>
    split
    · refine MessageOp.Outcome.ofExcept_canonical ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
      refine Except.CanonicalOn.bind (liftMachExecution_canonical hc) fun d hd1 => ?_
      exact Except.canonicalOn_ok
        (genericCreate.step_canonical hs (by exact hd1) _ _ _ _)
    · refine MessageOp.Outcome.ofExcept_canonical ?_
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd) fun _ _ => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
      refine Except.CanonicalOn.bind (liftMachExecution_canonical hc) fun d hd1 => ?_
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd1) fun _ _ => ?_
      apply Except.canonicalOn_ok
      apply genericCreateAmsterdam.step_canonical
      · exact hs
      · exact Devm.Canonical.of_world_eq hd1 rfl
  case create2 =>
    split
    · split
      · refine MessageOp.Outcome.ofExcept_canonical ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun e he => ?_
        refine Except.CanonicalOn.bind (liftMachExecution_canonical he)
          fun d hd1 => ?_
        exact Except.canonicalOn_ok
          (genericCreate.step_canonical hs (by exact hd1) _ _ _ _)
      · refine MessageOp.Outcome.ofExcept_canonical ?_
        refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd)
          fun _ _ => ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun e he => ?_
        refine Except.CanonicalOn.bind (liftMachExecution_canonical he)
          fun d hd1 => ?_
        refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd1)
          fun _ _ => ?_
        apply Except.canonicalOn_ok
        apply genericCreateAmsterdam.step_canonical
        · exact hs
        · exact Devm.Canonical.of_world_eq hd1 rfl
    · -- Gate off: the undefined-opcode error keeps the machine.
      refine MessageOp.Outcome.ofExcept_canonical ?_
      exact hd
  case call =>
    split
    · refine MessageOp.Outcome.ofExcept_canonical ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun d hd1 => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd1) fun e he => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn he) fun f hf => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hf) fun g hg => ?_
      refine Except.CanonicalOn.bind
        (liftMachExecution_canonical
          (ForkRules.accessDelegation_canonical
            (rules := sevm.benvStat.rules)
            (devm := match sevm.benvStat.rules.access with
              | .eip2929 => addAccessedAddress g.2 b.1
              | .flat _ => g.2)
            (by split <;> exact hg) _))
        fun d2 hd2 => ?_
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd2) fun _ _ => ?_
      split
      · refine Except.CanonicalOn.bind
          (liftMachExecution_canonical (by exact hd2)) fun d3 hd3 => ?_
        exact hd3
      · exact Except.canonicalOn_ok
          (genericCall.step_canonical hs (by exact hd2)
            _ _ _ _ _ _ _ _ _ _ _ _ _)
    · refine MessageOp.Outcome.ofExcept_canonical ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun d hd1 => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd1) fun e he => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn he) fun f hf => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hf) fun g hg => ?_
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hg) fun _ _ => ?_
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hg) fun _ _ => ?_
      have hbase : (addAccessedAddress g.2 b.1).Canonical :=
        Devm.Canonical.of_world_eq hg rfl
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hbase) fun _ _ => ?_
      have haccess := completeDelegationAccess_canonical
        (show (Devm.balReadAccount sevm.benvStat.rules
            (sevm.benvStat.rules.delegationCost (addAccessedAddress g.2 b.1) b.1).2.1
            (Devm.balReadAccount sevm.benvStat.rules b.1 (addAccessedAddress g.2 b.1))).Canonical
          from hbase)
        (sevm.benvStat.rules.delegationCost
          (addAccessedAddress g.2 b.1) b.1).1
        (sevm.benvStat.rules.delegationCost
          (addAccessedAddress g.2 b.1) b.1).2.1
      refine Except.CanonicalOn.bind (liftMachExecution_canonical haccess) fun d2 hd2 => ?_
      split
      · refine Except.CanonicalOn.bind (liftMachExecution_canonical hd2) fun d3 hd3 => ?_
        refine Except.CanonicalOn.bind (liftMachExecution_canonical hd3) fun d4 hd4 => ?_
        apply Except.canonicalOn_ok
        apply genericCallAmsterdam.step_canonical
        · exact hs
        · exact Devm.Canonical.of_world_eq hd4 rfl
      · refine Except.CanonicalOn.bind (Except.canonicalOn_ok hd2) fun d3 hd3 => ?_
        refine Except.CanonicalOn.bind (liftMachExecution_canonical hd3) fun d4 hd4 => ?_
        apply Except.canonicalOn_ok
        apply genericCallAmsterdam.step_canonical
        · exact hs
        · exact Devm.Canonical.of_world_eq hd4 rfl
  case callcode =>
    split
    · refine MessageOp.Outcome.ofExcept_canonical ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun d hd1 => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd1) fun e he => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn he) fun f hf => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hf) fun g hg => ?_
      refine Except.CanonicalOn.bind
        (liftMachExecution_canonical
          (ForkRules.accessDelegation_canonical
            (rules := sevm.benvStat.rules)
            (devm := match sevm.benvStat.rules.access with
              | .eip2929 => addAccessedAddress g.2 b.1
              | .flat _ => g.2)
            (by split <;> exact hg) _))
        fun d2 hd2 => ?_
      split
      · refine Except.CanonicalOn.bind
          (liftMachExecution_canonical (by exact hd2)) fun d3 hd3 => ?_
        exact hd3
      · exact Except.canonicalOn_ok
          (genericCall.step_canonical hs (by exact hd2)
            _ _ _ _ _ _ _ _ _ _ _ _ _)
    · refine MessageOp.Outcome.ofExcept_canonical ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun d hd1 => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd1) fun e he => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn he) fun f hf => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hf) fun g hg => ?_
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hg) fun _ _ => ?_
      have hbase : (addAccessedAddress g.2 b.1).Canonical :=
        Devm.Canonical.of_world_eq hg rfl
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hbase) fun _ _ => ?_
      have haccess := completeDelegationAccess_canonical
        (show (Devm.balReadAccount sevm.benvStat.rules
            (sevm.benvStat.rules.delegationCost (addAccessedAddress g.2 b.1) b.1).2.1
            (Devm.balReadAccount sevm.benvStat.rules b.1 (addAccessedAddress g.2 b.1))).Canonical
          from hbase)
        (sevm.benvStat.rules.delegationCost
          (addAccessedAddress g.2 b.1) b.1).1
        (sevm.benvStat.rules.delegationCost
          (addAccessedAddress g.2 b.1) b.1).2.1
      refine Except.CanonicalOn.bind (liftMachExecution_canonical haccess) fun d2 hd2 => ?_
      apply Except.canonicalOn_ok
      apply genericCallAmsterdam.step_canonical
      · exact hs
      · exact Devm.Canonical.of_world_eq hd2 rfl
  case delegatecall =>
    split
    · refine MessageOp.Outcome.ofExcept_canonical ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun d hd1 => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd1) fun e he => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn he) fun f hf => ?_
      refine Except.CanonicalOn.bind
        (liftMachExecution_canonical
          (ForkRules.accessDelegation_canonical
            (rules := sevm.benvStat.rules)
            (devm := match sevm.benvStat.rules.access with
              | .eip2929 => addAccessedAddress f.2 b.1
              | .flat _ => f.2)
            (by split <;> exact hf) _))
        fun d2 hd2 => ?_
      exact Except.canonicalOn_ok
        (genericCall.step_canonical hs (by exact hd2)
          _ _ _ _ _ _ _ _ _ _ _ _ _)
    · refine MessageOp.Outcome.ofExcept_canonical ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun d hd1 => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd1) fun e he => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn he) fun f hf => ?_
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hf) fun _ _ => ?_
      have hbase : (addAccessedAddress f.2 b.1).Canonical :=
        Devm.Canonical.of_world_eq hf rfl
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hbase) fun _ _ => ?_
      have haccess := completeDelegationAccess_canonical
        (show (Devm.balReadAccount sevm.benvStat.rules
            (sevm.benvStat.rules.delegationCost (addAccessedAddress f.2 b.1) b.1).2.1
            (Devm.balReadAccount sevm.benvStat.rules b.1 (addAccessedAddress f.2 b.1))).Canonical
          from hbase)
        (sevm.benvStat.rules.delegationCost
          (addAccessedAddress f.2 b.1) b.1).1
        (sevm.benvStat.rules.delegationCost
          (addAccessedAddress f.2 b.1) b.1).2.1
      refine Except.CanonicalOn.bind (liftMachExecution_canonical haccess) fun d2 hd2 => ?_
      apply Except.canonicalOn_ok
      apply genericCallAmsterdam.step_canonical
      · exact hs
      · exact Devm.Canonical.of_world_eq hd2 rfl
  case staticcall =>
    split
    · refine MessageOp.Outcome.ofExcept_canonical ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun d hd1 => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd1) fun e he => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn he) fun f hf => ?_
      refine Except.CanonicalOn.bind
        (liftMachExecution_canonical
          (ForkRules.accessDelegation_canonical
            (rules := sevm.benvStat.rules)
            (devm := match sevm.benvStat.rules.access with
              | .eip2929 => addAccessedAddress f.2 b.1
              | .flat _ => f.2)
            (by split <;> exact hf) _))
        fun d2 hd2 => ?_
      exact Except.canonicalOn_ok
        (genericCall.step_canonical hs (by exact hd2)
          _ _ _ _ _ _ _ _ _ _ _ _ _)
    · refine MessageOp.Outcome.ofExcept_canonical ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun d hd1 => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn hd1) fun e he => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn he) fun f hf => ?_
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hf) fun _ _ => ?_
      have hbase : (addAccessedAddress f.2 b.1).Canonical :=
        Devm.Canonical.of_world_eq hf rfl
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hbase) fun _ _ => ?_
      have haccess := completeDelegationAccess_canonical
        (show (Devm.balReadAccount sevm.benvStat.rules
            (sevm.benvStat.rules.delegationCost (addAccessedAddress f.2 b.1) b.1).2.1
            (Devm.balReadAccount sevm.benvStat.rules b.1 (addAccessedAddress f.2 b.1))).Canonical
          from hbase)
        (sevm.benvStat.rules.delegationCost
          (addAccessedAddress f.2 b.1) b.1).1
        (sevm.benvStat.rules.delegationCost
          (addAccessedAddress f.2 b.1) b.1).2.1
      refine Except.CanonicalOn.bind (liftMachExecution_canonical haccess) fun d2 hd2 => ?_
      apply Except.canonicalOn_ok
      apply genericCallAmsterdam.step_canonical
      · exact hs
      · exact Devm.Canonical.of_world_eq hd2 rfl

theorem NextOp.step_canonical {evm : Evm} (h : evm.Canonical) (n : NextOp) :
    (NextOp.step evm n).Canonical := by
  cases n with
  | push xs prf =>
    simp only [NextOp.step]
    split
    · -- Gate off: the undefined-opcode error keeps the machine.
      refine Step.ofExecution_canonical _ ?_
      exact h.2
    · refine Step.ofExecution_canonical _ ?_
      exact Except.CanonicalOn.bind (liftMachExecution_canonical h.2)
        fun d hd => liftMachExecution_canonical hd
  | plain r => exact Step.ofExecution_canonical _ (PlainOp.run_canonical h.2 r)
  | message x => exact MessageOp.Outcome.toStep_canonical _ (MessageOp.step_canonical h.1 h.2 x)
  | dupn imm =>
    refine Step.ofExecution_canonical _ ?_
    split
    · refine Except.CanonicalOn.bind (liftMachExecution_canonical h.2) fun d hd => ?_
      split
      · exact hd
      · split
        · exact hd
        · exact liftMachExecution_canonical hd
    · exact h.2
  | swapn imm =>
    refine Step.ofExecution_canonical _ ?_
    split
    · refine Except.CanonicalOn.bind (liftMachExecution_canonical h.2) fun d hd => ?_
      split
      · exact hd
      · split
        · exact hd
        · exact Devm.Canonical.of_world_eq hd rfl
    · exact h.2
  | exchange imm =>
    refine Step.ofExecution_canonical _ ?_
    split
    · refine Except.CanonicalOn.bind (liftMachExecution_canonical h.2) fun d hd => ?_
      split
      · exact hd
      · split
        · exact hd
        · exact Devm.Canonical.of_world_eq hd rfl
    · exact h.2

/-- One interpreter step preserves the invariant: whatever the step decides --
halt, continue, or spawn -- every state it hands on is canonical. -/
theorem Evm.step_canonical {evm : Evm} (h : evm.Canonical) :
    (Evm.step evm).Canonical := by
  unfold Evm.step
  split
  · exact h.2
  · exact NextOp.step_canonical h _
  · exact Step.ofJump_canonical (JumpOp.run_canonicalOn h.2 _)
  · exact HaltOp.run_canonical h.2 _

/-! ### Entry, settlement, resumption and the driver -/

theorem World.Canonical.clearStorageWritesIfEmpty {w : World} (h : w.Canonical) (a : Address) :
    (w.clearStorageWritesIfEmpty a).Canonical := h

theorem World.Canonical.createSetUp {w : World} (h : w.Canonical) (a : Address) :
    (w.createSetUp a).Canonical :=
  ⟨State.Canonical.incrNonce (State.Canonical.setStor h.1 a Storage.canonical_empty) a, h.2⟩

theorem World.Canonical.subtractBalance {w w' : World} (h : w.Canonical) {a : Address} {v : U256}
    (hw : w.subtractBalance a v = some w') : w'.Canonical := by
  unfold World.subtractBalance at hw
  cases hs : w.state.subBal a v with
  | none => rw [hs] at hw; nomatch hw
  | some st =>
    rw [hs] at hw
    cases hw
    exact ⟨State.Canonical.subBal h.1 hs, h.2⟩

theorem World.Canonical.addBalance {w : World} (h : w.Canonical) (a : Address) (v : U256) :
    (w.addBalance a v).Canonical :=
  ⟨State.Canonical.addBal h.1 a v, h.2⟩

theorem Message.transfer_canonical {m : Message} {w w' : World} (h : w.Canonical)
    (hw : m.transfer w = .ok w') : w'.Canonical := by
  unfold Message.transfer at hw
  split at hw
  · split at hw
    · nomatch hw
    · rename_i w1 h1
      cases hw
      exact World.Canonical.addBalance (World.Canonical.subtractBalance h h1) _ _
  · cases hw; exact h

theorem Frame.enteredWorld_canonical {f : Frame} (hf : f.Canonical) : f.enteredWorld.Canonical := by
  unfold Frame.enteredWorld
  split
  · exact hf.1
  · exact World.Canonical.createSetUp hf.1 _

/-- What a frame result must preserve: a successful frame's world is canonical. -/
def Frame.Result.Canonical : Frame.Result → Prop
  | .success _ _ _ world _ _ => world.Canonical
  | _ => True

theorem Devm.chargeGas_world {cost : Nat} {d e : Devm} (h : Devm.chargeGas cost d = .ok e) :
    e.world = d.world := by
  unfold Devm.chargeGas at h
  split at h
  · cases h
  · cases h; rfl

theorem Devm.chargeStateGas_world {amount : Nat} {d e : Devm}
    (h : Devm.chargeStateGas amount d = .ok e) : e.world = d.world := by
  unfold Devm.chargeStateGas at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · simp only [reduceCtorEq] at h

theorem chargeDeposit_world {rules : ForkRules} {code : Bytes} {d e : Devm}
    (h : chargeDeposit rules code d = .ok e) : e.world = d.world := by
  unfold chargeDeposit at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals first
    | (simp only [reduceCtorEq] at h)
    | (rename_i hg _; cases h; exact Devm.chargeGas_world hg)
    | (rename_i hg; exact (Devm.chargeStateGas_world h).trans (Devm.chargeGas_world hg))
    | (rename_i hg; cases h; exact Devm.chargeGas_world hg)

theorem settle_canonical {f : Frame} {raw : Execution} (hraw : Execution.Canonical raw)
    {r : Frame.Result} (h : settle f raw = .ok r) : r.Canonical := by
  unfold settle at h
  dsimp only at h
  split at h
  · nomatch h
  · nomatch h
  · cases h; trivial
  · cases h; trivial
  · rename_i d
    have hd : (d.recordTouch f.message.context.block.rules true f.message.context.recipient).Canonical :=
      Devm.Canonical.of_world_eq hraw rfl
    split at h
    · cases h; exact hd
    · split at h
      · rename_i s hs
        cases h
        unfold depositCode at hs
        cases hc : chargeDeposit _ _ _ with
        | error e => rw [hc] at hs; nomatch hs
        | ok e =>
          rw [hc] at hs
          cases hs
          exact Devm.Canonical.setCode (Devm.Canonical.of_world_eq hd (chargeDeposit_world hc)) _ _
      · cases h; trivial

def Frame.Entry.Canonical : Frame.Entry → Prop
  | .run evm => evm.Canonical
  | .done (.ok r) => r.Canonical
  | .done (.error _) => True

theorem enterWith_canonical {f : Frame} (hf : f.Canonical) (start : Devm) :
    (enterWith f start).Canonical := by
  unfold enterWith
  dsimp only
  split
  · trivial
  · rename_i world hw
    have hworld := Message.transfer_canonical (Frame.enteredWorld_canonical hf) hw
    have hevm : Evm.Canonical ⟨0, f.message.sevm,
        (start.setWorld world).withCreatedAccounts f.enteredCreatedAccounts⟩ :=
      ⟨hf.2, Devm.Canonical.of_world_eq (devm := ⟨start.mach, start.meta, world⟩) hworld rfl⟩
    split
    · split
      · show Frame.Entry.Canonical (.done _)
        cases hs : settle f (executePrecompile _ _) with
        | error _ => trivial
        | ok r => exact settle_canonical (executePrecompile_canonical hevm.2 _) hs
      · exact hevm
    · exact hevm

theorem enter_canonical {f : Frame} (hf : f.Canonical) : (enter f).Canonical :=
  enterWith_canonical hf _

theorem resume_canonical {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} (hs : saved.world.Canonical) (hr : r.Canonical)
    {x : Except (ExceptionalHalt × Devm) Devm} (h : resume rules p saved r = .ok x) :
    x.CanonicalOn Devm.Canonical := by
  unfold resume at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; first | exact hs | exact hr) | (simp only [reduceCtorEq] at h)

theorem execFueled_run_canonical :
    ∀ (fuel : Nat) (evm : Evm), evm.Canonical →
      ∀ {raw : Execution}, (execFueled evm fuel).run = some raw →
        Execution.Canonical raw := by
  intro fuel
  induction fuel with
  | zero => intro evm _ raw h; nomatch h
  | succ fuel ih =>
    intro evm hevm raw h
    have hst := Evm.step_canonical hevm
    rw [execFueled] at h
    rcases hs : Evm.step evm with ex | ⟨pc, devm⟩ | ⟨child, pending, pc⟩ <;>
      rw [hs] at h hst <;> dsimp only at h
    · simp only [Fueled.ofExcept_run, Option.some.injEq] at h
      rw [← h]; exact hst
    · exact ih ⟨pc, evm.sta, devm⟩ ⟨hevm.1, hst⟩ h
    · have hent := enter_canonical hst
      have hset : ∀ res, (match enter child with
            | .done result => some result
            | .run childEvm => ((execFueled childEvm fuel).run).map (settle child)) = some (.ok res) →
          res.Canonical := by
        intro res hres
        rcases he : enter child with childEvm | result <;> rw [he] at hres hent <;>
          dsimp only at hres
        · rcases hc : (execFueled childEvm fuel).run with _ | raw2 <;> rw [hc] at hres
          · nomatch hres
          · simp only [Option.map, Option.some.injEq] at hres
            exact settle_canonical (ih childEvm hent hc) hres
        · cases hres; exact hent
      have hcp : Devm.Canonical child.checkpoint.toDevm := hst.1
      split at h
      · simp only [Fueled.exhausted_run, reduceCtorEq] at h
      · simp only [Fueled.ofExcept_run, Option.some.injEq] at h
        rw [← h]; exact hcp
      · rename_i res hres_eq
        have hres := hset res hres_eq
        split at h
        · simp only [Fueled.ofExcept_run, Option.some.injEq] at h
          rw [← h]; exact hcp
        · rename_i reason devm hr
          simp only [Fueled.ofExcept_run, Option.some.injEq] at h
          rw [← h]; exact resume_canonical hst.1 hres hr
        · rename_i devm hr
          exact ih ⟨pc, evm.sta, devm⟩ ⟨hevm.1, resume_canonical hst.1 hres hr⟩ h

theorem exec_canonical {evm : Evm} (h : evm.Canonical) : Execution.Canonical (exec evm) := by
  unfold exec
  cases hr : (execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run with
  | none => exact h.2
  | some raw => exact execFueled_run_canonical _ evm h hr

/-- A top-level frame's result leaves a canonical world. -/
theorem Frame.runTop_canonical {f : Frame} (hf : f.Canonical) {r : Frame.Result}
    (h : Frame.runTop f = .ok r) : (f.worldAfter r).Canonical := by
  have hr : r.Canonical := by
    unfold Frame.runTop at h
    have hent := enterWith_canonical hf f.checkpoint.toDevm
    split at h
    · rename_i result he
      rw [he] at hent
      subst h
      exact hent
    · rename_i evm he
      rw [he] at hent
      exact settle_canonical (exec_canonical hent) h
  unfold Frame.worldAfter
  split
  · exact hr
  · exact hf.1

theorem Frame.ofTop_canonical {msg : Msg} (h : msg.Canonical) (isCreate : Bool) :
    (Frame.ofTop msg isCreate).Canonical :=
  ⟨⟨h.1.1, h.2⟩, h.1.2⟩

theorem Frame.prepared_canonical {msg : Msg} {d : Devm} (hd : d.Canonical)
    (hm : msg.Canonical) (isCreate : Bool) :
    Frame.Canonical ⟨Message.ofLegacy msg isCreate, Frame.State.ofDevm d⟩ :=
  ⟨hd, hm.1.2⟩


end Jaune
