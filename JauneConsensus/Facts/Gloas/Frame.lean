import JauneConsensus.Facts.Gloas.Step

/-!
# The builder frame of Gloas epoch steps (goal `eip8282-gloas-cross-layer-v1`, U3)

`BuilderFrame s s'`: the builder registry and the two builder queues are unchanged. Validator-side
steps keep it; the EIP-8282 builder rows (B1 to B7) start from it. Each lemma is a run of the
relation-parametric generator (`Step.lean`) at `builderFrame`, with the leaf lemmas registered
below as `gstep_of` rules.
-/

namespace JauneConsensus.Facts.Gloas

open JauneConsensus JauneConsensus.Facts

variable {P : Preset}

/-- The builder registry and the builder queues are unchanged. -/
abbrev BuilderFrame (s s' : JauneConsensus.Gloas.BeaconState P) : Prop :=
  s'.builders = s.builders ∧ s'.builder_pending_payments = s.builder_pending_payments ∧
    s'.builder_pending_withdrawals = s.builder_pending_withdrawals

/-- `BuilderFrame` as a step relation. -/
@[reducible] def builderFrame : StepRel (JauneConsensus.Gloas.BeaconState P) where
  R := BuilderFrame
  refl _ := ⟨rfl, rfl, rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

/-- The generator's `dsimp` unfolds `builderFrame.R` to `BuilderFrame`, from which the relation
cannot be inferred: name it. -/
macro_rules
  | `(tactic| gstep_rebase $h) =>
    `(tactic| refine StepRel.ok_rebase builderFrame (by gstep_of $h) ?_)

/-- A record update that leaves the three builder fields alone. -/
macro_rules | `(tactic| gstep_close) => `(tactic| exact ⟨rfl, rfl, rfl⟩)

theorem increaseBalance_builderFrame (s : JauneConsensus.Gloas.BeaconState P)
    (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.increaseBalance s i d) (builderFrame.R s) := by
  unfold JauneConsensus.Gloas.increaseBalance; gvcg

theorem decreaseBalance_builderFrame (s : JauneConsensus.Gloas.BeaconState P)
    (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.decreaseBalance s i d) (builderFrame.R s) := by
  unfold JauneConsensus.Gloas.decreaseBalance; gvcg

macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (increaseBalance_builderFrame _ _ _) $h; exact hh))
macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (decreaseBalance_builderFrame _ _ _) $h; exact hh))

theorem computeExitEpochAndUpdateChurn_builderFrame (cfg : Config)
    (s : JauneConsensus.Gloas.BeaconState P) (b : Gwei) :
    Ok (JauneConsensus.Gloas.computeExitEpochAndUpdateChurn cfg s b)
      (fun p => builderFrame.R s p.1) := by
  unfold JauneConsensus.Gloas.computeExitEpochAndUpdateChurn; gvcg

macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (computeExitEpochAndUpdateChurn_builderFrame _ _ _) $h; exact hh))

theorem initiateValidatorExit_builderFrame (cfg : Config)
    (s : JauneConsensus.Gloas.BeaconState P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.initiateValidatorExit cfg s i) (builderFrame.R s) := by
  unfold JauneConsensus.Gloas.initiateValidatorExit; gvcg

macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (initiateValidatorExit_builderFrame _ _ _) $h; exact hh))

/-- **Pilot.** `process_effective_balance_updates` keeps the builder registry and queues. -/
theorem processEffectiveBalanceUpdates_builderFrame (cfg : Config)
    (s : JauneConsensus.Gloas.BeaconState P) :
    Ok (JauneConsensus.Gloas.processEffectiveBalanceUpdates cfg s) (builderFrame.R s) := by
  unfold JauneConsensus.Gloas.processEffectiveBalanceUpdates; gvcg

/-- `process_registry_updates` keeps the builder registry and queues (its ejections go through
the Gloas `initiate_validator_exit`). -/
theorem processRegistryUpdates_builderFrame (cfg : Config)
    (s : JauneConsensus.Gloas.BeaconState P) :
    Ok (JauneConsensus.Gloas.processRegistryUpdates cfg s) (builderFrame.R s) := by
  unfold JauneConsensus.Gloas.processRegistryUpdates; gvcg

end JauneConsensus.Facts.Gloas
