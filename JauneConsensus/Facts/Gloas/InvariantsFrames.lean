import JauneConsensus.Facts.Gloas.Invariants
import JauneConsensus.Facts.Gloas.BuilderTraces

/-!
# Frames of the Gloas block and slot steps for the G3 invariants (goal `eip8282-gloas-cross-layer-v1`, G3a)

`CoreFrame s s'`: the builders, `L`, `latest_block_hash`, the header slot, the slot and
`next_withdrawal_builder_index` are unchanged (the builder queues may change). Every step of a
Gloas block keeps it except the parent payload's builder requests and suffix, the header, the
withdrawals and the bid; the generator proves it for each, with the leaf rules registered locally.
The block and the slot loop are then split into their phases (`processBlock_phases`,
`processParentExecutionPayload_cases`, `processEpoch_phases`).
-/

namespace JauneConsensus.Facts.Gloas.Invariant

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-- The builders, `L`, `latest_block_hash`, the header slot, the slot and the builder sweep index
are unchanged. -/
def CoreFrame (s s' : GloasState P) : Prop :=
  s'.builders = s.builders ∧
    s'.latest_execution_payload_bid = s.latest_execution_payload_bid ∧
    s'.latest_block_hash = s.latest_block_hash ∧
    s'.latest_block_header.slot = s.latest_block_header.slot ∧ s'.slot = s.slot ∧
    s'.next_withdrawal_builder_index = s.next_withdrawal_builder_index

/-- `CoreFrame` as a step relation. -/
def coreFrame : StepRelation (GloasState P) where
  relation := CoreFrame
  refl _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.1.trans h₁.2.2.2.2.1,
    h₂.2.2.2.2.2.trans h₁.2.2.2.2.2⟩

theorem coreFrame_of_invariant {s s' : GloasState P} (h : InvariantFrame s s') : CoreFrame s s' :=
  ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

section Core

local macro_rules
  | `(tactic| gstep_close) =>
    `(tactic| exact (show CoreFrame _ _ from ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (increaseBalance_invariantFrame _ _ _) $h; exact coreFrame_of_invariant hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (decreaseBalance_invariantFrame _ _ _) $h; exact coreFrame_of_invariant hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (initiateValidatorExit_invariantFrame _ _ _) $h; exact coreFrame_of_invariant hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (computeExitEpochAndUpdateChurn_invariantFrame _ _ _) $h; exact coreFrame_of_invariant hh))

theorem queueExcessActiveBalance_core (s : GloasState P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.queueExcessActiveBalance s i) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.queueExcessActiveBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (queueExcessActiveBalance_core _ _) $h; exact hh))

theorem switchToCompoundingValidator_core (s : GloasState P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.switchToCompoundingValidator s i) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.switchToCompoundingValidator; gvcg
  all_goals exact StepRelation.ok_rebase coreFrame ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (queueExcessActiveBalance_core _ _)

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (switchToCompoundingValidator_core _ _) $h; exact hh))

theorem computeConsolidationEpochAndUpdateChurn_core (cfg : Config) (s : GloasState P) (b : Gwei) :
    Ok (JauneConsensus.Gloas.computeConsolidationEpochAndUpdateChurn cfg s b)
      (fun p => coreFrame.relation s p.1) := by
  unfold JauneConsensus.Gloas.computeConsolidationEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (computeConsolidationEpochAndUpdateChurn_core _ _ _) $h; exact hh))

theorem processWithdrawalRequest_core (cfg : Config) (s : GloasState P) (wr : WithdrawalRequest) :
    Ok (JauneConsensus.Gloas.processWithdrawalRequest cfg s wr) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.processWithdrawalRequest; gvcg
  all_goals exact fun x hx => coreFrame_of_invariant (initiateValidatorExit_invariantFrame _ _ _ x hx)

theorem processConsolidationRequest_core (cfg : Config) (s : GloasState P) (cr : ConsolidationRequest) :
    Ok (JauneConsensus.Gloas.processConsolidationRequest cfg s cr) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.processConsolidationRequest; gvcg
  all_goals exact switchToCompoundingValidator_core _ _

theorem settleBuilderPayment_core (s : GloasState P) (i : U64) :
    Ok (JauneConsensus.Gloas.settleBuilderPayment s i) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.settleBuilderPayment; gvcg
  all_goals first
    | exact (show CoreFrame _ _ from ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    | (split <;> exact (show CoreFrame _ _ from ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processWithdrawalRequest_core _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processConsolidationRequest_core _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (settleBuilderPayment_core _ _) $h; exact hh))

/-- A loop whose initial state is a record update of the step's state. -/
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine coreFrame.trans ?_ (StepRelation.forIn_array_relation coreFrame id ?_ _ _ $h)
               · exact (show CoreFrame _ _ from ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
               · intro _ _; gvcg))

/-- The parent payload up to the builder loops (`applyParentPrefix`): the settlement and the
validator requests keep `CoreFrame`. -/
theorem applyParentPrefix_core (ctx : Context) (s : GloasState P)
    (r : JauneConsensus.Gloas.ExecutionRequests) :
    Ok (JauneConsensus.Gloas.applyParentPrefix ctx s r) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.applyParentPrefix; gvcg

theorem slashValidator_core (cfg : Config) (s : GloasState P) (i : ValidatorIndex)
    (wb : Option ValidatorIndex) :
    Ok (JauneConsensus.Gloas.slashValidator cfg s i wb) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.slashValidator; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (slashValidator_core _ _ _ _) $h; exact hh))

theorem processProposerSlashing_core (ctx : Context) (s : GloasState P) (ps : ProposerSlashing) :
    Ok (JauneConsensus.Gloas.processProposerSlashing ctx s ps) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.processProposerSlashing; gvcg
  all_goals exact slashValidator_core _ _ _ _

theorem processAttesterSlashing_core (ctx : Context) (s : GloasState P)
    (as : JauneConsensus.Gloas.AttesterSlashing) :
    Ok (JauneConsensus.Gloas.processAttesterSlashing ctx s as) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.processAttesterSlashing; gvcg

theorem processVoluntaryExit_core (ctx : Context) (s : GloasState P) (sve : SignedVoluntaryExit) :
    Ok (JauneConsensus.Gloas.processVoluntaryExit ctx s sve) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.processVoluntaryExit; gvcg
  all_goals exact fun x hx => coreFrame_of_invariant (initiateValidatorExit_invariantFrame _ _ _ x hx)

theorem processBlsToExecutionChange_core (ctx : Context) (s : GloasState P)
    (sac : SignedBLSToExecutionChange) :
    Ok (JauneConsensus.Gloas.processBlsToExecutionChange ctx s sac) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.processBlsToExecutionChange; gvcg

theorem processPayloadAttestation_core (ctx : Context) (s : GloasState P)
    (pa : JauneConsensus.Gloas.PayloadAttestation P) :
    Ok (JauneConsensus.Gloas.processPayloadAttestation ctx s pa) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.processPayloadAttestation; gvcg

section Attestation

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (increaseBalance_invariantFrame _ _ _) $h; exact (coreFrame.trans (by split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (coreFrame_of_invariant hh))))

set_option maxHeartbeats 2000000 in
theorem processAttestation_core (ctx : Context) (s : GloasState P)
    (a : JauneConsensus.Gloas.Attestation P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processAttestation ctx s a ps) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.processAttestation; gvcg

end Attestation

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processProposerSlashing_core _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processAttesterSlashing_core _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processAttestation_core _ _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processVoluntaryExit_core _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processBlsToExecutionChange_core _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processPayloadAttestation_core _ _ _) $h; exact hh))

theorem processOperations_core (ctx : Context) (s : GloasState P)
    (body : JauneConsensus.Gloas.BeaconBlockBody P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processOperations ctx s body ps) (coreFrame.relation s) := by
  unfold JauneConsensus.Gloas.processOperations; gvcg

end Core

end JauneConsensus.Facts.Gloas.Invariant
