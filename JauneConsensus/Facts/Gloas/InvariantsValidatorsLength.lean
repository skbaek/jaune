import JauneConsensus.Facts.Gloas.InvariantsCover

/-!
# The validator registry's length after the withdrawals of a block (goal `eip8282-gloas-cross-layer-v1`, G3b)

G3-12's `validatorsBound` (`len(validators) ≤ 2^40`) is a run-level premise on joint states. A
block's withdrawals read the registry of an intermediate state (after the parent payload and the
header); this module shows that nothing after the withdrawals changes the registry's length (the
bid, RANDAO, eth1 data, the operations and the sync aggregate only overwrite entries), so the
bound at the block's post-state covers the state the withdrawals read (`afterWithdrawals_vlen`).
-/

namespace JauneConsensus.Facts.Gloas.Invariant

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-- The validator registry keeps its length. -/
def ValidatorsLength (s s' : GloasState P) : Prop := s'.validators.toArray.size = s.validators.toArray.size

/-- `VLen` as a step relation. -/
def validatorsLength : StepRelation (GloasState P) where
  relation := ValidatorsLength
  refl _ := rfl
  trans h₁ h₂ := h₂.trans h₁

/-- An entry of the registry overwritten. -/
theorem validatorsLength_of_set {a b : GloasState P} {vs : ProgressiveListRightSpine Validator} {i : Nat} {v : Validator}
    {site : String} (hb : b.validators = vs) (h : a.validators.set i v site = .ok vs) : ValidatorsLength a b := by
  unfold ValidatorsLength; rw [hb]; exact (progressiveList_set_ok h).1

section Generator

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show ValidatorsLength _ _ from rfl))
local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact validatorsLength_of_set rfl (by assumption))

theorem increaseBalance_validatorsLength (s : GloasState P) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.increaseBalance s i d) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.increaseBalance; gvcg

theorem decreaseBalance_validatorsLength (s : GloasState P) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.decreaseBalance s i d) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.decreaseBalance; gvcg

theorem computeExitEpochAndUpdateChurn_validatorsLength (cfg : Config) (s : GloasState P) (b : Gwei) :
    Ok (JauneConsensus.Gloas.computeExitEpochAndUpdateChurn cfg s b) (fun p => validatorsLength.relation s p.1) := by
  unfold JauneConsensus.Gloas.computeExitEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (computeExitEpochAndUpdateChurn_validatorsLength _ _ _) $h; exact hh))

theorem initiateValidatorExit_validatorsLength (cfg : Config) (s : GloasState P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.initiateValidatorExit cfg s i) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.initiateValidatorExit; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (initiateValidatorExit_validatorsLength _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (increaseBalance_validatorsLength _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (decreaseBalance_validatorsLength _ _ _) $h; exact hh))
/-- A sub-step from a state whose registry entry was just overwritten. -/
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (decreaseBalance_validatorsLength _ _ _) $h
               refine (validatorsLength).trans ?_ hh; exact validatorsLength_of_set rfl (by assumption)))

theorem slashValidator_validatorsLength (cfg : Config) (s : GloasState P) (i : ValidatorIndex)
    (wb : Option ValidatorIndex) :
    Ok (JauneConsensus.Gloas.slashValidator cfg s i wb) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.slashValidator; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (slashValidator_validatorsLength _ _ _ _) $h; exact hh))

theorem processProposerSlashing_validatorsLength (ctx : Ctx) (s : GloasState P) (ps : ProposerSlashing) :
    Ok (JauneConsensus.Gloas.processProposerSlashing ctx s ps) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.processProposerSlashing; gvcg
  all_goals exact slashValidator_validatorsLength _ _ _ _

theorem processAttesterSlashing_validatorsLength (ctx : Ctx) (s : GloasState P)
    (as : JauneConsensus.Gloas.AttesterSlashing) :
    Ok (JauneConsensus.Gloas.processAttesterSlashing ctx s as) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.processAttesterSlashing; gvcg

theorem processVoluntaryExit_validatorsLength (ctx : Ctx) (s : GloasState P) (sve : SignedVoluntaryExit) :
    Ok (JauneConsensus.Gloas.processVoluntaryExit ctx s sve) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.processVoluntaryExit; gvcg
  all_goals exact initiateValidatorExit_validatorsLength _ _ _

theorem processBlsToExecutionChange_validatorsLength (ctx : Ctx) (s : GloasState P)
    (sac : SignedBLSToExecutionChange) :
    Ok (JauneConsensus.Gloas.processBlsToExecutionChange ctx s sac) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.processBlsToExecutionChange; gvcg

theorem processPayloadAttestation_validatorsLength (ctx : Ctx) (s : GloasState P)
    (pa : JauneConsensus.Gloas.PayloadAttestation P) :
    Ok (JauneConsensus.Gloas.processPayloadAttestation ctx s pa) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.processPayloadAttestation; gvcg

section Attestation

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (increaseBalance_validatorsLength _ _ _) $h
               exact (validatorsLength).trans (by split <;> exact (show ValidatorsLength _ _ from rfl)) hh))

set_option maxHeartbeats 2000000 in
theorem processAttestation_validatorsLength (ctx : Ctx) (s : GloasState P)
    (a : JauneConsensus.Gloas.Attestation P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processAttestation ctx s a ps) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.processAttestation; gvcg

end Attestation

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processProposerSlashing_validatorsLength _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processAttesterSlashing_validatorsLength _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processAttestation_validatorsLength _ _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processVoluntaryExit_validatorsLength _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processBlsToExecutionChange_validatorsLength _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processPayloadAttestation_validatorsLength _ _ _) $h; exact hh))

theorem processOperations_validatorsLength (ctx : Ctx) (s : GloasState P)
    (body : JauneConsensus.Gloas.BeaconBlockBody P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processOperations ctx s body ps) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.processOperations; gvcg

theorem processRandao_validatorsLength (ctx : Ctx) (s : GloasState P)
    (body : JauneConsensus.Gloas.BeaconBlockBody P) :
    Ok (JauneConsensus.Gloas.processRandao ctx s body) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.processRandao; gvcg

theorem processEth1Data_validatorsLength (s : GloasState P) (body : JauneConsensus.Gloas.BeaconBlockBody P) :
    Ok (JauneConsensus.Gloas.processEth1Data s body) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.processEth1Data; gvcg

set_option maxHeartbeats 2000000 in
theorem processSyncAggregate_validatorsLength (ctx : Ctx) (s : GloasState P) (sa : SyncAggregate P) :
    Ok (JauneConsensus.Gloas.processSyncAggregate ctx s sa) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.processSyncAggregate; gvcg

set_option maxHeartbeats 1000000 in
theorem processExecutionPayloadBid_validatorsLength (ctx : Ctx) (s : GloasState P)
    (sb : JauneConsensus.Gloas.SignedExecutionPayloadBid) :
    Ok (JauneConsensus.Gloas.processExecutionPayloadBid ctx s sb) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.processExecutionPayloadBid; gvcg
  all_goals
    apply ok_pure
    rename_i hlast
    cases hlast
    exact (show ValidatorsLength _ _ from rfl)

end Generator

/-- **Nothing after a block's withdrawals changes the registry's length.** -/
theorem afterWithdrawals_validatorsLength {ctx : Ctx} {s3 s4 s5 s6 s7 s' : GloasState P}
    {blk : JauneConsensus.Gloas.BeaconBlock P} {ps : Slot}
    (h4 : JauneConsensus.Gloas.processExecutionPayloadBid ctx s3
      blk.body.signed_execution_payload_bid = .ok s4)
    (h5 : JauneConsensus.Gloas.processRandao ctx s4 blk.body = .ok s5)
    (h6 : JauneConsensus.Gloas.processEth1Data s5 blk.body = .ok s6)
    (h7 : JauneConsensus.Gloas.processOperations ctx s6 blk.body ps = .ok s7)
    (h8 : JauneConsensus.Gloas.processSyncAggregate ctx s7 blk.body.sync_aggregate = .ok s') :
    s'.validators.toArray.size = s3.validators.toArray.size :=
  validatorsLength.trans (processExecutionPayloadBid_validatorsLength _ _ _ _ h4)
    (validatorsLength.trans (processRandao_validatorsLength _ _ _ _ h5)
      (validatorsLength.trans (processEth1Data_validatorsLength _ _ _ h6)
        (validatorsLength.trans (processOperations_validatorsLength _ _ _ _ _ h7) (processSyncAggregate_validatorsLength _ _ _ _ h8))))

end JauneConsensus.Facts.Gloas.Invariant
