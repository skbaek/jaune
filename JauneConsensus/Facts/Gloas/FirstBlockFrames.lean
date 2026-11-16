import JauneConsensus.Facts.Gloas.StepBalanceFlow

/-!
# Frames of the first Gloas block and of `payload_expected_withdrawals` (goal `eip8282-gloas-cross-layer-v1`, G3c)

* **`payload_expected_withdrawals`** (G3-11's ledger form, B5(iv)): no Gloas step writes it but
  `process_withdrawals` past its early return. `PewEq` is its frame, proved by the generator of
  `Step.lean` for every epoch step (`processSlots_pew`) and for every block phase after the
  withdrawals. `processBlock_payloadExpectedWithdrawals`: after an EMPTY settlement
  (`parentFull = false`) `process_withdrawals` returns early and the field is unchanged; after a
  FULL one it is exactly the step's expected withdrawals (`stepWithdrawals`).
  `GStepView.payloadExpectedWithdrawals` lifts this to a Gloas joint step (the slots included).
* **The first Gloas block** (O-a's remainder, `crossing_builders_eq`): from `upgrade_to_gloas`'s
  state, through the crossing's slots and the first block with empty parent requests, the builder
  registry is exactly `upgrade_to_gloas`'s, balances included, and `builder_pending_withdrawals`
  stays empty. The slots append nothing (every payment is empty and the quorum is positive), the
  settlement appends nothing (empty payments, `L.value = 0`), and the withdrawals debit no
  builder: there is no pending builder withdrawal, the validator phases route to validators only
  (`validatorsBound`), and the sweep finds no builder withdrawable (all are at
  `FAR_FUTURE_EPOCH`, `2 ≤ SLOTS_PER_EPOCH`).
-/

namespace JauneConsensus.Facts.Gloas

open Jaune JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas.Invariant

variable {P : Preset}

/-! ## The frame of `payload_expected_withdrawals` -/

/-- `payload_expected_withdrawals` is unchanged. -/
def PayloadExpectedWithdrawalsEq (s s' : GloasState P) : Prop :=
  s'.payload_expected_withdrawals = s.payload_expected_withdrawals

/-- `PewEq` as a step relation. -/
def payloadExpectedWithdrawalsEq : StepRelation (GloasState P) where
  relation := PayloadExpectedWithdrawalsEq
  refl _ := rfl
  trans h₁ h₂ := Eq.trans h₂ h₁

section PewGen

local macro_rules
  | `(tactic| gstep_close) =>
    `(tactic| exact (show PayloadExpectedWithdrawalsEq _ _ from rfl))

theorem increaseBalance_payloadExpectedWithdrawals (s : GloasState P) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.increaseBalance s i d) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.increaseBalance; gvcg

theorem decreaseBalance_payloadExpectedWithdrawals (s : GloasState P) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.decreaseBalance s i d) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.decreaseBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (increaseBalance_payloadExpectedWithdrawals _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (decreaseBalance_payloadExpectedWithdrawals _ _ _) $h; exact hh))

theorem computeExitEpochAndUpdateChurn_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) (b : Gwei) :
    Ok (JauneConsensus.Gloas.computeExitEpochAndUpdateChurn cfg s b)
      (fun p => payloadExpectedWithdrawalsEq.relation s p.1) := by
  unfold JauneConsensus.Gloas.computeExitEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (computeExitEpochAndUpdateChurn_payloadExpectedWithdrawals _ _ _) $h; exact hh))

theorem initiateValidatorExit_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.initiateValidatorExit cfg s i) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.initiateValidatorExit; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (initiateValidatorExit_payloadExpectedWithdrawals _ _ _) $h; exact hh))

theorem addValidatorToRegistry_payloadExpectedWithdrawals (s : GloasState P) (pk : BLSPubkey) (wc : Bytes32)
    (amount : Gwei) :
    Ok (JauneConsensus.Gloas.addValidatorToRegistry s pk wc amount) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.addValidatorToRegistry; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (addValidatorToRegistry_payloadExpectedWithdrawals _ _ _ _) $h; exact hh))

theorem applyPendingDeposit_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P) (d : PendingDeposit) :
    Ok (JauneConsensus.Gloas.applyPendingDeposit ctx s d) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.applyPendingDeposit; gvcg
  · exact addValidatorToRegistry_payloadExpectedWithdrawals _ _ _ _
  · exact increaseBalance_payloadExpectedWithdrawals _ _ _

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (applyPendingDeposit_payloadExpectedWithdrawals _ _ _) $h; exact hh))

theorem processInactivityUpdates_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processInactivityUpdates cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processInactivityUpdates; gvcg

theorem processRewardsAndPenalties_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processRewardsAndPenalties cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processRewardsAndPenalties; gvcg

theorem processRegistryUpdates_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processRegistryUpdates cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processRegistryUpdates; gvcg

theorem processSlashings_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processSlashings cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processSlashings; gvcg

theorem processEth1DataReset_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processEth1DataReset cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processEth1DataReset; gvcg

section PendingDeposits

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRelation.forIn_array_relation _ (fun x => x.2.2.2.2) ?_ _ _ $h; intro _ _; gvcg))

theorem processPendingDeposits_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processPendingDeposits ctx s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processPendingDeposits; gvcg

end PendingDeposits

theorem processPendingConsolidations_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processPendingConsolidations cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processPendingConsolidations; gvcg

theorem processEffectiveBalanceUpdates_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processEffectiveBalanceUpdates cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processEffectiveBalanceUpdates; gvcg

theorem processSlashingsReset_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processSlashingsReset cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processSlashingsReset; gvcg

theorem processRandaoMixesReset_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processRandaoMixesReset cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processRandaoMixesReset; gvcg

theorem processHistoricalSummariesUpdate_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processHistoricalSummariesUpdate cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processHistoricalSummariesUpdate; gvcg

theorem processParticipationFlagUpdates_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processParticipationFlagUpdates cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processParticipationFlagUpdates; gvcg

theorem processSyncCommitteeUpdates_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processSyncCommitteeUpdates ctx s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processSyncCommitteeUpdates; gvcg

theorem processProposerLookahead_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processProposerLookahead cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processProposerLookahead; gvcg

theorem processPtcWindow_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processPtcWindow cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processPtcWindow; gvcg

theorem processRandao_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P)
    (body : JauneConsensus.Gloas.BeaconBlockBody P) :
    Ok (JauneConsensus.Gloas.processRandao ctx s body) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processRandao; gvcg

theorem processEth1Data_payloadExpectedWithdrawals (s : GloasState P) (body : JauneConsensus.Gloas.BeaconBlockBody P) :
    Ok (JauneConsensus.Gloas.processEth1Data s body) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processEth1Data; gvcg

set_option maxHeartbeats 2000000 in
theorem processSyncAggregate_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P) (sa : SyncAggregate P) :
    Ok (JauneConsensus.Gloas.processSyncAggregate ctx s sa) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processSyncAggregate; gvcg

theorem weighJustificationAndFinalization_payloadExpectedWithdrawals (s : GloasState P) (t p c : Gwei) :
    Ok (JauneConsensus.Gloas.weighJustificationAndFinalization s t p c) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.weighJustificationAndFinalization; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (weighJustificationAndFinalization_payloadExpectedWithdrawals _ _ _ _) $h; exact hh))

theorem processJustificationAndFinalization_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processJustificationAndFinalization cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processJustificationAndFinalization; gvcg
  all_goals exact weighJustificationAndFinalization_payloadExpectedWithdrawals _ _ _ _

theorem processSlotAbstractedHashes_payloadExpectedWithdrawals (h₁ : GloasState P → Root) (h₂ : BeaconBlockHeader → Root) (s : GloasState P) :
    Ok (Invariant.processSlotAbstractedHashes h₁ h₂ s) (payloadExpectedWithdrawalsEq.relation s) := by
  intro s' h
  unfold Invariant.processSlotAbstractedHashes at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  show PayloadExpectedWithdrawalsEq _ _
  split <;> rfl

theorem processSlot_payloadExpectedWithdrawals (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processSlot s) (payloadExpectedWithdrawalsEq.relation s) := by
  rw [Invariant.processSlot_eq]; exact processSlotAbstractedHashes_payloadExpectedWithdrawals _ _ s


theorem processBuilderPendingPayments_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processBuilderPendingPayments cfg s) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processBuilderPendingPayments; gvcg

theorem updateNextWithdrawalBuilderIndex_payloadExpectedWithdrawals (s : GloasState P) (n : U64) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex s n) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex; gvcg

theorem updateNextWithdrawalValidatorIndex_payloadExpectedWithdrawals (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex s ws) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex; gvcg

theorem slashValidator_payloadExpectedWithdrawals (cfg : Config) (s : GloasState P) (i : ValidatorIndex)
    (wb : Option ValidatorIndex) :
    Ok (JauneConsensus.Gloas.slashValidator cfg s i wb) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.slashValidator; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (slashValidator_payloadExpectedWithdrawals _ _ _ _) $h; exact hh))

theorem processProposerSlashing_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P) (ps : ProposerSlashing) :
    Ok (JauneConsensus.Gloas.processProposerSlashing ctx s ps) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processProposerSlashing; gvcg
  all_goals exact slashValidator_payloadExpectedWithdrawals _ _ _ _

theorem processAttesterSlashing_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P)
    (as : JauneConsensus.Gloas.AttesterSlashing) :
    Ok (JauneConsensus.Gloas.processAttesterSlashing ctx s as) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processAttesterSlashing; gvcg

theorem processVoluntaryExit_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P) (sve : SignedVoluntaryExit) :
    Ok (JauneConsensus.Gloas.processVoluntaryExit ctx s sve) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processVoluntaryExit; gvcg
  all_goals exact initiateValidatorExit_payloadExpectedWithdrawals _ _ _

theorem processBlsToExecutionChange_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P)
    (sac : SignedBLSToExecutionChange) :
    Ok (JauneConsensus.Gloas.processBlsToExecutionChange ctx s sac) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processBlsToExecutionChange; gvcg

set_option maxHeartbeats 1000000 in
theorem processPayloadAttestation_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P)
    (pa : JauneConsensus.Gloas.PayloadAttestation P) :
    Ok (JauneConsensus.Gloas.processPayloadAttestation ctx s pa) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processPayloadAttestation; gvcg

section Attestation

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (increaseBalance_payloadExpectedWithdrawals _ _ _) $h; exact (show PayloadExpectedWithdrawalsEq _ _ from Eq.trans hh (by split <;> rfl))))

set_option maxHeartbeats 2000000 in
theorem processAttestation_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P)
    (a : JauneConsensus.Gloas.Attestation P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processAttestation ctx s a ps) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processAttestation; gvcg

end Attestation

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processProposerSlashing_payloadExpectedWithdrawals _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processAttesterSlashing_payloadExpectedWithdrawals _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processAttestation_payloadExpectedWithdrawals _ _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processVoluntaryExit_payloadExpectedWithdrawals _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processBlsToExecutionChange_payloadExpectedWithdrawals _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processPayloadAttestation_payloadExpectedWithdrawals _ _ _) $h; exact hh))

theorem processOperations_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P)
    (body : JauneConsensus.Gloas.BeaconBlockBody P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processOperations ctx s body ps) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processOperations; gvcg

section BidFrame

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (exact StepRelation.of_ok (Q := StepRelation.relation payloadExpectedWithdrawalsEq _) (by gvcg) $h))

set_option maxHeartbeats 1000000 in
theorem processExecutionPayloadBid_payloadExpectedWithdrawals (ctx : Context) (s : GloasState P)
    (sb : JauneConsensus.Gloas.SignedExecutionPayloadBid) :
    Ok (JauneConsensus.Gloas.processExecutionPayloadBid ctx s sb) (payloadExpectedWithdrawalsEq.relation s) := by
  unfold JauneConsensus.Gloas.processExecutionPayloadBid; gvcg

end BidFrame

end PewGen

/-! ## Slots -/

/-- `process_epoch` keeps `payload_expected_withdrawals`. -/
theorem processEpoch_payloadExpectedWithdrawals {ctx : Context} {s s' : GloasState P}
    (h : JauneConsensus.Gloas.processEpoch ctx s = .ok s') : PayloadExpectedWithdrawalsEq s s' := by
  unfold JauneConsensus.Gloas.processEpoch at h
  obtain ⟨x1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x6, h6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x7, h7, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x8, h8, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x9, h9, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x10, h10, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x11, h11, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x12, h12, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x13, h13, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x14, h14, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x15, h15, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x16, h16, h⟩ := bind_eq_ok_iff.mp h
  have f1 := processJustificationAndFinalization_payloadExpectedWithdrawals _ _ _ h1
  have f2 := processInactivityUpdates_payloadExpectedWithdrawals _ _ _ h2
  have f3 := processRewardsAndPenalties_payloadExpectedWithdrawals _ _ _ h3
  have f4 := processRegistryUpdates_payloadExpectedWithdrawals _ _ _ h4
  have f5 := processSlashings_payloadExpectedWithdrawals _ _ _ h5
  have f6 := processEth1DataReset_payloadExpectedWithdrawals _ _ _ h6
  have f7 := processPendingDeposits_payloadExpectedWithdrawals _ _ _ h7
  have f8 := processPendingConsolidations_payloadExpectedWithdrawals _ _ _ h8
  have f9 := processBuilderPendingPayments_payloadExpectedWithdrawals _ _ _ h9
  have f10 := processEffectiveBalanceUpdates_payloadExpectedWithdrawals _ _ _ h10
  have f11 := processSlashingsReset_payloadExpectedWithdrawals _ _ _ h11
  have f12 := processRandaoMixesReset_payloadExpectedWithdrawals _ _ _ h12
  have f13 := processHistoricalSummariesUpdate_payloadExpectedWithdrawals _ _ _ h13
  have f14 := processParticipationFlagUpdates_payloadExpectedWithdrawals _ _ _ h14
  have f15 := processSyncCommitteeUpdates_payloadExpectedWithdrawals _ _ _ h15
  have f16 := processProposerLookahead_payloadExpectedWithdrawals _ _ _ h16
  have f17 := processPtcWindow_payloadExpectedWithdrawals _ _ _ h
  exact payloadExpectedWithdrawalsEq.trans f1 (payloadExpectedWithdrawalsEq.trans f2 (payloadExpectedWithdrawalsEq.trans f3 (payloadExpectedWithdrawalsEq.trans f4 (payloadExpectedWithdrawalsEq.trans f5
    (payloadExpectedWithdrawalsEq.trans f6 (payloadExpectedWithdrawalsEq.trans f7 (payloadExpectedWithdrawalsEq.trans f8 (payloadExpectedWithdrawalsEq.trans f9 (payloadExpectedWithdrawalsEq.trans f10
    (payloadExpectedWithdrawalsEq.trans f11 (payloadExpectedWithdrawalsEq.trans f12 (payloadExpectedWithdrawalsEq.trans f13 (payloadExpectedWithdrawalsEq.trans f14 (payloadExpectedWithdrawalsEq.trans f15
    (payloadExpectedWithdrawalsEq.trans f16 f17)))))))))))))))

/-- **Gloas `process_slots` keeps `payload_expected_withdrawals`.** -/
theorem processSlots_payloadExpectedWithdrawals {ctx : Context} {s s' : GloasState P} {slot : U64}
    (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s') :
    s'.payload_expected_withdrawals = s.payload_expected_withdrawals := by
  unfold JauneConsensus.Gloas.processSlots JauneConsensus.Gloas.processSlotsWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine range_forIn_invariant (fun m : GloasState P => m.payload_expected_withdrawals =
    s.payload_expected_withdrawals) (fun a b x hb hx => ?_) hout rfl
  obtain ⟨st1, h1, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨next, hn, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨r, hr, hx⟩ := bind_eq_ok_iff.mp hx
  have f1 : st1.payload_expected_withdrawals = b.payload_expected_withdrawals :=
    processSlot_payloadExpectedWithdrawals _ _ h1
  simp only [] at hx
  split at hx
  · obtain ⟨st2, he, hx⟩ := bind_eq_ok_iff.mp hx
    cases hx
    have f2 : st2.payload_expected_withdrawals = st1.payload_expected_withdrawals :=
      processEpoch_payloadExpectedWithdrawals he
    show st2.payload_expected_withdrawals = _
    rw [f2, f1, hb]
  · cases hx
    show st1.payload_expected_withdrawals = _
    rw [f1, hb]

/-- The crossing's slots function keeps `payload_expected_withdrawals`. -/
theorem crossingSlots_payloadExpectedWithdrawals {ctx : Context} {s s' : GloasState P} {slot : U64}
    (h : crossingSlots ctx s slot = .ok s') :
    s'.payload_expected_withdrawals = s.payload_expected_withdrawals := by
  unfold crossingSlots at h
  split at h
  · cases h; rfl
  · exact processSlots_payloadExpectedWithdrawals h

/-! ## The block -/

/-- The block phases after the withdrawals keep `payload_expected_withdrawals`. -/
theorem afterWithdrawals_payloadExpectedWithdrawals {ctx : Context} {s3 s4 s5 s6 s7 s' : GloasState P}
    {blk : JauneConsensus.Gloas.BeaconBlock P} {ps : Slot}
    (h4 : JauneConsensus.Gloas.processExecutionPayloadBid ctx s3
      blk.body.signed_execution_payload_bid = .ok s4)
    (h5 : JauneConsensus.Gloas.processRandao ctx s4 blk.body = .ok s5)
    (h6 : JauneConsensus.Gloas.processEth1Data s5 blk.body = .ok s6)
    (h7 : JauneConsensus.Gloas.processOperations ctx s6 blk.body ps = .ok s7)
    (h8 : JauneConsensus.Gloas.processSyncAggregate ctx s7 blk.body.sync_aggregate = .ok s') :
    s'.payload_expected_withdrawals = s3.payload_expected_withdrawals :=
  payloadExpectedWithdrawalsEq.trans (processExecutionPayloadBid_payloadExpectedWithdrawals _ _ _ _ h4) (payloadExpectedWithdrawalsEq.trans
    (processRandao_payloadExpectedWithdrawals _ _ _ _ h5) (payloadExpectedWithdrawalsEq.trans (processEth1Data_payloadExpectedWithdrawals _ _ _ h6)
    (payloadExpectedWithdrawalsEq.trans (processOperations_payloadExpectedWithdrawals _ _ _ _ _ h7) (processSyncAggregate_payloadExpectedWithdrawals _ _ _ _ h8))))

/-- `process_withdrawals` past its early return writes `payload_expected_withdrawals` to the
expected withdrawals. -/
theorem processWithdrawals_payloadExpectedWithdrawals_full {s s' : GloasState P}
    (hc : (s.latest_block_hash != s.latest_execution_payload_bid.block_hash) = false)
    (h : JauneConsensus.Gloas.processWithdrawals s = .ok s') :
    ∃ ex, JauneConsensus.Gloas.getExpectedWithdrawals s = .ok ex ∧
      s'.payload_expected_withdrawals.toArray.toList = ex.withdrawals.toList := by
  unfold JauneConsensus.Gloas.processWithdrawals at h
  simp only [hc, Bool.false_eq_true, ite_false] at h
  obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t6, h6, h⟩ := bind_eq_ok_iff.mp h
  have q6 := updateNextWithdrawalBuilderIndex_payloadExpectedWithdrawals _ _ _ h6
  have q7 := updateNextWithdrawalValidatorIndex_payloadExpectedWithdrawals _ _ _ h
  refine ⟨ex, hex, ?_⟩
  have e : s'.payload_expected_withdrawals = t6.payload_expected_withdrawals := q7
  rw [e, show t6.payload_expected_withdrawals = _ from q6]
  rfl

/-- **`payload_expected_withdrawals` over Gloas `process_block`.** After an EMPTY settlement
(`parentFull = false`), `process_withdrawals` returns early: the step withdraws nothing and the
field is unchanged. After a FULL one, the field is exactly the step's expected withdrawals. No
other phase writes it. -/
theorem processBlock_payloadExpectedWithdrawals {ccfg : Config} {bls : Bool} {st post : GloasState P}
    {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock (gloasContext ccfg bls) st blk = .ok post) :
    (parentFull st blk = false →
      post.payload_expected_withdrawals = st.payload_expected_withdrawals ∧
        stepWithdrawals ccfg bls st blk = .ok []) ∧
    (parentFull st blk = true → ∃ ws, stepWithdrawals ccfg bls st blk = .ok ws ∧
      post.payload_expected_withdrawals.toArray.toList = ws) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  have hpost := afterWithdrawals_payloadExpectedWithdrawals h4 h5 h6 h7 h8
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have w3 := processWithdrawals_withdrawalsFrame _ _ h3
  have b4 := processExecutionPayloadBid_post h4
  have hsw : stepWithdrawals ccfg bls st blk =
      (if s2.latest_block_hash != s2.latest_execution_payload_bid.block_hash then pure []
        else do let ex ← JauneConsensus.Gloas.getExpectedWithdrawals s2; pure ex.withdrawals.toList) := by
    simp only [stepWithdrawals, h1, h2, bind, Except.bind]
  refine ⟨fun hE => ?_, fun hF => ?_⟩
  · rcases processParentExecutionPayload_cases h1 with ⟨hs1, -⟩ | ⟨hpb, -⟩
    · subst hs1
      have hne : s2.latest_block_hash ≠ s2.latest_execution_payload_bid.block_hash := by
        intro heq
        have hpar : blk.body.signed_execution_payload_bid.message.parent_block_hash =
            s2.latest_block_hash := by rw [b4.2.2.1, w3.2.1]
        have : parentFull s1 blk = true := by
          unfold parentFull
          rw [hpar, heq, hm2]
          exact beq_self_eq_true _
        rw [this] at hE; cases hE
      rw [processWithdrawalsGloas_early_return s2 hne] at h3
      cases h3
      refine ⟨by rw [hpost, hm2], ?_⟩
      rw [hsw]
      have hc : (s2.latest_block_hash != s2.latest_execution_payload_bid.block_hash) = true := by
        simpa using hne
      rw [hc]; rfl
    · have : parentFull st blk = true := by
        unfold parentFull; rw [hpb]; exact beq_self_eq_true _
      rw [this] at hE; cases hE
  · rcases processParentExecutionPayload_cases h1 with ⟨-, hpb⟩ | ⟨-, a, d, e, ha, hd, he, hs⟩
    · unfold parentFull at hF
      exact absurd (beq_iff_eq.mp hF) hpb
    · obtain ⟨-, -, hL, hK, -, -⟩ := parentFull_frame ha hd he hs
      have hc : (s2.latest_block_hash != s2.latest_execution_payload_bid.block_hash) = false := by
        rw [hm2]; simp only [hL, hK, bne_self_eq_false]
      obtain ⟨ex, hex, hw⟩ := processWithdrawals_payloadExpectedWithdrawals_full hc h3
      refine ⟨ex.withdrawals.toList, ?_, by rw [hpost, hw]⟩
      rw [hsw, hc]
      simp [hex, bind, Except.bind, pure, Except.pure]

section View

variable {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
  {preB : Gloas.BeaconState P} {preExec : BlockChain} {preParent : ParentPayload P}
  {b : Gloas.SignedBeaconBlock P} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
  {postB : Gloas.BeaconState P} {postExec : BlockChain} {postParent : ParentPayload P}

/-- **`payload_expected_withdrawals` across a Gloas joint step** (G3-11's ledger form): across an
EMPTY settlement the step withdraws nothing and the field is the pre-state's; otherwise (FULL,
over a delivered or a landed payload) it is exactly the step's expected withdrawals. -/
theorem GloasStepView.payloadExpectedWithdrawals
    (V : GloasStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent) :
    (parentFull V.postSlots b.message = false →
      postB.payload_expected_withdrawals = preB.payload_expected_withdrawals ∧
        stepWithdrawals ccfg bls V.postSlots b.message = .ok []) ∧
    (parentFull V.postSlots b.message = true →
      ∃ ws, stepWithdrawals ccfg bls V.postSlots b.message = .ok ws ∧
        postB.payload_expected_withdrawals.toArray.toList = ws) := by
  obtain ⟨hE, hF⟩ := processBlock_payloadExpectedWithdrawals V.processBlock
  refine ⟨fun h => ?_, hF⟩
  obtain ⟨e, hw⟩ := hE h
  exact ⟨e.trans (processSlots_payloadExpectedWithdrawals V.slots), hw⟩

/-- The EMPTY case by the settlement: an `.empty` settlement keeps the field. -/
theorem GloasStepView.payloadExpectedWithdrawals_empty
    (V : GloasStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    (hs : V.settle = .empty) :
    postB.payload_expected_withdrawals = preB.payload_expected_withdrawals ∧
      stepWithdrawals ccfg bls V.postSlots b.message = .ok [] := by
  refine V.payloadExpectedWithdrawals.1 ?_
  rcases V.settle_cases with ⟨-, _, _, _, -, -, -, h⟩ | ⟨-, -, -, -, h⟩ | ⟨hf, -⟩
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h
  · exact hf

end View

/-! ## The first Gloas block: builders and pending builder withdrawals -/

/-- No pending builder withdrawal, every payment empty, and `L` pays nothing. -/
def CrossingClean (m : GloasState P) : Prop :=
  m.builder_pending_withdrawals.toArray.toList = [] ∧
    (∀ p ∈ m.builder_pending_payments.toArray.toList,
      p = JauneConsensus.Gloas.BuilderPendingPayment.empty) ∧
    m.latest_execution_payload_bid.value = U64.zero

theorem crossClean_of_invariant {s s' : GloasState P} (h : InvariantFrame s s') (hc : CrossingClean s) :
    CrossingClean s' := by
  unfold CrossingClean; rw [h.2.2.1, h.2.1, h.2.2.2.1]; exact hc

/-- `upgrade_to_gloas`'s state is clean. -/
theorem upgradeToGloas_crossClean {ctx : Context} {pre : JauneConsensus.BeaconState P .fulu}
    {post : GloasState P} (h : JauneConsensus.Gloas.upgradeToGloas ctx pre = .ok post) :
    CrossingClean post := by
  unfold JauneConsensus.Gloas.upgradeToGloas at h
  obtain ⟨p0, hp0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ptc, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨fr, -⟩ := onboard_post h
  unfold JauneConsensus.Gloas.upgradedState at hp0
  obtain ⟨_, _, hp0⟩ := bind_eq_ok_iff.mp hp0
  obtain ⟨_, _, hp0⟩ := bind_eq_ok_iff.mp hp0
  cases hp0
  obtain ⟨_, hP, hW, hL, -⟩ := fr
  simp only [] at hP hW hL
  refine ⟨by rw [hW]; rfl, fun p hp => ?_, by rw [hL]⟩
  have hPa : post.builder_pending_payments.toArray =
      Array.replicate (2 * P.SLOTS_PER_EPOCH) JauneConsensus.Gloas.BuilderPendingPayment.empty := by
    rw [hP]; rfl
  rw [hPa] at hp
  simp only [Array.toList_replicate, List.mem_replicate] at hp
  exact hp.2

/-- The epoch rotation keeps a clean state clean (the quorum is positive, so no empty payment is
appended). -/
theorem rotation_crossClean (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    {cfg : Config} {a b : GloasState P}
    (h : JauneConsensus.Gloas.processBuilderPendingPayments cfg a = .ok b) (hc : CrossingClean a) :
    CrossingClean b := by
  obtain ⟨-, q, hqh, hW, hP⟩ := processBuilderPendingPayments_frame h
  have hq0 := quorum_pos hq hqh
  have hL : b.latest_execution_payload_bid = a.latest_execution_payload_bid :=
    (processBuilderPendingPayments_core _ _ _ h).2.1
  refine ⟨?_, fun p hp => ?_, by rw [hL]; exact hc.2.2⟩
  · rw [hW, hc.1, List.nil_append]
    have : ((a.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH).toList.filter
        (fun p => decide (q ≤ p.weight))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro p hp
      have he := hc.2.1 p (mem_of_mem_extract' hp)
      subst he
      simp only [decide_eq_true_eq]
      intro hle
      have : q.toNat ≤ 0 := hle
      omega
    rw [this]; rfl
  · rw [hP] at hp
    simp only [Array.toList_append, List.mem_append, Array.toList_replicate,
      List.mem_replicate] at hp
    rcases hp with hp | ⟨_, rfl⟩
    · exact hc.2.1 p (mem_of_mem_extract' hp)
    · rfl

/-- Gloas `process_slots` keeps a clean state clean, and keeps the builders. -/
theorem processSlots_crossClean (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    {ctx : Context} {s s' : GloasState P} {slot : U64}
    (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s') (hc : CrossingClean s) :
    CrossingClean s' ∧ s'.builders = s.builders := by
  refine processSlots_induction (ctx := ctx) (fun m => CrossingClean m ∧ m.builders = s.builders)
    (fun st st1 st2 next hI f1 _ hcs => ?_) h ⟨hc, rfl⟩
  have hb := (slotIteration_core f1 hcs).1
  refine ⟨?_, hb.trans hI.2⟩
  have c1 := crossClean_of_invariant f1 hI.1
  show CrossingClean st2
  rcases hcs with ⟨rfl, _⟩ | ⟨_, he⟩
  · exact c1
  · obtain ⟨a, b, fa, hb', fb⟩ := processEpoch_phases he
    exact crossClean_of_invariant fb (rotation_crossClean hq hb' (crossClean_of_invariant fa c1))

/-- The crossing's slots function keeps a clean state clean, and keeps the builders. -/
theorem crossingSlots_crossClean (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    {ctx : Context} {s s' : GloasState P} {slot : U64}
    (h : crossingSlots ctx s slot = .ok s') (hc : CrossingClean s) :
    CrossingClean s' ∧ s'.builders = s.builders := by
  unfold crossingSlots at h
  split at h
  · cases h; exact ⟨hc, rfl⟩
  · exact processSlots_crossClean hq h hc

theorem progressiveList_ext {s : Spine} {α : Type} {a b : ProgressiveListOnSpine s α}
    (h : a.toArray = b.toArray) : a = b := by
  cases a; cases b; cases h; rfl

/-- The parent settlement of a block with empty requests, from a clean state, keeps the builders
and appends no pending builder withdrawal. -/
theorem parent_crossClean {ctx : Context} {s s1 : GloasState P} {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h1 : JauneConsensus.Gloas.processParentExecutionPayload ctx s blk = .ok s1)
    (hr : blk.body.parent_execution_requests = JauneConsensus.Gloas.ExecutionRequests.empty)
    (hc : CrossingClean s) :
    s1.builders = s.builders ∧ s1.builder_pending_withdrawals.toArray.toList = [] := by
  rcases processParentExecutionPayload_cases h1 with ⟨hs1, -⟩ | ⟨-, a, d, e, ha, hd, he, hs⟩
  · subst hs1; exact ⟨rfl, hc.1⟩
  · rw [hr] at hd he
    cases hd
    cases he
    have ca := applyParentPrefix_core _ _ _ _ ha
    obtain ⟨hb1, -, hw1, -⟩ := applyParentSuffix_post hs
    refine ⟨hb1.trans ca.1, ?_⟩
    rw [hw1]
    obtain ⟨x, fx, hx⟩ := applyParentPrefix_split ha
    rw [fx.2.2.1]
    rcases hx with ⟨idx, hset⟩ | ⟨hv, -⟩ | rfl
    · obtain ⟨-, p, hp, -, hz, -⟩ := settleBuilderPayment_frame hset
      have hpe := hc.2.1 p (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hp))
      subst hpe
      rw [hz (by rw [empty_amount_zero]; decide)]
      exact hc.1
    · rw [hc.2.2] at hv; exact absurd hv (by decide)
    · exact hc.1

/-- **O-a's remainder: the first Gloas block.** From `upgrade_to_gloas`'s state `upgraded`, the
crossing's slots and a first block whose parent requests are empty leave the builder registry
exactly `upgraded`'s, balances included, and `builder_pending_withdrawals` as `upgraded`'s (empty).
Premises: the config bounds `quorumPositive` and `slotsPerEpoch`, and the post-state bounds
`validatorsBound` and `buildersBound` (the N7 bounds `GStepView.builder_balance_equation` takes). -/
theorem crossing_builders_eq
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH)
    {ctx : Context} {atFork : JauneConsensus.BeaconState P .fulu} {upgraded postSlots post : GloasState P}
    {slot : Slot} {blk : JauneConsensus.Gloas.BeaconBlock P}
    (hup : JauneConsensus.Gloas.upgradeToGloas ctx atFork = .ok upgraded)
    (h0 : crossingSlots ctx upgraded slot = .ok postSlots)
    (hp : JauneConsensus.Gloas.processBlock ctx postSlots blk = .ok post)
    (hr : blk.body.parent_execution_requests = JauneConsensus.Gloas.ExecutionRequests.empty)
    (validatorsBound : post.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : post.builders.toArray.size ≤ 2 ^ 40) :
    post.builders = upgraded.builders ∧
      post.builder_pending_withdrawals = upgraded.builder_pending_withdrawals := by
  have hc0 := upgradeToGloas_crossClean hup
  obtain ⟨hfar0, hw0⟩ := upgradeToGloas_builders hup
  obtain ⟨hcS, hbS⟩ := crossingSlots_crossClean quorumPositive h0 hc0
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases hp
  obtain ⟨hb1, hw1⟩ := parent_crossClean h1 hr hcS
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have hb2 : s2.builders = upgraded.builders := by rw [hm2]; exact hb1.trans hbS
  have hw2 : s2.builder_pending_withdrawals.toArray.toList = [] := by rw [hm2]; exact hw1
  have b4 := processExecutionPayloadBid_post h4
  have c := afterBid_core h5 h6 h7 h8
  have hpostb : post.builders = s3.builders := by rw [c.1, b4.2.2.2.2.1]
  have w3 := processWithdrawals_withdrawalsFrame _ _ h3
  -- pending builder withdrawals
  have hwpost : post.builder_pending_withdrawals.toArray.toList = [] := by
    obtain ⟨⟨k, hk⟩, -⟩ := processWithdrawals_withdrawalQueue h3
    have o7 := processOperations_operations _ _ _ _ _ h7
    have e8 : post.builder_pending_withdrawals = s7.builder_pending_withdrawals :=
      (processSyncAggregate_invariantFrame _ _ _ _ h8).2.2.1
    have e6 : s6.builder_pending_withdrawals = s4.builder_pending_withdrawals :=
      ((processEth1Data_invariantFrame _ _ _ h6).2.2.1).trans (processRandao_invariantFrame _ _ _ _ h5).2.2.1
    rw [e8, o7.2.1, e6, b4.2.2.2.2.2.2.2.2.2.1, hk, hw2, List.drop_nil]
  refine ⟨?_, by rw [hw0]; exact progressiveList_ext (Array.toList_inj.mp (by rw [hwpost]; rfl))⟩
  rw [hpostb, ← hb2]
  -- the withdrawals debit no builder
  have hfar2 : BuildersFar s2 := by intro i x hx; rw [hb2] at hx; exact hfar0 i x hx
  cases hcw : (s2.latest_block_hash != s2.latest_execution_payload_bid.block_hash)
  · obtain ⟨ex, t, hex, ht, hs3⟩ := processWithdrawals_full hcw h3
    rw [hs3]
    have vb : s2.validators.toArray.size ≤ 2 ^ 40 := by
      rw [← processWithdrawals_validatorsLength _ _ h3, ← afterWithdrawals_validatorsLength h4 h5 h6 h7 h8]
      exact validatorsBound
    have bsz : t.builders.toArray.size = s2.builders.toArray.size := by
      rw [← hs3]; exact w3.2.2.2.2.2.1
    have bb : s2.builders.toArray.size ≤ 2 ^ 40 := by
      rw [← bsz, ← hs3, ← hpostb]; exact buildersBound
    have hz : ∀ bi : U64, bi.toNat < 2 ^ 40 → routedSum bi ex.withdrawals.toList = 0 := by
      intro bi hbi
      unfold JauneConsensus.Gloas.getExpectedWithdrawals at hex
      obtain ⟨⟨bw, i1, n1⟩, e1, hex⟩ := bind_eq_ok_iff.mp hex
      obtain ⟨⟨pw, i2, n2⟩, e2, hex⟩ := bind_eq_ok_iff.mp hex
      obtain ⟨⟨sw, i3, n3⟩, e3, hex⟩ := bind_eq_ok_iff.mp hex
      obtain ⟨⟨vw, i4, n4⟩, e4, hex⟩ := bind_eq_ok_iff.mp hex
      cases hex
      have hr40 : ∀ w ∈ s2.builder_pending_withdrawals.toArray.toList,
          w.builder_index.toNat < 2 ^ 40 := by
        intro w hw; rw [hw2] at hw; cases hw
      obtain ⟨-, rb⟩ := routed_builderWithdrawals e1 hr40 hbi
      rw [hw2] at rb
      have rp := routedSum_validatorPhase (getPendingPartialWithdrawals_inRange _ _ _ _ e2) vb bi
      have rv := routedSum_validatorPhase (getValidatorsSweepWithdrawals_inRange _ _ _ _ e4) vb bi
      have hsw0 : sw.size = 0 := by
        by_contra hne
        obtain ⟨bj, bb', e, he, -, hbj, hle, -⟩ :=
          getBuildersSweepWithdrawals_provenance e3 0 (by omega)
        rw [hfar2 _ _ hbj] at hle
        exact not_far_le_epoch slotsPerEpoch he hle
      have hswl : sw.toList = [] := by
        rw [← Array.length_toList] at hsw0; exact List.eq_nil_of_length_eq_zero hsw0
      simp only [Array.toList_append, routedSum_append, hswl] at rb rp rv ⊢
      simp [routedSum, pendingWithdrawalBalance] at rb
      simp only [routedSum] at rp rv
      simp [routedSum, rp, rv, rb]
    apply progressiveList_ext
    apply Array.ext_getElem?
    intro i
    cases hb : s2.builders.toArray[i]? with
    | none =>
      have hi : s2.builders.toArray.size ≤ i := by
        simpa using hb
      rw [Array.getElem?_eq_none (by omega)]
    | some x =>
      have hi : i < 2 ^ 40 := lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hb).1 bb
      obtain ⟨bi, hbi⟩ := (U64.ofNat?_ok_iff (site := "BuilderIndex")).mpr
        (lt_trans hi (by norm_num))
      have hbn : bi.toNat = i := U64.toNat_ofNat? hbi
      subst hbn
      obtain ⟨x', hx', hxe, hbal⟩ := applyWithdrawals_builder_balance ht bb hb
        (by rw [hz bi hi]; exact Nat.zero_le _)
      rw [hz bi hi] at hbal
      rw [hx', hxe]
      have : x'.balance = x.balance := U64.ext_toNat (by omega)
      rw [this]
  · have hne : s2.latest_block_hash ≠ s2.latest_execution_payload_bid.block_hash := by
      simpa using hcw
    rw [processWithdrawalsGloas_early_return s2 hne] at h3
    cases h3
    rfl

end JauneConsensus.Facts.Gloas
