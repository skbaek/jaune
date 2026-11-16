import JauneConsensus.Facts.Gloas.Invariants

/-!
# Frames of `latest_execution_payload_header` (goal `eip8282-gloas-cross-layer-v1`, G3c)

Electra and Fulu (fork-indexed) `process_slots` and `process_block` keep
`latest_execution_payload_header`, except `process_execution_payload`, which writes it to the
payload's header (`ExecutionPayload.toHeader`). `HdrEq` is the frame, proved by the generator of
`Step.lean` (`StepRel` over `BeaconState P f`) for every epoch step and every block phase.

Consequences for the joint model:

* `processSlots_header`, `processBlock_header`, `stateTransition_header`;
* **the Fulu head relation** (`jointStep_head`): after every pre-Gloas joint step (Electra,
  Fulu, or the Electra → Fulu crossing), the step's post execution chain is the engine's verdict on
  a request whose block hashes to the post-state's `latest_execution_payload_header.block_hash`;
  so the head relation "the built-upon chain's head hash is
  `latest_execution_payload_header.block_hash`" holds after every pre-Gloas step, whatever held
  before (G3-09 over `.pre` steps);
* `crossFromFulu_header`: the Fulu → Gloas crossing upgrades a state whose
  `latest_execution_payload_header` is the pre-crossing Fulu state's, so the crossing reads its
  Fulu head relation from the pre-state.
-/

namespace JauneConsensus.Facts.Gloas

open Jaune JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas.Invariant

variable {P : Preset} {f : ConsensusFork}

/-- The execution payload header `process_execution_payload` writes for `payload`. -/
def ExecutionPayload.toHeader (payload : ExecutionPayload P) : ExecutionPayloadHeader P :=
  { parent_hash := payload.parent_hash, fee_recipient := payload.fee_recipient,
    state_root := payload.state_root, receipts_root := payload.receipts_root,
    logs_bloom := payload.logs_bloom, prev_randao := payload.prev_randao,
    block_number := payload.block_number, gas_limit := payload.gas_limit,
    gas_used := payload.gas_used, timestamp := payload.timestamp,
    extra_data := payload.extra_data, base_fee_per_gas := payload.base_fee_per_gas,
    block_hash := payload.block_hash, transactions_root := hashTreeRoot payload.transactions,
    withdrawals_root := hashTreeRoot payload.withdrawals, blob_gas_used := payload.blob_gas_used,
    excess_blob_gas := payload.excess_blob_gas }

/-- `latest_execution_payload_header` is unchanged. -/
def HeaderEq (s s' : BeaconState P f) : Prop :=
  s'.latest_execution_payload_header = s.latest_execution_payload_header

/-- `HdrEq` as a step relation. -/
def headerEq : StepRelation (BeaconState P f) where
  relation := HeaderEq
  refl _ := rfl
  trans h₁ h₂ := Eq.trans h₂ h₁

/-- Close a tail call to a step whose header frame is proved. Extensible by `macro_rules`. -/
syntax "hdr_tail" : tactic

section HdrGen

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show HeaderEq _ _ from rfl))

theorem increaseBalance_header (s : BeaconState P f) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.increaseBalance s i d) (headerEq.relation s) := by
  unfold JauneConsensus.increaseBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (increaseBalance_header _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (increaseBalance_header _ _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (increaseBalance_header _ _ _); exact (show HeaderEq _ _ from rfl)))

theorem decreaseBalance_header (s : BeaconState P f) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.decreaseBalance s i d) (headerEq.relation s) := by
  unfold JauneConsensus.decreaseBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (decreaseBalance_header _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (decreaseBalance_header _ _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (decreaseBalance_header _ _ _); exact (show HeaderEq _ _ from rfl)))

theorem setDepositRequestsStartIndex_header (s : BeaconState P f) (v : U64) :
    Ok (JauneConsensus.BeaconState.setDepositRequestsStartIndex s v) (headerEq.relation s) := by
  unfold JauneConsensus.BeaconState.setDepositRequestsStartIndex; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (setDepositRequestsStartIndex_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setDepositRequestsStartIndex_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (setDepositRequestsStartIndex_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem setDepositBalanceToConsume_header (s : BeaconState P f) (v : Gwei) :
    Ok (JauneConsensus.BeaconState.setDepositBalanceToConsume s v) (headerEq.relation s) := by
  unfold JauneConsensus.BeaconState.setDepositBalanceToConsume; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (setDepositBalanceToConsume_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setDepositBalanceToConsume_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (setDepositBalanceToConsume_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem setExitBalanceToConsume_header (s : BeaconState P f) (v : Gwei) :
    Ok (JauneConsensus.BeaconState.setExitBalanceToConsume s v) (headerEq.relation s) := by
  unfold JauneConsensus.BeaconState.setExitBalanceToConsume; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (setExitBalanceToConsume_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setExitBalanceToConsume_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (setExitBalanceToConsume_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem setEarliestExitEpoch_header (s : BeaconState P f) (v : Epoch) :
    Ok (JauneConsensus.BeaconState.setEarliestExitEpoch s v) (headerEq.relation s) := by
  unfold JauneConsensus.BeaconState.setEarliestExitEpoch; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (setEarliestExitEpoch_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setEarliestExitEpoch_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (setEarliestExitEpoch_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem setConsolidationBalanceToConsume_header (s : BeaconState P f) (v : Gwei) :
    Ok (JauneConsensus.BeaconState.setConsolidationBalanceToConsume s v) (headerEq.relation s) := by
  unfold JauneConsensus.BeaconState.setConsolidationBalanceToConsume; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (setConsolidationBalanceToConsume_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setConsolidationBalanceToConsume_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (setConsolidationBalanceToConsume_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem setEarliestConsolidationEpoch_header (s : BeaconState P f) (v : Epoch) :
    Ok (JauneConsensus.BeaconState.setEarliestConsolidationEpoch s v) (headerEq.relation s) := by
  unfold JauneConsensus.BeaconState.setEarliestConsolidationEpoch; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (setEarliestConsolidationEpoch_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setEarliestConsolidationEpoch_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (setEarliestConsolidationEpoch_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem setPendingDeposits_header (s : BeaconState P f) (v : SszList PendingDeposit P.PENDING_DEPOSITS_LIMIT) :
    Ok (JauneConsensus.BeaconState.setPendingDeposits s v) (headerEq.relation s) := by
  unfold JauneConsensus.BeaconState.setPendingDeposits; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (setPendingDeposits_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setPendingDeposits_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (setPendingDeposits_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem setPendingPartialWithdrawals_header (s : BeaconState P f) (v : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT) :
    Ok (JauneConsensus.BeaconState.setPendingPartialWithdrawals s v) (headerEq.relation s) := by
  unfold JauneConsensus.BeaconState.setPendingPartialWithdrawals; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (setPendingPartialWithdrawals_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setPendingPartialWithdrawals_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (setPendingPartialWithdrawals_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem setPendingConsolidations_header (s : BeaconState P f) (v : SszList PendingConsolidation P.PENDING_CONSOLIDATIONS_LIMIT) :
    Ok (JauneConsensus.BeaconState.setPendingConsolidations s v) (headerEq.relation s) := by
  unfold JauneConsensus.BeaconState.setPendingConsolidations; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (setPendingConsolidations_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setPendingConsolidations_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (setPendingConsolidations_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem setProposerLookahead_header (s : BeaconState P f) (v : SszVector ValidatorIndex ((P.MIN_SEED_LOOKAHEAD + 1) * P.SLOTS_PER_EPOCH)) :
    Ok (JauneConsensus.BeaconState.setProposerLookahead s v) (headerEq.relation s) := by
  unfold JauneConsensus.BeaconState.setProposerLookahead; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (setProposerLookahead_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setProposerLookahead_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (setProposerLookahead_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem computeExitEpochAndUpdateChurn_header (cfg : Config) (s : BeaconState P f) (b : Gwei) :
    Ok (JauneConsensus.computeExitEpochAndUpdateChurn cfg s b) (fun p => headerEq.relation s p.1) := by
  unfold JauneConsensus.computeExitEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (computeExitEpochAndUpdateChurn_header _ _ _) $h; exact hh))

theorem computeConsolidationEpochAndUpdateChurn_header (cfg : Config) (s : BeaconState P f) (b : Gwei) :
    Ok (JauneConsensus.computeConsolidationEpochAndUpdateChurn cfg s b) (fun p => headerEq.relation s p.1) := by
  unfold JauneConsensus.computeConsolidationEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (computeConsolidationEpochAndUpdateChurn_header _ _ _) $h; exact hh))

theorem pure_pair_header {α : Type} {s : BeaconState P f} {q : α} {a : BeaconState P f × α}
    (h : (pure (s, q) : Fallible (BeaconState P f × α)) = .ok a) : HeaderEq s a.1 := by
  cases h; rfl

section IVE

/-- The exit queue epoch before Electra: a pair returned by `pure`. -/
local macro_rules
  | `(tactic| gstep_of $h) => `(tactic| (have hh := pure_pair_header $h; exact hh))

set_option maxHeartbeats 2000000 in
theorem initiateValidatorExit_header (cfg : Config) (s : BeaconState P f) (i : ValidatorIndex) :
    Ok (JauneConsensus.initiateValidatorExit cfg s i) (headerEq.relation s) := by
  unfold JauneConsensus.initiateValidatorExit; gvcg

end IVE

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (initiateValidatorExit_header _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (initiateValidatorExit_header _ _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (initiateValidatorExit_header _ _ _); exact (show HeaderEq _ _ from rfl)))

theorem slashValidator_header (cfg : Config) (s : BeaconState P f) (i : ValidatorIndex) (wb : Option ValidatorIndex) :
    Ok (JauneConsensus.slashValidator cfg s i wb) (headerEq.relation s) := by
  unfold JauneConsensus.slashValidator; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (slashValidator_header _ _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (slashValidator_header _ _ _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (slashValidator_header _ _ _ _); exact (show HeaderEq _ _ from rfl)))

theorem queueExcessActiveBalance_header (s : BeaconState P f) (i : ValidatorIndex) :
    Ok (JauneConsensus.queueExcessActiveBalance s i) (headerEq.relation s) := by
  unfold JauneConsensus.queueExcessActiveBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (queueExcessActiveBalance_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (queueExcessActiveBalance_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (queueExcessActiveBalance_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem switchToCompoundingValidator_header (s : BeaconState P f) (i : ValidatorIndex) :
    Ok (JauneConsensus.switchToCompoundingValidator s i) (headerEq.relation s) := by
  unfold JauneConsensus.switchToCompoundingValidator; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (switchToCompoundingValidator_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (switchToCompoundingValidator_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (switchToCompoundingValidator_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem addValidatorToRegistry_header (s : BeaconState P f) (pk : BLSPubkey) (wc : Bytes32) (a : U64) :
    Ok (JauneConsensus.addValidatorToRegistry s pk wc a) (headerEq.relation s) := by
  unfold JauneConsensus.addValidatorToRegistry; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (addValidatorToRegistry_header _ _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (addValidatorToRegistry_header _ _ _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (addValidatorToRegistry_header _ _ _ _); exact (show HeaderEq _ _ from rfl)))

theorem applyDeposit_header (ctx : Context) (s : BeaconState P f) (pk : BLSPubkey) (wc : Bytes32) (a : U64) (sig : BLSSignature) :
    Ok (JauneConsensus.applyDeposit ctx s pk wc a sig) (headerEq.relation s) := by
  unfold JauneConsensus.applyDeposit; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (applyDeposit_header _ _ _ _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (applyDeposit_header _ _ _ _ _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (applyDeposit_header _ _ _ _ _ _); exact (show HeaderEq _ _ from rfl)))

theorem processDeposit_header (ctx : Context) (s : BeaconState P f) (d : Deposit) :
    Ok (JauneConsensus.processDeposit ctx s d) (headerEq.relation s) := by
  unfold JauneConsensus.processDeposit; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processDeposit_header _ _ _) $h; exact hh))

theorem processProposerSlashing_header (ctx : Context) (s : BeaconState P f) (ps : ProposerSlashing) :
    Ok (JauneConsensus.processProposerSlashing ctx s ps) (headerEq.relation s) := by
  unfold JauneConsensus.processProposerSlashing; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processProposerSlashing_header _ _ _) $h; exact hh))

theorem processAttesterSlashing_header (ctx : Context) (s : BeaconState P f) (as : AttesterSlashing P f) :
    Ok (JauneConsensus.processAttesterSlashing ctx s as) (headerEq.relation s) := by
  unfold JauneConsensus.processAttesterSlashing; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processAttesterSlashing_header _ _ _) $h; exact hh))

set_option maxHeartbeats 4000000 in
theorem processAttestation_header (ctx : Context) (s : BeaconState P f) (a : Attestation P f) :
    Ok (JauneConsensus.processAttestation ctx s a) (headerEq.relation s) := by
  unfold JauneConsensus.processAttestation; jvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processAttestation_header _ _ _) $h; exact hh))

theorem processVoluntaryExit_header (ctx : Context) (s : BeaconState P f) (sve : SignedVoluntaryExit) :
    Ok (JauneConsensus.processVoluntaryExit ctx s sve) (headerEq.relation s) := by
  unfold JauneConsensus.processVoluntaryExit; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processVoluntaryExit_header _ _ _) $h; exact hh))

theorem processBlsToExecutionChange_header (ctx : Context) (s : BeaconState P f) (sac : SignedBLSToExecutionChange) :
    Ok (JauneConsensus.processBlsToExecutionChange ctx s sac) (headerEq.relation s) := by
  unfold JauneConsensus.processBlsToExecutionChange; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processBlsToExecutionChange_header _ _ _) $h; exact hh))

theorem processDepositRequest_header (s : BeaconState P f) (dr : DepositRequest) :
    Ok (JauneConsensus.processDepositRequest s dr) (headerEq.relation s) := by
  unfold JauneConsensus.processDepositRequest; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processDepositRequest_header _ _) $h; exact hh))

theorem processWithdrawalRequest_header (cfg : Config) (s : BeaconState P f) (wr : WithdrawalRequest) :
    Ok (JauneConsensus.processWithdrawalRequest cfg s wr) (headerEq.relation s) := by
  unfold JauneConsensus.processWithdrawalRequest; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processWithdrawalRequest_header _ _ _) $h; exact hh))

theorem processConsolidationRequest_header (cfg : Config) (s : BeaconState P f) (cr : ConsolidationRequest) :
    Ok (JauneConsensus.processConsolidationRequest cfg s cr) (headerEq.relation s) := by
  unfold JauneConsensus.processConsolidationRequest; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processConsolidationRequest_header _ _ _) $h; exact hh))

set_option maxHeartbeats 2000000 in
theorem processOperations_header (ctx : Context) (s : BeaconState P f) (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processOperations ctx s body) (headerEq.relation s) := by
  unfold JauneConsensus.processOperations; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processOperations_header _ _ _) $h; exact hh))

theorem processBlockHeader_header (s : BeaconState P f) (blk : BeaconBlock P f) :
    Ok (JauneConsensus.processBlockHeader s blk) (headerEq.relation s) := by
  unfold JauneConsensus.processBlockHeader; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processBlockHeader_header _ _) $h; exact hh))

theorem processRandao_header (ctx : Context) (s : BeaconState P f) (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processRandao ctx s body) (headerEq.relation s) := by
  unfold JauneConsensus.processRandao; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processRandao_header _ _ _) $h; exact hh))

theorem processEth1Data_header (s : BeaconState P f) (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processEth1Data s body) (headerEq.relation s) := by
  unfold JauneConsensus.processEth1Data; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processEth1Data_header _ _) $h; exact hh))

set_option maxHeartbeats 4000000 in
theorem processSyncAggregate_header (ctx : Context) (s : BeaconState P f) (sa : SyncAggregate P) :
    Ok (JauneConsensus.processSyncAggregate ctx s sa) (headerEq.relation s) := by
  unfold JauneConsensus.processSyncAggregate; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processSyncAggregate_header _ _ _) $h; exact hh))

set_option maxHeartbeats 2000000 in
theorem processWithdrawals_header (s : BeaconState P f) (pl : ExecutionPayload P) :
    Ok (JauneConsensus.processWithdrawals s pl) (headerEq.relation s) := by
  unfold JauneConsensus.processWithdrawals; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processWithdrawals_header _ _) $h; exact hh))

set_option maxHeartbeats 4000000 in
theorem weighJustificationAndFinalization_header (s : BeaconState P f) (t p c : Gwei) :
    Ok (JauneConsensus.weighJustificationAndFinalization s t p c) (headerEq.relation s) := by
  unfold JauneConsensus.weighJustificationAndFinalization; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (weighJustificationAndFinalization_header _ _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (weighJustificationAndFinalization_header _ _ _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (weighJustificationAndFinalization_header _ _ _ _); exact (show HeaderEq _ _ from rfl)))

set_option maxHeartbeats 4000000 in
theorem processJustificationAndFinalization_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processJustificationAndFinalization cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processJustificationAndFinalization; jvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processJustificationAndFinalization_header _ _) $h; exact hh))

set_option maxHeartbeats 4000000 in
theorem processInactivityUpdates_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processInactivityUpdates cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processInactivityUpdates; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processInactivityUpdates_header _ _) $h; exact hh))

theorem processRewardsAndPenalties_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processRewardsAndPenalties cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processRewardsAndPenalties; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processRewardsAndPenalties_header _ _) $h; exact hh))

theorem processRegistryUpdatesElectra_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processRegistryUpdatesElectra cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processRegistryUpdatesElectra; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processRegistryUpdatesElectra_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (processRegistryUpdatesElectra_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (processRegistryUpdatesElectra_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem processRegistryUpdatesDeneb_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processRegistryUpdatesDeneb cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processRegistryUpdatesDeneb; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processRegistryUpdatesDeneb_header _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (processRegistryUpdatesDeneb_header _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (processRegistryUpdatesDeneb_header _ _); exact (show HeaderEq _ _ from rfl)))

theorem processRegistryUpdates_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processRegistryUpdates cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processRegistryUpdates; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processRegistryUpdates_header _ _) $h; exact hh))

set_option maxHeartbeats 4000000 in
theorem processSlashings_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processSlashings cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processSlashings; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processSlashings_header _ _) $h; exact hh))

theorem processEth1DataReset_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processEth1DataReset cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processEth1DataReset; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processEth1DataReset_header _ _) $h; exact hh))

theorem applyPendingDeposit_header (ctx : Context) (s : BeaconState P f) (d : PendingDeposit) :
    Ok (JauneConsensus.applyPendingDeposit ctx s d) (headerEq.relation s) := by
  unfold JauneConsensus.applyPendingDeposit; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (applyPendingDeposit_header _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (applyPendingDeposit_header _ _ _)
      | (refine StepRelation.ok_rebase headerEq ?_ (applyPendingDeposit_header _ _ _); exact (show HeaderEq _ _ from rfl)))

section PendingDeposits

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRelation.forIn_array_relation _ (fun x => x.2.2.2.2) ?_ _ _ $h; intro _ _; gvcg))

set_option maxHeartbeats 4000000 in
theorem processPendingDeposits_header (ctx : Context) (s : BeaconState P f) :
    Ok (JauneConsensus.processPendingDeposits ctx s) (headerEq.relation s) := by
  unfold JauneConsensus.processPendingDeposits; gvcg
  all_goals hdr_tail

end PendingDeposits

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processPendingDeposits_header _ _) $h; exact hh))

theorem processPendingConsolidations_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processPendingConsolidations cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processPendingConsolidations; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processPendingConsolidations_header _ _) $h; exact hh))

theorem processEffectiveBalanceUpdates_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processEffectiveBalanceUpdates cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processEffectiveBalanceUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processEffectiveBalanceUpdates_header _ _) $h; exact hh))

theorem processSlashingsReset_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processSlashingsReset cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processSlashingsReset; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processSlashingsReset_header _ _) $h; exact hh))

theorem processRandaoMixesReset_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processRandaoMixesReset cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processRandaoMixesReset; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processRandaoMixesReset_header _ _) $h; exact hh))

theorem processHistoricalSummariesUpdate_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processHistoricalSummariesUpdate cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processHistoricalSummariesUpdate; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processHistoricalSummariesUpdate_header _ _) $h; exact hh))

theorem processParticipationFlagUpdates_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processParticipationFlagUpdates cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processParticipationFlagUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processParticipationFlagUpdates_header _ _) $h; exact hh))

theorem processSyncCommitteeUpdates_header (ctx : Context) (s : BeaconState P f) :
    Ok (JauneConsensus.processSyncCommitteeUpdates ctx s) (headerEq.relation s) := by
  unfold JauneConsensus.processSyncCommitteeUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processSyncCommitteeUpdates_header _ _) $h; exact hh))

theorem processProposerLookahead_header (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processProposerLookahead cfg s) (headerEq.relation s) := by
  unfold JauneConsensus.processProposerLookahead; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processProposerLookahead_header _ _) $h; exact hh))


/-- `process_slot` with its two hashes abstracted: the proof never meets `hash_tree_root` of a
state. -/
def processSlotAbstractedHashesForkIndexed (h₁ : BeaconState P f → Root) (h₂ : BeaconBlockHeader → Root)
    (state : BeaconState P f) : Fallible (BeaconState P f) := do
  let slotsPerHistoricalRoot ← u64 P.SLOTS_PER_HISTORICAL_ROOT "SLOTS_PER_HISTORICAL_ROOT"
  let i := (← state.slot.mod? slotsPerHistoricalRoot "process_slot: slot % SLOTS_PER_HISTORICAL_ROOT").toNat
  let previousStateRoot : Root := h₁ state
  let state := { state with
    state_roots := ← state.state_roots.set i previousStateRoot "process_slot: state_roots" }
  let state :=
    if Bytes32.beq state.latest_block_header.state_root (0 : Jaune.U256) then
      { state with latest_block_header :=
          { state.latest_block_header with state_root := previousStateRoot } }
    else state
  let previousBlockRoot : Root := h₂ state.latest_block_header
  pure { state with
    block_roots := ← state.block_roots.set i previousBlockRoot "process_slot: block_roots" }

theorem processSlot_eqForkIndexed (s : BeaconState P f) :
    JauneConsensus.processSlot s = processSlotAbstractedHashesForkIndexed Ssz.hashTreeRoot Ssz.hashTreeRoot s := rfl

theorem processSlotAbstractedHashesForkIndexed_header (h₁ : BeaconState P f → Root) (h₂ : BeaconBlockHeader → Root)
    (s : BeaconState P f) : Ok (processSlotAbstractedHashesForkIndexed h₁ h₂ s) (headerEq.relation s) := by
  intro s' h
  unfold processSlotAbstractedHashesForkIndexed at h
  repeat (obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h)
  cases h
  show HeaderEq _ _
  unfold HeaderEq
  split <;> rfl

theorem processSlot_header (s : BeaconState P f) :
    Ok (JauneConsensus.processSlot s) (headerEq.relation s) := by
  rw [processSlot_eqForkIndexed]; exact processSlotAbstractedHashesForkIndexed_header _ _ s

end HdrGen

set_option hygiene false in
/-- The steps of `process_epoch` after the pending queues, from `h`. -/
local macro "epoch_tail" : tactic => `(tactic| (
  obtain ⟨x8, h8, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x9, h9, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x10, h10, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x11, h11, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x12, h12, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x13, h13, h⟩ := bind_eq_ok_iff.mp h
  have f14 : HeaderEq x13 s' := by
    split at h
    · exact processProposerLookahead_header _ _ _ h
    · cases h; rfl
  exact (headerEq).trans (processEffectiveBalanceUpdates_header _ _ _ h8) <|
    (headerEq).trans (processSlashingsReset_header _ _ _ h9) <|
    (headerEq).trans (processRandaoMixesReset_header _ _ _ h10) <|
    (headerEq).trans (processHistoricalSummariesUpdate_header _ _ _ h11) <|
    (headerEq).trans (processParticipationFlagUpdates_header _ _ _ h12) <|
    (headerEq).trans (processSyncCommitteeUpdates_header _ _ _ h13) f14))

/-- `process_epoch` keeps `latest_execution_payload_header`. -/
theorem processEpoch_header (ctx : Context) (s : BeaconState P f) :
    Ok (processEpoch ctx s) (headerEq.relation s) := by
  intro s' h
  unfold processEpoch at h
  obtain ⟨x1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x6, h6, h⟩ := bind_eq_ok_iff.mp h
  have f6 : HeaderEq s x6 :=
    headerEq.trans (processJustificationAndFinalization_header _ _ _ h1) <|
    headerEq.trans (processInactivityUpdates_header _ _ _ h2) <|
    headerEq.trans (processRewardsAndPenalties_header _ _ _ h3) <|
    headerEq.trans (processRegistryUpdates_header _ _ _ h4) <|
    headerEq.trans (processSlashings_header _ _ _ h5) (processEth1DataReset_header _ _ _ h6)
  simp only [] at h
  split at h
  · obtain ⟨y7, h7a, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x7, h7, h⟩ := bind_eq_ok_iff.mp h
    have f7 : HeaderEq x6 x7 := headerEq.trans (processPendingDeposits_header _ _ _ h7a)
      (processPendingConsolidations_header _ _ _ h7)
    refine headerEq.trans f6 (headerEq.trans f7 ?_)
    epoch_tail
  · obtain ⟨x7, h7, h⟩ := bind_eq_ok_iff.mp h
    cases h7
    refine headerEq.trans f6 ?_
    epoch_tail

theorem range_forIn_invariant' {β : Type} (I : β → Prop) {r : Std.Legacy.Range} {init out : β}
    {body : Nat → β → Fallible (ForInStep β)} (hb : ∀ a b x, I b → body a b = .ok x → I x.value)
    (h : forIn r init body = .ok out) (hI : I init) : I out := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact list_forIn_relation (fun a b => I a → I b) (fun _ h => h) (fun _ _ _ h1 h2 x => h2 (h1 x))
    body (fun a b x hx hIb => hb a b x hIb hx) _ init out h hI

/-- `process_slots` with any epoch function keeping the header keeps the header. -/
theorem processSlotsWith_header {pe : BeaconState P f → Fallible (BeaconState P f)}
    (hE : ∀ a, Ok (pe a) (headerEq.relation a)) {s s' : BeaconState P f} {slot : Slot}
    (h : processSlotsWith pe s slot = .ok s') :
    s'.latest_execution_payload_header = s.latest_execution_payload_header := by
  unfold processSlotsWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine range_forIn_invariant' (fun m : BeaconState P f => m.latest_execution_payload_header =
    s.latest_execution_payload_header) (fun a b x hb hx => ?_) hout rfl
  obtain ⟨st1, h1, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨next, hn, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨r, hr, hx⟩ := bind_eq_ok_iff.mp hx
  have f1 : st1.latest_execution_payload_header = b.latest_execution_payload_header :=
    processSlot_header _ _ h1
  simp only [] at hx
  split at hx
  · obtain ⟨st2, he, hx⟩ := bind_eq_ok_iff.mp hx
    cases hx
    have f2 : st2.latest_execution_payload_header = st1.latest_execution_payload_header :=
      hE _ _ he
    show st2.latest_execution_payload_header = _
    rw [f2, f1, hb]
  · cases hx
    show st1.latest_execution_payload_header = _
    rw [f1, hb]

/-- **`process_slots` keeps `latest_execution_payload_header`.** -/
theorem processSlots_header {ctx : Context} {s s' : BeaconState P f} {slot : Slot}
    (h : processSlots ctx s slot = .ok s') :
    s'.latest_execution_payload_header = s.latest_execution_payload_header :=
  processSlotsWith_header (fun a => processEpoch_header ctx a) h

section ExecPayload

local macro_rules | `(tactic| gstep_close) => `(tactic| rfl)

/-- `process_execution_payload` writes the payload's header. -/
theorem processExecutionPayload_header (ctx : Context) (s : BeaconState P f)
    (body : BeaconBlockBody P f) :
    Ok (processExecutionPayload ctx s body) (fun s' =>
      s'.latest_execution_payload_header = ExecutionPayload.toHeader body.execution_payload) := by
  unfold processExecutionPayload; gvcg

end ExecPayload

/-- **`process_block` writes `latest_execution_payload_header` once, to the payload's header**
(in `process_execution_payload`); the phases after it keep it. -/
theorem processBlock_header {ctx : Context} {s s' : BeaconState P f} {blk : BeaconBlock P f}
    (h : processBlock ctx s blk = .ok s') :
    s'.latest_execution_payload_header = ExecutionPayload.toHeader blk.body.execution_payload := by
  unfold processBlock processBlockWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h⟩ := bind_eq_ok_iff.mp h
  have e3 := processExecutionPayload_header _ _ _ _ h3
  exact (headerEq.trans (processRandao_header _ _ _ _ h4) (headerEq.trans (processEth1Data_header _ _ _ h5)
    (headerEq.trans (processOperations_header _ _ _ _ h6) (processSyncAggregate_header _ _ _ _ h)))).trans e3

/-- `state_transition` is `process_slots` then `process_block` (and the two checks). -/
theorem stateTransition_split {ctx : Context} {s s' : BeaconState P f} {sb : SignedBeaconBlock P f}
    {vr : Bool} (h : stateTransition ctx s sb vr = .ok s') :
    ∃ m, processSlots ctx s sb.message.slot = .ok m ∧ processBlock ctx m sb.message = .ok s' := by
  unfold stateTransition stateTransitionWith at h
  obtain ⟨m, hm, h⟩ := bind_eq_ok_iff.mp h
  refine ⟨m, hm, ?_⟩
  cases vr
  · simp only [Bool.false_eq_true, ite_false] at h
    obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
    cases h; exact hy
  · simp only [ite_true] at h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    cases h; exact hy

/-- **`state_transition` leaves the block's payload header.** -/
theorem stateTransition_header {ctx : Context} {s s' : BeaconState P f} {sb : SignedBeaconBlock P f}
    {vr : Bool} (h : stateTransition ctx s sb vr = .ok s') :
    s'.latest_execution_payload_header =
      ExecutionPayload.toHeader sb.message.body.execution_payload := by
  obtain ⟨m, -, hb⟩ := stateTransition_split h
  exact processBlock_header hb

/-- The crossing's block at the fork slot: the signature check, `process_block`, the state root. -/
theorem atSlot_processBlock {ctx : Context} {bls : Bool} {s s' : BeaconState P f}
    {sb : SignedBeaconBlock P f}
    (h : (do require (← verifyBlockSignature bls s sb) "state_transition: verify_block_signature"
             let s ← processBlock ctx s sb.message
             require (Bytes32.beq sb.message.state_root (Ssz.hashTreeRoot s))
               "state_transition: block.state_root"
             pure s) = .ok s') :
    processBlock ctx s sb.message = .ok s' := by
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h; exact hy

/-- The engine's request for a block with an accepted payload hashes to the payload's
`block_hash`, which is the block's payload header's. -/
theorem engineVerdict_head {cfg : ChainConfig} {cf : ConsensusFork} {exec exec' : BlockChain}
    {g : ConsensusFork} (hg : g.atLeast .electra = true) {blk : BeaconBlock P g}
    {req : NewPayloadRequest P} (hreq : NewPayloadRequest.ofBlock blk = .ok req)
    (hv : engineVerdict cfg cf exec req = .ok exec') :
    (payloadToBlock req).header.hash =
      (ExecutionPayload.toHeader blk.body.execution_payload).block_hash := by
  have h1 := (engineVerdict_ok_iff.mp hv).2.1
  rw [NewPayloadRequest.ofBlock_ok (h := hg)] at hreq
  cases hreq
  exact h1

/-- **The Fulu head relation across a pre-Gloas joint step** (G3-09 over `.pre` steps). After
every Electra, Fulu or Electra → Fulu joint step, the post execution chain is the engine's verdict,
at the post-state's fork, on a request whose execution block hashes to the post-state's
`latest_execution_payload_header.block_hash`. (That chain then ends with that block, so its head
hash is `latest_execution_payload_header.block_hash`, whatever held before the step.) -/
theorem jointStep_head {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s s' : JointState P}
    {b : AnySignedBlock P} (h : jointStep cfg ccfg bls s b = .ok s') :
    ∃ req : NewPayloadRequest P, engineVerdict cfg s'.fork s.execution req = .ok s'.execution ∧
      (payloadToBlock req).header.hash = s'.beacon.latest_execution_payload_header.block_hash := by
  obtain ⟨sf, beacon, exec⟩ := s
  obtain ⟨g, sb⟩ := b
  cases sf <;> cases g
  case electra.electra =>
    obtain ⟨-, req, beacon', exec', hreq, hv, hst, rfl⟩ := jointStep_electra_ok_iff.mp h
    exact ⟨req, hv, by rw [stateTransition_header hst]; exact engineVerdict_head rfl hreq hv⟩
  case fulu.fulu =>
    obtain ⟨req, beacon', exec', hreq, hv, hst, rfl⟩ := jointStep_fulu_ok_iff.mp h
    exact ⟨req, hv, by rw [stateTransition_header hst]; exact engineVerdict_head rfl hreq hv⟩
  case electra.fulu =>
    obtain ⟨-, -, req, fs, b1, b2, beacon', exec', h1, h2, h3, hreq, hv, hst, rfl⟩ :=
      jointStep_cross_ok_iff.mp h
    refine ⟨req, hv, ?_⟩
    have hh : beacon'.latest_execution_payload_header =
        ExecutionPayload.toHeader sb.message.body.execution_payload := by
      split at hst
      · exact processBlock_header (atSlot_processBlock hst)
      · exact stateTransition_header hst
    show _ = beacon'.latest_execution_payload_header.block_hash
    rw [hh]; exact engineVerdict_head rfl hreq hv
  all_goals simp [jointStep] at h

/-- **The crossing reads its Fulu head relation from the pre-state.** `crossFromFulu` upgrades a
Fulu state whose `latest_execution_payload_header` is the pre-crossing state's (the Fulu
`process_slots` to the fork slot keeps it). -/
theorem crossFromFulu_header {ctx : Context} {pre : JauneConsensus.BeaconState P .fulu}
    {post : JauneConsensus.Gloas.BeaconState P}
    (h : JauneConsensus.Gloas.crossFromFulu ctx pre = .ok post) :
    ∃ atFork : JauneConsensus.BeaconState P .fulu,
      JauneConsensus.Gloas.upgradeToGloas ctx atFork = .ok post ∧
      atFork.latest_execution_payload_header = pre.latest_execution_payload_header := by
  unfold JauneConsensus.Gloas.crossFromFulu at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  simp only [] at h
  split at h
  · obtain ⟨atFork, ha, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    exact ⟨atFork, h, processSlots_header ha⟩
  · obtain ⟨atFork, ha, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    cases ha
    exact ⟨_, h, rfl⟩

end JauneConsensus.Facts.Gloas
