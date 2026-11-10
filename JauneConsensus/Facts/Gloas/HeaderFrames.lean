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

open Jaune JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {f : CFork}

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
def HdrEq (s s' : BeaconState P f) : Prop :=
  s'.latest_execution_payload_header = s.latest_execution_payload_header

/-- `HdrEq` as a step relation. -/
def hdrEq : StepRel (BeaconState P f) where
  R := HdrEq
  refl _ := rfl
  trans h₁ h₂ := Eq.trans h₂ h₁

/-- Close a tail call to a step whose header frame is proved. Extensible by `macro_rules`. -/
syntax "hdr_tail" : tactic

section HdrGen

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show HdrEq _ _ from rfl))

theorem increaseBalance_hdr (s : BeaconState P f) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.increaseBalance s i d) (hdrEq.R s) := by
  unfold JauneConsensus.increaseBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (increaseBalance_hdr _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (increaseBalance_hdr _ _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (increaseBalance_hdr _ _ _); exact (show HdrEq _ _ from rfl)))

theorem decreaseBalance_hdr (s : BeaconState P f) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.decreaseBalance s i d) (hdrEq.R s) := by
  unfold JauneConsensus.decreaseBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (decreaseBalance_hdr _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (decreaseBalance_hdr _ _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (decreaseBalance_hdr _ _ _); exact (show HdrEq _ _ from rfl)))

theorem setDepositRequestsStartIndex_hdr (s : BeaconState P f) (v : U64) :
    Ok (JauneConsensus.BeaconState.setDepositRequestsStartIndex s v) (hdrEq.R s) := by
  unfold JauneConsensus.BeaconState.setDepositRequestsStartIndex; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (setDepositRequestsStartIndex_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setDepositRequestsStartIndex_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (setDepositRequestsStartIndex_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem setDepositBalanceToConsume_hdr (s : BeaconState P f) (v : Gwei) :
    Ok (JauneConsensus.BeaconState.setDepositBalanceToConsume s v) (hdrEq.R s) := by
  unfold JauneConsensus.BeaconState.setDepositBalanceToConsume; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (setDepositBalanceToConsume_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setDepositBalanceToConsume_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (setDepositBalanceToConsume_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem setExitBalanceToConsume_hdr (s : BeaconState P f) (v : Gwei) :
    Ok (JauneConsensus.BeaconState.setExitBalanceToConsume s v) (hdrEq.R s) := by
  unfold JauneConsensus.BeaconState.setExitBalanceToConsume; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (setExitBalanceToConsume_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setExitBalanceToConsume_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (setExitBalanceToConsume_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem setEarliestExitEpoch_hdr (s : BeaconState P f) (v : Epoch) :
    Ok (JauneConsensus.BeaconState.setEarliestExitEpoch s v) (hdrEq.R s) := by
  unfold JauneConsensus.BeaconState.setEarliestExitEpoch; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (setEarliestExitEpoch_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setEarliestExitEpoch_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (setEarliestExitEpoch_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem setConsolidationBalanceToConsume_hdr (s : BeaconState P f) (v : Gwei) :
    Ok (JauneConsensus.BeaconState.setConsolidationBalanceToConsume s v) (hdrEq.R s) := by
  unfold JauneConsensus.BeaconState.setConsolidationBalanceToConsume; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (setConsolidationBalanceToConsume_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setConsolidationBalanceToConsume_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (setConsolidationBalanceToConsume_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem setEarliestConsolidationEpoch_hdr (s : BeaconState P f) (v : Epoch) :
    Ok (JauneConsensus.BeaconState.setEarliestConsolidationEpoch s v) (hdrEq.R s) := by
  unfold JauneConsensus.BeaconState.setEarliestConsolidationEpoch; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (setEarliestConsolidationEpoch_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setEarliestConsolidationEpoch_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (setEarliestConsolidationEpoch_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem setPendingDeposits_hdr (s : BeaconState P f) (v : SszList PendingDeposit P.PENDING_DEPOSITS_LIMIT) :
    Ok (JauneConsensus.BeaconState.setPendingDeposits s v) (hdrEq.R s) := by
  unfold JauneConsensus.BeaconState.setPendingDeposits; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (setPendingDeposits_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setPendingDeposits_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (setPendingDeposits_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem setPendingPartialWithdrawals_hdr (s : BeaconState P f) (v : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT) :
    Ok (JauneConsensus.BeaconState.setPendingPartialWithdrawals s v) (hdrEq.R s) := by
  unfold JauneConsensus.BeaconState.setPendingPartialWithdrawals; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (setPendingPartialWithdrawals_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setPendingPartialWithdrawals_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (setPendingPartialWithdrawals_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem setPendingConsolidations_hdr (s : BeaconState P f) (v : SszList PendingConsolidation P.PENDING_CONSOLIDATIONS_LIMIT) :
    Ok (JauneConsensus.BeaconState.setPendingConsolidations s v) (hdrEq.R s) := by
  unfold JauneConsensus.BeaconState.setPendingConsolidations; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (setPendingConsolidations_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setPendingConsolidations_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (setPendingConsolidations_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem setProposerLookahead_hdr (s : BeaconState P f) (v : SszVector ValidatorIndex ((P.MIN_SEED_LOOKAHEAD + 1) * P.SLOTS_PER_EPOCH)) :
    Ok (JauneConsensus.BeaconState.setProposerLookahead s v) (hdrEq.R s) := by
  unfold JauneConsensus.BeaconState.setProposerLookahead; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (setProposerLookahead_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (setProposerLookahead_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (setProposerLookahead_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem computeExitEpochAndUpdateChurn_hdr (cfg : Config) (s : BeaconState P f) (b : Gwei) :
    Ok (JauneConsensus.computeExitEpochAndUpdateChurn cfg s b) (fun p => hdrEq.R s p.1) := by
  unfold JauneConsensus.computeExitEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (computeExitEpochAndUpdateChurn_hdr _ _ _) $h; exact hh))

theorem computeConsolidationEpochAndUpdateChurn_hdr (cfg : Config) (s : BeaconState P f) (b : Gwei) :
    Ok (JauneConsensus.computeConsolidationEpochAndUpdateChurn cfg s b) (fun p => hdrEq.R s p.1) := by
  unfold JauneConsensus.computeConsolidationEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (computeConsolidationEpochAndUpdateChurn_hdr _ _ _) $h; exact hh))

theorem pure_pair_hdr {α : Type} {s : BeaconState P f} {q : α} {a : BeaconState P f × α}
    (h : (pure (s, q) : M (BeaconState P f × α)) = .ok a) : HdrEq s a.1 := by
  cases h; rfl

section IVE

/-- The exit queue epoch before Electra: a pair returned by `pure`. -/
local macro_rules
  | `(tactic| gstep_of $h) => `(tactic| (have hh := pure_pair_hdr $h; exact hh))

set_option maxHeartbeats 2000000 in
theorem initiateValidatorExit_hdr (cfg : Config) (s : BeaconState P f) (i : ValidatorIndex) :
    Ok (JauneConsensus.initiateValidatorExit cfg s i) (hdrEq.R s) := by
  unfold JauneConsensus.initiateValidatorExit; gvcg

end IVE

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (initiateValidatorExit_hdr _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (initiateValidatorExit_hdr _ _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (initiateValidatorExit_hdr _ _ _); exact (show HdrEq _ _ from rfl)))

theorem slashValidator_hdr (cfg : Config) (s : BeaconState P f) (i : ValidatorIndex) (wb : Option ValidatorIndex) :
    Ok (JauneConsensus.slashValidator cfg s i wb) (hdrEq.R s) := by
  unfold JauneConsensus.slashValidator; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (slashValidator_hdr _ _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (slashValidator_hdr _ _ _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (slashValidator_hdr _ _ _ _); exact (show HdrEq _ _ from rfl)))

theorem queueExcessActiveBalance_hdr (s : BeaconState P f) (i : ValidatorIndex) :
    Ok (JauneConsensus.queueExcessActiveBalance s i) (hdrEq.R s) := by
  unfold JauneConsensus.queueExcessActiveBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (queueExcessActiveBalance_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (queueExcessActiveBalance_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (queueExcessActiveBalance_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem switchToCompoundingValidator_hdr (s : BeaconState P f) (i : ValidatorIndex) :
    Ok (JauneConsensus.switchToCompoundingValidator s i) (hdrEq.R s) := by
  unfold JauneConsensus.switchToCompoundingValidator; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (switchToCompoundingValidator_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (switchToCompoundingValidator_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (switchToCompoundingValidator_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem addValidatorToRegistry_hdr (s : BeaconState P f) (pk : BLSPubkey) (wc : Bytes32) (a : U64) :
    Ok (JauneConsensus.addValidatorToRegistry s pk wc a) (hdrEq.R s) := by
  unfold JauneConsensus.addValidatorToRegistry; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (addValidatorToRegistry_hdr _ _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (addValidatorToRegistry_hdr _ _ _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (addValidatorToRegistry_hdr _ _ _ _); exact (show HdrEq _ _ from rfl)))

theorem applyDeposit_hdr (ctx : Ctx) (s : BeaconState P f) (pk : BLSPubkey) (wc : Bytes32) (a : U64) (sig : BLSSignature) :
    Ok (JauneConsensus.applyDeposit ctx s pk wc a sig) (hdrEq.R s) := by
  unfold JauneConsensus.applyDeposit; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (applyDeposit_hdr _ _ _ _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (applyDeposit_hdr _ _ _ _ _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (applyDeposit_hdr _ _ _ _ _ _); exact (show HdrEq _ _ from rfl)))

theorem processDeposit_hdr (ctx : Ctx) (s : BeaconState P f) (d : Deposit) :
    Ok (JauneConsensus.processDeposit ctx s d) (hdrEq.R s) := by
  unfold JauneConsensus.processDeposit; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processDeposit_hdr _ _ _) $h; exact hh))

theorem processProposerSlashing_hdr (ctx : Ctx) (s : BeaconState P f) (ps : ProposerSlashing) :
    Ok (JauneConsensus.processProposerSlashing ctx s ps) (hdrEq.R s) := by
  unfold JauneConsensus.processProposerSlashing; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processProposerSlashing_hdr _ _ _) $h; exact hh))

theorem processAttesterSlashing_hdr (ctx : Ctx) (s : BeaconState P f) (as : AttesterSlashing P f) :
    Ok (JauneConsensus.processAttesterSlashing ctx s as) (hdrEq.R s) := by
  unfold JauneConsensus.processAttesterSlashing; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processAttesterSlashing_hdr _ _ _) $h; exact hh))

set_option maxHeartbeats 4000000 in
theorem processAttestation_hdr (ctx : Ctx) (s : BeaconState P f) (a : Attestation P f) :
    Ok (JauneConsensus.processAttestation ctx s a) (hdrEq.R s) := by
  unfold JauneConsensus.processAttestation; jvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processAttestation_hdr _ _ _) $h; exact hh))

theorem processVoluntaryExit_hdr (ctx : Ctx) (s : BeaconState P f) (sve : SignedVoluntaryExit) :
    Ok (JauneConsensus.processVoluntaryExit ctx s sve) (hdrEq.R s) := by
  unfold JauneConsensus.processVoluntaryExit; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processVoluntaryExit_hdr _ _ _) $h; exact hh))

theorem processBlsToExecutionChange_hdr (ctx : Ctx) (s : BeaconState P f) (sac : SignedBLSToExecutionChange) :
    Ok (JauneConsensus.processBlsToExecutionChange ctx s sac) (hdrEq.R s) := by
  unfold JauneConsensus.processBlsToExecutionChange; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processBlsToExecutionChange_hdr _ _ _) $h; exact hh))

theorem processDepositRequest_hdr (s : BeaconState P f) (dr : DepositRequest) :
    Ok (JauneConsensus.processDepositRequest s dr) (hdrEq.R s) := by
  unfold JauneConsensus.processDepositRequest; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processDepositRequest_hdr _ _) $h; exact hh))

theorem processWithdrawalRequest_hdr (cfg : Config) (s : BeaconState P f) (wr : WithdrawalRequest) :
    Ok (JauneConsensus.processWithdrawalRequest cfg s wr) (hdrEq.R s) := by
  unfold JauneConsensus.processWithdrawalRequest; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processWithdrawalRequest_hdr _ _ _) $h; exact hh))

theorem processConsolidationRequest_hdr (cfg : Config) (s : BeaconState P f) (cr : ConsolidationRequest) :
    Ok (JauneConsensus.processConsolidationRequest cfg s cr) (hdrEq.R s) := by
  unfold JauneConsensus.processConsolidationRequest; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processConsolidationRequest_hdr _ _ _) $h; exact hh))

set_option maxHeartbeats 2000000 in
theorem processOperations_hdr (ctx : Ctx) (s : BeaconState P f) (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processOperations ctx s body) (hdrEq.R s) := by
  unfold JauneConsensus.processOperations; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processOperations_hdr _ _ _) $h; exact hh))

theorem processBlockHeader_hdr (s : BeaconState P f) (blk : BeaconBlock P f) :
    Ok (JauneConsensus.processBlockHeader s blk) (hdrEq.R s) := by
  unfold JauneConsensus.processBlockHeader; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processBlockHeader_hdr _ _) $h; exact hh))

theorem processRandao_hdr (ctx : Ctx) (s : BeaconState P f) (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processRandao ctx s body) (hdrEq.R s) := by
  unfold JauneConsensus.processRandao; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processRandao_hdr _ _ _) $h; exact hh))

theorem processEth1Data_hdr (s : BeaconState P f) (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processEth1Data s body) (hdrEq.R s) := by
  unfold JauneConsensus.processEth1Data; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processEth1Data_hdr _ _) $h; exact hh))

set_option maxHeartbeats 4000000 in
theorem processSyncAggregate_hdr (ctx : Ctx) (s : BeaconState P f) (sa : SyncAggregate P) :
    Ok (JauneConsensus.processSyncAggregate ctx s sa) (hdrEq.R s) := by
  unfold JauneConsensus.processSyncAggregate; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processSyncAggregate_hdr _ _ _) $h; exact hh))

set_option maxHeartbeats 2000000 in
theorem processWithdrawals_hdr (s : BeaconState P f) (pl : ExecutionPayload P) :
    Ok (JauneConsensus.processWithdrawals s pl) (hdrEq.R s) := by
  unfold JauneConsensus.processWithdrawals; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processWithdrawals_hdr _ _) $h; exact hh))

set_option maxHeartbeats 4000000 in
theorem weighJustificationAndFinalization_hdr (s : BeaconState P f) (t p c : Gwei) :
    Ok (JauneConsensus.weighJustificationAndFinalization s t p c) (hdrEq.R s) := by
  unfold JauneConsensus.weighJustificationAndFinalization; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (weighJustificationAndFinalization_hdr _ _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (weighJustificationAndFinalization_hdr _ _ _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (weighJustificationAndFinalization_hdr _ _ _ _); exact (show HdrEq _ _ from rfl)))

set_option maxHeartbeats 4000000 in
theorem processJustificationAndFinalization_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processJustificationAndFinalization cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processJustificationAndFinalization; jvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processJustificationAndFinalization_hdr _ _) $h; exact hh))

set_option maxHeartbeats 4000000 in
theorem processInactivityUpdates_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processInactivityUpdates cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processInactivityUpdates; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processInactivityUpdates_hdr _ _) $h; exact hh))

theorem processRewardsAndPenalties_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processRewardsAndPenalties cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processRewardsAndPenalties; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processRewardsAndPenalties_hdr _ _) $h; exact hh))

theorem processRegistryUpdatesElectra_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processRegistryUpdatesElectra cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processRegistryUpdatesElectra; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processRegistryUpdatesElectra_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (processRegistryUpdatesElectra_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (processRegistryUpdatesElectra_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem processRegistryUpdatesDeneb_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processRegistryUpdatesDeneb cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processRegistryUpdatesDeneb; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processRegistryUpdatesDeneb_hdr _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (processRegistryUpdatesDeneb_hdr _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (processRegistryUpdatesDeneb_hdr _ _); exact (show HdrEq _ _ from rfl)))

theorem processRegistryUpdates_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processRegistryUpdates cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processRegistryUpdates; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processRegistryUpdates_hdr _ _) $h; exact hh))

set_option maxHeartbeats 4000000 in
theorem processSlashings_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processSlashings cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processSlashings; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processSlashings_hdr _ _) $h; exact hh))

theorem processEth1DataReset_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processEth1DataReset cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processEth1DataReset; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processEth1DataReset_hdr _ _) $h; exact hh))

theorem applyPendingDeposit_hdr (ctx : Ctx) (s : BeaconState P f) (d : PendingDeposit) :
    Ok (JauneConsensus.applyPendingDeposit ctx s d) (hdrEq.R s) := by
  unfold JauneConsensus.applyPendingDeposit; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (applyPendingDeposit_hdr _ _ _) $h; exact hh))

local macro_rules
  | `(tactic| hdr_tail) =>
    `(tactic| first
      | exact (applyPendingDeposit_hdr _ _ _)
      | (refine StepRel.ok_rebase hdrEq ?_ (applyPendingDeposit_hdr _ _ _); exact (show HdrEq _ _ from rfl)))

section PendingDeposits

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRel.forIn_array_rel _ (fun x => x.2.2.2.2) ?_ _ _ $h; intro _ _; gvcg))

set_option maxHeartbeats 4000000 in
theorem processPendingDeposits_hdr (ctx : Ctx) (s : BeaconState P f) :
    Ok (JauneConsensus.processPendingDeposits ctx s) (hdrEq.R s) := by
  unfold JauneConsensus.processPendingDeposits; gvcg
  all_goals hdr_tail

end PendingDeposits

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processPendingDeposits_hdr _ _) $h; exact hh))

theorem processPendingConsolidations_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processPendingConsolidations cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processPendingConsolidations; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processPendingConsolidations_hdr _ _) $h; exact hh))

theorem processEffectiveBalanceUpdates_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processEffectiveBalanceUpdates cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processEffectiveBalanceUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processEffectiveBalanceUpdates_hdr _ _) $h; exact hh))

theorem processSlashingsReset_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processSlashingsReset cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processSlashingsReset; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processSlashingsReset_hdr _ _) $h; exact hh))

theorem processRandaoMixesReset_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processRandaoMixesReset cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processRandaoMixesReset; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processRandaoMixesReset_hdr _ _) $h; exact hh))

theorem processHistoricalSummariesUpdate_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processHistoricalSummariesUpdate cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processHistoricalSummariesUpdate; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processHistoricalSummariesUpdate_hdr _ _) $h; exact hh))

theorem processParticipationFlagUpdates_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processParticipationFlagUpdates cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processParticipationFlagUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processParticipationFlagUpdates_hdr _ _) $h; exact hh))

theorem processSyncCommitteeUpdates_hdr (ctx : Ctx) (s : BeaconState P f) :
    Ok (JauneConsensus.processSyncCommitteeUpdates ctx s) (hdrEq.R s) := by
  unfold JauneConsensus.processSyncCommitteeUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processSyncCommitteeUpdates_hdr _ _) $h; exact hh))

theorem processProposerLookahead_hdr (cfg : Config) (s : BeaconState P f) :
    Ok (JauneConsensus.processProposerLookahead cfg s) (hdrEq.R s) := by
  unfold JauneConsensus.processProposerLookahead; gvcg
  all_goals hdr_tail

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processProposerLookahead_hdr _ _) $h; exact hh))


/-- `process_slot` with its two hashes abstracted: the proof never meets `hash_tree_root` of a
state. -/
def processSlotHF (h₁ : BeaconState P f → Root) (h₂ : BeaconBlockHeader → Root)
    (state : BeaconState P f) : M (BeaconState P f) := do
  let slotsPerHistoricalRoot ← u64 P.SLOTS_PER_HISTORICAL_ROOT "SLOTS_PER_HISTORICAL_ROOT"
  let i := (← state.slot.mod? slotsPerHistoricalRoot "process_slot: slot % SLOTS_PER_HISTORICAL_ROOT").toNat
  let previousStateRoot : Root := h₁ state
  let state := { state with
    state_roots := ← state.state_roots.set i previousStateRoot "process_slot: state_roots" }
  let state :=
    if B256.beq state.latest_block_header.state_root (0 : B256) then
      { state with latest_block_header :=
          { state.latest_block_header with state_root := previousStateRoot } }
    else state
  let previousBlockRoot : Root := h₂ state.latest_block_header
  pure { state with
    block_roots := ← state.block_roots.set i previousBlockRoot "process_slot: block_roots" }

theorem processSlot_eqF (s : BeaconState P f) :
    JauneConsensus.processSlot s = processSlotHF Ssz.hashTreeRoot Ssz.hashTreeRoot s := rfl

theorem processSlotHF_hdr (h₁ : BeaconState P f → Root) (h₂ : BeaconBlockHeader → Root)
    (s : BeaconState P f) : Ok (processSlotHF h₁ h₂ s) (hdrEq.R s) := by
  intro s' h
  unfold processSlotHF at h
  repeat (obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h)
  cases h
  show HdrEq _ _
  unfold HdrEq
  split <;> rfl

theorem processSlot_hdr (s : BeaconState P f) :
    Ok (JauneConsensus.processSlot s) (hdrEq.R s) := by
  rw [processSlot_eqF]; exact processSlotHF_hdr _ _ s

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
  have f14 : HdrEq x13 s' := by
    split at h
    · exact processProposerLookahead_hdr _ _ _ h
    · cases h; rfl
  exact hdrEq.trans (processEffectiveBalanceUpdates_hdr _ _ _ h8) <|
    hdrEq.trans (processSlashingsReset_hdr _ _ _ h9) <|
    hdrEq.trans (processRandaoMixesReset_hdr _ _ _ h10) <|
    hdrEq.trans (processHistoricalSummariesUpdate_hdr _ _ _ h11) <|
    hdrEq.trans (processParticipationFlagUpdates_hdr _ _ _ h12) <|
    hdrEq.trans (processSyncCommitteeUpdates_hdr _ _ _ h13) f14))

/-- `process_epoch` keeps `latest_execution_payload_header`. -/
theorem processEpoch_hdr (ctx : Ctx) (s : BeaconState P f) :
    Ok (processEpoch ctx s) (hdrEq.R s) := by
  intro s' h
  unfold processEpoch at h
  obtain ⟨x1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x6, h6, h⟩ := bind_eq_ok_iff.mp h
  have f6 : HdrEq s x6 :=
    hdrEq.trans (processJustificationAndFinalization_hdr _ _ _ h1) <|
    hdrEq.trans (processInactivityUpdates_hdr _ _ _ h2) <|
    hdrEq.trans (processRewardsAndPenalties_hdr _ _ _ h3) <|
    hdrEq.trans (processRegistryUpdates_hdr _ _ _ h4) <|
    hdrEq.trans (processSlashings_hdr _ _ _ h5) (processEth1DataReset_hdr _ _ _ h6)
  simp only [] at h
  split at h
  · obtain ⟨y7, h7a, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x7, h7, h⟩ := bind_eq_ok_iff.mp h
    have f7 : HdrEq x6 x7 := hdrEq.trans (processPendingDeposits_hdr _ _ _ h7a)
      (processPendingConsolidations_hdr _ _ _ h7)
    refine hdrEq.trans f6 (hdrEq.trans f7 ?_)
    epoch_tail
  · obtain ⟨x7, h7, h⟩ := bind_eq_ok_iff.mp h
    cases h7
    refine hdrEq.trans f6 ?_
    epoch_tail

theorem range_forIn_inv' {β : Type} (I : β → Prop) {r : Std.Legacy.Range} {init out : β}
    {body : Nat → β → M (ForInStep β)} (hb : ∀ a b x, I b → body a b = .ok x → I x.value)
    (h : forIn r init body = .ok out) (hI : I init) : I out := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact list_forIn_rel (fun a b => I a → I b) (fun _ h => h) (fun _ _ _ h1 h2 x => h2 (h1 x))
    body (fun a b x hx hIb => hb a b x hIb hx) _ init out h hI

/-- `process_slots` with any epoch function keeping the header keeps the header. -/
theorem processSlotsWith_hdr {pe : BeaconState P f → M (BeaconState P f)}
    (hE : ∀ a, Ok (pe a) (hdrEq.R a)) {s s' : BeaconState P f} {slot : Slot}
    (h : processSlotsWith pe s slot = .ok s') :
    s'.latest_execution_payload_header = s.latest_execution_payload_header := by
  unfold processSlotsWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine range_forIn_inv' (fun m : BeaconState P f => m.latest_execution_payload_header =
    s.latest_execution_payload_header) (fun a b x hb hx => ?_) hout rfl
  obtain ⟨st1, h1, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨next, hn, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨r, hr, hx⟩ := bind_eq_ok_iff.mp hx
  have f1 : st1.latest_execution_payload_header = b.latest_execution_payload_header :=
    processSlot_hdr _ _ h1
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
theorem processSlots_header {ctx : Ctx} {s s' : BeaconState P f} {slot : Slot}
    (h : processSlots ctx s slot = .ok s') :
    s'.latest_execution_payload_header = s.latest_execution_payload_header :=
  processSlotsWith_hdr (fun a => processEpoch_hdr ctx a) h

section ExecPayload

local macro_rules | `(tactic| gstep_close) => `(tactic| rfl)

/-- `process_execution_payload` writes the payload's header. -/
theorem processExecutionPayload_header (ctx : Ctx) (s : BeaconState P f)
    (body : BeaconBlockBody P f) :
    Ok (processExecutionPayload ctx s body) (fun s' =>
      s'.latest_execution_payload_header = ExecutionPayload.toHeader body.execution_payload) := by
  unfold processExecutionPayload; gvcg

end ExecPayload

/-- **`process_block` writes `latest_execution_payload_header` once, to the payload's header**
(in `process_execution_payload`); the phases after it keep it. -/
theorem processBlock_header {ctx : Ctx} {s s' : BeaconState P f} {blk : BeaconBlock P f}
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
  exact (hdrEq.trans (processRandao_hdr _ _ _ _ h4) (hdrEq.trans (processEth1Data_hdr _ _ _ h5)
    (hdrEq.trans (processOperations_hdr _ _ _ _ h6) (processSyncAggregate_hdr _ _ _ _ h)))).trans e3

/-- `state_transition` is `process_slots` then `process_block` (and the two checks). -/
theorem stateTransition_split {ctx : Ctx} {s s' : BeaconState P f} {sb : SignedBeaconBlock P f}
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
theorem stateTransition_header {ctx : Ctx} {s s' : BeaconState P f} {sb : SignedBeaconBlock P f}
    {vr : Bool} (h : stateTransition ctx s sb vr = .ok s') :
    s'.latest_execution_payload_header =
      ExecutionPayload.toHeader sb.message.body.execution_payload := by
  obtain ⟨m, -, hb⟩ := stateTransition_split h
  exact processBlock_header hb

/-- The crossing's block at the fork slot: the signature check, `process_block`, the state root. -/
theorem atSlot_processBlock {ctx : Ctx} {bls : Bool} {s s' : BeaconState P f}
    {sb : SignedBeaconBlock P f}
    (h : (do require (← verifyBlockSignature bls s sb) "state_transition: verify_block_signature"
             let s ← processBlock ctx s sb.message
             require (B256.beq sb.message.state_root (Ssz.hashTreeRoot s))
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
theorem engineVerdict_head {cfg : ChainConfig} {cf : CFork} {exec exec' : BlockChain}
    {g : CFork} (hg : g.atLeast .electra = true) {blk : BeaconBlock P g}
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
    ∃ req : NewPayloadRequest P, engineVerdict cfg s'.fork s.exec req = .ok s'.exec ∧
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
theorem crossFromFulu_header {ctx : Ctx} {pre : JauneConsensus.BeaconState P .fulu}
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
