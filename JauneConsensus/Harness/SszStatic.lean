import JauneConsensus.Containers
import JauneConsensus.Harness.SszGeneric

/-!
# `ssz_static` case checks (harness only)

`tests/formats/ssz_static/core.md` (`consensus-specs` `v1.6.1`): for a container type named by
the handler, `serialized` must decode, re-encode to the same bytes, have the
`roots.yaml: root` hash-tree-root, and equal `value.yaml`. The checks run the library's
containers (`JauneConsensus/Containers.lean`) for the case's preset and fork.
-/

namespace JauneConsensus.Harness
open Yaml

yaml_container Fork [previous_version, current_version, epoch]
yaml_container ForkData [current_version, genesis_validators_root]
yaml_container Checkpoint [epoch, root]
yaml_container Validator [pubkey, withdrawal_credentials, effective_balance, slashed, activation_eligibility_epoch, activation_epoch, exit_epoch, withdrawable_epoch]
yaml_container AttestationData [slot, index, beacon_block_root, source, target]
yaml_container IndexedAttestation (P : Preset) (f : CFork) [attesting_indices, data, signature]
yaml_container PendingAttestation (P : Preset) [aggregation_bits, data, inclusion_delay, proposer_index]
yaml_container Eth1Data [deposit_root, deposit_count, block_hash]
yaml_container HistoricalBatch (P : Preset) [block_roots, state_roots]
yaml_container DepositMessage [pubkey, withdrawal_credentials, amount]
yaml_container DepositData [pubkey, withdrawal_credentials, amount, signature]
yaml_container BeaconBlockHeader [slot, proposer_index, parent_root, state_root, body_root]
yaml_container SigningData [object_root, domain]
yaml_container SignedBeaconBlockHeader [message, signature]
yaml_container ProposerSlashing [signed_header_1, signed_header_2]
yaml_container AttesterSlashing (P : Preset) (f : CFork) [attestation_1, attestation_2]
yaml_container Attestation (P : Preset) (f : CFork) [aggregation_bits, data, signature, committee_bits]
yaml_container Deposit [proof, data]
yaml_container VoluntaryExit [epoch, validator_index]
yaml_container SignedVoluntaryExit [message, signature]
yaml_container Eth1Block [timestamp, deposit_root, deposit_count]
yaml_container AggregateAndProof (P : Preset) (f : CFork) [aggregator_index, aggregate, selection_proof]
yaml_container SignedAggregateAndProof (P : Preset) (f : CFork) [message, signature]
yaml_container SyncAggregate (P : Preset) [sync_committee_bits, sync_committee_signature]
yaml_container SyncCommittee (P : Preset) [pubkeys, aggregate_pubkey]
yaml_container SyncCommitteeMessage [slot, beacon_block_root, validator_index, signature]
yaml_container SyncCommitteeContribution (P : Preset) [slot, beacon_block_root, subcommittee_index, aggregation_bits, signature]
yaml_container ContributionAndProof (P : Preset) [aggregator_index, contribution, selection_proof]
yaml_container SignedContributionAndProof (P : Preset) [message, signature]
yaml_container SyncAggregatorSelectionData [slot, subcommittee_index]
yaml_container PowBlock [block_hash, parent_hash, total_difficulty]
yaml_container Withdrawal [index, validator_index, address, amount]
yaml_container BLSToExecutionChange [validator_index, from_bls_pubkey, to_execution_address]
yaml_container SignedBLSToExecutionChange [message, signature]
yaml_container HistoricalSummary [block_summary_root, state_summary_root]
yaml_container ExecutionPayload (P : Preset) [parent_hash, fee_recipient, state_root, receipts_root, logs_bloom, prev_randao, block_number, gas_limit, gas_used, timestamp, extra_data, base_fee_per_gas, block_hash, transactions, withdrawals, blob_gas_used, excess_blob_gas]
yaml_container ExecutionPayloadHeader (P : Preset) [parent_hash, fee_recipient, state_root, receipts_root, logs_bloom, prev_randao, block_number, gas_limit, gas_used, timestamp, extra_data, base_fee_per_gas, block_hash, transactions_root, withdrawals_root, blob_gas_used, excess_blob_gas]
yaml_container BlobIdentifier [block_root, index]
yaml_container BlobSidecar (P : Preset) [index, blob, kzg_commitment, kzg_proof, signed_block_header, kzg_commitment_inclusion_proof]
yaml_container PendingDeposit [pubkey, withdrawal_credentials, amount, signature, slot]
yaml_container PendingPartialWithdrawal [validator_index, amount, withdrawable_epoch]
yaml_container PendingConsolidation [source_index, target_index]
yaml_container DepositRequest [pubkey, withdrawal_credentials, amount, signature, index]
yaml_container WithdrawalRequest [source_address, validator_pubkey, amount]
yaml_container ConsolidationRequest [source_address, source_pubkey, target_pubkey]
yaml_container ExecutionRequests (P : Preset) [deposits, withdrawals, consolidations]
yaml_container SingleAttestation [committee_index, attester_index, data, signature]
yaml_container BeaconBlockBody (P : Preset) (f : CFork) [randao_reveal, eth1_data, graffiti, proposer_slashings, attester_slashings, attestations, deposits, voluntary_exits, sync_aggregate, execution_payload, bls_to_execution_changes, blob_kzg_commitments, execution_requests]
yaml_container BeaconBlock (P : Preset) (f : CFork) [slot, proposer_index, parent_root, state_root, body]
yaml_container SignedBeaconBlock (P : Preset) (f : CFork) [message, signature]
yaml_container BeaconState (P : Preset) (f : CFork) [genesis_time, genesis_validators_root, slot, fork, latest_block_header, block_roots, state_roots, historical_roots, eth1_data, eth1_data_votes, eth1_deposit_index, validators, balances, randao_mixes, slashings, previous_epoch_participation, current_epoch_participation, justification_bits, previous_justified_checkpoint, current_justified_checkpoint, finalized_checkpoint, inactivity_scores, current_sync_committee, next_sync_committee, latest_execution_payload_header, next_withdrawal_index, next_withdrawal_validator_index, historical_summaries, deposit_requests_start_index, deposit_balance_to_consume, exit_balance_to_consume, earliest_exit_epoch, consolidation_balance_to_consume, earliest_consolidation_epoch, pending_deposits, pending_partial_withdrawals, pending_consolidations, proposer_lookahead]
yaml_container LightClientHeader (P : Preset) [beacon, execution, execution_branch]
yaml_container LightClientBootstrap (P : Preset) (f : CFork) [header, current_sync_committee, current_sync_committee_branch]
yaml_container LightClientUpdate (P : Preset) (f : CFork) [attested_header, next_sync_committee, next_sync_committee_branch, finalized_header, finality_branch, sync_aggregate, signature_slot]
yaml_container LightClientFinalityUpdate (P : Preset) (f : CFork) [attested_header, finalized_header, finality_branch, sync_aggregate, signature_slot]
yaml_container LightClientOptimisticUpdate (P : Preset) [attested_header, sync_aggregate, signature_slot]
yaml_container DataColumnSidecar (P : Preset) [index, column, kzg_commitments, kzg_proofs, signed_block_header, kzg_commitments_inclusion_proof]
yaml_container MatrixEntry (P : Preset) [cell, kzg_proof, column_index, row_index]
yaml_container DataColumnsByRootIdentifier (P : Preset) [block_root, columns]

/-- The container type of an `ssz_static` handler at a preset and fork. -/
def sszStaticChecks (P : Preset) (f : CFork) (name : String) : Option TypeChecks :=
  match name with
  | "Fork" => some (.of Fork)
  | "ForkData" => some (.of ForkData)
  | "Checkpoint" => some (.of Checkpoint)
  | "Validator" => some (.of Validator)
  | "AttestationData" => some (.of AttestationData)
  | "IndexedAttestation" => some (.of (IndexedAttestation P f))
  | "PendingAttestation" => some (.of (PendingAttestation P))
  | "Eth1Data" => some (.of Eth1Data)
  | "HistoricalBatch" => some (.of (HistoricalBatch P))
  | "DepositMessage" => some (.of DepositMessage)
  | "DepositData" => some (.of DepositData)
  | "BeaconBlockHeader" => some (.of BeaconBlockHeader)
  | "SigningData" => some (.of SigningData)
  | "SignedBeaconBlockHeader" => some (.of SignedBeaconBlockHeader)
  | "ProposerSlashing" => some (.of ProposerSlashing)
  | "AttesterSlashing" => some (.of (AttesterSlashing P f))
  | "Attestation" => some (.of (Attestation P f))
  | "Deposit" => some (.of Deposit)
  | "VoluntaryExit" => some (.of VoluntaryExit)
  | "SignedVoluntaryExit" => some (.of SignedVoluntaryExit)
  | "Eth1Block" => some (.of Eth1Block)
  | "AggregateAndProof" => some (.of (AggregateAndProof P f))
  | "SignedAggregateAndProof" => some (.of (SignedAggregateAndProof P f))
  | "SyncAggregate" => some (.of (SyncAggregate P))
  | "SyncCommittee" => some (.of (SyncCommittee P))
  | "SyncCommitteeMessage" => some (.of SyncCommitteeMessage)
  | "SyncCommitteeContribution" => some (.of (SyncCommitteeContribution P))
  | "ContributionAndProof" => some (.of (ContributionAndProof P))
  | "SignedContributionAndProof" => some (.of (SignedContributionAndProof P))
  | "SyncAggregatorSelectionData" => some (.of SyncAggregatorSelectionData)
  | "PowBlock" => some (.of PowBlock)
  | "Withdrawal" => some (.of Withdrawal)
  | "BLSToExecutionChange" => some (.of BLSToExecutionChange)
  | "SignedBLSToExecutionChange" => some (.of SignedBLSToExecutionChange)
  | "HistoricalSummary" => some (.of HistoricalSummary)
  | "ExecutionPayload" => some (.of (ExecutionPayload P))
  | "ExecutionPayloadHeader" => some (.of (ExecutionPayloadHeader P))
  | "BlobIdentifier" => some (.of BlobIdentifier)
  | "BlobSidecar" => some (.of (BlobSidecar P))
  | "PendingDeposit" => some (.of PendingDeposit)
  | "PendingPartialWithdrawal" => some (.of PendingPartialWithdrawal)
  | "PendingConsolidation" => some (.of PendingConsolidation)
  | "DepositRequest" => some (.of DepositRequest)
  | "WithdrawalRequest" => some (.of WithdrawalRequest)
  | "ConsolidationRequest" => some (.of ConsolidationRequest)
  | "ExecutionRequests" => some (.of (ExecutionRequests P))
  | "SingleAttestation" => some (.of SingleAttestation)
  | "BeaconBlockBody" => some (.of (BeaconBlockBody P f))
  | "BeaconBlock" => some (.of (BeaconBlock P f))
  | "SignedBeaconBlock" => some (.of (SignedBeaconBlock P f))
  | "BeaconState" => some (.of (BeaconState P f))
  | "LightClientHeader" => some (.of (LightClientHeader P))
  | "LightClientBootstrap" => some (.of (LightClientBootstrap P f))
  | "LightClientUpdate" => some (.of (LightClientUpdate P f))
  | "LightClientFinalityUpdate" => some (.of (LightClientFinalityUpdate P f))
  | "LightClientOptimisticUpdate" => some (.of (LightClientOptimisticUpdate P))
  | "DataColumnSidecar" => some (.of (DataColumnSidecar P))
  | "MatrixEntry" => some (.of (MatrixEntry P))
  | "DataColumnsByRootIdentifier" => some (.of (DataColumnsByRootIdentifier P))

  | _ => none

end JauneConsensus.Harness
