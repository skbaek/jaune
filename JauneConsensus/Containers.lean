import JauneConsensus.SSZ.Container
import JauneConsensus.Preset
import JauneConsensus.Fork

/-!
# Consensus containers, Deneb to Fulu

The SSZ containers of `ethereum/consensus-specs` (`v1.6.1`, and `v1.7.0-beta.4` for
`SszNewPayloadRequest` and the Fulu partial-column containers) that the Electra and Fulu vectors
use,
each declared once and indexed by the preset `P` (list and vector sizes) and, where the type
changed between forks, by the fork `f : CFork`:

* a size that changed is a `Nat` function of the fork inside the field's type (for example
  `Attestation.aggregation_bits : Bitlist (attestationBitsLimit P f)`, which is
  `MAX_VALIDATORS_PER_COMMITTEE` before Electra and that times `MAX_COMMITTEES_PER_SLOT` from
  Electra on);
* a field a fork introduced is `Gated (f.atLeast g) T`: for a concrete fork the gate reduces by
  `rfl` to `T` or to an absent field, which contributes no bytes and no Merkle leaf.

Each container cites the spec file of its latest definition at or before Fulu. Field names and
order follow the spec exactly (they are the SSZ field order).
-/

namespace JauneConsensus


/-! ## Custom types (`specs/*/beacon-chain.md`, "Custom types") -/

abbrev Slot := U64
abbrev Epoch := U64
abbrev CommitteeIndex := U64
abbrev ValidatorIndex := U64
abbrev Gwei := U64
abbrev WithdrawalIndex := U64
abbrev BlobIndex := U64
abbrev ColumnIndex := U64
abbrev RowIndex := U64
/-- `Root`, `Bytes32`, `Hash32`, `Domain`: a 32-byte chunk. -/
abbrev Root := Jaune.B256
abbrev Bytes32 := Jaune.B256
abbrev Hash32 := Jaune.B256
abbrev Domain := Jaune.B256
abbrev Version := SszVector UInt8 4
abbrev BLSPubkey := SszVector UInt8 48
abbrev BLSSignature := SszVector UInt8 96
abbrev KZGCommitment := SszVector UInt8 48
abbrev KZGProof := SszVector UInt8 48
/-- `ExecutionAddress` is Jaune's execution-layer address type (outcome O7). -/
abbrev ExecutionAddress := Jaune.Adr
abbrev ParticipationFlags := U8

/-! ## Constants -/

/-- `JUSTIFICATION_BITS_LENGTH` (`specs/phase0/beacon-chain.md`). -/
def JUSTIFICATION_BITS_LENGTH : Nat := 4
/-- `DEPOSIT_CONTRACT_TREE_DEPTH` (`specs/phase0/beacon-chain.md`). -/
def DEPOSIT_CONTRACT_TREE_DEPTH : Nat := 32
/-- `SYNC_COMMITTEE_SUBNET_COUNT` (`specs/altair/validator.md`). -/
def SYNC_COMMITTEE_SUBNET_COUNT : Nat := 4
/-- `BYTES_PER_FIELD_ELEMENT` (`specs/deneb/polynomial-commitments.md`). -/
def BYTES_PER_FIELD_ELEMENT : Nat := 32

/-! ## Fork-dependent sizes -/

/-- `Attestation.aggregation_bits` and `IndexedAttestation.attesting_indices` limit:
`MAX_VALIDATORS_PER_COMMITTEE` (phase0) or `MAX_VALIDATORS_PER_COMMITTEE *
MAX_COMMITTEES_PER_SLOT` (`specs/electra/beacon-chain.md`, EIP-7549). -/
def attestationBitsLimit (P : Preset) (f : CFork) : Nat :=
  if f.atLeast .electra then P.MAX_VALIDATORS_PER_COMMITTEE * P.MAX_COMMITTEES_PER_SLOT
  else P.MAX_VALIDATORS_PER_COMMITTEE

/-- `BeaconBlockBody.attester_slashings` limit: `MAX_ATTESTER_SLASHINGS`, or
`MAX_ATTESTER_SLASHINGS_ELECTRA` from Electra. -/
def maxAttesterSlashings (P : Preset) (f : CFork) : Nat :=
  if f.atLeast .electra then P.MAX_ATTESTER_SLASHINGS_ELECTRA else P.MAX_ATTESTER_SLASHINGS

/-- `BeaconBlockBody.attestations` limit: `MAX_ATTESTATIONS`, or `MAX_ATTESTATIONS_ELECTRA`. -/
def maxAttestations (P : Preset) (f : CFork) : Nat :=
  if f.atLeast .electra then P.MAX_ATTESTATIONS_ELECTRA else P.MAX_ATTESTATIONS

/-- `floorlog2` of the light-client generalized indices: `FINALIZED_ROOT_GINDEX` (105) before
Electra, `FINALIZED_ROOT_GINDEX_ELECTRA` (169) from Electra (`specs/electra/light-client/
sync-protocol.md`). -/
def finalityBranchDepth (f : CFork) : Nat := if f.atLeast .electra then 7 else 6
/-- `floorlog2(CURRENT_SYNC_COMMITTEE_GINDEX)`: 54 before Electra, 86 from Electra; and
`NEXT_SYNC_COMMITTEE_GINDEX`: 55 and 87. Both give the same depth. -/
def syncCommitteeBranchDepth (f : CFork) : Nat := if f.atLeast .electra then 6 else 5
/-- `floorlog2(EXECUTION_PAYLOAD_GINDEX)` with `EXECUTION_PAYLOAD_GINDEX = 25`
(`specs/capella/light-client/sync-protocol.md`). -/
def executionBranchDepth : Nat := 4

/-! ## phase0 -/

/-- `specs/phase0/beacon-chain.md` -/
ssz_container Fork where
  previous_version : Version
  current_version : Version
  epoch : Epoch

/-- `specs/phase0/beacon-chain.md` -/
ssz_container ForkData where
  current_version : Version
  genesis_validators_root : Root

/-- `specs/phase0/beacon-chain.md` -/
ssz_container Checkpoint where
  epoch : Epoch
  root : Root

/-- `specs/phase0/beacon-chain.md` -/
ssz_container Validator where
  pubkey : BLSPubkey
  withdrawal_credentials : Bytes32
  effective_balance : Gwei
  slashed : Bool
  activation_eligibility_epoch : Epoch
  activation_epoch : Epoch
  exit_epoch : Epoch
  withdrawable_epoch : Epoch

/-- `specs/phase0/beacon-chain.md` -/
ssz_container AttestationData where
  slot : Slot
  index : CommitteeIndex
  beacon_block_root : Root
  source : Checkpoint
  target : Checkpoint

/-- `specs/phase0/beacon-chain.md` (`IndexedAttestation`); the limit of `attesting_indices`
grows at Electra (`specs/electra/beacon-chain.md`). -/
ssz_container IndexedAttestation (P : Preset) (f : CFork) where
  attesting_indices : (SszList ValidatorIndex (attestationBitsLimit P f))
  data : AttestationData
  signature : BLSSignature

/-- `specs/phase0/beacon-chain.md` -/
ssz_container PendingAttestation (P : Preset) where
  aggregation_bits : (Bitlist P.MAX_VALIDATORS_PER_COMMITTEE)
  data : AttestationData
  inclusion_delay : Slot
  proposer_index : ValidatorIndex

/-- `specs/phase0/beacon-chain.md` -/
ssz_container Eth1Data where
  deposit_root : Root
  deposit_count : U64
  block_hash : Hash32

/-- `specs/phase0/beacon-chain.md` -/
ssz_container HistoricalBatch (P : Preset) where
  block_roots : (SszVector Root P.SLOTS_PER_HISTORICAL_ROOT)
  state_roots : (SszVector Root P.SLOTS_PER_HISTORICAL_ROOT)

/-- `specs/phase0/beacon-chain.md` -/
ssz_container DepositMessage where
  pubkey : BLSPubkey
  withdrawal_credentials : Bytes32
  amount : Gwei

/-- `specs/phase0/beacon-chain.md` -/
ssz_container DepositData where
  pubkey : BLSPubkey
  withdrawal_credentials : Bytes32
  amount : Gwei
  signature : BLSSignature

/-- `specs/phase0/beacon-chain.md` -/
ssz_container BeaconBlockHeader where
  slot : Slot
  proposer_index : ValidatorIndex
  parent_root : Root
  state_root : Root
  body_root : Root

/-- `specs/phase0/beacon-chain.md` -/
ssz_container SigningData where
  object_root : Root
  domain : Domain

/-- `specs/phase0/beacon-chain.md` -/
ssz_container SignedBeaconBlockHeader where
  message : BeaconBlockHeader
  signature : BLSSignature

/-- `specs/phase0/beacon-chain.md` -/
ssz_container ProposerSlashing where
  signed_header_1 : SignedBeaconBlockHeader
  signed_header_2 : SignedBeaconBlockHeader

/-- `specs/phase0/beacon-chain.md`; Electra's `IndexedAttestation` sizes
(`specs/electra/beacon-chain.md`). -/
ssz_container AttesterSlashing (P : Preset) (f : CFork) where
  attestation_1 : (IndexedAttestation P f)
  attestation_2 : (IndexedAttestation P f)

/-- `specs/electra/beacon-chain.md` (`Attestation`, EIP-7549): `aggregation_bits` spans every
committee of the slot and `committee_bits` names them; before Electra
(`specs/phase0/beacon-chain.md`) there is one committee and no `committee_bits`. -/
ssz_container Attestation (P : Preset) (f : CFork) where
  aggregation_bits : (Bitlist (attestationBitsLimit P f))
  data : AttestationData
  signature : BLSSignature
  committee_bits : (Gated (f.atLeast .electra) (Bitvector P.MAX_COMMITTEES_PER_SLOT))

/-- `specs/phase0/beacon-chain.md` -/
ssz_container Deposit where
  proof : (SszVector Bytes32 (DEPOSIT_CONTRACT_TREE_DEPTH + 1))
  data : DepositData

/-- `specs/phase0/beacon-chain.md` -/
ssz_container VoluntaryExit where
  epoch : Epoch
  validator_index : ValidatorIndex

/-- `specs/phase0/beacon-chain.md` -/
ssz_container SignedVoluntaryExit where
  message : VoluntaryExit
  signature : BLSSignature

/-- `specs/phase0/validator.md` -/
ssz_container Eth1Block where
  timestamp : U64
  deposit_root : Root
  deposit_count : U64

/-- `specs/phase0/validator.md`, with Electra's `Attestation` (`specs/electra/validator.md`). -/
ssz_container AggregateAndProof (P : Preset) (f : CFork) where
  aggregator_index : ValidatorIndex
  aggregate : (Attestation P f)
  selection_proof : BLSSignature

/-- `specs/phase0/validator.md`, `specs/electra/validator.md` -/
ssz_container SignedAggregateAndProof (P : Preset) (f : CFork) where
  message : (AggregateAndProof P f)
  signature : BLSSignature

/-! ## Altair -/

/-- `specs/altair/beacon-chain.md` -/
ssz_container SyncAggregate (P : Preset) where
  sync_committee_bits : (Bitvector P.SYNC_COMMITTEE_SIZE)
  sync_committee_signature : BLSSignature

/-- `specs/altair/beacon-chain.md` -/
ssz_container SyncCommittee (P : Preset) where
  pubkeys : (SszVector BLSPubkey P.SYNC_COMMITTEE_SIZE)
  aggregate_pubkey : BLSPubkey

/-- `specs/altair/validator.md` -/
ssz_container SyncCommitteeMessage where
  slot : Slot
  beacon_block_root : Root
  validator_index : ValidatorIndex
  signature : BLSSignature

/-- `specs/altair/validator.md` -/
ssz_container SyncCommitteeContribution (P : Preset) where
  slot : Slot
  beacon_block_root : Root
  subcommittee_index : U64
  aggregation_bits : (Bitvector (P.SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT))
  signature : BLSSignature

/-- `specs/altair/validator.md` -/
ssz_container ContributionAndProof (P : Preset) where
  aggregator_index : ValidatorIndex
  contribution : (SyncCommitteeContribution P)
  selection_proof : BLSSignature

/-- `specs/altair/validator.md` -/
ssz_container SignedContributionAndProof (P : Preset) where
  message : (ContributionAndProof P)
  signature : BLSSignature

/-- `specs/altair/validator.md` -/
ssz_container SyncAggregatorSelectionData where
  slot : Slot
  subcommittee_index : U64

/-! ## Bellatrix to Deneb -/

/-- `specs/bellatrix/fork-choice.md` -/
ssz_container PowBlock where
  block_hash : Hash32
  parent_hash : Hash32
  total_difficulty : U256

/-- `specs/capella/beacon-chain.md` -/
ssz_container Withdrawal where
  index : WithdrawalIndex
  validator_index : ValidatorIndex
  address : ExecutionAddress
  amount : Gwei

/-- `specs/capella/beacon-chain.md` -/
ssz_container BLSToExecutionChange where
  validator_index : ValidatorIndex
  from_bls_pubkey : BLSPubkey
  to_execution_address : ExecutionAddress

/-- `specs/capella/beacon-chain.md` -/
ssz_container SignedBLSToExecutionChange where
  message : BLSToExecutionChange
  signature : BLSSignature

/-- `specs/capella/beacon-chain.md` -/
ssz_container HistoricalSummary where
  block_summary_root : Root
  state_summary_root : Root

/-- `Transaction` (`specs/bellatrix/beacon-chain.md`): `ByteList[MAX_BYTES_PER_TRANSACTION]`. -/
abbrev Transaction (P : Preset) := SszList UInt8 P.MAX_BYTES_PER_TRANSACTION

/-- `specs/deneb/beacon-chain.md` (unchanged in Electra and Fulu). -/
ssz_container ExecutionPayload (P : Preset) where
  parent_hash : Hash32
  fee_recipient : ExecutionAddress
  state_root : Bytes32
  receipts_root : Bytes32
  logs_bloom : (SszVector UInt8 P.BYTES_PER_LOGS_BLOOM)
  prev_randao : Bytes32
  block_number : U64
  gas_limit : U64
  gas_used : U64
  timestamp : U64
  extra_data : (SszList UInt8 P.MAX_EXTRA_DATA_BYTES)
  base_fee_per_gas : U256
  block_hash : Hash32
  transactions : (SszList (Transaction P) P.MAX_TRANSACTIONS_PER_PAYLOAD)
  withdrawals : (SszList Withdrawal P.MAX_WITHDRAWALS_PER_PAYLOAD)
  blob_gas_used : U64
  excess_blob_gas : U64

/-- `specs/deneb/beacon-chain.md` (unchanged in Electra and Fulu). -/
ssz_container ExecutionPayloadHeader (P : Preset) where
  parent_hash : Hash32
  fee_recipient : ExecutionAddress
  state_root : Bytes32
  receipts_root : Bytes32
  logs_bloom : (SszVector UInt8 P.BYTES_PER_LOGS_BLOOM)
  prev_randao : Bytes32
  block_number : U64
  gas_limit : U64
  gas_used : U64
  timestamp : U64
  extra_data : (SszList UInt8 P.MAX_EXTRA_DATA_BYTES)
  base_fee_per_gas : U256
  block_hash : Hash32
  transactions_root : Root
  withdrawals_root : Root
  blob_gas_used : U64
  excess_blob_gas : U64

/-- `Blob` (`specs/deneb/polynomial-commitments.md`). -/
abbrev Blob (P : Preset) := SszVector UInt8 (BYTES_PER_FIELD_ELEMENT * P.FIELD_ELEMENTS_PER_BLOB)

/-- `specs/deneb/p2p-interface.md` -/
ssz_container BlobIdentifier where
  block_root : Root
  index : BlobIndex

/-- `specs/deneb/p2p-interface.md` -/
ssz_container BlobSidecar (P : Preset) where
  index : BlobIndex
  blob : (Blob P)
  kzg_commitment : KZGCommitment
  kzg_proof : KZGProof
  signed_block_header : SignedBeaconBlockHeader
  kzg_commitment_inclusion_proof : (SszVector Bytes32 P.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH)

/-! ## Electra -/

/-- `specs/electra/beacon-chain.md` -/
ssz_container PendingDeposit where
  pubkey : BLSPubkey
  withdrawal_credentials : Bytes32
  amount : Gwei
  signature : BLSSignature
  slot : Slot

/-- `specs/electra/beacon-chain.md` -/
ssz_container PendingPartialWithdrawal where
  validator_index : ValidatorIndex
  amount : Gwei
  withdrawable_epoch : Epoch

/-- `specs/electra/beacon-chain.md` -/
ssz_container PendingConsolidation where
  source_index : ValidatorIndex
  target_index : ValidatorIndex

/-- `specs/electra/beacon-chain.md` -/
ssz_container DepositRequest where
  pubkey : BLSPubkey
  withdrawal_credentials : Bytes32
  amount : Gwei
  signature : BLSSignature
  index : U64

/-- `specs/electra/beacon-chain.md` -/
ssz_container WithdrawalRequest where
  source_address : ExecutionAddress
  validator_pubkey : BLSPubkey
  amount : Gwei

/-- `specs/electra/beacon-chain.md` -/
ssz_container ConsolidationRequest where
  source_address : ExecutionAddress
  source_pubkey : BLSPubkey
  target_pubkey : BLSPubkey

/-- `specs/electra/beacon-chain.md` -/
ssz_container ExecutionRequests (P : Preset) where
  deposits : (SszList DepositRequest P.MAX_DEPOSIT_REQUESTS_PER_PAYLOAD)
  withdrawals : (SszList WithdrawalRequest P.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD)
  consolidations : (SszList ConsolidationRequest P.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD)

/-- `specs/electra/beacon-chain.md` -/
ssz_container SingleAttestation where
  committee_index : CommitteeIndex
  attester_index : ValidatorIndex
  data : AttestationData
  signature : BLSSignature

/-- `NewPayloadRequest` (`specs/electra/beacon-chain.md`), the SSZ container of the
`ssz_static` vectors from `v1.7.0-beta.4` on; named `SszNewPayloadRequest` because
`JauneConsensus.NewPayloadRequest` (`Engine.lean`) is the engine-facing form with the requests
already listed. `versioned_hashes` is Deneb's `VersionedHashes`
(`List[VersionedHash, MAX_BLOB_COMMITMENTS_PER_BLOCK]`). -/
ssz_container SszNewPayloadRequest (P : Preset) where
  execution_payload : (ExecutionPayload P)
  versioned_hashes : (SszList Bytes32 P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
  parent_beacon_block_root : Root
  execution_requests : (ExecutionRequests P)

/-! ## Blocks -/

/-- `specs/electra/beacon-chain.md` (`BeaconBlockBody`); the Deneb body
(`specs/deneb/beacon-chain.md`) has the phase0 slashing and attestation limits and no
`execution_requests`. -/
ssz_container BeaconBlockBody (P : Preset) (f : CFork) where
  randao_reveal : BLSSignature
  eth1_data : Eth1Data
  graffiti : Bytes32
  proposer_slashings : (SszList ProposerSlashing P.MAX_PROPOSER_SLASHINGS)
  attester_slashings : (SszList (AttesterSlashing P f) (maxAttesterSlashings P f))
  attestations : (SszList (Attestation P f) (maxAttestations P f))
  deposits : (SszList Deposit P.MAX_DEPOSITS)
  voluntary_exits : (SszList SignedVoluntaryExit P.MAX_VOLUNTARY_EXITS)
  sync_aggregate : (SyncAggregate P)
  execution_payload : (ExecutionPayload P)
  bls_to_execution_changes : (SszList SignedBLSToExecutionChange P.MAX_BLS_TO_EXECUTION_CHANGES)
  blob_kzg_commitments : (SszList KZGCommitment P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
  execution_requests : (Gated (f.atLeast .electra) (ExecutionRequests P))

/-- `specs/phase0/beacon-chain.md` -/
ssz_container BeaconBlock (P : Preset) (f : CFork) where
  slot : Slot
  proposer_index : ValidatorIndex
  parent_root : Root
  state_root : Root
  body : (BeaconBlockBody P f)

/-- `specs/phase0/beacon-chain.md` -/
ssz_container SignedBeaconBlock (P : Preset) (f : CFork) where
  message : (BeaconBlock P f)
  signature : BLSSignature

/-! ## State -/

/-- `specs/fulu/beacon-chain.md` (`BeaconState`). Electra's fields
(`specs/electra/beacon-chain.md`) are gated at Electra and `proposer_lookahead` at Fulu; the
Deneb state (`specs/deneb/beacon-chain.md`) has neither. -/
ssz_container BeaconState (P : Preset) (f : CFork) where
  genesis_time : U64
  genesis_validators_root : Root
  slot : Slot
  fork : Fork
  latest_block_header : BeaconBlockHeader
  block_roots : (SszVector Root P.SLOTS_PER_HISTORICAL_ROOT)
  state_roots : (SszVector Root P.SLOTS_PER_HISTORICAL_ROOT)
  historical_roots : (SszList Root P.HISTORICAL_ROOTS_LIMIT)
  eth1_data : Eth1Data
  eth1_data_votes : (SszList Eth1Data (P.EPOCHS_PER_ETH1_VOTING_PERIOD * P.SLOTS_PER_EPOCH))
  eth1_deposit_index : U64
  validators : (SszList Validator P.VALIDATOR_REGISTRY_LIMIT)
  balances : (SszList Gwei P.VALIDATOR_REGISTRY_LIMIT)
  randao_mixes : (SszVector Bytes32 P.EPOCHS_PER_HISTORICAL_VECTOR)
  slashings : (SszVector Gwei P.EPOCHS_PER_SLASHINGS_VECTOR)
  previous_epoch_participation : (SszList ParticipationFlags P.VALIDATOR_REGISTRY_LIMIT)
  current_epoch_participation : (SszList ParticipationFlags P.VALIDATOR_REGISTRY_LIMIT)
  justification_bits : (Bitvector JUSTIFICATION_BITS_LENGTH)
  previous_justified_checkpoint : Checkpoint
  current_justified_checkpoint : Checkpoint
  finalized_checkpoint : Checkpoint
  inactivity_scores : (SszList U64 P.VALIDATOR_REGISTRY_LIMIT)
  current_sync_committee : (SyncCommittee P)
  next_sync_committee : (SyncCommittee P)
  latest_execution_payload_header : (ExecutionPayloadHeader P)
  next_withdrawal_index : WithdrawalIndex
  next_withdrawal_validator_index : ValidatorIndex
  historical_summaries : (SszList HistoricalSummary P.HISTORICAL_ROOTS_LIMIT)
  deposit_requests_start_index : (Gated (f.atLeast .electra) U64)
  deposit_balance_to_consume : (Gated (f.atLeast .electra) Gwei)
  exit_balance_to_consume : (Gated (f.atLeast .electra) Gwei)
  earliest_exit_epoch : (Gated (f.atLeast .electra) Epoch)
  consolidation_balance_to_consume : (Gated (f.atLeast .electra) Gwei)
  earliest_consolidation_epoch : (Gated (f.atLeast .electra) Epoch)
  pending_deposits : (Gated (f.atLeast .electra) (SszList PendingDeposit P.PENDING_DEPOSITS_LIMIT))
  pending_partial_withdrawals :
    (Gated (f.atLeast .electra) (SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT))
  pending_consolidations :
    (Gated (f.atLeast .electra) (SszList PendingConsolidation P.PENDING_CONSOLIDATIONS_LIMIT))
  proposer_lookahead :
    (Gated (f.atLeast .fulu) (SszVector ValidatorIndex ((P.MIN_SEED_LOOKAHEAD + 1) * P.SLOTS_PER_EPOCH)))

/-! ## Light client (`specs/capella/light-client/sync-protocol.md`, branch depths from
`specs/electra/light-client/sync-protocol.md`) -/

/-- `specs/capella/light-client/sync-protocol.md` -/
ssz_container LightClientHeader (P : Preset) where
  beacon : BeaconBlockHeader
  execution : (ExecutionPayloadHeader P)
  execution_branch : (SszVector Bytes32 executionBranchDepth)

/-- `specs/altair/light-client/sync-protocol.md`, Capella header, Electra branch depth. -/
ssz_container LightClientBootstrap (P : Preset) (f : CFork) where
  header : (LightClientHeader P)
  current_sync_committee : (SyncCommittee P)
  current_sync_committee_branch : (SszVector Bytes32 (syncCommitteeBranchDepth f))

/-- `specs/altair/light-client/sync-protocol.md`, Capella header, Electra branch depths. -/
ssz_container LightClientUpdate (P : Preset) (f : CFork) where
  attested_header : (LightClientHeader P)
  next_sync_committee : (SyncCommittee P)
  next_sync_committee_branch : (SszVector Bytes32 (syncCommitteeBranchDepth f))
  finalized_header : (LightClientHeader P)
  finality_branch : (SszVector Bytes32 (finalityBranchDepth f))
  sync_aggregate : (SyncAggregate P)
  signature_slot : Slot

/-- `specs/altair/light-client/sync-protocol.md`, Capella header, Electra branch depth. -/
ssz_container LightClientFinalityUpdate (P : Preset) (f : CFork) where
  attested_header : (LightClientHeader P)
  finalized_header : (LightClientHeader P)
  finality_branch : (SszVector Bytes32 (finalityBranchDepth f))
  sync_aggregate : (SyncAggregate P)
  signature_slot : Slot

/-- `specs/altair/light-client/sync-protocol.md`, Capella header. -/
ssz_container LightClientOptimisticUpdate (P : Preset) where
  attested_header : (LightClientHeader P)
  sync_aggregate : (SyncAggregate P)
  signature_slot : Slot

/-! ## Fulu -/

/-- `Cell` (`specs/fulu/polynomial-commitments-sampling.md`). -/
abbrev Cell (P : Preset) := SszVector UInt8 (BYTES_PER_FIELD_ELEMENT * P.FIELD_ELEMENTS_PER_CELL)

/-- `specs/fulu/das-core.md` -/
ssz_container DataColumnSidecar (P : Preset) where
  index : ColumnIndex
  column : (SszList (Cell P) P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
  kzg_commitments : (SszList KZGCommitment P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
  kzg_proofs : (SszList KZGProof P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
  signed_block_header : SignedBeaconBlockHeader
  kzg_commitments_inclusion_proof : (SszVector Bytes32 P.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH)

/-- `specs/fulu/das-core.md` -/
ssz_container MatrixEntry (P : Preset) where
  cell : (Cell P)
  kzg_proof : KZGProof
  column_index : ColumnIndex
  row_index : RowIndex

/-- `specs/fulu/p2p-interface.md` -/
ssz_container DataColumnsByRootIdentifier (P : Preset) where
  block_root : Root
  columns : (SszList ColumnIndex P.NUMBER_OF_COLUMNS)

/-- `specs/fulu/partial-columns/p2p-interface.md` (`v1.7.0-beta.4`): `kzg_commitments` is
`BlobKZGCommitments`, `kzg_commitments_inclusion_proof` is `KZGCommitmentsInclusionProof`. -/
ssz_container PartialDataColumnHeader (P : Preset) where
  kzg_commitments : (SszList KZGCommitment P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
  signed_block_header : SignedBeaconBlockHeader
  kzg_commitments_inclusion_proof : (SszVector Bytes32 P.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH)

/-- `specs/fulu/partial-columns/p2p-interface.md`: `CellsBitList` is
`BitList[MAX_BLOB_COMMITMENTS_PER_BLOCK]`, `DataColumn` and `KZGProofs` are lists of that limit,
and `header` is `OptionalPartialDataColumnHeader` (`List[PartialDataColumnHeader, 1]`). -/
ssz_container PartialDataColumnSidecar (P : Preset) where
  cells_present_bitmap : (Bitlist P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
  partial_column : (SszList (Cell P) P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
  kzg_proofs : (SszList KZGProof P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
  header : (SszList (PartialDataColumnHeader P) 1)

/-- `specs/fulu/partial-columns/p2p-interface.md` -/
ssz_container PartialDataColumnPartsMetadata (P : Preset) where
  available : (Bitlist P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
  requests : (Bitlist P.MAX_BLOB_COMMITMENTS_PER_BLOCK)

/-- `specs/fulu/partial-columns/p2p-interface.md` -/
ssz_container PartialDataColumnGroupID where
  beacon_block_root : Root

end JauneConsensus
