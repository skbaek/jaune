import JauneConsensus.Containers
import JauneConsensus.SSZ.Progressive

/-!
# Consensus containers, Gloas

The SSZ containers of `ethereum/consensus-specs` `v1.7.0-beta.4` for Gloas, from
`specs/gloas/beacon-chain.md` ("Types", "Containers"), `specs/gloas/p2p-interface.md`,
`specs/gloas/partial-columns/p2p-interface.md` and `specs/gloas/light-client/sync-protocol.md`.
Field names and order follow the spec exactly (they are the SSZ field order).

**Why separate declarations, in `namespace JauneConsensus.Gloas`.** `Containers.lean` indexes a
container by the fork and models a fork's change as a size function or as a `Gated` field that a
fork *introduces*. Gloas does three things that scheme does not express:

* it *removes* fields (`BeaconBlockBody` loses `execution_payload`, `blob_kzg_commitments` and
  `execution_requests`; `BeaconState` loses `latest_execution_payload_header`;
  `DataColumnSidecar` loses three, `LightClientHeader` loses `execution`);
* it changes the Merkleization of seven containers (EIP-7688 `ProgressiveContainer`:
  `Attestation`, `IndexedAttestation`, `BeaconBlockBody`, `BeaconState`, `ExecutionPayload`,
  `ExecutionRequests`, `NewPayloadRequest`, plus the new `PayloadAttestation`,
  `IndexedPayloadAttestation`, `ExecutionPayloadBid` and `ExecutionPayloadEnvelope`);
* it retypes 22 bounded lists as `ProgressiveList` (no limit at all: `Validators` and the new
  `Builders` have no `LIMIT`), and `AggregationBits` as `ProgressiveBitList`.

A fork-dependent `Ssz` instance over the Fulu structures would need fields that exist only before
Gloas and a second Merkleization inside every instance; separate structures keep each fork's
container a plain record whose type is its spec class. Containers Gloas leaves unchanged
(`Checkpoint`, `Validator`, `AttestationData`, `SyncAggregate`, `Withdrawal`, ...) are reused from
`Containers.lean`. Progressive lists carry no type-level limit, so decoding accepts any length; the
`MAX_*` caps are state-transition asserts, not SSZ bounds.

The progressive primitives are `SSZ/Progressive.lean`'s (`merkleize_progressive`,
`mix_in_active_fields`, progressive lists and bitlists), written for the `v1.6.1` `ssz_generic`
vectors under the EIP-7916/7495 names. Gloas cites EIP-7688 and imports them from the external
`eth-ssz-specs==0.1.0` package, whose `merkleize_progressive` puts the spine's successor on the
*right* where `v1.6.1` put it on the left; the Gloas `ssz_static` roots fix that revision, so
every progressive type here is the `.successorRight` one (`ProgressiveListR`,
`ProgressiveBitlistR`, `ProgressiveByteList`, `spine .successorRight`). Gloas uses only
`active_fields(width=N)` (all `1`, no gaps) and no compatible union.
-/

namespace JauneConsensus.Gloas

open Jaune

/-! ## Types (`specs/gloas/beacon-chain.md`, "Types") -/

/-- `BuilderIndex` (`Uint64`). -/
abbrev BuilderIndex := U64
/-- `Transaction` (`ProgressiveList[Byte]`, EIP-7688). -/
abbrev Transaction := ProgressiveByteList
/-- `BlockAccessList` (`ProgressiveList[Byte]`, EIP-7928). -/
abbrev BlockAccessList := ProgressiveByteList
/-- `PayloadTimelinessCommitteeBits` (`BitVector[PTC_SIZE]`). -/
abbrev PayloadTimelinessCommitteeBits (P : Preset) := Bitvector P.PTC_SIZE
/-- `PayloadTimelinessCommitteeIndices` (`List[ValidatorIndex, PTC_SIZE]`). -/
abbrev PayloadTimelinessCommitteeIndices (P : Preset) := SszList ValidatorIndex P.PTC_SIZE
/-- `PayloadTimelinessCommittee` (`Vector[ValidatorIndex, PTC_SIZE]`). -/
abbrev PayloadTimelinessCommittee (P : Preset) := SszVector ValidatorIndex P.PTC_SIZE
/-- `PayloadTimelinessCommitteeWindow`: `(MIN_SEED_LOOKAHEAD + 2) * SLOTS_PER_EPOCH` committees. -/
abbrev PayloadTimelinessCommitteeWindow (P : Preset) :=
  SszVector (PayloadTimelinessCommittee P) ((P.MIN_SEED_LOOKAHEAD + 2) * P.SLOTS_PER_EPOCH)
/-- `ExecutionPayloadAvailability` (`BitVector[SLOTS_PER_HISTORICAL_ROOT]`). -/
abbrev ExecutionPayloadAvailability (P : Preset) := Bitvector P.SLOTS_PER_HISTORICAL_ROOT

/-- Light-client branch depths at Gloas (`specs/gloas/light-client/sync-protocol.md`):
`floorlog2(CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS = 2945)` and `floorlog2(NEXT_... = 2946)` are 11,
`floorlog2(FINALIZED_ROOT_GINDEX_GLOAS = 735)` is 9, `floorlog2(EXECUTION_BLOCK_HASH_GINDEX_GLOAS
= 2856)` is 11 (the constants pysetup hardcodes, `pysetup/spec_builders/gloas.py`). -/
def syncCommitteeBranchDepth : Nat := 11
def finalityBranchDepth : Nat := 9
def executionBranchDepth : Nat := 11

-- The depths are `floorlog2` of the generalized indices.
#guard Nat.log2 2945 == syncCommitteeBranchDepth && Nat.log2 2946 == syncCommitteeBranchDepth
#guard Nat.log2 735 == finalityBranchDepth && Nat.log2 2856 == executionBranchDepth

/-! ## New containers (`specs/gloas/beacon-chain.md`) -/

/-- `specs/gloas/beacon-chain.md` -/
ssz_container Builder where
  pubkey : BLSPubkey
  version : U8
  execution_address : ExecutionAddress
  balance : Gwei
  deposit_epoch : Epoch
  withdrawable_epoch : Epoch

/-- `specs/gloas/beacon-chain.md` -/
ssz_container BuilderPendingWithdrawal where
  fee_recipient : ExecutionAddress
  amount : Gwei
  builder_index : BuilderIndex

/-- `specs/gloas/beacon-chain.md` -/
ssz_container BuilderPendingPayment where
  weight : Gwei
  withdrawal : BuilderPendingWithdrawal
  proposer_index : ValidatorIndex

/-- `specs/gloas/beacon-chain.md` (EIP-8282) -/
ssz_container BuilderDepositRequest where
  pubkey : BLSPubkey
  withdrawal_credentials : Bytes32
  amount : Gwei
  signature : BLSSignature

/-- `specs/gloas/beacon-chain.md` (EIP-8282) -/
ssz_container BuilderExitRequest where
  source_address : ExecutionAddress
  pubkey : BLSPubkey

/-- `specs/gloas/beacon-chain.md` -/
ssz_container PayloadAttestationData where
  beacon_block_root : Root
  slot : Slot
  payload_present : Bool
  blob_data_available : Bool

/-- `specs/gloas/beacon-chain.md`: `ACTIVE_FIELDS = active_fields(width=3)`. -/
ssz_progressive_container PayloadAttestation (P : Preset) [1, 1, 1] spine .successorRight where
  aggregation_bits : (PayloadTimelinessCommitteeBits P)
  data : PayloadAttestationData
  signature : BLSSignature

/-- `specs/gloas/beacon-chain.md` -/
ssz_container PayloadAttestationMessage where
  validator_index : ValidatorIndex
  data : PayloadAttestationData
  signature : BLSSignature

/-- `specs/gloas/beacon-chain.md`: `ACTIVE_FIELDS = active_fields(width=3)`. -/
ssz_progressive_container IndexedPayloadAttestation (P : Preset) [1, 1, 1] spine .successorRight where
  attesting_indices : (PayloadTimelinessCommitteeIndices P)
  data : PayloadAttestationData
  signature : BLSSignature

/-- `specs/gloas/beacon-chain.md`: `ACTIVE_FIELDS = active_fields(width=12)`. -/
ssz_progressive_container ExecutionPayloadBid [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] spine .successorRight where
  parent_block_hash : Hash32
  parent_block_root : Root
  block_hash : Hash32
  prev_randao : Bytes32
  fee_recipient : ExecutionAddress
  gas_limit : U64
  builder_index : BuilderIndex
  slot : Slot
  value : Gwei
  execution_payment : Gwei
  blob_kzg_commitments : (ProgressiveListR KZGCommitment)
  execution_requests_root : Root

/-- `specs/gloas/beacon-chain.md` -/
ssz_container SignedExecutionPayloadBid where
  message : ExecutionPayloadBid
  signature : BLSSignature

/-! ## Modified containers (`specs/gloas/beacon-chain.md`) -/

/-- `specs/gloas/beacon-chain.md` (EIP-7688, EIP-7928 `block_access_list`, EIP-7843
`slot_number`): `ACTIVE_FIELDS = active_fields(width=19)`. -/
ssz_progressive_container ExecutionPayload (P : Preset)
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] spine .successorRight where
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
  transactions : (ProgressiveListR Transaction)
  withdrawals : (ProgressiveListR Withdrawal)
  blob_gas_used : U64
  excess_blob_gas : U64
  block_access_list : BlockAccessList
  slot_number : U64

/-- `specs/gloas/beacon-chain.md` (EIP-7688; EIP-8282 `builder_deposits`, `builder_exits`):
`ACTIVE_FIELDS = active_fields(width=5)`. -/
ssz_progressive_container ExecutionRequests [1, 1, 1, 1, 1] spine .successorRight where
  deposits : (ProgressiveListR DepositRequest)
  withdrawals : (ProgressiveListR WithdrawalRequest)
  consolidations : (ProgressiveListR ConsolidationRequest)
  builder_deposits : (ProgressiveListR BuilderDepositRequest)
  builder_exits : (ProgressiveListR BuilderExitRequest)

/-- `specs/gloas/beacon-chain.md`: `ACTIVE_FIELDS = active_fields(width=5)`. -/
ssz_progressive_container ExecutionPayloadEnvelope (P : Preset) [1, 1, 1, 1, 1] spine .successorRight where
  payload : (ExecutionPayload P)
  execution_requests : ExecutionRequests
  builder_index : BuilderIndex
  beacon_block_root : Root
  parent_beacon_block_root : Root

/-- `specs/gloas/beacon-chain.md` -/
ssz_container SignedExecutionPayloadEnvelope (P : Preset) where
  message : (ExecutionPayloadEnvelope P)
  signature : BLSSignature

/-- `specs/gloas/beacon-chain.md` (EIP-7688): `ACTIVE_FIELDS = active_fields(width=4)`;
`aggregation_bits` is `AggregationBits(ProgressiveBitList)`. -/
ssz_progressive_container Attestation (P : Preset) [1, 1, 1, 1] spine .successorRight where
  aggregation_bits : ProgressiveBitlistR
  data : AttestationData
  signature : BLSSignature
  committee_bits : (Bitvector P.MAX_COMMITTEES_PER_SLOT)

/-- `specs/gloas/beacon-chain.md` (EIP-7688): `ACTIVE_FIELDS = active_fields(width=3)`. -/
ssz_progressive_container IndexedAttestation [1, 1, 1] spine .successorRight where
  attesting_indices : (ProgressiveListR ValidatorIndex)
  data : AttestationData
  signature : BLSSignature

/-- `specs/phase0/beacon-chain.md`, with Gloas's `IndexedAttestation`. -/
ssz_container AttesterSlashing where
  attestation_1 : IndexedAttestation
  attestation_2 : IndexedAttestation

/-- `specs/phase0/validator.md`, with Gloas's `Attestation`. -/
ssz_container AggregateAndProof (P : Preset) where
  aggregator_index : ValidatorIndex
  aggregate : (Attestation P)
  selection_proof : BLSSignature

/-- `specs/phase0/validator.md`, with Gloas's `Attestation`. -/
ssz_container SignedAggregateAndProof (P : Preset) where
  message : (AggregateAndProof P)
  signature : BLSSignature

/-- `specs/gloas/beacon-chain.md` (EIP-7688, EIP-7732): `ACTIVE_FIELDS = active_fields(width=13)`.
`execution_payload`, `blob_kzg_commitments` and `execution_requests` are removed (they live in
`ExecutionPayloadEnvelope`). -/
ssz_progressive_container BeaconBlockBody (P : Preset)
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] spine .successorRight where
  randao_reveal : BLSSignature
  eth1_data : Eth1Data
  graffiti : Bytes32
  proposer_slashings : (ProgressiveListR ProposerSlashing)
  attester_slashings : (ProgressiveListR AttesterSlashing)
  attestations : (ProgressiveListR (Attestation P))
  deposits : (ProgressiveListR Deposit)
  voluntary_exits : (ProgressiveListR SignedVoluntaryExit)
  sync_aggregate : (SyncAggregate P)
  bls_to_execution_changes : (ProgressiveListR SignedBLSToExecutionChange)
  signed_execution_payload_bid : SignedExecutionPayloadBid
  payload_attestations : (ProgressiveListR (PayloadAttestation P))
  parent_execution_requests : ExecutionRequests

/-- `specs/phase0/beacon-chain.md`, with Gloas's body. -/
ssz_container BeaconBlock (P : Preset) where
  slot : Slot
  proposer_index : ValidatorIndex
  parent_root : Root
  state_root : Root
  body : (BeaconBlockBody P)

/-- `specs/phase0/beacon-chain.md`, with Gloas's block. -/
ssz_container SignedBeaconBlock (P : Preset) where
  message : (BeaconBlock P)
  signature : BLSSignature

/-- `specs/gloas/beacon-chain.md` (EIP-7688, EIP-7732): `ACTIVE_FIELDS = active_fields(width=46)`.
`latest_execution_payload_header` is removed; `latest_block_hash` takes its place, and the
builder registry, payment and PTC fields are appended. -/
ssz_progressive_container BeaconState (P : Preset)
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
     1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] spine .successorRight where
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
  validators : (ProgressiveListR Validator)
  balances : (ProgressiveListR Gwei)
  randao_mixes : (SszVector Bytes32 P.EPOCHS_PER_HISTORICAL_VECTOR)
  slashings : (SszVector Gwei P.EPOCHS_PER_SLASHINGS_VECTOR)
  previous_epoch_participation : (ProgressiveListR ParticipationFlags)
  current_epoch_participation : (ProgressiveListR ParticipationFlags)
  justification_bits : (Bitvector JUSTIFICATION_BITS_LENGTH)
  previous_justified_checkpoint : Checkpoint
  current_justified_checkpoint : Checkpoint
  finalized_checkpoint : Checkpoint
  inactivity_scores : (ProgressiveListR U64)
  current_sync_committee : (SyncCommittee P)
  next_sync_committee : (SyncCommittee P)
  latest_block_hash : Hash32
  next_withdrawal_index : WithdrawalIndex
  next_withdrawal_validator_index : ValidatorIndex
  historical_summaries : (SszList HistoricalSummary P.HISTORICAL_ROOTS_LIMIT)
  deposit_requests_start_index : U64
  deposit_balance_to_consume : Gwei
  exit_balance_to_consume : Gwei
  earliest_exit_epoch : Epoch
  consolidation_balance_to_consume : Gwei
  earliest_consolidation_epoch : Epoch
  pending_deposits : (ProgressiveListR PendingDeposit)
  pending_partial_withdrawals : (ProgressiveListR PendingPartialWithdrawal)
  pending_consolidations : (ProgressiveListR PendingConsolidation)
  proposer_lookahead : (SszVector ValidatorIndex ((P.MIN_SEED_LOOKAHEAD + 1) * P.SLOTS_PER_EPOCH))
  builders : (ProgressiveListR Builder)
  next_withdrawal_builder_index : BuilderIndex
  execution_payload_availability : (ExecutionPayloadAvailability P)
  builder_pending_payments : (SszVector BuilderPendingPayment (2 * P.SLOTS_PER_EPOCH))
  builder_pending_withdrawals : (ProgressiveListR BuilderPendingWithdrawal)
  latest_execution_payload_bid : ExecutionPayloadBid
  payload_expected_withdrawals : (ProgressiveListR Withdrawal)
  ptc_window : (PayloadTimelinessCommitteeWindow P)

/-- `specs/gloas/beacon-chain.md` (EIP-7688): `ACTIVE_FIELDS = active_fields(width=4)`;
`versioned_hashes` is Deneb's `VersionedHashes` (`List[VersionedHash,
MAX_BLOB_COMMITMENTS_PER_BLOCK]`). -/
ssz_progressive_container NewPayloadRequest (P : Preset) [1, 1, 1, 1] spine .successorRight where
  execution_payload : (ExecutionPayload P)
  versioned_hashes : (SszList Bytes32 P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
  parent_beacon_block_root : Root
  execution_requests : ExecutionRequests

/-! ## Networking (`specs/gloas/p2p-interface.md`, `specs/gloas/partial-columns/p2p-interface.md`) -/

/-- `specs/gloas/p2p-interface.md`: `column` is `DataColumn(ProgressiveList[Cell])` and
`kzg_proofs` is `KZGProofs(ProgressiveList[KZGProof])` (EIP-7688); `kzg_commitments`,
`signed_block_header` and `kzg_commitments_inclusion_proof` are removed (EIP-7732). -/
ssz_container DataColumnSidecar (P : Preset) where
  index : ColumnIndex
  column : (ProgressiveListR (Cell P))
  kzg_proofs : (ProgressiveListR KZGProof)
  slot : Slot
  beacon_block_root : Root

/-- `specs/gloas/p2p-interface.md` -/
ssz_container ProposerPreferences where
  dependent_root : Root
  proposal_slot : Slot
  validator_index : ValidatorIndex
  fee_recipient : ExecutionAddress
  target_gas_limit : U64

/-- `specs/gloas/p2p-interface.md` -/
ssz_container SignedProposerPreferences where
  message : ProposerPreferences
  signature : BLSSignature

/-- `specs/gloas/partial-columns/p2p-interface.md`: `CellsBitList` is a `ProgressiveBitList`;
`header` is removed. -/
ssz_container PartialDataColumnSidecar (P : Preset) where
  cells_present_bitmap : ProgressiveBitlistR
  partial_column : (ProgressiveListR (Cell P))
  kzg_proofs : (ProgressiveListR KZGProof)

/-- `specs/gloas/partial-columns/p2p-interface.md` -/
ssz_container PartialDataColumnPartsMetadata where
  available : ProgressiveBitlistR
  requests : ProgressiveBitlistR

/-- `specs/gloas/partial-columns/p2p-interface.md` -/
ssz_container PartialDataColumnGroupID where
  beacon_block_root : Root
  slot : Slot

/-! ## Light client (`specs/gloas/light-client/sync-protocol.md`) -/

/-- `specs/gloas/light-client/sync-protocol.md`: `execution` is replaced by
`execution_block_hash` (EIP-7732), with the Gloas `ExecutionBranch`. -/
ssz_container LightClientHeader where
  beacon : BeaconBlockHeader
  execution_block_hash : Hash32
  execution_branch : (SszVector Bytes32 executionBranchDepth)

/-- `specs/altair/light-client/sync-protocol.md`, Gloas header and branch depth. -/
ssz_container LightClientBootstrap (P : Preset) where
  header : LightClientHeader
  current_sync_committee : (SyncCommittee P)
  current_sync_committee_branch : (SszVector Bytes32 syncCommitteeBranchDepth)

/-- `specs/altair/light-client/sync-protocol.md`, Gloas header and branch depths. -/
ssz_container LightClientUpdate (P : Preset) where
  attested_header : LightClientHeader
  next_sync_committee : (SyncCommittee P)
  next_sync_committee_branch : (SszVector Bytes32 syncCommitteeBranchDepth)
  finalized_header : LightClientHeader
  finality_branch : (SszVector Bytes32 finalityBranchDepth)
  sync_aggregate : (SyncAggregate P)
  signature_slot : Slot

/-- `specs/altair/light-client/sync-protocol.md`, Gloas header and branch depth. -/
ssz_container LightClientFinalityUpdate (P : Preset) where
  attested_header : LightClientHeader
  finalized_header : LightClientHeader
  finality_branch : (SszVector Bytes32 finalityBranchDepth)
  sync_aggregate : (SyncAggregate P)
  signature_slot : Slot

/-- `specs/altair/light-client/sync-protocol.md`, Gloas header. -/
ssz_container LightClientOptimisticUpdate (P : Preset) where
  attested_header : LightClientHeader
  sync_aggregate : (SyncAggregate P)
  signature_slot : Slot

end JauneConsensus.Gloas
