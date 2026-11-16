import JauneConsensus.GossipCore
import JauneConsensus.ForkChoice
import JauneConsensus.LightClient
import JauneConsensus.SSZ.Proof

/-!
# Store-dependent gossip validators, Electra and Fulu (goal `eip8282-gloas-cross-layer-v1`, M6)

Transcribed from `ethereum/consensus-specs` `v1.7.0-beta.4` over the fork-choice `Store P f`
(`JauneConsensus/ForkChoice.lean`) and the fork-indexed `BeaconState P f`. Each definition cites
its `validate_<topic>_gossip` and keeps the spec's check order and reason strings verbatim:

* `validate_beacon_block_gossip`: Electra (`specs/electra/p2p-interface.md:128`, EIP-7691's
  `MAX_BLOBS_PER_BLOCK_ELECTRA`) and Fulu (`specs/fulu/p2p-interface.md:305`, EIP-7892's
  `get_blob_parameters`); the two differ only in that bound;
* `validate_beacon_aggregate_and_proof_gossip` (`specs/electra/p2p-interface.md:232`) and
  `validate_beacon_attestation_gossip` (`:375`, over `SingleAttestation`), which Fulu inherits;
* `validate_blob_sidecar_gossip` (`specs/electra/p2p-interface.md:479`; Fulu deprecates the
  topic);
* `validate_data_column_sidecar_gossip` (`specs/fulu/p2p-interface.md:415`);
* `validate_partial_data_column_sidecar_gossip` (`specs/fulu/partial-columns/p2p-interface.md:227`).

**`Seen`.** The store-dependent fields of the Electra and Fulu `Seen` (the union of the two
dataclasses; Electra has `blob_sidecar_tuples`, Fulu `data_column_sidecar_tuples` and
`partial_data_column_headers`) are the extension `StoreSeen`. Python sets are association lists,
as in `GossipCore.lean`.

**What a validator returns.** Every validator but the partial one records the message in `Seen`
only as its last statement, so the cache after a gossip exception is the cache before it
(`Gossip.outcome`). `validate_partial_data_column_sidecar_gossip` writes
`seen.partial_data_column_headers` at the end of its header part and may then raise in its cell
part; pyspec's `Seen` is mutated in place, so that header stays cached. The validator here
therefore returns the outcome together with the cache Python would hold afterwards.

`get_head(store)` is `JauneConsensus.getHead` with `ctx.cfg`; `bls.Verify` is `blsVerify` under
`ctx.blsActive`.
-/

namespace JauneConsensus.Gossip
open Jaune (Bytes B256)

variable {P : Preset} {f : CFork}

/-! ## `Seen`, `PayloadValidationStatus` -/

/-- The store-dependent fields of `Seen` (Electra `specs/electra/p2p-interface.md:52`, Fulu
`specs/fulu/p2p-interface.md:125`). -/
structure StoreSeen (P : Preset) where
  proposer_slots : List (Slot × ValidatorIndex) := []
  aggregator_epochs : List (Epoch × ValidatorIndex) := []
  aggregate_data_roots : List ((Root × CommitteeIndex) × List (List Bool)) := []
  attestation_validator_epochs : List (Epoch × ValidatorIndex) := []
  blob_sidecar_tuples : List (Slot × ValidatorIndex × BlobIndex) := []
  data_column_sidecar_tuples : List (Slot × ValidatorIndex × ColumnIndex) := []
  partial_data_column_headers : List (Root × PartialDataColumnHeader P) := []

/-- The cache of the store-dependent validators. -/
abbrev SSeen (P : Preset) := Seen (StoreSeen P)

/-- `PayloadValidationStatus` (`specs/bellatrix/p2p-interface.md:47`): `PAYLOAD_STATUS_*`. -/
inductive PayloadValidationStatus
  | notValidated | invalidated | valid
  deriving DecidableEq, Repr

/-! ## Helpers -/

/-- Run a model computation inside a gossip validation (its exceptions stay model exceptions). -/
@[inline] def liftModel {α : Type} (x : M α) : GM α := ExceptT.lift x

/-- `TARGET_AGGREGATORS_PER_COMMITTEE = 2**4` (`specs/phase0/validator.md`). -/
def TARGET_AGGREGATORS_PER_COMMITTEE : Nat := 16

/-- `get_generalized_index(BeaconBlockBody, "blob_kzg_commitments")`: the Electra and Fulu
body has 13 fields (padded to 16 chunks) and `blob_kzg_commitments` is field 11. -/
def BLOB_KZG_COMMITMENTS_GINDEX : Nat := 16 + 11

/-- `store.block_states[get_head(store).root]`. -/
def headState (ctx : Ctx) (store : Store P f) : M (BeaconState P f) := do
  lookup store.block_states (← getHead ctx.cfg store).root
    "store.block_states[get_head(store).root]"

/-- `compute_subnet_for_attestation(committees_per_slot, slot, committee_index)`
(`specs/phase0/validator.md:702`); `Uint64` arithmetic. -/
def computeSubnetForAttestation (cfg : Config) (committeesPerSlot : U64) (slot : Slot)
    (committeeIndex : CommitteeIndex) : M U64 := do
  let site := "compute_subnet_for_attestation"
  let slotsSinceEpochStart ← U64.mod? slot (← c64 P.SLOTS_PER_EPOCH) site
  let committeesSinceEpochStart ← U64.mul? committeesPerSlot slotsSinceEpochStart site
  U64.mod? (← U64.add? committeesSinceEpochStart committeeIndex site)
    (← c64 cfg.ATTESTATION_SUBNET_COUNT) site

/-- `compute_subnet_for_blob_sidecar(blob_index)` (`specs/electra/validator.md:271`). -/
def computeSubnetForBlobSidecar (cfg : Config) (blobIndex : BlobIndex) : M U64 := do
  U64.mod? blobIndex (← c64 cfg.BLOB_SIDECAR_SUBNET_COUNT_ELECTRA)
    "compute_subnet_for_blob_sidecar"

/-- `is_aggregator(state, slot, index, slot_signature)` (`specs/phase0/validator.md:733`). -/
def isAggregator (state : BeaconState P f) (slot : Slot) (index : CommitteeIndex)
    (slotSignature : BLSSignature) : M Bool := do
  let committee ← getBeaconCommittee state slot index
  let modulo := max 1 (committee.size / TARGET_AGGREGATORS_PER_COMMITTEE)
  let v ← bytesToUint64 ((hashBytes slotSignature.toArray.toList).take 8)
  pure (v.toNat % modulo == 0)

/-- `verify_blob_sidecar_inclusion_proof(blob_sidecar)` (`specs/deneb/p2p-interface.md:253`):
the commitment's generalized index is `get_generalized_index(BeaconBlockBody,
"blob_kzg_commitments", index)`, the list's data root (`* 2`) at width
`MAX_BLOB_COMMITMENTS_PER_BLOCK` (a power of two in both presets). -/
def verifyBlobSidecarInclusionProof (blobSidecar : BlobSidecar P) : M Bool := do
  let gindex := BLOB_KZG_COMMITMENTS_GINDEX * 2 * getPowerOfTwoCeil P.MAX_BLOB_COMMITMENTS_PER_BLOCK +
    blobSidecar.index.toNat
  isValidMerkleBranch (Ssz.hashTreeRoot blobSidecar.kzg_commitment)
    blobSidecar.kzg_commitment_inclusion_proof.toArray.toList
    (← c64 P.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH) (← getSubtreeIndex gindex)
    blobSidecar.signed_block_header.message.body_root

/-- `verify_blob_kzg_proof(blob, commitment_bytes, proof_bytes)` (`specs/deneb/
polynomial-commitments.md`), raising on malformed inputs as pyspec does. -/
def verifyBlobKzgProofM (blob : Blob P) (commitment : KZGCommitment) (proof : KZGProof) :
    M Bool :=
  liftCrypto "verify_blob_kzg_proof"
    (verifyBlobKzgProof blob.toArray.toList commitment.toArray.toList proof.toArray.toList)

/-- `is_valid_merkle_branch` of `hash_tree_root(kzg_commitments)` against `body_root`, at
`get_subtree_index(get_generalized_index(BeaconBlockBody, "blob_kzg_commitments"))`: the body
of `verify_data_column_sidecar_inclusion_proof` (`specs/fulu/p2p-interface.md:249`) and of
`verify_partial_data_column_header_inclusion_proof`
(`specs/fulu/partial-columns/p2p-interface.md`). -/
def verifyKzgCommitmentsInclusionProof
    (commitments : SszList KZGCommitment P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
    (branch : SszVector Bytes32 P.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH) (bodyRoot : Root) :
    M Bool := do
  isValidMerkleBranch (Ssz.hashTreeRoot commitments) branch.toArray.toList
    (← c64 P.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH) (← getSubtreeIndex BLOB_KZG_COMMITMENTS_GINDEX)
    bodyRoot

/-- `verify_data_column_sidecar_inclusion_proof(sidecar)` (`specs/fulu/p2p-interface.md:249`). -/
def verifyDataColumnSidecarInclusionProof (sidecar : DataColumnSidecar P) : M Bool :=
  verifyKzgCommitmentsInclusionProof sidecar.kzg_commitments
    sidecar.kzg_commitments_inclusion_proof sidecar.signed_block_header.message.body_root

/-- `verify_partial_data_column_header_inclusion_proof(header)`
(`specs/fulu/partial-columns/p2p-interface.md`). -/
def verifyPartialDataColumnHeaderInclusionProof (header : PartialDataColumnHeader P) : M Bool :=
  verifyKzgCommitmentsInclusionProof header.kzg_commitments
    header.kzg_commitments_inclusion_proof header.signed_block_header.message.body_root

/-- `verify_partial_data_column_sidecar_kzg_proofs(sidecar, all_commitments, column_index)`
(`specs/fulu/partial-columns/p2p-interface.md`): `all_commitments[index]` raises `IndexError`
past the end. -/
def verifyPartialDataColumnSidecarKzgProofs (sidecar : PartialDataColumnSidecar P)
    (allCommitments : SszList KZGCommitment P.MAX_BLOB_COMMITMENTS_PER_BLOCK)
    (columnIndex : ColumnIndex) : M Bool := do
  -- Get the blob indices from the bitmap
  let blobIndices := ((sidecar.cells_present_bitmap.bits.toList.zipIdx).filter (·.1)).map (·.2)
  -- The cell index is the column index for all cells in this column
  let cellIndices := List.replicate blobIndices.length columnIndex.toNat
  let commitments ← blobIndices.mapM fun i =>
    getAt allCommitments.toArray i "verify_partial_data_column_sidecar_kzg_proofs: all_commitments"
  -- Batch verify that the cells match the corresponding commitments and proofs
  verifyCellKzgProofBatchM (commitments.map (·.toArray.toList)) cellIndices
    (sidecar.partial_column.toArray.toList.map (·.toArray.toList))
    (sidecar.kzg_proofs.toArray.toList.map (·.toArray.toList))

/-- The parent-state proposer check shared by the block and sidecar validators: a copy of
`store.block_states[parent_root]`, `process_slots` to `slot`, `get_beacon_proposer_index`. -/
def expectedProposer (ctx : Ctx) (store : Store P f) (parentRoot : Root) (slot : Slot) :
    M ValidatorIndex := do
  let parentState ← lookup store.block_states parentRoot "store.block_states[parent_root]"
  getBeaconProposerIndex (← processSlots ctx parentState slot)

/-! ## `beacon_block` -/

/-- `validate_beacon_block_gossip` (Electra `specs/electra/p2p-interface.md:128`, Fulu
`specs/fulu/p2p-interface.md:305`). `blockPayloadStatuses` is `block_payload_statuses`. -/
def validateBeaconBlockGossip (ctx : Ctx) (seen : SSeen P) (store : Store P f)
    (signedBeaconBlock : SignedBeaconBlock P f) (currentTimeMs : U64)
    (blockPayloadStatuses : Root → Option PayloadValidationStatus) : GM (SSeen P) := do
  let cfg := ctx.cfg
  let block := signedBeaconBlock.message
  let executionPayload := block.body.execution_payload
  -- [IGNORE] The block is the first block with valid signature received for the slot and proposer
  let proposerSlotKey := (block.slot, block.proposer_index)
  if seen.ext.proposer_slots.contains proposerSlotKey then
    ignore "block is not the first valid block for this slot and proposer"
  -- [IGNORE] The block is not from a future slot
  if ← isFutureSlot cfg store.genesis_time_ms block.slot currentTimeMs then
    ignore "block is from a future slot"
  -- [IGNORE] The block is from a slot greater than the latest finalized slot
  let finalizedSlot ← computeStartSlotAtEpoch P store.finalized_checkpoint.epoch
  if block.slot ≤ finalizedSlot then
    ignore "block is not from a slot greater than the latest finalized slot"
  -- [IGNORE] The block's parent has been seen (via gossip or non-gossip sources)
  if !store.blocks.contains block.parent_root then ignore "block's parent has not been seen"
  let parentPayloadStatus : PayloadValidationStatus :=
    match blockPayloadStatuses block.parent_root with
    | some status => status
    | none => .notValidated
  if !store.block_states.contains block.parent_root then
    if parentPayloadStatus == .notValidated then
      -- [REJECT] The block's parent failed validation and its execution payload is optimistic
      reject "block's parent is invalid and its payload is optimistic"
    -- [IGNORE] The block's parent failed validation and its execution payload is processed
    ignore "block's parent is invalid and its payload is processed"
  -- [IGNORE] The block's parent passed validation but its execution payload is invalid
  if parentPayloadStatus == .invalidated then
    ignore "block's parent is valid and its payload is invalid"
  let state ← headState ctx store
  -- [REJECT] The proposer index is a valid validator index
  if block.proposer_index.toNat ≥ state.validators.length then reject "proposer index out of range"
  -- [REJECT] The proposer signature is valid
  let proposer ← state.validators.get block.proposer_index.toNat "validate_beacon_block_gossip"
  let domain ← getDomain state DOMAIN_BEACON_PROPOSER (some (← computeEpochAtSlot P block.slot))
  if !blsVerify ctx.blsActive proposer.pubkey (computeSigningRoot block domain)
      signedBeaconBlock.signature then
    reject "invalid proposer signature"
  -- [REJECT] The block's execution payload timestamp is correct with respect to the slot
  if executionPayload.timestamp != (← computeTimeAtSlotOf cfg state.genesis_time block.slot) then
    reject "incorrect execution payload timestamp"
  -- [REJECT] The block is from a higher slot than its parent
  let parent : BeaconBlock P f ← liftModel (lookup store.blocks block.parent_root
    "store.blocks[block.parent_root]")
  if block.slot ≤ parent.slot then reject "block is not from a higher slot than its parent"
  -- [REJECT] The current finalized checkpoint is an ancestor of the block
  let finalizedCheckpointBlock ← getCheckpointBlock store block.parent_root
    store.finalized_checkpoint.epoch
  if finalizedCheckpointBlock != store.finalized_checkpoint.root then
    reject "finalized checkpoint is not an ancestor of block"
  -- [REJECT] The length of KZG commitments is less than or equal to the limit
  -- (Electra: `MAX_BLOBS_PER_BLOCK_ELECTRA`; Fulu: `get_blob_parameters(...)`)
  let maxBlobs ← if f.atLeast .fulu then do
      pure (← getBlobParameters cfg (← computeEpochAtSlot P block.slot)).maxBlobsPerBlock.toNat
    else pure cfg.MAX_BLOBS_PER_BLOCK_ELECTRA
  if block.body.blob_kzg_commitments.toArray.size > maxBlobs then
    reject "too many blob kzg commitments"
  -- [REJECT] The block is proposed by the expected proposer for the slot
  if block.proposer_index != (← expectedProposer ctx store block.parent_root block.slot) then
    reject "block proposer_index does not match expected proposer"
  -- Mark this block as seen
  pure { seen with ext := { seen.ext with
    proposer_slots := seen.ext.proposer_slots ++ [proposerSlotKey] } }

/-! ## `beacon_aggregate_and_proof`, `beacon_attestation_{subnet_id}` -/

/-- `validate_beacon_aggregate_and_proof_gossip` (`specs/electra/p2p-interface.md:232`). -/
def validateBeaconAggregateAndProofGossip (ctx : Ctx) (seen : SSeen P) (store : Store P f)
    (signedAggregateAndProof : SignedAggregateAndProof P f) (currentTimeMs : U64) :
    GM (SSeen P) := do
  let cfg := ctx.cfg
  let aggregateAndProof := signedAggregateAndProof.message
  let aggregate := aggregateAndProof.aggregate
  let aggregationBits := aggregate.aggregation_bits.bits.toList
  -- [REJECT] The aggregate attestation's data index is zero
  if aggregate.data.index != U64.zero then reject "aggregate data index is non-zero"
  -- [REJECT] Exactly one committee is specified by the committee bits
  let committeeBits : Bitvector P.MAX_COMMITTEES_PER_SLOT ←
    liftModel (Gated.read aggregate.committee_bits "aggregate.committee_bits")
  let committeeIndices ← getCommitteeIndices committeeBits
  let index ← match committeeIndices.toList with
    | [i] => pure i
    | _ => reject "aggregate committee bits must specify exactly one committee"
  -- [IGNORE] A valid aggregate with a superset of aggregation bits has not already been seen
  let aggregateDataRoot : Root := Ssz.hashTreeRoot aggregate.data
  let aggregateCacheKey := (aggregateDataRoot, index)
  let seenBits := lookupSet seen.ext.aggregate_data_roots aggregateCacheKey
  if ← isNonStrictSuperset seenBits aggregationBits then
    ignore "already seen aggregate for this data"
  -- [IGNORE] This is the first valid aggregate for this epoch and aggregator
  let aggregatorIndex := aggregateAndProof.aggregator_index
  let targetEpoch := aggregate.data.target.epoch
  let aggregatorEpochKey := (targetEpoch, aggregatorIndex)
  if seen.ext.aggregator_epochs.contains aggregatorEpochKey then
    ignore "already seen aggregate for this epoch and aggregator"
  -- [IGNORE] The block being voted for has been seen (via gossip or non-gossip sources)
  let blockRoot := aggregate.data.beacon_block_root
  if !store.blocks.contains blockRoot then ignore "block being voted for has not been seen"
  -- [REJECT] The block being voted for passes validation
  if !store.block_states.contains blockRoot then reject "block being voted for failed validation"
  let state ← headState ctx store
  -- [REJECT] The committee index is within the expected range
  let committeeCount ← getCommitteeCountPerSlot state aggregate.data.target.epoch
  if index ≥ committeeCount then reject "committee index out of range"
  -- [IGNORE] The aggregate attestation's slot is not from a future slot
  if ← isFutureSlot cfg store.genesis_time_ms aggregate.data.slot currentTimeMs then
    ignore "aggregate slot is from a future slot"
  -- [IGNORE] The aggregate attestation's epoch is either the current or previous epoch
  let attestationEpoch ← computeEpochAtSlot P aggregate.data.slot
  if !(← isCurrentOrPreviousEpoch P cfg store.genesis_time_ms attestationEpoch currentTimeMs) then
    ignore "aggregate epoch is not current or previous epoch"
  -- [REJECT] The aggregate attestation's epoch matches its target
  if aggregate.data.target.epoch != (← computeEpochAtSlot P aggregate.data.slot) then
    reject "attestation epoch does not match target epoch"
  -- [REJECT] The number of aggregation bits matches the committee size
  let committee ← getBeaconCommittee state aggregate.data.slot index
  if aggregationBits.length != committee.size then
    reject "aggregation bits length does not match committee size"
  -- [REJECT] The aggregate attestation has participants
  let attestingIndices ← getAttestingIndices state aggregate
  if attestingIndices.size < 1 then reject "aggregate has no participants"
  -- [REJECT] The selection proof selects the validator as an aggregator
  if !(← isAggregator state aggregate.data.slot index aggregateAndProof.selection_proof) then
    reject "validator is not selected as aggregator"
  -- [REJECT] The aggregator is a member of the committee
  if !committee.contains aggregatorIndex then reject "aggregator is not a member of the committee"
  -- [REJECT] The selection proof signature is valid
  let aggregator ← state.validators.get aggregatorIndex.toNat
    "validate_beacon_aggregate_and_proof_gossip"
  let domain ← getDomain state DOMAIN_SELECTION_PROOF (some targetEpoch)
  if !blsVerify ctx.blsActive aggregator.pubkey (computeSigningRoot aggregate.data.slot domain)
      aggregateAndProof.selection_proof then
    reject "invalid selection proof signature"
  -- [REJECT] The aggregator signature is valid
  let domain ← getDomain state DOMAIN_AGGREGATE_AND_PROOF (some targetEpoch)
  if !blsVerify ctx.blsActive aggregator.pubkey (computeSigningRoot aggregateAndProof domain)
      signedAggregateAndProof.signature then
    reject "invalid aggregator signature"
  -- [REJECT] The aggregate signature is valid
  if !(← isValidIndexedAttestation ctx state (← getIndexedAttestation state aggregate)) then
    reject "invalid aggregate signature"
  -- [REJECT] The target block is an ancestor of the LMD vote block
  let checkpointBlock ← getCheckpointBlock store blockRoot aggregate.data.target.epoch
  if checkpointBlock != aggregate.data.target.root then
    reject "target block is not an ancestor of LMD vote block"
  -- [IGNORE] The finalized checkpoint is an ancestor of the block
  let finalizedCheckpointBlock ← getCheckpointBlock store blockRoot
    store.finalized_checkpoint.epoch
  if finalizedCheckpointBlock != store.finalized_checkpoint.root then
    ignore "finalized checkpoint is not an ancestor of block"
  -- Mark this aggregate as seen
  pure { seen with ext := { seen.ext with
    aggregator_epochs := seen.ext.aggregator_epochs ++ [aggregatorEpochKey]
    aggregate_data_roots :=
      addToSet seen.ext.aggregate_data_roots aggregateCacheKey aggregationBits } }

/-- `validate_beacon_attestation_gossip` (`specs/electra/p2p-interface.md:375`). -/
def validateBeaconAttestationGossip (ctx : Ctx) (seen : SSeen P) (store : Store P f)
    (attestation : SingleAttestation) (currentTimeMs : U64) (subnetId : U64) : GM (SSeen P) := do
  let cfg := ctx.cfg
  let data := attestation.data
  let committeeIndex := attestation.committee_index
  let attesterIndex := attestation.attester_index
  let targetEpoch := data.target.epoch
  -- [IGNORE] No other valid attestation seen for this target epoch and validator
  let attestationEpochKey := (targetEpoch, attesterIndex)
  if seen.ext.attestation_validator_epochs.contains attestationEpochKey then
    ignore "already seen attestation for this epoch and validator"
  -- [REJECT] The attestation's data index is zero
  if data.index != U64.zero then reject "attestation data index is non-zero"
  -- [IGNORE] The block being voted for has been seen (via gossip or non-gossip sources)
  let blockRoot := data.beacon_block_root
  if !store.blocks.contains blockRoot then ignore "block being voted for has not been seen"
  -- [REJECT] The block being voted for passes validation
  if !store.block_states.contains blockRoot then reject "block being voted for failed validation"
  let state ← headState ctx store
  -- [REJECT] The committee index is within the expected range
  let committeesPerSlot ← getCommitteeCountPerSlot state targetEpoch
  if committeeIndex ≥ committeesPerSlot then reject "committee index out of range"
  -- [REJECT] The attestation is for the correct subnet
  let expectedSubnet ← computeSubnetForAttestation (P := P) cfg committeesPerSlot data.slot
    committeeIndex
  if expectedSubnet != subnetId then reject "attestation is for wrong subnet"
  -- [IGNORE] The attestation's slot is not from a future slot
  if ← isFutureSlot cfg store.genesis_time_ms data.slot currentTimeMs then
    ignore "attestation slot is from a future slot"
  -- [IGNORE] The attestation's epoch is either the current or previous epoch
  let attestationEpoch ← computeEpochAtSlot P data.slot
  if !(← isCurrentOrPreviousEpoch P cfg store.genesis_time_ms attestationEpoch currentTimeMs) then
    ignore "attestation epoch is not current or previous epoch"
  -- [REJECT] The attestation's epoch matches its target
  if targetEpoch != (← computeEpochAtSlot P data.slot) then
    reject "attestation epoch does not match target epoch"
  -- [REJECT] The attester is a member of the committee
  let committee ← getBeaconCommittee state data.slot committeeIndex
  if !committee.contains attesterIndex then reject "attester is not a member of the committee"
  -- [REJECT] The attestation signature is valid
  let attester ← state.validators.get attesterIndex.toNat "validate_beacon_attestation_gossip"
  let domain ← getDomain state DOMAIN_BEACON_ATTESTER (some targetEpoch)
  if !blsVerify ctx.blsActive attester.pubkey (computeSigningRoot data domain)
      attestation.signature then
    reject "invalid attestation signature"
  -- [REJECT] The attestation's target block is an ancestor of the LMD vote block
  let targetCheckpointBlock ← getCheckpointBlock store blockRoot targetEpoch
  if targetCheckpointBlock != data.target.root then
    reject "target block is not an ancestor of LMD vote block"
  -- [IGNORE] The current finalized_checkpoint is an ancestor of the block
  let finalizedCheckpointBlock ← getCheckpointBlock store blockRoot
    store.finalized_checkpoint.epoch
  if finalizedCheckpointBlock != store.finalized_checkpoint.root then
    ignore "finalized checkpoint is not an ancestor of block"
  -- Mark this attestation as seen
  pure { seen with ext := { seen.ext with
    attestation_validator_epochs := seen.ext.attestation_validator_epochs ++ [attestationEpochKey] } }

/-! ## Sidecars -/

/-- `validate_blob_sidecar_gossip` (`specs/electra/p2p-interface.md:479`). -/
def validateBlobSidecarGossip (ctx : Ctx) (seen : SSeen P) (store : Store P f)
    (blobSidecar : BlobSidecar P) (currentTimeMs : U64) (subnetId : U64) : GM (SSeen P) := do
  let cfg := ctx.cfg
  let blockHeader := blobSidecar.signed_block_header.message
  -- [IGNORE] The sidecar is the first sidecar for the tuple
  let sidecarTuple := (blockHeader.slot, blockHeader.proposer_index, blobSidecar.index)
  if seen.ext.blob_sidecar_tuples.contains sidecarTuple then
    ignore "already seen blob sidecar from this proposer for this slot and index"
  -- [REJECT] The sidecar's index is consistent with MAX_BLOBS_PER_BLOCK_ELECTRA
  if blobSidecar.index.toNat ≥ cfg.MAX_BLOBS_PER_BLOCK_ELECTRA then reject "blob index out of range"
  -- [REJECT] The sidecar is for the correct subnet
  if (← computeSubnetForBlobSidecar cfg blobSidecar.index) != subnetId then
    reject "blob sidecar is for wrong subnet"
  -- [IGNORE] The sidecar is not from a future slot
  if ← isFutureSlot cfg store.genesis_time_ms blockHeader.slot currentTimeMs then
    ignore "blob sidecar is from a future slot"
  -- [IGNORE] The sidecar is from a slot greater than the latest finalized slot
  let finalizedSlot ← computeStartSlotAtEpoch P store.finalized_checkpoint.epoch
  if blockHeader.slot ≤ finalizedSlot then
    ignore "blob sidecar is not from a slot greater than the latest finalized slot"
  -- [IGNORE] The sidecar's block's parent has been seen
  let parentRoot := blockHeader.parent_root
  if !store.blocks.contains parentRoot then ignore "blob sidecar's parent has not been seen"
  -- [REJECT] The sidecar's block's parent passes validation
  if !store.block_states.contains parentRoot then reject "blob sidecar's parent failed validation"
  let state ← headState ctx store
  -- [REJECT] The proposer index is a valid validator index
  if blockHeader.proposer_index.toNat ≥ state.validators.length then
    reject "proposer index out of range"
  -- [REJECT] The proposer signature of blob_sidecar.signed_block_header is valid
  let proposer ← state.validators.get blockHeader.proposer_index.toNat
    "validate_blob_sidecar_gossip"
  let domain ← getDomain state DOMAIN_BEACON_PROPOSER
    (some (← computeEpochAtSlot P blockHeader.slot))
  if !blsVerify ctx.blsActive proposer.pubkey (computeSigningRoot blockHeader domain)
      blobSidecar.signed_block_header.signature then
    reject "invalid proposer signature on blob sidecar block header"
  -- [REJECT] The sidecar is from a higher slot than the sidecar's block's parent
  let parent : BeaconBlock P f ← liftModel (lookup store.blocks parentRoot "store.blocks[parent_root]")
  if blockHeader.slot ≤ parent.slot then
    reject "blob sidecar is not from a higher slot than its parent"
  -- [REJECT] The current finalized_checkpoint is an ancestor of the sidecar's block
  let finalizedCheckpointBlock ← getCheckpointBlock store parentRoot
    store.finalized_checkpoint.epoch
  if finalizedCheckpointBlock != store.finalized_checkpoint.root then
    reject "finalized checkpoint is not an ancestor of blob sidecar's block"
  -- [REJECT] The sidecar's inclusion proof is valid
  if !(← verifyBlobSidecarInclusionProof blobSidecar) then
    reject "invalid blob sidecar inclusion proof"
  -- [REJECT] The sidecar's blob is valid as verified by verify_blob_kzg_proof
  if !(← verifyBlobKzgProofM blobSidecar.blob blobSidecar.kzg_commitment blobSidecar.kzg_proof) then
    reject "invalid blob kzg proof"
  -- [REJECT] The sidecar is proposed by the expected proposer_index
  if blockHeader.proposer_index != (← expectedProposer ctx store parentRoot blockHeader.slot) then
    reject "blob sidecar proposer_index does not match expected proposer"
  -- Mark this blob sidecar as seen
  pure { seen with ext := { seen.ext with
    blob_sidecar_tuples := seen.ext.blob_sidecar_tuples ++ [sidecarTuple] } }

/-- `validate_data_column_sidecar_gossip` (`specs/fulu/p2p-interface.md:415`). -/
def validateDataColumnSidecarGossip (ctx : Ctx) (seen : SSeen P) (store : Store P f)
    (sidecar : DataColumnSidecar P) (currentTimeMs : U64) (subnetId : U64) : GM (SSeen P) := do
  let cfg := ctx.cfg
  let blockHeader := sidecar.signed_block_header.message
  -- [IGNORE] The sidecar is the first sidecar for the tuple
  let sidecarKey := (blockHeader.slot, blockHeader.proposer_index, sidecar.index)
  if seen.ext.data_column_sidecar_tuples.contains sidecarKey then
    ignore "already seen sidecar from this proposer for this slot and index"
  -- [REJECT] The sidecar is valid as verified by verify_data_column_sidecar
  if !(← verifyDataColumnSidecar cfg sidecar) then reject "invalid sidecar"
  -- [REJECT] The sidecar is for the correct subnet
  if (← computeSubnetForDataColumnSidecar cfg sidecar.index) != subnetId then
    reject "sidecar is for wrong subnet"
  -- [IGNORE] The sidecar is not from a future slot
  if ← isFutureSlot cfg store.genesis_time_ms blockHeader.slot currentTimeMs then
    ignore "sidecar is from a future slot"
  -- [IGNORE] The sidecar is from a slot greater than the latest finalized slot
  let finalizedSlot ← computeStartSlotAtEpoch P store.finalized_checkpoint.epoch
  if blockHeader.slot ≤ finalizedSlot then
    ignore "sidecar is not from a slot greater than the latest finalized slot"
  -- [IGNORE] The sidecar's block's parent has been seen
  let parentRoot := blockHeader.parent_root
  if !store.blocks.contains parentRoot then ignore "sidecar's parent has not been seen"
  -- [REJECT] The sidecar's block's parent passes validation
  if !store.block_states.contains parentRoot then reject "sidecar's parent failed validation"
  let state ← headState ctx store
  -- [REJECT] The proposer index is a valid validator index
  if blockHeader.proposer_index.toNat ≥ state.validators.length then
    reject "proposer index out of range"
  -- [REJECT] The proposer signature of sidecar.signed_block_header is valid
  let proposer ← state.validators.get blockHeader.proposer_index.toNat
    "validate_data_column_sidecar_gossip"
  let domain ← getDomain state DOMAIN_BEACON_PROPOSER
    (some (← computeEpochAtSlot P blockHeader.slot))
  if !blsVerify ctx.blsActive proposer.pubkey (computeSigningRoot blockHeader domain)
      sidecar.signed_block_header.signature then
    reject "invalid proposer signature on sidecar block header"
  -- [REJECT] The sidecar is from a higher slot than the sidecar's block's parent
  let parent : BeaconBlock P f ← liftModel (lookup store.blocks parentRoot "store.blocks[parent_root]")
  if blockHeader.slot ≤ parent.slot then reject "sidecar is not from a higher slot than its parent"
  -- [REJECT] The current finalized_checkpoint is an ancestor of the sidecar's block
  let finalizedCheckpointBlock ← getCheckpointBlock store parentRoot
    store.finalized_checkpoint.epoch
  if finalizedCheckpointBlock != store.finalized_checkpoint.root then
    reject "finalized checkpoint is not an ancestor of sidecar's block"
  -- [REJECT] The sidecar is valid as verified by verify_data_column_sidecar_inclusion_proof
  if !(← verifyDataColumnSidecarInclusionProof sidecar) then
    reject "invalid sidecar inclusion proof"
  -- [REJECT] The sidecar is valid as verified by verify_data_column_sidecar_kzg_proofs
  if !(← verifyDataColumnSidecarKzgProofs sidecar) then reject "invalid sidecar kzg proofs"
  -- [REJECT] The sidecar is proposed by the expected proposer_index
  if blockHeader.proposer_index != (← expectedProposer ctx store parentRoot blockHeader.slot) then
    reject "sidecar proposer_index does not match expected proposer"
  -- Mark this data column sidecar as seen
  pure { seen with ext := { seen.ext with
    data_column_sidecar_tuples := seen.ext.data_column_sidecar_tuples ++ [sidecarKey] } }

/-! ## `partial_data_column_sidecar` -/

/-- `seen.partial_data_column_headers.get(root)`. -/
def cachedPartialHeader (seen : SSeen P) (root : Root) : Option (PartialDataColumnHeader P) :=
  (seen.ext.partial_data_column_headers.find? (·.1 == root)).map (·.2)

/-- `seen.partial_data_column_headers[root] = header`. -/
def cachePartialHeader (seen : SSeen P) (root : Root) (header : PartialDataColumnHeader P) :
    SSeen P :=
  { seen with ext := { seen.ext with partial_data_column_headers :=
    (seen.ext.partial_data_column_headers.filter (·.1 != root)) ++ [(root, header)] } }

/-- The header part of `validate_partial_data_column_sidecar_gossip`
(`specs/fulu/partial-columns/p2p-interface.md:227`), from `if has_header:` through
`seen.partial_data_column_headers[group_id.beacon_block_root] = header`. -/
def validatePartialHeader (ctx : Ctx) (seen : SSeen P) (store : Store P f)
    (header : PartialDataColumnHeader P) (currentTimeMs : U64) (groupId : PartialDataColumnGroupID) :
    GM (SSeen P) := do
  let cfg := ctx.cfg
  let blockHeader := header.signed_block_header.message
  -- [REJECT] The received header MUST equal any previously validated header for this block
  if let some priorHeader := cachedPartialHeader seen groupId.beacon_block_root then
    if priorHeader != header then reject "header differs from previously validated header"
  -- [REJECT] The signed_block_header hash matches the partial message's group id
  if (Ssz.hashTreeRoot blockHeader : Root) != groupId.beacon_block_root then
    reject "header's block root does not match group id's block root"
  -- [REJECT] The header's kzg_commitments list is non-empty
  if header.kzg_commitments.toArray.size == 0 then reject "header's kzg_commitments is empty"
  -- [IGNORE] The header is not from a future slot
  if ← isFutureSlot cfg store.genesis_time_ms blockHeader.slot currentTimeMs then
    ignore "header is from a future slot"
  -- [IGNORE] The header is from a slot greater than the latest finalized slot
  let finalizedSlot ← computeStartSlotAtEpoch P store.finalized_checkpoint.epoch
  if blockHeader.slot ≤ finalizedSlot then
    ignore "header is not from a slot greater than the latest finalized slot"
  -- [IGNORE] The header's block's parent has been seen
  let parentRoot := blockHeader.parent_root
  if !store.blocks.contains parentRoot then ignore "header's parent has not been seen"
  -- [REJECT] The header's block's parent passes validation
  if !store.block_states.contains parentRoot then reject "header's parent failed validation"
  let state ← headState ctx store
  -- [REJECT] The proposer index is a valid validator index
  if blockHeader.proposer_index.toNat ≥ state.validators.length then
    reject "proposer index out of range"
  -- [REJECT] The proposer signature of signed_block_header is valid
  let proposer ← state.validators.get blockHeader.proposer_index.toNat
    "validate_partial_data_column_sidecar_gossip"
  let domain ← getDomain state DOMAIN_BEACON_PROPOSER
    (some (← computeEpochAtSlot P blockHeader.slot))
  if !blsVerify ctx.blsActive proposer.pubkey (computeSigningRoot blockHeader domain)
      header.signed_block_header.signature then
    reject "invalid proposer signature on header"
  -- [REJECT] The header is from a higher slot than the header's block's parent
  let parent : BeaconBlock P f ← liftModel (lookup store.blocks parentRoot "store.blocks[parent_root]")
  if blockHeader.slot ≤ parent.slot then reject "header is not from a higher slot than its parent"
  -- [REJECT] The current finalized_checkpoint is an ancestor of the header's block
  let finalizedCheckpointBlock ← getCheckpointBlock store parentRoot
    store.finalized_checkpoint.epoch
  if finalizedCheckpointBlock != store.finalized_checkpoint.root then
    reject "finalized checkpoint is not an ancestor of header's block"
  -- [REJECT] The header's kzg_commitments inclusion proof is valid
  if !(← verifyPartialDataColumnHeaderInclusionProof header) then
    reject "invalid header inclusion proof"
  -- [REJECT] The header is proposed by the expected proposer_index
  if blockHeader.proposer_index != (← expectedProposer ctx store parentRoot blockHeader.slot) then
    reject "header proposer_index does not match expected proposer"
  -- Mark this header as seen
  pure (cachePartialHeader seen groupId.beacon_block_root header)

/-- The cell part of `validate_partial_data_column_sidecar_gossip`, from `if has_cells:`. -/
def validatePartialCells (ctx : Ctx) (seen : SSeen P) (store : Store P f)
    (sidecar : PartialDataColumnSidecar P) (currentTimeMs : U64)
    (groupId : PartialDataColumnGroupID) (columnIndex : ColumnIndex) : GM Unit := do
  let cfg := ctx.cfg
  -- [IGNORE] A valid corresponding PartialDataColumnHeader has been seen
  let some header := cachedPartialHeader seen groupId.beacon_block_root
    | ignore "valid corresponding header has not been seen"
  let blockHeader := header.signed_block_header.message
  -- [IGNORE] The corresponding header is not from a future slot
  if ← isFutureSlot cfg store.genesis_time_ms blockHeader.slot currentTimeMs then
    ignore "corresponding header is from a future slot"
  -- [IGNORE] The corresponding header is from a slot greater than the latest finalized slot
  let finalizedSlot ← computeStartSlotAtEpoch P store.finalized_checkpoint.epoch
  if blockHeader.slot ≤ finalizedSlot then
    ignore "corresponding header is not from a slot greater than the latest finalized slot"
  -- [REJECT] The cells present bitmap length equals the number of header commitments
  if sidecar.cells_present_bitmap.bits.size != header.kzg_commitments.toArray.size then
    reject "bitmap length does not match commitments length"
  -- [REJECT] The sidecar's cell and proof data passes KZG verification
  if !(← verifyPartialDataColumnSidecarKzgProofs sidecar header.kzg_commitments columnIndex) then
    reject "invalid sidecar kzg proofs"

/-- `validate_partial_data_column_sidecar_gossip` (`specs/fulu/partial-columns/
p2p-interface.md:227`): the outcome and the cache pyspec holds afterwards (see the module
note). A model exception is the outer error. -/
def validatePartialDataColumnSidecarGossip (ctx : Ctx) (seen : SSeen P) (store : Store P f)
    (sidecar : PartialDataColumnSidecar P) (currentTimeMs : U64)
    (groupId : PartialDataColumnGroupID) (columnIndex : ColumnIndex) : M (Outcome × SSeen P) := do
  let headers := sidecar.header.toArray.toList
  let hasHeader := headers.length == 1
  let numCellsPresent := (sidecar.cells_present_bitmap.bits.toList.filter id).length
  let hasCells := numCellsPresent > 0
  let pre : GM Unit := do
    -- [REJECT] A header and/or cells are present in the message
    if !(hasHeader || hasCells) then reject "partial message is semantically empty"
    -- [REJECT] The cell count equals the number of set bits in the bitmap
    if sidecar.partial_column.toArray.size != numCellsPresent then
      reject "number of cells does not match number of set bits"
    -- [REJECT] The proof count equals the number of set bits in the bitmap
    if sidecar.kzg_proofs.toArray.size != numCellsPresent then
      reject "number of proofs does not match number of set bits"
  let (o, seen) ← outcome seen (do pre; pure seen)
  if o != .valid then return (o, seen)
  let (o, seen) ← match headers with
    | [header] => outcome seen (validatePartialHeader ctx seen store header currentTimeMs groupId)
    | _ => pure (Outcome.valid, seen)
  if o != .valid then return (o, seen)
  if hasCells then
    let (o, _) ← outcome () (validatePartialCells ctx seen store sidecar currentTimeMs groupId
      columnIndex)
    return (o, seen)
  pure (.valid, seen)

end JauneConsensus.Gossip
