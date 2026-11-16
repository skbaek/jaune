import JauneConsensus.GossipStore
import JauneConsensus.GloasGossip
import JauneConsensus.GloasForkChoice
import JauneConsensus.GloasTransition

/-!
# Store-dependent gossip validators, Gloas (goal `eip8282-gloas-cross-layer-v1`, M6)

Transcribed from `ethereum/consensus-specs` `v1.7.0-beta.4`, `specs/gloas/p2p-interface.md` and
`specs/gloas/partial-columns/p2p-interface.md`, over M4's Gloas fork-choice `Store`
(`JauneConsensus/GloasForkChoice.lean`) and `Gloas.BeaconState`. Each definition keeps the
spec's check order and reason strings verbatim:

* `validate_beacon_block_gossip` (`:565`), with `verify_block_body_operation_limits` (`:470`)
  and `verify_execution_requests_limits` (`:509`);
* `validate_beacon_aggregate_and_proof_gossip` (`:681`) and `validate_beacon_attestation_gossip`
  (`:1187`), with `verify_attestation_payload_status` (`:429`);
* `validate_execution_payload_envelope_gossip` (`:817`);
* `validate_payload_attestation_message_gossip` (`:891`);
* `validate_execution_payload_bid_gossip` (`:956`), with `is_bid_compatible_with_head` (`:401`);
* `validate_proposer_preferences_gossip` (`:1103`);
* `validate_data_column_sidecar_gossip` (`:1297`);
* `validate_partial_data_column_sidecar_gossip` (partial columns, which takes no `Seen`).

Inside `namespace JauneConsensus.Gloas` an unqualified accessor (`getDomain`, `getCurrentEpoch`,
`getBeaconCommittee`, `getHead`, `getCheckpointBlock`, ...) is the Gloas one. The Gloas `Seen`
fields beyond the store-free ones are `GloasStoreSeen`.
-/

namespace JauneConsensus.Gloas
open Jaune (Bytes B256)
open JauneConsensus.Gossip (GM ignore reject outcome Outcome Seen lookupSet addToSet
  isNonStrictSuperset isFutureSlot isCurrentSlot isCurrentOrPreviousEpoch isCurrentOrNextSlot
  isPastSlot isGasLimitTargetCompatible computeSubnetForDataColumnSidecar
  computeSubnetForAttestation PayloadValidationStatus liftModel TARGET_AGGREGATORS_PER_COMMITTEE)

variable {P : Preset}

/-! ## `Seen`, constants -/

/-- The store-dependent fields of the Gloas `Seen` (`specs/gloas/p2p-interface.md:192`).
Dictionaries are association lists. -/
structure GloasStoreSeen (P : Preset) where
  proposer_slots : List (Slot × ValidatorIndex) := []
  aggregator_epochs : List (Epoch × ValidatorIndex) := []
  aggregate_data_roots : List ((Root × CommitteeIndex) × List (List Bool)) := []
  attestation_validator_epochs : List (Epoch × ValidatorIndex) := []
  data_column_sidecar_tuples : List (Root × ColumnIndex) := []
  execution_payloads : List (Hash32 × ExecutionPayload P) := []
  execution_payload_envelopes : List (Root × BuilderIndex) := []
  payload_attestation_validators : List (Slot × ValidatorIndex) := []
  execution_payload_bids : List (Slot × Hash32 × Root × BuilderIndex) := []
  best_execution_payload_bid : List ((Slot × Hash32 × Root) × Gwei) := []
  proposer_preferences : List ((Slot × Root) × ProposerPreferences) := []

/-- The Gloas gossip cache. -/
abbrev GSeen (P : Preset) := Seen (GloasStoreSeen P)

/-- `DOMAIN_PROPOSER_PREFERENCES = DomainType('0x0D000000')` (`specs/gloas/beacon-chain.md:564`). -/
def DOMAIN_PROPOSER_PREFERENCES : DomainType := #v[0x0D, 0x00, 0x00, 0x00]

/-- `d[k] = v` on an association list. -/
def assocSet {κ α : Type} [BEq κ] (d : List (κ × α)) (k : κ) (v : α) : List (κ × α) :=
  (d.filter (·.1 != k)) ++ [(k, v)]

/-- `d.get(k)` on an association list. -/
def assocGet {κ α : Type} [BEq κ] (d : List (κ × α)) (k : κ) : Option α :=
  (d.find? (·.1 == k)).map (·.2)

/-! ## Helpers -/

/-- `store.block_states[get_head(store).root]`. -/
def gossipHeadState (ctx : Ctx) (store : Store P) : M (BeaconState P) := do
  lookup store.block_states (← getHead ctx.cfg store).root
    "store.block_states[get_head(store).root]"

/-- `is_aggregator(state, slot, index, slot_signature)` (`specs/phase0/validator.md:733`) over
the Gloas committee. -/
def isAggregatorGloas (state : BeaconState P) (slot : Slot) (index : CommitteeIndex)
    (slotSignature : BLSSignature) : M Bool := do
  let committee ← getBeaconCommittee state slot index
  let modulo := max 1 (committee.size / TARGET_AGGREGATORS_PER_COMMITTEE)
  let v ← bytesToUint64 ((hashBytes slotSignature.toArray.toList).take 8)
  pure (v.toNat % modulo == 0)

/-- `verify_block_body_operation_limits(body)` (`:470`). -/
def verifyBlockBodyOperationLimits (body : BeaconBlockBody P) : GM Unit := do
  -- [REJECT] The proposer slashing count is within the limit
  if body.proposer_slashings.length > P.MAX_PROPOSER_SLASHINGS then
    reject "too many proposer slashings"
  -- [REJECT] The attester slashing count is within the limit
  if body.attester_slashings.length > P.MAX_ATTESTER_SLASHINGS_ELECTRA then
    reject "too many attester slashings"
  -- [REJECT] The attestation count is within the limit
  if body.attestations.length > P.MAX_ATTESTATIONS_ELECTRA then reject "too many attestations"
  -- [REJECT] The block contains no deposits
  if body.deposits.length != 0 then reject "block must not contain deposits"
  -- [REJECT] The voluntary exit count is within the limit
  if body.voluntary_exits.length > P.MAX_VOLUNTARY_EXITS then reject "too many voluntary exits"
  -- [REJECT] The BLS to execution change count is within the limit
  if body.bls_to_execution_changes.length > P.MAX_BLS_TO_EXECUTION_CHANGES then
    reject "too many bls to execution changes"
  -- [REJECT] The payload attestation count is within the limit
  if body.payload_attestations.length > P.MAX_PAYLOAD_ATTESTATIONS then
    reject "too many payload attestations"

/-- `verify_execution_requests_limits(execution_requests)` (`:509`). -/
def verifyExecutionRequestsLimits (executionRequests : ExecutionRequests) : GM Unit := do
  -- [REJECT] The withdrawal request count is within the limit
  if executionRequests.withdrawals.length > P.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD then
    reject "too many withdrawal requests"
  -- [REJECT] The consolidation request count is within the limit
  if executionRequests.consolidations.length > P.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD then
    reject "too many consolidation requests"
  -- [REJECT] The builder deposit request count is within the limit
  if executionRequests.builder_deposits.length > P.MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD then
    reject "too many builder deposit requests"
  -- [REJECT] The builder exit request count is within the limit
  if executionRequests.builder_exits.length > P.MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD then
    reject "too many builder exit requests"

/-- `verify_attestation_payload_status(store, data, block_payload_statuses)` (`:429`). -/
def verifyAttestationPayloadStatus (store : Store P) (data : AttestationData)
    (blockPayloadStatuses : Root → Option PayloadValidationStatus) : GM Unit := do
  let blockRoot := data.beacon_block_root
  let block : BeaconBlock P ← liftModel (lookup store.blocks blockRoot "store.blocks[block_root]")
  -- [REJECT] For same-slot attestations, the payload cannot yet be present
  if block.slot == data.slot && data.index != U64.zero then
    reject "same-slot attestation must attest with index 0"
  if data.index != U64.one then return
  -- [IGNORE] The corresponding execution payload envelope has been seen and verified
  if !isPayloadVerified store blockRoot then
    ignore "execution payload envelope has not been seen"
  -- [IGNORE] The attested execution payload is optimistic
  let payloadStatus : PayloadValidationStatus :=
    match blockPayloadStatuses blockRoot with
    | some status => status
    | none => .notValidated
  if payloadStatus == .notValidated then ignore "attested payload is optimistic"
  -- [REJECT] The attested execution payload is processed and invalid
  if payloadStatus == .invalidated then reject "attested payload is invalid"

/-- `is_bid_compatible_with_head(store, bid)` (`:401`). -/
def isBidCompatibleWithHead (ctx : Ctx) (store : Store P) (bid : ExecutionPayloadBid) : M Bool := do
  let headNode ← getHead ctx.cfg store
  let headBlock ← lookup store.blocks headNode.root "store.blocks[head_node.root]"
  let headBid := headBlock.body.signed_execution_payload_bid.message
  let buildsOnParentBlock := bid.parent_block_root == headBlock.parent_root
  let buildsOnParentPayload := bid.parent_block_hash == headBid.parent_block_hash
  if buildsOnParentBlock && buildsOnParentPayload then return true
  if bid.parent_block_root != headNode.root then return false
  let buildsOnHeadPayload := bid.parent_block_hash == headBid.block_hash
  if ← shouldBuildOnFull store headNode bid.slot then return buildsOnHeadPayload
  return buildsOnParentPayload

/-! ## `beacon_block` -/

/-- `validate_beacon_block_gossip` (Gloas, `:565`). -/
def validateBeaconBlockGossip (ctx : Ctx) (seen : GSeen P) (store : Store P)
    (signedBeaconBlock : SignedBeaconBlock P) (currentTimeMs : U64) : GM (GSeen P) := do
  let cfg := ctx.cfg
  let block := signedBeaconBlock.message
  let bid := block.body.signed_execution_payload_bid.message
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
  -- [REJECT] The block body operation counts are within their limits
  verifyBlockBodyOperationLimits block.body
  -- [REJECT] The parent execution request counts are within their limits
  verifyExecutionRequestsLimits (P := P) block.body.parent_execution_requests
  -- [IGNORE] The block's parent has been seen (via gossip or non-gossip sources)
  if !store.blocks.contains block.parent_root then ignore "block's parent has not been seen"
  -- [REJECT] The block's parent passes validation
  if !store.block_states.contains block.parent_root then reject "block's parent is invalid"
  let state ← gossipHeadState ctx store
  -- [REJECT] The proposer index is a valid validator index
  if block.proposer_index.toNat ≥ state.validators.length then reject "proposer index out of range"
  -- [REJECT] The proposer signature is valid
  let proposer ← state.validators.get block.proposer_index.toNat "validate_beacon_block_gossip"
  let domain ← getDomain state DOMAIN_BEACON_PROPOSER (some (← computeEpochAtSlot P block.slot))
  if !blsVerify ctx.blsActive proposer.pubkey (computeSigningRoot block domain)
      signedBeaconBlock.signature then
    reject "invalid proposer signature"
  -- [IGNORE] If the parent block is full, the parent payload is valid
  if ← isParentNodeFull store block then
    if !isPayloadVerified store block.parent_root then ignore "parent payload is not verified"
  -- [REJECT] The block is from a higher slot than its parent
  let parent : BeaconBlock P ← liftModel (lookup store.blocks block.parent_root
    "store.blocks[block.parent_root]")
  if block.slot ≤ parent.slot then reject "block is not from a higher slot than its parent"
  -- [REJECT] The current finalized checkpoint is an ancestor of the block
  let finalizedCheckpointBlock ← getCheckpointBlock store block.parent_root
    store.finalized_checkpoint.epoch
  if finalizedCheckpointBlock != store.finalized_checkpoint.root then
    reject "finalized checkpoint is not an ancestor of block"
  -- [REJECT] The bid's blob KZG commitment count is within the per-epoch limit
  let maxBlobs := (← getBlobParameters cfg (← computeEpochAtSlot P block.slot)).maxBlobsPerBlock
  if bid.blob_kzg_commitments.length > maxBlobs.toNat then reject "too many blob kzg commitments"
  -- [REJECT] The bid's parent equals the block's parent
  if bid.parent_block_root != block.parent_root then
    reject "bid's parent does not equal block's parent"
  -- [REJECT] The block is proposed by the expected proposer for the slot
  let parentState : BeaconState P ← liftModel (lookup store.block_states block.parent_root
    "store.block_states[block.parent_root]")
  let parentState ← processSlots ctx parentState block.slot
  if block.proposer_index != (← getBeaconProposerIndex parentState) then
    reject "block proposer_index does not match expected proposer"
  -- [REJECT] If the parent is not full, the bid builds on the parent's execution head
  if !(← isParentNodeFull store block) then
    if bid.parent_block_hash != parentState.latest_block_hash then
      reject "bid does not build on the parent's execution head"
  -- Mark this block as seen
  pure { seen with ext := { seen.ext with
    proposer_slots := seen.ext.proposer_slots ++ [proposerSlotKey] } }

/-! ## `beacon_aggregate_and_proof`, `beacon_attestation_{subnet_id}` -/

/-- `validate_beacon_aggregate_and_proof_gossip` (Gloas, `:681`). -/
def validateBeaconAggregateAndProofGossip (ctx : Ctx) (seen : GSeen P) (store : Store P)
    (signedAggregateAndProof : SignedAggregateAndProof P) (currentTimeMs : U64)
    (blockPayloadStatuses : Root → Option PayloadValidationStatus) : GM (GSeen P) := do
  let cfg := ctx.cfg
  let aggregateAndProof := signedAggregateAndProof.message
  let aggregate := aggregateAndProof.aggregate
  let aggregationBits := aggregate.aggregation_bits.bits.toList
  -- [REJECT] The aggregate attestation's data index is 0 or 1
  if aggregate.data.index > U64.one then reject "aggregate data index must be 0 or 1"
  -- [REJECT] Exactly one committee is specified by the committee bits
  let committeeIndices ← getCommitteeIndices aggregate.committee_bits
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
  let state ← gossipHeadState ctx store
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
  if !(← isAggregatorGloas state aggregate.data.slot index aggregateAndProof.selection_proof) then
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
  -- The attested payload status is consistent with the block's execution payload
  verifyAttestationPayloadStatus store aggregate.data blockPayloadStatuses
  -- Mark this aggregate as seen
  pure { seen with ext := { seen.ext with
    aggregator_epochs := seen.ext.aggregator_epochs ++ [aggregatorEpochKey]
    aggregate_data_roots :=
      addToSet seen.ext.aggregate_data_roots aggregateCacheKey aggregationBits } }

/-- `validate_beacon_attestation_gossip` (Gloas, `:1187`). -/
def validateBeaconAttestationGossip (ctx : Ctx) (seen : GSeen P) (store : Store P)
    (attestation : SingleAttestation) (currentTimeMs : U64) (subnetId : U64)
    (blockPayloadStatuses : Root → Option PayloadValidationStatus) : GM (GSeen P) := do
  let cfg := ctx.cfg
  let data := attestation.data
  let committeeIndex := attestation.committee_index
  let attesterIndex := attestation.attester_index
  let targetEpoch := data.target.epoch
  -- [IGNORE] No other valid attestation seen for this target epoch and validator
  let attestationEpochKey := (targetEpoch, attesterIndex)
  if seen.ext.attestation_validator_epochs.contains attestationEpochKey then
    ignore "already seen attestation for this epoch and validator"
  -- [REJECT] The attestation's data index is 0 or 1
  if data.index > U64.one then reject "attestation data index must be 0 or 1"
  -- [IGNORE] The block being voted for has been seen (via gossip or non-gossip sources)
  let blockRoot := data.beacon_block_root
  if !store.blocks.contains blockRoot then ignore "block being voted for has not been seen"
  -- [REJECT] The block being voted for passes validation
  if !store.block_states.contains blockRoot then reject "block being voted for failed validation"
  let state ← gossipHeadState ctx store
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
  -- [IGNORE] The current finalized checkpoint is an ancestor of the block
  let finalizedCheckpointBlock ← getCheckpointBlock store blockRoot
    store.finalized_checkpoint.epoch
  if finalizedCheckpointBlock != store.finalized_checkpoint.root then
    ignore "finalized checkpoint is not an ancestor of block"
  -- The attested payload status is consistent with the block's execution payload
  verifyAttestationPayloadStatus store data blockPayloadStatuses
  -- Mark this attestation as seen
  pure { seen with ext := { seen.ext with
    attestation_validator_epochs := seen.ext.attestation_validator_epochs ++ [attestationEpochKey] } }

/-! ## `execution_payload`, `payload_attestation_message` -/

/-- `validate_execution_payload_envelope_gossip` (`:817`). -/
def validateExecutionPayloadEnvelopeGossip (ctx : Ctx) (seen : GSeen P) (store : Store P)
    (signedEnvelope : SignedExecutionPayloadEnvelope P) : GM (GSeen P) := do
  let envelope := signedEnvelope.message
  let payload := envelope.payload
  let blockRoot := envelope.beacon_block_root
  -- [IGNORE] The node has not seen another valid envelope for this block root from this builder
  let envelopeKey := (blockRoot, envelope.builder_index)
  if seen.ext.execution_payload_envelopes.contains envelopeKey then
    ignore "already seen envelope for this block root from this builder"
  -- [IGNORE] The envelope's block root has been seen (via gossip or non-gossip sources)
  if !store.blocks.contains blockRoot then ignore "envelope's block has not been seen"
  -- [REJECT] The envelope's block passes validation
  if !store.block_states.contains blockRoot then reject "envelope's block failed validation"
  let state : BeaconState P ← liftModel (lookup store.block_states blockRoot
    "store.block_states[block_root]")
  -- [IGNORE] The envelope is from a slot greater than or equal to the latest finalized slot
  let finalizedSlot ← computeStartSlotAtEpoch P store.finalized_checkpoint.epoch
  if payload.slot_number < finalizedSlot then
    ignore "envelope is from a slot before the latest finalized slot"
  let block : BeaconBlock P ← liftModel (lookup store.blocks blockRoot "store.blocks[block_root]")
  let bid := block.body.signed_execution_payload_bid.message
  -- [REJECT] The block's slot matches the payload's slot number
  if block.slot != payload.slot_number then
    reject "block's slot does not match payload's slot number"
  -- [REJECT] The envelope is from the builder committed to by the bid
  if envelope.builder_index != bid.builder_index then
    reject "envelope's builder index does not match the bid's builder index"
  -- [REJECT] The payload's block hash matches the bid's block hash
  if payload.block_hash != bid.block_hash then
    reject "payload's block hash does not match the bid's block hash"
  -- [REJECT] The envelope's execution requests root matches the bid's execution requests root
  if (Ssz.hashTreeRoot envelope.execution_requests : Root) != bid.execution_requests_root then
    reject "envelope's execution requests root does not match the bid's"
  -- [REJECT] The execution request counts are within their limits
  verifyExecutionRequestsLimits (P := P) envelope.execution_requests
  -- [REJECT] The number of withdrawals is within the limit
  if payload.withdrawals.length > P.MAX_WITHDRAWALS_PER_PAYLOAD then reject "too many withdrawals"
  -- [REJECT] The envelope signature is valid
  if !(← verifyExecutionPayloadEnvelopeSignatureB ctx.blsActive state signedEnvelope) then
    reject "invalid envelope signature"
  -- Mark this envelope as seen and store its payload
  pure { seen with ext := { seen.ext with
    execution_payload_envelopes := seen.ext.execution_payload_envelopes ++ [envelopeKey]
    execution_payloads := assocSet seen.ext.execution_payloads payload.block_hash payload } }

/-- `validate_payload_attestation_message_gossip` (`:891`). -/
def validatePayloadAttestationMessageGossip (ctx : Ctx) (seen : GSeen P) (store : Store P)
    (message : PayloadAttestationMessage) (currentTimeMs : U64) : GM (GSeen P) := do
  let cfg := ctx.cfg
  let data := message.data
  let validatorIndex := message.validator_index
  -- [REJECT] The payload attestation's slot is at or after the Gloas fork
  if (← computeEpochAtSlot P data.slot).toNat < cfg.GLOAS_FORK_EPOCH then
    reject "payload attestation's slot is pre-gloas"
  -- [IGNORE] This is the first valid payload attestation from this validator index
  let payloadAttestationKey := (data.slot, validatorIndex)
  if seen.ext.payload_attestation_validators.contains payloadAttestationKey then
    ignore "already seen payload attestation from this validator"
  -- [IGNORE] The payload attestation's slot is for the current slot
  if !(← isCurrentSlot cfg store.genesis_time_ms data.slot currentTimeMs) then
    ignore "payload attestation is not for the current slot"
  -- [IGNORE] The payload attestation's block has been seen (via gossip or non-gossip sources)
  if !store.blocks.contains data.beacon_block_root then
    ignore "payload attestation's block has not been seen"
  -- [REJECT] The payload attestation's block passes validation
  if !store.block_states.contains data.beacon_block_root then
    reject "payload attestation's block failed validation"
  -- [IGNORE] The payload attestation's block is at the assigned slot
  let block : BeaconBlock P ← liftModel (lookup store.blocks data.beacon_block_root
    "store.blocks[data.beacon_block_root]")
  if block.slot != data.slot then ignore "payload attestation's block is not at the assigned slot"
  let state ← gossipHeadState ctx store
  -- [REJECT] The validator index is valid
  if validatorIndex.toNat ≥ state.validators.length then reject "validator index out of range"
  -- [REJECT] The validator is a member of the payload timeliness committee
  if !(← getPtc cfg state data.slot).toArray.contains validatorIndex then
    reject "validator is not in the payload timeliness committee"
  -- [REJECT] The signature is valid
  let validator ← state.validators.get validatorIndex.toNat
    "validate_payload_attestation_message_gossip"
  let domain ← getDomain state DOMAIN_PTC_ATTESTER (some (← computeEpochAtSlot P data.slot))
  if !blsVerify ctx.blsActive validator.pubkey (computeSigningRoot data domain)
      message.signature then
    reject "invalid payload attestation signature"
  -- Mark this payload_attestation as seen
  pure { seen with ext := { seen.ext with
    payload_attestation_validators :=
      seen.ext.payload_attestation_validators ++ [payloadAttestationKey] } }

/-! ## `execution_payload_bid`, `proposer_preferences` -/

/-- `validate_execution_payload_bid_gossip` (`:956`). -/
def validateExecutionPayloadBidGossip (ctx : Ctx) (seen : GSeen P) (store : Store P)
    (signedBid : SignedExecutionPayloadBid) (currentTimeMs : U64) : GM (GSeen P) := do
  let cfg := ctx.cfg
  let bid := signedBid.message
  -- [IGNORE] This is the first bid for this slot, parent, and builder
  let bidKey := (bid.slot, bid.parent_block_hash, bid.parent_block_root, bid.builder_index)
  if seen.ext.execution_payload_bids.contains bidKey then
    ignore "already seen valid bid for this slot, parent, and builder"
  -- [IGNORE] This is the highest value bid seen for the slot and parent
  let bestBidKey := (bid.slot, bid.parent_block_hash, bid.parent_block_root)
  if let some best := assocGet seen.ext.best_execution_payload_bid bestBidKey then
    if bid.value ≤ best then
      ignore "bid is not the highest value bid seen for this slot and parent"
  -- [IGNORE] The bid's slot is the current slot or the next slot
  if !(← isCurrentOrNextSlot cfg store.genesis_time_ms bid.slot currentTimeMs) then
    ignore "bid's slot is not the current or next slot"
  -- [REJECT] The bid's execution payment is zero
  if bid.execution_payment != U64.zero then reject "bid's execution payment must be zero"
  -- [REJECT] The bid's block hash is not equal to its parent block hash
  if bid.block_hash == bid.parent_block_hash then
    reject "bid's block hash equals its parent block hash"
  -- [REJECT] The bid's blob KZG commitment count is within the per-epoch limit
  let proposalEpoch ← computeEpochAtSlot P bid.slot
  let maxBlobs := (← getBlobParameters cfg proposalEpoch).maxBlobsPerBlock
  if bid.blob_kzg_commitments.length > maxBlobs.toNat then reject "too many blob kzg commitments"
  -- [IGNORE] The bid's parent block root is a known beacon block
  if !store.blocks.contains bid.parent_block_root then
    ignore "bid's parent block root is not a known beacon block"
  -- [REJECT] The bid is for a higher slot than its parent block
  let parent : BeaconBlock P ← liftModel (lookup store.blocks bid.parent_block_root
    "store.blocks[bid.parent_block_root]")
  if bid.slot ≤ parent.slot then reject "bid's slot is not higher than its parent's slot"
  -- [IGNORE] The bid's parent block has been imported
  if !store.block_states.contains bid.parent_block_root then
    ignore "bid's parent block post-state is unavailable"
  let state : BeaconState P ← liftModel (lookup store.block_states bid.parent_block_root
    "store.block_states[bid.parent_block_root]")
  -- [IGNORE] The bid's slot is within the parent's proposer lookahead
  if proposalEpoch > (← U64.add? (← getCurrentEpoch state) (← c64 P.MIN_SEED_LOOKAHEAD)
      "get_current_epoch(state) + MIN_SEED_LOOKAHEAD") then
    ignore "bid's slot is past the parent's proposer lookahead"
  -- [IGNORE] The matching proposer preferences have been seen
  let dependentRoot ← getShufflingDependentRoot store bid.parent_block_root proposalEpoch
  let some proposerPreferences := assocGet seen.ext.proposer_preferences (bid.slot, dependentRoot)
    | ignore "matching proposer preferences have not been seen"
  -- [IGNORE] The bid's fee recipient matches the proposer's preference
  if bid.fee_recipient != proposerPreferences.fee_recipient then
    ignore "bid's fee recipient does not match the proposer's preference"
  -- [IGNORE] The bid's parent block hash is the hash of a known execution payload
  let some parentPayload := assocGet seen.ext.execution_payloads bid.parent_block_hash
    | ignore "bid's parent block hash is not a known execution payload"
  -- [IGNORE] The bid's gas limit is compatible with the proposer's target gas limit
  if !(← isGasLimitTargetCompatible parentPayload.gas_limit bid.gas_limit
      proposerPreferences.target_gas_limit) then
    ignore "bid's gas limit is not compatible with the proposer's target"
  -- [IGNORE] The bid is compatible with the current head branch
  if !(← isBidCompatibleWithHead ctx store bid) then
    ignore "bid is not compatible with the current head branch"
  -- [REJECT] The bid's previous randao is correct
  if bid.prev_randao != (← getRandaoMix state (← getCurrentEpoch state)) then
    reject "bid's previous randao is incorrect"
  let state ← processSlots ctx state bid.slot
  -- [REJECT] The builder index is valid
  if bid.builder_index.toNat ≥ state.builders.length then reject "builder index out of range"
  let builder ← state.builders.get bid.builder_index.toNat "validate_execution_payload_bid_gossip"
  -- [REJECT] The builder is a payload builder
  if builder.version != PAYLOAD_BUILDER_VERSION then reject "builder is not a payload builder"
  -- [REJECT] The builder is active
  if !(← isActiveBuilder state bid.builder_index) then reject "builder is not active"
  -- [IGNORE] The builder can cover the bid
  if !(← canBuilderCoverBid state bid.builder_index bid.value) then
    ignore "builder cannot cover bid value"
  -- [IGNORE] The parent's payload does not try to exit the builder
  if bid.parent_block_hash == state.latest_execution_payload_bid.block_hash then
    let envelope : ExecutionPayloadEnvelope P ← liftModel (lookup store.payloads
      bid.parent_block_root "store.payloads[bid.parent_block_root]")
    for request in envelope.execution_requests.builder_exits.toArray do
      if request.pubkey == builder.pubkey then
        if request.source_address == builder.execution_address then
          ignore "builder may exit"
  -- [REJECT] The bid signature is valid
  if !(← verifyExecutionPayloadBidSignature ctx state signedBid) then reject "invalid bid signature"
  -- Mark this bid as seen and update the highest-value bid for this slot/parent
  pure { seen with ext := { seen.ext with
    execution_payload_bids := seen.ext.execution_payload_bids ++ [bidKey]
    best_execution_payload_bid := assocSet seen.ext.best_execution_payload_bid bestBidKey bid.value } }

/-- `validate_proposer_preferences_gossip` (`:1103`). -/
def validateProposerPreferencesGossip (ctx : Ctx) (seen : GSeen P) (store : Store P)
    (signed : SignedProposerPreferences) (currentTimeMs : U64) : GM (GSeen P) := do
  let cfg := ctx.cfg
  let preferences := signed.message
  -- [IGNORE] These are the first valid preferences seen for this dependent root and slot
  let prefsKey := (preferences.proposal_slot, preferences.dependent_root)
  if (assocGet seen.ext.proposer_preferences prefsKey).isSome then
    ignore "already seen preferences for this dependent root and proposal slot"
  -- [IGNORE] The proposal epoch is after the Gloas upgrade
  let proposalEpoch ← computeEpochAtSlot P preferences.proposal_slot
  if proposalEpoch.toNat < cfg.GLOAS_FORK_EPOCH then ignore "proposal epoch is pre-gloas"
  -- [IGNORE] The proposal slot has not started yet
  if ← isPastSlot cfg store.genesis_time_ms preferences.proposal_slot currentTimeMs then
    ignore "proposal slot has already started"
  -- [IGNORE] The proposer for the proposal slot is known
  let lookaheadStartSlot ← computeShufflingLookaheadStartSlot P proposalEpoch
  if ← isFutureSlot cfg store.genesis_time_ms lookaheadStartSlot currentTimeMs then
    ignore "proposer for the proposal slot is not yet known"
  -- [IGNORE] The dependent block has been seen (via gossip or non-gossip sources)
  if !store.blocks.contains preferences.dependent_root then
    ignore "dependent block has not been seen"
  -- [IGNORE] The dependent block passes validation
  if !store.block_states.contains preferences.dependent_root then
    ignore "dependent block failed validation"
  -- [REJECT] The dependent block's slot is not after the shuffling dependent slot
  let dependentSlot ← computeShufflingDependentSlot P proposalEpoch
  let dependentBlock : BeaconBlock P ← liftModel (lookup store.blocks preferences.dependent_root
    "store.blocks[preferences.dependent_root]")
  if dependentBlock.slot > dependentSlot then
    reject "dependent block is after the shuffling dependent slot"
  -- [IGNORE] The dependent block is a possible dependent block for the proposer lookahead
  if !(← isValidDependentRoot cfg store preferences.dependent_root dependentSlot) then
    ignore "dependent block is not a possible dependent block"
  let state : BeaconState P ← liftModel (lookup store.block_states preferences.dependent_root
    "store.block_states[preferences.dependent_root]")
  let state ← if state.slot < lookaheadStartSlot then do
      processSlots ctx state lookaheadStartSlot
    else pure state
  -- [REJECT] The validator is the proposer for the given slot in the proposer lookahead
  let lookaheadIndex ← U64.sub? preferences.proposal_slot lookaheadStartSlot
    "preferences.proposal_slot - lookahead_start_slot"
  let proposer ← state.proposer_lookahead.get lookaheadIndex.toNat "state.proposer_lookahead"
  if proposer != preferences.validator_index then
    reject "validator is not the proposer for the given slot"
  -- [REJECT] The signature is valid
  let validator ← state.validators.get preferences.validator_index.toNat
    "validate_proposer_preferences_gossip"
  -- `compute_fork_version` is the Gloas chain (`GossipCore.lean`), not `LightClient.lean`'s Fulu one
  let domain := computeDomain DOMAIN_PROPOSER_PREFERENCES
    (← Gossip.computeForkVersion cfg proposalEpoch) state.genesis_validators_root
  if !blsVerify ctx.blsActive validator.pubkey (computeSigningRoot preferences domain)
      signed.signature then
    reject "invalid proposer preferences signature"
  -- Mark these preferences as seen
  pure { seen with ext := { seen.ext with
    proposer_preferences := assocSet seen.ext.proposer_preferences prefsKey preferences } }

/-! ## Sidecars -/

/-- `validate_data_column_sidecar_gossip` (Gloas, `:1297`). -/
def validateDataColumnSidecarGossip (ctx : Ctx) (seen : GSeen P) (store : Store P)
    (sidecar : DataColumnSidecar P) (currentTimeMs : U64) (subnetId : U64) : GM (GSeen P) := do
  let cfg := ctx.cfg
  -- [IGNORE] This is the first sidecar seen for this block root and column index
  let sidecarKey := (sidecar.beacon_block_root, sidecar.index)
  if seen.ext.data_column_sidecar_tuples.contains sidecarKey then
    ignore "already seen sidecar for this block root and index"
  -- [REJECT] The sidecar is for the correct subnet
  if (← computeSubnetForDataColumnSidecar cfg sidecar.index) != subnetId then
    reject "sidecar is for wrong subnet"
  -- [IGNORE] The sidecar is not from a future slot
  if ← isFutureSlot cfg store.genesis_time_ms sidecar.slot currentTimeMs then
    ignore "sidecar is from a future slot"
  -- [IGNORE] A block for the sidecar has been seen (via gossip or non-gossip sources)
  if !store.blocks.contains sidecar.beacon_block_root then
    ignore "block for sidecar's beacon block root has not been seen"
  -- [REJECT] The block for the sidecar passes validation
  if !store.block_states.contains sidecar.beacon_block_root then
    reject "block for sidecar's beacon block root failed validation"
  let block : BeaconBlock P ← liftModel (lookup store.blocks sidecar.beacon_block_root
    "store.blocks[sidecar.beacon_block_root]")
  -- [REJECT] The sidecar's slot matches the slot of the block
  if sidecar.slot != block.slot then reject "sidecar's slot does not match block's slot"
  let commitments := block.body.signed_execution_payload_bid.message.blob_kzg_commitments.toArray.toList
  -- [REJECT] The sidecar passes structural validation
  if !verifyDataColumnSidecar sidecar commitments then reject "invalid sidecar"
  -- [REJECT] The sidecar's column data passes KZG verification
  if !(← verifyDataColumnSidecarKzgProofs sidecar commitments) then
    reject "invalid sidecar kzg proofs"
  -- Mark this data column sidecar as seen
  pure { seen with ext := { seen.ext with
    data_column_sidecar_tuples := seen.ext.data_column_sidecar_tuples ++ [sidecarKey] } }

/-- `verify_partial_data_column_sidecar_kzg_proofs(sidecar, all_commitments, column_index)`
(Fulu's, over the Gloas partial sidecar): `all_commitments[index]` raises past the end. -/
def verifyPartialDataColumnSidecarKzgProofsGloas (sidecar : PartialDataColumnSidecar P)
    (allCommitments : List KZGCommitment) (columnIndex : ColumnIndex) : M Bool := do
  let blobIndices := ((sidecar.cells_present_bitmap.bits.toList.zipIdx).filter (·.1)).map (·.2)
  let cellIndices := List.replicate blobIndices.length columnIndex.toNat
  let commitments ← blobIndices.mapM fun i =>
    getAt allCommitments.toArray i "verify_partial_data_column_sidecar_kzg_proofs: all_commitments"
  verifyCellKzgProofBatchM (commitments.map (·.toArray.toList)) cellIndices
    (sidecar.partial_column.toArray.toList.map (·.toArray.toList))
    (sidecar.kzg_proofs.toArray.toList.map (·.toArray.toList))

/-- `validate_partial_data_column_sidecar_gossip` (`specs/gloas/partial-columns/
p2p-interface.md`): no `Seen` and no `current_time_ms`. -/
def validatePartialDataColumnSidecarGossip (store : Store P) (sidecar : PartialDataColumnSidecar P)
    (groupId : PartialDataColumnGroupID) (columnIndex : ColumnIndex) : GM Unit := do
  let numCellsPresent := (sidecar.cells_present_bitmap.bits.toList.filter id).length
  -- [REJECT] The message contains at least one cell
  if numCellsPresent == 0 then reject "partial message is semantically empty"
  -- [REJECT] The cell count equals the number of set bits in the bitmap
  if sidecar.partial_column.length != numCellsPresent then
    reject "number of cells does not match number of set bits"
  -- [REJECT] The proof count equals the number of set bits in the bitmap
  if sidecar.kzg_proofs.length != numCellsPresent then
    reject "number of proofs does not match number of set bits"
  -- [IGNORE] The group ID's block has been seen (via gossip or non-gossip sources)
  if !store.blocks.contains groupId.beacon_block_root then
    ignore "group id's block has not been seen"
  -- [REJECT] The group ID's block passes validation
  if !store.block_states.contains groupId.beacon_block_root then
    reject "group id's block failed validation"
  let block : BeaconBlock P ← liftModel (lookup store.blocks groupId.beacon_block_root
    "store.blocks[group_id.beacon_block_root]")
  -- [REJECT] The group ID's slot matches the slot of the block
  if groupId.slot != block.slot then reject "group id's slot does not match the block's slot"
  let commitments := block.body.signed_execution_payload_bid.message.blob_kzg_commitments.toArray.toList
  -- [REJECT] The cells present bitmap length equals the number of bid commitments
  if sidecar.cells_present_bitmap.bits.size != commitments.length then
    reject "bitmap length does not match commitments length"
  -- [REJECT] The sidecar's cell and proof data passes KZG verification
  if !(← verifyPartialDataColumnSidecarKzgProofsGloas sidecar commitments columnIndex) then
    reject "invalid sidecar kzg proofs"

end JauneConsensus.Gloas
