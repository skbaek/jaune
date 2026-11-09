import JauneConsensus.GloasOperations

/-!
# Gloas block processing (goal `eip8282-gloas-cross-layer-v1`, U4)

`process_block` (`specs/gloas/beacon-chain.md:1754`) and the steps it calls that are not in
`GloasWithdrawals.lean` or `GloasOperations.lean`, transcribed from `ethereum/consensus-specs`
`v1.7.0-beta.4` over `JauneConsensus.Gloas.BeaconState`:

* reused by reference: `process_block_header`, `process_randao`, `process_eth1_data` (phase0)
  and `process_sync_aggregate` (Altair);
* new in Gloas: `apply_parent_execution_payload` (:1776, with its four EIP-7688 request caps at
  :1792-1795; validator deposit requests are uncapped), `process_parent_execution_payload`
  (:1833), `verify_execution_payload_bid_signature` (:2146), `can_builder_cover_bid` (:1181) and
  `process_execution_payload_bid` (:2159);
* modified in Gloas: `process_operations` (:2220, with the six EIP-7688 operation caps at
  :2241-2247, `assert len(body.deposits) == 0`, `parent_slot` to `process_attestation`, payload
  attestations, and no execution requests: those are the parent's, applied by
  `apply_parent_execution_payload`).

`get_execution_requests_list` is U6's (`GloasAccessors.lean`). Each execution request keeps its
own processing call (`for_ops`), so the per-request structure is visible to the B rows.
-/

namespace JauneConsensus

namespace Bitvector

/-- `bits[i] = b`, rejecting out of range. -/
def set {n : Nat} (xs : Bitvector n) (i : Nat) (b : Bool) (site : String) : M (Bitvector n) :=
  if h : i < xs.bits.size then pure ⟨xs.bits.set i b h, by simpa using xs.size_eq⟩
  else throw (.index site i xs.bits.size)

end Bitvector

namespace Gloas

open Jaune

variable {P : Preset}

/-- `ExecutionRequests.empty()`: every list empty. -/
def ExecutionRequests.empty : ExecutionRequests :=
  { deposits := ProgressiveListS.empty, withdrawals := ProgressiveListS.empty,
    consolidations := ProgressiveListS.empty, builder_deposits := ProgressiveListS.empty,
    builder_exits := ProgressiveListS.empty }

/-! ## Header, RANDAO, eth1 data (phase0) -/

/-- `process_block_header(state, block)` (phase0). -/
def processBlockHeader (state : BeaconState P) (block : BeaconBlock P) : M (BeaconState P) := do
  let site := "process_block_header"
  require (block.slot == state.slot) s!"{site}: block.slot == state.slot"
  require (state.latest_block_header.slot < block.slot) s!"{site}: newer block"
  require (block.proposer_index == (← getBeaconProposerIndex state)) s!"{site}: proposer index"
  require (block.parent_root == Ssz.hashTreeRoot state.latest_block_header) s!"{site}: parent root"
  let state := { state with latest_block_header :=
    { slot := block.slot, proposer_index := block.proposer_index, parent_root := block.parent_root,
      state_root := Jaune.Bytes.toB256 (List.replicate 32 0),
      body_root := Ssz.hashTreeRoot block.body } }
  let proposer ← state.validators.get block.proposer_index.toNat site
  require (!proposer.slashed) s!"{site}: proposer not slashed"
  pure state

/-- `process_randao(state, body)` (phase0). -/
def processRandao (ctx : Ctx) (state : BeaconState P) (body : BeaconBlockBody P) :
    M (BeaconState P) := do
  let site := "process_randao"
  let epoch ← getCurrentEpoch state
  let proposer ← state.validators.get (← getBeaconProposerIndex state).toNat site
  let root := computeSigningRoot epoch (← getDomain state DOMAIN_RANDAO (some epoch))
  require (blsVerify ctx.blsActive proposer.pubkey root body.randao_reveal) s!"{site}: bls.Verify"
  let mix := xor (← getRandaoMix state epoch) (hash (vbytes body.randao_reveal))
  let i ← epoch.mod? (← c64 P.EPOCHS_PER_HISTORICAL_VECTOR) site
  pure { state with randao_mixes := ← state.randao_mixes.set i.toNat mix site }

/-- `process_eth1_data(state, body)` (phase0). -/
def processEth1Data (state : BeaconState P) (body : BeaconBlockBody P) : M (BeaconState P) := do
  let votes ← state.eth1_data_votes.push body.eth1_data "process_eth1_data"
  let state := { state with eth1_data_votes := votes }
  let count := (votes.toArray.filter (· == body.eth1_data)).size
  if count * 2 > P.EPOCHS_PER_ETH1_VOTING_PERIOD * P.SLOTS_PER_EPOCH then
    pure { state with eth1_data := body.eth1_data }
  else pure state

/-! ## Sync aggregate (Altair) -/

/-- `process_sync_aggregate(state, sync_aggregate)` (Altair, the optimized form of `v1.6.0` on).
The participant key is computed only when the signature is verified (`bls_active`); a key that
does not decode fails the verification. -/
def processSyncAggregate (ctx : Ctx) (state : BeaconState P) (sa : SyncAggregate P) :
    M (BeaconState P) := do
  let site := "process_sync_aggregate"
  let pubkeys := state.current_sync_committee.pubkeys.toArray
  let bits := sa.sync_committee_bits.bits
  let participants := (bits.filter id).size
  let participantPubkeys : List Bytes ←
    if participants == P.SYNC_COMMITTEE_SIZE then
      -- All members participated - use precomputed aggregate key
      pure [vbytes state.current_sync_committee.aggregate_pubkey]
    else if participants > P.SYNC_COMMITTEE_SIZE / 2 then do
      -- More than half participated - subtract non-participant keys
      let nonPart := ((pubkeys.zip bits).filter (fun (_, b) => !b)).toList.map (vbytes ·.1)
      -- `eth_aggregate_pubkeys` is `bls.AggregatePKs`, which from `v1.7.0-beta.4` pyspec computes
      -- whatever the BLS switch (`eth_consensus_specs/utils/bls.py`)
      let nonAgg ← ethAggregatePubkeysM nonPart
      let full ← liftCrypto s!"{site}: bls.bytes48_to_G1(aggregate_pubkey)"
        (pubkeyToPoint (vbytes state.current_sync_committee.aggregate_pubkey))
      let nonP ← liftCrypto s!"{site}: bls.bytes48_to_G1(non_participant_aggregate)"
        (pubkeyToPoint nonAgg)
      pure [g1Compress (full + -nonP)]
    else
      -- Less than half participated - aggregate participant keys
      pure (((pubkeys.zip bits).filter (·.2)).toList.map (vbytes ·.1))
  let prevSlot ← (if U64.one < state.slot then state.slot else U64.one).sub? U64.one site
  let domain ← getDomain state DOMAIN_SYNC_COMMITTEE (some (← computeEpochAtSlot P prevSlot))
  let root := computeSigningRoot (← getBlockRootAtSlot state prevSlot) domain
  let verified := !ctx.blsActive ||
    ethFastAggregateVerify participantPubkeys root.toBytes (vbytes sa.sync_committee_signature)
  require verified s!"{site}: eth_fast_aggregate_verify"
  let totalActiveIncrements ← (← getTotalActiveBalance state).div?
    (← c64 P.EFFECTIVE_BALANCE_INCREMENT) site
  let totalBaseRewards ← (← getBaseRewardPerIncrement state).mul? totalActiveIncrements site
  let maxParticipant ← (← (← totalBaseRewards.mul? (← c64 SYNC_REWARD_WEIGHT) site).div?
    (← c64 WEIGHT_DENOMINATOR) site).div? (← c64 P.SLOTS_PER_EPOCH) site
  let participantReward ← maxParticipant.div? (← c64 P.SYNC_COMMITTEE_SIZE) site
  let proposerReward ← (← participantReward.mul? (← c64 PROPOSER_WEIGHT) site).div?
    (← c64 (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT)) site
  let allPubkeys := state.validators.toArray.map (·.pubkey)
  let mut committeeIndices := #[]
  for pk in pubkeys do
    match allPubkeys.findIdx? (· == pk) with
    | some i => committeeIndices := committeeIndices.push (← U64.ofNat? i site)
    | none => throw (.assert s!"{site}: all_pubkeys.index(pubkey)")
  let mut state := state
  for (idx, bit) in committeeIndices.zip bits do
    if bit then
      state ← increaseBalance state idx participantReward
      state ← increaseBalance state (← getBeaconProposerIndex state) proposerReward
    else
      state ← decreaseBalance state idx participantReward
  pure state

/-! ## Execution payload bid (Gloas) -/

/-- `verify_execution_payload_bid_signature(state, signed_bid)` (Gloas, :2146). -/
def verifyExecutionPayloadBidSignature (ctx : Ctx) (state : BeaconState P)
    (signedBid : SignedExecutionPayloadBid) : M Bool := do
  let builder ← state.builders.get signedBid.message.builder_index.toNat
    "verify_execution_payload_bid_signature"
  let root := computeSigningRoot signedBid.message (← getDomain state DOMAIN_BEACON_BUILDER)
  pure (blsVerify ctx.blsActive builder.pubkey root signedBid.signature)

/-- `can_builder_cover_bid(state, builder_index, bid_amount)` (Gloas, :1181). -/
def canBuilderCoverBid (state : BeaconState P) (builderIndex : BuilderIndex) (bidAmount : Gwei) :
    M Bool := do
  let site := "can_builder_cover_bid"
  let builderBalance := (← state.builders.get builderIndex.toNat site).balance
  let pending ← getPendingBalanceToWithdrawForBuilder state builderIndex
  let minBalance ← (← c64 P.MIN_DEPOSIT_AMOUNT).add? pending site
  if builderBalance < minBalance then return false
  pure (bidAmount ≤ (← builderBalance.sub? minBalance site))

/-- `process_execution_payload_bid(state, signed_bid)` (Gloas, :2159). -/
def processExecutionPayloadBid (ctx : Ctx) (state : BeaconState P)
    (signedBid : SignedExecutionPayloadBid) : M (BeaconState P) := do
  let site := "process_execution_payload_bid"
  let bid := signedBid.message
  let builderIndex := bid.builder_index
  let amount := bid.value
  -- For self-builds, amount must be zero regardless of withdrawal credential prefix
  if builderIndex == BUILDER_INDEX_SELF_BUILD then
    require (amount == U64.zero) s!"{site}: self-build amount == 0"
    require (signedBid.signature == g2PointAtInfinitySignature)
      s!"{site}: self-build signature == G2_POINT_AT_INFINITY"
  else
    -- Verify that the builder is active
    require (← isActiveBuilder state builderIndex) s!"{site}: is_active_builder"
    -- Verify that the builder is a payload builder
    require ((← state.builders.get builderIndex.toNat site).version == PAYLOAD_BUILDER_VERSION)
      s!"{site}: PAYLOAD_BUILDER_VERSION"
    -- Verify that the builder has funds to cover the bid
    require (← canBuilderCoverBid state builderIndex amount) s!"{site}: can_builder_cover_bid"
    -- Verify that the bid signature is valid
    require (← verifyExecutionPayloadBidSignature ctx state signedBid) s!"{site}: bid signature"
  -- Verify commitments are under limit
  let maxBlobs := (← getBlobParameters ctx.cfg (← getCurrentEpoch state)).maxBlobsPerBlock
  require (bid.blob_kzg_commitments.length ≤ maxBlobs.toNat) s!"{site}: blob commitments"
  -- Verify that the bid is for the current slot
  require (bid.slot == state.slot) s!"{site}: bid.slot == state.slot"
  require (GENESIS_SLOT < state.slot) s!"{site}: state.slot > GENESIS_SLOT"
  -- Verify that the bid is for the right parent block
  require (bid.parent_block_hash == state.latest_block_hash) s!"{site}: parent block hash"
  -- Verify that the bid's block hash differs from its parent block hash
  require (bid.block_hash != bid.parent_block_hash) s!"{site}: block hash differs from parent"
  require (bid.parent_block_root == (← getBlockRootAtSlot state (← state.slot.sub? U64.one site)))
    s!"{site}: parent block root"
  require (bid.prev_randao == (← getRandaoMix state (← getCurrentEpoch state))) s!"{site}: prev_randao"
  -- Record the pending payment if there is some payment
  let state ← if U64.zero < amount then do
      let pendingPayment : BuilderPendingPayment :=
        { weight := U64.zero
          withdrawal := { fee_recipient := bid.fee_recipient, amount, builder_index := builderIndex }
          proposer_index := ← getBeaconProposerIndex state }
      let spe ← c64 P.SLOTS_PER_EPOCH
      let i ← spe.add? (← bid.slot.mod? spe site) site
      pure { state with builder_pending_payments :=
        ← state.builder_pending_payments.set i.toNat pendingPayment site }
    else pure state
  -- Cache the signed execution payload bid
  pure { state with latest_execution_payload_bid := bid }

/-! ## Parent execution payload (Gloas) -/

/-- `apply_parent_execution_payload(state, requests)` (Gloas, :1776): the four EIP-7688 request
caps, the parent's builder payment, the parent's execution requests (each through its own
processing call, at the child's slot), then payload availability and the latest block hash. -/
def applyParentExecutionPayload (ctx : Ctx) (state : BeaconState P) (requests : ExecutionRequests) :
    M (BeaconState P) := do
  let site := "apply_parent_execution_payload"
  let parentBid := state.latest_execution_payload_bid
  let parentSlot := state.latest_block_header.slot
  let parentEpoch ← computeEpochAtSlot P parentSlot
  require (requests.withdrawals.length ≤ P.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD)
    s!"{site}: len(requests.withdrawals) <= MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD"
  require (requests.consolidations.length ≤ P.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD)
    s!"{site}: len(requests.consolidations) <= MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD"
  require (requests.builder_deposits.length ≤ P.MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD)
    s!"{site}: len(requests.builder_deposits) <= MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD"
  require (requests.builder_exits.length ≤ P.MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD)
    s!"{site}: len(requests.builder_exits) <= MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD"
  -- Settle the builder payment before the requests so that a builder exit request is rejected
  -- while the payment is pending
  let spe ← c64 P.SLOTS_PER_EPOCH
  let mut state := state
  if parentEpoch == (← getCurrentEpoch state) then
    let paymentIndex ← spe.add? (← parentSlot.mod? spe site) site
    state ← settleBuilderPayment state paymentIndex
  else if parentEpoch == (← getPreviousEpoch state) then
    let paymentIndex ← parentSlot.mod? spe site
    state ← settleBuilderPayment state paymentIndex
  else if U64.zero < parentBid.value then
    -- Parent is older than the previous epoch, its payment entry has been evicted from
    -- builder_pending_payments. Append the withdrawal directly.
    let w : BuilderPendingWithdrawal :=
      { fee_recipient := parentBid.fee_recipient, amount := parentBid.value,
        builder_index := parentBid.builder_index }
    state := { state with builder_pending_withdrawals := state.builder_pending_withdrawals.push w }
  -- Process execution requests from parent's payload, at state.slot (the child's slot)
  for op in requests.deposits.toArray do state := processDepositRequest state op
  for op in requests.withdrawals.toArray do state ← processWithdrawalRequest ctx.cfg state op
  for op in requests.consolidations.toArray do state ← processConsolidationRequest ctx.cfg state op
  for op in requests.builder_deposits.toArray do state ← processBuilderDepositRequest ctx state op
  for op in requests.builder_exits.toArray do state ← processBuilderExitRequest ctx.cfg state op
  -- Update parent payload availability and latest block hash
  let i ← parentSlot.mod? (← c64 P.SLOTS_PER_HISTORICAL_ROOT) site
  pure { state with
    execution_payload_availability := ← state.execution_payload_availability.set i.toNat true site
    latest_block_hash := parentBid.block_hash }

/-- `process_parent_execution_payload(state, block)` (Gloas, :1833): an EMPTY parent (the bid
does not build on the parent bid's block hash) must carry no requests; a FULL parent's requests
must match the parent bid's `execution_requests_root` and are applied. -/
def processParentExecutionPayload (ctx : Ctx) (state : BeaconState P) (block : BeaconBlock P) :
    M (BeaconState P) := do
  let site := "process_parent_execution_payload"
  let bid := block.body.signed_execution_payload_bid.message
  let parentBid := state.latest_execution_payload_bid
  let requests := block.body.parent_execution_requests
  if bid.parent_block_hash != parentBid.block_hash then
    -- Parent was EMPTY -- no execution requests expected
    require (requests == ExecutionRequests.empty) s!"{site}: requests == ExecutionRequests.empty()"
    return state
  -- Parent was FULL -- verify the bid commitment and apply the payload
  require (Ssz.hashTreeRoot requests == parentBid.execution_requests_root)
    s!"{site}: hash_tree_root(requests) == parent_bid.execution_requests_root"
  applyParentExecutionPayload ctx state requests

/-! ## Operations and the block -/

/-- `process_operations(state, body, parent_slot)` (Gloas, :2220). -/
def processOperations (ctx : Ctx) (state : BeaconState P) (body : BeaconBlockBody P)
    (parentSlot : Slot) : M (BeaconState P) := do
  let site := "process_operations"
  require (body.deposits.length == 0) s!"{site}: len(body.deposits) == 0"
  -- [New in Gloas:EIP7688]
  require (body.proposer_slashings.length ≤ P.MAX_PROPOSER_SLASHINGS)
    s!"{site}: len(body.proposer_slashings) <= MAX_PROPOSER_SLASHINGS"
  require (body.attester_slashings.length ≤ P.MAX_ATTESTER_SLASHINGS_ELECTRA)
    s!"{site}: len(body.attester_slashings) <= MAX_ATTESTER_SLASHINGS_ELECTRA"
  require (body.attestations.length ≤ P.MAX_ATTESTATIONS_ELECTRA)
    s!"{site}: len(body.attestations) <= MAX_ATTESTATIONS_ELECTRA"
  require (body.voluntary_exits.length ≤ P.MAX_VOLUNTARY_EXITS)
    s!"{site}: len(body.voluntary_exits) <= MAX_VOLUNTARY_EXITS"
  require (body.bls_to_execution_changes.length ≤ P.MAX_BLS_TO_EXECUTION_CHANGES)
    s!"{site}: len(body.bls_to_execution_changes) <= MAX_BLS_TO_EXECUTION_CHANGES"
  require (body.payload_attestations.length ≤ P.MAX_PAYLOAD_ATTESTATIONS)
    s!"{site}: len(body.payload_attestations) <= MAX_PAYLOAD_ATTESTATIONS"
  let mut state := state
  for op in body.proposer_slashings.toArray do state ← processProposerSlashing ctx state op
  for op in body.attester_slashings.toArray do state ← processAttesterSlashing ctx state op
  for op in body.attestations.toArray do state ← processAttestation ctx state op parentSlot
  for op in body.voluntary_exits.toArray do state ← processVoluntaryExit ctx state op
  for op in body.bls_to_execution_changes.toArray do
    state ← processBlsToExecutionChange ctx state op
  for op in body.payload_attestations.toArray do state ← processPayloadAttestation ctx state op
  pure state

/-- `process_block(state, block)` (Gloas, :1754), in the spec's order. -/
def processBlock (ctx : Ctx) (state : BeaconState P) (block : BeaconBlock P) :
    M (BeaconState P) := do
  -- [New in Gloas:EIP7732]
  let parentSlot := state.latest_block_header.slot
  let state ← processParentExecutionPayload ctx state block
  let state ← processBlockHeader state block
  let state ← processWithdrawals state
  let state ← processExecutionPayloadBid ctx state block.body.signed_execution_payload_bid
  let state ← processRandao ctx state block.body
  let state ← processEth1Data state block.body
  let state ← processOperations ctx state block.body parentSlot
  processSyncAggregate ctx state block.body.sync_aggregate

end Gloas
end JauneConsensus
