import JauneConsensus.GossipCore

/-!
# Store-free gossip validators, Electra and Fulu (goal `eip8282-gloas-cross-layer-v1`, U7a)

Transcribed from `ethereum/consensus-specs` `v1.7.0-beta.4`, over the fork-indexed
`BeaconState P f`. Each definition cites its `validate_<topic>_gossip` and keeps the spec's
check order and reason strings. Electra and Fulu inherit these by reference:

* `validate_proposer_slashing_gossip`, `validate_attester_slashing_gossip`
  (`specs/phase0/p2p-interface.md:882`, `:941`; Electra changes only the `AttesterSlashing`
  sizes, `specs/electra/p2p-interface.md:358`);
* `validate_voluntary_exit_gossip` (`specs/deneb/p2p-interface.md:529`, the EIP-7044 domain);
* `validate_bls_to_execution_change_gossip` (`specs/capella/p2p-interface.md:205`);
* `validate_sync_committee_contribution_and_proof_gossip`, `validate_sync_committee_message_gossip`
  (`specs/altair/p2p-interface.md:230`, `:349`).

Each reads `store` only through `store.genesis_time_ms` and the head state (`HeadView`), and
returns the updated `Seen` when the message is valid. `ctx.blsActive` is pyspec's BLS switch.
-/

namespace JauneConsensus.Gossip
open Jaune (Bytes)

variable {P : Preset} {f : CFork} {Ext : Type}

/-- `validate_voluntary_exit_gossip` (deneb). -/
def validateVoluntaryExitGossip (ctx : Ctx) (seen : Seen Ext) (store : HeadView (BeaconState P f))
    (signedVoluntaryExit : SignedVoluntaryExit) (currentTimeMs : U64) : GM (Seen Ext) := do
  let voluntaryExit := signedVoluntaryExit.message
  let validatorIndex := voluntaryExit.validator_index
  -- [IGNORE] The voluntary exit is the first valid voluntary exit received for the validator
  if seen.voluntary_exit_indices.contains validatorIndex then
    ignore "already seen voluntary exit for this validator"
  -- [IGNORE] The voluntary exit epoch is not in the future
  if ← isFutureEpoch P ctx.cfg store.genesisTimeMs voluntaryExit.epoch.toNat currentTimeMs then
    ignore "voluntary exit epoch is in the future"
  let state := store.headState
  -- [REJECT] The validator index is valid
  if validatorIndex.toNat ≥ state.validators.length then reject "validator index out of range"
  let validator ← state.validators.get validatorIndex.toNat "validate_voluntary_exit_gossip"
  let currentEpoch ← getCurrentEpoch state
  -- [IGNORE] The validator has not already initiated exit
  if validator.exit_epoch != FAR_FUTURE_EPOCH then ignore "validator has already initiated exit"
  -- [REJECT] The validator is active
  if !isActiveValidator validator currentEpoch then reject "validator is not active"
  -- [REJECT] The validator has been active long enough
  if currentEpoch < (← U64.add? validator.activation_epoch (← c64 ctx.cfg.SHARD_COMMITTEE_PERIOD)
      "validate_voluntary_exit_gossip") then
    reject "validator has not been active long enough"
  -- [Modified in Deneb:EIP7044] [REJECT] The signature is valid
  let domain := computeDomain DOMAIN_VOLUNTARY_EXIT (← versionOf ctx.cfg.CAPELLA_FORK_VERSION)
    state.genesis_validators_root
  let signingRoot := computeSigningRoot voluntaryExit domain
  if !blsVerify ctx.blsActive validator.pubkey signingRoot signedVoluntaryExit.signature then
    reject "invalid voluntary exit signature"
  -- Mark this voluntary exit as seen
  pure { seen with voluntary_exit_indices := seen.voluntary_exit_indices ++ [validatorIndex] }

/-- `validate_proposer_slashing_gossip` (phase0). -/
def validateProposerSlashingGossip (ctx : Ctx) (seen : Seen Ext)
    (store : HeadView (BeaconState P f)) (proposerSlashing : ProposerSlashing) : GM (Seen Ext) := do
  let header1 := proposerSlashing.signed_header_1.message
  let header2 := proposerSlashing.signed_header_2.message
  let proposerIndex := header1.proposer_index
  -- [IGNORE] The proposer slashing is the first valid proposer slashing received for this proposer
  if seen.proposer_slashing_indices.contains proposerIndex then
    ignore "already seen proposer slashing for this proposer"
  -- [REJECT] The header slots match
  if header1.slot != header2.slot then reject "header slots do not match"
  -- [REJECT] The header proposer indices match
  if header1.proposer_index != header2.proposer_index then
    reject "header proposer indices do not match"
  -- [REJECT] The headers are different
  if header1 == header2 then reject "headers are not different"
  let state := store.headState
  -- [REJECT] The proposer index is a valid validator index
  if proposerIndex.toNat ≥ state.validators.length then reject "proposer index out of range"
  -- [REJECT] The proposer is slashable
  let proposer ← state.validators.get proposerIndex.toNat "validate_proposer_slashing_gossip"
  if !isSlashableValidator proposer (← getCurrentEpoch state) then
    reject "proposer is not slashable"
  -- [REJECT] The signatures are valid
  for signedHeader in [proposerSlashing.signed_header_1, proposerSlashing.signed_header_2] do
    let domain ← getDomain state DOMAIN_BEACON_PROPOSER
      (some (← computeEpochAtSlot P signedHeader.message.slot))
    let signingRoot := computeSigningRoot signedHeader.message domain
    if !blsVerify ctx.blsActive proposer.pubkey signingRoot signedHeader.signature then
      reject "invalid proposer slashing signature"
  -- Mark this proposer slashing as seen
  pure { seen with proposer_slashing_indices := seen.proposer_slashing_indices ++ [proposerIndex] }

/-- `set(a).intersection(set(b))`, sorted (the order of a Python set is not observable here:
the uses are membership, emptiness and an `any`). -/
def intersectIndices (a b : List ValidatorIndex) : List ValidatorIndex :=
  ((a.filter b.contains).toArray.qsort (·.toNat < ·.toNat)).toList.eraseDups

/-- `validate_attester_slashing_gossip` (phase0; Electra sizes). -/
def validateAttesterSlashingGossip (ctx : Ctx) (seen : Seen Ext)
    (store : HeadView (BeaconState P f)) (attesterSlashing : AttesterSlashing P f) :
    GM (Seen Ext) := do
  let attestation1 := attesterSlashing.attestation_1
  let attestation2 := attesterSlashing.attestation_2
  let indices1 := attestation1.attesting_indices.toArray.toList
  let indices2 := attestation2.attesting_indices.toArray.toList
  let slashableIndices := intersectIndices indices1 indices2
  -- [IGNORE] At least one index in the intersection has not yet been seen
  let newIndices := slashableIndices.filter (!seen.attester_slashing_indices.contains ·)
  if newIndices.length == 0 then ignore "all attester slashing indices already seen"
  -- [REJECT] The attestation data is slashable (double vote or surround vote)
  if !isSlashableAttestationData attestation1.data attestation2.data then
    reject "attestation data is not slashable"
  let state := store.headState
  -- [REJECT] All validator indices in the first indexed attestation are valid
  if indices1.any (·.toNat ≥ state.validators.length) then
    reject "validator index out of range in indexed attestation 1"
  -- [REJECT] The first indexed attestation has valid properties
  if !(← isValidIndexedAttestation ctx state attestation1) then
    reject "invalid indexed attestation 1"
  -- [REJECT] All validator indices in the second indexed attestation are valid
  if indices2.any (·.toNat ≥ state.validators.length) then
    reject "validator index out of range in indexed attestation 2"
  -- [REJECT] The second indexed attestation has valid properties
  if !(← isValidIndexedAttestation ctx state attestation2) then
    reject "invalid indexed attestation 2"
  -- [REJECT] At least one validator in the intersection is slashable
  let currentEpoch ← getCurrentEpoch state
  let mut slashableAny := false
  for index in slashableIndices do
    let v ← state.validators.get index.toNat "validate_attester_slashing_gossip"
    if isSlashableValidator v currentEpoch then
      slashableAny := true
      break
  if !slashableAny then reject "no slashable validators in intersection"
  -- Mark these indices as seen
  let added := slashableIndices.filter (!seen.attester_slashing_indices.contains ·)
  pure { seen with attester_slashing_indices := seen.attester_slashing_indices ++ added }

/-- `validate_bls_to_execution_change_gossip` (capella). -/
def validateBlsToExecutionChangeGossip (ctx : Ctx) (seen : Seen Ext)
    (store : HeadView (BeaconState P f)) (signedChange : SignedBLSToExecutionChange)
    (currentTimeMs : U64) : GM (Seen Ext) := do
  let change := signedChange.message
  let validatorIndex := change.validator_index
  -- [IGNORE] This is the first valid bls_to_execution_change received for the validator
  if seen.bls_to_execution_change_indices.contains validatorIndex then
    ignore "already seen BLS to execution change for this validator"
  -- [IGNORE] The current epoch is at or after the Capella fork epoch
  if ← isFutureEpoch P ctx.cfg store.genesisTimeMs ctx.cfg.CAPELLA_FORK_EPOCH currentTimeMs then
    ignore "current epoch is pre-capella"
  let state := store.headState
  -- [REJECT] The validator index is valid
  if validatorIndex.toNat ≥ state.validators.length then reject "validator index out of range"
  let validator ← state.validators.get validatorIndex.toNat "validate_bls_to_execution_change_gossip"
  let wc := validator.withdrawal_credentials.toBytes
  -- [REJECT] The validator has BLS withdrawal credentials
  if wc.take 1 != [BLS_WITHDRAWAL_PREFIX] then
    reject "validator does not have BLS withdrawal credentials"
  -- [REJECT] The bls_to_execution_change is for the validator's withdrawal pubkey
  let pubkey := change.from_bls_pubkey
  if wc.drop 1 != (hashBytes pubkey.toArray.toList).drop 1 then
    reject "pubkey does not match validator withdrawal credentials"
  -- [REJECT] The signature is valid
  let domain := computeDomain DOMAIN_BLS_TO_EXECUTION_CHANGE
    (← versionOf ctx.cfg.GENESIS_FORK_VERSION) state.genesis_validators_root
  let signingRoot := computeSigningRoot change domain
  if !blsVerify ctx.blsActive pubkey signingRoot signedChange.signature then
    reject "invalid BLS to execution change signature"
  -- Mark this bls_to_execution_change as seen
  pure { seen with bls_to_execution_change_indices :=
    seen.bls_to_execution_change_indices ++ [validatorIndex] }

/-- `get_sync_subcommittee_pubkeys(state, subcommittee_index)` (altair). -/
def getSyncSubcommitteePubkeys (state : BeaconState P f) (subcommitteeIndex : U64) :
    M (List BLSPubkey) := do
  let committee ← syncCommitteeForNextSlot P state.slot state.current_sync_committee
    state.next_sync_committee
  pure (subcommitteePubkeys P committee subcommitteeIndex)

/-- `compute_subnets_for_sync_committee(state, validator_index)` (`specs/altair/validator.md`). -/
def computeSubnetsForSyncCommittee (state : BeaconState P f) (validatorIndex : ValidatorIndex) :
    M (List Nat) := do
  let committee ← syncCommitteeForNextSlot P state.slot state.current_sync_committee
    state.next_sync_committee
  let target ← state.validators.get validatorIndex.toNat "compute_subnets_for_sync_committee"
  pure (subnetsForPubkey P committee target.pubkey)

/-- `validate_sync_committee_contribution_and_proof_gossip` (altair). -/
def validateSyncCommitteeContributionAndProofGossip (ctx : Ctx) (seen : Seen Ext)
    (store : HeadView (BeaconState P f)) (signed : SignedContributionAndProof P)
    (currentTimeMs : U64) : GM (Seen Ext) := do
  let contributionAndProof := signed.message
  let contribution := contributionAndProof.contribution
  -- [IGNORE] A valid contribution with equal slot, beacon_block_root and subcommittee_index whose
  -- aggregation_bits is a non-strict superset has not already been seen
  let contributionKey := (contribution.slot, contribution.beacon_block_root,
    contribution.subcommittee_index)
  let contributionBits := contribution.aggregation_bits.bits.toList
  let seenBits := lookupSet seen.sync_contribution_data contributionKey
  if ← isNonStrictSuperset seenBits contributionBits then
    ignore "already seen contribution for this data"
  -- [IGNORE] The first valid contribution for the slot, aggregator and subcommittee index
  let aggregatorKey := (contribution.slot, contributionAndProof.aggregator_index,
    contribution.subcommittee_index)
  if seen.sync_contribution_aggregator_slots.contains aggregatorKey then
    ignore "already seen contribution from this aggregator"
  -- [IGNORE] The contribution's slot is for the current slot
  if !(← isCurrentSlot ctx.cfg store.genesisTimeMs contribution.slot currentTimeMs) then
    ignore "contribution is not for the current slot"
  -- [REJECT] The subcommittee index is in the allowed range
  if contribution.subcommittee_index.toNat ≥ SYNC_COMMITTEE_SUBNET_COUNT then
    reject "subcommittee index out of range"
  -- [REJECT] The contribution has participants
  if !contributionBits.any id then reject "contribution has no participants"
  -- [REJECT] The selection_proof selects the validator as an aggregator for the slot
  if !(← isSyncCommitteeAggregator P contributionAndProof.selection_proof) then
    reject "validator is not selected as aggregator"
  let state := store.headState
  -- [REJECT] The aggregator index is valid
  if contributionAndProof.aggregator_index.toNat ≥ state.validators.length then
    reject "aggregator index out of range"
  -- [REJECT] The aggregator is a member of the committee
  let aggregatorPubkey := (← state.validators.get contributionAndProof.aggregator_index.toNat
    "validate_sync_committee_contribution_and_proof_gossip").pubkey
  let subcommitteePubkeys ← getSyncSubcommitteePubkeys state contribution.subcommittee_index
  if !subcommitteePubkeys.contains aggregatorPubkey then
    reject "aggregator is not a member of the committee"
  -- [REJECT] The selection_proof is a valid signature of the SyncAggregatorSelectionData
  let selectionData : SyncAggregatorSelectionData :=
    { slot := contribution.slot, subcommittee_index := contribution.subcommittee_index }
  let epoch ← computeEpochAtSlot P contribution.slot
  let domain ← getDomain state DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF (some epoch)
  if !blsVerify ctx.blsActive aggregatorPubkey (computeSigningRoot selectionData domain)
      contributionAndProof.selection_proof then
    reject "invalid selection proof signature"
  -- [REJECT] The aggregator signature is valid
  let domain ← getDomain state DOMAIN_CONTRIBUTION_AND_PROOF (some epoch)
  if !blsVerify ctx.blsActive aggregatorPubkey (computeSigningRoot contributionAndProof domain)
      signed.signature then
    reject "invalid aggregator signature"
  -- [REJECT] The aggregate signature is valid for beacon_block_root and the participants
  let participantPubkeys := (subcommitteePubkeys.zip contributionBits).filterMap
    fun (pk, bit) => if bit then some pk else none
  let domain ← getDomain state DOMAIN_SYNC_COMMITTEE (some epoch)
  if !blsEthFastAggregateVerify ctx.blsActive participantPubkeys
      (computeSigningRootOfRoot contribution.beacon_block_root domain) contribution.signature then
    reject "invalid aggregate signature"
  -- Mark this contribution as seen
  pure { seen with
    sync_contribution_aggregator_slots := seen.sync_contribution_aggregator_slots ++ [aggregatorKey]
    sync_contribution_data := addToSet seen.sync_contribution_data contributionKey contributionBits }

/-- `validate_sync_committee_message_gossip` (altair). -/
def validateSyncCommitteeMessageGossip (ctx : Ctx) (seen : Seen Ext)
    (store : HeadView (BeaconState P f)) (message : SyncCommitteeMessage) (currentTimeMs : U64)
    (subnetId : U64) : GM (Seen Ext) := do
  -- [IGNORE] No other valid sync committee message for the slot, validator and subnet
  let messageKey := (message.slot, message.validator_index, subnetId)
  if seen.sync_message_validator_slots.contains messageKey then
    ignore "already seen message from this validator for this slot and subnet"
  -- [IGNORE] The message's slot is for the current slot
  if !(← isCurrentSlot ctx.cfg store.genesisTimeMs message.slot currentTimeMs) then
    ignore "message is not for the current slot"
  let state := store.headState
  -- [REJECT] The validator index is valid
  if message.validator_index.toNat ≥ state.validators.length then
    reject "validator index out of range"
  -- [REJECT] The subnet_id is valid for the given validator
  let validSubnets ← computeSubnetsForSyncCommittee state message.validator_index
  if !validSubnets.contains subnetId.toNat then
    reject "subnet_id is not valid for the validator"
  -- [REJECT] The signature is valid
  let validator ← state.validators.get message.validator_index.toNat
    "validate_sync_committee_message_gossip"
  let domain ← getDomain state DOMAIN_SYNC_COMMITTEE (some (← computeEpochAtSlot P message.slot))
  if !blsVerify ctx.blsActive validator.pubkey
      (computeSigningRootOfRoot message.beacon_block_root domain) message.signature then
    reject "invalid sync committee message signature"
  -- Mark this message as seen
  pure { seen with sync_message_validator_slots := seen.sync_message_validator_slots ++ [messageKey] }

end JauneConsensus.Gossip
