import JauneConsensus.GloasBlock
import JauneConsensus.Deposits

/-!
# The Fulu → Gloas upgrade (goal `eip8282-gloas-cross-layer-v1`, U5)

`specs/gloas/fork.md` of `ethereum/consensus-specs` `v1.7.0-beta.4`, transcribed over the Fulu
`BeaconState P .fulu` (`Containers.lean`) and the Gloas `JauneConsensus.Gloas.BeaconState P`
(`ContainersGloas.lean`):

* `initialize_ptc_window` (:37) and `onboard_builders_from_pending_deposits` (:70), with the
  Gloas `is_pending_validator` (`specs/gloas/beacon-chain.md:1119`);
* `upgrade_to_gloas` (:135): the field copy, then `initialize_ptc_window`, then the builder
  onboarding, in that order. The initial `execution_payload_availability` is all ones and the
  self-build `latest_execution_payload_bid` commits to `hash_tree_root(ExecutionRequests.empty())`;
* `upgrade_attestation_to_gloas`, `upgrade_indexed_attestation_to_gloas` and
  `upgrade_attester_slashing_to_gloas` (:242-261).

**The onboarding loop.** `onboardBuilderDeposit` is one iteration of the spec's loop, with its
branches in the spec's order: a deposit for a validator pubkey (the pre-loop snapshot) is kept; a
deposit for a pubkey that is not a builder's is kept when its credentials are not `0xB0`, kept
when a pending validator deposit with a valid signature for that pubkey is already in the
accumulator (`is_pending_validator` scans only the accumulator), dropped when its signature is
invalid, and otherwise registers a builder; a deposit for a known builder pubkey (including one
onboarded earlier in this loop) tops that builder up with no further check. The loop is a left
fold of that step over `state.pending_deposits`, so a statement about the loop is an induction
over the deposits with one case per branch.

The deposit signature check is `is_valid_deposit_signature` (`Deposits.lean`) under the context's
BLS switch.
-/

namespace JauneConsensus.Gloas

open Jaune

variable {P : Preset}

private theorem fulu_atLeast_electra : CFork.fulu.atLeast .electra = true := by decide
private theorem fulu_atLeast_fulu : CFork.fulu.atLeast .fulu = true := by decide

/-! ## `initialize_ptc_window` -/

/-- `initialize_ptc_window(state)` (fork.md:37): `SLOTS_PER_EPOCH` zero committees for the
previous epoch, then `compute_ptc` for every slot of the current epoch and the
`MIN_SEED_LOOKAHEAD` epochs after it. -/
def initializePtcWindow (state : BeaconState P) : M (PayloadTimelinessCommitteeWindow P) := do
  let site := "initialize_ptc_window"
  let zeroCommittee : PayloadTimelinessCommittee P :=
    ⟨Array.replicate P.PTC_SIZE U64.zero, by simp⟩
  let emptyPreviousEpoch := Array.replicate P.SLOTS_PER_EPOCH zeroCommittee
  let mut ptcs : Array (PayloadTimelinessCommittee P) := #[]
  let currentEpoch ← getCurrentEpoch state
  for e in [0:1 + P.MIN_SEED_LOOKAHEAD] do
    let epoch ← currentEpoch.add? (← U64.ofNat? e "Epoch") site
    let startSlot ← computeStartSlotAtEpoch P epoch
    for index in [0:P.SLOTS_PER_EPOCH] do
      ptcs := ptcs.push (← computePtc state (← startSlot.add? (← U64.ofNat? index "Slot") site))
  SszVector.ofArray (emptyPreviousEpoch ++ ptcs) site

/-! ## `onboard_builders_from_pending_deposits` -/

/-- `is_pending_validator(pending_deposits, pubkey)` (beacon-chain.md:1119): some deposit in
`pendingDeposits` for `pubkey` has a valid deposit signature. -/
def isPendingValidator (ctx : Ctx) (pendingDeposits : Array PendingDeposit) (pubkey : BLSPubkey) :
    M Bool := do
  for pendingDeposit in pendingDeposits do
    if pendingDeposit.pubkey != pubkey then continue
    if ← isValidDepositSignature ctx pendingDeposit.pubkey pendingDeposit.withdrawal_credentials
        pendingDeposit.amount pendingDeposit.signature then
      return true
  return false

/-- One iteration of the onboarding loop (fork.md:80-117) on `(state, pending_deposits)`, the
state and the accumulator of kept deposits. `validatorPubkeys` is the snapshot taken before the
loop. The branches, in the spec's order:

1. `deposit.pubkey in validator_pubkeys`: keep;
2. not a builder pubkey (recomputed from `state.builders` each iteration):
   a. credentials are not `0xB0`: keep;
   b. `is_pending_validator(pending_deposits, deposit.pubkey)`: keep;
   c. invalid deposit signature: drop;
   d. otherwise `add_builder_to_registry` (version `PAYLOAD_BUILDER_VERSION`, the address
      `withdrawal_credentials[12:]`, the deposit's amount and slot);
3. a builder pubkey: `state.builders[builder_index].balance += deposit.amount`. -/
def onboardBuilderDeposit (ctx : Ctx) (validatorPubkeys : Array BLSPubkey)
    (acc : BeaconState P × Array PendingDeposit) (deposit : PendingDeposit) :
    M (BeaconState P × Array PendingDeposit) := do
  let site := "onboard_builders_from_pending_deposits"
  let (state, pendingDeposits) := acc
  -- Deposits for existing validators stay in the pending queue
  if validatorPubkeys.contains deposit.pubkey then
    return (state, pendingDeposits.push deposit)
  -- The builder pubkeys are recomputed each iteration: a deposit above may have added a builder
  let builderPubkeys := state.builders.toArray.map (·.pubkey)
  match builderPubkeys.idxOf? deposit.pubkey with
  | none =>
    -- Deposits for non-builders stay in the pending queue
    if !isBuilderWithdrawalCredential deposit.withdrawal_credentials then
      return (state, pendingDeposits.push deposit)
    -- A valid pending deposit for a new validator with this pubkey keeps this one queued
    if ← isPendingValidator ctx pendingDeposits deposit.pubkey then
      return (state, pendingDeposits.push deposit)
    if !(← isValidDepositSignature ctx deposit.pubkey deposit.withdrawal_credentials
        deposit.amount deposit.signature) then
      return (state, pendingDeposits)
    let state ← addBuilderToRegistry state deposit.pubkey PAYLOAD_BUILDER_VERSION
      (← addressOfCredentials deposit.withdrawal_credentials) deposit.amount deposit.slot
    return (state, pendingDeposits)
  | some builderIndex =>
    let builder ← state.builders.get builderIndex site
    let builder := { builder with balance := ← builder.balance.add? deposit.amount site }
    return ({ state with builders := ← state.builders.set builderIndex builder site },
      pendingDeposits)

/-- `onboard_builders_from_pending_deposits(state)` (fork.md:70): the left fold of
`onboardBuilderDeposit` over `state.pending_deposits` from an empty accumulator, which becomes
the new `pending_deposits`. -/
def onboardBuildersFromPendingDeposits (ctx : Ctx) (state : BeaconState P) :
    M (BeaconState P) := do
  let validatorPubkeys := state.validators.toArray.map (·.pubkey)
  let (state, pendingDeposits) ← state.pending_deposits.toArray.foldlM
    (onboardBuilderDeposit ctx validatorPubkeys) (state, #[])
  pure { state with pending_deposits := ProgressiveListS.ofArray pendingDeposits }

/-! ## `upgrade_to_gloas` -/

/-- `ExecutionPayloadAvailability(data=[0b1 for _ in range(SLOTS_PER_HISTORICAL_ROOT)])`. -/
def allAvailable : ExecutionPayloadAvailability P :=
  ⟨Array.replicate P.SLOTS_PER_HISTORICAL_ROOT true, by simp⟩

/-- `BuilderPendingPayments()`: the default vector. -/
def emptyBuilderPendingPayments : SszVector BuilderPendingPayment (2 * P.SLOTS_PER_EPOCH) :=
  ⟨Array.replicate (2 * P.SLOTS_PER_EPOCH) BuilderPendingPayment.empty, by simp⟩

/-- `PayloadTimelinessCommitteeWindow()`: the default vector (all-zero committees). It is a
placeholder that `upgrade_to_gloas` overwrites with `initialize_ptc_window(post)` at once;
`compute_ptc` does not read the window. -/
def defaultPtcWindow : PayloadTimelinessCommitteeWindow P :=
  ⟨Array.replicate ((P.MIN_SEED_LOOKAHEAD + 2) * P.SLOTS_PER_EPOCH)
    ⟨Array.replicate P.PTC_SIZE U64.zero, by simp⟩, by simp⟩

/-- The `BeaconState(...)` constructor call of `upgrade_to_gloas` (fork.md:138-224): the Fulu
fields copied (the EIP-7688 lists re-typed as progressive lists), `latest_execution_payload_header`
replaced by `latest_block_hash`, and the new EIP-7732 fields at their initial values. -/
def upgradedState (cfg : Config) (pre : JauneConsensus.BeaconState P .fulu) : M (BeaconState P) := do
  let epoch ← JauneConsensus.getCurrentEpoch pre
  let header := pre.latest_execution_payload_header
  pure {
    genesis_time := pre.genesis_time
    genesis_validators_root := pre.genesis_validators_root
    slot := pre.slot
    fork := {
      previous_version := pre.fork.current_version
      -- [Modified in Gloas]
      current_version := ← versionOf cfg.GLOAS_FORK_VERSION
      epoch := epoch }
    latest_block_header := pre.latest_block_header
    block_roots := pre.block_roots
    state_roots := pre.state_roots
    historical_roots := pre.historical_roots
    eth1_data := pre.eth1_data
    eth1_data_votes := pre.eth1_data_votes
    eth1_deposit_index := pre.eth1_deposit_index
    -- [Modified in Gloas:EIP7688]
    validators := ProgressiveListS.ofArray pre.validators.toArray
    balances := ProgressiveListS.ofArray pre.balances.toArray
    randao_mixes := pre.randao_mixes
    slashings := pre.slashings
    previous_epoch_participation := ProgressiveListS.ofArray pre.previous_epoch_participation.toArray
    current_epoch_participation := ProgressiveListS.ofArray pre.current_epoch_participation.toArray
    justification_bits := pre.justification_bits
    previous_justified_checkpoint := pre.previous_justified_checkpoint
    current_justified_checkpoint := pre.current_justified_checkpoint
    finalized_checkpoint := pre.finalized_checkpoint
    inactivity_scores := ProgressiveListS.ofArray pre.inactivity_scores.toArray
    current_sync_committee := pre.current_sync_committee
    next_sync_committee := pre.next_sync_committee
    -- [New in Gloas:EIP7732] (`latest_execution_payload_header` removed)
    latest_block_hash := header.block_hash
    next_withdrawal_index := pre.next_withdrawal_index
    next_withdrawal_validator_index := pre.next_withdrawal_validator_index
    historical_summaries := pre.historical_summaries
    deposit_requests_start_index := Gated.get fulu_atLeast_electra pre.deposit_requests_start_index
    deposit_balance_to_consume := Gated.get fulu_atLeast_electra pre.deposit_balance_to_consume
    exit_balance_to_consume := Gated.get fulu_atLeast_electra pre.exit_balance_to_consume
    earliest_exit_epoch := Gated.get fulu_atLeast_electra pre.earliest_exit_epoch
    consolidation_balance_to_consume :=
      Gated.get fulu_atLeast_electra pre.consolidation_balance_to_consume
    earliest_consolidation_epoch := Gated.get fulu_atLeast_electra pre.earliest_consolidation_epoch
    -- [Modified in Gloas:EIP7688]
    pending_deposits :=
      ProgressiveListS.ofArray (Gated.get fulu_atLeast_electra pre.pending_deposits).toArray
    pending_partial_withdrawals :=
      ProgressiveListS.ofArray (Gated.get fulu_atLeast_electra pre.pending_partial_withdrawals).toArray
    pending_consolidations :=
      ProgressiveListS.ofArray (Gated.get fulu_atLeast_electra pre.pending_consolidations).toArray
    proposer_lookahead := Gated.get fulu_atLeast_fulu pre.proposer_lookahead
    -- [New in Gloas:EIP7732]
    builders := ProgressiveListS.empty
    next_withdrawal_builder_index := U64.zero
    execution_payload_availability := allAvailable
    builder_pending_payments := emptyBuilderPendingPayments
    builder_pending_withdrawals := ProgressiveListS.empty
    latest_execution_payload_bid := {
      parent_block_hash := header.parent_hash
      parent_block_root := pre.latest_block_header.parent_root
      block_hash := header.block_hash
      prev_randao := header.prev_randao
      fee_recipient := zeroAddress
      gas_limit := header.gas_limit
      builder_index := BUILDER_INDEX_SELF_BUILD
      slot := pre.latest_block_header.slot
      value := U64.zero
      execution_payment := U64.zero
      blob_kzg_commitments := ProgressiveListS.empty
      execution_requests_root := Ssz.hashTreeRoot ExecutionRequests.empty }
    payload_expected_withdrawals := ProgressiveListS.empty
    ptc_window := defaultPtcWindow }

/-- `upgrade_to_gloas(pre)` (fork.md:135): the upgraded state, then
`post.ptc_window = initialize_ptc_window(post)`, then
`onboard_builders_from_pending_deposits(post)`. The window is computed before onboarding. -/
def upgradeToGloas (ctx : Ctx) (pre : JauneConsensus.BeaconState P .fulu) : M (BeaconState P) := do
  let post ← upgradedState ctx.cfg pre
  -- [New in Gloas:EIP7732]
  let post := { post with ptc_window := ← initializePtcWindow post }
  -- [New in Gloas:EIP7732]
  onboardBuildersFromPendingDeposits ctx post

/-! ## Upgrading attestations and attester slashings (fork.md:242-261) -/

/-- `upgrade_attestation_to_gloas(pre)`. -/
def upgradeAttestationToGloas (pre : JauneConsensus.Attestation P .fulu) : Attestation P :=
  { aggregation_bits := ProgressiveBitlistS.ofArray pre.aggregation_bits.bits
    data := pre.data
    signature := pre.signature
    committee_bits := Gated.get fulu_atLeast_electra pre.committee_bits }

/-- `upgrade_indexed_attestation_to_gloas(pre)`. -/
def upgradeIndexedAttestationToGloas (pre : JauneConsensus.IndexedAttestation P .fulu) :
    IndexedAttestation :=
  { attesting_indices := ProgressiveListS.ofArray pre.attesting_indices.toArray
    data := pre.data
    signature := pre.signature }

/-- `upgrade_attester_slashing_to_gloas(pre)`. -/
def upgradeAttesterSlashingToGloas (pre : JauneConsensus.AttesterSlashing P .fulu) :
    AttesterSlashing :=
  { attestation_1 := upgradeIndexedAttestationToGloas pre.attestation_1
    attestation_2 := upgradeIndexedAttestationToGloas pre.attestation_2 }

end JauneConsensus.Gloas
