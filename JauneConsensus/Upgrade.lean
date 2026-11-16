import JauneConsensus.Signing

/-!
# Fork upgrades

`upgrade_to_electra` (`specs/electra/fork.md`, from a Deneb `BeaconState`) and `upgrade_to_fulu`
(`specs/fulu/fork.md`, from an Electra `BeaconState`), transcribed in the spec's order. The
fields the two states share have the same types (the state is one structure indexed by the
fork), so they are copied as they are; the fields the target fork introduces are built with
`Gated.mk` under the fork fact.
-/

namespace JauneConsensus

open Jaune

variable {P : Preset}

/-- `UNSET_DEPOSIT_REQUESTS_START_INDEX = uint64(2**64 - 1)` (`specs/electra/beacon-chain.md`). -/
def UNSET_DEPOSIT_REQUESTS_START_INDEX : U64 := U64.max

private theorem electra_atLeast_electra : CFork.electra.atLeast .electra = true := by decide
private theorem fulu_atLeast_fulu : CFork.fulu.atLeast .fulu = true := by decide
private theorem fulu_atLeast_electra : CFork.fulu.atLeast .electra = true := by decide

/-- `upgrade_to_electra(pre)`. -/
def upgradeToElectra (cfg : Config) (pre : BeaconState P .deneb) : M (BeaconState P .electra) := do
  let site := "upgrade_to_electra"
  let epoch ← getCurrentEpoch pre
  let mut earliestExitEpoch ← computeActivationExitEpoch P (← getCurrentEpoch pre)
  for validator in pre.validators.toArray do
    if validator.exit_epoch != FAR_FUTURE_EPOCH then
      if validator.exit_epoch > earliestExitEpoch then
        earliestExitEpoch := validator.exit_epoch
  earliestExitEpoch ← U64.add? earliestExitEpoch U64.one s!"{site}: earliest_exit_epoch += 1"
  let h := electra_atLeast_electra
  let post : BeaconState P .electra := {
    genesis_time := pre.genesis_time
    genesis_validators_root := pre.genesis_validators_root
    slot := pre.slot
    fork := {
      previous_version := pre.fork.current_version
      -- [Modified in Electra]
      current_version := ← versionOf cfg.ELECTRA_FORK_VERSION
      epoch := epoch }
    latest_block_header := pre.latest_block_header
    block_roots := pre.block_roots
    state_roots := pre.state_roots
    historical_roots := pre.historical_roots
    eth1_data := pre.eth1_data
    eth1_data_votes := pre.eth1_data_votes
    eth1_deposit_index := pre.eth1_deposit_index
    validators := pre.validators
    balances := pre.balances
    randao_mixes := pre.randao_mixes
    slashings := pre.slashings
    previous_epoch_participation := pre.previous_epoch_participation
    current_epoch_participation := pre.current_epoch_participation
    justification_bits := pre.justification_bits
    previous_justified_checkpoint := pre.previous_justified_checkpoint
    current_justified_checkpoint := pre.current_justified_checkpoint
    finalized_checkpoint := pre.finalized_checkpoint
    inactivity_scores := pre.inactivity_scores
    current_sync_committee := pre.current_sync_committee
    next_sync_committee := pre.next_sync_committee
    latest_execution_payload_header := pre.latest_execution_payload_header
    next_withdrawal_index := pre.next_withdrawal_index
    next_withdrawal_validator_index := pre.next_withdrawal_validator_index
    historical_summaries := pre.historical_summaries
    -- [New in Electra:EIP6110]
    deposit_requests_start_index := Gated.mk h UNSET_DEPOSIT_REQUESTS_START_INDEX
    -- [New in Electra:EIP7251]
    deposit_balance_to_consume := Gated.mk h U64.zero
    exit_balance_to_consume := Gated.mk h U64.zero
    earliest_exit_epoch := Gated.mk h earliestExitEpoch
    consolidation_balance_to_consume := Gated.mk h U64.zero
    earliest_consolidation_epoch :=
      Gated.mk h (← computeActivationExitEpoch P (← getCurrentEpoch pre))
    pending_deposits := Gated.mk h SszList.empty
    pending_partial_withdrawals := Gated.mk h SszList.empty
    pending_consolidations := Gated.mk h SszList.empty
    proposer_lookahead := () }
  let post ← post.setExitBalanceToConsume (← getActivationExitChurnLimit cfg post)
  let post ← post.setConsolidationBalanceToConsume (← getConsolidationChurnLimit cfg post)
  -- [New in Electra:EIP7251]
  -- add validators that are not yet active to pending balance deposits
  let vs := post.validators.toArray
  let preActivation := ((List.range vs.size).filter fun index =>
      match vs[index]? with
      | some v => v.activation_epoch == FAR_FUTURE_EPOCH
      | none => false).mergeSort fun a b =>
    -- key=lambda index: (post.validators[index].activation_eligibility_epoch, index)
    match vs[a]?, vs[b]? with
    | some va, some vb =>
      decide (va.activation_eligibility_epoch < vb.activation_eligibility_epoch) ||
        (va.activation_eligibility_epoch == vb.activation_eligibility_epoch && decide (a ≤ b))
    | _, _ => decide (a ≤ b)
  let mut post := post
  for index in preActivation do
    let balance ← post.balances.get index site
    let balances ← post.balances.set index U64.zero site
    let validator ← post.validators.get index site
    let validator := { validator with
      effective_balance := U64.zero
      activation_eligibility_epoch := FAR_FUTURE_EPOCH }
    let validators ← post.validators.set index validator site
    -- Use bls.G2_POINT_AT_INFINITY as a signature field placeholder
    -- and GENESIS_SLOT to distinguish from a pending deposit request
    let pending ← (← post.pendingDeposits).push
      { pubkey := validator.pubkey
        withdrawal_credentials := validator.withdrawal_credentials
        amount := balance
        signature := g2PointAtInfinitySignature
        slot := GENESIS_SLOT } site
    post ← ({ post with balances, validators } : BeaconState P .electra).setPendingDeposits pending
  -- Ensure early adopters of compounding credentials go through the activation churn
  for index in [0:post.validators.length] do
    let validator ← post.validators.get index site
    if hasCompoundingWithdrawalCredential validator then
      post ← queueExcessActiveBalance post (← U64.ofNat? index "ValidatorIndex")
  pure post

/-- `upgrade_to_fulu(pre)`. -/
def upgradeToFulu (cfg : Config) (pre : BeaconState P .electra) : M (BeaconState P .fulu) := do
  let epoch ← getCurrentEpoch pre
  pure {
    genesis_time := pre.genesis_time
    genesis_validators_root := pre.genesis_validators_root
    slot := pre.slot
    fork := {
      previous_version := pre.fork.current_version
      -- [Modified in Fulu]
      current_version := ← versionOf cfg.FULU_FORK_VERSION
      epoch := epoch }
    latest_block_header := pre.latest_block_header
    block_roots := pre.block_roots
    state_roots := pre.state_roots
    historical_roots := pre.historical_roots
    eth1_data := pre.eth1_data
    eth1_data_votes := pre.eth1_data_votes
    eth1_deposit_index := pre.eth1_deposit_index
    validators := pre.validators
    balances := pre.balances
    randao_mixes := pre.randao_mixes
    slashings := pre.slashings
    previous_epoch_participation := pre.previous_epoch_participation
    current_epoch_participation := pre.current_epoch_participation
    justification_bits := pre.justification_bits
    previous_justified_checkpoint := pre.previous_justified_checkpoint
    current_justified_checkpoint := pre.current_justified_checkpoint
    finalized_checkpoint := pre.finalized_checkpoint
    inactivity_scores := pre.inactivity_scores
    current_sync_committee := pre.current_sync_committee
    next_sync_committee := pre.next_sync_committee
    latest_execution_payload_header := pre.latest_execution_payload_header
    next_withdrawal_index := pre.next_withdrawal_index
    next_withdrawal_validator_index := pre.next_withdrawal_validator_index
    historical_summaries := pre.historical_summaries
    deposit_requests_start_index := Gated.mk fulu_atLeast_electra (← pre.depositRequestsStartIndex)
    deposit_balance_to_consume := Gated.mk fulu_atLeast_electra (← pre.depositBalanceToConsume)
    exit_balance_to_consume := Gated.mk fulu_atLeast_electra (← pre.exitBalanceToConsume)
    earliest_exit_epoch := Gated.mk fulu_atLeast_electra (← pre.earliestExitEpoch)
    consolidation_balance_to_consume := Gated.mk fulu_atLeast_electra (← pre.consolidationBalanceToConsume)
    earliest_consolidation_epoch := Gated.mk fulu_atLeast_electra (← pre.earliestConsolidationEpoch)
    pending_deposits := Gated.mk fulu_atLeast_electra (← pre.pendingDeposits)
    pending_partial_withdrawals := Gated.mk fulu_atLeast_electra (← pre.pendingPartialWithdrawals)
    pending_consolidations := Gated.mk fulu_atLeast_electra (← pre.pendingConsolidations)
    -- [New in Fulu:EIP7917]
    proposer_lookahead :=
      Gated.mk fulu_atLeast_fulu (← SszVector.ofArray (← initializeProposerLookahead pre)
        "upgrade_to_fulu: proposer_lookahead") }

end JauneConsensus
