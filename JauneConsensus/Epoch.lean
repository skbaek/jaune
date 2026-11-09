import JauneConsensus.EpochAccessors
import JauneConsensus.Deposits

/-!
# Epoch processing (Electra and Fulu)

`process_epoch` and each of its sub-steps, transcribed from `ethereum/consensus-specs` `v1.6.1`
in the operation order of `specs/electra/beacon-chain.md` (`process_epoch`) and
`specs/fulu/beacon-chain.md` (which appends `process_proposer_lookahead`). Each definition cites
the spec file of its latest definition at or before Fulu. Every step is a function
`Config → BeaconState P f → M (BeaconState P f)`: pyspec mutates the state in place; a failure
anywhere is a typed rejection and no partial state is returned.

Typed `uint64` arithmetic is checked (`U64`); Python `int` arithmetic is `Nat`. The general
accessors are `Accessors.lean`, the epoch-only ones `EpochAccessors.lean`.
-/

namespace JauneConsensus
open Jaune (Bytes B256)

variable {P : Preset} {f : CFork}

/-! ## Justification and finalization -/

/-- `weigh_justification_and_finalization` (`specs/phase0/beacon-chain.md`). -/
def weighJustificationAndFinalization (state : BeaconState P f) (totalActiveBalance : Gwei)
    (previousEpochTargetBalance currentEpochTargetBalance : Gwei) : M (BeaconState P f) := do
  let site := "weigh_justification_and_finalization"
  let previousEpoch ← getPreviousEpoch state
  let currentEpoch ← getCurrentEpoch state
  let oldPreviousJustified := state.previous_justified_checkpoint
  let oldCurrentJustified := state.current_justified_checkpoint
  -- Process justifications
  let mut state := { state with previous_justified_checkpoint := state.current_justified_checkpoint }
  -- `justification_bits[1:] = justification_bits[:JUSTIFICATION_BITS_LENGTH - 1]`, `bits[0] = 0`
  let old := state.justification_bits.bits
  let mut bits : Array Bool := #[false] ++ old.extract 0 (JUSTIFICATION_BITS_LENGTH - 1)
  let three ← c64 3
  let two ← c64 2
  let total2 ← totalActiveBalance.mul? two site
  if (← previousEpochTargetBalance.mul? three site) ≥ total2 then
    state := { state with current_justified_checkpoint :=
      { epoch := previousEpoch, root := ← getBlockRoot state previousEpoch } }
    bits := bits.setIfInBounds 1 true
  if (← currentEpochTargetBalance.mul? three site) ≥ total2 then
    state := { state with current_justified_checkpoint :=
      { epoch := currentEpoch, root := ← getBlockRoot state currentEpoch } }
    bits := bits.setIfInBounds 0 true
  if h : bits.size = JUSTIFICATION_BITS_LENGTH then
    state := { state with justification_bits := ⟨bits, h⟩ }
  else throw (.assert s!"{site}: justification_bits length")
  -- Process finalizations
  let b (i : Nat) : M Bool := getAt bits i s!"{site}: bits"
  let allOf (is : List Nat) : M Bool := is.allM b
  -- `all(...) and epoch + k == current_epoch`, short-circuiting as Python's `and` does
  let finalizes (is : List Nat) (cp : Checkpoint) (k : U64) : M Bool := do
    if ← allOf is then
      let e ← cp.epoch.add? k site
      pure (e == currentEpoch)
    else pure false
  if ← finalizes [1, 2, 3] oldPreviousJustified three then
    state := { state with finalized_checkpoint := oldPreviousJustified }
  if ← finalizes [1, 2] oldPreviousJustified two then
    state := { state with finalized_checkpoint := oldPreviousJustified }
  if ← finalizes [0, 1, 2] oldCurrentJustified two then
    state := { state with finalized_checkpoint := oldCurrentJustified }
  if ← finalizes [0, 1] oldCurrentJustified U64.one then
    state := { state with finalized_checkpoint := oldCurrentJustified }
  pure state

/-- `process_justification_and_finalization` (`specs/altair/beacon-chain.md`). -/
def processJustificationAndFinalization (_cfg : Config) (state : BeaconState P f) :
    M (BeaconState P f) := do
  let current ← getCurrentEpoch state
  if current.toNat ≤ GENESIS_EPOCH.toNat + 1 then return state
  let previousIndices ← getUnslashedParticipatingIndices state TIMELY_TARGET_FLAG_INDEX
    (← getPreviousEpoch state)
  let currentIndices ← getUnslashedParticipatingIndices state TIMELY_TARGET_FLAG_INDEX current
  let totalActiveBalance ← getTotalActiveBalance state
  let previousTargetBalance ← getTotalBalance state previousIndices
  let currentTargetBalance ← getTotalBalance state currentIndices
  weighJustificationAndFinalization state totalActiveBalance previousTargetBalance
    currentTargetBalance

/-! ## Inactivity, rewards and penalties -/

/-- `process_inactivity_updates` (`specs/altair/beacon-chain.md`). -/
def processInactivityUpdates (cfg : Config) (state : BeaconState P f) : M (BeaconState P f) := do
  let site := "process_inactivity_updates"
  if (← getCurrentEpoch state) == GENESIS_EPOCH then return state
  let n := state.validators.toArray.size
  -- pyspec recomputes these from a state whose inputs the loop does not change
  let participating := indexTable n
    (← getUnslashedParticipatingIndices state TIMELY_TARGET_FLAG_INDEX (← getPreviousEpoch state))
  let leak ← isInInactivityLeak state
  let bias ← c64 cfg.INACTIVITY_SCORE_BIAS
  let recovery ← c64 cfg.INACTIVITY_SCORE_RECOVERY_RATE
  let mut scores := state.inactivity_scores
  for index in ← getEligibleValidatorIndices state do
    let i := index.toNat
    if ← getAt participating i site then
      scores ← scores.modify i (fun s => s.sub? (if s < U64.one then s else U64.one) site) site
    else
      scores ← scores.modify i (fun s => s.add? bias site) site
    if !leak then
      scores ← scores.modify i (fun s => s.sub? (if s < recovery then s else recovery) site) site
  pure { state with inactivity_scores := scores }

/-- The four deltas of `process_rewards_and_penalties`: one per participation flag, then the
inactivity penalties (`specs/altair/beacon-chain.md`). -/
def rewardsAndPenaltiesDeltas (cfg : Config) (state : BeaconState P f) : M (List Deltas) := do
  let flagDeltas ← (List.range PARTICIPATION_FLAG_WEIGHTS.length).mapM (getFlagIndexDeltas state)
  pure (flagDeltas ++ [← getInactivityPenaltyDeltas cfg state])

/-- `process_rewards_and_penalties` (`specs/altair/beacon-chain.md`). -/
def processRewardsAndPenalties (cfg : Config) (state : BeaconState P f) : M (BeaconState P f) := do
  if (← getCurrentEpoch state) == GENESIS_EPOCH then return state
  let deltas ← rewardsAndPenaltiesDeltas cfg state
  let mut state := state
  for (rewards, penalties) in deltas do
    for i in List.range state.validators.toArray.size do
      let index ← U64.ofNat? i "ValidatorIndex"
      state ← increaseBalance state index (← getAt rewards i "process_rewards_and_penalties")
      state ← decreaseBalance state index (← getAt penalties i "process_rewards_and_penalties")
  pure state

/-! ## Registry and slashings -/

/-- `process_registry_updates`, Electra (`specs/electra/beacon-chain.md`). Each iteration reads
the validator from the current state, as pyspec's view does. -/
def processRegistryUpdatesElectra (cfg : Config) (state : BeaconState P f) :
    M (BeaconState P f) := do
  let site := "process_registry_updates"
  let currentEpoch ← getCurrentEpoch state
  let activationEpoch ← computeActivationExitEpoch P currentEpoch
  let ejection ← c64 cfg.EJECTION_BALANCE
  let mut state := state
  for i in List.range state.validators.toArray.size do
    let validator ← state.validators.get i site
    if isEligibleForActivationQueue P f validator then
      let e ← currentEpoch.add? U64.one site
      state := { state with validators :=
        ← state.validators.set i { validator with activation_eligibility_epoch := e } site }
    else if isActiveValidator validator currentEpoch && validator.effective_balance ≤ ejection then
      state ← initiateValidatorExit cfg state (← U64.ofNat? i "ValidatorIndex")
    else if isEligibleForActivation state validator then
      state := { state with validators :=
        ← state.validators.set i { validator with activation_epoch := activationEpoch } site }
  pure state

/-- `get_validator_activation_churn_limit(state)` (`specs/deneb/beacon-chain.md`, EIP-7514):
`min(MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT, get_validator_churn_limit(state))`. -/
def getValidatorActivationChurnLimit (cfg : Config) (state : BeaconState P f) : M U64 := do
  let maxChurn ← c64 cfg.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT
  let churn ← getValidatorChurnLimit cfg state
  pure (if maxChurn < churn then maxChurn else churn)

/-- `process_registry_updates`, Deneb (`specs/deneb/beacon-chain.md`): eligibility and ejections,
then the activation queue sorted by `(activation_eligibility_epoch, index)` and cut at the
activation churn limit. -/
def processRegistryUpdatesDeneb (cfg : Config) (state : BeaconState P f) :
    M (BeaconState P f) := do
  let site := "process_registry_updates"
  let ejection ← c64 cfg.EJECTION_BALANCE
  let mut state := state
  for i in List.range state.validators.toArray.size do
    let validator ← state.validators.get i site
    if isEligibleForActivationQueue P f validator then
      let e ← (← getCurrentEpoch state).add? U64.one site
      state := { state with validators :=
        ← state.validators.set i { validator with activation_eligibility_epoch := e } site }
    let validator ← state.validators.get i site
    if isActiveValidator validator (← getCurrentEpoch state) &&
        validator.effective_balance ≤ ejection then
      state ← initiateValidatorExit cfg state (← U64.ofNat? i "ValidatorIndex")
  let mut queue : List (Nat × Nat) := []
  let mut i := 0
  for v in state.validators.toArray do
    if isEligibleForActivation state v then queue := (v.activation_eligibility_epoch.toNat, i) :: queue
    i := i + 1
  let sorted := queue.reverse.mergeSort (fun a b => decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)))
  let limit := (← getValidatorActivationChurnLimit cfg state).toNat
  for (_, index) in sorted.take limit do
    let validator ← state.validators.get index site
    let e ← computeActivationExitEpoch P (← getCurrentEpoch state)
    state := { state with validators :=
      ← state.validators.set index { validator with activation_epoch := e } site }
  pure state

/-- `process_registry_updates`: Electra from Electra on, Deneb before. -/
def processRegistryUpdates (cfg : Config) (state : BeaconState P f) : M (BeaconState P f) :=
  if f.atLeast .electra then processRegistryUpdatesElectra cfg state
  else processRegistryUpdatesDeneb cfg state

/-- `process_slashings`: Electra (`specs/electra/beacon-chain.md`) computes a penalty per
effective-balance increment; Bellatrix to Deneb (`specs/bellatrix/beacon-chain.md`) scale each
validator's increments by the adjusted total and divide by the total balance.
`sum(state.slashings)` adds typed `Gwei` values, so it is checked `uint64` addition.
Pyspec's remerkleable `uint64` coerces `0 + Gwei` and `int + Gwei` to `uint64` and raises on overflow, so the checked adds here are exact. -/
def processSlashings (_cfg : Config) (state : BeaconState P f) : M (BeaconState P f) := do
  let site := "process_slashings"
  let epoch ← getCurrentEpoch state
  let totalBalance ← getTotalActiveBalance state
  let sumSlashings ← state.slashings.toArray.foldlM (fun acc x => acc.add? x site) U64.zero
  let scaled ← sumSlashings.mul? (← c64 P.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX) site
  let adjusted := if scaled < totalBalance then scaled else totalBalance
  let increment ← c64 P.EFFECTIVE_BALANCE_INCREMENT
  let half ← c64 (P.EPOCHS_PER_SLASHINGS_VECTOR / 2)
  let mut state := state
  if f.atLeast .electra then
    let penaltyPerIncrement ← adjusted.div? (← totalBalance.div? increment site) site
    for i in List.range state.validators.toArray.size do
      let validator ← state.validators.get i site
      if validator.slashed then
        if (← epoch.add? half site) == validator.withdrawable_epoch then
          let increments ← validator.effective_balance.div? increment site
          let penalty ← penaltyPerIncrement.mul? increments site
          state ← decreaseBalance state (← U64.ofNat? i "ValidatorIndex") penalty
  else
    for i in List.range state.validators.toArray.size do
      let validator ← state.validators.get i site
      if validator.slashed then
        if (← epoch.add? half site) == validator.withdrawable_epoch then
          let numerator ← (← validator.effective_balance.div? increment site).mul? adjusted site
          let penalty ← (← numerator.div? totalBalance site).mul? increment site
          state ← decreaseBalance state (← U64.ofNat? i "ValidatorIndex") penalty
  pure state

/-- `process_eth1_data_reset` (`specs/phase0/beacon-chain.md`). -/
def processEth1DataReset (_cfg : Config) (state : BeaconState P f) : M (BeaconState P f) := do
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one "process_eth1_data_reset"
  let r ← nextEpoch.mod? (← c64 P.EPOCHS_PER_ETH1_VOTING_PERIOD) "process_eth1_data_reset"
  if r.toNat == 0 then pure { state with eth1_data_votes := SszList.empty }
  else pure state

/-! ## Pending deposits, consolidations and effective balances (Electra) -/

/-- The index of the validator with `pubkey` (`validator_pubkeys.index(pubkey)`), if any. -/
def findValidatorIndex (state : BeaconState P f) (pubkey : BLSPubkey) : Option Nat :=
  state.validators.toArray.findIdx? (·.pubkey == pubkey)

/-- `apply_pending_deposit(state, deposit)` (`specs/electra/beacon-chain.md`). -/
def applyPendingDeposit (ctx : Ctx) (state : BeaconState P f) (deposit : PendingDeposit) :
    M (BeaconState P f) := do
  match findValidatorIndex state deposit.pubkey with
  | none =>
    if ← isValidDepositSignature ctx deposit.pubkey deposit.withdrawal_credentials deposit.amount
        deposit.signature then
      addValidatorToRegistry state deposit.pubkey deposit.withdrawal_credentials deposit.amount
    else pure state
  | some i => increaseBalance state (← U64.ofNat? i "ValidatorIndex") deposit.amount

/-- `process_pending_deposits(state)` (`specs/electra/beacon-chain.md`; Fulu's override drops
the Eth1-bridge break). `processed_amount`
starts as the Python `int` `0` and becomes `Gwei` at its first addition, so its arithmetic is
`uint64`. Pyspec's remerkleable `uint64` coerces `int + Gwei` to `uint64` and raises on overflow, so the checked adds here are exact. -/
def processPendingDeposits (ctx : Ctx) (state : BeaconState P f) : M (BeaconState P f) := do
  let site := "process_pending_deposits"
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
  let availableForProcessing ← (← state.depositBalanceToConsume).add?
    (← getActivationExitChurnLimit ctx.cfg state) site
  let mut processedAmount := U64.zero
  let mut nextDepositIndex := 0
  let mut depositsToPostpone : Array PendingDeposit := #[]
  let mut isChurnLimitReached := false
  let finalizedSlot ← computeStartSlotAtEpoch P state.finalized_checkpoint.epoch
  let requestsStart ← state.depositRequestsStartIndex
  let pending ← state.pendingDeposits
  let mut state := state
  for deposit in pending.toArray do
    -- Do not process deposit requests if Eth1 bridge deposits are not yet applied
    -- (Electra; Fulu drops the check, `v1.7.0-beta.4` `specs/fulu/beacon-chain.md`).
    if !(f.atLeast .fulu) && deposit.slot > GENESIS_SLOT && state.eth1_deposit_index < requestsStart then break
    -- Check if deposit has been finalized, otherwise, stop processing.
    if deposit.slot > finalizedSlot then break
    -- Check if number of processed deposits has not reached the limit, otherwise, stop processing.
    if nextDepositIndex ≥ P.MAX_PENDING_DEPOSITS_PER_EPOCH then break
    -- Read validator state
    let mut isValidatorExited := false
    let mut isValidatorWithdrawn := false
    if let some i := findValidatorIndex state deposit.pubkey then
      let validator ← state.validators.get i site
      isValidatorExited := validator.exit_epoch < FAR_FUTURE_EPOCH
      isValidatorWithdrawn := validator.withdrawable_epoch < nextEpoch
    if isValidatorWithdrawn then
      -- Deposited balance will never become active. Increase balance but do not consume churn
      state ← applyPendingDeposit ctx state deposit
    else if isValidatorExited then
      -- Validator is exiting, postpone the deposit until after withdrawable epoch
      depositsToPostpone := depositsToPostpone.push deposit
    else
      -- Check if deposit fits in the churn, otherwise, do no more deposit processing in this epoch.
      isChurnLimitReached := (← processedAmount.add? deposit.amount site) > availableForProcessing
      if isChurnLimitReached then break
      -- Consume churn and apply deposit.
      processedAmount ← processedAmount.add? deposit.amount site
      state ← applyPendingDeposit ctx state deposit
    -- Regardless of how the deposit was handled, we move on in the queue.
    nextDepositIndex := nextDepositIndex + 1
  let rest := pending.toArray.extract nextDepositIndex pending.length ++ depositsToPostpone
  state ← state.setPendingDeposits (← SszList.ofArray rest site)
  -- Accumulate churn only if the churn limit has been hit.
  if isChurnLimitReached then
    state.setDepositBalanceToConsume (← availableForProcessing.sub? processedAmount site)
  else
    state.setDepositBalanceToConsume U64.zero


/-- `process_pending_consolidations` (`specs/electra/beacon-chain.md`). -/
def processPendingConsolidations (_cfg : Config) (state : BeaconState P f) :
    M (BeaconState P f) := do
  let site := "process_pending_consolidations"
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
  let pending ← state.pendingConsolidations
  let mut state := state
  let mut next := 0
  for pc in pending.toArray do
    let source ← state.validators.get pc.source_index.toNat site
    if source.slashed then
      next := next + 1
      continue
    if source.withdrawable_epoch > nextEpoch then break
    let balance ← state.balances.get pc.source_index.toNat site
    let sourceEffective := if balance < source.effective_balance then balance
      else source.effective_balance
    state ← decreaseBalance state pc.source_index sourceEffective
    state ← increaseBalance state pc.target_index sourceEffective
    next := next + 1
  state.setPendingConsolidations (← SszList.ofArray (pending.toArray.extract next pending.length) site)

/-- `process_effective_balance_updates`: the ceiling is `get_max_effective_balance(validator)` from
Electra (`specs/electra/beacon-chain.md`), `MAX_EFFECTIVE_BALANCE` before
(`specs/phase0/beacon-chain.md`). -/
def processEffectiveBalanceUpdates (_cfg : Config) (state : BeaconState P f) :
    M (BeaconState P f) := do
  let site := "process_effective_balance_updates"
  let inc ← c64 P.EFFECTIVE_BALANCE_INCREMENT
  let hysteresisIncrement ← inc.div? (← c64 P.HYSTERESIS_QUOTIENT) site
  let downward ← hysteresisIncrement.mul? (← c64 P.HYSTERESIS_DOWNWARD_MULTIPLIER) site
  let upward ← hysteresisIncrement.mul? (← c64 P.HYSTERESIS_UPWARD_MULTIPLIER) site
  let mut validators := state.validators
  for i in List.range validators.toArray.size do
    let validator ← validators.get i site
    let balance ← state.balances.get i site
    let maxEffective ← c64 (if f.atLeast .electra then getMaxEffectiveBalance P validator
      else P.MAX_EFFECTIVE_BALANCE)
    -- `a < b or c < d`, short-circuiting as Python's `or` does
    let low ← balance.add? downward site
    let update ← if low < validator.effective_balance then pure true
      else do
        let high ← validator.effective_balance.add? upward site
        pure (high < balance)
    if update then
      let rounded ← balance.sub? (← balance.mod? inc site) site
      let eb := if rounded < maxEffective then rounded else maxEffective
      validators ← validators.set i { validator with effective_balance := eb } site
  pure { state with validators }

/-! ## Resets, summaries and participation -/

/-- `process_slashings_reset` (`specs/phase0/beacon-chain.md`). -/
def processSlashingsReset (_cfg : Config) (state : BeaconState P f) : M (BeaconState P f) := do
  let site := "process_slashings_reset"
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
  let i ← nextEpoch.mod? (← c64 P.EPOCHS_PER_SLASHINGS_VECTOR) site
  pure { state with slashings := ← state.slashings.set i.toNat U64.zero site }

/-- `process_randao_mixes_reset` (`specs/phase0/beacon-chain.md`). -/
def processRandaoMixesReset (_cfg : Config) (state : BeaconState P f) : M (BeaconState P f) := do
  let site := "process_randao_mixes_reset"
  let currentEpoch ← getCurrentEpoch state
  let nextEpoch ← currentEpoch.add? U64.one site
  let i ← nextEpoch.mod? (← c64 P.EPOCHS_PER_HISTORICAL_VECTOR) site
  let mix ← getRandaoMix state currentEpoch
  pure { state with randao_mixes := ← state.randao_mixes.set i.toNat mix site }

/-- `process_historical_summaries_update` (`specs/capella/beacon-chain.md`). -/
def processHistoricalSummariesUpdate (_cfg : Config) (state : BeaconState P f) :
    M (BeaconState P f) := do
  let site := "process_historical_summaries_update"
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
  let period ← c64 (P.SLOTS_PER_HISTORICAL_ROOT / P.SLOTS_PER_EPOCH)
  if (← nextEpoch.mod? period site).toNat == 0 then
    let summary : HistoricalSummary :=
      { block_summary_root := hashTreeRoot state.block_roots
        state_summary_root := hashTreeRoot state.state_roots }
    pure { state with historical_summaries := ← state.historical_summaries.push summary site }
  else pure state

/-- `process_participation_flag_updates` (`specs/altair/beacon-chain.md`). -/
def processParticipationFlagUpdates (_cfg : Config) (state : BeaconState P f) :
    M (BeaconState P f) := do
  let site := "process_participation_flag_updates"
  pure { state with
    previous_epoch_participation := state.current_epoch_participation
    current_epoch_participation :=
      ← SszList.ofArray (Array.replicate state.validators.toArray.size UIntN.zero) site }

/-- `process_sync_committee_updates` (`specs/altair/beacon-chain.md`). -/
def processSyncCommitteeUpdates (ctx : Ctx) (state : BeaconState P f) :
    M (BeaconState P f) := do
  let site := "process_sync_committee_updates"
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
  if (← nextEpoch.mod? (← c64 P.EPOCHS_PER_SYNC_COMMITTEE_PERIOD) site).toNat == 0 then
    let next ← getNextSyncCommittee state
    pure { state with current_sync_committee := state.next_sync_committee,
                      next_sync_committee := next }
  else pure state

/-! ## Proposer lookahead (Fulu) -/

/-- `process_proposer_lookahead` (`specs/fulu/beacon-chain.md`). -/
def processProposerLookahead (_cfg : Config) (state : BeaconState P f) : M (BeaconState P f) := do
  let site := "process_proposer_lookahead"
  let lookahead ← state.proposerLookahead
  let la := lookahead.toArray
  let lastEpochStart := la.size - P.SLOTS_PER_EPOCH
  require (la.size ≥ P.SLOTS_PER_EPOCH) s!"{site}: len(proposer_lookahead) >= SLOTS_PER_EPOCH"
  let e ← (← (← getCurrentEpoch state).add? (← c64 P.MIN_SEED_LOOKAHEAD) site).add? U64.one site
  let lastEpochProposers ← getBeaconProposerIndices state e
  -- `lookahead[:last_epoch_start] = lookahead[SLOTS_PER_EPOCH:]`;
  -- `lookahead[last_epoch_start:] = last_epoch_proposers` (the slice assignment keeps the length)
  require (lastEpochProposers.size == la.size - lastEpochStart)
    s!"{site}: last epoch proposers fill the tail"
  state.setProposerLookahead
    (← SszVector.ofArray (la.extract P.SLOTS_PER_EPOCH la.size ++ lastEpochProposers) site)

/-! ## `process_epoch` -/

/-- `process_epoch(state)`: Electra's order (`specs/electra/beacon-chain.md`), with Fulu's
`process_proposer_lookahead` appended (`specs/fulu/beacon-chain.md`); before Electra, Capella's
order as Deneb keeps it (`specs/capella/beacon-chain.md`: no pending deposits or consolidations).
-/
def processEpoch (ctx : Ctx) (state : BeaconState P f) : M (BeaconState P f) := do
  let cfg := ctx.cfg
  let state ← processJustificationAndFinalization cfg state
  let state ← processInactivityUpdates cfg state
  let state ← processRewardsAndPenalties cfg state
  let state ← processRegistryUpdates cfg state
  let state ← processSlashings cfg state
  let state ← processEth1DataReset cfg state
  let state ← if f.atLeast .electra then do
      let state ← processPendingDeposits ctx state
      processPendingConsolidations cfg state
    else pure state
  let state ← processEffectiveBalanceUpdates cfg state
  let state ← processSlashingsReset cfg state
  let state ← processRandaoMixesReset cfg state
  let state ← processHistoricalSummariesUpdate cfg state
  let state ← processParticipationFlagUpdates cfg state
  let state ← processSyncCommitteeUpdates ctx state
  if f.atLeast .fulu then processProposerLookahead cfg state else pure state

end JauneConsensus
