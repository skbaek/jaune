import JauneConsensus.GloasEpochAccessors

/-!
# Gloas epoch processing (goal `eip8282-gloas-cross-layer-v1`, U3)

`process_epoch` (`specs/gloas/beacon-chain.md`, :1633) and each of its sub-steps over
`JauneConsensus.Gloas.BeaconState`, transcribed from `ethereum/consensus-specs` `v1.7.0-beta.4`:

* reused by reference and copied here, each reaching the Gloas helpers through name resolution
  (`GloasOps.lean`): justification and finalization, inactivity, rewards and penalties
  (Altair), registry updates (Electra, reaching the Gloas exit churn through
  `initiate_validator_exit`), slashings (Electra), the eth1, slashings and randao resets
  (phase0), pending consolidations and effective balances (Electra), historical summaries
  (Capella), participation flags and the sync committee (Altair, reaching the Gloas
  `get_next_sync_committee_indices`), and the proposer lookahead (Fulu, reaching the Gloas
  `get_beacon_proposer_indices`);
* modified in Gloas: `process_pending_deposits` (:1659, EIP-8061: the activation churn, and no
  Eth1-bridge check);
* new in Gloas: `process_builder_pending_payments` (:1719) and `process_ptc_window` (:1737).

Every step is `Config → BeaconState P → M (BeaconState P)` (or takes the `Ctx` where it needs the
BLS switch); a failure anywhere is a typed rejection and no partial state is returned.
-/

namespace JauneConsensus.Gloas

open Jaune

variable {P : Preset}

/-! ## Justification and finalization -/

/-- `weigh_justification_and_finalization` (phase0). -/
def weighJustificationAndFinalization (state : BeaconState P) (totalActiveBalance : Gwei)
    (previousEpochTargetBalance currentEpochTargetBalance : Gwei) : M (BeaconState P) := do
  let site := "weigh_justification_and_finalization"
  let previousEpoch ← getPreviousEpoch state
  let currentEpoch ← getCurrentEpoch state
  let oldPreviousJustified := state.previous_justified_checkpoint
  let oldCurrentJustified := state.current_justified_checkpoint
  let mut state := { state with previous_justified_checkpoint := state.current_justified_checkpoint }
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
  let b (i : Nat) : M Bool := getAt bits i s!"{site}: bits"
  let allOf (is : List Nat) : M Bool := is.allM b
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

/-- `process_justification_and_finalization` (Altair). -/
def processJustificationAndFinalization (_cfg : Config) (state : BeaconState P) :
    M (BeaconState P) := do
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

/-- `process_inactivity_updates` (Altair; `saturating_sub` is `x - min(x, y)`). -/
def processInactivityUpdates (cfg : Config) (state : BeaconState P) : M (BeaconState P) := do
  let site := "process_inactivity_updates"
  if (← getCurrentEpoch state) == GENESIS_EPOCH then return state
  let n := state.validators.toArray.size
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

/-- The four deltas of `process_rewards_and_penalties` (Altair). -/
def rewardsAndPenaltiesDeltas (cfg : Config) (state : BeaconState P) : M (List Deltas) := do
  let flagDeltas ← (List.range PARTICIPATION_FLAG_WEIGHTS.length).mapM (getFlagIndexDeltas state)
  pure (flagDeltas ++ [← getInactivityPenaltyDeltas cfg state])

/-- `process_rewards_and_penalties` (Altair). -/
def processRewardsAndPenalties (cfg : Config) (state : BeaconState P) : M (BeaconState P) := do
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

/-- `process_registry_updates` (Electra): each iteration reads the validator from the current
state; an ejection goes through the Gloas `initiate_validator_exit`. -/
def processRegistryUpdates (cfg : Config) (state : BeaconState P) : M (BeaconState P) := do
  let site := "process_registry_updates"
  let currentEpoch ← getCurrentEpoch state
  let activationEpoch ← computeActivationExitEpoch P currentEpoch
  let ejection ← c64 cfg.EJECTION_BALANCE
  let mut state := state
  for i in List.range state.validators.toArray.size do
    let validator ← state.validators.get i site
    if isEligibleForActivationQueue P .gloas validator then
      let e ← currentEpoch.add? U64.one site
      state := { state with validators :=
        ← state.validators.set i { validator with activation_eligibility_epoch := e } site }
    else if isActiveValidator validator currentEpoch && validator.effective_balance ≤ ejection then
      state ← initiateValidatorExit cfg state (← U64.ofNat? i "ValidatorIndex")
    else if isEligibleForActivation state validator then
      state := { state with validators :=
        ← state.validators.set i { validator with activation_epoch := activationEpoch } site }
  pure state

/-- `process_slashings` (Electra): a penalty per effective-balance increment;
`Gwei(sum(state.slashings))` is checked `uint64` addition. -/
def processSlashings (_cfg : Config) (state : BeaconState P) : M (BeaconState P) := do
  let site := "process_slashings"
  let epoch ← getCurrentEpoch state
  let totalBalance ← getTotalActiveBalance state
  let sumSlashings ← state.slashings.toArray.foldlM (fun acc x => acc.add? x site) U64.zero
  let scaled ← sumSlashings.mul? (← c64 P.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX) site
  let adjusted := if scaled < totalBalance then scaled else totalBalance
  let increment ← c64 P.EFFECTIVE_BALANCE_INCREMENT
  let half ← c64 (P.EPOCHS_PER_SLASHINGS_VECTOR / 2)
  let penaltyPerIncrement ← adjusted.div? (← totalBalance.div? increment site) site
  let mut state := state
  for i in List.range state.validators.toArray.size do
    let validator ← state.validators.get i site
    if validator.slashed then
      if (← epoch.add? half site) == validator.withdrawable_epoch then
        let increments ← validator.effective_balance.div? increment site
        let penalty ← penaltyPerIncrement.mul? increments site
        state ← decreaseBalance state (← U64.ofNat? i "ValidatorIndex") penalty
  pure state

/-- `process_eth1_data_reset` (phase0). -/
def processEth1DataReset (_cfg : Config) (state : BeaconState P) : M (BeaconState P) := do
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one "process_eth1_data_reset"
  let r ← nextEpoch.mod? (← c64 P.EPOCHS_PER_ETH1_VOTING_PERIOD) "process_eth1_data_reset"
  if r.toNat == 0 then pure { state with eth1_data_votes := SszList.empty }
  else pure state

/-! ## Pending deposits, consolidations, builder payments, effective balances -/

/-- The index of the validator with `pubkey` (`validator_pubkeys.index(pubkey)`), if any. -/
def findValidatorIndex (state : BeaconState P) (pubkey : BLSPubkey) : Option Nat :=
  state.validators.toArray.findIdx? (·.pubkey == pubkey)

/-- `apply_pending_deposit(state, deposit)` (Electra). -/
def applyPendingDeposit (ctx : Ctx) (state : BeaconState P) (deposit : PendingDeposit) :
    M (BeaconState P) := do
  match findValidatorIndex state deposit.pubkey with
  | none =>
    if ← isValidDepositSignature ctx deposit.pubkey deposit.withdrawal_credentials deposit.amount
        deposit.signature then
      addValidatorToRegistry state deposit.pubkey deposit.withdrawal_credentials deposit.amount
    else pure state
  | some i => increaseBalance state (← U64.ofNat? i "ValidatorIndex") deposit.amount

/-- `process_pending_deposits(state)` (Gloas, :1659, EIP-8061): deposits consume
`get_activation_churn_limit`; there is no Eth1-bridge check. `processed_amount` is `Gwei` from its
first addition, so its arithmetic is checked `uint64`. -/
def processPendingDeposits (ctx : Ctx) (state : BeaconState P) : M (BeaconState P) := do
  let site := "process_pending_deposits"
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
  let availableForProcessing ← state.deposit_balance_to_consume.add?
    (← getActivationChurnLimit ctx.cfg state) site
  let mut processedAmount := U64.zero
  let mut nextDepositIndex := 0
  let mut depositsToPostpone : Array PendingDeposit := #[]
  let mut isChurnLimitReached := false
  let finalizedSlot ← computeStartSlotAtEpoch P state.finalized_checkpoint.epoch
  let pending := state.pending_deposits
  let mut state := state
  for deposit in pending.toArray do
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
  let toConsume ← if isChurnLimitReached then availableForProcessing.sub? processedAmount site
    else pure U64.zero
  -- Accumulate churn only if the churn limit has been hit.
  pure { state with pending_deposits := ProgressiveListS.ofArray rest
                    deposit_balance_to_consume := toConsume }

/-- `process_pending_consolidations` (Electra). -/
def processPendingConsolidations (_cfg : Config) (state : BeaconState P) : M (BeaconState P) := do
  let site := "process_pending_consolidations"
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
  let pending := state.pending_consolidations
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
  pure { state with pending_consolidations :=
    ProgressiveListS.ofArray (pending.toArray.extract next pending.length) }

/-- `process_builder_pending_payments(state)` (Gloas, :1719): the previous epoch's payments
(the first `SLOTS_PER_EPOCH`) whose weight reaches the quorum become pending withdrawals; the
current epoch's payments move down and the second half is emptied. -/
def processBuilderPendingPayments (_cfg : Config) (state : BeaconState P) : M (BeaconState P) := do
  let site := "process_builder_pending_payments"
  let quorum ← getBuilderPaymentQuorumThreshold state
  let payments := state.builder_pending_payments.toArray
  let spe := P.SLOTS_PER_EPOCH
  require (decide (spe ≤ payments.size)) s!"{site}: SLOTS_PER_EPOCH <= len(builder_pending_payments)"
  let mut withdrawals := state.builder_pending_withdrawals
  for payment in payments.extract 0 spe do
    if quorum ≤ payment.weight then withdrawals := withdrawals.push payment.withdrawal
  -- `payments[:SPE] = payments[SPE:]; payments[SPE:] = [empty] * SPE` (each slice assignment keeps
  -- the length)
  let oldPayments := payments.extract spe payments.size
  require (oldPayments.size == spe) s!"{site}: old payments fill the first half"
  let shifted := oldPayments ++ Array.replicate spe BuilderPendingPayment.empty
  pure { state with
    builder_pending_withdrawals := withdrawals
    builder_pending_payments := ← SszVector.ofArray shifted site }

/-- `process_effective_balance_updates` (Electra): the ceiling is `get_max_effective_balance`. -/
def processEffectiveBalanceUpdates (_cfg : Config) (state : BeaconState P) : M (BeaconState P) := do
  let site := "process_effective_balance_updates"
  let inc ← c64 P.EFFECTIVE_BALANCE_INCREMENT
  let hysteresisIncrement ← inc.div? (← c64 P.HYSTERESIS_QUOTIENT) site
  let downward ← hysteresisIncrement.mul? (← c64 P.HYSTERESIS_DOWNWARD_MULTIPLIER) site
  let upward ← hysteresisIncrement.mul? (← c64 P.HYSTERESIS_UPWARD_MULTIPLIER) site
  let mut validators := state.validators
  for i in List.range validators.toArray.size do
    let validator ← validators.get i site
    let balance ← state.balances.get i site
    let maxEffective ← c64 (getMaxEffectiveBalance P validator)
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

/-- `process_slashings_reset` (phase0). -/
def processSlashingsReset (_cfg : Config) (state : BeaconState P) : M (BeaconState P) := do
  let site := "process_slashings_reset"
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
  let i ← nextEpoch.mod? (← c64 P.EPOCHS_PER_SLASHINGS_VECTOR) site
  pure { state with slashings := ← state.slashings.set i.toNat U64.zero site }

/-- `process_randao_mixes_reset` (phase0). -/
def processRandaoMixesReset (_cfg : Config) (state : BeaconState P) : M (BeaconState P) := do
  let site := "process_randao_mixes_reset"
  let currentEpoch ← getCurrentEpoch state
  let nextEpoch ← currentEpoch.add? U64.one site
  let i ← nextEpoch.mod? (← c64 P.EPOCHS_PER_HISTORICAL_VECTOR) site
  let mix ← getRandaoMix state currentEpoch
  pure { state with randao_mixes := ← state.randao_mixes.set i.toNat mix site }

/-- `process_historical_summaries_update` (Capella). -/
def processHistoricalSummariesUpdate (_cfg : Config) (state : BeaconState P) :
    M (BeaconState P) := do
  let site := "process_historical_summaries_update"
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
  let period ← c64 (P.SLOTS_PER_HISTORICAL_ROOT / P.SLOTS_PER_EPOCH)
  if (← nextEpoch.mod? period site).toNat == 0 then
    let summary : HistoricalSummary :=
      { block_summary_root := hashTreeRoot state.block_roots
        state_summary_root := hashTreeRoot state.state_roots }
    pure { state with historical_summaries := ← state.historical_summaries.push summary site }
  else pure state

/-- `process_participation_flag_updates` (Altair). -/
def processParticipationFlagUpdates (_cfg : Config) (state : BeaconState P) :
    M (BeaconState P) := do
  pure { state with
    previous_epoch_participation := state.current_epoch_participation
    current_epoch_participation :=
      ProgressiveListS.ofArray (Array.replicate state.validators.toArray.size UIntN.zero) }

/-- `process_sync_committee_updates` (Altair), with the Gloas next sync committee. -/
def processSyncCommitteeUpdates (ctx : Ctx) (state : BeaconState P) : M (BeaconState P) := do
  let site := "process_sync_committee_updates"
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
  if (← nextEpoch.mod? (← c64 P.EPOCHS_PER_SYNC_COMMITTEE_PERIOD) site).toNat == 0 then
    let next ← getNextSyncCommittee ctx.blsActive state
    pure { state with current_sync_committee := state.next_sync_committee,
                      next_sync_committee := next }
  else pure state

/-! ## Lookaheads -/

/-- `process_proposer_lookahead` (Fulu), with the Gloas `get_beacon_proposer_indices`. -/
def processProposerLookahead (_cfg : Config) (state : BeaconState P) : M (BeaconState P) := do
  let site := "process_proposer_lookahead"
  let la := state.proposer_lookahead.toArray
  let lastEpochStart := la.size - P.SLOTS_PER_EPOCH
  require (la.size ≥ P.SLOTS_PER_EPOCH) s!"{site}: len(proposer_lookahead) >= SLOTS_PER_EPOCH"
  let e ← (← (← getCurrentEpoch state).add? (← c64 P.MIN_SEED_LOOKAHEAD) site).add? U64.one site
  let lastEpochProposers ← getBeaconProposerIndices state e
  require (lastEpochProposers.size == la.size - lastEpochStart)
    s!"{site}: last epoch proposers fill the tail"
  pure { state with proposer_lookahead :=
    ← SszVector.ofArray (la.extract P.SLOTS_PER_EPOCH la.size ++ lastEpochProposers) site }

/-- `process_ptc_window(state)` (Gloas, :1737): shift the window one epoch forward, then fill the
last epoch with `compute_ptc` for each slot of epoch `current + MIN_SEED_LOOKAHEAD + 1`. The new
committees are computed after the shift; `compute_ptc` does not read the window. -/
def processPtcWindow (_cfg : Config) (state : BeaconState P) : M (BeaconState P) := do
  let site := "process_ptc_window"
  let window := state.ptc_window.toArray
  let spe := P.SLOTS_PER_EPOCH
  require (decide (spe ≤ window.size)) s!"{site}: SLOTS_PER_EPOCH <= len(ptc_window)"
  let nextEpoch ← (← (← getCurrentEpoch state).add? (← c64 P.MIN_SEED_LOOKAHEAD) site).add?
    U64.one site
  let startSlot ← computeStartSlotAtEpoch P nextEpoch
  let endSlot ← startSlot.add? (← c64 spe) site
  let mut last : Array (PayloadTimelinessCommittee P) := #[]
  for slot in [startSlot.toNat:endSlot.toNat] do
    last := last.push (← computePtc state (← U64.ofNat? slot "Slot"))
  pure { state with ptc_window := ← SszVector.ofArray (window.extract spe window.size ++ last) site }

/-! ## `process_epoch` -/

/-- `process_epoch(state)` (Gloas, :1633). -/
def processEpoch (ctx : Ctx) (state : BeaconState P) : M (BeaconState P) := do
  let cfg := ctx.cfg
  let state ← processJustificationAndFinalization cfg state
  let state ← processInactivityUpdates cfg state
  let state ← processRewardsAndPenalties cfg state
  let state ← processRegistryUpdates cfg state
  let state ← processSlashings cfg state
  let state ← processEth1DataReset cfg state
  let state ← processPendingDeposits ctx state
  let state ← processPendingConsolidations cfg state
  let state ← processBuilderPendingPayments cfg state
  let state ← processEffectiveBalanceUpdates cfg state
  let state ← processSlashingsReset cfg state
  let state ← processRandaoMixesReset cfg state
  let state ← processHistoricalSummariesUpdate cfg state
  let state ← processParticipationFlagUpdates cfg state
  let state ← processSyncCommitteeUpdates ctx state
  let state ← processProposerLookahead cfg state
  processPtcWindow cfg state

end JauneConsensus.Gloas
