import JauneConsensus.GloasOps

/-!
# Gloas beacon-state mutators (goal `eip8282-gloas-cross-layer-v1`, U3)

The mutators of `ethereum/consensus-specs` `v1.7.0-beta.4` over
`JauneConsensus.Gloas.BeaconState`, each a function returning the new state (pyspec mutates in
place; a failure anywhere is a typed rejection and no partial state is returned).

* Reused by reference, copied over the Gloas state: `increase_balance`, `decrease_balance`
  (phase0), `compute_consolidation_epoch_and_update_churn`, `initiate_validator_exit`,
  `queue_excess_active_balance`, `switch_to_compounding_validator`, `add_validator_to_registry`
  (Electra). Each calls the Gloas helpers it reaches: `initiate_validator_exit` reaches the Gloas
  `compute_exit_epoch_and_update_churn` and through it `get_exit_churn_limit`;
  `compute_consolidation_epoch_and_update_churn` reaches the Gloas `get_consolidation_churn_limit`.
* Modified in Gloas: `compute_exit_epoch_and_update_churn` (:1495, EIP-8061) and
  `slash_validator` (:1549, which also clears the slashed proposer's `builder_pending_payments`).
* New in Gloas: `initiate_builder_exit` (:1526) and `settle_builder_payment` (:1538).

The state-free deposit helpers (`getValidatorFromDeposit` at `.gloas`, `isValidDepositSignature`)
are reused from `Deposits.lean`.
-/

namespace JauneConsensus.Gloas

open Jaune

variable {P : Preset}

/-- The zero `ExecutionAddress`. -/
def zeroAddress : ExecutionAddress := ⟨0, 0, 0⟩

/-- `BuilderPendingWithdrawal()`: every field zero. -/
def BuilderPendingWithdrawal.empty : BuilderPendingWithdrawal :=
  { fee_recipient := zeroAddress, amount := U64.zero, builder_index := U64.zero }

/-- `BuilderPendingPayment.empty()`: every field zero. -/
def BuilderPendingPayment.empty : BuilderPendingPayment :=
  { weight := U64.zero, withdrawal := BuilderPendingWithdrawal.empty, proposer_index := U64.zero }

/-! ## Balances -/

/-- `increase_balance` (phase0). -/
def increaseBalance (state : BeaconState P) (index : ValidatorIndex) (delta : Gwei) :
    M (BeaconState P) := do
  let balances ← state.balances.modify index.toNat
    (fun b => U64.add? b delta "increase_balance") "increase_balance"
  pure { state with balances }

/-- `decrease_balance` (phase0), with underflow protection. -/
def decreaseBalance (state : BeaconState P) (index : ValidatorIndex) (delta : Gwei) :
    M (BeaconState P) := do
  let balances ← state.balances.modify index.toNat
    (fun b => if b < delta then pure U64.zero else U64.sub? b delta "decrease_balance")
    "decrease_balance"
  pure { state with balances }

/-! ## Churn -/

/-- `compute_exit_epoch_and_update_churn(state, exit_balance)` (Gloas, :1495, EIP-8061): the
Electra algorithm with `per_epoch_churn = get_exit_churn_limit(state)`. Returns the state and the
exit epoch. -/
def computeExitEpochAndUpdateChurn (cfg : Config) (state : BeaconState P) (exitBalance : Gwei) :
    M (BeaconState P × Epoch) := do
  let site := "compute_exit_epoch_and_update_churn"
  let activationExit ← computeActivationExitEpoch P (← getCurrentEpoch state)
  let mut earliest := if state.earliest_exit_epoch < activationExit then activationExit
    else state.earliest_exit_epoch
  let perEpochChurn ← getExitChurnLimit cfg state
  let mut toConsume := if state.earliest_exit_epoch < earliest then perEpochChurn
    else state.exit_balance_to_consume
  if toConsume < exitBalance then
    let balanceToProcess ← exitBalance.sub? toConsume site
    let additional ← (← (← balanceToProcess.sub? U64.one site).div? perEpochChurn site).add?
      U64.one site
    earliest ← earliest.add? additional site
    toConsume ← toConsume.add? (← additional.mul? perEpochChurn site) site
  let remaining ← toConsume.sub? exitBalance site
  pure ({ state with exit_balance_to_consume := remaining, earliest_exit_epoch := earliest },
    earliest)

/-- `compute_consolidation_epoch_and_update_churn` (Electra), reaching the Gloas
`get_consolidation_churn_limit`. -/
def computeConsolidationEpochAndUpdateChurn (cfg : Config) (state : BeaconState P)
    (consolidationBalance : Gwei) : M (BeaconState P × Epoch) := do
  let site := "compute_consolidation_epoch_and_update_churn"
  let activationExit ← computeActivationExitEpoch P (← getCurrentEpoch state)
  let mut earliest := if state.earliest_consolidation_epoch < activationExit then activationExit
    else state.earliest_consolidation_epoch
  let perEpochChurn ← getConsolidationChurnLimit cfg state
  let mut toConsume := if state.earliest_consolidation_epoch < earliest then perEpochChurn
    else state.consolidation_balance_to_consume
  if toConsume < consolidationBalance then
    let balanceToProcess ← consolidationBalance.sub? toConsume site
    let additional ← (← (← balanceToProcess.sub? U64.one site).div? perEpochChurn site).add?
      U64.one site
    earliest ← earliest.add? additional site
    toConsume ← toConsume.add? (← additional.mul? perEpochChurn site) site
  let remaining ← toConsume.sub? consolidationBalance site
  pure ({ state with consolidation_balance_to_consume := remaining,
                     earliest_consolidation_epoch := earliest }, earliest)

/-! ## Exits and slashing -/

/-- `initiate_validator_exit` (Electra), reaching the Gloas `compute_exit_epoch_and_update_churn`. -/
def initiateValidatorExit (cfg : Config) (state : BeaconState P) (index : ValidatorIndex) :
    M (BeaconState P) := do
  let site := "initiate_validator_exit"
  let validator ← state.validators.get index.toNat site
  if validator.exit_epoch != FAR_FUTURE_EPOCH then return state
  let (state, exitQueueEpoch) ← computeExitEpochAndUpdateChurn cfg state validator.effective_balance
  let withdrawable ← exitQueueEpoch.add? (← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY) site
  let validators ← state.validators.set index.toNat
    { validator with exit_epoch := exitQueueEpoch, withdrawable_epoch := withdrawable } site
  pure { state with validators }

/-- `slash_validator(state, slashed_index, whistleblower_index=None)` (Gloas, :1549): Electra's
body (`MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA`, `WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA`), then
every `builder_pending_payments` entry whose `proposer_index` is the slashed validator becomes
`BuilderPendingPayment.empty()` (EIP-7732). -/
def slashValidator (cfg : Config) (state : BeaconState P) (slashedIndex : ValidatorIndex)
    (whistleblowerIndex : Option ValidatorIndex := none) : M (BeaconState P) := do
  let site := "slash_validator"
  let epoch ← getCurrentEpoch state
  let state ← initiateValidatorExit cfg state slashedIndex
  let validator ← state.validators.get slashedIndex.toNat site
  let w ← epoch.add? (← c64 P.EPOCHS_PER_SLASHINGS_VECTOR) site
  let validator := { validator with
    slashed := true
    withdrawable_epoch := if validator.withdrawable_epoch < w then w else validator.withdrawable_epoch }
  let validators ← state.validators.set slashedIndex.toNat validator site
  let si ← epoch.mod? (← c64 P.EPOCHS_PER_SLASHINGS_VECTOR) site
  let old ← state.slashings.get si.toNat site
  let slashings ← state.slashings.set si.toNat (← old.add? validator.effective_balance site) site
  let state := { state with validators, slashings }
  let penalty ← validator.effective_balance.div? (← c64 P.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA) site
  let state ← decreaseBalance state slashedIndex penalty
  -- Apply proposer and whistleblower rewards
  let proposerIndex ← getBeaconProposerIndex state
  let whistleblower := match whistleblowerIndex with
    | some w => w
    | none => proposerIndex
  let whistleblowerReward ← validator.effective_balance.div?
    (← c64 P.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA) site
  let proposerReward ← (← whistleblowerReward.mul? (← c64 PROPOSER_WEIGHT) site).div?
    (← c64 WEIGHT_DENOMINATOR) site
  let state ← increaseBalance state proposerIndex proposerReward
  let state ← increaseBalance state whistleblower (← whistleblowerReward.sub? proposerReward site)
  -- [New in Gloas:EIP7732] Remove pending builder payments for blocks proposed by the slashed
  -- validator
  let payments := state.builder_pending_payments
  pure { state with builder_pending_payments :=
    ⟨payments.toArray.map fun p =>
        if p.proposer_index == slashedIndex then BuilderPendingPayment.empty else p,
      by simpa using payments.size_eq⟩ }

/-! ## Deposits and credentials -/

/-- `add_validator_to_registry` (Electra), over the Gloas registry: every list is a
`ProgressiveList`, so `set_or_append_list` never meets a limit. -/
def addValidatorToRegistry (state : BeaconState P) (pubkey : BLSPubkey) (wc : Bytes32)
    (amount : Gwei) : M (BeaconState P) := do
  let site := "add_validator_to_registry"
  let index ← U64.ofNat? state.validators.length "get_index_for_new_validator"
  let validator ← getValidatorFromDeposit P .gloas pubkey wc amount
  let zeroFlags : ParticipationFlags := UIntN.zero
  pure { state with
    validators := ← state.validators.setOrAppend index validator site
    balances := ← state.balances.setOrAppend index amount site
    previous_epoch_participation := ← state.previous_epoch_participation.setOrAppend index zeroFlags site
    current_epoch_participation := ← state.current_epoch_participation.setOrAppend index zeroFlags site
    inactivity_scores := ← state.inactivity_scores.setOrAppend index U64.zero site }

/-- `queue_excess_active_balance` (Electra). -/
def queueExcessActiveBalance (state : BeaconState P) (index : ValidatorIndex) :
    M (BeaconState P) := do
  let site := "queue_excess_active_balance"
  let balance ← state.balances.get index.toNat site
  let minAct ← c64 P.MIN_ACTIVATION_BALANCE
  if minAct < balance then
    let excess ← balance.sub? minAct site
    let balances ← state.balances.set index.toNat minAct site
    let validator ← state.validators.get index.toNat site
    pure { state with
      balances
      pending_deposits := state.pending_deposits.push
        { pubkey := validator.pubkey
          withdrawal_credentials := validator.withdrawal_credentials
          amount := excess
          signature := g2PointAtInfinitySignature
          slot := GENESIS_SLOT } }
  else pure state

/-- `switch_to_compounding_validator` (Electra). -/
def switchToCompoundingValidator (state : BeaconState P) (index : ValidatorIndex) :
    M (BeaconState P) := do
  let site := "switch_to_compounding_validator"
  let validator ← state.validators.get index.toNat site
  let wc := Jaune.Bytes.toB256
    (COMPOUNDING_WITHDRAWAL_PREFIX :: validator.withdrawal_credentials.toBytes.drop 1)
  let validators ← state.validators.set index.toNat { validator with withdrawal_credentials := wc } site
  queueExcessActiveBalance { state with validators } index

/-! ## Builders (Gloas) -/

/-- `initiate_builder_exit(state, builder_index)` (Gloas, :1526). -/
def initiateBuilderExit (cfg : Config) (state : BeaconState P) (builderIndex : BuilderIndex) :
    M (BeaconState P) := do
  let site := "initiate_builder_exit"
  let builder ← state.builders.get builderIndex.toNat site
  let w ← (← getCurrentEpoch state).add? (← c64 cfg.MIN_BUILDER_WITHDRAWABILITY_DELAY) site
  pure { state with builders :=
    ← state.builders.set builderIndex.toNat { builder with withdrawable_epoch := w } site }

/-- `settle_builder_payment(state, payment_index)` (Gloas, :1538). -/
def settleBuilderPayment (state : BeaconState P) (paymentIndex : U64) : M (BeaconState P) := do
  let site := "settle_builder_payment"
  require (decide (paymentIndex.toNat < state.builder_pending_payments.toArray.size))
    s!"{site}: payment_index < len(state.builder_pending_payments)"
  let payment ← state.builder_pending_payments.get paymentIndex.toNat site
  let state := if U64.zero < payment.withdrawal.amount then
      { state with builder_pending_withdrawals :=
          state.builder_pending_withdrawals.push payment.withdrawal }
    else state
  pure { state with builder_pending_payments :=
    ← state.builder_pending_payments.set paymentIndex.toNat BuilderPendingPayment.empty site }

end JauneConsensus.Gloas
