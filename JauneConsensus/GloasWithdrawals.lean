import JauneConsensus.GloasEpochAccessors

/-!
# Gloas withdrawals (goal `eip8282-gloas-cross-layer-v1`, U4)

`process_withdrawals` and its phases, transcribed from `ethereum/consensus-specs`
`v1.7.0-beta.4` over `JauneConsensus.Gloas.BeaconState`:

* new in Gloas (`specs/gloas/beacon-chain.md`): `get_builder_withdrawals` (:1858),
  `get_builder_balance_after_withdrawals` (:1892), `get_builders_sweep_withdrawals` (:1909),
  `update_payload_expected_withdrawals`, `update_builder_pending_withdrawals`,
  `update_next_withdrawal_builder_index` (:2009-2035);
* modified in Gloas: `get_expected_withdrawals` (:1950, four phases and the five-field
  `ExpectedWithdrawals` dataclass), `apply_withdrawals` (:1994) and `process_withdrawals` (:2042,
  with the early return when the parent block is EMPTY);
* reused by reference: Electra's `get_pending_partial_withdrawals` and
  `get_validators_sweep_withdrawals` (`specs/electra/beacon-chain.md:1356, :1403`), Capella's
  `get_balance_after_withdrawals`, `update_next_withdrawal_index` and
  `update_next_withdrawal_validator_index`, Electra's `update_pending_partial_withdrawals`.

**Prior withdrawals.** Each phase takes the withdrawals of the phases before it
(`prior_withdrawals`) and checks its own bound against them: the builder phases assert
`len(prior) <= MAX_WITHDRAWALS_PER_PAYLOAD - 1`, the partial phase asserts
`len(prior) <= min(len(prior) + MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP,
MAX_WITHDRAWALS_PER_PAYLOAD - 1)` (`electra:1362-1366`), and the validator sweep asserts
`len(prior) < MAX_WITHDRAWALS_PER_PAYLOAD`. Each loop tests `len(prior + withdrawals) >= limit`
at the top of each iteration, as the spec does. These are transcriptions of the spec's
functions, not of the inlined Electra loops of `Block.lean` (whose "no prior withdrawals"
argument does not hold in Gloas, where the builder withdrawals come first).

Arithmetic: `WithdrawalIndex` and the processed counts are `uint64` (checked); the sums of
`Gwei` amounts are `uint64` (pyspec's `sum` starts at `0`, and `0 + Gwei` is `Gwei`).
-/

namespace JauneConsensus.Gloas

open Jaune

variable {P : Preset}

/-! ## Builder index conversion (`specs/gloas/beacon-chain.md`, "Misc") -/

/-- `convert_builder_index_to_validator_index(builder_index)`:
`ValidatorIndex(builder_index | BUILDER_INDEX_FLAG)`. Both operands are below `2^64`, so the
result is too. -/
def convertBuilderIndexToValidatorIndex (builderIndex : BuilderIndex) : M ValidatorIndex :=
  U64.ofNat? (builderIndex.toNat ||| BUILDER_INDEX_FLAG.toNat) "convert_builder_index_to_validator_index"

/-- `convert_validator_index_to_builder_index(validator_index)`:
`BuilderIndex(validator_index & ~BUILDER_INDEX_FLAG)`, where `~` is the `uint64` complement
`2^64 - 1 - BUILDER_INDEX_FLAG`. -/
def convertValidatorIndexToBuilderIndex (validatorIndex : ValidatorIndex) : M BuilderIndex :=
  U64.ofNat? (validatorIndex.toNat &&& (2 ^ 64 - 1 - BUILDER_INDEX_FLAG.toNat))
    "convert_validator_index_to_builder_index"

/-! ## The dataclass -/

/-- `ExpectedWithdrawals` (Gloas, :1001). -/
structure ExpectedWithdrawals where
  withdrawals : Array Withdrawal
  processed_builder_withdrawals_count : U64
  processed_partial_withdrawals_count : U64
  processed_builders_sweep_count : U64
  processed_sweep_withdrawals_count : U64

/-- The result of one phase: `(withdrawals, withdrawal_index, processed_count)`. -/
abbrev WithdrawalsPhase := Array Withdrawal × WithdrawalIndex × U64

/-! ## Balances after withdrawals -/

/-- `sum(w.amount for w in withdrawals if w.validator_index == index)`, typed `Gwei`. -/
def withdrawnAmount (withdrawals : Array Withdrawal) (index : ValidatorIndex) : M Gwei :=
  withdrawals.foldlM (fun acc w =>
    if w.validator_index == index then acc.add? w.amount "withdrawn" else pure acc) U64.zero

/-- `saturating_sub(a, b)` on `Gwei`. -/
def saturatingSubGwei (a b : Gwei) : M Gwei :=
  if b < a then a.sub? b "saturating_sub" else pure U64.zero

/-- `get_balance_after_withdrawals(state, validator_index, withdrawals)` (Capella): the
balance less what `withdrawals` already take from it (`uint64`, raising on underflow). -/
def getBalanceAfterWithdrawals (state : BeaconState P) (validatorIndex : ValidatorIndex)
    (withdrawals : Array Withdrawal) : M Gwei := do
  let site := "get_balance_after_withdrawals"
  (← state.balances.get validatorIndex.toNat site).sub? (← withdrawnAmount withdrawals validatorIndex)
    site

/-- `get_builder_balance_after_withdrawals(state, builder_index, withdrawals)` (Gloas, :1892). -/
def getBuilderBalanceAfterWithdrawals (state : BeaconState P) (builderIndex : BuilderIndex)
    (withdrawals : Array Withdrawal) : M Gwei := do
  let validatorIndex ← convertBuilderIndexToValidatorIndex builderIndex
  let withdrawn ← withdrawnAmount withdrawals validatorIndex
  let builder ← state.builders.get builderIndex.toNat "get_builder_balance_after_withdrawals"
  saturatingSubGwei builder.balance withdrawn

/-- `ExecutionAddress(withdrawal_credentials[12:])`. -/
def addressOfCredentials (wc : Bytes32) : M ExecutionAddress :=
  match Jaune.Bytes.toAdr? (wc.toBytes.drop 12) with
  | some a => pure a
  | none => throw (.assert "ExecutionAddress(withdrawal_credentials[12:])")

/-! ## The four phases -/

/-- `get_builder_withdrawals(state, withdrawal_index, prior_withdrawals)` (Gloas, :1858). -/
def getBuilderWithdrawals (state : BeaconState P) (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) : M WithdrawalsPhase := do
  let site := "get_builder_withdrawals"
  let withdrawalsLimit := P.MAX_WITHDRAWALS_PER_PAYLOAD - 1
  require (prior.size ≤ withdrawalsLimit) s!"{site}: len(prior_withdrawals) <= withdrawals_limit"
  let mut processed := U64.zero
  let mut withdrawals : Array Withdrawal := #[]
  let mut withdrawalIndex := withdrawalIndex
  for withdrawal in state.builder_pending_withdrawals.toArray do
    let allWithdrawals := prior ++ withdrawals
    if allWithdrawals.size ≥ withdrawalsLimit then break
    withdrawals := withdrawals.push
      { index := withdrawalIndex
        validator_index := ← convertBuilderIndexToValidatorIndex withdrawal.builder_index
        address := withdrawal.fee_recipient
        amount := withdrawal.amount }
    withdrawalIndex ← withdrawalIndex.add? U64.one site
    processed ← processed.add? U64.one site
  pure (withdrawals, withdrawalIndex, processed)

/-- `is_eligible_for_partial_withdrawals(validator, balance)` (Electra). -/
def isEligibleForPartialWithdrawals (validator : Validator) (balance : Gwei) : M Bool := do
  let minAct ← c64 P.MIN_ACTIVATION_BALANCE
  pure (validator.exit_epoch == FAR_FUTURE_EPOCH && minAct ≤ validator.effective_balance &&
    minAct < balance)

/-- `get_pending_partial_withdrawals(state, withdrawal_index, prior_withdrawals)` (Electra,
:1356), with its `len(prior_withdrawals) <= withdrawals_limit` assert (:1362-1366). -/
def getPendingPartialWithdrawals (state : BeaconState P) (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) : M WithdrawalsPhase := do
  let site := "get_pending_partial_withdrawals"
  let epoch ← getCurrentEpoch state
  let withdrawalsLimit := min (prior.size + P.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP)
    (P.MAX_WITHDRAWALS_PER_PAYLOAD - 1)
  require (prior.size ≤ withdrawalsLimit) s!"{site}: len(prior_withdrawals) <= withdrawals_limit"
  let minAct ← c64 P.MIN_ACTIVATION_BALANCE
  let mut processed := U64.zero
  let mut withdrawals : Array Withdrawal := #[]
  let mut withdrawalIndex := withdrawalIndex
  for withdrawal in state.pending_partial_withdrawals.toArray do
    let allWithdrawals := prior ++ withdrawals
    let isWithdrawable := withdrawal.withdrawable_epoch ≤ epoch
    let hasReachedLimit := allWithdrawals.size ≥ withdrawalsLimit
    if !isWithdrawable || hasReachedLimit then break
    let validatorIndex := withdrawal.validator_index
    let validator ← state.validators.get validatorIndex.toNat site
    let balance ← getBalanceAfterWithdrawals state validatorIndex allWithdrawals
    if ← isEligibleForPartialWithdrawals (P := P) validator balance then
      let excess ← balance.sub? minAct site
      withdrawals := withdrawals.push
        { index := withdrawalIndex
          validator_index := validatorIndex
          address := ← addressOfCredentials validator.withdrawal_credentials
          amount := if excess < withdrawal.amount then excess else withdrawal.amount }
      withdrawalIndex ← withdrawalIndex.add? U64.one site
    processed ← processed.add? U64.one site
  pure (withdrawals, withdrawalIndex, processed)

/-- `get_builders_sweep_withdrawals(state, withdrawal_index, prior_withdrawals)` (Gloas, :1909). -/
def getBuildersSweepWithdrawals (state : BeaconState P) (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) : M WithdrawalsPhase := do
  let site := "get_builders_sweep_withdrawals"
  let epoch ← getCurrentEpoch state
  let buildersLimit := min state.builders.length P.MAX_BUILDERS_PER_WITHDRAWALS_SWEEP
  let withdrawalsLimit := P.MAX_WITHDRAWALS_PER_PAYLOAD - 1
  require (prior.size ≤ withdrawalsLimit) s!"{site}: len(prior_withdrawals) <= withdrawals_limit"
  let mut processed := U64.zero
  let mut withdrawals : Array Withdrawal := #[]
  let mut withdrawalIndex := withdrawalIndex
  let mut builderIndex := state.next_withdrawal_builder_index
  for _ in [0:buildersLimit] do
    let allWithdrawals := prior ++ withdrawals
    if allWithdrawals.size ≥ withdrawalsLimit then break
    let builder ← state.builders.get builderIndex.toNat site
    let balance ← getBuilderBalanceAfterWithdrawals state builderIndex allWithdrawals
    if builder.withdrawable_epoch ≤ epoch && U64.zero < balance then
      withdrawals := withdrawals.push
        { index := withdrawalIndex
          validator_index := ← convertBuilderIndexToValidatorIndex builderIndex
          address := builder.execution_address
          amount := balance }
      withdrawalIndex ← withdrawalIndex.add? U64.one site
    builderIndex ← (← builderIndex.add? U64.one site).mod?
      (← U64.ofNat? state.builders.length site) site
    processed ← processed.add? U64.one site
  pure (withdrawals, withdrawalIndex, processed)

/-- `get_validators_sweep_withdrawals(state, withdrawal_index, prior_withdrawals)` (Electra,
:1403: the partial amount is `balance - get_max_effective_balance(validator)`). -/
def getValidatorsSweepWithdrawals (state : BeaconState P) (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) : M WithdrawalsPhase := do
  let site := "get_validators_sweep_withdrawals"
  let epoch ← getCurrentEpoch state
  let validatorsLimit := min state.validators.length P.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP
  let withdrawalsLimit := P.MAX_WITHDRAWALS_PER_PAYLOAD
  -- There must be at least one space reserved for validator sweep withdrawals
  require (prior.size < withdrawalsLimit) s!"{site}: len(prior_withdrawals) < withdrawals_limit"
  let mut processed := U64.zero
  let mut withdrawals : Array Withdrawal := #[]
  let mut withdrawalIndex := withdrawalIndex
  let mut validatorIndex := state.next_withdrawal_validator_index
  for _ in [0:validatorsLimit] do
    let allWithdrawals := prior ++ withdrawals
    if allWithdrawals.size ≥ withdrawalsLimit then break
    let validator ← state.validators.get validatorIndex.toNat site
    let balance ← getBalanceAfterWithdrawals state validatorIndex allWithdrawals
    if isFullyWithdrawableValidator .gloas validator balance epoch then
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validator_index := validatorIndex
          address := ← addressOfCredentials validator.withdrawal_credentials, amount := balance }
      withdrawalIndex ← withdrawalIndex.add? U64.one site
    else if isPartiallyWithdrawableValidator P .gloas validator balance then
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validator_index := validatorIndex
          address := ← addressOfCredentials validator.withdrawal_credentials
          amount := ← balance.sub? (← c64 (getMaxEffectiveBalance P validator)) site }
      withdrawalIndex ← withdrawalIndex.add? U64.one site
    validatorIndex ← (← validatorIndex.add? U64.one site).mod?
      (← U64.ofNat? state.validators.length site) site
    processed ← processed.add? U64.one site
  pure (withdrawals, withdrawalIndex, processed)

/-- `get_expected_withdrawals(state)` (Gloas, :1950): builder withdrawals, pending partial
withdrawals, the builders sweep and the validators sweep, each phase given the withdrawals of
the phases before it. -/
def getExpectedWithdrawals (state : BeaconState P) : M ExpectedWithdrawals := do
  let withdrawalIndex := state.next_withdrawal_index
  let withdrawals : Array Withdrawal := #[]
  -- [New in Gloas:EIP7732] Get builder withdrawals
  let (builderWithdrawals, withdrawalIndex, processedBuilderWithdrawals) ←
    getBuilderWithdrawals state withdrawalIndex withdrawals
  let withdrawals := withdrawals ++ builderWithdrawals
  -- Get partial withdrawals
  let (partialWithdrawals, withdrawalIndex, processedPartialWithdrawals) ←
    getPendingPartialWithdrawals state withdrawalIndex withdrawals
  let withdrawals := withdrawals ++ partialWithdrawals
  -- [New in Gloas:EIP7732] Get builders sweep withdrawals
  let (buildersSweepWithdrawals, withdrawalIndex, processedBuildersSweep) ←
    getBuildersSweepWithdrawals state withdrawalIndex withdrawals
  let withdrawals := withdrawals ++ buildersSweepWithdrawals
  -- Get validators sweep withdrawals
  let (validatorsSweepWithdrawals, _, processedValidatorsSweep) ←
    getValidatorsSweepWithdrawals state withdrawalIndex withdrawals
  let withdrawals := withdrawals ++ validatorsSweepWithdrawals
  pure { withdrawals
         processed_builder_withdrawals_count := processedBuilderWithdrawals
         processed_partial_withdrawals_count := processedPartialWithdrawals
         processed_builders_sweep_count := processedBuildersSweep
         processed_sweep_withdrawals_count := processedValidatorsSweep }

/-! ## Applying and updating -/

/-- `apply_withdrawals(state, withdrawals)` (Gloas, :1994): a builder withdrawal debits the
builder's balance (saturating), any other the validator's (`decrease_balance`). -/
def applyWithdrawals (state : BeaconState P) (withdrawals : Array Withdrawal) :
    M (BeaconState P) := do
  let site := "apply_withdrawals"
  let mut state := state
  for withdrawal in withdrawals do
    if isBuilderIndex withdrawal.validator_index then
      let builderIndex ← convertValidatorIndexToBuilderIndex withdrawal.validator_index
      let builders ← state.builders.modify builderIndex.toNat (fun b => do
        pure { b with balance := ← saturatingSubGwei b.balance withdrawal.amount }) site
      state := { state with builders }
    else
      state ← decreaseBalance state withdrawal.validator_index withdrawal.amount
  pure state

/-- `update_next_withdrawal_index(state, withdrawals)` (Capella). -/
def updateNextWithdrawalIndex (state : BeaconState P) (withdrawals : Array Withdrawal) :
    M (BeaconState P) := do
  match withdrawals.back? with
  | none => pure state
  | some latest =>
    pure { state with next_withdrawal_index := ← latest.index.add? U64.one "update_next_withdrawal_index" }

/-- `update_payload_expected_withdrawals(state, withdrawals)` (Gloas). -/
def updatePayloadExpectedWithdrawals (state : BeaconState P) (withdrawals : Array Withdrawal) :
    BeaconState P :=
  { state with payload_expected_withdrawals := ProgressiveListS.ofArray withdrawals }

/-- `update_builder_pending_withdrawals(state, processed_builder_withdrawals_count)` (Gloas):
the slice `[processed:]`. -/
def updateBuilderPendingWithdrawals (state : BeaconState P) (processed : U64) : BeaconState P :=
  let xs := state.builder_pending_withdrawals.toArray
  { state with builder_pending_withdrawals :=
      ProgressiveListS.ofArray (xs.extract processed.toNat xs.size) }

/-- `update_pending_partial_withdrawals(state, processed_partial_withdrawals_count)` (Electra):
the slice `[processed:]`. -/
def updatePendingPartialWithdrawals (state : BeaconState P) (processed : U64) : BeaconState P :=
  let xs := state.pending_partial_withdrawals.toArray
  { state with pending_partial_withdrawals :=
      ProgressiveListS.ofArray (xs.extract processed.toNat xs.size) }

/-- `update_next_withdrawal_builder_index(state, processed_builders_sweep_count)` (Gloas). -/
def updateNextWithdrawalBuilderIndex (state : BeaconState P) (processed : U64) :
    M (BeaconState P) := do
  let site := "update_next_withdrawal_builder_index"
  if 0 < state.builders.length then
    -- Update the next builder index to start the next withdrawal sweep
    let nextIndex ← state.next_withdrawal_builder_index.add? processed site
    let next ← nextIndex.mod? (← U64.ofNat? state.builders.length site) site
    pure { state with next_withdrawal_builder_index := next }
  else pure state

/-- `update_next_withdrawal_validator_index(state, withdrawals)` (Capella). -/
def updateNextWithdrawalValidatorIndex (state : BeaconState P) (withdrawals : Array Withdrawal) :
    M (BeaconState P) := do
  let site := "update_next_withdrawal_validator_index"
  let n ← U64.ofNat? state.validators.length site
  match withdrawals.back? with
  | some latest =>
    if withdrawals.size == P.MAX_WITHDRAWALS_PER_PAYLOAD then
      -- Next sweep starts after the latest withdrawal's validator index
      let next ← (← latest.validator_index.add? U64.one site).mod? n site
      return { state with next_withdrawal_validator_index := next }
  | none => pure ()
  -- Advance sweep by the max length of the sweep if there was not a full set of withdrawals
  let nextIndex ← state.next_withdrawal_validator_index.add?
    (← c64 P.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP) site
  pure { state with next_withdrawal_validator_index := ← nextIndex.mod? n site }

/-- `process_withdrawals(state)` (Gloas, :2042): nothing when the parent block is EMPTY
(`state.latest_block_hash != state.latest_execution_payload_bid.block_hash`); otherwise the
expected withdrawals are applied and the six update steps run in the spec's order. -/
def processWithdrawals (state : BeaconState P) : M (BeaconState P) := do
  -- [New in Gloas:EIP7732] Return early if the parent block is empty
  if state.latest_block_hash != state.latest_execution_payload_bid.block_hash then
    return state
  let expected ← getExpectedWithdrawals state
  let state ← applyWithdrawals state expected.withdrawals
  let state ← updateNextWithdrawalIndex state expected.withdrawals
  let state := updatePayloadExpectedWithdrawals state expected.withdrawals
  let state := updateBuilderPendingWithdrawals state expected.processed_builder_withdrawals_count
  let state := updatePendingPartialWithdrawals state expected.processed_partial_withdrawals_count
  let state ← updateNextWithdrawalBuilderIndex state expected.processed_builders_sweep_count
  updateNextWithdrawalValidatorIndex state expected.withdrawals

end JauneConsensus.Gloas
