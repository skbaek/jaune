import JauneConsensus.Deposits
import JauneConsensus.EpochAccessors
import JauneConsensus.Upgrade

/-!
# Block processing: header, RANDAO, eth1 data and the operations (Electra and Fulu)

Transcribed from `ethereum/consensus-specs` `v1.6.1`: `process_block_header`, `process_randao`,
`process_eth1_data` (phase0), `process_operations` and its operations (phase0 to Electra, latest
versions), `process_withdrawals` and `get_expected_withdrawals` (Electra),
`process_execution_payload` (Fulu, with Electra's blob limit before Fulu) and
`process_sync_aggregate` (Altair). Each definition cites its pyspec function and keeps its
statement order; every `assert` is `require` (a `Reject.assert`).

These are the Electra and Fulu versions; they read Electra state fields through the gated
accessors, so applied to a Deneb state they reject (the Deneb block functions are the transition
stream's).

The context `Ctx` carries the configuration and the two switches pyspec's test harness sets:
`blsActive` (pyspec's `bls.bls_active`: when off, only the verification predicates are switched,
to `True`) and `executionValid` (the mocked execution engine's verdict, `execution.yaml`).
-/

namespace JauneConsensus
open Jaune (Bytes B256)

/-! ## Constants -/

-- `PARTICIPATION_FLAG_WEIGHTS`, the `TIMELY_*_FLAG_INDEX` values and `SYNC_REWARD_WEIGHT` are in
-- `Accessors.lean` (shared with epoch processing).
/-- `FULL_EXIT_REQUEST_AMOUNT = uint64(0)` (Electra). -/
def FULL_EXIT_REQUEST_AMOUNT : U64 := U64.zero

variable {P : Preset} {f : CFork}

/-- The bytes of a fixed-length byte vector. -/
private def vbytes {n : Nat} (v : SszVector UInt8 n) : Bytes := v.toArray.toList

/-! ## Header, RANDAO, eth1 data -/

/-- `process_block_header` (phase0). -/
def processBlockHeader (state : BeaconState P f) (block : BeaconBlock P f) :
    M (BeaconState P f) := do
  require (block.slot == state.slot) "process_block_header: block.slot == state.slot"
  require (state.latest_block_header.slot < block.slot) "process_block_header: newer block"
  require (block.proposer_index == (← getBeaconProposerIndex state))
    "process_block_header: proposer index"
  require (block.parent_root == hashTreeRoot state.latest_block_header)
    "process_block_header: parent root"
  let state := { state with latest_block_header :=
    { slot := block.slot, proposer_index := block.proposer_index, parent_root := block.parent_root,
      state_root := Jaune.Bytes.toB256 (List.replicate 32 0), body_root := hashTreeRoot block.body } }
  let proposer ← state.validators.get block.proposer_index.toNat "process_block_header"
  require (!proposer.slashed) "process_block_header: proposer not slashed"
  pure state

/-- `process_randao` (phase0). -/
def processRandao (ctx : Ctx) (state : BeaconState P f) (body : BeaconBlockBody P f) :
    M (BeaconState P f) := do
  let epoch ← getCurrentEpoch state
  let proposer ← state.validators.get (← getBeaconProposerIndex state).toNat "process_randao"
  let root := computeSigningRoot epoch (← getDomain state DOMAIN_RANDAO (some epoch))
  require (blsVerify ctx.blsActive proposer.pubkey root body.randao_reveal)
    "process_randao: bls.Verify"
  let mix := xor (← getRandaoMix state epoch) (hash (vbytes body.randao_reveal))
  let i ← U64.mod? epoch (← c64 P.EPOCHS_PER_HISTORICAL_VECTOR) "process_randao"
  pure { state with randao_mixes := ← state.randao_mixes.set i.toNat mix "process_randao" }

/-- `process_eth1_data` (phase0). -/
def processEth1Data (state : BeaconState P f) (body : BeaconBlockBody P f) :
    M (BeaconState P f) := do
  let votes ← state.eth1_data_votes.push body.eth1_data "process_eth1_data"
  let state := { state with eth1_data_votes := votes }
  let count := (votes.toArray.filter (· == body.eth1_data)).size
  if count * 2 > P.EPOCHS_PER_ETH1_VOTING_PERIOD * P.SLOTS_PER_EPOCH then
    pure { state with eth1_data := body.eth1_data }
  else pure state

/-! ## Rewards helpers (Altair) -/

-- `get_base_reward_per_increment` and `get_base_reward` are in `EpochAccessors.lean`.

/-! ## Slashings -/

/-- `is_valid_indexed_attestation` (phase0). -/
def isValidIndexedAttestation (ctx : Ctx) (state : BeaconState P f)
    (ia : IndexedAttestation P f) : M Bool := do
  let indices := ia.attesting_indices.toArray
  let sortedUnique := (indices.qsort (· < ·)).toList.eraseDups.toArray
  if indices.size == 0 || !(indices == sortedUnique) then return false
  let mut pubkeys := #[]
  for i in indices do
    pubkeys := pubkeys.push (← state.validators.get i.toNat "is_valid_indexed_attestation").pubkey
  let root := computeSigningRoot ia.data (← getDomain state DOMAIN_BEACON_ATTESTER (some ia.data.target.epoch))
  pure (blsFastAggregateVerify ctx.blsActive pubkeys.toList root ia.signature)

/-- `process_proposer_slashing` (phase0). -/
def processProposerSlashing (ctx : Ctx) (state : BeaconState P f) (ps : ProposerSlashing) :
    M (BeaconState P f) := do
  let h1 := ps.signed_header_1.message
  let h2 := ps.signed_header_2.message
  require (h1.slot == h2.slot) "process_proposer_slashing: slots match"
  require (h1.proposer_index == h2.proposer_index) "process_proposer_slashing: proposers match"
  require (!(h1 == h2)) "process_proposer_slashing: headers differ"
  let proposer ← state.validators.get h1.proposer_index.toNat "process_proposer_slashing"
  require (isSlashableValidator proposer (← getCurrentEpoch state))
    "process_proposer_slashing: slashable"
  for sh in [ps.signed_header_1, ps.signed_header_2] do
    let domain ← getDomain state DOMAIN_BEACON_PROPOSER (some (← computeEpochAtSlot P sh.message.slot))
    let root := computeSigningRoot sh.message domain
    require (blsVerify ctx.blsActive proposer.pubkey root sh.signature)
      "process_proposer_slashing: bls.Verify"
  slashValidator ctx.cfg state h1.proposer_index

/-- `process_attester_slashing` (phase0). -/
def processAttesterSlashing (ctx : Ctx) (state : BeaconState P f) (as : AttesterSlashing P f) :
    M (BeaconState P f) := do
  let a1 := as.attestation_1
  let a2 := as.attestation_2
  require (isSlashableAttestationData a1.data a2.data) "process_attester_slashing: slashable data"
  require (← isValidIndexedAttestation ctx state a1) "process_attester_slashing: attestation_1"
  require (← isValidIndexedAttestation ctx state a2) "process_attester_slashing: attestation_2"
  let s2 := a2.attesting_indices.toArray
  let indices := ((a1.attesting_indices.toArray.filter (s2.contains ·)).qsort (· < ·)).toList.eraseDups
  let mut state := state
  let mut slashedAny := false
  for index in indices do
    let v ← state.validators.get index.toNat "process_attester_slashing"
    if isSlashableValidator v (← getCurrentEpoch state) then
      state ← slashValidator ctx.cfg state index
      slashedAny := true
  require slashedAny "process_attester_slashing: slashed_any"
  pure state

/-! ## Attestations -/

/-- `get_attestation_participation_flag_indices` (Deneb, EIP-7045). -/
def getAttestationParticipationFlagIndices (state : BeaconState P f) (data : AttestationData)
    (inclusionDelay : U64) : M (List Nat) := do
  let current ← getCurrentEpoch state
  let justified := if data.target.epoch == current then state.current_justified_checkpoint
    else state.previous_justified_checkpoint
  let isMatchingSource := data.source == justified
  let targetRoot ← getBlockRoot state data.target.epoch
  let isMatchingTarget := isMatchingSource && data.target.root == targetRoot
  let headRoot ← getBlockRootAtSlot state data.slot
  let isMatchingHead := isMatchingTarget && data.beacon_block_root == headRoot
  require isMatchingSource "get_attestation_participation_flag_indices: matching source"
  let mut out := []
  if isMatchingSource then
    if inclusionDelay ≤ (← integerSquareroot (← c64 P.SLOTS_PER_EPOCH)) then
      out := out ++ [TIMELY_SOURCE_FLAG_INDEX]
  if isMatchingTarget then out := out ++ [TIMELY_TARGET_FLAG_INDEX]
  if isMatchingHead && inclusionDelay.toNat == P.MIN_ATTESTATION_INCLUSION_DELAY then
    out := out ++ [TIMELY_HEAD_FLAG_INDEX]
  pure out

/-- `process_attestation` (Electra, EIP-7549; the Deneb version, `specs/deneb/beacon-chain.md`,
names one committee by `data.index`). -/
def processAttestation (ctx : Ctx) (state : BeaconState P f) (attestation : Attestation P f) :
    M (BeaconState P f) := do
  let site := "process_attestation"
  let data := attestation.data
  let current ← getCurrentEpoch state
  let previous ← getPreviousEpoch state
  require (data.target.epoch == previous || data.target.epoch == current) s!"{site}: target epoch"
  require (data.target.epoch == (← computeEpochAtSlot P data.slot)) s!"{site}: target epoch of slot"
  require ((← U64.add? data.slot (← c64 P.MIN_ATTESTATION_INCLUSION_DELAY) site) ≤ state.slot)
    s!"{site}: inclusion delay"
  let bits := attestation.aggregation_bits.bits
  if f.atLeast .electra then
    require (data.index == U64.zero) s!"{site}: data.index == 0"
    let cbits ← Gated.read attestation.committee_bits site
    let mut offset := 0
    for ci in ← getCommitteeIndices cbits do
      require (ci < (← getCommitteeCountPerSlot state data.target.epoch)) s!"{site}: committee index"
      let committee ← getBeaconCommittee state data.slot ci
      let mut attesters := 0
      for i in [0:committee.size] do
        if ← getAt bits (offset + i) "aggregation_bits" then attesters := attesters + 1
      require (attesters > 0) s!"{site}: committee attesters"
      offset := offset + committee.size
    require (bits.size == offset) s!"{site}: bitfield length"
  else
    -- Deneb (`specs/deneb/beacon-chain.md`): one committee, `data.index`.
    require (data.index < (← getCommitteeCountPerSlot state data.target.epoch)) s!"{site}: committee index"
    let committee ← getBeaconCommittee state data.slot data.index
    require (bits.size == committee.size) s!"{site}: bitfield length"
  let flags ← getAttestationParticipationFlagIndices state data
    (← U64.sub? state.slot data.slot site)
  require (← isValidIndexedAttestation ctx state (← getIndexedAttestation state attestation))
    s!"{site}: indexed attestation"
  let isCurrent := data.target.epoch == current
  let mut participation :=
    if isCurrent then state.current_epoch_participation else state.previous_epoch_participation
  -- `proposer_reward_numerator = 0` is a Python `int`, but `0 + Gwei` is `uint64`
  -- (remerkleable's `__radd__`), so the accumulation and each `get_base_reward * weight`
  -- (`uint64 * uint64`) raise on overflow
  let mut numerator := U64.zero
  for index in ← getAttestingIndices state attestation do
    for (flagIndex, weight) in (List.range PARTICIPATION_FLAG_WEIGHTS.length).zip PARTICIPATION_FLAG_WEIGHTS do
      -- `flag_index in participation_flag_indices and not has_flag(epoch_participation[index], ...)`
      -- short-circuits: the participation read happens only for a listed flag
      if flags.contains flagIndex then
        let cur ← participation.get index.toNat site
        if !(← hasFlag cur flagIndex) then
          participation ← participation.set index.toNat (← addFlag cur flagIndex) site
          numerator ← U64.add? numerator
            (← U64.mul? (← getBaseReward state index) (← c64 weight) site) site
  let state := if isCurrent then { state with current_epoch_participation := participation }
    else { state with previous_epoch_participation := participation }
  let denominator ← U64.div? (← U64.mul? (← c64 (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))
    (← c64 WEIGHT_DENOMINATOR) site) (← c64 PROPOSER_WEIGHT) site
  let reward ← U64.div? numerator denominator s!"{site}: Gwei(proposer_reward)"
  increaseBalance state (← getBeaconProposerIndex state) reward

/-! ## Deposits -/

/-- The index of the validator with `pubkey`, if any (`validator_pubkeys.index(pubkey)`). -/
def validatorIndexOf (state : BeaconState P f) (pubkey : BLSPubkey) : M (Option ValidatorIndex) := do
  match state.validators.toArray.findIdx? (·.pubkey == pubkey) with
  | some i => pure (some (← U64.ofNat? i "ValidatorIndex"))
  | none => pure none

/-- `apply_deposit` (Electra: queue a pending deposit; phase0 to Deneb: credit the balance). -/
def applyDeposit (ctx : Ctx) (state : BeaconState P f) (pubkey : BLSPubkey) (wc : Bytes32)
    (amount : U64) (signature : BLSSignature) : M (BeaconState P f) := do
  let mut state := state
  if !(f.atLeast .electra) then
    -- phase0/Altair (`specs/phase0/beacon-chain.md`): credit the balance directly.
    match ← validatorIndexOf state pubkey with
    | none =>
      if ← isValidDepositSignature ctx pubkey wc amount signature then
        return (← addValidatorToRegistry state pubkey wc amount)
      else return state
    | some index => return (← increaseBalance state index amount)
  if !(state.validators.toArray.any (·.pubkey == pubkey)) then
    if ← isValidDepositSignature ctx pubkey wc amount signature then
      state ← addValidatorToRegistry state pubkey wc U64.zero
    else return state
  let pending ← (← state.pendingDeposits).push
    { pubkey, withdrawal_credentials := wc, amount, signature, slot := GENESIS_SLOT } "apply_deposit"
  state.setPendingDeposits pending

/-- `process_deposit` (Electra). -/
def processDeposit (ctx : Ctx) (state : BeaconState P f) (deposit : Deposit) :
    M (BeaconState P f) := do
  let ok ← isValidMerkleBranch (hashTreeRoot deposit.data) deposit.proof.toArray.toList
    (← c64 (DEPOSIT_CONTRACT_TREE_DEPTH + 1)) state.eth1_deposit_index state.eth1_data.deposit_root
  require ok "process_deposit: merkle branch"
  let state := { state with
    eth1_deposit_index := ← U64.add? state.eth1_deposit_index U64.one "process_deposit" }
  applyDeposit ctx state deposit.data.pubkey deposit.data.withdrawal_credentials
    deposit.data.amount deposit.data.signature

/-! ## Exits and credential changes -/

/-- `process_voluntary_exit` (Electra; Deneb lacks the pending-withdrawal check; both use the
EIP-7044 domain of `CAPELLA_FORK_VERSION`). -/
def processVoluntaryExit (ctx : Ctx) (state : BeaconState P f) (sve : SignedVoluntaryExit) :
    M (BeaconState P f) := do
  let site := "process_voluntary_exit"
  let ve := sve.message
  let validator ← state.validators.get ve.validator_index.toNat site
  let current ← getCurrentEpoch state
  require (isActiveValidator validator current) s!"{site}: active"
  require (validator.exit_epoch == FAR_FUTURE_EPOCH) s!"{site}: not exiting"
  require (ve.epoch ≤ current) s!"{site}: epoch"
  require ((← U64.add? validator.activation_epoch (← c64 ctx.cfg.SHARD_COMMITTEE_PERIOD) site) ≤ current)
    s!"{site}: active long enough"
  if f.atLeast .electra then
    require ((← getPendingBalanceToWithdraw state ve.validator_index) == U64.zero)
      s!"{site}: no pending withdrawals"
  let domain ← pure <| computeDomain DOMAIN_VOLUNTARY_EXIT (← versionOf ctx.cfg.CAPELLA_FORK_VERSION)
    state.genesis_validators_root
  let root := computeSigningRoot ve domain
  require (blsVerify ctx.blsActive validator.pubkey root sve.signature)
    s!"{site}: bls.Verify"
  initiateValidatorExit ctx.cfg state ve.validator_index

/-- `process_bls_to_execution_change` (Capella). -/
def processBlsToExecutionChange (ctx : Ctx) (state : BeaconState P f)
    (sac : SignedBLSToExecutionChange) : M (BeaconState P f) := do
  let site := "process_bls_to_execution_change"
  let ac := sac.message
  require (ac.validator_index.toNat < state.validators.length) s!"{site}: index"
  let validator ← state.validators.get ac.validator_index.toNat site
  let wc := validator.withdrawal_credentials.toBytes
  require (wc.take 1 == [BLS_WITHDRAWAL_PREFIX]) s!"{site}: BLS prefix"
  require (wc.drop 1 == (hashBytes (vbytes ac.from_bls_pubkey)).drop 1) s!"{site}: pubkey hash"
  let domain ← pure <| computeDomain DOMAIN_BLS_TO_EXECUTION_CHANGE (← versionOf ctx.cfg.GENESIS_FORK_VERSION)
    state.genesis_validators_root
  let root := computeSigningRoot ac domain
  require (blsVerify ctx.blsActive ac.from_bls_pubkey root sac.signature)
    s!"{site}: bls.Verify"
  let newWc := Jaune.Bytes.toB256 (ETH1_ADDRESS_WITHDRAWAL_PREFIX :: List.replicate 11 0 ++
    ac.to_execution_address.toBytes)
  let validators ← state.validators.set ac.validator_index.toNat
    { validator with withdrawal_credentials := newWc } site
  pure { state with validators }

/-! ## Withdrawals -/

/-- `ExecutionAddress(validator.withdrawal_credentials[12:])`. -/
def withdrawalAddress (v : Validator) : M ExecutionAddress :=
  match Jaune.Bytes.toAdr? (v.withdrawal_credentials.toBytes.drop 12) with
  | some a => pure a
  | none => throw (.assert "withdrawal address")

/-- The `sum(w.amount for w in withdrawals if w.validator_index == index)` of typed `Gwei`. -/
private def withdrawnFor (ws : Array Withdrawal) (index : ValidatorIndex) : M Gwei :=
  ws.foldlM (fun acc w => if w.validator_index == index then U64.add? acc w.amount "total_withdrawn"
    else pure acc) U64.zero

/-- `get_expected_withdrawals` (Electra): the withdrawals and the number of processed pending
partial withdrawals. Before Electra (`specs/capella/beacon-chain.md`) there is no pending queue
and the partial amount is `balance - MAX_EFFECTIVE_BALANCE`. -/
def getExpectedWithdrawals (state : BeaconState P f) : M (Array Withdrawal × Nat) := do
  let site := "get_expected_withdrawals"
  let epoch ← getCurrentEpoch state
  let mut withdrawalIndex := state.next_withdrawal_index
  let mut validatorIndex := state.next_withdrawal_validator_index
  let mut withdrawals : Array Withdrawal := #[]
  let mut processed := 0
  let minAct ← c64 P.MIN_ACTIVATION_BALANCE
  -- (a nested `←` inside a term-level `if` would run before the `if`, reading the Electra
  -- field at every fork; the `do` keeps the read inside the Electra branch)
  let pendingPartials ← if f.atLeast .electra then do
      pure (← state.pendingPartialWithdrawals).toArray
    else pure #[]  -- Capella to Deneb: no pending partial withdrawals
  for w in pendingPartials do
    if epoch < w.withdrawable_epoch || withdrawals.size == P.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP then
      break
    let validator ← state.validators.get w.validator_index.toNat site
    let sufficient := minAct ≤ validator.effective_balance
    let balance ← U64.sub? (← state.balances.get w.validator_index.toNat site)
      (← withdrawnFor withdrawals w.validator_index) site
    let excess := minAct < balance
    if validator.exit_epoch == FAR_FUTURE_EPOCH && sufficient && excess then
      let avail ← U64.sub? balance minAct site
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validator_index := w.validator_index,
          address := ← withdrawalAddress validator,
          amount := if avail < w.amount then avail else w.amount }
      withdrawalIndex ← U64.add? withdrawalIndex U64.one site
    processed := processed + 1
  let n := state.validators.length
  let bound := min n P.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP
  for _ in [0:bound] do
    let validator ← state.validators.get validatorIndex.toNat site
    let balance ← U64.sub? (← state.balances.get validatorIndex.toNat site)
      (← withdrawnFor withdrawals validatorIndex) site
    if isFullyWithdrawableValidator f validator balance epoch then
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validator_index := validatorIndex,
          address := ← withdrawalAddress validator, amount := balance }
      withdrawalIndex ← U64.add? withdrawalIndex U64.one site
    else if isPartiallyWithdrawableValidator P f validator balance then
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validator_index := validatorIndex,
          address := ← withdrawalAddress validator,
          amount := ← U64.sub? balance (← c64 (if f.atLeast .electra then
            getMaxEffectiveBalance P validator else P.MAX_EFFECTIVE_BALANCE)) site }
      withdrawalIndex ← U64.add? withdrawalIndex U64.one site
    if withdrawals.size == P.MAX_WITHDRAWALS_PER_PAYLOAD then break
    validatorIndex ← U64.mod? (← U64.add? validatorIndex U64.one site) (← U64.ofNat? n site) site
  pure (withdrawals, processed)

/-- `process_withdrawals` (Electra; Capella to Deneb have no pending-queue update). -/
def processWithdrawals (state : BeaconState P f) (payload : ExecutionPayload P) :
    M (BeaconState P f) := do
  let site := "process_withdrawals"
  let (expected, processed) ← getExpectedWithdrawals state
  require (payload.withdrawals.toArray == expected) s!"{site}: payload withdrawals"
  let mut state := state
  for w in expected do
    state ← decreaseBalance state w.validator_index w.amount
  if f.atLeast .electra then
    let pending ← state.pendingPartialWithdrawals
    state ← state.setPendingPartialWithdrawals (← SszList.ofArray (pending.toArray.extract processed pending.length) site)
  if h : 0 < expected.size then
    let latest := expected[expected.size - 1]
    state := { state with next_withdrawal_index := ← U64.add? latest.index U64.one site }
    if expected.size == P.MAX_WITHDRAWALS_PER_PAYLOAD then
      let next ← U64.mod? (← U64.add? latest.validator_index U64.one site)
        (← U64.ofNat? state.validators.length site) site
      return { state with next_withdrawal_validator_index := next }
  let nextIndex ← U64.add? state.next_withdrawal_validator_index
    (← c64 P.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP) site
  let next ← U64.mod? nextIndex (← U64.ofNat? state.validators.length site) site
  pure { state with next_withdrawal_validator_index := next }

/-! ## Execution payload -/

/-- `compute_time_at_slot` (phase0). -/
def computeTimeAtSlot (cfg : Config) (state : BeaconState P f) (slot : Slot) : M U64 := do
  let since ← U64.sub? slot GENESIS_SLOT "compute_time_at_slot"
  U64.add? state.genesis_time (← U64.mul? since (← c64 cfg.SECONDS_PER_SLOT) "compute_time_at_slot")
    "compute_time_at_slot"

/-- `process_execution_payload` (Fulu: the blob limit is `get_blob_parameters(epoch)`;
Electra: `MAX_BLOBS_PER_BLOCK_ELECTRA`; Deneb: `MAX_BLOBS_PER_BLOCK`). The engine's verdict is `ctx.executionValid`. -/
def processExecutionPayload (ctx : Ctx) (state : BeaconState P f) (body : BeaconBlockBody P f) :
    M (BeaconState P f) := do
  let site := "process_execution_payload"
  let payload := body.execution_payload
  require (payload.parent_hash == state.latest_execution_payload_header.block_hash) s!"{site}: parent hash"
  let epoch ← getCurrentEpoch state
  require (payload.prev_randao == (← getRandaoMix state epoch)) s!"{site}: prev_randao"
  require (payload.timestamp == (← computeTimeAtSlot ctx.cfg state state.slot)) s!"{site}: timestamp"
  let maxBlobs ←
    if f.atLeast .fulu then do pure (← getBlobParameters ctx.cfg epoch).maxBlobsPerBlock.toNat
    -- configuration values are `uint64` in pyspec, as `get_blob_parameters` reads them
    else if f.atLeast .electra then do pure (← c64 ctx.cfg.MAX_BLOBS_PER_BLOCK_ELECTRA).toNat
    else do pure (← c64 ctx.cfg.MAX_BLOBS_PER_BLOCK).toNat
  require (body.blob_kzg_commitments.length ≤ maxBlobs) s!"{site}: blob commitments"
  require ctx.executionValid s!"{site}: execution engine"
  pure { state with latest_execution_payload_header :=
    { parent_hash := payload.parent_hash, fee_recipient := payload.fee_recipient,
      state_root := payload.state_root, receipts_root := payload.receipts_root,
      logs_bloom := payload.logs_bloom, prev_randao := payload.prev_randao,
      block_number := payload.block_number, gas_limit := payload.gas_limit,
      gas_used := payload.gas_used, timestamp := payload.timestamp,
      extra_data := payload.extra_data, base_fee_per_gas := payload.base_fee_per_gas,
      block_hash := payload.block_hash, transactions_root := hashTreeRoot payload.transactions,
      withdrawals_root := hashTreeRoot payload.withdrawals, blob_gas_used := payload.blob_gas_used,
      excess_blob_gas := payload.excess_blob_gas } }

/-! ## Sync aggregate -/

/-- `process_sync_aggregate` (Altair). The participant key is computed only when the signature
is verified (`bls_active`); a key that does not decode fails the verification. -/
def processSyncAggregate (ctx : Ctx) (state : BeaconState P f) (sa : SyncAggregate P) :
    M (BeaconState P f) := do
  let site := "process_sync_aggregate"
  let pubkeys := state.current_sync_committee.pubkeys.toArray
  let bits := sa.sync_committee_bits.bits
  let participants := (bits.filter id).size
  -- the participant keys first, as in the specification (its optimized form, from `v1.6.0`)
  let participantPubkeys : List Bytes ←
    if participants == P.SYNC_COMMITTEE_SIZE then
      -- All members participated - use precomputed aggregate key
      pure [vbytes state.current_sync_committee.aggregate_pubkey]
    else if participants > P.SYNC_COMMITTEE_SIZE / 2 then do
      -- More than half participated - subtract non-participant keys
      -- No KeyValidate on the stored aggregate: pyspec raw-decodes both points here (specs/altair/beacon-chain.md:592-596); validation lives in `eth_aggregate_pubkeys` (specs/altair/bls.md:47).
      let nonPart := ((pubkeys.zip bits).filter (fun (_, b) => !b)).toList.map (vbytes ·.1)
      -- `eth_aggregate_pubkeys` is `bls.AggregatePKs`, which pyspec's BLS switch stubs to
      -- `STUB_PUBKEY` (`eth2spec/utils/bls.py`); the point decoding, negation and addition
      -- that follow are not switched
      let nonAgg ← if ctx.blsActive then ethAggregatePubkeysM nonPart else pure STUB_PUBKEY
      let full ← liftCrypto s!"{site}: bls.bytes48_to_G1(aggregate_pubkey)"
        (pubkeyToPoint (vbytes state.current_sync_committee.aggregate_pubkey))
      let nonP ← liftCrypto s!"{site}: bls.bytes48_to_G1(non_participant_aggregate)"
        (pubkeyToPoint nonAgg)
      pure [g1Compress (full + -nonP)]
    else
      -- Less than half participated - aggregate participant keys
      pure (((pubkeys.zip bits).filter (·.2)).toList.map (vbytes ·.1))
  let prevSlot ← U64.sub? (if U64.one < state.slot then state.slot else U64.one) U64.one site
  let domain ← getDomain state DOMAIN_SYNC_COMMITTEE (some (← computeEpochAtSlot P prevSlot))
  let root := computeSigningRoot (← getBlockRootAtSlot state prevSlot) domain
  -- under the switch, `eth_fast_aggregate_verify` is `True` (its empty-key check, then the
  -- stubbed `FastAggregateVerify`)
  let verified := !ctx.blsActive ||
    ethFastAggregateVerify participantPubkeys root.toBytes (vbytes sa.sync_committee_signature)
  require verified s!"{site}: eth_fast_aggregate_verify"
  let totalActiveIncrements ← U64.div? (← getTotalActiveBalance state)
    (← c64 P.EFFECTIVE_BALANCE_INCREMENT) site
  let totalBaseRewards ← U64.mul? (← getBaseRewardPerIncrement state) totalActiveIncrements site
  let maxParticipant ← U64.div? (← U64.div? (← U64.mul? totalBaseRewards (← c64 SYNC_REWARD_WEIGHT) site)
    (← c64 WEIGHT_DENOMINATOR) site) (← c64 P.SLOTS_PER_EPOCH) site
  let participantReward ← U64.div? maxParticipant (← c64 P.SYNC_COMMITTEE_SIZE) site
  let proposerReward ← U64.div? (← U64.mul? participantReward (← c64 PROPOSER_WEIGHT) site)
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

/-! ## Execution requests (Electra) -/

/-- `process_deposit_request` (Electra). -/
def processDepositRequest (state : BeaconState P f) (dr : DepositRequest) : M (BeaconState P f) := do
  let mut state := state
  if (← state.depositRequestsStartIndex) == UNSET_DEPOSIT_REQUESTS_START_INDEX then
    state ← state.setDepositRequestsStartIndex dr.index
  let pending ← (← state.pendingDeposits).push
    { pubkey := dr.pubkey, withdrawal_credentials := dr.withdrawal_credentials, amount := dr.amount,
      signature := dr.signature, slot := state.slot } "process_deposit_request"
  state.setPendingDeposits pending

/-- `process_withdrawal_request` (Electra). -/
def processWithdrawalRequest (cfg : Config) (state : BeaconState P f) (wr : WithdrawalRequest) :
    M (BeaconState P f) := do
  let site := "process_withdrawal_request"
  let amount := wr.amount
  let isFullExit := amount == FULL_EXIT_REQUEST_AMOUNT
  if (← state.pendingPartialWithdrawals).length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT && !isFullExit then
    return state
  let some index ← validatorIndexOf state wr.validator_pubkey | return state
  let validator ← state.validators.get index.toNat site
  let hasCorrectCredential := hasExecutionWithdrawalCredential validator
  let isCorrectSource := validator.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes
  if !(hasCorrectCredential && isCorrectSource) then return state
  let current ← getCurrentEpoch state
  if !isActiveValidator validator current then return state
  if validator.exit_epoch != FAR_FUTURE_EPOCH then return state
  if current < (← U64.add? validator.activation_epoch (← c64 cfg.SHARD_COMMITTEE_PERIOD) site) then
    return state
  let pendingBalance ← getPendingBalanceToWithdraw state index
  if isFullExit then
    if pendingBalance == U64.zero then return (← initiateValidatorExit cfg state index)
    return state
  let minAct ← c64 P.MIN_ACTIVATION_BALANCE
  let balance ← state.balances.get index.toNat site
  let sufficient := minAct ≤ validator.effective_balance
  let excess := (← U64.add? minAct pendingBalance site) < balance
  if hasCompoundingWithdrawalCredential validator && sufficient && excess then
    let avail ← U64.sub? (← U64.sub? balance minAct site) pendingBalance site
    let toWithdraw := if avail < amount then avail else amount
    let (state, exitQueueEpoch) ← computeExitEpochAndUpdateChurn cfg state toWithdraw
    let withdrawable ← U64.add? exitQueueEpoch (← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY) site
    let pending ← (← state.pendingPartialWithdrawals).push
      { validator_index := index, amount := toWithdraw, withdrawable_epoch := withdrawable } site
    state.setPendingPartialWithdrawals pending
  else pure state

/-- `is_valid_switch_to_compounding_request` (Electra). -/
def isValidSwitchToCompoundingRequest (state : BeaconState P f) (cr : ConsolidationRequest) :
    M Bool := do
  if !(cr.source_pubkey == cr.target_pubkey) then return false
  let some i ← validatorIndexOf state cr.source_pubkey | return false
  let source ← state.validators.get i.toNat "is_valid_switch_to_compounding_request"
  if !(source.withdrawal_credentials.toBytes.drop 12 == cr.source_address.toBytes) then return false
  if !hasEth1WithdrawalCredential source then return false
  if !isActiveValidator source (← getCurrentEpoch state) then return false
  if source.exit_epoch != FAR_FUTURE_EPOCH then return false
  pure true

/-- `process_consolidation_request` (Electra). -/
def processConsolidationRequest (cfg : Config) (state : BeaconState P f) (cr : ConsolidationRequest) :
    M (BeaconState P f) := do
  let site := "process_consolidation_request"
  if ← isValidSwitchToCompoundingRequest state cr then
    let some sourceIndex ← validatorIndexOf state cr.source_pubkey
      | throw (.assert s!"{site}: validator_pubkeys.index")
    return (← switchToCompoundingValidator state sourceIndex)
  if cr.source_pubkey == cr.target_pubkey then return state
  if (← state.pendingConsolidations).length == P.PENDING_CONSOLIDATIONS_LIMIT then return state
  if (← getConsolidationChurnLimit cfg state).toNat ≤ P.MIN_ACTIVATION_BALANCE then return state
  let some sourceIndex ← validatorIndexOf state cr.source_pubkey | return state
  let some targetIndex ← validatorIndexOf state cr.target_pubkey | return state
  let source ← state.validators.get sourceIndex.toNat site
  let target ← state.validators.get targetIndex.toNat site
  if !(hasExecutionWithdrawalCredential source &&
      source.withdrawal_credentials.toBytes.drop 12 == cr.source_address.toBytes) then return state
  if !hasCompoundingWithdrawalCredential target then return state
  let current ← getCurrentEpoch state
  if !isActiveValidator source current then return state
  if !isActiveValidator target current then return state
  if source.exit_epoch != FAR_FUTURE_EPOCH then return state
  if target.exit_epoch != FAR_FUTURE_EPOCH then return state
  if current < (← U64.add? source.activation_epoch (← c64 cfg.SHARD_COMMITTEE_PERIOD) site) then
    return state
  if U64.zero < (← getPendingBalanceToWithdraw state sourceIndex) then return state
  let (state, exitEpoch) ← computeConsolidationEpochAndUpdateChurn cfg state source.effective_balance
  let withdrawable ← U64.add? exitEpoch (← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY) site
  let source ← state.validators.get sourceIndex.toNat site
  let validators ← state.validators.set sourceIndex.toNat
    { source with exit_epoch := exitEpoch, withdrawable_epoch := withdrawable } site
  let state := { state with validators }
  let pending ← (← state.pendingConsolidations).push
    { source_index := sourceIndex, target_index := targetIndex } site
  state.setPendingConsolidations pending

/-! ## Operations -/

/-- `process_operations` (Electra; Capella to Deneb: the deposit count is
`min(MAX_DEPOSITS, eth1_data.deposit_count - eth1_deposit_index)` and there are no execution
requests). -/
def processOperations (ctx : Ctx) (state : BeaconState P f) (body : BeaconBlockBody P f) :
    M (BeaconState P f) := do
  let site := "process_operations"
  let startIndex ← if f.atLeast .electra then state.depositRequestsStartIndex
    else pure U64.max  -- Capella to Deneb: the eth1 deposit count alone bounds deposits
  let limit := if state.eth1_data.deposit_count < startIndex then state.eth1_data.deposit_count
    else startIndex
  if !(f.atLeast .electra) then
    -- `eth1_data.deposit_count - eth1_deposit_index` is typed `uint64` and raises on underflow.
    let _ ← U64.sub? state.eth1_data.deposit_count state.eth1_deposit_index site
  if state.eth1_deposit_index < limit then
    let remaining ← U64.sub? limit state.eth1_deposit_index site
    require (body.deposits.length == min P.MAX_DEPOSITS remaining.toNat) s!"{site}: deposit count"
  else
    require (body.deposits.length == 0) s!"{site}: no deposits"
  let mut state := state
  for op in body.proposer_slashings.toArray do state ← processProposerSlashing ctx state op
  for op in body.attester_slashings.toArray do state ← processAttesterSlashing ctx state op
  for op in body.attestations.toArray do state ← processAttestation ctx state op
  for op in body.deposits.toArray do state ← processDeposit ctx state op
  for op in body.voluntary_exits.toArray do state ← processVoluntaryExit ctx state op
  for op in body.bls_to_execution_changes.toArray do state ← processBlsToExecutionChange ctx state op
  if f.atLeast .electra then
    let requests ← Gated.read body.execution_requests "execution_requests"
    for op in requests.deposits.toArray do state ← processDepositRequest state op
    for op in requests.withdrawals.toArray do state ← processWithdrawalRequest ctx.cfg state op
    for op in requests.consolidations.toArray do state ← processConsolidationRequest ctx.cfg state op
  pure state

/-! ## Block -/

/-- `process_block` (Electra; Fulu unchanged) under a context. -/
def processBlockWith (ctx : Ctx) (state : BeaconState P f) (block : BeaconBlock P f) :
    M (BeaconState P f) := do
  let state ← processBlockHeader state block
  let state ← processWithdrawals state block.body.execution_payload
  let state ← processExecutionPayload ctx state block.body
  let state ← processRandao ctx state block.body
  let state ← processEth1Data state block.body
  let state ← processOperations ctx state block.body
  processSyncAggregate ctx state block.body.sync_aggregate

/-- `process_block`: the entry point (`ctx` carries the configuration, the BLS switch and the
engine verdict). -/
def processBlock (ctx : Ctx) (state : BeaconState P f) (block : BeaconBlock P f) :
    M (BeaconState P f) :=
  processBlockWith ctx state block

end JauneConsensus
