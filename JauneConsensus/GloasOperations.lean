import JauneConsensus.GloasWithdrawals

/-!
# Gloas operations (goal `eip8282-gloas-cross-layer-v1`, U4)

The block operations and execution-layer requests of `ethereum/consensus-specs` `v1.7.0-beta.4`
over `JauneConsensus.Gloas.BeaconState`, each transcribed from the spec text in statement order:

* reused by reference: `process_proposer_slashing`, `process_attester_slashing` (phase0),
  `process_voluntary_exit` (Electra), `process_bls_to_execution_change` (Capella),
  `process_deposit_request` (Fulu, `v1.7.0-beta.4`: no `deposit_requests_start_index`),
  `process_withdrawal_request`, `is_valid_switch_to_compounding_request`,
  `process_consolidation_request` (Electra), `get_attesting_indices` (Electra) and
  `get_indexed_attestation` (phase0). Each reaches the Gloas helpers it calls: the slashings reach
  the Gloas `slash_validator` (:1549) and the Gloas `is_valid_indexed_attestation` (:1019); the
  exit and withdrawal request reach the Gloas `compute_exit_epoch_and_update_churn`; the
  consolidation request the Gloas `get_consolidation_churn_limit`. Inside
  `namespace JauneConsensus.Gloas` the Fulu twins cannot take a Gloas state, so an unqualified
  call either reaches the Gloas helper or fails to elaborate (`GloasOps.lean`);
* modified in Gloas: `is_valid_indexed_attestation` (:1019, the EIP-7688 cap),
  `get_attestation_participation_flag_indices` (:1339, payload matching) and
  `process_attestation` (:2388, `parent_slot` and builder-payment weight);
* new in Gloas: `is_attestation_same_slot` (:1074), `get_indexed_payload_attestation` (:1407),
  `is_valid_indexed_payload_attestation` (:1091), `process_payload_attestation` (:2485),
  `is_valid_builder_deposit_signature` (:2268), `get_index_for_new_builder` (:2287),
  `add_builder_to_registry` (:2297), `process_builder_deposit_request` (:2322) and
  `process_builder_exit_request` (:2365).

Every BLS check is the real verification under pyspec's switch (`ctx.blsActive`, the case's
`bls_setting`).
-/

namespace JauneConsensus.Gloas

open Jaune

variable {P : Preset}

/-! ## Constants (`specs/gloas/beacon-chain.md`) -/

/-- `DOMAIN_BUILDER_DEPOSIT = DomainType('0x0E000000')`. -/
def DOMAIN_BUILDER_DEPOSIT : DomainType := #v[0x0E, 0x00, 0x00, 0x00]

/-- `PAYLOAD_BUILDER_VERSION = Uint8(0)`. -/
def PAYLOAD_BUILDER_VERSION : U8 := UIntN.zero

/-- The bytes of a fixed-length byte vector. -/
def vbytes {n : Nat} (v : SszVector UInt8 n) : Bytes := v.toArray.toList

/-! ## Attestation indices and validity -/

/-- `is_valid_indexed_attestation(state, indexed_attestation)` (Gloas, :1019): non-empty, at
most `MAX_VALIDATORS_PER_COMMITTEE * MAX_COMMITTEES_PER_SLOT` indices (EIP-7688), sorted and
unique, and a valid aggregate signature. -/
def isValidIndexedAttestation (ctx : Ctx) (state : BeaconState P) (ia : IndexedAttestation) :
    M Bool := do
  let indices := ia.attesting_indices.toArray
  let sortedUnique := (indices.qsort (· < ·)).toList.eraseDups.toArray
  if indices.size == 0
      -- [New in Gloas:EIP7688]
      || indices.size > P.MAX_VALIDATORS_PER_COMMITTEE * P.MAX_COMMITTEES_PER_SLOT
      || !(indices == sortedUnique) then
    return false
  let mut pubkeys := #[]
  for i in indices do
    pubkeys := pubkeys.push (← state.validators.get i.toNat "is_valid_indexed_attestation").pubkey
  let domain ← getDomain state DOMAIN_BEACON_ATTESTER (some ia.data.target.epoch)
  let root := computeSigningRoot ia.data domain
  pure (blsFastAggregateVerify ctx.blsActive pubkeys.toList root ia.signature)

/-- `get_attesting_indices(state, attestation)` (Electra): the committees named by
`committee_bits`, consuming `aggregation_bits` committee by committee; returned as a sorted set. -/
def getAttestingIndices (state : BeaconState P) (attestation : Attestation P) :
    M (Array ValidatorIndex) := do
  let bits := attestation.aggregation_bits.bits
  let mut out : Array ValidatorIndex := #[]
  let mut offset := 0
  for ci in ← getCommitteeIndices attestation.committee_bits do
    let committee ← getBeaconCommittee state attestation.data.slot ci
    let mut i := 0
    for a in committee do
      if ← getAt bits (offset + i) "aggregation_bits" then out := out.push a
      i := i + 1
    offset := offset + committee.size
  pure ((out.qsort (· < ·)).toList.eraseDups.toArray)

/-- `get_indexed_attestation(state, attestation)` (phase0). -/
def getIndexedAttestation (state : BeaconState P) (attestation : Attestation P) :
    M IndexedAttestation := do
  pure { attesting_indices := ProgressiveListS.ofArray (← getAttestingIndices state attestation)
         data := attestation.data
         signature := attestation.signature }

/-! ## Slashings -/

/-- `process_proposer_slashing` (phase0), reaching the Gloas `slash_validator`. -/
def processProposerSlashing (ctx : Ctx) (state : BeaconState P) (ps : ProposerSlashing) :
    M (BeaconState P) := do
  let site := "process_proposer_slashing"
  let h1 := ps.signed_header_1.message
  let h2 := ps.signed_header_2.message
  require (h1.slot == h2.slot) s!"{site}: slots match"
  require (h1.proposer_index == h2.proposer_index) s!"{site}: proposers match"
  require (!(h1 == h2)) s!"{site}: headers differ"
  let proposer ← state.validators.get h1.proposer_index.toNat site
  require (isSlashableValidator proposer (← getCurrentEpoch state)) s!"{site}: slashable"
  for sh in [ps.signed_header_1, ps.signed_header_2] do
    let domain ← getDomain state DOMAIN_BEACON_PROPOSER
      (some (← computeEpochAtSlot P sh.message.slot))
    let root := computeSigningRoot sh.message domain
    require (blsVerify ctx.blsActive proposer.pubkey root sh.signature) s!"{site}: bls.Verify"
  slashValidator ctx.cfg state h1.proposer_index

/-- `process_attester_slashing` (phase0), reaching the Gloas `is_valid_indexed_attestation` and
`slash_validator`. -/
def processAttesterSlashing (ctx : Ctx) (state : BeaconState P) (as : AttesterSlashing) :
    M (BeaconState P) := do
  let site := "process_attester_slashing"
  let a1 := as.attestation_1
  let a2 := as.attestation_2
  require (isSlashableAttestationData a1.data a2.data) s!"{site}: slashable data"
  require (← isValidIndexedAttestation ctx state a1) s!"{site}: attestation_1"
  require (← isValidIndexedAttestation ctx state a2) s!"{site}: attestation_2"
  let s2 := a2.attesting_indices.toArray
  let indices :=
    ((a1.attesting_indices.toArray.filter (s2.contains ·)).qsort (· < ·)).toList.eraseDups
  let mut state := state
  let mut slashedAny := false
  for index in indices do
    let v ← state.validators.get index.toNat site
    if isSlashableValidator v (← getCurrentEpoch state) then
      state ← slashValidator ctx.cfg state index
      slashedAny := true
  require slashedAny s!"{site}: slashed_any"
  pure state

/-! ## Attestations -/

/-- `is_attestation_same_slot(state, data)` (Gloas, :1074): the attestation votes for the block
proposed at its slot. -/
def isAttestationSameSlot (state : BeaconState P) (data : AttestationData) : M Bool := do
  if data.slot == U64.zero then return true
  let blockroot := data.beacon_block_root
  let slotBlockroot ← getBlockRootAtSlot state data.slot
  let prevBlockroot ← getBlockRootAtSlot state (← data.slot.sub? U64.one "is_attestation_same_slot")
  pure (blockroot == slotBlockroot && !(blockroot == prevBlockroot))

/-- `get_attestation_participation_flag_indices(state, data, inclusion_delay, parent_slot)`
(Gloas, :1339): the head flag also needs the payload status `data.index` to match the payload
availability recorded at `parent_slot` (or, for a same-slot attestation, `data.index == 0`). -/
def getAttestationParticipationFlagIndices (state : BeaconState P) (data : AttestationData)
    (inclusionDelay : U64) (parentSlot : Slot) : M (List Nat) := do
  let site := "get_attestation_participation_flag_indices"
  let current ← getCurrentEpoch state
  -- Matching source
  let justified := if data.target.epoch == current then state.current_justified_checkpoint
    else state.previous_justified_checkpoint
  let isMatchingSource := data.source == justified
  -- Matching target
  let targetRoot ← getBlockRoot state data.target.epoch
  let isMatchingTarget := isMatchingSource && data.target.root == targetRoot
  -- [New in Gloas:EIP7732]
  let payloadMatches ←
    if ← isAttestationSameSlot state data then do
      require (data.index == U64.zero) s!"{site}: data.index == 0"
      pure true
    else do
      let slotIndex ← parentSlot.mod? (← c64 P.SLOTS_PER_HISTORICAL_ROOT) site
      let payloadIndex ← getAt state.execution_payload_availability.bits slotIndex.toNat site
      pure (data.index.toNat == (if payloadIndex then 1 else 0))
  -- Matching head
  let headRoot ← getBlockRootAtSlot state data.slot
  let isMatchingHead := isMatchingTarget && data.beacon_block_root == headRoot && payloadMatches
  require isMatchingSource s!"{site}: matching source"
  let mut out := []
  if isMatchingSource && inclusionDelay ≤ (← integerSquareroot (← c64 P.SLOTS_PER_EPOCH)) then
    out := out ++ [TIMELY_SOURCE_FLAG_INDEX]
  if isMatchingTarget then out := out ++ [TIMELY_TARGET_FLAG_INDEX]
  if isMatchingHead && inclusionDelay.toNat == P.MIN_ATTESTATION_INCLUSION_DELAY then
    out := out ++ [TIMELY_HEAD_FLAG_INDEX]
  pure out

/-- `process_attestation(state, attestation, parent_slot)` (Gloas, :2388): Electra's checks
with `data.index < 2`, the Gloas flag indices, and the builder-payment weight: an attester that
had no participation flag and sets one for a same-slot attestation adds its effective balance
to the pending payment of the attested slot, when that payment is non-zero. -/
def processAttestation (ctx : Ctx) (state : BeaconState P) (attestation : Attestation P)
    (parentSlot : Slot) : M (BeaconState P) := do
  let site := "process_attestation"
  let data := attestation.data
  let current ← getCurrentEpoch state
  let previous ← getPreviousEpoch state
  require (data.target.epoch == previous || data.target.epoch == current) s!"{site}: target epoch"
  require (data.target.epoch == (← computeEpochAtSlot P data.slot)) s!"{site}: target epoch of slot"
  require ((← data.slot.add? (← c64 P.MIN_ATTESTATION_INCLUSION_DELAY) site) ≤ state.slot)
    s!"{site}: inclusion delay"
  -- [Modified in Gloas:EIP7732]
  require (data.index < (← c64 2)) s!"{site}: data.index < 2"
  let bits := attestation.aggregation_bits.bits
  let mut offset := 0
  for ci in ← getCommitteeIndices attestation.committee_bits do
    require (ci < (← getCommitteeCountPerSlot state data.target.epoch)) s!"{site}: committee index"
    let committee ← getBeaconCommittee state data.slot ci
    let mut attesters := 0
    for i in [0:committee.size] do
      if ← getAt bits (offset + i) "aggregation_bits" then attesters := attesters + 1
    require (attesters > 0) s!"{site}: committee attesters"
    offset := offset + committee.size
  -- Bitfield length matches total number of participants
  require (bits.size == offset) s!"{site}: bitfield length"
  -- [Modified in Gloas:EIP7732]
  let flags ← getAttestationParticipationFlagIndices state data
    (← state.slot.sub? data.slot site) parentSlot
  -- Verify signature
  require (← isValidIndexedAttestation ctx state (← getIndexedAttestation state attestation))
    s!"{site}: indexed attestation"
  -- [Modified in Gloas:EIP7732]
  let spe ← c64 P.SLOTS_PER_EPOCH
  let isCurrent := data.target.epoch == current
  let paymentIndex ← if isCurrent then do spe.add? (← data.slot.mod? spe site) site
    else data.slot.mod? spe site
  let mut payment ← state.builder_pending_payments.get paymentIndex.toNat site
  let mut participation :=
    if isCurrent then state.current_epoch_participation else state.previous_epoch_participation
  let mut numerator := U64.zero
  for index in ← getAttestingIndices state attestation do
    -- [New in Gloas:EIP7732]
    let hadNoParticipation := (← participation.get index.toNat site) == UIntN.zero
    let mut willSetNewFlag := false
    for (flagIndex, weight) in
        (List.range PARTICIPATION_FLAG_WEIGHTS.length).zip PARTICIPATION_FLAG_WEIGHTS do
      if flags.contains flagIndex then
        let cur ← participation.get index.toNat site
        if !(← hasFlag cur flagIndex) then
          participation ← participation.set index.toNat (← addFlag cur flagIndex) site
          numerator ← numerator.add? (← (← getBaseReward state index).mul? (← c64 weight) site) site
          -- [New in Gloas:EIP7732]
          willSetNewFlag := true
    -- [New in Gloas:EIP7732] (`and` short-circuits, left to right)
    if willSetNewFlag && hadNoParticipation then
      if ← isAttestationSameSlot state data then
        if U64.zero < payment.withdrawal.amount then
          let v ← state.validators.get index.toNat site
          payment := { payment with weight := ← payment.weight.add? v.effective_balance site }
  let state := if isCurrent then { state with current_epoch_participation := participation }
    else { state with previous_epoch_participation := participation }
  -- Reward proposer
  let denominator ← (← (← c64 (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT)).mul?
    (← c64 WEIGHT_DENOMINATOR) site).div? (← c64 PROPOSER_WEIGHT) site
  let reward ← numerator.div? denominator s!"{site}: Gwei(proposer_reward)"
  let state ← increaseBalance state (← getBeaconProposerIndex state) reward
  -- [New in Gloas:EIP7732] Update builder payment weight
  pure { state with builder_pending_payments :=
    ← state.builder_pending_payments.set paymentIndex.toNat payment site }

/-! ## Payload attestations -/

/-- `get_indexed_payload_attestation(state, payload_attestation)` (Gloas, :1407): the PTC
members whose bit is set, sorted (a member drawn twice appears twice). -/
def getIndexedPayloadAttestation (cfg : Config) (state : BeaconState P)
    (pa : PayloadAttestation P) : M (IndexedPayloadAttestation P) := do
  let site := "get_indexed_payload_attestation"
  let ptc ← getPtc cfg state pa.data.slot
  let bits := pa.aggregation_bits.bits
  let mut attesting : Array ValidatorIndex := #[]
  let mut index := 0
  for validatorIndex in ptc.toArray do
    if ← getAt bits index site then attesting := attesting.push validatorIndex
    index := index + 1
  pure { attesting_indices := ← SszList.ofArray (attesting.qsort (· < ·)) site
         data := pa.data
         signature := pa.signature }

/-- `is_valid_indexed_payload_attestation(state, attestation)` (Gloas, :1091): non-empty, sorted
(duplicates allowed), and a valid aggregate signature under `DOMAIN_PTC_ATTESTER`. -/
def isValidIndexedPayloadAttestation (ctx : Ctx) (state : BeaconState P)
    (ia : IndexedPayloadAttestation P) : M Bool := do
  let site := "is_valid_indexed_payload_attestation"
  let indices := ia.attesting_indices.toArray
  if indices.size == 0 || !(indices == indices.qsort (· < ·)) then return false
  let pubkeys ← indices.mapM fun i => do pure (← state.validators.get i.toNat site).pubkey
  let domain ← getDomain state DOMAIN_PTC_ATTESTER (some (← computeEpochAtSlot P ia.data.slot))
  let root := computeSigningRoot ia.data domain
  pure (blsFastAggregateVerify ctx.blsActive pubkeys.toList root ia.signature)

/-- `process_payload_attestation(state, payload_attestation)` (Gloas, :2485). -/
def processPayloadAttestation (ctx : Ctx) (state : BeaconState P) (pa : PayloadAttestation P) :
    M (BeaconState P) := do
  let site := "process_payload_attestation"
  let data := pa.data
  -- Check that the attestation is for the parent beacon block
  require (data.beacon_block_root == state.latest_block_header.parent_root)
    s!"{site}: parent beacon block"
  -- Check that the attestation is for the previous slot
  require ((← data.slot.add? U64.one site) == state.slot) s!"{site}: previous slot"
  -- Verify signature
  let indexed ← getIndexedPayloadAttestation ctx.cfg state pa
  require (← isValidIndexedPayloadAttestation ctx state indexed) s!"{site}: indexed payload attestation"
  pure state

/-! ## Exits and credential changes -/

/-- `process_voluntary_exit` (Electra), reaching the Gloas exit churn. -/
def processVoluntaryExit (ctx : Ctx) (state : BeaconState P) (sve : SignedVoluntaryExit) :
    M (BeaconState P) := do
  let site := "process_voluntary_exit"
  let ve := sve.message
  let validator ← state.validators.get ve.validator_index.toNat site
  let current ← getCurrentEpoch state
  require (isActiveValidator validator current) s!"{site}: active"
  require (validator.exit_epoch == FAR_FUTURE_EPOCH) s!"{site}: not exiting"
  require (ve.epoch ≤ current) s!"{site}: epoch"
  require ((← validator.activation_epoch.add? (← c64 ctx.cfg.SHARD_COMMITTEE_PERIOD) site) ≤ current)
    s!"{site}: active long enough"
  require ((← getPendingBalanceToWithdraw state ve.validator_index) == U64.zero)
    s!"{site}: no pending withdrawals"
  let domain := computeDomain DOMAIN_VOLUNTARY_EXIT (← versionOf ctx.cfg.CAPELLA_FORK_VERSION)
    state.genesis_validators_root
  let root := computeSigningRoot ve domain
  require (blsVerify ctx.blsActive validator.pubkey root sve.signature) s!"{site}: bls.Verify"
  initiateValidatorExit ctx.cfg state ve.validator_index

/-- `process_bls_to_execution_change` (Capella). -/
def processBlsToExecutionChange (ctx : Ctx) (state : BeaconState P)
    (sac : SignedBLSToExecutionChange) : M (BeaconState P) := do
  let site := "process_bls_to_execution_change"
  let ac := sac.message
  require (ac.validator_index.toNat < state.validators.length) s!"{site}: index"
  let validator ← state.validators.get ac.validator_index.toNat site
  let wc := validator.withdrawal_credentials.toBytes
  require (wc.take 1 == [BLS_WITHDRAWAL_PREFIX]) s!"{site}: BLS prefix"
  require (wc.drop 1 == (hashBytes (vbytes ac.from_bls_pubkey)).drop 1) s!"{site}: pubkey hash"
  let domain := computeDomain DOMAIN_BLS_TO_EXECUTION_CHANGE
    (← versionOf ctx.cfg.GENESIS_FORK_VERSION) state.genesis_validators_root
  let root := computeSigningRoot ac domain
  require (blsVerify ctx.blsActive ac.from_bls_pubkey root sac.signature) s!"{site}: bls.Verify"
  let newWc := Jaune.Bytes.toB256 (ETH1_ADDRESS_WITHDRAWAL_PREFIX :: List.replicate 11 0 ++
    ac.to_execution_address.toBytes)
  let validators ← state.validators.set ac.validator_index.toNat
    { validator with withdrawal_credentials := newWc } site
  pure { state with validators }

/-! ## Execution-layer requests (Electra, Fulu) -/

/-- `validator_pubkeys.index(pubkey)`, if present. -/
def validatorIndexOf (state : BeaconState P) (pubkey : BLSPubkey) : M (Option ValidatorIndex) := do
  match state.validators.toArray.findIdx? (·.pubkey == pubkey) with
  | some i => pure (some (← U64.ofNat? i "ValidatorIndex"))
  | none => pure none

/-- `process_deposit_request` (Fulu, `v1.7.0-beta.4`): append a pending deposit at
`state.slot`. -/
def processDepositRequest (state : BeaconState P) (dr : DepositRequest) : BeaconState P :=
  let deposit : PendingDeposit :=
    { pubkey := dr.pubkey, withdrawal_credentials := dr.withdrawal_credentials,
      amount := dr.amount, signature := dr.signature, slot := state.slot }
  { state with pending_deposits := state.pending_deposits.push deposit }

/-- `process_withdrawal_request` (Electra), reaching the Gloas exit churn. -/
def processWithdrawalRequest (cfg : Config) (state : BeaconState P) (wr : WithdrawalRequest) :
    M (BeaconState P) := do
  let site := "process_withdrawal_request"
  let amount := wr.amount
  let isFullExit := amount == FULL_EXIT_REQUEST_AMOUNT
  -- If partial withdrawal queue is full, only full exits are processed
  if state.pending_partial_withdrawals.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT && !isFullExit then
    return state
  let some index ← validatorIndexOf state wr.validator_pubkey | return state
  let validator ← state.validators.get index.toNat site
  let hasCorrectCredential := hasExecutionWithdrawalCredential validator
  let isCorrectSource := validator.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes
  if !(hasCorrectCredential && isCorrectSource) then return state
  let current ← getCurrentEpoch state
  if !isActiveValidator validator current then return state
  if validator.exit_epoch != FAR_FUTURE_EPOCH then return state
  if current < (← validator.activation_epoch.add? (← c64 cfg.SHARD_COMMITTEE_PERIOD) site) then
    return state
  let pendingBalance ← getPendingBalanceToWithdraw state index
  if isFullExit then
    if pendingBalance == U64.zero then return (← initiateValidatorExit cfg state index)
    return state
  let minAct ← c64 P.MIN_ACTIVATION_BALANCE
  let balance ← state.balances.get index.toNat site
  let sufficient := minAct ≤ validator.effective_balance
  let excess := (← minAct.add? pendingBalance site) < balance
  if hasCompoundingWithdrawalCredential validator && sufficient && excess then
    let avail ← (← balance.sub? minAct site).sub? pendingBalance site
    let toWithdraw := if avail < amount then avail else amount
    let (state, exitQueueEpoch) ← computeExitEpochAndUpdateChurn cfg state toWithdraw
    let withdrawable ← exitQueueEpoch.add? (← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY) site
    let w : PendingPartialWithdrawal :=
      { validator_index := index, amount := toWithdraw, withdrawable_epoch := withdrawable }
    pure { state with pending_partial_withdrawals := state.pending_partial_withdrawals.push w }
  else pure state

/-- `is_valid_switch_to_compounding_request` (Electra). -/
def isValidSwitchToCompoundingRequest (state : BeaconState P) (cr : ConsolidationRequest) :
    M Bool := do
  if !(cr.source_pubkey == cr.target_pubkey) then return false
  let some i ← validatorIndexOf state cr.source_pubkey | return false
  let source ← state.validators.get i.toNat "is_valid_switch_to_compounding_request"
  if !(source.withdrawal_credentials.toBytes.drop 12 == cr.source_address.toBytes) then return false
  if !hasEth1WithdrawalCredential source then return false
  if !isActiveValidator source (← getCurrentEpoch state) then return false
  if source.exit_epoch != FAR_FUTURE_EPOCH then return false
  pure true

/-- `process_consolidation_request` (Electra), reaching the Gloas consolidation churn. -/
def processConsolidationRequest (cfg : Config) (state : BeaconState P) (cr : ConsolidationRequest) :
    M (BeaconState P) := do
  let site := "process_consolidation_request"
  if ← isValidSwitchToCompoundingRequest state cr then
    let some sourceIndex ← validatorIndexOf state cr.source_pubkey
      | throw (.assert s!"{site}: validator_pubkeys.index")
    return (← switchToCompoundingValidator state sourceIndex)
  if cr.source_pubkey == cr.target_pubkey then return state
  if state.pending_consolidations.length == P.PENDING_CONSOLIDATIONS_LIMIT then return state
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
  if current < (← source.activation_epoch.add? (← c64 cfg.SHARD_COMMITTEE_PERIOD) site) then
    return state
  if U64.zero < (← getPendingBalanceToWithdraw state sourceIndex) then return state
  let (state, exitEpoch) ← computeConsolidationEpochAndUpdateChurn cfg state source.effective_balance
  let withdrawable ← exitEpoch.add? (← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY) site
  let source ← state.validators.get sourceIndex.toNat site
  let validators ← state.validators.set sourceIndex.toNat
    { source with exit_epoch := exitEpoch, withdrawable_epoch := withdrawable } site
  pure { state with
    validators
    pending_consolidations := state.pending_consolidations.push
      { source_index := sourceIndex, target_index := targetIndex } }

/-! ## Builder deposit requests (Gloas, EIP-8282) -/

/-- `is_valid_builder_deposit_signature(request)` (Gloas, :2268): the `DepositMessage` signed
under `compute_domain(DOMAIN_BUILDER_DEPOSIT)` (the phase0 defaults: `GENESIS_FORK_VERSION` and
the zero root). -/
def isValidBuilderDepositSignature (ctx : Ctx) (request : BuilderDepositRequest) : M Bool := do
  let msg : DepositMessage :=
    { pubkey := request.pubkey, withdrawal_credentials := request.withdrawal_credentials,
      amount := request.amount }
  let domain ← computeDomainDefault ctx.cfg DOMAIN_BUILDER_DEPOSIT
  let root := computeSigningRoot msg domain
  pure (blsVerify ctx.blsActive request.pubkey root request.signature)

/-- `get_index_for_new_builder(state)` (Gloas, :2287): the first exited, swept builder slot, or
the end of the registry. -/
def getIndexForNewBuilder (state : BeaconState P) : M BuilderIndex := do
  let epoch ← getCurrentEpoch state
  let mut index := 0
  for builder in state.builders.toArray do
    if builder.withdrawable_epoch ≤ epoch && builder.balance == U64.zero then
      return ← U64.ofNat? index "BuilderIndex"
    index := index + 1
  U64.ofNat? state.builders.length "BuilderIndex"

/-- `add_builder_to_registry(state, pubkey, version, execution_address, amount, slot)` (Gloas,
:2297). -/
def addBuilderToRegistry (state : BeaconState P) (pubkey : BLSPubkey) (version : U8)
    (executionAddress : ExecutionAddress) (amount : Gwei) (slot : Slot) : M (BeaconState P) := do
  let index ← getIndexForNewBuilder state
  let builder : Builder :=
    { pubkey, version, execution_address := executionAddress, balance := amount,
      deposit_epoch := ← computeEpochAtSlot P slot, withdrawable_epoch := FAR_FUTURE_EPOCH }
  pure { state with builders := ← state.builders.setOrAppend index builder "add_builder_to_registry" }

/-- `process_builder_deposit_request(state, request)` (Gloas, :2322): a new pubkey with a valid
signature registers a builder; a known pubkey tops up its builder (resetting the withdrawable
epoch of an exited, swept builder). Requests without the builder credential prefix are ignored. -/
def processBuilderDepositRequest (ctx : Ctx) (state : BeaconState P)
    (request : BuilderDepositRequest) : M (BeaconState P) := do
  let site := "process_builder_deposit_request"
  -- Ignore deposits with unexpected withdrawal credential prefixes
  if !isBuilderWithdrawalCredential request.withdrawal_credentials then return state
  match state.builders.toArray.findIdx? (·.pubkey == request.pubkey) with
  | none =>
    if ← isValidBuilderDepositSignature ctx request then
      addBuilderToRegistry state request.pubkey PAYLOAD_BUILDER_VERSION
        (← addressOfCredentials request.withdrawal_credentials) request.amount state.slot
    else pure state
  | some i =>
    let builder ← state.builders.get i site
    -- If exited and swept, reset the withdrawable epoch
    let builder ← if builder.withdrawable_epoch != FAR_FUTURE_EPOCH && builder.balance == U64.zero
      then do
        let epoch ← getCurrentEpoch state
        pure { builder with
          withdrawable_epoch := ← epoch.add? (← c64 ctx.cfg.MIN_BUILDER_WITHDRAWABILITY_DELAY) site }
      else pure builder
    -- Increase balance by deposit amount
    let builder := { builder with balance := ← builder.balance.add? request.amount site }
    pure { state with builders := ← state.builders.set i builder site }

/-! ## Builder exit requests (Gloas, EIP-8282) -/

/-- `process_builder_exit_request(state, request)` (Gloas, :2365): an active builder whose
`execution_address` is the request's `source_address` and that has nothing pending exits. -/
def processBuilderExitRequest (cfg : Config) (state : BeaconState P) (request : BuilderExitRequest) :
    M (BeaconState P) := do
  let some i := state.builders.toArray.findIdx? (·.pubkey == request.pubkey) | return state
  let builderIndex ← U64.ofNat? i "BuilderIndex"
  let builder ← state.builders.get i "process_builder_exit_request"
  if !(← isActiveBuilder state builderIndex) then return state
  if builder.execution_address != request.source_address then return state
  if (← getPendingBalanceToWithdrawForBuilder state builderIndex) != U64.zero then return state
  initiateBuilderExit cfg state builderIndex

end JauneConsensus.Gloas
