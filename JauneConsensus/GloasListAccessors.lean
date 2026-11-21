import JauneConsensus.GloasAccessors

/-!
# Gloas list methods and read-only state accessors (goal `eip8282-gloas-cross-layer-v1`, U3)

Transcribed from `ethereum/consensus-specs` `v1.7.0-beta.4`. Gloas keeps most phase0 to Fulu
accessors by reference; under Gloas they read `JauneConsensus.Gloas.BeaconState`, a separate
structure (`ContainersGloas.lean`), so each reused accessor is copied here over that state, in the
spec's operation order. The accessors Gloas *modifies* (`specs/gloas/beacon-chain.md`) are written
from the Gloas text: `compute_proposer_indices` (:1240), `get_beacon_proposer_indices` (:1294), the
churn limits (:1445, :1461, :1479), and the new `compute_balance_weighted_selection` (:1198),
`compute_ptc` (:1266), `get_ptc` (:1392) and `get_builder_payment_quorum_threshold` (:1433).

**Name resolution.** Inside `namespace JauneConsensus.Gloas` an unqualified name such as
`getTotalActiveBalance` resolves to both `JauneConsensus.getTotalActiveBalance` and
`JauneConsensus.Gloas.getTotalActiveBalance`; Lean treats the pair as an overload and keeps the
alternative that elaborates. Every overridden helper takes the state, and the Fulu alternative
cannot take a Gloas state, so a call from a Gloas body reaches the Gloas helper or fails to
elaborate; it never silently reaches the Fulu one.

**Progressive lists.** `ProgressiveListS`/`ProgressiveBitlistS` get the method names of `SszList`
(`get`, `set`, `modify`, `push`, `length`, `empty`, `ofArray`). A progressive list has no limit,
so `push` and `ofArray` are total; `get`, `set` and `modify` reject out of range (`Reject.index`).

Conventions as in `Accessors.lean`: typed `uint64` arithmetic is checked `U64`; Python `int` is
`Nat`; there is no defaulted read.
-/

namespace JauneConsensus

/-! ## Progressive list and bitlist methods -/

namespace ProgressiveListOnSpine
variable {s : Spine} {α : Type}

/-- `xs[i]`, rejecting out of range. -/
@[inline] def get (xs : ProgressiveListOnSpine s α) (i : Nat) (site : String) : Fallible α :=
  getAt xs.toArray i site

/-- `xs[i] = v`, rejecting out of range. -/
def set (xs : ProgressiveListOnSpine s α) (i : Nat) (v : α) (site : String) :
    Fallible (ProgressiveListOnSpine s α) :=
  if h : i < xs.toArray.size then pure ⟨xs.toArray.set i v h⟩
  else throw (.index site i xs.toArray.size)

/-- `xs[i] = g(xs[i])`. -/
def modify (xs : ProgressiveListOnSpine s α) (i : Nat) (g : α → Fallible α) (site : String) :
    Fallible (ProgressiveListOnSpine s α) := do
  let v ← xs.get i site
  xs.set i (← g v) site

/-- `xs.append(v)`: total, a progressive list has no limit. -/
def push (xs : ProgressiveListOnSpine s α) (v : α) : ProgressiveListOnSpine s α := ⟨xs.toArray.push v⟩

/-- `len(xs)`. -/
@[inline] def length (xs : ProgressiveListOnSpine s α) : Nat := xs.toArray.size

/-- The empty list. -/
def empty : ProgressiveListOnSpine s α := ⟨#[]⟩

/-- A list from an array: total, a progressive list has no limit. -/
def ofArray (xs : Array α) : ProgressiveListOnSpine s α := ⟨xs⟩

/-- `set_or_append_list(xs, index, value)` (`specs/altair/beacon-chain.md`, which accepts a
`ProgressiveList`): append when `index == len(xs)`, otherwise set. -/
def setOrAppend (xs : ProgressiveListOnSpine s α) (index : ValidatorIndex) (v : α) (site : String) :
    Fallible (ProgressiveListOnSpine s α) :=
  if index.toNat == xs.length then pure (xs.push v) else xs.set index.toNat v site

end ProgressiveListOnSpine

namespace ProgressiveBitlistOnSpine
variable {s : Spine}

/-- `bits[i]`, rejecting out of range. -/
@[inline] def get (xs : ProgressiveBitlistOnSpine s) (i : Nat) (site : String) : Fallible Bool :=
  getAt xs.bits i site

/-- `bits[i] = b`, rejecting out of range. -/
def set (xs : ProgressiveBitlistOnSpine s) (i : Nat) (b : Bool) (site : String) :
    Fallible (ProgressiveBitlistOnSpine s) :=
  if h : i < xs.bits.size then pure ⟨xs.bits.set i b h⟩
  else throw (.index site i xs.bits.size)

/-- `bits.append(b)`: total. -/
def push (xs : ProgressiveBitlistOnSpine s) (b : Bool) : ProgressiveBitlistOnSpine s := ⟨xs.bits.push b⟩

/-- `len(bits)`. -/
@[inline] def length (xs : ProgressiveBitlistOnSpine s) : Nat := xs.bits.size

/-- The empty bitlist. -/
def empty : ProgressiveBitlistOnSpine s := ⟨#[]⟩

/-- A bitlist from an array: total. -/
def ofArray (bs : Array Bool) : ProgressiveBitlistOnSpine s := ⟨bs⟩

end ProgressiveBitlistOnSpine

namespace Gloas

open Jaune

variable {P : Preset}

/-! ## Constants (`specs/gloas/beacon-chain.md`) -/

/-- `DOMAIN_PTC_ATTESTER = DomainType('0x0C000000')`. -/
def DOMAIN_PTC_ATTESTER : DomainType := #v[0x0C, 0x00, 0x00, 0x00]
/-- `BUILDER_PAYMENT_THRESHOLD_NUMERATOR = Uint64(6)`. -/
def BUILDER_PAYMENT_THRESHOLD_NUMERATOR : Nat := 6
/-- `BUILDER_PAYMENT_THRESHOLD_DENOMINATOR = Uint64(10)`. -/
def BUILDER_PAYMENT_THRESHOLD_DENOMINATOR : Nat := 10
/-- `BUILDER_WITHDRAWAL_PREFIX = Bytes1('0xB0')`. -/
def BUILDER_WITHDRAWAL_PREFIX : UInt8 := 0xB0

/-! ## Predicates -/

/-- `is_eligible_for_activation` (phase0). -/
def isEligibleForActivation (state : BeaconState P) (v : Validator) : Bool :=
  v.activation_eligibility_epoch ≤ state.finalized_checkpoint.epoch &&
    v.activation_epoch == FAR_FUTURE_EPOCH

/-- `is_builder_index` (Gloas): `validator_index & BUILDER_INDEX_FLAG != 0`. -/
def isBuilderIndex (validatorIndex : ValidatorIndex) : Bool :=
  validatorIndex.toNat &&& BUILDER_INDEX_FLAG.toNat != 0

/-- `is_builder_withdrawal_credential` (Gloas). -/
def isBuilderWithdrawalCredential (wc : Bytes32) : Bool :=
  credentialPrefix wc == BUILDER_WITHDRAWAL_PREFIX

/-- `is_active_builder` (Gloas). -/
def isActiveBuilder (state : BeaconState P) (builderIndex : BuilderIndex) : Fallible Bool := do
  let builder ← state.builders.get builderIndex.toNat "is_active_builder"
  pure (builder.deposit_epoch < state.finalized_checkpoint.epoch &&
    builder.withdrawable_epoch == FAR_FUTURE_EPOCH)

/-! ## Epochs, seeds, committees -/

/-- `get_previous_epoch` (phase0). -/
def getPreviousEpoch (state : BeaconState P) : Fallible Epoch := do
  let current ← getCurrentEpoch state
  if current == GENESIS_EPOCH then pure GENESIS_EPOCH
  else U64.sub? current U64.one "get_previous_epoch"

/-- `get_active_validator_indices` (phase0). -/
def getActiveValidatorIndices (state : BeaconState P) (epoch : Epoch) :
    Fallible (Array ValidatorIndex) := do
  let mut out := #[]
  let mut i := 0
  for v in state.validators.toArray do
    if isActiveValidator v epoch then out := out.push (← U64.ofNat? i "ValidatorIndex")
    i := i + 1
  pure out

/-- `get_randao_mix` (phase0). -/
def getRandaoMix (state : BeaconState P) (epoch : Epoch) : Fallible Bytes32 := do
  let m ← U64.mod? epoch (← u64Checked P.EPOCHS_PER_HISTORICAL_VECTOR) "get_randao_mix"
  state.randao_mixes.get m.toNat "get_randao_mix"

/-- `get_seed` (phase0). -/
def getSeed (state : BeaconState P) (epoch : Epoch) (domainType : DomainType) : Fallible Bytes32 := do
  let e ← U64.add? epoch (← u64Checked P.EPOCHS_PER_HISTORICAL_VECTOR) "get_seed"
  let e ← U64.sub? e (← u64Checked P.MIN_SEED_LOOKAHEAD) "get_seed"
  let e ← U64.sub? e U64.one "get_seed"
  let mix ← getRandaoMix state e
  pure (hash (domainType.toList ++ uintToBytes 8 epoch.toNat ++ mix.toBytes))

/-- `get_committee_count_per_slot` (phase0). -/
def getCommitteeCountPerSlot (state : BeaconState P) (epoch : Epoch) : Fallible U64 := do
  let n := (← getActiveValidatorIndices state epoch).size
  let perSlot ← U64.div? (← U64.ofNat? n "uint64(len)") (← u64Checked P.SLOTS_PER_EPOCH) "committee count"
  let perSlot ← U64.div? perSlot (← u64Checked P.TARGET_COMMITTEE_SIZE) "committee count"
  let maxC ← u64Checked P.MAX_COMMITTEES_PER_SLOT
  let m := if perSlot < maxC then perSlot else maxC
  pure (if U64.one < m then m else U64.one)

/-- `get_beacon_committee` (phase0), with the state-free `compute_committee` of `Accessors.lean`. -/
def getBeaconCommittee (state : BeaconState P) (slot : Slot) (index : CommitteeIndex) :
    Fallible (Array ValidatorIndex) := do
  let epoch ← computeEpochAtSlot P slot
  let committeesPerSlot ← getCommitteeCountPerSlot state epoch
  let spe ← u64Checked P.SLOTS_PER_EPOCH
  let slotInEpoch ← U64.mod? slot spe "get_beacon_committee"
  let idx ← U64.add? (← U64.mul? slotInEpoch committeesPerSlot "get_beacon_committee") index
    "get_beacon_committee"
  let count ← U64.mul? committeesPerSlot spe "get_beacon_committee"
  computeCommittee P (← getActiveValidatorIndices state epoch)
    (← getSeed state epoch DOMAIN_BEACON_ATTESTER) idx count

/-! ## Balance-weighted selection, proposers, PTC (Gloas) -/

/-- `compute_balance_weighted_selection(state, indices, seed, size, shuffle_indices)` (Gloas,
:1198). The effective balances are read before the loop, as pyspec's list comprehension does;
`i` is a `Uint64`, so its increment is checked. pyspec's `while` loop runs on `SAMPLING_FUEL`
iterations (`Accessors.lean`, with its probability bound) and rejects if it is exhausted. -/
def computeBalanceWeightedSelection (state : BeaconState P) (indices : Array ValidatorIndex)
    (seed : Bytes32) (size : Nat) (shuffleIndices : Bool) : Fallible (Array ValidatorIndex) := do
  let site := "compute_balance_weighted_selection"
  let maxRandomValue ← u64Checked (2 ^ 16 - 1)
  let total ← U64.ofNat? indices.size site
  require (U64.zero < total) s!"{site}: total > 0"
  let effectiveBalances ← indices.mapM fun i => do
    pure (← state.validators.get i.toNat site).effective_balance
  let maxEb ← u64Checked P.MAX_EFFECTIVE_BALANCE_ELECTRA
  let sixteen ← u64Checked 16
  let two ← u64Checked 2
  let rec loop (fuel : Nat) (i : U64) (randomBytes : Bytes) (acc : Array ValidatorIndex) :
      Fallible (Array ValidatorIndex) := do
    match fuel with
    | 0 => throw (.assert s!"{site}: loop bound")
    | fuel + 1 =>
      if acc.size ≥ size then return acc
      let offset := (← (← i.mod? sixteen site).mul? two site).toNat
      let randomBytes ← if offset == 0 then do
          pure (hashBytes (seed.toBytes ++ uintToBytes 8 (← i.div? sixteen site).toNat))
        else pure randomBytes
      let next ← i.mod? total site
      let next ← if shuffleIndices then computeShuffledIndex P next total seed else pure next
      let weight ← (← getAt effectiveBalances next.toNat site).mul? maxRandomValue site
      let randomValue ← bytesToUint64 ((randomBytes.drop offset).take 2)
      let threshold ← maxEb.mul? randomValue site
      let acc ← if threshold ≤ weight then do pure (acc.push (← getAt indices next.toNat site))
        else pure acc
      loop fuel (← i.add? U64.one site) randomBytes acc
  loop samplingFuel U64.zero [] #[]

/-- `compute_proposer_indices(state, epoch, seed, indices)` (Gloas, :1240): one balance-weighted
draw of size 1, with shuffling, per slot seed. The seeds are built in full first. -/
def computeProposerIndices (state : BeaconState P) (epoch : Epoch) (seed : Bytes32)
    (indices : Array ValidatorIndex) : Fallible (Array ValidatorIndex) := do
  let site := "compute_proposer_indices"
  let startSlot ← computeStartSlotAtEpoch P epoch
  let seeds ← (List.range P.SLOTS_PER_EPOCH).mapM fun i => do
    let s ← U64.add? startSlot (← U64.ofNat? i "Slot") site
    pure (hash (seed.toBytes ++ uintToBytes 8 s.toNat))
  let mut out := #[]
  for sd in seeds do
    let selected ← computeBalanceWeightedSelection state indices sd 1 true
    out := out.push (← getAt selected 0 site)
  pure out

/-- `get_beacon_proposer_indices(state, epoch)` (Gloas, :1294, EIP-8045): the active validators
that are not slashed. -/
def getBeaconProposerIndices (state : BeaconState P) (epoch : Epoch) :
    Fallible (Array ValidatorIndex) := do
  let site := "get_beacon_proposer_indices"
  let active ← getActiveValidatorIndices state epoch
  let indices ← active.filterM fun i => do
    pure !(← state.validators.get i.toNat site).slashed
  let seed ← getSeed state epoch DOMAIN_BEACON_PROPOSER
  computeProposerIndices state epoch seed indices

/-- `get_beacon_proposer_index` (Fulu, unchanged in Gloas): `state.proposer_lookahead[state.slot
% SLOTS_PER_EPOCH]`. -/
def getBeaconProposerIndex (state : BeaconState P) : Fallible ValidatorIndex := do
  let s ← U64.mod? state.slot (← u64Checked P.SLOTS_PER_EPOCH) "get_beacon_proposer_index"
  state.proposer_lookahead.get s.toNat "get_beacon_proposer_index"

/-- `compute_ptc(state, slot)` (Gloas, :1266): the slot's committees concatenated in order, then
`PTC_SIZE` balance-weighted draws without shuffling. -/
def computePtc (state : BeaconState P) (slot : Slot) : Fallible (PayloadTimelinessCommittee P) := do
  let site := "compute_ptc"
  let epoch ← computeEpochAtSlot P slot
  let seed := hash ((← getSeed state epoch DOMAIN_PTC_ATTESTER).toBytes ++ uintToBytes 8 slot.toNat)
  let committeesPerSlot ← getCommitteeCountPerSlot state epoch
  let mut indices : Array ValidatorIndex := #[]
  for i in [0:committeesPerSlot.toNat] do
    indices := indices ++ (← getBeaconCommittee state slot (← U64.ofNat? i "CommitteeIndex"))
  Ssz.Vector.ofArray (← computeBalanceWeightedSelection state indices seed P.PTC_SIZE false) site

/-- `get_ptc(state, slot)` (Gloas, :1392): the cached committee from `state.ptc_window`. -/
def getPtc (cfg : Config) (state : BeaconState P) (slot : Slot) :
    Fallible (PayloadTimelinessCommittee P) := do
  let site := "get_ptc"
  let epoch ← computeEpochAtSlot P slot
  require (decide (epoch.toNat ≥ cfg.GLOAS_FORK_EPOCH)) s!"{site}: epoch >= GLOAS_FORK_EPOCH"
  let stateEpoch ← getCurrentEpoch state
  let spe ← u64Checked P.SLOTS_PER_EPOCH
  let inEpoch ← slot.mod? spe site
  if epoch < stateEpoch then
    require ((← epoch.add? U64.one site) == stateEpoch) s!"{site}: epoch + 1 == state_epoch"
    state.ptc_window.get inEpoch.toNat site
  else
    require (epoch ≤ (← stateEpoch.add? (← u64Checked P.MIN_SEED_LOOKAHEAD) site))
      s!"{site}: epoch <= state_epoch + MIN_SEED_LOOKAHEAD"
    let offset ← (← (← epoch.sub? stateEpoch site).add? U64.one site).mul? spe site
    state.ptc_window.get (← offset.add? inEpoch site).toNat site

/-! ## Balances and churn -/

/-- `get_total_balance` (phase0): `Gwei(max(EFFECTIVE_BALANCE_INCREMENT, sum(...)))` over the
distinct indices, with `uint64` addition. -/
def getTotalBalance (state : BeaconState P) (indices : Array ValidatorIndex) : Fallible Gwei := do
  let distinct := indices.toList.eraseDups
  let mut total := U64.zero
  for i in distinct do
    let v ← state.validators.get i.toNat "get_total_balance"
    total ← U64.add? total v.effective_balance "get_total_balance"
  let inc ← u64Checked P.EFFECTIVE_BALANCE_INCREMENT
  pure (if inc < total then total else inc)

/-- `get_total_active_balance` (phase0). -/
def getTotalActiveBalance (state : BeaconState P) : Fallible Gwei := do
  getTotalBalance state (← getActiveValidatorIndices state (← getCurrentEpoch state))

/-- `churn - churn % EFFECTIVE_BALANCE_INCREMENT` (`uint64`). -/
def roundToIncrement (churn : Gwei) (site : String) : Fallible Gwei := do
  churn.sub? (← churn.mod? (← u64Checked P.EFFECTIVE_BALANCE_INCREMENT) site) site

/-- `get_activation_churn_limit(state)` (Gloas, :1445, EIP-8061): the exit churn capped at
`MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS`. -/
def getActivationChurnLimit (cfg : Config) (state : BeaconState P) : Fallible Gwei := do
  let site := "get_activation_churn_limit"
  let q ← (← getTotalActiveBalance state).div? (← u64Checked cfg.CHURN_LIMIT_QUOTIENT_GLOAS) site
  let minC ← u64Checked cfg.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
  let churn ← roundToIncrement (P := P) (if q < minC then minC else q) site
  let maxC ← u64Checked cfg.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS
  pure (if churn < maxC then churn else maxC)

/-- `get_exit_churn_limit(state)` (Gloas, :1461, EIP-8061): uncapped. -/
def getExitChurnLimit (cfg : Config) (state : BeaconState P) : Fallible Gwei := do
  let site := "get_exit_churn_limit"
  let q ← (← getTotalActiveBalance state).div? (← u64Checked cfg.CHURN_LIMIT_QUOTIENT_GLOAS) site
  let minC ← u64Checked cfg.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
  roundToIncrement (P := P) (if q < minC then minC else q) site

/-- `get_consolidation_churn_limit(state)` (Gloas, :1479): `total_active //
CONSOLIDATION_CHURN_LIMIT_QUOTIENT`, rounded down to an increment. -/
def getConsolidationChurnLimit (cfg : Config) (state : BeaconState P) : Fallible Gwei := do
  let site := "get_consolidation_churn_limit"
  let churn ← (← getTotalActiveBalance state).div? (← u64Checked cfg.CONSOLIDATION_CHURN_LIMIT_QUOTIENT) site
  roundToIncrement (P := P) churn site

/-- `get_builder_payment_quorum_threshold(state)` (Gloas, :1433). -/
def getBuilderPaymentQuorumThreshold (state : BeaconState P) : Fallible Gwei := do
  let site := "get_builder_payment_quorum_threshold"
  let perSlot ← (← getTotalActiveBalance state).div? (← u64Checked P.SLOTS_PER_EPOCH) site
  let quorum ← perSlot.mul? (← u64Checked BUILDER_PAYMENT_THRESHOLD_NUMERATOR) site
  quorum.div? (← u64Checked BUILDER_PAYMENT_THRESHOLD_DENOMINATOR) site

/-- `get_pending_balance_to_withdraw` (Electra), over the Gloas state. -/
def getPendingBalanceToWithdraw (state : BeaconState P) (index : ValidatorIndex) : Fallible Gwei :=
  state.pending_partial_withdrawals.toArray.foldlM (fun acc w =>
    if w.validator_index == index then U64.add? acc w.amount "get_pending_balance_to_withdraw"
    else pure acc) U64.zero

/-- `get_pending_balance_to_withdraw_for_builder(state, builder_index)` (Gloas): the builder's
pending withdrawals, then its pending payments (`Gwei` addition). -/
def getPendingBalanceToWithdrawForBuilder (state : BeaconState P) (builderIndex : BuilderIndex) :
    Fallible Gwei := do
  let site := "get_pending_balance_to_withdraw_for_builder"
  let acc ← state.builder_pending_withdrawals.toArray.foldlM (fun acc w =>
    if w.builder_index == builderIndex then acc.add? w.amount site else pure acc) U64.zero
  state.builder_pending_payments.toArray.foldlM (fun acc p =>
    if p.withdrawal.builder_index == builderIndex then acc.add? p.withdrawal.amount site
    else pure acc) acc

/-! ## Block roots -/

/-- `get_block_root_at_slot` (phase0). -/
def getBlockRootAtSlot (state : BeaconState P) (slot : Slot) : Fallible Root := do
  require (slot < state.slot) "get_block_root_at_slot: slot range"
  let upper ← U64.add? slot (← u64Checked P.SLOTS_PER_HISTORICAL_ROOT) "get_block_root_at_slot"
  require (state.slot ≤ upper) "get_block_root_at_slot: slot range"
  let i ← U64.mod? slot (← u64Checked P.SLOTS_PER_HISTORICAL_ROOT) "get_block_root_at_slot"
  state.block_roots.get i.toNat "get_block_root_at_slot"

/-- `get_block_root` (phase0). -/
def getBlockRoot (state : BeaconState P) (epoch : Epoch) : Fallible Root := do
  getBlockRootAtSlot state (← computeStartSlotAtEpoch P epoch)

end Gloas
end JauneConsensus
