import JauneConsensus.Containers
import JauneConsensus.Config
import JauneConsensus.Helpers
import JauneConsensus.Shuffle

/-!
# Beacon-state accessors, predicates and mutators (Deneb to Fulu)

Transcribed from `ethereum/consensus-specs` `v1.6.1`, `specs/{phase0,altair,capella,electra,
fulu}/beacon-chain.md`. Each definition cites its pyspec function and keeps its operation order;
where a fork modified a function, one definition branches on the fork `f` and cites both versions.

Conventions (goal outcome O5):
* typed `uint64` arithmetic (`Epoch`, `Gwei`, `ValidatorIndex`, `uint64(...)`) goes through the
  checked `U64` operations and rejects exactly where remerkleable raises;
* Python `int` arithmetic (`len(...)`, `sum(...)` before a cast, loop counters) is `Nat`, and the
  cast back (`uint64(...)`, `Gwei(...)`) is `U64.ofNat?`, which rejects when out of range;
* `seq[i]` is `getAt` (or the `SszList`/`SszVector` operations below), rejecting with
  `Reject.index`; there is no defaulted read;
* a fork-gated state field (`Gated`) is read and written through `Gated.read`/`Gated.write`,
  which reject before the field's fork (unreachable in the Electra and Fulu transitions);
* pyspec's unbounded rejection-sampling loops (`compute_proposer_index`,
  `get_next_sync_committee_indices`) run on `SAMPLING_FUEL` iterations and reject with
  `Reject.assert` if it is exhausted, where pyspec would keep drawing. This is a residual
  divergence, bounded in probability: see `SAMPLING_FUEL`.

Configuration values are the runtime `Config` (`cfg`); preset values are the `Preset` `P` that
also indexes the state's types.
-/

namespace JauneConsensus
open Jaune (Bytes B256)

/-! ## Collection and gated-field operations -/

namespace SszList
variable {α : Type} {n : Nat}

/-- `xs[i]`, rejecting out of range. -/
@[inline] def get (xs : SszList α n) (i : Nat) (site : String) : M α := getAt xs.toArray i site

/-- `xs[i] = v`, rejecting out of range. -/
def set (xs : SszList α n) (i : Nat) (v : α) (site : String) : M (SszList α n) :=
  if h : i < xs.toArray.size then
    pure ⟨xs.toArray.set i v h, by simpa using xs.size_le⟩
  else throw (.index site i xs.toArray.size)

/-- `xs[i] = g(xs[i])`. -/
def modify (xs : SszList α n) (i : Nat) (g : α → M α) (site : String) : M (SszList α n) := do
  let v ← xs.get i site
  xs.set i (← g v) site

/-- `xs.append(v)`, rejecting past the limit (remerkleable raises). -/
def push (xs : SszList α n) (v : α) (site : String) : M (SszList α n) :=
  if h : xs.toArray.size + 1 ≤ n then pure ⟨xs.toArray.push v, by simpa using h⟩
  else throw (.limit site n (xs.toArray.size + 1))

/-- `len(xs)`. -/
@[inline] def length (xs : SszList α n) : Nat := xs.toArray.size

/-- The empty list. -/
def empty : SszList α n := ⟨#[], Nat.zero_le _⟩

/-- A list from an array, rejecting past the limit. -/
def ofArray (xs : Array α) (site : String) : M (SszList α n) :=
  if h : xs.size ≤ n then pure ⟨xs, h⟩ else throw (.limit site n xs.size)

end SszList

namespace SszVector
variable {α : Type} {n : Nat}

/-- `xs[i]`, rejecting out of range. -/
@[inline] def get (xs : SszVector α n) (i : Nat) (site : String) : M α := getAt xs.toArray i site

/-- `xs[i] = v`, rejecting out of range. -/
def set (xs : SszVector α n) (i : Nat) (v : α) (site : String) : M (SszVector α n) :=
  if h : i < xs.toArray.size then
    pure ⟨xs.toArray.set i v h, by simpa using xs.size_eq⟩
  else throw (.index site i xs.toArray.size)

/-- A vector from an array of exactly `n` elements. -/
def ofArray (xs : Array α) (site : String) : M (SszVector α n) :=
  if h : xs.size = n then pure ⟨xs, h⟩ else throw (.assert site)

end SszVector

namespace Gated
variable {α : Type}

/-- Read a fork-gated field; rejects before the field's fork. -/
def read : {c : Bool} → Gated c α → (site : String) → M α
  | true, x, _ => pure x
  | false, _, site => throw (.assert s!"{site}: field absent at this fork")

/-- Write a fork-gated field; rejects before the field's fork. -/
def write : (c : Bool) → α → (site : String) → M (Gated c α)
  | true, x, _ => pure x
  | false, _, site => throw (.assert s!"{site}: field absent at this fork")

/-- Read a gated field given the fork fact (`h : f.atLeast g = true`): no rejection path. -/
def get : {c : Bool} → c = true → Gated c α → α
  | true, _, x => x

/-- Build a gated field value given the fork fact. -/
def mk : {c : Bool} → c = true → α → Gated c α
  | true, _, x => x

/-- Update a gated field given the fork fact. -/
def modify {c : Bool} (h : c = true) (g : α → α) (x : Gated c α) : Gated c α :=
  mk h (g (get h x))

theorem get_mk {c : Bool} (h : c = true) (a : α) : get h (mk h a) = a := by
  cases c with
  | true => rfl
  | false => cases h

end Gated

/-! ### Per-field accessors for the fork-gated state fields

Usage pattern. Code that is generic in the fork reads and writes Electra and Fulu state fields
through these `M`-valued accessors (`state.earliestExitEpoch`, `state.setEarliestExitEpoch v`,
...), which reject only before the field's fork, so no caller specialises per fork. Code that
already holds the fork fact (`h : f.atLeast .electra = true`) can use `Gated.get h` /
`Gated.mk h` directly, with no rejection path. -/

namespace BeaconState
variable {P : Preset} {f : CFork}

def depositRequestsStartIndex (s : BeaconState P f) : M U64 :=
  Gated.read s.deposit_requests_start_index "deposit_requests_start_index"
def depositBalanceToConsume (s : BeaconState P f) : M Gwei :=
  Gated.read s.deposit_balance_to_consume "deposit_balance_to_consume"
def exitBalanceToConsume (s : BeaconState P f) : M Gwei :=
  Gated.read s.exit_balance_to_consume "exit_balance_to_consume"
def earliestExitEpoch (s : BeaconState P f) : M Epoch :=
  Gated.read s.earliest_exit_epoch "earliest_exit_epoch"
def consolidationBalanceToConsume (s : BeaconState P f) : M Gwei :=
  Gated.read s.consolidation_balance_to_consume "consolidation_balance_to_consume"
def earliestConsolidationEpoch (s : BeaconState P f) : M Epoch :=
  Gated.read s.earliest_consolidation_epoch "earliest_consolidation_epoch"
def pendingDeposits (s : BeaconState P f) : M (SszList PendingDeposit P.PENDING_DEPOSITS_LIMIT) :=
  Gated.read s.pending_deposits "pending_deposits"
def pendingPartialWithdrawals (s : BeaconState P f) :
    M (SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT) :=
  Gated.read s.pending_partial_withdrawals "pending_partial_withdrawals"
def pendingConsolidations (s : BeaconState P f) :
    M (SszList PendingConsolidation P.PENDING_CONSOLIDATIONS_LIMIT) :=
  Gated.read s.pending_consolidations "pending_consolidations"
def proposerLookahead (s : BeaconState P f) :
    M (SszVector ValidatorIndex ((P.MIN_SEED_LOOKAHEAD + 1) * P.SLOTS_PER_EPOCH)) :=
  Gated.read s.proposer_lookahead "proposer_lookahead"

def setDepositRequestsStartIndex (s : BeaconState P f) (v : U64) : M (BeaconState P f) := do
  pure { s with deposit_requests_start_index := ← Gated.write _ v "deposit_requests_start_index" }
def setDepositBalanceToConsume (s : BeaconState P f) (v : Gwei) : M (BeaconState P f) := do
  pure { s with deposit_balance_to_consume := ← Gated.write _ v "deposit_balance_to_consume" }
def setExitBalanceToConsume (s : BeaconState P f) (v : Gwei) : M (BeaconState P f) := do
  pure { s with exit_balance_to_consume := ← Gated.write _ v "exit_balance_to_consume" }
def setEarliestExitEpoch (s : BeaconState P f) (v : Epoch) : M (BeaconState P f) := do
  pure { s with earliest_exit_epoch := ← Gated.write _ v "earliest_exit_epoch" }
def setConsolidationBalanceToConsume (s : BeaconState P f) (v : Gwei) : M (BeaconState P f) := do
  pure { s with consolidation_balance_to_consume :=
    ← Gated.write _ v "consolidation_balance_to_consume" }
def setEarliestConsolidationEpoch (s : BeaconState P f) (v : Epoch) : M (BeaconState P f) := do
  pure { s with earliest_consolidation_epoch := ← Gated.write _ v "earliest_consolidation_epoch" }
def setPendingDeposits (s : BeaconState P f) (v : SszList PendingDeposit P.PENDING_DEPOSITS_LIMIT) :
    M (BeaconState P f) := do
  pure { s with pending_deposits := ← Gated.write _ v "pending_deposits" }
def setPendingPartialWithdrawals (s : BeaconState P f)
    (v : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT) :
    M (BeaconState P f) := do
  pure { s with pending_partial_withdrawals := ← Gated.write _ v "pending_partial_withdrawals" }
def setPendingConsolidations (s : BeaconState P f)
    (v : SszList PendingConsolidation P.PENDING_CONSOLIDATIONS_LIMIT) : M (BeaconState P f) := do
  pure { s with pending_consolidations := ← Gated.write _ v "pending_consolidations" }
def setProposerLookahead (s : BeaconState P f)
    (v : SszVector ValidatorIndex ((P.MIN_SEED_LOOKAHEAD + 1) * P.SLOTS_PER_EPOCH)) :
    M (BeaconState P f) := do
  pure { s with proposer_lookahead := ← Gated.write _ v "proposer_lookahead" }

end BeaconState

/-- `uint64(n)` of a configuration or preset constant (rejects if it does not fit). -/
@[inline] def c64 (n : Nat) : M U64 := U64.ofNat? n "uint64 constant"

/-! ## Constants -/

/-- `DOMAIN_BEACON_PROPOSER` (`specs/phase0/beacon-chain.md`, "Domain types"). -/
def DOMAIN_BEACON_PROPOSER : Bytes := [0x00, 0x00, 0x00, 0x00]
/-- `DOMAIN_BEACON_ATTESTER`. -/
def DOMAIN_BEACON_ATTESTER : Bytes := [0x01, 0x00, 0x00, 0x00]
/-- `PROPOSER_WEIGHT` (`specs/altair/beacon-chain.md`). -/
def PROPOSER_WEIGHT : Nat := 8
/-- `WEIGHT_DENOMINATOR`. -/
def WEIGHT_DENOMINATOR : Nat := 64
/-- `TIMELY_SOURCE_FLAG_INDEX` (`specs/altair/beacon-chain.md`). -/
def TIMELY_SOURCE_FLAG_INDEX : Nat := 0
/-- `TIMELY_TARGET_FLAG_INDEX`. -/
def TIMELY_TARGET_FLAG_INDEX : Nat := 1
/-- `TIMELY_HEAD_FLAG_INDEX`. -/
def TIMELY_HEAD_FLAG_INDEX : Nat := 2
/-- `PARTICIPATION_FLAG_WEIGHTS = [TIMELY_SOURCE_WEIGHT, TIMELY_TARGET_WEIGHT, TIMELY_HEAD_WEIGHT]`
`= [uint64(14), uint64(26), uint64(14)]`. -/
def PARTICIPATION_FLAG_WEIGHTS : List Nat := [14, 26, 14]
/-- `SYNC_REWARD_WEIGHT = uint64(2)`. -/
def SYNC_REWARD_WEIGHT : Nat := 2
/-- `bls.G2_POINT_AT_INFINITY` (`specs/altair/bls.md`). -/
def G2_POINT_AT_INFINITY_BYTES : Array UInt8 := #[0xc0] ++ Array.replicate 95 0

/-- `bls.G2_POINT_AT_INFINITY` as a `BLSSignature`. -/
def g2PointAtInfinitySignature : BLSSignature := ⟨G2_POINT_AT_INFINITY_BYTES, by decide⟩

variable {P : Preset} {f : CFork}

/-! ## Predicates (`specs/*/beacon-chain.md`, "Predicates") -/

/-- `is_active_validator` (phase0). -/
def isActiveValidator (v : Validator) (epoch : Epoch) : Bool :=
  v.activation_epoch ≤ epoch && epoch < v.exit_epoch

/-- `is_slashable_validator` (phase0). -/
def isSlashableValidator (v : Validator) (epoch : Epoch) : Bool :=
  !v.slashed && (v.activation_epoch ≤ epoch && epoch < v.withdrawable_epoch)

/-- `is_slashable_attestation_data` (phase0). -/
def isSlashableAttestationData (d1 d2 : AttestationData) : Bool :=
  (!(d1 == d2) && d1.target.epoch == d2.target.epoch) ||
  (d1.source.epoch < d2.source.epoch && d2.target.epoch < d1.target.epoch)

/-- `is_eligible_for_activation_queue` (Electra: `effective_balance >= MIN_ACTIVATION_BALANCE`;
before Electra, phase0: `== MAX_EFFECTIVE_BALANCE`). -/
def isEligibleForActivationQueue (P : Preset) (f : CFork) (v : Validator) : Bool :=
  v.activation_eligibility_epoch == FAR_FUTURE_EPOCH &&
    (if f.atLeast .electra then decide (v.effective_balance.toNat ≥ P.MIN_ACTIVATION_BALANCE)
     else v.effective_balance.toNat == P.MAX_EFFECTIVE_BALANCE)

/-- `is_eligible_for_activation` (phase0). -/
def isEligibleForActivation (state : BeaconState P f) (v : Validator) : Bool :=
  v.activation_eligibility_epoch ≤ state.finalized_checkpoint.epoch &&
    v.activation_epoch == FAR_FUTURE_EPOCH

/-- The first byte of a withdrawal credential (`withdrawal_credentials[:1]`). -/
def credentialPrefix (wc : Bytes32) : UInt8 :=
  match wc.toBytes with
  | b :: _ => b
  | [] => 0  -- unreachable: `B256.toBytes` has 32 bytes

/-- `has_eth1_withdrawal_credential` (Capella). -/
def hasEth1WithdrawalCredential (v : Validator) : Bool :=
  credentialPrefix v.withdrawal_credentials == ETH1_ADDRESS_WITHDRAWAL_PREFIX

/-- `has_compounding_withdrawal_credential` (Electra). -/
def hasCompoundingWithdrawalCredential (v : Validator) : Bool :=
  isCompoundingWithdrawalCredential v.withdrawal_credentials

/-- `has_execution_withdrawal_credential` (Electra). -/
def hasExecutionWithdrawalCredential (v : Validator) : Bool :=
  hasEth1WithdrawalCredential v || hasCompoundingWithdrawalCredential v

/-- `get_max_effective_balance` (Electra). -/
def getMaxEffectiveBalance (P : Preset) (v : Validator) : Nat :=
  if hasCompoundingWithdrawalCredential v then P.MAX_EFFECTIVE_BALANCE_ELECTRA
  else P.MIN_ACTIVATION_BALANCE

/-- `is_fully_withdrawable_validator` (Electra; Capella checked the eth1 credential only). -/
def isFullyWithdrawableValidator (f : CFork) (v : Validator) (balance : Gwei) (epoch : Epoch) :
    Bool :=
  (if f.atLeast .electra then hasExecutionWithdrawalCredential v
   else hasEth1WithdrawalCredential v) &&
    v.withdrawable_epoch ≤ epoch && balance.toNat > 0

/-- `is_partially_withdrawable_validator` (Electra; Capella used `MAX_EFFECTIVE_BALANCE` and the
eth1 credential). -/
def isPartiallyWithdrawableValidator (P : Preset) (f : CFork) (v : Validator) (balance : Gwei) :
    Bool :=
  if f.atLeast .electra then
    let maxEb := getMaxEffectiveBalance P v
    hasExecutionWithdrawalCredential v && v.effective_balance.toNat == maxEb &&
      balance.toNat > maxEb
  else
    hasEth1WithdrawalCredential v && v.effective_balance.toNat == P.MAX_EFFECTIVE_BALANCE &&
      balance.toNat > P.MAX_EFFECTIVE_BALANCE

/-! ## Accessors -/

/-- `get_current_epoch` (phase0). -/
def getCurrentEpoch (state : BeaconState P f) : M Epoch := computeEpochAtSlot P state.slot

/-- `get_previous_epoch` (phase0). -/
def getPreviousEpoch (state : BeaconState P f) : M Epoch := do
  let current ← getCurrentEpoch state
  if current == GENESIS_EPOCH then pure GENESIS_EPOCH
  else U64.sub? current U64.one "get_previous_epoch"

/-- `get_active_validator_indices` (phase0). -/
def getActiveValidatorIndices (state : BeaconState P f) (epoch : Epoch) : M (Array ValidatorIndex) := do
  let mut out := #[]
  let mut i := 0
  for v in state.validators.toArray do
    if isActiveValidator v epoch then out := out.push (← U64.ofNat? i "ValidatorIndex")
    i := i + 1
  pure out

/-- `get_randao_mix` (phase0). -/
def getRandaoMix (state : BeaconState P f) (epoch : Epoch) : M Bytes32 := do
  let m ← U64.mod? epoch (← c64 P.EPOCHS_PER_HISTORICAL_VECTOR) "get_randao_mix"
  state.randao_mixes.get m.toNat "get_randao_mix"

/-- `get_seed` (phase0): `hash(domain_type + uint_to_bytes(epoch) + mix)` with the mix of
`epoch + EPOCHS_PER_HISTORICAL_VECTOR - MIN_SEED_LOOKAHEAD - 1`. -/
def getSeed (state : BeaconState P f) (epoch : Epoch) (domainType : Bytes) : M Bytes32 := do
  let e ← U64.add? epoch (← c64 P.EPOCHS_PER_HISTORICAL_VECTOR) "get_seed"
  let e ← U64.sub? e (← c64 P.MIN_SEED_LOOKAHEAD) "get_seed"
  let e ← U64.sub? e U64.one "get_seed"
  let mix ← getRandaoMix state e
  pure (hash (domainType ++ uintToBytes 8 epoch.toNat ++ mix.toBytes))

/-- `get_committee_count_per_slot` (phase0). -/
def getCommitteeCountPerSlot (state : BeaconState P f) (epoch : Epoch) : M U64 := do
  let n := (← getActiveValidatorIndices state epoch).size
  let perSlot ← U64.div? (← U64.ofNat? n "uint64(len)") (← c64 P.SLOTS_PER_EPOCH) "committee count"
  let perSlot ← U64.div? perSlot (← c64 P.TARGET_COMMITTEE_SIZE) "committee count"
  let maxC ← c64 P.MAX_COMMITTEES_PER_SLOT
  let m := if perSlot < maxC then perSlot else maxC
  pure (if U64.one < m then m else U64.one)

/-- `compute_committee` (phase0). `start` and `end` are computed in `uint64` as pyspec does
(`len(indices) * index` is a Python `int` times a `uint64`, which remerkleable types `uint64`). -/
def computeCommittee (P : Preset) (indices : Array ValidatorIndex) (seed : Bytes32)
    (index count : U64) : M (Array ValidatorIndex) := do
  let len ← U64.ofNat? indices.size "uint64(len(indices))"
  let start ← U64.div? (← U64.mul? len index "compute_committee") count "compute_committee"
  let stop ← U64.div? (← U64.mul? len (← U64.add? index U64.one "compute_committee")
    "compute_committee") count "compute_committee"
  let mut out := #[]
  for i in [start.toNat:stop.toNat] do
    let s ← computeShuffledIndex P (← U64.ofNat? i "uint64(i)") len seed
    out := out.push (← getAt indices s.toNat "compute_committee")
  pure out

/-- `get_beacon_committee` (phase0). -/
def getBeaconCommittee (state : BeaconState P f) (slot : Slot) (index : CommitteeIndex) :
    M (Array ValidatorIndex) := do
  let epoch ← computeEpochAtSlot P slot
  let committeesPerSlot ← getCommitteeCountPerSlot state epoch
  let spe ← c64 P.SLOTS_PER_EPOCH
  let slotInEpoch ← U64.mod? slot spe "get_beacon_committee"
  let idx ← U64.add? (← U64.mul? slotInEpoch committeesPerSlot "get_beacon_committee") index
    "get_beacon_committee"
  let count ← U64.mul? committeesPerSlot spe "get_beacon_committee"
  computeCommittee P (← getActiveValidatorIndices state epoch)
    (← getSeed state epoch DOMAIN_BEACON_ATTESTER) idx count

/-- The iteration bound of the rejection-sampling loops (`compute_proposer_index`, Altair and
Electra `get_next_sync_committee_indices`), which are unbounded `while` loops in pyspec. The
worst case for every loop is all candidates at effective balance 0, where a draw accepts only
when its random value is 0: probability `2^-16` per draw with Electra's 16-bit values (`2^-8`
with one byte before Electra). Treating the hash as a random oracle, `2^28` draws expect `4096`
acceptances; the probability of fewer than one (`compute_proposer_index`) is below `e^-4096`,
and of fewer than `SYNC_COMMITTEE_SIZE = 512` below `e^-1568` (Chernoff). Only then does the
model reject where pyspec would continue. The bound costs nothing on ordinary inputs: every loop
returns at its first or 512th acceptance. -/
def SAMPLING_FUEL : Nat := 2 ^ 28

/-- `compute_proposer_index`: Electra samples a 16-bit random value against
`MAX_EFFECTIVE_BALANCE_ELECTRA` (`specs/electra/beacon-chain.md`); before Electra a random byte
against `MAX_EFFECTIVE_BALANCE` (`specs/phase0/beacon-chain.md`). -/
def computeProposerIndex (state : BeaconState P f) (indices : Array ValidatorIndex)
    (seed : Bytes32) : M ValidatorIndex := do
  require (indices.size > 0) "compute_proposer_index: len(indices) > 0"
  let total ← U64.ofNat? indices.size "uint64(len(indices))"
  let rec loop : Nat → U64 → M ValidatorIndex
    | 0, _ => throw (.assert "compute_proposer_index: iteration fuel exhausted")
    | fuel + 1, i => do
      let candidate ← getAt indices
        (← computeShuffledIndex P (← U64.mod? i total "compute_proposer_index") total seed).toNat
        "compute_proposer_index"
      let eb := (← state.validators.get candidate.toNat "compute_proposer_index").effective_balance
      let accept ←
        if f.atLeast .electra then do
          let maxRandom := 2 ^ 16 - 1
          let randomBytes := (hash (seed.toBytes ++ uintToBytes 8 (i.toNat / 16))).toBytes
          let offset := i.toNat % 16 * 2
          let randomValue ← bytesToUint64 ((randomBytes.drop offset).take 2)
          let lhs ← U64.mul? eb (← c64 maxRandom) "compute_proposer_index"
          let rhs ← U64.mul? (← c64 P.MAX_EFFECTIVE_BALANCE_ELECTRA) randomValue
            "compute_proposer_index"
          pure (decide (rhs ≤ lhs))
        else do
          let maxRandom := 2 ^ 8 - 1
          let randomBytes := (hash (seed.toBytes ++ uintToBytes 8 (i.toNat / 32))).toBytes
          let randomByte ← getAt randomBytes.toArray (i.toNat % 32) "compute_proposer_index"
          let lhs ← U64.mul? eb (← c64 maxRandom) "compute_proposer_index"
          let rhs ← U64.mul? (← c64 P.MAX_EFFECTIVE_BALANCE) (← c64 randomByte.toNat)
            "compute_proposer_index"
          pure (decide (rhs ≤ lhs))
      if accept then pure candidate
      else loop fuel (← U64.add? i U64.one "compute_proposer_index")
  loop SAMPLING_FUEL U64.zero

/-- `compute_proposer_indices` (Fulu). -/
def computeProposerIndices (state : BeaconState P f) (epoch : Epoch) (seed : Bytes32)
    (indices : Array ValidatorIndex) : M (Array ValidatorIndex) := do
  let startSlot ← computeStartSlotAtEpoch P epoch
  -- `seeds = [hash(seed + uint_to_bytes(Slot(start_slot + i))) for i in range(SLOTS_PER_EPOCH)]`
  -- is built in full before any `compute_proposer_index`
  let seeds ← (List.range P.SLOTS_PER_EPOCH).mapM fun i => do
    let s ← U64.add? startSlot (← U64.ofNat? i "Slot") "compute_proposer_indices"
    pure (hash (seed.toBytes ++ uintToBytes 8 s.toNat))
  let mut out := #[]
  for sd in seeds do
    out := out.push (← computeProposerIndex state indices sd)
  pure out

/-- `get_beacon_proposer_indices` (Fulu). -/
def getBeaconProposerIndices (state : BeaconState P f) (epoch : Epoch) :
    M (Array ValidatorIndex) := do
  let indices ← getActiveValidatorIndices state epoch
  let seed ← getSeed state epoch DOMAIN_BEACON_PROPOSER
  computeProposerIndices state epoch seed indices

/-- `initialize_proposer_lookahead` (`specs/fulu/fork.md`). -/
def initializeProposerLookahead (state : BeaconState P f) : M (Array ValidatorIndex) := do
  let current ← getCurrentEpoch state
  let mut out := #[]
  for i in [0:P.MIN_SEED_LOOKAHEAD + 1] do
    out := out ++ (← getBeaconProposerIndices state
      (← U64.add? current (← U64.ofNat? i "Epoch") "initialize_proposer_lookahead"))
  pure out

/-- `get_beacon_proposer_index`: Fulu reads `state.proposer_lookahead[state.slot %
SLOTS_PER_EPOCH]` (`specs/fulu/beacon-chain.md`); before Fulu it samples with the seed
`hash(get_seed(state, epoch, DOMAIN_BEACON_PROPOSER) + uint_to_bytes(state.slot))`
(`specs/phase0/beacon-chain.md`). -/
def getBeaconProposerIndex (state : BeaconState P f) : M ValidatorIndex := do
  if f.atLeast .fulu then
    let lookahead ← Gated.read state.proposer_lookahead "proposer_lookahead"
    let s ← U64.mod? state.slot (← c64 P.SLOTS_PER_EPOCH) "get_beacon_proposer_index"
    lookahead.get s.toNat "get_beacon_proposer_index"
  else
    let epoch ← getCurrentEpoch state
    let seed := hash ((← getSeed state epoch DOMAIN_BEACON_PROPOSER).toBytes ++
      uintToBytes 8 state.slot.toNat)
    computeProposerIndex state (← getActiveValidatorIndices state epoch) seed

/-- `get_total_balance` (phase0): `Gwei(max(EFFECTIVE_BALANCE_INCREMENT, sum(...)))`. The sum
runs over the distinct indices (pyspec passes a `Set`) of typed `Gwei` values, so it is `uint64`
addition. -/
def getTotalBalance (state : BeaconState P f) (indices : Array ValidatorIndex) : M Gwei := do
  let distinct := indices.toList.eraseDups
  let mut total := U64.zero
  for i in distinct do
    let v ← state.validators.get i.toNat "get_total_balance"
    total ← U64.add? total v.effective_balance "get_total_balance"
  let inc ← c64 P.EFFECTIVE_BALANCE_INCREMENT
  pure (if inc < total then total else inc)

/-- `get_total_active_balance` (phase0). -/
def getTotalActiveBalance (state : BeaconState P f) : M Gwei := do
  getTotalBalance state (← getActiveValidatorIndices state (← getCurrentEpoch state))

/-- `get_validator_churn_limit` (phase0). -/
def getValidatorChurnLimit (cfg : Config) (state : BeaconState P f) : M U64 := do
  let n := (← getActiveValidatorIndices state (← getCurrentEpoch state)).size
  let q ← U64.div? (← U64.ofNat? n "uint64(len)") (← c64 cfg.CHURN_LIMIT_QUOTIENT)
    "get_validator_churn_limit"
  let minC ← c64 cfg.MIN_PER_EPOCH_CHURN_LIMIT
  pure (if minC < q then q else minC)

/-- `get_balance_churn_limit` (Electra). -/
def getBalanceChurnLimit (cfg : Config) (state : BeaconState P f) : M Gwei := do
  let q ← U64.div? (← getTotalActiveBalance state) (← c64 cfg.CHURN_LIMIT_QUOTIENT)
    "get_balance_churn_limit"
  let minC ← c64 cfg.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
  let churn := if minC < q then q else minC
  U64.sub? churn (← U64.mod? churn (← c64 P.EFFECTIVE_BALANCE_INCREMENT) "get_balance_churn_limit")
    "get_balance_churn_limit"

/-- `get_activation_exit_churn_limit` (Electra). -/
def getActivationExitChurnLimit (cfg : Config) (state : BeaconState P f) : M Gwei := do
  let b ← getBalanceChurnLimit cfg state
  let maxC ← c64 cfg.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
  pure (if maxC < b then maxC else b)

/-- `get_consolidation_churn_limit` (Electra). -/
def getConsolidationChurnLimit (cfg : Config) (state : BeaconState P f) : M Gwei := do
  U64.sub? (← getBalanceChurnLimit cfg state) (← getActivationExitChurnLimit cfg state)
    "get_consolidation_churn_limit"

/-- `get_block_root_at_slot` (phase0). -/
def getBlockRootAtSlot (state : BeaconState P f) (slot : Slot) : M Root := do
  -- `assert slot < state.slot <= slot + SLOTS_PER_HISTORICAL_ROOT` chains left to right: the
  -- sum is formed only when the first comparison holds
  require (slot < state.slot) "get_block_root_at_slot: slot range"
  let upper ← U64.add? slot (← c64 P.SLOTS_PER_HISTORICAL_ROOT) "get_block_root_at_slot"
  require (state.slot ≤ upper) "get_block_root_at_slot: slot range"
  let i ← U64.mod? slot (← c64 P.SLOTS_PER_HISTORICAL_ROOT) "get_block_root_at_slot"
  state.block_roots.get i.toNat "get_block_root_at_slot"

/-- `get_block_root` (phase0). -/
def getBlockRoot (state : BeaconState P f) (epoch : Epoch) : M Root := do
  getBlockRootAtSlot state (← computeStartSlotAtEpoch P epoch)

/-- `get_committee_indices` (Electra). -/
def getCommitteeIndices {n : Nat} (bits : Bitvector n) : M (Array CommitteeIndex) := do
  let mut out := #[]
  let mut i := 0
  for b in bits.bits do
    if b then out := out.push (← U64.ofNat? i "CommitteeIndex")
    i := i + 1
  pure out

/-- `get_attesting_indices`: Electra walks the committees named by `committee_bits`, consuming
`aggregation_bits` committee by committee (`specs/electra/beacon-chain.md`); before Electra the
attestation names one committee, `data.index` (`specs/phase0/beacon-chain.md`). The result is
the set of indices, returned sorted and without duplicates. -/
def getAttestingIndices (state : BeaconState P f) (attestation : Attestation P f) :
    M (Array ValidatorIndex) := do
  let bits := attestation.aggregation_bits.bits
  let mut out : Array ValidatorIndex := #[]
  if f.atLeast .electra then
    let cbits ← Gated.read attestation.committee_bits "committee_bits"
    let mut offset := 0
    for ci in ← getCommitteeIndices cbits do
      let committee ← getBeaconCommittee state attestation.data.slot ci
      let mut i := 0
      for a in committee do
        if ← getAt bits (offset + i) "aggregation_bits" then out := out.push a
        i := i + 1
      offset := offset + committee.size
  else
    -- phase0 `get_attesting_indices` has no length check (that `assert` is in
    -- `process_attestation`); a short bitlist raises `IndexError` at `aggregation_bits[i]`
    let committee ← getBeaconCommittee state attestation.data.slot attestation.data.index
    let mut i := 0
    for a in committee do
      if ← getAt bits i "aggregation_bits" then out := out.push a
      i := i + 1
  pure ((out.qsort (· < ·)).toList.eraseDups.toArray)

/-- `get_indexed_attestation` (phase0): `attesting_indices = sorted(attesting_indices)`. -/
def getIndexedAttestation (state : BeaconState P f) (attestation : Attestation P f) :
    M (IndexedAttestation P f) := do
  let indices ← getAttestingIndices state attestation
  pure { attesting_indices := ← SszList.ofArray indices "IndexedAttestation.attesting_indices"
         data := attestation.data
         signature := attestation.signature }

/-- `get_pending_balance_to_withdraw` (Electra). The sum of typed `Gwei` amounts is `uint64`. -/
def getPendingBalanceToWithdraw (state : BeaconState P f) (index : ValidatorIndex) : M Gwei := do
  let pending ← Gated.read state.pending_partial_withdrawals "pending_partial_withdrawals"
  pending.toArray.foldlM (fun acc w =>
    if w.validator_index == index then U64.add? acc w.amount "get_pending_balance_to_withdraw"
    else pure acc) U64.zero

/-! ## Mutators -/

/-- `increase_balance` (phase0): `state.balances[index] += delta` (typed `Gwei`). -/
def increaseBalance (state : BeaconState P f) (index : ValidatorIndex) (delta : Gwei) :
    M (BeaconState P f) := do
  let balances ← state.balances.modify index.toNat
    (fun b => U64.add? b delta "increase_balance") "increase_balance"
  pure { state with balances }

/-- `decrease_balance` (phase0), with underflow protection. -/
def decreaseBalance (state : BeaconState P f) (index : ValidatorIndex) (delta : Gwei) :
    M (BeaconState P f) := do
  let balances ← state.balances.modify index.toNat
    (fun b => if b < delta then pure U64.zero else U64.sub? b delta "decrease_balance")
    "decrease_balance"
  pure { state with balances }

/-- `compute_exit_epoch_and_update_churn` (Electra). Returns the state and the exit epoch. -/
def computeExitEpochAndUpdateChurn (cfg : Config) (state : BeaconState P f) (exitBalance : Gwei) :
    M (BeaconState P f × Epoch) := do
  let stateEarliest ← Gated.read state.earliest_exit_epoch "earliest_exit_epoch"
  let activationExit ← computeActivationExitEpoch P (← getCurrentEpoch state)
  let mut earliest := if stateEarliest < activationExit then activationExit else stateEarliest
  let perEpochChurn ← getActivationExitChurnLimit cfg state
  let mut toConsume ←
    if stateEarliest < earliest then pure perEpochChurn
    else Gated.read state.exit_balance_to_consume "exit_balance_to_consume"
  if toConsume < exitBalance then
    let balanceToProcess ← U64.sub? exitBalance toConsume "compute_exit_epoch_and_update_churn"
    let additional ← U64.add? (← U64.div? (← U64.sub? balanceToProcess U64.one
      "compute_exit_epoch_and_update_churn") perEpochChurn "compute_exit_epoch_and_update_churn")
      U64.one "compute_exit_epoch_and_update_churn"
    earliest ← U64.add? earliest additional "compute_exit_epoch_and_update_churn"
    toConsume ← U64.add? toConsume (← U64.mul? additional perEpochChurn
      "compute_exit_epoch_and_update_churn") "compute_exit_epoch_and_update_churn"
  let remaining ← U64.sub? toConsume exitBalance "compute_exit_epoch_and_update_churn"
  let state := { state with
    exit_balance_to_consume := ← Gated.write _ remaining "exit_balance_to_consume"
    earliest_exit_epoch := ← Gated.write _ earliest "earliest_exit_epoch" }
  pure (state, earliest)

/-- `compute_consolidation_epoch_and_update_churn` (Electra). -/
def computeConsolidationEpochAndUpdateChurn (cfg : Config) (state : BeaconState P f)
    (consolidationBalance : Gwei) : M (BeaconState P f × Epoch) := do
  let stateEarliest ← Gated.read state.earliest_consolidation_epoch "earliest_consolidation_epoch"
  let activationExit ← computeActivationExitEpoch P (← getCurrentEpoch state)
  let mut earliest := if stateEarliest < activationExit then activationExit else stateEarliest
  let perEpochChurn ← getConsolidationChurnLimit cfg state
  let mut toConsume ←
    if stateEarliest < earliest then pure perEpochChurn
    else Gated.read state.consolidation_balance_to_consume "consolidation_balance_to_consume"
  if toConsume < consolidationBalance then
    let site := "compute_consolidation_epoch_and_update_churn"
    let balanceToProcess ← U64.sub? consolidationBalance toConsume site
    let additional ← U64.add? (← U64.div? (← U64.sub? balanceToProcess U64.one site)
      perEpochChurn site) U64.one site
    earliest ← U64.add? earliest additional site
    toConsume ← U64.add? toConsume (← U64.mul? additional perEpochChurn site) site
  let remaining ← U64.sub? toConsume consolidationBalance
    "compute_consolidation_epoch_and_update_churn"
  let state := { state with
    consolidation_balance_to_consume := ← Gated.write _ remaining "consolidation_balance_to_consume"
    earliest_consolidation_epoch := ← Gated.write _ earliest "earliest_consolidation_epoch" }
  pure (state, earliest)

/-- `initiate_validator_exit`: Electra computes the exit epoch from the balance churn
(`compute_exit_epoch_and_update_churn`, `specs/electra/beacon-chain.md`); before Electra from the
exit queue and `get_validator_churn_limit` (`specs/phase0/beacon-chain.md`). -/
def initiateValidatorExit (cfg : Config) (state : BeaconState P f) (index : ValidatorIndex) :
    M (BeaconState P f) := do
  let validator ← state.validators.get index.toNat "initiate_validator_exit"
  if validator.exit_epoch != FAR_FUTURE_EPOCH then return state
  let (state, exitQueueEpoch) ←
    if f.atLeast .electra then
      computeExitEpochAndUpdateChurn cfg state validator.effective_balance
    else do
      let activationExit ← computeActivationExitEpoch P (← getCurrentEpoch state)
      let mut q := activationExit
      for v in state.validators.toArray do
        if v.exit_epoch != FAR_FUTURE_EPOCH && q < v.exit_epoch then q := v.exit_epoch
      let churn := (state.validators.toArray.filter (·.exit_epoch == q)).size
      if churn ≥ (← getValidatorChurnLimit cfg state).toNat then
        q ← U64.add? q U64.one "initiate_validator_exit"
      pure (state, q)
  let withdrawable ← U64.add? exitQueueEpoch (← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY)
    "initiate_validator_exit"
  let validators ← state.validators.set index.toNat
    { validator with exit_epoch := exitQueueEpoch, withdrawable_epoch := withdrawable }
    "initiate_validator_exit"
  pure { state with validators }

/-- `slash_validator`: Electra uses `MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA` and
`WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA` (`specs/electra/beacon-chain.md`); Bellatrix to Deneb use
`MIN_SLASHING_PENALTY_QUOTIENT_BELLATRIX` and `WHISTLEBLOWER_REWARD_QUOTIENT`
(`specs/bellatrix/beacon-chain.md`). -/
def slashValidator (cfg : Config) (state : BeaconState P f) (slashedIndex : ValidatorIndex)
    (whistleblowerIndex : Option ValidatorIndex := none) : M (BeaconState P f) := do
  let site := "slash_validator"
  let epoch ← getCurrentEpoch state
  let state ← initiateValidatorExit cfg state slashedIndex
  let validator ← state.validators.get slashedIndex.toNat site
  let w ← U64.add? epoch (← c64 P.EPOCHS_PER_SLASHINGS_VECTOR) site
  let validator := { validator with
    slashed := true
    withdrawable_epoch := if validator.withdrawable_epoch < w then w else validator.withdrawable_epoch }
  let validators ← state.validators.set slashedIndex.toNat validator site
  let si ← U64.mod? epoch (← c64 P.EPOCHS_PER_SLASHINGS_VECTOR) site
  let old ← state.slashings.get si.toNat site
  let slashings ← state.slashings.set si.toNat (← U64.add? old validator.effective_balance site) site
  let state := { state with validators, slashings }
  let (penaltyQ, whistleQ) :=
    if f.atLeast .electra then
      (P.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA, P.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA)
    else (P.MIN_SLASHING_PENALTY_QUOTIENT_BELLATRIX, P.WHISTLEBLOWER_REWARD_QUOTIENT)
  let penalty ← U64.div? validator.effective_balance (← c64 penaltyQ) site
  let state ← decreaseBalance state slashedIndex penalty
  let proposerIndex ← getBeaconProposerIndex state
  let whistleblower := match whistleblowerIndex with
    | some w => w
    | none => proposerIndex
  let whistleblowerReward ← U64.div? validator.effective_balance (← c64 whistleQ) site
  let proposerReward ← U64.div? (← U64.mul? whistleblowerReward (← c64 PROPOSER_WEIGHT) site)
    (← c64 WEIGHT_DENOMINATOR) site
  let state ← increaseBalance state proposerIndex proposerReward
  increaseBalance state whistleblower (← U64.sub? whistleblowerReward proposerReward site)

/-- `queue_excess_active_balance` (Electra). -/
def queueExcessActiveBalance (state : BeaconState P f) (index : ValidatorIndex) :
    M (BeaconState P f) := do
  let site := "queue_excess_active_balance"
  let balance ← state.balances.get index.toNat site
  let minAct ← c64 P.MIN_ACTIVATION_BALANCE
  if minAct < balance then
    let excess ← U64.sub? balance minAct site
    let balances ← state.balances.set index.toNat minAct site
    let validator ← state.validators.get index.toNat site
    let pending ← Gated.read state.pending_deposits site
    let pending ← pending.push
      { pubkey := validator.pubkey
        withdrawal_credentials := validator.withdrawal_credentials
        amount := excess
        signature := g2PointAtInfinitySignature
        slot := GENESIS_SLOT } site
    pure { state with balances, pending_deposits := ← Gated.write _ pending site }
  else pure state

/-- `switch_to_compounding_validator` (Electra). -/
def switchToCompoundingValidator (state : BeaconState P f) (index : ValidatorIndex) :
    M (BeaconState P f) := do
  let site := "switch_to_compounding_validator"
  let validator ← state.validators.get index.toNat site
  let wc := Jaune.Bytes.toB256 (COMPOUNDING_WITHDRAWAL_PREFIX :: validator.withdrawal_credentials.toBytes.drop 1)
  let validators ← state.validators.set index.toNat { validator with withdrawal_credentials := wc } site
  queueExcessActiveBalance { state with validators } index

end JauneConsensus
