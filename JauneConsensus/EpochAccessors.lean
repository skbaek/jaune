import JauneConsensus.Accessors
import JauneConsensus.Signing
import JauneConsensus.Crypto.Boundary

/-!
# Accessors used by epoch processing

The epoch-only accessors of `ethereum/consensus-specs` `v1.6.1`: participation and rewards
(`specs/altair/beacon-chain.md`, with Bellatrix's inactivity quotient), the inactivity-leak test
(`specs/phase0/beacon-chain.md`), and the next sync committee (`specs/altair/beacon-chain.md`,
with Electra's balance-weighted sampling). The general accessors are in `Accessors.lean`.

Typed `uint64` arithmetic is checked (`U64`); Python `int` arithmetic is `Nat`.
-/

namespace JauneConsensus
open Jaune (Bytes B256)

variable {P : Preset} {f : CFork}


/-! ## Participation and rewards -/

/-- `get_unslashed_participating_indices(state, flag_index, epoch)` (Altair). The result is a set
in pyspec; here it is the active indices that qualify, in index order (no duplicates). -/
def getUnslashedParticipatingIndices (state : BeaconState P f) (flagIndex : Nat) (epoch : Epoch) :
    M (Array ValidatorIndex) := do
  let current ← getCurrentEpoch state
  let previous ← getPreviousEpoch state
  require (epoch == previous || epoch == current)
    "get_unslashed_participating_indices: epoch in (previous, current)"
  let participation :=
    if epoch == current then state.current_epoch_participation else state.previous_epoch_participation
  let active ← getActiveValidatorIndices state epoch
  let mut out := #[]
  for i in active do
    let flags ← participation.get i.toNat "get_unslashed_participating_indices: participation"
    if ← hasFlag flags flagIndex then
      let v ← state.validators.get i.toNat "get_unslashed_participating_indices: validators"
      if !v.slashed then out := out.push i
  pure out

/-- `get_base_reward_per_increment(state)` (Altair):
`Gwei(EFFECTIVE_BALANCE_INCREMENT * BASE_REWARD_FACTOR // integer_squareroot(total_active))`. -/
def getBaseRewardPerIncrement (state : BeaconState P f) : M Gwei := do
  let num ← (← c64 P.EFFECTIVE_BALANCE_INCREMENT).mul? (← c64 P.BASE_REWARD_FACTOR)
    "get_base_reward_per_increment"
  num.div? (← integerSquareroot (← getTotalActiveBalance state)) "get_base_reward_per_increment"

/-- `get_base_reward(state, index)` (Altair), given `get_base_reward_per_increment(state)`
(`perIncrement`). pyspec recomputes that value for every index from the same state; computing it
once gives the same value. -/
def getBaseRewardWith (state : BeaconState P f) (perIncrement : Gwei) (index : ValidatorIndex) :
    M Gwei := do
  let v ← state.validators.get index.toNat "get_base_reward"
  let increments ← v.effective_balance.div? (← c64 P.EFFECTIVE_BALANCE_INCREMENT) "get_base_reward"
  increments.mul? perIncrement "get_base_reward"

/-- `get_base_reward(state, index)` (Altair). -/
def getBaseReward (state : BeaconState P f) (index : ValidatorIndex) : M Gwei := do
  getBaseRewardWith state (← getBaseRewardPerIncrement state) index

/-- `get_finality_delay(state) = get_previous_epoch(state) - state.finalized_checkpoint.epoch`
(phase0, `uint64`). -/
def getFinalityDelay (state : BeaconState P f) : M U64 := do
  (← getPreviousEpoch state).sub? state.finalized_checkpoint.epoch "get_finality_delay"

/-- `is_in_inactivity_leak(state) = get_finality_delay(state) > MIN_EPOCHS_TO_INACTIVITY_PENALTY`
(phase0). -/
def isInInactivityLeak (state : BeaconState P f) : M Bool := do
  pure ((← getFinalityDelay state).toNat > P.MIN_EPOCHS_TO_INACTIVITY_PENALTY)

/-- `get_eligible_validator_indices(state)` (phase0). -/
def getEligibleValidatorIndices (state : BeaconState P f) : M (Array ValidatorIndex) := do
  let previous ← getPreviousEpoch state
  let mut out := #[]
  let mut i := 0
  for v in state.validators.toArray do
    -- `active or (slashed and previous_epoch + 1 < withdrawable_epoch)`, short-circuiting
    let eligible ←
      if isActiveValidator v previous then pure true
      else if v.slashed then do
        let next ← previous.add? U64.one "get_eligible_validator_indices: previous_epoch + 1"
        pure (next < v.withdrawable_epoch)
      else pure false
    if eligible then out := out.push (← U64.ofNat? i "ValidatorIndex")
    i := i + 1
  pure out

/-- Membership in a set of validator indices, as a table over the registry. -/
def indexTable (n : Nat) (xs : Array ValidatorIndex) : Array Bool :=
  xs.foldl (fun t i => t.setIfInBounds i.toNat true) (Array.replicate n false)

/-- Rewards and penalties, one entry per validator. -/
abbrev Deltas := Array Gwei × Array Gwei

/-- `rewards[index] += delta` on a per-validator array (`Gwei` addition). -/
def addAt (xs : Array Gwei) (index : ValidatorIndex) (delta : Gwei) (site : String) :
    M (Array Gwei) := do
  let v ← getAt xs index.toNat site
  pure (xs.setIfInBounds index.toNat (← v.add? delta site))

/-- `get_flag_index_deltas(state, flag_index)` (Altair). -/
def getFlagIndexDeltas (state : BeaconState P f) (flagIndex : Nat) : M Deltas := do
  let n := state.validators.toArray.size
  let mut rewards := Array.replicate n U64.zero
  let mut penalties := Array.replicate n U64.zero
  let previous ← getPreviousEpoch state
  let participating ← getUnslashedParticipatingIndices state flagIndex previous
  let isParticipating := indexTable n participating
  let weight ← c64 (← getAt PARTICIPATION_FLAG_WEIGHTS.toArray flagIndex
    "get_flag_index_deltas: PARTICIPATION_FLAG_WEIGHTS")
  let inc ← c64 P.EFFECTIVE_BALANCE_INCREMENT
  let participatingBalance ← getTotalBalance state participating
  let participatingIncrements ← participatingBalance.div? inc "get_flag_index_deltas"
  let activeIncrements ← (← getTotalActiveBalance state).div? inc "get_flag_index_deltas"
  let perIncrement ← getBaseRewardPerIncrement state
  let leak ← isInInactivityLeak state
  let denom ← c64 WEIGHT_DENOMINATOR
  for index in ← getEligibleValidatorIndices state do
    let baseReward ← getBaseRewardWith state perIncrement index
    if ← getAt isParticipating index.toNat "get_flag_index_deltas" then
      if !leak then
        let num ← (← baseReward.mul? weight "get_flag_index_deltas").mul?
          participatingIncrements "get_flag_index_deltas"
        let d ← num.div? (← activeIncrements.mul? denom "get_flag_index_deltas")
          "get_flag_index_deltas"
        rewards ← addAt rewards index d "get_flag_index_deltas: rewards"
    else if flagIndex != TIMELY_HEAD_FLAG_INDEX then
      let d ← (← baseReward.mul? weight "get_flag_index_deltas").div? denom
        "get_flag_index_deltas"
      penalties ← addAt penalties index d "get_flag_index_deltas: penalties"
  pure (rewards, penalties)

/-- `get_inactivity_penalty_deltas(state)` (`specs/bellatrix/beacon-chain.md`, with
`INACTIVITY_PENALTY_QUOTIENT_BELLATRIX`). -/
def getInactivityPenaltyDeltas (cfg : Config) (state : BeaconState P f) : M Deltas := do
  let n := state.validators.toArray.size
  let rewards := Array.replicate n U64.zero
  let mut penalties := Array.replicate n U64.zero
  let previous ← getPreviousEpoch state
  let matching := indexTable n (← getUnslashedParticipatingIndices state TIMELY_TARGET_FLAG_INDEX previous)
  let denom ← (← c64 cfg.INACTIVITY_SCORE_BIAS).mul?
    (← c64 P.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX) "get_inactivity_penalty_deltas"
  for index in ← getEligibleValidatorIndices state do
    if !(← getAt matching index.toNat "get_inactivity_penalty_deltas") then
      let v ← state.validators.get index.toNat "get_inactivity_penalty_deltas"
      let score ← state.inactivity_scores.get index.toNat "get_inactivity_penalty_deltas"
      let num ← v.effective_balance.mul? score "get_inactivity_penalty_deltas"
      penalties ← addAt penalties index (← num.div? denom "get_inactivity_penalty_deltas")
        "get_inactivity_penalty_deltas: penalties"
  pure (rewards, penalties)

/-! ## The next sync committee -/

/-- `get_next_sync_committee_indices(state)` before Electra (`specs/altair/beacon-chain.md`):
sampling weighted by effective balance with one random byte per candidate, against
`MAX_EFFECTIVE_BALANCE`. Fuel as below. -/
def getNextSyncCommitteeIndicesAltair (state : BeaconState P f) : M (Array ValidatorIndex) := do
  let site := "get_next_sync_committee_indices"
  let epoch ← (← getCurrentEpoch state).add? U64.one site
  let maxRandomByte ← c64 (2 ^ 8 - 1)
  let active ← getActiveValidatorIndices state epoch
  let count ← U64.ofNat? active.size site
  let seed ← getSeed state epoch DOMAIN_SYNC_COMMITTEE
  let maxEb ← c64 P.MAX_EFFECTIVE_BALANCE
  -- `i` is a Python `int`; `uint64(i % count)` and `uint64(i // 32)` are the typed casts
  let rec loop (fuel : Nat) (i : Nat) (acc : Array ValidatorIndex) : M (Array ValidatorIndex) := do
    match fuel with
    | 0 => throw (.assert s!"{site}: loop bound")
    | fuel + 1 =>
      if acc.size ≥ P.SYNC_COMMITTEE_SIZE then return acc
      if count.toNat == 0 then throw (.divByZero s!"{site}: i % active_validator_count")
      let shuffled ← computeShuffledIndex P (← U64.ofNat? (i % count.toNat) site) count seed
      let candidate ← getAt active shuffled.toNat site
      let block ← U64.ofNat? (i / 32) site
      let randomByte ← getAt (hashBytes (seed.toBytes ++ uintToBytes 8 block.toNat)).toArray
        (i % 32) site
      let v ← state.validators.get candidate.toNat site
      let acc := if (← v.effective_balance.mul? maxRandomByte site).toNat ≥
          (← maxEb.mul? (← c64 randomByte.toNat) site).toNat then acc.push candidate else acc
      loop fuel (i + 1) acc
  loop (2 ^ 20) 0 #[]

/-- `get_next_sync_committee_indices(state)` (`specs/electra/beacon-chain.md`): sampling weighted
by effective balance with 16-bit random values. pyspec's `while` loop runs on fuel (`2^20`
iterations, far beyond any input the specification can produce with non-negligible probability)
and rejects with `Reject.assert` if it is exhausted. -/
def getNextSyncCommitteeIndices (state : BeaconState P f) : M (Array ValidatorIndex) := do
  let site := "get_next_sync_committee_indices"
  let epoch ← (← getCurrentEpoch state).add? U64.one site
  let maxRandomValue ← c64 (2 ^ 16 - 1)
  let active ← getActiveValidatorIndices state epoch
  let count ← U64.ofNat? active.size site
  let seed ← getSeed state epoch DOMAIN_SYNC_COMMITTEE
  let maxEb ← c64 P.MAX_EFFECTIVE_BALANCE_ELECTRA
  let rec loop (fuel : Nat) (i : U64) (acc : Array ValidatorIndex) : M (Array ValidatorIndex) := do
    match fuel with
    | 0 => throw (.assert s!"{site}: loop bound")
    | fuel + 1 =>
      if acc.size ≥ P.SYNC_COMMITTEE_SIZE then return acc
      let shuffled ← computeShuffledIndex P (← i.mod? count site) count seed
      let candidate ← getAt active shuffled.toNat site
      let randomBytes := hashBytes (seed.toBytes ++ uintToBytes 8 (← i.div? (← c64 16) site).toNat)
      let offset := (← (← i.mod? (← c64 16) site).mul? (← c64 2) site).toNat
      let randomValue ← bytesToUint64 ((randomBytes.drop offset).take 2)
      let v ← state.validators.get candidate.toNat site
      let acc := if (← v.effective_balance.mul? maxRandomValue site).toNat ≥
          (← maxEb.mul? randomValue site).toNat then acc.push candidate else acc
      loop fuel (← i.add? U64.one site) acc
  loop (2 ^ 20) U64.zero #[]

/-- `get_next_sync_committee(state)` (Altair; Electra's sampling from Electra on): the sampled
validators' pubkeys and their
aggregate (`eth_aggregate_pubkeys`, `Crypto/Boundary.lean`). -/
def getNextSyncCommittee (state : BeaconState P f) : M (SyncCommittee P) := do
  let site := "get_next_sync_committee"
  let indices ← if f.atLeast .electra then getNextSyncCommitteeIndices state
    else getNextSyncCommitteeIndicesAltair state
  let pubkeys ← indices.mapM fun i => do
    pure (← state.validators.get i.toNat site).pubkey
  let agg ← ethAggregatePubkeysM (pubkeys.toList.map (·.toArray.toList))
  let aggregate : BLSPubkey ← SszVector.ofArray agg.toArray site
  pure { pubkeys := ← SszVector.ofArray pubkeys site, aggregate_pubkey := aggregate }

end JauneConsensus
