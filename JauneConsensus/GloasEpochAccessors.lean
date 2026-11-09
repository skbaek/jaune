import JauneConsensus.GloasMutators
import JauneConsensus.EpochAccessors

/-!
# Gloas accessors used by epoch processing (goal `eip8282-gloas-cross-layer-v1`, U3)

The epoch-only accessors of `ethereum/consensus-specs` `v1.7.0-beta.4` over
`JauneConsensus.Gloas.BeaconState`: participation and rewards (`specs/altair/beacon-chain.md`,
with Bellatrix's inactivity quotient) and the inactivity-leak test (`specs/phase0/
beacon-chain.md`), reused by reference and copied here; and the next sync committee, whose
indices Gloas modifies (:1315) to use `compute_balance_weighted_selection`.

State-free pieces are reused from `EpochAccessors.lean` (`indexTable`, `addAt`, `Deltas`).
-/

namespace JauneConsensus.Gloas

open Jaune

variable {P : Preset}

/-! ## Participation and rewards -/

/-- `get_unslashed_participating_indices(state, flag_index, epoch)` (Altair): the active indices
that qualify, in index order. -/
def getUnslashedParticipatingIndices (state : BeaconState P) (flagIndex : Nat) (epoch : Epoch) :
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

/-- `get_base_reward_per_increment(state)` (Altair). -/
def getBaseRewardPerIncrement (state : BeaconState P) : M Gwei := do
  let num ← (← c64 P.EFFECTIVE_BALANCE_INCREMENT).mul? (← c64 P.BASE_REWARD_FACTOR)
    "get_base_reward_per_increment"
  num.div? (← integerSquareroot (← getTotalActiveBalance state)) "get_base_reward_per_increment"

/-- `get_base_reward(state, index)` (Altair), given `get_base_reward_per_increment(state)`. -/
def getBaseRewardWith (state : BeaconState P) (perIncrement : Gwei) (index : ValidatorIndex) :
    M Gwei := do
  let v ← state.validators.get index.toNat "get_base_reward"
  let increments ← v.effective_balance.div? (← c64 P.EFFECTIVE_BALANCE_INCREMENT) "get_base_reward"
  increments.mul? perIncrement "get_base_reward"

/-- `get_base_reward(state, index)` (Altair). -/
def getBaseReward (state : BeaconState P) (index : ValidatorIndex) : M Gwei := do
  getBaseRewardWith state (← getBaseRewardPerIncrement state) index

/-- `get_finality_delay(state)` (phase0, `uint64`). -/
def getFinalityDelay (state : BeaconState P) : M U64 := do
  (← getPreviousEpoch state).sub? state.finalized_checkpoint.epoch "get_finality_delay"

/-- `is_in_inactivity_leak(state)` (phase0). -/
def isInInactivityLeak (state : BeaconState P) : M Bool := do
  pure ((← getFinalityDelay state).toNat > P.MIN_EPOCHS_TO_INACTIVITY_PENALTY)

/-- `get_eligible_validator_indices(state)` (phase0). -/
def getEligibleValidatorIndices (state : BeaconState P) : M (Array ValidatorIndex) := do
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

/-- `get_flag_index_deltas(state, flag_index)` (Altair). -/
def getFlagIndexDeltas (state : BeaconState P) (flagIndex : Nat) : M Deltas := do
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

/-- `get_inactivity_penalty_deltas(state)` (`specs/bellatrix/beacon-chain.md`). -/
def getInactivityPenaltyDeltas (cfg : Config) (state : BeaconState P) : M Deltas := do
  let n := state.validators.toArray.size
  let rewards := Array.replicate n U64.zero
  let mut penalties := Array.replicate n U64.zero
  let previous ← getPreviousEpoch state
  let matching := indexTable n
    (← getUnslashedParticipatingIndices state TIMELY_TARGET_FLAG_INDEX previous)
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

/-- `get_next_sync_committee_indices(state)` (Gloas, :1315): `SYNC_COMMITTEE_SIZE`
balance-weighted draws, with shuffling, from the next epoch's active validators. -/
def getNextSyncCommitteeIndices (state : BeaconState P) : M (Array ValidatorIndex) := do
  let epoch ← (← getCurrentEpoch state).add? U64.one "get_next_sync_committee_indices"
  let seed ← getSeed state epoch DOMAIN_SYNC_COMMITTEE
  let indices ← getActiveValidatorIndices state epoch
  computeBalanceWeightedSelection state indices seed P.SYNC_COMMITTEE_SIZE true

/-- `get_next_sync_committee(state)` (Altair), with the Gloas indices. From `v1.7.0-beta.4` pyspec
computes `bls.AggregatePKs` whatever the BLS switch, because the aggregate is state data
(`eth_consensus_specs/utils/bls.py`), so it is never stubbed (as in `EpochAccessors.lean`). -/
def getNextSyncCommittee (state : BeaconState P) : M (SyncCommittee P) := do
  let site := "get_next_sync_committee"
  let indices ← getNextSyncCommitteeIndices state
  let pubkeys ← indices.mapM fun i => do
    pure (← state.validators.get i.toNat site).pubkey
  let agg ← ethAggregatePubkeysM (pubkeys.toList.map (·.toArray.toList))
  let aggregate : BLSPubkey ← SszVector.ofArray agg.toArray site
  pure { pubkeys := ← SszVector.ofArray pubkeys site, aggregate_pubkey := aggregate }

end JauneConsensus.Gloas
