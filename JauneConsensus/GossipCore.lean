import JauneConsensus.Block

/-!
# Gossip validation: outcomes, `Seen`, and the shared p2p helpers (goal
`eip8282-gloas-cross-layer-v1`, U7a)

Transcribed from `ethereum/consensus-specs` `v1.7.0-beta.4`, the `p2p-interface.md` files of
phase0 to Gloas. The executable gossip validators there (`validate_<topic>_gossip`) raise
`GossipIgnore` or `GossipReject` and otherwise return after recording the message in a `Seen`
cache. Here a validator is a computation in `GM := ExceptT Fail M`:

* `Fail.ignore reason` / `Fail.reject reason` are the two gossip exceptions, with the spec's
  reason string verbatim;
* an error of the inner `M` (a `Reject`: an index error, a `uint64` overflow, ...) is an
  exception other than the two gossip ones, which pyspec would propagate. The vectors never
  provoke one, so the harness reports it as a failure of the case.

**The store a validator reads.** Every validator takes the fork-choice `Store`. The store-free
ones (this unit) read only `store.genesis_time_ms` and the head state
`store.block_states[get_head(store).root]`; they take that pair as a `HeadView`. A
Store-dependent validator (unit M6) builds the same `HeadView` from its `Store` and may call
every helper here.

**`Seen`.** The fields the store-free validators use are spelled as in the spec (the union over
phase0 to Gloas, which never changes their types). The remaining fields, whose types differ by
fork (Fulu's and Gloas's `data_column_sidecar_tuples`) or carry containers (Gloas
`execution_payloads`, `proposer_preferences`; Fulu `partial_data_column_headers`), belong to the
Store-dependent validators and live in the extension `ext : Ext`. Python sets and dictionaries
are association lists: a case validates a handful of messages, and only membership and
insertion are needed.
-/

namespace JauneConsensus.Gossip
open Jaune (Bytes)

/-! ## Outcomes -/

/-- The two gossip exceptions (`GossipIgnore`, `GossipReject`), with the spec's reason. -/
inductive Fail where
  | ignore (reason : String)
  | reject (reason : String)
  deriving Repr, BEq

/-- A gossip validation: a gossip exception, a model exception (`M`), or success. -/
abbrev GM := ExceptT Fail M

/-- `raise GossipIgnore(reason)`. -/
@[inline] def ignore {α : Type} (reason : String) : GM α := throw (.ignore reason)

/-- `raise GossipReject(reason)`. -/
@[inline] def reject {α : Type} (reason : String) : GM α := throw (.reject reason)

/-- The verdict of one message, as the vectors' `expected` field names it. -/
inductive Outcome where
  | valid
  | ignore (reason : String)
  | reject (reason : String)
  deriving Repr, BEq

/-- Run a validation that returns the updated cache. A model exception is returned as the outer
`.error`; a gossip exception leaves the cache unchanged. -/
def outcome {σ : Type} (seen : σ) (v : GM σ) : M (Outcome × σ) :=
  match v.run with
  | .error r => .error r
  | .ok (.ok seen') => .ok (.valid, seen')
  | .ok (.error (.ignore r)) => .ok (.ignore r, seen)
  | .ok (.error (.reject r)) => .ok (.reject r, seen)

/-! ## The head view -/

/-- What a store-free validator reads from the fork-choice `Store`: `store.genesis_time_ms` and
`state = store.block_states[get_head(store).root]`. -/
structure HeadView (S : Type) where
  genesisTimeMs : U64
  headState : S

/-! ## `Seen` -/

/-- `Seen` (`specs/gloas/p2p-interface.md:192` and the earlier forks' versions), restricted to
the fields the store-free validators read and write; `ext` holds the rest. -/
structure Seen (Ext : Type) where
  voluntary_exit_indices : List ValidatorIndex := []
  proposer_slashing_indices : List ValidatorIndex := []
  attester_slashing_indices : List ValidatorIndex := []
  sync_contribution_aggregator_slots : List (Slot × ValidatorIndex × U64) := []
  sync_contribution_data : List ((Slot × Root × U64) × List (List Bool)) := []
  sync_message_validator_slots : List (Slot × ValidatorIndex × U64) := []
  bls_to_execution_change_indices : List ValidatorIndex := []
  ext : Ext

/-- The empty cache. -/
def Seen.empty {Ext : Type} (ext : Ext) : Seen Ext := { ext }

/-- `d.get(key, set())` on an association list. -/
def lookupSet {κ : Type} [BEq κ] (d : List (κ × List (List Bool))) (k : κ) : List (List Bool) :=
  match d.find? (·.1 == k) with
  | some (_, s) => s
  | none => []

/-- `d[key].add(bits)`, creating `d[key] = set()` first if absent. -/
def addToSet {κ : Type} [BEq κ] (d : List (κ × List (List Bool))) (k : κ) (bits : List Bool) :
    List (κ × List (List Bool)) :=
  if d.any (·.1 == k) then
    d.map fun (k', s) => if k' == k then (k', if s.contains bits then s else s ++ [bits]) else (k', s)
  else d ++ [(k, [bits])]

/-! ## Constants -/

/-- `TARGET_AGGREGATORS_PER_SYNC_SUBCOMMITTEE = 2**4` (`specs/altair/validator.md`). -/
def TARGET_AGGREGATORS_PER_SYNC_SUBCOMMITTEE : Nat := 16

/-! ## Time helpers (`specs/phase0/p2p-interface.md`, altair, deneb, gloas)

`current_time_ms` is a `Uint64`, so `current_time_ms + MAXIMUM_GOSSIP_CLOCK_DISPARITY` is checked
`uint64` arithmetic, as are the `Slot` sums. -/

section Time
variable (P : Preset) (cfg : Config) (genesisTimeMs : U64)

/-- `is_future_slot(store, slot, current_time_ms)` (phase0). -/
def isFutureSlot (slot : Slot) (currentTimeMs : U64) : M Bool := do
  let slotTimeMs ← computeTimeAtSlotMs cfg genesisTimeMs slot
  pure ((← U64.add? currentTimeMs (← c64 cfg.MAXIMUM_GOSSIP_CLOCK_DISPARITY) "is_future_slot")
    < slotTimeMs)

/-- `is_future_epoch(store, epoch, current_time_ms)` (phase0). `epoch` may be a config value
(`CAPELLA_FORK_EPOCH`), a Python `int`. -/
def isFutureEpoch (epoch : Nat) (currentTimeMs : U64) : M Bool := do
  let withDisparity ← U64.add? currentTimeMs (← c64 cfg.MAXIMUM_GOSSIP_CLOCK_DISPARITY)
    "is_future_epoch"
  let currentSlot ← computeSlotAtTimeMs cfg genesisTimeMs withDisparity
  pure ((← computeEpochAtSlot P currentSlot).toNat < epoch)

/-- `is_within_slot_range(store, slot, slot_range, current_time_ms)` (phase0). -/
def isWithinSlotRange (slot slotRange : U64) (currentTimeMs : U64) : M Bool := do
  let site := "is_within_slot_range"
  let disparity ← c64 cfg.MAXIMUM_GOSSIP_CLOCK_DISPARITY
  let startTimeMs ← computeTimeAtSlotMs cfg genesisTimeMs slot
  if (← U64.add? currentTimeMs disparity site) < startTimeMs then return false
  let endSlot ← U64.add? (← U64.add? slot slotRange site) U64.one site
  let endTimeMs ← computeTimeAtSlotMs cfg genesisTimeMs endSlot
  if (← U64.add? endTimeMs disparity site) < currentTimeMs then return false
  pure true

/-- `is_current_slot(store, slot, current_time_ms)` (altair). -/
def isCurrentSlot (slot : Slot) (currentTimeMs : U64) : M Bool :=
  isWithinSlotRange cfg genesisTimeMs slot U64.zero currentTimeMs

/-- `is_within_epoch(store, epoch, current_time_ms)` (deneb). -/
def isWithinEpoch (epoch : Epoch) (currentTimeMs : U64) : M Bool := do
  isWithinSlotRange cfg genesisTimeMs (← computeStartSlotAtEpoch P epoch)
    (← c64 (P.SLOTS_PER_EPOCH - 1)) currentTimeMs

/-- `is_current_or_previous_epoch(store, epoch, current_time_ms)` (deneb). Both operands are
evaluated, as in the spec. -/
def isCurrentOrPreviousEpoch (epoch : Epoch) (currentTimeMs : U64) : M Bool := do
  let isCurrent ← isWithinEpoch P cfg genesisTimeMs epoch currentTimeMs
  let isPrevious ← isWithinEpoch P cfg genesisTimeMs
    (← U64.add? epoch U64.one "is_current_or_previous_epoch") currentTimeMs
  pure (isCurrent || isPrevious)

/-- `is_current_or_next_slot(store, slot, current_time_ms)` (gloas). `slot - 1` is `Slot`
arithmetic and raises at slot 0. -/
def isCurrentOrNextSlot (slot : Slot) (currentTimeMs : U64) : M Bool := do
  let isCurrent ← isCurrentSlot cfg genesisTimeMs slot currentTimeMs
  let isNext ← isCurrentSlot cfg genesisTimeMs
    (← U64.sub? slot U64.one "is_current_or_next_slot") currentTimeMs
  pure (isCurrent || isNext)

/-- `is_past_slot(store, slot, current_time_ms)` (gloas). -/
def isPastSlot (slot : Slot) (currentTimeMs : U64) : M Bool := do
  let slotTimeMs ← computeTimeAtSlotMs cfg genesisTimeMs slot
  pure ((← U64.add? slotTimeMs (← c64 cfg.MAXIMUM_GOSSIP_CLOCK_DISPARITY) "is_past_slot")
    < currentTimeMs)

end Time

/-! ## Other shared helpers -/

/-- `is_non_strict_superset(seen_bits_set, new_bits)` (phase0). `zip(..., strict=True)` raises
on a length mismatch. -/
def isNonStrictSuperset (seenBitsSet : List (List Bool)) (newBits : List Bool) : M Bool := do
  for priorBits in seenBitsSet do
    if priorBits.length != newBits.length then
      throw (.assert "is_non_strict_superset: zip(strict=True)")
    if (priorBits.zip newBits).all (fun (p, n) => !n || p) then return true
  pure false

/-- `compute_fork_version(epoch)` (`specs/gloas/p2p-interface.md:225`). -/
def computeForkVersion (cfg : Config) (epoch : Epoch) : M Version := do
  let e := epoch.toNat
  versionOf <|
    if e ≥ cfg.GLOAS_FORK_EPOCH then cfg.GLOAS_FORK_VERSION
    else if e ≥ cfg.FULU_FORK_EPOCH then cfg.FULU_FORK_VERSION
    else if e ≥ cfg.ELECTRA_FORK_EPOCH then cfg.ELECTRA_FORK_VERSION
    else if e ≥ cfg.DENEB_FORK_EPOCH then cfg.DENEB_FORK_VERSION
    else if e ≥ cfg.CAPELLA_FORK_EPOCH then cfg.CAPELLA_FORK_VERSION
    else if e ≥ cfg.BELLATRIX_FORK_EPOCH then cfg.BELLATRIX_FORK_VERSION
    else if e ≥ cfg.ALTAIR_FORK_EPOCH then cfg.ALTAIR_FORK_VERSION
    else cfg.GENESIS_FORK_VERSION

/-- `compute_subnet_for_data_column_sidecar(column_index)` (fulu). -/
def computeSubnetForDataColumnSidecar (cfg : Config) (columnIndex : ColumnIndex) : M U64 := do
  U64.mod? columnIndex (← c64 cfg.DATA_COLUMN_SIDECAR_SUBNET_COUNT)
    "compute_subnet_for_data_column_sidecar"

/-- `is_gas_limit_target_compatible(parent_gas_limit, gas_limit, target_gas_limit)` (gloas).
`parent_gas_limit - max_gas_limit_difference` and the sum are `Uint64` arithmetic. -/
def isGasLimitTargetCompatible (parentGasLimit gasLimit targetGasLimit : U64) : M Bool := do
  let site := "is_gas_limit_target_compatible"
  let maxDiff ← c64 (saturatingSub (parentGasLimit.toNat / 1024) 1)
  let minGasLimit ← U64.sub? parentGasLimit maxDiff site
  let maxGasLimit ← U64.add? parentGasLimit maxDiff site
  if targetGasLimit < minGasLimit then return gasLimit.toNat == minGasLimit.toNat
  if maxGasLimit < targetGasLimit then return gasLimit.toNat == maxGasLimit.toNat
  pure (gasLimit.toNat == targetGasLimit.toNat)

/-- `is_sync_committee_aggregator(signature)` (`specs/altair/validator.md`). -/
def isSyncCommitteeAggregator (P : Preset) (signature : BLSSignature) : M Bool := do
  let modulo := max 1 (P.SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT /
    TARGET_AGGREGATORS_PER_SYNC_SUBCOMMITTEE)
  let v ← bytesToUint64 ((hashBytes signature.toArray.toList).take 8)
  pure (v.toNat % modulo == 0)

/-- `compute_sync_committee_period(epoch)` (altair). -/
def computeSyncCommitteePeriod (P : Preset) (epoch : Epoch) : M U64 := do
  U64.div? epoch (← c64 P.EPOCHS_PER_SYNC_COMMITTEE_PERIOD) "compute_sync_committee_period"

/-- The sync committee `get_sync_subcommittee_pubkeys` and `compute_subnets_for_sync_committee`
read: the current one when `state.slot + 1` is in the current period, else the next. -/
def syncCommitteeForNextSlot (P : Preset) (stateSlot : Slot) (current next : SyncCommittee P) :
    M (SyncCommittee P) := do
  let nextSlotEpoch ← computeEpochAtSlot P (← U64.add? stateSlot U64.one "state.slot + 1")
  let currentPeriod ← computeSyncCommitteePeriod P (← computeEpochAtSlot P stateSlot)
  if currentPeriod.toNat == (← computeSyncCommitteePeriod P nextSlotEpoch).toNat then pure current
  else pure next

/-- `sync_committee.pubkeys[i : i + sync_subcommittee_size]` with
`i = subcommittee_index * sync_subcommittee_size` (Python slicing clamps). -/
def subcommitteePubkeys (P : Preset) (committee : SyncCommittee P) (subcommitteeIndex : U64) :
    List BLSPubkey :=
  let size := P.SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT
  ((committee.pubkeys.toArray.toList.drop (subcommitteeIndex.toNat * size)).take size)

/-- The subnets of `compute_subnets_for_sync_committee` for `target_pubkey`. -/
def subnetsForPubkey (P : Preset) (committee : SyncCommittee P) (targetPubkey : BLSPubkey) :
    List Nat :=
  let size := P.SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT
  ((committee.pubkeys.toArray.toList.zipIdx.filter (·.1 == targetPubkey)).map
    (fun (_, i) => i / size)).eraseDups

end JauneConsensus.Gossip
