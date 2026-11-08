import JauneConsensus.Signing
import JauneConsensus.Ctx

/-!
# Light-client sync protocol (Altair, with the Capella header and Electra generalized indices)

Transcribed from `ethereum/consensus-specs` `v1.6.1`, `specs/altair/light-client/sync-protocol.md`
(store, validation, application, force update, ranking), `specs/capella/light-client/
sync-protocol.md` and `specs/deneb/light-client/sync-protocol.md` (`is_valid_light_client_header`),
`specs/electra/light-client/sync-protocol.md` (generalized indices, `get_lc_execution_root`) and
`specs/phase0/p2p-interface.md` / Electra and Fulu (`compute_fork_version`).

The store is indexed by the preset and the fork of its objects (`LightClientUpdate P f`). Typed
`uint64` arithmetic is checked `U64`; `sum(bits)` and `len(bits)` are Python `int` (`Nat`).
-/

namespace JauneConsensus
open Jaune (Bytes B256)

variable {P : Preset} {f : CFork}

/-! ## Constants and defaults -/

/-- Generalized indices (`specs/altair/light-client/sync-protocol.md`, Electra modified). -/
def FINALIZED_ROOT_GINDEX : Nat := 105
def CURRENT_SYNC_COMMITTEE_GINDEX : Nat := 54
def NEXT_SYNC_COMMITTEE_GINDEX : Nat := 55
def FINALIZED_ROOT_GINDEX_ELECTRA : Nat := 169
def CURRENT_SYNC_COMMITTEE_GINDEX_ELECTRA : Nat := 86
def NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA : Nat := 87
/-- `EXECUTION_PAYLOAD_GINDEX` (`specs/capella/light-client/sync-protocol.md`). -/
def EXECUTION_PAYLOAD_GINDEX : Nat := 25

/-- `floorlog2(x)` for `x ≥ 1`. -/
def floorlog2 (x : Nat) : Nat := Nat.log2 x

/-- The zero byte vector. -/
def zeroBytesVec (n : Nat) : SszVector UInt8 n := ⟨Array.replicate n 0, by simp⟩
/-- The zero root vector. -/
def zeroRootVec (n : Nat) : SszVector Root n := ⟨Array.replicate n (Jaune.Bytes.toB256 []), by simp⟩
-- The zero root `Bytes32()` is `zeroRoot` (`Helpers.lean`).

/-- `ExecutionPayloadHeader()`. -/
def defaultExecutionPayloadHeader : ExecutionPayloadHeader P :=
  { parent_hash := zeroRoot, fee_recipient := (0 : Jaune.Adr), state_root := zeroRoot,
    receipts_root := zeroRoot, logs_bloom := zeroBytesVec _, prev_randao := zeroRoot,
    block_number := U64.zero, gas_limit := U64.zero, gas_used := U64.zero, timestamp := U64.zero,
    extra_data := SszList.empty, base_fee_per_gas := UIntN.zero, block_hash := zeroRoot,
    transactions_root := zeroRoot, withdrawals_root := zeroRoot, blob_gas_used := U64.zero,
    excess_blob_gas := U64.zero }

/-- `LightClientHeader()`. -/
def defaultLightClientHeader : LightClientHeader P :=
  { beacon := { slot := U64.zero, proposer_index := U64.zero, parent_root := zeroRoot,
                state_root := zeroRoot, body_root := zeroRoot },
    execution := defaultExecutionPayloadHeader, execution_branch := zeroRootVec _ }

/-- `SyncCommittee()`. -/
def defaultSyncCommittee : SyncCommittee P :=
  { pubkeys := ⟨Array.replicate P.SYNC_COMMITTEE_SIZE (zeroBytesVec 48), by simp⟩,
    aggregate_pubkey := zeroBytesVec 48 }

/-- The Capella `ExecutionPayloadHeader` (no blob fields), for `get_lc_execution_root` before
Deneb (`specs/capella/beacon-chain.md`). -/
ssz_container CapellaExecutionPayloadHeader (P : Preset) where
  parent_hash : Hash32
  fee_recipient : ExecutionAddress
  state_root : Bytes32
  receipts_root : Bytes32
  logs_bloom : (SszVector UInt8 P.BYTES_PER_LOGS_BLOOM)
  prev_randao : Bytes32
  block_number : U64
  gas_limit : U64
  gas_used : U64
  timestamp : U64
  extra_data : (SszList UInt8 P.MAX_EXTRA_DATA_BYTES)
  base_fee_per_gas : U256
  block_hash : Hash32
  transactions_root : Root
  withdrawals_root : Root

/-! ## Helpers -/

/-- `compute_sync_committee_period_at_slot` (Altair). -/
def computeSyncCommitteePeriodAtSlot (P : Preset) (slot : Slot) : M U64 := do
  U64.div? (← computeEpochAtSlot P slot) (← c64 P.EPOCHS_PER_SYNC_COMMITTEE_PERIOD)
    "compute_sync_committee_period"

/-- `compute_fork_version(epoch)` (Fulu's version of the chain of comparisons). -/
def computeForkVersion (cfg : Config) (epoch : Epoch) : M Version := do
  let e := epoch.toNat
  versionOf <|
    if e ≥ cfg.FULU_FORK_EPOCH then cfg.FULU_FORK_VERSION
    else if e ≥ cfg.ELECTRA_FORK_EPOCH then cfg.ELECTRA_FORK_VERSION
    else if e ≥ cfg.DENEB_FORK_EPOCH then cfg.DENEB_FORK_VERSION
    else if e ≥ cfg.CAPELLA_FORK_EPOCH then cfg.CAPELLA_FORK_VERSION
    else if e ≥ cfg.BELLATRIX_FORK_EPOCH then cfg.BELLATRIX_FORK_VERSION
    else if e ≥ cfg.ALTAIR_FORK_EPOCH then cfg.ALTAIR_FORK_VERSION
    else cfg.GENESIS_FORK_VERSION

/-- `compute_fork_digest`: Fulu XORs the fork data root with the hash of the blob parameters
at `epoch` (`specs/fulu/beacon-chain.md`, EIP-7892); before Fulu it is the first four bytes of
`compute_fork_data_root(current_version, genesis_validators_root)`
(`specs/phase0/p2p-interface.md`). -/
def computeForkDigest (cfg : Config) (f : CFork) (gvr : Root) (epoch : Epoch) : M Bytes := do
  let version ← computeForkVersion cfg epoch
  let base := computeForkDataRoot version gvr
  if f.atLeast .fulu then
    let bp ← getBlobParameters cfg epoch
    let mask := hash (uintToBytes 8 bp.epoch.toNat ++ uintToBytes 8 bp.maxBlobsPerBlock.toNat)
    pure ((xor base mask).toBytes.take 4)
  else pure (base.toBytes.take 4)

/-- The fork digests an object of fork `f` can carry: `f`'s digest at its activation epoch and,
from Fulu, at every later `BLOB_SCHEDULE` epoch. -/
def forkDigestsOf (cfg : Config) (f : CFork) (gvr : Root) : M (List Bytes) := do
  let start := if f.atLeast .fulu then cfg.FULU_FORK_EPOCH else cfg.ELECTRA_FORK_EPOCH
  let epochs := if f.atLeast .fulu then
      start :: (cfg.BLOB_SCHEDULE.map (·.EPOCH)).filter (· ≥ start)
    else [start]
  epochs.mapM fun e => do computeForkDigest cfg f gvr (← U64.ofNat? e "fork digest epoch")

/-- `get_subtree_index(generalized_index)`. -/
def getSubtreeIndex (g : Nat) : M U64 := U64.ofNat? (g % 2 ^ floorlog2 g) "get_subtree_index"

/-- `get_lc_execution_root` (Electra). -/
def getLcExecutionRoot (cfg : Config) (header : LightClientHeader P) : M Root := do
  let epoch := (← computeEpochAtSlot P header.beacon.slot).toNat
  let e := header.execution
  if epoch ≥ cfg.ELECTRA_FORK_EPOCH then return hashTreeRoot e
  -- the Deneb header has the same fields and order as the Electra one
  if epoch ≥ cfg.DENEB_FORK_EPOCH then return hashTreeRoot e
  if epoch ≥ cfg.CAPELLA_FORK_EPOCH then
    let c : CapellaExecutionPayloadHeader P :=
      { parent_hash := e.parent_hash, fee_recipient := e.fee_recipient, state_root := e.state_root,
        receipts_root := e.receipts_root, logs_bloom := e.logs_bloom, prev_randao := e.prev_randao,
        block_number := e.block_number, gas_limit := e.gas_limit, gas_used := e.gas_used,
        timestamp := e.timestamp, extra_data := e.extra_data, base_fee_per_gas := e.base_fee_per_gas,
        block_hash := e.block_hash, transactions_root := e.transactions_root,
        withdrawals_root := e.withdrawals_root }
    return hashTreeRoot c
  pure zeroRoot

/-- `is_valid_light_client_header` (Deneb). -/
def isValidLightClientHeader (cfg : Config) (header : LightClientHeader P) : M Bool := do
  let epoch := (← computeEpochAtSlot P header.beacon.slot).toNat
  if epoch < cfg.DENEB_FORK_EPOCH then
    if header.execution.blob_gas_used != U64.zero then return false
    if header.execution.excess_blob_gas != U64.zero then return false
  if epoch < cfg.CAPELLA_FORK_EPOCH then
    return header.execution == defaultExecutionPayloadHeader &&
      header.execution_branch == zeroRootVec _
  isValidMerkleBranch (← getLcExecutionRoot cfg header) header.execution_branch.toArray.toList
    (← c64 (floorlog2 EXECUTION_PAYLOAD_GINDEX)) (← getSubtreeIndex EXECUTION_PAYLOAD_GINDEX)
    header.beacon.body_root

/-- `finalized_root_gindex_at_slot` (Electra). -/
def finalizedRootGindexAtSlot (cfg : Config) (P : Preset) (slot : Slot) : M Nat := do
  if (← computeEpochAtSlot P slot).toNat ≥ cfg.ELECTRA_FORK_EPOCH then
    pure FINALIZED_ROOT_GINDEX_ELECTRA else pure FINALIZED_ROOT_GINDEX

/-- `current_sync_committee_gindex_at_slot` (Electra). -/
def currentSyncCommitteeGindexAtSlot (cfg : Config) (P : Preset) (slot : Slot) : M Nat := do
  if (← computeEpochAtSlot P slot).toNat ≥ cfg.ELECTRA_FORK_EPOCH then
    pure CURRENT_SYNC_COMMITTEE_GINDEX_ELECTRA else pure CURRENT_SYNC_COMMITTEE_GINDEX

/-- `next_sync_committee_gindex_at_slot` (Electra). -/
def nextSyncCommitteeGindexAtSlot (cfg : Config) (P : Preset) (slot : Slot) : M Nat := do
  if (← computeEpochAtSlot P slot).toNat ≥ cfg.ELECTRA_FORK_EPOCH then
    pure NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA else pure NEXT_SYNC_COMMITTEE_GINDEX

/-- `is_valid_normalized_merkle_branch` (Altair). -/
def isValidNormalizedMerkleBranch (leaf : Bytes32) (branch : List Bytes32) (gindex : Nat)
    (root : Root) : M Bool := do
  let depth := floorlog2 gindex
  let index ← getSubtreeIndex gindex
  let numExtra := branch.length - depth
  if (branch.take numExtra).any (· != zeroRoot) then return false
  isValidMerkleBranch leaf (branch.drop numExtra) (← c64 depth) index root

/-! ## Store -/

/-- `LightClientStore` (Altair). -/
structure LightClientStore (P : Preset) (f : CFork) where
  finalized_header : LightClientHeader P
  current_sync_committee : SyncCommittee P
  next_sync_committee : SyncCommittee P
  best_valid_update : Option (LightClientUpdate P f)
  optimistic_header : LightClientHeader P
  previous_max_active_participants : U64
  current_max_active_participants : U64

/-- `is_sync_committee_update`. -/
def isSyncCommitteeUpdate (u : LightClientUpdate P f) : Bool :=
  !(u.next_sync_committee_branch == zeroRootVec _)

/-- `is_finality_update`. -/
def isFinalityUpdate (u : LightClientUpdate P f) : Bool :=
  !(u.finality_branch == zeroRootVec _)

/-- `is_next_sync_committee_known`. -/
def isNextSyncCommitteeKnown (s : LightClientStore P f) : Bool :=
  !(s.next_sync_committee == defaultSyncCommittee)

/-- `get_safety_threshold`. -/
def getSafetyThreshold (s : LightClientStore P f) : M U64 := do
  let m := if s.previous_max_active_participants < s.current_max_active_participants then
    s.current_max_active_participants else s.previous_max_active_participants
  U64.div? m (← c64 2) "get_safety_threshold"

/-- `sum(bits)`. -/
def bitCount {n : Nat} (b : Bitvector n) : Nat := (b.bits.filter id).size

/-- `initialize_light_client_store` (Altair). -/
def initializeLightClientStore (cfg : Config) (trustedBlockRoot : Root)
    (bootstrap : LightClientBootstrap P f) : M (LightClientStore P f) := do
  require (← isValidLightClientHeader cfg bootstrap.header) "initialize_light_client_store: header"
  require (hashTreeRoot bootstrap.header.beacon == trustedBlockRoot)
    "initialize_light_client_store: trusted block root"
  require (← isValidNormalizedMerkleBranch (hashTreeRoot bootstrap.current_sync_committee)
    bootstrap.current_sync_committee_branch.toArray.toList
    (← currentSyncCommitteeGindexAtSlot cfg P bootstrap.header.beacon.slot)
    bootstrap.header.beacon.state_root) "initialize_light_client_store: sync committee branch"
  pure { finalized_header := bootstrap.header, current_sync_committee := bootstrap.current_sync_committee,
         next_sync_committee := defaultSyncCommittee, best_valid_update := none,
         optimistic_header := bootstrap.header, previous_max_active_participants := U64.zero,
         current_max_active_participants := U64.zero }

/-- `validate_light_client_update` (Altair). -/
def validateLightClientUpdate (ctx : Ctx) (store : LightClientStore P f) (update : LightClientUpdate P f)
    (currentSlot : Slot) (genesisValidatorsRoot : Root) : M Unit := do
  let cfg := ctx.cfg
  let site := "validate_light_client_update"
  let sa := update.sync_aggregate
  require (bitCount sa.sync_committee_bits ≥ P.MIN_SYNC_COMMITTEE_PARTICIPANTS) s!"{site}: participants"
  require (← isValidLightClientHeader cfg update.attested_header) s!"{site}: attested header"
  let attestedSlot := update.attested_header.beacon.slot
  let finalizedSlot := update.finalized_header.beacon.slot
  require (update.signature_slot ≤ currentSlot && attestedSlot < update.signature_slot &&
    finalizedSlot ≤ attestedSlot) s!"{site}: slots"
  let storePeriod ← computeSyncCommitteePeriodAtSlot P store.finalized_header.beacon.slot
  let sigPeriod ← computeSyncCommitteePeriodAtSlot P update.signature_slot
  if isNextSyncCommitteeKnown store then
    require (sigPeriod == storePeriod || sigPeriod == (← U64.add? storePeriod U64.one site))
      s!"{site}: signature period"
  else
    require (sigPeriod == storePeriod) s!"{site}: signature period"
  let attestedPeriod ← computeSyncCommitteePeriodAtSlot P attestedSlot
  let hasNextSyncCommittee := !isNextSyncCommitteeKnown store &&
    (isSyncCommitteeUpdate update && attestedPeriod == storePeriod)
  require (store.finalized_header.beacon.slot < attestedSlot || hasNextSyncCommittee) s!"{site}: relevant"
  if !isFinalityUpdate update then
    require (update.finalized_header == defaultLightClientHeader) s!"{site}: empty finalized header"
  else
    let finalizedRoot ←
      if finalizedSlot == GENESIS_SLOT then do
        require (update.finalized_header == defaultLightClientHeader) s!"{site}: genesis finalized header"
        pure zeroRoot
      else do
        require (← isValidLightClientHeader cfg update.finalized_header) s!"{site}: finalized header"
        pure (hashTreeRoot update.finalized_header.beacon)
    require (← isValidNormalizedMerkleBranch finalizedRoot update.finality_branch.toArray.toList
      (← finalizedRootGindexAtSlot cfg P attestedSlot) update.attested_header.beacon.state_root)
      s!"{site}: finality branch"
  if !isSyncCommitteeUpdate update then
    require (update.next_sync_committee == defaultSyncCommittee) s!"{site}: empty next sync committee"
  else
    if attestedPeriod == storePeriod && isNextSyncCommitteeKnown store then
      require (update.next_sync_committee == store.next_sync_committee) s!"{site}: known next committee"
    require (← isValidNormalizedMerkleBranch (hashTreeRoot update.next_sync_committee)
      update.next_sync_committee_branch.toArray.toList
      (← nextSyncCommitteeGindexAtSlot cfg P attestedSlot) update.attested_header.beacon.state_root)
      s!"{site}: next sync committee branch"
  let committee := if sigPeriod == storePeriod then store.current_sync_committee
    else store.next_sync_committee
  let pubkeys := ((sa.sync_committee_bits.bits.zip committee.pubkeys.toArray).filter (·.1)).toList.map (·.2)
  let forkVersionSlot ← U64.sub? (if U64.one < update.signature_slot then update.signature_slot else U64.one)
    U64.one site
  let forkVersion ← computeForkVersion cfg (← computeEpochAtSlot P forkVersionSlot)
  let domain := computeDomain DOMAIN_SYNC_COMMITTEE forkVersion genesisValidatorsRoot
  let root := computeSigningRoot update.attested_header.beacon domain
  require (blsFastAggregateVerify ctx.blsActive pubkeys root sa.sync_committee_signature)
    s!"{site}: bls.FastAggregateVerify"

/-- `apply_light_client_update` (Altair). -/
def applyLightClientUpdate (store : LightClientStore P f) (update : LightClientUpdate P f) :
    M (LightClientStore P f) := do
  let site := "apply_light_client_update"
  let storePeriod ← computeSyncCommitteePeriodAtSlot P store.finalized_header.beacon.slot
  let finalizedPeriod ← computeSyncCommitteePeriodAtSlot P update.finalized_header.beacon.slot
  let mut store := store
  if !isNextSyncCommitteeKnown store then
    require (finalizedPeriod == storePeriod) s!"{site}: finalized period"
    store := { store with next_sync_committee := update.next_sync_committee }
  else if finalizedPeriod == (← U64.add? storePeriod U64.one site) then
    store := { store with
      current_sync_committee := store.next_sync_committee
      next_sync_committee := update.next_sync_committee
      previous_max_active_participants := store.current_max_active_participants
      current_max_active_participants := U64.zero }
  if store.finalized_header.beacon.slot < update.finalized_header.beacon.slot then
    store := { store with finalized_header := update.finalized_header }
    if store.optimistic_header.beacon.slot < store.finalized_header.beacon.slot then
      store := { store with optimistic_header := store.finalized_header }
  pure store

/-- `process_light_client_store_force_update` (Altair). -/
def processLightClientStoreForceUpdate (store : LightClientStore P f) (currentSlot : Slot) :
    M (LightClientStore P f) := do
  let timeout ← U64.add? store.finalized_header.beacon.slot (← c64 P.UPDATE_TIMEOUT)
    "process_light_client_store_force_update"
  match store.best_valid_update with
  | some best =>
    if timeout < currentSlot then
      let best := if best.finalized_header.beacon.slot ≤ store.finalized_header.beacon.slot then
        { best with finalized_header := best.attested_header } else best
      let store ← applyLightClientUpdate store best
      pure { store with best_valid_update := none }
    else pure store
  | none => pure store

/-- `is_better_update` (Altair). -/
def isBetterUpdate (P : Preset) (newU oldU : LightClientUpdate P f) : M Bool := do
  let maxActive := newU.sync_aggregate.sync_committee_bits.bits.size
  let newN := bitCount newU.sync_aggregate.sync_committee_bits
  let oldN := bitCount oldU.sync_aggregate.sync_committee_bits
  let newSuper := newN * 3 ≥ maxActive * 2
  let oldSuper := oldN * 3 ≥ maxActive * 2
  if newSuper != oldSuper then return newSuper
  if !newSuper && newN != oldN then return decide (newN > oldN)
  let period := computeSyncCommitteePeriodAtSlot P
  let newRelevant := isSyncCommitteeUpdate newU &&
    (← period newU.attested_header.beacon.slot) == (← period newU.signature_slot)
  let oldRelevant := isSyncCommitteeUpdate oldU &&
    (← period oldU.attested_header.beacon.slot) == (← period oldU.signature_slot)
  if newRelevant != oldRelevant then return newRelevant
  let newFin := isFinalityUpdate newU
  let oldFin := isFinalityUpdate oldU
  if newFin != oldFin then return newFin
  if newFin then
    let newScf := (← period newU.finalized_header.beacon.slot) == (← period newU.attested_header.beacon.slot)
    let oldScf := (← period oldU.finalized_header.beacon.slot) == (← period oldU.attested_header.beacon.slot)
    if newScf != oldScf then return newScf
  if newN != oldN then return decide (newN > oldN)
  if newU.attested_header.beacon.slot != oldU.attested_header.beacon.slot then
    return decide (newU.attested_header.beacon.slot < oldU.attested_header.beacon.slot)
  pure (decide (newU.signature_slot < oldU.signature_slot))

/-- `process_light_client_update` (Altair). -/
def processLightClientUpdate (ctx : Ctx) (store : LightClientStore P f) (update : LightClientUpdate P f)
    (currentSlot : Slot) (genesisValidatorsRoot : Root) : M (LightClientStore P f) := do
  validateLightClientUpdate ctx store update currentSlot genesisValidatorsRoot
  let bits := update.sync_aggregate.sync_committee_bits
  let n := bitCount bits
  let mut store := store
  let better ← match store.best_valid_update with
    | none => pure true
    | some b => isBetterUpdate P update b
  if better then store := { store with best_valid_update := some update }
  let nU ← U64.ofNat? n "sum(sync_committee_bits)"
  store := { store with current_max_active_participants :=
    if store.current_max_active_participants < nU then nU else store.current_max_active_participants }
  if (← getSafetyThreshold store) < nU &&
      store.optimistic_header.beacon.slot < update.attested_header.beacon.slot then
    store := { store with optimistic_header := update.attested_header }
  let period := computeSyncCommitteePeriodAtSlot P
  let hasFinalizedNext := !isNextSyncCommitteeKnown store && isSyncCommitteeUpdate update &&
    isFinalityUpdate update &&
    (← period update.finalized_header.beacon.slot) == (← period update.attested_header.beacon.slot)
  if n * 3 ≥ bits.bits.size * 2 &&
      (store.finalized_header.beacon.slot < update.finalized_header.beacon.slot || hasFinalizedNext) then
    store ← applyLightClientUpdate store update
    store := { store with best_valid_update := none }
  pure store

end JauneConsensus
