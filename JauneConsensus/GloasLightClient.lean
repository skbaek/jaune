import JauneConsensus.LightClient
import JauneConsensus.ContainersGloas
import JauneConsensus.GossipCore

/-!
# Gloas light-client sync protocol

Transcribed from `ethereum/consensus-specs` `v1.7.0-beta.4`,
`specs/gloas/light-client/sync-protocol.md` (the Gloas generalized indices, the
`*_gindex_at_slot` helpers, `get_lc_execution_root`, `is_valid_light_client_header`), with the
store, validation, application, force update and ranking of
`specs/altair/light-client/sync-protocol.md` over the Gloas containers
(`JauneConsensus/ContainersGloas.lean`). `compute_fork_version` is Gloas's
(`specs/gloas/p2p-interface.md`, `Gossip.computeForkVersion`); `compute_fork_digest` is Fulu's,
unchanged by Gloas.

The Altair bodies are spec-shaped copies of `LightClient.lean`'s over `Gloas.LightClientHeader`
(`execution_block_hash` in place of `execution`), per master decision
`eip8282-w1-gloas-reuse-a-prime`; the type-independent helpers (`isValidNormalizedMerkleBranch`,
`getSubtreeIndex`, `computeSyncCommitteePeriodAtSlot`, `bitCount`, `defaultSyncCommittee`) are
called, not copied.
-/

namespace JauneConsensus.Gloas
open Jaune (Bytes B256)
open JauneConsensus

variable {P : Preset}

/-! ## Constants -/

/-- `FINALIZED_ROOT_GINDEX_GLOAS` (`get_generalized_index(BeaconState, "finalized_checkpoint",
"root")`; pysetup hardcodes it, `pysetup/spec_builders/gloas.py`). -/
def FINALIZED_ROOT_GINDEX_GLOAS : Nat := 735
/-- `CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS`. -/
def CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS : Nat := 2945
/-- `NEXT_SYNC_COMMITTEE_GINDEX_GLOAS`. -/
def NEXT_SYNC_COMMITTEE_GINDEX_GLOAS : Nat := 2946
/-- `EXECUTION_BLOCK_HASH_GINDEX` (`capella.BeaconBlockBody`, `execution_payload`, `block_hash`). -/
def EXECUTION_BLOCK_HASH_GINDEX : Nat := 412
/-- `EXECUTION_BLOCK_HASH_GINDEX_DENEB` (`deneb.BeaconBlockBody`, `execution_payload`,
`block_hash`). -/
def EXECUTION_BLOCK_HASH_GINDEX_DENEB : Nat := 812
/-- `EXECUTION_BLOCK_HASH_GINDEX_GLOAS` (`BeaconBlockBody`, `signed_execution_payload_bid`,
`message`, `parent_block_hash`). -/
def EXECUTION_BLOCK_HASH_GINDEX_GLOAS : Nat := 2856

/-- `get_generalized_index(deneb.ExecutionPayloadHeader, "block_hash")`: field 12 of 17 (padded
to 32). -/
def BLOCK_HASH_GINDEX_DENEB : Nat := 32 + 12
/-- `get_generalized_index(capella.ExecutionPayloadHeader, "block_hash")`: field 12 of 15 (padded
to 16). -/
def BLOCK_HASH_GINDEX_CAPELLA : Nat := 16 + 12

-- The branch lengths of `ContainersGloas.lean` are `floorlog2` of these indices.
#guard floorlog2 CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS == syncCommitteeBranchDepth &&
  floorlog2 NEXT_SYNC_COMMITTEE_GINDEX_GLOAS == syncCommitteeBranchDepth &&
  floorlog2 FINALIZED_ROOT_GINDEX_GLOAS == finalityBranchDepth &&
  floorlog2 EXECUTION_BLOCK_HASH_GINDEX_GLOAS == executionBranchDepth
-- The pre-Gloas execution indices are the payload index followed by the header's `block_hash`.
#guard EXECUTION_BLOCK_HASH_GINDEX == EXECUTION_PAYLOAD_GINDEX * 16 + 12 &&
  EXECUTION_BLOCK_HASH_GINDEX_DENEB == EXECUTION_PAYLOAD_GINDEX * 32 + 12

/-! ## Defaults -/

/-- `LightClientHeader()`. -/
def defaultLightClientHeader : LightClientHeader :=
  { beacon := { slot := U64.zero, proposer_index := U64.zero, parent_root := zeroRoot,
                state_root := zeroRoot, body_root := zeroRoot },
    execution_block_hash := zeroRoot, execution_branch := zeroRootVec _ }

/-! ## Fork version and digest -/

/-- `compute_fork_digest` (`specs/fulu/beacon-chain.md`, unchanged in Gloas) with Gloas's
`compute_fork_version`. -/
def computeForkDigest (cfg : Config) (gvr : Root) (epoch : Epoch) : M Bytes := do
  let version ← Gossip.computeForkVersion cfg epoch
  let base := computeForkDataRoot version gvr
  if epoch.toNat < cfg.FULU_FORK_EPOCH then return base.toBytes.take 4
  let bp ← getBlobParameters cfg epoch
  let mask := hash (uintToBytes 8 bp.epoch.toNat ++ uintToBytes 8 bp.maxBlobsPerBlock.toNat)
  pure ((xor base mask).toBytes.take 4)

/-- The fork digests a Gloas object can carry: the digest at `GLOAS_FORK_EPOCH` and at every
later `BLOB_SCHEDULE` epoch. -/
def forkDigests (cfg : Config) (gvr : Root) : M (List Bytes) := do
  let start := cfg.GLOAS_FORK_EPOCH
  let epochs := start :: (cfg.BLOB_SCHEDULE.map (·.EPOCH)).filter (· ≥ start)
  epochs.mapM fun e => do computeForkDigest cfg gvr (← U64.ofNat? e "fork digest epoch")

/-! ## Helpers -/

/-- `compute_merkle_branch_root(leaf, branch, depth, index)` (`specs/phase0/beacon-chain.md`);
`branch[i]` out of range raises. -/
def computeMerkleBranchRoot (leaf : Bytes32) (branch : List Bytes32) (depth index : Nat) :
    M Root := do
  let mut value := leaf
  for i in List.range depth do
    let b ← match branch[i]? with
      | some b => pure b
      | none => throw (.index "compute_merkle_branch_root: branch[i]" i branch.length)
    if index / 2 ^ i % 2 == 1 then value := hashPair b value
    else value := hashPair value b
  pure value

/-- Python's `xs[a:]` for a possibly negative `a`. -/
private def sliceFrom {α : Type} (xs : List α) (a : Int) : List α :=
  if a < 0 then xs.drop (xs.length - a.natAbs) else xs.drop a.toNat

/-- `get_lc_execution_root` (Gloas). -/
def getLcExecutionRoot (cfg : Config) (P : Preset) (header : LightClientHeader) : M Root := do
  let epoch := (← computeEpochAtSlot P header.beacon.slot).toNat
  -- [New in Gloas:EIP7732]
  if epoch ≥ cfg.GLOAS_FORK_EPOCH then return header.execution_block_hash
  let blockHashGindex ←
    if epoch ≥ cfg.DENEB_FORK_EPOCH then do
      if header.beacon.slot == GENESIS_SLOT then
        return hashTreeRoot (defaultExecutionPayloadHeader (P := P))
      pure BLOCK_HASH_GINDEX_DENEB
    else if epoch ≥ cfg.CAPELLA_FORK_EPOCH then do
      if header.beacon.slot == GENESIS_SLOT then
        let e : ExecutionPayloadHeader P := defaultExecutionPayloadHeader
        let c : CapellaExecutionPayloadHeader P :=
          { parent_hash := e.parent_hash, fee_recipient := e.fee_recipient,
            state_root := e.state_root, receipts_root := e.receipts_root,
            logs_bloom := e.logs_bloom, prev_randao := e.prev_randao,
            block_number := e.block_number, gas_limit := e.gas_limit, gas_used := e.gas_used,
            timestamp := e.timestamp, extra_data := e.extra_data,
            base_fee_per_gas := e.base_fee_per_gas, block_hash := e.block_hash,
            transactions_root := e.transactions_root, withdrawals_root := e.withdrawals_root }
        return hashTreeRoot c
      pure BLOCK_HASH_GINDEX_CAPELLA
    else return zeroRoot
  -- [Modified in Gloas:EIP7732]
  let branch := header.execution_branch.toArray.toList
  let inner := branch.take (branch.length - floorlog2 EXECUTION_PAYLOAD_GINDEX)
  let depth := floorlog2 blockHashGindex
  computeMerkleBranchRoot header.execution_block_hash
    (sliceFrom inner ((inner.length : Int) - depth)) depth
    (← getSubtreeIndex blockHashGindex).toNat

/-- `is_valid_light_client_header` (Gloas). -/
def isValidLightClientHeader (cfg : Config) (P : Preset) (header : LightClientHeader) : M Bool := do
  let epoch := (← computeEpochAtSlot P header.beacon.slot).toNat
  let branch := header.execution_branch.toArray.toList
  let check (gindex : Nat) : M Bool :=
    isValidNormalizedMerkleBranch header.execution_block_hash branch gindex header.beacon.body_root
  if epoch ≥ cfg.GLOAS_FORK_EPOCH then return ← check EXECUTION_BLOCK_HASH_GINDEX_GLOAS
  if epoch ≥ cfg.DENEB_FORK_EPOCH then return ← check EXECUTION_BLOCK_HASH_GINDEX_DENEB
  if epoch ≥ cfg.CAPELLA_FORK_EPOCH then return ← check EXECUTION_BLOCK_HASH_GINDEX
  pure (header.execution_block_hash == zeroRoot && header.execution_branch == zeroRootVec _)

/-- `finalized_root_gindex_at_slot` (Gloas). -/
def finalizedRootGindexAtSlot (cfg : Config) (P : Preset) (slot : Slot) : M Nat := do
  let epoch := (← computeEpochAtSlot P slot).toNat
  if epoch ≥ cfg.GLOAS_FORK_EPOCH then return FINALIZED_ROOT_GINDEX_GLOAS
  if epoch ≥ cfg.ELECTRA_FORK_EPOCH then return FINALIZED_ROOT_GINDEX_ELECTRA
  pure FINALIZED_ROOT_GINDEX

/-- `current_sync_committee_gindex_at_slot` (Gloas). -/
def currentSyncCommitteeGindexAtSlot (cfg : Config) (P : Preset) (slot : Slot) : M Nat := do
  let epoch := (← computeEpochAtSlot P slot).toNat
  if epoch ≥ cfg.GLOAS_FORK_EPOCH then return CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS
  if epoch ≥ cfg.ELECTRA_FORK_EPOCH then return CURRENT_SYNC_COMMITTEE_GINDEX_ELECTRA
  pure CURRENT_SYNC_COMMITTEE_GINDEX

/-- `next_sync_committee_gindex_at_slot` (Gloas). -/
def nextSyncCommitteeGindexAtSlot (cfg : Config) (P : Preset) (slot : Slot) : M Nat := do
  let epoch := (← computeEpochAtSlot P slot).toNat
  if epoch ≥ cfg.GLOAS_FORK_EPOCH then return NEXT_SYNC_COMMITTEE_GINDEX_GLOAS
  if epoch ≥ cfg.ELECTRA_FORK_EPOCH then return NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA
  pure NEXT_SYNC_COMMITTEE_GINDEX

/-! ## Store -/

/-- `LightClientStore` (Altair) over the Gloas containers. -/
structure LightClientStore (P : Preset) where
  finalized_header : LightClientHeader
  current_sync_committee : SyncCommittee P
  next_sync_committee : SyncCommittee P
  best_valid_update : Option (LightClientUpdate P)
  optimistic_header : LightClientHeader
  previous_max_active_participants : U64
  current_max_active_participants : U64

/-- `is_sync_committee_update`. -/
def isSyncCommitteeUpdate (u : LightClientUpdate P) : Bool :=
  !(u.next_sync_committee_branch == zeroRootVec _)

/-- `is_finality_update`. -/
def isFinalityUpdate (u : LightClientUpdate P) : Bool :=
  !(u.finality_branch == zeroRootVec _)

/-- `is_next_sync_committee_known`. -/
def isNextSyncCommitteeKnown (s : LightClientStore P) : Bool :=
  !(s.next_sync_committee == defaultSyncCommittee)

/-- `get_safety_threshold`. -/
def getSafetyThreshold (s : LightClientStore P) : M U64 := do
  let m := if s.previous_max_active_participants < s.current_max_active_participants then
    s.current_max_active_participants else s.previous_max_active_participants
  U64.div? m (← c64 2) "get_safety_threshold"

/-- `initialize_light_client_store` (Altair). -/
def initializeLightClientStore (cfg : Config) (trustedBlockRoot : Root)
    (bootstrap : LightClientBootstrap P) : M (LightClientStore P) := do
  require (← isValidLightClientHeader cfg P bootstrap.header)
    "initialize_light_client_store: header"
  require (hashTreeRoot bootstrap.header.beacon == trustedBlockRoot)
    "initialize_light_client_store: trusted block root"
  require (← isValidNormalizedMerkleBranch (hashTreeRoot bootstrap.current_sync_committee)
    bootstrap.current_sync_committee_branch.toArray.toList
    (← currentSyncCommitteeGindexAtSlot cfg P bootstrap.header.beacon.slot)
    bootstrap.header.beacon.state_root) "initialize_light_client_store: sync committee branch"
  pure { finalized_header := bootstrap.header,
         current_sync_committee := bootstrap.current_sync_committee,
         next_sync_committee := defaultSyncCommittee, best_valid_update := none,
         optimistic_header := bootstrap.header, previous_max_active_participants := U64.zero,
         current_max_active_participants := U64.zero }

/-- `validate_light_client_update` (Altair). -/
def validateLightClientUpdate (ctx : Ctx) (store : LightClientStore P) (update : LightClientUpdate P)
    (currentSlot : Slot) (genesisValidatorsRoot : Root) : M Unit := do
  let cfg := ctx.cfg
  let site := "validate_light_client_update"
  let sa := update.sync_aggregate
  require (bitCount sa.sync_committee_bits ≥ P.MIN_SYNC_COMMITTEE_PARTICIPANTS) s!"{site}: participants"
  require (← isValidLightClientHeader cfg P update.attested_header) s!"{site}: attested header"
  let attestedSlot := update.attested_header.beacon.slot
  let finalizedSlot := update.finalized_header.beacon.slot
  require (update.signature_slot ≤ currentSlot && attestedSlot < update.signature_slot &&
    finalizedSlot ≤ attestedSlot) s!"{site}: slots"
  let storePeriod ← computeSyncCommitteePeriodAtSlot P store.finalized_header.beacon.slot
  let sigPeriod ← computeSyncCommitteePeriodAtSlot P update.signature_slot
  if isNextSyncCommitteeKnown store then
    -- the tuple `(store_period, store_period + 1)` is built first
    let nextPeriod ← U64.add? storePeriod U64.one site
    require (sigPeriod == storePeriod || sigPeriod == nextPeriod) s!"{site}: signature period"
  else
    require (sigPeriod == storePeriod) s!"{site}: signature period"
  let attestedPeriod ← computeSyncCommitteePeriodAtSlot P attestedSlot
  let hasNextSyncCommittee := !isNextSyncCommitteeKnown store &&
    (isSyncCommitteeUpdate update && attestedPeriod == storePeriod)
  require (store.finalized_header.beacon.slot < attestedSlot || hasNextSyncCommittee)
    s!"{site}: relevant"
  if !isFinalityUpdate update then
    require (update.finalized_header == defaultLightClientHeader) s!"{site}: empty finalized header"
  else
    let finalizedRoot ←
      if finalizedSlot == GENESIS_SLOT then do
        require (update.finalized_header == defaultLightClientHeader)
          s!"{site}: genesis finalized header"
        pure zeroRoot
      else do
        require (← isValidLightClientHeader cfg P update.finalized_header)
          s!"{site}: finalized header"
        pure (hashTreeRoot update.finalized_header.beacon)
    require (← isValidNormalizedMerkleBranch finalizedRoot update.finality_branch.toArray.toList
      (← finalizedRootGindexAtSlot cfg P attestedSlot) update.attested_header.beacon.state_root)
      s!"{site}: finality branch"
  if !isSyncCommitteeUpdate update then
    require (update.next_sync_committee == defaultSyncCommittee)
      s!"{site}: empty next sync committee"
  else
    if attestedPeriod == storePeriod && isNextSyncCommitteeKnown store then
      require (update.next_sync_committee == store.next_sync_committee)
        s!"{site}: known next committee"
    require (← isValidNormalizedMerkleBranch (hashTreeRoot update.next_sync_committee)
      update.next_sync_committee_branch.toArray.toList
      (← nextSyncCommitteeGindexAtSlot cfg P attestedSlot) update.attested_header.beacon.state_root)
      s!"{site}: next sync committee branch"
  let committee := if sigPeriod == storePeriod then store.current_sync_committee
    else store.next_sync_committee
  let pubkeys :=
    ((sa.sync_committee_bits.bits.zip committee.pubkeys.toArray).filter (·.1)).toList.map (·.2)
  let forkVersionSlot ← U64.sub?
    (if U64.one < update.signature_slot then update.signature_slot else U64.one) U64.one site
  let forkVersion ← Gossip.computeForkVersion cfg (← computeEpochAtSlot P forkVersionSlot)
  let domain := computeDomain DOMAIN_SYNC_COMMITTEE forkVersion genesisValidatorsRoot
  let root := computeSigningRoot update.attested_header.beacon domain
  require (blsFastAggregateVerify ctx.blsActive pubkeys root sa.sync_committee_signature)
    s!"{site}: bls.FastAggregateVerify"

/-- `apply_light_client_update` (Altair). -/
def applyLightClientUpdate (store : LightClientStore P) (update : LightClientUpdate P) :
    M (LightClientStore P) := do
  let site := "apply_light_client_update"
  let storePeriod ← computeSyncCommitteePeriodAtSlot P store.finalized_header.beacon.slot
  let finalizedPeriod ← computeSyncCommitteePeriodAtSlot P update.finalized_header.beacon.slot
  let mut store := store
  if !isNextSyncCommitteeKnown store then
    require (finalizedPeriod == storePeriod) s!"{site}: finalized period"
    store := { store with next_sync_committee := update.next_sync_committee }
  else
    -- `elif`: `store_period + 1` is formed only on this branch
    if finalizedPeriod == (← U64.add? storePeriod U64.one site) then
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
def processLightClientStoreForceUpdate (store : LightClientStore P) (currentSlot : Slot) :
    M (LightClientStore P) := do
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
def isBetterUpdate (P : Preset) (newU oldU : LightClientUpdate P) : M Bool := do
  let maxActive := newU.sync_aggregate.sync_committee_bits.bits.size
  let newN := bitCount newU.sync_aggregate.sync_committee_bits
  let oldN := bitCount oldU.sync_aggregate.sync_committee_bits
  let newSuper := newN * 3 ≥ maxActive * 2
  let oldSuper := oldN * 3 ≥ maxActive * 2
  if newSuper != oldSuper then return newSuper
  if !newSuper && newN != oldN then return decide (newN > oldN)
  let period := computeSyncCommitteePeriodAtSlot P
  -- `and` short-circuits: the periods are computed only for a sync committee update
  let newRelevant ← if isSyncCommitteeUpdate newU then do
      pure ((← period newU.attested_header.beacon.slot) == (← period newU.signature_slot))
    else pure false
  let oldRelevant ← if isSyncCommitteeUpdate oldU then do
      pure ((← period oldU.attested_header.beacon.slot) == (← period oldU.signature_slot))
    else pure false
  if newRelevant != oldRelevant then return newRelevant
  let newFin := isFinalityUpdate newU
  let oldFin := isFinalityUpdate oldU
  if newFin != oldFin then return newFin
  if newFin then
    let newScf :=
      (← period newU.finalized_header.beacon.slot) == (← period newU.attested_header.beacon.slot)
    let oldScf :=
      (← period oldU.finalized_header.beacon.slot) == (← period oldU.attested_header.beacon.slot)
    if newScf != oldScf then return newScf
  if newN != oldN then return decide (newN > oldN)
  if newU.attested_header.beacon.slot != oldU.attested_header.beacon.slot then
    return decide (newU.attested_header.beacon.slot < oldU.attested_header.beacon.slot)
  pure (decide (newU.signature_slot < oldU.signature_slot))

/-- `process_light_client_update` (Altair). -/
def processLightClientUpdate (ctx : Ctx) (store : LightClientStore P) (update : LightClientUpdate P)
    (currentSlot : Slot) (genesisValidatorsRoot : Root) : M (LightClientStore P) := do
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
  let hasFinalizedNext ←
    if !isNextSyncCommitteeKnown store && isSyncCommitteeUpdate update && isFinalityUpdate update
    then do
      pure ((← period update.finalized_header.beacon.slot) ==
        (← period update.attested_header.beacon.slot))
    else pure false
  if n * 3 ≥ bits.bits.size * 2 &&
      (store.finalized_header.beacon.slot < update.finalized_header.beacon.slot || hasFinalizedNext)
  then
    store ← applyLightClientUpdate store update
    store := { store with best_valid_update := none }
  pure store

/-- `process_light_client_finality_update` (Altair). -/
def processLightClientFinalityUpdate (ctx : Ctx) (store : LightClientStore P)
    (finalityUpdate : LightClientFinalityUpdate P) (currentSlot : Slot)
    (genesisValidatorsRoot : Root) : M (LightClientStore P) := do
  let update : LightClientUpdate P :=
    { attested_header := finalityUpdate.attested_header,
      next_sync_committee := defaultSyncCommittee,
      next_sync_committee_branch := zeroRootVec _,
      finalized_header := finalityUpdate.finalized_header,
      finality_branch := finalityUpdate.finality_branch,
      sync_aggregate := finalityUpdate.sync_aggregate,
      signature_slot := finalityUpdate.signature_slot }
  processLightClientUpdate ctx store update currentSlot genesisValidatorsRoot

/-- `process_light_client_optimistic_update` (Altair). -/
def processLightClientOptimisticUpdate (ctx : Ctx) (store : LightClientStore P)
    (optimisticUpdate : LightClientOptimisticUpdate P) (currentSlot : Slot)
    (genesisValidatorsRoot : Root) : M (LightClientStore P) := do
  let update : LightClientUpdate P :=
    { attested_header := optimisticUpdate.attested_header,
      next_sync_committee := defaultSyncCommittee,
      next_sync_committee_branch := zeroRootVec _,
      finalized_header := defaultLightClientHeader,
      finality_branch := zeroRootVec _,
      sync_aggregate := optimisticUpdate.sync_aggregate,
      signature_slot := optimisticUpdate.signature_slot }
  processLightClientUpdate ctx store update currentSlot genesisValidatorsRoot

end JauneConsensus.Gloas
