import JauneConsensus.GloasLightClientFullNode
import JauneConsensus.GloasTransition
import JauneConsensus.GloasBlock
import JauneConsensus.Harness.LightClientDataCollection

/-!
# `light_client/data_collection` at Gloas (harness only)

Goal `eip8282-gloas-cross-layer-v1`, unit U7c. The Gloas copy of
`Harness/LightClientDataCollection.lean`: the same transcription of the generator's
`tests/core/pyspec/eth_consensus_specs/test/helpers/light_client_data_collection.py`
(`consensus-specs` `v1.7.0-beta.4`, CC0), definition for definition and in the same order of
operations (see that module's note for the cached-data mutation, the pruning at finalization and
the aliasing of advanced checkpoint states, all kept here), over the Gloas containers:

* the blocks run through the Gloas `state_transition` (`Gloas.stateTransitionWith` with U3's
  `processEpoch` and U4's `processBlock`, `GloasTransition.lean`), BLS verified as for
  `bls_setting` 0, and a stored checkpoint state advances by the Gloas `process_slots`;
* headers, Merkle branches and ranking are U7b's (`GloasLightClientFullNode.lean`,
  `GloasLightClient.lean`): `block_to_light_client_header`, the Gloas progressive `BeaconState`
  proof tree, the `*_gindex_at_slot` helpers, `is_better_update`; `latest_*_gindex` are the
  `*_GINDEX_GLOAS` constants and `latest_normalize_merkle_branch` is `normalize_merkle_branch`;
* `create_signed_genesis_block` (`helpers/genesis.py`) sets the Gloas genesis body's
  `signed_execution_payload_bid.message` to `state.latest_execution_payload_bid`;
* a served object's `fork_digest` is the Gloas `compute_fork_digest` (`Gloas.computeForkDigest`)
  at the epoch of its slot.

The pinned case (`minimal/gloas/light_client/data_collection`) has `GLOAS_FORK_EPOCH: 0` and no
`phases`, so it never crosses a fork: every object is a Gloas object and the helper's
`upgrade_lc_*_to_new_spec` calls are the identity (a Gloas `initial_state` is the only input this
harness decodes). Its `config.yaml` steps the `BLOB_SCHEDULE` every epoch, so the fork digest
changes from epoch to epoch within the fork.

The type-independent pieces (`Dict`, `BlockID`) are the Electra/Fulu module's.
-/

namespace JauneConsensus.Harness.GloasDataCollection
open Jaune (Bytes B256)
open JauneConsensus
open JauneConsensus.Harness.DataCollection (Dict BlockID)
open Yaml

/-! ## State of the collection -/

variable {P : Preset}

/-- `CachedLightClientData`. -/
structure Cached (P : Preset) where
  currentSyncCommitteeBranch : List Root
  nextSyncCommitteeBranch : List Root
  finalizedSlot : Slot
  finalityBranch : List Root
  currentPeriodBestUpdate : Option (Gloas.LightClientUpdate P)
  latestSignatureSlot : Slot

/-- `LightClientDataCollectionTest` with its `LightClientDataStore` (cache and DB) flattened. -/
structure Test (P : Preset) where
  cfg : Config
  ctx : Ctx
  blocks : Dict Root (Gloas.SignedBeaconBlock P)
  finalizedBlockRoots : Dict Nat Root
  states : Dict Root (Gloas.BeaconState P)
  finalizedCheckpointStates : Dict Root (Gloas.BeaconState P)
  /-- The `states` wrappers rebound by an in-place advance (see the Electra/Fulu module note). -/
  advanced : Dict Root (Gloas.BeaconState P)
  /-- State roots whose `finalized_checkpoint_states` entry is the `states` wrapper. -/
  aliased : List Root
  latestFinalizedEpoch : Epoch
  latestFinalizedBid : BlockID
  historicalTailSlot : Slot
  -- `lc_data_store.cache`
  cacheData : Dict BlockID (Cached P)
  latest : Option (Gloas.LightClientFinalityUpdate P)
  tailSlot : Slot
  -- `lc_data_store.db`
  headers : Dict Root Gloas.LightClientHeader
  currentBranches : Dict Nat (List Root)
  syncCommittees : Dict Nat (Option (SyncCommittee P))
  bestUpdates : Dict Nat (Gloas.LightClientUpdate P)

/-- The collection monad: the test state, failing with a reason. -/
abbrev DC (P : Preset) := StateT (Test P) (Except String)

/-- Run a specification computation, its rejection a failure. -/
def lift {α : Type} (x : M α) (what : String) : DC P α :=
  match x with
  | .ok v => pure v
  | .error e => throw s!"{what}: rejected: {repr e}"

def cfgOf : DC P Config := do pure (← get).cfg

/-- A key that must be present (`KeyError` otherwise). -/
def need {κ α : Type} [BEq κ] [ToString κ] (d : Dict κ α) (k : κ) (what : String) : DC P α :=
  match d.get? k with
  | some v => pure v
  | none => throw s!"KeyError: {what}[{k}]"

def toVec {n : Nat} (xs : List Root) (what : String) : DC P (SszVector Bytes32 n) :=
  lift (SszVector.ofArray xs.toArray what) what

/-! ## Slot helpers -/

def periodAt (slot : Slot) : DC P U64 :=
  lift (computeSyncCommitteePeriodAtSlot P slot) "compute_sync_committee_period_at_slot"

def startSlotAtEpoch (epoch : Epoch) : DC P Slot :=
  lift (computeStartSlotAtEpoch P epoch) "compute_start_slot_at_epoch"

/-- `compute_start_slot_at_sync_committee_period` (`helpers/light_client.py`). -/
def startSlotAtPeriod (period : U64) : DC P Slot := do
  startSlotAtEpoch (← lift (do U64.mul? period (← c64 P.EPOCHS_PER_SYNC_COMMITTEE_PERIOD))
    "sync_committee_period * EPOCHS_PER_SYNC_COMMITTEE_PERIOD")

/-- `_next_epoch_boundary_slot`. -/
def nextEpochBoundarySlot (slot : Slot) : DC P Slot := do
  let s ← lift (do U64.sub? (← U64.add? slot (← c64 P.SLOTS_PER_EPOCH)) U64.one)
    "slot + SLOTS_PER_EPOCH - 1"
  startSlotAtEpoch (← lift (computeEpochAtSlot P s) "compute_epoch_at_slot")

def maxSlot (a b : Slot) : Slot := if a < b then b else a

/-- `_block_to_block_id`. -/
def blockToBlockId (block : Gloas.SignedBeaconBlock P) : BlockID :=
  { slot := block.message.slot, root := hashTreeRoot block.message }

/-- `_state_to_block_id`. -/
def stateToBlockId (state : Gloas.BeaconState P) : BlockID :=
  { slot := state.latest_block_header.slot, root := hashTreeRoot (Gloas.stateBlockHeader state) }

/-! ## History access -/

/-- `get_ancestor_of_block_id`: `None` on a missing block (`KeyError`). Parent slots strictly
decrease, so the walk is bounded by the number of blocks (fuel). -/
def getAncestorOfBlockId (bid : BlockID) (slot : Slot) : DC P (Option BlockID) := do
  let t ← get
  let some b := t.blocks.get? bid.root | return none
  let mut block := b
  for _ in [0:t.blocks.length + 1] do
    if block.message.slot ≤ slot then return some (blockToBlockId block)
    match t.blocks.get? block.message.parent_root with
    | some p => block := p
    | none => return none
  throw "get_ancestor_of_block_id: walk bound"

/-- `_block_id_at_finalized_slot`. -/
def blockIdAtFinalizedSlot (slot : Slot) : DC P (Option BlockID) := do
  let t ← get
  let mut s := slot
  for _ in [0:slot.toNat + 2] do
    if s < t.historicalTailSlot then return none
    match t.finalizedBlockRoots.get? s.toNat with
    | some r => return some { slot := s, root := r }
    | none => s ← lift (U64.sub? s U64.one) "_block_id_at_finalized_slot: slot - 1"
  throw "_block_id_at_finalized_slot: walk bound"

/-- `_get_current_sync_committee_for_finalized_period`. -/
def currentSyncCommitteeForFinalizedPeriod (period : U64) : DC P (Option (SyncCommittee P)) := do
  let t ← get
  let lowSlot := maxSlot t.historicalTailSlot
    (← startSlotAtEpoch (← lift (U64.ofNat? t.cfg.ALTAIR_FORK_EPOCH) "ALTAIR_FORK_EPOCH"))
  if period < (← periodAt lowSlot) then return none
  let periodStartSlot ← startSlotAtPeriod period
  let syncCommitteeSlot := maxSlot periodStartSlot lowSlot
  let some bid ← blockIdAtFinalizedSlot syncCommitteeSlot | return none
  let block ← need t.blocks bid.root "blocks"
  let state ← need t.finalizedCheckpointStates block.message.state_root
    "finalized_checkpoint_states"
  if state.slot < syncCommitteeSlot then
    -- `transition_across_forks(state.spec, state.data, sync_committee_slot)`: one fork, so
    -- `transition_to`, i.e. the Gloas `process_slots`; the wrapper is rebound, and so is the
    -- aliased `states` entry
    let root := block.message.state_root
    let post ← lift (Gloas.processSlotsWith (Gloas.processEpoch t.ctx) state syncCommitteeSlot)
      "transition_across_forks"
    modify fun t => { t with
      finalizedCheckpointStates := t.finalizedCheckpointStates.put root post,
      advanced := if t.aliased.contains root && (t.states.get? root).isSome then
        t.advanced.put root post else t.advanced }
    return some post.current_sync_committee
  pure (some state.current_sync_committee)

/-- `_light_client_header_for_block_id`. -/
def headerForBlockId (bid : BlockID) : DC P Gloas.LightClientHeader := do
  let t ← get
  let block ← need t.blocks bid.root "blocks"
  lift (Gloas.blockToLightClientHeader block) "block_to_light_client_header"

/-- `_get_light_client_data`. -/
def getLightClientData (bid : BlockID) : DC P (Cached P) := do
  match (← get).cacheData.get? bid with
  | some d => pure d
  | none => throw "Trying to get light client data that was not cached"

/-- `_cache_lc_data`, with `latest_normalize_merkle_branch` and the `*_GINDEX_GLOAS` constants. -/
def cacheLcData (state : Gloas.BeaconState P) (bid : BlockID)
    (currentPeriodBestUpdate : Option (Gloas.LightClientUpdate P)) (latestSignatureSlot : Slot) :
    DC P Unit := do
  let cfg ← cfgOf
  let tree := Gloas.BeaconState.proofTree state
  let proof (g : M Nat) (what : String) : DC P (List Root) := do
    lift (do computeMerkleProof tree (← g)) s!"compute_merkle_proof ({what})"
  let cached : Cached P :=
    { currentSyncCommitteeBranch := normalizeMerkleBranch
        (← proof (Gloas.currentSyncCommitteeGindexAtSlot cfg P state.slot) "current_sync_committee")
        Gloas.CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS,
      nextSyncCommitteeBranch := normalizeMerkleBranch
        (← proof (Gloas.nextSyncCommitteeGindexAtSlot cfg P state.slot) "next_sync_committee")
        Gloas.NEXT_SYNC_COMMITTEE_GINDEX_GLOAS,
      finalizedSlot := ← startSlotAtEpoch state.finalized_checkpoint.epoch,
      finalityBranch := normalizeMerkleBranch
        (← proof (Gloas.finalizedRootGindexAtSlot cfg P state.slot) "finalized_root")
        Gloas.FINALIZED_ROOT_GINDEX_GLOAS,
      currentPeriodBestUpdate, latestSignatureSlot }
  if ((← get).cacheData.get? bid).isSome then throw "Redundant `_cache_lc_data` call"
  modify fun t => { t with cacheData := t.cacheData.put bid cached }

/-! ## Creating light client data -/

/-- `_create_lc_finality_update_from_lc_data`. -/
def createLcFinalityUpdateFromLcData (attestedBid : BlockID) (signatureSlot : Slot)
    (syncAggregate : SyncAggregate P) : DC P (Gloas.LightClientFinalityUpdate P) := do
  let attestedHeader ← headerForBlockId attestedBid
  let attestedData ← getLightClientData attestedBid
  let some finalizedBid ← blockIdAtFinalizedSlot attestedData.finalizedSlot
    | throw "_create_lc_finality_update_from_lc_data: finalized_header unbound (no finalized block)"
  if finalizedBid.slot != attestedData.finalizedSlot then
    -- Empty slots at end of epoch, update cache for latest block slot
    let moved : Cached P := { attestedData with finalizedSlot := finalizedBid.slot }
    modify fun t => { t with cacheData := t.cacheData.put attestedBid moved }
  let finalizedHeader ←
    if finalizedBid.slot == GENESIS_SLOT then pure Gloas.defaultLightClientHeader
    else headerForBlockId finalizedBid
  pure { attested_header := attestedHeader, finalized_header := finalizedHeader,
         finality_branch := ← toVec attestedData.finalityBranch "FinalityBranch",
         sync_aggregate := syncAggregate, signature_slot := signatureSlot }

/-- `_create_lc_update_from_lc_data`. -/
def createLcUpdateFromLcData (attestedBid : BlockID) (signatureSlot : Slot)
    (syncAggregate : SyncAggregate P) (nextSyncCommittee : SyncCommittee P) :
    DC P (Gloas.LightClientUpdate P) := do
  let fu ← createLcFinalityUpdateFromLcData attestedBid signatureSlot syncAggregate
  let attestedData ← getLightClientData attestedBid
  pure { attested_header := fu.attested_header, next_sync_committee := nextSyncCommittee,
         next_sync_committee_branch :=
           ← toVec attestedData.nextSyncCommitteeBranch "NextSyncCommitteeBranch",
         finalized_header := fu.finalized_header, finality_branch := fu.finality_branch,
         sync_aggregate := fu.sync_aggregate, signature_slot := fu.signature_slot }

/-- `_create_lc_update`: the update a block's sync aggregate gives its parent, and the best one
of the period so far, cached for the block. -/
def createLcUpdate (state : Gloas.BeaconState P) (block : Gloas.SignedBeaconBlock P)
    (parentBid : BlockID) : DC P Unit := do
  -- Verify attested block (parent) is recent enough and that state is available
  let attestedBid := parentBid
  let attestedSlot := attestedBid.slot
  if attestedSlot < (← get).tailSlot then
    cacheLcData state (blockToBlockId block) none GENESIS_SLOT
    return
  -- If sync committee period changed, reset `best`
  let attestedPeriod ← periodAt attestedSlot
  let signatureSlot := block.message.slot
  let signaturePeriod ← periodAt signatureSlot
  let attestedData ← getLightClientData attestedBid
  let best := if attestedPeriod != signaturePeriod then none else attestedData.currentPeriodBestUpdate
  -- If sync committee does not have sufficient participants, do not bump latest
  let syncAggregate := block.message.body.sync_aggregate
  let numActiveParticipants := bitCount syncAggregate.sync_committee_bits
  let latestSignatureSlot := if numActiveParticipants < P.MIN_SYNC_COMMITTEE_PARTICIPANTS then
    attestedData.latestSignatureSlot else signatureSlot
  -- To update `best`, sync committee must have sufficient participants, and
  -- `signature_slot` must be in `attested_slot`'s sync committee period
  if numActiveParticipants < P.MIN_SYNC_COMMITTEE_PARTICIPANTS ||
      attestedPeriod != signaturePeriod then
    cacheLcData state (blockToBlockId block) best latestSignatureSlot
    return
  -- Check if light client data improved
  let update ← createLcUpdateFromLcData attestedBid signatureSlot syncAggregate
    state.next_sync_committee
  let isBetter ← match best with
    | none => pure true
    | some b => lift (Gloas.isBetterUpdate P update b) "is_better_update"
  -- Update best light client data for current sync committee period
  let best := if isBetter then some update else best
  cacheLcData state (blockToBlockId block) best latestSignatureSlot

/-- `_create_lc_bootstrap`. -/
def createLcBootstrap (bid : BlockID) : DC P Unit := do
  let t ← get
  let block ← need t.blocks bid.root "blocks"
  let period ← periodAt bid.slot
  if (t.syncCommittees.get? period.toNat).isNone then
    let sc ← currentSyncCommitteeForFinalizedPeriod period
    modify fun t => { t with syncCommittees := t.syncCommittees.put period.toNat sc }
  let header ← lift (Gloas.blockToLightClientHeader block) "block_to_light_client_header"
  modify fun t => { t with headers := t.headers.put bid.root header }
  let branch := (← getLightClientData bid).currentSyncCommitteeBranch
  modify fun t => { t with currentBranches := t.currentBranches.put bid.slot.toNat branch }

/-- `_process_new_block_for_light_client` (Gloas is post-Altair). -/
def processNewBlockForLightClient (state : Gloas.BeaconState P) (block : Gloas.SignedBeaconBlock P)
    (parentBid : BlockID) : DC P Unit := do
  if block.message.slot < (← get).tailSlot then return
  createLcUpdate state block parentBid

/-- The second half of `_process_head_change_for_light_client`: the new
`cache.latest`, `None` wherever the helper resets it. -/
def latestFinalityUpdate (headBid : BlockID) (lowSlot : Slot) :
    DC P (Option (Gloas.LightClientFinalityUpdate P)) := do
  let headData ← getLightClientData headBid
  let signatureSlot := headData.latestSignatureSlot
  if signatureSlot ≤ lowSlot then return none
  let some signatureBid ← getAncestorOfBlockId headBid signatureSlot | return none
  if signatureBid.slot ≤ lowSlot then return none
  let some attestedBid ← getAncestorOfBlockId signatureBid
      (← lift (U64.sub? signatureBid.slot U64.one) "signature_bid.slot - 1") | return none
  if attestedBid.slot < lowSlot then return none
  let syncAggregate := (← need (← get).blocks signatureBid.root "blocks").message.body.sync_aggregate
  some <$> createLcFinalityUpdateFromLcData attestedBid signatureSlot syncAggregate

/-- `_process_head_change_for_light_client`. -/
def processHeadChangeForLightClient (headBid oldFinalizedBid : BlockID) : DC P Unit := do
  let t ← get
  if headBid.slot < t.tailSlot then return
  -- Commit best light client data for non-finalized periods
  let headPeriod ← periodAt headBid.slot
  let lowSlot := maxSlot t.tailSlot oldFinalizedBid.slot
  let lowPeriod ← periodAt lowSlot
  let mut bid := headBid
  -- `for period in reversed(range(low_period, head_period + 1))`
  for k in [0:headPeriod.toNat + 1 - lowPeriod.toNat] do
    let period ← lift (U64.ofNat? (headPeriod.toNat - k)) "period"
    let periodEndSlot ← lift (do U64.sub? (← computeStartSlotAtEpoch P (← U64.mul?
      (← U64.add? period U64.one) (← c64 P.EPOCHS_PER_SYNC_COMMITTEE_PERIOD))) U64.one)
      "compute_start_slot_at_sync_committee_period(period + 1) - 1"
    let some b ← getAncestorOfBlockId bid periodEndSlot | break
    bid := b
    if bid.slot < lowSlot then break
    let best := (← getLightClientData bid).currentPeriodBestUpdate
    match best with
    | some u =>
      if bitCount u.sync_aggregate.sync_committee_bits < P.MIN_SYNC_COMMITTEE_PARTICIPANTS then
        modify fun t => { t with bestUpdates := t.bestUpdates.del period.toNat }
      else modify fun t => { t with bestUpdates := t.bestUpdates.put period.toNat u }
    | none => modify fun t => { t with bestUpdates := t.bestUpdates.del period.toNat }
  -- Update latest light client data
  let latest ← latestFinalityUpdate headBid lowSlot
  modify fun t => { t with latest := latest }

/-- `_process_finalization_for_light_client`. -/
def processFinalizationForLightClient (finalizedBid oldFinalizedBid : BlockID) : DC P Unit := do
  let finalizedSlot := finalizedBid.slot
  if finalizedSlot < (← get).tailSlot then return
  -- Cache `LightClientBootstrap` for newly finalized epoch boundary blocks
  let firstNewSlot ← lift (U64.add? oldFinalizedBid.slot U64.one) "old_finalized_bid.slot + 1"
  let lowSlot := maxSlot firstNewSlot (← get).tailSlot
  let mut boundarySlot := finalizedSlot
  -- each round strictly lowers `boundary_slot`, so `finalized_slot + 1` rounds bound the loop
  for _ in [0:finalizedSlot.toNat + 1] do
    if boundarySlot < lowSlot then break
    let some bid ← blockIdAtFinalizedSlot boundarySlot | break
    if lowSlot ≤ bid.slot then createLcBootstrap bid
    boundarySlot ← nextEpochBoundarySlot bid.slot
    if boundarySlot.toNat < P.SLOTS_PER_EPOCH then break
    boundarySlot ← lift (do U64.sub? boundarySlot (← c64 P.SLOTS_PER_EPOCH))
      "boundary_slot - SLOTS_PER_EPOCH"
  -- Prune light client data that is no longer referable by future updates
  modify fun t => { t with cacheData := t.cacheData.filter (fun e => !(e.1.slot < finalizedBid.slot)) }

/-! ## Serving light client data -/

/-- `get_light_client_bootstrap`. -/
def getLightClientBootstrap (blockRoot : Root) : DC P (Option (Gloas.LightClientBootstrap P)) := do
  let t ← get
  let some header := t.headers.get? blockRoot | return none
  let slot := header.beacon.slot
  let period ← periodAt slot
  let some sc ← need t.syncCommittees period.toNat "sync_committees"
    | throw "LightClientBootstrap(current_sync_committee=None)"
  let branch ← need t.currentBranches slot.toNat "current_branches"
  pure (some { header, current_sync_committee := sc,
               current_sync_committee_branch := ← toVec branch "CurrentSyncCommitteeBranch" })

/-- `get_light_client_optimistic_update`. -/
def optimisticOf (u : Gloas.LightClientFinalityUpdate P) : Gloas.LightClientOptimisticUpdate P :=
  { attested_header := u.attested_header, sync_aggregate := u.sync_aggregate,
    signature_slot := u.signature_slot }

/-! ## Test driving -/

/-- `create_signed_genesis_block(spec, state)` (`helpers/genesis.py`) at Gloas:
`SignedBeaconBlock(message=BeaconBlock(state_root=hash_tree_root(state), body=body))`, `body`
being `BeaconBlockBody()` (every field at its default) with
`body.signed_execution_payload_bid.message = state.latest_execution_payload_bid`. -/
def signedGenesisBlock (state : Gloas.BeaconState P) : Gloas.SignedBeaconBlock P :=
  let body : Gloas.BeaconBlockBody P :=
    { randao_reveal := zeroBytesVec 96,
      eth1_data := { deposit_root := zeroRoot, deposit_count := U64.zero, block_hash := zeroRoot },
      graffiti := zeroRoot, proposer_slashings := ProgressiveListS.empty,
      attester_slashings := ProgressiveListS.empty, attestations := ProgressiveListS.empty,
      deposits := ProgressiveListS.empty, voluntary_exits := ProgressiveListS.empty,
      sync_aggregate :=
        { sync_committee_bits := ⟨Array.replicate P.SYNC_COMMITTEE_SIZE false, by simp⟩,
          sync_committee_signature := zeroBytesVec 96 },
      bls_to_execution_changes := ProgressiveListS.empty,
      signed_execution_payload_bid :=
        { message := state.latest_execution_payload_bid, signature := zeroBytesVec 96 },
      payload_attestations := ProgressiveListS.empty,
      parent_execution_requests := Gloas.ExecutionRequests.empty }
  { message := { slot := U64.zero, proposer_index := U64.zero, parent_root := zeroRoot,
                 state_root := hashTreeRoot state, body },
    signature := zeroBytesVec 96 }

/-- `setup_lc_data_collection_test`. -/
def setup (cfg : Config) (ctx : Ctx) (state : Gloas.BeaconState P) : Except String (Test P) := do
  let run {α : Type} (x : M α) (what : String) : Except String α :=
    x.mapError fun e => s!"{what}: rejected: {repr e}"
  let spe ← run (c64 P.SLOTS_PER_EPOCH) "SLOTS_PER_EPOCH"
  if (← run (U64.mod? state.slot spe) "slot % SLOTS_PER_EPOCH") != U64.zero then
    throw "initial_state is not epoch aligned"
  let altairStart ← run (do computeStartSlotAtEpoch P (← U64.ofNat? cfg.ALTAIR_FORK_EPOCH))
    "ALTAIR_FORK_EPOCH"
  let t0 : Test P :=
    { cfg, ctx, blocks := [], finalizedBlockRoots := [], states := [],
      finalizedCheckpointStates := [], advanced := [], aliased := [],
      latestFinalizedEpoch := state.finalized_checkpoint.epoch,
      latestFinalizedBid := { slot := ← run (computeStartSlotAtEpoch P state.finalized_checkpoint.epoch)
                                "compute_start_slot_at_epoch",
                              root := state.finalized_checkpoint.root },
      historicalTailSlot := state.slot,
      cacheData := [], latest := none, tailSlot := maxSlot state.slot altairStart,
      headers := [], currentBranches := [], syncCommittees := [], bestUpdates := [] }
  let bid := stateToBlockId state
  let stateRoot := hashTreeRoot state
  let t1 := { t0 with blocks := t0.blocks.put bid.root (signedGenesisBlock state),
                      finalizedBlockRoots := t0.finalizedBlockRoots.put bid.slot.toNat bid.root,
                      states := t0.states.put stateRoot state,
                      finalizedCheckpointStates := t0.finalizedCheckpointStates.put stateRoot state }
  let go : DC P Unit := do
    cacheLcData state bid none GENESIS_SLOT
    createLcBootstrap bid
  (·.2) <$> go.run t1

/-- `add_new_block`, given the imported block: its parent's post-state is the state the
generator built on, and the Gloas `state_transition` gives the block's post-state. -/
def addNewBlock (block : Gloas.SignedBeaconBlock P) : DC P Unit := do
  let t ← get
  let parent ← need t.blocks block.message.parent_root "blocks"
  let state ← need t.states parent.message.state_root "states"
  let parentBid := stateToBlockId state
  let ctx := t.ctx
  let post ← lift (Gloas.stateTransitionWith (Gloas.processEpoch ctx) (Gloas.processBlock ctx)
    ctx.blsActive state block) "state_transition"
  let bid := blockToBlockId block
  modify fun t => { t with blocks := t.blocks.put bid.root block,
                           states := t.states.put block.message.state_root post,
                           advanced := t.advanced.del block.message.state_root,
                           aliased := t.aliased.filter (· != block.message.state_root) }
  processNewBlockForLightClient post block parentBid

/-- `test.states[root]`: the wrapper's current data (rebound by an in-place advance). -/
def stateView (root : Root) : DC P (Gloas.BeaconState P) := do
  let t ← get
  match t.advanced.get? root with
  | some s => pure s
  | none => need t.states root "states"

/-- `select_new_head`, up to the checks. -/
def selectNewHead (headBid : BlockID) : DC P Unit := do
  let oldFinalizedBid := (← get).latestFinalizedBid
  processHeadChangeForLightClient headBid oldFinalizedBid
  -- Process finalization
  let t ← get
  let headBlock ← need t.blocks headBid.root "blocks"
  let headState ← stateView headBlock.message.state_root
  if headState.finalized_checkpoint.epoch == GENESIS_EPOCH then return
  let mut block ← need t.blocks headState.finalized_checkpoint.root "blocks"
  let mut bid := blockToBlockId block
  let newFinalizedBid := bid
  if !(oldFinalizedBid.slot < newFinalizedBid.slot) then return
  let mut oldFinalizedEpoch : Option Epoch := none
  let newFinalizedEpoch := headState.finalized_checkpoint.epoch
  for _ in [0:t.blocks.length + 1] do
    if !((← get).latestFinalizedBid.slot < bid.slot) then break
    modify fun t => { t with finalizedBlockRoots := t.finalizedBlockRoots.put bid.slot.toNat bid.root }
    let finalizedEpoch ← lift (do computeEpochAtSlot P (← U64.sub?
      (← U64.add? bid.slot (← c64 P.SLOTS_PER_EPOCH)) U64.one)) "compute_epoch_at_slot"
    if oldFinalizedEpoch != some finalizedEpoch then
      let state ← stateView block.message.state_root
      modify fun t => { t with
        finalizedCheckpointStates := t.finalizedCheckpointStates.put block.message.state_root state,
        aliased := if t.aliased.contains block.message.state_root then t.aliased
          else block.message.state_root :: t.aliased }
      oldFinalizedEpoch := some finalizedEpoch
    block ← need (← get).blocks block.message.parent_root "blocks"
    bid := blockToBlockId block
  if (← get).latestFinalizedBid.slot < bid.slot then throw "select_new_head: walk bound"
  modify fun t => { t with latestFinalizedEpoch := newFinalizedEpoch,
                           latestFinalizedBid := newFinalizedBid }
  processFinalizationForLightClient newFinalizedBid oldFinalizedBid
  modify fun t => { t with
    blocks := t.blocks.filter (fun e => !(e.2.message.slot < newFinalizedBid.slot)),
    states := t.states.filter (fun e =>
      !((match t.advanced.get? e.1 with | some a => a | none => e.2).slot < newFinalizedBid.slot)) }
  modify fun t => { t with
    advanced := t.advanced.filter (fun e => (t.states.get? e.1).isSome),
    aliased := t.aliased.filter (fun r => (t.states.get? r).isSome) }

/-! ## Checks -/

/-- The case files, Snappy-decoded, by name without the extension. -/
abbrev Files := Dict String Bytes

private def y {α : Type} (x : Res α) : Except String α := x.mapError toString

private def root32 (v : YVal) : Except String B256 := do
  let bs ← y v.asHex
  if bs.length = 32 then pure (Jaune.Bytes.toB256 bs) else throw "expected 32 bytes"

private def scalarText (v : YVal) (what : String) : Except String String :=
  match v with
  | .scalar s _ => pure s
  | _ => throw s!"{what}: expected a scalar"

/-- Check one encoded object (`_encode_lc_object`): its `fork_digest` is the Gloas
`compute_fork_digest` at the epoch of `slot`, its file name is `{prefix}_{slot}_{hash_tree_root}`,
and the file holds exactly its serialization. -/
def checkObject {α : Type} [Ssz α] (cfg : Config) (gvr : Root) (files : Files)
    (pre : String) (obj : α) (slot : Slot) (entry : YVal) : Except String Unit := do
  y (entry.expectKeys ["fork_digest", "data"])
  let digest ← y ((entry.field "fork_digest").bind YVal.asHex)
  let expected ← (do Gloas.computeForkDigest cfg gvr (← computeEpochAtSlot P slot) : M Bytes).mapError
    fun e => s!"{pre}: compute_fork_digest: {repr e}"
  if digest != expected then throw s!"{pre}: fork_digest {digest} != {expected}"
  let name ← scalarText (← y (entry.field "data")) s!"{pre}.data"
  let want := s!"{pre}_{slot.toNat}_0x{(hashTreeRoot obj).toHex}"
  if name.toLower != want.toLower then throw s!"{pre}: file {name}, computed object is {want}"
  let some bytes := files.get? name | throw s!"{pre}: no file {name}.ssz_snappy"
  if bytes != serialize obj then throw s!"{pre}: {name} differs from the computed object"

/-- The checks of a `new_head` step against the collected data. -/
def checkHead (files : Files) (gvr : Root) (headBid : BlockID) (checks : YVal) : DC P Unit := do
  let t ← get
  let ex {α : Type} (x : Except String α) : DC P α := match x with
    | .ok v => pure v
    | .error e => throw e
  let obj {α : Type} [Ssz α] (pre : String) (o : α) (slot : Slot) (v : YVal) : DC P Unit :=
    ex (checkObject (P := P) t.cfg gvr files pre o slot v)
  let finality := t.latest
  let keys := ["latest_finalized_checkpoint", "bootstraps", "best_updates"] ++
    (if finality.isSome then ["latest_finality_update", "latest_optimistic_update"] else [])
  ex (y (checks.expectKeys keys))
  -- latest_finalized_checkpoint
  let lfc ← ex (y (checks.field "latest_finalized_checkpoint"))
  ex (y (lfc.expectKeys ["epoch", "root"]))
  let epoch ← ex (y ((lfc.field "epoch").bind YVal.asNat))
  let root ← ex (root32 (← ex (y (lfc.field "root"))))
  if epoch != t.latestFinalizedEpoch.toNat then
    throw s!"latest_finalized_checkpoint.epoch {epoch} != {t.latestFinalizedEpoch.toNat}"
  if root != t.latestFinalizedBid.root then throw "latest_finalized_checkpoint.root differs"
  -- bootstraps, one per finalized checkpoint state in insertion order
  let entries ← ex (y ((checks.field "bootstraps").bind YVal.asSeq))
  if entries.length != t.finalizedCheckpointStates.length then
    throw s!"bootstraps: {entries.length} entries, {t.finalizedCheckpointStates.length} collected"
  for (e, (_, state)) in entries.zip t.finalizedCheckpointStates do
    let bid := stateToBlockId state
    let bootstrap ← getLightClientBootstrap bid.root
    ex (y (e.expectKeys (["block_root"] ++ if bootstrap.isSome then ["bootstrap"] else [])))
    if (← ex (root32 (← ex (y (e.field "block_root"))))) != bid.root then
      throw "bootstraps: block_root differs"
    if let some b := bootstrap then
      obj "bootstrap" b b.header.beacon.slot (← ex (y (e.field "bootstrap")))
  -- best_updates, one per period from the tail's to the head's
  let lowPeriod ← periodAt t.tailSlot
  let headPeriod ← periodAt headBid.slot
  let ups ← ex (y ((checks.field "best_updates").bind YVal.asSeq))
  let periods := (List.range (headPeriod.toNat + 1)).drop lowPeriod.toNat
  if ups.length != periods.length then
    throw s!"best_updates: {ups.length} entries for {periods.length} periods"
  for (e, period) in ups.zip periods do
    let u := t.bestUpdates.get? period
    ex (y (e.expectKeys (["period"] ++ if u.isSome then ["update"] else [])))
    if (← ex (y ((e.field "period").bind YVal.asNat))) != period then
      throw s!"best_updates: period differs at {period}"
    if let some u := u then
      obj "update" u u.attested_header.beacon.slot (← ex (y (e.field "update")))
  -- latest finality and optimistic updates
  if let some fu := finality then
    obj "finality_update" fu fu.attested_header.beacon.slot
      (← ex (y (checks.field "latest_finality_update")))
    obj "optimistic_update" (optimisticOf fu) fu.attested_header.beacon.slot
      (← ex (y (checks.field "latest_optimistic_update")))

/-- Run the steps. -/
def runSteps (files : Files) (gvr : Root) (steps : List YVal) : DC P Unit := do
  let ex {α : Type} (x : Except String α) : DC P α := match x with
    | .ok v => pure v
    | .error e => throw e
  for (st, i) in steps.zip (List.range steps.length) do
    match st with
    | .map [("new_block", nb)] =>
      let name ← ex (scalarText (← ex (y (nb.field "data"))) "new_block.data")
      let some bytes := files.get? name | throw s!"step {i}: no file {name}"
      let block : Gloas.SignedBeaconBlock P ←
        match (deserialize bytes : M (Gloas.SignedBeaconBlock P)) with
        | .ok b => pure b
        | .error e => throw s!"step {i}: {name} does not decode: {repr e}"
      let t ← get
      ex (checkObject (P := P) t.cfg gvr files "block" block block.message.slot nb)
      try addNewBlock block catch e => throw s!"step {i} (new_block {name}): {e}"
    | .map [("new_head", nh)] =>
      ex (y (nh.expectKeys ["head_block_root", "checks"]))
      let root ← ex (root32 (← ex (y (nh.field "head_block_root"))))
      let block ← need (← get).blocks root "blocks"
      let headBid := blockToBlockId block
      if headBid.root != root then throw s!"step {i}: head block root differs"
      try
        selectNewHead headBid
        checkHead files gvr headBid (← ex (y (nh.field "checks")))
      catch e => throw s!"step {i} (new_head {root}): {e}"
    | _ => throw s!"step {i}: unknown step"

end JauneConsensus.Harness.GloasDataCollection

namespace JauneConsensus.Harness
open Yaml

/-- `light_client/data_collection` at Gloas: a single-fork Gloas case (`GLOAS_FORK_EPOCH` at the
initial state's epoch or before), run over the Gloas state transition and light client. -/
def gloasLightClientDataCollection (P : Preset) (cfg : Config) (c : Case) :
    IO (Except String Unit) := do
  let mut files : GloasDataCollection.Files := []
  for name in c.files do
    if name.endsWith ".ssz_snappy" then
      match Snappy.decompress (← IO.FS.readBinFile (c.dir / name)) with
      | .ok b => files := files ++ [((name.dropEnd ".ssz_snappy".length).toString, b.toList)]
      | .error e => return .error s!"{name}: snappy: {e}"
    else if name != "steps.yaml" && name != "config.yaml" then
      return .error s!"unexpected file {name}"
  let stepsDoc := (parse (← IO.FS.readBinFile (c.dir / "steps.yaml"))).mapError
    (s!"steps.yaml: " ++ toString ·)
  pure do
    let steps ← (stepsDoc.bind fun v => v.asSeq.mapError toString)
    let some initial := files.lookup "initial_state" | throw "no initial_state"
    let state : Gloas.BeaconState P ← (deserialize initial : M (Gloas.BeaconState P)).mapError
      fun e => s!"initial_state: decode rejected: {repr e}"
    -- a single-fork case: the initial state is already at or past `GLOAS_FORK_EPOCH`
    let epoch ← (computeEpochAtSlot P state.slot).mapError fun e => s!"initial_state: {repr e}"
    if epoch.toNat < cfg.GLOAS_FORK_EPOCH then
      throw s!"refused: initial_state at epoch {epoch.toNat} precedes GLOAS_FORK_EPOCH"
    let t ← GloasDataCollection.setup cfg { cfg } state
    let _ ← (GloasDataCollection.runSteps files state.genesis_validators_root steps).run t

end JauneConsensus.Harness
