import JauneConsensus.GloasLightClient
import JauneConsensus.LightClientFullNode

/-!
# Gloas light client: proofs, full node and fork upgrade

Transcribed from `ethereum/consensus-specs` `v1.7.0-beta.4`:

* `specs/gloas/light-client/full-node.md` (`block_to_light_client_header`), with the Altair
  `create_light_client_bootstrap` / `create_light_client_update` /
  `create_light_client_finality_update` / `create_light_client_optimistic_update`
  (`specs/altair/light-client/full-node.md`) over the Gloas containers;
* `specs/gloas/light-client/fork.md` (the six `upgrade_lc_*_to_gloas`, Electra objects to Gloas).

`compute_merkle_proof` runs over a `ProofTree` (`LightClientFullNode.lean`). Gloas's
`BeaconState`, `BeaconBlockBody` and `ExecutionPayloadBid` are progressive containers (EIP-7688,
`eth-ssz-specs==0.1.0`'s right-leaning spine, `SSZ/Progressive.lean`), so their trees are built by
`ProofTree.ofProgressive` (`LightClientFullNode.lean`): the root node is `(spine root, active-fields chunk)`, and each spine node
is `(subtree of this level, rest of the spine)`, the levels holding 1, 4, 16, ... chunks. A
one-chunk level is the chunk itself (`merkleize([x], 1) = x`), so every node of the tree has at
least two children and every descent of `computeMerkleProof` consumes a level of the generalized
index.
-/

namespace JauneConsensus.Gloas
open Jaune (Bytes B256)
open JauneConsensus

variable {P : Preset} {f : CFork}

/-- The field chunks of a progressive container, field `i` expanded into `sub`. -/
def expandAt (roots : List B256) (i : Nat) (sub : ProofTree) : List (B256 × Option ProofTree) :=
  roots.mapIdx fun j r => (r, if j = i then some sub else none)

/-- The position of `finalized_checkpoint` among Gloas `BeaconState`'s fields (unchanged from
phase0; `FINALIZED_ROOT_GINDEX_GLOAS = 735 = 2 * (22 * 16 + (20 - 5)) + 1`, field 20 lying in the
third spine level, fields 5 to 20, at generalized index 22). -/
def FINALIZED_CHECKPOINT_FIELD_INDEX : Nat := 20

/-- The position of `signed_execution_payload_bid` among Gloas `BeaconBlockBody`'s fields
(`EXECUTION_BLOCK_HASH_GINDEX_GLOAS = 2856 = 2 * (2 * (22 * 16 + (10 - 5))) * 2`: field 10, its
`message` (0), whose `parent_block_hash` is field 0 of a progressive container). -/
def SIGNED_EXECUTION_PAYLOAD_BID_FIELD_INDEX : Nat := 10

#guard FINALIZED_ROOT_GINDEX_GLOAS == 2 * (22 * 16 + (FINALIZED_CHECKPOINT_FIELD_INDEX - 5)) + 1
#guard EXECUTION_BLOCK_HASH_GINDEX_GLOAS ==
  2 * (2 * (2 * (22 * 16 + (SIGNED_EXECUTION_PAYLOAD_BID_FIELD_INDEX - 5)) + 0))

/-- A Gloas `BeaconState`'s proof tree, with `finalized_checkpoint` expanded (the sync committees
are field leaves). -/
def BeaconState.proofTree (s : BeaconState P) : ProofTree :=
  .ofProgressive (expandAt s.fieldRoots FINALIZED_CHECKPOINT_FIELD_INDEX
    (.ofFields s.finalized_checkpoint.fieldRoots))

/-- A Gloas `BeaconBlockBody`'s proof tree, with `signed_execution_payload_bid.message` expanded
(the execution block hash of a light-client header). -/
def BeaconBlockBody.proofTree (b : BeaconBlockBody P) : ProofTree :=
  .ofProgressive (expandAt b.fieldRoots SIGNED_EXECUTION_PAYLOAD_BID_FIELD_INDEX
    ((ProofTree.ofFields b.signed_execution_payload_bid.fieldRoots).expand 0
      (.ofProgressive (b.signed_execution_payload_bid.message.fieldRoots.map (·, none)))))

/-! ## Full node -/

/-- `block_to_light_client_header` (Gloas). -/
def blockToLightClientHeader (block : SignedBeaconBlock P) : M LightClientHeader := do
  let branch ← computeMerkleProof block.message.body.proofTree EXECUTION_BLOCK_HASH_GINDEX_GLOAS
  pure { beacon := { slot := block.message.slot, proposer_index := block.message.proposer_index,
                     parent_root := block.message.parent_root,
                     state_root := block.message.state_root,
                     body_root := hashTreeRoot block.message.body },
         execution_block_hash := block.message.body.signed_execution_payload_bid.message.parent_block_hash,
         execution_branch := ← SszVector.ofArray branch.toArray "ExecutionBranch" }

/-- `state.latest_block_header` with `state_root = hash_tree_root(state)`. -/
def stateBlockHeader (state : BeaconState P) : BeaconBlockHeader :=
  { state.latest_block_header with state_root := hashTreeRoot state }

/-- `create_light_client_bootstrap(state, block)` (Altair, Gloas types). -/
def createLightClientBootstrap (cfg : Config) (state : BeaconState P) (block : SignedBeaconBlock P) :
    M (LightClientBootstrap P) := do
  let site := "create_light_client_bootstrap"
  require ((← computeEpochAtSlot P state.slot).toNat ≥ cfg.ALTAIR_FORK_EPOCH) s!"{site}: epoch"
  require (state.slot == state.latest_block_header.slot) s!"{site}: state.slot"
  require (hashTreeRoot (stateBlockHeader state) == hashTreeRoot block.message) s!"{site}: block"
  let branch ← computeMerkleProof state.proofTree
    (← currentSyncCommitteeGindexAtSlot cfg P state.slot)
  pure { header := ← blockToLightClientHeader block,
         current_sync_committee := state.current_sync_committee,
         current_sync_committee_branch := ← SszVector.ofArray branch.toArray
           s!"{site}: CurrentSyncCommitteeBranch" }

/-- `LightClientUpdate()`. -/
def defaultLightClientUpdate : LightClientUpdate P :=
  { attested_header := defaultLightClientHeader, next_sync_committee := defaultSyncCommittee,
    next_sync_committee_branch := zeroRootVec _, finalized_header := defaultLightClientHeader,
    finality_branch := zeroRootVec _,
    sync_aggregate := { sync_committee_bits := ⟨Array.replicate P.SYNC_COMMITTEE_SIZE false, by simp⟩,
                        sync_committee_signature := zeroBytesVec 96 },
    signature_slot := U64.zero }

/-- `create_light_client_update(state, block, attested_state, attested_block, finalized_block)`
(Altair, Gloas types). -/
def createLightClientUpdate (cfg : Config) (state : BeaconState P) (block : SignedBeaconBlock P)
    (attestedState : BeaconState P) (attestedBlock : SignedBeaconBlock P)
    (finalizedBlock : Option (SignedBeaconBlock P)) : M (LightClientUpdate P) := do
  let site := "create_light_client_update"
  require ((← computeEpochAtSlot P attestedState.slot).toNat ≥ cfg.ALTAIR_FORK_EPOCH)
    s!"{site}: epoch"
  require (bitCount block.message.body.sync_aggregate.sync_committee_bits ≥
    P.MIN_SYNC_COMMITTEE_PARTICIPANTS) s!"{site}: participants"
  require (state.slot == state.latest_block_header.slot) s!"{site}: state.slot"
  require (hashTreeRoot (stateBlockHeader state) == hashTreeRoot block.message) s!"{site}: block"
  let updateSignaturePeriod ← computeSyncCommitteePeriodAtSlot P block.message.slot
  require (attestedState.slot == attestedState.latest_block_header.slot)
    s!"{site}: attested_state.slot"
  let attestedRoot := hashTreeRoot attestedBlock.message
  require (hashTreeRoot (stateBlockHeader attestedState) == attestedRoot &&
    attestedRoot == block.message.parent_root) s!"{site}: attested block"
  let updateAttestedPeriod ← computeSyncCommitteePeriodAtSlot P attestedBlock.message.slot
  let mut update : LightClientUpdate P := defaultLightClientUpdate
  update := { update with attested_header := ← blockToLightClientHeader attestedBlock }
  -- `next_sync_committee` is only useful if the message is signed by the current sync committee
  if updateAttestedPeriod == updateSignaturePeriod then
    let branch ← computeMerkleProof attestedState.proofTree
      (← nextSyncCommitteeGindexAtSlot cfg P attestedState.slot)
    update := { update with
      next_sync_committee := attestedState.next_sync_committee
      next_sync_committee_branch := ← SszVector.ofArray branch.toArray
        s!"{site}: NextSyncCommitteeBranch" }
  -- Indicate finality whenever possible
  if let some finalizedBlock := finalizedBlock then
    if finalizedBlock.message.slot != GENESIS_SLOT then
      update := { update with finalized_header := ← blockToLightClientHeader finalizedBlock }
      require (hashTreeRoot update.finalized_header.beacon ==
        attestedState.finalized_checkpoint.root) s!"{site}: finalized header"
    else
      require (attestedState.finalized_checkpoint.root == zeroRoot) s!"{site}: genesis finality"
    let branch ← computeMerkleProof attestedState.proofTree
      (← finalizedRootGindexAtSlot cfg P attestedState.slot)
    update := { update with
      finality_branch := ← SszVector.ofArray branch.toArray s!"{site}: FinalityBranch" }
  pure { update with sync_aggregate := block.message.body.sync_aggregate,
                     signature_slot := block.message.slot }

/-- `create_light_client_finality_update(update)`. -/
def createLightClientFinalityUpdate (update : LightClientUpdate P) : LightClientFinalityUpdate P :=
  { attested_header := update.attested_header, finalized_header := update.finalized_header,
    finality_branch := update.finality_branch, sync_aggregate := update.sync_aggregate,
    signature_slot := update.signature_slot }

/-- `create_light_client_optimistic_update(update)`. -/
def createLightClientOptimisticUpdate (update : LightClientUpdate P) :
    LightClientOptimisticUpdate P :=
  { attested_header := update.attested_header, sync_aggregate := update.sync_aggregate,
    signature_slot := update.signature_slot }

/-! ## Upgrading Electra light-client data (`specs/gloas/light-client/fork.md`) -/

/-- The Capella `ExecutionPayloadHeader` of an Electra header's execution fields. -/
def capellaHeaderOf (e : ExecutionPayloadHeader P) : CapellaExecutionPayloadHeader P :=
  { parent_hash := e.parent_hash, fee_recipient := e.fee_recipient, state_root := e.state_root,
    receipts_root := e.receipts_root, logs_bloom := e.logs_bloom, prev_randao := e.prev_randao,
    block_number := e.block_number, gas_limit := e.gas_limit, gas_used := e.gas_used,
    timestamp := e.timestamp, extra_data := e.extra_data, base_fee_per_gas := e.base_fee_per_gas,
    block_hash := e.block_hash, transactions_root := e.transactions_root,
    withdrawals_root := e.withdrawals_root }

/-- `ExecutionBranch(data=...)`: a vector of exactly `floorlog2(EXECUTION_BLOCK_HASH_GINDEX_GLOAS)`
roots. -/
private def branchVec {n : Nat} (xs : List Bytes32) (what : String) : M (SszVector Bytes32 n) :=
  SszVector.ofArray xs.toArray what

/-- `upgrade_lc_header_to_gloas`. -/
def upgradeLcHeaderToGloas (cfg : Config) (pre : JauneConsensus.LightClientHeader P) :
    M LightClientHeader := do
  if pre == JauneConsensus.defaultLightClientHeader then return defaultLightClientHeader
  let epoch := (← computeEpochAtSlot P pre.beacon.slot).toNat
  let site := "upgrade_lc_header_to_gloas"
  let preBranch := pre.execution_branch.toArray.toList
  if epoch ≥ cfg.DENEB_FORK_EPOCH then
    let proof ← computeMerkleProof (.ofFields pre.execution.fieldRoots) BLOCK_HASH_GINDEX_DENEB
    return { beacon := pre.beacon, execution_block_hash := pre.execution.block_hash,
             execution_branch := ← branchVec (normalizeMerkleBranch (proof ++ preBranch)
               EXECUTION_BLOCK_HASH_GINDEX_GLOAS) site }
  if epoch ≥ cfg.CAPELLA_FORK_EPOCH then
    let executionHeader := capellaHeaderOf pre.execution
    let proof ← computeMerkleProof (.ofFields executionHeader.fieldRoots) BLOCK_HASH_GINDEX_CAPELLA
    return { beacon := pre.beacon, execution_block_hash := pre.execution.block_hash,
             execution_branch := ← branchVec (normalizeMerkleBranch (proof ++ preBranch)
               EXECUTION_BLOCK_HASH_GINDEX_GLOAS) site }
  pure { beacon := pre.beacon, execution_block_hash := zeroRoot,
         execution_branch := zeroRootVec _ }

/-- `upgrade_lc_bootstrap_to_gloas`. -/
def upgradeLcBootstrapToGloas (cfg : Config) (pre : JauneConsensus.LightClientBootstrap P f) :
    M (LightClientBootstrap P) := do
  pure { header := ← upgradeLcHeaderToGloas cfg pre.header,
         current_sync_committee := pre.current_sync_committee,
         current_sync_committee_branch := ← branchVec (normalizeMerkleBranch
           pre.current_sync_committee_branch.toArray.toList CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS)
           "upgrade_lc_bootstrap_to_gloas" }

/-- `upgrade_lc_update_to_gloas`. -/
def upgradeLcUpdateToGloas (cfg : Config) (pre : JauneConsensus.LightClientUpdate P f) :
    M (LightClientUpdate P) := do
  let site := "upgrade_lc_update_to_gloas"
  pure { attested_header := ← upgradeLcHeaderToGloas cfg pre.attested_header,
         next_sync_committee := pre.next_sync_committee,
         next_sync_committee_branch := ← branchVec (normalizeMerkleBranch
           pre.next_sync_committee_branch.toArray.toList NEXT_SYNC_COMMITTEE_GINDEX_GLOAS) site,
         finalized_header := ← upgradeLcHeaderToGloas cfg pre.finalized_header,
         finality_branch := ← branchVec (normalizeMerkleBranch
           pre.finality_branch.toArray.toList FINALIZED_ROOT_GINDEX_GLOAS) site,
         sync_aggregate := pre.sync_aggregate, signature_slot := pre.signature_slot }

/-- `upgrade_lc_finality_update_to_gloas`. -/
def upgradeLcFinalityUpdateToGloas (cfg : Config)
    (pre : JauneConsensus.LightClientFinalityUpdate P f) : M (LightClientFinalityUpdate P) := do
  pure { attested_header := ← upgradeLcHeaderToGloas cfg pre.attested_header,
         finalized_header := ← upgradeLcHeaderToGloas cfg pre.finalized_header,
         finality_branch := ← branchVec (normalizeMerkleBranch
           pre.finality_branch.toArray.toList FINALIZED_ROOT_GINDEX_GLOAS)
           "upgrade_lc_finality_update_to_gloas",
         sync_aggregate := pre.sync_aggregate, signature_slot := pre.signature_slot }

/-- `upgrade_lc_optimistic_update_to_gloas`. -/
def upgradeLcOptimisticUpdateToGloas (cfg : Config)
    (pre : JauneConsensus.LightClientOptimisticUpdate P) : M (LightClientOptimisticUpdate P) := do
  pure { attested_header := ← upgradeLcHeaderToGloas cfg pre.attested_header,
         sync_aggregate := pre.sync_aggregate, signature_slot := pre.signature_slot }

/-- `upgrade_lc_store_to_gloas`. -/
def upgradeLcStoreToGloas (cfg : Config) (pre : JauneConsensus.LightClientStore P f) :
    M (LightClientStore P) := do
  let best ← match pre.best_valid_update with
    | none => pure none
    | some u => some <$> upgradeLcUpdateToGloas cfg u
  pure { finalized_header := ← upgradeLcHeaderToGloas cfg pre.finalized_header,
         current_sync_committee := pre.current_sync_committee,
         next_sync_committee := pre.next_sync_committee,
         best_valid_update := best,
         optimistic_header := ← upgradeLcHeaderToGloas cfg pre.optimistic_header,
         previous_max_active_participants := pre.previous_max_active_participants,
         current_max_active_participants := pre.current_max_active_participants }

/-! ## Tests on hand values -/

private def L (k : Nat) : B256 := Jaune.Nat.toB256 (k + 1)
private def ok? {α} (x : M α) : Option α := x.toOption
private def allActiveRoot (roots : List B256) : B256 :=
  if h : roots.length ≤ 256 then
    progressiveContainerRoot (List.replicate roots.length true) roots (by simpa using h) .successorRight
  else zeroChunk

-- the progressive tree's root is `progressiveContainerRoot` over the same chunks, for sizes that
-- end inside each of the first three spine levels
#guard [1, 3, 5, 6, 21, 22, 46].all fun n =>
  let roots := (List.range n).map L
  match ProofTree.ofProgressive (roots.map (·, none)) with
  | .node cs =>
    (ok? (merkleTreeRoot (cs.map (·.1)))).map (B256.beq · (allActiveRoot roots)) == some true
-- a field proof verifies against that root at its generalized index: field 0 at 4, field 2 at
-- `2 * 5 * 4 + 1` (level 1 at index 10, position 1), field 20 at `22 * 16 + 15`
#guard [(0, 4), (2, 41), (20, 367), (22, 2945)].all fun (i, g) =>
  let roots := (List.range 46).map L
  let t := ProofTree.ofProgressive (roots.map (·, none))
  match ok? (computeMerkleProof t g), roots[i]? with
  | some pr, some leaf => ok? (verifyMerkleProof leaf pr g (allActiveRoot roots)) == some true
  | _, _ => false

end JauneConsensus.Gloas
