import JauneConsensus.LightClient
import JauneConsensus.SSZ.Proof

/-!
# Light-client data derivation on a full node

Transcribed from `ethereum/consensus-specs` `v1.6.1`: `specs/altair/light-client/full-node.md`
(`compute_merkle_proof`, `create_light_client_bootstrap`, `create_light_client_update`,
`create_light_client_finality_update`, `create_light_client_optimistic_update`),
`specs/capella/light-client/full-node.md` and `specs/deneb/light-client/full-node.md`
(`block_to_light_client_header`), and `specs/electra/light-client/fork.md`
(`normalize_merkle_branch`). Electra changes these only through the generalized indices
(`*_gindex_at_slot`, `LightClient.lean`); Fulu has no light-client changes.

`compute_merkle_proof(object, index)` is declared without a body in the specification ("the
Merkle proof of the given SSZ object at generalized index"). Here an object is presented as a
`ProofTree`: its field chunks (`Name.fieldRoots`, the leaves `hash_tree_root` merkleizes), each
optionally expanded into the subtree of that field where a proof descends below it. The proof is
the chunk-level `computeMerkleProofOfLeaves` (`SSZ/Proof.lean`) at each level, concatenated
leaf to root.
-/

namespace JauneConsensus
open Jaune (Bytes B256)

variable {P : Preset} {f : CFork}

/-! ## `compute_merkle_proof` -/

/-- An SSZ object's Merkle tree as far as a proof needs it: the chunks of one merkleization
(padded to a power of two by `merkle_tree`), each with the subtree it is the root of when a
proof may descend below it. -/
inductive ProofTree where
  | node (children : List (B256 × Option ProofTree))

/-- A tree with no expansion: the given chunks. -/
def ProofTree.ofChunks (chunks : List B256) : ProofTree := .node (chunks.map (·, none))

/-- A container's tree from its field leaves (`Name.fieldRoots`; absent fork-gated fields have
no leaf). -/
def ProofTree.ofFields (roots : List (Option B256)) : ProofTree := .ofChunks (roots.filterMap id)

/-- Expand chunk `i` of a tree's top level into `sub`. -/
def ProofTree.expand (t : ProofTree) (i : Nat) (sub : ProofTree) : ProofTree :=
  match t with
  | .node cs => .node (cs.mapIdx fun j (r, s) => if j = i then (r, some sub) else (r, s))

/-- The tree of a `List[T, N]` of composite `T`: `mix_in_length(merkleize(roots, limit=N), len)`,
that is a node over the data root (expanded into the `N` element roots, zero-padded) and the
length chunk. -/
def ProofTree.ofCompositeList {α : Type} [Ssz α] {n : Nat} (xs : SszList α n) : ProofTree :=
  let roots := xs.toArray.toList.map hashTreeRoot
  let data := roots ++ List.replicate (n - roots.length) zeroChunk
  .node [(merkleizeDepth roots (depthOf n), some (.ofChunks data)),
         (Jaune.Bytes.toB256 (leBytes 32 roots.length), none)]

/-- The proof at generalized index `g` of a tree: below the tree's own depth it descends into
the expanded chunk, concatenating the inner proof (deeper nodes first) with the proof of that
chunk. `fuel` bounds the descent and is never reached for `fuel > floorlog2 g`. -/
def proofTreeProof : Nat → ProofTree → GeneralizedIndex → M (List B256)
  | 0, _, _ => throw (.assert "compute_merkle_proof: descent bound")
  | fuel + 1, .node cs, g => do
    let d ← getGeneralizedIndexLength g
    let roots := cs.map (·.1)
    let depth := floorlog2 (getPowerOfTwoCeil roots.length)
    if d ≤ depth then return ← computeMerkleProofOfLeaves roots g
    let top := g >>> (d - depth)
    match cs[top - 2 ^ depth]? with
    | some (_, some sub) =>
      let inner := g - (top <<< (d - depth)) + 2 ^ (d - depth)
      pure ((← proofTreeProof fuel sub inner) ++ (← computeMerkleProofOfLeaves roots top))
    | _ => throw (.assert s!"compute_merkle_proof: index {g} is below an unexpanded chunk")

/-- `compute_merkle_proof(object, index)` over an object's proof tree. -/
def computeMerkleProof (t : ProofTree) (index : GeneralizedIndex) : M (List B256) :=
  proofTreeProof (floorlog2 index + 1) t index

/-- The position of `finalized_checkpoint` among `BeaconState`'s fields (phase0 field order,
unchanged through Fulu; `FINALIZED_ROOT_GINDEX_ELECTRA = 169 = 2 * (64 + 20) + 1`). -/
def FINALIZED_CHECKPOINT_FIELD_INDEX : Nat := 20

/-- The position of `blob_kzg_commitments` among `BeaconBlockBody`'s fields (Deneb field order,
unchanged through Fulu). -/
def BLOB_KZG_COMMITMENTS_FIELD_INDEX : Nat := 11

/-- A `BeaconState`'s proof tree: its field leaves, with `finalized_checkpoint` expanded (the
proofs the light-client protocol takes from a state are to sync committees and to
`finalized_checkpoint.root`). -/
def BeaconState.proofTree (s : BeaconState P f) : ProofTree :=
  (ProofTree.ofFields s.fieldRoots).expand FINALIZED_CHECKPOINT_FIELD_INDEX
    (.ofFields s.finalized_checkpoint.fieldRoots)

/-- A `BeaconBlockBody`'s proof tree: its field leaves, with `blob_kzg_commitments` expanded
(`execution_payload` for light-client headers; a commitment or the whole list for blob and
column sidecars). -/
def BeaconBlockBody.proofTree (b : BeaconBlockBody P f) : ProofTree :=
  (ProofTree.ofFields b.fieldRoots).expand BLOB_KZG_COMMITMENTS_FIELD_INDEX
    (.ofCompositeList b.blob_kzg_commitments)

/-- `normalize_merkle_branch(branch, gindex)` (`specs/electra/light-client/fork.md`):
left-pad with zero roots to `floorlog2(gindex)`. -/
def normalizeMerkleBranch (branch : List Bytes32) (gindex : GeneralizedIndex) : List Bytes32 :=
  List.replicate (floorlog2 gindex - branch.length) zeroRoot ++ branch

/-! ## Headers -/

/-- `BeaconBlockBody()`: every field at its default. -/
def defaultBeaconBlockBody : BeaconBlockBody P f :=
  { randao_reveal := zeroBytesVec 96,
    eth1_data := { deposit_root := zeroRoot, deposit_count := U64.zero, block_hash := zeroRoot },
    graffiti := zeroRoot, proposer_slashings := SszList.empty, attester_slashings := SszList.empty,
    attestations := SszList.empty, deposits := SszList.empty, voluntary_exits := SszList.empty,
    sync_aggregate := { sync_committee_bits := ⟨Array.replicate P.SYNC_COMMITTEE_SIZE false, by simp⟩,
                        sync_committee_signature := zeroBytesVec 96 },
    execution_payload :=
      { parent_hash := zeroRoot, fee_recipient := (0 : Jaune.Adr), state_root := zeroRoot,
        receipts_root := zeroRoot, logs_bloom := zeroBytesVec _, prev_randao := zeroRoot,
        block_number := U64.zero, gas_limit := U64.zero, gas_used := U64.zero,
        timestamp := U64.zero, extra_data := SszList.empty, base_fee_per_gas := UIntN.zero,
        block_hash := zeroRoot, transactions := SszList.empty, withdrawals := SszList.empty,
        blob_gas_used := U64.zero, excess_blob_gas := U64.zero },
    bls_to_execution_changes := SszList.empty, blob_kzg_commitments := SszList.empty,
    execution_requests := gatedDefault
      { deposits := SszList.empty, withdrawals := SszList.empty, consolidations := SszList.empty } }
where
  /-- A gated field's default: the value from its fork, the absent field before. -/
  gatedDefault {α : Type} {c : Bool} (x : α) : Gated c α :=
    match c with
    | true => x
    | false => ()

/-- `block_to_light_client_header` (`specs/deneb/light-client/full-node.md`, extending the Capella
and Altair versions). -/
def blockToLightClientHeader (cfg : Config) (block : SignedBeaconBlock P f) :
    M (LightClientHeader P) := do
  let epoch := (← computeEpochAtSlot P block.message.slot).toNat
  let (executionHeader, executionBranch) ←
    if epoch ≥ cfg.CAPELLA_FORK_EPOCH then do
      let payload := block.message.body.execution_payload
      let executionHeader : ExecutionPayloadHeader P :=
        { parent_hash := payload.parent_hash, fee_recipient := payload.fee_recipient,
          state_root := payload.state_root, receipts_root := payload.receipts_root,
          logs_bloom := payload.logs_bloom, prev_randao := payload.prev_randao,
          block_number := payload.block_number, gas_limit := payload.gas_limit,
          gas_used := payload.gas_used, timestamp := payload.timestamp,
          extra_data := payload.extra_data, base_fee_per_gas := payload.base_fee_per_gas,
          block_hash := payload.block_hash,
          transactions_root := hashTreeRoot payload.transactions,
          withdrawals_root := hashTreeRoot payload.withdrawals,
          blob_gas_used := U64.zero, excess_blob_gas := U64.zero }
      -- [New in Deneb:EIP4844]
      let executionHeader := if epoch ≥ cfg.DENEB_FORK_EPOCH then
          { executionHeader with blob_gas_used := payload.blob_gas_used,
                                 excess_blob_gas := payload.excess_blob_gas }
        else executionHeader
      let branch ← computeMerkleProof block.message.body.proofTree EXECUTION_PAYLOAD_GINDEX
      pure (executionHeader, ← SszVector.ofArray branch.toArray "ExecutionBranch")
    else
      pure (defaultExecutionPayloadHeader, zeroRootVec _)
  pure { beacon := { slot := block.message.slot, proposer_index := block.message.proposer_index,
                     parent_root := block.message.parent_root,
                     state_root := block.message.state_root,
                     body_root := hashTreeRoot block.message.body },
         execution := executionHeader, execution_branch := executionBranch }

/-! ## Deriving light client data -/

/-- `state.latest_block_header` with `state_root = hash_tree_root(state)`: the header of the block
whose post-state `state` is, when `state.slot == state.latest_block_header.slot`. -/
def stateBlockHeader (state : BeaconState P f) : BeaconBlockHeader :=
  { state.latest_block_header with state_root := hashTreeRoot state }

/-- `create_light_client_bootstrap(state, block)` (`specs/altair/light-client/full-node.md`). -/
def createLightClientBootstrap (cfg : Config) (state : BeaconState P f)
    (block : SignedBeaconBlock P f) : M (LightClientBootstrap P f) := do
  let site := "create_light_client_bootstrap"
  require ((← computeEpochAtSlot P state.slot).toNat ≥ cfg.ALTAIR_FORK_EPOCH) s!"{site}: epoch"
  require (state.slot == state.latest_block_header.slot) s!"{site}: state.slot"
  require (hashTreeRoot (stateBlockHeader state) == hashTreeRoot block.message) s!"{site}: block"
  -- No `normalize_merkle_branch` here (nor in `createLightClientUpdate`): the creators store raw `compute_merkle_proof` output (specs/altair/light-client/full-node.md); only the Electra fork-upgrade functions normalize (specs/electra/light-client/fork.md `upgrade_lc_*_to_electra`).
  let branch ← computeMerkleProof state.proofTree
    (← currentSyncCommitteeGindexAtSlot cfg P state.slot)
  pure { header := ← blockToLightClientHeader cfg block,
         current_sync_committee := state.current_sync_committee,
         current_sync_committee_branch := ← SszVector.ofArray branch.toArray
           s!"{site}: CurrentSyncCommitteeBranch" }

/-- `LightClientUpdate()`. -/
def defaultLightClientUpdate : LightClientUpdate P f :=
  { attested_header := defaultLightClientHeader, next_sync_committee := defaultSyncCommittee,
    next_sync_committee_branch := zeroRootVec _, finalized_header := defaultLightClientHeader,
    finality_branch := zeroRootVec _,
    sync_aggregate := defaultBeaconBlockBody.sync_aggregate (f := f),
    signature_slot := U64.zero }

/-- `create_light_client_update(state, block, attested_state, attested_block, finalized_block)`
(`specs/altair/light-client/full-node.md`). -/
def createLightClientUpdate (cfg : Config) (state : BeaconState P f) (block : SignedBeaconBlock P f)
    (attestedState : BeaconState P f) (attestedBlock : SignedBeaconBlock P f)
    (finalizedBlock : Option (SignedBeaconBlock P f)) : M (LightClientUpdate P f) := do
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
  let mut update : LightClientUpdate P f := defaultLightClientUpdate
  update := { update with attested_header := ← blockToLightClientHeader cfg attestedBlock }
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
      update := { update with finalized_header := ← blockToLightClientHeader cfg finalizedBlock }
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
def createLightClientFinalityUpdate (update : LightClientUpdate P f) :
    LightClientFinalityUpdate P f :=
  { attested_header := update.attested_header, finalized_header := update.finalized_header,
    finality_branch := update.finality_branch, sync_aggregate := update.sync_aggregate,
    signature_slot := update.signature_slot }

/-- `create_light_client_optimistic_update(update)`. -/
def createLightClientOptimisticUpdate (update : LightClientUpdate P f) :
    LightClientOptimisticUpdate P :=
  { attested_header := update.attested_header, sync_aggregate := update.sync_aggregate,
    signature_slot := update.signature_slot }

/-! ## Tests: proof trees on hand values -/

private def L (k : Nat) : B256 := Jaune.Nat.toB256 (k + 1)
private def ok? {α} (x : M α) : Option α := x.toOption

-- a flat tree is the chunk-level proof
#guard (ok? (computeMerkleProof (.ofChunks [L 0, L 1, L 2, L 3]) 6)).map (·.map B256.toBytes) ==
  (ok? (computeMerkleProofOfLeaves [L 0, L 1, L 2, L 3] 6)).map (·.map B256.toBytes)
-- descending into chunk 2 of four (index 6), itself two chunks: index 13 is its right child;
-- the proof is the sibling inside, then the outer proof of index 6
#guard (ok? (computeMerkleProof ((ProofTree.ofChunks [L 0, L 1, hashPair (L 7) (L 8), L 3]).expand 2
    (.ofChunks [L 7, L 8])) 13)).map (·.map B256.toBytes) ==
  some [(L 7).toBytes, (L 3).toBytes, (hashPair (L 0) (L 1)).toBytes]
-- an index below an unexpanded chunk rejects
#guard (computeMerkleProof (.ofChunks [L 0, L 1, L 2, L 3]) 13).toBool == false
#guard normalizeMerkleBranch [L 0] 9 == [zeroRoot, zeroRoot, L 0]

end JauneConsensus
