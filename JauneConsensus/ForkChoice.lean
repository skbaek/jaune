import Jaune.Types
import JauneConsensus.Block
import JauneConsensus.Epoch
import JauneConsensus.StateTransition
import JauneConsensus.Crypto.Boundary
import Std.Data.TreeMap
import Std.Data.TreeSet

/-!
# Fork choice (Electra and Fulu)

`specs/phase0/fork-choice.md` with the later forks' modifications at `v1.7.0-beta.4`:
`specs/bellatrix/fork-choice.md` and `specs/capella/fork-choice.md` (`on_block` without the merge
check), `specs/deneb/fork-choice.md` (`is_data_available` over blobs, the `on_block` Electra uses;
Electra's fork-choice document adds nothing) and `specs/fulu/fork-choice.md` (`is_data_available`
over data-column sidecars, with `verify_data_column_sidecar` and
`verify_data_column_sidecar_kzg_proofs` from `specs/fulu/p2p-interface.md`, and `get_proposer_head`
without the shuffling-stability condition).

The release moved the store to milliseconds (`time_ms`, `genesis_time_ms`), introduced the
`ForkChoiceNode` abstraction (a block root in Phase0; Gloas adds the payload status), split the
weight into `get_attestation_score` and the proposer score, made `on_block` idempotent and its
proposer boost conditional on the shuffling dependent root, added `is_proposer_equivocation` to
`get_proposer_head`, counted equivocating head-slot committee members in `is_head_weak`, and
removed `should_override_forkchoice_update`.

The `Store` is a value; every handler returns the updated store or a typed rejection, so an
invalid call leaves the caller's store as it was ("Invalid calls to handlers must not modify
`store`"). Its dictionaries are `Std.TreeMap`s under the existing `Ord B256` order, its sets
`Std.TreeSet`s. Validator indices key them by `toNat`.

The spec's implementation-dependent oracles `retrieve_blobs_and_proofs` and
`retrieve_column_sidecars` are a parameter (`DataOracle`).

Loops and recursions that the Python bounds only by the shape of the block tree
(`get_ancestor`, `filter_node_tree`, `get_head`) carry fuel equal to the number of blocks in
the store plus one, which a walk along parent links over distinct blocks never exhausts; running
out (possible only for a cyclic parent relation, where Python recurses or loops forever) is a
rejection.
-/

namespace JauneConsensus

open Jaune (Bytes B256)

variable {P : Preset} {f : CFork}

/-! ## The state transition entry points -/

-- `processSlots` and `stateTransition` (the spec's `process_slots` and `state_transition` with
-- `process_epoch` and `process_block`) are in `JauneConsensus/StateTransition.lean`.

/-! ## Constants, nodes and the store -/

/-- `BASIS_POINTS` (`specs/phase0/fork-choice.md`, "Constants"). -/
def BASIS_POINTS : Nat := 10000

/-- `ForkChoiceNode` (`specs/phase0/fork-choice.md`): in Phase0 to Fulu one-to-one with blocks.
Gloas extends it with a `payload_status`; every function here takes and returns nodes where the
spec does, so that extension changes the node's fields and `ForkChoiceNode.cmp`, not the
signatures. -/
structure ForkChoiceNode where
  root : Root
  deriving DecidableEq, BEq

/-- The order keying sets of nodes: by root. -/
def ForkChoiceNode.cmp (a b : ForkChoiceNode) : Ordering := compare a.root b.root

/-- A set of nodes (the spec's `Sequence[ForkChoiceNode]` where only membership is read). -/
abbrev NodeSet := Std.TreeSet ForkChoiceNode ForkChoiceNode.cmp

/-- `LatestMessage` (`specs/phase0/fork-choice.md`). -/
structure LatestMessage where
  epoch : Epoch
  root : Root
  deriving DecidableEq, BEq

/-- The order keying `checkpoint_states` by `Checkpoint`: epoch, then root. -/
def Checkpoint.cmp (a b : Checkpoint) : Ordering :=
  (compare a.epoch.toNat b.epoch.toNat).then (compare a.root b.root)

/-- A dictionary keyed by `Root`. -/
abbrev RootMap (α : Type) := Std.TreeMap Root α compare

/-- `Store` (`specs/phase0/fork-choice.md`). -/
structure Store (P : Preset) (f : CFork) where
  time_ms : U64
  genesis_time_ms : U64
  justified_checkpoint : Checkpoint
  finalized_checkpoint : Checkpoint
  unrealized_justified_checkpoint : Checkpoint
  unrealized_finalized_checkpoint : Checkpoint
  proposer_boost_root : Root
  equivocating_indices : Std.TreeSet Nat compare
  blocks : RootMap (BeaconBlock P f)
  block_states : RootMap (BeaconState P f)
  block_timeliness : RootMap Bool
  checkpoint_states : Std.TreeMap Checkpoint (BeaconState P f) Checkpoint.cmp
  latest_messages : Std.TreeMap Nat LatestMessage compare
  unrealized_justifications : RootMap Checkpoint

/-- `d[k]` on a Python dictionary: the value, or `KeyError` (`Reject.key`). -/
@[inline] def lookup {κ α : Type} {cmp : κ → κ → Ordering} (m : Std.TreeMap κ α cmp) (k : κ)
    (site : String) : M α :=
  match m.get? k with
  | some a => pure a
  | none => throw (.key site)

/-! ## Time -/

-- `seconds_to_milliseconds`, `milliseconds_to_seconds`, `compute_time_at_slot_ms` and
-- `compute_slot_at_time_ms` are in `JauneConsensus/Block.lean`.

/-- `get_forkchoice_store(anchor_state, anchor_block)`. -/
def getForkchoiceStore (cfg : Config) (anchorState : BeaconState P f)
    (anchorBlock : BeaconBlock P f) : M (Store P f) := do
  let site := "get_forkchoice_store"
  require (anchorBlock.state_root == Ssz.hashTreeRoot anchorState) s!"{site}: anchor state root"
  let anchorRoot : Root := Ssz.hashTreeRoot anchorBlock
  let anchorEpoch ← getCurrentEpoch anchorState
  let justifiedCheckpoint : Checkpoint := { epoch := anchorEpoch, root := anchorRoot }
  let finalizedCheckpoint : Checkpoint := { epoch := anchorEpoch, root := anchorRoot }
  let genesisTimeMs ← secondsToMilliseconds anchorState.genesis_time
  pure {
    time_ms := ← computeTimeAtSlotMs cfg genesisTimeMs anchorState.slot
    genesis_time_ms := genesisTimeMs
    justified_checkpoint := justifiedCheckpoint
    finalized_checkpoint := finalizedCheckpoint
    unrealized_justified_checkpoint := justifiedCheckpoint
    unrealized_finalized_checkpoint := finalizedCheckpoint
    proposer_boost_root := zeroRoot
    equivocating_indices := ∅
    blocks := (∅ : RootMap _).insert anchorRoot anchorBlock
    block_states := (∅ : RootMap _).insert anchorRoot anchorState
    block_timeliness := ∅
    checkpoint_states := (∅ : Std.TreeMap Checkpoint _ Checkpoint.cmp).insert justifiedCheckpoint
      anchorState
    latest_messages := ∅
    unrealized_justifications := (∅ : RootMap _).insert anchorRoot justifiedCheckpoint }

/-- `get_slots_since_genesis(store)`. -/
def getSlotsSinceGenesis (cfg : Config) (store : Store P f) : M Slot :=
  computeSlotAtTimeMs cfg store.genesis_time_ms store.time_ms

/-- `get_current_slot(store)`. -/
def getCurrentSlot (cfg : Config) (store : Store P f) : M Slot :=
  getSlotsSinceGenesis cfg store

/-- `get_time_into_slot_ms(store)`. -/
def getTimeIntoSlotMs (cfg : Config) (store : Store P f) : M U64 := do
  store.time_ms.sub? (← computeTimeAtSlotMs cfg store.genesis_time_ms (← getCurrentSlot cfg store))
    "get_time_into_slot_ms"

/-- `get_current_store_epoch(store)`. -/
def getCurrentStoreEpoch (cfg : Config) (store : Store P f) : M Epoch := do
  computeEpochAtSlot P (← getCurrentSlot cfg store)

/-- `compute_slots_since_epoch_start(slot)`. -/
def computeSlotsSinceEpochStart (P : Preset) (slot : Slot) : M Slot := do
  slot.sub? (← computeStartSlotAtEpoch P (← computeEpochAtSlot P slot))
    "compute_slots_since_epoch_start"

/-- `get_slot_component_duration_ms(basis_points)`. -/
def getSlotComponentDurationMs (cfg : Config) (basisPoints : U64) : M U64 := do
  let site := "get_slot_component_duration_ms"
  (← basisPoints.mul? (← u64 cfg.SLOT_DURATION_MS "SLOT_DURATION_MS") site).div?
    (← c64 BASIS_POINTS) site

/-- `get_attestation_due_ms()`. -/
def getAttestationDueMs (cfg : Config) : M U64 := do
  getSlotComponentDurationMs cfg (← u64 cfg.ATTESTATION_DUE_BPS "ATTESTATION_DUE_BPS")

/-- `get_proposer_reorg_cutoff_ms()`. -/
def getProposerReorgCutoffMs (cfg : Config) : M U64 := do
  getSlotComponentDurationMs cfg (← u64 cfg.PROPOSER_REORG_CUTOFF_BPS "PROPOSER_REORG_CUTOFF_BPS")

/-! ## Block tree helpers -/

/-- `get_ancestor` with an explicit bound on the number of parent steps. -/
def getAncestorFuel (blocks : RootMap (BeaconBlock P f)) :
    Nat → ForkChoiceNode → Slot → M ForkChoiceNode
  | 0, _, _ => throw (.assert "get_ancestor: parent chain longer than the store")
  | fuel + 1, node, slot => do
    let block ← lookup blocks node.root "get_ancestor: store.blocks[node.root]"
    if block.slot > slot then getAncestorFuel blocks fuel { root := block.parent_root } slot
    else pure node

/-- `get_ancestor(store, node, slot)`. -/
def getAncestor (store : Store P f) (node : ForkChoiceNode) (slot : Slot) : M ForkChoiceNode :=
  getAncestorFuel store.blocks (store.blocks.size + 1) node slot

/-- `is_ancestor(store, node, ancestor)`. -/
def isAncestor (store : Store P f) (node ancestor : ForkChoiceNode) : M Bool := do
  let ancestorBlock ← lookup store.blocks ancestor.root "is_ancestor: store.blocks[ancestor.root]"
  pure ((← getAncestor store node ancestorBlock.slot) == ancestor)

/-- The unslashed members of `get_active_validator_indices(state, get_current_epoch(state))`, in
index order, reading `state.validators[index].slashed` for each as the spec's loops do. -/
def unslashedActiveIndices (state : BeaconState P f) (site : String) : M (Array ValidatorIndex) := do
  let active ← getActiveValidatorIndices state (← getCurrentEpoch state)
  let mut out : Array ValidatorIndex := #[]
  for i in active do
    if !(← state.validators.get i.toNat s!"{site}: state.validators[index]").slashed then
      out := out.push i
  pure out

/-- `calculate_committee_fraction(state, committee_percent)`: over the unslashed active
balance (`get_total_balance` of the set, so with its `EFFECTIVE_BALANCE_INCREMENT` floor). -/
def calculateCommitteeFraction (state : BeaconState P f) (committeePercent : U64) : M Gwei := do
  let site := "calculate_committee_fraction"
  let totalBalance ← getTotalBalance state (← unslashedActiveIndices state site)
  let committeeWeight ← totalBalance.div? (← c64 P.SLOTS_PER_EPOCH) site
  (← committeeWeight.mul? committeePercent site).div? (← c64 100) site

/-- `get_checkpoint_block(store, root, epoch)`. -/
def getCheckpointBlock (store : Store P f) (root : Root) (epoch : Epoch) : M Root := do
  pure (← getAncestor store { root } (← computeStartSlotAtEpoch P epoch)).root

/-- `get_supported_node(store, message)`. -/
def getSupportedNode (message : LatestMessage) : ForkChoiceNode := { root := message.root }

/-- `get_attestation_score(store, node, state)`: in index order, the effective balances (at
`state`) of its unslashed active validators whose latest message is not equivocating and
supports a descendant of `node`; the conditions are evaluated as Python's `and` does, left to
right. -/
def getAttestationScore (store : Store P f) (node : ForkChoiceNode) (state : BeaconState P f) :
    M Gwei := do
  let site := "get_attestation_score"
  let mut score := U64.zero
  for i in ← unslashedActiveIndices state site do
    match store.latest_messages.get? i.toNat with
    | none => pure ()
    | some message =>
      if !store.equivocating_indices.contains i.toNat then
        if ← isAncestor store (getSupportedNode message) node then
          let v ← state.validators.get i.toNat s!"{site}: state.validators[index]"
          score ← score.add? v.effective_balance site
  pure score

/-- `compute_proposer_score(state)`. -/
def computeProposerScore (cfg : Config) (state : BeaconState P f) : M Gwei := do
  calculateCommitteeFraction state (← u64 cfg.PROPOSER_SCORE_BOOST "PROPOSER_SCORE_BOOST")

/-- `store.checkpoint_states[store.justified_checkpoint]`. -/
def justifiedCheckpointState (store : Store P f) (site : String) : M (BeaconState P f) :=
  lookup store.checkpoint_states store.justified_checkpoint
    s!"{site}: store.checkpoint_states[store.justified_checkpoint]"

/-- `get_proposer_score(store)`. -/
def getProposerScore (cfg : Config) (store : Store P f) : M Gwei := do
  computeProposerScore cfg (← justifiedCheckpointState store "get_proposer_score")

/-- `get_weight(store, node)`. -/
def getWeight (cfg : Config) (store : Store P f) (node : ForkChoiceNode) : M Gwei := do
  let site := "get_weight"
  let state ← justifiedCheckpointState store site
  let attestationScore ← getAttestationScore store node state
  if store.proposer_boost_root == zeroRoot then
    -- Return only attestation score if `proposer_boost_root` is not set
    return attestationScore
  -- Calculate proposer score if `proposer_boost_root` is set
  let mut proposerScore := U64.zero
  let proposerBoostNode : ForkChoiceNode := { root := store.proposer_boost_root }
  -- Boost is applied if `node` is an ancestor of `proposer_boost_node`
  if ← isAncestor store proposerBoostNode node then
    proposerScore ← getProposerScore cfg store
  attestationScore.add? proposerScore site

/-- `get_voting_source(store, block_root)`. -/
def getVotingSource (cfg : Config) (store : Store P f) (blockRoot : Root) : M Checkpoint := do
  let site := "get_voting_source"
  let block ← lookup store.blocks blockRoot s!"{site}: store.blocks[block_root]"
  let currentEpoch ← getCurrentStoreEpoch cfg store
  let blockEpoch ← computeEpochAtSlot P block.slot
  if currentEpoch > blockEpoch then
    -- The block is from a prior epoch, the voting source will be pulled-up
    lookup store.unrealized_justifications blockRoot s!"{site}: store.unrealized_justifications"
  else
    -- The block is not from a prior epoch, therefore the voting source is not pulled up
    let headState ← lookup store.block_states blockRoot s!"{site}: store.block_states"
    pure headState.current_justified_checkpoint

/-- `get_node_children(store, node)`: the nodes whose block's `parent_root` is `node.root`, in
key order. -/
def getNodeChildren (store : Store P f) (node : ForkChoiceNode) : List ForkChoiceNode :=
  store.blocks.toList.filterMap fun (r, b) =>
    if b.parent_root == node.root then some { root := r } else none

/-- `filter_node_tree(store, node)`, returning the viable nodes of the subtree as a set (the
callers only test membership). Every child is visited before the results are combined, as the
Python loop does. -/
def filterNodeTree (cfg : Config) (store : Store P f) : Nat → ForkChoiceNode → M NodeSet
  | 0, _ => throw (.assert "filter_node_tree: node tree deeper than the store")
  | fuel + 1, node => do
  let site := "filter_node_tree"
  let children := getNodeChildren store node
  -- If any children branches contain expected finalized/justified checkpoints,
  -- include this node and those descendants in the filtered node tree.
  if !children.isEmpty then
    let mut viableNodes : NodeSet := ∅
    for child in children do
      viableNodes := viableNodes.insertMany (← filterNodeTree cfg store fuel child)
    if !viableNodes.isEmpty then
      return viableNodes.insert node
    return ∅
  let currentEpoch ← getCurrentStoreEpoch cfg store
  let votingSource ← getVotingSource cfg store node.root
  -- The voting source should be either at the same height as the store's justified checkpoint or
  -- not more than two epochs ago
  let correctJustified ←
    if store.justified_checkpoint.epoch == GENESIS_EPOCH then pure true
    else if votingSource.epoch == store.justified_checkpoint.epoch then pure true
    else pure ((← votingSource.epoch.add? (← c64 2) site) ≥ currentEpoch)
  let finalizedCheckpointBlock ← getCheckpointBlock store node.root store.finalized_checkpoint.epoch
  let correctFinalized :=
    store.finalized_checkpoint.epoch == GENESIS_EPOCH ||
      store.finalized_checkpoint.root == finalizedCheckpointBlock
  -- If expected finalized/justified, add to viable node tree and signal viability to parent.
  if correctJustified && correctFinalized then
    return (∅ : NodeSet).insert node
  -- Otherwise, branch not viable
  return ∅

/-- `get_filtered_node_tree(store)`. -/
def getFilteredNodeTree (cfg : Config) (store : Store P f) : M NodeSet := do
  let base : ForkChoiceNode := { root := store.justified_checkpoint.root }
  filterNodeTree cfg store (store.blocks.size + 1) base

/-- The LMD-GHOST walk of `get_head` over the filtered node tree, skipping the children for
which `excluded` holds. `get_head` excludes nothing; optimistic sync excludes `INVALIDATED`
blocks (`JauneConsensus/Sync.lean`). Children are compared by `(get_weight, root)`, ties in
weight broken by the lexicographically higher root (`Root` order is byte order). -/
def getHeadExcluding (cfg : Config) (store : Store P f) (excluded : Root → Bool) :
    M ForkChoiceNode := do
  -- Get filtered node tree that only includes viable branches
  let nodes ← getFilteredNodeTree cfg store
  -- Execute the LMD-GHOST fork choice
  let mut head : ForkChoiceNode := { root := store.justified_checkpoint.root }
  for _ in [0:store.blocks.size + 1] do
    let children := (getNodeChildren store head).filter
      (fun c => nodes.contains c && !excluded c.root)
    if children.isEmpty then return head
    -- Sort by latest attesting balance with ties broken lexicographically
    let mut best : Option (Gwei × ForkChoiceNode) := none
    for child in children do
      let w ← getWeight cfg store child
      best := match best with
        | none => some (w, child)
        | some (bw, b) =>
          if bw < w || (bw == w && b.root < child.root) then some (w, child) else some (bw, b)
    match best with
    | some (_, n) => head := n
    | none => return head
  throw (.assert "get_head: walk longer than the block tree")

/-- `get_head(store)`. -/
def getHead (cfg : Config) (store : Store P f) : M ForkChoiceNode :=
  getHeadExcluding cfg store (fun _ => false)

/-- `update_checkpoints(store, justified_checkpoint, finalized_checkpoint)`. -/
def updateCheckpoints (store : Store P f) (justifiedCheckpoint finalizedCheckpoint : Checkpoint) :
    Store P f :=
  -- Update justified checkpoint
  let store := if justifiedCheckpoint.epoch > store.justified_checkpoint.epoch then
      { store with justified_checkpoint := justifiedCheckpoint } else store
  -- Update finalized checkpoint
  if finalizedCheckpoint.epoch > store.finalized_checkpoint.epoch then
    { store with finalized_checkpoint := finalizedCheckpoint } else store

/-- `update_unrealized_checkpoints(store, unrealized_justified_checkpoint,
unrealized_finalized_checkpoint)`. -/
def updateUnrealizedCheckpoints (store : Store P f)
    (unrealizedJustified unrealizedFinalized : Checkpoint) : Store P f :=
  let store := if unrealizedJustified.epoch > store.unrealized_justified_checkpoint.epoch then
      { store with unrealized_justified_checkpoint := unrealizedJustified } else store
  if unrealizedFinalized.epoch > store.unrealized_finalized_checkpoint.epoch then
    { store with unrealized_finalized_checkpoint := unrealizedFinalized } else store

/-- `get_latest_message_epoch(latest_message)`. -/
def getLatestMessageEpoch (latestMessage : LatestMessage) : Epoch := latestMessage.epoch

/-! ## Proposer head and re-org helpers -/

/-- `is_head_late(store, head_root)`. -/
def isHeadLate (store : Store P f) (headRoot : Root) : M Bool := do
  pure !(← lookup store.block_timeliness headRoot "is_head_late: store.block_timeliness")

/-- `is_shuffling_stable(slot)`. -/
def isShufflingStable (P : Preset) (slot : Slot) : M Bool := do
  pure ((← slot.mod? (← c64 P.SLOTS_PER_EPOCH) "is_shuffling_stable").toNat != 0)

/-- `is_ffg_competitive(store, head_root, parent_root)`. -/
def isFfgCompetitive (store : Store P f) (headRoot parentRoot : Root) : M Bool := do
  let site := "is_ffg_competitive: store.unrealized_justifications"
  pure ((← lookup store.unrealized_justifications headRoot site) ==
    (← lookup store.unrealized_justifications parentRoot site))

/-- `is_finalization_ok(store, slot)`. -/
def isFinalizationOk (cfg : Config) (store : Store P f) (slot : Slot) : M Bool := do
  let epochsSinceFinalization ← (← computeEpochAtSlot P slot).sub?
    store.finalized_checkpoint.epoch "is_finalization_ok"
  pure (epochsSinceFinalization ≤
    (← u64 cfg.REORG_MAX_EPOCHS_SINCE_FINALIZATION "REORG_MAX_EPOCHS_SINCE_FINALIZATION"))

/-- `is_proposing_on_time(store)`. -/
def isProposingOnTime (cfg : Config) (store : Store P f) : M Bool := do
  pure ((← getTimeIntoSlotMs cfg store) ≤ (← getProposerReorgCutoffMs cfg))

/-- `is_head_weak(store, head_root)`: the attestation score of the head at the justified state
plus the justified-state effective balances of the equivocating members of the head slot's
committees (computed from the head's post-state), against the head threshold. -/
def isHeadWeak (cfg : Config) (store : Store P f) (headRoot : Root) : M Bool := do
  let site := "is_head_weak"
  -- Calculate weight threshold for weak head
  let justifiedState ← justifiedCheckpointState store site
  let reorgThreshold ← calculateCommitteeFraction justifiedState
    (← u64 cfg.REORG_HEAD_WEIGHT_THRESHOLD "REORG_HEAD_WEIGHT_THRESHOLD")
  -- Compute head weight including equivocations
  let headState ← lookup store.block_states headRoot s!"{site}: store.block_states[head_root]"
  let headBlock ← lookup store.blocks headRoot s!"{site}: store.blocks[head_root]"
  let epoch ← computeEpochAtSlot P headBlock.slot
  let mut headWeight ← getAttestationScore store { root := headRoot } justifiedState
  for index in [0:(← getCommitteeCountPerSlot headState epoch).toNat] do
    let committee ← getBeaconCommittee headState headBlock.slot (← u64 index "CommitteeIndex")
    let mut equivocating := U64.zero
    for i in committee do
      if store.equivocating_indices.contains i.toNat then
        let v ← justifiedState.validators.get i.toNat s!"{site}: justified_state.validators[index]"
        equivocating ← equivocating.add? v.effective_balance site
    headWeight ← headWeight.add? equivocating site
  pure (headWeight < reorgThreshold)

/-- `is_parent_strong(store, root)`: the attestation score of `root`'s parent. -/
def isParentStrong (cfg : Config) (store : Store P f) (root : Root) : M Bool := do
  let site := "is_parent_strong"
  let justifiedState ← justifiedCheckpointState store site
  let parentThreshold ← calculateCommitteeFraction justifiedState
    (← u64 cfg.REORG_PARENT_WEIGHT_THRESHOLD "REORG_PARENT_WEIGHT_THRESHOLD")
  let parentRoot := (← lookup store.blocks root s!"{site}: store.blocks[root]").parent_root
  let parentWeight ← getAttestationScore store { root := parentRoot } justifiedState
  pure (parentWeight > parentThreshold)

/-- `is_proposer_equivocation(store, root)`: more than one stored block has `root`'s proposer
and slot. -/
def isProposerEquivocation (store : Store P f) (root : Root) : M Bool := do
  let block ← lookup store.blocks root "is_proposer_equivocation: store.blocks[root]"
  let matching := store.blocks.toList.filter fun (_, b) =>
    b.proposer_index == block.proposer_index && b.slot == block.slot
  pure (matching.length > 1)

/-- `get_proposer_head(store, head_node, slot)`: Phase0's, or from Fulu on the modified one
without the shuffling-stability condition (`specs/fulu/fork-choice.md`). Every condition is
computed before they are combined, as the Python builds the lists passed to `all`. -/
def getProposerHead (cfg : Config) (store : Store P f) (headNode : ForkChoiceNode) (slot : Slot) :
    M ForkChoiceNode := do
  let site := "get_proposer_head"
  let headBlock ← lookup store.blocks headNode.root s!"{site}: store.blocks[head_node.root]"
  let parentRoot := headBlock.parent_root
  let parentBlock ← lookup store.blocks parentRoot s!"{site}: store.blocks[parent_root]"
  let parentNode : ForkChoiceNode := { root := parentRoot }
  -- Only re-org the head block if it arrived later than the attestation deadline.
  let headLate ← isHeadLate store headNode.root
  -- Do not re-org on an epoch boundary where the proposer shuffling could change.
  -- [Removed in Fulu] the proposer lookahead fixes proposer assignments before the boundary.
  let shufflingStable ← if f.atLeast .fulu then pure true else isShufflingStable P slot
  -- Ensure that the FFG information of the new head will be competitive with the current head.
  let ffgCompetitive ← isFfgCompetitive store headNode.root parentRoot
  -- Do not re-org if the chain is not finalizing with acceptable frequency.
  let finalizationOk ← isFinalizationOk cfg store slot
  -- Only re-org if we are proposing on-time.
  let proposingOnTime ← isProposingOnTime cfg store
  -- Only re-org a single slot at most.
  let parentSlotOk := (← parentBlock.slot.add? U64.one site) == headBlock.slot
  let currentTimeOk := (← headBlock.slot.add? U64.one site) == slot
  let singleSlotReorg := parentSlotOk && currentTimeOk
  -- Check that the head has few enough votes to be overpowered by our proposer boost.
  require (store.proposer_boost_root != headNode.root) s!"{site}: boost has worn off"
  let headWeak ← isHeadWeak cfg store headNode.root
  -- Check that the missing votes are assigned to the parent and not being hoarded.
  let parentStrong ← isParentStrong cfg store headNode.root
  -- Re-org more aggressively if there is a proposer equivocation in the previous slot.
  let proposerEquivocation ← isProposerEquivocation store headNode.root
  if [headLate, shufflingStable, ffgCompetitive, finalizationOk, proposingOnTime,
      singleSlotReorg, headWeak, parentStrong].all id then
    -- We can re-org the current head by building upon its parent node.
    pure parentNode
  else if [headWeak, currentTimeOk, proposerEquivocation].all id then
    pure parentNode
  else
    pure headNode

/-! ## Pull-up tip and tick handlers -/

/-- `compute_pulled_up_tip(store, block_root)`. -/
def computePulledUpTip (cfg : Config) (store : Store P f) (blockRoot : Root) : M (Store P f) := do
  let site := "compute_pulled_up_tip"
  let state ← lookup store.block_states blockRoot s!"{site}: store.block_states"
  -- Pull up the post-state of the block to the next epoch boundary
  let state ← processJustificationAndFinalization cfg state
  let store := { store with
    unrealized_justifications :=
      store.unrealized_justifications.insert blockRoot state.current_justified_checkpoint }
  let store := updateUnrealizedCheckpoints store state.current_justified_checkpoint
    state.finalized_checkpoint
  -- If the block is from a prior epoch, apply the realized values
  let blockEpoch ← computeEpochAtSlot P (← lookup store.blocks blockRoot s!"{site}: store.blocks").slot
  let currentEpoch ← getCurrentStoreEpoch cfg store
  if blockEpoch < currentEpoch then
    pure (updateCheckpoints store state.current_justified_checkpoint state.finalized_checkpoint)
  else pure store

/-- `on_tick_per_slot(store, time_ms)`. -/
def onTickPerSlot (cfg : Config) (store : Store P f) (timeMs : U64) : M (Store P f) := do
  let previousSlot ← getCurrentSlot cfg store
  -- Update store time
  let store := { store with time_ms := timeMs }
  let currentSlot ← getCurrentSlot cfg store
  -- If this is a new slot, reset store.proposer_boost_root
  let store := if currentSlot > previousSlot then { store with proposer_boost_root := zeroRoot }
    else store
  -- If a new epoch, pull-up justification and finalization from previous epoch
  if currentSlot > previousSlot then
    if (← computeSlotsSinceEpochStart P currentSlot).toNat == 0 then
      return updateCheckpoints store store.unrealized_justified_checkpoint
        store.unrealized_finalized_checkpoint
  pure store

/-- `on_tick(store, time_ms)`. The `while` loop advances `get_current_slot(store)` by exactly one
per iteration, so it runs at most `tick_slot - get_current_slot(store)` times; the bound is that
count, and the loop condition is re-checked on every iteration as in the Python. -/
def onTick (cfg : Config) (store : Store P f) (timeMs : U64) : M (Store P f) := do
  let site := "on_tick"
  -- If the `store.time_ms` falls behind, while loop catches up slot by slot
  -- to ensure that every previous slot is processed with `on_tick_per_slot`
  let tickSlot ← computeSlotAtTimeMs cfg store.genesis_time_ms timeMs
  let bound := tickSlot.toNat - (← getCurrentSlot cfg store).toNat
  let mut store := store
  for _ in [0:bound] do
    let currentSlot ← getCurrentSlot cfg store
    if currentSlot < tickSlot then
      let nextSlot ← currentSlot.add? U64.one site
      let nextSlotTimeMs ← computeTimeAtSlotMs cfg store.genesis_time_ms nextSlot
      store ← onTickPerSlot cfg store nextSlotTimeMs
  require (!((← getCurrentSlot cfg store) < tickSlot)) s!"{site}: catch-up loop bound"
  onTickPerSlot cfg store timeMs

/-! ## Attestation and attester-slashing handlers -/

/-- `validate_target_epoch_against_current_time(store, attestation)`. -/
def validateTargetEpochAgainstCurrentTime (cfg : Config) (store : Store P f)
    (attestation : Attestation P f) : M Unit := do
  let target := attestation.data.target
  -- Attestations must be from the current or previous epoch
  let currentEpoch ← getCurrentStoreEpoch cfg store
  -- `saturating_sub(current_epoch, 1)`
  let previousEpoch ← if currentEpoch > U64.one then
      currentEpoch.sub? U64.one "validate_target_epoch_against_current_time"
    else currentEpoch.sub? currentEpoch "validate_target_epoch_against_current_time"
  -- If attestation target is from a future epoch, delay consideration until the epoch arrives
  require (target.epoch == currentEpoch || target.epoch == previousEpoch)
    "validate_target_epoch_against_current_time: target epoch"

/-- `validate_on_attestation(store, attestation, is_from_block)`. -/
def validateOnAttestation (cfg : Config) (store : Store P f) (attestation : Attestation P f)
    (isFromBlock : Bool) : M Unit := do
  let site := "validate_on_attestation"
  let target := attestation.data.target
  -- If the given attestation is not from a beacon block message, we have to check the target epoch scope.
  if !isFromBlock then validateTargetEpochAgainstCurrentTime cfg store attestation
  -- Check that the epoch number and slot number are matching
  require (target.epoch == (← computeEpochAtSlot P attestation.data.slot)) s!"{site}: target epoch"
  -- Attestation target must be for a known block.
  require (store.blocks.contains target.root) s!"{site}: target block known"
  -- Attestations must be for a known block.
  require (store.blocks.contains attestation.data.beacon_block_root) s!"{site}: block known"
  -- Attestations must not be for blocks in the future.
  let block ← lookup store.blocks attestation.data.beacon_block_root s!"{site}: store.blocks"
  require (block.slot ≤ attestation.data.slot) s!"{site}: block not from the future"
  -- LMD vote must be consistent with FFG vote target
  require (target.root == (← getCheckpointBlock store attestation.data.beacon_block_root target.epoch))
    s!"{site}: LMD vote consistent with FFG target"
  -- Attestations can only affect the fork choice of subsequent slots.
  require ((← getCurrentSlot cfg store) ≥ (← attestation.data.slot.add? U64.one site))
    s!"{site}: attestation slot in the past"

/-- `store_target_checkpoint_state(store, target)`. -/
def storeTargetCheckpointState (ctx : Ctx) (store : Store P f) (target : Checkpoint) :
    M (Store P f) := do
  -- Store target checkpoint state if not yet seen
  if store.checkpoint_states.contains target then return store
  let baseState ← lookup store.block_states target.root
    "store_target_checkpoint_state: store.block_states[target.root]"
  let startSlot ← computeStartSlotAtEpoch P target.epoch
  let baseState ← if baseState.slot < startSlot then processSlots ctx baseState startSlot
    else pure baseState
  pure { store with checkpoint_states := store.checkpoint_states.insert target baseState }

/-- `update_latest_messages(store, attesting_indices, attestation)`. -/
def updateLatestMessages (store : Store P f) (attestingIndices : Array ValidatorIndex)
    (attestation : Attestation P f) : Store P f := Id.run do
  let target := attestation.data.target
  let beaconBlockRoot := attestation.data.beacon_block_root
  let nonEquivocating := attestingIndices.filter (fun i => !store.equivocating_indices.contains i.toNat)
  let mut latest := store.latest_messages
  for i in nonEquivocating do
    let update := match latest.get? i.toNat with
      | none => true
      | some m => target.epoch > m.epoch
    if update then
      latest := latest.insert i.toNat { epoch := target.epoch, root := beaconBlockRoot }
  pure { store with latest_messages := latest }

/-- `on_attestation(store, attestation, is_from_block)`. -/
def onAttestation (ctx : Ctx) (store : Store P f) (attestation : Attestation P f)
    (isFromBlock : Bool := false) : M (Store P f) := do
  validateOnAttestation ctx.cfg store attestation isFromBlock
  let store ← storeTargetCheckpointState ctx store attestation.data.target
  -- Get state at the `target` to fully validate attestation
  let targetState ← lookup store.checkpoint_states attestation.data.target
    "on_attestation: store.checkpoint_states[target]"
  let indexedAttestation ← getIndexedAttestation targetState attestation
  require (← isValidIndexedAttestation ctx targetState indexedAttestation)
    "on_attestation: is_valid_indexed_attestation"
  -- Update latest messages for attesting indices
  pure (updateLatestMessages store indexedAttestation.attesting_indices.toArray attestation)

/-- `on_attester_slashing(store, attester_slashing)`. -/
def onAttesterSlashing (ctx : Ctx) (store : Store P f) (attesterSlashing : AttesterSlashing P f) :
    M (Store P f) := do
  let site := "on_attester_slashing"
  let attestation1 := attesterSlashing.attestation_1
  let attestation2 := attesterSlashing.attestation_2
  require (isSlashableAttestationData attestation1.data attestation2.data) s!"{site}: slashable"
  let state ← lookup store.block_states store.justified_checkpoint.root
    s!"{site}: store.block_states[store.justified_checkpoint.root]"
  require (← isValidIndexedAttestation ctx state attestation1) s!"{site}: attestation_1"
  require (← isValidIndexedAttestation ctx state attestation2) s!"{site}: attestation_2"
  let indices2 := attestation2.attesting_indices.toArray
  let mut equivocating := store.equivocating_indices
  for i in attestation1.attesting_indices.toArray do
    if indices2.contains i then equivocating := equivocating.insert i.toNat
  pure { store with equivocating_indices := equivocating }

/-! ## Data availability and `on_block` -/

/-- The data-availability oracles, implementation and context dependent in the spec:
`retrieve_blobs_and_proofs(beacon_block_root)` (`specs/deneb/fork-choice.md`) and
`retrieve_column_sidecars(beacon_block_root)` (`specs/fulu/fork-choice.md`). Each returns what
it retrieved, or rejects when the data is not available. -/
structure DataOracle (P : Preset) where
  retrieveBlobsAndProofs : Root → M (List (Blob P) × List KZGProof)
  retrieveColumnSidecars : Root → M (List (DataColumnSidecar P))

/-- `is_data_available(beacon_block_root, blob_kzg_commitments)` (`specs/deneb/fork-choice.md`). -/
def isDataAvailableBlobs (oracle : DataOracle P) (beaconBlockRoot : Root)
    (blobKzgCommitments : List KZGCommitment) : M Bool := do
  let (blobs, proofs) ← oracle.retrieveBlobsAndProofs beaconBlockRoot
  verifyBlobKzgProofBatchM (blobs.map (·.toArray.toList)) (blobKzgCommitments.map (·.toArray.toList))
    (proofs.map (·.toArray.toList))

/-- `verify_data_column_sidecar(sidecar)` (`specs/fulu/p2p-interface.md`). -/
def verifyDataColumnSidecar (cfg : Config) (sidecar : DataColumnSidecar P) : M Bool := do
  -- The sidecar index must be within the valid range
  if sidecar.index.toNat ≥ P.NUMBER_OF_COLUMNS then return false
  -- A sidecar for zero blobs is invalid
  let n := sidecar.kzg_commitments.toArray.size
  if n == 0 then return false
  -- Check that the sidecar respects the blob limit
  let epoch ← computeEpochAtSlot P sidecar.signed_block_header.message.slot
  if n > (← getBlobParameters cfg epoch).maxBlobsPerBlock.toNat then return false
  -- The column length must be equal to the number of commitments/proofs
  let len := sidecar.column.toArray.size
  if len != n || len != sidecar.kzg_proofs.toArray.size then return false
  return true

/-- `verify_data_column_sidecar_kzg_proofs(sidecar)` (`specs/fulu/p2p-interface.md`). -/
def verifyDataColumnSidecarKzgProofs (sidecar : DataColumnSidecar P) : M Bool := do
  -- The column index also represents the cell index
  let cellIndices := List.replicate sidecar.column.toArray.size sidecar.index.toNat
  -- Batch verify that the cells match the corresponding commitments and proofs
  verifyCellKzgProofBatchM (sidecar.kzg_commitments.toArray.toList.map (·.toArray.toList))
    cellIndices (sidecar.column.toArray.toList.map (·.toArray.toList))
    (sidecar.kzg_proofs.toArray.toList.map (·.toArray.toList))

/-- `is_data_available(beacon_block_root)` (`specs/fulu/fork-choice.md`): `all(...)` over the
retrieved sidecars, stopping at the first that fails, each conjunction evaluated left to right. -/
def isDataAvailableColumns (cfg : Config) (oracle : DataOracle P) (beaconBlockRoot : Root) :
    M Bool := do
  let columnSidecars ← oracle.retrieveColumnSidecars beaconBlockRoot
  for sidecar in columnSidecars do
    if !(← verifyDataColumnSidecar cfg sidecar) then return false
    if !(← verifyDataColumnSidecarKzgProofs sidecar) then return false
  return true

/-- `record_block_timeliness(store, root)`. -/
def recordBlockTimeliness (cfg : Config) (store : Store P f) (root : Root) : M (Store P f) := do
  let block ← lookup store.blocks root "record_block_timeliness: store.blocks[root]"
  let timeIntoSlotMs ← getTimeIntoSlotMs cfg store
  let attestationThresholdMs ← getAttestationDueMs cfg
  let isBeforeAttestingInterval := timeIntoSlotMs < attestationThresholdMs
  let isTimely := (← getCurrentSlot cfg store) == block.slot && isBeforeAttestingInterval
  pure { store with block_timeliness := store.block_timeliness.insert root isTimely }

/-- `saturating_sub(a, b)` on `Uint64` (`specs/phase0/beacon-chain.md`): `a - b` if `a > b`, else
`a - a`. -/
def saturatingSubU64 (a b : U64) (site : String) : M U64 :=
  if a > b then a.sub? b site else a.sub? a site

/-- `compute_shuffling_lookahead_start_slot(epoch)`. -/
def computeShufflingLookaheadStartSlot (P : Preset) (epoch : Epoch) : M Slot := do
  let site := "compute_shuffling_lookahead_start_slot"
  computeStartSlotAtEpoch P (← saturatingSubU64 epoch (← c64 P.MIN_SEED_LOOKAHEAD) site)

/-- `compute_shuffling_dependent_slot(epoch)`. -/
def computeShufflingDependentSlot (P : Preset) (epoch : Epoch) : M Slot := do
  saturatingSubU64 (← computeShufflingLookaheadStartSlot P epoch) U64.one
    "compute_shuffling_dependent_slot"

/-- `get_shuffling_dependent_root(store, root, epoch)`. -/
def getShufflingDependentRoot (store : Store P f) (root : Root) (epoch : Epoch) : M Root := do
  pure (← getAncestor store { root } (← computeShufflingDependentSlot P epoch)).root

/-- `update_proposer_boost_root(store, head, root)`: the boost goes to a timely first block of the
slot whose shuffling dependent root equals the canonical head's. -/
def updateProposerBoostRoot (cfg : Config) (store : Store P f) (head root : Root) :
    M (Store P f) := do
  let isFirstBlock := store.proposer_boost_root == zeroRoot
  let isTimely ← lookup store.block_timeliness root "update_proposer_boost_root: block_timeliness"
  let epoch ← getCurrentStoreEpoch cfg store
  let headDependentRoot ← getShufflingDependentRoot store head epoch
  let blockDependentRoot ← getShufflingDependentRoot store root epoch
  let isSameDependentRoot := headDependentRoot == blockDependentRoot
  -- Add proposer score boost if the block is timely, not conflicting with an
  -- existing block, with the same dependent root as the canonical chain head.
  if isTimely && isFirstBlock && isSameDependentRoot then
    pure { store with proposer_boost_root := root }
  else pure store

/-- `on_block(store, signed_block)`: Deneb's handler for Electra (with `is_data_available` over
blobs), Fulu's for Fulu (over data-column sidecars). Each keeps its own operation order: Fulu
copies the parent state right after the parent check, Deneb after the availability check. A
known block returns the store unchanged. -/
def onBlock (ctx : Ctx) (oracle : DataOracle P) (store : Store P f)
    (signedBlock : SignedBeaconBlock P f) : M (Store P f) := do
  let cfg := ctx.cfg
  let site := "on_block"
  let block := signedBlock.message
  let blockRoot : Root := Ssz.hashTreeRoot block
  -- Return early if the block is already known
  if store.blocks.contains blockRoot then return store
  -- Parent block must be known
  require (store.block_states.contains block.parent_root) s!"{site}: parent known"
  -- [Fulu] Make a copy of the state to avoid mutability issues
  let fuluPreState ← if f.atLeast .fulu then
      some <$> lookup store.block_states block.parent_root s!"{site}: store.block_states[parent]"
    else pure none
  -- Blocks cannot be in the future.
  require ((← getCurrentSlot cfg store) ≥ block.slot) s!"{site}: not from the future"
  -- Check that block is later than the finalized epoch slot
  let finalizedSlot ← computeStartSlotAtEpoch P store.finalized_checkpoint.epoch
  require (block.slot > finalizedSlot) s!"{site}: later than the finalized slot"
  -- Check block is a descendant of the finalized block at the checkpoint finalized slot
  let finalizedCheckpointBlock ← getCheckpointBlock store block.parent_root
    store.finalized_checkpoint.epoch
  require (store.finalized_checkpoint.root == finalizedCheckpointBlock)
    s!"{site}: descends from the finalized checkpoint"
  -- Check if blob data is available
  let state ← match fuluPreState with
    | some state => do
      -- [Fulu] `is_data_available(block_root)`
      require (← isDataAvailableColumns cfg oracle blockRoot) s!"{site}: is_data_available"
      pure state
    | none => do
      -- [Deneb] `is_data_available(block_root, block.body.blob_kzg_commitments)`
      require (← isDataAvailableBlobs oracle blockRoot
        block.body.blob_kzg_commitments.toArray.toList) s!"{site}: is_data_available"
      -- [Deneb] Make a copy of the state to avoid mutability issues
      lookup store.block_states block.parent_root s!"{site}: store.block_states[parent]"
  -- Check the block is valid and compute the post-state
  let state ← stateTransition ctx state signedBlock true
  -- Compute head before applying the block
  let head ← getHead cfg store
  -- Add new block and its state to the store
  let store := { store with
    blocks := store.blocks.insert blockRoot block
    block_states := store.block_states.insert blockRoot state }
  let store ← recordBlockTimeliness cfg store blockRoot
  let store ← updateProposerBoostRoot cfg store head.root blockRoot
  -- Update checkpoints in store if necessary
  let store := updateCheckpoints store state.current_justified_checkpoint state.finalized_checkpoint
  -- Eagerly compute unrealized justification and finality.
  computePulledUpTip cfg store blockRoot

end JauneConsensus
