import JauneConsensus.ForkChoice
import JauneConsensus.GloasEnvelope
import JauneConsensus.GloasBlock
import JauneConsensus.GloasEpoch

/-!
# Fork choice (Gloas)

`specs/gloas/fork-choice.md` at `v1.7.0-beta.4` over the phase0 fork choice of the same release
(`JauneConsensus/ForkChoice.lean` transcribes phase0 to Fulu): ePBS (EIP-7732) splits every block
into a *pending* node with an *empty* and, once its envelope is verified, a *full* child; the
store gains the verified envelopes (`payloads`) and the payload-timeliness committee's two votes
per block; latest messages carry their slot and whether they attest to the payload.

Gloas states, blocks and attestations are the separate structures of
`JauneConsensus/ContainersGloas.lean`, so the store, the node and every function that reads them
are restated here over those types, in `namespace JauneConsensus.Gloas`, where an unqualified name
resolves to the Gloas declaration first. The functions Gloas leaves unmodified keep the phase0 text
of `ForkChoice.lean`; the type-independent helpers (time, slot arithmetic,
`compute_shuffling_dependent_slot`, `lookup`) are reused from there.

The Gloas state transition (`process_slots`, `state_transition`) is a parameter (`Transition`) like
the data-availability oracle (`DataOracle`): `on_block`, `on_attestation` and the fast confirmation
rule's pulled-up head state call it.

As in `ForkChoice.lean` the `Store` is a value, every handler returns the updated store or a typed
rejection, and the walks the Python bounds only by the shape of the block tree carry fuel equal to
the number of stored blocks plus one (each `pending` node has at most two children, and every node
of a walk is a distinct `(root, payload_status)`).
-/

namespace JauneConsensus.Gloas

open Jaune (Bytes B256)

variable {P : Preset}

/-! ## Types and constants -/

/-- `PayloadStatus` (`Uint8`): one of `PAYLOAD_STATUS_EMPTY` (0), `PAYLOAD_STATUS_FULL` (1),
`PAYLOAD_STATUS_PENDING` (2). -/
inductive PayloadStatus
  | empty | full | pending
  deriving DecidableEq, BEq, Repr

/-- The `Uint8` value of a payload status. -/
def PayloadStatus.toNat : PayloadStatus → Nat
  | .empty => 0
  | .full => 1
  | .pending => 2

/-- `PAYLOAD_TIMELY_THRESHOLD`: `PTC_SIZE // 2`. -/
def PAYLOAD_TIMELY_THRESHOLD (P : Preset) : Nat := P.PTC_SIZE / 2

/-- `DATA_AVAILABILITY_TIMELY_THRESHOLD`: `PTC_SIZE // 2`. -/
def DATA_AVAILABILITY_TIMELY_THRESHOLD (P : Preset) : Nat := P.PTC_SIZE / 2

/-- `ATTESTATION_TIMELINESS_INDEX`. -/
def ATTESTATION_TIMELINESS_INDEX : Nat := 0

/-- `PTC_TIMELINESS_INDEX`. -/
def PTC_TIMELINESS_INDEX : Nat := 1

/-- `ForkChoiceNode` (Gloas): a block root and a payload status. -/
structure ForkChoiceNode where
  root : Root
  payload_status : PayloadStatus
  deriving DecidableEq, BEq

/-- The order keying sets of nodes: by root, then by payload status. -/
def ForkChoiceNode.cmp (a b : ForkChoiceNode) : Ordering :=
  (compare a.root b.root).then (compare a.payload_status.toNat b.payload_status.toNat)

/-- A set of nodes (the spec's `Sequence[ForkChoiceNode]` where only membership is read). -/
abbrev NodeSet := Std.TreeSet ForkChoiceNode ForkChoiceNode.cmp

/-- `LatestMessage` (Gloas): the slot instead of the epoch, and `payload_present`. -/
structure LatestMessage where
  slot : Slot
  root : Root
  payload_present : Bool
  deriving DecidableEq, BEq

/-- `Store` (Gloas). `block_timeliness[root]` has `NUM_BLOCK_TIMELINESS_DEADLINES` (2) entries;
each vote list has `PTC_SIZE` entries, `none` for a position that has not voted. -/
structure Store (P : Preset) where
  time_ms : U64
  genesis_time_ms : U64
  justified_checkpoint : Checkpoint
  finalized_checkpoint : Checkpoint
  unrealized_justified_checkpoint : Checkpoint
  unrealized_finalized_checkpoint : Checkpoint
  proposer_boost_root : Root
  equivocating_indices : Std.TreeSet Nat compare
  blocks : RootMap (BeaconBlock P)
  block_states : RootMap (BeaconState P)
  block_timeliness : RootMap (Array Bool)
  checkpoint_states : Std.TreeMap Checkpoint (BeaconState P) Checkpoint.cmp
  latest_messages : Std.TreeMap Nat LatestMessage compare
  unrealized_justifications : RootMap Checkpoint
  payloads : RootMap (ExecutionPayloadEnvelope P)
  payload_timeliness_vote : RootMap (Array (Option Bool))
  payload_data_availability_vote : RootMap (Array (Option Bool))

/-- The Gloas state transition the handlers call: `process_slots(state, slot)` and
`state_transition(state, signed_block, validate_result)`. -/
structure Transition (P : Preset) where
  processSlots : Ctx → BeaconState P → Slot → M (BeaconState P)
  stateTransition : Ctx → BeaconState P → SignedBeaconBlock P → Bool → M (BeaconState P)

/-- The implementation-dependent oracle `retrieve_column_sidecars_and_kzg_commitments`
(`specs/gloas/fork-choice.md`, `is_data_available`): the column sidecars to sample and the
block's KZG commitments, or a rejection when they are not available. -/
structure DataOracle (P : Preset) where
  retrieveColumnSidecarsAndKzgCommitments :
    Root → M (List (DataColumnSidecar P) × List KZGCommitment)

/-! ## The store and time -/

/-- `get_forkchoice_store(anchor_state, anchor_block)` (Gloas). -/
def getForkchoiceStore (cfg : Config) (anchorState : BeaconState P)
    (anchorBlock : BeaconBlock P) : M (Store P) := do
  let site := "get_forkchoice_store"
  require (anchorBlock.state_root == Ssz.hashTreeRoot anchorState) s!"{site}: anchor state root"
  let anchorRoot : Root := Ssz.hashTreeRoot anchorBlock
  let anchorEpoch ← getCurrentEpoch anchorState
  let justifiedCheckpoint : Checkpoint := { epoch := anchorEpoch, root := anchorRoot }
  let finalizedCheckpoint : Checkpoint := { epoch := anchorEpoch, root := anchorRoot }
  let genesisTimeMs ← secondsToMilliseconds anchorState.genesis_time
  let noVotes : Array (Option Bool) := Array.replicate P.PTC_SIZE none
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
    block_timeliness := (∅ : RootMap _).insert anchorRoot #[true, true]
    checkpoint_states := (∅ : Std.TreeMap Checkpoint _ Checkpoint.cmp).insert justifiedCheckpoint
      anchorState
    latest_messages := ∅
    unrealized_justifications := (∅ : RootMap _).insert anchorRoot justifiedCheckpoint
    payloads := ∅
    payload_timeliness_vote := (∅ : RootMap _).insert anchorRoot noVotes
    payload_data_availability_vote := (∅ : RootMap _).insert anchorRoot noVotes }

/-- `get_current_slot(store)`. -/
def getCurrentSlot (cfg : Config) (store : Store P) : M Slot :=
  computeSlotAtTimeMs cfg store.genesis_time_ms store.time_ms

/-- `get_time_into_slot_ms(store)`. -/
def getTimeIntoSlotMs (cfg : Config) (store : Store P) : M U64 := do
  store.time_ms.sub? (← computeTimeAtSlotMs cfg store.genesis_time_ms (← getCurrentSlot cfg store))
    "get_time_into_slot_ms"

/-- `get_current_store_epoch(store)`. -/
def getCurrentStoreEpoch (cfg : Config) (store : Store P) : M Epoch := do
  computeEpochAtSlot P (← getCurrentSlot cfg store)

/-- `get_attestation_due_ms()` (Gloas: `ATTESTATION_DUE_BPS_GLOAS`). -/
def getAttestationDueMs (cfg : Config) : M U64 := do
  getSlotComponentDurationMs cfg (← u64 cfg.ATTESTATION_DUE_BPS_GLOAS "ATTESTATION_DUE_BPS_GLOAS")

/-- `get_payload_due_ms()`. -/
def getPayloadDueMs (cfg : Config) : M U64 := do
  getSlotComponentDurationMs cfg (← u64 cfg.PAYLOAD_DUE_BPS "PAYLOAD_DUE_BPS")

/-- `get_payload_attestation_due_ms()`. -/
def getPayloadAttestationDueMs (cfg : Config) : M U64 := do
  getSlotComponentDurationMs cfg (← u64 cfg.PAYLOAD_ATTESTATION_DUE_BPS "PAYLOAD_ATTESTATION_DUE_BPS")

/-! ## Payload status helpers -/

/-- `is_payload_verified(store, root)`. -/
def isPayloadVerified (store : Store P) (root : Root) : Bool := store.payloads.contains root

/-- The count of non-`None` votes equal to `want`. -/
private def countVotes (votes : Array (Option Bool)) (want : Bool) : Nat :=
  votes.foldl (fun n v => match v with | some b => if b == want then n + 1 else n | none => n) 0

/-- `payload_timeliness(store, root, timely)`. -/
def payloadTimeliness (store : Store P) (root : Root) (timely : Bool) : M Bool := do
  -- The beacon block root must be known
  require (store.payload_timeliness_vote.contains root) "payload_timeliness: root known"
  -- If the payload is not locally available, the payload
  -- is not considered available regardless of the PTC vote
  if !isPayloadVerified store root then return !timely
  let votes ← lookup store.payload_timeliness_vote root "payload_timeliness"
  pure (countVotes votes timely > PAYLOAD_TIMELY_THRESHOLD P)

/-- `payload_data_availability(store, root, available)`. -/
def payloadDataAvailability (store : Store P) (root : Root) (available : Bool) : M Bool := do
  -- The beacon block root must be known
  require (store.payload_data_availability_vote.contains root)
    "payload_data_availability: root known"
  -- If the payload is not locally available, the blob data
  -- is not considered available regardless of the PTC vote
  if !isPayloadVerified store root then return !available
  let votes ← lookup store.payload_data_availability_vote root "payload_data_availability"
  pure (countVotes votes available > DATA_AVAILABILITY_TIMELY_THRESHOLD P)

/-- `get_parent_payload_status(store, block)`: `FULL` when the block's bid builds on the parent's
committed payload hash. -/
def getParentPayloadStatus (store : Store P) (block : BeaconBlock P) : M PayloadStatus := do
  let parent ← lookup store.blocks block.parent_root
    "get_parent_payload_status: store.blocks[block.parent_root]"
  let parentBlockHash := block.body.signed_execution_payload_bid.message.parent_block_hash
  let messageBlockHash := parent.body.signed_execution_payload_bid.message.block_hash
  pure (if parentBlockHash == messageBlockHash then .full else .empty)

/-- `is_parent_node_full(store, block)`. -/
def isParentNodeFull (store : Store P) (block : BeaconBlock P) : M Bool := do
  pure ((← getParentPayloadStatus store block) == .full)

/-! ## Block tree helpers -/

/-- `get_ancestor` with an explicit bound on the number of parent steps. -/
def getAncestorFuel (store : Store P) : Nat → ForkChoiceNode → Slot → M ForkChoiceNode
  | 0, _, _ => throw (.assert "get_ancestor: parent chain longer than the store")
  | fuel + 1, node, slot => do
    let block ← lookup store.blocks node.root "get_ancestor: store.blocks[node.root]"
    if block.slot > slot then
      let parent : ForkChoiceNode :=
        { root := block.parent_root, payload_status := ← getParentPayloadStatus store block }
      getAncestorFuel store fuel parent slot
    else pure node

/-- `get_ancestor(store, node, slot)` (Gloas): the ancestor node at `slot`, with the payload status
its child on the chain builds on. -/
def getAncestor (store : Store P) (node : ForkChoiceNode) (slot : Slot) : M ForkChoiceNode :=
  getAncestorFuel store (store.blocks.size + 1) node slot

/-- `is_ancestor(store, node, ancestor)` (Gloas): a `PENDING` ancestor matches either payload
status. -/
def isAncestor (store : Store P) (node ancestor : ForkChoiceNode) : M Bool := do
  let ancestorBlock ← lookup store.blocks ancestor.root "is_ancestor: store.blocks[ancestor.root]"
  let nodeAncestor ← getAncestor store node ancestorBlock.slot
  if nodeAncestor.root != ancestor.root then return false
  pure (nodeAncestor.payload_status == ancestor.payload_status ||
    ancestor.payload_status == .pending)

/-- `get_checkpoint_block(store, root, epoch)` (Gloas). -/
def getCheckpointBlock (store : Store P) (root : Root) (epoch : Epoch) : M Root := do
  let epochFirstSlot ← computeStartSlotAtEpoch P epoch
  pure (← getAncestor store { root, payload_status := .pending } epochFirstSlot).root

/-- `get_supported_node(store, message)` (Gloas): a message from a later slot than its block
supports the block's `FULL` or `EMPTY` node, otherwise its `PENDING` node. -/
def getSupportedNode (store : Store P) (message : LatestMessage) : M ForkChoiceNode := do
  let block ← lookup store.blocks message.root "get_supported_node: store.blocks[message.root]"
  let payloadStatus : PayloadStatus :=
    if block.slot < message.slot then
      if message.payload_present then .full else .empty
    else .pending
  pure { root := message.root, payload_status := payloadStatus }

/-- The unslashed members of `get_active_validator_indices(state, get_current_epoch(state))`, in
index order. -/
def unslashedActiveIndices (state : BeaconState P) (site : String) : M (Array ValidatorIndex) := do
  let active ← getActiveValidatorIndices state (← getCurrentEpoch state)
  let mut out : Array ValidatorIndex := #[]
  for i in active do
    if !(← state.validators.get i.toNat s!"{site}: state.validators[index]").slashed then
      out := out.push i
  pure out

/-- `calculate_committee_fraction(state, committee_percent)`. -/
def calculateCommitteeFraction (state : BeaconState P) (committeePercent : U64) : M Gwei := do
  let site := "calculate_committee_fraction"
  let totalBalance ← getTotalBalance state (← unslashedActiveIndices state site)
  let committeeWeight ← totalBalance.div? (← c64 P.SLOTS_PER_EPOCH) site
  (← committeeWeight.mul? committeePercent site).div? (← c64 100) site

/-- `get_attestation_score(store, node, state)`: in index order, the effective balances (at
`state`) of its unslashed active validators whose non-equivocating latest message supports a
descendant of `node`. -/
def getAttestationScore (store : Store P) (node : ForkChoiceNode) (state : BeaconState P) :
    M Gwei := do
  let site := "get_attestation_score"
  let mut score := U64.zero
  for i in ← unslashedActiveIndices state site do
    match store.latest_messages.get? i.toNat with
    | none => pure ()
    | some message =>
      if !store.equivocating_indices.contains i.toNat then
        if ← isAncestor store (← getSupportedNode store message) node then
          let v ← state.validators.get i.toNat s!"{site}: state.validators[index]"
          score ← score.add? v.effective_balance site
  pure score

/-- `compute_proposer_score(state)`. -/
def computeProposerScore (cfg : Config) (state : BeaconState P) : M Gwei := do
  calculateCommitteeFraction state (← u64 cfg.PROPOSER_SCORE_BOOST "PROPOSER_SCORE_BOOST")

/-- `store.checkpoint_states[store.justified_checkpoint]`. -/
def justifiedCheckpointState (store : Store P) (site : String) : M (BeaconState P) :=
  lookup store.checkpoint_states store.justified_checkpoint
    s!"{site}: store.checkpoint_states[store.justified_checkpoint]"

/-- `get_proposer_score(store)`. -/
def getProposerScore (cfg : Config) (store : Store P) : M Gwei := do
  computeProposerScore cfg (← justifiedCheckpointState store "get_proposer_score")

/-! ## Proposer head and re-org helpers -/

/-- `is_head_late(store, head_root)` (Gloas): the attestation-deadline timeliness. -/
def isHeadLate (store : Store P) (headRoot : Root) : M Bool := do
  let t ← lookup store.block_timeliness headRoot "is_head_late: store.block_timeliness"
  pure !(← getAt t ATTESTATION_TIMELINESS_INDEX "is_head_late: block_timeliness[root]")

/-- `is_head_weak(store, head_root)` (Gloas): the attestation score of the head's `PENDING` node
at the justified state plus the justified-state effective balances of the equivocating members of
the head slot's committees, against the head threshold. -/
def isHeadWeak (cfg : Config) (store : Store P) (headRoot : Root) : M Bool := do
  let site := "is_head_weak"
  -- Calculate weight threshold for weak head
  let justifiedState ← justifiedCheckpointState store site
  let reorgThreshold ← calculateCommitteeFraction justifiedState
    (← u64 cfg.REORG_HEAD_WEIGHT_THRESHOLD "REORG_HEAD_WEIGHT_THRESHOLD")
  -- Compute head weight including equivocations
  let headState ← lookup store.block_states headRoot s!"{site}: store.block_states[head_root]"
  let headBlock ← lookup store.blocks headRoot s!"{site}: store.blocks[head_root]"
  let epoch ← computeEpochAtSlot P headBlock.slot
  let headNode : ForkChoiceNode := { root := headRoot, payload_status := .pending }
  let mut headWeight ← getAttestationScore store headNode justifiedState
  for index in [0:(← getCommitteeCountPerSlot headState epoch).toNat] do
    let committee ← getBeaconCommittee headState headBlock.slot (← u64 index "CommitteeIndex")
    let mut equivocating := U64.zero
    for i in committee do
      if store.equivocating_indices.contains i.toNat then
        let v ← justifiedState.validators.get i.toNat s!"{site}: justified_state.validators[index]"
        equivocating ← equivocating.add? v.effective_balance site
    headWeight ← headWeight.add? equivocating site
  pure (headWeight < reorgThreshold)

/-- `is_parent_strong(store, root)` (Gloas): the attestation score of the parent's `PENDING`
node. -/
def isParentStrong (cfg : Config) (store : Store P) (root : Root) : M Bool := do
  let site := "is_parent_strong"
  let justifiedState ← justifiedCheckpointState store site
  let parentThreshold ← calculateCommitteeFraction justifiedState
    (← u64 cfg.REORG_PARENT_WEIGHT_THRESHOLD "REORG_PARENT_WEIGHT_THRESHOLD")
  let parentRoot := (← lookup store.blocks root s!"{site}: store.blocks[root]").parent_root
  let parentNode : ForkChoiceNode := { root := parentRoot, payload_status := .pending }
  let parentWeight ← getAttestationScore store parentNode justifiedState
  pure (parentWeight > parentThreshold)

/-- `is_ffg_competitive(store, head_root, parent_root)`. -/
def isFfgCompetitive (store : Store P) (headRoot parentRoot : Root) : M Bool := do
  let site := "is_ffg_competitive: store.unrealized_justifications"
  pure ((← lookup store.unrealized_justifications headRoot site) ==
    (← lookup store.unrealized_justifications parentRoot site))

/-- `is_finalization_ok(store, slot)`. -/
def isFinalizationOk (cfg : Config) (store : Store P) (slot : Slot) : M Bool := do
  let epochsSinceFinalization ← (← computeEpochAtSlot P slot).sub?
    store.finalized_checkpoint.epoch "is_finalization_ok"
  pure (epochsSinceFinalization ≤
    (← u64 cfg.REORG_MAX_EPOCHS_SINCE_FINALIZATION "REORG_MAX_EPOCHS_SINCE_FINALIZATION"))

/-- `is_proposing_on_time(store)`. -/
def isProposingOnTime (cfg : Config) (store : Store P) : M Bool := do
  pure ((← getTimeIntoSlotMs cfg store) ≤ (← getProposerReorgCutoffMs cfg))

/-- `is_proposer_equivocation(store, root)`: more than one stored block has `root`'s proposer
and slot. -/
def isProposerEquivocation (store : Store P) (root : Root) : M Bool := do
  let block ← lookup store.blocks root "is_proposer_equivocation: store.blocks[root]"
  let matching := store.blocks.toList.filter fun (_, b) =>
    b.proposer_index == block.proposer_index && b.slot == block.slot
  pure (matching.length > 1)

/-! ## Weights and the head -/

/-- `is_previous_slot_payload_decision(store, node)`: a `FULL` or `EMPTY` node of a block from the
previous slot. -/
def isPreviousSlotPayloadDecision (cfg : Config) (store : Store P) (node : ForkChoiceNode) :
    M Bool := do
  let site := "is_previous_slot_payload_decision"
  let block ← lookup store.blocks node.root s!"{site}: store.blocks[node.root]"
  let isPreviousSlot := (← block.slot.add? U64.one site) == (← getCurrentSlot cfg store)
  let isPayloadDecision := node.payload_status == .empty || node.payload_status == .full
  pure (isPreviousSlot && isPayloadDecision)

/-- `should_build_on_full(store, head, slot)` (called by a proposer; no handler reads it). -/
def shouldBuildOnFull (store : Store P) (head : ForkChoiceNode) (slot : Slot) : M Bool := do
  let site := "should_build_on_full"
  require (head.payload_status != .pending) s!"{site}: head not pending"
  let block ← lookup store.blocks head.root s!"{site}: store.blocks[head.root]"
  if (← block.slot.add? U64.one site) != slot then return head.payload_status == .full
  if head.payload_status == .empty then return false
  if ← payloadTimeliness store head.root false then return false
  if ← payloadDataAvailability store head.root false then return false
  return true

/-- `should_extend_payload(store, root)`: the `or` is evaluated left to right with short
circuit. -/
def shouldExtendPayload (cfg : Config) (store : Store P) (root : Root) : M Bool := do
  let site := "should_extend_payload"
  let block ← lookup store.blocks root s!"{site}: store.blocks[root]"
  require ((← block.slot.add? U64.one site) == (← getCurrentSlot cfg store)) s!"{site}: previous slot"
  if !isPayloadVerified store root then return false
  let proposerRoot := store.proposer_boost_root
  let payloadIsTimely ← payloadTimeliness store root true
  let payloadDataIsAvailable ← payloadDataAvailability store root true
  if payloadIsTimely && payloadDataIsAvailable then return true
  if proposerRoot == zeroRoot then return true
  let proposerBlock ← lookup store.blocks proposerRoot s!"{site}: store.blocks[proposer_root]"
  if proposerBlock.parent_root != root then return true
  isParentNodeFull store proposerBlock

/-- `get_payload_status_tiebreaker(store, node)`. -/
def getPayloadStatusTiebreaker (cfg : Config) (store : Store P) (node : ForkChoiceNode) : M Nat := do
  if ← isPreviousSlotPayloadDecision cfg store node then
    -- To decide on a payload from the previous slot, choose
    -- between FULL and EMPTY based on `should_extend_payload`
    if node.payload_status == .empty then return 1
    if ← shouldExtendPayload cfg store node.root then return 2
    return 0
  else
    return node.payload_status.toNat

/-- `should_apply_proposer_boost(store)`. The comprehension reads `block_timeliness` first for
each stored block, as the Python's `and` does. -/
def shouldApplyProposerBoost (cfg : Config) (store : Store P) : M Bool := do
  let site := "should_apply_proposer_boost"
  if store.proposer_boost_root == zeroRoot then return false
  let block ← lookup store.blocks store.proposer_boost_root s!"{site}: store.blocks[boost]"
  let parentRoot := block.parent_root
  let parent ← lookup store.blocks parentRoot s!"{site}: store.blocks[parent_root]"
  let slot := block.slot
  -- Apply proposer boost if `parent` is not from the previous slot
  if (← parent.slot.add? U64.one site) < slot then return true
  -- Apply proposer boost if `parent` is not weak
  if !(← isHeadWeak cfg store parentRoot) then return true
  -- If `parent` is weak and from the previous slot, apply
  -- proposer boost if there are no early equivocations
  let mut equivocations := 0
  for (root, b) in store.blocks do
    let t ← lookup store.block_timeliness root s!"{site}: store.block_timeliness[root]"
    if ← getAt t PTC_TIMELINESS_INDEX s!"{site}: block_timeliness[root]" then
      if b.proposer_index == parent.proposer_index then
        if (← b.slot.add? U64.one site) == slot then
          if root != parentRoot then equivocations := equivocations + 1
  pure (equivocations == 0)

/-- `get_weight(store, node)` (Gloas). -/
def getWeight (cfg : Config) (store : Store P) (node : ForkChoiceNode) : M Gwei := do
  let site := "get_weight"
  if ← isPreviousSlotPayloadDecision cfg store node then return U64.zero
  let state ← justifiedCheckpointState store site
  let attestationScore ← getAttestationScore store node state
  if !(← shouldApplyProposerBoost cfg store) then
    -- Return only attestation score if proposer boost should not apply
    return attestationScore
  -- Calculate proposer score if proposer boost should apply
  let mut proposerScore := U64.zero
  let proposerBoostNode : ForkChoiceNode :=
    { root := store.proposer_boost_root, payload_status := .pending }
  -- Boost is applied if `node` is an ancestor of `proposer_boost_node`
  if ← isAncestor store proposerBoostNode node then
    proposerScore ← getProposerScore cfg store
  attestationScore.add? proposerScore site

/-- `get_voting_source(store, block_root)`. -/
def getVotingSource (cfg : Config) (store : Store P) (blockRoot : Root) : M Checkpoint := do
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

/-- `get_node_children(store, node)` (Gloas): a `PENDING` node's `EMPTY` child and, once its
payload is verified, its `FULL` child; an `EMPTY` or `FULL` node's children are the `PENDING`
nodes of the blocks built on it with that parent payload status, in key order. -/
def getNodeChildren (store : Store P) (node : ForkChoiceNode) : M (List ForkChoiceNode) := do
  if node.payload_status == .pending then
    let empty : ForkChoiceNode := { root := node.root, payload_status := .empty }
    if isPayloadVerified store node.root then
      return [empty, { root := node.root, payload_status := .full }]
    return [empty]
  let mut out : Array ForkChoiceNode := #[]
  for (r, b) in store.blocks do
    if b.parent_root == node.root then
      if node.payload_status == (← getParentPayloadStatus store b) then
        out := out.push { root := r, payload_status := .pending }
  pure out.toList

/-- `filter_node_tree(store, node)`, returning the viable nodes of the subtree as a set. -/
def filterNodeTree (cfg : Config) (store : Store P) : Nat → ForkChoiceNode → M NodeSet
  | 0, _ => throw (.assert "filter_node_tree: node tree deeper than the store")
  | fuel + 1, node => do
  let site := "filter_node_tree"
  let children ← getNodeChildren store node
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
    else do pure ((← votingSource.epoch.add? (← c64 2) site) ≥ currentEpoch)
  let finalizedCheckpointBlock ← getCheckpointBlock store node.root store.finalized_checkpoint.epoch
  let correctFinalized :=
    store.finalized_checkpoint.epoch == GENESIS_EPOCH ||
      store.finalized_checkpoint.root == finalizedCheckpointBlock
  -- If expected finalized/justified, add to viable node tree and signal viability to parent.
  if correctJustified && correctFinalized then
    return (∅ : NodeSet).insert node
  -- Otherwise, branch not viable
  return ∅

/-- The fuel for walks over nodes: every block gives at most three nodes. -/
def nodeFuel (store : Store P) : Nat := 3 * store.blocks.size + 1

/-- `get_filtered_node_tree(store)` (Gloas): from the justified root's `PENDING` node. -/
def getFilteredNodeTree (cfg : Config) (store : Store P) : M NodeSet := do
  let base : ForkChoiceNode := { root := store.justified_checkpoint.root, payload_status := .pending }
  filterNodeTree cfg store (nodeFuel store) base

/-- `get_head(store)` (Gloas): the LMD-GHOST walk from the justified root's `PENDING` node over the
filtered node tree, children compared by `(get_weight, root, get_payload_status_tiebreaker)`; the
keys of a node's children are distinct, so the maximum is unique. With no viable node, the
justified root's `EMPTY` node. -/
def getHead (cfg : Config) (store : Store P) : M ForkChoiceNode := do
  -- Get filtered node tree that only includes viable branches
  let nodes ← getFilteredNodeTree cfg store
  -- Return empty node if there are no viable nodes
  if nodes.isEmpty then
    return { root := store.justified_checkpoint.root, payload_status := .empty }
  -- Execute the LMD-GHOST fork-choice
  let mut head : ForkChoiceNode :=
    { root := store.justified_checkpoint.root, payload_status := .pending }
  for _ in [0:nodeFuel store] do
    let children := (← getNodeChildren store head).filter nodes.contains
    if children.isEmpty then return head
    -- Sort by latest attesting balance with ties broken lexicographically
    let mut best : Option ((Gwei × Root × Nat) × ForkChoiceNode) := none
    for child in children do
      let key := (← getWeight cfg store child, child.root,
        ← getPayloadStatusTiebreaker cfg store child)
      best := match best with
        | none => some (key, child)
        | some (bk, b) =>
          let greater := bk.1 < key.1 || (bk.1 == key.1 &&
            (bk.2.1 < key.2.1 || (bk.2.1 == key.2.1 && bk.2.2 < key.2.2)))
          if greater then some (key, child) else some (bk, b)
    match best with
    | some (_, n) => head := n
    | none => return head
  throw (.assert "get_head: walk longer than the node tree")

/-- `update_checkpoints(store, justified_checkpoint, finalized_checkpoint)`. -/
def updateCheckpoints (store : Store P) (justifiedCheckpoint finalizedCheckpoint : Checkpoint) :
    Store P :=
  let store := if justifiedCheckpoint.epoch > store.justified_checkpoint.epoch then
      { store with justified_checkpoint := justifiedCheckpoint } else store
  if finalizedCheckpoint.epoch > store.finalized_checkpoint.epoch then
    { store with finalized_checkpoint := finalizedCheckpoint } else store

/-- `update_unrealized_checkpoints(store, unrealized_justified, unrealized_finalized)`. -/
def updateUnrealizedCheckpoints (store : Store P)
    (unrealizedJustified unrealizedFinalized : Checkpoint) : Store P :=
  let store := if unrealizedJustified.epoch > store.unrealized_justified_checkpoint.epoch then
      { store with unrealized_justified_checkpoint := unrealizedJustified } else store
  if unrealizedFinalized.epoch > store.unrealized_finalized_checkpoint.epoch then
    { store with unrealized_finalized_checkpoint := unrealizedFinalized } else store

/-- `get_latest_message_epoch(latest_message)` (Gloas): the epoch of the message's slot. -/
def getLatestMessageEpoch (P : Preset) (latestMessage : LatestMessage) : M Epoch :=
  computeEpochAtSlot P latestMessage.slot

/-- `is_valid_dependent_root(store, root, dependent_slot)` (read by gossip validation; no
handler reads it). -/
def isValidDependentRoot (cfg : Config) (store : Store P) (root : Root) (dependentSlot : Slot) :
    M Bool := do
  if root == (← getHead cfg store).root then return true
  for (_, block) in store.blocks do
    if block.parent_root == root then
      if block.slot > dependentSlot then return true
  return false

/-- `get_proposer_head(store, head_node, slot)` (Gloas): the re-org target keeps the parent's
payload status. Every condition is computed before they are combined. -/
def getProposerHead (cfg : Config) (store : Store P) (headNode : ForkChoiceNode) (slot : Slot) :
    M ForkChoiceNode := do
  let site := "get_proposer_head"
  let headBlock ← lookup store.blocks headNode.root s!"{site}: store.blocks[head_node.root]"
  let parentRoot := headBlock.parent_root
  let parentBlock ← lookup store.blocks parentRoot s!"{site}: store.blocks[parent_root]"
  let parentPayloadStatus ← getParentPayloadStatus store headBlock
  let parentNode : ForkChoiceNode := { root := parentRoot, payload_status := parentPayloadStatus }
  -- Only re-org the head block if it arrived later than the attestation deadline.
  let headLate ← isHeadLate store headNode.root
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
  if [headLate, ffgCompetitive, finalizationOk, proposingOnTime, singleSlotReorg, headWeak,
      parentStrong].all id then
    -- We can re-org the current head by building upon its parent node.
    pure parentNode
  else if [headWeak, currentTimeOk, proposerEquivocation].all id then
    pure parentNode
  else
    pure headNode

/-! ## Pull-up tip and tick handlers -/

/-- `compute_pulled_up_tip(store, block_root)`. -/
def computePulledUpTip (cfg : Config) (store : Store P) (blockRoot : Root) : M (Store P) := do
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
def onTickPerSlot (cfg : Config) (store : Store P) (timeMs : U64) : M (Store P) := do
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

/-- `on_tick(store, time_ms)`: the catch-up loop runs at most `tick_slot - current_slot` times. -/
def onTick (cfg : Config) (store : Store P) (timeMs : U64) : M (Store P) := do
  let site := "on_tick"
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
def validateTargetEpochAgainstCurrentTime (cfg : Config) (store : Store P)
    (attestation : Attestation P) : M Unit := do
  let target := attestation.data.target
  let currentEpoch ← getCurrentStoreEpoch cfg store
  let previousEpoch ← saturatingSubU64 currentEpoch U64.one
    "validate_target_epoch_against_current_time"
  require (target.epoch == currentEpoch || target.epoch == previousEpoch)
    "validate_target_epoch_against_current_time: target epoch"

/-- `validate_on_attestation(store, attestation, is_from_block)` (Gloas: the committee index is
the payload vote, `1` only for an earlier block whose payload is verified). -/
def validateOnAttestation (cfg : Config) (store : Store P) (attestation : Attestation P)
    (isFromBlock : Bool) : M Unit := do
  let site := "validate_on_attestation"
  let target := attestation.data.target
  -- If the given attestation is not from a beacon block message, we have to check the target epoch scope.
  if !isFromBlock then validateTargetEpochAgainstCurrentTime cfg store attestation
  -- Check that the epoch number and slot number are matching.
  require (target.epoch == (← computeEpochAtSlot P attestation.data.slot)) s!"{site}: target epoch"
  -- Attestation target must be for a known block.
  require (store.blocks.contains target.root) s!"{site}: target block known"
  -- Attestations must be for a known block.
  require (store.blocks.contains attestation.data.beacon_block_root) s!"{site}: block known"
  -- Attestations must not be for blocks in the future.
  let blockSlot := (← lookup store.blocks attestation.data.beacon_block_root
    s!"{site}: store.blocks").slot
  require (blockSlot ≤ attestation.data.slot) s!"{site}: block not from the future"
  -- [New in Gloas:EIP7732]
  let index := attestation.data.index.toNat
  require (index == 0 || index == 1) s!"{site}: index in [0, 1]"
  if blockSlot == attestation.data.slot then
    require (index == 0) s!"{site}: same-slot index 0"
  -- If attesting for a full node, the payload must be known
  if index == 1 then
    require (isPayloadVerified store attestation.data.beacon_block_root) s!"{site}: payload known"
  -- LMD vote must be consistent with FFG vote target
  require (target.root == (← getCheckpointBlock store attestation.data.beacon_block_root target.epoch))
    s!"{site}: LMD vote consistent with FFG target"
  -- Attestations can only affect the fork-choice of subsequent slots.
  require ((← getCurrentSlot cfg store) ≥ (← attestation.data.slot.add? U64.one site))
    s!"{site}: attestation slot in the past"

/-- `store_target_checkpoint_state(store, target)`. -/
def storeTargetCheckpointState (tr : Transition P) (ctx : Ctx) (store : Store P)
    (target : Checkpoint) : M (Store P) := do
  -- Store target checkpoint state if not yet seen
  if store.checkpoint_states.contains target then return store
  let baseState ← lookup store.block_states target.root
    "store_target_checkpoint_state: store.block_states[target.root]"
  let startSlot ← computeStartSlotAtEpoch P target.epoch
  let baseState ← if baseState.slot < startSlot then tr.processSlots ctx baseState startSlot
    else pure baseState
  pure { store with checkpoint_states := store.checkpoint_states.insert target baseState }

/-- `update_latest_messages(store, attesting_indices, attestation)` (Gloas: by slot, with the
payload vote). -/
def updateLatestMessages (store : Store P) (attestingIndices : Array ValidatorIndex)
    (attestation : Attestation P) : Store P := Id.run do
  let slot := attestation.data.slot
  let beaconBlockRoot := attestation.data.beacon_block_root
  let payloadPresent := attestation.data.index.toNat == 1
  let nonEquivocating := attestingIndices.filter (fun i => !store.equivocating_indices.contains i.toNat)
  let mut latest := store.latest_messages
  for i in nonEquivocating do
    let update := match latest.get? i.toNat with
      | none => true
      | some m => slot > m.slot
    if update then
      latest := latest.insert i.toNat
        { slot, root := beaconBlockRoot, payload_present := payloadPresent }
  pure { store with latest_messages := latest }

/-- `on_attestation(store, attestation, is_from_block)`. -/
def onAttestation (tr : Transition P) (ctx : Ctx) (store : Store P) (attestation : Attestation P)
    (isFromBlock : Bool := false) : M (Store P) := do
  validateOnAttestation ctx.cfg store attestation isFromBlock
  let store ← storeTargetCheckpointState tr ctx store attestation.data.target
  -- Get state at the `target` to fully validate attestation
  let targetState ← lookup store.checkpoint_states attestation.data.target
    "on_attestation: store.checkpoint_states[target]"
  let indexedAttestation ← getIndexedAttestation targetState attestation
  require (← isValidIndexedAttestation ctx targetState indexedAttestation)
    "on_attestation: is_valid_indexed_attestation"
  -- Update latest messages for attesting indices
  pure (updateLatestMessages store indexedAttestation.attesting_indices.toArray attestation)

/-- `on_attester_slashing(store, attester_slashing)`. -/
def onAttesterSlashing (ctx : Ctx) (store : Store P) (attesterSlashing : AttesterSlashing) :
    M (Store P) := do
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

/-! ## Payload attestations and envelopes -/

/-- `BLSSignature()`: 96 zero bytes. -/
def emptySignature : BLSSignature := ⟨Array.replicate 96 0, by simp⟩

/-- `on_payload_attestation_message(store, ptc_message, is_from_block)`: the message's vote at
every position its validator holds in the slot's PTC. A message for another slot than its
block's leaves the store unchanged. -/
def onPayloadAttestationMessage (ctx : Ctx) (store : Store P)
    (ptcMessage : PayloadAttestationMessage) (isFromBlock : Bool := false) : M (Store P) := do
  let site := "on_payload_attestation_message"
  let data := ptcMessage.data
  -- PTC attestation must be for a known block.
  require (store.block_states.contains data.beacon_block_root) s!"{site}: block known"
  let state ← lookup store.block_states data.beacon_block_root s!"{site}: store.block_states"
  -- PTC votes can only change the vote for their assigned beacon block, return early otherwise
  if data.slot != state.slot then return store
  -- Get all positions of the attester in the PTC
  let ptc ← getPtc ctx.cfg state data.slot
  let mut ptcIndices : Array Nat := #[]
  let mut ptcIndex := 0
  for validatorIndex in ptc.toArray do
    if validatorIndex == ptcMessage.validator_index then ptcIndices := ptcIndices.push ptcIndex
    ptcIndex := ptcIndex + 1
  -- Check that the attester is from the PTC
  require (ptcIndices.size > 0) s!"{site}: attester in the PTC"
  -- Verify the signature and check that its for the current slot if it is coming from the wire
  if !isFromBlock then
    -- Check that the attestation is for the current slot
    require (data.slot == (← getCurrentSlot ctx.cfg store)) s!"{site}: current slot"
    -- Verify the signature
    let indexed : IndexedPayloadAttestation P := {
      attesting_indices := ← SszList.ofArray #[ptcMessage.validator_index] site
      data
      signature := ptcMessage.signature }
    require (← isValidIndexedPayloadAttestation ctx state indexed) s!"{site}: signature"
  -- Update the votes for the block
  let mut timeliness ← lookup store.payload_timeliness_vote data.beacon_block_root
    s!"{site}: store.payload_timeliness_vote"
  let mut availability ← lookup store.payload_data_availability_vote data.beacon_block_root
    s!"{site}: store.payload_data_availability_vote"
  for i in ptcIndices do
    if h : i < timeliness.size then timeliness := timeliness.set i (some data.payload_present) h
    else throw (.index s!"{site}: payload_timeliness_vote" i timeliness.size)
    if h : i < availability.size then
      availability := availability.set i (some data.blob_data_available) h
    else throw (.index s!"{site}: payload_data_availability_vote" i availability.size)
  pure { store with
    payload_timeliness_vote := store.payload_timeliness_vote.insert data.beacon_block_root timeliness
    payload_data_availability_vote :=
      store.payload_data_availability_vote.insert data.beacon_block_root availability }

/-- `notify_ptc_messages(store, state, payload_attestations)`: each block-carried payload
attestation as one message per attesting index, from the block (no signature check). -/
def notifyPtcMessages (ctx : Ctx) (store : Store P) (state : BeaconState P)
    (payloadAttestations : Array (PayloadAttestation P)) : M (Store P) := do
  if state.slot.toNat == 0 then return store
  let mut store := store
  for payloadAttestation in payloadAttestations do
    let indexed ← getIndexedPayloadAttestation ctx.cfg state payloadAttestation
    for idx in indexed.attesting_indices.toArray do
      store ← onPayloadAttestationMessage ctx store
        { validator_index := idx, data := payloadAttestation.data, signature := emptySignature }
        true
  pure store

/-- `verify_data_column_sidecar(sidecar, kzg_commitments)` (`specs/gloas/p2p-interface.md`). -/
def verifyDataColumnSidecar (sidecar : DataColumnSidecar P) (kzgCommitments : List KZGCommitment) :
    Bool :=
  let len := sidecar.column.toArray.size
  -- The sidecar index must be within the valid range
  if sidecar.index.toNat ≥ P.NUMBER_OF_COLUMNS then false
  -- A sidecar for zero blobs is invalid
  else if len == 0 then false
  -- The column length must be equal to the number of commitments
  else if len != kzgCommitments.length then false
  -- The column length must be equal to the number of proofs
  else if len != sidecar.kzg_proofs.toArray.size then false
  else true

/-- `verify_data_column_sidecar_kzg_proofs(sidecar, kzg_commitments)`
(`specs/gloas/p2p-interface.md`). -/
def verifyDataColumnSidecarKzgProofs (sidecar : DataColumnSidecar P)
    (kzgCommitments : List KZGCommitment) : M Bool := do
  -- The column index also represents the cell index
  let cellIndices := List.replicate sidecar.column.toArray.size sidecar.index.toNat
  -- Batch verify that the cells match the corresponding commitments and proofs
  verifyCellKzgProofBatchM (kzgCommitments.map (·.toArray.toList)) cellIndices
    (sidecar.column.toArray.toList.map (·.toArray.toList))
    (sidecar.kzg_proofs.toArray.toList.map (·.toArray.toList))

/-- `is_data_available(beacon_block_root)` (Gloas): `all(...)` over the retrieved sidecars,
stopping at the first that fails. -/
def isDataAvailable (oracle : DataOracle P) (beaconBlockRoot : Root) : M Bool := do
  let (columnSidecars, kzgCommitments) ←
    oracle.retrieveColumnSidecarsAndKzgCommitments beaconBlockRoot
  for sidecar in columnSidecars do
    if !verifyDataColumnSidecar sidecar kzgCommitments then return false
    if !(← verifyDataColumnSidecarKzgProofs sidecar kzgCommitments) then return false
  return true

/-- `on_execution_payload_envelope(store, signed_envelope)`: the envelope of a known block,
whose blob data is available, verified against the block's post-state (with
`ctx.executionValid` as the engine's verdict) and stored. -/
def onExecutionPayloadEnvelope (ctx : Ctx) (oracle : DataOracle P) (store : Store P)
    (signedEnvelope : SignedExecutionPayloadEnvelope P) : M (Store P) := do
  let site := "on_execution_payload_envelope"
  let envelope := signedEnvelope.message
  -- The corresponding beacon block root needs to be known
  require (store.block_states.contains envelope.beacon_block_root) s!"{site}: block known"
  -- Check if blob data is available
  require (← isDataAvailable oracle envelope.beacon_block_root) s!"{site}: is_data_available"
  let state ← lookup store.block_states envelope.beacon_block_root s!"{site}: store.block_states"
  -- Verify the execution payload envelope
  verifyExecutionPayloadEnvelopeB ctx.blsActive ctx.cfg (fun _ => ctx.executionValid) state
    signedEnvelope
  -- Add execution payload envelope to the store
  pure { store with payloads := store.payloads.insert envelope.beacon_block_root envelope }

/-! ## `on_block` -/

/-- `record_block_timeliness(store, root)` (Gloas): timeliness against the attestation and the
PTC deadlines. -/
def recordBlockTimeliness (cfg : Config) (store : Store P) (root : Root) : M (Store P) := do
  let block ← lookup store.blocks root "record_block_timeliness: store.blocks[root]"
  let timeIntoSlotMs ← getTimeIntoSlotMs cfg store
  let attestationThresholdMs ← getAttestationDueMs cfg
  let isCurrentSlot := (← getCurrentSlot cfg store) == block.slot
  let ptcThresholdMs ← getPayloadAttestationDueMs cfg
  let timeliness := #[attestationThresholdMs, ptcThresholdMs].map fun threshold =>
    isCurrentSlot && timeIntoSlotMs < threshold
  pure { store with block_timeliness := store.block_timeliness.insert root timeliness }

/-- `get_shuffling_dependent_root(store, root, epoch)` (Gloas). -/
def getShufflingDependentRoot (store : Store P) (root : Root) (epoch : Epoch) : M Root := do
  let node : ForkChoiceNode := { root, payload_status := .pending }
  let dependentSlot ← computeShufflingDependentSlot P epoch
  pure (← getAncestor store node dependentSlot).root

/-- `update_proposer_boost_root(store, head, root)` (Gloas: attestation-deadline timeliness). -/
def updateProposerBoostRoot (cfg : Config) (store : Store P) (head root : Root) :
    M (Store P) := do
  let isFirstBlock := store.proposer_boost_root == zeroRoot
  let t ← lookup store.block_timeliness root "update_proposer_boost_root: block_timeliness"
  let isTimely ← getAt t ATTESTATION_TIMELINESS_INDEX "update_proposer_boost_root: block_timeliness[root]"
  let epoch ← getCurrentStoreEpoch cfg store
  let headDependentRoot ← getShufflingDependentRoot store head epoch
  let blockDependentRoot ← getShufflingDependentRoot store root epoch
  let isSameDependentRoot := headDependentRoot == blockDependentRoot
  -- Add proposer score boost if the block is timely, not conflicting with an
  -- existing block, with the same dependent root as the canonical chain head.
  if isTimely && isFirstBlock && isSameDependentRoot then
    pure { store with proposer_boost_root := root }
  else pure store

/-- `on_block(store, signed_block)` (Gloas): a block building on its parent's full payload needs
that payload verified; blob availability moves to the envelope; the block's payload attestations
reach the store as PTC messages. A known block returns the store unchanged. -/
def onBlock (tr : Transition P) (ctx : Ctx) (store : Store P) (signedBlock : SignedBeaconBlock P) :
    M (Store P) := do
  let cfg := ctx.cfg
  let site := "on_block"
  let block := signedBlock.message
  let blockRoot : Root := Ssz.hashTreeRoot block
  -- Return early if the block is already known
  if store.blocks.contains blockRoot then return store
  -- Parent block must be known
  require (store.block_states.contains block.parent_root) s!"{site}: parent known"
  -- If this block builds on the parent's full payload, that payload must
  -- have been verified by on_execution_payload_envelope
  if ← isParentNodeFull store block then
    require (isPayloadVerified store block.parent_root) s!"{site}: parent payload verified"
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
  -- Make a copy of the state to avoid mutability issues
  let state ← lookup store.block_states block.parent_root s!"{site}: store.block_states[parent]"
  -- Check the block is valid and compute the post-state
  let state ← tr.stateTransition ctx state signedBlock true
  -- Compute head before applying the block
  let head ← getHead cfg store
  -- Add new block and its state to the store, and a new PTC voting for this block
  let noVotes : Array (Option Bool) := Array.replicate P.PTC_SIZE none
  let store := { store with
    blocks := store.blocks.insert blockRoot block
    block_states := store.block_states.insert blockRoot state
    payload_timeliness_vote := store.payload_timeliness_vote.insert blockRoot noVotes
    payload_data_availability_vote := store.payload_data_availability_vote.insert blockRoot noVotes }
  -- Notify the store about the payload_attestations in the block
  let store ← notifyPtcMessages ctx store state block.body.payload_attestations.toArray
  let store ← recordBlockTimeliness cfg store blockRoot
  let store ← updateProposerBoostRoot cfg store head.root blockRoot
  -- Update checkpoints in store if necessary
  let store := updateCheckpoints store state.current_justified_checkpoint state.finalized_checkpoint
  -- Eagerly compute unrealized justification and finality.
  computePulledUpTip cfg store blockRoot

end JauneConsensus.Gloas
