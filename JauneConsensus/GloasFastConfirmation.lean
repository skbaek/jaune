import JauneConsensus.FastConfirmation
import JauneConsensus.GloasForkChoice

/-!
# Fast confirmation (Gloas)

`specs/gloas/fast-confirmation.md` at `v1.7.0-beta.4` over the phase0 rule of the same release
(`JauneConsensus/FastConfirmation.lean`): Gloas modifies only `get_node_for_root` (the block's
`PENDING` node) and `get_safe_execution_block_hash` (the confirmed block's bid's parent block
hash). Every other function is the phase0 text, restated here over the Gloas fork-choice store
(`JauneConsensus/GloasForkChoice.lean`), so the Gloas `get_ancestor`, `is_ancestor`,
`get_supported_node`, `get_attestation_score` and `get_latest_message_epoch` (by slot) are the ones
it reaches. The type-independent helpers (`is_start_slot_at_epoch`,
`estimate_committee_weight_between_slots` and those it calls, the two constants) are reused from
`FastConfirmation.lean`.

The module notes of `FastConfirmation.lean` apply unchanged: one `get_head(store)` per
`on_fast_confirmation` call (`FcrView.head`), the optimistic-sync status `FcrView.isValid`, and
checked `uint64` arithmetic. `FcrView.tr` is the Gloas `process_slots` the pulled-up head state
uses.
-/

namespace JauneConsensus.Gloas

open Jaune (Bytes B256)

variable {P : Preset}

/-! ## The store -/

/-- `FastConfirmationStore` (`specs/phase0/fast-confirmation.md`). `store` is the fork-choice
store the rule reads; the harness refreshes it from the live store before every call, as the
Python object shares it by reference. -/
structure FastConfirmationStore (P : Preset) where
  store : Store P
  confirmed_root : Root
  previous_epoch_observed_justified_checkpoint : Checkpoint
  current_epoch_observed_justified_checkpoint : Checkpoint
  previous_epoch_greatest_unrealized_checkpoint : Checkpoint
  previous_slot_head : Root
  current_slot_head : Root

/-- `get_fast_confirmation_store(store)`: every variable at the finalized checkpoint. -/
def getFastConfirmationStore (store : Store P) : FastConfirmationStore P :=
  { store
    confirmed_root := store.finalized_checkpoint.root
    previous_epoch_observed_justified_checkpoint := store.finalized_checkpoint
    current_epoch_observed_justified_checkpoint := store.finalized_checkpoint
    previous_epoch_greatest_unrealized_checkpoint := store.finalized_checkpoint
    previous_slot_head := store.finalized_checkpoint.root
    current_slot_head := store.finalized_checkpoint.root }

/-- The reads shared by one `on_fast_confirmation` call (see the module note): the processing
context, the read-only fork-choice store, `get_head(store)` of it, and the optimistic-sync status
`is_one_confirmed` consults. -/
structure FcrView (P : Preset) where
  ctx : Ctx
  store : Store P
  head : ForkChoiceNode
  isValid : Root → Bool
  tr : Transition P

/-! ## Misc helpers -/

/-- `get_node_for_root(block_root)` (Gloas): the block's `PENDING` node. -/
def getNodeForRoot (blockRoot : Root) : ForkChoiceNode :=
  { root := blockRoot, payload_status := .pending }

/-- `get_block_slot(store, block_root)`. -/
def getBlockSlot (store : Store P) (blockRoot : Root) : M Slot := do
  pure (← lookup store.blocks blockRoot "get_block_slot: store.blocks[block_root]").slot

/-- `get_block_epoch(store, block_root)`. -/
def getBlockEpoch (store : Store P) (blockRoot : Root) : M Epoch := do
  computeEpochAtSlot P (← lookup store.blocks blockRoot "get_block_epoch: store.blocks[block_root]").slot

/-- `get_checkpoint_for_block(store, block_root, epoch)`. -/
def getCheckpointForBlock (store : Store P) (blockRoot : Root) (epoch : Epoch) : M Checkpoint := do
  pure { epoch, root := ← getCheckpointBlock store blockRoot epoch }

/-- `get_current_target(store)`. -/
def getCurrentTarget (v : FcrView P) : M Checkpoint := do
  let currentEpoch ← getCurrentStoreEpoch v.ctx.cfg v.store
  getCheckpointForBlock v.store v.head.root currentEpoch

/-- `get_ancestor_roots(store, block_root, terminal_root)`: the ancestors of `block_root`,
inclusive, down to `terminal_root`, exclusive, oldest first; empty when `terminal_root` is not on
the chain. The `while` loop moves to a strictly lower slot each turn; its bound is the number of
stored blocks plus one, and running out is a rejection. -/
def getAncestorRoots (store : Store P) (blockRoot terminalRoot : Root) : M (List Root) := do
  let site := "get_ancestor_roots: store.blocks"
  let mut root := blockRoot
  let mut ancestorRoots : List Root := []
  for _ in [0:store.blocks.size + 1] do
    let block ← lookup store.blocks root site
    let terminal ← lookup store.blocks terminalRoot site
    if !(block.slot > terminal.slot) then
      -- Return empty list if terminal_root is not in the chain of block_root
      return []
    ancestorRoots := root :: ancestorRoots
    root := block.parent_root
    -- Return when terminal_root is reached
    if root == terminalRoot then return ancestorRoots
  throw (.assert "get_ancestor_roots: walk longer than the store")

/-! ## State helpers -/

/-- `get_slot_committee(store, slot)`: every member of every committee of `slot`, shuffled from
the head's post-state. -/
def getSlotCommittee (v : FcrView P) (slot : Slot) : M (Std.TreeSet Nat compare) := do
  let shufflingSource ← lookup v.store.block_states v.head.root
    "get_slot_committee: store.block_states[head]"
  let committeesCount ← getCommitteeCountPerSlot shufflingSource (← computeEpochAtSlot P slot)
  let mut participants : Std.TreeSet Nat compare := ∅
  for i in [0:committeesCount.toNat] do
    for index in ← getBeaconCommittee shufflingSource slot (← u64 i "CommitteeIndex") do
      participants := participants.insert index.toNat
  pure participants

/-- `get_pulled_up_head_state(store)`: the head's post-state, advanced to the start of the
current store epoch when it is from an earlier epoch. -/
def getPulledUpHeadState (v : FcrView P) : M (BeaconState P) := do
  let headState ← lookup v.store.block_states v.head.root
    "get_pulled_up_head_state: store.block_states[head]"
  let currentStoreEpoch ← getCurrentStoreEpoch v.ctx.cfg v.store
  if (← getCurrentEpoch headState) < currentStoreEpoch then
    v.tr.processSlots v.ctx headState (← computeStartSlotAtEpoch P currentStoreEpoch)
  else pure headState

/-- `get_previous_balance_source(fcr_store)`. -/
def getPreviousBalanceSource (fcr : FastConfirmationStore P) : M (BeaconState P) :=
  lookup fcr.store.checkpoint_states fcr.previous_epoch_observed_justified_checkpoint
    "get_previous_balance_source: store.checkpoint_states"

/-- `get_current_balance_source(fcr_store)`. -/
def getCurrentBalanceSource (fcr : FastConfirmationStore P) : M (BeaconState P) :=
  lookup fcr.store.checkpoint_states fcr.current_epoch_observed_justified_checkpoint
    "get_current_balance_source: store.checkpoint_states"

/-! ## LMD-GHOST helpers -/

/-- The union of `get_slot_committee` over `range(start_slot, end_slot + 1)`. -/
def committeesBetweenSlots (v : FcrView P) (startSlot endSlot : Slot) (site : String) :
    M (Std.TreeSet Nat compare) := do
  let stop ← endSlot.add? U64.one site
  let mut out : Std.TreeSet Nat compare := ∅
  for slot in [startSlot.toNat:stop.toNat] do
    out := out.insertMany (← getSlotCommittee v (← u64 slot "Slot"))
  pure out

/-- `get_node_support_between_slots(store, balance_source, node, start_slot, end_slot)`: the
`balance_source` effective balances of the unslashed members, active at its epoch, of the
committees of the slots in the range whose non-equivocating latest message supports `node`
itself. -/
def getNodeSupportBetweenSlots (v : FcrView P) (balanceSource : BeaconState P)
    (node : ForkChoiceNode) (startSlot endSlot : Slot) : M Gwei := do
  let site := "get_node_support_between_slots"
  let participants ← committeesBetweenSlots v startSlot endSlot site
  -- Keep validators that were active at the balance_source epoch, also filter out slashed ones
  let epoch ← getCurrentEpoch balanceSource
  let mut unslashedAndActive : Array Nat := #[]
  for index in participants do
    let val ← balanceSource.validators.get index s!"{site}: balance_source.validators[index]"
    if !val.slashed && isActiveValidator val epoch then
      unslashedAndActive := unslashedAndActive.push index
  let mut total := U64.zero
  for index in unslashedAndActive do
    -- Check that validator has voted in the support of the node and has not been slashed
    match v.store.latest_messages.get? index with
    | none => pure ()
    | some message =>
      if (← getSupportedNode v.store message) == node && !v.store.equivocating_indices.contains index then
        let val ← balanceSource.validators.get index s!"{site}: balance_source.validators[index]"
        total ← total.add? val.effective_balance site
  pure total

/-- `get_equivocation_score(store, balance_source, start_slot, end_slot)`: the `balance_source`
effective balances of the equivocating committee members of the range active at its epoch. -/
def getEquivocationScore (v : FcrView P) (balanceSource : BeaconState P)
    (startSlot endSlot : Slot) : M Gwei := do
  let site := "get_equivocation_score"
  let committeeIndices ← committeesBetweenSlots v startSlot endSlot site
  let epoch ← getCurrentEpoch balanceSource
  let mut activeEquivocating : Array Nat := #[]
  for index in committeeIndices do
    if v.store.equivocating_indices.contains index then
      let val ← balanceSource.validators.get index s!"{site}: balance_source.validators[index]"
      if isActiveValidator val epoch then activeEquivocating := activeEquivocating.push index
  let mut total := U64.zero
  for index in activeEquivocating do
    let val ← balanceSource.validators.get index s!"{site}: balance_source.validators[index]"
    total ← total.add? val.effective_balance site
  pure total

/-- `compute_adversarial_weight(store, balance_source, start_slot, end_slot)`: the
`CONFIRMATION_BYZANTINE_THRESHOLD` share of the range's estimated committee weight, less the
weight that has already equivocated. -/
def computeAdversarialWeight (v : FcrView P) (balanceSource : BeaconState P)
    (startSlot endSlot : Slot) : M Gwei := do
  let site := "compute_adversarial_weight"
  let totalActiveBalance ← getTotalActiveBalance balanceSource
  let maximumWeight ← estimateCommitteeWeightBetweenSlots P totalActiveBalance startSlot endSlot
  let maxAdversarialWeight ← (← maximumWeight.div? (← c64 100) site).mul?
    (← confirmationByzantineThreshold v.ctx.cfg) site
  -- Discount total weight of equivocating validators
  let equivocationScore ← getEquivocationScore v balanceSource startSlot endSlot
  if maxAdversarialWeight > equivocationScore then
    maxAdversarialWeight.sub? equivocationScore site
  else pure U64.zero

/-- `get_adversarial_weight(store, balance_source, block_root)`: from the block's slot, or from
the first slot of its epoch when it opens a new epoch, to the slot before the current one. -/
def getAdversarialWeight (v : FcrView P) (balanceSource : BeaconState P) (blockRoot : Root) :
    M Gwei := do
  let site := "get_adversarial_weight"
  let currentSlot ← getCurrentSlot v.ctx.cfg v.store
  let block ← lookup v.store.blocks blockRoot s!"{site}: store.blocks[block_root]"
  let blockEpoch ← getBlockEpoch v.store blockRoot
  if blockEpoch > (← getBlockEpoch v.store block.parent_root) then
    -- Use the first epoch slot as the start slot when crossing epoch boundary
    let startSlot ← computeStartSlotAtEpoch P blockEpoch
    computeAdversarialWeight v balanceSource startSlot (← currentSlot.sub? U64.one site)
  else
    computeAdversarialWeight v balanceSource block.slot (← currentSlot.sub? U64.one site)

/-- `compute_empty_slot_support_discount(store, balance_source, block_root)`: the support the
parent received from the committees of the empty slots before the block, less their adversarial
weight. -/
def computeEmptySlotSupportDiscount (v : FcrView P) (balanceSource : BeaconState P)
    (blockRoot : Root) : M Gwei := do
  let site := "compute_empty_slot_support_discount"
  let block ← lookup v.store.blocks blockRoot s!"{site}: store.blocks[block_root]"
  let parentBlock ← lookup v.store.blocks block.parent_root s!"{site}: store.blocks[parent_root]"
  -- No empty slot
  if (← parentBlock.slot.add? U64.one site) == block.slot then return U64.zero
  -- Discount votes supporting the parent block if they are from the committees of empty slots
  let parentNode ← getAncestor v.store (getNodeForRoot blockRoot) parentBlock.slot
  let firstEmpty ← parentBlock.slot.add? U64.one site
  let lastEmpty ← block.slot.sub? U64.one site
  let parentSupportInEmptySlots ←
    getNodeSupportBetweenSlots v balanceSource parentNode firstEmpty lastEmpty
  -- Adversarial weight is not discounted
  let adversarialWeight ← computeAdversarialWeight v balanceSource firstEmpty lastEmpty
  if parentSupportInEmptySlots > adversarialWeight then
    parentSupportInEmptySlots.sub? adversarialWeight site
  else pure U64.zero

/-- `get_support_discount(store, balance_source, block_root)`. -/
def getSupportDiscount (v : FcrView P) (balanceSource : BeaconState P) (blockRoot : Root) :
    M Gwei :=
  computeEmptySlotSupportDiscount v balanceSource blockRoot

/-- `compute_safety_threshold(store, block_root, balance_source)`:
`(maximum_support + proposer_score - support_discount) // 2 + adversarial_weight`, computed as
`(maximum_support + proposer_score + 2 * adversarial_weight - support_discount) // 2` under the
spec's underflow guard. -/
def computeSafetyThreshold (v : FcrView P) (blockRoot : Root) (balanceSource : BeaconState P) :
    M Gwei := do
  let site := "compute_safety_threshold"
  let currentSlot ← getCurrentSlot v.ctx.cfg v.store
  let block ← lookup v.store.blocks blockRoot s!"{site}: store.blocks[block_root]"
  let parentBlock ← lookup v.store.blocks block.parent_root s!"{site}: store.blocks[parent_root]"
  let totalActiveBalance ← getTotalActiveBalance balanceSource
  let proposerScore ← computeProposerScore v.ctx.cfg balanceSource
  let maximumSupport ← estimateCommitteeWeightBetweenSlots P totalActiveBalance
    (← parentBlock.slot.add? U64.one site) (← currentSlot.sub? U64.one site)
  let supportDiscount ← getSupportDiscount v balanceSource blockRoot
  let adversarialWeight ← getAdversarialWeight v balanceSource blockRoot
  let bound ← (← maximumSupport.add? proposerScore site).add?
    (← (← c64 2).mul? adversarialWeight site) site
  if supportDiscount < bound then
    (← bound.sub? supportDiscount site).div? (← c64 2) site
  else pure U64.zero

/-- `is_one_confirmed(store, balance_source, block_root)`: the block's attestation score exceeds
its safety threshold; `False` for a block whose payload is not `VALID` (see the module note). -/
def isOneConfirmed (v : FcrView P) (balanceSource : BeaconState P) (blockRoot : Root) :
    M Bool := do
  if !v.isValid blockRoot then return false
  let support ← getAttestationScore v.store (getNodeForRoot blockRoot) balanceSource
  let safetyThreshold ← computeSafetyThreshold v blockRoot balanceSource
  pure (support > safetyThreshold)

/-- `is_confirmed_chain_safe(fcr_store, confirmed_root)`: every block of the confirmed chain from
`current_epoch_observed_justified_checkpoint` (or from the first block of the previous epoch) is
LMD-GHOST safe under the previous balance source. -/
def isConfirmedChainSafe (fcr : FastConfirmationStore P) (v : FcrView P)
    (confirmedRoot : Root) : M Bool := do
  let site := "is_confirmed_chain_safe"
  let store := v.store
  let observed := fcr.current_epoch_observed_justified_checkpoint
  -- Check if the confirmed_root has current_epoch_observed_justified_checkpoint in its chain
  if observed != (← getCheckpointForBlock store confirmedRoot observed.epoch) then return false
  let currentEpoch ← getCurrentStoreEpoch v.ctx.cfg store
  let startRootExclusive ←
    if (← observed.epoch.add? U64.one site) ≥ currentEpoch then
      -- Exclude the justified checkpoint block if it is from the previous epoch
      pure observed.root
    else do
      -- Limit reconfirmation to the first block of the previous epoch
      let ancestorAtPreviousEpochStart := (← getAncestor store (getNodeForRoot confirmedRoot)
        (← computeStartSlotAtEpoch P (← currentEpoch.sub? U64.one site))).root
      if (← (← getBlockEpoch store ancestorAtPreviousEpochStart).add? U64.one site) == currentEpoch
      then
        -- The parent of the first block of the previous epoch
        pure (← lookup store.blocks ancestorAtPreviousEpochStart s!"{site}: store.blocks").parent_root
      else
        -- The last block of the epoch before the previous one
        pure ancestorAtPreviousEpochStart
  -- Run is_one_confirmed for each block in the confirmed chain with the previous epoch balance
  -- source (`all` stops at the first `False`)
  for root in ← getAncestorRoots store confirmedRoot startRootExclusive do
    if !(← isOneConfirmed v (← getPreviousBalanceSource fcr) root) then return false
  return true

/-! ## FFG helpers -/

/-- `get_current_target_score(store)`: the pulled-up head state's effective balances of its
unslashed active validators whose non-equivocating latest message has the current target as its
checkpoint. -/
def getCurrentTargetScore (v : FcrView P) : M Gwei := do
  let site := "get_current_target_score"
  let target ← getCurrentTarget v
  let state ← getPulledUpHeadState v
  let mut total := U64.zero
  for index in ← unslashedActiveIndices state site do
    match v.store.latest_messages.get? index.toNat with
    | none => pure ()
    | some message =>
      if !v.store.equivocating_indices.contains index.toNat then
        if target == (← getCheckpointForBlock v.store message.root (← getLatestMessageEpoch P message))
        then
          let val ← state.validators.get index.toNat s!"{site}: state.validators[index]"
          total ← total.add? val.effective_balance site
  pure total

/-- `compute_honest_ffg_support_for_current_target(store)`. -/
def computeHonestFfgSupportForCurrentTarget (v : FcrView P) : M Gwei := do
  let site := "compute_honest_ffg_support_for_current_target"
  let currentSlot ← getCurrentSlot v.ctx.cfg v.store
  let currentEpoch ← computeEpochAtSlot P currentSlot
  let balanceSource ← getPulledUpHeadState v
  let totalActiveBalance ← getTotalActiveBalance balanceSource
  -- Compute FFG support for the target
  let ffgSupportForCheckpoint ← getCurrentTargetScore v
  -- Compute the total FFG weight up to, but excluding, the current slot
  let epochStart ← computeStartSlotAtEpoch P currentEpoch
  let previousSlot ← currentSlot.sub? U64.one site
  let ffgWeightTillNow ← estimateCommitteeWeightBetweenSlots P totalActiveBalance epochStart
    previousSlot
  -- Compute remaining honest FFG weight
  let remainingFfgWeight ← totalActiveBalance.sub? ffgWeightTillNow site
  let remainingHonestFfgWeight ← (← remainingFfgWeight.div? (← c64 100) site).mul?
    (← (← c64 100).sub? (← confirmationByzantineThreshold v.ctx.cfg) site) site
  -- Compute potential adversarial weight
  let adversarialWeight ← computeAdversarialWeight v balanceSource epochStart previousSlot
  -- Compute min honest FFG support
  let minHonestFfgSupport ← saturatingSubU64 ffgSupportForCheckpoint adversarialWeight site
  minHonestFfgSupport.add? remainingHonestFfgWeight site

/-- `will_no_conflicting_checkpoint_be_justified(store)`. -/
def willNoConflictingCheckpointBeJustified (v : FcrView P) : M Bool := do
  let site := "will_no_conflicting_checkpoint_be_justified"
  -- If the target is unrealized justified then no conflicting checkpoint can be justified
  if (← getCurrentTarget v) == v.store.unrealized_justified_checkpoint then return true
  let state ← getPulledUpHeadState v
  let totalActiveBalance ← getTotalActiveBalance state
  let honestFfgSupport ← computeHonestFfgSupportForCurrentTarget v
  pure ((← (← c64 3).mul? honestFfgSupport site) > (← (← c64 1).mul? totalActiveBalance site))

/-- `will_current_target_be_justified(store)`. -/
def willCurrentTargetBeJustified (v : FcrView P) : M Bool := do
  let site := "will_current_target_be_justified"
  let state ← getPulledUpHeadState v
  let totalActiveBalance ← getTotalActiveBalance state
  let honestFfgSupport ← computeHonestFfgSupportForCurrentTarget v
  pure ((← (← c64 3).mul? honestFfgSupport site) ≥ (← (← c64 2).mul? totalActiveBalance site))

/-! ## The algorithm -/

/-- `update_fast_confirmation_variables(fcr_store)`, with `get_head(store)` given as `v.head`. -/
def updateFastConfirmationVariables (fcr : FastConfirmationStore P) (v : FcrView P) :
    M (FastConfirmationStore P) := do
  let site := "update_fast_confirmation_variables"
  let currentSlot ← getCurrentSlot v.ctx.cfg v.store
  -- Update prev and curr slot head
  let fcr := { fcr with previous_slot_head := fcr.current_slot_head, current_slot_head := v.head.root }
  -- Update greatest unrealized justified checkpoint at the last slot of an epoch
  let fcr := if ← isStartSlotAtEpoch P (← currentSlot.add? U64.one site) then
      { fcr with previous_epoch_greatest_unrealized_checkpoint := v.store.unrealized_justified_checkpoint }
    else fcr
  -- Update observed justified checkpoints at the start of an epoch
  if ← isStartSlotAtEpoch P currentSlot then
    pure { fcr with
      previous_epoch_observed_justified_checkpoint := fcr.current_epoch_observed_justified_checkpoint
      current_epoch_observed_justified_checkpoint := fcr.previous_epoch_greatest_unrealized_checkpoint }
  else pure fcr

/-- `find_latest_confirmed_descendant(fcr_store, latest_confirmed_root)`. The Python's `and`/`or`
are evaluated left to right with short circuit, so each read happens exactly when the spec makes
it. -/
def findLatestConfirmedDescendant (fcr : FastConfirmationStore P) (v : FcrView P)
    (latestConfirmedRoot : Root) : M Root := do
  let site := "find_latest_confirmed_descendant"
  let store := v.store
  let head := v.head.root
  let currentSlot ← getCurrentSlot v.ctx.cfg store
  let currentEpoch ← getCurrentStoreEpoch v.ctx.cfg store
  let unrealizedOk (root : Root) : M Bool := do
    let j ← lookup store.unrealized_justifications root s!"{site}: store.unrealized_justifications"
    pure ((← j.epoch.add? U64.one site) ≥ currentEpoch)
  let mut confirmedRoot := latestConfirmedRoot
  let advanceFromPrevious ←
    if (← (← getBlockEpoch store confirmedRoot).add? U64.one site) == currentEpoch then
      if (← (← getVotingSource v.ctx.cfg store fcr.previous_slot_head).epoch.add? (← c64 2) site)
          ≥ currentEpoch then
        if ← isStartSlotAtEpoch P currentSlot then pure true
        else if ← willNoConflictingCheckpointBeJustified v then
          if ← unrealizedOk fcr.previous_slot_head then pure true else unrealizedOk head
        else pure false
      else pure false
    else pure false
  if advanceFromPrevious then
    -- Get suffix of the canonical chain
    let canonicalRoots ← getAncestorRoots store head confirmedRoot
    -- Starting with the child of the latest_confirmed_root move towards the head in attempt to
    -- advance the confirmed block and stop when the first unconfirmed descendant is encountered
    for blockRoot in canonicalRoots do
      let blockEpoch ← getBlockEpoch store blockRoot
      -- If the current epoch is reached, exit the loop
      if blockEpoch == currentEpoch then break
      -- The algorithm can only rely on the previous head if it is a descendant of the block that
      -- is attempted to be confirmed
      if !(← isAncestor store (getNodeForRoot fcr.previous_slot_head) (getNodeForRoot blockRoot))
      then break
      if !(← isOneConfirmed v (← getCurrentBalanceSource fcr) blockRoot) then break
      confirmedRoot := blockRoot
  let advanceInCurrent ←
    if ← isStartSlotAtEpoch P currentSlot then pure true else unrealizedOk head
  if advanceInCurrent then
    -- Get suffix of the canonical chain
    let canonicalRoots ← getAncestorRoots store head confirmedRoot
    let mut tentativeConfirmedRoot := confirmedRoot
    for blockRoot in canonicalRoots do
      let blockEpoch ← getBlockEpoch store blockRoot
      let tentativeConfirmedEpoch ← getBlockEpoch store tentativeConfirmedRoot
      -- The following condition can only be true the first time the algorithm advances to a
      -- block from the current epoch
      if blockEpoch > tentativeConfirmedEpoch then
        -- To confirm blocks from the current epoch ensure that current epoch target will be
        -- justified
        if !(← willCurrentTargetBeJustified v) then break
      if !(← isOneConfirmed v (← getCurrentBalanceSource fcr) blockRoot) then break
      tentativeConfirmedRoot := blockRoot
    -- The tentative_confirmed_root can only be confirmed if it is for sure not going to be
    -- reorged out in either the current or next epoch.
    let confirm ←
      if (← getBlockEpoch store tentativeConfirmedRoot) == currentEpoch then pure true
      else if (← (← getVotingSource v.ctx.cfg store tentativeConfirmedRoot).epoch.add? (← c64 2) site)
          ≥ currentEpoch then
        if ← isStartSlotAtEpoch P currentSlot then pure true
        else willNoConflictingCheckpointBeJustified v
      else pure false
    if confirm then confirmedRoot := tentativeConfirmedRoot
  pure confirmedRoot

/-- `get_latest_confirmed(fcr_store)`. -/
def getLatestConfirmed (fcr : FastConfirmationStore P) (v : FcrView P) : M Root := do
  let site := "get_latest_confirmed"
  let store := v.store
  let mut confirmedRoot := fcr.confirmed_root
  let currentEpoch ← getCurrentStoreEpoch v.ctx.cfg store
  let currentSlot ← getCurrentSlot v.ctx.cfg store
  let head := v.head.root
  -- Revert to finalized block if the latest confirmed block's epoch is older than the previous
  -- epoch, if it does not belong to the canonical chain, or if the confirmed chain from the
  -- current epoch observed justified checkpoint cannot be re-confirmed at the start of the epoch
  let revert ←
    if (← (← getBlockEpoch store confirmedRoot).add? U64.one site) < currentEpoch then pure true
    else if !(← isAncestor store (getNodeForRoot head) (getNodeForRoot confirmedRoot)) then pure true
    else if ← isStartSlotAtEpoch P currentSlot then
      pure !(← isConfirmedChainSafe fcr v confirmedRoot)
    else pure false
  if revert then confirmedRoot := store.finalized_checkpoint.root
  -- Restart the confirmation chain if it is the start of the current epoch, the observed
  -- justified block is from the previous epoch, it equals the head's unrealized justification,
  -- and the confirmed block is older than it
  let observed := fcr.current_epoch_observed_justified_checkpoint
  let isEpochStart ← isStartSlotAtEpoch P currentSlot
  let observedJustifiedBlockSlot ← getBlockSlot store observed.root
  let isObservedJustifiedBlockEpochOk :=
    (← (← computeEpochAtSlot P observedJustifiedBlockSlot).add? U64.one site) == currentEpoch
  let isHeadUnrealizedJustifiedOk :=
    observed == (← lookup store.unrealized_justifications head s!"{site}: store.unrealized_justifications")
  let isConfirmedBlockStale := (← getBlockSlot store confirmedRoot) < observedJustifiedBlockSlot
  if isEpochStart && isObservedJustifiedBlockEpochOk && isHeadUnrealizedJustifiedOk &&
      isConfirmedBlockStale then
    confirmedRoot := observed.root
  -- Attempt to further advance the latest confirmed block
  if (← (← getBlockEpoch store confirmedRoot).add? U64.one site) ≥ currentEpoch then
    findLatestConfirmedDescendant fcr v confirmedRoot
  else pure confirmedRoot

/-- `block_should_be_finalized(store, block_root)`. -/
def blockShouldBeFinalized (cfg : Config) (store : Store P) (blockRoot : Root) : M Bool := do
  let site := "block_should_be_finalized"
  let blockSlot ← getBlockSlot store blockRoot
  let nextCheckpointEpoch ← computeEpochAtSlot P
    (← (← blockSlot.add? (← c64 P.SLOTS_PER_EPOCH) site).sub? U64.one site)
  let earliestFinalitySlot ← computeStartSlotAtEpoch P (← nextCheckpointEpoch.add? (← c64 2) site)
  pure (earliestFinalitySlot ≤ (← getCurrentSlot cfg store))

/-- `get_restart_resilient_confirmed_root(fcr_store)`, with the implementation-dependent
`get_root_confirmed_before_restart()` given as `rootBeforeRestart`. Optional ("MAY"); no vector
exercises it. -/
def getRestartResilientConfirmedRoot (v : FcrView P) (fcr : FastConfirmationStore P)
    (rootBeforeRestart : Root) : M Root := do
  let store := v.store
  let rootBeforeRestartSlot ← getBlockSlot store rootBeforeRestart
  -- Recently confirmed block has advanced beyond the block confirmed before the restart
  if rootBeforeRestartSlot ≤ (← getBlockSlot store fcr.confirmed_root) then
    return fcr.confirmed_root
  -- If the block is old enough it either has been finalized already or finality has been
  -- delayed which makes block confirmed before restart unreliable
  if ← blockShouldBeFinalized v.ctx.cfg store rootBeforeRestart then return fcr.confirmed_root
  -- If a block confirmed before the restart is not canonical, return the recently confirmed block
  if !(← isAncestor store v.head (getNodeForRoot rootBeforeRestart)) then return fcr.confirmed_root
  pure rootBeforeRestart

/-! ## Handler -/

/-- `on_fast_confirmation(fcr_store)`: `update_fast_confirmation_variables`, then
`fcr_store.confirmed_root = get_latest_confirmed(fcr_store)`. `get_head(store)` is computed once,
as the first read `update_fast_confirmation_variables` makes, and shared (see the module note). -/
def onFastConfirmation (tr : Transition P) (ctx : Ctx) (isValid : Root → Bool)
    (fcr : FastConfirmationStore P) : M (FastConfirmationStore P) := do
  let head ← getHead ctx.cfg fcr.store
  let v : FcrView P := { ctx, store := fcr.store, head, isValid, tr }
  let fcr ← updateFastConfirmationVariables fcr v
  pure { fcr with confirmed_root := ← getLatestConfirmed fcr v }

/-- `get_safe_execution_block_hash(fcr_store)` (Gloas): only the parent payload of a confirmed
beacon block is safe, so the confirmed block's bid's `parent_block_hash`. -/
def getSafeExecutionBlockHash (fcr : FastConfirmationStore P) : M Hash32 := do
  let safeBlock ← lookup fcr.store.blocks fcr.confirmed_root
    "get_safe_execution_block_hash: store.blocks[confirmed_root]"
  pure safeBlock.body.signed_execution_payload_bid.message.parent_block_hash

end JauneConsensus.Gloas
