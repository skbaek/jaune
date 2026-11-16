import JauneConsensus.GloasUpgrade
import JauneConsensus.GloasEpoch
import JauneConsensus.StateTransition

/-!
# The Gloas state transition (goal `eip8282-gloas-cross-layer-v1`, U5)

`state_transition`, `verify_block_signature` and `process_slots` (`specs/phase0/beacon-chain.md`,
unchanged in text through Gloas) and the Gloas `process_slot` (`specs/gloas/beacon-chain.md:1605`,
which also clears the next slot's `execution_payload_availability` bit), over
`JauneConsensus.Gloas.BeaconState` and `SignedBeaconBlock`, with U3's `processEpoch`
(`GloasEpoch.lean`) and U4's `processBlock` (`GloasBlock.lean`).

**Entry points.**

* `Gloas.processSlots ctx state slot` and `Gloas.stateTransition ctx state signedBlock
  validateResult`: the Gloas `process_slots` and `state_transition`; the BLS switch is
  `ctx.blsActive`. `processSlotsWith`/`stateTransitionWith` take `process_epoch` and
  `process_block` as arguments (as `Transition.lean` does for the earlier forks).
* `Gloas.upgradeToGloas ctx pre` (`GloasUpgrade.lean`): `upgrade_to_gloas`.
* `Gloas.crossFromFulu ctx pre`: the irregular crossing at `ctx.cfg.GLOAS_FORK_EPOCH` as the
  generators drive it (`do_fork`, `transition_until_fork` in
  `eth2spec/test/helpers/fork_transition.py`): the Fulu `process_slots` to the fork epoch's first
  slot (when the state is not there already), then `upgrade_to_gloas`.
* `Gloas.processBlockAtSlot ctx state signedBlock`: `state_transition` with no slot to advance
  (the block's slot is the state's), which is how the generators apply the block at the fork slot
  right after the upgrade: the signature and state-root checks apply.

Execution payload envelopes are not part of `state_transition` in Gloas: a block's parent
payload is applied by `process_parent_execution_payload` inside `process_block`.
-/

namespace JauneConsensus.Gloas

open Jaune

variable {P : Preset}

/-- `process_slot(state)` (Gloas, beacon-chain.md:1605): cache the state root and the block root,
then `state.execution_payload_availability[(state.slot + 1) % SLOTS_PER_HISTORICAL_ROOT] =
False`. -/
def processSlot (state : BeaconState P) : M (BeaconState P) := do
  let slotsPerHistoricalRoot ← u64 P.SLOTS_PER_HISTORICAL_ROOT "SLOTS_PER_HISTORICAL_ROOT"
  let i := (← state.slot.mod? slotsPerHistoricalRoot
    "process_slot: slot % SLOTS_PER_HISTORICAL_ROOT").toNat
  -- Cache state root
  let previousStateRoot : Root := Ssz.hashTreeRoot state
  let state := { state with
    state_roots := ← state.state_roots.set i previousStateRoot "process_slot: state_roots" }
  -- Cache latest block header state root
  let state :=
    if B256.beq state.latest_block_header.state_root (0 : B256) then
      { state with latest_block_header :=
          { state.latest_block_header with state_root := previousStateRoot } }
    else state
  -- Cache block root
  let previousBlockRoot : Root := Ssz.hashTreeRoot state.latest_block_header
  let state := { state with
    block_roots := ← state.block_roots.set i previousBlockRoot "process_slot: block_roots" }
  -- [New in Gloas:EIP7732] Unset the next payload availability
  let nextSlotIndex := (← (← state.slot.add? U64.one "process_slot: state.slot + 1").mod?
    slotsPerHistoricalRoot "process_slot: (state.slot + 1) % SLOTS_PER_HISTORICAL_ROOT").toNat
  pure { state with
    execution_payload_availability := ← state.execution_payload_availability.set nextSlotIndex
      false "process_slot: execution_payload_availability" }

/-- `process_slots(state, slot)`, with `process_epoch` given as `processEpoch`. The loop runs
`slot - state.slot` times: each iteration advances `state.slot` by one. -/
def processSlotsWith (processEpoch : BeaconState P → M (BeaconState P))
    (state : BeaconState P) (slot : Slot) : M (BeaconState P) := do
  require (decide (state.slot < slot)) "process_slots: state.slot < slot"
  let slotsPerEpoch ← u64 P.SLOTS_PER_EPOCH "SLOTS_PER_EPOCH"
  let mut state := state
  for _ in [0:slot.toNat - state.slot.toNat] do
    state ← processSlot state
    -- Process epoch on the start slot of the next epoch
    let next ← state.slot.add? U64.one "process_slots: state.slot + 1"
    if (← next.mod? slotsPerEpoch "process_slots: (state.slot + 1) % SLOTS_PER_EPOCH").toNat == 0 then
      state ← processEpoch state
    state := { state with slot := next }
  pure state

/-- `process_slots(state, slot)` with the Gloas `process_epoch`. -/
def processSlots (ctx : Ctx) (state : BeaconState P) (slot : Slot) : M (BeaconState P) :=
  processSlotsWith (processEpoch ctx) state slot

/-- `verify_block_signature(state, signed_block)` under the BLS switch `bls`. -/
def verifyBlockSignature (bls : Bool) (state : BeaconState P) (signedBlock : SignedBeaconBlock P) :
    M Bool := do
  let proposer ← state.validators.get signedBlock.message.proposer_index.toNat
    "verify_block_signature: state.validators[proposer_index]"
  let signingRoot := computeSigningRoot signedBlock.message (← getDomain state DOMAIN_BEACON_PROPOSER)
  pure (blsVerify bls proposer.pubkey signingRoot signedBlock.signature)

/-- The tail of `state_transition` after `process_slots`: verify the signature, process the
block, verify the state root (the two checks under `validate_result`). -/
def applySignedBlockWith (processBlock : BeaconState P → BeaconBlock P → M (BeaconState P))
    (bls : Bool) (state : BeaconState P) (signedBlock : SignedBeaconBlock P)
    (validateResult : Bool := true) : M (BeaconState P) := do
  let block := signedBlock.message
  -- Verify signature
  if validateResult then
    require (← verifyBlockSignature bls state signedBlock) "state_transition: verify_block_signature"
  -- Process block
  let state ← processBlock state block
  -- Verify state root
  if validateResult then
    require (B256.beq block.state_root (Ssz.hashTreeRoot state)) "state_transition: block.state_root"
  pure state

/-- `state_transition(state, signed_block, validate_result)`, with `process_epoch` and
`process_block` given. -/
def stateTransitionWith (processEpoch : BeaconState P → M (BeaconState P))
    (processBlock : BeaconState P → BeaconBlock P → M (BeaconState P))
    (bls : Bool) (state : BeaconState P) (signedBlock : SignedBeaconBlock P)
    (validateResult : Bool := true) : M (BeaconState P) := do
  -- Process slots (including those with no blocks) since block
  let state ← processSlotsWith processEpoch state signedBlock.message.slot
  applySignedBlockWith processBlock bls state signedBlock validateResult

/-- `state_transition(state, signed_block, validate_result)` (Gloas); the BLS switch is
`ctx.blsActive`. -/
def stateTransition (ctx : Ctx) (state : BeaconState P) (signedBlock : SignedBeaconBlock P)
    (validateResult : Bool := true) : M (BeaconState P) :=
  stateTransitionWith (processEpoch ctx) (processBlock ctx) ctx.blsActive state signedBlock
    validateResult

/-- `state_transition` factors as `process_slots` to the block's slot, then the signature check,
`process_block` and the state-root check (`applySignedBlockWith`): a caller can run the slots
once and read the post-slots state. -/
theorem stateTransition_eq (ctx : Ctx) (state : BeaconState P) (signedBlock : SignedBeaconBlock P)
    (validateResult : Bool) :
    stateTransition ctx state signedBlock validateResult =
      (do
        let state ← processSlots ctx state signedBlock.message.slot
        applySignedBlockWith (processBlock ctx) ctx.blsActive state signedBlock validateResult) :=
  rfl

/-- `state_transition` for a block at the state's own slot, with no `process_slots` step: the
generators' block at the fork slot (`_state_transition_and_sign_block_at_slot` after `do_fork`).
The signature and state-root checks apply. -/
def processBlockAtSlot (ctx : Ctx) (state : BeaconState P) (signedBlock : SignedBeaconBlock P) :
    M (BeaconState P) := do
  require (signedBlock.message.slot == state.slot) "process_block_at_slot: block.slot == state.slot"
  applySignedBlockWith (processBlock ctx) ctx.blsActive state signedBlock

/-! ## The Fulu → Gloas crossing -/

/-- The irregular state change at `GLOAS_FORK_EPOCH` (`ctx.cfg.GLOAS_FORK_EPOCH`): the Fulu
`process_slots` to `compute_start_slot_at_epoch(GLOAS_FORK_EPOCH)` when the state is before it,
then `upgrade_to_gloas`. The state must then be at the fork epoch's first slot (fork.md,
"Upgrading the state"). The same configuration carries on to the Gloas blocks, where
`get_ptc` reads `GLOAS_FORK_EPOCH`. -/
def crossFromFulu (ctx : Ctx) (pre : JauneConsensus.BeaconState P .fulu) : M (BeaconState P) := do
  let forkSlot ← computeStartSlotAtEpoch P (← U64.ofNat? ctx.cfg.GLOAS_FORK_EPOCH "GLOAS_FORK_EPOCH")
  let pre ← if pre.slot < forkSlot then JauneConsensus.processSlots ctx pre forkSlot else pure pre
  require (pre.slot == forkSlot)
    "upgrade_to_gloas: state.slot == compute_start_slot_at_epoch(GLOAS_FORK_EPOCH)"
  upgradeToGloas ctx pre

end JauneConsensus.Gloas
