import JauneConsensus.Signing

/-!
# The beacon-chain state transition function

`specs/phase0/beacon-chain.md`, "Beacon chain state transition function": `state_transition`,
`verify_block_signature`, `process_slots` and `process_slot`, unchanged in text through Fulu;
what changes per fork is the `process_block` and `process_epoch` they call, which branch on the
fork inside their own definitions.

`processSlotsWith` and `stateTransitionWith` take the epoch and block processing functions as
arguments, so the composition is one definition for every fork; `processSlots` and
`stateTransition` in `JauneConsensus/StateTransition.lean` instantiate them with the spec's
`process_epoch` and `process_block` (kept apart so this composition does not depend on the
processing modules).
-/

namespace JauneConsensus

open Jaune

variable {P : Preset} {f : CFork}

/-- `process_slot(state)`. -/
def processSlot (state : BeaconState P f) : M (BeaconState P f) := do
  let slotsPerHistoricalRoot ← u64 P.SLOTS_PER_HISTORICAL_ROOT "SLOTS_PER_HISTORICAL_ROOT"
  let i := (← state.slot.mod? slotsPerHistoricalRoot "process_slot: slot % SLOTS_PER_HISTORICAL_ROOT").toNat
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
  pure { state with
    block_roots := ← state.block_roots.set i previousBlockRoot "process_slot: block_roots" }

/-- `process_slots(state, slot)`, with `process_epoch` given as `processEpoch`. The loop runs
`slot - state.slot` times: each iteration advances `state.slot` by one. -/
def processSlotsWith (processEpoch : BeaconState P f → M (BeaconState P f))
    (state : BeaconState P f) (slot : Slot) : M (BeaconState P f) := do
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

/-- `verify_block_signature(state, signed_block)` under the BLS switch `bls`. -/
def verifyBlockSignature (bls : Bool) (state : BeaconState P f) (signedBlock : SignedBeaconBlock P f) :
    M Bool := do
  let proposer ← state.validators.get signedBlock.message.proposer_index.toNat
    "verify_block_signature: state.validators[proposer_index]"
  let signingRoot := computeSigningRoot signedBlock.message (← getDomain state DOMAIN_BEACON_PROPOSER)
  pure (blsVerify bls proposer.pubkey signingRoot signedBlock.signature)

/-- `state_transition(state, signed_block, validate_result)`, with `process_epoch` and
`process_block` given. -/
def stateTransitionWith (processEpoch : BeaconState P f → M (BeaconState P f))
    (processBlock : BeaconState P f → BeaconBlock P f → M (BeaconState P f))
    (bls : Bool) (state : BeaconState P f) (signedBlock : SignedBeaconBlock P f)
    (validateResult : Bool := true) : M (BeaconState P f) := do
  let block := signedBlock.message
  -- Process slots (including those with no blocks) since block
  let state ← processSlotsWith processEpoch state block.slot
  -- Verify signature
  if validateResult then
    require (← verifyBlockSignature bls state signedBlock) "state_transition: verify_block_signature"
  -- Process block
  let state ← processBlock state block
  -- Verify state root
  if validateResult then
    require (B256.beq block.state_root (Ssz.hashTreeRoot state)) "state_transition: block.state_root"
  pure state

end JauneConsensus
