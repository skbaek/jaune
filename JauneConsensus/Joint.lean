import JauneConsensus.Engine
import JauneConsensus.StateTransition

/-!
# The joint execution–consensus step

One step of a chain the joint protocol accepts: the consensus `state_transition` for a signed
beacon block, with the execution engine's verdict given by `engineVerdict` (Jaune's execution
semantics) in place of the mocked `Ctx.executionValid`, and the execution chain advanced by the
payload's block (goal `eip7002-cross-layer-v1`, O1).

The step is defined for Electra and Fulu, the forks the consensus model implements, and for
the Electra→Fulu crossing, which it makes exactly as the `transition` vectors' harness does
(`Harness/StateTransition.lean`, `transitionCase`): the pre-fork `process_slots` up to the first
slot of `FULU_FORK_EPOCH`, `upgrade_to_fulu`, then the block, without a further `process_slots`
when the block is at that slot. Every other fork pair, Gloas in particular, is refused.
-/

namespace JauneConsensus

open Jaune

variable {P : Preset}

/-- A joint state: the beacon state at its consensus fork, and Jaune's execution chain. -/
structure JointState (P : Preset) where
  fork : CFork
  beacon : BeaconState P fork
  exec : Jaune.BlockChain

/-- A signed beacon block of whichever consensus fork its slot is in. -/
abbrev AnySignedBlock (P : Preset) := Σ f : CFork, SignedBeaconBlock P f

/-- `state_transition` for `signedBlock` with the engine's verdict on the block's payload,
returning the beacon state and the execution chain after it. `atSlot` is the post-upgrade case
of a fork crossing: the state is already at the block's slot, so `process_slots` is skipped
(the signature and state-root checks still apply). The engine's verdict is computed from the
block and the execution chain alone; `process_execution_payload` reads it through
`Ctx.executionValid`. -/
def jointTransitionAt (cfg : ChainConfig) (ccfg : Config) (bls : Bool) {f : CFork}
    (beacon : BeaconState P f) (exec : BlockChain) (signedBlock : SignedBeaconBlock P f)
    (atSlot : Bool := false) : M (BeaconState P f × BlockChain) := do
  let req ← NewPayloadRequest.ofBlock signedBlock.message
  let verdict := engineVerdict cfg f exec req
  let ctx : Ctx := { cfg := ccfg, blsActive := bls, executionValid := verdict.isOk }
  let beacon ← if atSlot then do
      require (← verifyBlockSignature bls beacon signedBlock) "state_transition: verify_block_signature"
      let s ← processBlock ctx beacon signedBlock.message
      require (B256.beq signedBlock.message.state_root (Ssz.hashTreeRoot s))
        "state_transition: block.state_root"
      pure s
    else do
      stateTransition ctx beacon signedBlock
  match verdict with
  | .ok exec' => pure (beacon, exec')
  | .error _ => throw (.assert "process_execution_payload: execution engine")

/-- The first slot of `FULU_FORK_EPOCH`, as a natural number (the configured epoch may be the
far-future sentinel, whose slot does not fit a `Slot`). -/
def fuluForkSlot (ccfg : Config) : Nat := ccfg.FULU_FORK_EPOCH * P.SLOTS_PER_EPOCH

/-- One joint step: the joint state after the signed block `b`. -/
def jointStep (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (s : JointState P)
    (b : AnySignedBlock P) : M (JointState P) :=
  match s, b with
  | ⟨.electra, beacon, exec⟩, ⟨.electra, signedBlock⟩ => do
    require (decide (signedBlock.message.slot.toNat < fuluForkSlot (P := P) ccfg))
      "joint step: an Electra block at or after the Fulu fork slot"
    let (beacon, exec) ← jointTransitionAt cfg ccfg bls beacon exec signedBlock
    pure ⟨.electra, beacon, exec⟩
  | ⟨.fulu, beacon, exec⟩, ⟨.fulu, signedBlock⟩ => do
    let (beacon, exec) ← jointTransitionAt cfg ccfg bls beacon exec signedBlock
    pure ⟨.fulu, beacon, exec⟩
  | ⟨.electra, beacon, exec⟩, ⟨.fulu, signedBlock⟩ => do
    let forkSlotNat := fuluForkSlot (P := P) ccfg
    require (decide (beacon.slot.toNat ≤ forkSlotNat ∧ forkSlotNat ≤ signedBlock.message.slot.toNat))
      "joint step: a Fulu block crossing from an Electra state"
    let forkSlot ← U64.ofNat? forkSlotNat "joint step: Fulu fork slot"
    let ctx : Ctx := { cfg := ccfg, blsActive := bls }
    let beacon ← if beacon.slot < forkSlot then do processSlots ctx beacon forkSlot else pure beacon
    let beacon ← upgradeToFulu ccfg beacon
    let (beacon, exec) ← jointTransitionAt cfg ccfg bls beacon exec signedBlock
      (atSlot := signedBlock.message.slot == beacon.slot)
    pure ⟨.fulu, beacon, exec⟩
  | _, _ => throw (.assert "joint step: fork pair outside Electra and Fulu")

end JauneConsensus
