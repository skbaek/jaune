import JauneConsensus.GloasGossip
import JauneConsensus.Harness.GossipCases

/-!
# The store-free gossip handlers (harness only; goal `eip8282-gloas-cross-layer-v1`, U7a)

`proposer_slashing`, `attester_slashing`, `voluntary_exit`, `bls_to_execution_change`,
`sync_committee` and `sync_committee_contribution_and_proof`, at Electra, Fulu and Gloas. Their
validators read the `Store` only through `store.genesis_time_ms` and the head state, so the
handler sets the store up as `get_forkchoice_store` would from the anchor alone:

* `blocks` must be exactly the anchor, with no `failed`, `pending`, `payload_status` or
  `payload`, and the case has no `finalized_checkpoint` or preloaded headers (a case that needs
  more is refused, never approximated);
* the anchor block's `state_root` must equal `hash_tree_root(state)`, the format's consistency
  condition; with one block, `get_head(store)` is the anchor root and
  `store.block_states[anchor_root]` is the anchor state;
* `store.genesis_time_ms = seconds_to_milliseconds(anchor_state.genesis_time)`.
-/

namespace JauneConsensus.Harness
open Jaune (Bytes)

/-- The store-free head view of a case: see the module note. `stateRoot` and `blockStateRoot`
are the fork's `hash_tree_root(state)` and `signed_block.message.state_root`. -/
def storeFreeHead {S B : Type} [Ssz S] [Ssz B] (env : GossipEnv) (genesisTime : S → U64)
    (blockStateRoot : B → Root) : IO (Except String (Gossip.HeadView S)) := do
  let m := env.caseMeta
  let some anchor := (match m.blocks with | [b] => some b | _ => none)
    | return .error s!"store-free handler: {m.blocks.length} blocks, expected the anchor alone"
  if anchor.failed || anchor.pending || anchor.payloadStatus.isSome || anchor.payload.isSome ||
      m.finalizedCheckpoint.isSome || !m.seenPartialHeaders.isEmpty then
    return .error "store-free handler: the case needs a fork-choice Store"
  let state : S ← match ← env.decode "state" with
    | .ok s => pure s
    | .error e => return .error e
  let block : B ← match ← env.decode anchor.block with
    | .ok b => pure b
    | .error e => return .error e
  if blockStateRoot block != Ssz.hashTreeRoot state then
    return .error "anchor block state_root differs from hash_tree_root(state)"
  match secondsToMilliseconds (genesisTime state) with
  | .ok genesisTimeMs => pure (.ok { genesisTimeMs, headState := state })
  | .error r => pure (.error s!"genesis_time_ms: {repr r}")

/-- The six store-free validators, as handler steps over one fork's state `S`. -/
structure StoreFreeSteps (S : Type) (AS : Type) (P : Preset) where
  voluntaryExit : Ctx → Gossip.Seen Unit → Gossip.HeadView S → SignedVoluntaryExit → U64 →
    Gossip.GM (Gossip.Seen Unit)
  proposerSlashing : Ctx → Gossip.Seen Unit → Gossip.HeadView S → ProposerSlashing →
    Gossip.GM (Gossip.Seen Unit)
  attesterSlashing : Ctx → Gossip.Seen Unit → Gossip.HeadView S → AS →
    Gossip.GM (Gossip.Seen Unit)
  blsChange : Ctx → Gossip.Seen Unit → Gossip.HeadView S → SignedBLSToExecutionChange → U64 →
    Gossip.GM (Gossip.Seen Unit)
  contribution : Ctx → Gossip.Seen Unit → Gossip.HeadView S → SignedContributionAndProof P →
    U64 → Gossip.GM (Gossip.Seen Unit)
  syncMessage : Ctx → Gossip.Seen Unit → Gossip.HeadView S → SyncCommitteeMessage → U64 → U64 →
    Gossip.GM (Gossip.Seen Unit)

/-- Run a store-free handler `h` (`gossip_<topic>` without the prefix) on one fork. -/
def runStoreFree {S B AS : Type} [Ssz S] [Ssz B] [Ssz AS] {P : Preset} (env : GossipEnv)
    (genesisTime : S → U64) (blockStateRoot : B → Root) (steps : StoreFreeSteps S AS P)
    (h : String) : IO (Except String (List Gossip.Outcome)) := do
  let head ← match ← storeFreeHead env genesisTime blockStateRoot with
    | .ok v => pure v
    | .error e => return .error e
  let ctx : Ctx := { cfg := env.cfg, blsActive := env.blsActive }
  let seen : Gossip.Seen Unit := Gossip.Seen.empty ()
  let time (m : GossipMessage) := gossipNeed "current_time_ms" m.currentTimeMs
  match h with
  | "voluntary_exit" =>
    gossipRunMessages env seen fun s m (x : SignedVoluntaryExit) => do
      pure (steps.voluntaryExit ctx s head x (← time m))
  | "proposer_slashing" =>
    gossipRunMessages env seen fun s _ (x : ProposerSlashing) => do
      pure (steps.proposerSlashing ctx s head x)
  | "attester_slashing" =>
    gossipRunMessages env seen fun s _ (x : AS) => do
      pure (steps.attesterSlashing ctx s head x)
  | "bls_to_execution_change" =>
    gossipRunMessages env seen fun s m (x : SignedBLSToExecutionChange) => do
      pure (steps.blsChange ctx s head x (← time m))
  | "sync_committee_contribution_and_proof" =>
    gossipRunMessages env seen fun s m (x : SignedContributionAndProof P) => do
      pure (steps.contribution ctx s head x (← time m))
  | "sync_committee_message" =>
    gossipRunMessages env seen fun s m (x : SyncCommitteeMessage) => do
      pure (steps.syncMessage ctx s head x (← time m) (← gossipNeed "subnet_id" m.subnetId))
  | _ => pure (.error s!"no store-free handler {h}")

/-- The fork-indexed steps (Electra, Fulu). -/
def forkSteps (P : Preset) (f : CFork) : StoreFreeSteps (BeaconState P f) (AttesterSlashing P f) P where
  voluntaryExit := Gossip.validateVoluntaryExitGossip
  proposerSlashing := Gossip.validateProposerSlashingGossip
  attesterSlashing := Gossip.validateAttesterSlashingGossip
  blsChange := Gossip.validateBlsToExecutionChangeGossip
  contribution := Gossip.validateSyncCommitteeContributionAndProofGossip
  syncMessage := Gossip.validateSyncCommitteeMessageGossip

/-- The Gloas steps (`GloasGossip.lean`). -/
def gloasSteps (P : Preset) : StoreFreeSteps (Gloas.BeaconState P) Gloas.AttesterSlashing P where
  voluntaryExit := Gloas.validateVoluntaryExitGossip
  proposerSlashing := Gloas.validateProposerSlashingGossip
  attesterSlashing := Gloas.validateAttesterSlashingGossip
  blsChange := Gloas.validateBlsToExecutionChangeGossip
  contribution := Gloas.validateSyncCommitteeContributionAndProofGossip
  syncMessage := Gloas.validateSyncCommitteeMessageGossip

/-- A store-free handler: `topic` and `filePrefix` from the format, `h` the validator. -/
def storeFreeHandler (topic filePrefix h : String) : GossipHandler where
  topic := topic
  filePrefix := filePrefix
  run env := do
    let P := env.preset
    match env.case.key.fork with
    | "electra" =>
      runStoreFree (S := BeaconState P .electra) (B := SignedBeaconBlock P .electra) env
        (·.genesis_time) (·.message.state_root) (forkSteps P .electra) h
    | "fulu" =>
      runStoreFree (S := BeaconState P .fulu) (B := SignedBeaconBlock P .fulu) env
        (·.genesis_time) (·.message.state_root) (forkSteps P .fulu) h
    | "gloas" =>
      runStoreFree (S := Gloas.BeaconState P) (B := Gloas.SignedBeaconBlock P) env
        (·.genesis_time) (·.message.state_root) (gloasSteps P) h
    | f => pure (.error s!"no store-free gossip handler at fork {f}")

end JauneConsensus.Harness
