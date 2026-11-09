import JauneConsensus.GossipStore
import JauneConsensus.Harness.GossipCases

/-!
# The Store-dependent gossip handlers, Electra and Fulu (harness only; goal
`eip8282-gloas-cross-layer-v1`, M6)

`beacon_block`, `beacon_attestation`, `beacon_aggregate_and_proof`, `blob_sidecar` (Electra),
`data_column_sidecar` and `partial_data_column_sidecar` (Fulu), over the validators of
`JauneConsensus/GossipStore.lean`. The store is set up as the format's "Condition"
(`tests/formats/networking/gossip_validation.md` at `v1.7.0-beta.4`) says:

1. `get_forkchoice_store(anchor_state, anchor_block)` from `state.ssz_snappy` and the first
   `blocks` entry (its `state_root` must be `hash_tree_root(state)`), not state-transitioned;
2. every later entry, oldest first: `failed` or `pending` records the block in `store.blocks`
   with no post-state; otherwise `state_transition(store.block_states[parent_root], block)`
   (signatures and state root checked) gives the post-state, and the block and its state are
   recorded as the generator's helpers record them (in `store.blocks` and
   `store.block_states`, without `on_block`'s checkpoint or timeliness updates);
   `payload_status` enters `block_payload_statuses`; `payload` is Gloas-only and refused here;
3. `finalized_checkpoint` (with `root`, or `block` naming a block file whose message root is
   used) replaces `store.finalized_checkpoint`;
4. `seen_partial_data_column_headers` preloads `seen.partial_data_column_headers`;
5. the messages run in order through one `Seen`.

A case at a fork where its topic does not exist (`blob_sidecar` after Electra, the column topics
before Fulu) is refused.
-/

namespace JauneConsensus.Harness
open Jaune (Bytes B256)
open Yaml
open Gossip (StoreSeen SSeen PayloadValidationStatus)

private def hexRoot (what s : String) : Except String Root :=
  match s.toList with
  | '0' :: 'x' :: cs =>
    match YVal.hexBytes cs with
    | some bs => if bs.length == 32 then .ok (B256.ofBytes bs) else .error s!"{what}: not 32 bytes"
    | none => .error s!"{what}: bad hex {s}"
  | _ => .error s!"{what}: no 0x prefix in {s}"

private def payloadStatusOf : String → Except String PayloadValidationStatus
  | "VALID" => .ok .valid
  | "INVALIDATED" => .ok .invalidated
  | "NOT_VALIDATED" => .ok .notValidated
  | s => .error s!"payload_status {s}"

/-- The store of a case, and its `block_payload_statuses`. -/
structure GossipStoreSetup (P : Preset) (f : CFork) where
  store : Store P f
  payloadStatuses : List (Root × PayloadValidationStatus)

/-- Set the store up as the module note says. -/
def gossipStoreSetup {P : Preset} {f : CFork} (env : GossipEnv) (ctx : Ctx) :
    IO (Except String (GossipStoreSetup P f)) := ExceptT.run do
  let m := env.caseMeta
  let some anchor := m.blocks.head? | throw "no anchor block"
  let state : BeaconState P f ← ExceptT.mk (env.decode "state")
  let anchorBlock : SignedBeaconBlock P f ← ExceptT.mk (env.decode anchor.block)
  if anchor.failed || anchor.pending || anchor.payload.isSome then
    throw "anchor block marked failed, pending or with a payload"
  let mut store ← match getForkchoiceStore ctx.cfg state anchorBlock.message with
    | .ok s => pure s
    | .error r => throw s!"get_forkchoice_store: {repr r}"
  let mut statuses : List (Root × PayloadValidationStatus) := []
  let mut blockRoots : List (String × Root) := [(anchor.block, Ssz.hashTreeRoot anchorBlock.message)]
  let addStatus (statuses : List (Root × PayloadValidationStatus)) (root : Root)
      (s : Option String) : Except String (List (Root × PayloadValidationStatus)) := do
    match s with
    | none => pure statuses
    | some s => pure (statuses ++ [(root, ← payloadStatusOf s)])
  statuses ← ExceptT.mk (pure (addStatus statuses (Ssz.hashTreeRoot anchorBlock.message)
    anchor.payloadStatus))
  for b in m.blocks.drop 1 do
    if b.payload.isSome then throw s!"{b.block}: payload is Gloas-only"
    if b.failed && b.pending then throw s!"{b.block}: both failed and pending"
    let signed : SignedBeaconBlock P f ← ExceptT.mk (env.decode b.block)
    let root : Root := Ssz.hashTreeRoot signed.message
    blockRoots := blockRoots ++ [(b.block, root)]
    if b.failed || b.pending then
      store := { store with blocks := store.blocks.insert root signed.message }
    else
      let parentState ← match store.block_states.get? signed.message.parent_root with
        | some s => pure s
        | none => throw s!"{b.block}: parent state unknown"
      let post ← match stateTransition ctx parentState signed true with
        | .ok s => pure s
        | .error r => throw s!"{b.block}: state_transition rejected: {repr r}"
      store := { store with
        blocks := store.blocks.insert root signed.message
        block_states := store.block_states.insert root post }
    statuses ← ExceptT.mk (pure (addStatus statuses root b.payloadStatus))
  if let some fc := m.finalizedCheckpoint then
    let keys := fc.keys
    if !(keys.all (· ∈ ["epoch", "root", "block"])) || keys.contains "root" == keys.contains "block" then
      throw s!"finalized_checkpoint: keys {keys}"
    let epochN ← ExceptT.mk (pure ((fc.field "epoch").bind YVal.asNat |>.mapError toString))
    let epoch ← match U64.ofNat? epochN "finalized_checkpoint.epoch" with
      | .ok e => pure e
      | .error _ => throw "finalized_checkpoint.epoch out of range"
    let root ← match fc.get? "root", fc.get? "block" with
      | some (.scalar s _), _ => ExceptT.mk (pure (hexRoot "finalized_checkpoint.root" s))
      | _, some (.scalar name _) =>
        match blockRoots.find? (·.1 == name) with
        | some (_, r) => pure r
        | none =>
          let blk : SignedBeaconBlock P f ← ExceptT.mk (env.decode name)
          pure (Ssz.hashTreeRoot blk.message)
      | _, _ => throw "finalized_checkpoint: root or block"
    store := { store with finalized_checkpoint := { epoch, root } }
  pure { store, payloadStatuses := statuses }

/-- The initial `Seen`, with `seen_partial_data_column_headers` preloaded. -/
def gossipStoreSeen {P : Preset} (env : GossipEnv) : IO (Except String (SSeen P)) := ExceptT.run do
  let mut seen : SSeen P := Gossip.Seen.empty {}
  for (rootHex, file) in env.caseMeta.seenPartialHeaders do
    let root ← ExceptT.mk (pure (hexRoot "seen_partial_data_column_headers.block_root" rootHex))
    let header : PartialDataColumnHeader P ← ExceptT.mk (env.decode file)
    seen := Gossip.cachePartialHeader seen root header
  pure seen

/-- Run one Store-dependent handler `h` at fork `f`. -/
def runStoreGossip (P : Preset) (f : CFork) (env : GossipEnv) (h : String) :
    IO (Except String (List Gossip.Outcome)) := ExceptT.run do
  let ctx : Ctx := { cfg := env.cfg, blsActive := env.blsActive }
  let setup : GossipStoreSetup P f ← ExceptT.mk (gossipStoreSetup env ctx)
  let store := setup.store
  let seen : SSeen P ← ExceptT.mk (gossipStoreSeen env)
  let time (m : GossipMessage) := gossipNeed "current_time_ms" m.currentTimeMs
  let subnet (m : GossipMessage) := gossipNeed "subnet_id" m.subnetId
  let fulu := f.atLeast .fulu
  match h with
  | "beacon_block" =>
    let statuses (r : Root) := (setup.payloadStatuses.find? (·.1 == r)).map (·.2)
    ExceptT.mk <| gossipRunMessages env seen fun s m (x : SignedBeaconBlock P f) => do
      pure (Gossip.validateBeaconBlockGossip ctx s store x (← time m) statuses)
  | "beacon_aggregate_and_proof" =>
    ExceptT.mk <| gossipRunMessages env seen fun s m (x : SignedAggregateAndProof P f) => do
      pure (Gossip.validateBeaconAggregateAndProofGossip ctx s store x (← time m))
  | "beacon_attestation" =>
    ExceptT.mk <| gossipRunMessages env seen fun s m (x : SingleAttestation) => do
      pure (Gossip.validateBeaconAttestationGossip ctx s store x (← time m) (← subnet m))
  | "blob_sidecar" =>
    if fulu then throw "blob_sidecar is deprecated from Fulu"
    ExceptT.mk <| gossipRunMessages env seen fun s m (x : BlobSidecar P) => do
      pure (Gossip.validateBlobSidecarGossip ctx s store x (← time m) (← subnet m))
  | "data_column_sidecar" =>
    if !fulu then throw "data_column_sidecar starts at Fulu"
    ExceptT.mk <| gossipRunMessages env seen fun s m (x : DataColumnSidecar P) => do
      pure (Gossip.validateDataColumnSidecarGossip ctx s store x (← time m) (← subnet m))
  | "partial_data_column_sidecar" =>
    if !fulu then throw "partial_data_column_sidecar starts at Fulu"
    let mut seen := seen
    let mut out := #[]
    for m in env.caseMeta.messages do
      let sidecar : PartialDataColumnSidecar P ← ExceptT.mk (env.decode m.message)
      let some gid := m.groupId | throw s!"{m.message}: group_id is missing"
      let groupId : PartialDataColumnGroupID ← ExceptT.mk (env.decode gid)
      let t ← ExceptT.mk (pure (time m))
      let col ← ExceptT.mk (pure (gossipNeed "column_index" m.columnIndex))
      match Gossip.validatePartialDataColumnSidecarGossip ctx seen store sidecar t groupId col with
      | .error r => throw s!"{m.message}: model raised {repr r}"
      | .ok (o, seen') =>
        out := out.push o
        seen := seen'
    pure out.toList
  | _ => throw s!"no Store-dependent gossip handler {h}"

/-- A Store-dependent handler (Electra, Fulu): `topic` and `filePrefix` from `gossipTopics`,
`h` the validator. -/
def storeGossipHandler (topic filePrefix h : String) : GossipHandler where
  topic := topic
  filePrefix := filePrefix
  run env := do
    let P := env.preset
    match env.case.key.fork with
    | "electra" => runStoreGossip P .electra env h
    | "fulu" => runStoreGossip P .fulu env h
    | fk => pure (.error s!"UNIMPLEMENTED: Store-dependent gossip handler {h} at fork {fk}")

end JauneConsensus.Harness
