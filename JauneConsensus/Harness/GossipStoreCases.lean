import JauneConsensus.GossipStore
import JauneConsensus.GloasGossipStore
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

/-! ## Gloas

The Gloas store follows the same Condition over M4's `Gloas.Store`: each imported block also
gets the empty PTC vote slots `on_block` creates (the generator's `record_block_in_store`); a
`payload` entry records the envelope's message in `store.payloads` (as
`on_execution_payload_envelope` does); `finalized_checkpoint` replaces the store's and, for the
state-based view (builder activation reads `state.finalized_checkpoint`), every stored post-state's
`finalized_checkpoint`. -/

/-- The Gloas store of a case, and its `block_payload_statuses`. -/
structure GloasGossipStoreSetup (P : Preset) where
  store : Gloas.Store P
  payloadStatuses : List (Root × PayloadValidationStatus)

/-- Set the Gloas store up. -/
def gloasGossipStoreSetup {P : Preset} (env : GossipEnv) (ctx : Ctx) :
    IO (Except String (GloasGossipStoreSetup P)) := ExceptT.run do
  let m := env.caseMeta
  let some anchor := m.blocks.head? | throw "no anchor block"
  let state : Gloas.BeaconState P ← ExceptT.mk (env.decode "state")
  let anchorBlock : Gloas.SignedBeaconBlock P ← ExceptT.mk (env.decode anchor.block)
  if anchor.failed || anchor.pending then throw "anchor block marked failed or pending"
  let mut store ← match Gloas.getForkchoiceStore ctx.cfg state anchorBlock.message with
    | .ok s => pure s
    | .error r => throw s!"get_forkchoice_store: {repr r}"
  let noVotes : Array (Option Bool) := Array.replicate P.PTC_SIZE none
  let mut statuses : List (Root × PayloadValidationStatus) := []
  let mut blockRoots : List (String × Root) := []
  for b in m.blocks do
    let isAnchor := blockRoots.isEmpty
    if b.failed && b.pending then throw s!"{b.block}: both failed and pending"
    let signed : Gloas.SignedBeaconBlock P ← ExceptT.mk (env.decode b.block)
    let root : Root := Ssz.hashTreeRoot signed.message
    blockRoots := blockRoots ++ [(b.block, root)]
    if !isAnchor then
      if b.failed || b.pending then
        store := { store with blocks := store.blocks.insert root signed.message }
      else
        let parentState ← match store.block_states.get? signed.message.parent_root with
          | some s => pure s
          | none => throw s!"{b.block}: parent state unknown"
        let post ← match Gloas.stateTransition ctx parentState signed true with
          | .ok s => pure s
          | .error r => throw s!"{b.block}: state_transition rejected: {repr r}"
        store := { store with
          blocks := store.blocks.insert root signed.message
          block_states := store.block_states.insert root post
          payload_timeliness_vote := store.payload_timeliness_vote.insert root noVotes
          payload_data_availability_vote :=
            store.payload_data_availability_vote.insert root noVotes }
    if let some pfile := b.payload then
      let env' : Gloas.SignedExecutionPayloadEnvelope P ← ExceptT.mk (env.decode pfile)
      store := { store with payloads := store.payloads.insert root env'.message }
    if let some s := b.payloadStatus then
      statuses := statuses ++ [(root, ← ExceptT.mk (pure (payloadStatusOf s)))]
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
        | none => throw s!"finalized_checkpoint.block {name} is not a blocks entry"
      | _, _ => throw "finalized_checkpoint: root or block"
    let cp : Checkpoint := { epoch, root }
    store := { store with
      finalized_checkpoint := cp
      block_states := store.block_states.map fun _ st => { st with finalized_checkpoint := cp } }
  pure { store, payloadStatuses := statuses }

/-- The message kinds a Gloas `execution_payload_bid` case interleaves: the bid validator reads
the proposer preferences and parent payloads that earlier valid messages put in `Seen`. -/
def gloasBidCasePrefixes : List String :=
  ["proposer_preferences_", "execution_payload_envelope_", "execution_payload_bid_"]

/-- Run one Gloas Store-dependent handler `h`. -/
def runGloasStoreGossip (P : Preset) (env : GossipEnv) (h : String) :
    IO (Except String (List Gossip.Outcome)) := ExceptT.run do
  let ctx : Ctx := { cfg := env.cfg, blsActive := env.blsActive }
  let setup : GloasGossipStoreSetup P ← ExceptT.mk (gloasGossipStoreSetup env ctx)
  let store := setup.store
  if !env.caseMeta.seenPartialHeaders.isEmpty then
    throw "seen_partial_data_column_headers: Gloas has no partial headers"
  let seen : Gloas.GSeen P := Gossip.Seen.empty {}
  let statuses (r : Root) := (setup.payloadStatuses.find? (·.1 == r)).map (·.2)
  let time (m : GossipMessage) := gossipNeed "current_time_ms" m.currentTimeMs
  let subnet (m : GossipMessage) := gossipNeed "subnet_id" m.subnetId
  match h with
  | "beacon_block" =>
    ExceptT.mk <| gossipRunMessages env seen fun s m (x : Gloas.SignedBeaconBlock P) => do
      pure (Gloas.validateBeaconBlockGossip ctx s store x (← time m))
  | "beacon_aggregate_and_proof" =>
    ExceptT.mk <| gossipRunMessages env seen fun s m (x : Gloas.SignedAggregateAndProof P) => do
      pure (Gloas.validateBeaconAggregateAndProofGossip ctx s store x (← time m) statuses)
  | "beacon_attestation" =>
    ExceptT.mk <| gossipRunMessages env seen fun s m (x : SingleAttestation) => do
      pure (Gloas.validateBeaconAttestationGossip ctx s store x (← time m) (← subnet m) statuses)
  | "data_column_sidecar" =>
    ExceptT.mk <| gossipRunMessages env seen fun s m (x : Gloas.DataColumnSidecar P) => do
      pure (Gloas.validateDataColumnSidecarGossip ctx s store x (← time m) (← subnet m))
  | "partial_data_column_sidecar" =>
    let mut out := #[]
    for m in env.caseMeta.messages do
      if m.currentTimeMs.isSome then throw s!"{m.message}: current_time_ms: the validator takes none"
      let x : Gloas.PartialDataColumnSidecar P ← ExceptT.mk (env.decode m.message)
      let some gid := m.groupId | throw s!"{m.message}: group_id is missing"
      let groupId : Gloas.PartialDataColumnGroupID ← ExceptT.mk (env.decode gid)
      let col ← ExceptT.mk (pure (gossipNeed "column_index" m.columnIndex))
      match Gossip.outcome () (Gloas.validatePartialDataColumnSidecarGossip store x groupId col) with
      | .error r => throw s!"{m.message}: model raised {repr r}"
      | .ok (o, _) => out := out.push o
    pure out.toList
  | "execution_payload" =>
    ExceptT.mk <| gossipRunMessages env seen fun s m (x : Gloas.SignedExecutionPayloadEnvelope P) => do
      if m.currentTimeMs.isSome then throw "current_time_ms: the validator takes none"
      pure (Gloas.validateExecutionPayloadEnvelopeGossip ctx s store x)
  | "payload_attestation_message" =>
    ExceptT.mk <| gossipRunMessages env seen fun s m (x : Gloas.PayloadAttestationMessage) => do
      pure (Gloas.validatePayloadAttestationMessageGossip ctx s store x (← time m))
  | "proposer_preferences" =>
    ExceptT.mk <| gossipRunMessages env seen fun s m (x : Gloas.SignedProposerPreferences) => do
      pure (Gloas.validateProposerPreferencesGossip ctx s store x (← time m))
  | "execution_payload_bid" =>
    let mut seen := seen
    let mut out := #[]
    for m in env.caseMeta.messages do
      let v : Gossip.GM (Gloas.GSeen P) ←
        if m.message.startsWith "proposer_preferences_" then do
          let x : Gloas.SignedProposerPreferences ← ExceptT.mk (env.decode m.message)
          pure (Gloas.validateProposerPreferencesGossip ctx seen store x
            (← ExceptT.mk (pure (time m))))
        else if m.message.startsWith "execution_payload_envelope_" then do
          if m.currentTimeMs.isSome then throw s!"{m.message}: current_time_ms: the validator takes none"
          let x : Gloas.SignedExecutionPayloadEnvelope P ← ExceptT.mk (env.decode m.message)
          pure (Gloas.validateExecutionPayloadEnvelopeGossip ctx seen store x)
        else if m.message.startsWith "execution_payload_bid_" then do
          let x : Gloas.SignedExecutionPayloadBid ← ExceptT.mk (env.decode m.message)
          pure (Gloas.validateExecutionPayloadBidGossip ctx seen store x
            (← ExceptT.mk (pure (time m))))
        else throw s!"message {m.message} has none of the prefixes {gloasBidCasePrefixes}"
      match Gossip.outcome seen v with
      | .error r => throw s!"{m.message}: model raised {repr r}"
      | .ok (o, seen') =>
        out := out.push o
        seen := seen'
    pure out.toList
  | _ => throw s!"no Gloas Store-dependent gossip handler {h}"

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
    | "gloas" => runGloasStoreGossip P env h
    | fk => pure (.error s!"UNIMPLEMENTED: Store-dependent gossip handler {h} at fork {fk}")

end JauneConsensus.Harness
