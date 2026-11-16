import JauneConsensus.GossipCore
import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Snappy
import JauneConsensus.Harness.Yaml

/-!
# `networking/gossip_*` cases: the driver (harness only; goal `eip8282-gloas-cross-layer-v1`, U7a)

`tests/formats/networking/gossip_validation.md` (`consensus-specs` `v1.7.0-beta.4`). A case holds
`meta.yaml`, the anchor `state.ssz_snappy`, block files `block_0x<root>.ssz_snappy`, message
files named `<prefix>0x<root>.ssz_snappy`, and possibly `config.yaml`. `meta.yaml` names the
`topic`, the `blocks` to set up the store with (the first is the anchor), optional
`finalized_checkpoint` and `seen_partial_data_column_headers`, and the `messages` to validate
in sequence, each with its `expected` result (`valid`, `ignore` or `reject`) and, for a failure,
the spec's `reason`.

The format document's message-file prefixes are incomplete at the pin (review F6). The prefixes
below were read from the vectors (every file of every `gossip_*` case of `minimal` and
`mainnet`, Electra, Fulu and Gloas): `beacon_attestation` uses `single_attestation_`, not the
documented `attestation_`, and the Gloas topics use `execution_payload_bid_`,
`execution_payload_envelope_`, `payload_attestation_message_` and `proposer_preferences_`.
`payload_status` in `blocks` is the format's own vocabulary (`VALID`, `INVALIDATED`,
`NOT_VALIDATED`), read as a string and left to the handler to map onto its fork's
`PAYLOAD_STATUS_*`.

**The verdict.** The driver parses `meta.yaml` strictly (unknown keys refuse), checks the topic
against the handler's, checks that every referenced file exists and every message file carries
the handler's prefix, runs the handler, and compares its outcomes with `expected` one by one.
The `reason` is informational in the format (clients may order independent checks freely); the
validators here are transcribed in the spec's order with its reason strings, so the driver also
requires the reason to match when the vector gives one. A handler error (decoding, a model
exception, a missing `current_time_ms`) fails the case.

**Extension point.** A handler is a `GossipHandler`: its topic, its message-file prefix and a
`run` from the parsed case (`GossipEnv`) to one `Gossip.Outcome` per message. The handlers live
in `GossipTable.lean`'s `gossipHandlers`; the store-free ones are in `GossipStoreFree.lean`. A
Store-dependent handler (unit M6) is a new module that builds its `GossipHandler` (decoding the
blocks, replaying them into its `Store`, honouring `failed`/`pending`/`payload_status`/`payload`
and `finalized_checkpoint`) and one new row in that table; this driver does not change.
-/

namespace JauneConsensus.Harness
open Jaune (Bytes)
open Yaml

/-- `expected` of a message. -/
inductive GossipExpected | valid | ignore | reject
  deriving Repr, BEq

/-- One entry of `meta.yaml`'s `blocks`. -/
structure GossipBlockEntry where
  block : String
  failed : Bool := false
  pending : Bool := false
  payloadStatus : Option String := none
  payload : Option String := none
  deriving Repr

/-- One entry of `meta.yaml`'s `messages`. -/
structure GossipMessage where
  message : String
  expected : GossipExpected
  reason : Option String := none
  currentTimeMs : Option Nat := none
  subnetId : Option Nat := none
  columnIndex : Option Nat := none
  groupId : Option String := none
  deriving Repr

/-- `meta.yaml` of a gossip case. -/
structure GossipMeta where
  topic : String
  blocks : List GossipBlockEntry
  /-- `finalized_checkpoint` as given (`epoch` and `root` or `block`); the Store-dependent
  handlers read it. -/
  finalizedCheckpoint : Option YVal := none
  /-- `seen_partial_data_column_headers`: `(block_root, header file)` pairs. -/
  seenPartialHeaders : List (String × String) := []
  messages : List GossipMessage
  blsSetting : Option Nat := none

/-- What a handler receives. -/
structure GossipEnv where
  case : Case
  cfg : Config
  preset : Preset
  caseMeta : GossipMeta
  /-- `bls_setting` 2 turns BLS off; the gossip vectors carry only `1` or nothing. -/
  blsActive : Bool

/-- A gossip topic handler. -/
structure GossipHandler where
  /-- `meta.yaml` `topic`. -/
  topic : String
  /-- The message-file prefix (`voluntary_exit_` for `voluntary_exit_0x<root>.ssz_snappy`). -/
  filePrefix : String
  /-- One outcome per message, in order. -/
  run : GossipEnv → IO (Except String (List Gossip.Outcome))

/-! ## Reading `meta.yaml` -/

private def asStr (v : YVal) (what : String) : Except String String :=
  match v with
  | .scalar s _ => .ok s
  | _ => .error s!"{what}: expected a scalar"

private def onlyKeys (v : YVal) (allowed : List String) (what : String) : Except String Unit :=
  match v with
  | .map kvs =>
    match kvs.find? (fun (k, _) => !allowed.contains k) with
    | some (k, _) => .error s!"{what}: unknown key {k}"
    | none => .ok ()
  | _ => .error s!"{what}: expected a mapping"

private def optNat (v : YVal) (k : String) : Except String (Option Nat) :=
  match v.get? k with
  | none => .ok none
  | some x => (some <$> x.asNat).mapError (s!"{k}: " ++ toString ·)

private def optStr (v : YVal) (k : String) : Except String (Option String) :=
  match v.get? k with
  | none => .ok none
  | some x => some <$> asStr x k

private def optBool (v : YVal) (k : String) : Except String Bool :=
  match v.get? k with
  | none => .ok false
  | some x => x.asBool.mapError (s!"{k}: " ++ toString ·)

private def reqStr (v : YVal) (k : String) : Except String String := do
  asStr (← (v.field k).mapError toString) k

def parseGossipBlock (v : YVal) : Except String GossipBlockEntry := do
  onlyKeys v ["block", "failed", "pending", "payload_status", "payload"] "blocks entry"
  let payloadStatus ← optStr v "payload_status"
  if let some s := payloadStatus then
    if !["VALID", "INVALIDATED", "NOT_VALIDATED"].contains s then
      throw s!"payload_status: unknown value {s}"
  pure { block := ← reqStr v "block", failed := ← optBool v "failed",
         pending := ← optBool v "pending", payloadStatus, payload := ← optStr v "payload" }

def parseGossipMessage (v : YVal) : Except String GossipMessage := do
  onlyKeys v ["current_time_ms", "subnet_id", "column_index", "group_id", "message", "expected",
    "reason"] "messages entry"
  let expected ← match ← reqStr v "expected" with
    | "valid" => pure GossipExpected.valid
    | "ignore" => pure .ignore
    | "reject" => pure .reject
    | s => throw s!"expected: unknown value {s}"
  pure { message := ← reqStr v "message", expected, reason := ← optStr v "reason",
         currentTimeMs := ← optNat v "current_time_ms", subnetId := ← optNat v "subnet_id",
         columnIndex := ← optNat v "column_index", groupId := ← optStr v "group_id" }

def parseGossipMeta (v : YVal) : Except String GossipMeta := do
  onlyKeys v ["topic", "blocks", "messages", "bls_setting", "finalized_checkpoint",
    "seen_partial_data_column_headers"] "meta.yaml"
  let blocks ← match v.get? "blocks" with
    | none => pure []
    | some b => (← b.asSeq.mapError toString).mapM parseGossipBlock
  let messages ← (← ((v.field "messages").bind YVal.asSeq).mapError toString).mapM parseGossipMessage
  if messages.isEmpty then throw "meta.yaml: no messages"
  let seenPartialHeaders ← match v.get? "seen_partial_data_column_headers" with
    | none => pure []
    | some s => (← s.asSeq.mapError toString).mapM fun e => do
      onlyKeys e ["block_root", "header"] "seen_partial_data_column_headers entry"
      pure (← reqStr e "block_root", ← reqStr e "header")
  pure { topic := ← reqStr v "topic", blocks, messages, seenPartialHeaders,
         finalizedCheckpoint := v.get? "finalized_checkpoint",
         blsSetting := ← optNat v "bls_setting" }

/-! ## Files -/

/-- Read and Snappy-decode `<name>.ssz_snappy` of the case. -/
def GossipEnv.load (env : GossipEnv) (name : String) : IO (Except String Bytes) := do
  let file := name ++ ".ssz_snappy"
  if !env.case.has file then return .error s!"{file}: not in the case"
  match Snappy.decompress (← IO.FS.readBinFile (env.case.dir / file)) with
  | .ok b => pure (.ok b.toList)
  | .error e => pure (.error s!"{file}: snappy: {e}")

/-- Decode an SSZ value. -/
def gossipDecode {α : Type} [Ssz α] (bytes : Bytes) (what : String) : Except String α :=
  match (deserialize bytes : M α) with
  | .ok v => .ok v
  | .error r => .error s!"{what}: decode rejected: {repr r}"

/-- Load and decode a case file. -/
def GossipEnv.decode {α : Type} [Ssz α] (env : GossipEnv) (name : String) : IO (Except String α) := do
  pure ((← env.load name).bind (gossipDecode · name))

/-! ## Running and comparing -/

/-- Run the messages in order through `step` from `init`: each message file is decoded as `α`
and validated; the cache threads through. A model exception fails the case. -/
def gossipRunMessages {σ α : Type} [Ssz α] (env : GossipEnv) (init : σ)
    (step : σ → GossipMessage → α → Except String (Gossip.GM σ)) :
    IO (Except String (List Gossip.Outcome)) := do
  let mut seen := init
  let mut out := #[]
  for m in env.caseMeta.messages do
    let msg : α ← match ← env.decode m.message with
      | .ok x => pure x
      | .error e => return .error e
    let v ← match step seen m msg with
      | .ok v => pure v
      | .error e => return .error s!"{m.message}: {e}"
    match Gossip.outcome seen v with
    | .error r => return .error s!"{m.message}: model raised {repr r}"
    | .ok (o, seen') =>
      out := out.push o
      seen := seen'
  pure (.ok out.toList)

/-- A required per-message field. -/
def gossipNeed (field : String) : Option Nat → Except String U64
  | some n => (U64.ofNat? n field).mapError (fun r => s!"{field}: {repr r}")
  | none => .error s!"{field} is missing"

private def render : Gossip.Outcome → String
  | .valid => "valid"
  | .ignore r => s!"ignore ({r})"
  | .reject r => s!"reject ({r})"

/-- Compare one outcome with the vector's `expected` and `reason`. -/
def gossipMatches (m : GossipMessage) (o : Gossip.Outcome) : Option String :=
  let want := match m.expected with
    | .valid => "valid" | .ignore => "ignore" | .reject => "reject"
  let ok := match m.expected, o with
    | .valid, .valid => true
    | .ignore, .ignore r | .reject, .reject r => m.reason.all (· == r)
    | _, _ => false
  if ok then none
  else some s!"{m.message}: got {render o}, expected {want}{(m.reason.map (s!" ({·})")).getD ""}"

/-- Run a `networking/gossip_*` case through the handler table under `cfg`. -/
def gossipCase (handlers : String → Option GossipHandler) (cfg : Config) (c : Case) :
    IO (Except String Unit) := do
  let some preset := Preset.ofName? c.preset | return .error s!"no preset {c.preset}"
  let some h := handlers c.key.handler
    | return .error s!"UNIMPLEMENTED: no gossip handler {c.key.handler} at {c.key.fork}"
  if !c.has "meta.yaml" || !c.has "state.ssz_snappy" then
    return .error s!"unexpected files {c.files}"
  let cm ← match (parse (← IO.FS.readBinFile (c.dir / "meta.yaml"))).mapError toString
      |>.bind parseGossipMeta with
    | .ok m => pure m
    | .error e => return .error s!"meta.yaml: {e}"
  if cm.topic != h.topic then
    return .error s!"meta.yaml topic {cm.topic}, handler topic {h.topic}"
  for b in cm.blocks do
    if !c.has (b.block ++ ".ssz_snappy") then return .error s!"block file {b.block} missing"
  for m in cm.messages do
    if !m.message.startsWith h.filePrefix then
      return .error s!"message {m.message} lacks the prefix {h.filePrefix}"
    if !c.has (m.message ++ ".ssz_snappy") then return .error s!"message file {m.message} missing"
  let env : GossipEnv := { case := c, cfg, preset, caseMeta := cm, blsActive := cm.blsSetting != some 2 }
  match ← h.run env with
  | .error e => pure (.error e)
  | .ok outs =>
    if outs.length != cm.messages.length then
      return .error s!"{outs.length} outcomes for {cm.messages.length} messages"
    for (m, o) in cm.messages.zip outs do
      if let some why := gossipMatches m o then return .error why
    pure (.ok ())

end JauneConsensus.Harness
