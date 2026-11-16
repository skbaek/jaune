import JauneConsensus.Harness.GossipStoreFree
import JauneConsensus.Harness.GossipStoreCases

/-!
# The gossip handler table (harness only; goal `eip8282-gloas-cross-layer-v1`, U7a)

`gossipHandlers` maps a `networking` handler directory (`gossip_<name>`) to its
`GossipHandler`. A handler absent here fails its cases as `UNIMPLEMENTED`, never a skip.

**Extension point for the Store-dependent validators (unit M6).** Write the validator over the
`Store` (it may build a `Gossip.HeadView` from the store for the shared helpers of
`GossipCore.lean`, and extend `Gossip.Seen` through its `ext` field), write its handler as a
`GossipHandler` in a new harness module (topic and prefix from `gossipTopics` below), import
that module here and replace the `none` of its row with the handler. The driver
(`GossipCases.lean`), discovery's file kinds and the dispatch in `Runner.lean` need no change.

`gossipTopics` records, per handler directory, the `meta.yaml` topic and the message-file
prefix read from the `v1.7.0-beta.4` vectors, with the owner: `U7a` for the store-free
validators, `M6` for the Store-dependent ones (they read `store.blocks`, a parent's post-state
or the finalized checkpoint's ancestry, which need the blocks imported).
-/

namespace JauneConsensus.Harness

/-- `(handler directory, topic, message-file prefix, owner)`. -/
def gossipTopics : List (String × String × String × String) :=
  [ ("gossip_proposer_slashing", "proposer_slashing", "proposer_slashing_", "U7a"),
    ("gossip_attester_slashing", "attester_slashing", "attester_slashing_", "U7a"),
    ("gossip_voluntary_exit", "voluntary_exit", "voluntary_exit_", "U7a"),
    ("gossip_bls_to_execution_change", "bls_to_execution_change", "bls_to_execution_change_", "U7a"),
    ("gossip_sync_committee_message", "sync_committee", "sync_committee_message_", "U7a"),
    ("gossip_sync_committee_contribution_and_proof", "sync_committee_contribution_and_proof",
      "contribution_", "U7a"),
    ("gossip_beacon_block", "beacon_block", "block_", "M6"),
    ("gossip_beacon_attestation", "beacon_attestation", "single_attestation_", "M6"),
    ("gossip_beacon_aggregate_and_proof", "beacon_aggregate_and_proof", "aggregate_", "M6"),
    ("gossip_blob_sidecar", "blob_sidecar", "blob_sidecar_", "M6"),
    ("gossip_data_column_sidecar", "data_column_sidecar", "data_column_sidecar_", "M6"),
    ("gossip_partial_data_column_sidecar", "partial_data_column_sidecar",
      "partial_data_column_sidecar_", "M6"),
    ("gossip_execution_payload_envelope", "execution_payload", "execution_payload_envelope_", "M6"),
    ("gossip_payload_attestation_message", "payload_attestation_message",
      "payload_attestation_message_", "M6"),
    ("gossip_execution_payload_bid", "execution_payload_bid", "execution_payload_bid_", "M6"),
    ("gossip_proposer_preferences", "proposer_preferences", "proposer_preferences_", "M6") ]

/-- The store-free row for a handler directory. -/
private def storeFree (dir : String) : Option GossipHandler :=
  match gossipTopics.find? (·.1 == dir) with
  | some (_, topic, pfx, _) => some (storeFreeHandler topic pfx (dir.drop 7).toString)
  | none => none

/-- The Store-dependent row for a handler directory (`GossipStoreCases.lean`). -/
private def storeDep (dir : String) : Option GossipHandler :=
  match gossipTopics.find? (·.1 == dir) with
  | some (_, topic, pfx, _) => some (storeGossipHandler topic pfx topic)
  | none => none

/-- The handler table. -/
def gossipHandlers : String → Option GossipHandler
  | "gossip_proposer_slashing" => storeFree "gossip_proposer_slashing"
  | "gossip_attester_slashing" => storeFree "gossip_attester_slashing"
  | "gossip_voluntary_exit" => storeFree "gossip_voluntary_exit"
  | "gossip_bls_to_execution_change" => storeFree "gossip_bls_to_execution_change"
  | "gossip_sync_committee_message" => storeFree "gossip_sync_committee_message"
  | "gossip_sync_committee_contribution_and_proof" =>
    storeFree "gossip_sync_committee_contribution_and_proof"
  -- M6 (Store-dependent; Electra and Fulu, and Gloas)
  | "gossip_beacon_block" => storeDep "gossip_beacon_block"
  | "gossip_beacon_attestation" => storeDep "gossip_beacon_attestation"
  | "gossip_beacon_aggregate_and_proof" => storeDep "gossip_beacon_aggregate_and_proof"
  | "gossip_blob_sidecar" => storeDep "gossip_blob_sidecar"
  | "gossip_data_column_sidecar" => storeDep "gossip_data_column_sidecar"
  | "gossip_partial_data_column_sidecar" => storeDep "gossip_partial_data_column_sidecar"
  | "gossip_execution_payload_envelope" => storeDep "gossip_execution_payload_envelope"
  | "gossip_payload_attestation_message" => storeDep "gossip_payload_attestation_message"
  -- A bid case interleaves `proposer_preferences_`, `execution_payload_envelope_` and
  -- `execution_payload_bid_` messages (the bid reads what they put in `Seen`), so the driver's
  -- single-prefix check is off (empty prefix) and the handler checks the three prefixes itself.
  | "gossip_execution_payload_bid" =>
    some (storeGossipHandler "execution_payload_bid" "" "execution_payload_bid")
  | "gossip_proposer_preferences" => storeDep "gossip_proposer_preferences"
  | _ => none

#guard (gossipHandlers "gossip_voluntary_exit").map (·.filePrefix) == some "voluntary_exit_"
#guard (gossipHandlers "gossip_sync_committee_message").map (·.topic) == some "sync_committee"
#guard (gossipHandlers "gossip_beacon_block").map (·.filePrefix) == some "block_"
#guard (gossipHandlers "gossip_execution_payload_bid").map (·.filePrefix) == some ""

end JauneConsensus.Harness
