import JauneConsensus.GloasAccessors

/-!
# Gloas execution payload envelope verification (goal `eip8282-gloas-cross-layer-v1`, unit U6)

`verify_execution_payload_envelope_signature` (`specs/gloas/beacon-chain.md`, "Execution
payload") and `verify_execution_payload_envelope` (`specs/gloas/fork-choice.md`) of
`ethereum/consensus-specs` `v1.7.0-beta.4`, the check the cross-layer seam consumes.

* **BLS is switched, real when on.** The `B` forms (`verifyExecutionPayloadEnvelopeSignatureB`,
  `verifyExecutionPayloadEnvelopeB`, `EnvelopeChecksB`) take the pyspec `bls_active` switch and
  check the signature with `Signing.lean`'s `blsVerify bls` (`Crypto/BLSSig.lean`'s `verify`, the
  spec's `bls.Verify`, when `bls = true`; accept when `bls = false`, as the Electra/Fulu switch
  does). The unswitched names are the `B` forms at `true`, by definition:
  `verifyExecutionPayloadEnvelopeSignature_eq_blsVerify` states the unswitched check is
  `blsVerify true`.
* **The execution engine is a parameter**, `engine : NewPayloadRequest P → Bool`, standing for
  `execution_engine.verify_and_notify_new_payload`. It receives the spec's own Gloas
  `NewPayloadRequest` container. Wiring it to Jaune's Amsterdam execution is the seam's (G2) job.
* **One `require` per spec `assert`, in spec order**, and `EnvelopeChecksB` has one named field
  per `assert`, in the same order; `verifyExecutionPayloadEnvelopeB_ok_iff` says the function
  succeeds exactly when every field holds (`verifyExecutionPayloadEnvelope_ok_iff` at `true`).

**Roots and lists.** The spec compares the withdrawals and the execution requests only through
`hash_tree_root`. `WithdrawalsMatchExpected` is the list form of the withdrawals check, and
`withdrawalsRoot_of_withdrawalsMatchExpected` is the direction that holds: equal lists give equal
roots. The converse (equal roots give equal lists) would need `hash_tree_root` to be injective,
which is the SSZ collision caveat: it is **not provable** and is not claimed. The same holds for the
requests (`ExecutionRequests.lists`, `ExecutionRequests.hashTreeRoot_eq_of_lists_eq` in
`GloasAccessors.lean`): the bid commits only to their root.
-/

namespace JauneConsensus.Gloas

open Jaune

variable {P : Preset}

/-! ## `verify_execution_payload_envelope_signature` -/

/-- `verify_execution_payload_envelope_signature(state, signed_envelope)` under the BLS switch
`bls`: the envelope's signing root under `get_domain(state, DOMAIN_BEACON_BUILDER)`, verified
with `blsVerify bls` (`bls.Verify` when `bls = true`) against the self-build proposer's validator
key or the builder's key. Raises (`Reject.index`) when the index is out of range, whatever `bls`
is. -/
def verifyExecutionPayloadEnvelopeSignatureB (bls : Bool) (state : BeaconState P)
    (signedEnvelope : SignedExecutionPayloadEnvelope P) : M Bool := do
  let pubkey ← builderSigningPubkey state signedEnvelope.message.builder_index
  let signingRoot :=
    computeSigningRoot signedEnvelope.message (← getDomain state DOMAIN_BEACON_BUILDER)
  pure (blsVerify bls pubkey signingRoot signedEnvelope.signature)

/-- `verify_execution_payload_envelope_signature(state, signed_envelope)` with real BLS: the
switched check at `bls = true`. -/
def verifyExecutionPayloadEnvelopeSignature (state : BeaconState P)
    (signedEnvelope : SignedExecutionPayloadEnvelope P) : M Bool :=
  verifyExecutionPayloadEnvelopeSignatureB true state signedEnvelope

/-- With the switch **off**, the signature check (the `EnvelopeChecksB.signature` conjunct at
`bls = false`) holds whenever the key lookup and the domain succeed; the spec's own raises
remain. -/
theorem verifyExecutionPayloadEnvelopeSignatureB_false {state : BeaconState P}
    {signedEnvelope : SignedExecutionPayloadEnvelope P} {pubkey : BLSPubkey} {domain : Domain}
    (hpk : builderSigningPubkey state signedEnvelope.message.builder_index = .ok pubkey)
    (hdom : getDomain state DOMAIN_BEACON_BUILDER = .ok domain) :
    verifyExecutionPayloadEnvelopeSignatureB false state signedEnvelope = .ok true := by
  simp [verifyExecutionPayloadEnvelopeSignatureB, hpk, hdom, blsVerify]
  rfl

/-- The signature check is the switched `blsVerify` with the switch **on**. -/
theorem verifyExecutionPayloadEnvelopeSignature_eq_blsVerify (state : BeaconState P)
    (signedEnvelope : SignedExecutionPayloadEnvelope P) :
    verifyExecutionPayloadEnvelopeSignature state signedEnvelope = (do
      let pubkey ← builderSigningPubkey state signedEnvelope.message.builder_index
      let domain ← getDomain state DOMAIN_BEACON_BUILDER
      pure (blsVerify true pubkey (computeSigningRoot signedEnvelope.message domain)
        signedEnvelope.signature)) := by
  rfl

/-! ## The `NewPayloadRequest` -/

/-- The `NewPayloadRequest` `verify_execution_payload_envelope` hands the engine: the payload,
the versioned hashes of the committed bid's `blob_kzg_commitments`, the envelope's
`parent_beacon_block_root` and `execution_requests`. Raises only when the versioned hashes
exceed `MAX_BLOB_COMMITMENTS_PER_BLOCK`. -/
def envelopeNewPayloadRequest (state : BeaconState P)
    (signedEnvelope : SignedExecutionPayloadEnvelope P) : M (NewPayloadRequest P) := do
  let envelope := signedEnvelope.message
  let versionedHashes ←
    blobVersionedHashes (P := P) state.latest_execution_payload_bid.blob_kzg_commitments
  pure { execution_payload := envelope.payload
         versioned_hashes := versionedHashes
         parent_beacon_block_root := envelope.parent_beacon_block_root
         execution_requests := envelope.execution_requests }

/-! ## `verify_execution_payload_envelope` -/

/-- `verify_execution_payload_envelope(state, signed_envelope, execution_engine)`
(`specs/gloas/fork-choice.md`), with `engine` for
`execution_engine.verify_and_notify_new_payload`, under the BLS switch `bls`. One `require` per
`assert`, in spec order. -/
def verifyExecutionPayloadEnvelopeB (bls : Bool) (cfg : Config)
    (engine : NewPayloadRequest P → Bool) (state : BeaconState P)
    (signedEnvelope : SignedExecutionPayloadEnvelope P) : M Unit := do
  let site := "verify_execution_payload_envelope"
  let envelope := signedEnvelope.message
  let payload := envelope.payload
  -- Verify signature
  require (← verifyExecutionPayloadEnvelopeSignatureB bls state signedEnvelope)
    s!"{site}: signature"
  -- Verify consistency with the beacon block
  require (envelope.beacon_block_root == latestBlockRoot state) s!"{site}: beacon_block_root"
  require (envelope.parent_beacon_block_root == state.latest_block_header.parent_root)
    s!"{site}: parent_beacon_block_root"
  -- Verify consistency with the committed bid
  let bid := state.latest_execution_payload_bid
  require (envelope.builder_index == bid.builder_index) s!"{site}: builder_index"
  require (payload.prev_randao == bid.prev_randao) s!"{site}: prev_randao"
  require (payload.gas_limit == bid.gas_limit) s!"{site}: gas_limit"
  require (payload.block_hash == bid.block_hash) s!"{site}: block_hash"
  require (Ssz.hashTreeRoot envelope.execution_requests == bid.execution_requests_root)
    s!"{site}: execution_requests_root"
  -- Verify the execution payload is valid
  require (payload.slot_number == state.slot) s!"{site}: slot_number"
  require (payload.parent_hash == state.latest_block_hash) s!"{site}: parent_hash"
  require (payload.timestamp == (← computeTimeAtSlot cfg state state.slot)) s!"{site}: timestamp"
  require (Ssz.hashTreeRoot payload.withdrawals ==
      Ssz.hashTreeRoot state.payload_expected_withdrawals) s!"{site}: withdrawals root"
  -- Compute versioned hashes, then the engine
  require (engine (← envelopeNewPayloadRequest state signedEnvelope)) s!"{site}: execution engine"

/-- `verify_execution_payload_envelope` with real BLS: the switched check at `bls = true`. -/
def verifyExecutionPayloadEnvelope (cfg : Config) (engine : NewPayloadRequest P → Bool)
    (state : BeaconState P) (signedEnvelope : SignedExecutionPayloadEnvelope P) : M Unit :=
  verifyExecutionPayloadEnvelopeB true cfg engine state signedEnvelope

/-- The named conjuncts of `verify_execution_payload_envelope`, one per spec `assert`, in spec
order. The two root checks are the spec's (`hash_tree_root` comparisons); their list forms are
`WithdrawalsMatchExpected` and `ExecutionRequests.lists`. Only `signature` depends on the BLS
switch `bls`. -/
structure EnvelopeChecksB (bls : Bool) (cfg : Config) (engine : NewPayloadRequest P → Bool)
    (state : BeaconState P) (signedEnvelope : SignedExecutionPayloadEnvelope P) : Prop where
  /-- `assert verify_execution_payload_envelope_signature(state, signed_envelope)`. -/
  signature : verifyExecutionPayloadEnvelopeSignatureB bls state signedEnvelope = .ok true
  /-- `assert envelope.beacon_block_root == hash_tree_root(header)`. -/
  beaconBlockRoot : signedEnvelope.message.beacon_block_root = latestBlockRoot state
  /-- `assert envelope.parent_beacon_block_root == state.latest_block_header.parent_root`. -/
  parentBeaconBlockRoot :
    signedEnvelope.message.parent_beacon_block_root = state.latest_block_header.parent_root
  /-- `assert envelope.builder_index == bid.builder_index`. -/
  builderIndex :
    signedEnvelope.message.builder_index = state.latest_execution_payload_bid.builder_index
  /-- `assert payload.prev_randao == bid.prev_randao`. -/
  prevRandao :
    signedEnvelope.message.payload.prev_randao = state.latest_execution_payload_bid.prev_randao
  /-- `assert payload.gas_limit == bid.gas_limit`. -/
  gasLimit :
    signedEnvelope.message.payload.gas_limit = state.latest_execution_payload_bid.gas_limit
  /-- `assert payload.block_hash == bid.block_hash`. -/
  blockHash :
    signedEnvelope.message.payload.block_hash = state.latest_execution_payload_bid.block_hash
  /-- `assert hash_tree_root(envelope.execution_requests) == bid.execution_requests_root`. -/
  executionRequestsRoot :
    Ssz.hashTreeRoot signedEnvelope.message.execution_requests =
      state.latest_execution_payload_bid.execution_requests_root
  /-- `assert payload.slot_number == state.slot`. -/
  slotNumber : signedEnvelope.message.payload.slot_number = state.slot
  /-- `assert payload.parent_hash == state.latest_block_hash`. -/
  parentHash : signedEnvelope.message.payload.parent_hash = state.latest_block_hash
  /-- `assert payload.timestamp == compute_time_at_slot(state.genesis_time, state.slot)`
  (`compute_time_at_slot` itself raises on overflow, so it must succeed with that value). -/
  timestamp : computeTimeAtSlot cfg state state.slot = .ok signedEnvelope.message.payload.timestamp
  /-- `assert hash_tree_root(payload.withdrawals) ==
  hash_tree_root(state.payload_expected_withdrawals)`. -/
  withdrawalsRoot :
    Ssz.hashTreeRoot signedEnvelope.message.payload.withdrawals =
      Ssz.hashTreeRoot state.payload_expected_withdrawals
  /-- `assert execution_engine.verify_and_notify_new_payload(NewPayloadRequest(...))`, with the
  versioned hashes computed (which raises past `MAX_BLOB_COMMITMENTS_PER_BLOCK`). -/
  engine : ∃ req, envelopeNewPayloadRequest state signedEnvelope = .ok req ∧ engine req = true

/-- The named conjuncts with real BLS: `EnvelopeChecksB` at `bls = true`. -/
abbrev EnvelopeChecks (cfg : Config) (engine : NewPayloadRequest P → Bool)
    (state : BeaconState P) (signedEnvelope : SignedExecutionPayloadEnvelope P) : Prop :=
  EnvelopeChecksB true cfg engine state signedEnvelope

/-! ## The characterization -/

/-- `verify_execution_payload_envelope` under the switch `bls` succeeds exactly when every named
conjunct holds. -/
theorem verifyExecutionPayloadEnvelopeB_ok_iff {bls : Bool} {cfg : Config}
    {engine : NewPayloadRequest P → Bool} {state : BeaconState P}
    {signedEnvelope : SignedExecutionPayloadEnvelope P} :
    verifyExecutionPayloadEnvelopeB bls cfg engine state signedEnvelope = .ok () ↔
      EnvelopeChecksB bls cfg engine state signedEnvelope := by
  simp only [verifyExecutionPayloadEnvelopeB, Except.bind_eq_ok_iff, require_eq_ok_iff,
    exists_unit_iff, beq_iff_eq]
  constructor
  · rintro ⟨b, hsig, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, t, ht, rfl, h10, heng⟩
    exact ⟨hsig, h1, h2, h3, h4, h5, h6, h7, h8, h9, ht, h10, heng⟩
  · rintro ⟨hsig, h1, h2, h3, h4, h5, h6, h7, h8, h9, ht, h10, heng⟩
    exact ⟨true, hsig, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, ht, rfl, h10, heng⟩

/-- `verify_execution_payload_envelope` with real BLS succeeds exactly when every named conjunct
holds. -/
theorem verifyExecutionPayloadEnvelope_ok_iff {cfg : Config} {engine : NewPayloadRequest P → Bool}
    {state : BeaconState P} {signedEnvelope : SignedExecutionPayloadEnvelope P} :
    verifyExecutionPayloadEnvelope cfg engine state signedEnvelope = .ok () ↔
      EnvelopeChecks cfg engine state signedEnvelope :=
  verifyExecutionPayloadEnvelopeB_ok_iff

/-! ## List-level predicates for the seam -/

/-- The list form of the withdrawals check: the payload's withdrawals are
`state.payload_expected_withdrawals`, element for element. The spec compares only their
`hash_tree_root`s; this implies that comparison (`withdrawalsRoot_of_withdrawalsMatchExpected`),
and the converse is the SSZ collision caveat, which is not provable and not claimed. -/
def WithdrawalsMatchExpected (state : BeaconState P)
    (signedEnvelope : SignedExecutionPayloadEnvelope P) : Prop :=
  signedEnvelope.message.payload.withdrawals.toArray.toList =
    state.payload_expected_withdrawals.toArray.toList

/-- List equality of the withdrawals gives the spec's root equality. -/
theorem withdrawalsRoot_of_withdrawalsMatchExpected {state : BeaconState P}
    {signedEnvelope : SignedExecutionPayloadEnvelope P}
    (h : WithdrawalsMatchExpected state signedEnvelope) :
    Ssz.hashTreeRoot signedEnvelope.message.payload.withdrawals =
      Ssz.hashTreeRoot state.payload_expected_withdrawals :=
  ProgressiveListS.hashTreeRoot_eq_of_toList_eq h

/-- The envelope's execution requests as the five request lists (the list-level value the seam
compares with what the execution layer produced). -/
def envelopeRequestLists (signedEnvelope : SignedExecutionPayloadEnvelope P) :
    List DepositRequest × List WithdrawalRequest × List ConsolidationRequest ×
      List BuilderDepositRequest × List BuilderExitRequest :=
  signedEnvelope.message.execution_requests.lists

/-- The envelope's execution requests in `get_execution_requests_list` form (what the engine's
`NewPayloadRequest.execution_requests` stands for on the execution side). -/
def envelopeRequestsList (signedEnvelope : SignedExecutionPayloadEnvelope P) :
    ExecutionRequestsList :=
  getExecutionRequestsList signedEnvelope.message.execution_requests

/-- If the envelope's request lists are those of requests `r` whose root the bid commits to, the
envelope passes the requests-root check (the easy direction; the converse is the collision
caveat). -/
theorem executionRequestsRoot_of_lists_eq {state : BeaconState P}
    {signedEnvelope : SignedExecutionPayloadEnvelope P} {r : ExecutionRequests}
    (hlists : envelopeRequestLists signedEnvelope = r.lists)
    (hroot : Ssz.hashTreeRoot r = state.latest_execution_payload_bid.execution_requests_root) :
    Ssz.hashTreeRoot signedEnvelope.message.execution_requests =
      state.latest_execution_payload_bid.execution_requests_root := by
  rw [ExecutionRequests.hashTreeRoot_eq_of_lists_eq hlists, hroot]

/-! ## Rejections (kernel-checked controls for the seam) -/

/-- An envelope whose withdrawals root differs from that of `payload_expected_withdrawals` is
rejected, under either setting of the BLS switch. -/
theorem verifyExecutionPayloadEnvelopeB_rejects_of_withdrawalsRoot_ne {bls : Bool} {cfg : Config}
    {engine : NewPayloadRequest P → Bool} {state : BeaconState P}
    {signedEnvelope : SignedExecutionPayloadEnvelope P}
    (hne : Ssz.hashTreeRoot signedEnvelope.message.payload.withdrawals ≠
      Ssz.hashTreeRoot state.payload_expected_withdrawals) :
    verifyExecutionPayloadEnvelopeB bls cfg engine state signedEnvelope ≠ .ok () := fun h =>
  hne (verifyExecutionPayloadEnvelopeB_ok_iff.mp h).withdrawalsRoot

/-- An envelope whose withdrawals root differs from that of `payload_expected_withdrawals` is
rejected. -/
theorem verifyExecutionPayloadEnvelope_rejects_of_withdrawalsRoot_ne {cfg : Config}
    {engine : NewPayloadRequest P → Bool} {state : BeaconState P}
    {signedEnvelope : SignedExecutionPayloadEnvelope P}
    (hne : Ssz.hashTreeRoot signedEnvelope.message.payload.withdrawals ≠
      Ssz.hashTreeRoot state.payload_expected_withdrawals) :
    verifyExecutionPayloadEnvelope cfg engine state signedEnvelope ≠ .ok () := fun h =>
  hne (verifyExecutionPayloadEnvelope_ok_iff.mp h).withdrawalsRoot

/-- An envelope whose withdrawals differ, as lists, from `payload_expected_withdrawals` is
accepted only under an SSZ `hash_tree_root` collision: acceptance forces equal roots. -/
theorem withdrawalsRoot_eq_of_verifyExecutionPayloadEnvelope_ok {cfg : Config}
    {engine : NewPayloadRequest P → Bool} {state : BeaconState P}
    {signedEnvelope : SignedExecutionPayloadEnvelope P}
    (h : verifyExecutionPayloadEnvelope cfg engine state signedEnvelope = .ok ()) :
    Ssz.hashTreeRoot signedEnvelope.message.payload.withdrawals =
      Ssz.hashTreeRoot state.payload_expected_withdrawals :=
  (verifyExecutionPayloadEnvelope_ok_iff.mp h).withdrawalsRoot

/-- An envelope whose execution requests root differs from the committed bid's
`execution_requests_root` is rejected, under either setting of the BLS switch. -/
theorem verifyExecutionPayloadEnvelopeB_rejects_of_requestsRoot_ne {bls : Bool} {cfg : Config}
    {engine : NewPayloadRequest P → Bool} {state : BeaconState P}
    {signedEnvelope : SignedExecutionPayloadEnvelope P}
    (hne : Ssz.hashTreeRoot signedEnvelope.message.execution_requests ≠
      state.latest_execution_payload_bid.execution_requests_root) :
    verifyExecutionPayloadEnvelopeB bls cfg engine state signedEnvelope ≠ .ok () := fun h =>
  hne (verifyExecutionPayloadEnvelopeB_ok_iff.mp h).executionRequestsRoot

/-- An envelope whose execution requests root differs from the committed bid's
`execution_requests_root` is rejected. -/
theorem verifyExecutionPayloadEnvelope_rejects_of_requestsRoot_ne {cfg : Config}
    {engine : NewPayloadRequest P → Bool} {state : BeaconState P}
    {signedEnvelope : SignedExecutionPayloadEnvelope P}
    (hne : Ssz.hashTreeRoot signedEnvelope.message.execution_requests ≠
      state.latest_execution_payload_bid.execution_requests_root) :
    verifyExecutionPayloadEnvelope cfg engine state signedEnvelope ≠ .ok () := fun h =>
  hne (verifyExecutionPayloadEnvelope_ok_iff.mp h).executionRequestsRoot

end JauneConsensus.Gloas
