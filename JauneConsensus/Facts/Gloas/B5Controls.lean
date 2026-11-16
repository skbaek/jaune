import JauneConsensus.Facts.JointGloas
import JauneConsensus.Facts.Gloas.B5Witnesses

/-!
# B5 envelope mutant control (goal `eip8282-gloas-cross-layer-v1`, statements.md §0.3, B5 (2))

Function-level (**F**) negative control for the withdrawals clause of the envelope check.

* `verifyEnvelopeNoWithdrawals` is U6's `verifyExecutionPayloadEnvelopeB` with the one
  withdrawals assert (`hash_tree_root(payload.withdrawals) ==
  hash_tree_root(state.payload_expected_withdrawals)`) removed: the other 11 of its 12 checks, in
  spec order.
* `mutantEnvelope st e0 ws t` is an envelope built from a state `st`: every field a check compares
  with the state is copied from the state (`beacon_block_root := latestBlockRoot st`, the bid's
  fields, `slot`, `latest_block_hash`), and its payload carries the arbitrary withdrawals `ws`.
* `mutant_accepts` (symbolic in the state): at `bls = false` with the stub engine `fun _ => true`,
  the mutant accepts `mutantEnvelope st e0 ws t` for **every** `ws`, given the four lookups succeed
  and the bid commits to the envelope's requests root. No root is evaluated: the two
  root-mentioning checks compare a term with itself.
* `mutant_admits_other_address` (closed): on a minimal-preset state whose only expected
  withdrawal pays address 1, the mutant accepts an envelope whose only withdrawal pays address 2,
  so `¬ WithdrawalsMatchExpected`; the real seam check `verifyEnvelopeG` (G2's list `require`,
  `verifyEnvelopeG_rejects_of_withdrawals_ne`) and the joint envelope arm `deliver` reject that
  same envelope under every configuration, chain and BLS setting. The state's
  `hash_tree_root` occurs only symbolically; the kernel never evaluates it.
-/

namespace JauneConsensus.Facts.Gloas.B5Controls

open JauneConsensus JauneConsensus.Gloas

variable {P : Preset}

/-- **B5 mutant**: `verify_execution_payload_envelope` (U6's `verifyExecutionPayloadEnvelopeB`)
without the withdrawals-root assert; the other eleven checks are unchanged and in spec order. -/
def verifyEnvelopeNoWithdrawals (bls : Bool) (cfg : Config)
    (engine : JauneConsensus.Gloas.NewPayloadRequest P → Bool) (state : JauneConsensus.Gloas.BeaconState P)
    (signedEnvelope : SignedExecutionPayloadEnvelope P) : M Unit := do
  let site := "verify_execution_payload_envelope"
  let envelope := signedEnvelope.message
  let payload := envelope.payload
  require (← verifyExecutionPayloadEnvelopeSignatureB bls state signedEnvelope)
    s!"{site}: signature"
  require (envelope.beacon_block_root == latestBlockRoot state) s!"{site}: beacon_block_root"
  require (envelope.parent_beacon_block_root == state.latest_block_header.parent_root)
    s!"{site}: parent_beacon_block_root"
  let bid := state.latest_execution_payload_bid
  require (envelope.builder_index == bid.builder_index) s!"{site}: builder_index"
  require (payload.prev_randao == bid.prev_randao) s!"{site}: prev_randao"
  require (payload.gas_limit == bid.gas_limit) s!"{site}: gas_limit"
  require (payload.block_hash == bid.block_hash) s!"{site}: block_hash"
  require (Ssz.hashTreeRoot envelope.execution_requests == bid.execution_requests_root)
    s!"{site}: execution_requests_root"
  require (payload.slot_number == state.slot) s!"{site}: slot_number"
  require (payload.parent_hash == state.latest_block_hash) s!"{site}: parent_hash"
  require (payload.timestamp == (← JauneConsensus.Gloas.computeTimeAtSlot cfg state state.slot)) s!"{site}: timestamp"
  -- the withdrawals-root assert is removed here
  require (engine (← envelopeNewPayloadRequest state signedEnvelope)) s!"{site}: execution engine"

/-- The envelope built from `st`: every field a check compares with the state is the state's,
the payload's timestamp is `t`, its withdrawals are `ws`; the rest is the template `e0`. -/
def mutantEnvelope (st : JauneConsensus.Gloas.BeaconState P) (e0 : SignedExecutionPayloadEnvelope P)
    (ws : ProgressiveListR JauneConsensus.Withdrawal) (t : U64) : SignedExecutionPayloadEnvelope P :=
  { e0 with message :=
    { e0.message with
      beacon_block_root := latestBlockRoot st
      parent_beacon_block_root := st.latest_block_header.parent_root
      builder_index := st.latest_execution_payload_bid.builder_index
      payload :=
        { e0.message.payload with
          prev_randao := st.latest_execution_payload_bid.prev_randao
          gas_limit := st.latest_execution_payload_bid.gas_limit
          block_hash := st.latest_execution_payload_bid.block_hash
          slot_number := st.slot
          parent_hash := st.latest_block_hash
          timestamp := t
          withdrawals := ws } } }

/-- The mutant succeeds exactly when the eleven remaining conjuncts of `EnvelopeChecksB` hold
(every field but `withdrawalsRoot`). -/
theorem verifyEnvelopeNoWithdrawals_ok_iff {bls : Bool} {cfg : Config}
    {engine : JauneConsensus.Gloas.NewPayloadRequest P → Bool} {state : JauneConsensus.Gloas.BeaconState P}
    {e : SignedExecutionPayloadEnvelope P} :
    verifyEnvelopeNoWithdrawals bls cfg engine state e = .ok () ↔
      verifyExecutionPayloadEnvelopeSignatureB bls state e = .ok true ∧
      e.message.beacon_block_root = latestBlockRoot state ∧
      e.message.parent_beacon_block_root = state.latest_block_header.parent_root ∧
      e.message.builder_index = state.latest_execution_payload_bid.builder_index ∧
      e.message.payload.prev_randao = state.latest_execution_payload_bid.prev_randao ∧
      e.message.payload.gas_limit = state.latest_execution_payload_bid.gas_limit ∧
      e.message.payload.block_hash = state.latest_execution_payload_bid.block_hash ∧
      Ssz.hashTreeRoot e.message.execution_requests =
        state.latest_execution_payload_bid.execution_requests_root ∧
      e.message.payload.slot_number = state.slot ∧
      e.message.payload.parent_hash = state.latest_block_hash ∧
      JauneConsensus.Gloas.computeTimeAtSlot cfg state state.slot =
        .ok e.message.payload.timestamp ∧
      ∃ req, envelopeNewPayloadRequest state e = .ok req ∧ engine req = true := by
  simp only [verifyEnvelopeNoWithdrawals, Jaune.Except.bind_eq_ok_iff, require_eq_ok_iff,
    exists_unit_iff, beq_iff_eq]
  constructor
  · rintro ⟨b, hsig, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, t, ht, rfl, heng⟩
    exact ⟨hsig, h1, h2, h3, h4, h5, h6, h7, h8, h9, ht, heng⟩
  · rintro ⟨hsig, h1, h2, h3, h4, h5, h6, h7, h8, h9, ht, heng⟩
    exact ⟨true, hsig, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, ht, rfl, heng⟩

/-- **The mutant accepts any withdrawals** (symbolic in the state). At `bls = false` with the stub
engine `fun _ => true`, when the signing key, the domain, the slot time and the versioned hashes
are defined and the bid commits to the template's requests root, the mutant accepts the envelope
built from `st` whatever its withdrawals `ws` are. No root is evaluated. -/
theorem mutant_accepts (cfg : Config) (st : JauneConsensus.Gloas.BeaconState P)
    (e0 : SignedExecutionPayloadEnvelope P) (ws : ProgressiveListR JauneConsensus.Withdrawal)
    {pk : BLSPubkey} {d : Domain} {t : U64}
    {vh : SszList Bytes32 P.MAX_BLOB_COMMITMENTS_PER_BLOCK}
    (hpk : builderSigningPubkey st st.latest_execution_payload_bid.builder_index = .ok pk)
    (hdom : JauneConsensus.Gloas.getDomain st DOMAIN_BEACON_BUILDER = .ok d)
    (htime : JauneConsensus.Gloas.computeTimeAtSlot cfg st st.slot = .ok t)
    (hvh : blobVersionedHashes (P := P) st.latest_execution_payload_bid.blob_kzg_commitments =
      .ok vh)
    (hreq : st.latest_execution_payload_bid.execution_requests_root =
      Ssz.hashTreeRoot e0.message.execution_requests) :
    verifyEnvelopeNoWithdrawals false cfg (fun _ => true) st (mutantEnvelope st e0 ws t) =
      .ok () := by
  have hsig := verifyExecutionPayloadEnvelopeSignatureB_false
    (signedEnvelope := mutantEnvelope st e0 ws t) hpk hdom
  have hnpr : envelopeNewPayloadRequest st (mutantEnvelope st e0 ws t) =
      .ok { execution_payload := (mutantEnvelope st e0 ws t).message.payload
            versioned_hashes := vh
            parent_beacon_block_root := (mutantEnvelope st e0 ws t).message.parent_beacon_block_root
            execution_requests := (mutantEnvelope st e0 ws t).message.execution_requests } := by
    unfold envelopeNewPayloadRequest
    rw [hvh]
    rfl
  refine verifyEnvelopeNoWithdrawals_ok_iff.mpr ⟨hsig, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    _, hnpr, rfl⟩
  all_goals simp only [mutantEnvelope]
  · exact hreq.symm
  · exact htime

/-! ## The closed witness -/

section Closed

local instance {α : Type} [Inhabited α] {n : Nat} : Inhabited (SszVector α n) :=
  ⟨⟨Array.replicate n default, Array.size_replicate⟩⟩
local instance {α : Type} {n : Nat} : Inhabited (SszList α n) := ⟨⟨#[], Nat.zero_le _⟩⟩
local instance {s : Spine} {α : Type} : Inhabited (ProgressiveListS s α) := ⟨⟨#[]⟩⟩
local instance : Inhabited ProgressiveByteList := ⟨⟨default⟩⟩

/-- The minimal preset. -/
abbrev Pm : Preset := Preset.minimal

/-- The template envelope: every field at its zero value. -/
def zEnvelope : SignedExecutionPayloadEnvelope Pm where
  message :=
    { payload := by constructor <;> exact default
      execution_requests := by constructor <;> exact default
      builder_index := default
      beacon_block_root := default
      parent_beacon_block_root := default }
  signature := default

/-- The withdrawal the state expects: 5 gwei to address 1. -/
def wExpected : JauneConsensus.Withdrawal :=
  { index := U64.zero, validator_index := U64.zero, address := ((0 : UInt32), (0, 1)),
    amount := U64.lit 5 }

/-- The withdrawal the envelope carries instead: the same 5 gwei to address 2. -/
def wOther : JauneConsensus.Withdrawal := { wExpected with address := ((0 : UInt32), (0, 2)) }

/-- B5Witnesses' `satState` (builder 0 registered, every other field at zero) with one expected
withdrawal, to address 1, and a zero bid for builder 0 with no blob commitments, committing to the
template's requests root (a symbolic term; it is never evaluated). -/
def ctrlState : JauneConsensus.Gloas.BeaconState Pm :=
  { Facts.Gloas.B5Witnesses.satState with
    payload_expected_withdrawals := ProgressiveListS.ofArray #[wExpected]
    latest_execution_payload_bid :=
      { parent_block_hash := default, parent_block_root := default, block_hash := default,
        prev_randao := default, fee_recipient := default, gas_limit := U64.zero,
        builder_index := U64.zero, slot := U64.zero, value := U64.zero,
        execution_payment := U64.zero, blob_kzg_commitments := ProgressiveListS.ofArray #[],
        execution_requests_root := Ssz.hashTreeRoot zEnvelope.message.execution_requests } }

/-- The envelope built from `ctrlState`, paying `wOther`. -/
def ctrlEnvelope : SignedExecutionPayloadEnvelope Pm :=
  mutantEnvelope ctrlState zEnvelope (ProgressiveListS.ofArray #[wOther]) U64.zero

/-- **B5 control (2): the mutant admits another address.** On `ctrlState` (expected: 5 gwei to
address 1), the mutant without the withdrawals clause, at `bls = false` with the stub engine
`fun _ => true`, accepts `ctrlEnvelope`, whose only withdrawal pays address 2, which no expected
withdrawal names, so `¬ WithdrawalsMatchExpected`. The real seam check `verifyEnvelopeG` and the
envelope arm `deliver` reject that same envelope, under every chain configuration, BLS setting,
chain and parent payload. -/
theorem mutant_admits_other_address :
    verifyEnvelopeNoWithdrawals false Config.minimal (fun _ => true) ctrlState ctrlEnvelope =
      .ok () ∧
    ¬ WithdrawalsMatchExpected ctrlState ctrlEnvelope ∧
    (∃ w ∈ ctrlEnvelope.message.payload.withdrawals.toArray.toList,
      ∀ x ∈ ctrlState.payload_expected_withdrawals.toArray.toList, x.address ≠ w.address) ∧
    (∀ (cfg : Jaune.ChainConfig) (bls : Bool) (exec : Jaune.BlockChain)
        (r : JauneConsensus.Gloas.NewPayloadRequest Pm × Jaune.BlockChain),
      verifyEnvelopeG cfg Config.minimal bls ctrlState exec ctrlEnvelope ≠ .ok r) ∧
    (∀ (cfg : Jaune.ChainConfig) (bls : Bool) (exec : Jaune.BlockChain) (parent : ParentPayload Pm)
        (s' : GJointState Pm),
      deliver cfg Config.minimal bls (.gloas ctrlState exec parent) ctrlEnvelope ≠ .ok s') := by
  have hne : ¬ WithdrawalsMatchExpected ctrlState ctrlEnvelope := by
    unfold WithdrawalsMatchExpected
    simp only [ctrlEnvelope, mutantEnvelope, ctrlState, ProgressiveListS.ofArray]
    decide
  have hvh : blobVersionedHashes (P := Pm)
      ctrlState.latest_execution_payload_bid.blob_kzg_commitments = .ok ⟨#[], Nat.zero_le _⟩ := by
    unfold blobVersionedHashes
    simp [ctrlState, ProgressiveListS.ofArray, pure, Except.pure]
  refine ⟨mutant_accepts _ _ _ _ (pk := Facts.Gloas.B5Witnesses.satBuilder.pubkey)
    rfl rfl rfl hvh rfl, hne,
    ⟨wOther, ?_, ?_⟩, fun _ _ _ r => verifyEnvelopeG_rejects_of_withdrawals_ne hne r,
    fun _ _ _ _ s' => deliver_rejects_of_withdrawals_ne hne s'⟩
  · simp [ctrlEnvelope, mutantEnvelope, ProgressiveListS.ofArray]
  · intro x hx
    simp only [ctrlState, ProgressiveListS.ofArray, List.mem_singleton] at hx
    subst hx
    decide

end Closed

end JauneConsensus.Facts.Gloas.B5Controls
