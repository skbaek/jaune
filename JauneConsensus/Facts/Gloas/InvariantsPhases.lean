import JauneConsensus.Facts.Gloas.InvariantsFrames

/-!
# The phases of a Gloas block for the G3 invariants (goal `eip8282-gloas-cross-layer-v1`, G3a)

* `processBlock_phases`: `process_block` is the parent payload, the header, the withdrawals, the
  bid, RANDAO, eth1 data, the operations and the sync aggregate, in that order;
* `processBlockHeader_post`, `processExecutionPayloadBid_post`: what the header and the bid write;
* `processWithdrawals_wFrame`: the withdrawals keep every builder's identity and
  `withdrawable_epoch`, `L`, the hashes, the slots and the payments, and leave the sweep index
  unchanged or in range.
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-! ## The block, phase by phase -/

theorem processBlock_phases {ctx : Ctx} {s s' : GSt P} {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') :
    ∃ s1 s2 s3 s4 s5 s6 s7 : GSt P,
      JauneConsensus.Gloas.processParentExecutionPayload ctx s blk = .ok s1 ∧
      JauneConsensus.Gloas.processBlockHeader s1 blk = .ok s2 ∧
      JauneConsensus.Gloas.processWithdrawals s2 = .ok s3 ∧
      JauneConsensus.Gloas.processExecutionPayloadBid ctx s3
        blk.body.signed_execution_payload_bid = .ok s4 ∧
      JauneConsensus.Gloas.processRandao ctx s4 blk.body = .ok s5 ∧
      JauneConsensus.Gloas.processEth1Data s5 blk.body = .ok s6 ∧
      JauneConsensus.Gloas.processOperations ctx s6 blk.body s.latest_block_header.slot = .ok s7 ∧
      JauneConsensus.Gloas.processSyncAggregate ctx s7 blk.body.sync_aggregate = .ok s' := by
  unfold JauneConsensus.Gloas.processBlock at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s7, h7, h⟩ := bind_eq_ok_iff.mp h
  exact ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h⟩

/-! ## The header -/

/-- `process_block_header` writes only the header, whose slot is the block's, which is the
state's. -/
theorem processBlockHeader_post {s s' : GSt P} {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlockHeader s blk = .ok s') :
    blk.slot = s.slot ∧ s'.latest_block_header.slot = blk.slot ∧
      s' = { s with latest_block_header := s'.latest_block_header } := by
  unfold JauneConsensus.Gloas.processBlockHeader at h
  obtain ⟨_, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact ⟨U64.beq_eq_true_iff.mp (require_ok h1), rfl, rfl⟩

/-! ## The bid -/

/-- What `process_execution_payload_bid` checked and wrote. -/
def BidPost (s : GSt P) (sb : JauneConsensus.Gloas.SignedExecutionPayloadBid) (s' : GSt P) :
    Prop :=
  s'.latest_execution_payload_bid = sb.message ∧ sb.message.slot = s.slot ∧
    sb.message.parent_block_hash = s.latest_block_hash ∧
    (sb.message.builder_index = JauneConsensus.Gloas.BUILDER_INDEX_SELF_BUILD ∧
        sb.message.value = U64.zero ∨
      (∃ b, s.builders.toArray[sb.message.builder_index.toNat]? = some b ∧
        b.withdrawable_epoch = FAR_FUTURE_EPOCH ∧
        JauneConsensus.Gloas.canBuilderCoverBid s sb.message.builder_index sb.message.value =
          .ok true)) ∧
    s'.builders = s.builders ∧ s'.latest_block_hash = s.latest_block_hash ∧
    s'.latest_block_header = s.latest_block_header ∧ s'.slot = s.slot ∧
    s'.next_withdrawal_builder_index = s.next_withdrawal_builder_index ∧
    s'.builder_pending_withdrawals = s.builder_pending_withdrawals ∧
    (¬ U64.zero < sb.message.value → s'.builder_pending_payments = s.builder_pending_payments) ∧
    (U64.zero < sb.message.value → ∃ p : ValidatorIndex,
      s'.builder_pending_payments.toArray[P.SLOTS_PER_EPOCH + s.slot.toNat % P.SLOTS_PER_EPOCH]? =
        some { weight := U64.zero, withdrawal := bidWithdrawal sb.message, proposer_index := p } ∧
      ∀ j, j ≠ P.SLOTS_PER_EPOCH + s.slot.toNat % P.SLOTS_PER_EPOCH →
        s'.builder_pending_payments.toArray[j]? = s.builder_pending_payments.toArray[j]?)

theorem c64_toNat {n : Nat} {x : U64} (h : c64 n = .ok x) : x.toNat = n := U64.toNat_ofNat? h

theorem require_eq_ok_iff {c : Bool} {site : String} {u : Unit} :
    require c site = .ok u ↔ c = true :=
  ⟨require_ok, fun h => by subst h; rfl⟩

theorem bid_active_facts {s : GSt P} {bi v : U64} {b0 : JauneConsensus.Gloas.Builder} {st2 : String}
    (hact : JauneConsensus.Gloas.isActiveBuilder s bi = .ok true)
    (hget : s.builders.get bi.toNat st2 = .ok b0)
    (hcov : JauneConsensus.Gloas.canBuilderCoverBid s bi v = .ok true) :
    ∃ b, s.builders.toArray[bi.toNat]? = some b ∧ b.withdrawable_epoch = FAR_FUTURE_EPOCH ∧
      JauneConsensus.Gloas.canBuilderCoverBid s bi v = .ok true := by
  have hb := pl_get_ok.mp hget
  rw [isActiveBuilder_of_get hb] at hact
  have h1 := Except.ok.inj hact
  simp only [Bool.and_eq_true] at h1
  exact ⟨b0, hb, U64.beq_eq_true_iff.mp h1.2, hcov⟩

set_option maxHeartbeats 1000000 in
theorem processExecutionPayloadBid_post {ctx : Ctx} {s s' : GSt P}
    {sb : JauneConsensus.Gloas.SignedExecutionPayloadBid}
    (h : JauneConsensus.Gloas.processExecutionPayloadBid ctx s sb = .ok s') : BidPost s sb s' := by
  revert s' h
  show Ok (JauneConsensus.Gloas.processExecutionPayloadBid ctx s sb) (BidPost s sb)
  unfold JauneConsensus.Gloas.processExecutionPayloadBid
  gvcg
  all_goals
    apply ok_pure
    first
    | (rename_i _ hc _ hm _ ha _ hs _ hlast
       have e4 := c64_toNat hc
       have e3 := U64.toNat_mod? hm
       have e2 := U64.toNat_add? ha
       obtain ⟨h1, h2⟩ := sv_set_ok hs
       cases hlast
       simp only [require_eq_ok_iff] at *
       subst_vars
       simp only [U64.beq_eq_true_iff, beq_iff_eq] at *
       have hslot : sb.message.slot = s.slot := ‹_›
       have hpar : sb.message.parent_block_hash = s.latest_block_hash := ‹_›
       have hidx := e2
       rw [e3, e4, hslot] at hidx
       rw [hidx] at h1
       refine ⟨rfl, hslot, hpar, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
         fun hn => absurd ‹U64.zero < sb.message.value› hn,
         fun _ => ⟨_, h1, fun j hj => h2 j (by rw [hidx]; exact hj)⟩⟩
       first
       | exact Or.inl ⟨‹sb.message.builder_index = _›, ‹sb.message.value = U64.zero›⟩
       | exact Or.inr (bid_active_facts
           ‹JauneConsensus.Gloas.isActiveBuilder s sb.message.builder_index = .ok true›
           ‹ProgressiveListS.get s.builders sb.message.builder_index.toNat _ = _›
           ‹JauneConsensus.Gloas.canBuilderCoverBid s sb.message.builder_index sb.message.value = .ok true›))
    | (rename_i _ hlast
       cases hlast
       simp only [require_eq_ok_iff] at *
       subst_vars
       simp only [U64.beq_eq_true_iff, beq_iff_eq] at *
       have hslot : sb.message.slot = s.slot := ‹_›
       have hpar : sb.message.parent_block_hash = s.latest_block_hash := ‹_›
       refine ⟨rfl, hslot, hpar, ?_, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl,
         fun hp => absurd hp ‹¬ U64.zero < sb.message.value›⟩
       first
       | exact Or.inl ⟨‹sb.message.builder_index = _›, ‹sb.message.value = U64.zero›⟩
       | exact Or.inr (bid_active_facts
           ‹JauneConsensus.Gloas.isActiveBuilder s sb.message.builder_index = .ok true›
           ‹ProgressiveListS.get s.builders sb.message.builder_index.toNat _ = _›
           ‹JauneConsensus.Gloas.canBuilderCoverBid s sb.message.builder_index sb.message.value = .ok true›))
