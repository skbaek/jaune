import JauneConsensus.Facts.Gloas.InvariantsSlots

/-!
# G3-01 and G3-06: preservation (goal `eip8282-gloas-cross-layer-v1`, G3a)

The frame-shaped invariants, from the step frames (`InvFrame`, `CoreFrame`, `WFrame`, the bid's
`BidPost`) and the two request lemmas (`depReq_cases`, `exitReq_cases`):

* **G3-01 BuilderPubkeysUnique** is preserved by `Gloas.processSlots`
  (`processSlots_pubkeysUnique`), `Gloas.processBlock` (`processBlock_pubkeysUnique`) and hence
  `Gloas.stateTransition` (`stateTransition_pubkeysUnique`). The only writer of a pubkey is a
  registration, which `process_builder_deposit_request` makes only for a pubkey not in the
  registry.
* **G3-06 NextBuilderIndexInRange** likewise (`processSlots_nextBuilderIndexInRange`,
  `processBlock_nextBuilderIndexInRange`, `stateTransition_nextBuilderIndexInRange`). A FULL
  parent may grow the registry from empty; the same block's `process_withdrawals` then runs
  (`latest_block_hash = L.block_hash`) and reduces the index modulo the length.
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-! ## Shared plumbing -/

theorem applySignedBlockWith_ok {ctx : Ctx} {bls : Bool} {st s' : GSt P}
    {sb : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool}
    (h : JauneConsensus.Gloas.applySignedBlockWith (JauneConsensus.Gloas.processBlock ctx) bls st sb v
      = .ok s') : JauneConsensus.Gloas.processBlock ctx st sb.message = .ok s' := by
  revert s' h
  show Ok (JauneConsensus.Gloas.applySignedBlockWith (JauneConsensus.Gloas.processBlock ctx) bls st sb v)
    (fun r => JauneConsensus.Gloas.processBlock ctx st sb.message = .ok r)
  unfold JauneConsensus.Gloas.applySignedBlockWith
  gvcg
  all_goals (apply ok_pure; assumption)

/-- `state_transition` is `process_slots` then `process_block` (the checks around it only
reject). -/
theorem stateTransition_split {ctx : Ctx} {s s' : GSt P}
    {sb : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool}
    (h : JauneConsensus.Gloas.stateTransition ctx s sb v = .ok s') :
    ∃ m, JauneConsensus.Gloas.processSlots ctx s sb.message.slot = .ok m ∧
      JauneConsensus.Gloas.processBlock ctx m sb.message = .ok s' := by
  rw [JauneConsensus.Gloas.stateTransition_eq] at h
  obtain ⟨m, hm, h⟩ := bind_eq_ok_iff.mp h
  exact ⟨m, hm, applySignedBlockWith_ok h⟩

theorem processBuilderPendingPayments_core (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processBuilderPendingPayments cfg s) (coreFrame.R s) := by
  unfold JauneConsensus.Gloas.processBuilderPendingPayments; gvcg
  all_goals (apply ok_pure; exact (show CoreFrame _ _ from ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))

/-- One slot iteration keeps `CoreFrame` except the slot, which advances. -/
theorem slotIter_core {ctx : Ctx} {st st1 st2 : GSt P} {next : U64} (f1 : InvFrame st st1)
    (h : (st2 = st1 ∧ next.toNat % P.SLOTS_PER_EPOCH ≠ 0) ∨
      (next.toNat % P.SLOTS_PER_EPOCH = 0 ∧ JauneConsensus.Gloas.processEpoch ctx st1 = .ok st2)) :
    st2.builders = st.builders ∧
      st2.latest_execution_payload_bid = st.latest_execution_payload_bid ∧
      st2.latest_block_hash = st.latest_block_hash ∧
      st2.latest_block_header.slot = st.latest_block_header.slot ∧
      st2.next_withdrawal_builder_index = st.next_withdrawal_builder_index := by
  have c1 := coreFrame_of_inv f1
  rcases h with ⟨rfl, _⟩ | ⟨_, he⟩
  · exact ⟨c1.1, c1.2.1, c1.2.2.1, c1.2.2.2.1, c1.2.2.2.2.2⟩
  · obtain ⟨a, b, fa, hb, fb⟩ := processEpoch_phases he
    have c := coreFrame.trans c1 (coreFrame.trans (coreFrame_of_inv fa)
      (coreFrame.trans (processBuilderPendingPayments_core _ _ _ hb) (coreFrame_of_inv fb)))
    exact ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.2⟩

/-! ## G3-01 -/

/-- Pubkeys index by index, and the length, carry uniqueness. -/
theorem pubkeysUnique_of_pk {s s' : GSt P}
    (hsz : s'.builders.toArray.size = s.builders.toArray.size)
    (hpk : ∀ (j : Nat) (b : JauneConsensus.Gloas.Builder), s.builders.toArray[j]? = some b →
      ∃ b', s'.builders.toArray[j]? = some b' ∧ b'.pubkey = b.pubkey)
    (h : BuilderPubkeysUnique s) : BuilderPubkeysUnique s' := by
  intro i j bi bj hij hi hj
  have hi' : i < s.builders.toArray.size := by
    rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hi).1
  have hj' : j < s.builders.toArray.size := by
    rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hj).1
  obtain ⟨ci, hci, epi⟩ := hpk i _ (Array.getElem?_eq_getElem hi')
  obtain ⟨cj, hcj, epj⟩ := hpk j _ (Array.getElem?_eq_getElem hj')
  rw [hi] at hci; cases hci
  rw [hj] at hcj; cases hcj
  rw [epi, epj]
  exact h i j _ _ hij (Array.getElem?_eq_getElem hi') (Array.getElem?_eq_getElem hj')

theorem pubkeysUnique_of_eq {s s' : GSt P} (h : s'.builders = s.builders)
    (hu : BuilderPubkeysUnique s) : BuilderPubkeysUnique s' := by
  unfold BuilderPubkeysUnique; rw [h]; exact hu

theorem depReq_pubkeysUnique {ctx : Ctx} {m m' : GSt P}
    {r : JauneConsensus.Gloas.BuilderDepositRequest}
    (h : JauneConsensus.Gloas.processBuilderDepositRequest ctx m r = .ok m')
    (hu : BuilderPubkeysUnique m) : BuilderPubkeysUnique m' := by
  obtain ⟨_, hcase⟩ := depReq_cases h
  rcases hcase with heq | ⟨i, b, b', hb, hb', hsz, hoth, hid, _⟩ |
      ⟨i, b', hnot, _, hb', hpk, _, _, _, hoth⟩
  · exact pubkeysUnique_of_eq heq hu
  · refine pubkeysUnique_of_pk hsz (fun j c hc => ?_) hu
    by_cases hj : j = i
    · subst hj; rw [hb] at hc; cases hc; exact ⟨b', hb', hid.1⟩
    · exact ⟨c, by rw [hoth j hj]; exact hc, rfl⟩
  · have hfresh : ∀ (q : Nat) (c : JauneConsensus.Gloas.Builder), q ≠ i →
        m'.builders.toArray[q]? = some c → c.pubkey ≠ r.pubkey := by
      intro q c hq hc
      rw [hoth q hq] at hc
      exact hnot c (Array.mem_of_getElem? hc)
    intro p q bp bq hpq hp hq
    by_cases hpi : p = i
    · subst hpi
      rw [hb'] at hp; cases hp
      rw [hpk]
      exact fun e => hfresh q bq (by omega) hq e.symm
    · by_cases hqi : q = i
      · subst hqi
        rw [hb'] at hq; cases hq
        rw [hpk]
        exact hfresh p bp hpi hp
      · rw [hoth p hpi] at hp
        rw [hoth q hqi] at hq
        exact hu p q bp bq hpq hp hq

theorem exitReq_pubkeysUnique {cfg : Config} {m m' : GSt P}
    {r : JauneConsensus.Gloas.BuilderExitRequest}
    (h : JauneConsensus.Gloas.processBuilderExitRequest cfg m r = .ok m')
    (hu : BuilderPubkeysUnique m) : BuilderPubkeysUnique m' := by
  obtain ⟨_, hcase⟩ := exitReq_cases h
  rcases hcase with heq | ⟨i, b, w, hb, hb', _, _, _, hsz, hoth⟩
  · subst heq; exact hu
  · refine pubkeysUnique_of_pk hsz (fun j c hc => ?_) hu
    by_cases hj : j = i
    · subst hj; rw [hb] at hc; cases hc; exact ⟨_, hb', rfl⟩
    · exact ⟨c, by rw [hoth j hj]; exact hc, rfl⟩

/-- **G3-01 over `process_slots`.** -/
theorem processSlots_pubkeysUnique {ctx : Ctx} {s s' : GSt P} {slot : U64}
    (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s') (hu : BuilderPubkeysUnique s) :
    BuilderPubkeysUnique s' :=
  processSlots_ind (ctx := ctx) BuilderPubkeysUnique
    (fun _ _ _ _ hI f1 _ hc => pubkeysUnique_of_eq (slotIter_core f1 hc).1 hI) h hu

/-- **G3-01 over `process_block`.** -/
theorem processBlock_pubkeysUnique {ctx : Ctx} {s s' : GSt P}
    {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') (hu : BuilderPubkeysUnique s) :
    BuilderPubkeysUnique s' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  have u1 : BuilderPubkeysUnique s1 := by
    rcases processParentExecutionPayload_cases h1 with ⟨rfl, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
    · exact hu
    · have ua := pubkeysUnique_of_eq (applyParentPrefix_core _ _ _ _ ha).1 hu
      have ud := forIn_yield_inv BuilderPubkeysUnique _ (fun _ _ _ hI hm => depReq_pubkeysUnique hm hI)
        _ _ _ hd ua
      have ue := forIn_yield_inv BuilderPubkeysUnique _ (fun _ _ _ hI hm => exitReq_pubkeysUnique hm hI)
        _ _ _ he ud
      exact pubkeysUnique_of_eq (applyParentSuffix_post hs).1 ue
  have u2 : BuilderPubkeysUnique s2 := by
    obtain ⟨_, _, hm⟩ := processBlockHeader_post h2
    exact pubkeysUnique_of_eq (by rw [hm]) u1
  have u3 : BuilderPubkeysUnique s3 := by
    obtain ⟨_, _, _, _, _, hsz, hid, _⟩ := processWithdrawals_wFrame _ _ h3
    exact pubkeysUnique_of_pk hsz (fun j b hb => by
      obtain ⟨b', hb', hi⟩ := hid j b hb; exact ⟨b', hb', hi.1.1⟩) u2
  have u4 := pubkeysUnique_of_eq (processExecutionPayloadBid_post h4).2.2.2.2.1 u3
  have u5 := pubkeysUnique_of_eq (processRandao_invFrame _ _ _ _ h5).1 u4
  have u6 := pubkeysUnique_of_eq (processEth1Data_invFrame _ _ _ h6).1 u5
  have u7 := pubkeysUnique_of_eq (processOperations_core _ _ _ _ _ h7).1 u6
  exact pubkeysUnique_of_eq (processSyncAggregate_invFrame _ _ _ _ h8).1 u7

/-- **G3-01 over `state_transition`.** -/
theorem stateTransition_pubkeysUnique {ctx : Ctx} {s s' : GSt P}
    {sb : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool}
    (h : JauneConsensus.Gloas.stateTransition ctx s sb v = .ok s') (hu : BuilderPubkeysUnique s) :
    BuilderPubkeysUnique s' := by
  obtain ⟨m, hm, hb⟩ := stateTransition_split h
  exact processBlock_pubkeysUnique hb (processSlots_pubkeysUnique hm hu)

/-! ## G3-06 -/

theorem nextBuilderIndexInRange_of {s s' : GSt P}
    (hsz : s.builders.toArray.size ≤ s'.builders.toArray.size)
    (hn : s'.next_withdrawal_builder_index = s.next_withdrawal_builder_index)
    (hpos : 0 < s.builders.toArray.size) (h : NextBuilderIndexInRange s) :
    NextBuilderIndexInRange s' := fun _ => by rw [hn]; exact Nat.lt_of_lt_of_le (h hpos) hsz

/-- A FULL parent payload: the registry can only grow, and `L`, the sweep index and the header
slot are kept; `latest_block_hash` becomes `L.block_hash`. -/
theorem parentFull_frame {ctx : Ctx} {s a d e s1 : GSt P}
    {r : JauneConsensus.Gloas.ExecutionRequests}
    (ha : JauneConsensus.Gloas.applyParentPrefix ctx s r = .ok a)
    (hd : forIn r.builder_deposits.toArray.toList a
          (fun op s => do
            let s' ← JauneConsensus.Gloas.processBuilderDepositRequest ctx s op
            pure (ForInStep.yield s')) = .ok d)
    (he : forIn r.builder_exits.toArray.toList d
          (fun op s => do
            let s' ← JauneConsensus.Gloas.processBuilderExitRequest ctx.cfg s op
            pure (ForInStep.yield s')) = .ok e)
    (hs : JauneConsensus.Gloas.applyParentSuffix s e = .ok s1) :
    s.builders.toArray.size ≤ s1.builders.toArray.size ∧
      s1.next_withdrawal_builder_index = s.next_withdrawal_builder_index ∧
      s1.latest_execution_payload_bid = s.latest_execution_payload_bid ∧
      s1.latest_block_hash = s.latest_execution_payload_bid.block_hash ∧
      s1.latest_block_header.slot = s.latest_block_header.slot ∧ s1.slot = s.slot := by
  have ca := applyParentPrefix_core _ _ _ _ ha
  let I : GSt P → Prop := fun m => a.builders.toArray.size ≤ m.builders.toArray.size ∧
    m.next_withdrawal_builder_index = a.next_withdrawal_builder_index ∧
    m.latest_execution_payload_bid = a.latest_execution_payload_bid ∧
    m.latest_block_header.slot = a.latest_block_header.slot ∧ m.slot = a.slot
  have hId : I d := forIn_yield_inv I _ (fun m _ m' hI hm => by
    obtain ⟨hm', hcase⟩ := depReq_cases hm
    have hsz : m.builders.toArray.size ≤ m'.builders.toArray.size := by
      rcases hcase with heq | ⟨_, _, _, _, _, hsz, _⟩ | ⟨_, _, _, _, _, _, _, _, hsz, _⟩
      · rw [heq]
      · rw [hsz]
      · exact hsz
    rw [hm'] at hsz ⊢
    exact ⟨Nat.le_trans hI.1 hsz, hI.2⟩) _ _ _ hd ⟨Nat.le_refl _, rfl, rfl, rfl, rfl⟩
  have hIe : I e := forIn_yield_inv I _ (fun m _ m' hI hm => by
    obtain ⟨hm', hcase⟩ := exitReq_cases hm
    have hsz : m.builders.toArray.size ≤ m'.builders.toArray.size := by
      rcases hcase with heq | ⟨_, _, _, _, _, _, _, _, hsz, _⟩
      · rw [heq]
      · rw [hsz]
    rw [hm'] at hsz ⊢
    exact ⟨Nat.le_trans hI.1 hsz, hI.2⟩) _ _ _ he hId
  obtain ⟨hb, _, _, hl, hk, hd', ht, hn⟩ := applyParentSuffix_post hs
  refine ⟨?_, ?_, ?_, hk, ?_, ?_⟩
  · rw [hb, ← ca.1]; exact hIe.1
  · rw [hn, hIe.2.1, ca.2.2.2.2.2]
  · rw [hl, hIe.2.2.1, ca.2.1]
  · rw [hd', hIe.2.2.2.1, ca.2.2.2.1]
  · rw [ht, hIe.2.2.2.2, ca.2.2.2.2.1]

theorem updateNextWithdrawalBuilderIndex_inRange {s s' : GSt P} {n : U64}
    (h : JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex s n = .ok s')
    (hpos : 0 < s.builders.toArray.size) :
    s'.next_withdrawal_builder_index.toNat < s'.builders.toArray.size := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex at h
  simp only [] at h
  rw [if_pos (show 0 < ProgressiveListS.length s.builders from hpos)] at h
  obtain ⟨x, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨len, hlen, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨nx, hnx, h⟩ := bind_eq_ok_iff.mp h
  cases h
  show nx.toNat < s.builders.toArray.size
  rw [U64.toNat_mod? hnx, U64.toNat_ofNat? hlen]
  exact Nat.mod_lt _ hpos

/-- When the parent block is FULL (`latest_block_hash = L.block_hash`), `process_withdrawals`
leaves the builder sweep index in range. -/
theorem processWithdrawals_inRange {s s' : GSt P}
    (h : JauneConsensus.Gloas.processWithdrawals s = .ok s')
    (hfull : s.latest_block_hash = s.latest_execution_payload_bid.block_hash)
    (hpos : 0 < s.builders.toArray.size) :
    s'.next_withdrawal_builder_index.toNat < s'.builders.toArray.size := by
  unfold JauneConsensus.Gloas.processWithdrawals at h
  rw [if_neg (by simp [hfull])] at h
  obtain ⟨ex, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t6, h6, h⟩ := bind_eq_ok_iff.mp h
  have w1 := applyWithdrawals_wf _ _ _ h1
  have w2 := updateNextWithdrawalIndex_wf _ _ _ h2
  have w7 := updateNextWithdrawalValidatorIndex_wf _ _ _ h
  have hpos6 : 0 < (JauneConsensus.Gloas.updatePendingPartialWithdrawals
      (JauneConsensus.Gloas.updateBuilderPendingWithdrawals
        (JauneConsensus.Gloas.updatePayloadExpectedWithdrawals t2 ex.withdrawals)
        ex.processed_builder_withdrawals_count)
      ex.processed_partial_withdrawals_count).builders.toArray.size := by
    show 0 < t2.builders.toArray.size
    rw [w2.2.2.2.2.2.1, w1.2.2.2.2.2.1]; exact hpos
  have h6' := updateNextWithdrawalBuilderIndex_inRange h6 hpos6
  obtain ⟨_, _, _, _, _, hsz, _, hn⟩ := w7
  rcases hn with hn | hn
  · rw [hn, hsz]; exact h6'
  · rw [hsz]; exact hn (by rw [← hsz]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) (by
      rw [hsz]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) h6'))

/-- **G3-06 over `process_slots`.** -/
theorem processSlots_nextBuilderIndexInRange {ctx : Ctx} {s s' : GSt P} {slot : U64}
    (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s')
    (hu : NextBuilderIndexInRange s) : NextBuilderIndexInRange s' :=
  processSlots_ind (ctx := ctx) NextBuilderIndexInRange
    (fun _ _ _ _ hI f1 _ hc => by
      obtain ⟨hb, _, _, _, hn⟩ := slotIter_core f1 hc
      intro hpos
      show _ < _
      simp only [] at hpos ⊢
      rw [hb] at hpos ⊢; rw [hn]; exact hI hpos) h hu

/-- **G3-06 over `process_block`.** -/
theorem processBlock_nextBuilderIndexInRange {ctx : Ctx} {s s' : GSt P}
    {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') (hu : NextBuilderIndexInRange s) :
    NextBuilderIndexInRange s' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have w3 := processWithdrawals_wFrame _ _ h3
  -- after the withdrawals, the registry and the index are fixed for the rest of the block
  have u3 : NextBuilderIndexInRange s3 := by
    rcases processParentExecutionPayload_cases h1 with ⟨rfl, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
    · -- EMPTY: the registry and the index are those of `s`
      intro hpos
      obtain ⟨_, _, _, _, _, hsz, _, hn⟩ := w3
      have hb2 : s2.builders = s1.builders := by rw [hm2]
      have hn2 : s2.next_withdrawal_builder_index = s1.next_withdrawal_builder_index := by rw [hm2]
      rw [hsz, hb2] at hpos ⊢
      rcases hn with hn | hn
      · rw [hn, hn2]; exact hu hpos
      · have := hn (by rw [hb2]; exact hpos); rw [hb2] at this; exact this
    · obtain ⟨_, _, hl, hk, _, _⟩ := parentFull_frame ha hd he hs
      intro hpos
      have hsz := w3.2.2.2.2.2.1
      have hfull : s2.latest_block_hash = s2.latest_execution_payload_bid.block_hash := by
        rw [hm2]; show s1.latest_block_hash = s1.latest_execution_payload_bid.block_hash
        rw [hk, hl]
      exact processWithdrawals_inRange h3 hfull (by rw [← hsz]; exact hpos)
  have b4 := processExecutionPayloadBid_post h4
  have c5 := coreFrame_of_inv (processRandao_invFrame _ _ _ _ h5)
  have c6 := coreFrame_of_inv (processEth1Data_invFrame _ _ _ h6)
  have c7 := processOperations_core _ _ _ _ _ h7
  have c8 := coreFrame_of_inv (processSyncAggregate_invFrame _ _ _ _ h8)
  have hb : s'.builders = s3.builders := by
    rw [c8.1, c7.1, c6.1, c5.1, b4.2.2.2.2.1]
  have hn : s'.next_withdrawal_builder_index = s3.next_withdrawal_builder_index := by
    rw [c8.2.2.2.2.2, c7.2.2.2.2.2, c6.2.2.2.2.2, c5.2.2.2.2.2, b4.2.2.2.2.2.2.2.2.1]
  intro hpos
  show _ < _
  rw [hn, hb]; rw [hb] at hpos; exact u3 hpos

/-- **G3-06 over `state_transition`.** -/
theorem stateTransition_nextBuilderIndexInRange {ctx : Ctx} {s s' : GSt P}
    {sb : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool}
    (h : JauneConsensus.Gloas.stateTransition ctx s sb v = .ok s')
    (hu : NextBuilderIndexInRange s) : NextBuilderIndexInRange s' := by
  obtain ⟨m, hm, hb⟩ := stateTransition_split h
  exact processBlock_nextBuilderIndexInRange hb (processSlots_nextBuilderIndexInRange hm hu)

/-! ## G3-02 -/

theorem SameIdentity.refl (b : JauneConsensus.Gloas.Builder) : SameIdentity b b := ⟨rfl, rfl, rfl⟩

theorem SameIdentity.trans {a b c : JauneConsensus.Gloas.Builder} (h₁ : SameIdentity a b)
    (h₂ : SameIdentity b c) : SameIdentity a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

/-- `BuilderIdentityStable` with the reuse epoch given. -/
def BPresAt (e : Nat) (s s' : GSt P) : Prop :=
  s.builders.toArray.size ≤ s'.builders.toArray.size ∧
    ∀ (i : Nat) (b : JauneConsensus.Gloas.Builder), s.builders.toArray[i]? = some b →
      ∃ b', s'.builders.toArray[i]? = some b' ∧
        (SameIdentity b b' ∨
          (Reusable b e ∧ b'.pubkey ≠ b.pubkey ∧
            b'.version = JauneConsensus.Gloas.PAYLOAD_BUILDER_VERSION))

theorem bpresAt_refl (e : Nat) (s : GSt P) : BPresAt e s s :=
  ⟨Nat.le_refl _, fun _ b hb => ⟨b, hb, Or.inl (SameIdentity.refl b)⟩⟩

/-- Extend by a step that keeps every identity and the length. -/
theorem bpresAt_then_same {e : Nat} {s m m' : GSt P} (h : BPresAt e s m)
    (hsz : m.builders.toArray.size ≤ m'.builders.toArray.size)
    (hid : ∀ (j : Nat) (b : JauneConsensus.Gloas.Builder), m.builders.toArray[j]? = some b →
      ∃ b', m'.builders.toArray[j]? = some b' ∧ SameIdentity b b') : BPresAt e s m' := by
  refine ⟨Nat.le_trans h.1 hsz, fun i b hb => ?_⟩
  obtain ⟨bm, hbm, hc⟩ := h.2 i b hb
  obtain ⟨b', hb', hs⟩ := hid i bm hbm
  refine ⟨b', hb', ?_⟩
  rcases hc with hc | ⟨hr, hpk, hv⟩
  · exact Or.inl (hc.trans hs)
  · exact Or.inr ⟨hr, by rw [hs.1]; exact hpk, by rw [hs.2.1]; exact hv⟩

theorem bpresAt_then_eq {e : Nat} {s m m' : GSt P} (h : BPresAt e s m)
    (heq : m'.builders = m.builders) : BPresAt e s m' :=
  bpresAt_then_same h (by rw [heq]) (fun _ b hb => ⟨b, by rw [heq]; exact hb, SameIdentity.refl b⟩)

/-- The deposit-loop invariant of G3-02, relative to the loop's start `a`. -/
def DepInv (delay : Nat) (a m : GSt P) : Prop :=
  a.builders.toArray.size ≤ m.builders.toArray.size ∧ m.slot = a.slot ∧
    ∀ (j : Nat) (b : JauneConsensus.Gloas.Builder), a.builders.toArray[j]? = some b →
      ∃ bm, m.builders.toArray[j]? = some bm ∧
        ((SameIdentity b bm ∧ b.balance.toNat ≤ bm.balance.toNat ∧
            (bm.withdrawable_epoch = b.withdrawable_epoch ∨
              bm.withdrawable_epoch.toNat = curEpoch a + delay)) ∨
          (Reusable b (curEpoch a) ∧ bm.pubkey ≠ b.pubkey ∧
            bm.version = JauneConsensus.Gloas.PAYLOAD_BUILDER_VERSION ∧
            bm.withdrawable_epoch = FAR_FUTURE_EPOCH))

theorem depInv_step (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx}
    (hdelay : 0 < ctx.cfg.MIN_BUILDER_WITHDRAWABILITY_DELAY) {a m m' : GSt P}
    {r : JauneConsensus.Gloas.BuilderDepositRequest}
    (hI : DepInv ctx.cfg.MIN_BUILDER_WITHDRAWABILITY_DELAY a m)
    (h : JauneConsensus.Gloas.processBuilderDepositRequest ctx m r = .ok m') :
    DepInv ctx.cfg.MIN_BUILDER_WITHDRAWABILITY_DELAY a m' := by
  obtain ⟨hsz0, hslot, hall⟩ := hI
  obtain ⟨hm', hcase⟩ := depReq_cases h
  have hslot' : m'.slot = a.slot := by rw [hm']; exact hslot
  have hep : curEpoch m = curEpoch a := by unfold curEpoch; rw [hslot]
  rcases hcase with heq | ⟨i, b, b', hb, hb', hsz, hoth, hid, hbal, hwe⟩ |
      ⟨i, b', hnot, hidx, hb', hpk, hver, hfar, hsz, hoth⟩
  · exact ⟨by rw [heq]; exact hsz0, hslot', fun j c hc => by rw [heq]; exact hall j c hc⟩
  · refine ⟨by rw [hsz]; exact hsz0, hslot', fun j c hc => ?_⟩
    obtain ⟨bm, hbm, hcm⟩ := hall j c hc
    by_cases hj : j = i
    · subst hj
      rw [hb] at hbm; cases hbm
      refine ⟨b', hb', ?_⟩
      rcases hcm with ⟨hs, hle, hw⟩ | ⟨hr, hp, hv, hf⟩
      · refine Or.inl ⟨hs.trans hid, by omega, ?_⟩
        rcases hwe with hwe | ⟨_, _, hwe⟩
        · rw [hwe]; exact hw
        · exact Or.inr (by rw [hwe, hep])
      · refine Or.inr ⟨hr, by rw [hid.1]; exact hp, by rw [hid.2.1]; exact hv, ?_⟩
        rcases hwe with hwe | ⟨hne, _, _⟩
        · rw [hwe]; exact hf
        · exact absurd hf hne
    · exact ⟨bm, by rw [hoth j hj]; exact hbm, hcm⟩
  · refine ⟨Nat.le_trans hsz0 hsz, hslot', fun j c hc => ?_⟩
    obtain ⟨bm, hbm, hcm⟩ := hall j c hc
    by_cases hj : j = i
    · subst hj
      refine ⟨b', hb', ?_⟩
      rcases hidx with hidx | ⟨bm', hbm', hreu⟩
      · have : j < m.builders.toArray.size := (Array.getElem?_eq_some_iff.mp hbm).1
        omega
      · rw [hbm] at hbm'; cases hbm'
        have hne : b'.pubkey ≠ bm.pubkey := by
          rw [hpk]; exact fun e => hnot bm (Array.mem_of_getElem? hbm) e.symm
        rcases hcm with ⟨hs, hle, hw⟩ | ⟨_, _, _, hf⟩
        · obtain ⟨hwr, hz⟩ := hreu
          have hz' : c.balance = U64.zero := by
            apply U64.eq_zero_of_toNat_eq_zero
            rw [hz] at hle; exact Nat.le_zero.mp hle
          refine Or.inr ⟨⟨?_, hz'⟩, by rw [← hs.1]; exact hne, hver, hfar⟩
          rcases hw with hw | hw
          · rw [← hw, ← hep]; exact hwr
          · rw [hw, hep] at hwr; omega
        · have := epoch_lt_far hspe m
          have h2 := hreu.1
          rw [hf] at h2
          omega
    · exact ⟨bm, by rw [hoth j hj]; exact hbm, hcm⟩

/-- **G3-02 over `process_slots`** (the registry is unchanged). -/
theorem processSlots_identityStable {ctx : Ctx} {s s' : GSt P} {slot : U64}
    (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s') :
    s'.builders = s.builders := by
  have := processSlots_ind (ctx := ctx) (fun m => m.builders = s.builders)
    (fun _ _ _ _ hI f1 _ hc => by
      show _ = _; exact (slotIter_core f1 hc).1.trans hI) h rfl
  exact this

theorem identityStable_of_eq {s s' : GSt P} (h : s'.builders = s.builders) :
    BuilderIdentityStable s s' :=
  ⟨by rw [h], fun _ b hb => ⟨b, by rw [h]; exact hb, Or.inl (SameIdentity.refl b)⟩⟩

/-- **G3-02 over `process_block`.** Needs `2 ≤ SLOTS_PER_EPOCH` and
`0 < MIN_BUILDER_WITHDRAWABILITY_DELAY` (see the report: with a zero delay, a zero-amount top-up
of an exited, swept builder makes it reusable in the same payload, so the overwritten record was
not reusable at the block's pre-state). -/
theorem processBlock_identityStable (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx}
    (hdelay : 0 < ctx.cfg.MIN_BUILDER_WITHDRAWABILITY_DELAY) {s s' : GSt P}
    {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') : BuilderIdentityStable s s' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  have p1 : BPresAt (curEpoch s) s s1 ∧ s1.slot = s.slot := by
    rcases processParentExecutionPayload_cases h1 with ⟨hs1, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
    · rw [hs1]; exact ⟨bpresAt_refl _ _, rfl⟩
    · have ca := applyParentPrefix_core _ _ _ _ ha
      have hep : curEpoch a = curEpoch s := by unfold curEpoch; rw [ca.2.2.2.2.1]
      have hdI := forIn_yield_inv (DepInv ctx.cfg.MIN_BUILDER_WITHDRAWABILITY_DELAY a) _
        (fun _ _ _ hI hm => depInv_step hspe hdelay hI hm) _ _ _ hd
        ⟨Nat.le_refl _, rfl, fun _ b hb => ⟨b, hb, Or.inl ⟨SameIdentity.refl b, Nat.le_refl _,
          Or.inl rfl⟩⟩⟩
      have b0 : BPresAt (curEpoch s) s d := by
        refine ⟨by rw [← ca.1]; exact hdI.1, fun j b hb => ?_⟩
        obtain ⟨bm, hbm, hc⟩ := hdI.2.2 j b (by rw [ca.1]; exact hb)
        refine ⟨bm, hbm, ?_⟩
        rcases hc with ⟨hs, _, _⟩ | ⟨hr, hp, hv, _⟩
        · exact Or.inl hs
        · exact Or.inr ⟨by rw [← hep]; exact hr, hp, hv⟩
      have be := forIn_yield_inv (fun m => BPresAt (curEpoch s) s m) _
        (fun m _ m' hI hm => by
          obtain ⟨hm', hcase⟩ := exitReq_cases hm
          rcases hcase with heq | ⟨i, b, w, hb, hb', _, _, _, hsz, hoth⟩
          · rw [heq]; exact hI
          · refine bpresAt_then_same hI (by rw [hsz]) (fun j c hc => ?_)
            by_cases hj : j = i
            · subst hj; rw [hb] at hc; cases hc; exact ⟨_, hb', ⟨rfl, rfl, rfl⟩⟩
            · exact ⟨c, by rw [hoth j hj]; exact hc, SameIdentity.refl c⟩) _ _ _ he b0
      exact ⟨bpresAt_then_eq be (applyParentSuffix_post hs).1,
        (parentFull_frame ha hd he hs).2.2.2.2.2⟩
  obtain ⟨hs2slot, _, hm2⟩ := processBlockHeader_post h2
  have w3 := processWithdrawals_wFrame _ _ h3
  have b4 := processExecutionPayloadBid_post h4
  have c5 := coreFrame_of_inv (processRandao_invFrame _ _ _ _ h5)
  have c6 := coreFrame_of_inv (processEth1Data_invFrame _ _ _ h6)
  have c7 := processOperations_core _ _ _ _ _ h7
  have c8 := coreFrame_of_inv (processSyncAggregate_invFrame _ _ _ _ h8)
  have q2 := bpresAt_then_eq p1.1 (show s2.builders = s1.builders by rw [hm2])
  have q3 := bpresAt_then_same q2 (by rw [w3.2.2.2.2.2.1]) (fun j b hb => by
    obtain ⟨b', hb', hi⟩ := w3.2.2.2.2.2.2.1 j b hb; exact ⟨b', hb', hi.1⟩)
  have hb : s'.builders = s3.builders := by rw [c8.1, c7.1, c6.1, c5.1, b4.2.2.2.2.1]
  have hslot : s'.slot = s.slot := by
    rw [c8.2.2.2.2.1, c7.2.2.2.2.1, c6.2.2.2.2.1, c5.2.2.2.2.1, b4.2.2.2.2.2.2.2.1,
      w3.2.2.2.1, show s2.slot = s1.slot by rw [hm2], p1.2]
  have := bpresAt_then_eq q3 hb
  unfold BuilderIdentityStable
  rw [show curEpoch s' = curEpoch s by unfold curEpoch; rw [hslot]]
  exact this

/-- **G3-02 over `state_transition`.** -/
theorem stateTransition_identityStable (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx}
    (hdelay : 0 < ctx.cfg.MIN_BUILDER_WITHDRAWABILITY_DELAY) {s s' : GSt P}
    {sb : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool}
    (h : JauneConsensus.Gloas.stateTransition ctx s sb v = .ok s') : BuilderIdentityStable s s' := by
  obtain ⟨m, hm, hb⟩ := stateTransition_split h
  have hbm := processSlots_identityStable hm
  have := processBlock_identityStable hspe hdelay hb
  unfold BuilderIdentityStable at this ⊢
  rw [hbm] at this
  exact this

end JauneConsensus.Facts.Gloas.Inv
