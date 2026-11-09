import JauneConsensus.Facts.Gloas.InvariantsRefs

/-!
# G3-07: preservation (goal `eip8282-gloas-cross-layer-v1`, G3a)

**G3-07 NoLiveWeightOnLatestBid** (rev-3 form) with the auxiliary **FutureEmpty**:

* after a block, `L` is the block's bid, at the current slot's entry; that entry is `L`'s own
  with weight `0` (written by the bid, and no attestation of the block can weigh the current
  slot's entry since `1 ≤ MIN_ATTESTATION_INCLUSION_DELAY`), or empty (a self-slash in the block,
  or a value-`0` bid, which writes nothing: the entry was empty, `FutureEmpty`, because the block's
  parent is older than its slot). So `processBlock_noLiveWeight` needs FutureEmpty at the
  pre-state, not G3-07;
* `process_slots` keeps G3-07 and FutureEmpty: the entries move down one epoch at an epoch
  boundary together with `L`'s window index (`processSlots_noLiveWeight`).
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

theorem processBlockHeader_lt {s s' : GSt P} {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlockHeader s blk = .ok s') :
    s.latest_block_header.slot.toNat < blk.slot.toNat := by
  unfold JauneConsensus.Gloas.processBlockHeader at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, h2, _⟩ := bind_eq_ok_iff.mp h
  exact of_decide_eq_true (require_ok h2)

/-- A payment entry is kept or emptied. -/
def PayKeep (s s' : GSt P) : Prop :=
  ∀ j : Nat, s'.builder_pending_payments.toArray[j]? = s.builder_pending_payments.toArray[j]? ∨
    s'.builder_pending_payments.toArray[j]? = some JauneConsensus.Gloas.BuilderPendingPayment.empty

theorem payKeep_refl (s : GSt P) : PayKeep s s := fun _ => Or.inl rfl

theorem payKeep_trans {a b c : GSt P} (h₁ : PayKeep a b) (h₂ : PayKeep b c) : PayKeep a c := by
  intro j
  rcases h₂ j with e | e
  · rw [e]; exact h₁ j
  · exact Or.inr e

theorem payKeep_of_eq {s s' : GSt P}
    (h : s'.builder_pending_payments = s.builder_pending_payments) : PayKeep s s' :=
  fun _ => Or.inl (by rw [h])

/-- Up to the bid, a block only keeps or empties payment entries. -/
theorem beforeBid_payKeep {ctx : Ctx} {s s1 s2 s3 : GSt P} {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h1 : JauneConsensus.Gloas.processParentExecutionPayload ctx s blk = .ok s1)
    (h2 : JauneConsensus.Gloas.processBlockHeader s1 blk = .ok s2)
    (h3 : JauneConsensus.Gloas.processWithdrawals s2 = .ok s3) : PayKeep s s3 := by
  have k1 : PayKeep s s1 := by
    rcases processParentExecutionPayload_cases h1 with ⟨hs1, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
    · rw [hs1]; exact payKeep_refl _
    obtain ⟨x, fx, hx⟩ := applyParentPrefix_split ha
    have kx : PayKeep s x := by
      rcases hx with ⟨idx, hset⟩ | ⟨_, rfl, _, _⟩ | rfl
      · obtain ⟨_, p, _, _, _, hemp, hoth⟩ := settleBuilderPayment_frame hset
        intro j
        by_cases hj : j = idx.toNat
        · subst hj; exact Or.inr hemp
        · exact Or.inl (hoth j hj)
      · exact payKeep_of_eq rfl
      · exact payKeep_refl _
    have hd' : d.builder_pending_payments = a.builder_pending_payments :=
      forIn_yield_inv (fun m => m.builder_pending_payments = a.builder_pending_payments) _
        (fun m _ m' hI hm => by
          show _ = _
          rw [(depReq_cases hm).1]; exact hI) _ _ _ hd rfl
    have he' : e.builder_pending_payments = d.builder_pending_payments :=
      forIn_yield_inv (fun m => m.builder_pending_payments = d.builder_pending_payments) _
        (fun m _ m' hI hm => by
          show _ = _
          rw [(exitReq_cases hm).1]; exact hI) _ _ _ he rfl
    have hs' := (applyParentSuffix_post hs).2.1
    exact payKeep_trans kx (payKeep_of_eq (by rw [hs', he', hd', fx.2.1]))
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have k2 : PayKeep s1 s2 := payKeep_of_eq (by rw [hm2])
  exact payKeep_trans k1 (payKeep_trans k2 (payKeep_of_eq (processWithdrawals_wq h3).2))

/-- After a block, `L`'s window index is the current slot's entry. -/
theorem bidIndex_of_slot {s : GSt P} (hL : s.latest_execution_payload_bid.slot = s.slot) :
    bidIndex s = some (P.SLOTS_PER_EPOCH + s.slot.toNat % P.SLOTS_PER_EPOCH) := by
  unfold bidIndex curEpoch; simp only []; rw [hL]; simp

/-- **G3-07 and FutureEmpty over `process_block`** (from FutureEmpty at the pre-state; needs
`1 ≤ MIN_ATTESTATION_INCLUSION_DELAY` and `0 < SLOTS_PER_EPOCH`). -/
theorem processBlock_noLiveWeight (hdel : 1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s s' : GSt P}
    {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') (hfe : FutureEmpty s) :
    NoLiveWeightOnLatestBid s' ∧ FutureEmpty s' := by
  have hsl := processBlock_slots h
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  have k3 := beforeBid_payKeep h1 h2 h3
  have hlt := processBlockHeader_lt h2
  obtain ⟨hbs, _, hm2⟩ := processBlockHeader_post h2
  have hs1 : s1.slot = s.slot := by
    rcases processParentExecutionPayload_cases h1 with ⟨hs1, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
    · rw [hs1]
    · exact (parentFull_frame ha hd he hs).2.2.2.2.2
  have hh1 : s1.latest_block_header.slot = s.latest_block_header.slot := by
    rcases processParentExecutionPayload_cases h1 with ⟨hs1, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
    · rw [hs1]
    · exact (parentFull_frame ha hd he hs).2.2.2.2.1
  have w3 := processWithdrawals_wFrame _ _ h3
  have hs3 : s3.slot = s.slot := by rw [w3.2.2.2.1, show s2.slot = s1.slot by rw [hm2], hs1]
  have b4 := processExecutionPayloadBid_post h4
  obtain ⟨hL4, hbslot, _, _, _, _, _, hs4, _, _, hnp, hpp⟩ := id b4
  have f5 := processRandao_invFrame _ _ _ _ h5
  have f6 := processEth1Data_invFrame _ _ _ h6
  obtain ⟨c7, _, hp7⟩ := processOperations_ops _ _ _ _ _ h7
  have f8 := processSyncAggregate_invFrame _ _ _ _ h8
  have hs6 : s6.slot = s.slot := by rw [f6.2.2.2.2.2.2.1, f5.2.2.2.2.2.2.1, hs4, hs3]
  set K := P.SLOTS_PER_EPOCH + s.slot.toNat % P.SLOTS_PER_EPOCH with hK
  -- the current slot's entry before the bid is empty
  have e0 : s.builder_pending_payments.toArray[K]? =
      some JauneConsensus.Gloas.BuilderPendingPayment.empty := by
    refine hfe.2 ?_
    rw [← hh1, ← hs1, ← hbs]; exact hlt
  have e3 : s3.builder_pending_payments.toArray[K]? =
      some JauneConsensus.Gloas.BuilderPendingPayment.empty := by
    rcases k3 K with e | e
    · rw [e, e0]
    · exact e
  -- the entry after the operations
  have hpay6 : s6.builder_pending_payments = s4.builder_pending_payments := by
    rw [f6.2.1, f5.2.1]
  have hK3 : K = P.SLOTS_PER_EPOCH + s3.slot.toNat % P.SLOTS_PER_EPOCH := by rw [hs3]
  have hL' : s'.latest_execution_payload_bid = blk.body.signed_execution_payload_bid.message := by
    rw [f8.2.2.2.1, c7.2.1, f6.2.2.2.1, f5.2.2.2.1, hL4]
  have hslot' : s'.slot = s.slot := hsl.1
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [bidIndex_of_slot (by rw [hL', hbslot, hs3, hslot'])] at hk
    cases hk
    rw [hslot']
    have hpay' : s'.builder_pending_payments = s7.builder_pending_payments := f8.2.1
    rw [hpay']
    have step7 := hp7 K
    rw [hpay6] at step7
    rw [hL']
    by_cases hv : U64.zero < blk.body.signed_execution_payload_bid.message.value
    · obtain ⟨pp, hidx, _⟩ := hpp hv
      rw [← hK3] at hidx
      rcases step7 with e | e | ⟨_, _, _, _, _, hj⟩
      · rw [e, hidx]
        exact ⟨_, rfl, rfl, Or.inl ⟨hv, rfl⟩⟩
      · rw [e]; exact ⟨_, rfl, rfl, Or.inr rfl⟩
      · exact absurd (by rw [hs6]) (hj hdel hspe)
    · have hp4 := hnp hv
      rw [hp4] at step7
      rcases step7 with e | e | ⟨_, _, _, _, _, hj⟩
      · rw [e, e3]; exact ⟨_, rfl, rfl, Or.inr rfl⟩
      · rw [e]; exact ⟨_, rfl, rfl, Or.inr rfl⟩
      · exact absurd (by rw [hs6]) (hj hdel hspe)
  · intro j hj hjs
    rw [hslot'] at hjs
    have ej : s.builder_pending_payments.toArray[P.SLOTS_PER_EPOCH + j]? =
        some JauneConsensus.Gloas.BuilderPendingPayment.empty := hfe.1 j hj hjs
    have ej3 : s3.builder_pending_payments.toArray[P.SLOTS_PER_EPOCH + j]? =
        some JauneConsensus.Gloas.BuilderPendingPayment.empty := by
      rcases k3 (P.SLOTS_PER_EPOCH + j) with e | e
      · rw [e, ej]
      · exact e
    have hne : P.SLOTS_PER_EPOCH + j ≠ K := by omega
    have ej4 : s4.builder_pending_payments.toArray[P.SLOTS_PER_EPOCH + j]? =
        some JauneConsensus.Gloas.BuilderPendingPayment.empty := by
      by_cases hv : U64.zero < blk.body.signed_execution_payload_bid.message.value
      · obtain ⟨_, _, hoth⟩ := hpp hv
        rw [hoth _ (by rw [← hK3]; exact hne)]; exact ej3
      · rw [hnp hv]; exact ej3
    rw [f8.2.1]
    have step7 := hp7 (P.SLOTS_PER_EPOCH + j)
    rw [hpay6, ej4] at step7
    rcases step7 with e | e | ⟨p0, _, hp0, _, hst, _⟩
    · exact e
    · exact e
    · cases hp0
      rcases hst.2.2 with e | e
      · rw [‹s7.builder_pending_payments.toArray[_]? = some _›, e]
      · exact absurd e (by decide)
  · intro hlt'
    rw [hsl.2, hslot'] at hlt'
    exact absurd hlt' (Nat.lt_irrefl _)

/-! ## `process_slots` -/

theorem shifted_lo {A : Array JauneConsensus.Gloas.BuilderPendingPayment} {n k : Nat}
    (hA : A.size = 2 * n) (hk : k < n) :
    (A.extract n A.size ++ Array.replicate n JauneConsensus.Gloas.BuilderPendingPayment.empty)[k]? =
      A[n + k]? := by
  rw [Array.getElem?_append_left (by simp [hA]; omega)]
  rw [Array.getElem?_extract]
  simp only [hA]
  rw [if_pos (by omega)]

theorem shifted_hi {A : Array JauneConsensus.Gloas.BuilderPendingPayment} {n k : Nat}
    (hA : A.size = 2 * n) (hk1 : n ≤ k) (hk2 : k < 2 * n) :
    (A.extract n A.size ++ Array.replicate n JauneConsensus.Gloas.BuilderPendingPayment.empty)[k]? =
      some JauneConsensus.Gloas.BuilderPendingPayment.empty := by
  have hs : (A.extract n A.size).size = n := by simp [hA]; omega
  rw [Array.getElem?_append_right (by rw [hs]; exact hk1), hs, Array.getElem?_replicate,
    if_pos (by omega)]

theorem div_succ_of_mod_ne {t n : Nat} (h : (t + 1) % n ≠ 0) :
    (t + 1) / n = t / n ∧ (t + 1) % n = t % n + 1 := by
  have hd := Nat.succ_div_of_mod_ne_zero h
  refine ⟨hd, ?_⟩
  have h1 := Nat.div_add_mod t n
  have h2 := Nat.div_add_mod (t + 1) n
  rw [hd] at h2
  omega

/-- One slot iteration keeps G3-07 and FutureEmpty. -/
theorem slotIter_noLiveWeight (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {st st1 st2 : GSt P}
    {next : U64} (hI : NoLiveWeightOnLatestBid st ∧ FutureEmpty st) (f1 : InvFrame st st1)
    (hn : next.toNat = st.slot.toNat + 1)
    (hc : (st2 = st1 ∧ next.toNat % P.SLOTS_PER_EPOCH ≠ 0) ∨
      (next.toNat % P.SLOTS_PER_EPOCH = 0 ∧ JauneConsensus.Gloas.processEpoch ctx st1 = .ok st2)) :
    NoLiveWeightOnLatestBid { st2 with slot := next } ∧ FutureEmpty { st2 with slot := next } := by
  obtain ⟨g7, fe⟩ := hI
  have hL2 : st2.latest_execution_payload_bid = st.latest_execution_payload_bid :=
    (slotIter_core f1 hc).2.1
  have hH2 : st2.latest_block_header.slot = st.latest_block_header.slot :=
    (slotIter_core f1 hc).2.2.2.1
  rcases hc with ⟨rfl, hne⟩ | ⟨h0, he⟩
  · -- inside an epoch: same window, same entries
    rw [hn] at hne
    obtain ⟨hdiv, hmod⟩ := div_succ_of_mod_ne hne
    have hp : st2.builder_pending_payments = st.builder_pending_payments := f1.2.1
    have hbi : bidIndex { st2 with slot := next } = bidIndex st := by
      unfold bidIndex curEpoch; simp only []; rw [hL2, hn, hdiv]
    refine ⟨fun k hk => ?_, fun j hj hjs => ?_, fun _ => ?_⟩
    · rw [hbi] at hk
      show ∃ E, st2.builder_pending_payments.toArray[k]? = some E ∧ _
      rw [hp, hL2]; exact g7 k hk
    · show st2.builder_pending_payments.toArray[_]? = _
      simp only [] at hjs
      rw [hn, hmod] at hjs
      rw [hp]; exact fe.1 j hj (by omega)
    · show st2.builder_pending_payments.toArray[_]? = _
      simp only []
      rw [hn, hmod, hp]
      have := Nat.mod_lt (st.slot.toNat + 1) hspe
      exact fe.1 _ (by omega) (by omega)
  · -- an epoch boundary: the payments move down one epoch with the window
    obtain ⟨a, b, fa, hb, fb⟩ := processEpoch_phases he
    obtain ⟨_, _, _, _, hP⟩ := processBuilderPendingPayments_frame hb
    have hsz : a.builder_pending_payments.toArray.size = 2 * P.SLOTS_PER_EPOCH :=
      a.builder_pending_payments.size_eq
    have hpa : a.builder_pending_payments = st.builder_pending_payments := by
      rw [fa.2.1, f1.2.1]
    have hp2 : st2.builder_pending_payments.toArray =
        a.builder_pending_payments.toArray.extract P.SLOTS_PER_EPOCH
          a.builder_pending_payments.toArray.size ++
        Array.replicate P.SLOTS_PER_EPOCH JauneConsensus.Gloas.BuilderPendingPayment.empty := by
      rw [fb.2.1, hP]
    have hdiv : next.toNat / P.SLOTS_PER_EPOCH = st.slot.toNat / P.SLOTS_PER_EPOCH + 1 := by
      rw [hn]; rw [hn] at h0; exact Nat.succ_div_of_mod_eq_zero h0
    refine ⟨fun k hk => ?_, fun j hj hjs => ?_, fun _ => ?_⟩
    · show ∃ E, st2.builder_pending_payments.toArray[k]? = some E ∧ _
      rw [hp2, hL2]
      unfold bidIndex curEpoch at hk
      simp only [] at hk
      rw [hL2, hdiv] at hk
      have hLm := Nat.mod_lt st.latest_execution_payload_bid.slot.toNat hspe
      split at hk
      · cases hk
        rw [shifted_hi hsz (by omega) (by omega)]
        exact ⟨_, rfl, rfl, Or.inr rfl⟩
      · split at hk
        · rename_i hne1 heq
          cases hk
          rw [shifted_lo hsz hLm, hpa]
          exact g7 _ (by unfold bidIndex curEpoch; simp only []; rw [if_pos (by omega)])
        · cases hk
    · show st2.builder_pending_payments.toArray[_]? = _
      rw [hp2]; exact shifted_hi hsz (by omega) (by omega)
    · show st2.builder_pending_payments.toArray[_]? = _
      simp only []
      rw [hp2, h0]; exact shifted_hi hsz (by omega) (by omega)

/-- **G3-07 and FutureEmpty over `process_slots`.** -/
theorem processSlots_noLiveWeight (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s s' : GSt P}
    {slot : U64} (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s')
    (hu : NoLiveWeightOnLatestBid s ∧ FutureEmpty s) :
    NoLiveWeightOnLatestBid s' ∧ FutureEmpty s' :=
  processSlots_ind (ctx := ctx) (fun m => NoLiveWeightOnLatestBid m ∧ FutureEmpty m)
    (fun _ _ _ _ hI f1 hn hc => slotIter_noLiveWeight hspe hI f1 hn hc) h hu

/-- **G3-07 and FutureEmpty over `state_transition`.** -/
theorem stateTransition_noLiveWeight (hdel : 1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s s' : GSt P}
    {sb : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool}
    (h : JauneConsensus.Gloas.stateTransition ctx s sb v = .ok s')
    (hu : NoLiveWeightOnLatestBid s ∧ FutureEmpty s) :
    NoLiveWeightOnLatestBid s' ∧ FutureEmpty s' := by
  obtain ⟨m, hm, hb⟩ := stateTransition_split h
  exact processBlock_noLiveWeight hdel hspe hb (processSlots_noLiveWeight hspe hm hu).2

end JauneConsensus.Facts.Gloas.Inv
