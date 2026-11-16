import JauneConsensus.Facts.Gloas.InvariantsQueues

/-!
# G3-03 and G3-04: preservation (goal `eip8282-gloas-cross-layer-v1`, G3a)

* **LatestBidBuilderActive** (auxiliary: a paying `L`'s builder is not exiting) holds after every
  block from any pre-state (the bid checks `is_active_builder`, and nothing after the bid writes
  the registry), and `process_slots` keeps it.
* **G3-03 PendingRefsInRange** is preserved by `process_slots` given quorum positivity
  (`2 * SLOTS_PER_EPOCH ≤ EFFECTIVE_BALANCE_INCREMENT`: an unattested or emptied entry is never
  appended at a rotation), and by `process_block` given LatestBidBuilderActive (the direct append
  names `L`'s builder).
* **G3-04 ExitedHaveNoPending** is preserved by `process_slots`, and by `process_block` given
  LatestBidBuilderActive (the direct append charges `L`'s builder; an exit is initiated only with
  nothing pending; the bid charges an active builder).
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-! ## LatestBidBuilderActive -/

theorem processBlock_latestBidBuilderActive {ctx : Ctx} {s s' : GSt P}
    {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') : LatestBidBuilderActive s' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  have b4 := processExecutionPayloadBid_post h4
  have c := afterBid_core h5 h6 h7 h8
  intro hv
  rw [c.2.1, b4.1] at hv ⊢
  rw [c.1, b4.2.2.2.2.1]
  rcases b4.2.2.2.1 with ⟨_, hz⟩ | ⟨b, hb, hf, _⟩
  · rw [hz] at hv; exact absurd hv (by decide)
  · exact ⟨b, hb, hf⟩

theorem processSlots_latestBidBuilderActive {ctx : Ctx} {s s' : GSt P} {slot : U64}
    (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s') (hu : LatestBidBuilderActive s) :
    LatestBidBuilderActive s' :=
  processSlots_ind (ctx := ctx) LatestBidBuilderActive
    (fun _ _ _ _ hI f1 _ hc => by
      obtain ⟨hb, hl, _, _, _⟩ := slotIter_core f1 hc
      intro hv
      show ∃ b, _ ∧ _
      simp only [] at hv ⊢
      rw [hl] at hv ⊢; rw [hb]; exact hI hv) h hu

/-! ## Entrywise comparisons -/

theorem list_sum_le_of_entries {α : Type} (f : α → Nat) :
    ∀ (l l' : List α), l.length = l'.length →
      (∀ (j : Nat) (x y : α), l[j]? = some x → l'[j]? = some y → f y ≤ f x) →
      (l'.map f).sum ≤ (l.map f).sum
  | [], [], _, _ => le_refl _
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: l, y :: l', h, hle => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := hle 0 x y rfl rfl
    have h2 := list_sum_le_of_entries f l l' (by simpa using h)
      (fun j a b ha hb => hle (j + 1) a b (by simpa using ha) (by simpa using hb))
    omega

theorem pendP_le_of_entries {a b : SszVector JauneConsensus.Gloas.BuilderPendingPayment (2 * P.SLOTS_PER_EPOCH)}
    (hle : ∀ (j : Nat) (x y : JauneConsensus.Gloas.BuilderPendingPayment),
      a.toArray[j]? = some x → b.toArray[j]? = some y →
      ∀ i, wAmt i y.withdrawal ≤ wAmt i x.withdrawal) (i : Nat) :
    pendP b.toArray.toList i ≤ pendP a.toArray.toList i :=
  list_sum_le_of_entries (fun p : JauneConsensus.Gloas.BuilderPendingPayment => wAmt i p.withdrawal) _ _
    (by simp [a.size_eq, b.size_eq])
    (fun j x y hx hy => hle j x y (by simpa using hx) (by simpa using hy) i)

/-! ## G3-03 -/

theorem refs_mono {s : GSt P} {n : Nat} (h : PendingRefsInRange s)
    (hn : s.builders.toArray.size ≤ n) :
    (∀ w ∈ s.builder_pending_withdrawals.toArray.toList, w.builder_index.toNat < n) ∧
      ∀ p ∈ s.builder_pending_payments.toArray.toList,
        p ≠ JauneConsensus.Gloas.BuilderPendingPayment.empty → p.withdrawal.builder_index.toNat < n :=
  ⟨fun w hw => Nat.lt_of_lt_of_le (h.1 w hw) hn, fun p hp hne => Nat.lt_of_lt_of_le (h.2 p hp hne) hn⟩

theorem refs_of_queues {s' : GSt P}
    (hW : ∀ w ∈ s'.builder_pending_withdrawals.toArray.toList,
      w.builder_index.toNat < s'.builders.toArray.size)
    (hP : ∀ p ∈ s'.builder_pending_payments.toArray.toList,
      p ≠ JauneConsensus.Gloas.BuilderPendingPayment.empty →
        p.withdrawal.builder_index.toNat < s'.builders.toArray.size) :
    PendingRefsInRange s' := ⟨hW, hP⟩

theorem refs_of_inv {s s' : GSt P} (hf : InvFrame s s') (h : PendingRefsInRange s) :
    PendingRefsInRange s' := by
  unfold PendingRefsInRange; rw [hf.1, hf.2.1, hf.2.2.1]; exact h

theorem mem_of_getElem?' {α : Type} {a : Array α} {j : Nat} {x : α} (h : a[j]? = some x) :
    x ∈ a.toList := by
  rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? h

theorem getElem?_of_mem' {α : Type} {a : Array α} {x : α} (h : x ∈ a.toList) :
    ∃ j : Nat, a[j]? = some x := by
  rw [Array.mem_toList_iff] at h; exact Array.mem_iff_getElem?.mp h

theorem empty_amount_zero :
    JauneConsensus.Gloas.BuilderPendingPayment.empty.withdrawal.amount = U64.zero := rfl

theorem ne_empty_of_amount {p : JauneConsensus.Gloas.BuilderPendingPayment}
    (h : U64.zero < p.withdrawal.amount) : p ≠ JauneConsensus.Gloas.BuilderPendingPayment.empty := by
  intro e; subst e; exact absurd h (by decide)

/-- `settle_builder_payment` keeps G3-03 and every `pend`. -/
theorem settle_refs_pend {s x : GSt P} {idx : U64}
    (h : JauneConsensus.Gloas.settleBuilderPayment s idx = .ok x) :
    x.builders = s.builders ∧ (PendingRefsInRange s → PendingRefsInRange x) ∧ ∀ i, pend x i = pend s i := by
  obtain ⟨hb, p, hp, hpos, hnpos, hemp, hoth⟩ := settleBuilderPayment_frame h
  have hP := pendP_of_one hp hemp hoth
  refine ⟨hb, fun hr => ?_, fun i => ?_⟩
  · refine ⟨fun w hw => ?_, fun q hq hne => ?_⟩
    · rw [hb]
      by_cases ha : U64.zero < p.withdrawal.amount
      · rw [hpos ha] at hw
        simp only [ProgressiveListS.push, Array.toList_push, List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact hr.1 w hw
        · exact hr.2 p (mem_of_getElem?' hp) (ne_empty_of_amount ha)
      · rw [hnpos ha] at hw; exact hr.1 w hw
    · rw [hb]
      obtain ⟨j, hj⟩ := getElem?_of_mem' hq
      by_cases hji : j = idx.toNat
      · subst hji; rw [hemp] at hj; cases hj; exact absurd rfl hne
      · rw [hoth j hji] at hj; exact hr.2 q (mem_of_getElem?' hj) hne
  · have e := hP i
    rw [wAmt_empty] at e
    unfold pend
    by_cases ha : U64.zero < p.withdrawal.amount
    · rw [hpos ha]
      simp only [ProgressiveListS.push, Array.toList_push, pendW_append, pendW_cons]
      simp only [pendW, List.map_nil, List.sum_nil]
      omega
    · rw [hnpos ha]
      have : wAmt i p.withdrawal = 0 := by
        have := wAmt_le i p.withdrawal
        have : p.withdrawal.amount.toNat = 0 := by
          simp only [U64.lt_iff, U64.toNat_zero] at ha; omega
        omega
      omega

/-- Transfer of G3-03: every withdrawal is old or in range; every non-empty payment carries an
old non-empty entry's builder index or is in range; the registry does not shrink. -/
theorem refs_transfer {s s' : GSt P} (hsz : s.builders.toArray.size ≤ s'.builders.toArray.size)
    (hW : ∀ w ∈ s'.builder_pending_withdrawals.toArray.toList,
      w ∈ s.builder_pending_withdrawals.toArray.toList ∨
        w.builder_index.toNat < s'.builders.toArray.size)
    (hP : ∀ (j : Nat) (p' : JauneConsensus.Gloas.BuilderPendingPayment),
      s'.builder_pending_payments.toArray[j]? = some p' →
      p' ≠ JauneConsensus.Gloas.BuilderPendingPayment.empty →
      (∃ p, s.builder_pending_payments.toArray[j]? = some p ∧
          p ≠ JauneConsensus.Gloas.BuilderPendingPayment.empty ∧
          p.withdrawal.builder_index = p'.withdrawal.builder_index) ∨
        p'.withdrawal.builder_index.toNat < s'.builders.toArray.size)
    (h : PendingRefsInRange s) : PendingRefsInRange s' := by
  refine ⟨fun w hw => ?_, fun p' hp' hne => ?_⟩
  · rcases hW w hw with hw | hw
    · exact Nat.lt_of_lt_of_le (h.1 w hw) hsz
    · exact hw
  · obtain ⟨j, hj⟩ := getElem?_of_mem' hp'
    rcases hP j p' hj hne with ⟨p, hp, hpn, he⟩ | hlt
    · rw [← he]; exact Nat.lt_of_lt_of_le (h.2 p (mem_of_getElem?' hp) hpn) hsz
    · exact hlt

/-- Transfer of G3-03 when only the registry changes, and grows. -/
theorem refs_of_builders {s s' : GSt P} (hm : s' = { s with builders := s'.builders })
    (hsz : s.builders.toArray.size ≤ s'.builders.toArray.size) (h : PendingRefsInRange s) :
    PendingRefsInRange s' := by
  have hw : s'.builder_pending_withdrawals = s.builder_pending_withdrawals := by rw [hm]
  have hp : s'.builder_pending_payments = s.builder_pending_payments := by rw [hm]
  exact refs_transfer hsz (fun w hw' => Or.inl (by rw [← hw]; exact hw'))
    (fun j p' hj hne => Or.inl ⟨p', by rw [← hp]; exact hj, hne, rfl⟩) h

theorem depReq_size {ctx : Ctx} {m m' : GSt P} {r : JauneConsensus.Gloas.BuilderDepositRequest}
    (h : JauneConsensus.Gloas.processBuilderDepositRequest ctx m r = .ok m') :
    m.builders.toArray.size ≤ m'.builders.toArray.size := by
  rcases (depReq_cases h).2 with heq | ⟨_, _, _, _, _, hsz, _⟩ | ⟨_, _, _, _, _, _, _, _, hsz, _⟩
  · rw [heq]
  · rw [hsz]
  · exact hsz

theorem exitReq_size {cfg : Config} {m m' : GSt P} {r : JauneConsensus.Gloas.BuilderExitRequest}
    (h : JauneConsensus.Gloas.processBuilderExitRequest cfg m r = .ok m') :
    m.builders.toArray.size ≤ m'.builders.toArray.size := by
  rcases (exitReq_cases h).2 with heq | ⟨_, _, _, _, _, _, _, _, hsz, _⟩
  · rw [heq]
  · rw [hsz]

/-- `quorumPositive`: `2 * SLOTS_PER_EPOCH ≤ EFFECTIVE_BALANCE_INCREMENT` makes the builder
payment quorum positive (`get_total_balance` is at least `EFFECTIVE_BALANCE_INCREMENT`). -/
theorem quorum_pos (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) {s : GSt P}
    {q : U64} (h : JauneConsensus.Gloas.getBuilderPaymentQuorumThreshold s = .ok q) :
    0 < q.toNat := by
  unfold JauneConsensus.Gloas.getBuilderPaymentQuorumThreshold at h
  obtain ⟨tot, ht, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨per, hper, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨six, hsix, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨qq, hqq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ten, hten, h⟩ := bind_eq_ok_iff.mp h
  have htot : P.EFFECTIVE_BALANCE_INCREMENT ≤ tot.toNat := by
    unfold JauneConsensus.Gloas.getTotalActiveBalance at ht
    obtain ⟨_, _, ht⟩ := bind_eq_ok_iff.mp ht
    obtain ⟨_, _, ht⟩ := bind_eq_ok_iff.mp ht
    unfold JauneConsensus.Gloas.getTotalBalance at ht
    obtain ⟨_, _, ht⟩ := bind_eq_ok_iff.mp ht
    obtain ⟨inc, hinc, ht⟩ := bind_eq_ok_iff.mp ht
    cases ht
    have := c64_toNat hinc
    split
    · rename_i hlt; have : inc.toNat < _ := hlt; omega
    · omega
  rw [U64.toNat_div? h, U64.toNat_mul? hqq, c64_toNat hsix, c64_toNat hten, U64.toNat_div? hper,
    c64_toNat hspe]
  have hs0 : 0 < P.SLOTS_PER_EPOCH := by
    have := U64.toNat_div? hper; rw [c64_toNat hspe] at this
    have h0 := (U64.div?_ok_iff (a := tot) (b := spe) (site := "get_builder_payment_quorum_threshold")).mp
      ⟨_, hper⟩
    rw [c64_toNat hspe] at h0; omega
  have h2 : 2 ≤ tot.toNat / P.SLOTS_PER_EPOCH := by
    rw [Nat.le_div_iff_mul_le hs0]; omega
  unfold JauneConsensus.Gloas.BUILDER_PAYMENT_THRESHOLD_NUMERATOR
    JauneConsensus.Gloas.BUILDER_PAYMENT_THRESHOLD_DENOMINATOR
  omega

theorem mem_of_mem_extract' {α : Type} {a : Array α} {i j : Nat} {x : α}
    (h : x ∈ (a.extract i j).toList) : x ∈ a.toList := by
  simp only [Array.toList_extract, List.extract] at h
  exact List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem filter_map_sum_le {α : Type} (c : α → Bool) (f : α → Nat) :
    ∀ l : List α, ((l.filter c).map f).sum ≤ (l.map f).sum
  | [] => le_refl _
  | a :: l => by
    have := filter_map_sum_le c f l
    by_cases hc : c a = true
    · simp [hc]; omega
    · simp [hc]; omega

/-- `process_builder_pending_payments` keeps G3-03 (given a positive quorum) and does not raise
any `pend`. -/
theorem rotation_refs_pend (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    {cfg : Config} {a b : GSt P}
    (h : JauneConsensus.Gloas.processBuilderPendingPayments cfg a = .ok b) :
    b.builders = a.builders ∧ (PendingRefsInRange a → PendingRefsInRange b) ∧
      ∀ i, pend b i ≤ pend a i := by
  obtain ⟨hb, q, hqh, hW, hP⟩ := processBuilderPendingPayments_frame h
  have hq0 := quorum_pos hq hqh
  have hsz := a.builder_pending_payments.size_eq
  refine ⟨hb, fun hr => ?_, fun i => ?_⟩
  · refine ⟨fun w hw => ?_, fun p hp hne => ?_⟩
    · rw [hb]
      rw [hW] at hw
      simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hw
      rcases hw with hw | ⟨p, ⟨hp, hpq⟩, rfl⟩
      · exact hr.1 w hw
      · have hpm : p ∈ a.builder_pending_payments.toArray.toList := by
          exact mem_of_mem_extract' hp
        refine hr.2 p hpm (fun e => ?_)
        subst e
        have : q.toNat ≤ 0 := hpq
        omega
    · rw [hb]
      rw [hP] at hp
      simp only [Array.toList_append, List.mem_append, Array.toList_replicate, List.mem_replicate] at hp
      rcases hp with hp | ⟨_, rfl⟩
      · exact hr.2 p (mem_of_mem_extract' hp) hne
      · exact absurd rfl hne
  · unfold pend
    rw [hW, hP]
    have hsplit : a.builder_pending_payments.toArray.toList =
        (a.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH).toList ++
          (a.builder_pending_payments.toArray.extract P.SLOTS_PER_EPOCH
            a.builder_pending_payments.toArray.size).toList := by
      have hl : a.builder_pending_payments.toArray.toList.length =
          a.builder_pending_payments.toArray.size := Array.length_toList
      simp only [Array.toList_extract, List.extract, List.drop_zero, ← hl, Nat.sub_zero]
      have e : (a.builder_pending_payments.toArray.toList.drop P.SLOTS_PER_EPOCH).take
          (a.builder_pending_payments.toArray.toList.length - P.SLOTS_PER_EPOCH) =
          a.builder_pending_payments.toArray.toList.drop P.SLOTS_PER_EPOCH :=
        List.take_of_length_le (by simp)
      rw [e]
      exact (List.take_append_drop _ _).symm
    rw [hsplit, pendW_append, Array.toList_append, pendP_append, pendP_append]
    have hrep : pendP (Array.replicate P.SLOTS_PER_EPOCH
        JauneConsensus.Gloas.BuilderPendingPayment.empty).toList i = 0 := by
      simp [pendP, wAmt_empty]
    rw [hrep]
    have hfil : pendW (((a.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH).toList.filter
        (fun p => decide (q ≤ p.weight))).map (·.withdrawal)) i ≤
        pendP (a.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH).toList i := by
      unfold pendW pendP
      rw [List.map_map]
      exact filter_map_sum_le _ _ _
    omega

/-! ## G3-03 and G3-04 over the steps -/

theorem refs_of_eqs {s s' : GSt P} (hb : s'.builders = s.builders)
    (hw : s'.builder_pending_withdrawals = s.builder_pending_withdrawals)
    (hp : s'.builder_pending_payments = s.builder_pending_payments) (h : PendingRefsInRange s) :
    PendingRefsInRange s' := by
  unfold PendingRefsInRange; rw [hb, hw, hp]; exact h

theorem pend_of_eqs {s s' : GSt P}
    (hw : s'.builder_pending_withdrawals = s.builder_pending_withdrawals)
    (hp : s'.builder_pending_payments = s.builder_pending_payments) (i : Nat) :
    pend s' i = pend s i := by
  unfold pend; rw [hw, hp]

theorem x04_of {s s' : GSt P} (hb : s'.builders = s.builders) (hp : ∀ i, pend s' i ≤ pend s i)
    (h : ExitedHaveNoPending s) : ExitedHaveNoPending s' := by
  intro i b hbi hne
  rw [hb] at hbi
  have := h i b hbi hne
  have := hp i
  omega

theorem x04_of_eqs {s s' : GSt P} (hb : s'.builders = s.builders)
    (hw : s'.builder_pending_withdrawals = s.builder_pending_withdrawals)
    (hp : s'.builder_pending_payments = s.builder_pending_payments) (h : ExitedHaveNoPending s) :
    ExitedHaveNoPending s' :=
  x04_of hb (fun i => (pend_of_eqs hw hp i).le) h

/-- **G3-03 over `process_slots`** (needs quorum positivity). -/
theorem processSlots_pendingRefsInRange
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) {ctx : Ctx} {s s' : GSt P}
    {slot : U64} (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s')
    (hu : PendingRefsInRange s) : PendingRefsInRange s' :=
  processSlots_ind (ctx := ctx) PendingRefsInRange
    (fun _ st1 st2 _ hI f1 _ hc => by
      have r1 := refs_of_inv f1 hI
      show PendingRefsInRange st2
      rcases hc with ⟨rfl, _⟩ | ⟨_, he⟩
      · exact r1
      · obtain ⟨a, b, fa, hb, fb⟩ := processEpoch_phases he
        exact refs_of_inv fb ((rotation_refs_pend hq hb).2.1 (refs_of_inv fa r1))) h hu

/-- **G3-04 over `process_slots`.** -/
theorem processSlots_exitedHaveNoPending
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) {ctx : Ctx} {s s' : GSt P}
    {slot : U64} (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s')
    (hu : ExitedHaveNoPending s) : ExitedHaveNoPending s' :=
  processSlots_ind (ctx := ctx) ExitedHaveNoPending
    (fun _ st1 st2 _ hI f1 _ hc => by
      have r1 := x04_of_eqs f1.1 f1.2.2.1 f1.2.1 hI
      show ExitedHaveNoPending st2
      rcases hc with ⟨rfl, _⟩ | ⟨_, he⟩
      · exact r1
      · obtain ⟨a, b, fa, hb, fb⟩ := processEpoch_phases he
        have ra := x04_of_eqs fa.1 fa.2.2.1 fa.2.1 r1
        obtain ⟨hbb, _, hpp⟩ := rotation_refs_pend hq hb
        exact x04_of_eqs fb.1 fb.2.2.1 fb.2.1 (x04_of hbb hpp ra)) h hu

theorem directAppend_pend (s : GSt P) (i : Nat) :
    pend (directAppend s) i = pend s i + wAmt i (bidWithdrawal s.latest_execution_payload_bid) := by
  unfold pend directAppend
  simp only [ProgressiveListS.push, Array.toList_push, pendW_append, pendW_cons, bidWithdrawal]
  simp only [pendW, List.map_nil, List.sum_nil]
  omega

/-- The parent payload keeps G3-03 and G3-04, given LatestBidBuilderActive. -/
theorem parent_refs_x04 {ctx : Ctx} {s s1 : GSt P} {blk : JauneConsensus.Gloas.BeaconBlock P}
    (hA : LatestBidBuilderActive s)
    (h1 : JauneConsensus.Gloas.processParentExecutionPayload ctx s blk = .ok s1) :
    (PendingRefsInRange s → PendingRefsInRange s1) ∧
      (ExitedHaveNoPending s → ExitedHaveNoPending s1) := by
  rcases processParentExecutionPayload_cases h1 with ⟨hs1, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · subst hs1; exact ⟨id, id⟩
  obtain ⟨x, fx, hx⟩ := applyParentPrefix_split ha
  -- the settlement
  have px : (PendingRefsInRange s → PendingRefsInRange x) ∧
      (ExitedHaveNoPending s → ExitedHaveNoPending x) := by
    rcases hx with ⟨idx, hset⟩ | ⟨hv, rfl, _, _⟩ | rfl
    · obtain ⟨hb, hr, hp⟩ := settle_refs_pend hset
      exact ⟨hr, x04_of hb (fun i => (hp i).le)⟩
    · obtain ⟨b, hb, hfar⟩ := hA hv
      refine ⟨fun hr => refs_transfer (s := s) (s' := directAppend s) (le_refl _) (fun w hw => ?_)
        (fun j p hj hne => Or.inl ⟨p, hj, hne, rfl⟩) hr, fun hx4 i c hc hne => ?_⟩
      · simp only [directAppend, ProgressiveListS.push, Array.toList_push, List.mem_append,
          List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact Or.inl hw
        · exact Or.inr (Array.getElem?_eq_some_iff.mp hb).1
      · change s.builders.toArray[i]? = some c at hc
        rw [directAppend_pend]
        have h0 := hx4 i c hc hne
        by_cases hi : s.latest_execution_payload_bid.builder_index.toNat = i
        · subst hi; rw [hb] at hc; cases hc; exact absurd hfar hne
        · have : wAmt i (bidWithdrawal s.latest_execution_payload_bid) = 0 := by
            unfold wAmt bidWithdrawal; rw [if_neg hi]
          omega
    · exact ⟨id, id⟩
  have pa : (PendingRefsInRange s → PendingRefsInRange a) ∧
      (ExitedHaveNoPending s → ExitedHaveNoPending a) :=
    ⟨fun hr => refs_of_inv fx (px.1 hr), fun h4 => x04_of_eqs fx.1 fx.2.2.1 fx.2.1 (px.2 h4)⟩
  -- the builder deposits
  have pd : (PendingRefsInRange a → PendingRefsInRange d) ∧
      (ExitedHaveNoPending a → ExitedHaveNoPending d) := by
    refine ⟨fun hr => forIn_yield_inv PendingRefsInRange _ (fun _ _ _ hI hm =>
      refs_of_builders (depReq_cases hm).1 (depReq_size hm) hI) _ _ _ hd hr,
      fun h4 => forIn_yield_inv ExitedHaveNoPending _ (fun m _ m' hI hm => ?_) _ _ _ hd h4⟩
    obtain ⟨hm', hcase⟩ := depReq_cases hm
    have hpe : ∀ i, pend m' i = pend m i :=
      pend_of_eqs (by rw [hm']) (by rw [hm'])
    intro i c hc hne
    rw [hpe]
    rcases hcase with heq | ⟨k, b, b', hb, hb', _, hoth, _, _, hwe⟩ |
        ⟨k, b', _, _, hb', _, _, hfar, _, hoth⟩
    · rw [heq] at hc; exact hI i c hc hne
    · by_cases hik : i = k
      · subst hik; rw [hb'] at hc; cases hc
        rcases hwe with hwe | ⟨hne', _, _⟩
        · exact hI i b hb (by rw [← hwe]; exact hne)
        · exact hI i b hb hne'
      · rw [hoth i hik] at hc; exact hI i c hc hne
    · by_cases hik : i = k
      · subst hik; rw [hb'] at hc; cases hc; exact absurd hfar hne
      · rw [hoth i hik] at hc; exact hI i c hc hne
  -- the builder exits
  have pe : (PendingRefsInRange d → PendingRefsInRange e) ∧
      (ExitedHaveNoPending d → ExitedHaveNoPending e) := by
    refine ⟨fun hr => forIn_yield_inv PendingRefsInRange _ (fun _ _ _ hI hm =>
      refs_of_builders (exitReq_cases hm).1 (exitReq_size hm) hI) _ _ _ he hr,
      fun h4 => forIn_yield_inv ExitedHaveNoPending _ (fun m _ m' hI hm => ?_) _ _ _ he h4⟩
    obtain ⟨hm', hcase⟩ := exitReq_cases hm
    have hpe : ∀ i, pend m' i = pend m i :=
      pend_of_eqs (by rw [hm']) (by rw [hm'])
    intro i c hc hne
    rw [hpe]
    rcases hcase with heq | ⟨k, b, w, hb, hb', _, ⟨bi, hbi, hpend⟩, _, _, hoth⟩
    · rw [heq] at hc; exact hI i c hc hne
    · by_cases hik : i = k
      · subst hik
        have := getPendingBalance_toNat hpend
        rw [U64.toNat_ofNat? hbi, U64.toNat_zero] at this
        exact this.symm
      · rw [hoth i hik] at hc; exact hI i c hc hne
  obtain ⟨hb, hp, hw, _⟩ := applyParentSuffix_post hs
  exact ⟨fun hr => refs_of_eqs hb hw hp (pe.1 (pd.1 (pa.1 hr))),
    fun h4 => x04_of_eqs hb hw hp (pe.2 (pd.2 (pa.2 h4)))⟩

/-- The rest of the block after the parent payload keeps G3-03 and G3-04. -/
theorem afterParent_refs_x04 {ctx : Ctx} {s1 s' : GSt P} {blk : JauneConsensus.Gloas.BeaconBlock P}
    {s2 s3 s4 s5 s6 s7 : GSt P} {ps : Slot}
    (h2 : JauneConsensus.Gloas.processBlockHeader s1 blk = .ok s2)
    (h3 : JauneConsensus.Gloas.processWithdrawals s2 = .ok s3)
    (h4 : JauneConsensus.Gloas.processExecutionPayloadBid ctx s3
      blk.body.signed_execution_payload_bid = .ok s4)
    (h5 : JauneConsensus.Gloas.processRandao ctx s4 blk.body = .ok s5)
    (h6 : JauneConsensus.Gloas.processEth1Data s5 blk.body = .ok s6)
    (h7 : JauneConsensus.Gloas.processOperations ctx s6 blk.body ps = .ok s7)
    (h8 : JauneConsensus.Gloas.processSyncAggregate ctx s7 blk.body.sync_aggregate = .ok s') :
    (PendingRefsInRange s1 → PendingRefsInRange s') ∧
      (ExitedHaveNoPending s1 → ExitedHaveNoPending s') := by
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have e2b : s2.builders = s1.builders := by rw [hm2]
  have e2w : s2.builder_pending_withdrawals = s1.builder_pending_withdrawals := by rw [hm2]
  have e2p : s2.builder_pending_payments = s1.builder_pending_payments := by rw [hm2]
  obtain ⟨⟨k, hk⟩, hq3⟩ := processWithdrawals_wq h3
  have w3 := processWithdrawals_wFrame _ _ h3
  have b4 := processExecutionPayloadBid_post h4
  obtain ⟨_, _, _, _, hb4, _, _, _, _, hw4, hnp, hpp⟩ := id b4
  have f5 := processRandao_invFrame _ _ _ _ h5
  have f6 := processEth1Data_invFrame _ _ _ h6
  obtain ⟨c7, hw7, hp7⟩ := processOperations_ops _ _ _ _ _ h7
  have f8 := processSyncAggregate_invFrame _ _ _ _ h8
  -- withdrawals: drop a prefix, registry kept with the same withdrawable epochs
  have t3 : (PendingRefsInRange s2 → PendingRefsInRange s3) ∧
      (ExitedHaveNoPending s2 → ExitedHaveNoPending s3) := by
    refine ⟨fun hr => refs_transfer (le_of_eq w3.2.2.2.2.2.1.symm) (fun w hw => ?_)
      (fun j p hj hne => Or.inl ⟨p, by rw [← hq3]; exact hj, hne, rfl⟩) hr, fun h4 i c hc hne => ?_⟩
    · rw [hk] at hw; exact Or.inl (List.mem_of_mem_drop hw)
    · have hi : i < s2.builders.toArray.size := by
        rw [← w3.2.2.2.2.2.1]; exact (Array.getElem?_eq_some_iff.mp hc).1
      obtain ⟨b0, hb0, hid⟩ := w3.2.2.2.2.2.2.1 i _ (Array.getElem?_eq_getElem hi)
      rw [hc] at hb0; cases hb0
      have h0 := h4 i _ (Array.getElem?_eq_getElem hi) (by rw [← hid.2]; exact hne)
      unfold pend at h0 ⊢
      rw [hk, hq3]
      have := pendW_drop_le s2.builder_pending_withdrawals.toArray.toList k i
      omega
  -- the bid: one entry, for an active builder
  have t4 : (PendingRefsInRange s3 → PendingRefsInRange s4) ∧
      (ExitedHaveNoPending s3 → ExitedHaveNoPending s4) := by
    by_cases hv : U64.zero < blk.body.signed_execution_payload_bid.message.value
    · obtain ⟨pp, hidx, hoth⟩ := hpp hv
      obtain ⟨bb, hbb, hfar, _⟩ : ∃ b, s3.builders.toArray[
          blk.body.signed_execution_payload_bid.message.builder_index.toNat]? = some b ∧
          b.withdrawable_epoch = FAR_FUTURE_EPOCH ∧ True := by
        rcases b4.2.2.2.1 with ⟨_, hz⟩ | ⟨b, hb, hf, _⟩
        · rw [hz] at hv; exact absurd hv (by decide)
        · exact ⟨b, hb, hf, trivial⟩
      have hlt : P.SLOTS_PER_EPOCH + s3.slot.toNat % P.SLOTS_PER_EPOCH <
          s3.builder_pending_payments.toArray.size := by
        rw [s3.builder_pending_payments.size_eq]
        have : 0 < P.SLOTS_PER_EPOCH := by
          have := (Array.getElem?_eq_some_iff.mp hidx).1
          rw [s4.builder_pending_payments.size_eq] at this; omega
        have := Nat.mod_lt s3.slot.toNat this; omega
      obtain ⟨x, hx⟩ : ∃ x, s3.builder_pending_payments.toArray[
          P.SLOTS_PER_EPOCH + s3.slot.toNat % P.SLOTS_PER_EPOCH]? = some x :=
        ⟨_, Array.getElem?_eq_getElem hlt⟩
      have hP := pendP_of_one hx hidx hoth
      refine ⟨fun hr => refs_transfer (by rw [hb4])
        (fun w hw => Or.inl (by rw [← hw4]; exact hw)) (fun j p hj hne => ?_) hr,
        fun h4 i c hc hne => ?_⟩
      · by_cases hjk : j = P.SLOTS_PER_EPOCH + s3.slot.toNat % P.SLOTS_PER_EPOCH
        · subst hjk; rw [hidx] at hj; cases hj
          exact Or.inr (by rw [hb4]; exact (Array.getElem?_eq_some_iff.mp hbb).1)
        · exact Or.inl ⟨p, by rw [← hoth j hjk]; exact hj, hne, rfl⟩
      · rw [hb4] at hc
        have h0 := h4 i c hc hne
        have hP' := hP i
        unfold pend at h0 ⊢
        rw [hw4]
        by_cases hi : blk.body.signed_execution_payload_bid.message.builder_index.toNat = i
        · subst hi; rw [hbb] at hc; cases hc; exact absurd hfar hne
        · have : wAmt i (bidWithdrawal blk.body.signed_execution_payload_bid.message) = 0 := by
            unfold wAmt bidWithdrawal; rw [if_neg hi]
          simp only [] at hP'
          omega
    · have hp4 := hnp hv
      exact ⟨refs_of_eqs hb4 hw4 hp4, x04_of_eqs hb4 hw4 hp4⟩
  -- the operations: entries kept, emptied, or reweighted
  have t7 : (PendingRefsInRange s6 → PendingRefsInRange s7) ∧
      (ExitedHaveNoPending s6 → ExitedHaveNoPending s7) := by
    refine ⟨fun hr => refs_transfer (le_of_eq (congrArg (·.toArray.size) c7.1).symm)
      (fun w hw => Or.inl (by rw [← hw7]; exact hw)) (fun j p hj hne => ?_) hr,
      x04_of c7.1 (fun i => ?_)⟩
    · rcases hp7 j with e | e | ⟨p0, p1, hp0, hp1, hst, _⟩
      · exact Or.inl ⟨p, by rw [← e]; exact hj, hne, rfl⟩
      · rw [e] at hj; cases hj; exact absurd rfl hne
      · rw [hp1] at hj; cases hj
        refine Or.inl ⟨p0, hp0, ?_, by rw [hst.1]⟩
        rcases hst.2.2 with e | e
        · subst e; exact hne
        · exact ne_empty_of_amount e
    · unfold pend; rw [hw7]
      have := pendP_le_of_entries (a := s6.builder_pending_payments) (b := s7.builder_pending_payments)
        (fun j x y hx hy i => by
          rcases hp7 j with e | e | ⟨p0, p1, hp0, hp1, hst, _⟩
          · rw [e, hx] at hy; cases hy; exact le_refl _
          · rw [e] at hy; cases hy; rw [wAmt_empty]; exact Nat.zero_le _
          · rw [hx] at hp0; cases hp0; rw [hy] at hp1; cases hp1; rw [hst.1]) i
      omega
  refine ⟨fun hr => ?_, fun h4 => ?_⟩
  · have r2 := refs_of_eqs e2b e2w e2p hr
    have r4 := t4.1 (t3.1 r2)
    have r6 := refs_of_inv f6 (refs_of_inv f5 r4)
    exact refs_of_inv f8 (t7.1 r6)
  · have r2 := x04_of_eqs e2b e2w e2p h4
    have r4 := t4.2 (t3.2 r2)
    have r6 := x04_of_eqs f6.1 f6.2.2.1 f6.2.1 (x04_of_eqs f5.1 f5.2.2.1 f5.2.1 r4)
    have r7 := t7.2 r6
    exact x04_of_eqs f8.1 f8.2.2.1 f8.2.1 r7

/-- **G3-03 over `process_block`** (needs LatestBidBuilderActive at the pre-state). -/
theorem processBlock_pendingRefsInRange {ctx : Ctx} {s s' : GSt P}
    {blk : JauneConsensus.Gloas.BeaconBlock P} (hA : LatestBidBuilderActive s)
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') (hu : PendingRefsInRange s) :
    PendingRefsInRange s' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  exact (afterParent_refs_x04 h2 h3 h4 h5 h6 h7 h8).1 ((parent_refs_x04 hA h1).1 hu)

/-- **G3-04 over `process_block`** (needs LatestBidBuilderActive at the pre-state). -/
theorem processBlock_exitedHaveNoPending {ctx : Ctx} {s s' : GSt P}
    {blk : JauneConsensus.Gloas.BeaconBlock P} (hA : LatestBidBuilderActive s)
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') (hu : ExitedHaveNoPending s) :
    ExitedHaveNoPending s' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  exact (afterParent_refs_x04 h2 h3 h4 h5 h6 h7 h8).2 ((parent_refs_x04 hA h1).2 hu)

/-- **G3-03 over `state_transition`.** -/
theorem stateTransition_pendingRefsInRange
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) {ctx : Ctx} {s s' : GSt P}
    {sb : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool} (hA : LatestBidBuilderActive s)
    (h : JauneConsensus.Gloas.stateTransition ctx s sb v = .ok s') (hu : PendingRefsInRange s) :
    PendingRefsInRange s' := by
  obtain ⟨m, hm, hb⟩ := stateTransition_split h
  exact processBlock_pendingRefsInRange (processSlots_latestBidBuilderActive hm hA) hb
    (processSlots_pendingRefsInRange hq hm hu)

/-- **G3-04 over `state_transition`.** -/
theorem stateTransition_exitedHaveNoPending
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) {ctx : Ctx} {s s' : GSt P}
    {sb : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool} (hA : LatestBidBuilderActive s)
    (h : JauneConsensus.Gloas.stateTransition ctx s sb v = .ok s') (hu : ExitedHaveNoPending s) :
    ExitedHaveNoPending s' := by
  obtain ⟨m, hm, hb⟩ := stateTransition_split h
  exact processBlock_exitedHaveNoPending (processSlots_latestBidBuilderActive hm hA) hb
    (processSlots_exitedHaveNoPending hq hm hu)

/-- **LatestBidBuilderActive over `state_transition`** (from any pre-state). -/
theorem stateTransition_latestBidBuilderActive {ctx : Ctx} {s s' : GSt P}
    {sb : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool}
    (h : JauneConsensus.Gloas.stateTransition ctx s sb v = .ok s') : LatestBidBuilderActive s' := by
  obtain ⟨m, _, hb⟩ := stateTransition_split h
  exact processBlock_latestBidBuilderActive hb

end JauneConsensus.Facts.Gloas.Inv
