import JauneConsensus.Facts.Gloas.InvariantsWithdrawals

/-!
# G3-05: preservation by `process_block` and `state_transition` (goal `eip8282-gloas-cross-layer-v1`, G3b)

**G3-05 PendingCovered** (`pend + expo ≤ balance`) over a Gloas block, phase by phase:

1. **up to the bid** only `PendLe` (`pend ≤ balance`) is carried: the parent payload's settlement
   keeps `pend`, its direct append moves `L.value` from `expo` (`L` evicted, so not live) into
   `pend`, a builder deposit only raises a balance or fills a slot with nothing pending (G3-03 for
   a fresh index, G3-04 for a reusable one), an exit keeps the balance
   (`parent_pendLe`); the withdrawals keep `PendLe` (`processWithdrawals_pendLe`, under the two
   G3-12 bounds);
2. **the bid** leaves `expo = 0` (its entry is live, or its value is `0`), and
   `can_builder_cover_bid` covers its builder's new `pend` (`bid_cover`);
3. **the operations** do not raise `pend + expo`: an emptied live entry moves `L.value` from `pend`
   into `expo` (`ops_cover`).

The two G3-12 bounds are taken at the block's post-state (a joint state of the run): the registry
lengths there are those of the state the withdrawals read (`afterWithdrawals_vlen` and the builder
frames).
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-! ## Transfers -/

theorem pendLe_of_eqs {s s' : GSt P} (hb : s'.builders = s.builders)
    (hw : s'.builder_pending_withdrawals = s.builder_pending_withdrawals)
    (hp : s'.builder_pending_payments = s.builder_pending_payments) (h : PendLe s) : PendLe s' := by
  intro i b hb'
  rw [hb] at hb'
  rw [pend_of_eqs hw hp]
  exact h i b hb'

theorem covered_of_inv {s s' : GSt P} (hf : InvFrame s s') (h : PendingCovered s) :
    PendingCovered s' := by
  intro i b hb
  rw [hf.1] at hb
  rw [pend_congr hf, expo_congr hf.2.2.2.1 hf.2.1 hf.2.2.2.2.2.2.1]
  exact h i b hb

theorem sum_map_zero {α : Type} (f : α → Nat) :
    ∀ (l : List α), (∀ x ∈ l, f x = 0) → (l.map f).sum = 0
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    rw [h a (by simp), sum_map_zero f l (fun x hx => h x (by simp [hx]))]

/-- Under G3-03 nothing is pending for an index past the registry. -/
theorem pend_zero_of_ge {s : GSt P} (hr : PendingRefsInRange s) {k : Nat}
    (hk : s.builders.toArray.size ≤ k) : pend s k = 0 := by
  have h1 : pendW s.builder_pending_withdrawals.toArray.toList k = 0 := by
    unfold pendW
    refine sum_map_zero _ _ (fun w hw => ?_)
    have := hr.1 w hw
    unfold wAmt; rw [if_neg (by omega)]
  have h2 : pendP s.builder_pending_payments.toArray.toList k = 0 := by
    unfold pendP
    refine sum_map_zero _ _ (fun p hp => ?_)
    by_cases he : p = JauneConsensus.Gloas.BuilderPendingPayment.empty
    · subst he; exact wAmt_empty k
    · have := hr.2 p hp he
      unfold wAmt; rw [if_neg (by omega)]
  unfold pend; rw [h1, h2]

/-- The carried triple before the bid: `PendLe`, G3-03 and G3-04. -/
def I3 (s : GSt P) : Prop := PendLe s ∧ PendingRefsInRange s ∧ ExitedHaveNoPending s

/-! ## The parent payload -/

theorem depReq_I3 (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx} {m m' : GSt P}
    {r : JauneConsensus.Gloas.BuilderDepositRequest}
    (hm : JauneConsensus.Gloas.processBuilderDepositRequest ctx m r = .ok m') (hI : I3 m) :
    I3 m' := by
  obtain ⟨hle, hr, hx⟩ := hI
  obtain ⟨hm', hcase⟩ := depReq_cases hm
  have hpe : ∀ i, pend m' i = pend m i := pend_of_eqs (by rw [hm']) (by rw [hm'])
  refine ⟨?_, refs_of_builders hm' (depReq_size hm) hr, ?_⟩
  · intro i c hc
    rw [hpe]
    rcases hcase with heq | ⟨k, b, b', hb, hb', _, hoth, _, hbal, _⟩ |
        ⟨k, b', _, hidx, hb', _, _, hfar, _, hoth⟩
    · rw [heq] at hc; exact hle i c hc
    · by_cases hik : i = k
      · subst hik; rw [hb'] at hc; cases hc
        have := hle i b hb
        omega
      · rw [hoth i hik] at hc; exact hle i c hc
    · by_cases hik : i = k
      · subst hik
        have h0 : pend m i = 0 := by
          rcases hidx with hsz | ⟨b, hb, hreu⟩
          · exact pend_zero_of_ge hr (by omega)
          · refine hx i b hb ?_
            intro hf
            have h1 := hreu.1
            rw [hf] at h1
            have := epoch_lt_far hspe m
            omega
        omega
      · rw [hoth i hik] at hc; exact hle i c hc
  · intro i c hc hne
    rw [hpe]
    rcases hcase with heq | ⟨k, b, b', hb, hb', _, hoth, _, _, hwe⟩ |
        ⟨k, b', _, _, hb', _, _, hfar, _, hoth⟩
    · rw [heq] at hc; exact hx i c hc hne
    · by_cases hik : i = k
      · subst hik; rw [hb'] at hc; cases hc
        rcases hwe with hwe | ⟨hne', _, _⟩
        · exact hx i b hb (by rw [← hwe]; exact hne)
        · exact hx i b hb hne'
      · rw [hoth i hik] at hc; exact hx i c hc hne
    · by_cases hik : i = k
      · subst hik; rw [hb'] at hc; cases hc; exact absurd hfar hne
      · rw [hoth i hik] at hc; exact hx i c hc hne

theorem exitReq_I3 {cfg : Config} {m m' : GSt P} {r : JauneConsensus.Gloas.BuilderExitRequest}
    (hm : JauneConsensus.Gloas.processBuilderExitRequest cfg m r = .ok m') (hI : I3 m) : I3 m' := by
  obtain ⟨hle, hr, hx⟩ := hI
  obtain ⟨hm', hcase⟩ := exitReq_cases hm
  have hpe : ∀ i, pend m' i = pend m i := pend_of_eqs (by rw [hm']) (by rw [hm'])
  refine ⟨?_, refs_of_builders hm' (exitReq_size hm) hr, ?_⟩
  · intro i c hc
    rw [hpe]
    rcases hcase with heq | ⟨k, b, w, hb, hb', _, _, _, _, hoth⟩
    · rw [heq] at hc; exact hle i c hc
    · by_cases hik : i = k
      · subst hik; rw [hb'] at hc; cases hc; exact hle i b hb
      · rw [hoth i hik] at hc; exact hle i c hc
  · intro i c hc hne
    rw [hpe]
    rcases hcase with heq | ⟨k, b, w, hb, hb', _, ⟨bi, hbi, hpend⟩, _, _, hoth⟩
    · rw [heq] at hc; exact hx i c hc hne
    · by_cases hik : i = k
      · subst hik
        have := getPendingBalance_toNat hpend
        rw [U64.toNat_ofNat? hbi, U64.toNat_zero] at this
        exact this.symm
      · rw [hoth i hik] at hc; exact hx i c hc hne

/-- **The parent payload keeps the triple**, from G3-05 (with G3-08: a direct append's `L` is
evicted, so its value is in `expo`) and LatestBidBuilderActive. -/
theorem parent_I3 (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx} {s s1 : GSt P}
    {blk : JauneConsensus.Gloas.BeaconBlock P} (hA : LatestBidBuilderActive s)
    (h1 : JauneConsensus.Gloas.processParentExecutionPayload ctx s blk = .ok s1)
    (g5 : PendingCovered s) (g3 : PendingRefsInRange s) (g4 : ExitedHaveNoPending s)
    (g8 : LatestBidCoherence s) : I3 s1 := by
  rcases processParentExecutionPayload_cases h1 with ⟨hs1, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · subst hs1; exact ⟨pendLe_of_covered g5, g3, g4⟩
  obtain ⟨x, fx, hx⟩ := applyParentPrefix_split ha
  have px : I3 x := by
    rcases hx with ⟨idx, hset⟩ | ⟨hv, rfl, hc1, hc2⟩ | rfl
    · obtain ⟨hb, hr, hp⟩ := settle_refs_pend hset
      refine ⟨fun i c hc => ?_, hr g3, x04_of hb (fun i => (hp i).le) g4⟩
      rw [hb] at hc; rw [hp]; exact pendLe_of_covered g5 i c hc
    · obtain ⟨b, hb, hfar⟩ := hA hv
      have hnone : bidIndex s = none := by
        simp only [bidIndex, g8.1, hc1, hc2, ↓reduceIte]
      have hnl : ¬ BidLive s := by
        rintro ⟨_, _, hk, _⟩; rw [hnone] at hk; cases hk
      refine ⟨fun i c hc => ?_, refs_transfer (s := s) (s' := directAppend s) (le_refl _)
        (fun w hw => ?_) (fun j p hj hne => Or.inl ⟨p, hj, hne, rfl⟩) g3, fun i c hc hne => ?_⟩
      · change s.builders.toArray[i]? = some c at hc
        rw [directAppend_pend]
        have := g5 i c hc
        rw [expo_of_not_live hnl] at this
        exact this
      · simp only [directAppend, ProgressiveListS.push, Array.toList_push, List.mem_append,
          List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact Or.inl hw
        · exact Or.inr (Array.getElem?_eq_some_iff.mp hb).1
      · change s.builders.toArray[i]? = some c at hc
        rw [directAppend_pend]
        have h0 := g4 i c hc hne
        by_cases hi : s.latest_execution_payload_bid.builder_index.toNat = i
        · subst hi; rw [hb] at hc; cases hc; exact absurd hfar hne
        · have : wAmt i (bidWithdrawal s.latest_execution_payload_bid) = 0 := by
            unfold wAmt bidWithdrawal; rw [if_neg hi]
          omega
    · exact ⟨pendLe_of_covered g5, g3, g4⟩
  have pa : I3 a := ⟨pendLe_of_eqs fx.1 fx.2.2.1 fx.2.1 px.1, refs_of_inv fx px.2.1,
    x04_of_eqs fx.1 fx.2.2.1 fx.2.1 px.2.2⟩
  have pd : I3 d := forIn_yield_inv I3 _ (fun _ _ _ hI hm => depReq_I3 hspe hm hI) _ _ _ hd pa
  have pe : I3 e := forIn_yield_inv I3 _ (fun _ _ _ hI hm => exitReq_I3 hm hI) _ _ _ he pd
  obtain ⟨hb, hp, hw, _⟩ := applyParentSuffix_post hs
  exact ⟨pendLe_of_eqs hb hw hp pe.1, refs_of_eqs hb hw hp pe.2.1, x04_of_eqs hb hw hp pe.2.2⟩

/-! ## The withdrawals keep the validator registry's length -/

section WithdrawalsVLen

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show VLen _ _ from rfl))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (decreaseBalance_vlen _ _ _) $h; exact hh))

theorem applyWithdrawals_vlen (s : GSt P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.applyWithdrawals s ws) (vLen.R s) := by
  unfold JauneConsensus.Gloas.applyWithdrawals; gvcg

theorem updateNextWithdrawalIndex_vlen (s : GSt P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalIndex s ws) (vLen.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalIndex; gvcg

theorem updateNextWithdrawalBuilderIndex_vlen (s : GSt P) (n : U64) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex s n) (vLen.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex; gvcg

theorem updateNextWithdrawalValidatorIndex_vlen (s : GSt P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex s ws) (vLen.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (applyWithdrawals_vlen _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (updateNextWithdrawalIndex_vlen _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (updateNextWithdrawalBuilderIndex_vlen _ _) $h; exact hh))

theorem processWithdrawals_vlen (s : GSt P) :
    Ok (JauneConsensus.Gloas.processWithdrawals s) (vLen.R s) := by
  unfold JauneConsensus.Gloas.processWithdrawals; gvcg
  all_goals exact StepRel.ok_rebase vLen (vLen.refl _) (updateNextWithdrawalValidatorIndex_vlen _ _)

end WithdrawalsVLen

/-! ## The bid -/

/-- `can_builder_cover_bid` in `ℕ`: the builder's balance covers its `pend` and the bid. -/
theorem canBuilderCoverBid_cover {s : GSt P} {bi v : U64} {b : JauneConsensus.Gloas.Builder}
    (hb : s.builders.toArray[bi.toNat]? = some b)
    (h : JauneConsensus.Gloas.canBuilderCoverBid s bi v = .ok true) :
    pend s bi.toNat + v.toNat ≤ b.balance.toNat := by
  unfold JauneConsensus.Gloas.canBuilderCoverBid at h
  obtain ⟨b0, hg, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pd, hpd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨mn, hmn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨mb, hmb, h⟩ := bind_eq_ok_iff.mp h
  rw [pl_get_ok.mp hg] at hb
  cases hb
  have e1 := getPendingBalance_toNat hpd
  have e2 := U64.toNat_add? hmb
  split at h
  · exact absurd (Except.ok.inj h) (by decide)
  · rename_i hlt
    obtain ⟨d, hd, h⟩ := bind_eq_ok_iff.mp h
    have e3 := U64.toNat_sub? hd
    have hvd : v.toNat ≤ d.toNat := of_decide_eq_true (Except.ok.inj h)
    have hlt' : ¬ b.balance.toNat < mb.toNat := hlt
    omega

/-- **The bid leaves G3-05 with `expo = 0`**, from `PendLe` before it. -/
theorem bid_cover {ctx : Ctx} {s3 s4 : GSt P}
    {sb : JauneConsensus.Gloas.SignedExecutionPayloadBid}
    (h4 : JauneConsensus.Gloas.processExecutionPayloadBid ctx s3 sb = .ok s4) (hle : PendLe s3) :
    PendingCovered s4 := by
  obtain ⟨hL, hslot, _, hcase, hb4, _, _, hs4, _, hw4, hnp, hpp⟩ :=
    processExecutionPayloadBid_post h4
  intro i c hc
  rw [hb4] at hc
  by_cases hv : U64.zero < sb.message.value
  · obtain ⟨pp, hidx, hoth⟩ := hpp hv
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
    have hP := pendP_of_one hx hidx hoth i
    have hlive : BidLive s4 := by
      have hk := bidIndex_of_slot (s := s4) (by rw [hL, hs4]; exact hslot)
      rw [hs4] at hk
      exact ⟨_, _, hk, hidx, by rw [hL]⟩
    rw [expo_le_live hlive, Nat.add_zero]
    have hp4 : pend s4 i + wAmt i x.withdrawal =
        pend s3 i + wAmt i (bidWithdrawal sb.message) := by
      unfold pend; rw [hw4]; simp only [] at hP; omega
    by_cases hi : sb.message.builder_index.toNat = i
    · subst hi
      rcases hcase with ⟨_, hz⟩ | ⟨b, hb, _, hcov⟩
      · rw [hz] at hv; exact absurd hv (by decide)
      · rw [hb] at hc; cases hc
        have := canBuilderCoverBid_cover hb hcov
        have hw : wAmt sb.message.builder_index.toNat (bidWithdrawal sb.message) =
            sb.message.value.toNat := by
          unfold wAmt bidWithdrawal; rw [if_pos rfl]
        omega
    · have : wAmt i (bidWithdrawal sb.message) = 0 := by
        unfold wAmt bidWithdrawal; rw [if_neg hi]
      have := hle i c hc
      omega
  · have hp4 := hnp hv
    have hz : expo s4 i = 0 := by
      unfold expo
      rw [if_neg]
      intro hex
      apply hv
      have := hex.2.1
      rw [hL] at this
      exact this
    rw [hz, Nat.add_zero, pend_of_eqs hw4 hp4]
    exact hle i c hc

/-! ## The operations -/

theorem list_sum_le_of_entries_at {α : Type} (f : α → Nat) :
    ∀ (l l' : List α), l.length = l'.length →
      (∀ (j : Nat) (x y : α), l[j]? = some x → l'[j]? = some y → f y ≤ f x) →
      ∀ (k : Nat) (x y : α) (c : Nat), l[k]? = some x → l'[k]? = some y → f y + c ≤ f x →
        (l'.map f).sum + c ≤ (l.map f).sum
  | [], [], _, _, _, _, _, _, hx, _, _ => by simp at hx
  | [], _ :: _, h, _, _, _, _, _, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _, _, _, _, _, _ => by simp at h
  | a :: l, b :: l', h, hle, 0, x, y, c, hx, hy, hc => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
    subst hx; subst hy
    simp only [List.map_cons, List.sum_cons]
    have := list_sum_le_of_entries f l l' (by simpa using h)
      (fun j u v hu hv => hle (j + 1) u v (by simpa using hu) (by simpa using hv))
    omega
  | a :: l, b :: l', h, hle, k + 1, x, y, c, hx, hy, hc => by
    simp only [List.map_cons, List.sum_cons]
    have h0 := hle 0 a b rfl rfl
    have := list_sum_le_of_entries_at f l l' (by simpa using h)
      (fun j u v hu hv => hle (j + 1) u v (by simpa using hu) (by simpa using hv)) k x y c
      (by simpa using hx) (by simpa using hy) hc
    omega

/-- **The operations do not raise `pend + expo`.** -/
theorem ops_cover {s s' : GSt P} (h : OpsRel s s') (i : Nat) :
    pend s' i + expo s' i ≤ pend s i + expo s i := by
  obtain ⟨c, hw, hp⟩ := h
  have hent : ∀ (j : Nat) (x y : JauneConsensus.Gloas.BuilderPendingPayment),
      s.builder_pending_payments.toArray[j]? = some x →
      s'.builder_pending_payments.toArray[j]? = some y → wAmt i y.withdrawal ≤ wAmt i x.withdrawal := by
    intro j x y hx hy
    rcases hp j with e | e | ⟨p0, p1, hp0, hp1, hst, _⟩
    · rw [e, hx] at hy; cases hy; exact le_refl _
    · rw [e] at hy; cases hy; rw [wAmt_empty]; exact Nat.zero_le _
    · rw [hx] at hp0; cases hp0; rw [hy] at hp1; cases hp1; rw [hst.1]
  have hpP : pendP s'.builder_pending_payments.toArray.toList i ≤
      pendP s.builder_pending_payments.toArray.toList i :=
    pendP_le_of_entries (fun j x y hx hy i' => by
      rcases hp j with e | e | ⟨p0, p1, hp0, hp1, hst, _⟩
      · rw [e, hx] at hy; cases hy; exact le_refl _
      · rw [e] at hy; cases hy; rw [wAmt_empty]; exact Nat.zero_le _
      · rw [hx] at hp0; cases hp0; rw [hy] at hp1; cases hp1; rw [hst.1]) i
  have hbi : bidIndex s' = bidIndex s := by
    unfold bidIndex curEpoch; rw [c.2.1, c.2.2.2.2.1]
  have hL : s'.latest_execution_payload_bid = s.latest_execution_payload_bid := c.2.1
  have pe : pend s' i = pendW s.builder_pending_withdrawals.toArray.toList i +
      pendP s'.builder_pending_payments.toArray.toList i := by
    unfold pend; rw [hw]
  have pe0 : pend s i = pendW s.builder_pending_withdrawals.toArray.toList i +
      pendP s.builder_pending_payments.toArray.toList i := rfl
  have hexpo' : expo s' i ≤ wAmt i (bidWithdrawal s.latest_execution_payload_bid) := by
    by_cases hl : BidLive s'
    · rw [expo_le_live hl]; exact Nat.zero_le _
    · rw [expo_of_not_live hl, hL]
  by_cases hl : BidLive s
  · obtain ⟨k, E, hk, hE, hEw⟩ := hl
    rw [expo_le_live ⟨k, E, hk, hE, hEw⟩]
    rcases hp k with e | e | ⟨p0, p1, hp0, hp1, hst, _⟩
    · have hl' : BidLive s' := ⟨k, E, by rw [hbi]; exact hk, by rw [e]; exact hE, by rw [hL]; exact hEw⟩
      rw [expo_le_live hl']; omega
    · have hdrop : pendP s'.builder_pending_payments.toArray.toList i + wAmt i E.withdrawal ≤
          pendP s.builder_pending_payments.toArray.toList i :=
        list_sum_le_of_entries_at (fun p : JauneConsensus.Gloas.BuilderPendingPayment => wAmt i p.withdrawal)
          s.builder_pending_payments.toArray.toList s'.builder_pending_payments.toArray.toList
          (by simp [s.builder_pending_payments.size_eq, s'.builder_pending_payments.size_eq])
          (fun j x y hx hy => hent j x y (by simpa using hx) (by simpa using hy))
          k E JauneConsensus.Gloas.BuilderPendingPayment.empty (wAmt i E.withdrawal)
          (by simpa using hE) (by simpa using e) (by rw [wAmt_empty]; omega)
      rw [hEw] at hdrop
      omega
    · rw [hE] at hp0; cases hp0
      have hl' : BidLive s' := ⟨k, p1, by rw [hbi]; exact hk, hp1, by rw [hL, hst.1]; exact hEw⟩
      rw [expo_le_live hl']; omega
  · rw [expo_of_not_live hl]; omega

/-! ## The block and the state transition -/

/-- **G3-05 over `process_block`.** Hypotheses: G3-05, G3-03, G3-04, G3-08 and
LatestBidBuilderActive at the pre-state, `2 ≤ SLOTS_PER_EPOCH`, and the two G3-12 bounds
(`validatorsBound`, `buildersBound`) at the post-state. -/
theorem processBlock_pendingCovered (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx} {s s' : GSt P}
    {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s')
    (g5 : PendingCovered s) (g3 : PendingRefsInRange s) (g4 : ExitedHaveNoPending s)
    (g8 : LatestBidCoherence s) (hA : LatestBidBuilderActive s)
    (validatorsBound : s'.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : s'.builders.toArray.size ≤ 2 ^ 40) : PendingCovered s' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  obtain ⟨l1, r1, x1⟩ := parent_I3 hspe hA h1 g5 g3 g4 g8
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have e2b : s2.builders = s1.builders := by rw [hm2]
  have e2w : s2.builder_pending_withdrawals = s1.builder_pending_withdrawals := by rw [hm2]
  have e2p : s2.builder_pending_payments = s1.builder_pending_payments := by rw [hm2]
  have e2v : s2.validators = s1.validators := by rw [hm2]
  have w3 := processWithdrawals_wFrame _ _ h3
  have b4 := processExecutionPayloadBid_post h4
  have c := afterBid_core h5 h6 h7 h8
  have vb3 : s'.validators.toArray.size = s3.validators.toArray.size := afterWithdrawals_vlen h4 h5 h6 h7 h8
  have vb2 : s3.validators.toArray.size = s2.validators.toArray.size := processWithdrawals_vlen _ _ h3
  have bb : s'.builders.toArray.size = s2.builders.toArray.size := by
    rw [c.1, b4.2.2.2.2.1]; exact w3.2.2.2.2.2.1
  have l3 := processWithdrawals_pendLe hspe h3 (refs_of_eqs e2b e2w e2p r1)
    (x04_of_eqs e2b e2w e2p x1) (by omega) (by omega) (pendLe_of_eqs e2b e2w e2p l1)
  have v4 := bid_cover h4 l3
  have v6 := covered_of_inv (processEth1Data_invFrame _ _ _ h6)
    (covered_of_inv (processRandao_invFrame _ _ _ _ h5) v4)
  have o7 := processOperations_ops _ _ _ _ _ h7
  have v7 : PendingCovered s7 := by
    intro i b hb
    rw [o7.1.1] at hb
    exact Nat.le_trans (ops_cover o7 i) (v6 i b hb)
  exact covered_of_inv (processSyncAggregate_invFrame _ _ _ _ h8) v7

/-- **G3-05 over `state_transition`.** Hypotheses: G3-05, G3-03, G3-04, G3-07, G3-08, FutureEmpty
and LatestBidBuilderActive at the pre-state, quorum positivity, `2 ≤ SLOTS_PER_EPOCH`, and the two
G3-12 bounds at the post-state. -/
theorem stateTransition_pendingCovered
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    {ctx : Ctx} {s s' : GSt P} {sb : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool}
    (h : JauneConsensus.Gloas.stateTransition ctx s sb v = .ok s')
    (g5 : PendingCovered s) (g3 : PendingRefsInRange s) (g4 : ExitedHaveNoPending s)
    (g7 : NoLiveWeightOnLatestBid s) (g8 : LatestBidCoherence s) (fe : FutureEmpty s)
    (hA : LatestBidBuilderActive s)
    (validatorsBound : s'.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : s'.builders.toArray.size ≤ 2 ^ 40) : PendingCovered s' := by
  obtain ⟨m, hm, hb⟩ := stateTransition_split h
  have hs := processSlots_pendingCovered hq (by omega) hm ⟨g5, g7, fe⟩
  exact processBlock_pendingCovered hspe hb hs.1 (processSlots_pendingRefsInRange hq hm g3)
    (processSlots_exitedHaveNoPending hq hm g4) (processSlots_latestBidCoherence hm g8)
    (processSlots_latestBidBuilderActive hm hA) validatorsBound buildersBound

end JauneConsensus.Facts.Gloas.Inv
