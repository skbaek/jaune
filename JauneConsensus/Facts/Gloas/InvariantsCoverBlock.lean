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

namespace JauneConsensus.Facts.Gloas.Invariant

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-! ## Transfers -/

theorem pendingBalanceLe_of_equalities {s s' : GloasState P} (hb : s'.builders = s.builders)
    (hw : s'.builder_pending_withdrawals = s.builder_pending_withdrawals)
    (hp : s'.builder_pending_payments = s.builder_pending_payments) (h : PendingBalanceLe s) : PendingBalanceLe s' := by
  intro i b hb'
  rw [hb] at hb'
  rw [pendingBalance_of_equalities hw hp]
  exact h i b hb'

theorem covered_of_invariant {s s' : GloasState P} (hf : InvariantFrame s s') (h : PendingCovered s) :
    PendingCovered s' := by
  intro i b hb
  rw [hf.1] at hb
  rw [pendingBalance_congr hf, exposure_congr hf.2.2.2.1 hf.2.1 hf.2.2.2.2.2.2.1]
  exact h i b hb

theorem sum_map_zero {α : Type} (f : α → Nat) :
    ∀ (l : List α), (∀ x ∈ l, f x = 0) → (l.map f).sum = 0
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    rw [h a (by simp), sum_map_zero f l (fun x hx => h x (by simp [hx]))]

/-- Under G3-03 nothing is pending for an index past the registry. -/
theorem pendingBalance_zero_of_ge {s : GloasState P} (hr : PendingReferencesInRange s) {k : Nat}
    (hk : s.builders.toArray.size ≤ k) : pendingBalance s k = 0 := by
  have h1 : pendingWithdrawalBalance s.builder_pending_withdrawals.toArray.toList k = 0 := by
    unfold pendingWithdrawalBalance
    refine sum_map_zero _ _ (fun w hw => ?_)
    have := hr.1 w hw
    unfold withdrawalAmount; rw [if_neg (by omega)]
  have h2 : pendingPaymentBalance s.builder_pending_payments.toArray.toList k = 0 := by
    unfold pendingPaymentBalance
    refine sum_map_zero _ _ (fun p hp => ?_)
    by_cases he : p = JauneConsensus.Gloas.BuilderPendingPayment.empty
    · subst he; exact withdrawalAmount_empty k
    · have := hr.2 p hp he
      unfold withdrawalAmount; rw [if_neg (by omega)]
  unfold pendingBalance; rw [h1, h2]

/-- The carried triple before the bid: `PendLe`, G3-03 and G3-04. -/
def PendingBalanceReferencesExited (s : GloasState P) : Prop := PendingBalanceLe s ∧ PendingReferencesInRange s ∧ ExitedHaveNoPending s

/-! ## The parent payload -/

theorem depositRequest_PendingBalanceReferencesExited (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Context} {m m' : GloasState P}
    {r : JauneConsensus.Gloas.BuilderDepositRequest}
    (hm : JauneConsensus.Gloas.processBuilderDepositRequest ctx m r = .ok m') (hI : PendingBalanceReferencesExited m) :
    PendingBalanceReferencesExited m' := by
  obtain ⟨hle, hr, hx⟩ := hI
  obtain ⟨hm', hcase⟩ := depositRequest_cases hm
  have hpe : ∀ i, pendingBalance m' i = pendingBalance m i := pendingBalance_of_equalities (by rw [hm']) (by rw [hm'])
  refine ⟨?_, references_of_builders hm' (depositRequest_size hm) hr, ?_⟩
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
        have h0 : pendingBalance m i = 0 := by
          rcases hidx with hsz | ⟨b, hb, hreu⟩
          · exact pendingBalance_zero_of_ge hr (by omega)
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

theorem exitRequest_PendingBalanceReferencesExited {cfg : Config} {m m' : GloasState P} {r : JauneConsensus.Gloas.BuilderExitRequest}
    (hm : JauneConsensus.Gloas.processBuilderExitRequest cfg m r = .ok m') (hI : PendingBalanceReferencesExited m) : PendingBalanceReferencesExited m' := by
  obtain ⟨hle, hr, hx⟩ := hI
  obtain ⟨hm', hcase⟩ := exitRequest_cases hm
  have hpe : ∀ i, pendingBalance m' i = pendingBalance m i := pendingBalance_of_equalities (by rw [hm']) (by rw [hm'])
  refine ⟨?_, references_of_builders hm' (exitRequest_size hm) hr, ?_⟩
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
theorem parent_PendingBalanceReferencesExited (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Context} {s s1 : GloasState P}
    {blk : JauneConsensus.Gloas.BeaconBlock P} (hA : LatestBidBuilderActive s)
    (h1 : JauneConsensus.Gloas.processParentExecutionPayload ctx s blk = .ok s1)
    (g5 : PendingCovered s) (g3 : PendingReferencesInRange s) (g4 : ExitedHaveNoPending s)
    (g8 : LatestBidCoherence s) : PendingBalanceReferencesExited s1 := by
  rcases processParentExecutionPayload_cases h1 with ⟨hs1, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · subst hs1; exact ⟨pendingBalanceLe_of_covered g5, g3, g4⟩
  obtain ⟨x, fx, hx⟩ := applyParentPrefix_split ha
  have px : PendingBalanceReferencesExited x := by
    rcases hx with ⟨idx, hset⟩ | ⟨hv, rfl, hc1, hc2⟩ | rfl
    · obtain ⟨hb, hr, hp⟩ := settle_references_pendingBalance hset
      refine ⟨fun i c hc => ?_, hr g3, exitedHaveNoPending_of hb (fun i => (hp i).le) g4⟩
      rw [hb] at hc; rw [hp]; exact pendingBalanceLe_of_covered g5 i c hc
    · obtain ⟨b, hb, hfar⟩ := hA hv
      have hnone : bidIndex s = none := by
        simp only [bidIndex, g8.1, hc1, hc2, ↓reduceIte]
      have hnl : ¬ BidLive s := by
        rintro ⟨_, _, hk, _⟩; rw [hnone] at hk; cases hk
      refine ⟨fun i c hc => ?_, references_transfer (s := s) (s' := directAppend s) (le_refl _)
        (fun w hw => ?_) (fun j p hj hne => Or.inl ⟨p, hj, hne, rfl⟩) g3, fun i c hc hne => ?_⟩
      · change s.builders.toArray[i]? = some c at hc
        rw [directAppend_pendingBalance]
        have := g5 i c hc
        rw [exposure_of_not_live hnl] at this
        exact this
      · simp only [directAppend, ProgressiveListOnSpine.push, Array.toList_push, List.mem_append,
          List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact Or.inl hw
        · exact Or.inr (Array.getElem?_eq_some_iff.mp hb).1
      · change s.builders.toArray[i]? = some c at hc
        rw [directAppend_pendingBalance]
        have h0 := g4 i c hc hne
        by_cases hi : s.latest_execution_payload_bid.builder_index.toNat = i
        · subst hi; rw [hb] at hc; cases hc; exact absurd hfar hne
        · have : withdrawalAmount i (bidWithdrawal s.latest_execution_payload_bid) = 0 := by
            unfold withdrawalAmount bidWithdrawal; rw [if_neg hi]
          omega
    · exact ⟨pendingBalanceLe_of_covered g5, g3, g4⟩
  have pa : PendingBalanceReferencesExited a := ⟨pendingBalanceLe_of_equalities fx.1 fx.2.2.1 fx.2.1 px.1, references_of_invariant fx px.2.1,
    exitedHaveNoPending_of_equalities fx.1 fx.2.2.1 fx.2.1 px.2.2⟩
  have pd : PendingBalanceReferencesExited d := forIn_yield_invariant PendingBalanceReferencesExited _ (fun _ _ _ hI hm => depositRequest_PendingBalanceReferencesExited hspe hm hI) _ _ _ hd pa
  have pe : PendingBalanceReferencesExited e := forIn_yield_invariant PendingBalanceReferencesExited _ (fun _ _ _ hI hm => exitRequest_PendingBalanceReferencesExited hm hI) _ _ _ he pd
  obtain ⟨hb, hp, hw, _⟩ := applyParentSuffix_post hs
  exact ⟨pendingBalanceLe_of_equalities hb hw hp pe.1, references_of_equalities hb hw hp pe.2.1, exitedHaveNoPending_of_equalities hb hw hp pe.2.2⟩

/-! ## The withdrawals keep the validator registry's length -/

section WithdrawalsVLen

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show ValidatorsLength _ _ from rfl))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (decreaseBalance_validatorsLength _ _ _) $h; exact hh))

theorem applyWithdrawals_validatorsLength (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.applyWithdrawals s ws) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.applyWithdrawals; gvcg

theorem updateNextWithdrawalIndex_validatorsLength (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalIndex s ws) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalIndex; gvcg

theorem updateNextWithdrawalBuilderIndex_validatorsLength (s : GloasState P) (n : U64) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex s n) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex; gvcg

theorem updateNextWithdrawalValidatorIndex_validatorsLength (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex s ws) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (applyWithdrawals_validatorsLength _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (updateNextWithdrawalIndex_validatorsLength _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (updateNextWithdrawalBuilderIndex_validatorsLength _ _) $h; exact hh))

theorem processWithdrawals_validatorsLength (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processWithdrawals s) (validatorsLength.relation s) := by
  unfold JauneConsensus.Gloas.processWithdrawals; gvcg
  all_goals exact StepRelation.ok_rebase validatorsLength (validatorsLength.refl _) (updateNextWithdrawalValidatorIndex_validatorsLength _ _)

end WithdrawalsVLen

/-! ## The bid -/

/-- `can_builder_cover_bid` in `ℕ`: the builder's balance covers its `pend` and the bid. -/
theorem canBuilderCoverBid_cover {s : GloasState P} {bi v : U64} {b : JauneConsensus.Gloas.Builder}
    (hb : s.builders.toArray[bi.toNat]? = some b)
    (h : JauneConsensus.Gloas.canBuilderCoverBid s bi v = .ok true) :
    pendingBalance s bi.toNat + v.toNat ≤ b.balance.toNat := by
  unfold JauneConsensus.Gloas.canBuilderCoverBid at h
  obtain ⟨b0, hg, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pd, hpd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨mn, hmn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨mb, hmb, h⟩ := bind_eq_ok_iff.mp h
  rw [progressiveList_get_ok.mp hg] at hb
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
theorem bid_cover {ctx : Context} {s3 s4 : GloasState P}
    {sb : JauneConsensus.Gloas.SignedExecutionPayloadBid}
    (h4 : JauneConsensus.Gloas.processExecutionPayloadBid ctx s3 sb = .ok s4) (hle : PendingBalanceLe s3) :
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
    have hP := pendingPaymentBalance_of_one hx hidx hoth i
    have hlive : BidLive s4 := by
      have hk := bidIndex_of_slot (s := s4) (by rw [hL, hs4]; exact hslot)
      rw [hs4] at hk
      exact ⟨_, _, hk, hidx, by rw [hL]⟩
    rw [exposure_eq_zero_of_bidLive hlive, Nat.add_zero]
    have hp4 : pendingBalance s4 i + withdrawalAmount i x.withdrawal =
        pendingBalance s3 i + withdrawalAmount i (bidWithdrawal sb.message) := by
      unfold pendingBalance; rw [hw4]; simp only [] at hP; omega
    by_cases hi : sb.message.builder_index.toNat = i
    · subst hi
      rcases hcase with ⟨_, hz⟩ | ⟨b, hb, _, hcov⟩
      · rw [hz] at hv; exact absurd hv (by decide)
      · rw [hb] at hc; cases hc
        have := canBuilderCoverBid_cover hb hcov
        have hw : withdrawalAmount sb.message.builder_index.toNat (bidWithdrawal sb.message) =
            sb.message.value.toNat := by
          unfold withdrawalAmount bidWithdrawal; rw [if_pos rfl]
        omega
    · have : withdrawalAmount i (bidWithdrawal sb.message) = 0 := by
        unfold withdrawalAmount bidWithdrawal; rw [if_neg hi]
      have := hle i c hc
      omega
  · have hp4 := hnp hv
    have hz : exposure s4 i = 0 := by
      unfold exposure
      rw [if_neg]
      intro hex
      apply hv
      have := hex.2.1
      rw [hL] at this
      exact this
    rw [hz, Nat.add_zero, pendingBalance_of_equalities hw4 hp4]
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
theorem operations_cover {s s' : GloasState P} (h : OperationsRelation s s') (i : Nat) :
    pendingBalance s' i + exposure s' i ≤ pendingBalance s i + exposure s i := by
  obtain ⟨c, hw, hp⟩ := h
  have hent : ∀ (j : Nat) (x y : JauneConsensus.Gloas.BuilderPendingPayment),
      s.builder_pending_payments.toArray[j]? = some x →
      s'.builder_pending_payments.toArray[j]? = some y → withdrawalAmount i y.withdrawal ≤ withdrawalAmount i x.withdrawal := by
    intro j x y hx hy
    rcases hp j with e | e | ⟨p0, p1, hp0, hp1, hst, _⟩
    · rw [e, hx] at hy; cases hy; exact le_refl _
    · rw [e] at hy; cases hy; rw [withdrawalAmount_empty]; exact Nat.zero_le _
    · rw [hx] at hp0; cases hp0; rw [hy] at hp1; cases hp1; rw [hst.1]
  have hpP : pendingPaymentBalance s'.builder_pending_payments.toArray.toList i ≤
      pendingPaymentBalance s.builder_pending_payments.toArray.toList i :=
    pendingPaymentBalance_le_of_entries (fun j x y hx hy i' => by
      rcases hp j with e | e | ⟨p0, p1, hp0, hp1, hst, _⟩
      · rw [e, hx] at hy; cases hy; exact le_refl _
      · rw [e] at hy; cases hy; rw [withdrawalAmount_empty]; exact Nat.zero_le _
      · rw [hx] at hp0; cases hp0; rw [hy] at hp1; cases hp1; rw [hst.1]) i
  have hbi : bidIndex s' = bidIndex s := by
    unfold bidIndex currentEpoch; rw [c.2.1, c.2.2.2.2.1]
  have hL : s'.latest_execution_payload_bid = s.latest_execution_payload_bid := c.2.1
  have pe : pendingBalance s' i = pendingWithdrawalBalance s.builder_pending_withdrawals.toArray.toList i +
      pendingPaymentBalance s'.builder_pending_payments.toArray.toList i := by
    unfold pendingBalance; rw [hw]
  have pe0 : pendingBalance s i = pendingWithdrawalBalance s.builder_pending_withdrawals.toArray.toList i +
      pendingPaymentBalance s.builder_pending_payments.toArray.toList i := rfl
  have hexpo' : exposure s' i ≤ withdrawalAmount i (bidWithdrawal s.latest_execution_payload_bid) := by
    by_cases hl : BidLive s'
    · rw [exposure_eq_zero_of_bidLive hl]; exact Nat.zero_le _
    · rw [exposure_of_not_live hl, hL]
  by_cases hl : BidLive s
  · obtain ⟨k, E, hk, hE, hEw⟩ := hl
    rw [exposure_eq_zero_of_bidLive ⟨k, E, hk, hE, hEw⟩]
    rcases hp k with e | e | ⟨p0, p1, hp0, hp1, hst, _⟩
    · have hl' : BidLive s' := ⟨k, E, by rw [hbi]; exact hk, by rw [e]; exact hE, by rw [hL]; exact hEw⟩
      rw [exposure_eq_zero_of_bidLive hl']; omega
    · have hdrop : pendingPaymentBalance s'.builder_pending_payments.toArray.toList i + withdrawalAmount i E.withdrawal ≤
          pendingPaymentBalance s.builder_pending_payments.toArray.toList i :=
        list_sum_le_of_entries_at (fun p : JauneConsensus.Gloas.BuilderPendingPayment => withdrawalAmount i p.withdrawal)
          s.builder_pending_payments.toArray.toList s'.builder_pending_payments.toArray.toList
          (by simp [s.builder_pending_payments.size_eq, s'.builder_pending_payments.size_eq])
          (fun j x y hx hy => hent j x y (by simpa using hx) (by simpa using hy))
          k E JauneConsensus.Gloas.BuilderPendingPayment.empty (withdrawalAmount i E.withdrawal)
          (by simpa using hE) (by simpa using e) (by rw [withdrawalAmount_empty]; omega)
      rw [hEw] at hdrop
      omega
    · rw [hE] at hp0; cases hp0
      have hl' : BidLive s' := ⟨k, p1, by rw [hbi]; exact hk, hp1, by rw [hL, hst.1]; exact hEw⟩
      rw [exposure_eq_zero_of_bidLive hl']; omega
  · rw [exposure_of_not_live hl]; omega

/-! ## The block and the state transition -/

/-- **G3-05 over `process_block`.** Hypotheses: G3-05, G3-03, G3-04, G3-08 and
LatestBidBuilderActive at the pre-state, `2 ≤ SLOTS_PER_EPOCH`, and the two G3-12 bounds
(`validatorsBound`, `buildersBound`) at the post-state. -/
theorem processBlock_pendingCovered (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Context} {s s' : GloasState P}
    {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s')
    (g5 : PendingCovered s) (g3 : PendingReferencesInRange s) (g4 : ExitedHaveNoPending s)
    (g8 : LatestBidCoherence s) (hA : LatestBidBuilderActive s)
    (validatorsBound : s'.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : s'.builders.toArray.size ≤ 2 ^ 40) : PendingCovered s' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  obtain ⟨l1, r1, x1⟩ := parent_PendingBalanceReferencesExited hspe hA h1 g5 g3 g4 g8
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have e2b : s2.builders = s1.builders := by rw [hm2]
  have e2w : s2.builder_pending_withdrawals = s1.builder_pending_withdrawals := by rw [hm2]
  have e2p : s2.builder_pending_payments = s1.builder_pending_payments := by rw [hm2]
  have e2v : s2.validators = s1.validators := by rw [hm2]
  have w3 := processWithdrawals_withdrawalsFrame _ _ h3
  have b4 := processExecutionPayloadBid_post h4
  have c := afterBid_core h5 h6 h7 h8
  have vb3 : s'.validators.toArray.size = s3.validators.toArray.size := afterWithdrawals_validatorsLength h4 h5 h6 h7 h8
  have vb2 : s3.validators.toArray.size = s2.validators.toArray.size := processWithdrawals_validatorsLength _ _ h3
  have bb : s'.builders.toArray.size = s2.builders.toArray.size := by
    rw [c.1, b4.2.2.2.2.1]; exact w3.2.2.2.2.2.1
  have l3 := processWithdrawals_pendingBalanceLe hspe h3 (references_of_equalities e2b e2w e2p r1)
    (exitedHaveNoPending_of_equalities e2b e2w e2p x1) (by omega) (by omega) (pendingBalanceLe_of_equalities e2b e2w e2p l1)
  have v4 := bid_cover h4 l3
  have v6 := covered_of_invariant (processEth1Data_invariantFrame _ _ _ h6)
    (covered_of_invariant (processRandao_invariantFrame _ _ _ _ h5) v4)
  have o7 := processOperations_operations _ _ _ _ _ h7
  have v7 : PendingCovered s7 := by
    intro i b hb
    rw [o7.1.1] at hb
    exact Nat.le_trans (operations_cover o7 i) (v6 i b hb)
  exact covered_of_invariant (processSyncAggregate_invariantFrame _ _ _ _ h8) v7

/-- **G3-05 over `state_transition`.** Hypotheses: G3-05, G3-03, G3-04, G3-07, G3-08, FutureEmpty
and LatestBidBuilderActive at the pre-state, quorum positivity, `2 ≤ SLOTS_PER_EPOCH`, and the two
G3-12 bounds at the post-state. -/
theorem stateTransition_pendingCovered
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    {ctx : Context} {s s' : GloasState P} {sb : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool}
    (h : JauneConsensus.Gloas.stateTransition ctx s sb v = .ok s')
    (g5 : PendingCovered s) (g3 : PendingReferencesInRange s) (g4 : ExitedHaveNoPending s)
    (g7 : NoLiveWeightOnLatestBid s) (g8 : LatestBidCoherence s) (fe : FutureEmpty s)
    (hA : LatestBidBuilderActive s)
    (validatorsBound : s'.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : s'.builders.toArray.size ≤ 2 ^ 40) : PendingCovered s' := by
  obtain ⟨m, hm, hb⟩ := stateTransition_split h
  have hs := processSlots_pendingCovered hq (by omega) hm ⟨g5, g7, fe⟩
  exact processBlock_pendingCovered hspe hb hs.1 (processSlots_pendingReferencesInRange hq hm g3)
    (processSlots_exitedHaveNoPending hq hm g4) (processSlots_latestBidCoherence hm g8)
    (processSlots_latestBidBuilderActive hm hA) validatorsBound buildersBound

end JauneConsensus.Facts.Gloas.Invariant
