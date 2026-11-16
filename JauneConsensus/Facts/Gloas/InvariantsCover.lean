import JauneConsensus.Facts.Gloas.InvariantsControls

/-!
# G3-05: preservation by `process_slots` (goal `eip8282-gloas-cross-layer-v1`, G3a)

**G3-05 PendingCovered** (`pend + expo ≤ balance`) over `process_slots`
(`processSlots_pendingCovered`), with G3-07 and quorum positivity: inside an epoch nothing it reads
changes; at an epoch boundary `L`'s entry moves down with `L`'s window index, or, when `L` leaves
the window, its live entry (weight `0` by G3-07, so not appended since the quorum is positive)
leaves `pend` exactly when `expo` takes `L.value`.
-/

namespace JauneConsensus.Facts.Gloas.Invariant

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-- A filtered sum leaves out an excluded element. -/
theorem filter_sum_le_of_excluded {α : Type} (c : α → Bool) (f : α → Nat) :
    ∀ (l : List α) (k : Nat) (e : α), l[k]? = some e → c e = false →
      ((l.filter c).map f).sum + f e ≤ (l.map f).sum
  | [], _, _, h, _ => by simp at h
  | a :: l, 0, e, h, hc => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.filter_cons, hc, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
    have := filter_map_sum_le c f l
    omega
  | a :: l, k + 1, e, h, hc => by
    simp only [List.getElem?_cons_succ] at h
    have ih := filter_sum_le_of_excluded c f l k e h hc
    by_cases ha : c a = true
    · simp only [List.filter_cons, ha, ↓reduceIte, List.map_cons, List.sum_cons]; omega
    · simp only [List.filter_cons, ha, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      omega

theorem exposure_congr {s s' : GloasState P} (hL : s'.latest_execution_payload_bid = s.latest_execution_payload_bid)
    (hp : s'.builder_pending_payments = s.builder_pending_payments) (hs : s'.slot = s.slot) (i : Nat) :
    exposure s' i = exposure s i := by
  unfold exposure Exposed BidLive bidIndex currentEpoch; rw [hL, hp, hs]

theorem pendingBalance_congr {s s' : GloasState P} (hf : InvariantFrame s s') (i : Nat) : pendingBalance s' i = pendingBalance s i :=
  pendingBalance_of_equalities hf.2.2.1 hf.2.1 i

theorem exposure_le_live {s : GloasState P} {i : Nat} (h : BidLive s) : exposure s i = 0 := by
  unfold exposure; rw [if_neg (fun e => e.2.2 h)]

theorem exposure_of_not_live {s : GloasState P} {i : Nat} (h : ¬ BidLive s) :
    exposure s i = withdrawalAmount i (bidWithdrawal s.latest_execution_payload_bid) := by
  unfold exposure Exposed withdrawalAmount bidWithdrawal
  simp only []
  by_cases hb : s.latest_execution_payload_bid.builder_index.toNat = i
  · by_cases hv : 0 < s.latest_execution_payload_bid.value.toNat
    · rw [if_pos ⟨hb, hv, h⟩, if_pos hb]
    · rw [if_neg (fun e => hv e.2.1), if_pos hb]; omega
  · rw [if_neg (fun e => hb e.1), if_neg hb]

/-- **The epoch rotation with the slot's advance does not raise `pend + expo`.** -/
theorem rotation_cover (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {cfg : Config} {a b : GloasState P} {next : U64}
    (hb : JauneConsensus.Gloas.processBuilderPendingPayments cfg a = .ok b)
    (g7 : NoLiveWeightOnLatestBid a) (hn : next.toNat = a.slot.toNat + 1)
    (h0 : next.toNat % P.SLOTS_PER_EPOCH = 0) (i : Nat) :
    pendingBalance b i + exposure { b with slot := next } i ≤ pendingBalance a i + exposure a i := by
  obtain ⟨_, q, hqh, hW, hP⟩ := processBuilderPendingPayments_frame hb
  have hq0 := quorum_pos hq hqh
  have hsz : a.builder_pending_payments.toArray.size = 2 * P.SLOTS_PER_EPOCH :=
    a.builder_pending_payments.size_eq
  have hLb : b.latest_execution_payload_bid = a.latest_execution_payload_bid := by
    have := (processBuilderPendingPayments_core cfg a b hb).2.1; exact this
  -- pend
  set A := a.builder_pending_payments.toArray with hA
  have hsplit : A.toList = (A.extract 0 P.SLOTS_PER_EPOCH).toList ++
      (A.extract P.SLOTS_PER_EPOCH A.size).toList := by
    have hl : A.toList.length = A.size := Array.length_toList
    simp only [Array.toList_extract, List.extract, List.drop_zero, ← hl, Nat.sub_zero]
    have e : (A.toList.drop P.SLOTS_PER_EPOCH).take (A.toList.length - P.SLOTS_PER_EPOCH) =
        A.toList.drop P.SLOTS_PER_EPOCH := List.take_of_length_le (by simp)
    rw [e]
    exact (List.take_append_drop _ _).symm
  have hpa : pendingBalance a i = pendingWithdrawalBalance a.builder_pending_withdrawals.toArray.toList i +
      ((A.extract 0 P.SLOTS_PER_EPOCH).toList.map (fun p => withdrawalAmount i p.withdrawal)).sum +
      ((A.extract P.SLOTS_PER_EPOCH A.size).toList.map (fun p => withdrawalAmount i p.withdrawal)).sum := by
    unfold pendingBalance; rw [hsplit, pendingPaymentBalance_append]; unfold pendingPaymentBalance; omega
  have hpb : pendingBalance b i = pendingWithdrawalBalance a.builder_pending_withdrawals.toArray.toList i +
      ((((A.extract 0 P.SLOTS_PER_EPOCH).toList.filter (fun p => decide (q ≤ p.weight))).map
        (fun p => withdrawalAmount i p.withdrawal)).sum) +
      ((A.extract P.SLOTS_PER_EPOCH A.size).toList.map (fun p => withdrawalAmount i p.withdrawal)).sum := by
    unfold pendingBalance; rw [hW, hP, pendingWithdrawalBalance_append, Array.toList_append, pendingPaymentBalance_append]
    have hrep : pendingPaymentBalance (Array.replicate P.SLOTS_PER_EPOCH
        JauneConsensus.Gloas.BuilderPendingPayment.empty).toList i = 0 := by
      simp [pendingPaymentBalance, withdrawalAmount_empty]
    rw [hrep]
    simp only [pendingWithdrawalBalance, List.map_map, pendingPaymentBalance]
    rfl
  have hfil := filter_map_sum_le (fun p : JauneConsensus.Gloas.BuilderPendingPayment =>
    decide (q ≤ p.weight)) (fun p => withdrawalAmount i p.withdrawal) (A.extract 0 P.SLOTS_PER_EPOCH).toList
  have hle : pendingBalance b i ≤ pendingBalance a i := by
    rw [hpa, hpb]; omega
  -- epochs
  have hdiv : next.toNat / P.SLOTS_PER_EPOCH = a.slot.toNat / P.SLOTS_PER_EPOCH + 1 := by
    rw [hn]; rw [hn] at h0; exact Nat.succ_div_of_mod_eq_zero h0
  set L := a.latest_execution_payload_bid with hL
  have hLm := Nat.mod_lt L.slot.toNat hspe
  have hbi_a : bidIndex a = (if L.slot.toNat / P.SLOTS_PER_EPOCH = a.slot.toNat / P.SLOTS_PER_EPOCH then
      some (P.SLOTS_PER_EPOCH + L.slot.toNat % P.SLOTS_PER_EPOCH)
    else if L.slot.toNat / P.SLOTS_PER_EPOCH + 1 = a.slot.toNat / P.SLOTS_PER_EPOCH then
      some (L.slot.toNat % P.SLOTS_PER_EPOCH) else none) := rfl
  have hbi_b : bidIndex { b with slot := next } =
      (if L.slot.toNat / P.SLOTS_PER_EPOCH = a.slot.toNat / P.SLOTS_PER_EPOCH + 1 then
        some (P.SLOTS_PER_EPOCH + L.slot.toNat % P.SLOTS_PER_EPOCH)
      else if L.slot.toNat / P.SLOTS_PER_EPOCH + 1 = a.slot.toNat / P.SLOTS_PER_EPOCH + 1 then
        some (L.slot.toNat % P.SLOTS_PER_EPOCH) else none) := by
    unfold bidIndex currentEpoch; simp only []; rw [hLb, hdiv]
  have hbp : ({ b with slot := next } : GloasState P).builder_pending_payments.toArray =
      A.extract P.SLOTS_PER_EPOCH A.size ++
        Array.replicate P.SLOTS_PER_EPOCH JauneConsensus.Gloas.BuilderPendingPayment.empty := hP
  have hLb' : ({ b with slot := next } : GloasState P).latest_execution_payload_bid = L := hLb
  by_cases e1 : L.slot.toNat / P.SLOTS_PER_EPOCH = a.slot.toNat / P.SLOTS_PER_EPOCH
  · -- L in the current epoch: its entry moves to the first half, unchanged
    have hka : bidIndex a = some (P.SLOTS_PER_EPOCH + L.slot.toNat % P.SLOTS_PER_EPOCH) := by
      rw [hbi_a, if_pos e1]
    have hkb : bidIndex { b with slot := next } = some (L.slot.toNat % P.SLOTS_PER_EPOCH) := by
      rw [hbi_b, if_neg (by omega), if_pos (by omega)]
    have hiff : BidLive { b with slot := next } ↔ BidLive a := by
      constructor
      · rintro ⟨k, E, hk, hE, hw⟩
        rw [hkb] at hk; cases hk
        have hE' : (A.extract P.SLOTS_PER_EPOCH A.size ++ Array.replicate P.SLOTS_PER_EPOCH
            JauneConsensus.Gloas.BuilderPendingPayment.empty)[L.slot.toNat % P.SLOTS_PER_EPOCH]? =
            some E := by rw [← hbp]; exact hE
        rw [shifted_low hsz hLm] at hE'
        exact ⟨_, E, hka, hE', by rw [hLb'] at hw; exact hw⟩
      · rintro ⟨k, E, hk, hE, hw⟩
        rw [hka] at hk; cases hk
        refine ⟨_, E, hkb, ?_, by rw [hLb']; exact hw⟩
        show ({ b with slot := next } : GloasState P).builder_pending_payments.toArray[_]? = _
        rw [hbp, shifted_low hsz hLm]; exact hE
    by_cases hl : BidLive a
    · rw [exposure_le_live hl, exposure_le_live (hiff.mpr hl)]; omega
    · rw [exposure_of_not_live hl, exposure_of_not_live (fun h => hl (hiff.mp h)), hLb', ← hL]; omega
  · by_cases e2 : L.slot.toNat / P.SLOTS_PER_EPOCH + 1 = a.slot.toNat / P.SLOTS_PER_EPOCH
    · -- L in the previous epoch: it leaves the window
      have hka : bidIndex a = some (L.slot.toNat % P.SLOTS_PER_EPOCH) := by
        rw [hbi_a, if_neg e1, if_pos e2]
      have hkb : bidIndex { b with slot := next } = none := by
        rw [hbi_b, if_neg (by omega), if_neg (by omega)]
      have hnl : ¬ BidLive { b with slot := next } := by
        rintro ⟨_, _, h, _⟩; rw [hkb] at h; cases h
      rw [exposure_of_not_live hnl, hLb']
      by_cases hlive : BidLive a
      · rw [exposure_le_live hlive]
        obtain ⟨k, E, hk, hE, hEw⟩ := hlive
        rw [hka] at hk; cases hk
        obtain ⟨E', hE', hw0, _⟩ := g7 _ hka
        rw [hE] at hE'; cases hE'
        have hEf : (A.extract 0 P.SLOTS_PER_EPOCH).toList[L.slot.toNat % P.SLOTS_PER_EPOCH]? = some E := by
          rw [Array.getElem?_toList, Array.getElem?_extract]
          simp only [hsz]
          rw [if_pos (by omega)]
          simpa using hE
        have hex := filter_sum_le_of_excluded (fun p : JauneConsensus.Gloas.BuilderPendingPayment =>
          decide (q ≤ p.weight)) (fun p => withdrawalAmount i p.withdrawal) _ _ E hEf
          (by simp only [decide_eq_false_iff_not]; rw [hw0]; show ¬ q.toNat ≤ 0; omega)
        rw [hEw, ← hL] at hex
        rw [hpa, hpb]; omega
      · rw [exposure_of_not_live hlive, ← hL]
        omega
    · -- L older (or later): out of the window before; after, either still out or in the
      -- emptied second half
      have hka : bidIndex a = none := by rw [hbi_a, if_neg e1, if_neg e2]
      have hnla : ¬ BidLive a := by unfold BidLive; rw [hka]; rintro ⟨_, _, h, _⟩; cases h
      have hnlb : ¬ BidLive { b with slot := next } ∨ L.value.toNat = 0 := by
        by_cases e3 : L.slot.toNat / P.SLOTS_PER_EPOCH = a.slot.toNat / P.SLOTS_PER_EPOCH + 1
        · by_cases hv : L.value.toNat = 0
          · exact Or.inr hv
          · refine Or.inl ?_
            rintro ⟨_, E, hk, hE, hEw⟩
            rw [hbi_b, if_pos e3] at hk
            cases hk
            have hE' : (A.extract P.SLOTS_PER_EPOCH A.size ++ Array.replicate P.SLOTS_PER_EPOCH
                JauneConsensus.Gloas.BuilderPendingPayment.empty)[P.SLOTS_PER_EPOCH +
                  L.slot.toNat % P.SLOTS_PER_EPOCH]? = some E := by rw [← hbp]; exact hE
            rw [shifted_high hsz (by omega) (by omega)] at hE'
            cases hE'
            rw [hLb'] at hEw
            apply hv
            have := congrArg (·.amount) hEw
            simp only [bidWithdrawal] at this
            rw [← this]; rfl
        · refine Or.inl ?_
          rintro ⟨_, _, h, _⟩
          rw [hbi_b, if_neg e3, if_neg (by omega)] at h; cases h
      rw [exposure_of_not_live hnla, ← hL]
      rcases hnlb with hnlb | hv
      · rw [exposure_of_not_live hnlb, hLb']; omega
      · have : exposure { b with slot := next } i = 0 := by
          unfold exposure; rw [if_neg (fun e => by have := e.2.1; rw [hLb'] at this; omega)]
        omega

theorem noLiveWeight_congr {s s' : GloasState P} (hf : InvariantFrame s s') (h : NoLiveWeightOnLatestBid s) :
    NoLiveWeightOnLatestBid s' := by
  have hb : bidIndex s' = bidIndex s := by
    unfold bidIndex currentEpoch; rw [hf.2.2.2.1, hf.2.2.2.2.2.2.1]
  intro k hk
  rw [hb] at hk
  rw [hf.2.1, hf.2.2.2.1]
  exact h k hk

/-- **G3-05 over `process_slots`**, together with G3-07 and FutureEmpty (needs quorum
positivity and `0 < SLOTS_PER_EPOCH`). -/
theorem processSlots_pendingCovered (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Context} {s s' : GloasState P} {slot : U64}
    (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s')
    (hu : PendingCovered s ∧ NoLiveWeightOnLatestBid s ∧ FutureEmpty s) :
    PendingCovered s' ∧ NoLiveWeightOnLatestBid s' ∧ FutureEmpty s' :=
  processSlots_induction (ctx := ctx) (fun m => PendingCovered m ∧ NoLiveWeightOnLatestBid m ∧ FutureEmpty m)
    (fun st st1 st2 next hI f1 hn hc => by
      obtain ⟨g5, g7, fe⟩ := hI
      have h7 := slotIteration_noLiveWeight hspe ⟨g7, fe⟩ f1 hn hc
      refine ⟨?_, h7⟩
      have hb2 : st2.builders = st.builders := (slotIteration_core f1 hc).1
      have key : ∀ i, pendingBalance { st2 with slot := next } i + exposure { st2 with slot := next } i ≤
          pendingBalance st i + exposure st i := by
        intro i
        rcases hc with ⟨rfl, hne⟩ | ⟨h0, he⟩
        · rw [hn] at hne
          obtain ⟨hdiv, _⟩ := div_succ_of_mod_ne hne
          have hbi : bidIndex { st2 with slot := next } = bidIndex st := by
            unfold bidIndex currentEpoch; simp only []; rw [f1.2.2.2.1, hn, hdiv]
          have hiff : BidLive { st2 with slot := next } ↔ BidLive st := by
            unfold BidLive
            rw [hbi]
            show (∃ k E, bidIndex st = some k ∧ st2.builder_pending_payments.toArray[k]? = some E ∧
              E.withdrawal = bidWithdrawal st2.latest_execution_payload_bid) ↔ _
            rw [f1.2.1, f1.2.2.2.1]
          have hp : pendingBalance { st2 with slot := next } i = pendingBalance st i := pendingBalance_congr f1 i
          by_cases hl : BidLive st
          · rw [exposure_le_live hl, exposure_le_live (hiff.mpr hl), hp]
          · rw [exposure_of_not_live hl, exposure_of_not_live (fun h => hl (hiff.mp h)), hp]
            show _ + withdrawalAmount i (bidWithdrawal st2.latest_execution_payload_bid) ≤ _
            rw [f1.2.2.2.1]
        · obtain ⟨a, b, fa, hb, fb⟩ := processEpoch_phases he
          have fa' := invariantFrame.trans f1 fa
          have g7a := noLiveWeight_congr fa' g7
          have hn' : next.toNat = a.slot.toNat + 1 := by rw [fa'.2.2.2.2.2.2.1]; exact hn
          have rc := rotation_cover hq hspe hb g7a hn' h0 i
          have e1 : pendingBalance { st2 with slot := next } i = pendingBalance b i := pendingBalance_congr fb i
          have e2 : exposure { st2 with slot := next } i = exposure { b with slot := next } i :=
            exposure_congr (s := { b with slot := next }) (s' := { st2 with slot := next })
              fb.2.2.2.1 fb.2.1 rfl i
          have e3 : pendingBalance a i = pendingBalance st i := pendingBalance_congr fa' i
          have e4 : exposure a i = exposure st i :=
            exposure_congr fa'.2.2.2.1 fa'.2.1 fa'.2.2.2.2.2.2.1 i
          omega
      intro i bb hbb
      have hbb' : st.builders.toArray[i]? = some bb := by
        have : ({ st2 with slot := next } : GloasState P).builders = st.builders := hb2
        rw [← this]; exact hbb
      exact Nat.le_trans (key i) (g5 i bb hbb')) h hu

end JauneConsensus.Facts.Gloas.Invariant
