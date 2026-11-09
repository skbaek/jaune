import JauneConsensus.Facts.Gloas.InvariantsVLen

/-!
# G3-05 through `process_withdrawals` (goal `eip8282-gloas-cross-layer-v1`, G3b)

The withdrawals of a block run before its bid, so what they must keep is `PendLe`
(`pend ≤ balance` for every builder); the bid then restores the exposure term. Under the two
G3-12 bounds (`len(validators) ≤ 2^40`, `len(builders) ≤ 2^40`):

* **provenance** (`getPendingPartialWithdrawals_inRange`, `getValidatorsSweepWithdrawals_inRange`):
  every withdrawal of the two validator phases names an index of the registry, so under
  `validatorsBound` none carries `BUILDER_INDEX_FLAG` and none is routed to a builder;
* the builder-withdrawal phase routes to builder `i` exactly the `pendW` of the processed prefix of
  `builder_pending_withdrawals` (`routed_builderWithdrawals`: the provenance of
  `getBuilderWithdrawals` and the injectivity of `convert_builder_index_to_validator_index` below
  `2^40`, with G3-03);
* the builders sweep routes nothing to a builder with something pending
  (`routed_sweep_zero`: it pays only withdrawable builders, which G3-04 leaves with nothing
  pending);
* so a builder with something pending loses exactly the paid prefix from both `pend` and its
  balance (`applyWithdrawals_builder_balance`), and `processWithdrawals_pendLe` follows.
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-- `pend ≤ balance` for every builder: G3-05 without the exposure term. -/
def PendLe (s : GSt P) : Prop :=
  ∀ (i : Nat) (b : JauneConsensus.Gloas.Builder), s.builders.toArray[i]? = some b →
    pend s i ≤ b.balance.toNat

theorem pendLe_of_covered {s : GSt P} (h : PendingCovered s) : PendLe s := fun i b hb =>
  Nat.le_trans (Nat.le_add_right _ _) (h i b hb)

/-! ## Routing arithmetic -/

theorem sum_filter_eq_ite {α : Type} (p : α → Bool) (f : α → Nat) (l : List α) :
    ((l.filter p).map f).sum = (l.map (fun x => if p x then f x else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [List.filter_cons, h, ih]

theorem routedSum_append (bi : U64) (l m : List Withdrawal) :
    routedSum bi (l ++ m) = routedSum bi l + routedSum bi m := by
  simp [routedSum, List.filter_append, List.sum_append]

theorem routedSum_zero {bi : U64} {l : List Withdrawal} (h : ∀ w ∈ l, ¬ Routes bi w) :
    routedSum bi l = 0 := by
  unfold routedSum
  rw [List.filter_eq_nil_iff.mpr (fun w hw => by simpa using h w hw)]
  rfl

/-- A withdrawal whose validator index is below `2^40` is routed to no builder. -/
theorem not_routes_of_lt {bi : U64} {w : Withdrawal} (hw : w.validator_index.toNat < 2 ^ 40) :
    ¬ Routes bi w := by
  intro h
  rw [Routes, convertBuilderIndexToValidatorIndex_eq_ok_iff] at h
  have hf : JauneConsensus.Gloas.BUILDER_INDEX_FLAG.toNat = 2 ^ 40 := rfl
  rw [hf] at h
  have h1 : w.validator_index.toNat.testBit 40 = false := Nat.testBit_lt_two_pow hw
  rw [h, Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true] at h1
  exact absurd h1 (by decide)

/-- `convert_builder_index_to_validator_index` is injective below `2^40`. -/
theorem routes_inj {bi bj : U64} {w : Withdrawal} (h1 : Routes bi w)
    (h2 : JauneConsensus.Gloas.convertBuilderIndexToValidatorIndex bj = .ok w.validator_index)
    (hi : bi.toNat < 2 ^ 40) (hj : bj.toNat < 2 ^ 40) : bi.toNat = bj.toNat := by
  rw [Routes, convertBuilderIndexToValidatorIndex_eq_ok_iff] at h1
  rw [convertBuilderIndexToValidatorIndex_eq_ok_iff] at h2
  have hf : JauneConsensus.Gloas.BUILDER_INDEX_FLAG.toNat = 2 ^ 40 := rfl
  rw [hf] at h1 h2
  rw [← mask_or_flag _ hi, ← mask_or_flag _ hj, ← h1, ← h2]

/-! ## Provenance of the two validator phases -/

/-- A property of every collected withdrawal is kept. -/
def keepAll (Pw : Withdrawal → Prop) : StepRel (Array Withdrawal) where
  R x y := (∀ w ∈ x.toList, Pw w) → ∀ w ∈ y.toList, Pw w
  refl _ h := h
  trans h₁ h₂ h := h₂ (h₁ h)

theorem keepAll_push {Pw : Withdrawal → Prop} {x : Array Withdrawal} {w : Withdrawal}
    (hw : Pw w) : (keepAll Pw).R x (x.push w) := by
  intro h v hv
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | rfl
  · exact h v hv
  · exact hw

section Provenance

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRel.forIn_array_rel _ (fun x => x.2.1) ?_ _ _ $h; intro _ _; gvcg))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRel.forIn_list_rel _ (fun x => x.2.1) ?_ _ _ $h; intro _ _; gvcg))
local macro_rules
  | `(tactic| gstep_close) =>
    `(tactic| exact keepAll_push (Array.getElem?_eq_some_iff.mp (pl_get_ok.mp (by assumption))).1)

theorem getPendingPartialWithdrawals_inRange (st : GSt P) (idx : U64) (prior : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.getPendingPartialWithdrawals st idx prior)
      (fun r => (keepAll (fun w => w.validator_index.toNat < st.validators.toArray.size)).R
        #[] r.1) := by
  unfold JauneConsensus.Gloas.getPendingPartialWithdrawals; gvcg

theorem getValidatorsSweepWithdrawals_inRange (st : GSt P) (idx : U64) (prior : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.getValidatorsSweepWithdrawals st idx prior)
      (fun r => (keepAll (fun w => w.validator_index.toNat < st.validators.toArray.size)).R
        #[] r.1) := by
  unfold JauneConsensus.Gloas.getValidatorsSweepWithdrawals
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  gvcg

end Provenance

/-- A validator-phase output routes to no builder, under `validatorsBound`. -/
theorem routedSum_validatorPhase {st : GSt P} {ws : Array Withdrawal}
    (h : (keepAll (fun w => w.validator_index.toNat < st.validators.toArray.size)).R #[] ws)
    (hvb : st.validators.toArray.size ≤ 2 ^ 40) (bi : U64) : routedSum bi ws.toList = 0 :=
  routedSum_zero (fun w hw => not_routes_of_lt
    (Nat.lt_of_lt_of_le (h (fun _ hv => by simp at hv) w hw) hvb))

/-! ## The builder phases -/

/-- The builder-withdrawal phase routes to builder `bi` the `pendW` of the processed prefix. -/
theorem routed_builderWithdrawals {st : GSt P} {idx : U64} {prior bw : Array Withdrawal}
    {idx' n : U64}
    (h : JauneConsensus.Gloas.getBuilderWithdrawals st idx prior = .ok (bw, idx', n))
    (hr : ∀ w ∈ st.builder_pending_withdrawals.toArray.toList, w.builder_index.toNat < 2 ^ 40)
    {bi : U64} (hbi : bi.toNat < 2 ^ 40) :
    n.toNat = bw.size ∧ routedSum bi bw.toList =
      pendW (st.builder_pending_withdrawals.toArray.toList.take bw.size) bi.toNat := by
  obtain ⟨hn, hp⟩ := getBuilderWithdrawals_provenance h
  refine ⟨hn, ?_⟩
  have hL : ∀ k (hk : k < bw.size), ∃ e,
      st.builder_pending_withdrawals.toArray.toList[k]? = some e ∧ bw[k].amount = e.amount ∧
      JauneConsensus.Gloas.convertBuilderIndexToValidatorIndex e.builder_index =
        .ok bw[k].validator_index := by
    intro k hk
    obtain ⟨e, he, _, h2, h3⟩ := hp k hk
    exact ⟨e, by rw [Array.getElem?_toList]; exact he, h2, h3⟩
  have hlen : bw.size ≤ st.builder_pending_withdrawals.toArray.toList.length := by
    by_cases h0 : bw.size = 0
    · omega
    · obtain ⟨e, he, -⟩ := hL (bw.size - 1) (by omega)
      have h3 := (List.getElem?_eq_some_iff.mp he).1
      have h4 : st.builder_pending_withdrawals.toArray.toList.length =
          st.builder_pending_withdrawals.toArray.size := Array.length_toList
      omega
  unfold routedSum pendW
  rw [sum_filter_eq_ite]
  congr 1
  apply List.ext_getElem
  · have h4 : st.builder_pending_withdrawals.toArray.toList.length =
        st.builder_pending_withdrawals.toArray.size := Array.length_toList
    simp only [List.length_map, Array.length_toList, List.length_take]; omega
  · intro k h1 h2
    have hk : k < bw.size := by simpa using h1
    obtain ⟨e, he, hamt, hcv⟩ := hL k hk
    obtain ⟨hkL, hke⟩ := List.getElem?_eq_some_iff.mp he
    have hemem : e ∈ st.builder_pending_withdrawals.toArray.toList := by
      rw [← hke]; exact List.getElem_mem hkL
    have heb := hr e hemem
    simp only [List.getElem_map, Array.getElem_toList, List.getElem_take, hke]
    split
    · rename_i hc
      have hR : Routes bi bw[k] := by simpa using hc
      have hij := routes_inj hR hcv hbi heb
      unfold wAmt
      rw [if_pos hij.symm]
      simp [hamt]
    · rename_i hc
      have hR : ¬ Routes bi bw[k] := by simpa using hc
      unfold wAmt
      rw [if_neg]
      intro hij
      apply hR
      have : e.builder_index = bi := U64.ext_toNat hij
      rw [Routes, ← this]
      exact hcv

/-- The builders sweep routes nothing to a builder with something pending (G3-04). -/
theorem routed_sweep_zero (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {st : GSt P} {idx : U64}
    {prior sw : Array Withdrawal} {idx' n : U64}
    (h : JauneConsensus.Gloas.getBuildersSweepWithdrawals st idx prior = .ok (sw, idx', n))
    (hbb : st.builders.toArray.size ≤ 2 ^ 40) (hx : ExitedHaveNoPending st)
    {bi : U64} {b : JauneConsensus.Gloas.Builder} (hb : st.builders.toArray[bi.toNat]? = some b)
    (hp : pend st bi.toNat ≠ 0) : routedSum bi sw.toList = 0 := by
  have hbi : bi.toNat < 2 ^ 40 := lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hb).1 hbb
  refine routedSum_zero (fun w hw hR => ?_)
  obtain ⟨k, hk, hkw⟩ := List.mem_iff_getElem.mp hw
  have hk' : k < sw.size := by simpa using hk
  have hkw' : sw[k] = w := by rw [← hkw]; simp
  obtain ⟨bj, b', e, he, hcv, hb', hwe, -⟩ := getBuildersSweepWithdrawals_provenance h k hk'
  rw [hkw'] at hcv
  have hbj : bj.toNat < 2 ^ 40 := lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hb').1 hbb
  have hij := routes_inj hR hcv hbi hbj
  rw [hij, hb'] at hb
  cases hb
  have hwe' : b.withdrawable_epoch.toNat ≤ e.toNat := hwe
  have hel := epoch_lt_far hspe st
  rw [← getCurrentEpoch_toNat he] at hel
  have hne : b.withdrawable_epoch ≠ FAR_FUTURE_EPOCH := by
    intro hf; rw [hf] at hwe'; omega
  exact hp (by rw [hij]; exact hx _ b hb' hne)

/-! ## The shape of `process_withdrawals` -/

theorem getExpectedWithdrawals_parts {s : GSt P} {ex : JauneConsensus.Gloas.ExpectedWithdrawals}
    (h : JauneConsensus.Gloas.getExpectedWithdrawals s = .ok ex) :
    ∃ (bw pw sw vw p2 p3 p4 : Array Withdrawal) (i1 i2 i3 i4 n2 n3 n4 : U64),
      JauneConsensus.Gloas.getBuilderWithdrawals s s.next_withdrawal_index #[] =
        .ok (bw, i1, ex.processed_builder_withdrawals_count) ∧
      JauneConsensus.Gloas.getPendingPartialWithdrawals s i1 p2 = .ok (pw, i2, n2) ∧
      JauneConsensus.Gloas.getBuildersSweepWithdrawals s i2 p3 = .ok (sw, i3, n3) ∧
      JauneConsensus.Gloas.getValidatorsSweepWithdrawals s i3 p4 = .ok (vw, i4, n4) ∧
      ex.withdrawals.toList = bw.toList ++ pw.toList ++ sw.toList ++ vw.toList := by
  unfold JauneConsensus.Gloas.getExpectedWithdrawals at h
  obtain ⟨⟨bw, i1, n1⟩, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨⟨pw, i2, n2⟩, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨⟨sw, i3, n3⟩, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨⟨vw, i4, n4⟩, h4, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact ⟨bw, pw, sw, vw, _, _, _, i1, i2, i3, i4, n2, n3, n4, h1, h2, h3, h4, by simp⟩

/-- The builders and both builder queues are unchanged. -/
def BQ (s s' : GSt P) : Prop :=
  s'.builders = s.builders ∧ s'.builder_pending_withdrawals = s.builder_pending_withdrawals ∧
    s'.builder_pending_payments = s.builder_pending_payments

def bq : StepRel (GSt P) where
  R := BQ
  refl _ := ⟨rfl, rfl, rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

/-- Both builder queues are unchanged. -/
def QE (s s' : GSt P) : Prop :=
  s'.builder_pending_withdrawals = s.builder_pending_withdrawals ∧
    s'.builder_pending_payments = s.builder_pending_payments

def qe : StepRel (GSt P) where
  R := QE
  refl _ := ⟨rfl, rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

section Gen

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show BQ _ _ from ⟨rfl, rfl, rfl⟩))

theorem updateNextWithdrawalIndex_bq (s : GSt P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalIndex s ws) (bq.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalIndex; gvcg

theorem updateNextWithdrawalBuilderIndex_bq (s : GSt P) (n : U64) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex s n) (bq.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex; gvcg

theorem updateNextWithdrawalValidatorIndex_bq (s : GSt P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex s ws) (bq.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex; gvcg

end Gen

section GenQ

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show QE _ _ from ⟨rfl, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (decreaseBalance_invFrame _ _ _) $h
               exact (show QE _ _ from ⟨hh.2.2.1, hh.2.1⟩)))

theorem applyWithdrawals_qe (s : GSt P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.applyWithdrawals s ws) (qe.R s) := by
  unfold JauneConsensus.Gloas.applyWithdrawals; gvcg

end GenQ

/-- `process_withdrawals` returns its state, or applies the expected withdrawals, keeps the
payments, and drops the processed prefix of the builder withdrawals. -/
theorem processWithdrawals_cases {s s' : GSt P}
    (h : JauneConsensus.Gloas.processWithdrawals s = .ok s') :
    s' = s ∨ ∃ ex t, JauneConsensus.Gloas.getExpectedWithdrawals s = .ok ex ∧
      JauneConsensus.Gloas.applyWithdrawals s ex.withdrawals = .ok t ∧
      s'.builders = t.builders ∧ s'.builder_pending_payments = s.builder_pending_payments ∧
      s'.builder_pending_withdrawals.toArray.toList =
        s.builder_pending_withdrawals.toArray.toList.drop
          ex.processed_builder_withdrawals_count.toNat := by
  unfold JauneConsensus.Gloas.processWithdrawals at h
  split at h
  · cases h; exact Or.inl rfl
  · obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨t1, h1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨t2, h2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨t6, h6, h⟩ := bind_eq_ok_iff.mp h
    have q1 := applyWithdrawals_qe _ _ _ h1
    have q2 := updateNextWithdrawalIndex_bq _ _ _ h2
    have q6 := updateNextWithdrawalBuilderIndex_bq _ _ _ h6
    have q7 := updateNextWithdrawalValidatorIndex_bq _ _ _ h
    refine Or.inr ⟨ex, t1, hex, h1, q7.1.trans (q6.1.trans q2.1),
      q7.2.2.trans (q6.2.2.trans (q2.2.2.trans q1.2)), ?_⟩
    rw [q7.2.1, q6.2.1]
    simp only [JauneConsensus.Gloas.updatePendingPartialWithdrawals,
      JauneConsensus.Gloas.updateBuilderPendingWithdrawals,
      JauneConsensus.Gloas.updatePayloadExpectedWithdrawals]
    rw [q2.2.1, q1.1]
    simp [ProgressiveListS.ofArray, Array.toList_extract]

/-! ## `PendLe` through the withdrawals -/

theorem pendW_take_drop (l : List JauneConsensus.Gloas.BuilderPendingWithdrawal) (n i : Nat) :
    pendW l i = pendW (l.take n) i + pendW (l.drop n) i := by
  conv_lhs => rw [← List.take_append_drop n l]
  exact pendW_append _ _ _

/-- **`process_withdrawals` keeps `PendLe`**, given G3-03 and G3-04 and the two G3-12 bounds at
the state it reads. -/
theorem processWithdrawals_pendLe (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {s s' : GSt P}
    (h : JauneConsensus.Gloas.processWithdrawals s = .ok s') (hr : PendingRefsInRange s)
    (hx : ExitedHaveNoPending s) (validatorsBound : s.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : s.builders.toArray.size ≤ 2 ^ 40) (hle : PendLe s) : PendLe s' := by
  rcases processWithdrawals_cases h with rfl | ⟨ex, t, hex, ht, hb', hp', hw'⟩
  · exact hle
  intro i b' hb
  rw [hb'] at hb
  have hsz : t.builders.toArray.size = s.builders.toArray.size :=
    (applyWithdrawals_wf _ _ _ ht).2.2.2.2.2.1
  have hi : i < s.builders.toArray.size := by
    rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hb).1
  obtain ⟨b, hb0⟩ : ∃ b, s.builders.toArray[i]? = some b := ⟨_, Array.getElem?_eq_getElem hi⟩
  set L := s.builder_pending_withdrawals.toArray.toList with hLdef
  set n := ex.processed_builder_withdrawals_count.toNat with hn
  have hpend' : pend s' i = pendW (L.drop n) i +
      pendP s.builder_pending_payments.toArray.toList i := by
    unfold pend; rw [hw', hp']
  have hpend : pend s i = pendW (L.take n) i + pendW (L.drop n) i +
      pendP s.builder_pending_payments.toArray.toList i := by
    unfold pend; rw [← hLdef, pendW_take_drop L n i]
  by_cases hz : pend s i = 0
  · rw [hpend']; omega
  obtain ⟨bi, hbi⟩ := (U64.ofNat?_ok_iff (site := "BuilderIndex")).mpr (show i < 2 ^ 64 by omega)
  have hbiN : bi.toNat = i := U64.toNat_ofNat? hbi
  have hbi40 : bi.toNat < 2 ^ 40 := by omega
  obtain ⟨bw, pw, sw, vw, p2, p3, p4, i1, i2, i3, i4, n2, n3, n4, h1, h2, h3, h4, hws⟩ :=
    getExpectedWithdrawals_parts hex
  have hr40 : ∀ w ∈ s.builder_pending_withdrawals.toArray.toList, w.builder_index.toNat < 2 ^ 40 :=
    fun w hw => Nat.lt_of_lt_of_le (hr.1 w hw) buildersBound
  obtain ⟨hnb, rb⟩ := routed_builderWithdrawals h1 hr40 hbi40
  have rp := routedSum_validatorPhase (getPendingPartialWithdrawals_inRange _ _ _ _ h2)
    validatorsBound bi
  have rv := routedSum_validatorPhase (getValidatorsSweepWithdrawals_inRange _ _ _ _ h4)
    validatorsBound bi
  have rs := routed_sweep_zero hspe h3 buildersBound hx (bi := bi) (b := b) (by rw [hbiN]; exact hb0)
    (by rw [hbiN]; exact hz)
  have hroute : routedSum bi ex.withdrawals.toList = pendW (L.take n) i := by
    rw [hws, routedSum_append, routedSum_append, routedSum_append, rb, rp, rs, rv, hbiN, ← hnb]
    simp only [Nat.add_zero]
    rfl
  have hcov := hle i b hb0
  obtain ⟨b'', hb'', -, hbal⟩ := applyWithdrawals_builder_balance ht buildersBound
    (bi := bi) (b := b) (by rw [hbiN]; exact hb0) (by rw [hroute]; omega)
  rw [hbiN, hb] at hb''
  cases hb''
  rw [hroute] at hbal
  rw [hpend']
  omega

end JauneConsensus.Facts.Gloas.Inv
