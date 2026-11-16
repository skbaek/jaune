import JauneConsensus.Facts.Gloas.Frame
import JauneConsensus.GloasBlock

/-!
# B5 at function level (goal `eip8282-gloas-cross-layer-v1`, BF1)

Function-level parts of statements.md B5 ("where builder balance goes") and its §0.3 controls:

* `processWithdrawalsG_early_return` (B5(iv)): an EMPTY parent block makes `process_withdrawals`
  return its state;
* `processExecutionPayloadBid_bls_indep` (§0.3): with `bls = false` the bid processing equals its
  `bls = true` run whenever the bid signature it would check verifies;
* `applyWithdrawals_builder_balance` (B5(i) at function level): over `apply_withdrawals`, the
  builder's balance falls by exactly the withdrawals routed to it, in ℕ, with no saturation, under
  the G3-05-shaped hypothesis (what is routed to the builder is at most its balance) and the
  `buildersBound` hypothesis;
* provenance of the builder withdrawals (B5(ii) at function level):
  `getBuilderWithdrawals_provenance` (each is a `builder_pending_withdrawals` prefix entry) and
  `getBuildersSweepWithdrawals_provenance` (each is a withdrawable builder's own
  `execution_address` with its balance after the prior withdrawals);
* closed-state witnesses: the six payment fates and the G3-05 saturation witness (see
  `B5Witnesses.lean`).
-/

namespace JauneConsensus.Facts.Gloas

open JauneConsensus JauneConsensus.Facts

variable {P : Preset}

/-! ## B5(iv): EMPTY parent -/

/-- `process_withdrawals` returns early when the parent block is EMPTY (CL:2073-2075). -/
theorem processWithdrawalsG_early_return (st : Gloas.BeaconState P)
    (h : st.latest_block_hash ≠ st.latest_execution_payload_bid.block_hash) :
    Gloas.processWithdrawals st = .ok st := by
  unfold Gloas.processWithdrawals
  simp [h]; rfl

/-! ## §0.3: the bid signature switch -/

/-- With `bls = false` the bid signature check returns what the `bls = true` check returns,
whenever the signature it would check verifies; every rejection (unknown builder index, domain)
is the same. -/
theorem verifyExecutionPayloadBidSignature_bls_indep (cfg : Config) (ev : Bool)
    (st : Gloas.BeaconState P) (sb : Gloas.SignedExecutionPayloadBid)
    (hsig : ∀ (builder : Gloas.Builder) (dom : Domain),
      st.builders.get sb.message.builder_index.toNat "verify_execution_payload_bid_signature" =
          .ok builder →
      Gloas.getDomain st Gloas.DOMAIN_BEACON_BUILDER = .ok dom →
      blsVerify true builder.pubkey (computeSigningRoot sb.message dom) sb.signature = true) :
    Gloas.verifyExecutionPayloadBidSignature { cfg, blsActive := false, executionValid := ev } st sb =
      Gloas.verifyExecutionPayloadBidSignature { cfg, blsActive := true, executionValid := ev } st sb := by
  unfold Gloas.verifyExecutionPayloadBidSignature
  cases hb : st.builders.get sb.message.builder_index.toNat "verify_execution_payload_bid_signature" with
  | error e => rfl
  | ok builder =>
    cases hd : Gloas.getDomain st Gloas.DOMAIN_BEACON_BUILDER with
    | error e => simp [bind, Except.bind]
    | ok dom =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [hsig builder dom hb hd]
      rfl

/-- §0.3 `processExecutionPayloadBid_bls_indep`: with `bls = false` the bid processing equals its
`bls = true` run whenever the bid signature it would check verifies. Every other check, effect
and rejection is shared (the switch reaches the function only through the signature check). -/
theorem processExecutionPayloadBid_bls_indep (cfg : Config) (ev : Bool)
    (st : Gloas.BeaconState P) (sb : Gloas.SignedExecutionPayloadBid)
    (hsig : ∀ (builder : Gloas.Builder) (dom : Domain),
      st.builders.get sb.message.builder_index.toNat "verify_execution_payload_bid_signature" =
          .ok builder →
      Gloas.getDomain st Gloas.DOMAIN_BEACON_BUILDER = .ok dom →
      blsVerify true builder.pubkey (computeSigningRoot sb.message dom) sb.signature = true) :
    Gloas.processExecutionPayloadBid { cfg, blsActive := false, executionValid := ev } st sb =
      Gloas.processExecutionPayloadBid { cfg, blsActive := true, executionValid := ev } st sb := by
  unfold Gloas.processExecutionPayloadBid
  rw [verifyExecutionPayloadBidSignature_bls_indep cfg ev st sb hsig]

/-! ## B5(i) at function level: `apply_withdrawals` and one builder's balance -/

/-- `(i | 2^40) & ~2^40 = i` for `i < 2^40`. -/
theorem mask_or_flag (i : ℕ) (h : i < 2 ^ 40) : (i ||| 2 ^ 40) &&& (2 ^ 64 - 1 - 2 ^ 40) = i := by
  have hm : (2 ^ 64 - 1 - 2 ^ 40 : ℕ) = (2 ^ 64 - 1) ^^^ 2 ^ 40 := by decide
  rw [hm]
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow]
  by_cases hk : k = 40
  · subst hk
    have : i.testBit 40 = false := Nat.testBit_lt_two_pow h
    simp [this]
  · by_cases hk2 : k < 64
    · simp [hk2, Ne.symm hk]
    · have : i.testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [this, hk2, Ne.symm hk]

/-- A withdrawal routed to builder `bi` (statements.md B5(i)'s filter):
`convert_builder_index_to_validator_index(bi) = w.validator_index`. -/
theorem convertBuilderIndexToValidatorIndex_eq_ok_iff (bi v : U64) :
    Gloas.convertBuilderIndexToValidatorIndex bi = .ok v ↔
      v.toNat = bi.toNat ||| Gloas.BUILDER_INDEX_FLAG.toNat := by
  have hlt : bi.toNat ||| Gloas.BUILDER_INDEX_FLAG.toNat < 2 ^ 64 :=
    Nat.or_lt_two_pow bi.toNat_lt (by decide)
  unfold Gloas.convertBuilderIndexToValidatorIndex
  constructor
  · intro h
    exact U64.toNat_ofNat? h
  · intro h
    obtain ⟨x, hx⟩ := U64.ofNat?_ok_iff.mpr hlt
    rw [hx]
    congr 1
    apply U64.ext_toNat
    rw [U64.toNat_ofNat? hx, h]

instance (bi : U64) (w : Withdrawal) :
    Decidable (Gloas.convertBuilderIndexToValidatorIndex bi = .ok w.validator_index) :=
  decidable_of_iff _ (convertBuilderIndexToValidatorIndex_eq_ok_iff bi w.validator_index).symm

/-- A withdrawal is routed to builder `bi`: `convert_builder_index_to_validator_index(bi) ==
w.validator_index` (B5(i)'s filter). -/
abbrev Routes (bi : U64) (w : Withdrawal) : Prop :=
  Gloas.convertBuilderIndexToValidatorIndex bi = .ok w.validator_index

private theorem or_flag_and_flag (i : ℕ) : (i ||| 2 ^ 40) &&& 2 ^ 40 = 2 ^ 40 := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hk : 40 = k <;> simp [hk]

private theorem eq_or_flag_of_mask {v i : ℕ} (hv : v < 2 ^ 64) (hb : v &&& 2 ^ 40 ≠ 0)
    (hm : v &&& (2 ^ 64 - 1 - 2 ^ 40) = i) : v = i ||| 2 ^ 40 := by
  have hm' : (2 ^ 64 - 1 - 2 ^ 40 : ℕ) = (2 ^ 64 - 1) ^^^ 2 ^ 40 := by decide
  rw [hm'] at hm
  subst hm
  have h40 : v.testBit 40 = true := by
    by_contra hc
    apply hb
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hk : 40 = k
    · subst hk; simp at hc; simp [hc]
    · simp [hk]
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow]
  by_cases hk : 40 = k
  · subst hk; simp [h40]
  · by_cases hk2 : k < 64
    · simp [hk2, hk]
    · have : v.testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [this, hk]

theorem isBuilderIndex_of_routes {bi : U64} {w : Withdrawal} (h : Routes bi w) :
    Gloas.isBuilderIndex w.validator_index = true := by
  rw [Routes, convertBuilderIndexToValidatorIndex_eq_ok_iff] at h
  unfold Gloas.isBuilderIndex
  rw [h]
  have : Gloas.BUILDER_INDEX_FLAG.toNat = 2 ^ 40 := rfl
  rw [this, or_flag_and_flag]
  decide

theorem convertValidatorIndexToBuilderIndex_of_routes {bi : U64} {w : Withdrawal} (h : Routes bi w)
    (hbi : bi.toNat < 2 ^ 40) :
    Gloas.convertValidatorIndexToBuilderIndex w.validator_index = .ok bi := by
  rw [Routes, convertBuilderIndexToValidatorIndex_eq_ok_iff] at h
  have : Gloas.BUILDER_INDEX_FLAG.toNat = 2 ^ 40 := rfl
  rw [this] at h
  unfold Gloas.convertValidatorIndexToBuilderIndex
  rw [h, this, mask_or_flag _ hbi]
  obtain ⟨x, hx⟩ := U64.ofNat?_ok_iff.mpr bi.toNat_lt
  rw [hx]
  congr 1
  apply U64.ext_toNat
  exact U64.toNat_ofNat? hx

theorem routes_of_convert {bi j : U64} {w : Withdrawal}
    (hb : Gloas.isBuilderIndex w.validator_index = true)
    (hc : Gloas.convertValidatorIndexToBuilderIndex w.validator_index = .ok j) (hj : j.toNat = bi.toNat) :
    Routes bi w := by
  rw [Routes, convertBuilderIndexToValidatorIndex_eq_ok_iff]
  have hf : Gloas.BUILDER_INDEX_FLAG.toNat = 2 ^ 40 := rfl
  rw [hf]
  unfold Gloas.isBuilderIndex at hb
  rw [hf] at hb
  unfold Gloas.convertValidatorIndexToBuilderIndex at hc
  have := U64.toNat_ofNat? hc
  rw [hf] at this
  rw [← hj]
  exact eq_or_flag_of_mask w.validator_index.toNat_lt (by simpa using hb) this.symm

theorem ProgressiveListS_modify_ok {s : Spine} {α : Type} {xs ys : ProgressiveListS s α} {j : Nat}
    {g : α → M α} {site : String} (h : xs.modify j g site = .ok ys) :
    ∃ v v', xs.toArray[j]? = some v ∧ g v = .ok v' ∧ ys.toArray.size = xs.toArray.size ∧
      ∀ k, ys.toArray[k]? = if k = j then some v' else xs.toArray[k]? := by
  unfold ProgressiveListS.modify ProgressiveListS.get getAt at h
  cases hv : xs.toArray[j]? with
  | none => simp [hv, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | some v =>
    simp only [hv, bind, Except.bind, pure, Except.pure] at h
    cases hg : g v with
    | error e => rw [hg] at h; cases h
    | ok v' =>
      rw [hg] at h
      simp only at h
      unfold ProgressiveListS.set at h
      have hj : j < xs.toArray.size := by
        rcases Array.getElem?_eq_some_iff.mp hv with ⟨hj, -⟩; exact hj
      simp only [hj, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨v, v', rfl, hg, by simp, fun k => ?_⟩
      simp only [Array.getElem?_set]
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk, Ne.symm hk]

theorem saturatingSubGwei_exact {a d x : U64} (hle : d.toNat ≤ a.toNat)
    (h : Gloas.saturatingSubGwei a d = .ok x) : x.toNat + d.toNat = a.toNat := by
  unfold Gloas.saturatingSubGwei at h
  split at h
  · rw [U64.toNat_sub? h]
    omega
  · rename_i hlt
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have : ¬ d.toNat < a.toNat := hlt
    show 0 + d.toNat = a.toNat
    omega

/-- The routed amounts of a withdrawal list, in ℕ. -/
abbrev routedSum (bi : U64) (l : List Withdrawal) : Nat :=
  ((l.filter (fun w => decide (Routes bi w))).map (·.amount.toNat)).sum

private theorem loop_builder_balance {bi : U64}
    {body : Withdrawal → Gloas.BeaconState P → M (ForInStep (Gloas.BeaconState P))}
    (hstep : ∀ w s r b, body w s = .ok r → s.builders.toArray[bi.toNat]? = some b →
      r = .yield r.value ∧ ∃ b', r.value.builders.toArray[bi.toNat]? = some b' ∧
        b' = { b with balance := b'.balance } ∧
        (Routes bi w → w.amount.toNat ≤ b.balance.toNat →
          b'.balance.toNat + w.amount.toNat = b.balance.toNat) ∧
        (¬ Routes bi w → b' = b)) :
    ∀ (l : List Withdrawal) (s s' : Gloas.BeaconState P) (b : Gloas.Builder),
      forIn l s body = .ok s' → s.builders.toArray[bi.toNat]? = some b →
      routedSum bi l ≤ b.balance.toNat →
      ∃ b', s'.builders.toArray[bi.toNat]? = some b' ∧ b' = { b with balance := b'.balance } ∧
        b'.balance.toNat + routedSum bi l = b.balance.toNat
  | [], s, s', b, h, hb, _ => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨b, hb, rfl, rfl⟩
  | w :: l, s, s', b, h, hb, hsum => by
    rw [List.forIn_cons] at h
    simp only [bind, Except.bind] at h
    cases hr : body w s with
    | error e => rw [hr] at h; cases h
    | ok r =>
      rw [hr] at h
      obtain ⟨hy, b1, hb1, hb1e, hroute, hnot⟩ := hstep w s r b hr hb
      rw [hy] at h
      simp only at h
      by_cases hw : Routes bi w
      · have hs : routedSum bi (w :: l) = w.amount.toNat + routedSum bi l := by
          simp only [routedSum]
          rw [List.filter_cons_of_pos (by simpa using hw), List.map_cons, List.sum_cons]
        have hle : w.amount.toNat ≤ b.balance.toNat := by omega
        have heq := hroute hw hle
        obtain ⟨b', hb', hb'e, hbal⟩ := loop_builder_balance hstep l r.value s' b1 h hb1 (by omega)
        refine ⟨b', hb', ?_, by omega⟩
        rw [hb'e, hb1e]
      · have hs : routedSum bi (w :: l) = routedSum bi l := by
          simp only [routedSum]
          rw [List.filter_cons_of_neg (by simpa using hw)]
        have := hnot hw
        subst this
        obtain ⟨b', hb', hb'e, hbal⟩ := loop_builder_balance hstep l r.value s' b1 h hb1 (by omega)
        exact ⟨b', hb', hb'e, by omega⟩

/-- **B5(i) at function level.** Over `apply_withdrawals`, builder `bi`'s record keeps every field
but `balance`, and its balance falls by exactly the amounts of the withdrawals routed to it
(`convert_builder_index_to_validator_index(bi) == w.validator_index`), in ℕ and with no
saturation, given the G3-05-shaped hypothesis `g305` (the routed amounts fit the balance) and the
`buildersBound`-shaped hypothesis (`len(builders) ≤ 2^40`, so the index round-trips through the
`| 2^40` map). No validator bound is needed at this level: any withdrawal `apply_withdrawals`
routes to builder `bi` is in the filter, whichever phase produced it. -/
theorem applyWithdrawals_builder_balance {st st' : Gloas.BeaconState P} {ws : Array Withdrawal}
    (h : Gloas.applyWithdrawals st ws = .ok st') (buildersBound : st.builders.length ≤ 2 ^ 40)
    {bi : Gloas.BuilderIndex} {b : Gloas.Builder} (hb : st.builders.toArray[bi.toNat]? = some b)
    (g305 : routedSum bi ws.toList ≤ b.balance.toNat) :
    ∃ b', st'.builders.toArray[bi.toNat]? = some b' ∧ b' = { b with balance := b'.balance } ∧
      b'.balance.toNat + routedSum bi ws.toList = b.balance.toNat := by
  have hbi : bi.toNat < 2 ^ 40 :=
    lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hb).1 buildersBound
  unfold Gloas.applyWithdrawals at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i s'' hfor
  simp only [Except.ok.injEq] at h
  subst h
  rw [← Array.forIn_toList] at hfor
  refine loop_builder_balance ?_ ws.toList st s'' b hfor hb g305
  intro w s r b0 hr hb0
  split at hr
  · rename_i hib
    split at hr
    · cases hr
    · rename_i j hc
      split at hr
      · cases hr
      · rename_i bs hm
        simp only [Except.ok.injEq] at hr
        subst hr
        obtain ⟨v, v', hv, hg, -, hk⟩ := ProgressiveListS_modify_ok hm
        refine ⟨rfl, ?_⟩
        simp only [ForInStep.value]
        rw [hk]
        by_cases hji : U64.toNat bi = U64.toNat j
        · have hroutes : Routes bi w := routes_of_convert hib hc hji.symm
          simp only [hji, ↓reduceIte]
          rw [← hji, hb0] at hv
          cases hv
          split at hg
          · cases hg
          · rename_i x hx
            simp only [Except.ok.injEq] at hg
            subst hg
            exact ⟨_, rfl, rfl, fun _ hle => saturatingSubGwei_exact hle hx,
              fun hn => absurd hroutes hn⟩
        · simp only [hji, ↓reduceIte]
          refine ⟨b0, hb0, rfl, fun hw _ => ?_, fun _ => rfl⟩
          have := convertValidatorIndexToBuilderIndex_of_routes hw hbi
          rw [this] at hc
          cases hc
          exact absurd rfl hji
  · rename_i hnb
    split at hr
    · cases hr
    · rename_i s1 hdec
      simp only [Except.ok.injEq] at hr
      subst hr
      have hf := decreaseBalance_builderFrame s w.validator_index w.amount s1 hdec
      refine ⟨rfl, b0, ?_, rfl, fun hw => absurd (isBuilderIndex_of_routes hw) hnb, fun _ => rfl⟩
      simp only [ForInStep.value]
      rw [hf.1]
      exact hb0

/-- B5(i)'s second conjunct at function level: under the G3-05-shaped hypothesis, each routed
withdrawal's amount fits the builder's running balance (its balance less the routed amounts
before it), so no debit saturates. -/
theorem routed_le_runningBalance {bi : U64} {l : List Withdrawal} {bal : Nat}
    (g305 : routedSum bi l ≤ bal) {k : Nat} {w : Withdrawal} (hw : l[k]? = some w)
    (hr : Routes bi w) : routedSum bi (l.take k) + w.amount.toNat ≤ bal := by
  have hsplit : l = l.take k ++ w :: l.drop (k + 1) := by
    obtain ⟨hk, hkw⟩ := List.getElem?_eq_some_iff.mp hw
    conv_lhs => rw [← List.take_append_drop k l]
    rw [List.drop_eq_getElem_cons hk, hkw]
  have : routedSum bi l = routedSum bi (l.take k) + w.amount.toNat + routedSum bi (l.drop (k + 1)) := by
    conv_lhs => rw [hsplit]
    simp only [routedSum, List.filter_append, List.map_append, List.sum_append]
    rw [List.filter_cons_of_pos (by simpa using hr), List.map_cons, List.sum_cons]
    omega
  omega

/-! ## B5(ii) at function level: where builder withdrawals come from -/

/-- A loop invariant indexed by the position in the list: a step at position `m` from a state
satisfying `Inv m` yields a state satisfying `Inv (m+1)`, or stops at a state satisfying `Inv m`. -/
theorem forIn_list_inv {α β : Type} (L : List α) (body : α → β → M (ForInStep β))
    (Inv : Nat → β → Prop)
    (hstep : ∀ m a b r, L[m]? = some a → Inv m b → body a b = .ok r →
      (∀ b', r = .yield b' → Inv (m + 1) b') ∧ (∀ b', r = .done b' → Inv m b')) :
    ∀ (l : List α) (m : Nat) (b out : β), L.drop m = l → Inv m b → forIn l b body = .ok out →
      ∃ m', Inv m' out
  | [], m, b, out, _, hI, h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨m, hI⟩
  | a :: l, m, b, out, hL, hI, h => by
    have ha : L[m]? = some a := by
      rw [← List.head?_drop, hL]; rfl
    have hL' : L.drop (m + 1) = l := by
      rw [← List.drop_drop, hL]; rfl
    rw [List.forIn_cons] at h
    simp only [bind, Except.bind] at h
    cases hr : body a b with
    | error e => rw [hr] at h; cases h
    | ok r =>
      rw [hr] at h
      obtain ⟨hy, hd⟩ := hstep m a b r ha hI hr
      cases r with
      | done b' =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; exact ⟨m, hd _ rfl⟩
      | yield b' =>
        exact forIn_list_inv L body Inv hstep l (m + 1) b' out hL' (hy _ rfl) h

theorem getBuilderWithdrawals_provenance {st : Gloas.BeaconState P} {idx : U64}
    {prior ws : Array Withdrawal} {idx' n : U64}
    (h : Gloas.getBuilderWithdrawals st idx prior = .ok (ws, idx', n)) :
    n.toNat = ws.size ∧ ∀ k (hk : k < ws.size), ∃ e,
      st.builder_pending_withdrawals.toArray[k]? = some e ∧ ws[k].address = e.fee_recipient ∧
      ws[k].amount = e.amount ∧
      Gloas.convertBuilderIndexToValidatorIndex e.builder_index = .ok ws[k].validator_index := by
  unfold Gloas.getBuilderWithdrawals at h
  simp only [require, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i out hfor
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rw [← Array.forIn_toList] at hfor
  let L := st.builder_pending_withdrawals.toArray.toList
  let Inv : Nat → U64 × Array Withdrawal × U64 → Prop := fun m x =>
    x.1.toNat = m ∧ x.2.1.size = m ∧ ∀ k (hk : k < x.2.1.size), ∃ e,
      L[k]? = some e ∧ x.2.1[k].address = e.fee_recipient ∧ x.2.1[k].amount = e.amount ∧
      Gloas.convertBuilderIndexToValidatorIndex e.builder_index = .ok x.2.1[k].validator_index
  obtain ⟨m, hm1, hm2, hm3⟩ := forIn_list_inv L _ Inv (by
      intro m a ⟨p, wsA, i⟩ r ha hI hr
      obtain ⟨hp, hsz, hold⟩ := hI
      simp only at hp hsz hold
      simp only at hr
      split at hr
      · simp only [Except.ok.injEq] at hr
        subst hr
        exact ⟨fun b' h => (by cases h), fun b' h => (by cases h; exact ⟨hp, hsz, hold⟩)⟩
      · split at hr
        · cases hr
        rename_i v hv
        split at hr
        · cases hr
        rename_i v1 hv1
        split at hr
        · cases hr
        rename_i v2 hv2
        simp only [Except.ok.injEq] at hr
        subst hr
        refine ⟨fun b' h => ?_, fun b' h => (by cases h)⟩
        cases h
        refine ⟨by rw [U64.toNat_add? hv2, ← hp]; rfl, by simp [hsz], fun k hk => ?_⟩
        simp only [Array.size_push] at hk
        by_cases hkm : k < wsA.size
        · obtain ⟨e, he, h1, h2, h3⟩ := hold k hkm
          refine ⟨e, he, ?_, ?_, ?_⟩ <;> simp [Array.getElem_push_lt hkm, h1, h2, h3]
        · have hk' : k = wsA.size := by omega
          subst hk'
          refine ⟨a, by rw [hsz]; exact ha, ?_, ?_, ?_⟩ <;> simp [hv]) L 0 _ out (by simp)
    ⟨rfl, rfl, fun k hk => absurd hk (by simp)⟩ hfor
  refine ⟨hm1.trans hm2.symm, fun k hk => ?_⟩
  obtain ⟨e, he, h1, h2, h3⟩ := hm3 k hk
  exact ⟨e, by simpa [L] using he, h1, h2, h3⟩

theorem ProgressiveListS_get_ok {s : Spine} {α : Type} {xs : ProgressiveListS s α} {i : Nat}
    {site : String} {x : α} (h : xs.get i site = .ok x) : xs.toArray[i]? = some x := by
  unfold ProgressiveListS.get getAt at h
  split at h
  · rename_i y hy; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hy
  · cases h

/-- **B5(ii), sweep half, at function level.** Each withdrawal of the builders sweep pays a
builder at a converted index, to that builder's own `execution_address`, only when its
`withdrawable_epoch` has passed, and its amount is the builder's balance after the prior
withdrawals (the phases before it and the sweep's own earlier entries), which is positive
(CL:1909-1946). -/
theorem getBuildersSweepWithdrawals_provenance {st : Gloas.BeaconState P} {idx : U64}
    {prior ws : Array Withdrawal} {idx' n : U64}
    (h : Gloas.getBuildersSweepWithdrawals st idx prior = .ok (ws, idx', n)) :
    ∀ k (hk : k < ws.size), ∃ (bi : Gloas.BuilderIndex) (b : Gloas.Builder) (e : Epoch),
      Gloas.getCurrentEpoch st = .ok e ∧
      Gloas.convertBuilderIndexToValidatorIndex bi = .ok ws[k].validator_index ∧
      st.builders.toArray[bi.toNat]? = some b ∧ b.withdrawable_epoch ≤ e ∧
      ws[k].address = b.execution_address ∧
      Gloas.getBuilderBalanceAfterWithdrawals st bi (prior ++ ws.extract 0 k) = .ok ws[k].amount ∧
      U64.zero < ws[k].amount := by
  unfold Gloas.getBuildersSweepWithdrawals at h
  simp only [require, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i e he
  split at h
  · cases h
  split at h
  · cases h
  rename_i out hfor
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hfor
  let Inv : Nat → U64 × Array Withdrawal × U64 × U64 → Prop := fun _ x =>
    ∀ k (hk : k < x.2.1.size), ∃ (bi : Gloas.BuilderIndex) (b : Gloas.Builder),
      Gloas.convertBuilderIndexToValidatorIndex bi = .ok x.2.1[k].validator_index ∧
      st.builders.toArray[bi.toNat]? = some b ∧ b.withdrawable_epoch ≤ e ∧
      x.2.1[k].address = b.execution_address ∧
      Gloas.getBuilderBalanceAfterWithdrawals st bi (prior ++ x.2.1.extract 0 k) =
        .ok x.2.1[k].amount ∧
      U64.zero < x.2.1[k].amount
  obtain ⟨m, hm⟩ := forIn_list_inv _ _ Inv (by
      intro m a ⟨p, wsA, i, bi⟩ r _ hI hr
      simp only [Inv] at hI ⊢
      split at hr
      · simp only [Except.ok.injEq] at hr
        subst hr
        exact ⟨fun b' h => (by cases h), fun b' h => (by cases h; exact hI)⟩
      split at hr
      · cases hr
      rename_i b hb
      split at hr
      · cases hr
      rename_i bal hbal
      split at hr
      · rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        split at hr
        · cases hr
        rename_i v hv
        repeat (split at hr; · cases hr)
        simp only [Except.ok.injEq] at hr
        subst hr
        refine ⟨fun b' h => ?_, fun b' h => (by cases h)⟩
        cases h
        intro k hk
        simp only [Array.size_push] at hk
        by_cases hkm : k < wsA.size
        · obtain ⟨bi', b'', h1, h2, h3, h4, h5, h6⟩ := hI k hkm
          have hext : ∀ w : Withdrawal, (wsA.push w).extract 0 k = wsA.extract 0 k := by
            intro w; apply Array.ext'; simp [Nat.le_of_lt hkm]
          refine ⟨bi', b'', ?_, h2, h3, ?_, ?_, ?_⟩ <;>
            simp_all [Array.getElem_push_lt hkm]
        · have hk' : k = wsA.size := by omega
          subst hk'
          refine ⟨bi, b, ?_, ProgressiveListS_get_ok hb, hcond.1, ?_, ?_, ?_⟩
          · simpa using hv
          · simp
          · simp; exact hbal
          · simpa using hcond.2
      · repeat (split at hr; · cases hr)
        simp only [Except.ok.injEq] at hr
        subst hr
        exact ⟨fun b' h => (by cases h; exact hI), fun b' h => (by cases h)⟩)
    _ 0 _ out rfl (fun k hk => absurd hk (by simp)) hfor
  intro k hk
  obtain ⟨bi, b, h1, h2, h3, h4, h5, h6⟩ := hm k hk
  exact ⟨bi, b, e, he, h1, h2, h3, h4, h5, h6⟩

end JauneConsensus.Facts.Gloas
