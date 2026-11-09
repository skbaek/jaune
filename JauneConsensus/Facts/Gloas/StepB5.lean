import JauneConsensus.Facts.Gloas.StepB246
import JauneConsensus.Facts.Gloas.InvariantsCoverBlock

/-!
# The per-step consensus layer of B5 (goal `eip8282-gloas-cross-layer-v1`, RBS)

B5(i), the builder balance equation over ONE Gloas joint step, in `ℕ` with no saturation.
BF1's function-level `applyWithdrawals_builder_balance` is lifted through `process_withdrawals`
and Gloas `process_block` to the step (`GStepView`, `StepB246.lean`):

* `withdrawnAmount_toNat`: the spec's `withdrawn` sum is the routed sum;
* `sweep_routed_le`: the builders sweep never routes more to a builder than its balance less what
  the earlier phases routed to it (each sweep entry is `saturating_sub(balance, withdrawn)` and is
  positive);
* `expected_routed_le`: under `PendLe`, G3-03 and the two G3-12 bounds, the expected withdrawals
  route to a builder at most its balance (the G3-05-shaped hypothesis of BF1);
* `depositLoop_balance`, `exitLoop_balance`: the builder request loops credit a builder exactly its
  top-ups (`creditedAt`), as long as no request registers a fresh record at its index
  (`NoRegisterAt`, the "same incarnation" condition), and exits never move a balance;
* `stepWithdrawals`: the withdrawals the step's `process_withdrawals` applies (`[]` when it
  returns early on an EMPTY parent);
* **`GStepView.builder_balance_equation`** (B5(i) per step): `b'.balance + routed = b.balance +
  credited` between the step's pre-state and post-state, and each routed withdrawal fits the
  running balance.
-/

namespace JauneConsensus.Facts.Gloas

open Jaune JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas.Inv

variable {P : Preset}

/-! ## Withdrawn amounts and the builders sweep -/

theorem routes_iff_of_convert {bi vi : U64}
    (hv : Gloas.convertBuilderIndexToValidatorIndex bi = .ok vi) (w : Withdrawal) :
    Routes bi w ↔ w.validator_index = vi := by
  rw [Routes, hv]
  exact ⟨fun h => (Except.ok.inj h).symm, fun h => by rw [h]⟩

theorem routedSum_single (bi : U64) (w : Withdrawal) :
    routedSum bi [w] = if Routes bi w then w.amount.toNat else 0 := by
  unfold routedSum
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp_all

theorem routedSum_cons (bi : U64) (w : Withdrawal) (l : List Withdrawal) :
    routedSum bi (w :: l) = (if Routes bi w then w.amount.toNat else 0) + routedSum bi l := by
  have := routedSum_append bi [w] l
  simp only [List.singleton_append] at this
  rw [this]
  rw [routedSum_single]

theorem withdrawnAmount_foldl {bi vi : U64}
    (hv : Gloas.convertBuilderIndexToValidatorIndex bi = .ok vi) :
    ∀ (l : List Withdrawal) (acc x : U64),
      l.foldlM (fun acc w => if w.validator_index == vi then acc.add? w.amount "withdrawn"
        else pure acc) acc = .ok x →
      x.toNat = acc.toNat + routedSum bi l
  | [], acc, x, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [routedSum]
  | w :: l, acc, x, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨a, ha, h⟩ := bind_eq_ok_iff.mp h
    have ih := withdrawnAmount_foldl hv l a x h
    rw [routedSum_cons, ih]
    by_cases hw : w.validator_index = vi
    · have hr : Routes bi w := (routes_iff_of_convert hv w).mpr hw
      simp only [hw, beq_self_eq_true, ite_true] at ha
      rw [U64.toNat_add? ha, if_pos hr]; omega
    · have hr : ¬ Routes bi w := fun h => hw ((routes_iff_of_convert hv w).mp h)
      have hb : (w.validator_index == vi) = false := by simpa using hw
      simp only [hb, Bool.false_eq_true, ite_false, pure, Except.pure, Except.ok.injEq] at ha
      subst ha
      rw [if_neg hr]; omega

/-- `sum(w.amount for w in withdrawals if w.validator_index == index)` is the routed sum. -/
theorem withdrawnAmount_toNat {bi vi x : U64} {ws : Array Withdrawal}
    (hv : Gloas.convertBuilderIndexToValidatorIndex bi = .ok vi)
    (h : Gloas.withdrawnAmount ws vi = .ok x) : x.toNat = routedSum bi ws.toList := by
  unfold Gloas.withdrawnAmount at h
  rw [← Array.foldlM_toList] at h
  have := withdrawnAmount_foldl hv ws.toList U64.zero x h
  have h0 : U64.zero.toNat = 0 := rfl
  omega

/-- A positive `saturating_sub(a, d)` is the exact difference. -/
theorem saturatingSubGwei_pos {a d x : U64} (h : Gloas.saturatingSubGwei a d = .ok x)
    (hx : U64.zero < x) : x.toNat + d.toNat = a.toNat := by
  unfold Gloas.saturatingSubGwei at h
  split at h
  · rename_i hlt
    have : d.toNat < a.toNat := hlt
    rw [U64.toNat_sub? h]; omega
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact absurd hx (by decide)

/-- **The builders sweep fits the balance.** If the earlier phases route at most `b.balance` to
builder `bi`, so do they together with the sweep: a sweep entry for `bi` is
`saturating_sub(balance, withdrawn so far)` and is positive, so it takes exactly the rest. -/
theorem sweep_routed_le {st : Gloas.BeaconState P} {idx : U64} {prior sw : Array Withdrawal}
    {idx' n : U64} (h : Gloas.getBuildersSweepWithdrawals st idx prior = .ok (sw, idx', n))
    (hbb : st.builders.toArray.size ≤ 2 ^ 40) {bi : U64} {b : Gloas.Builder}
    (hb : st.builders.toArray[bi.toNat]? = some b)
    (hprior : routedSum bi prior.toList ≤ b.balance.toNat) :
    routedSum bi (prior.toList ++ sw.toList) ≤ b.balance.toNat := by
  have hbi : bi.toNat < 2 ^ 40 := lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hb).1 hbb
  have prov := getBuildersSweepWithdrawals_provenance h
  suffices H : ∀ k, k ≤ sw.size → routedSum bi (prior.toList ++ sw.toList.take k) ≤ b.balance.toNat by
    have := H sw.size le_rfl
    rwa [show sw.toList.take sw.size = sw.toList by simp] at this
  intro k
  induction k with
  | zero => intro _; simpa using hprior
  | succ k ih =>
    intro hk
    have hk' : k < sw.size := by omega
    have ih := ih (by omega)
    have htake : sw.toList.take (k + 1) = sw.toList.take k ++ [sw[k]] := by
      rw [List.take_add_one]; simp [hk']
    rw [htake, ← List.append_assoc, routedSum_append]
    by_cases hr : Routes bi sw[k]
    · obtain ⟨bj, b', e, -, hcv, hb', -, -, hbal, hpos⟩ := prov k hk'
      have hbj : bj.toNat < 2 ^ 40 := lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hb').1 hbb
      have hij := routes_inj hr hcv hbi hbj
      have hbj' : bj = bi := U64.ext_toNat hij.symm
      rw [hbj'] at hb' hbal
      rw [hb] at hb'; cases hb'
      unfold Gloas.getBuilderBalanceAfterWithdrawals at hbal
      obtain ⟨vi, hvi, hbal⟩ := bind_eq_ok_iff.mp hbal
      obtain ⟨wd, hwd, hbal⟩ := bind_eq_ok_iff.mp hbal
      obtain ⟨b'', hg, hbal⟩ := bind_eq_ok_iff.mp hbal
      rw [ProgressiveListS_get_ok hg] at hb
      cases hb
      have hwdN := withdrawnAmount_toNat hvi hwd
      have hex := saturatingSubGwei_pos hbal hpos
      have hl : (prior ++ sw.extract 0 k).toList = prior.toList ++ sw.toList.take k := by
        simp [Array.toList_extract]
      rw [hl] at hwdN
      have : routedSum bi [sw[k]] = sw[k].amount.toNat := by rw [routedSum_single, if_pos hr]
      rw [this]; omega
    · have : routedSum bi [sw[k]] = 0 := by rw [routedSum_single, if_neg hr]
      rw [this]; omega

/-- **The expected withdrawals fit each builder's balance** (BF1's G3-05-shaped hypothesis, at the
state `process_withdrawals` reads): under `PendLe`, G3-03 and the two G3-12 bounds. The builder
withdrawals route the processed prefix of the builder's pending withdrawals (at most `pend`, at
most the balance); the validator phases route nothing; the sweep takes at most the rest. -/
theorem expected_routed_le {s : Gloas.BeaconState P} {ex : Gloas.ExpectedWithdrawals}
    (h : Gloas.getExpectedWithdrawals s = .ok ex) (hle : PendLe s) (hr : PendingRefsInRange s)
    (validatorsBound : s.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : s.builders.toArray.size ≤ 2 ^ 40) {bi : U64} {b : Gloas.Builder}
    (hb : s.builders.toArray[bi.toNat]? = some b) :
    routedSum bi ex.withdrawals.toList ≤ b.balance.toNat := by
  have hbi : bi.toNat < 2 ^ 40 := lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hb).1 buildersBound
  unfold Gloas.getExpectedWithdrawals at h
  obtain ⟨⟨bw, i1, n1⟩, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨⟨pw, i2, n2⟩, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨⟨sw, i3, n3⟩, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨⟨vw, i4, n4⟩, h4, h⟩ := bind_eq_ok_iff.mp h
  cases h
  have hr40 : ∀ w ∈ s.builder_pending_withdrawals.toArray.toList, w.builder_index.toNat < 2 ^ 40 :=
    fun w hw => Nat.lt_of_lt_of_le (hr.1 w hw) buildersBound
  obtain ⟨-, rb⟩ := routed_builderWithdrawals h1 hr40 hbi
  have rp := routedSum_validatorPhase (getPendingPartialWithdrawals_inRange _ _ _ _ h2)
    validatorsBound bi
  have rv := routedSum_validatorPhase (getValidatorsSweepWithdrawals_inRange _ _ _ _ h4)
    validatorsBound bi
  have hpend : pendW (s.builder_pending_withdrawals.toArray.toList.take bw.size) bi.toNat ≤
      b.balance.toNat := by
    have h1 := pendW_take_drop s.builder_pending_withdrawals.toArray.toList bw.size bi.toNat
    have h2 := hle bi.toNat b hb
    unfold pend at h2
    omega
  have hprior : routedSum bi (#[] ++ bw ++ pw).toList ≤ b.balance.toNat := by
    simp only [Array.toList_append, routedSum_append]
    rw [rb, rp]; simp [routedSum]; omega
  have hs := sweep_routed_le h3 buildersBound hb hprior
  simp only [Array.toList_append, routedSum_append] at hs ⊢
  rw [rv]
  omega

/-! ## The builder request loops -/

theorem scanM_cons_ok {σ α : Type} {f : σ → α → M σ} {s : σ} {a : α} {as : List α}
    {tr : List σ} (h : scanM f s (a :: as) = .ok tr) :
    ∃ s' rest, f s a = .ok s' ∧ scanM f s' as = .ok rest ∧ tr = s :: rest := by
  change (do let s' ← f s a; let rest ← scanM f s' as; pure (s :: rest) : M (List σ)) = _ at h
  obtain ⟨s', h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨rest, h2, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact ⟨s', rest, h1, h2, rfl⟩

theorem traceLast_scan_cons {σ α : Type} {f : σ → α → M σ} {s s' : σ} {as : List α}
    {rest : List σ} (h : scanM f s' as = .ok rest) : traceLast s (s :: rest) = traceLast s' rest := by
  have hh := scanM_ok_head h
  cases rest with
  | nil => simp at hh
  | cons x xs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hh
    subst hh
    simp [traceLast, List.getLast?_cons]

/-- What one builder deposit outcome credits to builder `i`: a top-up of `i`'s amount. -/
def depositCredit (i : Nat) : BuilderDepositOutcome → Nat
  | .topUp j a _ => if j = i then a.toNat else 0
  | _ => 0

/-- The deposits credited to builder `i` along a deposit trace `tr` of the requests `rs`
(statements.md's `creditedDepositsAt`): the top-up amounts of the requests whose outcome at
their mid-list state is a top-up of `i`. -/
def creditedAt (ccfg : Config) (bls : Bool) (i : Nat) :
    List (Gloas.BeaconState P) → List Gloas.BuilderDepositRequest → Nat
  | m :: tr, r :: rs =>
    (match classifyBuilderDeposit ccfg bls m r with
      | .ok o => depositCredit i o
      | .error _ => 0) + creditedAt ccfg bls i tr rs
  | _, _ => 0

/-- No request of the deposit trace registers a fresh record at index `i` (the builder at `i`
keeps its incarnation through the loop). -/
def NoRegisterAt (ccfg : Config) (bls : Bool) (i : Nat) :
    List (Gloas.BeaconState P) → List Gloas.BuilderDepositRequest → Prop
  | m :: tr, r :: rs =>
    (∀ a, classifyBuilderDeposit ccfg bls m r ≠ .ok (.register i a)) ∧ NoRegisterAt ccfg bls i tr rs
  | _, _ => True

/-- **The builder-deposit loop credits builder `i` exactly its top-ups**, keeping its identity,
as long as no request registers a fresh record at `i`. -/
theorem depositLoop_balance {ccfg : Config} {bls : Bool} {i : Nat} :
    ∀ (rs : List Gloas.BuilderDepositRequest) (s : Gloas.BeaconState P) (tr : List (Gloas.BeaconState P))
      (b : Gloas.Builder),
      scanM (Gloas.processBuilderDepositRequest { cfg := ccfg, blsActive := bls }) s rs = .ok tr →
      s.builders.toArray[i]? = some b → NoRegisterAt ccfg bls i tr rs →
      ∃ b', (traceLast s tr).builders.toArray[i]? = some b' ∧ SameIdentity b b' ∧
        b'.balance.toNat = b.balance.toNat + creditedAt ccfg bls i tr rs
  | [], s, tr, b, h, hb, _ => by
    simp only [scanM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨b, hb, SameIdentity.refl b, by simp [creditedAt]⟩
  | r :: rs, s, tr, b, h, hb, hno => by
    obtain ⟨s', rest, h1, h2, rfl⟩ := scanM_cons_ok h
    have h1' := h1
    rw [processBuilderDepositRequest_eq] at h1'
    obtain ⟨o, hc, -⟩ := bind_eq_ok_iff.mp h1'
    obtain ⟨hpre, hbad, htop, hreg⟩ := classifyBuilderDeposit_effect (ctx := { cfg := ccfg, blsActive := bls }) hc h1
    simp only [NoRegisterAt] at hno
    obtain ⟨hno1, hno2⟩ := hno
    -- the builder at `i` after this request, and what it was credited
    obtain ⟨b1, hb1, hid1, hbal1⟩ : ∃ b1, s'.builders.toArray[i]? = some b1 ∧ SameIdentity b b1 ∧
        b1.balance.toNat = b.balance.toNat + depositCredit i o := by
      cases o with
      | ignoredPrefix => rw [hpre rfl]; exact ⟨b, hb, SameIdentity.refl b, by simp [depositCredit]⟩
      | ignoredBadSignature => rw [hbad rfl]; exact ⟨b, hb, SameIdentity.refl b, by simp [depositCredit]⟩
      | topUp j a reset =>
        obtain ⟨c, c', hc0, hc', -, hoth, hpk, hv, hadr, -, hbal, -⟩ := htop j a reset rfl
        by_cases hji : j = i
        · subst hji
          rw [hb] at hc0; cases hc0
          exact ⟨c', hc', ⟨hpk, hv, hadr⟩, by simp [depositCredit, hbal]⟩
        · exact ⟨b, by rw [hoth i (Ne.symm hji)]; exact hb, SameIdentity.refl b,
            by simp [depositCredit, hji]⟩
      | register j a =>
        obtain ⟨-, -, -, -, -, -, hoth, -⟩ := hreg j a rfl
        have hji : j ≠ i := fun hji => hno1 a (by rw [hc, hji])
        exact ⟨b, by rw [hoth i (Ne.symm hji)]; exact hb, SameIdentity.refl b,
          by simp [depositCredit]⟩
    obtain ⟨b', hb', hid', hbal'⟩ := depositLoop_balance rs s' rest b1 h2 hb1 hno2
    refine ⟨b', by rw [traceLast_scan_cons h2]; exact hb', SameIdentity.trans hid1 hid', ?_⟩
    simp only [creditedAt, hc]
    omega

/-- **The builder-exit loop moves no balance and keeps every identity.** -/
theorem exitLoop_balance {ccfg : Config} {i : Nat} :
    ∀ (rs : List Gloas.BuilderExitRequest) (s : Gloas.BeaconState P) (tr : List (Gloas.BeaconState P))
      (b : Gloas.Builder),
      scanM (Gloas.processBuilderExitRequest ccfg) s rs = .ok tr →
      s.builders.toArray[i]? = some b →
      ∃ b', (traceLast s tr).builders.toArray[i]? = some b' ∧ SameIdentity b b' ∧
        b'.balance = b.balance
  | [], s, tr, b, h, hb => by
    simp only [scanM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨b, hb, SameIdentity.refl b, rfl⟩
  | r :: rs, s, tr, b, h, hb => by
    obtain ⟨s', rest, h1, h2, rfl⟩ := scanM_cons_ok h
    obtain ⟨b1, hb1, hid1, hbal1⟩ : ∃ b1, s'.builders.toArray[i]? = some b1 ∧ SameIdentity b b1 ∧
        b1.balance = b.balance := by
      rcases (exitReq_cases h1).2 with rfl | ⟨j, c, w, hc, hc', -, -, -, -, hoth⟩
      · exact ⟨b, hb, SameIdentity.refl b, rfl⟩
      · by_cases hji : j = i
        · subst hji
          rw [hb] at hc; cases hc
          exact ⟨_, hc', ⟨rfl, rfl, rfl⟩, rfl⟩
        · exact ⟨b, by rw [hoth i (Ne.symm hji)]; exact hb, SameIdentity.refl b, rfl⟩
    obtain ⟨b', hb', hid', hbal'⟩ := exitLoop_balance rs s' rest b1 h2 hb1
    exact ⟨b', by rw [traceLast_scan_cons h2]; exact hb', SameIdentity.trans hid1 hid',
      hbal'.trans hbal1⟩

theorem traceLast_irrel {σ : Type} {tr : List σ} (h : tr ≠ []) (d d' : σ) :
    traceLast d tr = traceLast d' tr := by
  cases tr with
  | nil => exact absurd rfl h
  | cons x xs => exact traceLast_cons d d' x xs

/-- **The parent settlement credits builder `i` exactly its top-ups** (read along the deposit
trace at the state `process_block` receives), keeping its identity, as long as no request
registers a fresh record at `i`. An EMPTY parent changes nothing. -/
theorem parent_balance {ccfg : Config} {bls : Bool} {st s1 : Gloas.BeaconState P}
    {blk : Gloas.SignedBeaconBlock P}
    (h : Gloas.processParentExecutionPayload (gloasCtx ccfg bls) st blk.message = .ok s1)
    {trD : List (Gloas.BeaconState P)} (hD : builderDepositTrace ccfg bls st blk = .ok trD)
    {i : Nat} {b : Gloas.Builder} (hb : st.builders.toArray[i]? = some b)
    (hno : NoRegisterAt ccfg bls i trD (blockBuilderDeposits blk)) :
    ∃ b1, s1.builders.toArray[i]? = some b1 ∧ SameIdentity b b1 ∧
      b1.balance.toNat = b.balance.toNat + creditedAt ccfg bls i trD (blockBuilderDeposits blk) := by
  obtain ⟨trD', trE, hd, he, -, hEmpty, hFull⟩ := processParentExecutionPayload_traces (b := blk) h
  change builderDepositTrace ccfg bls st blk = .ok trD' at hd
  rw [hD] at hd; cases hd
  have hlen := builderDepositTrace_length hD
  cases hbne : (blk.message.body.signed_execution_payload_bid.message.parent_block_hash !=
      st.latest_execution_payload_bid.block_hash)
  · have hs1 := hFull hbne
    -- a start state of the deposit scan with the same builders
    obtain ⟨s0, hs0b, hscan⟩ : ∃ s0 : Gloas.BeaconState P, s0.builders = st.builders ∧
        scanM (Gloas.processBuilderDepositRequest { cfg := ccfg, blsActive := bls }) s0
          (blockBuilderDeposits blk) = .ok trD := by
      rcases builderDepositTrace_ok hD with ⟨hdn, -, rfl⟩ | ⟨s0, h0, hs⟩
      · exact ⟨st, rfl, by rw [hdn]; rfl⟩
      · exact ⟨s0, (applyParentPrefix_core _ _ _ _ h0).1, hs⟩
    obtain ⟨b0, hb0, hid0, hbal0⟩ := depositLoop_balance _ s0 trD b hscan (by rw [hs0b]; exact hb)
      hno
    have hne : trD ≠ [] := scanM_ok_ne_nil hscan
    rw [traceLast_irrel hne s0 st] at hb0
    obtain ⟨trD'', hd'', hsE, -⟩ := builderExitTrace_ok he
    change builderDepositTrace ccfg bls st blk = .ok trD'' at hd''
    rw [hD] at hd''; cases hd''
    obtain ⟨b2, hb2, hid2, hbal2⟩ := exitLoop_balance _ _ trE b0 hsE hb0
    have hneE : trE ≠ [] := scanM_ok_ne_nil hsE
    rw [traceLast_irrel hneE _ st] at hb2
    refine ⟨b2, by rw [(applyParentSuffix_post hs1).1]; exact hb2, SameIdentity.trans hid0 hid2, ?_⟩
    rw [hbal2]; exact hbal0
  · obtain ⟨rfl, rfl, -⟩ := hEmpty hbne
    have hnil : blockBuilderDeposits blk = [] := by
      simp only [List.length_singleton] at hlen; exact List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil]
    exact ⟨b, hb, SameIdentity.refl b, by simp [creditedAt]⟩

/-! ## `process_withdrawals` and the step's withdrawals -/

/-- `process_withdrawals` past its early return applies the expected withdrawals. -/
theorem processWithdrawals_full {s s' : Gloas.BeaconState P}
    (hc : (s.latest_block_hash != s.latest_execution_payload_bid.block_hash) = false)
    (h : Gloas.processWithdrawals s = .ok s') :
    ∃ ex t, Gloas.getExpectedWithdrawals s = .ok ex ∧ Gloas.applyWithdrawals s ex.withdrawals = .ok t ∧
      s'.builders = t.builders := by
  unfold Gloas.processWithdrawals at h
  simp only [hc, Bool.false_eq_true, ite_false] at h
  obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t6, h6, h⟩ := bind_eq_ok_iff.mp h
  have q2 := updateNextWithdrawalIndex_bq _ _ _ h2
  have q6 := updateNextWithdrawalBuilderIndex_bq _ _ _ h6
  have q7 := updateNextWithdrawalValidatorIndex_bq _ _ _ h
  exact ⟨ex, t1, hex, h1, q7.1.trans (q6.1.trans q2.1)⟩

/-- The withdrawals the step's `process_withdrawals` applies, read from the post-slots state `st`
and the block (statements.md's `expectedWithdrawals`): `[]` when it returns early on an EMPTY
parent (`latest_block_hash != L.block_hash` after the parent settlement and the header), else
`get_expected_withdrawals` at the state it reads. -/
def stepWithdrawals (ccfg : Config) (bls : Bool) (st : Gloas.BeaconState P)
    (blk : Gloas.BeaconBlock P) : M (List Withdrawal) := do
  let s1 ← Gloas.processParentExecutionPayload (gloasCtx ccfg bls) st blk
  let s2 ← Gloas.processBlockHeader s1 blk
  if s2.latest_block_hash != s2.latest_execution_payload_bid.block_hash then
    pure []
  else
    let ex ← Gloas.getExpectedWithdrawals s2
    pure ex.withdrawals.toList

/-! ## B5(i) per step -/

section Balance

variable {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
  {preB : Gloas.BeaconState P} {preExec : BlockChain} {preParent : ParentPayload P}
  {b : Gloas.SignedBeaconBlock P} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
  {postB : Gloas.BeaconState P} {postExec : BlockChain} {postParent : ParentPayload P}

/-- **B5(i) per step: the builder balance equation over a whole Gloas joint step**, in `ℕ`, with
no saturation. For builder `bi` of the step's pre-state, at the same incarnation (no request of
the step registers a fresh record at `bi`, `NoRegisterAt` along the deposit trace read at the
post-slots state):

`b'.balance + routedSum bi ws = b.balance + creditedAt … bi trD deposits`,

where `ws` is what the step's `process_withdrawals` applies (`stepWithdrawals`; `[]` on an EMPTY
parent), `routedSum bi ws` the amounts routed to `bi`
(`convert_builder_index_to_validator_index(bi) == w.validator_index`), and `creditedAt` the
top-ups of `bi` in the parent payload's builder deposits; `b'` is `bi`'s record in the post-state,
with the same identity. Each routed withdrawal fits the running balance (no debit saturates).

Hypotheses: the G3 invariants at the step's pre-state under their names (G3-05 `PendingCovered`,
G3-03 `PendingRefsInRange`, G3-04 `ExitedHaveNoPending`, G3-07 `NoLiveWeightOnLatestBid`, G3-08
`LatestBidCoherence`, and the auxiliary `FutureEmpty`, `LatestBidBuilderActive`), the two N7
(G3-12) bounds at the post-state as G3-05's block step takes them, and the config bounds
`quorumPositive`, `slotsPerEpoch`. -/
theorem GStepView.builder_balance_equation
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH)
    (g5 : PendingCovered preB) (g3 : PendingRefsInRange preB) (g4 : ExitedHaveNoPending preB)
    (g7 : NoLiveWeightOnLatestBid preB) (g8 : LatestBidCoherence preB) (fe : FutureEmpty preB)
    (hA : LatestBidBuilderActive preB)
    (validatorsBound : postB.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : postB.builders.toArray.size ≤ 2 ^ 40)
    {bi : Gloas.BuilderIndex} {bb : Gloas.Builder} (hb : preB.builders.toArray[bi.toNat]? = some bb)
    {trD : List (Gloas.BeaconState P)} (hD : builderDepositTrace ccfg bls V.postSlots b = .ok trD)
    (hno : NoRegisterAt ccfg bls bi.toNat trD (blockBuilderDeposits b)) :
    ∃ (ws : List Withdrawal) (bb' : Gloas.Builder),
      stepWithdrawals ccfg bls V.postSlots b.message = .ok ws ∧
      postB.builders.toArray[bi.toNat]? = some bb' ∧ SameIdentity bb bb' ∧
      bb'.balance.toNat + routedSum bi ws =
        bb.balance.toNat + creditedAt ccfg bls bi.toNat trD (blockBuilderDeposits b) ∧
      (∀ k w, ws[k]? = some w → Routes bi w →
        routedSum bi (ws.take k) + w.amount.toNat ≤
          bb.balance.toNat + creditedAt ccfg bls bi.toNat trD (blockBuilderDeposits b)) := by
  -- the slots: invariants carried, registry unchanged
  have hs := processSlots_pendingCovered quorumPositive (by omega) V.slots ⟨g5, g7, fe⟩
  have g3' := processSlots_pendingRefsInRange quorumPositive V.slots g3
  have g4' := processSlots_exitedHaveNoPending quorumPositive V.slots g4
  have g8' := processSlots_latestBidCoherence V.slots g8
  have hA' := processSlots_latestBidBuilderActive V.slots hA
  have hbS : V.postSlots.builders.toArray[bi.toNat]? = some bb := by
    rw [processSlots_identityStable V.slots]; exact hb
  -- the block, phase by phase
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    processBlock_phases V.processBlock
  obtain ⟨l1, r1, -⟩ := parent_I3 slotsPerEpoch hA' h1 hs.1 g3' g4' g8'
  obtain ⟨b1, hb1, hid1, hbal1⟩ := parent_balance h1 hD hbS hno
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have e2b : s2.builders = s1.builders := by rw [hm2]
  have e2w : s2.builder_pending_withdrawals = s1.builder_pending_withdrawals := by rw [hm2]
  have e2p : s2.builder_pending_payments = s1.builder_pending_payments := by rw [hm2]
  have w3 := processWithdrawals_wFrame _ _ h3
  have b4 := processExecutionPayloadBid_post h4
  have c := afterBid_core h5 h6 h7 h8
  have hpost : postB.builders = s3.builders := by rw [c.1, b4.2.2.2.2.1]
  have hb2 : s2.builders.toArray[bi.toNat]? = some b1 := by rw [e2b]; exact hb1
  have hsw : stepWithdrawals ccfg bls V.postSlots b.message =
      (if s2.latest_block_hash != s2.latest_execution_payload_bid.block_hash then pure []
        else do let ex ← Gloas.getExpectedWithdrawals s2; pure ex.withdrawals.toList) := by
    simp only [stepWithdrawals, h1, h2, bind, Except.bind]
  cases hc : (s2.latest_block_hash != s2.latest_execution_payload_bid.block_hash)
  · -- past the early return
    obtain ⟨ex, t, hex, ht, hs3⟩ := processWithdrawals_full hc h3
    have vb3 : postB.validators.toArray.size = s3.validators.toArray.size :=
      afterWithdrawals_vlen h4 h5 h6 h7 h8
    have vb2 : s3.validators.toArray.size = s2.validators.toArray.size :=
      processWithdrawals_vlen _ _ h3
    have bb2 : postB.builders.toArray.size = s2.builders.toArray.size := by
      rw [hpost]; exact w3.2.2.2.2.2.1
    have g305 := expected_routed_le hex (pendLe_of_eqs e2b e2w e2p l1) (refs_of_eqs e2b e2w e2p r1)
      (by omega) (by omega) hb2
    obtain ⟨b3, hb3, hb3e, hbal3⟩ := applyWithdrawals_builder_balance ht (by
      show s2.builders.toArray.size ≤ 2 ^ 40; omega) hb2 g305
    refine ⟨ex.withdrawals.toList, b3, by rw [hsw, hc]; simp [hex, bind, Except.bind, pure,
      Except.pure], by rw [hpost, hs3]; exact hb3, ?_, by omega, ?_⟩
    · rw [hb3e]; exact SameIdentity.trans hid1 ⟨rfl, rfl, rfl⟩
    · intro k w hw hr
      have := routed_le_runningBalance g305 hw hr
      omega
  · -- the early return: nothing is withdrawn
    have hne : s2.latest_block_hash ≠ s2.latest_execution_payload_bid.block_hash := by
      simpa using hc
    rw [processWithdrawalsG_early_return s2 hne] at h3
    cases h3
    refine ⟨[], b1, by rw [hsw, hc]; rfl, by rw [hpost, e2b]; exact hb1, hid1, by simp [routedSum, hbal1],
      fun k w hw => by simp at hw⟩

end Balance

end JauneConsensus.Facts.Gloas
