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

B5(ii), provenance per step:

* `Src s`: the withdrawal sources of a state (pending withdrawals, non-empty payments'
  withdrawals, a paying `L`'s withdrawal); `srcLe_processSlots`, `srcLe_parent`, `src_bid`,
  `srcLe_ops`: no phase creates a source except the block's own paying bid;
* **`GStepView.src_step`**: the post-state's sources are the pre-state's, or the step's own paying
  bid's withdrawal, whose signature passed `blsVerify bls` (real BLS at `bls = true`);
* **`GStepView.debit_provenance`**: each builder debit is a pending-withdrawal prefix entry that
  is a source of the pre-state, or a withdrawable builder's own sweep to its `execution_address`.

B5(iii), per step: `rotation_fate` (one epoch rotation: each previous-epoch entry is appended at
the quorum or dropped, each current-epoch entry moves down), `parent_payments` (the settlement:
nothing, `L`'s direct append, or one `settle_builder_payment`), and **`GStepView.payment_fate`**
(a live entry of the window the block sees is settled, still live, cleared, or overwritten by the
block's own bid).

B5(iv), per step: `GStepView.early_return` (an EMPTY parent with `latest_block_hash != L.block_hash`
withdraws nothing) and `GStepView.carried_withdrawals_equal` (a delivered envelope carries the
post-block state's `payload_expected_withdrawals` as lists).
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

/-! ## B5(ii): where a pending builder withdrawal can come from -/

/-- The withdrawal sources of a state: an entry of `builder_pending_withdrawals`, the withdrawal of
a non-empty `builder_pending_payments` entry, or `L`'s withdrawal when `L` pays. Every pending
builder withdrawal a later step debits is a source of the step's pre-state, or the withdrawal of
a bid made by a step in between (`GStepView.src_step`). -/
def Src (s : Gloas.BeaconState P) (x : Gloas.BuilderPendingWithdrawal) : Prop :=
  x ∈ s.builder_pending_withdrawals.toArray.toList ∨
    (∃ (j : Nat) (p : Gloas.BuilderPendingPayment), s.builder_pending_payments.toArray[j]? = some p ∧
      p ≠ Gloas.BuilderPendingPayment.empty ∧ p.withdrawal = x) ∨
    (U64.zero < s.latest_execution_payload_bid.value ∧ x = bidWithdrawal s.latest_execution_payload_bid)

/-- The sources of `s'` are sources of `s`. -/
def SrcLe (s s' : Gloas.BeaconState P) : Prop := ∀ x, Src s' x → Src s x

theorem SrcLe.refl (s : Gloas.BeaconState P) : SrcLe s s := fun _ h => h

theorem SrcLe.trans {a b c : Gloas.BeaconState P} (h₁ : SrcLe a b) (h₂ : SrcLe b c) : SrcLe a c :=
  fun x h => h₁ x (h₂ x h)

theorem srcLe_of_eqs {s s' : Gloas.BeaconState P}
    (hw : s'.builder_pending_withdrawals = s.builder_pending_withdrawals)
    (hp : s'.builder_pending_payments = s.builder_pending_payments)
    (hL : s'.latest_execution_payload_bid = s.latest_execution_payload_bid) : SrcLe s s' := by
  intro x h; unfold Src at h ⊢; rw [hw, hp, hL] at h; exact h

theorem srcLe_of_inv {s s' : Gloas.BeaconState P} (h : InvFrame s s') : SrcLe s s' :=
  srcLe_of_eqs h.2.2.1 h.2.1 h.2.2.2.1

theorem empty_weight : Gloas.BuilderPendingPayment.empty.weight = U64.zero := rfl

/-- The epoch rotation appends only withdrawals of non-empty payments (weight at least the quorum,
which is positive) and shifts the payments down, filling with empty entries. -/
theorem srcLe_rotation (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) {cfg : Config}
    {a b : Gloas.BeaconState P} (h : Gloas.processBuilderPendingPayments cfg a = .ok b) :
    SrcLe a b := by
  obtain ⟨-, q, hqh, hW, hP⟩ := processBuilderPendingPayments_frame h
  have hq0 := quorum_pos hq hqh
  have hL := (processBuilderPendingPayments_core cfg a b h).2.1
  intro x hx
  rcases hx with hx | ⟨j, p, hj, hne, hpx⟩ | ⟨hv, hx⟩
  · rw [hW, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hpm, hpw⟩ := List.mem_filter.mp hp
      obtain ⟨j, hj⟩ := getElem?_of_mem' (mem_of_mem_extract' hpm)
      refine Or.inr (Or.inl ⟨j, p, hj, ?_, rfl⟩)
      rintro rfl
      have : q.toNat ≤ 0 := of_decide_eq_true hpw
      omega
  · rw [hP] at hj
    have hsz := a.builder_pending_payments.size_eq
    by_cases hlt : j < a.builder_pending_payments.toArray.size - P.SLOTS_PER_EPOCH
    · rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_extract] at hj
      split at hj
      · exact Or.inr (Or.inl ⟨_, p, hj, hne, hpx⟩)
      · cases hj
    · rw [Array.getElem?_append_right (by simp; omega)] at hj
      simp only [Array.getElem?_replicate] at hj
      split at hj
      · cases hj; exact absurd rfl hne
      · cases hj
  · rw [hL] at hv hx; exact Or.inr (Or.inr ⟨hv, hx⟩)

/-- `process_slots` creates no source. -/
theorem srcLe_processSlots (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) {ctx : Ctx}
    {s s' : Gloas.BeaconState P} {slot : U64} (h : Gloas.processSlots ctx s slot = .ok s') :
    SrcLe s s' :=
  processSlots_ind (ctx := ctx) (fun m => SrcLe s m)
    (fun st st1 st2 next hI f1 _ hc => by
      have hs : SrcLe st st2 := by
        rcases hc with ⟨rfl, _⟩ | ⟨_, he⟩
        · exact srcLe_of_inv f1
        · obtain ⟨a, b, fa, hb, fb⟩ := processEpoch_phases he
          exact (srcLe_of_inv f1).trans ((srcLe_of_inv fa).trans
            ((srcLe_rotation hq hb).trans (srcLe_of_inv fb)))
      exact hI.trans (hs.trans (srcLe_of_eqs rfl rfl rfl))) h (SrcLe.refl s)

/-- The parent settlement creates no source: `settle_builder_payment` moves a non-empty payment's
withdrawal into the queue and empties the entry; the direct append moves `L`'s; the builder
requests touch only the registry. -/
theorem srcLe_parent {ctx : Ctx} {s s1 : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    (h : Gloas.processParentExecutionPayload ctx s blk = .ok s1) : SrcLe s s1 := by
  rcases processParentExecutionPayload_cases h with ⟨rfl, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · exact SrcLe.refl _
  obtain ⟨x, fx, hx⟩ := applyParentPrefix_split ha
  have hsx : SrcLe s x := by
    rcases hx with ⟨idx, hset⟩ | ⟨hv, rfl, _⟩ | rfl
    · obtain ⟨-, p, hp, hpos, hnpos, hemp, hoth⟩ := settleBuilderPayment_frame hset
      have hL := (settleBuilderPayment_core s idx x hset).2.1
      intro y hy
      rcases hy with hy | ⟨j, p', hj, hne, hpy⟩ | ⟨hv, hy⟩
      · by_cases hz : U64.zero < p.withdrawal.amount
        · rw [hpos hz] at hy
          change y ∈ (s.builder_pending_withdrawals.toArray.push p.withdrawal).toList at hy
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · exact Or.inl hy
          · refine Or.inr (Or.inl ⟨idx.toNat, p, hp, ?_, rfl⟩)
            rintro rfl; exact absurd hz (by decide)
        · rw [hnpos hz] at hy; exact Or.inl hy
      · by_cases hji : j = idx.toNat
        · subst hji; rw [hemp] at hj; cases hj; exact absurd rfl hne
        · rw [hoth j hji] at hj; exact Or.inr (Or.inl ⟨j, p', hj, hne, hpy⟩)
      · rw [hL] at hv hy; exact Or.inr (Or.inr ⟨hv, hy⟩)
    · intro y hy
      rcases hy with hy | hy | hy
      · simp only [directAppend, ProgressiveListS.push, Array.toList_push, List.mem_append,
          List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact Or.inl hy
        · exact Or.inr (Or.inr ⟨hv, rfl⟩)
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hy)
    · exact SrcLe.refl _
  have hxa := srcLe_of_inv fx
  have hda : SrcLe a d := by
    refine forIn_yield_inv (fun m => SrcLe a m) _ (fun m r m' hI hm' => ?_) _ a d hd (SrcLe.refl a)
    have hm := (depReq_cases hm').1
    exact hI.trans (srcLe_of_eqs (by rw [hm]) (by rw [hm]) (by rw [hm]))
  have hed : SrcLe d e := by
    refine forIn_yield_inv (fun m => SrcLe d m) _ (fun m r m' hI hm' => ?_) _ d e he (SrcLe.refl d)
    have hm := (exitReq_cases hm').1
    exact hI.trans (srcLe_of_eqs (by rw [hm]) (by rw [hm]) (by rw [hm]))
  obtain ⟨-, hp1, hw1, hL1, -⟩ := applyParentSuffix_post hs
  exact hsx.trans (hxa.trans (hda.trans (hed.trans (srcLe_of_eqs hw1 hp1 hL1))))

/-- A paying bid passes the builder checks, including its signature under the context's BLS
switch. -/
theorem processExecutionPayloadBid_sig {ctx : Ctx} {s s' : Gloas.BeaconState P}
    {sb : Gloas.SignedExecutionPayloadBid}
    (h : Gloas.processExecutionPayloadBid ctx s sb = .ok s') (hv : U64.zero < sb.message.value) :
    ∃ (builder : Gloas.Builder) (dom : Domain),
      s.builders.toArray[sb.message.builder_index.toNat]? = some builder ∧
      Gloas.getDomain s Gloas.DOMAIN_BEACON_BUILDER = .ok dom ∧
      blsVerify ctx.blsActive builder.pubkey (computeSigningRoot sb.message dom) sb.signature = true := by
  unfold Gloas.processExecutionPayloadBid at h
  dsimp only at h
  split at h
  · obtain ⟨u', hr, -⟩ := bind_eq_ok_iff.mp h
    have := (require_eq_ok_iff.mp hr)
    have hz : sb.message.value = U64.zero := by simpa using this
    rw [hz] at hv; exact absurd hv (by decide)
  · obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hver, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, hreq, -⟩ := bind_eq_ok_iff.mp h
    have hvt := require_eq_ok_iff.mp hreq
    subst hvt
    unfold Gloas.verifyExecutionPayloadBidSignature at hver
    obtain ⟨builder, hg, hver⟩ := bind_eq_ok_iff.mp hver
    obtain ⟨dom, hd, hver⟩ := bind_eq_ok_iff.mp hver
    exact ⟨builder, dom, ProgressiveListS_get_ok hg, hd, (Except.ok.inj hver)⟩

/-- The bid creates exactly one new source: its own withdrawal, when it pays. -/
theorem src_bid {ctx : Ctx} {s s' : Gloas.BeaconState P} {sb : Gloas.SignedExecutionPayloadBid}
    (h : Gloas.processExecutionPayloadBid ctx s sb = .ok s') (x : Gloas.BuilderPendingWithdrawal)
    (hx : Src s' x) :
    Src s x ∨ (x = bidWithdrawal sb.message ∧ U64.zero < sb.message.value) := by
  obtain ⟨hL, -, -, -, -, -, -, -, -, hq, hpz, hpp⟩ := processExecutionPayloadBid_post h
  rcases hx with hx | ⟨j, p, hj, hne, hpx⟩ | ⟨hv, hx⟩
  · rw [hq] at hx; exact Or.inl (Or.inl hx)
  · by_cases hv : U64.zero < sb.message.value
    · obtain ⟨pi, hk, hoth⟩ := hpp hv
      by_cases hjk : j = P.SLOTS_PER_EPOCH + s.slot.toNat % P.SLOTS_PER_EPOCH
      · subst hjk; rw [hk] at hj; cases hj
        exact Or.inr ⟨hpx.symm, hv⟩
      · rw [hoth j hjk] at hj; exact Or.inl (Or.inr (Or.inl ⟨j, p, hj, hne, hpx⟩))
    · rw [hpz hv] at hj; exact Or.inl (Or.inr (Or.inl ⟨j, p, hj, hne, hpx⟩))
  · rw [hL] at hv hx; exact Or.inr ⟨hx, hv⟩

theorem srcLe_ops {s s' : Gloas.BeaconState P} (h : OpsRel s s') : SrcLe s s' := by
  obtain ⟨c, hq, hpay⟩ := h
  intro x hx
  rcases hx with hx | ⟨j, p, hj, hne, hpx⟩ | ⟨hv, hx⟩
  · rw [hq] at hx; exact Or.inl hx
  · rcases hpay j with he | he | ⟨p0, p', h0, h1, hst⟩
    · rw [he] at hj; exact Or.inr (Or.inl ⟨j, p, hj, hne, hpx⟩)
    · rw [he] at hj; cases hj; exact absurd rfl hne
    · rw [h1] at hj; cases hj
      refine Or.inr (Or.inl ⟨j, p0, h0, ?_, hst.1.1 ▸ hpx⟩)
      rintro rfl
      rcases hst.1.2.2 with rfl | hpos
      · exact hne rfl
      · exact absurd hpos (by decide)
  · rw [c.2.1] at hv hx; exact Or.inr (Or.inr ⟨hv, hx⟩)

/-! ## B5(iii): what happens to a builder payment entry -/

/-- **One epoch rotation**, per entry (CL:1716-1731): an entry of the previous epoch's half has its
withdrawal appended when its weight reaches the quorum (`quorum`) and is otherwise dropped
(`droppedSubQuorum`); an entry of the current epoch's half moves down one epoch, unchanged. -/
theorem rotation_fate {cfg : Config} {a b : Gloas.BeaconState P}
    (h : Gloas.processBuilderPendingPayments cfg a = .ok b) :
    ∃ q, Gloas.getBuilderPaymentQuorumThreshold a = .ok q ∧
      b.builder_pending_withdrawals.toArray.toList =
        a.builder_pending_withdrawals.toArray.toList ++
          (((a.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH).toList.filter
            (fun p => decide (q ≤ p.weight))).map (·.withdrawal)) ∧
      (∀ j p, j < P.SLOTS_PER_EPOCH → a.builder_pending_payments.toArray[j]? = some p →
        (q ≤ p.weight ∧ p.withdrawal ∈ b.builder_pending_withdrawals.toArray.toList) ∨
        ¬ q ≤ p.weight) ∧
      (∀ j, a.builder_pending_payments.toArray[P.SLOTS_PER_EPOCH + j]? =
        b.builder_pending_payments.toArray[j]? ∨ P.SLOTS_PER_EPOCH ≤ j) := by
  obtain ⟨-, q, hqh, hW, hP⟩ := processBuilderPendingPayments_frame h
  refine ⟨q, hqh, hW, fun j p hj hp => ?_, fun j => ?_⟩
  · by_cases hw : q ≤ p.weight
    · refine Or.inl ⟨hw, ?_⟩
      rw [hW, List.mem_append]
      refine Or.inr (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨?_, by simpa using hw⟩, rfl⟩)
      have hsz := a.builder_pending_payments.size_eq
      have : (a.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH)[j]? = some p := by
        rw [Array.getElem?_extract]; simp only [Nat.zero_add]; rw [if_pos (by simp; omega)]; exact hp
      exact mem_of_getElem?' this
    · exact Or.inr hw
  · by_cases hj : P.SLOTS_PER_EPOCH ≤ j
    · exact Or.inr hj
    · left
      have hsz := a.builder_pending_payments.size_eq
      rw [hP, Array.getElem?_append_left (by simp; omega), Array.getElem?_extract, if_pos (by omega)]

/-- The parent settlement's effect on the payments and the builder withdrawals: none (EMPTY, or a
FULL parent whose payment was outside the window), the direct append of `L`'s withdrawal, or one
`settle_builder_payment`: its entry emptied, its withdrawal appended when its amount is positive. -/
theorem parent_payments {ctx : Ctx} {s s1 : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    (h : Gloas.processParentExecutionPayload ctx s blk = .ok s1) :
    (s1.builder_pending_payments = s.builder_pending_payments ∧
      (s1.builder_pending_withdrawals = s.builder_pending_withdrawals ∨
        (U64.zero < s.latest_execution_payload_bid.value ∧
          s1.builder_pending_withdrawals.toArray.toList =
            s.builder_pending_withdrawals.toArray.toList ++
              [bidWithdrawal s.latest_execution_payload_bid]))) ∨
    (∃ (idx : Nat) (p : Gloas.BuilderPendingPayment),
      s.builder_pending_payments.toArray[idx]? = some p ∧
      s1.builder_pending_payments.toArray[idx]? = some Gloas.BuilderPendingPayment.empty ∧
      (∀ j, j ≠ idx → s1.builder_pending_payments.toArray[j]? = s.builder_pending_payments.toArray[j]?) ∧
      (U64.zero < p.withdrawal.amount → s1.builder_pending_withdrawals.toArray.toList =
        s.builder_pending_withdrawals.toArray.toList ++ [p.withdrawal]) ∧
      (¬ U64.zero < p.withdrawal.amount → s1.builder_pending_withdrawals = s.builder_pending_withdrawals)) := by
  rcases processParentExecutionPayload_cases h with ⟨rfl, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · exact Or.inl ⟨rfl, Or.inl rfl⟩
  have hda : d.builder_pending_payments = a.builder_pending_payments ∧
      d.builder_pending_withdrawals = a.builder_pending_withdrawals := by
    refine forIn_yield_inv (fun m => m.builder_pending_payments = a.builder_pending_payments ∧
      m.builder_pending_withdrawals = a.builder_pending_withdrawals) _
      (fun m r m' hI hm' => ?_) _ a d hd ⟨rfl, rfl⟩
    have hm := (depReq_cases hm').1
    exact ⟨by rw [hm]; exact hI.1, by rw [hm]; exact hI.2⟩
  have hed : e.builder_pending_payments = a.builder_pending_payments ∧
      e.builder_pending_withdrawals = a.builder_pending_withdrawals := by
    refine forIn_yield_inv (fun m => m.builder_pending_payments = a.builder_pending_payments ∧
      m.builder_pending_withdrawals = a.builder_pending_withdrawals) _
      (fun m r m' hI hm' => ?_) _ d e he hda
    have hm := (exitReq_cases hm').1
    exact ⟨by rw [hm]; exact hI.1, by rw [hm]; exact hI.2⟩
  obtain ⟨-, hp1, hw1, -⟩ := applyParentSuffix_post hs
  have e1p : s1.builder_pending_payments = a.builder_pending_payments := hp1.trans hed.1
  have e1w : s1.builder_pending_withdrawals = a.builder_pending_withdrawals := hw1.trans hed.2
  obtain ⟨x, fx, hx⟩ := applyParentPrefix_split ha
  rw [fx.2.1] at e1p
  rw [fx.2.2.1] at e1w
  rcases hx with ⟨idx, hset⟩ | ⟨hv, rfl, _⟩ | rfl
  · obtain ⟨-, p, hp, hpos, hnpos, hemp, hoth⟩ := settleBuilderPayment_frame hset
    refine Or.inr ⟨idx.toNat, p, hp, by rw [e1p]; exact hemp, fun j hj => by rw [e1p]; exact hoth j hj,
      fun hz => ?_, fun hz => by rw [e1w]; exact hnpos hz⟩
    rw [e1w, hpos hz]; simp [ProgressiveListS.push]
  · refine Or.inl ⟨e1p, Or.inr ⟨hv, ?_⟩⟩
    rw [e1w]; simp [directAppend, ProgressiveListS.push, bidWithdrawal]
  · exact Or.inl ⟨e1p, Or.inl e1w⟩

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

/-- **B5(i) per step, over the raw step hypothesis** (the form the run-level theorems and B7's
per-step conservation consume): the post-slots state and the deposit trace read there exist, and
for a builder at the same incarnation the balance equation holds. -/
theorem gloasStep_builder_balance_equation
    (h : jointStepG cfg ccfg bls (.gloas preB preExec preParent) (.gloas b) env? =
      .ok (.gloas postB postExec postParent))
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH)
    (g5 : PendingCovered preB) (g3 : PendingRefsInRange preB) (g4 : ExitedHaveNoPending preB)
    (g7 : NoLiveWeightOnLatestBid preB) (g8 : LatestBidCoherence preB) (fe : FutureEmpty preB)
    (hA : LatestBidBuilderActive preB)
    (validatorsBound : postB.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : postB.builders.toArray.size ≤ 2 ^ 40)
    {bi : Gloas.BuilderIndex} {bb : Gloas.Builder} (hb : preB.builders.toArray[bi.toNat]? = some bb) :
    ∃ (postSlots : Gloas.BeaconState P) (trD : List (Gloas.BeaconState P)),
      Gloas.processSlots (gloasCtx ccfg bls) preB b.message.slot = .ok postSlots ∧
      builderDepositTrace ccfg bls postSlots b = .ok trD ∧
      (NoRegisterAt ccfg bls bi.toNat trD (blockBuilderDeposits b) →
        ∃ (ws : List Withdrawal) (bb' : Gloas.Builder),
          stepWithdrawals ccfg bls postSlots b.message = .ok ws ∧
          postB.builders.toArray[bi.toNat]? = some bb' ∧ SameIdentity bb bb' ∧
          bb'.balance.toNat + routedSum bi ws =
            bb.balance.toNat + creditedAt ccfg bls bi.toNat trD (blockBuilderDeposits b) ∧
          (∀ k w, ws[k]? = some w → Routes bi w →
            routedSum bi (ws.take k) + w.amount.toNat ≤
              bb.balance.toNat + creditedAt ccfg bls bi.toNat trD (blockBuilderDeposits b))) := by
  obtain ⟨V⟩ := gloasStep_view h
  obtain ⟨trD, -, hD, -, -⟩ := V.traces
  exact ⟨V.postSlots, trD, V.slots, hD, fun hno => V.builder_balance_equation quorumPositive
    slotsPerEpoch g5 g3 g4 g7 g8 fe hA validatorsBound buildersBound hb hD hno⟩

/-! ## B5(iv) per step -/

/-- **B5(iv), early return, per step.** When the state `process_withdrawals` reads after an EMPTY
parent (`parentFull = false`: the settlement leaves the post-slots state, the header keeps the
hashes) has `latest_block_hash != L.block_hash`, the step withdraws nothing. -/
theorem GStepView.early_return
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    (hE : parentFull V.postSlots b.message = false)
    (hne : V.postSlots.latest_block_hash ≠ V.postSlots.latest_execution_payload_bid.block_hash) :
    stepWithdrawals ccfg bls V.postSlots b.message = .ok [] := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, -⟩ := processBlock_phases V.processBlock
  have hs1 : s1 = V.postSlots := by
    rcases processParentExecutionPayload_ok_iff.mp h1 with ⟨_, _, h⟩ | ⟨hf, _⟩
    · exact h
    · rw [hE] at hf; cases hf
  subst hs1
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have hc : (s2.latest_block_hash != s2.latest_execution_payload_bid.block_hash) = true := by
    rw [hm2]; simpa using hne
  simp only [stepWithdrawals, h1, h2, bind, Except.bind, hc, ite_true]
  rfl

/-- **B5(iv), carried withdrawals, per step.** The envelope a step delivers carries exactly the
post-block state's `payload_expected_withdrawals`, as lists (U6's `WithdrawalsMatchExpected`);
the step that later settles that payload FULL reads it as its `.delivered` parent
(`GStepView.full_iff`). -/
theorem GStepView.carried_withdrawals_equal
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    {e : Gloas.SignedExecutionPayloadEnvelope P} (he : env? = some e) :
    ∃ req postE, postParent = .delivered e req postE ∧
      verifyEnvelopeG cfg ccfg bls postB postExec e = .ok (req, postE) ∧
      e.message.payload.withdrawals.toArray.toList =
        postB.payload_expected_withdrawals.toArray.toList := by
  rcases V.stepEnd with ⟨hn, -⟩ | ⟨e', req, postE, he', hv, hp⟩
  · rw [he] at hn; cases hn
  · rw [he] at he'; cases he'
    exact ⟨req, postE, hp, hv, (verifyEnvelopeG_ok_iff.mp hv).2.1⟩

/-- At a FULL step, the settled payload's withdrawals are those its delivering step's post-state
expected, as lists: the step reads the delivered parent, which a delivering step records only
with `WithdrawalsMatchExpected` (stated at the delivering step by `carried_withdrawals_equal`).
Here, the settling side: FULL names the pre-state's delivered payload. -/
theorem GStepView.settled_payload
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    {env : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P}
    {post : BlockChain} (hs : V.settle = .full env req post) :
    preParent = .delivered env req post ∧ postExec = post :=
  ⟨(V.full_iff.mp hs).2.1, (V.full_iff.mp hs).2.2.2⟩

/-! ## B5(iii) per step -/

/-- **B5(iii) per step, the block.** A live (non-empty) payment entry at index `j` of the window
the block sees (the post-slots state; the epoch rotations before it are `rotation_fate`) is, after
the block, in one of these situations:

* **settled**: the parent settlement emptied index `j` with `settle_builder_payment`, appending
  its withdrawal when its amount is positive (CL:1799-1804);
* **still live**: the post-state's entry `j` carries the same withdrawal and proposer (its weight
  may have grown by attestations);
* **cleared**: the post-state's entry `j` is empty though the settlement did not touch it (only
  `slash_validator` empties an entry in the operations, CL:1579-1581);
* **overwritten** by the block's own paying bid at its slot's index (impossible under
  `FutureEmpty`, which leaves that entry empty before the bid).

(`directAppend` is a fate of `L`, not of an entry: `parent_payments`.) -/
theorem GStepView.payment_fate
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    {j : Nat} {p : Gloas.BuilderPendingPayment}
    (hp : V.postSlots.builder_pending_payments.toArray[j]? = some p)
    (hne : p ≠ Gloas.BuilderPendingPayment.empty) :
    (∃ s1, Gloas.processParentExecutionPayload (gloasCtx ccfg bls) V.postSlots b.message = .ok s1 ∧
        s1.builder_pending_payments.toArray[j]? = some Gloas.BuilderPendingPayment.empty ∧
        (U64.zero < p.withdrawal.amount → s1.builder_pending_withdrawals.toArray.toList =
          V.postSlots.builder_pending_withdrawals.toArray.toList ++ [p.withdrawal]) ∧
        (¬ U64.zero < p.withdrawal.amount →
          s1.builder_pending_withdrawals = V.postSlots.builder_pending_withdrawals)) ∨
      (∃ p', postB.builder_pending_payments.toArray[j]? = some p' ∧ p'.withdrawal = p.withdrawal ∧
        p'.proposer_index = p.proposer_index) ∨
      postB.builder_pending_payments.toArray[j]? = some Gloas.BuilderPendingPayment.empty ∨
      (j = P.SLOTS_PER_EPOCH + b.message.body.signed_execution_payload_bid.message.slot.toNat %
          P.SLOTS_PER_EPOCH ∧ U64.zero < b.message.body.signed_execution_payload_bid.message.value) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    processBlock_phases V.processBlock
  -- after the parent settlement, either index `j` was settled, or it still holds `p`
  have hs1 : s1.builder_pending_payments.toArray[j]? = some p ∨
      (s1.builder_pending_payments.toArray[j]? = some Gloas.BuilderPendingPayment.empty ∧
        (U64.zero < p.withdrawal.amount → s1.builder_pending_withdrawals.toArray.toList =
          V.postSlots.builder_pending_withdrawals.toArray.toList ++ [p.withdrawal]) ∧
        (¬ U64.zero < p.withdrawal.amount →
          s1.builder_pending_withdrawals = V.postSlots.builder_pending_withdrawals)) := by
    rcases parent_payments h1 with ⟨hpay, -⟩ | ⟨idx, p0, hp0, hemp, hoth, hpos, hnpos⟩
    · left; rw [hpay]; exact hp
    · by_cases hji : j = idx
      · subst hji; rw [hp] at hp0; cases hp0
        exact Or.inr ⟨hemp, hpos, hnpos⟩
      · left; rw [hoth j hji]; exact hp
  rcases hs1 with hs1 | hs1
  swap
  · exact Or.inl ⟨s1, h1, hs1⟩
  right
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have w3 := processWithdrawals_wFrame _ _ h3
  have hs3 : s3.builder_pending_payments.toArray[j]? = some p := by
    rw [w3.2.2.2.2.1, hm2]; exact hs1
  have b4 := processExecutionPayloadBid_post h4
  obtain ⟨-, hslot, -, -, -, -, -, -, -, -, hpz, hpp⟩ := b4
  have hs4 : s4.builder_pending_payments.toArray[j]? = some p ∨
      (j = P.SLOTS_PER_EPOCH + b.message.body.signed_execution_payload_bid.message.slot.toNat %
          P.SLOTS_PER_EPOCH ∧ U64.zero < b.message.body.signed_execution_payload_bid.message.value) := by
    by_cases hv : U64.zero < b.message.body.signed_execution_payload_bid.message.value
    · obtain ⟨pi, -, hoth⟩ := hpp hv
      by_cases hjk : j = P.SLOTS_PER_EPOCH + s3.slot.toNat % P.SLOTS_PER_EPOCH
      · exact Or.inr ⟨by rw [hslot]; exact hjk, hv⟩
      · left; rw [hoth j hjk]; exact hs3
    · left; rw [hpz hv]; exact hs3
  rcases hs4 with hs4 | hs4
  swap
  · exact Or.inr (Or.inr hs4)
  have f5 := processRandao_invFrame _ _ _ _ h5
  have f6 := processEth1Data_invFrame _ _ _ h6
  have o7 := processOperations_ops _ _ _ _ _ h7
  have f8 := processSyncAggregate_invFrame _ _ _ _ h8
  have hs6 : s6.builder_pending_payments.toArray[j]? = some p := by
    rw [f6.2.1, f5.2.1]; exact hs4
  rw [f8.2.1]
  rcases o7.2.2 j with he | he | ⟨p0, p', h0, h1', hst⟩
  · rw [he]; exact Or.inl ⟨p, hs6, rfl, rfl⟩
  · rw [he]; exact Or.inr (Or.inl rfl)
  · rw [hs6] at h0; cases h0
    rw [h1']; exact Or.inl ⟨p', rfl, hst.1.1, hst.1.2.1⟩

/-! ## B5(ii) per step -/

/-- **B5(ii) per step, sources.** Every withdrawal source of the step's post-state is a source of
its pre-state, or the withdrawal of the step's own paying bid, which passed the builder checks
and its signature under the step's BLS switch (at `bls = true`, Jaune's real `blsVerify`) at the
state the bid was processed in (whose registry is the post-state's). Composed along a run, every
pending builder withdrawal is an anchor source (G3-14's witnessed entries) or a run bid's. -/
theorem GStepView.src_step
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (x : Gloas.BuilderPendingWithdrawal) (hx : Src postB x) :
    Src preB x ∨
      (x = bidWithdrawal b.message.body.signed_execution_payload_bid.message ∧
        U64.zero < b.message.body.signed_execution_payload_bid.message.value ∧
        ∃ (s3 s4 : Gloas.BeaconState P) (builder : Gloas.Builder) (dom : Domain),
          Gloas.processExecutionPayloadBid (gloasCtx ccfg bls) s3
            b.message.body.signed_execution_payload_bid = .ok s4 ∧
          s3.builders = postB.builders ∧
          s3.builders.toArray[b.message.body.signed_execution_payload_bid.message.builder_index.toNat]? =
            some builder ∧
          Gloas.getDomain s3 Gloas.DOMAIN_BEACON_BUILDER = .ok dom ∧
          blsVerify bls builder.pubkey
            (computeSigningRoot b.message.body.signed_execution_payload_bid.message dom)
            b.message.body.signed_execution_payload_bid.signature = true) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    processBlock_phases V.processBlock
  have hpre : SrcLe preB s3 := by
    obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
    have w3 := processWithdrawals_wFrame _ _ h3
    have hw3 : SrcLe s2 s3 := by
      rcases processWithdrawals_cases h3 with rfl | ⟨ex, t, -, -, -, hp', hw'⟩
      · exact SrcLe.refl _
      · intro y hy
        rcases hy with hy | hy | ⟨hv, hy⟩
        · rw [hw'] at hy; exact Or.inl (List.mem_of_mem_drop hy)
        · rw [hp'] at hy; exact Or.inr (Or.inl hy)
        · rw [w3.1] at hv hy; exact Or.inr (Or.inr ⟨hv, hy⟩)
    exact (srcLe_processSlots quorumPositive V.slots).trans ((srcLe_parent h1).trans
      ((srcLe_of_eqs (by rw [hm2]) (by rw [hm2]) (by rw [hm2])).trans hw3))
  have hpost : SrcLe s4 postB :=
    (srcLe_of_inv (processRandao_invFrame _ _ _ _ h5)).trans
      ((srcLe_of_inv (processEth1Data_invFrame _ _ _ h6)).trans
        ((srcLe_ops (processOperations_ops _ _ _ _ _ h7)).trans
          (srcLe_of_inv (processSyncAggregate_invFrame _ _ _ _ h8))))
  rcases src_bid h4 x (hpost x hx) with h | ⟨rfl, hv⟩
  · exact Or.inl (hpre x h)
  · obtain ⟨builder, dom, hb, hd, hsig⟩ := processExecutionPayloadBid_sig h4 hv
    have b4 := processExecutionPayloadBid_post h4
    have c := afterBid_core h5 h6 h7 h8
    exact Or.inr ⟨rfl, hv, s3, s4, builder, dom, h4, by rw [c.1, b4.2.2.2.2.1], hb, hd, hsig⟩

/-- **B5(ii) per step, debits.** Each withdrawal the step applies that is routed to a builder
(`Routes bi w`) is either (a) a prefix entry `e` of the builder pending withdrawals the step's
`process_withdrawals` reads, with `w`'s address, amount and index from `e`, and `e` a source of
the step's pre-state (`Src`: an old pending withdrawal, a settled or quorum-appended payment's,
or `L`'s by the direct append); or (b) the builders sweep paying a builder `bj` of the post-state
whose `withdrawable_epoch` has passed, to its own `execution_address`, a positive amount. The
validator phases route nothing to a builder (N7's `validatorsBound`). -/
theorem GStepView.debit_provenance
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (validatorsBound : postB.validators.toArray.size ≤ 2 ^ 40)
    {ws : List Withdrawal} (hws : stepWithdrawals ccfg bls V.postSlots b.message = .ok ws)
    {w : Withdrawal} (hw : w ∈ ws) {bi : U64} (hr : Routes bi w) :
    (∃ e, Src preB e ∧ w.address = e.fee_recipient ∧ w.amount = e.amount ∧
        Gloas.convertBuilderIndexToValidatorIndex e.builder_index = .ok w.validator_index) ∨
    (∃ (bj : Gloas.BuilderIndex) (bb : Gloas.Builder),
        Gloas.convertBuilderIndexToValidatorIndex bj = .ok w.validator_index ∧
        postB.builders.toArray[bj.toNat]? = some bb ∧ bb.withdrawable_epoch.toNat ≤ curEpoch postB ∧
        w.address = bb.execution_address ∧ U64.zero < w.amount) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    processBlock_phases V.processBlock
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have w3 := processWithdrawals_wFrame _ _ h3
  have b4 := processExecutionPayloadBid_post h4
  have c := afterBid_core h5 h6 h7 h8
  have hpost : postB.builders = s3.builders := by rw [c.1, b4.2.2.2.2.1]
  have hslot : postB.slot = s2.slot := by rw [c.2.2.2.2.1, b4.2.2.2.2.2.2.2.1, w3.2.2.2.1]
  have vb : s2.validators.toArray.size ≤ 2 ^ 40 := by
    have va : postB.validators.toArray.size = s3.validators.toArray.size :=
      afterWithdrawals_vlen h4 h5 h6 h7 h8
    have vb' : s3.validators.toArray.size = s2.validators.toArray.size :=
      processWithdrawals_vlen _ _ h3
    omega
  have hsrc : SrcLe preB s2 := (srcLe_processSlots quorumPositive V.slots).trans
    ((srcLe_parent h1).trans (srcLe_of_eqs (by rw [hm2]) (by rw [hm2]) (by rw [hm2])))
  simp only [stepWithdrawals, h1, h2, bind, Except.bind] at hws
  split at hws
  · cases hws; simp at hw
  obtain ⟨ex, hex, hws⟩ := bind_eq_ok_iff.mp hws
  cases hws
  unfold Gloas.getExpectedWithdrawals at hex
  obtain ⟨⟨bw, i1, n1⟩, e1, hex⟩ := bind_eq_ok_iff.mp hex
  obtain ⟨⟨pw, i2, n2⟩, e2, hex⟩ := bind_eq_ok_iff.mp hex
  obtain ⟨⟨sw, i3, n3⟩, e3, hex⟩ := bind_eq_ok_iff.mp hex
  obtain ⟨⟨vw, i4, n4⟩, e4, hex⟩ := bind_eq_ok_iff.mp hex
  cases hex
  simp only [Array.toList_append, List.mem_append, Array.toList_empty, List.nil_append] at hw
  have hval : ∀ (l : Array Withdrawal),
      (keepAll (fun w => w.validator_index.toNat < s2.validators.toArray.size)).R #[] l →
      w ∈ l.toList → False := fun l hk hm =>
    not_routes_of_lt (Nat.lt_of_lt_of_le (hk (fun _ hv => by simp at hv) w hm) vb) hr
  rcases hw with ((hw | hw) | hw) | hw
  · -- the builder withdrawals: a prefix entry of the queue
    obtain ⟨-, prov⟩ := getBuilderWithdrawals_provenance e1
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    have hk' : k < bw.size := by simpa using hk
    obtain ⟨e, he, ha, hm, hcv⟩ := prov k hk'
    refine Or.inl ⟨e, hsrc e (Or.inl (mem_of_getElem?' he)), by simpa using ha, by simpa using hm,
      by simpa using hcv⟩
  · exact (hval pw (getPendingPartialWithdrawals_inRange _ _ _ _ e2) hw).elim
  · -- the builders sweep
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    have hk' : k < sw.size := by simpa using hk
    obtain ⟨bj, bb, ep, hep, hcv, hbb, hwe, hadr, -, hpos⟩ := getBuildersSweepWithdrawals_provenance e3 k hk'
    obtain ⟨bb', hbb', hid⟩ := w3.2.2.2.2.2.2.1 _ _ hbb
    have hep' := getCurrentEpoch_toNat hep
    refine Or.inr ⟨bj, bb', by simpa using hcv, by rw [hpost]; exact hbb', ?_, ?_, by simpa using hpos⟩
    · rw [hid.2]
      have : bb.withdrawable_epoch.toNat ≤ ep.toNat := hwe
      unfold curEpoch at hep' ⊢
      rw [hslot]; omega
    · rw [hid.1.2.2]; simpa using hadr
  · exact (hval vw (getValidatorsSweepWithdrawals_inRange _ _ _ _ e4) hw).elim

end Balance

end JauneConsensus.Facts.Gloas
