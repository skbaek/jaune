import JauneConsensus.Block
import JauneConsensus.Facts.ExpectedWithdrawals
import JauneConsensus.Facts.AnchorInv
import JauneConsensus.Facts.Operations

namespace JauneConsensus
namespace Facts

variable {P : Preset} {f : CFork}

/-!
# Balance floor after `processWithdrawals` (P4 clause 2)

For a validator with `exit_epoch = FAR_FUTURE_EPOCH`, once anything has been
withdrawn for it in this call, `state.balances[i] - (sum for i) ≥ MIN_ACTIVATION_BALANCE`.
Combined with the `decreaseBalance` fold, the post-state balance stays at the floor.
-/

/-- Public copy of the private `withdrawnFor` fold in `Block.lean` (same body).
Any `.ok` hypothesis about the private fold can be used at this type by `exact`
(defeq unfolds both copies to the same `foldlM`). -/
def withdrawnSumU64 (ws : Array Withdrawal) (index : ValidatorIndex) : M Gwei :=
  ws.foldlM (fun acc w => if w.validator_index == index then U64.add? acc w.amount "total_withdrawn"
    else pure acc) U64.zero

/-- Public Nat sum of withdrawal amounts for one validator (propositional `=` test,
so `by_cases`/`if_pos` apply directly). -/
def sumFor (ws : Array Withdrawal) (idx : ValidatorIndex) : Nat :=
  ws.toList.foldl (fun acc w => if w.validator_index = idx then acc + w.amount.toNat else acc) 0

theorem sumFor_nil (idx : ValidatorIndex) : sumFor #[] idx = 0 := rfl

theorem sumFor_push (ws : Array Withdrawal) (w : Withdrawal) (idx : ValidatorIndex) :
    sumFor (ws.push w) idx =
      sumFor ws idx + (if w.validator_index = idx then w.amount.toNat else 0) := by
  unfold sumFor
  rw [Array.toList_push, List.foldl_append]
  by_cases he : w.validator_index = idx <;> simp [he]

/-- `foldl` from a nonzero start is the start plus the fold from zero. -/
theorem foldl_init_add (l : List Withdrawal) (idx : ValidatorIndex) (init : Nat) :
    l.foldl (fun a w => if w.validator_index = idx then a + w.amount.toNat else a) init =
      init + l.foldl (fun a w => if w.validator_index = idx then a + w.amount.toNat else a) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons w t ih =>
    simp only [List.foldl_cons]
    by_cases he : w.validator_index = idx <;> simp only [he, ite_true, ite_false]
    · have hA := ih (0 + w.amount.toNat)
      have hB := ih (init + w.amount.toNat)
      omega
    · exact ih init

/-- List-level bridge: a successful `List.foldlM` with checked `U64.add?` is the Nat sum. -/
theorem list_withdrawn_toNat (l : List Withdrawal) (idx : ValidatorIndex) (acc : U64) (u : U64)
    (h : l.foldlM (fun acc w => if w.validator_index == idx then U64.add? acc w.amount "total_withdrawn"
      else pure acc) acc = .ok u) :
    u.toNat = acc.toNat + l.foldl (fun a w => if w.validator_index = idx then a + w.amount.toNat else a) 0 := by
  induction l generalizing acc u with
  | nil =>
    simp at h ⊢
    cases h
    simp
  | cons w t ih =>
    simp only [List.foldlM_cons] at h
    by_cases hw : (w.validator_index == idx) = true
    · have hEq : w.validator_index = idx := (U64.beq_eq_true_iff.mp hw)
      have hIf : (if w.validator_index == idx then U64.add? acc w.amount "total_withdrawn"
          else pure acc) = U64.add? acc w.amount "total_withdrawn" := by
        simp [hw]
      rw [hIf] at h
      obtain ⟨u1, hu1, hu2⟩ := bind_ok_elim h
      have hadd := U64.toNat_add? hu1
      have hiht := ih _ _ hu2
      have hfold : (w :: t).foldl (fun a w => if w.validator_index = idx then a + w.amount.toNat else a) 0 =
          w.amount.toNat + t.foldl (fun a w => if w.validator_index = idx then a + w.amount.toNat else a) 0 := by
        simp only [List.foldl_cons, hEq, ite_true]
        have hA := foldl_init_add t idx (0 + w.amount.toNat)
        omega
      rw [hfold]
      omega
    · have hwF : ¬ (w.validator_index = idx) := by
        intro hcon
        apply hw
        exact U64.beq_eq_true_iff.mpr hcon
      have hBeqF : (w.validator_index == idx) = false := by
        cases he : (w.validator_index == idx) with
        | true => rw [he] at hw; cases hw rfl
        | false => rfl
      have hIf : (if w.validator_index == idx then U64.add? acc w.amount "total_withdrawn"
          else pure acc) = pure acc := by
        simp [hBeqF]
      rw [hIf] at h
      simp only [pure_bind] at h
      have hiht := ih _ _ h
      have hfold : (w :: t).foldl (fun a w => if w.validator_index = idx then a + w.amount.toNat else a) 0 =
          t.foldl (fun a w => if w.validator_index = idx then a + w.amount.toNat else a) 0 := by
        simp only [List.foldl_cons, hwF, ite_false]
      rw [hfold]
      omega

theorem withdrawnSumU64_toNat (ws : Array Withdrawal) (idx : ValidatorIndex) (u : U64)
    (h : withdrawnSumU64 ws idx = .ok u) :
    u.toNat = sumFor ws idx := by
  simp only [withdrawnSumU64] at h
  simp only [sumFor]
  rw [← Array.foldlM_toList] at h
  have h2 := list_withdrawn_toNat ws.toList idx U64.zero u h
  simpa [U64.toNat_zero] using h2

/-- List version of `sumFor`, for prefix invariants. -/
def sumForList (l : List Withdrawal) (idx : ValidatorIndex) : Nat :=
  l.foldl (fun acc w => if w.validator_index = idx then acc + w.amount.toNat else acc) 0

theorem sumForList_nil (idx : ValidatorIndex) : sumForList [] idx = 0 := rfl

theorem sumForList_push_single (l : List Withdrawal) (w : Withdrawal) (idx : ValidatorIndex) :
    sumForList (l ++ [w]) idx =
      sumForList l idx + (if w.validator_index = idx then w.amount.toNat else 0) := by
  unfold sumForList
  rw [List.foldl_append]
  by_cases he : w.validator_index = idx <;> simp [he]

theorem sumFor_eq_list (ws : Array Withdrawal) (idx : ValidatorIndex) :
    sumFor ws idx = sumForList ws.toList idx := rfl

/-- The loop epoch is below `FAR_FUTURE_EPOCH` when `2 ≤ SLOTS_PER_EPOCH`. -/
theorem epoch_lt_far (state : BeaconState P f) (epoch : U64)
    (hle : 2 ≤ P.SLOTS_PER_EPOCH)
    (h : getCurrentEpoch state = .ok epoch) :
    epoch.toNat < FAR_FUTURE_EPOCH.toNat := by
  unfold getCurrentEpoch computeEpochAtSlot at h
  obtain ⟨speU, hspe, hdiv⟩ := bind_ok_elim h
  have hspeNat : speU.toNat = P.SLOTS_PER_EPOCH := U64.ofNat?_toNat hspe
  have hdivNat : epoch.toNat = state.slot.toNat / speU.toNat := U64.toNat_div? hdiv
  have hslotLt : state.slot.toNat < 2 ^ 64 := U64.toNat_lt _
  have hfar : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have hdivLeSelf : epoch.toNat ≤ state.slot.toNat := by
    rw [hdivNat, hspeNat]
    exact Nat.div_le_self _ _
  have hEpochLt : epoch.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hdivLeSelf hslotLt
  have hMulLe : epoch.toNat * P.SLOTS_PER_EPOCH ≤ state.slot.toNat := by
    rw [hdivNat, hspeNat]
    exact Nat.div_mul_le_self _ _
  rw [hfar]
  by_contra hcon
  push_neg at hcon
  have hEq : epoch.toNat = 2 ^ 64 - 1 := by omega
  rw [hEq] at hMulLe
  omega

/-- `getMaxEffectiveBalance` is at least `MIN_ACTIVATION_BALANCE` under the preset premise. -/
theorem maxEb_ge_minAct (v : Validator)
    (hle : P.MIN_ACTIVATION_BALANCE ≤ P.MAX_EFFECTIVE_BALANCE_ELECTRA) :
    P.MIN_ACTIVATION_BALANCE ≤ getMaxEffectiveBalance P v := by
  unfold getMaxEffectiveBalance
  by_cases hc : hasCompoundingWithdrawalCredential v = true
  · simp [hc]
    exact hle
  · simp [hc]

/-- `SszList.get` after `SszList.set` at the same index. -/
theorem ssz_get_set_eq {α : Type} {n : Nat} (xs : SszList α n) (i : Nat) (v : α) (site1 site2 : String)
    (ys : SszList α n) (hset : xs.set i v site1 = .ok ys) (x : α)
    (hget : ys.get i site2 = .ok x) : x = v := by
  have hArr : ys.toArray[i]? = some x := get_ok hget
  unfold SszList.set at hset
  split at hset
  · rename_i hi
    cases hset
    rw [Array.getElem?_set] at hArr
    simp at hArr
    cases hArr
    rfl
  · cases hset

/-- `SszList.get` after `SszList.set` at a different index. -/
theorem ssz_get_set_ne {α : Type} {n : Nat} (xs : SszList α n) (i j : Nat) (v : α) (site1 site2 : String)
    (ys : SszList α n) (hset : xs.set i v site1 = .ok ys) (hne : i ≠ j) (x y : α)
    (hgetOld : xs.get j site2 = .ok x) (hgetNew : ys.get j site2 = .ok y) : y = x := by
  have hNewArr : ys.toArray[j]? = some y := get_ok hgetNew
  have hOldArr : xs.toArray[j]? = some x := get_ok hgetOld
  unfold SszList.set at hset
  split at hset
  · rename_i hi
    cases hset
    rw [Array.getElem?_set, if_neg hne] at hNewArr
    rw [hOldArr] at hNewArr
    cases hNewArr
    rfl
  · cases hset

/-- `sumFor` is zero when nothing was withdrawn for `idx`. -/
theorem sumFor_eq_zero_of_no_withdrawn (l : List Withdrawal) (idx : ValidatorIndex)
    (h : ∀ w ∈ l, w.validator_index ≠ idx) : l.foldl (fun acc w => if w.validator_index = idx then acc + w.amount.toNat else acc) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons w t ih =>
    simp only [List.foldl_cons]
    have hw : w.validator_index ≠ idx := h w (by simp)
    have ht : ∀ w ∈ t, w.validator_index ≠ idx := fun w hm => h w (List.mem_cons_of_mem _ hm)
    simp only [hw, ite_false]
    exact ih ht

theorem sumForArray_eq_zero_of_no_withdrawn (ws : Array Withdrawal) (idx : ValidatorIndex)
    (h : ∀ w ∈ ws.toList, w.validator_index ≠ idx) : sumFor ws idx = 0 := by
  unfold sumFor
  exact sumFor_eq_zero_of_no_withdrawn ws.toList idx h

/-- Per-validator floor invariant across both loops of `getExpectedWithdrawals`.
For a validator with `exit_epoch = FAR_FUTURE_EPOCH`, once anything has been withdrawn,
`state.balances[i] - (sum for i) ≥ MIN_ACTIVATION_BALANCE`. -/
def FloorInv (state : BeaconState P f) (ws : Array Withdrawal) : Prop :=
  ∀ (i : ValidatorIndex),
    (∃ v, state.validators.toArray[i.toNat]? = some v ∧ v.exit_epoch = FAR_FUTURE_EPOCH) →
    (∃ w ∈ ws.toList, w.validator_index = i) →
    ∀ sBalU : U64, state.balances.get i.toNat "get_expected_withdrawals" = .ok sBalU →
      sBalU.toNat - sumFor ws i ≥ P.MIN_ACTIVATION_BALANCE

/-- `FloorInv` holds vacuously for the empty accumulator. -/
theorem floorInv_nil (state : BeaconState P f) : FloorInv state #[] := by
  intro i _ hHas _ _
  obtain ⟨w, hmem, _⟩ := hHas
  simp at hmem

/-- From `isFullyWithdrawableValidator = true`, the withdrawable epoch is past. -/
theorem fully_withdrawable_le_of_true {v : Validator} {bal : Gwei} {epoch : U64}
    (h : isFullyWithdrawableValidator f v bal epoch = true) :
    v.withdrawable_epoch.toNat ≤ epoch.toNat := by
  unfold isFullyWithdrawableValidator at h
  have hConj := (Bool.and_eq_true_iff.mp h)
  have hRest := (Bool.and_eq_true_iff.mp hConj.left)
  exact of_decide_eq_true hRest.right

/-- From `isPartiallyWithdrawableValidator = true`, the balance exceeds `maxEb`
(Electra) or `MAX_EFFECTIVE_BALANCE` (pre-Electra). -/
theorem partially_gt_of_true {v : Validator} {bal : Gwei}
    (h : isPartiallyWithdrawableValidator P f v bal = true) :
    getMaxEffectiveBalance P v < bal.toNat ∨ (¬ f.atLeast .electra = true ∧ P.MAX_EFFECTIVE_BALANCE < bal.toNat) := by
  unfold isPartiallyWithdrawableValidator at h
  by_cases he : f.atLeast .electra = true
  · simp only [he] at h
    have hConj := (Bool.and_eq_true_iff.mp h)
    have hRest := (Bool.and_eq_true_iff.mp hConj.left)
    -- `hRest.right : decide (eff = maxEb) = true`, `hConj.right : decide (maxEb < bal) = true` up to `>`/`==`.
    -- The trailing conjunct is `decide (bal.toNat > maxEb)`; `>` is `<` flipped.
    have hGt : decide (getMaxEffectiveBalance P v < bal.toNat) = true := by
      have := hConj.right
      -- `bal.toNat > maxEb` unfolds to `maxEb < bal.toNat`; `decide` respects defeq.
      exact this
    exact .inl (of_decide_eq_true hGt)
  · simp only [he] at h
    have hConj := (Bool.and_eq_true_iff.mp h)
    have hRest := (Bool.and_eq_true_iff.mp hConj.left)
    exact .inr ⟨he, of_decide_eq_true hConj.right⟩

/-- Pure-Nat helper: a loop-1 emission preserves the floor. -/
theorem floor_emit_preserved (sBal sum_old amount minAct : Nat)
    (hBalGt : minAct < sBal - sum_old)
    (hAmt : amount ≤ (sBal - sum_old) - minAct) :
    sBal - (sum_old + amount) ≥ minAct := by
  omega

/-- Pure-Nat helper: a loop-2 partial top-up preserves the floor. -/
theorem floor_partial_preserved (sBal sum_old balance maxEb minAct : Nat)
    (hBal : balance = sBal - sum_old) (hGt : maxEb < balance) (hMax : minAct ≤ maxEb) :
    sBal - (sum_old + (balance - maxEb)) ≥ minAct := by
  omega

/-- Per-validator invariant across both loops (Electra): once anything has been withdrawn
for `i` with `exit_epoch = FAR`, `state.balances[i] - sum ≥ MIN_ACTIVATION_BALANCE`.
Uses `ExitImpliesWithdrawable` (weaker than `AnchorInv`) plus the two preset premises. -/
theorem getExpected_floorInv (state : BeaconState P f)
    (he : f.atLeast .electra = true)
    (hExit : ExitImpliesWithdrawable state)
    (hle2 : 2 ≤ P.SLOTS_PER_EPOCH)
    (hleMin : P.MIN_ACTIVATION_BALANCE ≤ P.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ws : Array Withdrawal) (processed : Nat)
    (h : getExpectedWithdrawals state = .ok (ws, processed)) :
    FloorInv state ws := by
  unfold getExpectedWithdrawals at h
  dsimp at h
  obtain ⟨epoch, hepoch, h1⟩ := bind_ok_elim h
  obtain ⟨minAct, hminAct, h2⟩ := bind_ok_elim h1
  have hminNat : minAct.toNat = P.MIN_ACTIVATION_BALANCE := U64.ofNat?_toNat hminAct
  have hEpochLt : epoch.toNat < FAR_FUTURE_EPOCH.toNat := epoch_lt_far state epoch hle2 hepoch
  simp [he] at h2
  obtain ⟨pendingList, hpend, h3⟩ := bind_ok_elim h2
  obtain ⟨s1, hForIn1, h4⟩ := bind_ok_elim h3
  obtain ⟨s2, hForIn2, hMap⟩ := map_ok_elim h4
  have hFinal : s2.2.2 = ws ∧ s1.2.2 = processed := by
    have hPair : (s2.2.2, s1.2.2) = (ws, processed) := hMap
    exact Prod.mk.inj hPair
  -- Loop 1 preserves `FloorInv`.
  have hFloor1 : FloorInv state s1.2.1 := by
    have hInit : FloorInv state (#[] : Array Withdrawal) := floorInv_nil state
    -- The loop-1 accumulator is `(wid, wsAcc, proc)`; the invariant is on `wsAcc`.
    refine array_forIn_ok_inv (Inv := fun s : WithdrawalIndex × Array Withdrawal × Nat => FloorInv state s.2.1) hInit ?hy1 ?hd1 hForIn1
    · intro w hw b hb b' hstep
      by_cases hBreak : (epoch < w.withdrawable_epoch ∨ b.2.1.size = P.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP)
      · rw [if_pos hBreak] at hstep
        have hEq : ForInStep.done b = ForInStep.yield b' := Except.ok.inj hstep
        cases hEq
      · rw [if_neg hBreak] at hstep
        obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
        obtain ⟨sBalU, hbal, h2⟩ := bind_ok_elim h1
        obtain ⟨wdrawnU, hwdPriv, h3⟩ := bind_ok_elim h2
        obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
        have hwdPub : withdrawnSumU64 b.2.1 w.validator_index = .ok wdrawnU := hwdPriv
        have hwdNat : wdrawnU.toNat = sumFor b.2.1 w.validator_index := withdrawnSumU64_toNat b.2.1 w.validator_index wdrawnU hwdPub
        have hbalNat : balance.toNat = sBalU.toNat - wdrawnU.toNat := U64.toNat_sub? hbal2
        by_cases hEmit : ((validator.exit_epoch = FAR_FUTURE_EPOCH ∧ minAct ≤ validator.effective_balance) ∧ minAct < balance)
        · rw [if_pos hEmit] at h4
          obtain ⟨avail, havail, h5⟩ := bind_ok_elim h4
          obtain ⟨addr, haddr, h6⟩ := bind_ok_elim h5
          obtain ⟨wid', hwid, hMapEq⟩ := map_ok_elim h6
          have hEq : (wid', b.2.1.push ⟨b.1, w.validator_index, addr, if avail < w.amount then avail else w.amount⟩, b.2.2 + 1) = b' :=
            ForInStep.yield.inj hMapEq
          subst hEq
          have havNat : avail.toNat = balance.toNat - minAct.toNat := U64.toNat_sub? havail
          have hAmtLe : (if avail < w.amount then avail else w.amount).toNat ≤ balance.toNat - minAct.toNat := by
            rw [U64.min_toNat]
            omega
          -- Show `FloorInv` for the pushed array.
          intro i hiExit hiHas sBal0 hget0
          have hHasOld_or_new : (∃ w0 ∈ b.2.1.toList, w0.validator_index = i) ∨ (⟨b.1, w.validator_index, addr, if avail < w.amount then avail else w.amount⟩ : Withdrawal).validator_index = i := by
            obtain ⟨w0, hmem, hidx⟩ := hiHas
            simp only [Array.toList_push] at hmem
            have hOr := List.mem_append.mp hmem
            cases hOr with
            | inl hOld => exact .inl ⟨w0, hOld, hidx⟩
            | inr hNew =>
              simp at hNew
              subst hNew
              exact .inr hidx
          by_cases hiEq : i = w.validator_index
          · subst hiEq
            have hBalEq : sBalU = sBal0 := by
              have hEq1 : state.balances.toArray[w.validator_index.toNat]? = some sBalU := get_ok hbal
              have hEq0 : state.balances.toArray[w.validator_index.toNat]? = some sBal0 := get_ok hget0
              rw [hEq1] at hEq0
              cases hEq0
              rfl
            subst hBalEq
            have hSumNew : sumFor (b.2.1.push ⟨b.1, w.validator_index, addr, if avail < w.amount then avail else w.amount⟩) w.validator_index =
                sumFor b.2.1 w.validator_index + (if avail < w.amount then avail else w.amount).toNat := by
              rw [sumFor_push]
              simp
            rw [hSumNew] at ⊢
            -- `balance.toNat = sBalU.toNat - sum_old`, `amount ≤ balance - MIN`.
            have hEmitNat : minAct.toNat < balance.toNat := hEmit.right
            have hBalEq2 : balance.toNat = sBalU.toNat - sumFor b.2.1 w.validator_index := by omega
            have hBalGt : P.MIN_ACTIVATION_BALANCE < sBalU.toNat - sumFor b.2.1 w.validator_index := by omega
            have hAmtLe2 : (if avail < w.amount then avail else w.amount).toNat ≤ (sBalU.toNat - sumFor b.2.1 w.validator_index) - P.MIN_ACTIVATION_BALANCE := by
              omega
            exact floor_emit_preserved sBalU.toNat (sumFor b.2.1 w.validator_index) _ P.MIN_ACTIVATION_BALANCE hBalGt hAmtLe2
          · -- `i ≠ newIdx`: sum and membership unchanged.
            have hNe : w.validator_index ≠ i := fun hcon => hiEq hcon.symm
            have hSumEq : sumFor (b.2.1.push ⟨b.1, w.validator_index, addr, if avail < w.amount then avail else w.amount⟩) i = sumFor b.2.1 i := by
              rw [sumFor_push]
              simp [hNe]
            rw [hSumEq]
            obtain ⟨w0, hmem, hidx⟩ := hiHas
            have hmemOld : w0 ∈ b.2.1.toList := by
              simp only [Array.toList_push] at hmem
              have hOr := List.mem_append.mp hmem
              cases hOr with
              | inl hOld => exact hOld
              | inr hNew =>
                simp at hNew
                subst hNew
                cases hiEq hidx.symm
            exact hb i hiExit ⟨w0, hmemOld, hidx⟩ sBal0 hget0
        · rw [if_neg hEmit] at h4
          have hEq : (b.1, b.2.1, b.2.2 + 1) = b' := by
            have hOk : Except.ok (ForInStep.yield (b.1, b.2.1, b.2.2 + 1)) = Except.ok (ForInStep.yield b') := h4
            exact ForInStep.yield.inj (Except.ok.inj hOk)
          subst hEq
          exact hb
    · intro w hw b hb b' hstep
      by_cases hBreak : (epoch < w.withdrawable_epoch ∨ b.2.1.size = P.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP)
      · rw [if_pos hBreak] at hstep
        have hEq : b = b' := ForInStep.done.inj (Except.ok.inj hstep)
        subst hEq
        exact hb
      · rw [if_neg hBreak] at hstep
        obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
        obtain ⟨sBalU, hbal, h2⟩ := bind_ok_elim h1
        obtain ⟨wdrawnU, hwdPriv, h3⟩ := bind_ok_elim h2
        obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
        by_cases hEmit : ((validator.exit_epoch = FAR_FUTURE_EPOCH ∧ minAct ≤ validator.effective_balance) ∧ minAct < balance)
        · rw [if_pos hEmit] at h4
          obtain ⟨avail, havail, h5⟩ := bind_ok_elim h4
          obtain ⟨addr, haddr, h6⟩ := bind_ok_elim h5
          obtain ⟨wid', hwid, hMapEq⟩ := map_ok_elim h6
          have hEq : ForInStep.yield (wid', b.2.1.push ⟨b.1, w.validator_index, addr, if avail < w.amount then avail else w.amount⟩, b.2.2 + 1) = ForInStep.done b' := hMapEq
          cases hEq
        · rw [if_neg hEmit] at h4
          have hEq : ForInStep.yield (b.1, b.2.1, b.2.2 + 1) = ForInStep.done b' := Except.ok.inj h4
          cases hEq
  -- Loop 2 preserves `FloorInv` starting from `s1.2.1`.
  have hFloor2 : FloorInv state s2.2.2 := by
    have hInit2 : FloorInv state s1.2.1 := hFloor1
    -- Loop-2 accumulator is `(wid, vid, wsAcc)`; invariant on `wsAcc`.
    refine list_forIn_ok_inv (Inv := fun s : WithdrawalIndex × ValidatorIndex × Array Withdrawal => FloorInv state s.2.2) hInit2 ?hy2 ?hd2 hForIn2
    · intro x hx b hb2 b' hstep
      obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
      obtain ⟨sBalU, hbal, h2⟩ := bind_ok_elim h1
      obtain ⟨wdrawnU, hwdPriv, h3⟩ := bind_ok_elim h2
      obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
      have hwdPub : withdrawnSumU64 b.2.2 b.2.1 = .ok wdrawnU := hwdPriv
      have hwdNat : wdrawnU.toNat = sumFor b.2.2 b.2.1 := withdrawnSumU64_toNat b.2.2 b.2.1 wdrawnU hwdPub
      have hbalNat : balance.toNat = sBalU.toNat - wdrawnU.toNat := U64.toNat_sub? hbal2
      -- `sBalU` is the initial balance at `b.2.1` (loop-2 reads `state.balances`, same as `FloorInv`).
      have hBalEqInit : ∀ sBal0 : U64, state.balances.get b.2.1.toNat "get_expected_withdrawals" = .ok sBal0 → sBalU = sBal0 := by
        intro sBal0 h0
        have h1arr := get_ok hbal
        have h0arr := get_ok h0
        rw [h1arr] at h0arr
        cases h0arr
        rfl
      by_cases hFull : isFullyWithdrawableValidator f validator balance epoch = true
      · rw [if_pos hFull] at h4
        obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
        obtain ⟨wid', hwid, h6⟩ := bind_ok_elim h5
        by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
        · rw [if_pos hCap] at h6
          have hEq : ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) = ForInStep.yield b' := Except.ok.inj h6
          cases hEq
        · rw [if_neg hCap] at h6
          obtain ⟨v1, hv1, h7⟩ := bind_ok_elim h6
          obtain ⟨n1, hn1, h8⟩ := bind_ok_elim h7
          obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h8
          have hEq : (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) = b' := ForInStep.yield.inj hMapEq
          subst hEq
          -- Full withdrawal for `i` with `exit = FAR` is impossible; otherwise `ws` unchanged for `i`.
          intro i hiExit hiHas sBal0 hget0
          by_cases hiEq : i = b.2.1
          · subst hiEq
            obtain ⟨v, hvArr, hexit⟩ := hiExit
            have hvalArr : state.validators.toArray[b.2.1.toNat]? = some validator := by
              have := (ssz_get_ok_iff (xs := state.validators) (i := b.2.1.toNat)).mp hval
              exact this
            rw [hvalArr] at hvArr
            cases hvArr
            -- `validator.exit = FAR` gives `withdrawable = FAR`, contradicting `FAR ≤ epoch < FAR`.
            have hExitEq := hExit validator (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hvalArr)) hexit
            have hLe := fully_withdrawable_le_of_true hFull
            have hWdrawNat : validator.withdrawable_epoch.toNat = FAR_FUTURE_EPOCH.toNat := congrArg U64.toNat hExitEq
            have hFarLt : FAR_FUTURE_EPOCH.toNat ≤ epoch.toNat := by omega
            have hEpochLt' : epoch.toNat < FAR_FUTURE_EPOCH.toNat := hEpochLt
            omega
          · have hNe : b.2.1 ≠ i := fun hcon => hiEq hcon.symm
            have hSumEq : sumFor (b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) i = sumFor b.2.2 i := by
              rw [sumFor_push]
              simp [hNe]
            rw [hSumEq]
            obtain ⟨w0, hmem, hidx⟩ := hiHas
            have hmemOld : w0 ∈ b.2.2.toList := by
              simp only [Array.toList_push] at hmem
              have hOr := List.mem_append.mp hmem
              cases hOr with
              | inl hOld => exact hOld
              | inr hNew =>
                simp at hNew
                subst hNew
                cases hiEq hidx.symm
            exact hb2 i hiExit ⟨w0, hmemOld, hidx⟩ sBal0 hget0
      · rw [if_neg hFull] at h4
        by_cases hPart : isPartiallyWithdrawableValidator P f validator balance = true
        · rw [if_pos hPart] at h4
          obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
          obtain ⟨maxEbU, hmax, h6⟩ := bind_ok_elim h5
          obtain ⟨amt, hamt, h7⟩ := bind_ok_elim h6
          obtain ⟨wid', hwid, h8⟩ := bind_ok_elim h7
          have hmaxNat : maxEbU.toNat = getMaxEffectiveBalance P validator := by
            have hmax' : c64 (getMaxEffectiveBalance P validator) = .ok maxEbU := by simpa [he] using hmax
            exact U64.ofNat?_toNat hmax'
          have hamtNat : amt.toNat = balance.toNat - maxEbU.toNat := U64.toNat_sub? hamt
          by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
          · rw [if_pos hCap] at h8
            have hEq : ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) = ForInStep.yield b' := Except.ok.inj h8
            cases hEq
          · rw [if_neg hCap] at h8
            obtain ⟨v1, hv1, h9⟩ := bind_ok_elim h8
            obtain ⟨n1, hn1, h10⟩ := bind_ok_elim h9
            obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h10
            have hEq : (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) = b' := ForInStep.yield.inj hMapEq
            subst hEq
            intro i hiExit hiHas sBal0 hget0
            have hPartGt := partially_gt_of_true hPart
            have hGtElectra : getMaxEffectiveBalance P validator < balance.toNat := by
              cases hPartGt with
              | inl h => exact h
              | inr h => cases h.left he
            have hMaxGe : P.MIN_ACTIVATION_BALANCE ≤ getMaxEffectiveBalance P validator := maxEb_ge_minAct validator hleMin
            by_cases hiEq : i = b.2.1
            · subst hiEq
              have hBalU_eq : sBalU = sBal0 := hBalEqInit sBal0 hget0
              subst sBalU
              have hSumNew : sumFor (b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) b.2.1 = sumFor b.2.2 b.2.1 + amt.toNat := by
                rw [sumFor_push]
                simp
              rw [hSumNew]
              have hBalEq2 : balance.toNat = sBal0.toNat - sumFor b.2.2 b.2.1 := by omega
              have hAmtEq : amt.toNat = balance.toNat - getMaxEffectiveBalance P validator := by omega
              have hFloor : sBal0.toNat - (sumFor b.2.2 b.2.1 + (balance.toNat - getMaxEffectiveBalance P validator)) ≥ P.MIN_ACTIVATION_BALANCE :=
                floor_partial_preserved sBal0.toNat (sumFor b.2.2 b.2.1) balance.toNat (getMaxEffectiveBalance P validator) P.MIN_ACTIVATION_BALANCE hBalEq2 hGtElectra hMaxGe
              omega
            · have hNe : b.2.1 ≠ i := fun hcon => hiEq hcon.symm
              have hSumEq : sumFor (b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) i = sumFor b.2.2 i := by
                rw [sumFor_push]
                simp [hNe]
              rw [hSumEq]
              obtain ⟨w0, hmem, hidx⟩ := hiHas
              have hmemOld : w0 ∈ b.2.2.toList := by
                simp only [Array.toList_push] at hmem
                have hOr := List.mem_append.mp hmem
                cases hOr with
                | inl hOld => exact hOld
                | inr hNew =>
                  simp at hNew
                  subst hNew
                  cases hiEq hidx.symm
              exact hb2 i hiExit ⟨w0, hmemOld, hidx⟩ sBal0 hget0
        · rw [if_neg hPart] at h4
          by_cases hCap : b.2.2.size = P.MAX_WITHDRAWALS_PER_PAYLOAD
          · rw [if_pos hCap] at h4
            have hEq : ForInStep.done b = ForInStep.yield b' := Except.ok.inj h4
            cases hEq
          · rw [if_neg hCap] at h4
            obtain ⟨v1, hv1, h5⟩ := bind_ok_elim h4
            obtain ⟨n1, hn1, h6⟩ := bind_ok_elim h5
            obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h6
            have hEq : (b.1, vid', b.2.2) = b' := ForInStep.yield.inj hMapEq
            subst hEq
            exact hb2
    · intro x hx b hb2 b' hstep
      obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
      obtain ⟨sBalU, hbal, h2⟩ := bind_ok_elim h1
      obtain ⟨wdrawnU, hwdPriv, h3⟩ := bind_ok_elim h2
      obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
      by_cases hFull : isFullyWithdrawableValidator f validator balance epoch = true
      · rw [if_pos hFull] at h4
        obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
        obtain ⟨wid', hwid, h6⟩ := bind_ok_elim h5
        by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
        · rw [if_pos hCap] at h6
          have hEq : (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) = b' := by
            have hOk : Except.ok (ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, balance⟩)) = Except.ok (ForInStep.done b') := h6
            exact ForInStep.done.inj (Except.ok.inj hOk)
          subst hEq
          intro i hiExit hiHas sBal0 hget0
          by_cases hiEq : i = b.2.1
          · subst hiEq
            obtain ⟨v, hvArr, hexit⟩ := hiExit
            have hvalArr : state.validators.toArray[b.2.1.toNat]? = some validator := by
              have := (ssz_get_ok_iff (xs := state.validators) (i := b.2.1.toNat)).mp hval
              exact this
            rw [hvalArr] at hvArr
            cases hvArr
            have hExitEq := hExit validator (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hvalArr)) hexit
            have hLe := fully_withdrawable_le_of_true hFull
            have hWdrawNat : validator.withdrawable_epoch.toNat = FAR_FUTURE_EPOCH.toNat := congrArg U64.toNat hExitEq
            omega
          · have hNe : b.2.1 ≠ i := fun hcon => hiEq hcon.symm
            have hSumEq : sumFor (b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) i = sumFor b.2.2 i := by
              rw [sumFor_push]
              simp [hNe]
            rw [hSumEq]
            obtain ⟨w0, hmem, hidx⟩ := hiHas
            have hmemOld : w0 ∈ b.2.2.toList := by
              simp only [Array.toList_push] at hmem
              have hOr := List.mem_append.mp hmem
              cases hOr with
              | inl hOld => exact hOld
              | inr hNew =>
                simp at hNew
                subst hNew
                cases hiEq hidx.symm
            exact hb2 i hiExit ⟨w0, hmemOld, hidx⟩ sBal0 hget0
        · rw [if_neg hCap] at h6
          obtain ⟨v1, hv1, h7⟩ := bind_ok_elim h6
          obtain ⟨n1, hn1, h8⟩ := bind_ok_elim h7
          obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h8
          have hEq : ForInStep.yield (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) = ForInStep.done b' := hMapEq
          cases hEq
      · rw [if_neg hFull] at h4
        by_cases hPart : isPartiallyWithdrawableValidator P f validator balance = true
        · rw [if_pos hPart] at h4
          obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
          obtain ⟨maxEbU, hmax, h6⟩ := bind_ok_elim h5
          obtain ⟨amt, hamt, h7⟩ := bind_ok_elim h6
          obtain ⟨wid', hwid, h8⟩ := bind_ok_elim h7
          by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
          · rw [if_pos hCap] at h8
            have hEq : (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) = b' := by
              have hOk : Except.ok (ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, amt⟩)) = Except.ok (ForInStep.done b') := h8
              exact ForInStep.done.inj (Except.ok.inj hOk)
            subst hEq
            intro i hiExit hiHas sBal0 hget0
            by_cases hiEq : i = b.2.1
            · subst hiEq
              obtain ⟨v, hvArr, hexit⟩ := hiExit
              have hvalArr : state.validators.toArray[b.2.1.toNat]? = some validator := by
                have := (ssz_get_ok_iff (xs := state.validators) (i := b.2.1.toNat)).mp hval
                exact this
              rw [hvalArr] at hvArr
              cases hvArr
              -- Partial still preserves floor via `maxEb ≥ MIN`; use `partially_gt` + `maxEb_ge`.
              have hPartGt := partially_gt_of_true hPart
              have hGtElectra : getMaxEffectiveBalance P validator < balance.toNat := by
                cases hPartGt with
                | inl h => exact h
                | inr h => cases h.left he
              have hMaxGe : P.MIN_ACTIVATION_BALANCE ≤ getMaxEffectiveBalance P validator := maxEb_ge_minAct validator hleMin
              have hwdPub : withdrawnSumU64 b.2.2 b.2.1 = .ok wdrawnU := hwdPriv
              have hwdNat : wdrawnU.toNat = sumFor b.2.2 b.2.1 := withdrawnSumU64_toNat b.2.2 b.2.1 wdrawnU hwdPub
              have hbalNat : balance.toNat = sBalU.toNat - wdrawnU.toNat := U64.toNat_sub? hbal2
              have hBalU_eq : sBalU = sBal0 := by
                have h1arr := get_ok hbal
                have h0arr := get_ok hget0
                rw [h1arr] at h0arr
                cases h0arr
                rfl
              subst sBalU
              have hmaxNat : maxEbU.toNat = getMaxEffectiveBalance P validator := by
                have hmax' : c64 (getMaxEffectiveBalance P validator) = .ok maxEbU := by simpa [he] using hmax
                exact U64.ofNat?_toNat hmax'
              have hamtNat : amt.toNat = balance.toNat - maxEbU.toNat := U64.toNat_sub? hamt
              have hSumNew : sumFor (b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) b.2.1 = sumFor b.2.2 b.2.1 + amt.toNat := by
                rw [sumFor_push]
                simp
              rw [hSumNew] at ⊢
              have hAmtEq : amt.toNat = balance.toNat - getMaxEffectiveBalance P validator := by
                rw [hamtNat, hmaxNat]
              have hBalEq2 : balance.toNat = sBal0.toNat - sumFor b.2.2 b.2.1 := by omega
              have hFloor := floor_partial_preserved sBal0.toNat (sumFor b.2.2 b.2.1) balance.toNat (getMaxEffectiveBalance P validator) P.MIN_ACTIVATION_BALANCE hBalEq2 hGtElectra hMaxGe
              omega
            · have hNe : b.2.1 ≠ i := fun hcon => hiEq hcon.symm
              have hSumEq : sumFor (b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) i = sumFor b.2.2 i := by
                rw [sumFor_push]
                simp [hNe]
              rw [hSumEq]
              obtain ⟨w0, hmem, hidx⟩ := hiHas
              have hmemOld : w0 ∈ b.2.2.toList := by
                simp only [Array.toList_push] at hmem
                have hOr := List.mem_append.mp hmem
                cases hOr with
                | inl hOld => exact hOld
                | inr hNew =>
                  simp at hNew
                  subst hNew
                  cases hiEq hidx.symm
              exact hb2 i hiExit ⟨w0, hmemOld, hidx⟩ sBal0 hget0
          · rw [if_neg hCap] at h8
            obtain ⟨v1, hv1, h9⟩ := bind_ok_elim h8
            obtain ⟨n1, hn1, h10⟩ := bind_ok_elim h9
            obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h10
            have hEq : ForInStep.yield (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) = ForInStep.done b' := hMapEq
            cases hEq
        · rw [if_neg hPart] at h4
          by_cases hCap : b.2.2.size = P.MAX_WITHDRAWALS_PER_PAYLOAD
          · rw [if_pos hCap] at h4
            have hEq : b = b' := by
              have hOk : Except.ok (ForInStep.done b) = Except.ok (ForInStep.done b') := h4
              exact ForInStep.done.inj (Except.ok.inj hOk)
            subst hEq
            exact hb2
          · rw [if_neg hCap] at h4
            obtain ⟨v1, hv1, h5⟩ := bind_ok_elim h4
            obtain ⟨n1, hn1, h6⟩ := bind_ok_elim h5
            obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h6
            have hEq : ForInStep.yield (b.1, vid', b.2.2) = ForInStep.done b' := hMapEq
            cases hEq
  have hWsEq : s2.2.2 = ws := hFinal.left
  rw [← hWsEq]
  exact hFloor2

/-- `decreaseBalance` in `Nat`: same index saturates, other indices unchanged. -/
theorem decreaseBalance_nat (s s' : BeaconState P f) (idx : ValidatorIndex) (d : Gwei)
    (h : decreaseBalance s idx d = .ok s') (j : Nat) (b0 b1 : U64)
    (h0 : s.balances.get j "decreaseBalance_nat" = .ok b0)
    (h1 : s'.balances.get j "decreaseBalance_nat" = .ok b1) :
    b1.toNat = if j = idx.toNat then (if b0.toNat < d.toNat then 0 else b0.toNat - d.toNat) else b0.toNat := by
  unfold decreaseBalance at h
  obtain ⟨mid, hmod, hpure⟩ := bind_ok_elim h
  cases hpure
  unfold SszList.modify at hmod
  obtain ⟨b, hget, hrest⟩ := bind_ok_elim hmod
  obtain ⟨newVal, hg, hset⟩ := bind_ok_elim hrest
  by_cases he : j = idx.toNat
  · subst he
    have hgetEq : b = b0 := by
      have h1arr := get_ok hget
      have h0arr := get_ok h0
      rw [h1arr] at h0arr
      cases h0arr
      rfl
    rw [hgetEq] at hg
    have hgBeta : (if b0 < d then pure U64.zero else U64.sub? b0 d "decrease_balance") = .ok newVal := hg
    by_cases hlt : b0 < d
    · rw [if_pos hlt] at hgBeta
      cases hgBeta
      have hNew : b1 = U64.zero :=
        ssz_get_set_eq s.balances idx.toNat U64.zero
          "decrease_balance" "decreaseBalance_nat" _ hset b1 h1
      rw [hNew]
      have hltNat : b0.toNat < d.toNat := hlt
      rw [if_pos rfl, if_pos hltNat]
      exact U64.toNat_zero
    · have hltF : ¬ (b0 < d) := hlt
      rw [if_neg hltF] at hgBeta
      have hNew : b1 = newVal :=
        ssz_get_set_eq s.balances idx.toNat newVal
          "decrease_balance" "decreaseBalance_nat" _ hset b1 h1
      rw [hNew]
      have hx : newVal.toNat = b0.toNat - d.toNat := U64.toNat_sub? hgBeta
      have hltNat : ¬ b0.toNat < d.toNat := by
        intro hcon
        apply hlt
        exact hcon
      rw [if_pos rfl, if_neg hltNat, hx]
  · have hne : idx.toNat ≠ j := fun hcon => he hcon.symm
    have hEq := ssz_get_set_ne s.balances idx.toNat j newVal
      "decrease_balance" "decreaseBalance_nat" _ hset hne b0 b1 h0 h1
    simp [he, hEq]

/-- Nat-indexed sum, matching `decreaseBalance_nat` (`j = idx.toNat`). -/
def sumForNatList (l : List Withdrawal) (j : Nat) : Nat :=
  l.foldl (fun acc w => if w.validator_index.toNat = j then acc + w.amount.toNat else acc) 0

theorem sumForNatList_nil (j : Nat) : sumForNatList [] j = 0 := rfl

theorem sumForNatList_push_single (l : List Withdrawal) (w : Withdrawal) (j : Nat) :
    sumForNatList (l ++ [w]) j = sumForNatList l j + (if w.validator_index.toNat = j then w.amount.toNat else 0) := by
  unfold sumForNatList
  rw [List.foldl_append]
  by_cases he : w.validator_index.toNat = j <;> simp [he]

/-- `sumForList` (U64 equality) equals `sumForNatList` (Nat `toNat` equality). -/
theorem sumForList_eq_sumForNatList (l : List Withdrawal) (idx : ValidatorIndex) :
    sumForList l idx = sumForNatList l idx.toNat := by
  induction l with
  | nil => rfl
  | cons w t ih =>
    simp only [sumForList, sumForNatList, List.foldl_cons] at ⊢
    -- `w.validator_index = idx ↔ w.validator_index.toNat = idx.toNat` via `U64.ext_toNat`.
    by_cases he : w.validator_index = idx
    · simp only [he, ite_true] at ⊢
      -- `ih` is stated with the `sumForList`/`sumForNatList` defs; unfold for `omega`.
      have ihFold : t.foldl (fun acc w => if w.validator_index = idx then acc + w.amount.toNat else acc) 0 =
          t.foldl (fun acc w => if w.validator_index.toNat = idx.toNat then acc + w.amount.toNat else acc) 0 := ih
      -- `foldl (init + amount) t = (init + amount) + foldl 0 t`, etc.
      have hA := foldl_init_add t idx (0 + w.amount.toNat)
      -- For `sumForNatList`, need the analogous `foldl_init_add` for Nat index.
      have hANat : t.foldl (fun acc w => if w.validator_index.toNat = idx.toNat then acc + w.amount.toNat else acc) (0 + w.amount.toNat) =
          (0 + w.amount.toNat) + t.foldl (fun acc w => if w.validator_index.toNat = idx.toNat then acc + w.amount.toNat else acc) 0 := by
        have hGen : ∀ (l : List Withdrawal) (init : Nat),
            l.foldl (fun acc w => if w.validator_index.toNat = idx.toNat then acc + w.amount.toNat else acc) init =
              init + l.foldl (fun acc w => if w.validator_index.toNat = idx.toNat then acc + w.amount.toNat else acc) 0 := by
          intro l init
          induction l generalizing init with
          | nil => simp
          | cons w2 t2 ih2 =>
            simp only [List.foldl_cons]
            by_cases he2 : w2.validator_index.toNat = idx.toNat <;> simp only [he2, ite_true, ite_false]
            · have h1 := ih2 (0 + w2.amount.toNat)
              have h2 := ih2 (init + w2.amount.toNat)
              omega
            · exact ih2 init
        exact hGen t (0 + w.amount.toNat)
      omega
    · have heNat : ¬ (w.validator_index.toNat = idx.toNat) := by
        intro hcon
        apply he
        exact U64.ext_toNat hcon
      simp only [he, heNat, ite_false] at ⊢
      exact ih

/-- `decreaseBalance` preserves `balances` length. -/
theorem decreaseBalance_length (s s' : BeaconState P f) (idx : ValidatorIndex) (d : Gwei)
    (h : decreaseBalance s idx d = .ok s') :
    s'.balances.toArray.size = s.balances.toArray.size := by
  unfold decreaseBalance at h
  obtain ⟨mid, hmod, hpure⟩ := bind_ok_elim h
  cases hpure
  unfold SszList.modify at hmod
  obtain ⟨b, hget, hrest⟩ := bind_ok_elim hmod
  obtain ⟨newVal, hg, hset⟩ := bind_ok_elim hrest
  unfold SszList.set at hset
  split at hset
  · rename_i hi
    cases hset
    simp
  · cases hset

/-- `foldl` from a nonzero start for the Nat-indexed sum. -/
theorem foldlNat_init_add (l : List Withdrawal) (j : Nat) (init : Nat) :
    l.foldl (fun acc w => if w.validator_index.toNat = j then acc + w.amount.toNat else acc) init =
      init + l.foldl (fun acc w => if w.validator_index.toNat = j then acc + w.amount.toNat else acc) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons w t ih =>
    simp only [List.foldl_cons]
    by_cases he : w.validator_index.toNat = j <;> simp only [he, ite_true, ite_false]
    · have hA := ih (0 + w.amount.toNat)
      have hB := ih (init + w.amount.toNat)
      omega
    · exact ih init

theorem sumForNatList_cons (w : Withdrawal) (t : List Withdrawal) (j : Nat) :
    sumForNatList (w :: t) j = (if w.validator_index.toNat = j then w.amount.toNat else 0) + sumForNatList t j := by
  unfold sumForNatList
  simp only [List.foldl_cons]
  by_cases he : w.validator_index.toNat = j <;> simp only [he, ite_true, ite_false]
  · rw [foldlNat_init_add]
    omega
  · omega

/-- `List.foldlM` with `decreaseBalance` gives `init - sum` and preserves length. -/
theorem foldlM_balances (l : List Withdrawal) (st mid : BeaconState P f)
    (h : List.foldlM (fun s w => decreaseBalance s w.validator_index w.amount) st l = .ok mid) :
    mid.balances.toArray.size = st.balances.toArray.size ∧
    ∀ (j : Nat) (b0 bMid : U64),
      st.balances.toArray[j]? = some b0 →
      mid.balances.toArray[j]? = some bMid →
      bMid.toNat = b0.toNat - sumForNatList l j := by
  induction l generalizing st mid with
  | nil =>
    simp at h
    cases h
    exact ⟨rfl, fun j b0 bMid h0 h1 => by
      rw [h0] at h1
      cases h1
      simp [sumForNatList_nil]⟩
  | cons w t ih =>
    simp only [List.foldlM_cons] at h
    obtain ⟨st1, hStep, hRest⟩ := bind_ok_elim h
    have hLen1 := decreaseBalance_length st st1 w.validator_index w.amount hStep
    obtain ⟨hLenRest, hBalRest⟩ := ih st1 mid hRest
    have hLen : mid.balances.toArray.size = st.balances.toArray.size := by omega
    refine ⟨hLen, fun j b0 bMid h0 h1 => ?_⟩
    have hjLt : j < st.balances.toArray.size := by
      by_contra hcon
      have hle : st.balances.toArray.size ≤ j := Nat.le_of_not_gt hcon
      have hNone := Array.getElem?_eq_none hle
      rw [hNone] at h0
      cases h0
    have hjLt1 : j < st1.balances.toArray.size := by omega
    obtain ⟨b1, h1arr⟩ : ∃ b1, st1.balances.toArray[j]? = some b1 :=
      ⟨st1.balances.toArray[j], Array.getElem?_eq_getElem hjLt1⟩
    -- `decreaseBalance_nat` needs site `"decreaseBalance_nat"`, convert via `toArray`.
    have h0nat : st.balances.get j "decreaseBalance_nat" = .ok b0 :=
      ssz_get_ok_iff.mpr h0
    have h1nat : st1.balances.get j "decreaseBalance_nat" = .ok b1 :=
      ssz_get_ok_iff.mpr h1arr
    have hStepNat := decreaseBalance_nat st st1 w.validator_index w.amount hStep j b0 b1 h0nat h1nat
    have hEqRest := hBalRest j b1 bMid h1arr h1
    have hSumCons := sumForNatList_cons w t j
    -- `hStepNat : b1.toNat = if j = w.validator_index.toNat then ... else b0.toNat`
    -- `hEqRest : bMid.toNat = b1.toNat - sumForNatList t j`
    -- Goal: `bMid.toNat = b0.toNat - sumForNatList (w :: t) j`
    -- with `sumForNatList (w :: t) = (if ... then amt else 0) + sum t`.
    rw [hSumCons] at ⊢
    by_cases heq : j = w.validator_index.toNat
    · have hCond : w.validator_index.toNat = j := heq.symm
      rw [if_pos hCond] at ⊢
      have hStepEq : b1.toNat = (if b0.toNat < w.amount.toNat then 0 else b0.toNat - w.amount.toNat) := by
        rw [hStepNat]
        simp [heq]
      by_cases hlt : b0.toNat < w.amount.toNat
      · rw [if_pos hlt] at hStepEq
        omega
      · rw [if_neg hlt] at hStepEq
        omega
    · have hCond : ¬ w.validator_index.toNat = j := fun h => heq h.symm
      rw [if_neg hCond] at ⊢
      have hStepEq : b1.toNat = b0.toNat := by
        rw [hStepNat]
        simp [heq]
      omega

/-- `setPendingPartialWithdrawals` preserves `balances.toArray`. -/
theorem setPendingPartialWithdrawals_balances_toArray (s s' : BeaconState P f)
    (v : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT)
    (h : s.setPendingPartialWithdrawals v = .ok s') :
    s'.balances.toArray = s.balances.toArray := by
  unfold BeaconState.setPendingPartialWithdrawals at h
  obtain ⟨w, _, hPure⟩ := bind_ok_elim h
  cases hPure
  rfl

/-- The `decreaseBalance` fold in `processWithdrawals`: `post = init ∸ sum`.
Stated with `toArray` reads to avoid site-string mismatches. -/
theorem processWithdrawals_balances_toArray (st : BeaconState P f) (payload : ExecutionPayload P)
    (post : BeaconState P f) (ws : Array Withdrawal) (processed : Nat)
    (hExp : getExpectedWithdrawals st = .ok (ws, processed))
    (hProc : processWithdrawals st payload = .ok post) :
    ∀ (j : Nat) (b0 b1 : U64),
      st.balances.toArray[j]? = some b0 →
      post.balances.toArray[j]? = some b1 →
      b1.toNat = b0.toNat - sumForNatList ws.toList j := by
  unfold processWithdrawals at hProc
  obtain ⟨expPair, hExpPair, hRest⟩ := bind_ok_elim hProc
  have hPairEq : expPair = (ws, processed) := by
    have h1 := hExp
    have h2 := hExpPair
    rw [h1] at h2
    exact Except.ok.inj h2 |>.symm
  subst hPairEq
  obtain ⟨_, hReq, hRest2⟩ := bind_ok_elim hRest
  -- `hRest2` is the tail after `require`: `forIn ws st ... >>= tail = ok post`.
  -- The `let mut state := st` is pure; `dsimp` exposes the `forIn`.
  dsimp at hRest2
  obtain ⟨mid, hFor, hTail⟩ := bind_ok_elim hRest2
  -- Convert the always-yield `forIn` to `foldlM`.
  have hFold : List.foldlM (fun s w => decreaseBalance s w.validator_index w.amount) st ws.toList = .ok mid := by
    have hEq := forArr_yield ws (fun s w => decreaseBalance s w.validator_index w.amount) st
    -- `hFor : forIn ws st body = ok mid`, `hEq : forIn ... = foldlM ...`, so `foldlM ... = ok mid`.
    rw [hEq] at hFor
    exact hFor
  obtain ⟨hLenMid, hMidBal⟩ := foldlM_balances ws.toList st mid hFold
  -- Tail after the `forIn` only touches non-`balances` fields:
  -- `setPendingPartialWithdrawals` (helper above) and record updates to
  -- `next_withdrawal_*`; the rest computes `U64`s. Case on each `if`;
  -- every leaf ends in `pure {s with ...}` so `cases` + `rfl`/`e1` closes it.
  have hPostArrEq : post.balances.toArray = mid.balances.toArray := by
    by_cases heE : f.atLeast .electra = true
    · simp [heE] at hTail
      obtain ⟨pend, hPend, hTail1⟩ := bind_ok_elim hTail
      obtain ⟨arr, hArr, hTail2⟩ := bind_ok_elim hTail1
      obtain ⟨mid1, hSet, hTail3⟩ := bind_ok_elim hTail2
      have e1 : mid1.balances.toArray = mid.balances.toArray :=
        setPendingPartialWithdrawals_balances_toArray mid mid1 arr hSet
      by_cases hSz : 0 < ws.size
      · simp [hSz] at hTail3
        obtain ⟨nwi, hNwi, hTail4⟩ := bind_ok_elim hTail3
        by_cases hCap : ws.size = P.MAX_WITHDRAWALS_PER_PAYLOAD
        · rw [if_pos hCap] at hTail4
          obtain ⟨x1, hx1, hTail5⟩ := bind_ok_elim hTail4
          obtain ⟨x2, hx2, hTail6⟩ := bind_ok_elim hTail5
          obtain ⟨nxt, hNxt, hTail7⟩ := bind_ok_elim hTail6
          cases hTail7
          exact e1
        · rw [if_neg hCap] at hTail4
          obtain ⟨x1, hx1, hTail5⟩ := bind_ok_elim hTail4
          obtain ⟨x2, hx2, hTail6⟩ := bind_ok_elim hTail5
          obtain ⟨x3, hx3, hTail7⟩ := bind_ok_elim hTail6
          obtain ⟨nxt, hNxt, hTail8⟩ := bind_ok_elim hTail7
          cases hTail8
          exact e1
      · simp [hSz] at hTail3
        obtain ⟨x1, hx1, hTail4⟩ := bind_ok_elim hTail3
        obtain ⟨x2, hx2, hTail5⟩ := bind_ok_elim hTail4
        obtain ⟨x3, hx3, hTail6⟩ := bind_ok_elim hTail5
        obtain ⟨nxt, hNxt, hTail7⟩ := bind_ok_elim hTail6
        cases hTail7
        exact e1
    · simp [heE] at hTail
      by_cases hSz : 0 < ws.size
      · simp [hSz] at hTail
        obtain ⟨nwi, hNwi, hTail1⟩ := bind_ok_elim hTail
        by_cases hCap : ws.size = P.MAX_WITHDRAWALS_PER_PAYLOAD
        · rw [if_pos hCap] at hTail1
          obtain ⟨x1, hx1, hTail2⟩ := bind_ok_elim hTail1
          obtain ⟨x2, hx2, hTail3⟩ := bind_ok_elim hTail2
          obtain ⟨nxt, hNxt, hTail4⟩ := bind_ok_elim hTail3
          cases hTail4
          rfl
        · rw [if_neg hCap] at hTail1
          obtain ⟨x1, hx1, hTail2⟩ := bind_ok_elim hTail1
          obtain ⟨x2, hx2, hTail3⟩ := bind_ok_elim hTail2
          obtain ⟨x3, hx3, hTail4⟩ := bind_ok_elim hTail3
          obtain ⟨nxt, hNxt, hTail5⟩ := bind_ok_elim hTail4
          cases hTail5
          rfl
      · simp [hSz] at hTail
        obtain ⟨x1, hx1, hTail1⟩ := bind_ok_elim hTail
        obtain ⟨x2, hx2, hTail2⟩ := bind_ok_elim hTail1
        obtain ⟨x3, hx3, hTail3⟩ := bind_ok_elim hTail2
        obtain ⟨nxt, hNxt, hTail4⟩ := bind_ok_elim hTail3
        cases hTail4
        rfl
  have hPostBal : ∀ (j : Nat) (bMid b1 : U64),
      mid.balances.toArray[j]? = some bMid →
      post.balances.toArray[j]? = some b1 →
      b1 = bMid := by
    intro j bMid b1 hMidArr hPostArr
    rw [hPostArrEq] at hPostArr
    rw [hMidArr] at hPostArr
    cases hPostArr
    rfl
  intro j b0 b1 h0 h1
  have hjLt : j < st.balances.toArray.size := by
    by_contra hcon
    have hle : st.balances.toArray.size ≤ j := Nat.le_of_not_gt hcon
    have hNone := Array.getElem?_eq_none hle
    rw [hNone] at h0
    cases h0
  have hLenSt : st.balances.toArray.size = mid.balances.toArray.size := hLenMid.symm
  have hjLtMid : j < mid.balances.toArray.size := by omega
  obtain ⟨bMid, hMidArr⟩ : ∃ bMid, mid.balances.toArray[j]? = some bMid :=
    ⟨mid.balances.toArray[j], Array.getElem?_eq_getElem hjLtMid⟩
  have hEqMid := hMidBal j b0 bMid h0 hMidArr
  have hEqPost : b1 = bMid := hPostBal j bMid b1 hMidArr h1
  subst hEqPost
  exact hEqMid

/-- Headline floor after `processWithdrawals` (Electra): for a validator with
`exit_epoch = FAR` that was withdrawn for, the post-state balance is at the floor.
This covers loop-1 emissions, since loop-1 output is a prefix of the final `ws`
(loop 2 only pushes; `Block.lean` 349-368), so any loop-1 `V` appears in final `ws`. -/
theorem processWithdrawals_floor (st : BeaconState P f) (payload : ExecutionPayload P)
    (post : BeaconState P f) (ws : Array Withdrawal) (processed : Nat)
    (he : f.atLeast .electra = true)
    (hExit : ExitImpliesWithdrawable st)
    (hle2 : 2 ≤ P.SLOTS_PER_EPOCH)
    (hleMin : P.MIN_ACTIVATION_BALANCE ≤ P.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hExp : getExpectedWithdrawals st = .ok (ws, processed))
    (hProc : processWithdrawals st payload = .ok post) :
    ∀ (i : ValidatorIndex),
      (∃ v, st.validators.toArray[i.toNat]? = some v ∧ v.exit_epoch = FAR_FUTURE_EPOCH) →
      (∃ w ∈ ws.toList, w.validator_index = i) →
      ∀ b0 b1 : U64,
        st.balances.get i.toNat "processWithdrawals_floor" = .ok b0 →
        post.balances.get i.toNat "processWithdrawals_floor" = .ok b1 →
        P.MIN_ACTIVATION_BALANCE ≤ b1.toNat := by
  intro i hiExit hiHas b0 b1 h0 h1
  have hFloor : FloorInv st ws := getExpected_floorInv st he hExit hle2 hleMin ws processed hExp
  have hInv := hFloor i hiExit hiHas b0 (by
    have h0arr := get_ok h0
    -- `FloorInv` expects site `"get_expected_withdrawals"`; convert via `toArray`.
    have h0' : st.balances.get i.toNat "get_expected_withdrawals" = .ok b0 :=
      ssz_get_ok_iff.mpr h0arr
    exact h0')
  -- `hInv : b0.toNat - sumFor ws i ≥ MIN`.
  have hBal : ∀ (j : Nat) (c0 c1 : U64),
      st.balances.toArray[j]? = some c0 →
      post.balances.toArray[j]? = some c1 →
      c1.toNat = c0.toNat - sumForNatList ws.toList j :=
    processWithdrawals_balances_toArray st payload post ws processed hExp hProc
  have h0arr := get_ok h0
  have h1arr := get_ok h1
  have hEq := hBal i.toNat b0 b1 h0arr h1arr
  -- Bridge `sumFor ws i = sumForNatList ws.toList i.toNat`.
  have hSumEq : sumFor ws i = sumForNatList ws.toList i.toNat := by
    rw [sumFor_eq_list]
    exact sumForList_eq_sumForNatList ws.toList i
  -- `hInv : b0 - sum ≥ MIN`, `hEq : b1 = b0 - sum`; no `sum ≤ b0` needed.
  omega

end Facts
end JauneConsensus
