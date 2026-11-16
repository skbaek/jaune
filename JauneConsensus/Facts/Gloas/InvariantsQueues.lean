import JauneConsensus.Facts.Gloas.InvariantsAttest

/-!
# The builder queues through a Gloas block and slot (goal `eip8282-gloas-cross-layer-v1`, G3a)

Arithmetic of `pend` (`pendW_append`, `pendP_set`, `pendW_drop_le`), the monadic
`get_pending_balance_to_withdraw_for_builder` read in `ℕ` (`getPendingBalance_toNat`), and what
each phase does to the two builder queues: the parent payload's settlement or direct append
(`applyParentPrefix_split`), the withdrawals (`processWithdrawals_queues`).
-/

namespace JauneConsensus.Facts.Gloas.Invariant

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-! ## Sums -/

theorem pendingWithdrawalBalance_append (l m : List JauneConsensus.Gloas.BuilderPendingWithdrawal) (i : Nat) :
    pendingWithdrawalBalance (l ++ m) i = pendingWithdrawalBalance l i + pendingWithdrawalBalance m i := by
  simp [pendingWithdrawalBalance, List.map_append, List.sum_append]

theorem pendingWithdrawalBalance_cons (w : JauneConsensus.Gloas.BuilderPendingWithdrawal)
    (l : List JauneConsensus.Gloas.BuilderPendingWithdrawal) (i : Nat) :
    pendingWithdrawalBalance (w :: l) i = withdrawalAmount i w + pendingWithdrawalBalance l i := by
  simp [pendingWithdrawalBalance]

theorem pendingWithdrawalBalance_drop_le (l : List JauneConsensus.Gloas.BuilderPendingWithdrawal) (k i : Nat) :
    pendingWithdrawalBalance (l.drop k) i ≤ pendingWithdrawalBalance l i := by
  conv => rhs; rw [← List.take_append_drop k l]
  rw [pendingWithdrawalBalance_append]; omega

theorem pendingPaymentBalance_append (l m : List JauneConsensus.Gloas.BuilderPendingPayment) (i : Nat) :
    pendingPaymentBalance (l ++ m) i = pendingPaymentBalance l i + pendingPaymentBalance m i := by
  simp [pendingPaymentBalance, List.map_append, List.sum_append]

theorem list_sum_set {α : Type} (f : α → Nat) :
    ∀ (l : List α) (k : Nat) (v : α) (x : α), l[k]? = some x →
      ((l.set k v).map f).sum + f x = (l.map f).sum + f v
  | [], _, _, _, h => by simp at h
  | a :: l, 0, v, x, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
    omega
  | a :: l, k + 1, v, x, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
    have := list_sum_set f l k v x h
    omega

theorem pendingPaymentBalance_set (l : List JauneConsensus.Gloas.BuilderPendingPayment) (k : Nat)
    (v x : JauneConsensus.Gloas.BuilderPendingPayment) (h : l[k]? = some x) (i : Nat) :
    pendingPaymentBalance (l.set k v) i + withdrawalAmount i x.withdrawal = pendingPaymentBalance l i + withdrawalAmount i v.withdrawal :=
  list_sum_set (fun p : JauneConsensus.Gloas.BuilderPendingPayment => withdrawalAmount i p.withdrawal) l k v x h

theorem withdrawalAmount_empty (i : Nat) :
    withdrawalAmount i JauneConsensus.Gloas.BuilderPendingPayment.empty.withdrawal = 0 := by
  unfold withdrawalAmount; split <;> rfl

theorem withdrawalAmount_le (i : Nat) (w : JauneConsensus.Gloas.BuilderPendingWithdrawal) :
    withdrawalAmount i w ≤ w.amount.toNat := by
  unfold withdrawalAmount; split <;> omega

/-- Changing one entry of a payments array. -/
theorem pendingPaymentBalance_of_one {a b : Array JauneConsensus.Gloas.BuilderPendingPayment} {k : Nat}
    {x v : JauneConsensus.Gloas.BuilderPendingPayment} (hx : a[k]? = some x) (hv : b[k]? = some v)
    (hoth : ∀ j, j ≠ k → b[j]? = a[j]?) (i : Nat) :
    pendingPaymentBalance b.toList i + withdrawalAmount i x.withdrawal = pendingPaymentBalance a.toList i + withdrawalAmount i v.withdrawal := by
  have hk : k < a.size := (Array.getElem?_eq_some_iff.mp hx).1
  have hb : b = a.set k v hk := by
    apply Array.ext_getElem?
    intro j
    by_cases hj : j = k
    · subst hj; rw [hv]; simp
    · rw [hoth j hj, Array.getElem?_set_ne hk (Ne.symm hj)]
  rw [hb, Array.toList_set]
  exact pendingPaymentBalance_set _ _ _ _ (by rw [Array.getElem?_toList]; exact hx) i

/-! ## The monadic read in `ℕ` -/

theorem foldlM_pendingBalance {α : Type} (f : α → JauneConsensus.Gloas.BuilderPendingWithdrawal) (bi : U64)
    (site : String) :
    ∀ (l : List α) (acc v : U64),
      l.foldlM (fun acc w => if (f w).builder_index == bi then acc.add? (f w).amount site
        else pure acc) acc = .ok v →
      v.toNat = acc.toNat + (l.map (fun w => withdrawalAmount bi.toNat (f w))).sum
  | [], acc, v, h => by cases h; simp
  | w :: l, acc, v, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', ha, h⟩ := bind_eq_ok_iff.mp h
    have ih := foldlM_pendingBalance f bi site l acc' v h
    simp only [List.map_cons, List.sum_cons]
    split at ha
    · rename_i hb
      have hb' := U64.beq_eq_true_iff.mp hb
      rw [ih, U64.toNat_add? ha]
      unfold withdrawalAmount; rw [if_pos (by rw [hb'])]; omega
    · rename_i hb
      cases ha
      rw [ih]
      unfold withdrawalAmount
      rw [if_neg (fun e => hb (U64.beq_eq_true_iff.mpr (U64.ext_toNat e)))]
      omega

/-- `get_pending_balance_to_withdraw_for_builder` returns `pend` (it never overflows when it
succeeds). -/
theorem getPendingBalance_toNat {s : GloasState P} {bi v : U64}
    (h : JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder s bi = .ok v) :
    v.toNat = pendingBalance s bi.toNat := by
  unfold JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder at h
  obtain ⟨acc, ha, h⟩ := bind_eq_ok_iff.mp h
  rw [← Array.foldlM_toList] at ha h
  have e1 := foldlM_pendingBalance id bi _ _ _ _ ha
  have e2 := foldlM_pendingBalance (fun p : JauneConsensus.Gloas.BuilderPendingPayment => p.withdrawal) bi _ _ _ _ h
  rw [e2, e1]
  simp [pendingBalance, pendingWithdrawalBalance, pendingPaymentBalance, U64.toNat_zero]

/-! ## The validator requests keep `InvFrame` -/

section ValidatorRequests

local macro_rules
  | `(tactic| gstep_close) =>
    `(tactic| exact (show InvariantFrame _ _ from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (increaseBalance_invariantFrame _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (decreaseBalance_invariantFrame _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (initiateValidatorExit_invariantFrame _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (computeExitEpochAndUpdateChurn_invariantFrame _ _ _) $h; exact hh))

theorem queueExcessActiveBalance_invariantFrame (s : GloasState P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.queueExcessActiveBalance s i) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.queueExcessActiveBalance; gvcg

theorem switchToCompoundingValidator_invariantFrame (s : GloasState P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.switchToCompoundingValidator s i) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.switchToCompoundingValidator; gvcg
  all_goals exact StepRelation.ok_rebase invariantFrame ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (queueExcessActiveBalance_invariantFrame _ _)

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (switchToCompoundingValidator_invariantFrame _ _) $h; exact hh))

theorem computeConsolidationEpochAndUpdateChurn_invariantFrame (cfg : Config) (s : GloasState P) (b : Gwei) :
    Ok (JauneConsensus.Gloas.computeConsolidationEpochAndUpdateChurn cfg s b)
      (fun p => invariantFrame.relation s p.1) := by
  unfold JauneConsensus.Gloas.computeConsolidationEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (computeConsolidationEpochAndUpdateChurn_invariantFrame _ _ _) $h; exact hh))

theorem processWithdrawalRequest_invariantFrame (cfg : Config) (s : GloasState P) (wr : WithdrawalRequest) :
    Ok (JauneConsensus.Gloas.processWithdrawalRequest cfg s wr) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processWithdrawalRequest; gvcg
  all_goals exact initiateValidatorExit_invariantFrame _ _ _

theorem processConsolidationRequest_invariantFrame (cfg : Config) (s : GloasState P)
    (cr : ConsolidationRequest) :
    Ok (JauneConsensus.Gloas.processConsolidationRequest cfg s cr) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processConsolidationRequest; gvcg
  all_goals exact switchToCompoundingValidator_invariantFrame _ _

end ValidatorRequests

/-- How the parent payload's prefix (`applyParentPrefix`) ends: one `settle_builder_payment`,
the direct append of `L`'s withdrawal (when `L`'s slot is neither in the current nor in the
previous epoch and `L.value > 0`), or nothing; then the validator requests, which keep
`InvFrame`. -/
def PrefixSplit (s a : GloasState P) : Prop :=
  ∃ x, InvariantFrame x a ∧
    ((∃ idx, JauneConsensus.Gloas.settleBuilderPayment s idx = .ok x) ∨
      (U64.zero < s.latest_execution_payload_bid.value ∧ x = directAppend s ∧
        s.latest_block_header.slot.toNat / P.SLOTS_PER_EPOCH ≠ currentEpoch s ∧
        s.latest_block_header.slot.toNat / P.SLOTS_PER_EPOCH + 1 ≠ currentEpoch s) ∨
      x = s)

theorem getPreviousEpoch_toNat {s : GloasState P} {cur prev : U64}
    (hc : JauneConsensus.Gloas.getCurrentEpoch s = .ok cur)
    (hp : JauneConsensus.Gloas.getPreviousEpoch s = .ok prev) :
    (cur.toNat = 0 → prev.toNat = 0) ∧ (cur.toNat ≠ 0 → prev.toNat + 1 = cur.toNat) := by
  unfold JauneConsensus.Gloas.getPreviousEpoch at hp
  rw [hc] at hp
  simp only [bind, Except.bind] at hp
  split at hp
  · rename_i h0
    cases hp
    have := U64.beq_eq_true_iff.mp h0
    subst this
    exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
  · rename_i h0
    have hne : cur ≠ GENESIS_EPOCH := fun e => h0 (U64.beq_eq_true_iff.mpr e)
    have hsub := U64.toNat_sub? hp
    refine ⟨fun h => absurd (U64.ext_toNat (by rw [h]; rfl)) hne, fun h => ?_⟩
    rw [hsub, U64.toNat_one]; omega

theorem direct_epochs {pe cur prev : U64} {a c : Nat} (he : pe.toNat = a) (hc : cur.toNat = c)
    (hpv : (cur.toNat = 0 → prev.toNat = 0) ∧ (cur.toNat ≠ 0 → prev.toNat + 1 = cur.toNat))
    (n1 : ¬ (pe == cur) = true) (n2 : ¬ (pe == prev) = true) : a ≠ c ∧ a + 1 ≠ c := by
  have e1 : pe.toNat ≠ cur.toNat := fun e => n1 (U64.beq_eq_true_iff.mpr (U64.ext_toNat e))
  have e2 : pe.toNat ≠ prev.toNat := fun e => n2 (U64.beq_eq_true_iff.mpr (U64.ext_toNat e))
  by_cases h0 : cur.toNat = 0
  · have := hpv.1 h0; omega
  · have := hpv.2 h0; omega

section Prefix

local macro_rules
  | `(tactic| gstep_close) =>
    `(tactic| exact (show InvariantFrame _ _ from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processWithdrawalRequest_invariantFrame _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processConsolidationRequest_invariantFrame _ _ _) $h; exact hh))

theorem applyParentPrefix_split {ctx : Context} {s a : GloasState P} {r : JauneConsensus.Gloas.ExecutionRequests}
    (h : JauneConsensus.Gloas.applyParentPrefix ctx s r = .ok a) : PrefixSplit s a := by
  revert a h
  show Ok (JauneConsensus.Gloas.applyParentPrefix ctx s r) (PrefixSplit s)
  unfold JauneConsensus.Gloas.applyParentPrefix
  gvcg
  all_goals
    apply ok_pure
    rename_i _ hl1 _ hl2 _ hl3
    have hf := invariantFrame.trans (StepRelation.forIn_array_relation invariantFrame id (fun _ _ => by gvcg) _ _ hl1)
      (invariantFrame.trans (StepRelation.forIn_array_relation invariantFrame id (fun _ _ => by gvcg) _ _ hl2)
        (StepRelation.forIn_array_relation invariantFrame id (fun _ _ => by gvcg) _ _ hl3))
    first
    | exact ⟨_, hf, Or.inl ⟨_, ‹JauneConsensus.Gloas.settleBuilderPayment s _ = _›⟩⟩
    | exact ⟨_, hf, Or.inr (Or.inr rfl)⟩
    | (refine ⟨_, hf, Or.inr (Or.inl ⟨‹_›, rfl, ?_⟩)⟩
       have he := computeEpochAtSlot_toNat ‹computeEpochAtSlot P s.latest_block_header.slot = _›
       have hc := getCurrentEpoch_toNat ‹JauneConsensus.Gloas.getCurrentEpoch s = _›
       have hpv := getPreviousEpoch_toNat ‹JauneConsensus.Gloas.getCurrentEpoch s = _›
         ‹JauneConsensus.Gloas.getPreviousEpoch s = _›
       exact direct_epochs he hc hpv ‹¬ (_ == _) = true› ‹¬ (_ == _) = true›)

end Prefix

/-! ## The withdrawals drop a prefix of the builder withdrawals -/

/-- The builder withdrawals lose a prefix, and the payments are unchanged. -/
def WithdrawalQueue (s s' : GloasState P) : Prop :=
  (∃ k, s'.builder_pending_withdrawals.toArray.toList =
    s.builder_pending_withdrawals.toArray.toList.drop k) ∧
    s'.builder_pending_payments = s.builder_pending_payments

def withdrawalQueue : StepRelation (GloasState P) where
  relation := WithdrawalQueue
  refl _ := ⟨⟨0, rfl⟩, rfl⟩
  trans h₁ h₂ := by
    obtain ⟨⟨k1, e1⟩, p1⟩ := h₁
    obtain ⟨⟨k2, e2⟩, p2⟩ := h₂
    exact ⟨⟨k1 + k2, by rw [e2, e1, List.drop_drop]⟩, p2.trans p1⟩

theorem withdrawalQueue_of_invariant {s s' : GloasState P} (h : InvariantFrame s s') : WithdrawalQueue s s' :=
  ⟨⟨0, by rw [h.2.2.1]; rfl⟩, h.2.1⟩

section WQGen

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show WithdrawalQueue _ _ from ⟨⟨0, rfl⟩, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (decreaseBalance_invariantFrame _ _ _) $h; exact withdrawalQueue_of_invariant hh))

theorem applyWithdrawals_withdrawalQueue (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.applyWithdrawals s ws) (withdrawalQueue.relation s) := by
  unfold JauneConsensus.Gloas.applyWithdrawals; gvcg

theorem updateNextWithdrawalIndex_withdrawalQueue (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalIndex s ws) (withdrawalQueue.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalIndex; gvcg

theorem updateNextWithdrawalBuilderIndex_withdrawalQueue (s : GloasState P) (n : U64) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex s n) (withdrawalQueue.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex; gvcg

theorem updateNextWithdrawalValidatorIndex_withdrawalQueue (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex s ws) (withdrawalQueue.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex; gvcg

end WQGen

/-- **`process_withdrawals` and the builder queues.** -/
theorem processWithdrawals_withdrawalQueue {s s' : GloasState P}
    (h : JauneConsensus.Gloas.processWithdrawals s = .ok s') : WithdrawalQueue s s' := by
  unfold JauneConsensus.Gloas.processWithdrawals at h
  split at h
  · cases h; exact withdrawalQueue.refl _
  · obtain ⟨ex, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨t1, h1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨t2, h2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨t6, h6, h⟩ := bind_eq_ok_iff.mp h
    have q1 := applyWithdrawals_withdrawalQueue _ _ _ h1
    have q2 := updateNextWithdrawalIndex_withdrawalQueue _ _ _ h2
    have q6 := updateNextWithdrawalBuilderIndex_withdrawalQueue _ _ _ h6
    have q7 := updateNextWithdrawalValidatorIndex_withdrawalQueue _ _ _ h
    have q5 : WithdrawalQueue t2 (JauneConsensus.Gloas.updatePendingPartialWithdrawals
        (JauneConsensus.Gloas.updateBuilderPendingWithdrawals
          (JauneConsensus.Gloas.updatePayloadExpectedWithdrawals t2 ex.withdrawals)
          ex.processed_builder_withdrawals_count)
        ex.processed_partial_withdrawals_count) := by
      refine ⟨⟨ex.processed_builder_withdrawals_count.toNat, ?_⟩, rfl⟩
      simp [JauneConsensus.Gloas.updatePendingPartialWithdrawals,
        JauneConsensus.Gloas.updateBuilderPendingWithdrawals,
        JauneConsensus.Gloas.updatePayloadExpectedWithdrawals, ProgressiveListOnSpine.ofArray,
        Array.toList_extract]
    exact withdrawalQueue.trans q1 (withdrawalQueue.trans q2 (withdrawalQueue.trans q5 (withdrawalQueue.trans q6 q7)))

end JauneConsensus.Facts.Gloas.Invariant
