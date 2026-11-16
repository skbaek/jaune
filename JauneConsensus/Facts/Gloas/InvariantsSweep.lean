import JauneConsensus.Facts.Gloas.InvariantsRequests

/-!
# `process_withdrawals` for the G3 invariants (goal `eip8282-gloas-cross-layer-v1`, G3a)

`WFrame s s'`: `L`, `latest_block_hash`, the header, the slot and the builder payments are
unchanged; the registry keeps its length, and every builder its pubkey, version, execution
address and `withdrawable_epoch` (balances may fall); `next_withdrawal_builder_index` is
unchanged or in range. `process_withdrawals` keeps it (`processWithdrawals_wFrame`), through the
generator with the leaf rules below.
-/

namespace JauneConsensus.Facts.Gloas.Invariant

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-- Same identity and `withdrawable_epoch`. -/
def BuilderIdentityWithdrawableEpoch (b b' : JauneConsensus.Gloas.Builder) : Prop :=
  SameIdentity b b' ∧ b'.withdrawable_epoch = b.withdrawable_epoch

theorem BuilderIdentityWithdrawableEpoch.refl (b : JauneConsensus.Gloas.Builder) : BuilderIdentityWithdrawableEpoch b b := ⟨⟨rfl, rfl, rfl⟩, rfl⟩

theorem BuilderIdentityWithdrawableEpoch.trans {a b c : JauneConsensus.Gloas.Builder} (h₁ : BuilderIdentityWithdrawableEpoch a b) (h₂ : BuilderIdentityWithdrawableEpoch b c) :
    BuilderIdentityWithdrawableEpoch a c :=
  ⟨⟨h₂.1.1.trans h₁.1.1, h₂.1.2.1.trans h₁.1.2.1, h₂.1.2.2.trans h₁.1.2.2⟩, h₂.2.trans h₁.2⟩

/-- The frame of `process_withdrawals`. -/
def WithdrawalsFrame (s s' : GloasState P) : Prop :=
  s'.latest_execution_payload_bid = s.latest_execution_payload_bid ∧
    s'.latest_block_hash = s.latest_block_hash ∧
    s'.latest_block_header.slot = s.latest_block_header.slot ∧ s'.slot = s.slot ∧
    s'.builder_pending_payments = s.builder_pending_payments ∧
    s'.builders.toArray.size = s.builders.toArray.size ∧
    (∀ (j : Nat) (b : JauneConsensus.Gloas.Builder), s.builders.toArray[j]? = some b →
      ∃ b', s'.builders.toArray[j]? = some b' ∧ BuilderIdentityWithdrawableEpoch b b') ∧
    (s'.next_withdrawal_builder_index = s.next_withdrawal_builder_index ∨
      (0 < s.builders.toArray.size →
        s'.next_withdrawal_builder_index.toNat < s.builders.toArray.size))

/-- `WFrame` as a step relation. -/
def withdrawalsFrame : StepRelation (GloasState P) where
  relation := WithdrawalsFrame
  refl _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ b h => ⟨b, h, BuilderIdentityWithdrawableEpoch.refl b⟩, Or.inl rfl⟩
  trans {a b c} h₁ h₂ := by
    obtain ⟨l1, k1, d1, t1, p1, z1, i1, n1⟩ := h₁
    obtain ⟨l2, k2, d2, t2, p2, z2, i2, n2⟩ := h₂
    refine ⟨l2.trans l1, k2.trans k1, d2.trans d1, t2.trans t1, p2.trans p1, z2.trans z1,
      fun j x hx => ?_, ?_⟩
    · obtain ⟨y, hy, hxy⟩ := i1 j x hx
      obtain ⟨z, hz, hyz⟩ := i2 j y hy
      exact ⟨z, hz, hxy.trans hyz⟩
    · rcases n2 with e2 | e2
      · rcases n1 with e1 | e1
        · exact Or.inl (e2.trans e1)
        · exact Or.inr (fun hp => by rw [e2]; exact e1 hp)
      · exact Or.inr (fun hp => by rw [← z1]; exact e2 (by rw [z1]; exact hp))

theorem withdrawalsFrame_of_invariant {s s' : GloasState P} (h : InvariantFrame s s') : WithdrawalsFrame s s' := by
  obtain ⟨hb, hp, _, hl, hk, hd, ht, hn⟩ := h
  exact ⟨hl, hk, hd, ht, hp, by rw [hb], fun j b hj => ⟨b, by rw [hb]; exact hj, BuilderIdentityWithdrawableEpoch.refl b⟩,
    Or.inl hn⟩

theorem withdrawalsFrame_of_modify {s : GloasState P} {i : Nat}
    {g : JauneConsensus.Gloas.Builder → Fallible JauneConsensus.Gloas.Builder} {site : String}
    {ys : ProgressiveListRightSpine JauneConsensus.Gloas.Builder}
    (h : s.builders.modify i g site = .ok ys) (hg : ∀ b b', g b = .ok b' → BuilderIdentityWithdrawableEpoch b b') :
    WithdrawalsFrame s { s with builders := ys } := by
  unfold ProgressiveListOnSpine.modify at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v', hv', h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨h1, h2, h3⟩ := progressiveList_set_ok h
  refine ⟨rfl, rfl, rfl, rfl, rfl, h1, fun j b hb => ?_, Or.inl rfl⟩
  by_cases hj : j = i
  · subst hj
    rw [progressiveList_get_ok.mp hv] at hb; cases hb
    exact ⟨v', h2, hg _ _ hv'⟩
  · exact ⟨b, by rw [h3 j hj]; exact hb, BuilderIdentityWithdrawableEpoch.refl b⟩

theorem updateNextWithdrawalBuilderIndex_withdrawalsFrame (s : GloasState P) (n : U64) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex s n) (withdrawalsFrame.relation s) := by
  intro s' h
  unfold JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex at h
  simp only [] at h
  split at h
  · rename_i hpos
    obtain ⟨x, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨len, hlen, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨nx, hnx, h⟩ := bind_eq_ok_iff.mp h
    cases h
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ b hb => ⟨b, hb, BuilderIdentityWithdrawableEpoch.refl b⟩, Or.inr fun _ => ?_⟩
    show nx.toNat < s.builders.toArray.size
    rw [U64.toNat_mod? hnx, U64.toNat_ofNat? hlen]
    exact Nat.mod_lt _ hpos
  · cases h
    exact withdrawalsFrame.refl _

section Generator

local macro_rules
  | `(tactic| gstep_close) =>
    `(tactic| exact (show WithdrawalsFrame _ _ from
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ b hb => ⟨b, hb, BuilderIdentityWithdrawableEpoch.refl b⟩, Or.inl rfl⟩))
local macro_rules
  | `(tactic| gstep_close) =>
    `(tactic| exact withdrawalsFrame_of_modify (by assumption) (fun b b' hb => by
      obtain ⟨_, _, hb⟩ := bind_eq_ok_iff.mp hb; cases hb; exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (decreaseBalance_invariantFrame _ _ _) $h; exact withdrawalsFrame_of_invariant hh))

theorem applyWithdrawals_withdrawalsFrame (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.applyWithdrawals s ws) (withdrawalsFrame.relation s) := by
  unfold JauneConsensus.Gloas.applyWithdrawals; gvcg

theorem updateNextWithdrawalIndex_withdrawalsFrame (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalIndex s ws) (withdrawalsFrame.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalIndex; gvcg

theorem updateNextWithdrawalValidatorIndex_withdrawalsFrame (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex s ws) (withdrawalsFrame.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (applyWithdrawals_withdrawalsFrame _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (updateNextWithdrawalIndex_withdrawalsFrame _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (updateNextWithdrawalBuilderIndex_withdrawalsFrame _ _) $h; exact hh))

/-- `process_withdrawals` keeps `WFrame`. -/
theorem processWithdrawals_withdrawalsFrame (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processWithdrawals s) (withdrawalsFrame.relation s) := by
  unfold JauneConsensus.Gloas.processWithdrawals; gvcg
  all_goals exact StepRelation.ok_rebase withdrawalsFrame (withdrawalsFrame.refl _) (updateNextWithdrawalValidatorIndex_withdrawalsFrame _ _)

end Generator

end JauneConsensus.Facts.Gloas.Invariant
