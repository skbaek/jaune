import JauneConsensus.Facts.Gloas.InvariantsRequests

/-!
# `process_withdrawals` for the G3 invariants (goal `eip8282-gloas-cross-layer-v1`, G3a)

`WFrame s s'`: `L`, `latest_block_hash`, the header, the slot and the builder payments are
unchanged; the registry keeps its length, and every builder its pubkey, version, execution
address and `withdrawable_epoch` (balances may fall); `next_withdrawal_builder_index` is
unchanged or in range. `process_withdrawals` keeps it (`processWithdrawals_wFrame`), through the
generator with the leaf rules below.
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-- Same identity and `withdrawable_epoch`. -/
def BIdW (b b' : JauneConsensus.Gloas.Builder) : Prop :=
  SameIdentity b b' ∧ b'.withdrawable_epoch = b.withdrawable_epoch

theorem BIdW.refl (b : JauneConsensus.Gloas.Builder) : BIdW b b := ⟨⟨rfl, rfl, rfl⟩, rfl⟩

theorem BIdW.trans {a b c : JauneConsensus.Gloas.Builder} (h₁ : BIdW a b) (h₂ : BIdW b c) :
    BIdW a c :=
  ⟨⟨h₂.1.1.trans h₁.1.1, h₂.1.2.1.trans h₁.1.2.1, h₂.1.2.2.trans h₁.1.2.2⟩, h₂.2.trans h₁.2⟩

/-- The frame of `process_withdrawals`. -/
def WFrame (s s' : GSt P) : Prop :=
  s'.latest_execution_payload_bid = s.latest_execution_payload_bid ∧
    s'.latest_block_hash = s.latest_block_hash ∧
    s'.latest_block_header.slot = s.latest_block_header.slot ∧ s'.slot = s.slot ∧
    s'.builder_pending_payments = s.builder_pending_payments ∧
    s'.builders.toArray.size = s.builders.toArray.size ∧
    (∀ (j : Nat) (b : JauneConsensus.Gloas.Builder), s.builders.toArray[j]? = some b →
      ∃ b', s'.builders.toArray[j]? = some b' ∧ BIdW b b') ∧
    (s'.next_withdrawal_builder_index = s.next_withdrawal_builder_index ∨
      (0 < s.builders.toArray.size →
        s'.next_withdrawal_builder_index.toNat < s.builders.toArray.size))

/-- `WFrame` as a step relation. -/
def wFrame : StepRel (GSt P) where
  R := WFrame
  refl _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ b h => ⟨b, h, BIdW.refl b⟩, Or.inl rfl⟩
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

theorem wf_of_inv {s s' : GSt P} (h : InvFrame s s') : WFrame s s' := by
  obtain ⟨hb, hp, _, hl, hk, hd, ht, hn⟩ := h
  exact ⟨hl, hk, hd, ht, hp, by rw [hb], fun j b hj => ⟨b, by rw [hb]; exact hj, BIdW.refl b⟩,
    Or.inl hn⟩

theorem wf_of_modify {s : GSt P} {i : Nat}
    {g : JauneConsensus.Gloas.Builder → M JauneConsensus.Gloas.Builder} {site : String}
    {ys : ProgressiveListR JauneConsensus.Gloas.Builder}
    (h : s.builders.modify i g site = .ok ys) (hg : ∀ b b', g b = .ok b' → BIdW b b') :
    WFrame s { s with builders := ys } := by
  unfold ProgressiveListS.modify at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v', hv', h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨h1, h2, h3⟩ := pl_set_ok h
  refine ⟨rfl, rfl, rfl, rfl, rfl, h1, fun j b hb => ?_, Or.inl rfl⟩
  by_cases hj : j = i
  · subst hj
    rw [pl_get_ok.mp hv] at hb; cases hb
    exact ⟨v', h2, hg _ _ hv'⟩
  · exact ⟨b, by rw [h3 j hj]; exact hb, BIdW.refl b⟩

theorem updateNextWithdrawalBuilderIndex_wf (s : GSt P) (n : U64) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex s n) (wFrame.R s) := by
  intro s' h
  unfold JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex at h
  simp only [] at h
  split at h
  · rename_i hpos
    obtain ⟨x, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨len, hlen, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨nx, hnx, h⟩ := bind_eq_ok_iff.mp h
    cases h
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ b hb => ⟨b, hb, BIdW.refl b⟩, Or.inr fun _ => ?_⟩
    show nx.toNat < s.builders.toArray.size
    rw [U64.toNat_mod? hnx, U64.toNat_ofNat? hlen]
    exact Nat.mod_lt _ hpos
  · cases h
    exact wFrame.refl _

section Generator

local macro_rules
  | `(tactic| gstep_close) =>
    `(tactic| exact (show WFrame _ _ from
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ b hb => ⟨b, hb, BIdW.refl b⟩, Or.inl rfl⟩))
local macro_rules
  | `(tactic| gstep_close) =>
    `(tactic| exact wf_of_modify (by assumption) (fun b b' hb => by
      obtain ⟨_, _, hb⟩ := bind_eq_ok_iff.mp hb; cases hb; exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (decreaseBalance_invFrame _ _ _) $h; exact wf_of_inv hh))

theorem applyWithdrawals_wf (s : GSt P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.applyWithdrawals s ws) (wFrame.R s) := by
  unfold JauneConsensus.Gloas.applyWithdrawals; gvcg

theorem updateNextWithdrawalIndex_wf (s : GSt P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalIndex s ws) (wFrame.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalIndex; gvcg

theorem updateNextWithdrawalValidatorIndex_wf (s : GSt P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex s ws) (wFrame.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (applyWithdrawals_wf _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (updateNextWithdrawalIndex_wf _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (updateNextWithdrawalBuilderIndex_wf _ _) $h; exact hh))

/-- `process_withdrawals` keeps `WFrame`. -/
theorem processWithdrawals_wFrame (s : GSt P) :
    Ok (JauneConsensus.Gloas.processWithdrawals s) (wFrame.R s) := by
  unfold JauneConsensus.Gloas.processWithdrawals; gvcg
  all_goals exact StepRel.ok_rebase wFrame (wFrame.refl _) (updateNextWithdrawalValidatorIndex_wf _ _)

end Generator

end JauneConsensus.Facts.Gloas.Inv
