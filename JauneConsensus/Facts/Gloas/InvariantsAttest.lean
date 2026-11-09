import JauneConsensus.Facts.Gloas.InvariantsBid

/-!
# Builder payments under the operations (goal `eip8282-gloas-cross-layer-v1`, G3a)

`process_attestation` changes one builder payment, the one of the attested slot, and only its
weight, and only when its amount is positive (`processAttestation_payments`); with
`1 ≤ MIN_ATTESTATION_INCLUSION_DELAY` that entry is not the current slot's
(`k ≠ SPE + slot % SPE`). `slash_validator` empties entries. Together: `PayStep`, the relation
the operations keep on the payments (`processOperations_payStep`).
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-- A payment keeps its withdrawal and proposer; it changes (in weight) only when its amount is
positive. -/
def PayStepP (p q : JauneConsensus.Gloas.BuilderPendingPayment) : Prop :=
  q.withdrawal = p.withdrawal ∧ q.proposer_index = p.proposer_index ∧
    (q = p ∨ U64.zero < p.withdrawal.amount)

theorem PayStepP.refl (p : JauneConsensus.Gloas.BuilderPendingPayment) : PayStepP p p :=
  ⟨rfl, rfl, Or.inl rfl⟩

theorem PayStepP.trans {p q r : JauneConsensus.Gloas.BuilderPendingPayment} (h₁ : PayStepP p q)
    (h₂ : PayStepP q r) : PayStepP p r := by
  refine ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, ?_⟩
  rcases h₁.2.2 with e | e
  · subst e; exact h₂.2.2
  · exact Or.inr e

theorem sv_get_ok {α : Type} {n : Nat} {xs : SszVector α n} {i : Nat} {site : String} {x : α}
    (h : xs.get i site = .ok x) : xs.toArray[i]? = some x := by
  unfold SszVector.get getAt at h
  split at h
  · cases h; assumption
  · cases h

/-- What `process_attestation` does to the builder payments. -/
def AttPay (s r : GSt P) : Prop :=
  r.builder_pending_withdrawals = s.builder_pending_withdrawals ∧
    ∃ k p0 p, s.builder_pending_payments.toArray[k]? = some p0 ∧
      r.builder_pending_payments.toArray[k]? = some p ∧
      (∀ j, j ≠ k → r.builder_pending_payments.toArray[j]? = s.builder_pending_payments.toArray[j]?) ∧
      PayStepP p0 p ∧
      (1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY → 0 < P.SLOTS_PER_EPOCH →
        k ≠ P.SLOTS_PER_EPOCH + s.slot.toNat % P.SLOTS_PER_EPOCH)

theorem att_idx_cur (hdel : 1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY) {s : GSt P}
    {dslot tgt cur te d x spe m k : U64}
    (hcur : JauneConsensus.Gloas.getCurrentEpoch s = .ok cur)
    (hte : computeEpochAtSlot P dslot = .ok te) (htt : tgt = te) (htc : tgt = cur)
    (hd : c64 P.MIN_ATTESTATION_INCLUSION_DELAY = .ok d) (hx : U64.add? dslot d "process_attestation" = .ok x)
    (hle : x.toNat ≤ s.slot.toNat) (hspe : c64 P.SLOTS_PER_EPOCH = .ok spe)
    (hm : U64.mod? dslot spe "process_attestation" = .ok m) (hk : U64.add? spe m "process_attestation" = .ok k) :
    k.toNat ≠ P.SLOTS_PER_EPOCH + s.slot.toNat % P.SLOTS_PER_EPOCH := by
  have e1 := getCurrentEpoch_toNat hcur
  have e2 := computeEpochAtSlot_toNat hte
  rw [U64.toNat_add? hk, U64.toNat_mod? hm, c64_toNat hspe]
  rw [U64.toNat_add? hx, c64_toNat hd] at hle
  subst htt; subst htc
  unfold curEpoch at e1
  intro heq
  have hmod : dslot.toNat % P.SLOTS_PER_EPOCH = s.slot.toNat % P.SLOTS_PER_EPOCH := by omega
  have hdiv : dslot.toNat / P.SLOTS_PER_EPOCH = s.slot.toNat / P.SLOTS_PER_EPOCH := by omega
  have := Nat.div_add_mod dslot.toNat P.SLOTS_PER_EPOCH
  have := Nat.div_add_mod s.slot.toNat P.SLOTS_PER_EPOCH
  have : dslot.toNat = s.slot.toNat := by
    rw [← Nat.div_add_mod dslot.toNat P.SLOTS_PER_EPOCH, ← Nat.div_add_mod s.slot.toNat P.SLOTS_PER_EPOCH,
      hmod, hdiv]
  omega

theorem att_idx_prev (hspe0 : 0 < P.SLOTS_PER_EPOCH) {s : GSt P} {dslot spe k : U64}
    (hspe : c64 P.SLOTS_PER_EPOCH = .ok spe)
    (hk : U64.mod? dslot spe "process_attestation" = .ok k) :
    k.toNat ≠ P.SLOTS_PER_EPOCH + s.slot.toNat % P.SLOTS_PER_EPOCH := by
  rw [U64.toNat_mod? hk, c64_toNat hspe]
  have := Nat.mod_lt dslot.toNat hspe0
  omega

set_option maxHeartbeats 4000000 in
/-- **`process_attestation` and the builder payments.** -/
theorem processAttestation_payments (ctx : Ctx) (s : GSt P)
    (a : JauneConsensus.Gloas.Attestation P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processAttestation ctx s a ps) (AttPay s) := by
  unfold JauneConsensus.Gloas.processAttestation
  gvcg
  all_goals
    apply ok_pure
    rename_i st1 hinc _ hset
    have hl := ‹forIn _ (_, _, U64.zero) _ = Except.ok _›
    have hloop := array_forIn_rel
      (fun x y : JauneConsensus.Gloas.BuilderPendingPayment × ProgressiveListR ParticipationFlags × U64 =>
        PayStepP x.1 y.1) (fun _ => PayStepP.refl _) (fun _ _ _ h1 h2 => h1.trans h2) _
      (fun _ _ r hr => by
        try (set_option simprocs false in simp only [] at hr)
        obtain ⟨_, _, hr⟩ := bind_eq_ok_iff.mp hr
        obtain ⟨_, _, hr⟩ := bind_eq_ok_iff.mp hr
        try (set_option simprocs false in simp only [] at hr)
        split at hr
        · obtain ⟨_, _, hr⟩ := bind_eq_ok_iff.mp hr
          split at hr
          · split at hr
            · rename_i hpos
              obtain ⟨_, _, hr⟩ := bind_eq_ok_iff.mp hr
              obtain ⟨_, _, hr⟩ := bind_eq_ok_iff.mp hr
              cases hr
              exact ⟨rfl, rfl, Or.inr hpos⟩
            · cases hr; exact PayStepP.refl _
          · cases hr; exact PayStepP.refl _
        · cases hr; exact PayStepP.refl _) _ _ _ hl
    have hp0 := sv_get_ok ‹SszVector.get s.builder_pending_payments _ _ = Except.ok _›
    have hf := increaseBalance_invFrame _ _ _ _ hinc
    obtain ⟨h1, h2⟩ := sv_set_ok hset
    have hpay1 : st1.builder_pending_payments = s.builder_pending_payments := by rw [hf.2.1]; split <;> rfl
    have hw1 : st1.builder_pending_withdrawals = s.builder_pending_withdrawals := by rw [hf.2.2.1]; split <;> rfl
    refine ⟨hw1, _, _, _, hp0, h1, fun j hj => by rw [h2 j hj, hpay1], hloop, fun hdel hspe0 => ?_⟩
    first
    | exact att_idx_cur hdel ‹JauneConsensus.Gloas.getCurrentEpoch s = _›
        ‹computeEpochAtSlot P a.data.slot = _›
        (U64.beq_eq_true_iff.mp (require_ok ‹require (a.data.target.epoch == _) _ = _›))
        (U64.beq_eq_true_iff.mp ‹(a.data.target.epoch == _) = true›)
        ‹c64 P.MIN_ATTESTATION_INCLUSION_DELAY = _› ‹U64.add? a.data.slot _ _ = _›
        (of_decide_eq_true (require_ok ‹require (decide (_ ≤ s.slot)) _ = _›))
        ‹c64 P.SLOTS_PER_EPOCH = _› ‹U64.mod? a.data.slot _ _ = _› ‹U64.add? _ _ "process_attestation" = _›
    | exact att_idx_prev hspe0 ‹c64 P.SLOTS_PER_EPOCH = _› ‹U64.mod? a.data.slot _ _ = _›

/-! ## The operations -/

/-- A builder payment entry across the operations: unchanged, emptied, or changed in weight only
(from a positive amount, at an entry other than the current slot's). -/
def PayEntryStep (spe slot : Nat) (o o' : Option JauneConsensus.Gloas.BuilderPendingPayment)
    (j : Nat) : Prop :=
  o' = o ∨ o' = some JauneConsensus.Gloas.BuilderPendingPayment.empty ∨
    ∃ p0 p, o = some p0 ∧ o' = some p ∧ PayStepP p0 p ∧
      (1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY → 0 < spe → j ≠ spe + slot % spe)

/-- The operations' relation: `CoreFrame`, the builder withdrawals unchanged, every payment
entry a `PayEntryStep`. -/
def OpsRel (s s' : GSt P) : Prop :=
  CoreFrame s s' ∧ s'.builder_pending_withdrawals = s.builder_pending_withdrawals ∧
    ∀ j, PayEntryStep (P := P) P.SLOTS_PER_EPOCH s.slot.toNat
      (s.builder_pending_payments.toArray[j]?) (s'.builder_pending_payments.toArray[j]?) j

theorem payEntryStep_trans {spe slot j : Nat} {a b c : Option JauneConsensus.Gloas.BuilderPendingPayment}
    (h₁ : PayEntryStep (P := P) spe slot a b j) (h₂ : PayEntryStep (P := P) spe slot b c j) :
    PayEntryStep (P := P) spe slot a c j := by
  rcases h₂ with e2 | e2 | ⟨q0, q, hq0, hq, hst, hj⟩
  · rw [e2]; exact h₁
  · exact Or.inr (Or.inl e2)
  · rcases h₁ with e1 | e1 | ⟨p0, p, hp0, hp, hst1, hj1⟩
    · subst e1; exact Or.inr (Or.inr ⟨q0, q, hq0, hq, hst, hj⟩)
    · rw [e1] at hq0; cases hq0
      rcases hst.2.2 with e | e
      · subst e; exact Or.inr (Or.inl hq)
      · exact absurd e (by decide)
    · rw [hp] at hq0; cases hq0
      exact Or.inr (Or.inr ⟨p0, q, hp0, hq, hst1.trans hst, hj1⟩)

/-- `OpsRel` as a step relation. -/
def opsRel : StepRel (GSt P) where
  R := OpsRel
  refl _ := ⟨coreFrame.refl _, rfl, fun _ => Or.inl rfl⟩
  trans {a b c} h₁ h₂ := by
    refine ⟨coreFrame.trans h₁.1 h₂.1, h₂.2.1.trans h₁.2.1, fun j => ?_⟩
    have := h₂.2.2 j
    rw [h₁.1.2.2.2.2.1] at this
    exact payEntryStep_trans (h₁.2.2 j) this

theorem opsRel_of_inv {s s' : GSt P} (h : InvFrame s s') : OpsRel s s' :=
  ⟨coreFrame_of_inv h, h.2.2.1, fun j => Or.inl (by rw [h.2.1])⟩

theorem opsRel_of_builderFrame {s s' : GSt P} (h : BuilderFrame s s') (hc : CoreFrame s s') :
    OpsRel s s' :=
  ⟨hc, h.2.2, fun j => Or.inl (by rw [h.2.1])⟩

section Ops

local macro_rules
  | `(tactic| gstep_close) =>
    `(tactic| exact (show OpsRel _ _ from ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, fun _ => Or.inl rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (exact (show OpsRel _ _ from ⟨slashValidator_core _ _ _ _ _ $h,
      (slashValidator_paymentsCleared _ _ _ _ _ $h).2.1,
      fun j => by
        rcases (slashValidator_paymentsCleared _ _ _ _ _ $h).2.2 j with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)⟩)))

theorem processProposerSlashing_ops (ctx : Ctx) (s : GSt P) (ps : ProposerSlashing) :
    Ok (JauneConsensus.Gloas.processProposerSlashing ctx s ps) (opsRel.R s) := by
  unfold JauneConsensus.Gloas.processProposerSlashing; gvcg
  all_goals exact fun x hx => (show OpsRel _ _ from ⟨slashValidator_core _ _ _ _ _ hx,
      (slashValidator_paymentsCleared _ _ _ _ _ hx).2.1,
      fun j => by
        rcases (slashValidator_paymentsCleared _ _ _ _ _ hx).2.2 j with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)⟩)

theorem processAttesterSlashing_ops (ctx : Ctx) (s : GSt P)
    (as : JauneConsensus.Gloas.AttesterSlashing) :
    Ok (JauneConsensus.Gloas.processAttesterSlashing ctx s as) (opsRel.R s) := by
  unfold JauneConsensus.Gloas.processAttesterSlashing; gvcg

theorem processAttestation_ops (ctx : Ctx) (s : GSt P) (a : JauneConsensus.Gloas.Attestation P)
    (ps : Slot) : Ok (JauneConsensus.Gloas.processAttestation ctx s a ps) (opsRel.R s) := by
  intro s' h
  obtain ⟨hw, k, p0, p, hp0, hp, hoth, hst, hk⟩ := processAttestation_payments ctx s a ps s' h
  refine ⟨processAttestation_core ctx s a ps s' h, hw, fun j => ?_⟩
  by_cases hj : j = k
  · subst hj; exact Or.inr (Or.inr ⟨p0, p, hp0, hp, hst, hk⟩)
  · exact Or.inl (hoth j hj)

theorem processVoluntaryExit_ops (ctx : Ctx) (s : GSt P) (sve : SignedVoluntaryExit) :
    Ok (JauneConsensus.Gloas.processVoluntaryExit ctx s sve) (opsRel.R s) := fun x hx =>
  opsRel_of_builderFrame (processVoluntaryExit_builderFrame _ _ _ x hx)
    (processVoluntaryExit_core _ _ _ x hx)

theorem processBlsToExecutionChange_ops (ctx : Ctx) (s : GSt P) (sac : SignedBLSToExecutionChange) :
    Ok (JauneConsensus.Gloas.processBlsToExecutionChange ctx s sac) (opsRel.R s) := fun x hx =>
  opsRel_of_builderFrame (processBlsToExecutionChange_builderFrame _ _ _ x hx)
    (processBlsToExecutionChange_core _ _ _ x hx)

theorem processPayloadAttestation_ops (ctx : Ctx) (s : GSt P)
    (pa : JauneConsensus.Gloas.PayloadAttestation P) :
    Ok (JauneConsensus.Gloas.processPayloadAttestation ctx s pa) (opsRel.R s) := by
  unfold JauneConsensus.Gloas.processPayloadAttestation; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processProposerSlashing_ops _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processAttesterSlashing_ops _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processAttestation_ops _ _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processVoluntaryExit_ops _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processBlsToExecutionChange_ops _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processPayloadAttestation_ops _ _ _) $h; exact hh))

/-- **The operations and the builder queues.** -/
theorem processOperations_ops (ctx : Ctx) (s : GSt P)
    (body : JauneConsensus.Gloas.BeaconBlockBody P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processOperations ctx s body ps) (opsRel.R s) := by
  unfold JauneConsensus.Gloas.processOperations; gvcg

end Ops

end JauneConsensus.Facts.Gloas.Inv
