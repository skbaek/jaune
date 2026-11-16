import JauneConsensus.Facts.Gloas.InvariantsSweep

/-!
# `process_slots` for the G3 invariants (goal `eip8282-gloas-cross-layer-v1`, G3a)

* `processEpoch_phases`: `process_epoch` is the frame-keeping steps before
  `process_builder_pending_payments`, that step, and the frame-keeping steps after it;
* `processSlots_ind`: an invariant of the slot loop needs only one iteration: `process_slot`
  (which keeps `InvFrame`), at an epoch boundary `process_epoch`, then `slot := slot + 1`.
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

theorem range_forIn_inv {β : Type} (I : β → Prop) {r : Std.Legacy.Range} {init out : β}
    {body : Nat → β → M (ForInStep β)} (hb : ∀ a b x, I b → body a b = .ok x → I x.value)
    (h : forIn r init body = .ok out) (hI : I init) : I out := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact list_forIn_rel (fun a b => I a → I b) (fun _ h => h) (fun _ _ _ h1 h2 x => h2 (h1 x))
    body (fun a b x hx hIb => hb a b x hIb hx) _ init out h hI

theorem invFrame_of {α : Type} {c : M α} {s : GSt P} {x : α} {f : α → GSt P}
    (hc : Ok c (fun r => invFrame.R s (f r))) (h : c = .ok x) : InvFrame s (f x) := hc x h

/-- `process_epoch`: frame, `process_builder_pending_payments`, frame. -/
theorem processEpoch_phases {ctx : Ctx} {s s' : GSt P}
    (h : JauneConsensus.Gloas.processEpoch ctx s = .ok s') :
    ∃ a b : GSt P, InvFrame s a ∧
      JauneConsensus.Gloas.processBuilderPendingPayments ctx.cfg a = .ok b ∧ InvFrame b s' := by
  unfold JauneConsensus.Gloas.processEpoch at h
  obtain ⟨x1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x6, h6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x7, h7, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x8, h8, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x9, h9, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x10, h10, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x11, h11, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x12, h12, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x13, h13, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x14, h14, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x15, h15, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x16, h16, h⟩ := bind_eq_ok_iff.mp h
  have f1 := processJustificationAndFinalization_invFrame _ _ _ h1
  have f2 := processInactivityUpdates_invFrame _ _ _ h2
  have f3 := processRewardsAndPenalties_invFrame _ _ _ h3
  have f4 := processRegistryUpdates_invFrame _ _ _ h4
  have f5 := processSlashings_invFrame _ _ _ h5
  have f6 := processEth1DataReset_invFrame _ _ _ h6
  have f7 := processPendingDeposits_invFrame _ _ _ h7
  have f8 := processPendingConsolidations_invFrame _ _ _ h8
  have f10 := processEffectiveBalanceUpdates_invFrame _ _ _ h10
  have f11 := processSlashingsReset_invFrame _ _ _ h11
  have f12 := processRandaoMixesReset_invFrame _ _ _ h12
  have f13 := processHistoricalSummariesUpdate_invFrame _ _ _ h13
  have f14 := processParticipationFlagUpdates_invFrame _ _ _ h14
  have f15 := processSyncCommitteeUpdates_invFrame _ _ _ h15
  have f16 := processProposerLookahead_invFrame _ _ _ h16
  have f17 := processPtcWindow_invFrame _ _ _ h
  refine ⟨x8, x9, ?_, h9, ?_⟩
  · exact invFrame.trans f1 (invFrame.trans f2 (invFrame.trans f3 (invFrame.trans f4
      (invFrame.trans f5 (invFrame.trans f6 (invFrame.trans f7 f8))))))
  · exact invFrame.trans f10 (invFrame.trans f11 (invFrame.trans f12 (invFrame.trans f13
      (invFrame.trans f14 (invFrame.trans f15 (invFrame.trans f16 f17))))))

/-- An invariant of the slot loop: it is enough that one iteration (`process_slot`, then
`process_epoch` at an epoch boundary, then `slot := slot + 1`) keeps it. -/
theorem processSlots_ind {ctx : Ctx} (I : GSt P → Prop)
    (hstep : ∀ st st1 st2 : GSt P, ∀ next : U64, I st → InvFrame st st1 →
      next.toNat = st.slot.toNat + 1 →
      ((st2 = st1 ∧ next.toNat % P.SLOTS_PER_EPOCH ≠ 0) ∨
        (next.toNat % P.SLOTS_PER_EPOCH = 0 ∧ JauneConsensus.Gloas.processEpoch ctx st1 = .ok st2)) →
      I { st2 with slot := next })
    {s s' : GSt P} {slot : U64} (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s')
    (hI : I s) : I s' := by
  unfold JauneConsensus.Gloas.processSlots JauneConsensus.Gloas.processSlotsWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine range_forIn_inv I (fun a b x hb hx => ?_) hout hI
  obtain ⟨st1, h1, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨next, hn, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨r, hr, hx⟩ := bind_eq_ok_iff.mp hx
  have f1 := processSlot_invFrame _ _ h1
  have hnext : next.toNat = b.slot.toNat + 1 := by
    rw [U64.toNat_add? hn, f1.2.2.2.2.2.2.1]; rfl
  have hrn : r.toNat = next.toNat % P.SLOTS_PER_EPOCH := by
    rw [U64.toNat_mod? hr, U64.toNat_ofNat? hspe]
  simp only [] at hx
  split at hx
  · rename_i hz
    obtain ⟨st2, he, hx⟩ := bind_eq_ok_iff.mp hx
    cases hx
    refine hstep b st1 st2 next hb f1 hnext (Or.inr ⟨?_, he⟩)
    rw [← hrn]; simpa using hz
  · rename_i hz
    cases hx
    refine hstep b st1 st1 next hb f1 hnext (Or.inl ⟨rfl, ?_⟩)
    rw [← hrn]; simpa using hz

end JauneConsensus.Facts.Gloas.Inv
