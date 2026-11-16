import JauneConsensus.Facts.Gloas.InvariantsSweep

/-!
# `process_slots` for the G3 invariants (goal `eip8282-gloas-cross-layer-v1`, G3a)

* `processEpoch_phases`: `process_epoch` is the frame-keeping steps before
  `process_builder_pending_payments`, that step, and the frame-keeping steps after it;
* `processSlots_ind`: an invariant of the slot loop needs only one iteration: `process_slot`
  (which keeps `InvFrame`), at an epoch boundary `process_epoch`, then `slot := slot + 1`.
-/

namespace JauneConsensus.Facts.Gloas.Invariant

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

theorem range_forIn_invariant {β : Type} (I : β → Prop) {r : Std.Legacy.Range} {init out : β}
    {body : Nat → β → Fallible (ForInStep β)} (hb : ∀ a b x, I b → body a b = .ok x → I x.value)
    (h : forIn r init body = .ok out) (hI : I init) : I out := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact list_forIn_relation (fun a b => I a → I b) (fun _ h => h) (fun _ _ _ h1 h2 x => h2 (h1 x))
    body (fun a b x hx hIb => hb a b x hIb hx) _ init out h hI

theorem invariantFrame_of {α : Type} {c : Fallible α} {s : GloasState P} {x : α} {f : α → GloasState P}
    (hc : Ok c (fun r => invariantFrame.relation s (f r))) (h : c = .ok x) : InvariantFrame s (f x) := hc x h

/-- `process_epoch`: frame, `process_builder_pending_payments`, frame. -/
theorem processEpoch_phases {ctx : Ctx} {s s' : GloasState P}
    (h : JauneConsensus.Gloas.processEpoch ctx s = .ok s') :
    ∃ a b : GloasState P, InvariantFrame s a ∧
      JauneConsensus.Gloas.processBuilderPendingPayments ctx.config a = .ok b ∧ InvariantFrame b s' := by
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
  have f1 := processJustificationAndFinalization_invariantFrame _ _ _ h1
  have f2 := processInactivityUpdates_invariantFrame _ _ _ h2
  have f3 := processRewardsAndPenalties_invariantFrame _ _ _ h3
  have f4 := processRegistryUpdates_invariantFrame _ _ _ h4
  have f5 := processSlashings_invariantFrame _ _ _ h5
  have f6 := processEth1DataReset_invariantFrame _ _ _ h6
  have f7 := processPendingDeposits_invariantFrame _ _ _ h7
  have f8 := processPendingConsolidations_invariantFrame _ _ _ h8
  have f10 := processEffectiveBalanceUpdates_invariantFrame _ _ _ h10
  have f11 := processSlashingsReset_invariantFrame _ _ _ h11
  have f12 := processRandaoMixesReset_invariantFrame _ _ _ h12
  have f13 := processHistoricalSummariesUpdate_invariantFrame _ _ _ h13
  have f14 := processParticipationFlagUpdates_invariantFrame _ _ _ h14
  have f15 := processSyncCommitteeUpdates_invariantFrame _ _ _ h15
  have f16 := processProposerLookahead_invariantFrame _ _ _ h16
  have f17 := processPtcWindow_invariantFrame _ _ _ h
  refine ⟨x8, x9, ?_, h9, ?_⟩
  · exact invariantFrame.trans f1 (invariantFrame.trans f2 (invariantFrame.trans f3 (invariantFrame.trans f4
      (invariantFrame.trans f5 (invariantFrame.trans f6 (invariantFrame.trans f7 f8))))))
  · exact invariantFrame.trans f10 (invariantFrame.trans f11 (invariantFrame.trans f12 (invariantFrame.trans f13
      (invariantFrame.trans f14 (invariantFrame.trans f15 (invariantFrame.trans f16 f17))))))

/-- An invariant of the slot loop: it is enough that one iteration (`process_slot`, then
`process_epoch` at an epoch boundary, then `slot := slot + 1`) keeps it. -/
theorem processSlots_induction {ctx : Ctx} (I : GloasState P → Prop)
    (hstep : ∀ st st1 st2 : GloasState P, ∀ next : U64, I st → InvariantFrame st st1 →
      next.toNat = st.slot.toNat + 1 →
      ((st2 = st1 ∧ next.toNat % P.SLOTS_PER_EPOCH ≠ 0) ∨
        (next.toNat % P.SLOTS_PER_EPOCH = 0 ∧ JauneConsensus.Gloas.processEpoch ctx st1 = .ok st2)) →
      I { st2 with slot := next })
    {s s' : GloasState P} {slot : U64} (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s')
    (hI : I s) : I s' := by
  unfold JauneConsensus.Gloas.processSlots JauneConsensus.Gloas.processSlotsWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine range_forIn_invariant I (fun a b x hb hx => ?_) hout hI
  obtain ⟨st1, h1, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨next, hn, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨r, hr, hx⟩ := bind_eq_ok_iff.mp hx
  have f1 := processSlot_invariantFrame _ _ h1
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

end JauneConsensus.Facts.Gloas.Invariant
