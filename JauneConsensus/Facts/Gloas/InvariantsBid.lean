import JauneConsensus.Facts.Gloas.InvariantsGen

/-!
# G3-08: preservation (goal `eip8282-gloas-cross-layer-v1`, G3a)

**G3-08 LatestBidCoherence** holds after every Gloas block whatever the pre-state
(`processBlock_latestBidCoherence`): the bid is the block's, made at the block's slot (the
header's), on `latest_block_hash` (which nothing after the bid moves), by the self-builder or a
registered builder (the registry only grows). `process_slots` keeps it
(`processSlots_latestBidCoherence`), hence so does `state_transition`.
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-- The fields a block writes after its bid: none of `L`, `latest_block_hash`, the builders,
the slot, the header slot, the builder sweep index or the builder withdrawals. -/
theorem afterBid_core {ctx : Ctx} {s4 s5 s6 s7 s' : GSt P}
    {body : JauneConsensus.Gloas.BeaconBlockBody P} {ps : Slot}
    (h5 : JauneConsensus.Gloas.processRandao ctx s4 body = .ok s5)
    (h6 : JauneConsensus.Gloas.processEth1Data s5 body = .ok s6)
    (h7 : JauneConsensus.Gloas.processOperations ctx s6 body ps = .ok s7)
    (h8 : JauneConsensus.Gloas.processSyncAggregate ctx s7 body.sync_aggregate = .ok s') :
    CoreFrame s4 s' :=
  coreFrame.trans (coreFrame_of_inv (processRandao_invFrame _ _ _ _ h5))
    (coreFrame.trans (coreFrame_of_inv (processEth1Data_invFrame _ _ _ h6))
      (coreFrame.trans (processOperations_core _ _ _ _ _ h7)
        (coreFrame_of_inv (processSyncAggregate_invFrame _ _ _ _ h8))))

/-- The slot is fixed through a block, and the header slot is the block's slot from the header
on. -/
theorem processBlock_slots {ctx : Ctx} {s s' : GSt P} {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') :
    s'.slot = s.slot ∧ s'.latest_block_header.slot = s.slot := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  have hs1 : s1.slot = s.slot := by
    rcases processParentExecutionPayload_cases h1 with ⟨hs1, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
    · rw [hs1]
    · exact (parentFull_frame ha hd he hs).2.2.2.2.2
  obtain ⟨hbs, hhs, hm2⟩ := processBlockHeader_post h2
  have w3 := processWithdrawals_wFrame _ _ h3
  have b4 := processExecutionPayloadBid_post h4
  have c := afterBid_core h5 h6 h7 h8
  have hs2 : s2.slot = s1.slot := by rw [hm2]
  refine ⟨?_, ?_⟩
  · rw [c.2.2.2.2.1, b4.2.2.2.2.2.2.2.1, w3.2.2.2.1, hs2, hs1]
  · rw [c.2.2.2.1, b4.2.2.2.2.2.2.1, w3.2.2.1, hhs, hbs, hs1]

/-- **G3-08 over `process_block`** (from any pre-state). -/
theorem processBlock_latestBidCoherence {ctx : Ctx} {s s' : GSt P}
    {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') : LatestBidCoherence s' := by
  have hsl := processBlock_slots h
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  have b4 := processExecutionPayloadBid_post h4
  have c := afterBid_core h5 h6 h7 h8
  have w3 := processWithdrawals_wFrame _ _ h3
  obtain ⟨hL, hbslot, hpar, hwho, hb, hk, _, hs4, _⟩ := b4
  have hs3 : s3.slot = s.slot := by
    rw [← hsl.1, c.2.2.2.2.1, hs4]
  refine ⟨?_, ?_, Or.inl ?_⟩
  · rw [c.2.1, hL, hbslot, hs3, hsl.2]
  · rw [c.2.1, hL, c.1, hb]
    rcases hwho with ⟨hself, _⟩ | ⟨b, hbb, _, _⟩
    · exact Or.inl hself
    · exact Or.inr (Array.getElem?_eq_some_iff.mp hbb).1
  · rw [c.2.2.1, c.2.1, hL, hk, hpar]

/-- **G3-08 over `process_slots`.** -/
theorem processSlots_latestBidCoherence {ctx : Ctx} {s s' : GSt P} {slot : U64}
    (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s') (hu : LatestBidCoherence s) :
    LatestBidCoherence s' :=
  processSlots_ind (ctx := ctx) LatestBidCoherence
    (fun _ _ _ _ hI f1 _ hc => by
      obtain ⟨hb, hl, hk, hd, _⟩ := slotIter_core f1 hc
      obtain ⟨i1, i2, i3⟩ := hI
      exact ⟨by show _ = _; rw [hl, hd]; exact i1, by show _ ∨ _; rw [hl, hb]; exact i2,
        by show _ ∨ _; rw [hl, hk]; exact i3⟩) h hu

/-- **G3-08 over `state_transition`** (from any pre-state). -/
theorem stateTransition_latestBidCoherence {ctx : Ctx} {s s' : GSt P}
    {sb : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool}
    (h : JauneConsensus.Gloas.stateTransition ctx s sb v = .ok s') : LatestBidCoherence s' := by
  obtain ⟨m, _, hb⟩ := stateTransition_split h
  exact processBlock_latestBidCoherence hb

end JauneConsensus.Facts.Gloas.Inv
