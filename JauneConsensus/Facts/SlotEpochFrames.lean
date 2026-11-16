import JauneConsensus.Facts.AnchorInvCorpus

/-!
# Slot, Epoch, and Upgrade Frame & Window Lemmas (G1b Deliverable 2)

Reusable consensus-side characterizations for Blanc's cross-layer `S9` rows (`R-S9`, `H-S9`,
`C-S9`, `D-S9`) across `processSlot`, `processEpoch`, `processSlots`, `upgradeToFulu`,
`processBlock`, `stateTransition`, `jointTransitionAt`, and `jointStep` (Electra, Fulu, and
Electra → Fulu crossing):

1. **`R-S9` (`latest_block_header` & `parent_root`):**
   - `filledHeader` / `filledHeaderRoot` and the 5-field `BeaconBlockHeader` / `BeaconBlock`
     SSZ `hashTreeRoot` identity (`beaconBlockHeader_root_eq_block_root`);
   - `processSlots_latest_block_header` under the exact single-slot-or-nonzero-root guard
     `(slot.toNat = s.slot.toNat + 1 ∨ (s.latest_block_header.state_root = 0 → Ssz.hashTreeRoot s ≠ 0))`
     (reflecting the `0 : B256` sentinel in `processSlot` with pure FIPS 180-4 SHA-256);
   - Exact 3-case `parent_root` characterization across Electra → Fulu crossing from an arbitrary
     anchor (`jointStep_cross_parent_root`), same-fork `jointStep` (`jointStep_electra_parent_root`,
     `jointStep_fulu_parent_root`), post-step header characterization
     (`jointStep_post_header_and_filledRoot`), and fork-independent consecutive-step chaining
     (`jointStep_consecutive_parent_root`).
2. **`H-S9` (`latest_execution_payload_header` & `parent_hash` / `block_hash`):**
   - `payloadHeader`, `processExecutionPayload_parent_and_header`,
     `processBlock_execution_payload_hashes`, `stateTransition_execution_payload_hashes`,
     `upgradeToFulu` / `processSlots` preservation, and unified `jointStep_execution_payload_hashes`.
3. **`C-S9` (`pending_consolidations` epoch split, block split, and `processSlots` / crossing chains):**
   - `epochPreQueues`, `epochPostQueues`, `epochBeforeConsolidations`, `processEpoch_split_queues`;
   - `processBlock_pendingConsolidations` and `ConsolidationRun` explicit indexed trace
     (`processPendingConsolidations_full_law`);
   - `EpochConsolidationChain`, `processSlots_consolidations_chain`, and
     `jointStep_cross_consolidations_chain`.
4. **`D-S9` (`pending_deposits` epoch split, exiting-validator invariance, block split, and chains):**
   - `pendingDepositsList`, `applyPendingDeposit` / `foldlM` exiting-validator invariance
     (`foldlM_applyPendingDeposit_exiting_iff`);
   - `processBlock_pendingDeposits_split` separating `GENESIS_SLOT` bridge/excess entries from
     `blk.slot > 0` EIP-6110 deposit-request entries;
   - `EpochDepositChain`, `processSlots_pendingDeposits_chain`, and
     `jointStep_cross_pendingDeposits_chain`.

Nothing here edits a spec definition.
-/

namespace JauneConsensus.Facts

open JauneConsensus

variable {P : Preset} {f : CFork}

/-! ## Basic `U64` and `B256` helpers -/

theorem u64_eq_of_toNat_eq {a b : U64} (h : a.toNat = b.toNat) : a = b :=
  U64.ext_toNat h

theorem b256_beq_eq_true_iff (a b : Jaune.B256) : B256.beq a b = true ↔ a = b := by
  unfold B256.beq
  rw [beq_iff_eq]
  constructor
  · intro h
    have h' := congrArg Jaune.Bytes.toB256 h
    rwa [Jaune.B256.toB256_toBytes, Jaune.B256.toB256_toBytes] at h'
  · intro h; subst h; rfl

theorem b256_beq_eq_false_iff (a b : Jaune.B256) : B256.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, b256_beq_eq_true_iff]

private theorem toB256_replicate_zero_any :
    ∀ n : Nat, Jaune.Bytes.toB256 (List.replicate n 0) = (0 : Jaune.B256)
  | 0 => by decide
  | n + 1 => by rw [List.replicate_succ, Jaune.Bytes.toB256_zero_cons, toB256_replicate_zero_any n]

theorem toB256_replicate_zero : Jaune.Bytes.toB256 (List.replicate 32 0) = (0 : Jaune.B256) :=
  toB256_replicate_zero_any 32

/-! ## Section 1 (`R-S9`): `filledHeader`, `filledHeaderRoot`, `processSlots`, `jointStep` -/

/-- Header produced when `process_slot` fills a zero `state_root` with `hash_tree_root(s)`. -/
def filledHeader (s : BeaconState P f) : BeaconBlockHeader :=
  if B256.beq s.latest_block_header.state_root (0 : Jaune.B256) then
    { s.latest_block_header with state_root := Ssz.hashTreeRoot s }
  else
    s.latest_block_header

/-- SSZ root of `filledHeader s`. -/
def filledHeaderRoot (s : BeaconState P f) : Root :=
  Ssz.hashTreeRoot (filledHeader s)

theorem filledHeader_of_zero {s : BeaconState P f}
    (h : s.latest_block_header.state_root = (0 : Jaune.B256)) :
    filledHeader s = { s.latest_block_header with state_root := Ssz.hashTreeRoot s } := by
  unfold filledHeader
  have hb : B256.beq s.latest_block_header.state_root (0 : Jaune.B256) = true :=
    (b256_beq_eq_true_iff _ _).mpr h
  rw [hb]; rfl

theorem filledHeader_of_nonzero {s : BeaconState P f}
    (h : s.latest_block_header.state_root ≠ (0 : Jaune.B256)) :
    filledHeader s = s.latest_block_header := by
  unfold filledHeader
  have hb : B256.beq s.latest_block_header.state_root (0 : Jaune.B256) = false :=
    (b256_beq_eq_false_iff _ _).mpr h
  rw [hb]; rfl

theorem filledHeader_state_root_ne_zero {s : BeaconState P f}
    (h : s.latest_block_header.state_root = (0 : Jaune.B256) →
         Ssz.hashTreeRoot s ≠ (0 : Jaune.B256)) :
    (filledHeader s).state_root ≠ (0 : Jaune.B256) := by
  by_cases hz : s.latest_block_header.state_root = (0 : Jaune.B256)
  · rw [filledHeader_of_zero hz]
    exact h hz
  · rw [filledHeader_of_nonzero hz]
    exact hz

/-- A `BeaconBlockHeader` with `body_root := Ssz.hashTreeRoot blk.body` and the other four fields
copied from `blk` has the exact same SSZ `hashTreeRoot` as `blk`. -/
theorem beaconBlockHeader_root_eq_block_root (blk : BeaconBlock P f) :
    Ssz.hashTreeRoot ({ slot := blk.slot,
                        proposer_index := blk.proposer_index,
                        parent_root := blk.parent_root,
                        state_root := blk.state_root,
                        body_root := Ssz.hashTreeRoot blk.body } : BeaconBlockHeader) =
      Ssz.hashTreeRoot blk := rfl

theorem processSlot_slot_and_header {s s' : BeaconState P f}
    (h : processSlot s = .ok s') :
    s'.slot = s.slot ∧ s'.latest_block_header = filledHeader s := by
  unfold processSlot at h
  unfold filledHeader
  generalize Ssz.hashTreeRoot s = prevStateRoot at h ⊢
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact ⟨by split <;> rfl, by split <;> rfl⟩

/-- Uniform loop extraction from `processSlots`: `s.slot < slot` and an abstract loop `body` over
`List.range' 0 (slot.toNat - s.slot.toNat)` whose each iteration runs `processSlot`, optionally
`processEpoch ctx`, and sets `slot := next` with `next.toNat = st.slot.toNat + 1`. -/
private theorem processSlots_loop_ok {ctx : Ctx} {s s' : BeaconState P f} {slot : Slot}
    (h : processSlots ctx s slot = .ok s') :
    s.slot < slot ∧
    ∃ (body : Nat → BeaconState P f → M (ForInStep (BeaconState P f))),
      forIn (List.range' 0 (slot.toNat - s.slot.toNat)) s body = .ok s' ∧
      ∀ k st r, body k st = .ok r →
        ∃ st1 next st2,
          processSlot st = .ok st1 ∧
          next.toNat = st.slot.toNat + 1 ∧
          (st2 = st1 ∨ processEpoch ctx st1 = .ok st2) ∧
          r = .yield { st2 with slot := next } := by
  unfold processSlots processSlotsWith at h
  obtain ⟨_, hreq, h⟩ := bind_eq_ok_iff.mp h
  have hlt : s.slot < slot := of_decide_eq_true (require_eq_ok_iff.mp hreq)
  obtain ⟨slotsPerEpoch, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s_out, hloop, hpure⟩ := bind_eq_ok_iff.mp h
  have hs_eq : s_out = s' := Except.ok.inj hpure
  rw [hs_eq] at hloop
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop
  have hsz : [:slot.toNat - s.slot.toNat].size = slot.toNat - s.slot.toNat := by
    simp [Std.Legacy.Range.size]
  dsimp only [] at hloop
  rw [hsz] at hloop
  refine ⟨hlt, _, hloop, fun _ st r hr => ?_⟩
  obtain ⟨st1, hslot, hr⟩ := bind_eq_ok_iff.mp hr
  obtain ⟨hsl1, _⟩ := processSlot_slot_and_header hslot
  obtain ⟨next, hnext, hr⟩ := bind_eq_ok_iff.mp hr
  have hn : next.toNat = st.slot.toNat + 1 := by
    rw [U64.toNat_add? hnext, hsl1]; rfl
  obtain ⟨rem, _, hr⟩ := bind_eq_ok_iff.mp hr
  split at hr
  · obtain ⟨st2, hep, hr⟩ := bind_eq_ok_iff.mp hr
    have hr_eq : ForInStep.yield { st2 with slot := next } = r := Except.ok.inj hr
    exact ⟨st1, next, st2, hslot, hn, Or.inr hep, hr_eq.symm⟩
  · have hr_eq : ForInStep.yield { st1 with slot := next } = r := Except.ok.inj hr
    exact ⟨st1, next, st1, hslot, hn, Or.inl rfl, hr_eq.symm⟩

private theorem body_step_header (hf : f.atLeast .electra = true) (ctx : Ctx)
    {body : Nat → BeaconState P f → M (ForInStep (BeaconState P f))}
    (hb : ∀ k st r, body k st = .ok r →
      ∃ st1 next st2,
        processSlot st = .ok st1 ∧
        next.toNat = st.slot.toNat + 1 ∧
        (st2 = st1 ∨ processEpoch ctx st1 = .ok st2) ∧
        r = .yield { st2 with slot := next })
    {k : Nat} {st : BeaconState P f} {r : ForInStep (BeaconState P f)}
    (hr : body k st = .ok r) :
    ∃ st', r = .yield st' ∧
      st'.slot.toNat = st.slot.toNat + 1 ∧
      st'.latest_block_header = filledHeader st := by
  obtain ⟨st1, next, st2, hslot, hn, hep_or, rfl⟩ := hb k st r hr
  obtain ⟨_, hhdr1⟩ := processSlot_slot_and_header hslot
  rcases hep_or with rfl | hep
  · exact ⟨_, rfl, hn, hhdr1⟩
  · have hep_fr := processEpoch_cpres_and_frame hf ctx hep
    exact ⟨_, rfl, hn, hep_fr.2.2.1.trans hhdr1⟩

private theorem range'_forIn_slot_only (hf : f.atLeast .electra = true) (ctx : Ctx)
    {body : Nat → BeaconState P f → M (ForInStep (BeaconState P f))}
    (hb : ∀ k st r, body k st = .ok r →
      ∃ st1 next st2,
        processSlot st = .ok st1 ∧
        next.toNat = st.slot.toNat + 1 ∧
        (st2 = st1 ∨ processEpoch ctx st1 = .ok st2) ∧
        r = .yield { st2 with slot := next }) :
    ∀ (n start : Nat) (cur out : BeaconState P f),
      forIn (List.range' start n) cur body = .ok out →
      out.slot.toNat = cur.slot.toNat + n
  | 0, _, cur, out, h => by
    have heq : cur = out := Except.ok.inj h
    rw [heq]; omega
  | n + 1, start, cur, out, h => by
    rw [List.range'_succ, List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨st1, rfl, hslot1, _⟩ := body_step_header hf ctx hb hr
    have hsl := range'_forIn_slot_only hf ctx hb n (start + 1) st1 out h
    omega

private theorem range'_forIn_slot_and_nonzero_header (hf : f.atLeast .electra = true) (ctx : Ctx)
    {body : Nat → BeaconState P f → M (ForInStep (BeaconState P f))}
    (hb : ∀ k st r, body k st = .ok r →
      ∃ st1 next st2,
        processSlot st = .ok st1 ∧
        next.toNat = st.slot.toNat + 1 ∧
        (st2 = st1 ∨ processEpoch ctx st1 = .ok st2) ∧
        r = .yield { st2 with slot := next }) :
    ∀ (n start : Nat) (cur out : BeaconState P f),
      cur.latest_block_header.state_root ≠ (0 : Jaune.B256) →
      forIn (List.range' start n) cur body = .ok out →
      out.slot.toNat = cur.slot.toNat + n ∧
      out.latest_block_header = cur.latest_block_header
  | 0, _, cur, out, _, h => by
    have heq : cur = out := Except.ok.inj h
    subst heq
    exact ⟨Nat.add_zero _, rfl⟩
  | n + 1, start, cur, out, hnz, h => by
    rw [List.range'_succ, List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨st1, rfl, hslot1, hhdr1⟩ := body_step_header hf ctx hb hr
    rw [filledHeader_of_nonzero hnz] at hhdr1
    have hnz1 : st1.latest_block_header.state_root ≠ (0 : Jaune.B256) := by
      rw [hhdr1]; exact hnz
    obtain ⟨hsl_rest, hhdr_rest⟩ :=
      range'_forIn_slot_and_nonzero_header hf ctx hb n (start + 1) st1 out hnz1 h
    exact ⟨by omega, hhdr_rest.trans hhdr1⟩

/-- Unconditional slot postcondition of `processSlots` at Electra/Fulu: `s.slot < slot` and
`s'.slot = slot`. -/
theorem processSlots_slot (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {slot : Slot}
    (h : processSlots ctx s slot = .ok s') :
    s.slot < slot ∧ s'.slot = slot := by
  obtain ⟨hlt, body, hloop, hb⟩ := processSlots_loop_ok h
  have hsl := range'_forIn_slot_only hf ctx hb (slot.toNat - s.slot.toNat) 0 s s' hloop
  have hlt_nat : s.slot.toNat < slot.toNat := hlt
  exact ⟨hlt, u64_eq_of_toNat_eq (by omega)⟩

/-- When `s.latest_block_header.state_root ≠ 0`, `processSlots` preserves `latest_block_header`
unconditionally across any number of slots. -/
theorem processSlots_header_of_nonzero (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {slot : Slot}
    (hnz : s.latest_block_header.state_root ≠ (0 : Jaune.B256))
    (h : processSlots ctx s slot = .ok s') :
    s.slot < slot ∧ s'.slot = slot ∧ s'.latest_block_header = s.latest_block_header := by
  obtain ⟨hlt, body, hloop, hb⟩ := processSlots_loop_ok h
  obtain ⟨hsl, hhdr⟩ :=
    range'_forIn_slot_and_nonzero_header hf ctx hb (slot.toNat - s.slot.toNat) 0 s s' hnz hloop
  have hlt_nat : s.slot.toNat < slot.toNat := hlt
  exact ⟨hlt, u64_eq_of_toNat_eq (by omega), hhdr⟩

/-- **`R-S9` `processSlots` `latest_block_header` characterization:**
Under the single-slot-or-nonzero-root guard
`(slot.toNat = s.slot.toNat + 1 ∨ (s.latest_block_header.state_root = 0 → Ssz.hashTreeRoot s ≠ 0))`,
`processSlots` advances `s.slot` to `slot` and leaves `s'.latest_block_header = filledHeader s`
(hence `Ssz.hashTreeRoot s'.latest_block_header = filledHeaderRoot s`). -/
theorem processSlots_latest_block_header (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {slot : Slot}
    (hguard : slot.toNat = s.slot.toNat + 1 ∨
      (s.latest_block_header.state_root = (0 : Jaune.B256) →
        Ssz.hashTreeRoot s ≠ (0 : Jaune.B256)))
    (h : processSlots ctx s slot = .ok s') :
    s.slot < slot ∧
    s'.slot = slot ∧
    s'.latest_block_header = filledHeader s ∧
    Ssz.hashTreeRoot s'.latest_block_header = filledHeaderRoot s := by
  obtain ⟨hlt, body, hloop, hb⟩ := processSlots_loop_ok h
  have hlt_nat : s.slot.toNat < slot.toNat := hlt
  obtain ⟨m, hm⟩ : ∃ m, slot.toNat - s.slot.toNat = m + 1 := ⟨slot.toNat - s.slot.toNat - 1, by omega⟩
  rw [hm, List.range'_succ, List.forIn_cons] at hloop
  obtain ⟨r, hr, hloop⟩ := bind_eq_ok_iff.mp hloop
  obtain ⟨st1, rfl, hslot1, hhdr1⟩ := body_step_header hf ctx hb hr
  rcases hguard with h1 | hnz_imp
  · have hm0 : m = 0 := by omega
    subst hm0
    have hst1_eq : st1 = s' := Except.ok.inj hloop
    rw [hst1_eq] at hslot1 hhdr1
    have hsl_eq : s'.slot = slot := u64_eq_of_toNat_eq (by omega)
    exact ⟨hlt, hsl_eq, hhdr1, congrArg Ssz.hashTreeRoot hhdr1⟩
  · have hnz1 : st1.latest_block_header.state_root ≠ (0 : Jaune.B256) := by
      rw [hhdr1]
      exact filledHeader_state_root_ne_zero hnz_imp
    obtain ⟨hsl_rest, hhdr_rest⟩ :=
      range'_forIn_slot_and_nonzero_header hf ctx hb m 1 st1 s' hnz1 hloop
    have hsl_eq : s'.slot = slot := u64_eq_of_toNat_eq (by omega)
    have hhdr_eq : s'.latest_block_header = filledHeader s := hhdr_rest.trans hhdr1
    exact ⟨hlt, hsl_eq, hhdr_eq, congrArg Ssz.hashTreeRoot hhdr_eq⟩

/-- Exact specification of `processBlockHeader` on `slot`, `parent_root`, and `latest_block_header`. -/
theorem processBlockHeader_spec {s s' : BeaconState P f} {blk : BeaconBlock P f}
    (h : processBlockHeader s blk = .ok s') :
    blk.slot = s.slot ∧
    s.latest_block_header.slot < blk.slot ∧
    0 < blk.slot.toNat ∧
    blk.parent_root = Ssz.hashTreeRoot s.latest_block_header ∧
    s'.slot = blk.slot ∧
    s'.latest_block_header =
      { slot := blk.slot,
        proposer_index := blk.proposer_index,
        parent_root := blk.parent_root,
        state_root := (0 : Jaune.B256),
        body_root := Ssz.hashTreeRoot blk.body } := by
  unfold processBlockHeader at h
  obtain ⟨_, hreq1, h⟩ := bind_eq_ok_iff.mp h
  have hsl : blk.slot = s.slot := beq_iff_eq.mp (require_eq_ok_iff.mp hreq1)
  obtain ⟨_, hreq2, h⟩ := bind_eq_ok_iff.mp h
  have hnewer : s.latest_block_header.slot < blk.slot :=
    of_decide_eq_true (require_eq_ok_iff.mp hreq2)
  have hpos : 0 < blk.slot.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hnewer
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, hreq4, h⟩ := bind_eq_ok_iff.mp h
  have hpr : blk.parent_root = Ssz.hashTreeRoot s.latest_block_header :=
    beq_iff_eq.mp (require_eq_ok_iff.mp hreq4)
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  have hs'_eq := (Except.ok.inj h).symm
  refine ⟨hsl, hnewer, hpos, hpr, ?_, ?_⟩
  · rw [hs'_eq]; exact hsl.symm
  · rw [hs'_eq, toB256_replicate_zero]

/-- Across `processBlock`, `blk.parent_root` equals `Ssz.hashTreeRoot s.latest_block_header`,
`0 < blk.slot.toNat`, `s'.slot = blk.slot`, and `s'.latest_block_header` is `blk`'s header with
unfilled `state_root = 0`. -/
theorem processBlock_latest_block_header (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {blk : BeaconBlock P f}
    (h : processBlock ctx s blk = .ok s') :
    blk.slot = s.slot ∧
    s.latest_block_header.slot < blk.slot ∧
    0 < blk.slot.toNat ∧
    blk.parent_root = Ssz.hashTreeRoot s.latest_block_header ∧
    s'.slot = blk.slot ∧
    s'.latest_block_header =
      { slot := blk.slot,
        proposer_index := blk.proposer_index,
        parent_root := blk.parent_root,
        state_root := (0 : Jaune.B256),
        body_root := Ssz.hashTreeRoot blk.body } := by
  unfold processBlock processBlockWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h7⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hsl, hnewer, hpos, hpr, hsl1, hhdr1⟩ := processBlockHeader_spec h1
  have c2 := processWithdrawals_csub h2
  have c3 := processExecutionPayload_corpusPres ctx h3
  have c4 := processRandao_csub ctx h4
  have c5 := processEth1Data_csub h5
  rw [processOperations_split_all ctx s5 blk.body hf] at h6
  obtain ⟨o1, ho1, h6⟩ := bind_eq_ok_iff.mp h6
  obtain ⟨o2, ho2, h6⟩ := bind_eq_ok_iff.mp h6
  obtain ⟨o3, ho3, ho4⟩ := bind_eq_ok_iff.mp h6
  have co1 := preDeposits_cpres_and_frame hf ctx ho1
  obtain ⟨_, _, hfr_o2⟩ := foldDepositRequests_spec hf _ ho2
  have co3 := foldWithdrawalRequests_csub ctx.cfg ho3
  obtain ⟨_, _, _, hsl_o4, _, hlbh_o4, _, _, _, _, _, _, _⟩ :=
    foldConsolidationRequests_frames_and_queues hf ctx.cfg _ ho4
  have c7 := processSyncAggregate_csub ctx h7
  have hsl_o2 : o2.slot = o1.slot := by rw [hfr_o2]
  have hlbh_o2 : o2.latest_block_header = o1.latest_block_header := by rw [hfr_o2]
  have hsl_all : s'.slot = s1.slot := by
    rw [c7.slot_eq, hsl_o4, co3.slot_eq, hsl_o2, co1.2.1, c5.slot_eq, c4.slot_eq, c3.2.1, c2.slot_eq]
  have hlbh_all : s'.latest_block_header = s1.latest_block_header := by
    rw [c7.lbh_eq, hlbh_o4, co3.lbh_eq, hlbh_o2, co1.2.2.1, c5.lbh_eq, c4.lbh_eq, c3.2.2.1, c2.lbh_eq]
  exact ⟨hsl, hnewer, hpos, hpr, hsl_all.trans hsl1, hlbh_all.trans hhdr1⟩

/-- Decomposition of `stateTransition` with `validateResult = true` (the default used by `jointStep`). -/
theorem stateTransition_true_split {ctx : Ctx} {s s' : BeaconState P f}
    {sb : SignedBeaconBlock P f}
    (h : stateTransition ctx s sb true = .ok s') :
    ∃ mid,
      processSlots ctx s sb.message.slot = .ok mid ∧
      processBlock ctx mid sb.message = .ok s' ∧
      sb.message.state_root = Ssz.hashTreeRoot s' := by
  unfold stateTransition stateTransitionWith at h
  obtain ⟨mid, hps, h⟩ := bind_eq_ok_iff.mp h
  simp only [ite_true] at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, hpb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, hsr, h⟩ := bind_eq_ok_iff.mp h
  have hroot : sb.message.state_root = Ssz.hashTreeRoot s2 :=
    (b256_beq_eq_true_iff _ _).mp (require_eq_ok_iff.mp hsr)
  have hs2 : s2 = s' := Except.ok.inj h
  exact ⟨mid, hps, hs2 ▸ hpb, hs2 ▸ hroot⟩

/-- Decomposition of the at-slot block verification & application branch in crossing `jointStep`. -/
theorem atSlot_block_split {ctx : Ctx} {bls : Bool} {s s' : BeaconState P f}
    {sb : SignedBeaconBlock P f}
    (h : (do require (← verifyBlockSignature bls s sb) "state_transition: verify_block_signature"
             let s ← processBlock ctx s sb.message
             require (B256.beq sb.message.state_root (Ssz.hashTreeRoot s))
               "state_transition: block.state_root"
             pure s) = .ok s') :
    processBlock ctx s sb.message = .ok s' ∧
    sb.message.state_root = Ssz.hashTreeRoot s' := by
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, hpb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, hsr, h⟩ := bind_eq_ok_iff.mp h
  have hroot : sb.message.state_root = Ssz.hashTreeRoot s2 :=
    (b256_beq_eq_true_iff _ _).mp (require_eq_ok_iff.mp hsr)
  have hs2 : s2 = s' := Except.ok.inj h
  exact ⟨hs2 ▸ hpb, hs2 ▸ hroot⟩

/-- Helper: after `processBlock` + state-root verification, `filledHeader s'` is `blk`'s 5-field
header and `filledHeaderRoot s' = Ssz.hashTreeRoot blk`. -/
theorem postBlock_filledHeaderRoot (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {blk : BeaconBlock P f}
    (hpb : processBlock ctx s blk = .ok s')
    (hsr : blk.state_root = Ssz.hashTreeRoot s') :
    s'.slot = blk.slot ∧
    s'.latest_block_header.slot = blk.slot ∧
    s'.latest_block_header.state_root = (0 : Jaune.B256) ∧
    filledHeader s' =
      { slot := blk.slot,
        proposer_index := blk.proposer_index,
        parent_root := blk.parent_root,
        state_root := blk.state_root,
        body_root := Ssz.hashTreeRoot blk.body } ∧
    filledHeaderRoot s' = Ssz.hashTreeRoot blk := by
  obtain ⟨_, _, _, _, hsl, hhdr⟩ := processBlock_latest_block_header hf ctx hpb
  have hz : s'.latest_block_header.state_root = (0 : Jaune.B256) := by rw [hhdr]
  have hfh0 : filledHeader s' = { s'.latest_block_header with state_root := Ssz.hashTreeRoot s' } :=
    filledHeader_of_zero hz
  have hfh : filledHeader s' =
      { slot := blk.slot,
        proposer_index := blk.proposer_index,
        parent_root := blk.parent_root,
        state_root := blk.state_root,
        body_root := Ssz.hashTreeRoot blk.body } := by
    refine hfh0.trans ?_
    generalize Ssz.hashTreeRoot s' = sr at hsr ⊢
    rw [hhdr, hsr]
  refine ⟨hsl, by rw [hhdr], hz, hfh, ?_⟩
  unfold filledHeaderRoot
  rw [hfh, beaconBlockHeader_root_eq_block_root]

open Jaune in
/-- **Unconditional post-step header & `filledHeaderRoot` identity across any `jointStep`:**
for every accepted `jointStep cfg ccfg bls s b = .ok s'`, `s'.beacon.slot = b.2.message.slot`,
`Ssz.hashTreeRoot s'.beacon = b.2.message.state_root`,
`s'.beacon.latest_block_header.state_root = 0`, and
`filledHeaderRoot s'.beacon = Ssz.hashTreeRoot b.2.message`. -/
theorem jointStep_post_header_and_filledRoot {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') :
    s'.beacon.slot = b.2.message.slot ∧
    Ssz.hashTreeRoot s'.beacon = b.2.message.state_root ∧
    s'.beacon.latest_block_header.slot = b.2.message.slot ∧
    s'.beacon.latest_block_header.state_root = (0 : Jaune.B256) ∧
    filledHeaderRoot s'.beacon = Ssz.hashTreeRoot b.2.message := by
  obtain ⟨fs, beacon, exec⟩ := s
  obtain ⟨fb, sb⟩ := b
  cases fs <;> cases fb
  case electra.electra =>
    obtain ⟨_, _, b', e', _, _, hst, rfl⟩ := jointStep_electra_ok_iff.mp h
    obtain ⟨mid, _, hpb, hsr⟩ := stateTransition_true_split hst
    obtain ⟨hsl, hhl, hz, _, hfr⟩ := postBlock_filledHeaderRoot rfl _ hpb hsr
    exact ⟨hsl, hsr.symm, hhl, hz, hfr⟩
  case fulu.fulu =>
    obtain ⟨_, b', e', _, _, hst, rfl⟩ := jointStep_fulu_ok_iff.mp h
    obtain ⟨mid, _, hpb, hsr⟩ := stateTransition_true_split hst
    obtain ⟨hsl, hhl, hz, _, hfr⟩ := postBlock_filledHeaderRoot rfl _ hpb hsr
    exact ⟨hsl, hsr.symm, hhl, hz, hfr⟩
  case electra.fulu =>
    obtain ⟨_, _, _, _, b1, b2, b', e', _, _, _, _, _, hb', rfl⟩ := jointStep_cross_ok_iff.mp h
    split at hb'
    · obtain ⟨hpb, hsr⟩ := atSlot_block_split hb'
      obtain ⟨hsl, hhl, hz, _, hfr⟩ := postBlock_filledHeaderRoot rfl _ hpb hsr
      exact ⟨hsl, hsr.symm, hhl, hz, hfr⟩
    · obtain ⟨mid, _, hpb, hsr⟩ := stateTransition_true_split hb'
      obtain ⟨hsl, hhl, hz, _, hfr⟩ := postBlock_filledHeaderRoot rfl _ hpb hsr
      exact ⟨hsl, hsr.symm, hhl, hz, hfr⟩
  all_goals (unfold jointStep at h; cases h)

open Jaune in
/-- **`R-S9` same-fork Electra `parent_root`:** -/
theorem jointStep_electra_parent_root {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .electra}
    {s' : JointState P}
    (hguard : sb.message.slot.toNat = beacon.slot.toNat + 1 ∨
      (beacon.latest_block_header.state_root = (0 : B256) →
        Ssz.hashTreeRoot beacon ≠ (0 : B256)))
    (h : jointStep cfg ccfg bls ⟨.electra, beacon, exec⟩ ⟨.electra, sb⟩ = .ok s') :
    beacon.slot < sb.message.slot ∧
    sb.message.parent_root = filledHeaderRoot beacon := by
  obtain ⟨_, _, b', _, _, _, hst, _⟩ := jointStep_electra_ok_iff.mp h
  obtain ⟨mid, hps, hpb, _⟩ := stateTransition_true_split hst
  obtain ⟨hlt, _, _, hroot⟩ := processSlots_latest_block_header rfl _ hguard hps
  obtain ⟨_, _, _, hpr, _, _⟩ := processBlock_latest_block_header rfl _ hpb
  exact ⟨hlt, hpr.trans hroot⟩

open Jaune in
/-- **`R-S9` same-fork Fulu `parent_root`:** -/
theorem jointStep_fulu_parent_root {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .fulu} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
    {s' : JointState P}
    (hguard : sb.message.slot.toNat = beacon.slot.toNat + 1 ∨
      (beacon.latest_block_header.state_root = (0 : B256) →
        Ssz.hashTreeRoot beacon ≠ (0 : B256)))
    (h : jointStep cfg ccfg bls ⟨.fulu, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok s') :
    beacon.slot < sb.message.slot ∧
    sb.message.parent_root = filledHeaderRoot beacon := by
  obtain ⟨_, b', _, _, _, hst, _⟩ := jointStep_fulu_ok_iff.mp h
  obtain ⟨mid, hps, hpb, _⟩ := stateTransition_true_split hst
  obtain ⟨hlt, _, _, hroot⟩ := processSlots_latest_block_header rfl _ hguard hps
  obtain ⟨_, _, _, hpr, _, _⟩ := processBlock_latest_block_header rfl _ hpb
  exact ⟨hlt, hpr.trans hroot⟩

open Jaune in
/-- **`R-S9` 3-case Electra → Fulu crossing `parent_root` characterization** from an arbitrary
anchor state `beacon`:
- **(a) `beacon.slot < forkSlot`:** under `sb.message.slot.toNat = beacon.slot.toNat + 1 ∨
  (beacon.latest_block_header.state_root = 0 → Ssz.hashTreeRoot beacon ≠ 0)`,
  `sb.message.parent_root = filledHeaderRoot beacon`;
- **(b) `beacon.slot = forkSlot` and `sb.message.slot = forkSlot`:** no `processSlots` runs, and
  `sb.message.parent_root = Ssz.hashTreeRoot beacon.latest_block_header`;
- **(c) `beacon.slot = forkSlot` and `forkSlot < sb.message.slot`:** `upgradeToFulu ccfg beacon`
  produces `upgraded`, and under `sb.message.slot.toNat = upgraded.slot.toNat + 1 ∨
  (upgraded.latest_block_header.state_root = 0 → Ssz.hashTreeRoot upgraded ≠ 0)`,
  `sb.message.parent_root = filledHeaderRoot upgraded`. -/
theorem jointStep_cross_parent_root {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
    {s' : JointState P}
    (h : jointStep cfg ccfg bls ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok s') :
    ∃ (forkSlot : Slot),
      forkSlot.toNat = fuluForkSlot (P := P) ccfg ∧
      beacon.slot ≤ forkSlot ∧
      forkSlot ≤ sb.message.slot ∧
      ((beacon.slot < forkSlot ∧
          (sb.message.slot.toNat = beacon.slot.toNat + 1 ∨
            (beacon.latest_block_header.state_root = (0 : B256) →
              Ssz.hashTreeRoot beacon ≠ (0 : B256)) →
            sb.message.parent_root = filledHeaderRoot beacon)) ∨
       (beacon.slot = forkSlot ∧ sb.message.slot = forkSlot ∧
          sb.message.parent_root = Ssz.hashTreeRoot beacon.latest_block_header) ∨
       (beacon.slot = forkSlot ∧ forkSlot < sb.message.slot ∧
          ∃ upgraded, upgradeToFulu ccfg beacon = .ok upgraded ∧
            (sb.message.slot.toNat = upgraded.slot.toNat + 1 ∨
              (upgraded.latest_block_header.state_root = (0 : B256) →
                Ssz.hashTreeRoot upgraded ≠ (0 : B256)) →
              sb.message.parent_root = filledHeaderRoot upgraded))) := by
  obtain ⟨hle1, hle2, _, forkSlot, b1, b2, b', _, hfslot, hb1, hup, _, _, hb', _⟩ :=
    jointStep_cross_ok_iff.mp h
  have hfslot_nat : forkSlot.toNat = fuluForkSlot (P := P) ccfg := U64.toNat_ofNat? hfslot
  have hle1' : beacon.slot ≤ forkSlot := by show beacon.slot.toNat ≤ forkSlot.toNat; omega
  have hle2' : forkSlot ≤ sb.message.slot := by show forkSlot.toNat ≤ sb.message.slot.toNat; omega
  have hup_fr := upgradeToFulu_cpres_and_frame ccfg hup
  refine ⟨forkSlot, hfslot_nat, hle1', hle2', ?_⟩
  by_cases hlt : beacon.slot < forkSlot
  · left
    rw [ite_eq_left hlt] at hb1
    refine ⟨hlt, fun hguard => ?_⟩
    have hlt_nat : beacon.slot.toNat < forkSlot.toNat := hlt
    rcases hguard with h1 | hnz_imp
    · have hfs_eq : forkSlot.toNat = beacon.slot.toNat + 1 := by omega
      obtain ⟨_, hsl_b1, hhdr_b1, hroot_b1⟩ :=
        processSlots_latest_block_header rfl _ (Or.inl hfs_eq) hb1
      have hsb_eq_b2 : (sb.message.slot == b2.slot) = true := by
        apply beq_iff_eq.mpr
        apply u64_eq_of_toNat_eq
        have : b2.slot = forkSlot := hup_fr.2.2.2.1.trans hsl_b1
        rw [this]
        omega
      rw [ite_eq_left hsb_eq_b2] at hb'
      obtain ⟨hpb, _⟩ := atSlot_block_split hb'
      obtain ⟨_, _, _, hpr, _, _⟩ := processBlock_latest_block_header rfl _ hpb
      rw [hpr, hup_fr.2.2.2.2.1, hroot_b1]
    · obtain ⟨_, hsl_b1, hhdr_b1, hroot_b1⟩ :=
        processSlots_latest_block_header rfl _ (Or.inr hnz_imp) hb1
      have hnz_b2 : b2.latest_block_header.state_root ≠ (0 : B256) := by
        rw [hup_fr.2.2.2.2.1, hhdr_b1]
        exact filledHeader_state_root_ne_zero hnz_imp
      by_cases hat : (sb.message.slot == b2.slot) = true
      · rw [ite_eq_left hat] at hb'
        obtain ⟨hpb, _⟩ := atSlot_block_split hb'
        obtain ⟨_, _, _, hpr, _, _⟩ := processBlock_latest_block_header rfl _ hpb
        rw [hpr, hup_fr.2.2.2.2.1, hroot_b1]
      · rw [ite_eq_right hat] at hb'
        obtain ⟨mid, hps2, hpb, _⟩ := stateTransition_true_split hb'
        obtain ⟨_, _, hhdr_mid⟩ := processSlots_header_of_nonzero rfl _ hnz_b2 hps2
        obtain ⟨_, _, _, hpr, _, _⟩ := processBlock_latest_block_header rfl _ hpb
        rw [hpr, hhdr_mid, hup_fr.2.2.2.2.1, hroot_b1]
  · right
    rw [ite_eq_right hlt] at hb1
    cases hb1
    have hlt_not : ¬ beacon.slot.toNat < forkSlot.toNat := hlt
    have hbs_eq : beacon.slot = forkSlot := u64_eq_of_toNat_eq (by omega)
    by_cases hat : (sb.message.slot == b2.slot) = true
    · left
      have hsb_eq : sb.message.slot = forkSlot :=
        (beq_iff_eq.mp hat).trans (hup_fr.2.2.2.1.trans hbs_eq)
      rw [ite_eq_left hat] at hb'
      obtain ⟨hpb, _⟩ := atSlot_block_split hb'
      obtain ⟨_, _, _, hpr, _, _⟩ := processBlock_latest_block_header rfl _ hpb
      rw [hup_fr.2.2.2.2.1] at hpr
      exact ⟨hbs_eq, hsb_eq, hpr⟩
    · right
      rw [ite_eq_right hat] at hb'
      obtain ⟨mid, hps2, hpb, _⟩ := stateTransition_true_split hb'
      obtain ⟨hlt2, _⟩ := processSlots_slot rfl _ hps2
      have hfs_lt : forkSlot < sb.message.slot := by
        rw [← hbs_eq, ← hup_fr.2.2.2.1]
        exact hlt2
      refine ⟨hbs_eq, hfs_lt, b2, hup, fun hguard => ?_⟩
      obtain ⟨_, _, _, hroot2⟩ := processSlots_latest_block_header rfl _ hguard hps2
      obtain ⟨_, _, _, hpr, _, _⟩ := processBlock_latest_block_header rfl _ hpb
      exact hpr.trans hroot2

open Jaune in
/-- **`R-S9` consecutive `jointStep` `parent_root` theorem (all fork pairs, including crossing):**
Whenever `jointStep cfg ccfg bls s₀ b₁ = .ok s₁` and `jointStep cfg ccfg bls s₁ b₂ = .ok s₂`
under `(b₂.2.message.slot.toNat = b₁.2.message.slot.toNat + 1 ∨ b₁.2.message.state_root ≠ 0)`,
`b₂.2.message.parent_root = Ssz.hashTreeRoot b₁.2.message`. -/
theorem jointStep_consecutive_parent_root {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s₁ s₂ : JointState P} {b₁ b₂ : AnySignedBlock P}
    (h₁ : jointStep cfg ccfg bls s₀ b₁ = .ok s₁)
    (h₂ : jointStep cfg ccfg bls s₁ b₂ = .ok s₂)
    (hguard : b₂.2.message.slot.toNat = b₁.2.message.slot.toNat + 1 ∨
              b₁.2.message.state_root ≠ (0 : B256)) :
    b₁.2.message.slot < b₂.2.message.slot ∧
    b₂.2.message.parent_root = Ssz.hashTreeRoot b₁.2.message := by
  obtain ⟨hsl₁, hsr₁, _, _, hfr₁⟩ := jointStep_post_header_and_filledRoot h₁
  obtain ⟨fs₁, beacon₁, exec₁⟩ := s₁
  obtain ⟨fb₂, sb₂⟩ := b₂
  change beacon₁.slot = b₁.2.message.slot at hsl₁
  change Ssz.hashTreeRoot beacon₁ = b₁.2.message.state_root at hsr₁
  change filledHeaderRoot beacon₁ = Ssz.hashTreeRoot b₁.2.message at hfr₁
  have hguard' :
      sb₂.message.slot.toNat = beacon₁.slot.toNat + 1 ∨
      (beacon₁.latest_block_header.state_root = (0 : B256) →
        Ssz.hashTreeRoot beacon₁ ≠ (0 : B256)) := by
    rcases hguard with h1 | hnz
    · exact Or.inl (by rw [hsl₁]; exact h1)
    · exact Or.inr (fun _ => by rw [hsr₁]; exact hnz)
  cases fs₁ <;> cases fb₂
  case electra.electra =>
    obtain ⟨hlt, hpr⟩ := jointStep_electra_parent_root hguard' h₂
    rw [hsl₁] at hlt
    exact ⟨hlt, hpr.trans hfr₁⟩
  case fulu.fulu =>
    obtain ⟨hlt, hpr⟩ := jointStep_fulu_parent_root hguard' h₂
    rw [hsl₁] at hlt
    exact ⟨hlt, hpr.trans hfr₁⟩
  case electra.fulu =>
    have hlt_fork : beacon₁.slot.toNat < fuluForkSlot (P := P) ccfg := by
      obtain ⟨fs₀, beacon₀, exec₀⟩ := s₀
      obtain ⟨fb₁, sb₁⟩ := b₁
      change beacon₁.slot = sb₁.message.slot at hsl₁
      cases fs₀ <;> cases fb₁
      case electra.electra =>
        obtain ⟨hsl_lt, _, _, _, _, _, _, _⟩ := jointStep_electra_ok_iff.mp h₁
        rw [hsl₁]; exact hsl_lt
      case electra.fulu =>
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, heq⟩ := jointStep_cross_ok_iff.mp h₁
        cases heq
      case fulu.fulu =>
        obtain ⟨_, _, _, _, _, _, heq⟩ := jointStep_fulu_ok_iff.mp h₁
        cases heq
      all_goals (unfold jointStep at h₁; cases h₁)
    obtain ⟨forkSlot, hfslot_nat, _, hle2, hcases⟩ := jointStep_cross_parent_root h₂
    rcases hcases with ⟨hlt_a, ha⟩ | ⟨heq_b, _, _⟩ | ⟨heq_c, _, _⟩
    · have hpr := ha hguard'
      have hlt12 : b₁.2.message.slot < sb₂.message.slot := by
        rw [← hsl₁]
        exact Nat.lt_of_lt_of_le hlt_a hle2
      exact ⟨hlt12, hpr.trans hfr₁⟩
    · exfalso; have : beacon₁.slot.toNat = forkSlot.toNat := congrArg U64.toNat heq_b; omega
    · exfalso; have : beacon₁.slot.toNat = forkSlot.toNat := congrArg U64.toNat heq_c; omega
  all_goals (unfold jointStep at h₂; cases h₂)

/-! ## Section 2 (`H-S9`): `latest_execution_payload_header`, `parent_hash`, and `block_hash` -/

/-- The `ExecutionPayloadHeader` constructed by `processExecutionPayload` from `payload`. -/
def payloadHeader (payload : ExecutionPayload P) : ExecutionPayloadHeader P :=
  { parent_hash := payload.parent_hash,
    fee_recipient := payload.fee_recipient,
    state_root := payload.state_root,
    receipts_root := payload.receipts_root,
    logs_bloom := payload.logs_bloom,
    prev_randao := payload.prev_randao,
    block_number := payload.block_number,
    gas_limit := payload.gas_limit,
    gas_used := payload.gas_used,
    timestamp := payload.timestamp,
    extra_data := payload.extra_data,
    base_fee_per_gas := payload.base_fee_per_gas,
    block_hash := payload.block_hash,
    transactions_root := Ssz.hashTreeRoot payload.transactions,
    withdrawals_root := Ssz.hashTreeRoot payload.withdrawals,
    blob_gas_used := payload.blob_gas_used,
    excess_blob_gas := payload.excess_blob_gas }

/-- `processExecutionPayload` enforces `payload.parent_hash = s.latest_execution_payload_header.block_hash`
and updates `s'.latest_execution_payload_header` to `payloadHeader payload`. -/
theorem processExecutionPayload_parent_and_header (ctx : Ctx) {body : BeaconBlockBody P f}
    {s s' : BeaconState P f} (h : processExecutionPayload ctx s body = .ok s') :
    body.execution_payload.parent_hash = s.latest_execution_payload_header.block_hash ∧
    s'.latest_execution_payload_header = payloadHeader body.execution_payload ∧
    s'.latest_execution_payload_header.block_hash = body.execution_payload.block_hash := by
  unfold processExecutionPayload at h
  obtain ⟨_, hreq1, h⟩ := bind_eq_ok_iff.mp h
  have hph : body.execution_payload.parent_hash = s.latest_execution_payload_header.block_hash :=
    beq_iff_eq.mp (require_eq_ok_iff.mp hreq1)
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨hph, rfl, rfl⟩)
    | cases h

/-- Across `processBlock` at Electra/Fulu, `blk.body.execution_payload.parent_hash` equals the
pre-state's `latest_execution_payload_header.block_hash`, and the post-state's
`latest_execution_payload_header` equals `payloadHeader blk.body.execution_payload`. -/
theorem processBlock_execution_payload_hashes (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {blk : BeaconBlock P f}
    (h : processBlock ctx s blk = .ok s') :
    blk.body.execution_payload.parent_hash = s.latest_execution_payload_header.block_hash ∧
    s'.latest_execution_payload_header = payloadHeader blk.body.execution_payload ∧
    s'.latest_execution_payload_header.block_hash = blk.body.execution_payload.block_hash := by
  unfold processBlock processBlockWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h7⟩ := bind_eq_ok_iff.mp h
  have c1 := processBlockHeader_corpusPres h1
  have c2 := processWithdrawals_csub h2
  obtain ⟨hph, hhdr3, _⟩ := processExecutionPayload_parent_and_header ctx h3
  have c4 := processRandao_csub ctx h4
  have c5 := processEth1Data_csub h5
  rw [processOperations_split_all ctx s5 blk.body hf] at h6
  obtain ⟨o1, ho1, h6⟩ := bind_eq_ok_iff.mp h6
  obtain ⟨o2, ho2, h6⟩ := bind_eq_ok_iff.mp h6
  obtain ⟨o3, ho3, ho4⟩ := bind_eq_ok_iff.mp h6
  have co1 := preDeposits_cpres_and_frame hf ctx ho1
  obtain ⟨_, _, hfr_o2⟩ := foldDepositRequests_spec hf _ ho2
  have co3 := foldWithdrawalRequests_csub ctx.cfg ho3
  obtain ⟨_, _, _, _, hlep_o4, _, _, _, _, _, _, _, _⟩ :=
    foldConsolidationRequests_frames_and_queues hf ctx.cfg _ ho4
  have c7 := processSyncAggregate_csub ctx h7
  have hlep_o2 : o2.latest_execution_payload_header = o1.latest_execution_payload_header := by
    rw [hfr_o2]
  have hph_pre : blk.body.execution_payload.parent_hash =
      s.latest_execution_payload_header.block_hash := by
    rw [hph, c2.lep_eq, c1.2.2.1]
  have hhdr_post : s'.latest_execution_payload_header = payloadHeader blk.body.execution_payload := by
    rw [c7.lep_eq, hlep_o4, co3.lep_eq, hlep_o2, co1.2.2.2.1, c5.lep_eq, c4.lep_eq, hhdr3]
  exact ⟨hph_pre, hhdr_post, by rw [hhdr_post]; rfl⟩

/-- Across `stateTransition` at Electra/Fulu, `processSlots` preserves
`latest_execution_payload_header` and `processBlock` checks `parent_hash` and writes
`payloadHeader sb.message.body.execution_payload`. -/
theorem stateTransition_execution_payload_hashes (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {sb : SignedBeaconBlock P f} {vr : Bool}
    (h : stateTransition ctx s sb vr = .ok s') :
    sb.message.body.execution_payload.parent_hash = s.latest_execution_payload_header.block_hash ∧
    s'.latest_execution_payload_header = payloadHeader sb.message.body.execution_payload ∧
    s'.latest_execution_payload_header.block_hash =
      sb.message.body.execution_payload.block_hash := by
  unfold stateTransition stateTransitionWith at h
  obtain ⟨mid, hps, h⟩ := bind_eq_ok_iff.mp h
  have hlep_ps := (processSlots_corpusPres hf ctx hps).2
  have hpb : processBlock ctx mid sb.message = .ok s' := by
    cases vr
    · simp only [Bool.false_eq_true, ite_false] at h
      obtain ⟨y, hy, hp⟩ := bind_eq_ok_iff.mp h
      exact (Except.ok.inj hp) ▸ hy
    · simp only [ite_true] at h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨_, _, hp⟩ := bind_eq_ok_iff.mp h
      exact (Except.ok.inj hp) ▸ hy
  obtain ⟨hph, hhdr, hbh⟩ := processBlock_execution_payload_hashes hf ctx hpb
  rw [hlep_ps] at hph
  exact ⟨hph, hhdr, hbh⟩

open Jaune in
/-- **`H-S9` unified `jointStep` execution-payload hash theorem** across Electra, Fulu, and
Electra → Fulu crossing. -/
theorem jointStep_execution_payload_hashes {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') :
    b.2.message.body.execution_payload.parent_hash =
      s.beacon.latest_execution_payload_header.block_hash ∧
    s'.beacon.latest_execution_payload_header = payloadHeader b.2.message.body.execution_payload ∧
    s'.beacon.latest_execution_payload_header.block_hash =
      b.2.message.body.execution_payload.block_hash := by
  obtain ⟨fs, beacon, exec⟩ := s
  obtain ⟨fb, sb⟩ := b
  cases fs <;> cases fb
  case electra.electra =>
    obtain ⟨_, _, b', _, _, _, hst, rfl⟩ := jointStep_electra_ok_iff.mp h
    exact stateTransition_execution_payload_hashes rfl _ hst
  case fulu.fulu =>
    obtain ⟨_, b', _, _, _, hst, rfl⟩ := jointStep_fulu_ok_iff.mp h
    exact stateTransition_execution_payload_hashes rfl _ hst
  case electra.fulu =>
    obtain ⟨_, _, _, _, b1, b2, b', _, _, hb1, hup, _, _, hb', rfl⟩ := jointStep_cross_ok_iff.mp h
    have hlep1 : b1.latest_execution_payload_header = beacon.latest_execution_payload_header := by
      split at hb1
      · exact (processSlots_corpusPres rfl _ hb1).2
      · cases hb1; rfl
    have hlep2 : b2.latest_execution_payload_header = beacon.latest_execution_payload_header :=
      (upgradeToFulu_cpres_and_frame ccfg hup).2.2.2.2.2.1.trans hlep1
    split at hb'
    · obtain ⟨hpb, _⟩ := atSlot_block_split hb'
      obtain ⟨hph, hhdr, hbh⟩ := processBlock_execution_payload_hashes rfl _ hpb
      rw [hlep2] at hph
      exact ⟨hph, hhdr, hbh⟩
    · obtain ⟨hph, hhdr, hbh⟩ := stateTransition_execution_payload_hashes rfl _ hb'
      rw [hlep2] at hph
      exact ⟨hph, hhdr, hbh⟩
  all_goals (unfold jointStep at h; cases h)

/-! ## Section 3 (`C-S9` & `D-S9` shared epoch split): `epochPreQueues` and `epochPostQueues` -/

/-- The six epoch passes before `processPendingDeposits` in `processEpoch`. -/
def epochPreQueues (cfg : Config) (state : BeaconState P f) : M (BeaconState P f) := do
  let state ← processJustificationAndFinalization cfg state
  let state ← processInactivityUpdates cfg state
  let state ← processRewardsAndPenalties cfg state
  let state ← processRegistryUpdates cfg state
  let state ← processSlashings cfg state
  processEth1DataReset cfg state

/-- The epoch passes after `processPendingConsolidations` in `processEpoch` (including Fulu's
`processProposerLookahead`). -/
def epochPostQueues (ctx : Ctx) (state : BeaconState P f) : M (BeaconState P f) := do
  let cfg := ctx.cfg
  let state ← processEffectiveBalanceUpdates cfg state
  let state ← processSlashingsReset cfg state
  let state ← processRandaoMixesReset cfg state
  let state ← processHistoricalSummariesUpdate cfg state
  let state ← processParticipationFlagUpdates cfg state
  let state ← processSyncCommitteeUpdates ctx state
  if f.atLeast .fulu then processProposerLookahead cfg state else pure state

/-- The epoch passes before `processPendingConsolidations` at Electra/Fulu. -/
def epochBeforeConsolidations (ctx : Ctx) (state : BeaconState P f) : M (BeaconState P f) := do
  let state ← epochPreQueues ctx.cfg state
  processPendingDeposits ctx state

/-- The epoch passes after `processPendingDeposits` at Electra/Fulu. -/
def epochAfterDeposits (ctx : Ctx) (state : BeaconState P f) : M (BeaconState P f) := do
  let state ← processPendingConsolidations ctx.cfg state
  epochPostQueues ctx state

/-- Decomposition of `processEpoch` at Electra/Fulu around `processPendingDeposits` and
`processPendingConsolidations`. -/
theorem processEpoch_split_queues (hf : f.atLeast .electra = true) (ctx : Ctx)
    (state : BeaconState P f) :
    processEpoch ctx state = (do
      let s1 ← epochPreQueues ctx.cfg state
      let s2 ← processPendingDeposits ctx s1
      let s3 ← processPendingConsolidations ctx.cfg s2
      epochPostQueues ctx s3) := by
  unfold processEpoch epochPreQueues epochPostQueues
  simp only [hf, ite_true, bind_assoc]

theorem epochPreQueues_csub (hf : f.atLeast .electra = true) (cfg : Config)
    {s s' : BeaconState P f} (h : epochPreQueues cfg s = .ok s') : CommonSubstep s s' := by
  unfold epochPreQueues at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h6⟩ := bind_eq_ok_iff.mp h
  exact (processJustificationAndFinalization_csub cfg h1).trans <|
    (processInactivityUpdates_csub cfg h2).trans <|
    (processRewardsAndPenalties_csub cfg h3).trans <|
    (processRegistryUpdates_csub cfg hf h4).trans <|
    (processSlashings_csub cfg h5).trans <|
    processEth1DataReset_csub cfg h6

theorem epochPostQueues_csub (ctx : Ctx)
    {s s' : BeaconState P f} (h : epochPostQueues ctx s = .ok s') : CommonSubstep s s' := by
  unfold epochPostQueues at h
  obtain ⟨s8, h8, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s9, h9, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s10, h10, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s11, h11, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s12, h12, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s13, h13, h⟩ := bind_eq_ok_iff.mp h
  have c_end : CommonSubstep s13 s' := by
    split at h
    · exact processProposerLookahead_csub ctx.cfg h
    · cases h; exact CommonSubstep.refl _
  exact (processEffectiveBalanceUpdates_csub ctx.cfg h8).trans <|
    (processSlashingsReset_csub ctx.cfg h9).trans <|
    (processRandaoMixesReset_csub ctx.cfg h10).trans <|
    (processHistoricalSummariesUpdate_csub ctx.cfg h11).trans <|
    (processParticipationFlagUpdates_csub ctx.cfg h12).trans <|
    (processSyncCommitteeUpdates_csub ctx h13).trans c_end

theorem epochBeforeConsolidations_pendingConsolidations (hf : f.atLeast .electra = true)
    (ctx : Ctx) {s s' : BeaconState P f}
    (h : epochBeforeConsolidations ctx s = .ok s') :
    s'.pending_consolidations = s.pending_consolidations ∧ s'.slot = s.slot := by
  unfold epochBeforeConsolidations at h
  obtain ⟨s1, h1, h2⟩ := bind_eq_ok_iff.mp h
  have c1 := epochPreQueues_csub hf ctx.cfg h1
  have c2 := processPendingDeposits_cpres_and_frame ctx h2
  exact ⟨c2.2.2.2.2.trans c1.pc_eq, c2.2.1.trans c1.slot_eq⟩

theorem epochAfterDeposits_pendingDeposits (hf : f.atLeast .electra = true)
    (ctx : Ctx) {s s' : BeaconState P f}
    (h : epochAfterDeposits ctx s = .ok s') :
    s'.pending_deposits = s.pending_deposits ∧ s'.slot = s.slot := by
  unfold epochAfterDeposits at h
  obtain ⟨s1, h1, h2⟩ := bind_eq_ok_iff.mp h
  have c1 := processPendingConsolidations_cpres_and_frame hf ctx.cfg h1
  have c2 := epochPostQueues_csub ctx h2
  exact ⟨c2.pd_eq.trans c1.2.2.2.2, c2.slot_eq.trans c1.2.1⟩

/-! ## Section 4 (`C-S9`): Block consolidation split, `ConsolidationRun` list law, and chains -/

/-- `processSyncAggregate` modifies only `balances` and leaves `validators` unchanged. -/
theorem processSyncAggregate_validators_eq (ctx : Ctx) {sa : SyncAggregate P}
    {s s' : BeaconState P f} (h : processSyncAggregate ctx s sa = .ok s') :
    s'.validators = s.validators := by
  revert s' h
  show Ok (processSyncAggregate ctx s sa) (fun s' => s'.validators = s.validators)
  unfold processSyncAggregate
  dsimp only []
  repeat' (with_reducible apply ok_ite <;> intro _)
  all_goals
    repeat (with_reducible apply ok_bind; intro _ _)
    refine ok_pure ?_
    rename_i out hloop
    refine array_forIn_rel (fun (a b : BeaconState P f) => b.validators = a.validators)
      (fun _ => rfl) (fun _ _ _ h1 h2 => h2.trans h1) _ (fun x st r hr => ?_) _ _ _ hloop
    split at hr
    · obtain ⟨st1, hinc1, hr⟩ := bind_eq_ok_iff.mp hr
      obtain ⟨_, _, hr⟩ := bind_eq_ok_iff.mp hr
      obtain ⟨st2, hinc2, hp⟩ := bind_eq_ok_iff.mp hr
      cases hp
      exact (increaseBalance_frame hinc2).1.trans (increaseBalance_frame hinc1).1
    · obtain ⟨st1, hdec, hp⟩ := bind_eq_ok_iff.mp hr
      cases hp
      exact (decreaseBalance_frame hdec).1

/-- Across `processBlock` at Electra/Fulu, all operations before `foldConsolidationRequests`
preserve `pending_consolidations`, `foldConsolidationRequests` appends the accepted consolidations
with `source_index ≠ target_index`, and `processSyncAggregate` preserves `pending_consolidations`
and `validators`. -/
theorem processBlock_pendingConsolidations (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {blk : BeaconBlock P f}
    (h : processBlock ctx s blk = .ok s') :
    ∃ (s_pre s_post : BeaconState P f) (outcomes : List ConsolidationOutcome),
      s_pre.slot = blk.slot ∧
      s_pre.pending_consolidations = s.pending_consolidations ∧
      pendingConsolidationsList s_pre = pendingConsolidationsList s ∧
      foldConsolidationRequests ctx.cfg s_pre
        (Gated.get hf blk.body.execution_requests).consolidations.toArray.toList = .ok s_post ∧
      outcomes.length =
        (Gated.get hf blk.body.execution_requests).consolidations.toArray.toList.length ∧
      (∀ pc ∈ outcomes.filterMap acceptedConsolidation, pc.source_index ≠ pc.target_index) ∧
      pendingConsolidationsList s' =
        pendingConsolidationsList s ++ outcomes.filterMap acceptedConsolidation ∧
      processSyncAggregate ctx s_post blk.body.sync_aggregate = .ok s' ∧
      s'.pending_consolidations = s_post.pending_consolidations ∧
      s'.validators = s_post.validators := by
  unfold processBlock processBlockWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h7⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, _, _, hsl1, _⟩ := processBlockHeader_spec h1
  have c1 := processBlockHeader_corpusPres h1
  have c2 := processWithdrawals_csub h2
  have c3 := processExecutionPayload_corpusPres ctx h3
  have c4 := processRandao_csub ctx h4
  have c5 := processEth1Data_csub h5
  rw [processOperations_split_consolidations ctx s5 blk.body hf] at h6
  obtain ⟨s_pre, hpre, hfold⟩ := bind_eq_ok_iff.mp h6
  rw [preConsolidations_eq ctx s5 blk.body hf, preRequests_eq_preDeposits_fold ctx s5 blk.body hf] at hpre
  simp only [bind_assoc] at hpre
  obtain ⟨o1, ho1, hpre⟩ := bind_eq_ok_iff.mp hpre
  obtain ⟨o2, ho2, ho3⟩ := bind_eq_ok_iff.mp hpre
  have co1 := preDeposits_cpres_and_frame hf ctx ho1
  obtain ⟨_, _, hfr_o2⟩ := foldDepositRequests_spec hf _ ho2
  have co3 := foldWithdrawalRequests_csub ctx.cfg ho3
  have hsl_o2 : o2.slot = o1.slot := by rw [hfr_o2]
  have hpc_o2 : o2.pending_consolidations = o1.pending_consolidations := by rw [hfr_o2]
  have hsl_pre : s_pre.slot = blk.slot := by
    rw [co3.slot_eq, hsl_o2, co1.2.1, c5.slot_eq, c4.slot_eq, c3.2.1, c2.slot_eq, hsl1]
  have hpc_pre : s_pre.pending_consolidations = s.pending_consolidations := by
    rw [co3.pc_eq, hpc_o2, co1.2.2.2.2.1, c5.pc_eq, c4.pc_eq, c3.2.2.2.1, c2.pc_eq, c1.2.2.2.1]
  have hpcl_pre : pendingConsolidationsList s_pre = pendingConsolidationsList s :=
    pendingConsolidationsList_congr hpc_pre
  obtain ⟨outcomes, _, hlen, _, _, _, _, _, _, hdist, hpc_post, _, _⟩ :=
    foldConsolidationRequests_frames_and_queues hf ctx.cfg _ hfold
  have c7 := processSyncAggregate_csub ctx h7
  have hval7 := processSyncAggregate_validators_eq ctx h7
  have hpcl_s' : pendingConsolidationsList s' =
      pendingConsolidationsList s ++ outcomes.filterMap acceptedConsolidation := by
    rw [pendingConsolidationsList_congr c7.pc_eq, pendingConsolidationsList_eq_get hf,
        hpc_post, ← pendingConsolidationsList_eq_get hf, hpcl_pre]
  exact ⟨s_pre, s6, outcomes, hsl_pre, hpc_pre, hpcl_pre, hfold, hlen, hdist, hpcl_s',
    h7, c7.pc_eq, hval7⟩

/-- Explicit indexed trace extracted from `ConsolidationRun`: intermediate states `us` of length
`L.length + 1` with `us[0] = s`, `us[L.length] = s'`, constant `validators`, and per-step skipped
or applied consolidation transition. -/
theorem ConsolidationRun.toTrace {nextEpoch : U64} :
    ∀ {s : BeaconState P f} {n : Nat} {L : List PendingConsolidation} {s' : BeaconState P f},
      ConsolidationRun nextEpoch s n L s' →
      ∃ us : List (BeaconState P f),
        us.length = L.length + 1 ∧
        us[0]? = some s ∧
        us[L.length]? = some s' ∧
        (∀ u ∈ us, u.validators = s.validators) ∧
        ∀ (j : Nat), j < L.length →
          ∃ pc u u' src,
            L[j]? = some pc ∧
            us[j]? = some u ∧
            us[j + 1]? = some u' ∧
            u.validators.toArray[pc.source_index.toNat]? = some src ∧
            ((src.slashed = true ∧ u' = u) ∨
             (src.slashed = false ∧ ¬ src.withdrawable_epoch > nextEpoch ∧
              ∃ bal mid, u.balances.toArray[pc.source_index.toNat]? = some bal ∧
                decreaseBalance u pc.source_index
                  (if bal < src.effective_balance then bal else src.effective_balance) = .ok mid ∧
                increaseBalance mid pc.target_index
                  (if bal < src.effective_balance then bal else src.effective_balance) = .ok u')) := by
  intro s n L s' hrun
  induction hrun with
  | nil s n =>
    exact ⟨[s], rfl, rfl, rfl,
      fun u hu => by simp only [List.mem_singleton] at hu; subst hu; rfl,
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | @cons s s1 s' n pc rest hstep _ ih =>
    obtain ⟨us, hlen, hu0, hulast, hvals, hsteps⟩ := ih
    obtain ⟨src, hsrc, hsp⟩ := pendingConsolidationStep_spec hstep
    have hs1_val : s1.validators = s.validators := by
      rcases hsp with ⟨_, heq⟩ | ⟨_, _, heq⟩ | ⟨_, _, bal, mid, st', _, hdec, hinc, heq⟩
      · cases heq; rfl
      · cases heq
      · cases heq
        obtain ⟨_, _, _, _, _, hd⟩ := decreaseBalance_spec hdec
        obtain ⟨_, _, _, _, _, hi⟩ := increaseBalance_spec hinc
        rw [hi, hd]
    refine ⟨s :: us, by simp [hlen], rfl, by simpa using hulast, ?_, ?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hmem
      · rfl
      · exact (hvals u hmem).trans hs1_val
    · intro j hj
      cases j with
      | zero =>
        refine ⟨pc, s, s1, src, rfl, rfl, by simpa using hu0, hsrc, ?_⟩
        rcases hsp with ⟨hsl, heq⟩ | ⟨_, _, heq⟩ | ⟨hsl, hnw, bal, mid, st', hb, hdec, hinc, heq⟩
        · cases heq; exact Or.inl ⟨hsl, rfl⟩
        · cases heq
        · cases heq; exact Or.inr ⟨hsl, hnw, bal, mid, hb, hdec, hinc⟩
      | succ j' =>
        have hj' : j' < rest.length := by simp at hj; omega
        obtain ⟨pc', u, u', src', hpc', huj, huj1, hsrc', hcase⟩ := hsteps j' hj'
        exact ⟨pc', u, u', src', hpc', huj, huj1, hsrc', hcase⟩

/-- Full indexed law for `processPendingConsolidations` (including `nextEpoch`, intermediate trace
`us`, suffix drop on `pendingConsolidationsList`, and the stopping witness when `d < queue.length`). -/
theorem processPendingConsolidations_full_law (hf : f.atLeast .electra = true) {cfg : Config}
    {state s' : BeaconState P f} (hp : processPendingConsolidations cfg state = .ok s') :
    ∃ (e0 nextEpoch : Epoch) (d : Nat) (mid : BeaconState P f) (us : List (BeaconState P f)),
      getCurrentEpoch state = .ok e0 ∧
      nextEpoch.toNat = e0.toNat + 1 ∧
      d ≤ (pendingConsolidationsList state).length ∧
      us.length = d + 1 ∧
      us[0]? = some state ∧
      us[d]? = some mid ∧
      (∀ u ∈ us, u.validators = state.validators) ∧
      s'.validators = state.validators ∧
      s'.balances = mid.balances ∧
      pendingConsolidationsList s' = (pendingConsolidationsList state).drop d ∧
      (∀ (j : Nat), j < d →
        ∃ pc u u' src,
          (pendingConsolidationsList state)[j]? = some pc ∧
          us[j]? = some u ∧
          us[j + 1]? = some u' ∧
          u.validators.toArray[pc.source_index.toNat]? = some src ∧
          ((src.slashed = true ∧ u' = u) ∨
           (src.slashed = false ∧ ¬ src.withdrawable_epoch > nextEpoch ∧
            ∃ bal mid_step, u.balances.toArray[pc.source_index.toNat]? = some bal ∧
              decreaseBalance u pc.source_index
                (if bal < src.effective_balance then bal else src.effective_balance) = .ok mid_step ∧
              increaseBalance mid_step pc.target_index
                (if bal < src.effective_balance then bal else src.effective_balance) = .ok u'))) ∧
      (d < (pendingConsolidationsList state).length →
        ∃ pc src,
          (pendingConsolidationsList state)[d]? = some pc ∧
          state.validators.toArray[pc.source_index.toNat]? = some src ∧
          src.slashed = false ∧ src.withdrawable_epoch > nextEpoch) := by
  rw [processPendingConsolidations_eq] at hp
  dsimp only at hp
  obtain ⟨e0, he0, hp⟩ := bind_eq_ok_iff.mp hp
  obtain ⟨nextEpoch, hne, hp⟩ := bind_eq_ok_iff.mp hp
  have hne_nat : nextEpoch.toNat = e0.toNat + 1 := U64.toNat_add? hne
  obtain ⟨pending, hpend, hp⟩ := bind_eq_ok_iff.mp hp
  have hpq : pending = Gated.get hf state.pending_consolidations := by
    unfold BeaconState.pendingConsolidations at hpend
    rw [gated_read_get hf] at hpend
    exact (Except.ok.inj hpend).symm
  subst hpq
  obtain ⟨out, hloop, hp⟩ := bind_eq_ok_iff.mp hp
  obtain ⟨d, hd_le, hrun, hn, hstop⟩ := pendingConsolidationsLoop_fate _ _ _ _ hloop
  obtain ⟨us, hus_len, hus0, husd, hus_vals, hus_steps⟩ := hrun.toTrace
  obtain ⟨q, hq, hp⟩ := bind_eq_ok_iff.mp hp
  unfold BeaconState.setPendingConsolidations at hp
  obtain ⟨g, hg, hp⟩ := bind_eq_ok_iff.mp hp
  cases hp
  have hgq : g = Gated.mk hf q := by
    rw [gated_write_eq hf] at hg; exact (Except.ok.inj hg).symm
  have hq_arr : q.toArray =
      (Gated.get hf state.pending_consolidations).toArray.extract out.2
        (Gated.get hf state.pending_consolidations).length := by
    unfold SszList.ofArray at hq
    split at hq
    · cases hq; rfl
    · cases hq
  have hpcl_state : pendingConsolidationsList state =
      (Gated.get hf state.pending_consolidations).toArray.toList :=
    pendingConsolidationsList_eq_get hf state
  have hd_le' : d ≤ (pendingConsolidationsList state).length := by
    rw [hpcl_state]; exact hd_le
  have htake_len : ((Gated.get hf state.pending_consolidations).toArray.toList.take d).length = d :=
    List.length_take_of_le hd_le
  have hmid_val : out.1.validators = state.validators := by
    rw [htake_len] at husd
    exact hus_vals out.1 (List.mem_of_getElem? husd)
  have hpcl_post :
      pendingConsolidationsList { out.1 with pending_consolidations := g } =
        (pendingConsolidationsList state).drop d := by
    rw [pendingConsolidationsList_eq_get hf, hpcl_state]
    show (Gated.get hf g).toArray.toList = _
    rw [hgq, Gated.get_mk, hq_arr, hn, Nat.zero_add, Array.toList_extract]
    have hsz : (Gated.get hf state.pending_consolidations).length =
        (Gated.get hf state.pending_consolidations).toArray.toList.length := by
      simp [SszList.length]
    rw [hsz]
    have hdrop_len :
        ((Gated.get hf state.pending_consolidations).toArray.toList.drop d).length ≤
          (Gated.get hf state.pending_consolidations).toArray.toList.length - d := by
      simp
    exact List.take_of_length_le hdrop_len
  refine ⟨e0, nextEpoch, d, out.1, us, he0, hne_nat, hd_le',
    by rw [← htake_len]; exact hus_len,
    hus0, by rw [← htake_len]; exact husd,
    hus_vals, hmid_val, rfl, hpcl_post, ?_, ?_⟩
  · intro j hj
    have hj_take : j < ((Gated.get hf state.pending_consolidations).toArray.toList.take d).length := by
      rw [htake_len]; exact hj
    obtain ⟨pc, u, u', src, hpc_take, huj, huj1, hsrc, hcase⟩ := hus_steps j hj_take
    have hpc_full : (pendingConsolidationsList state)[j]? = some pc := by
      rw [hpcl_state, ← List.getElem?_take_of_lt hj]
      exact hpc_take
    exact ⟨pc, u, u', src, hpc_full, huj, huj1, hsrc, hcase⟩
  · intro hd_lt
    have hd_lt_raw : d < (Gated.get hf state.pending_consolidations).toArray.toList.length := by
      rwa [← hpcl_state]
    have hdone := hstop hd_lt_raw
    obtain ⟨src, hsrc, hsp⟩ := pendingConsolidationStep_spec hdone
    rw [hmid_val] at hsrc
    let pc := (Gated.get hf state.pending_consolidations).toArray.toList[d]'hd_lt_raw
    have hpc_some : (pendingConsolidationsList state)[d]? = some pc := by
      rw [hpcl_state, List.getElem?_eq_getElem hd_lt_raw]
    rcases hsp with ⟨_, heq⟩ | ⟨hsl, hgt, _⟩ | ⟨_, _, _, _, _, _, _, _, heq⟩
    · cases heq
    · exact ⟨pc, src, hpc_some, hsrc, hsl, hgt⟩
    · cases heq

/-- Ordered chain of `processPendingConsolidations cfg` invocations transforming queue `q₀` to `q'`,
with `pendingConsolidationsList` unchanged between consecutive invocations. -/
inductive EpochConsolidationChain (cfg : Config) :
    List PendingConsolidation → List (BeaconState P f × BeaconState P f) →
    List PendingConsolidation → Prop where
  | nil (q : List PendingConsolidation) : EpochConsolidationChain cfg q [] q
  | cons {q : List PendingConsolidation} {w w' : BeaconState P f}
      {rest : List (BeaconState P f × BeaconState P f)} {q_out : List PendingConsolidation} :
      pendingConsolidationsList w = q →
      processPendingConsolidations cfg w = .ok w' →
      EpochConsolidationChain cfg (pendingConsolidationsList w') rest q_out →
      EpochConsolidationChain cfg q ((w, w') :: rest) q_out

theorem EpochConsolidationChain.append {cfg : Config}
    {q₀ q₁ q₂ : List PendingConsolidation}
    {c₁ c₂ : List (BeaconState P f × BeaconState P f)}
    (h₁ : EpochConsolidationChain cfg q₀ c₁ q₁)
    (h₂ : EpochConsolidationChain cfg q₁ c₂ q₂) :
    EpochConsolidationChain cfg q₀ (c₁ ++ c₂) q₂ := by
  induction h₁ with
  | nil _ => exact h₂
  | cons hw hp _ ih => exact .cons hw hp (ih h₂)

private theorem range'_forIn_consolidations_chain (hf : f.atLeast .electra = true) (ctx : Ctx)
    {body : Nat → BeaconState P f → M (ForInStep (BeaconState P f))}
    (hb : ∀ k st r, body k st = .ok r →
      ∃ st1 next st2,
        processSlot st = .ok st1 ∧
        next.toNat = st.slot.toNat + 1 ∧
        (st2 = st1 ∨ processEpoch ctx st1 = .ok st2) ∧
        r = .yield { st2 with slot := next }) :
    ∀ (n start : Nat) (cur out : BeaconState P f),
      forIn (List.range' start n) cur body = .ok out →
      ∃ calls : List (BeaconState P f × BeaconState P f),
        EpochConsolidationChain ctx.cfg (pendingConsolidationsList cur) calls
          (pendingConsolidationsList out)
  | 0, _, cur, out, h => by
    have heq : cur = out := Except.ok.inj h
    subst heq
    exact ⟨[], .nil _⟩
  | n + 1, start, cur, out, h => by
    rw [List.range'_succ, List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨st1, next, st2, hslot, _, hep_or, rfl⟩ := hb start cur r hr
    have hc_slot := processSlot_cpres_and_frame hslot
    rcases hep_or with hst2 | hep
    · rw [hst2] at h
      obtain ⟨calls_rest, hrest⟩ :=
        range'_forIn_consolidations_chain hf ctx hb n (start + 1)
          { st1 with slot := next } out h
      have hw'_eq :
          pendingConsolidationsList { st1 with slot := next } = pendingConsolidationsList cur :=
        pendingConsolidationsList_congr hc_slot.2.2.2.2.2.1
      rw [hw'_eq] at hrest
      exact ⟨calls_rest, hrest⟩
    · rw [processEpoch_split_queues hf ctx st1] at hep
      obtain ⟨ep1, hep1, hep⟩ := bind_eq_ok_iff.mp hep
      obtain ⟨ep2, hep2, hep⟩ := bind_eq_ok_iff.mp hep
      obtain ⟨ep3, hep3, hep4⟩ := bind_eq_ok_iff.mp hep
      have c_pre := epochPreQueues_csub hf ctx.cfg hep1
      have c_dep := processPendingDeposits_cpres_and_frame ctx hep2
      have c_post := epochPostQueues_csub ctx hep4
      obtain ⟨calls_rest, hrest⟩ :=
        range'_forIn_consolidations_chain hf ctx hb n (start + 1)
          { st2 with slot := next } out h
      have hw_eq : pendingConsolidationsList ep2 = pendingConsolidationsList cur :=
        pendingConsolidationsList_congr
          (c_dep.2.2.2.2.trans (c_pre.pc_eq.trans hc_slot.2.2.2.2.2.1))
      have hw'_eq :
          pendingConsolidationsList { st2 with slot := next } = pendingConsolidationsList ep3 :=
        pendingConsolidationsList_congr c_post.pc_eq
      rw [hw'_eq] at hrest
      exact ⟨(ep2, ep3) :: calls_rest, .cons hw_eq hep3 hrest⟩

/-- **`C-S9` `processSlots` consolidation chain:** `processSlots` changes `pendingConsolidationsList`
exclusively via an ordered sequence of `processPendingConsolidations` invocations. -/
theorem processSlots_consolidations_chain (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {slot : Slot}
    (h : processSlots ctx s slot = .ok s') :
    ∃ calls : List (BeaconState P f × BeaconState P f),
      EpochConsolidationChain ctx.cfg (pendingConsolidationsList s) calls
        (pendingConsolidationsList s') := by
  obtain ⟨_, body, hloop, hb⟩ := processSlots_loop_ok h
  exact range'_forIn_consolidations_chain hf ctx hb (slot.toNat - s.slot.toNat) 0 s s' hloop

open Jaune in
/-- **`C-S9` Electra → Fulu crossing decomposition:**
decomposes `jointStep` across the Electra → Fulu fork boundary into:
1. Pre-upgrade Electra `EpochConsolidationChain` (`callsE`, empty if `beacon.slot = forkSlot`),
2. Verbatim queue copy `pendingConsolidationsList b2 = pendingConsolidationsList b1` across
   `upgradeToFulu`,
3. Post-upgrade Fulu `EpochConsolidationChain` (`callsF`, empty if `sb.message.slot == b2.slot`),
4. Final `processBlock` on `b_preBlock` producing `b'` with `s' = ⟨.fulu, b', e'⟩`. -/
theorem jointStep_cross_consolidations_chain {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
    {s' : JointState P}
    (h : jointStep cfg ccfg bls ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok s') :
    ∃ (b1 : BeaconState P .electra) (b2 b_preBlock b' : BeaconState P .fulu) (e' : BlockChain)
      (callsE : List (BeaconState P .electra × BeaconState P .electra))
      (callsF : List (BeaconState P .fulu × BeaconState P .fulu)),
      s' = ⟨.fulu, b', e'⟩ ∧
      EpochConsolidationChain ccfg (pendingConsolidationsList beacon) callsE
        (pendingConsolidationsList b1) ∧
      upgradeToFulu ccfg b1 = .ok b2 ∧
      pendingConsolidationsList b2 = pendingConsolidationsList b1 ∧
      EpochConsolidationChain ccfg (pendingConsolidationsList b2) callsF
        (pendingConsolidationsList b_preBlock) ∧
      processBlock { cfg := ccfg, blsActive := bls } b_preBlock sb.message = .ok b' := by
  obtain ⟨_, _, _, _, b1, b2, b', e', _, hb1, hup, _, _, hb', hs'_eq⟩ :=
    jointStep_cross_ok_iff.mp h
  have hup_pcl := (upgradeToFulu_cpres_and_frame ccfg hup).2.2.2.2.2.2.1
  have hE : ∃ callsE : List (BeaconState P .electra × BeaconState P .electra),
      EpochConsolidationChain ccfg (pendingConsolidationsList beacon) callsE
        (pendingConsolidationsList b1) := by
    split at hb1
    · exact processSlots_consolidations_chain rfl _ hb1
    · cases hb1; exact ⟨[], .nil _⟩
  obtain ⟨callsE, hcallsE⟩ := hE
  split at hb'
  · obtain ⟨hpb, _⟩ := atSlot_block_split hb'
    exact ⟨b1, b2, b2, b', e', callsE, [], hs'_eq, hcallsE, hup, hup_pcl, .nil _, hpb⟩
  · obtain ⟨mid, hps2, hpb, _⟩ := stateTransition_true_split hb'
    obtain ⟨callsF, hcallsF⟩ := processSlots_consolidations_chain rfl _ hps2
    exact ⟨b1, b2, mid, b', e', callsE, callsF, hs'_eq, hcallsE, hup, hup_pcl, hcallsF, hpb⟩

/-! ## Section 5 (`D-S9`): `pendingDepositsList`, exiting-validator invariance, block split & chains -/

/-- Fork-uniform view of `state.pending_deposits` as `List PendingDeposit` (empty before Electra). -/
def pendingDepositsList (s : BeaconState P f) : List PendingDeposit :=
  if hf : f.atLeast .electra = true then
    (Gated.get hf s.pending_deposits).toArray.toList
  else []

theorem pendingDepositsList_eq_get (hf : f.atLeast .electra = true) (s : BeaconState P f) :
    pendingDepositsList s = (Gated.get hf s.pending_deposits).toArray.toList := by
  unfold pendingDepositsList
  split
  · rfl
  · rename_i hnot; exact absurd hf hnot

theorem pendingDepositsList_congr {s₁ s₂ : BeaconState P f}
    (h : s₁.pending_deposits = s₂.pending_deposits) :
    pendingDepositsList s₁ = pendingDepositsList s₂ := by
  unfold pendingDepositsList
  split
  · rw [h]
  · rfl

theorem upgradeToFulu_pendingDepositsList (cfg : Config)
    {pre : BeaconState P .electra} {post : BeaconState P .fulu}
    (h : upgradeToFulu cfg pre = .ok post) :
    pendingDepositsList post = pendingDepositsList pre := by
  have hpd := (upgradeToFulu_cpres_and_frame cfg h).2.2.2.2.2.2.2.2
  rw [pendingDepositsList_eq_get (f := .fulu) rfl, pendingDepositsList_eq_get (f := .electra) rfl]
  exact congrArg (fun x => x.toArray.toList) hpd

/-- One `applyPendingDeposit` preserves all existing validators at their indices, preserves all
existing `findValidatorIndex` lookups, and any newly appended validator has
`exit_epoch = FAR_FUTURE_EPOCH` and `withdrawable_epoch = FAR_FUTURE_EPOCH`. -/
theorem applyPendingDeposit_validators_step {ctx : Ctx} {s s' : BeaconState P f}
    {dep : PendingDeposit}
    (h : applyPendingDeposit ctx s dep = .ok s') :
    s.validators.toArray.size ≤ s'.validators.toArray.size ∧
    (∀ i, i < s.validators.toArray.size →
      s'.validators.toArray[i]? = s.validators.toArray[i]?) ∧
    (∀ pk i, findValidatorIndex s pk = some i → findValidatorIndex s' pk = some i) ∧
    (∀ i v, s.validators.toArray.size ≤ i → s'.validators.toArray[i]? = some v →
      v.exit_epoch = FAR_FUTURE_EPOCH ∧ v.withdrawable_epoch = FAR_FUTURE_EPOCH) ∧
    (∀ pk i, findValidatorIndex s' pk = some i → i < s.validators.toArray.size →
      findValidatorIndex s pk = some i) := by
  rw [applyPendingDeposit_eq] at h
  obtain ⟨o, _, ha⟩ := bind_eq_ok_iff.mp h
  cases o with
  | noCredit =>
    cases ha
    exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ h => h,
      fun i _ hle hg => absurd (Array.getElem?_eq_some_iff.mp hg).1 (Nat.not_lt.mpr hle),
      fun _ _ h _ => h⟩
  | topUp idx =>
    obtain ⟨_, _, _, _, _, hv_eq⟩ := applyPendingDeposit_topUp_credit ha
    refine ⟨by rw [hv_eq], fun _ _ => by rw [hv_eq], ?_, ?_, ?_⟩
    · intro pk i hf; unfold findValidatorIndex at hf ⊢; rw [hv_eq]; exact hf
    · intro i _ hle hg
      rw [hv_eq] at hg
      exact absurd (Array.getElem?_eq_some_iff.mp hg).1 (Nat.not_lt.mpr hle)
    · intro pk i hf _; unfold findValidatorIndex at hf ⊢; rw [hv_eq] at hf; exact hf
  | newValidator =>
    unfold applyPendingDepositOutcome addValidatorToRegistry at ha
    obtain ⟨index, hindex, ha⟩ := bind_eq_ok_iff.mp ha
    obtain ⟨v, hv, ha⟩ := bind_eq_ok_iff.mp ha
    obtain ⟨vals, hvals, ha⟩ := bind_eq_ok_iff.mp ha
    obtain ⟨_, _, ha⟩ := bind_eq_ok_iff.mp ha
    obtain ⟨_, _, ha⟩ := bind_eq_ok_iff.mp ha
    obtain ⟨_, _, ha⟩ := bind_eq_ok_iff.mp ha
    obtain ⟨_, _, ha⟩ := bind_eq_ok_iff.mp ha
    cases ha
    have hix : index.toNat = s.validators.toArray.size := U64.toNat_ofNat? hindex
    have hpush : vals.toArray = s.validators.toArray.push v := setOrAppendList_at_length hix hvals
    have hv_epochs : v.exit_epoch = FAR_FUTURE_EPOCH ∧ v.withdrawable_epoch = FAR_FUTURE_EPOCH := by
      unfold getValidatorFromDeposit at hv
      obtain ⟨_, _, hv⟩ := bind_eq_ok_iff.mp hv
      obtain ⟨_, _, hv⟩ := bind_eq_ok_iff.mp hv
      obtain ⟨_, _, hv⟩ := bind_eq_ok_iff.mp hv
      obtain ⟨_, _, hv⟩ := bind_eq_ok_iff.mp hv
      cases hv
      exact ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show s.validators.toArray.size ≤ vals.toArray.size
      rw [hpush, Array.size_push]; omega
    · intro i hi
      show vals.toArray[i]? = _
      rw [hpush, Array.getElem?_push, ite_eq_right (Nat.ne_of_lt hi)]
    · intro pk i hf
      unfold findValidatorIndex at hf ⊢
      show vals.toArray.findIdx? (·.pubkey == pk) = some i
      rw [hpush, Array.findIdx?_eq_some_iff_getElem]
      obtain ⟨hlt, hpk, hbefore⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
      refine ⟨by rw [Array.size_push]; omega, ?_, ?_⟩
      · rwa [Array.getElem_push_lt hlt]
      · intro j hj
        rw [Array.getElem_push_lt (Nat.lt_trans hj hlt)]
        exact hbefore j hj
    · intro i u hle hg
      change vals.toArray[i]? = some u at hg
      rw [hpush, Array.getElem?_push] at hg
      by_cases heq : i = s.validators.toArray.size
      · rw [ite_eq_left heq] at hg
        cases hg
        exact hv_epochs
      · rw [ite_eq_right heq] at hg
        exact absurd (Array.getElem?_eq_some_iff.mp hg).1 (by omega)
    · intro pk i hf hi_lt
      unfold findValidatorIndex at hf ⊢
      change vals.toArray.findIdx? (·.pubkey == pk) = some i at hf
      rw [hpush, Array.findIdx?_eq_some_iff_getElem] at hf
      obtain ⟨_, hpk, hbefore⟩ := hf
      rw [Array.getElem_push_lt hi_lt] at hpk
      rw [Array.findIdx?_eq_some_iff_getElem]
      refine ⟨hi_lt, hpk, fun j hj => ?_⟩
      have hjb := hbefore j hj
      rwa [Array.getElem_push_lt (Nat.lt_trans hj hi_lt)] at hjb

/-- **`D-S9` exiting-validator invariance across `List.foldlM (applyPendingDeposit ctx)`:**
An exiting validator (`v.exit_epoch < FAR_FUTURE_EPOCH`) resolved by `findValidatorIndex` at any
intermediate state `cur` of `processPendingDeposits` is the exact same validator at the exact same
index as in the pre-pass state `init` (newly created validators always have
`exit_epoch = FAR_FUTURE_EPOCH`, and `applyPendingDeposit` never modifies existing `validators`). -/
theorem foldlM_applyPendingDeposit_exiting_iff (ctx : Ctx) :
    ∀ (applied : List PendingDeposit) {init cur : BeaconState P f},
      List.foldlM (applyPendingDeposit ctx) init applied = .ok cur →
      ∀ (pk : BLSPubkey) (i : Nat) (v : Validator),
        (findValidatorIndex cur pk = some i ∧ cur.validators.toArray[i]? = some v ∧
          v.exit_epoch < FAR_FUTURE_EPOCH) ↔
        (findValidatorIndex init pk = some i ∧ init.validators.toArray[i]? = some v ∧
          v.exit_epoch < FAR_FUTURE_EPOCH) := by
  intro applied
  induction applied with
  | nil =>
    intro init cur h pk i v
    cases h
    exact Iff.rfl
  | cons dep rest ih =>
    intro init cur h pk i v
    rw [List.foldlM_cons] at h
    obtain ⟨mid, h1, hrest⟩ := bind_eq_ok_iff.mp h
    rw [ih hrest]
    obtain ⟨_, hpre, hfind_fwd, hnew, hfind_bwd⟩ := applyPendingDeposit_validators_step h1
    constructor
    · rintro ⟨hf_mid, hg_mid, hex⟩
      by_cases hi : i < init.validators.toArray.size
      · rw [hpre i hi] at hg_mid
        exact ⟨hfind_bwd pk i hf_mid hi, hg_mid, hex⟩
      · have hv_ff := (hnew i v (Nat.le_of_not_lt hi) hg_mid).1
        rw [hv_ff] at hex
        exact absurd hex (Nat.lt_irrefl _)
    · rintro ⟨hf_init, hg_init, hex⟩
      have hi : i < init.validators.toArray.size := (Array.getElem?_eq_some_iff.mp hg_init).1
      exact ⟨hfind_fwd pk i hf_init, (hpre i hi).trans hg_init, hex⟩

/-- **`D-S9` `processBlock` `pending_deposits` split (Electra & Fulu):**
Across `processBlock ctx s blk = .ok s'`, `0 < blk.slot.toNat` (`blk.slot ≠ GENESIS_SLOT`) and
`pendingDepositsList s'` equals:
`pendingDepositsList s ++ extraPre ++ drs.map (depositRequestPending · blk.slot) ++ extraPost`,
where:
- `extraPre` comes from `processDeposit` (`applyDeposit` Eth1 bridge deposits, all at `GENESIS_SLOT`,
  and `extraPre = []` in Fulu),
- `drs.map (depositRequestPending · blk.slot)` are the EIP-6110 deposit requests at `blk.slot > 0`,
- `extraPost` comes from `switchToCompoundingValidator` (`queueExcessActiveBalance` during
  `foldConsolidationRequests`, all at `GENESIS_SLOT`). -/
theorem processBlock_pendingDeposits_split (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {blk : BeaconBlock P f}
    (h : processBlock ctx s blk = .ok s') :
    0 < blk.slot.toNat ∧
    blk.slot ≠ GENESIS_SLOT ∧
    ∃ (extraPre extraPost : List PendingDeposit),
      pendingDepositsList s' =
        pendingDepositsList s ++
          extraPre ++
          ((Gated.get hf blk.body.execution_requests).deposits.toArray.toList.map
            (depositRequestPending · blk.slot)) ++
          extraPost ∧
      (f.atLeast .fulu = true → extraPre = []) ∧
      (∀ d ∈ extraPre, d.slot = GENESIS_SLOT) ∧
      (∀ d ∈ extraPost, d.slot = GENESIS_SLOT) := by
  unfold processBlock processBlockWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h7⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, hpos, _, hsl1, _⟩ := processBlockHeader_spec h1
  have hne_gen : blk.slot ≠ GENESIS_SLOT := by
    intro heq; rw [heq] at hpos; exact Nat.lt_irrefl 0 hpos
  have c1 := processBlockHeader_corpusPres h1
  have c2 := processWithdrawals_csub h2
  have c3 := processExecutionPayload_corpusPres ctx h3
  have c4 := processRandao_csub ctx h4
  have c5 := processEth1Data_csub h5
  rw [processOperations_split_all ctx s5 blk.body hf] at h6
  obtain ⟨o1, ho1, h6⟩ := bind_eq_ok_iff.mp h6
  obtain ⟨o2, ho2, h6⟩ := bind_eq_ok_iff.mp h6
  obtain ⟨o3, ho3, ho4⟩ := bind_eq_ok_iff.mp h6
  obtain ⟨_, hsl_o1, _, _, _, hfu_o1, extraPre_raw, hpd_o1, hgen_pre_raw⟩ :=
    preDeposits_cpres_and_frame hf ctx ho1
  have hsl_s5 : s5.slot = blk.slot := by
    rw [c5.slot_eq, c4.slot_eq, c3.2.1, c2.slot_eq, hsl1]
  have hsl_o1_blk : o1.slot = blk.slot := hsl_o1.trans hsl_s5
  obtain ⟨hpd_o2_arr, _, _⟩ := foldDepositRequests_spec hf _ ho2
  rw [hsl_o1_blk] at hpd_o2_arr
  have hpd_o2 : (Gated.get hf o2.pending_deposits).toArray.toList =
      (Gated.get hf o1.pending_deposits).toArray.toList ++
        ((Gated.get hf blk.body.execution_requests).deposits.toArray.toList.map
          (depositRequestPending · blk.slot)) := by
    have h' := congrArg Array.toList hpd_o2_arr
    simpa only [Array.toList_append] using h'
  have co3 := foldWithdrawalRequests_csub ctx.cfg ho3
  obtain ⟨_, extraPost, _, _, _, _, _, _, _, _, _, hpd_o4, hgen_post⟩ :=
    foldConsolidationRequests_frames_and_queues hf ctx.cfg _ ho4
  have c7 := processSyncAggregate_csub ctx h7
  have hpd_s5 : s5.pending_deposits = s.pending_deposits := by
    rw [c5.pd_eq, c4.pd_eq, c3.2.2.2.2, c2.pd_eq, c1.2.2.2.2]
  by_cases hfu : f.atLeast .fulu = true
  · refine ⟨hpos, hne_gen, [], extraPost, ?_, fun _ => rfl,
      (fun _ hm => nomatch hm), hgen_post⟩
    rw [pendingDepositsList_eq_get hf, pendingDepositsList_eq_get hf]
    have ho1_eq : o1.pending_deposits = s.pending_deposits := (hfu_o1 hfu).trans hpd_s5
    rw [c7.pd_eq, hpd_o4, co3.pd_eq, hpd_o2, ho1_eq, List.append_nil]
  · refine ⟨hpos, hne_gen, extraPre_raw, extraPost, ?_,
      fun hh => absurd hh hfu, hgen_pre_raw, hgen_post⟩
    rw [pendingDepositsList_eq_get hf, pendingDepositsList_eq_get hf]
    rw [c7.pd_eq, hpd_o4, co3.pd_eq, hpd_o2, hpd_o1, hpd_s5]

/-- Ordered chain of `processPendingDeposits ctx` invocations transforming queue `q₀` to `q'`,
with `pendingDepositsList` unchanged between consecutive invocations. -/
inductive EpochDepositChain (ctx : Ctx) :
    List PendingDeposit → List (BeaconState P f × BeaconState P f) →
    List PendingDeposit → Prop where
  | nil (q : List PendingDeposit) : EpochDepositChain ctx q [] q
  | cons {q : List PendingDeposit} {w w' : BeaconState P f}
      {rest : List (BeaconState P f × BeaconState P f)} {q_out : List PendingDeposit} :
      pendingDepositsList w = q →
      processPendingDeposits ctx w = .ok w' →
      EpochDepositChain ctx (pendingDepositsList w') rest q_out →
      EpochDepositChain ctx q ((w, w') :: rest) q_out

theorem EpochDepositChain.append {ctx : Ctx}
    {q₀ q₁ q₂ : List PendingDeposit}
    {c₁ c₂ : List (BeaconState P f × BeaconState P f)}
    (h₁ : EpochDepositChain ctx q₀ c₁ q₁)
    (h₂ : EpochDepositChain ctx q₁ c₂ q₂) :
    EpochDepositChain ctx q₀ (c₁ ++ c₂) q₂ := by
  induction h₁ with
  | nil _ => exact h₂
  | cons hw hp _ ih => exact .cons hw hp (ih h₂)

private theorem range'_forIn_deposits_chain (hf : f.atLeast .electra = true) (ctx : Ctx)
    {body : Nat → BeaconState P f → M (ForInStep (BeaconState P f))}
    (hb : ∀ k st r, body k st = .ok r →
      ∃ st1 next st2,
        processSlot st = .ok st1 ∧
        next.toNat = st.slot.toNat + 1 ∧
        (st2 = st1 ∨ processEpoch ctx st1 = .ok st2) ∧
        r = .yield { st2 with slot := next }) :
    ∀ (n start : Nat) (cur out : BeaconState P f),
      forIn (List.range' start n) cur body = .ok out →
      ∃ calls : List (BeaconState P f × BeaconState P f),
        EpochDepositChain ctx (pendingDepositsList cur) calls (pendingDepositsList out)
  | 0, _, cur, out, h => by
    have heq : cur = out := Except.ok.inj h
    subst heq
    exact ⟨[], .nil _⟩
  | n + 1, start, cur, out, h => by
    rw [List.range'_succ, List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨st1, next, st2, hslot, _, hep_or, rfl⟩ := hb start cur r hr
    have hc_slot := processSlot_cpres_and_frame hslot
    rcases hep_or with hst2 | hep
    · rw [hst2] at h
      obtain ⟨calls_rest, hrest⟩ :=
        range'_forIn_deposits_chain hf ctx hb n (start + 1)
          { st1 with slot := next } out h
      have hw'_eq :
          pendingDepositsList { st1 with slot := next } = pendingDepositsList cur :=
        pendingDepositsList_congr hc_slot.2.2.2.2.2.2
      rw [hw'_eq] at hrest
      exact ⟨calls_rest, hrest⟩
    · rw [processEpoch_split_queues hf ctx st1] at hep
      obtain ⟨ep1, hep1, hep⟩ := bind_eq_ok_iff.mp hep
      obtain ⟨ep2, hep2, hep⟩ := bind_eq_ok_iff.mp hep
      obtain ⟨ep3, hep3, hep4⟩ := bind_eq_ok_iff.mp hep
      have c_pre := epochPreQueues_csub hf ctx.cfg hep1
      have c_con := processPendingConsolidations_cpres_and_frame hf ctx.cfg hep3
      have c_post := epochPostQueues_csub ctx hep4
      obtain ⟨calls_rest, hrest⟩ :=
        range'_forIn_deposits_chain hf ctx hb n (start + 1)
          { st2 with slot := next } out h
      have hw_eq : pendingDepositsList ep1 = pendingDepositsList cur :=
        pendingDepositsList_congr (c_pre.pd_eq.trans hc_slot.2.2.2.2.2.2)
      have hw'_eq :
          pendingDepositsList { st2 with slot := next } = pendingDepositsList ep2 :=
        pendingDepositsList_congr (c_post.pd_eq.trans c_con.2.2.2.2)
      rw [hw'_eq] at hrest
      exact ⟨(ep1, ep2) :: calls_rest, .cons hw_eq hep2 hrest⟩

/-- **`D-S9` `processSlots` pending-deposits chain:** `processSlots` changes `pendingDepositsList`
exclusively via an ordered sequence of `processPendingDeposits` invocations. -/
theorem processSlots_pendingDeposits_chain (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {slot : Slot}
    (h : processSlots ctx s slot = .ok s') :
    ∃ calls : List (BeaconState P f × BeaconState P f),
      EpochDepositChain ctx (pendingDepositsList s) calls (pendingDepositsList s') := by
  obtain ⟨_, body, hloop, hb⟩ := processSlots_loop_ok h
  exact range'_forIn_deposits_chain hf ctx hb (slot.toNat - s.slot.toNat) 0 s s' hloop

open Jaune in
/-- **`D-S9` Electra → Fulu crossing decomposition:**
decomposes `jointStep` across the Electra → Fulu fork boundary into:
1. Pre-upgrade Electra `EpochDepositChain` (`callsE`, empty if `beacon.slot = forkSlot`),
2. Verbatim queue copy `pendingDepositsList b2 = pendingDepositsList b1` across `upgradeToFulu`,
3. Post-upgrade Fulu `EpochDepositChain` (`callsF`, empty if `sb.message.slot == b2.slot`),
4. Final `processBlock` on `b_preBlock` producing `b'` with `s' = ⟨.fulu, b', e'⟩`. -/
theorem jointStep_cross_pendingDeposits_chain {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
    {s' : JointState P}
    (h : jointStep cfg ccfg bls ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok s') :
    ∃ (b1 : BeaconState P .electra) (b2 b_preBlock b' : BeaconState P .fulu) (e' : BlockChain)
      (callsE : List (BeaconState P .electra × BeaconState P .electra))
      (callsF : List (BeaconState P .fulu × BeaconState P .fulu)),
      s' = ⟨.fulu, b', e'⟩ ∧
      EpochDepositChain { cfg := ccfg, blsActive := bls } (pendingDepositsList beacon) callsE
        (pendingDepositsList b1) ∧
      upgradeToFulu ccfg b1 = .ok b2 ∧
      pendingDepositsList b2 = pendingDepositsList b1 ∧
      EpochDepositChain { cfg := ccfg, blsActive := bls } (pendingDepositsList b2) callsF
        (pendingDepositsList b_preBlock) ∧
      processBlock { cfg := ccfg, blsActive := bls } b_preBlock sb.message = .ok b' := by
  obtain ⟨_, _, _, _, b1, b2, b', e', _, hb1, hup, _, _, hb', hs'_eq⟩ :=
    jointStep_cross_ok_iff.mp h
  have hup_pdl := upgradeToFulu_pendingDepositsList ccfg hup
  have hE : ∃ callsE : List (BeaconState P .electra × BeaconState P .electra),
      EpochDepositChain { cfg := ccfg, blsActive := bls }
        (pendingDepositsList beacon) callsE (pendingDepositsList b1) := by
    split at hb1
    · exact processSlots_pendingDeposits_chain rfl _ hb1
    · cases hb1; exact ⟨[], .nil _⟩
  obtain ⟨callsE, hcallsE⟩ := hE
  split at hb'
  · obtain ⟨hpb, _⟩ := atSlot_block_split hb'
    exact ⟨b1, b2, b2, b', e', callsE, [], hs'_eq, hcallsE, hup, hup_pdl, .nil _, hpb⟩
  · obtain ⟨mid, hps2, hpb, _⟩ := stateTransition_true_split hb'
    obtain ⟨callsF, hcallsF⟩ := processSlots_pendingDeposits_chain rfl _ hps2
    exact ⟨b1, b2, mid, b', e', callsE, callsF, hs'_eq, hcallsE, hup, hup_pdl, hcallsF, hpb⟩

end JauneConsensus.Facts
