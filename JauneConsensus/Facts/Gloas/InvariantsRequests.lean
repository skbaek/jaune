import JauneConsensus.Facts.Gloas.InvariantsPhases

/-!
# The parent payload's builder requests for the G3 invariants (goal `eip8282-gloas-cross-layer-v1`, G3a)

* `processParentExecutionPayload_cases`: an EMPTY parent leaves the state; a FULL parent is the
  prefix (settlement and validator requests), the builder-deposit loop, the builder-exit loop and
  the suffix (availability and `latest_block_hash := L.block_hash`);
* `depReq_cases`, `exitReq_cases`: what one builder deposit or exit request writes;
* `forIn_yield_inv`: an invariant of a request loop.
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-! ## Epochs -/

theorem computeEpochAtSlot_toNat {slot e : U64} (h : computeEpochAtSlot P slot = .ok e) :
    e.toNat = slot.toNat / P.SLOTS_PER_EPOCH := by
  unfold computeEpochAtSlot at h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  rw [U64.toNat_div? h, U64.toNat_ofNat? hspe]

theorem getCurrentEpoch_toNat {m : GSt P} {e : U64}
    (h : JauneConsensus.Gloas.getCurrentEpoch m = .ok e) : e.toNat = curEpoch m :=
  computeEpochAtSlot_toNat h

/-- With `2 ≤ SLOTS_PER_EPOCH`, an epoch read from a slot is below `FAR_FUTURE_EPOCH`. -/
theorem epoch_lt_far (hspe : 2 ≤ P.SLOTS_PER_EPOCH) (m : GSt P) :
    curEpoch m < FAR_FUTURE_EPOCH.toNat := by
  unfold curEpoch
  have h1 := U64.toNat_lt m.slot
  have h2 : m.slot.toNat / P.SLOTS_PER_EPOCH ≤ m.slot.toNat / 2 := Nat.div_le_div_left hspe (by decide)
  have h3 : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  omega

/-! ## Request loops -/

theorem forIn_yield_inv {α σ : Type} (I : σ → Prop) (f : σ → α → M σ)
    (hf : ∀ m a m', I m → f m a = .ok m' → I m') :
    ∀ (xs : List α) (init out : σ),
      forIn xs init (fun op s => do let s' ← f s op; pure (ForInStep.yield s')) = .ok out →
      I init → I out
  | [], init, out, h, hI => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hI
  | a :: l, init, out, h, hI => by
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨m', hm', hr⟩ := bind_eq_ok_iff.mp hr
    cases hr
    exact forIn_yield_inv I f hf l m' out h (hf _ _ _ hI hm')

/-! ## The parent payload -/

/-- The suffix writes availability and `latest_block_hash := L.block_hash` (of the pre-state). -/
theorem applyParentSuffix_post {st0 e s1 : GSt P}
    (h : JauneConsensus.Gloas.applyParentSuffix st0 e = .ok s1) :
    s1.builders = e.builders ∧ s1.builder_pending_payments = e.builder_pending_payments ∧
      s1.builder_pending_withdrawals = e.builder_pending_withdrawals ∧
      s1.latest_execution_payload_bid = e.latest_execution_payload_bid ∧
      s1.latest_block_hash = st0.latest_execution_payload_bid.block_hash ∧
      s1.latest_block_header = e.latest_block_header ∧ s1.slot = e.slot ∧
      s1.next_withdrawal_builder_index = e.next_withdrawal_builder_index := by
  unfold JauneConsensus.Gloas.applyParentSuffix at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An EMPTY parent leaves the state; a FULL parent is the prefix, the two builder loops and the
suffix. -/
theorem processParentExecutionPayload_cases {ctx : Ctx} {s s1 : GSt P}
    {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processParentExecutionPayload ctx s blk = .ok s1) :
    (s1 = s ∧ blk.body.signed_execution_payload_bid.message.parent_block_hash ≠
        s.latest_execution_payload_bid.block_hash) ∨
    (blk.body.signed_execution_payload_bid.message.parent_block_hash =
        s.latest_execution_payload_bid.block_hash ∧
      ∃ a d e : GSt P,
        JauneConsensus.Gloas.applyParentPrefix ctx s blk.body.parent_execution_requests = .ok a ∧
        forIn blk.body.parent_execution_requests.builder_deposits.toArray.toList a
          (fun op s => do
            let s' ← JauneConsensus.Gloas.processBuilderDepositRequest ctx s op
            pure (ForInStep.yield s')) = .ok d ∧
        forIn blk.body.parent_execution_requests.builder_exits.toArray.toList d
          (fun op s => do
            let s' ← JauneConsensus.Gloas.processBuilderExitRequest ctx.cfg s op
            pure (ForInStep.yield s')) = .ok e ∧
        JauneConsensus.Gloas.applyParentSuffix s e = .ok s1) := by
  unfold JauneConsensus.Gloas.processParentExecutionPayload at h
  simp only [] at h
  split at h
  · rename_i hne
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    cases h
    refine Or.inl ⟨rfl, fun heq => ?_⟩
    rw [heq] at hne
    simp at hne
  · rename_i hne
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    rw [JauneConsensus.Gloas.applyParentExecutionPayload_eq] at h
    obtain ⟨a, ha, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨d, hd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
    refine Or.inr ⟨?_, a, d, e, ha, hd, he, h⟩
    simpa using hne

/-! ## One builder request -/

/-- What one builder deposit request writes: nothing, a top-up of a known builder (resetting an
exited, swept builder's `withdrawable_epoch` to `epoch + MIN_BUILDER_WITHDRAWABILITY_DELAY`), or a
fresh record for a new pubkey at `get_index_for_new_builder` (the end of the registry or a
reusable slot). Only the builders change. -/
theorem depReq_cases {ctx : Ctx} {m m' : GSt P} {r : JauneConsensus.Gloas.BuilderDepositRequest}
    (h : JauneConsensus.Gloas.processBuilderDepositRequest ctx m r = .ok m') :
    m' = { m with builders := m'.builders } ∧
    (m'.builders = m.builders ∨
      (∃ (i : Nat) (b b' : JauneConsensus.Gloas.Builder), m.builders.toArray[i]? = some b ∧ m'.builders.toArray[i]? = some b' ∧
        m'.builders.toArray.size = m.builders.toArray.size ∧
        (∀ j, j ≠ i → m'.builders.toArray[j]? = m.builders.toArray[j]?) ∧
        SameIdentity b b' ∧ b'.balance.toNat = b.balance.toNat + r.amount.toNat ∧
        (b'.withdrawable_epoch = b.withdrawable_epoch ∨
          (b.withdrawable_epoch ≠ FAR_FUTURE_EPOCH ∧ b.balance = U64.zero ∧
            b'.withdrawable_epoch.toNat = curEpoch m + ctx.cfg.MIN_BUILDER_WITHDRAWABILITY_DELAY))) ∨
      (∃ (i : Nat) (b' : JauneConsensus.Gloas.Builder), (∀ b ∈ m.builders.toArray, b.pubkey ≠ r.pubkey) ∧
        (i = m.builders.toArray.size ∨ ∃ b, m.builders.toArray[i]? = some b ∧
          Reusable b (curEpoch m)) ∧
        m'.builders.toArray[i]? = some b' ∧ b'.pubkey = r.pubkey ∧
        b'.version = JauneConsensus.Gloas.PAYLOAD_BUILDER_VERSION ∧
        b'.withdrawable_epoch = FAR_FUTURE_EPOCH ∧
        m.builders.toArray.size ≤ m'.builders.toArray.size ∧
        (∀ j, j ≠ i → m'.builders.toArray[j]? = m.builders.toArray[j]?))) := by
  have h0 := h
  rw [processBuilderDepositRequest_eq] at h0
  obtain ⟨o, hco, _⟩ := bind_eq_ok_iff.mp h0
  obtain ⟨hpre, hbad, htop, hreg⟩ := classifyBuilderDeposit_effect hco h
  have hmean := classifyBuilderDeposit_meaning hco
  cases o with
  | ignoredPrefix => rw [hpre rfl]; exact ⟨rfl, Or.inl rfl⟩
  | ignoredBadSignature => rw [hbad rfl]; exact ⟨rfl, Or.inl rfl⟩
  | topUp i a reset =>
    obtain ⟨b, b', hb, hb', hsz, hoth, hpk, hv, hadr, _, hbal, hres, hnres, hm⟩ := htop i a reset rfl
    obtain ⟨_, _, ha, b0, hb0, hreset⟩ := (hmean.2.1 i a reset).mp rfl
    rw [hb] at hb0; cases hb0
    subst ha
    refine ⟨hm, Or.inr (Or.inl ⟨i, b, b', hb, hb', hsz, hoth, ⟨hpk, hv, hadr⟩, hbal, ?_⟩)⟩
    cases reset with
    | false => exact Or.inl (hnres rfl)
    | true =>
      obtain ⟨hne, hz⟩ := hreset.mp rfl
      obtain ⟨e, he, hw⟩ := hres rfl
      exact Or.inr ⟨hne, hz, by rw [hw, getCurrentEpoch_toNat he]⟩
  | register i a =>
    obtain ⟨addr, e, _, he, hb', hsz, hoth, hm⟩ := hreg i a rfl
    obtain ⟨_, hnot, _, _, idx, hidx, hi⟩ := (hmean.2.2.2 i a).mp rfl
    obtain ⟨e', he', hcase⟩ := getIndexForNewBuilder_spec hidx
    have hee : e'.toNat = curEpoch m := getCurrentEpoch_toNat he'
    refine ⟨hm, Or.inr (Or.inr ⟨i, _, hnot, ?_, hb', rfl, rfl, rfl, hsz, hoth⟩)⟩
    rcases hcase with hc | ⟨b, hb, hw, hz⟩
    · exact Or.inl (hi ▸ hc)
    · refine Or.inr ⟨b, hi ▸ hb, ?_, hz⟩
      have : b.withdrawable_epoch.toNat ≤ e'.toNat := hw
      omega

theorem exit_initiate_facts {cfg : Config} {m : GSt P} {r : JauneConsensus.Gloas.BuilderExitRequest}
    {i : Nat} (hco : classifyBuilderExit cfg m r = .ok (.initiate i)) :
    ∃ b bi, m.builders.toArray[i]? = some b ∧ U64.ofNat? i "BuilderIndex" = .ok bi ∧
      b.withdrawable_epoch = FAR_FUTURE_EPOCH ∧
      JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder m bi = .ok U64.zero := by
  rcases classifyBuilderExit_inv hco with ⟨_, h⟩ | ⟨i', b, bi, _, hb, hbi, hcase⟩
  · cases h
  · rcases hcase with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨⟨_, hfar⟩, _, p, hp, ⟨_, h⟩ | ⟨hp0, h⟩⟩
    · cases h
    · cases h
    · cases h
    · cases h
      subst hp0
      exact ⟨b, bi, hb, hbi, hfar, hp⟩

/-- What one builder exit request writes: nothing, or `withdrawable_epoch := epoch +
MIN_BUILDER_WITHDRAWABILITY_DELAY` for an active builder with nothing pending. Only the builders
change. -/
theorem exitReq_cases {cfg : Config} {m m' : GSt P} {r : JauneConsensus.Gloas.BuilderExitRequest}
    (h : JauneConsensus.Gloas.processBuilderExitRequest cfg m r = .ok m') :
    m' = { m with builders := m'.builders } ∧
    (m' = m ∨
      ∃ (i : Nat) (b : JauneConsensus.Gloas.Builder) (w : U64), m.builders.toArray[i]? = some b ∧
        m'.builders.toArray[i]? = some { b with withdrawable_epoch := w } ∧
        b.withdrawable_epoch = FAR_FUTURE_EPOCH ∧
        (∃ bi, U64.ofNat? i "BuilderIndex" = .ok bi ∧
          JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder m bi = .ok U64.zero) ∧
        w.toNat = curEpoch m + cfg.MIN_BUILDER_WITHDRAWABILITY_DELAY ∧
        m'.builders.toArray.size = m.builders.toArray.size ∧
        (∀ j, j ≠ i → m'.builders.toArray[j]? = m.builders.toArray[j]?)) := by
  have h0 := h
  rw [processBuilderExitRequest_eq] at h0
  obtain ⟨o, hco, _⟩ := bind_eq_ok_iff.mp h0
  obtain ⟨hign, hini⟩ := classifyBuilderExit_effect hco h
  cases o with
  | initiate i =>
    obtain ⟨b, e, w, hb, he, hw, hb', hsz, hoth, hm⟩ := hini i rfl
    obtain ⟨b0, bi, hb0, hbi, hfar, hpend⟩ := exit_initiate_facts hco
    rw [hb] at hb0; cases hb0
    refine ⟨hm, Or.inr ⟨i, b, w, hb, hb', hfar, ⟨bi, hbi, hpend⟩, ?_, hsz, hoth⟩⟩
    rw [hw, getCurrentEpoch_toNat he]
  | _ =>
    have := hign (fun _ h => by cases h)
    subst this
    exact ⟨rfl, Or.inl rfl⟩

end JauneConsensus.Facts.Gloas.Inv
