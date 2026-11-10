import JauneConsensus.Facts.Gloas.InvariantsPhases
import JauneConsensus.Facts.Gloas.InvariantsRequests
import JauneConsensus.Facts.Gloas.InvariantsSlots

/-!
# The anchor invariant FinalizedNotAhead (goal `eip8282-gloas-cross-layer-v1`, G3d)

`FinalizedNotAhead s`: `finalized_checkpoint.epoch ≤ get_current_epoch(s)`, stated on the Gloas
state (`FinalizedNotAhead`) and on the fork-indexed state (`FinalizedNotAheadF`, for the Fulu
anchors). Master decision eip8282-finalized-not-ahead-invariant-20261110: B1's post-state clause
is false without it (a fresh builder's `deposit_epoch` is the current epoch, and an anchor with
`finalized.epoch > current` makes it active, so a same-payload exit request could initiate its
exit); on reachable states it holds.

Preservation:

* a block writes neither the finalized checkpoint nor the slot (`FinSlot`, the generator of
  `Step.lean` at a new relation, for every phase of the Gloas and the fork-indexed block);
* the epoch step writes the finalized checkpoint only in `weigh_justification_and_finalization`,
  to a checkpoint whose epoch plus a positive `k` is the current epoch (`FinEp E`: the slot is
  kept and the checkpoint is kept or below `E`), and `process_slots` advances the slot only
  forward;
* the crossing (`crossFromFulu`, `upgrade_to_gloas`) copies the checkpoint and the slot.
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-! ## The invariant -/

/-- **FinalizedNotAhead** (Gloas): `finalized_checkpoint.epoch ≤ get_current_epoch(state)`. -/
def FinalizedNotAhead (s : GSt P) : Prop :=
  s.finalized_checkpoint.epoch.toNat ≤ curEpoch s

/-- **FinalizedNotAhead** on the fork-indexed state (the Fulu anchors). -/
def FinalizedNotAheadF {f : CFork} (s : BeaconState P f) : Prop :=
  s.finalized_checkpoint.epoch.toNat ≤ s.slot.toNat / P.SLOTS_PER_EPOCH

/-! ## The relations -/

/-- The finalized checkpoint and the slot are unchanged. -/
def FinSlot (s s' : GSt P) : Prop :=
  s'.finalized_checkpoint = s.finalized_checkpoint ∧ s'.slot = s.slot

def finSlot : StepRel (GSt P) where
  R := FinSlot
  refl _ := ⟨rfl, rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem FinSlot.fna {s s' : GSt P} (h : FinSlot s s') (hf : FinalizedNotAhead s) :
    FinalizedNotAhead s' := by
  unfold FinalizedNotAhead curEpoch at *; rw [h.1, h.2]; exact hf

/-! ## The Gloas block -/

section Block

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinSlot _ _ from ⟨rfl, rfl⟩))

theorem increaseBalance_fs (s : GSt P) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.increaseBalance s i d) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.increaseBalance; gvcg

theorem decreaseBalance_fs (s : GSt P) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.decreaseBalance s i d) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.decreaseBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (increaseBalance_fs _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (decreaseBalance_fs _ _ _) $h; exact hh))

theorem computeExitEpochAndUpdateChurn_fs (cfg : Config) (s : GSt P) (b : Gwei) :
    Ok (JauneConsensus.Gloas.computeExitEpochAndUpdateChurn cfg s b)
      (fun p => finSlot.R s p.1) := by
  unfold JauneConsensus.Gloas.computeExitEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (computeExitEpochAndUpdateChurn_fs _ _ _) $h; exact hh))

theorem initiateValidatorExit_fs (cfg : Config) (s : GSt P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.initiateValidatorExit cfg s i) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.initiateValidatorExit; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (initiateValidatorExit_fs _ _ _) $h; exact hh))

theorem queueExcessActiveBalance_fs (s : GSt P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.queueExcessActiveBalance s i) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.queueExcessActiveBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (queueExcessActiveBalance_fs _ _) $h; exact hh))

theorem switchToCompoundingValidator_fs (s : GSt P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.switchToCompoundingValidator s i) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.switchToCompoundingValidator; gvcg
  all_goals exact StepRel.ok_rebase finSlot ⟨rfl, rfl⟩ (queueExcessActiveBalance_fs _ _)

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (switchToCompoundingValidator_fs _ _) $h; exact hh))

theorem computeConsolidationEpochAndUpdateChurn_fs (cfg : Config) (s : GSt P) (b : Gwei) :
    Ok (JauneConsensus.Gloas.computeConsolidationEpochAndUpdateChurn cfg s b)
      (fun p => finSlot.R s p.1) := by
  unfold JauneConsensus.Gloas.computeConsolidationEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (computeConsolidationEpochAndUpdateChurn_fs _ _ _) $h; exact hh))

theorem processWithdrawalRequest_fs (cfg : Config) (s : GSt P) (wr : WithdrawalRequest) :
    Ok (JauneConsensus.Gloas.processWithdrawalRequest cfg s wr) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processWithdrawalRequest; gvcg
  all_goals exact fun x hx => initiateValidatorExit_fs _ _ _ x hx

theorem processConsolidationRequest_fs (cfg : Config) (s : GSt P) (cr : ConsolidationRequest) :
    Ok (JauneConsensus.Gloas.processConsolidationRequest cfg s cr) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processConsolidationRequest; gvcg
  all_goals exact switchToCompoundingValidator_fs _ _

theorem settleBuilderPayment_fs (s : GSt P) (i : U64) :
    Ok (JauneConsensus.Gloas.settleBuilderPayment s i) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.settleBuilderPayment; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processWithdrawalRequest_fs _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processConsolidationRequest_fs _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (settleBuilderPayment_fs _ _) $h; exact hh))

section Prefix

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine finSlot.trans ?_ (StepRel.forIn_array_rel finSlot id ?_ _ _ $h)
               · exact (show FinSlot _ _ from ⟨rfl, rfl⟩)
               · intro _ _; gvcg))

theorem applyParentPrefix_fs (ctx : Ctx) (s : GSt P)
    (r : JauneConsensus.Gloas.ExecutionRequests) :
    Ok (JauneConsensus.Gloas.applyParentPrefix ctx s r) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.applyParentPrefix; gvcg

end Prefix

theorem processBuilderDepositRequest_fs (ctx : Ctx) (s : GSt P)
    (r : JauneConsensus.Gloas.BuilderDepositRequest) :
    Ok (JauneConsensus.Gloas.processBuilderDepositRequest ctx s r) (finSlot.R s) := by
  intro s' h
  have := (processBuilderDepositRequest_frame h).2.2.2.2.2
  rw [this]; exact ⟨rfl, rfl⟩

theorem processBuilderExitRequest_fs (cfg : Config) (s : GSt P)
    (r : JauneConsensus.Gloas.BuilderExitRequest) :
    Ok (JauneConsensus.Gloas.processBuilderExitRequest cfg s r) (finSlot.R s) := by
  intro s' h
  have := (processBuilderExitRequest_frame h).2.2.2.2.2
  rw [this]; exact ⟨rfl, rfl⟩

theorem applyParentSuffix_fs (st0 s : GSt P) :
    Ok (JauneConsensus.Gloas.applyParentSuffix st0 s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.applyParentSuffix; gvcg

theorem processParentExecutionPayload_fs (ctx : Ctx) (s : GSt P)
    (blk : JauneConsensus.Gloas.BeaconBlock P) :
    Ok (JauneConsensus.Gloas.processParentExecutionPayload ctx s blk) (finSlot.R s) := by
  intro s1 h1
  rcases processParentExecutionPayload_cases h1 with ⟨rfl, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · exact finSlot.refl _
  have pa := applyParentPrefix_fs ctx s _ a ha
  have pd : FinSlot s d := forIn_yield_inv (FinSlot s) _
    (fun _ _ _ hI hm => finSlot.trans hI (processBuilderDepositRequest_fs _ _ _ _ hm)) _ _ _ hd pa
  have pe : FinSlot s e := forIn_yield_inv (FinSlot s) _
    (fun _ _ _ hI hm => finSlot.trans hI (processBuilderExitRequest_fs _ _ _ _ hm)) _ _ _ he pd
  exact finSlot.trans pe (applyParentSuffix_fs _ _ _ hs)

theorem processBlockHeader_fs (s : GSt P) (blk : JauneConsensus.Gloas.BeaconBlock P) :
    Ok (JauneConsensus.Gloas.processBlockHeader s blk) (finSlot.R s) := by
  intro s' h
  rw [(processBlockHeader_post h).2.2]; exact ⟨rfl, rfl⟩

theorem applyWithdrawals_fs (s : GSt P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.applyWithdrawals s ws) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.applyWithdrawals; gvcg

theorem updateNextWithdrawalIndex_fs (s : GSt P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalIndex s ws) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalIndex; gvcg

theorem updateNextWithdrawalBuilderIndex_fs (s : GSt P) (n : U64) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex s n) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex; gvcg

theorem updateNextWithdrawalValidatorIndex_fs (s : GSt P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex s ws) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (applyWithdrawals_fs _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (updateNextWithdrawalIndex_fs _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (updateNextWithdrawalBuilderIndex_fs _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (updateNextWithdrawalValidatorIndex_fs _ _) $h; exact hh))

theorem processWithdrawals_fs (s : GSt P) :
    Ok (JauneConsensus.Gloas.processWithdrawals s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processWithdrawals; gvcg
  all_goals exact updateNextWithdrawalValidatorIndex_fs _ _

set_option maxHeartbeats 1000000 in
theorem processExecutionPayloadBid_fs (ctx : Ctx) (s : GSt P)
    (sb : JauneConsensus.Gloas.SignedExecutionPayloadBid) :
    Ok (JauneConsensus.Gloas.processExecutionPayloadBid ctx s sb) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processExecutionPayloadBid; gvcg
  all_goals (apply ok_pure; rename_i hlast; cases hlast; exact ⟨rfl, rfl⟩)

theorem processRandao_fs (ctx : Ctx) (s : GSt P) (body : JauneConsensus.Gloas.BeaconBlockBody P) :
    Ok (JauneConsensus.Gloas.processRandao ctx s body) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processRandao; gvcg

theorem processEth1Data_fs (s : GSt P) (body : JauneConsensus.Gloas.BeaconBlockBody P) :
    Ok (JauneConsensus.Gloas.processEth1Data s body) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processEth1Data; gvcg

set_option maxHeartbeats 2000000 in
theorem processSyncAggregate_fs (ctx : Ctx) (s : GSt P) (sa : SyncAggregate P) :
    Ok (JauneConsensus.Gloas.processSyncAggregate ctx s sa) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processSyncAggregate; gvcg

theorem slashValidator_fs (cfg : Config) (s : GSt P) (i : ValidatorIndex)
    (wb : Option ValidatorIndex) :
    Ok (JauneConsensus.Gloas.slashValidator cfg s i wb) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.slashValidator; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (slashValidator_fs _ _ _ _) $h; exact hh))

theorem processProposerSlashing_fs (ctx : Ctx) (s : GSt P) (ps : ProposerSlashing) :
    Ok (JauneConsensus.Gloas.processProposerSlashing ctx s ps) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processProposerSlashing; gvcg
  all_goals exact slashValidator_fs _ _ _ _

theorem processAttesterSlashing_fs (ctx : Ctx) (s : GSt P)
    (as : JauneConsensus.Gloas.AttesterSlashing) :
    Ok (JauneConsensus.Gloas.processAttesterSlashing ctx s as) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processAttesterSlashing; gvcg

theorem processVoluntaryExit_fs (ctx : Ctx) (s : GSt P) (sve : SignedVoluntaryExit) :
    Ok (JauneConsensus.Gloas.processVoluntaryExit ctx s sve) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processVoluntaryExit; gvcg
  all_goals exact fun x hx => initiateValidatorExit_fs _ _ _ x hx

theorem processBlsToExecutionChange_fs (ctx : Ctx) (s : GSt P)
    (sac : SignedBLSToExecutionChange) :
    Ok (JauneConsensus.Gloas.processBlsToExecutionChange ctx s sac) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processBlsToExecutionChange; gvcg

theorem processPayloadAttestation_fs (ctx : Ctx) (s : GSt P)
    (pa : JauneConsensus.Gloas.PayloadAttestation P) :
    Ok (JauneConsensus.Gloas.processPayloadAttestation ctx s pa) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processPayloadAttestation; gvcg

section Attestation

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (increaseBalance_fs _ _ _) $h; exact (finSlot.trans (by split <;> exact ⟨rfl, rfl⟩) hh)))

set_option maxHeartbeats 2000000 in
theorem processAttestation_fs (ctx : Ctx) (s : GSt P)
    (a : JauneConsensus.Gloas.Attestation P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processAttestation ctx s a ps) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processAttestation; gvcg

end Attestation

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processProposerSlashing_fs _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processAttesterSlashing_fs _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processAttestation_fs _ _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processVoluntaryExit_fs _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processBlsToExecutionChange_fs _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processPayloadAttestation_fs _ _ _) $h; exact hh))

theorem processOperations_fs (ctx : Ctx) (s : GSt P)
    (body : JauneConsensus.Gloas.BeaconBlockBody P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processOperations ctx s body ps) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processOperations; gvcg

/-- **A Gloas block keeps the finalized checkpoint and the slot.** -/
theorem processBlock_finSlot {ctx : Ctx} {s s' : GSt P} {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') : FinSlot s s' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  exact finSlot.trans (processParentExecutionPayload_fs _ _ _ _ h1)
    (finSlot.trans (processBlockHeader_fs _ _ _ h2)
    (finSlot.trans (processWithdrawals_fs _ _ h3)
    (finSlot.trans (processExecutionPayloadBid_fs _ _ _ _ h4)
    (finSlot.trans (processRandao_fs _ _ _ _ h5)
    (finSlot.trans (processEth1Data_fs _ _ _ h6)
    (finSlot.trans (processOperations_fs _ _ _ _ _ h7)
      (processSyncAggregate_fs _ _ _ _ h8)))))))

/-- **A Gloas block preserves FinalizedNotAhead.** -/
theorem processBlock_finalizedNotAhead {ctx : Ctx} {s s' : GSt P}
    {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') (hf : FinalizedNotAhead s) :
    FinalizedNotAhead s' :=
  (processBlock_finSlot h).fna hf

end Block

/-! ## The Gloas epoch -/

/-- The slot is kept, and the finalized checkpoint is kept or has an epoch below `E`. -/
def FinEp (E : Nat) (s s' : GSt P) : Prop :=
  s'.slot = s.slot ∧
    (s'.finalized_checkpoint = s.finalized_checkpoint ∨ s'.finalized_checkpoint.epoch.toNat < E)

def finEp (E : Nat) : StepRel (GSt P) where
  R := FinEp E
  refl _ := ⟨rfl, Or.inl rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, by
    rcases h₂.2 with h | h
    · rw [h]; exact h₁.2
    · exact Or.inr h⟩

theorem FinSlot.finEp {E : Nat} {s s' : GSt P} (h : FinSlot s s') : FinEp E s s' :=
  ⟨h.2, Or.inl h.1⟩

/-- A finalization rule that fired (`all(bits) and cp.epoch + k == current_epoch`, with
`k ≥ 1`) finalizes a checkpoint of an epoch before the current one. -/
theorem finalizes_lt {ce k : U64} {cp : Checkpoint} {a : Bool} {lift : M Bool} {site : String}
    (h : (lift >>= fun l => if l = true then
        (U64.add? cp.epoch k site >>= fun e => pure (e == ce)) else pure false) = .ok a)
    (ha : a = true) (hk : 1 ≤ k.toNat) : cp.epoch.toNat < ce.toNat := by
  subst ha
  obtain ⟨l, -, h⟩ := bind_eq_ok_iff.mp h
  cases l
  · simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
  · simp only [↓reduceIte] at h
    obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    have hee := U64.beq_eq_true_iff.mp h
    subst hee
    have := U64.toNat_add? he
    omega

section Weigh

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinEp _ _ _ from ⟨rfl, Or.inl rfl⟩))

theorem weighJustificationAndFinalization_fe (s : GSt P) (t p c : Gwei) :
    Ok (JauneConsensus.Gloas.weighJustificationAndFinalization s t p c)
      ((finEp (curEpoch s)).R s) := by
  unfold JauneConsensus.Gloas.weighJustificationAndFinalization; jvcg
  all_goals
    refine StepRel.ok_rebase _ ?_ (JpOk2.call ‹_› _ _)
    rename_i hfin _ _ ha
    have hlt := finalizes_lt hfin ha (by
      first
      | (rw [c64_toNat ‹c64 3 = .ok _›]; decide)
      | (rw [c64_toNat ‹c64 2 = .ok _›]; decide)
      | decide)
    have hce := getCurrentEpoch_toNat ‹JauneConsensus.Gloas.getCurrentEpoch s = _›
    refine ⟨rfl, Or.inr ?_⟩
    dsimp only
    omega

end Weigh

section Epoch

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinSlot _ _ from ⟨rfl, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (increaseBalance_fs _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (decreaseBalance_fs _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (computeExitEpochAndUpdateChurn_fs _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (initiateValidatorExit_fs _ _ _) $h; exact hh))

theorem addValidatorToRegistry_fs (s : GSt P) (pk : BLSPubkey) (wc : Bytes32) (amount : Gwei) :
    Ok (JauneConsensus.Gloas.addValidatorToRegistry s pk wc amount) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.addValidatorToRegistry; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (addValidatorToRegistry_fs _ _ _ _) $h; exact hh))

theorem applyPendingDeposit_fs (ctx : Ctx) (s : GSt P) (d : PendingDeposit) :
    Ok (JauneConsensus.Gloas.applyPendingDeposit ctx s d) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.applyPendingDeposit; gvcg
  · exact addValidatorToRegistry_fs _ _ _ _
  · exact increaseBalance_fs _ _ _

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (applyPendingDeposit_fs _ _ _) $h; exact hh))

theorem processInactivityUpdates_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processInactivityUpdates cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processInactivityUpdates; gvcg

theorem processRewardsAndPenalties_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processRewardsAndPenalties cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processRewardsAndPenalties; gvcg

theorem processRegistryUpdates_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processRegistryUpdates cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processRegistryUpdates; gvcg

theorem processSlashings_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processSlashings cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processSlashings; gvcg

theorem processEth1DataReset_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processEth1DataReset cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processEth1DataReset; gvcg

section PendingDeposits

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRel.forIn_array_rel _ (fun x => x.2.2.2.2) ?_ _ _ $h; intro _ _; gvcg))

theorem processPendingDeposits_fs (ctx : Ctx) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processPendingDeposits ctx s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processPendingDeposits; gvcg

end PendingDeposits

theorem processPendingConsolidations_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processPendingConsolidations cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processPendingConsolidations; gvcg

theorem processBuilderPendingPayments_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processBuilderPendingPayments cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processBuilderPendingPayments; gvcg

theorem processEffectiveBalanceUpdates_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processEffectiveBalanceUpdates cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processEffectiveBalanceUpdates; gvcg

theorem processSlashingsReset_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processSlashingsReset cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processSlashingsReset; gvcg

theorem processRandaoMixesReset_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processRandaoMixesReset cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processRandaoMixesReset; gvcg

theorem processHistoricalSummariesUpdate_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processHistoricalSummariesUpdate cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processHistoricalSummariesUpdate; gvcg

theorem processParticipationFlagUpdates_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processParticipationFlagUpdates cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processParticipationFlagUpdates; gvcg

theorem processSyncCommitteeUpdates_fs (ctx : Ctx) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processSyncCommitteeUpdates ctx s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processSyncCommitteeUpdates; gvcg

theorem processProposerLookahead_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processProposerLookahead cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processProposerLookahead; gvcg

theorem processPtcWindow_fs (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processPtcWindow cfg s) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.processPtcWindow; gvcg

end Epoch

section EpochFE

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinEp _ _ _ from ⟨rfl, Or.inl rfl⟩))

theorem processJustificationAndFinalization_fe (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processJustificationAndFinalization cfg s)
      ((finEp (curEpoch s)).R s) := by
  unfold JauneConsensus.Gloas.processJustificationAndFinalization; gvcg
  all_goals exact weighJustificationAndFinalization_fe _ _ _ _

/-- **The Gloas epoch step** keeps the slot, and keeps the finalized checkpoint or moves it to
an epoch before the current one. -/
theorem processEpoch_fe {ctx : Ctx} {s s' : GSt P}
    (h : JauneConsensus.Gloas.processEpoch ctx s = .ok s') : FinEp (curEpoch s) s s' := by
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
  have f1 := processJustificationAndFinalization_fe _ _ _ h1
  have f : FinSlot x1 s' :=
    finSlot.trans (processInactivityUpdates_fs _ _ _ h2)
    (finSlot.trans (processRewardsAndPenalties_fs _ _ _ h3)
    (finSlot.trans (processRegistryUpdates_fs _ _ _ h4)
    (finSlot.trans (processSlashings_fs _ _ _ h5)
    (finSlot.trans (processEth1DataReset_fs _ _ _ h6)
    (finSlot.trans (processPendingDeposits_fs _ _ _ h7)
    (finSlot.trans (processPendingConsolidations_fs _ _ _ h8)
    (finSlot.trans (processBuilderPendingPayments_fs _ _ _ h9)
    (finSlot.trans (processEffectiveBalanceUpdates_fs _ _ _ h10)
    (finSlot.trans (processSlashingsReset_fs _ _ _ h11)
    (finSlot.trans (processRandaoMixesReset_fs _ _ _ h12)
    (finSlot.trans (processHistoricalSummariesUpdate_fs _ _ _ h13)
    (finSlot.trans (processParticipationFlagUpdates_fs _ _ _ h14)
    (finSlot.trans (processSyncCommitteeUpdates_fs _ _ _ h15)
    (finSlot.trans (processProposerLookahead_fs _ _ _ h16)
      (processPtcWindow_fs _ _ _ h)))))))))))))))
  exact (finEp _).trans f1 f.finEp

end EpochFE

theorem processSlot_fs (s : GSt P) :
    Ok (JauneConsensus.Gloas.processSlot s) (finSlot.R s) := by
  rw [processSlot_eq]
  intro s' h
  unfold processSlotH at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine ⟨?_, ?_⟩ <;> split <;> rfl

/-- One slot of the loop keeps FinalizedNotAhead: `process_slot`, at a boundary `process_epoch`,
then `slot := slot + 1`. -/
theorem slotIter_fna {st st1 st2 : GSt P} {next : U64} (hI : FinalizedNotAhead st)
    (f1 : FinSlot st st1) (hnext : next.toNat = st.slot.toNat + 1)
    (h2 : st2 = st1 ∨ FinEp (curEpoch st1) st1 st2) :
    FinalizedNotAhead { st2 with slot := next } := by
  have hmono : curEpoch st ≤ next.toNat / P.SLOTS_PER_EPOCH := by
    unfold curEpoch; rw [hnext]; exact Nat.div_le_div_right (by omega)
  have hc1 : curEpoch st1 = curEpoch st := by unfold curEpoch; rw [f1.2]
  have hf1 : st1.finalized_checkpoint = st.finalized_checkpoint := f1.1
  unfold FinalizedNotAhead at hI ⊢
  show st2.finalized_checkpoint.epoch.toNat ≤ next.toNat / P.SLOTS_PER_EPOCH
  rcases h2 with rfl | ⟨-, hf | hf⟩
  · rw [hf1]; omega
  · rw [hf, hf1]; omega
  · omega

/-- **Gloas `process_slots` preserves FinalizedNotAhead.** -/
theorem processSlots_finalizedNotAhead {ctx : Ctx} {s s' : GSt P} {slot : U64}
    (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s') (hI : FinalizedNotAhead s) :
    FinalizedNotAhead s' := by
  unfold JauneConsensus.Gloas.processSlots JauneConsensus.Gloas.processSlotsWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine range_forIn_inv FinalizedNotAhead (fun a b x hb hx => ?_) hout hI
  obtain ⟨st1, h1, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨next, hn, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨r, hr, hx⟩ := bind_eq_ok_iff.mp hx
  have f1 := processSlot_fs _ _ h1
  have hnext : next.toNat = b.slot.toNat + 1 := by
    rw [U64.toNat_add? hn, f1.2]; rfl
  simp only [] at hx
  split at hx
  · obtain ⟨st2, he, hx⟩ := bind_eq_ok_iff.mp hx
    cases hx
    exact slotIter_fna hb f1 hnext (Or.inr (processEpoch_fe he))
  · cases hx
    exact slotIter_fna hb f1 hnext (Or.inl rfl)

section Apply

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinSlot _ _ from ⟨rfl, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) => `(tactic| (have hh := processBlock_finSlot $h; exact hh))

theorem applySignedBlock_fs (ctx : Ctx) (s : GSt P) (b : JauneConsensus.Gloas.SignedBeaconBlock P)
    (v : Bool) :
    Ok (JauneConsensus.Gloas.applySignedBlockWith (JauneConsensus.Gloas.processBlock ctx)
      ctx.blsActive s b v) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.applySignedBlockWith; gvcg

end Apply

/-- **Gloas `state_transition` preserves FinalizedNotAhead.** -/
theorem stateTransition_finalizedNotAhead {ctx : Ctx} {s s' : GSt P}
    {b : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool}
    (h : JauneConsensus.Gloas.stateTransition ctx s b v = .ok s') (hI : FinalizedNotAhead s) :
    FinalizedNotAhead s' := by
  rw [JauneConsensus.Gloas.stateTransition_eq] at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  exact (applySignedBlock_fs _ _ _ _ _ h).fna (processSlots_finalizedNotAhead h1 hI)

/-! ## The fork-indexed state (the Fulu anchors) -/

section Forked

variable {f : CFork}

/-- The finalized checkpoint and the slot are unchanged (fork-indexed). -/
def FinSlotF (s s' : JauneConsensus.BeaconState P f) : Prop :=
  s'.finalized_checkpoint = s.finalized_checkpoint ∧ s'.slot = s.slot

def finSlotF : StepRel (JauneConsensus.BeaconState P f) where
  R := FinSlotF
  refl _ := ⟨rfl, rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem FinSlotF.fna {s s' : JauneConsensus.BeaconState P f} (h : FinSlotF s s')
    (hf : FinalizedNotAheadF s) : FinalizedNotAheadF s' := by
  unfold FinalizedNotAheadF at *; rw [h.1, h.2]; exact hf

section BlockF

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinSlotF _ _ from ⟨rfl, rfl⟩))

/-- Close a tail call `Ok (g st ..) (finSlotF.R base)` by `g`'s lemma, possibly after a record
update of the base. Extended below as the lemmas are proved. -/
syntax "ftail" : tactic
macro "ftail_of " t:term : tactic =>
  `(tactic| first
    | (with_reducible apply $t); done
    | ((with_reducible refine StepRel.ok_rebase finSlotF ?_ $t); exact ⟨rfl, rfl⟩))
local macro_rules | `(tactic| gstep) => `(tactic| ftail)
local macro_rules | `(tactic| jstep) => `(tactic| ftail)

theorem increaseBalance_fsF (s : JauneConsensus.BeaconState P f) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.increaseBalance s i d) (finSlotF.R s) := by
  unfold JauneConsensus.increaseBalance; gvcg

theorem decreaseBalance_fsF (s : JauneConsensus.BeaconState P f) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.decreaseBalance s i d) (finSlotF.R s) := by
  unfold JauneConsensus.decreaseBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (increaseBalance_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (increaseBalance_fsF _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (decreaseBalance_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (decreaseBalance_fsF _ _ _))

theorem computeExitEpochAndUpdateChurn_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f)
    (b : Gwei) :
    Ok (JauneConsensus.computeExitEpochAndUpdateChurn cfg s b) (fun p => finSlotF.R s p.1) := by
  unfold JauneConsensus.computeExitEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (computeExitEpochAndUpdateChurn_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (computeExitEpochAndUpdateChurn_fsF _ _ _))

theorem computeConsolidationEpochAndUpdateChurn_fsF (cfg : Config)
    (s : JauneConsensus.BeaconState P f) (b : Gwei) :
    Ok (JauneConsensus.computeConsolidationEpochAndUpdateChurn cfg s b)
      (fun p => finSlotF.R s p.1) := by
  unfold JauneConsensus.computeConsolidationEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (computeConsolidationEpochAndUpdateChurn_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (computeConsolidationEpochAndUpdateChurn_fsF _ _ _))

set_option maxHeartbeats 2000000 in
theorem initiateValidatorExit_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f)
    (i : ValidatorIndex) :
    Ok (JauneConsensus.initiateValidatorExit cfg s i) (finSlotF.R s) := by
  unfold JauneConsensus.initiateValidatorExit; gvcg
  all_goals
    apply ok_pure
    have hp := ‹(pure (s, _) : M (JauneConsensus.BeaconState P f × Epoch)) = Except.ok _›
    cases hp; exact ⟨rfl, rfl⟩

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (initiateValidatorExit_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (initiateValidatorExit_fsF _ _ _))

theorem slashValidator_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f)
    (i : ValidatorIndex) (wb : Option ValidatorIndex) :
    Ok (JauneConsensus.slashValidator cfg s i wb) (finSlotF.R s) := by
  unfold JauneConsensus.slashValidator; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (slashValidator_fsF _ _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (slashValidator_fsF _ _ _ _))

theorem queueExcessActiveBalance_fsF (s : JauneConsensus.BeaconState P f) (i : ValidatorIndex) :
    Ok (JauneConsensus.queueExcessActiveBalance s i) (finSlotF.R s) := by
  unfold JauneConsensus.queueExcessActiveBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (queueExcessActiveBalance_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (queueExcessActiveBalance_fsF _ _))

theorem switchToCompoundingValidator_fsF (s : JauneConsensus.BeaconState P f)
    (i : ValidatorIndex) :
    Ok (JauneConsensus.switchToCompoundingValidator s i) (finSlotF.R s) := by
  unfold JauneConsensus.switchToCompoundingValidator; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (switchToCompoundingValidator_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (switchToCompoundingValidator_fsF _ _))

theorem setDepositRequestsStartIndex_fsF (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setDepositRequestsStartIndex s v) (finSlotF.R s) := by
  unfold JauneConsensus.BeaconState.setDepositRequestsStartIndex; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (setDepositRequestsStartIndex_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setDepositRequestsStartIndex_fsF _ _))

theorem setDepositBalanceToConsume_fsF (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setDepositBalanceToConsume s v) (finSlotF.R s) := by
  unfold JauneConsensus.BeaconState.setDepositBalanceToConsume; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (setDepositBalanceToConsume_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setDepositBalanceToConsume_fsF _ _))

theorem setExitBalanceToConsume_fsF (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setExitBalanceToConsume s v) (finSlotF.R s) := by
  unfold JauneConsensus.BeaconState.setExitBalanceToConsume; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (setExitBalanceToConsume_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setExitBalanceToConsume_fsF _ _))

theorem setEarliestExitEpoch_fsF (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setEarliestExitEpoch s v) (finSlotF.R s) := by
  unfold JauneConsensus.BeaconState.setEarliestExitEpoch; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (setEarliestExitEpoch_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setEarliestExitEpoch_fsF _ _))

theorem setConsolidationBalanceToConsume_fsF (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setConsolidationBalanceToConsume s v) (finSlotF.R s) := by
  unfold JauneConsensus.BeaconState.setConsolidationBalanceToConsume; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (setConsolidationBalanceToConsume_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setConsolidationBalanceToConsume_fsF _ _))

theorem setEarliestConsolidationEpoch_fsF (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setEarliestConsolidationEpoch s v) (finSlotF.R s) := by
  unfold JauneConsensus.BeaconState.setEarliestConsolidationEpoch; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (setEarliestConsolidationEpoch_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setEarliestConsolidationEpoch_fsF _ _))

theorem setPendingDeposits_fsF (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setPendingDeposits s v) (finSlotF.R s) := by
  unfold JauneConsensus.BeaconState.setPendingDeposits; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (setPendingDeposits_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setPendingDeposits_fsF _ _))

theorem setPendingPartialWithdrawals_fsF (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setPendingPartialWithdrawals s v) (finSlotF.R s) := by
  unfold JauneConsensus.BeaconState.setPendingPartialWithdrawals; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (setPendingPartialWithdrawals_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setPendingPartialWithdrawals_fsF _ _))

theorem setPendingConsolidations_fsF (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setPendingConsolidations s v) (finSlotF.R s) := by
  unfold JauneConsensus.BeaconState.setPendingConsolidations; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (setPendingConsolidations_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setPendingConsolidations_fsF _ _))

theorem setProposerLookahead_fsF (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setProposerLookahead s v) (finSlotF.R s) := by
  unfold JauneConsensus.BeaconState.setProposerLookahead; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (setProposerLookahead_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setProposerLookahead_fsF _ _))

theorem addValidatorToRegistry_fsF (s : JauneConsensus.BeaconState P f) (pk : BLSPubkey)
    (wc : Bytes32) (amount : Gwei) :
    Ok (JauneConsensus.addValidatorToRegistry s pk wc amount) (finSlotF.R s) := by
  unfold JauneConsensus.addValidatorToRegistry; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (addValidatorToRegistry_fsF _ _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (addValidatorToRegistry_fsF _ _ _ _))

theorem applyDeposit_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f) (pk : BLSPubkey)
    (wc : Bytes32) (amount : Gwei) (sig : BLSSignature) :
    Ok (JauneConsensus.applyDeposit ctx s pk wc amount sig) (finSlotF.R s) := by
  unfold JauneConsensus.applyDeposit; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (applyDeposit_fsF _ _ _ _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (applyDeposit_fsF _ _ _ _ _ _))

theorem processDeposit_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f) (d : Deposit) :
    Ok (JauneConsensus.processDeposit ctx s d) (finSlotF.R s) := by
  unfold JauneConsensus.processDeposit; gvcg

theorem processDepositRequest_fsF (s : JauneConsensus.BeaconState P f) (dr : DepositRequest) :
    Ok (JauneConsensus.processDepositRequest s dr) (finSlotF.R s) := by
  unfold JauneConsensus.processDepositRequest; gvcg

theorem processWithdrawalRequest_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f)
    (wr : WithdrawalRequest) :
    Ok (JauneConsensus.processWithdrawalRequest cfg s wr) (finSlotF.R s) := by
  unfold JauneConsensus.processWithdrawalRequest; gvcg

theorem processConsolidationRequest_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f)
    (cr : ConsolidationRequest) :
    Ok (JauneConsensus.processConsolidationRequest cfg s cr) (finSlotF.R s) := by
  unfold JauneConsensus.processConsolidationRequest; gvcg

theorem processBlsToExecutionChange_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (sac : SignedBLSToExecutionChange) :
    Ok (JauneConsensus.processBlsToExecutionChange ctx s sac) (finSlotF.R s) := by
  unfold JauneConsensus.processBlsToExecutionChange; gvcg

theorem processVoluntaryExit_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (sve : SignedVoluntaryExit) :
    Ok (JauneConsensus.processVoluntaryExit ctx s sve) (finSlotF.R s) := by
  unfold JauneConsensus.processVoluntaryExit; gvcg

theorem processProposerSlashing_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (ps : ProposerSlashing) :
    Ok (JauneConsensus.processProposerSlashing ctx s ps) (finSlotF.R s) := by
  unfold JauneConsensus.processProposerSlashing; gvcg

theorem processAttesterSlashing_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (as : AttesterSlashing P f) :
    Ok (JauneConsensus.processAttesterSlashing ctx s as) (finSlotF.R s) := by
  unfold JauneConsensus.processAttesterSlashing; gvcg

set_option maxHeartbeats 8000000 in
theorem processAttestation_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (a : Attestation P f) :
    Ok (JauneConsensus.processAttestation ctx s a) (finSlotF.R s) := by
  unfold JauneConsensus.processAttestation; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processDeposit_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processDeposit_fsF _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processDepositRequest_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processDepositRequest_fsF _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processWithdrawalRequest_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processWithdrawalRequest_fsF _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processConsolidationRequest_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processConsolidationRequest_fsF _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processBlsToExecutionChange_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processBlsToExecutionChange_fsF _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processVoluntaryExit_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processVoluntaryExit_fsF _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processProposerSlashing_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processProposerSlashing_fsF _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processAttesterSlashing_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processAttesterSlashing_fsF _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processAttestation_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processAttestation_fsF _ _ _))

set_option maxHeartbeats 8000000 in
theorem processOperations_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processOperations ctx s body) (finSlotF.R s) := by
  unfold JauneConsensus.processOperations; jvcg

theorem processBlockHeader_fsF (s : JauneConsensus.BeaconState P f) (blk : BeaconBlock P f) :
    Ok (JauneConsensus.processBlockHeader s blk) (finSlotF.R s) := by
  unfold JauneConsensus.processBlockHeader; gvcg

theorem processRandao_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processRandao ctx s body) (finSlotF.R s) := by
  unfold JauneConsensus.processRandao; gvcg

theorem processEth1Data_fsF (s : JauneConsensus.BeaconState P f) (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processEth1Data s body) (finSlotF.R s) := by
  unfold JauneConsensus.processEth1Data; gvcg

theorem processWithdrawals_fsF (s : JauneConsensus.BeaconState P f) (pl : ExecutionPayload P) :
    Ok (JauneConsensus.processWithdrawals s pl) (finSlotF.R s) := by
  unfold JauneConsensus.processWithdrawals
  with_reducible apply ok_bind
  intro x hx
  rcases x with ⟨ex, n⟩
  jvcg

theorem processExecutionPayload_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processExecutionPayload ctx s body) (finSlotF.R s) := by
  unfold JauneConsensus.processExecutionPayload; gvcg

set_option maxHeartbeats 8000000 in
theorem processSyncAggregate_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (sa : SyncAggregate P) :
    Ok (JauneConsensus.processSyncAggregate ctx s sa) (finSlotF.R s) := by
  unfold JauneConsensus.processSyncAggregate; jvcg

/-- **A fork-indexed block keeps the finalized checkpoint and the slot.** -/
theorem processBlock_finSlotF {ctx : Ctx} {s s' : JauneConsensus.BeaconState P f}
    {blk : BeaconBlock P f} (h : JauneConsensus.processBlock ctx s blk = .ok s') :
    FinSlotF s s' := by
  unfold JauneConsensus.processBlock JauneConsensus.processBlockWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h⟩ := bind_eq_ok_iff.mp h
  exact finSlotF.trans (processBlockHeader_fsF _ _ _ h1)
    (finSlotF.trans (processWithdrawals_fsF _ _ _ h2)
    (finSlotF.trans (processExecutionPayload_fsF _ _ _ _ h3)
    (finSlotF.trans (processRandao_fsF _ _ _ _ h4)
    (finSlotF.trans (processEth1Data_fsF _ _ _ h5)
    (finSlotF.trans (processOperations_fsF _ _ _ _ h6)
      (processSyncAggregate_fsF _ _ _ _ h))))))

/-- **A fork-indexed (Fulu) block preserves FinalizedNotAhead.** -/
theorem processBlock_finalizedNotAheadF {ctx : Ctx} {s s' : JauneConsensus.BeaconState P f}
    {blk : BeaconBlock P f} (h : JauneConsensus.processBlock ctx s blk = .ok s')
    (hf : FinalizedNotAheadF s) : FinalizedNotAheadF s' :=
  (processBlock_finSlotF h).fna hf


set_option maxHeartbeats 4000000 in
theorem processInactivityUpdates_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processInactivityUpdates cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processInactivityUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processInactivityUpdates_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processInactivityUpdates_fsF _ _))

theorem processRewardsAndPenalties_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processRewardsAndPenalties cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processRewardsAndPenalties; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processRewardsAndPenalties_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processRewardsAndPenalties_fsF _ _))

theorem processRegistryUpdatesElectra_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processRegistryUpdatesElectra cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processRegistryUpdatesElectra; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processRegistryUpdatesElectra_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processRegistryUpdatesElectra_fsF _ _))

theorem processRegistryUpdatesDeneb_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processRegistryUpdatesDeneb cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processRegistryUpdatesDeneb; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processRegistryUpdatesDeneb_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processRegistryUpdatesDeneb_fsF _ _))

theorem processRegistryUpdates_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processRegistryUpdates cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processRegistryUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processRegistryUpdates_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processRegistryUpdates_fsF _ _))

set_option maxHeartbeats 4000000 in
theorem processSlashings_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processSlashings cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processSlashings; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processSlashings_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processSlashings_fsF _ _))

theorem processEth1DataReset_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processEth1DataReset cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processEth1DataReset; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processEth1DataReset_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processEth1DataReset_fsF _ _))

theorem applyPendingDeposit_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f) (d : PendingDeposit) :
    Ok (JauneConsensus.applyPendingDeposit ctx s d) (finSlotF.R s) := by
  unfold JauneConsensus.applyPendingDeposit; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (applyPendingDeposit_fsF _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (applyPendingDeposit_fsF _ _ _))

section PendingDepositsF

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRel.forIn_array_rel _ (fun x => x.2.2.2.2) ?_ _ _ $h; intro _ _; gvcg))

set_option maxHeartbeats 4000000 in
theorem processPendingDeposits_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processPendingDeposits ctx s) (finSlotF.R s) := by
  unfold JauneConsensus.processPendingDeposits; gvcg

end PendingDepositsF

theorem processPendingConsolidations_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processPendingConsolidations cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processPendingConsolidations; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processPendingConsolidations_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processPendingConsolidations_fsF _ _))

theorem processEffectiveBalanceUpdates_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processEffectiveBalanceUpdates cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processEffectiveBalanceUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processEffectiveBalanceUpdates_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processEffectiveBalanceUpdates_fsF _ _))

theorem processSlashingsReset_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processSlashingsReset cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processSlashingsReset; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processSlashingsReset_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processSlashingsReset_fsF _ _))

theorem processRandaoMixesReset_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processRandaoMixesReset cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processRandaoMixesReset; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processRandaoMixesReset_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processRandaoMixesReset_fsF _ _))

theorem processHistoricalSummariesUpdate_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processHistoricalSummariesUpdate cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processHistoricalSummariesUpdate; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processHistoricalSummariesUpdate_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processHistoricalSummariesUpdate_fsF _ _))

theorem processParticipationFlagUpdates_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processParticipationFlagUpdates cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processParticipationFlagUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processParticipationFlagUpdates_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processParticipationFlagUpdates_fsF _ _))

theorem processSyncCommitteeUpdates_fsF (ctx : Ctx) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processSyncCommitteeUpdates ctx s) (finSlotF.R s) := by
  unfold JauneConsensus.processSyncCommitteeUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processSyncCommitteeUpdates_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processSyncCommitteeUpdates_fsF _ _))

theorem processProposerLookahead_fsF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processProposerLookahead cfg s) (finSlotF.R s) := by
  unfold JauneConsensus.processProposerLookahead; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processProposerLookahead_fsF _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processProposerLookahead_fsF _ _))

end BlockF

/-- The slot is kept, and the finalized checkpoint is kept or has an epoch below `E`
(fork-indexed). -/
def FinEpF (E : Nat) (s s' : JauneConsensus.BeaconState P f) : Prop :=
  s'.slot = s.slot ∧
    (s'.finalized_checkpoint = s.finalized_checkpoint ∨ s'.finalized_checkpoint.epoch.toNat < E)

def finEpF (E : Nat) : StepRel (JauneConsensus.BeaconState P f) where
  R := FinEpF E
  refl _ := ⟨rfl, Or.inl rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, by
    rcases h₂.2 with h | h
    · rw [h]; exact h₁.2
    · exact Or.inr h⟩

theorem FinSlotF.finEp {E : Nat} {s s' : JauneConsensus.BeaconState P f} (h : FinSlotF s s') :
    FinEpF E s s' :=
  ⟨h.2, Or.inl h.1⟩

theorem getCurrentEpochF_toNat {s : JauneConsensus.BeaconState P f} {e : U64}
    (h : JauneConsensus.getCurrentEpoch s = .ok e) :
    e.toNat = s.slot.toNat / P.SLOTS_PER_EPOCH := by
  unfold JauneConsensus.getCurrentEpoch at h; exact computeEpochAtSlot_toNat h

section WeighF

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinEpF _ _ _ from ⟨rfl, Or.inl rfl⟩))

set_option maxHeartbeats 4000000 in
theorem weighJustificationAndFinalization_feF (s : JauneConsensus.BeaconState P f) (t p c : Gwei) :
    Ok (JauneConsensus.weighJustificationAndFinalization s t p c)
      ((finEpF (s.slot.toNat / P.SLOTS_PER_EPOCH)).R s) := by
  unfold JauneConsensus.weighJustificationAndFinalization; jvcg
  all_goals
    refine StepRel.ok_rebase _ ?_ (JpOk2.call ‹_› _ _)
    rename_i hfin _ _ ha
    have hlt := finalizes_lt hfin ha (by
      first
      | (rw [c64_toNat ‹c64 3 = .ok _›]; decide)
      | (rw [c64_toNat ‹c64 2 = .ok _›]; decide)
      | decide)
    have hce := getCurrentEpochF_toNat ‹JauneConsensus.getCurrentEpoch s = _›
    refine ⟨rfl, Or.inr ?_⟩
    dsimp only
    omega

end WeighF

section EpochF

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinEpF _ _ _ from ⟨rfl, Or.inl rfl⟩))

set_option maxHeartbeats 4000000 in
theorem processJustificationAndFinalization_feF (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processJustificationAndFinalization cfg s)
      ((finEpF (s.slot.toNat / P.SLOTS_PER_EPOCH)).R s) := by
  unfold JauneConsensus.processJustificationAndFinalization; gvcg
  all_goals exact weighJustificationAndFinalization_feF _ _ _ _

end EpochF

section EpochF2

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinEpF _ _ _ from ⟨rfl, Or.inl rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processJustificationAndFinalization_feF _ _) $h); exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processInactivityUpdates_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processRewardsAndPenalties_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processRegistryUpdates_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processSlashings_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processEth1DataReset_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processPendingDeposits_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processPendingConsolidations_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processEffectiveBalanceUpdates_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processSlashingsReset_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processRandaoMixesReset_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processHistoricalSummariesUpdate_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processParticipationFlagUpdates_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processSyncCommitteeUpdates_fsF _ _) $h); exact FinSlotF.finEp hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRel.of_ok (processProposerLookahead_fsF _ _) $h); exact FinSlotF.finEp hh))

/-- **The fork-indexed epoch step** keeps the slot, and keeps the finalized checkpoint or moves it
to an epoch before the current one. -/
theorem processEpoch_feF {ctx : Ctx} {s s' : JauneConsensus.BeaconState P f}
    (h : JauneConsensus.processEpoch ctx s = .ok s') :
    FinEpF (s.slot.toNat / P.SLOTS_PER_EPOCH) s s' := by
  unfold JauneConsensus.processEpoch at h
  dsimp only at h
  obtain ⟨x1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x6, h6, h⟩ := bind_eq_ok_iff.mp h
  have f1 := processJustificationAndFinalization_feF _ _ _ h1
  have f6 : FinSlotF x1 x6 :=
    finSlotF.trans (processInactivityUpdates_fsF _ _ _ h2)
    (finSlotF.trans (processRewardsAndPenalties_fsF _ _ _ h3)
    (finSlotF.trans (processRegistryUpdates_fsF _ _ _ h4)
    (finSlotF.trans (processSlashings_fsF _ _ _ h5) (processEth1DataReset_fsF _ _ _ h6))))
  have tail : ∀ x7 : JauneConsensus.BeaconState P f, FinSlotF x6 x7 →
      (do
        let state ← JauneConsensus.processEffectiveBalanceUpdates ctx.cfg x7
        let state ← JauneConsensus.processSlashingsReset ctx.cfg state
        let state ← JauneConsensus.processRandaoMixesReset ctx.cfg state
        let state ← JauneConsensus.processHistoricalSummariesUpdate ctx.cfg state
        let state ← JauneConsensus.processParticipationFlagUpdates ctx.cfg state
        let state ← JauneConsensus.processSyncCommitteeUpdates ctx state
        if f.atLeast CFork.fulu = true then JauneConsensus.processProposerLookahead ctx.cfg state
          else pure state) = .ok s' → FinSlotF x6 s' := by
    intro x7 f7 h
    obtain ⟨x8, h8, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x9, h9, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x10, h10, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x11, h11, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x12, h12, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x13, h13, h⟩ := bind_eq_ok_iff.mp h
    have f14 : FinSlotF x13 s' := by
      split at h
      · exact processProposerLookahead_fsF _ _ _ h
      · cases h; exact finSlotF.refl _
    exact finSlotF.trans f7
      (finSlotF.trans (processEffectiveBalanceUpdates_fsF _ _ _ h8)
      (finSlotF.trans (processSlashingsReset_fsF _ _ _ h9)
      (finSlotF.trans (processRandaoMixesReset_fsF _ _ _ h10)
      (finSlotF.trans (processHistoricalSummariesUpdate_fsF _ _ _ h11)
      (finSlotF.trans (processParticipationFlagUpdates_fsF _ _ _ h12)
      (finSlotF.trans (processSyncCommitteeUpdates_fsF _ _ _ h13) f14))))))
  have f : FinSlotF x6 s' := by
    split at h
    · obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨z, hz, h⟩ := bind_eq_ok_iff.mp h
      exact tail z (finSlotF.trans (processPendingDeposits_fsF _ _ _ hy)
        (processPendingConsolidations_fsF _ _ _ hz)) h
    · exact tail x6 (finSlotF.refl _) h
  exact (finEpF _).trans f1 (finSlotF.trans f6 f).finEp

end EpochF2

theorem processSlot_fsF (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processSlot s) (finSlotF.R s) := by
  intro s' h
  unfold JauneConsensus.processSlot at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine ⟨?_, ?_⟩ <;> split <;> rfl

/-- **Fork-indexed `process_slots` preserves FinalizedNotAhead.** -/
theorem processSlots_finalizedNotAheadF {ctx : Ctx} {s s' : JauneConsensus.BeaconState P f}
    {slot : U64} (h : JauneConsensus.processSlots ctx s slot = .ok s')
    (hI : FinalizedNotAheadF s) : FinalizedNotAheadF s' := by
  unfold JauneConsensus.processSlots JauneConsensus.processSlotsWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine range_forIn_inv FinalizedNotAheadF (fun a b x hb hx => ?_) hout hI
  obtain ⟨st1, h1, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨next, hn, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨r, hr, hx⟩ := bind_eq_ok_iff.mp hx
  have f1 := processSlot_fsF _ _ h1
  have hnext : next.toNat = b.slot.toNat + 1 := by
    rw [U64.toNat_add? hn, f1.2]; rfl
  have hmono : b.slot.toNat / P.SLOTS_PER_EPOCH ≤ next.toNat / P.SLOTS_PER_EPOCH := by
    rw [hnext]; exact Nat.div_le_div_right (by omega)
  have hf1 : st1.finalized_checkpoint = b.finalized_checkpoint := f1.1
  have hs1 : st1.slot = b.slot := f1.2
  unfold FinalizedNotAheadF at hb
  simp only [] at hx
  split at hx
  · obtain ⟨st2, he, hx⟩ := bind_eq_ok_iff.mp hx
    cases hx
    have fe := processEpoch_feF he
    show st2.finalized_checkpoint.epoch.toNat ≤ next.toNat / P.SLOTS_PER_EPOCH
    rw [hs1] at fe
    rcases fe.2 with hf | hf
    · rw [hf, hf1]; omega
    · omega
  · cases hx
    show st1.finalized_checkpoint.epoch.toNat ≤ next.toNat / P.SLOTS_PER_EPOCH
    rw [hf1]; omega

section ApplyF

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinSlotF _ _ from ⟨rfl, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) => `(tactic| (have hh := processBlock_finSlotF $h; exact hh))

/-- **Fork-indexed `state_transition` preserves FinalizedNotAhead.** -/
theorem stateTransition_finalizedNotAheadF {ctx : Ctx} {s s' : JauneConsensus.BeaconState P f}
    {b : SignedBeaconBlock P f} {v : Bool}
    (h : JauneConsensus.stateTransition ctx s b v = .ok s') (hI : FinalizedNotAheadF s) :
    FinalizedNotAheadF s' := by
  unfold JauneConsensus.stateTransition JauneConsensus.stateTransitionWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  have hI1 : FinalizedNotAheadF s1 := processSlots_finalizedNotAheadF (ctx := ctx) h1 hI
  refine FinSlotF.fna ((?_ : Ok _ (finSlotF.R s1)) _ h) hI1
  gvcg

end ApplyF

end Forked

/-! ## The crossing -/

theorem upgradedState_finSlot {cfg : Config} {pre : JauneConsensus.BeaconState P .fulu}
    {post : GSt P} (h : JauneConsensus.Gloas.upgradedState cfg pre = .ok post) :
    post.finalized_checkpoint = pre.finalized_checkpoint ∧ post.slot = pre.slot := by
  unfold JauneConsensus.Gloas.upgradedState at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact ⟨rfl, rfl⟩

section Onboard

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinSlot _ _ from ⟨rfl, rfl⟩))

theorem addBuilderToRegistry_fs (s : GSt P) (pk : BLSPubkey) (v : U8) (a : ExecutionAddress)
    (amount : Gwei) (slot : Slot) :
    Ok (JauneConsensus.Gloas.addBuilderToRegistry s pk v a amount slot) (finSlot.R s) := by
  unfold JauneConsensus.Gloas.addBuilderToRegistry; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (addBuilderToRegistry_fs _ _ _ _ _ _) $h; exact hh))

theorem onboardBuilderDeposit_fs (ctx : Ctx) (vp : Array BLSPubkey) (st : GSt P)
    (pd : Array PendingDeposit) (d : PendingDeposit) :
    Ok (JauneConsensus.Gloas.onboardBuilderDeposit ctx vp (st, pd) d)
      (fun r => finSlot.R st r.1) := by
  unfold JauneConsensus.Gloas.onboardBuilderDeposit; gvcg

end Onboard

theorem foldlM_onboard_fs (ctx : Ctx) (vp : Array BLSPubkey) :
    ∀ (l : List PendingDeposit) (st : GSt P) (pd : Array PendingDeposit) (out : GSt P × Array PendingDeposit),
      l.foldlM (JauneConsensus.Gloas.onboardBuilderDeposit ctx vp) (st, pd) = .ok out →
      FinSlot st out.1
  | [], st, pd, out, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact finSlot.refl _
  | d :: l, st, pd, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨⟨st', pd'⟩, h1, h⟩ := bind_eq_ok_iff.mp h
    exact finSlot.trans (onboardBuilderDeposit_fs ctx vp st pd d _ h1)
      (foldlM_onboard_fs ctx vp l st' pd' out h)

theorem onboardBuildersFromPendingDeposits_fs (ctx : Ctx) (s : GSt P) :
    Ok (JauneConsensus.Gloas.onboardBuildersFromPendingDeposits ctx s) (finSlot.R s) := by
  intro s' h
  unfold JauneConsensus.Gloas.onboardBuildersFromPendingDeposits at h
  obtain ⟨⟨st, pd⟩, h1, h⟩ := bind_eq_ok_iff.mp h
  cases h
  rw [← Array.foldlM_toList] at h1
  exact foldlM_onboard_fs ctx _ _ s #[] _ h1

/-- `upgrade_to_gloas` copies the finalized checkpoint and the slot. -/
theorem upgradeToGloas_finSlot {ctx : Ctx} {pre : JauneConsensus.BeaconState P .fulu}
    {post : GSt P} (h : JauneConsensus.Gloas.upgradeToGloas ctx pre = .ok post) :
    post.finalized_checkpoint = pre.finalized_checkpoint ∧ post.slot = pre.slot := by
  unfold JauneConsensus.Gloas.upgradeToGloas at h
  obtain ⟨p0, h0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, _, h⟩ := bind_eq_ok_iff.mp h
  have e0 := upgradedState_finSlot h0
  have e1 := onboardBuildersFromPendingDeposits_fs ctx _ _ h
  exact ⟨e1.1.trans e0.1, e1.2.trans e0.2⟩

/-- **`upgrade_to_gloas` preserves FinalizedNotAhead.** -/
theorem upgradeToGloas_finalizedNotAhead {ctx : Ctx} {pre : JauneConsensus.BeaconState P .fulu}
    {post : GSt P} (h : JauneConsensus.Gloas.upgradeToGloas ctx pre = .ok post)
    (hI : FinalizedNotAheadF pre) : FinalizedNotAhead post := by
  obtain ⟨e1, e2⟩ := upgradeToGloas_finSlot h
  unfold FinalizedNotAhead curEpoch; unfold FinalizedNotAheadF at hI
  rw [e1, e2]; exact hI

/-- **The crossing preserves FinalizedNotAhead**: the Fulu `process_slots` to the fork slot, then
`upgrade_to_gloas`. -/
theorem crossFromFulu_finalizedNotAhead {ctx : Ctx} {pre : JauneConsensus.BeaconState P .fulu}
    {post : GSt P} (h : JauneConsensus.Gloas.crossFromFulu ctx pre = .ok post)
    (hI : FinalizedNotAheadF pre) : FinalizedNotAhead post := by
  unfold JauneConsensus.Gloas.crossFromFulu at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨pre', hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    exact upgradeToGloas_finalizedNotAhead h (processSlots_finalizedNotAheadF hp hI)
  · obtain ⟨pre', hp, h⟩ := bind_eq_ok_iff.mp h
    cases hp
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    exact upgradeToGloas_finalizedNotAhead h hI

end JauneConsensus.Facts.Gloas.Inv
