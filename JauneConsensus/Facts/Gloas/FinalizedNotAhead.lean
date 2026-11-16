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

namespace JauneConsensus.Facts.Gloas.Invariant

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-! ## The invariant -/

/-- **FinalizedNotAhead** (Gloas): `finalized_checkpoint.epoch ≤ get_current_epoch(state)`. -/
def FinalizedNotAhead (s : GloasState P) : Prop :=
  s.finalized_checkpoint.epoch.toNat ≤ currentEpoch s

/-- **FinalizedNotAhead** on the fork-indexed state (the Fulu anchors). -/
def FinalizedNotAheadForkIndexed {f : ConsensusFork} (s : BeaconState P f) : Prop :=
  s.finalized_checkpoint.epoch.toNat ≤ s.slot.toNat / P.SLOTS_PER_EPOCH

/-! ## The relations -/

/-- The finalized checkpoint and the slot are unchanged. -/
def FinalizedCheckpointAndSlotKept (s s' : GloasState P) : Prop :=
  s'.finalized_checkpoint = s.finalized_checkpoint ∧ s'.slot = s.slot

def finalizedCheckpointAndSlotKept : StepRelation (GloasState P) where
  relation := FinalizedCheckpointAndSlotKept
  refl _ := ⟨rfl, rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem FinalizedCheckpointAndSlotKept.finalizedNotAhead {s s' : GloasState P} (h : FinalizedCheckpointAndSlotKept s s') (hf : FinalizedNotAhead s) :
    FinalizedNotAhead s' := by
  unfold FinalizedNotAhead currentEpoch at *; rw [h.1, h.2]; exact hf

/-! ## The Gloas block -/

section Block

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinalizedCheckpointAndSlotKept _ _ from ⟨rfl, rfl⟩))

theorem increaseBalance_finalizedAndSlotKept (s : GloasState P) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.increaseBalance s i d) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.increaseBalance; gvcg

theorem decreaseBalance_finalizedAndSlotKept (s : GloasState P) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.decreaseBalance s i d) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.decreaseBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (increaseBalance_finalizedAndSlotKept _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (decreaseBalance_finalizedAndSlotKept _ _ _) $h; exact hh))

theorem computeExitEpochAndUpdateChurn_finalizedAndSlotKept (cfg : Config) (s : GloasState P) (b : Gwei) :
    Ok (JauneConsensus.Gloas.computeExitEpochAndUpdateChurn cfg s b)
      (fun p => finalizedCheckpointAndSlotKept.relation s p.1) := by
  unfold JauneConsensus.Gloas.computeExitEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (computeExitEpochAndUpdateChurn_finalizedAndSlotKept _ _ _) $h; exact hh))

theorem initiateValidatorExit_finalizedAndSlotKept (cfg : Config) (s : GloasState P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.initiateValidatorExit cfg s i) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.initiateValidatorExit; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (initiateValidatorExit_finalizedAndSlotKept _ _ _) $h; exact hh))

theorem queueExcessActiveBalance_finalizedAndSlotKept (s : GloasState P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.queueExcessActiveBalance s i) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.queueExcessActiveBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (queueExcessActiveBalance_finalizedAndSlotKept _ _) $h; exact hh))

theorem switchToCompoundingValidator_finalizedAndSlotKept (s : GloasState P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.switchToCompoundingValidator s i) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.switchToCompoundingValidator; gvcg
  all_goals exact StepRelation.ok_rebase finalizedCheckpointAndSlotKept ⟨rfl, rfl⟩ (queueExcessActiveBalance_finalizedAndSlotKept _ _)

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (switchToCompoundingValidator_finalizedAndSlotKept _ _) $h; exact hh))

theorem computeConsolidationEpochAndUpdateChurn_finalizedAndSlotKept (cfg : Config) (s : GloasState P) (b : Gwei) :
    Ok (JauneConsensus.Gloas.computeConsolidationEpochAndUpdateChurn cfg s b)
      (fun p => finalizedCheckpointAndSlotKept.relation s p.1) := by
  unfold JauneConsensus.Gloas.computeConsolidationEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (computeConsolidationEpochAndUpdateChurn_finalizedAndSlotKept _ _ _) $h; exact hh))

theorem processWithdrawalRequest_finalizedAndSlotKept (cfg : Config) (s : GloasState P) (wr : WithdrawalRequest) :
    Ok (JauneConsensus.Gloas.processWithdrawalRequest cfg s wr) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processWithdrawalRequest; gvcg
  all_goals exact fun x hx => initiateValidatorExit_finalizedAndSlotKept _ _ _ x hx

theorem processConsolidationRequest_finalizedAndSlotKept (cfg : Config) (s : GloasState P) (cr : ConsolidationRequest) :
    Ok (JauneConsensus.Gloas.processConsolidationRequest cfg s cr) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processConsolidationRequest; gvcg
  all_goals exact switchToCompoundingValidator_finalizedAndSlotKept _ _

theorem settleBuilderPayment_finalizedAndSlotKept (s : GloasState P) (i : U64) :
    Ok (JauneConsensus.Gloas.settleBuilderPayment s i) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.settleBuilderPayment; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processWithdrawalRequest_finalizedAndSlotKept _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processConsolidationRequest_finalizedAndSlotKept _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (settleBuilderPayment_finalizedAndSlotKept _ _) $h; exact hh))

section Prefix

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine (finalizedCheckpointAndSlotKept).trans ?_ (StepRelation.forIn_array_relation finalizedCheckpointAndSlotKept id ?_ _ _ $h)
               · exact (show FinalizedCheckpointAndSlotKept _ _ from ⟨rfl, rfl⟩)
               · intro _ _; gvcg))

theorem applyParentPrefix_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P)
    (r : JauneConsensus.Gloas.ExecutionRequests) :
    Ok (JauneConsensus.Gloas.applyParentPrefix ctx s r) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.applyParentPrefix; gvcg

end Prefix

theorem processBuilderDepositRequest_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P)
    (r : JauneConsensus.Gloas.BuilderDepositRequest) :
    Ok (JauneConsensus.Gloas.processBuilderDepositRequest ctx s r) (finalizedCheckpointAndSlotKept.relation s) := by
  intro s' h
  have := (processBuilderDepositRequest_frame h).2.2.2.2.2
  rw [this]; exact ⟨rfl, rfl⟩

theorem processBuilderExitRequest_finalizedAndSlotKept (cfg : Config) (s : GloasState P)
    (r : JauneConsensus.Gloas.BuilderExitRequest) :
    Ok (JauneConsensus.Gloas.processBuilderExitRequest cfg s r) (finalizedCheckpointAndSlotKept.relation s) := by
  intro s' h
  have := (processBuilderExitRequest_frame h).2.2.2.2.2
  rw [this]; exact ⟨rfl, rfl⟩

theorem applyParentSuffix_finalizedAndSlotKept (st0 s : GloasState P) :
    Ok (JauneConsensus.Gloas.applyParentSuffix st0 s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.applyParentSuffix; gvcg

theorem processParentExecutionPayload_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P)
    (blk : JauneConsensus.Gloas.BeaconBlock P) :
    Ok (JauneConsensus.Gloas.processParentExecutionPayload ctx s blk) (finalizedCheckpointAndSlotKept.relation s) := by
  intro s1 h1
  rcases processParentExecutionPayload_cases h1 with ⟨rfl, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · exact finalizedCheckpointAndSlotKept.refl _
  have pa := applyParentPrefix_finalizedAndSlotKept ctx s _ a ha
  have pd : FinalizedCheckpointAndSlotKept s d := forIn_yield_invariant (FinalizedCheckpointAndSlotKept s) _
    (fun _ _ _ hI hm => finalizedCheckpointAndSlotKept.trans hI (processBuilderDepositRequest_finalizedAndSlotKept _ _ _ _ hm)) _ _ _ hd pa
  have pe : FinalizedCheckpointAndSlotKept s e := forIn_yield_invariant (FinalizedCheckpointAndSlotKept s) _
    (fun _ _ _ hI hm => finalizedCheckpointAndSlotKept.trans hI (processBuilderExitRequest_finalizedAndSlotKept _ _ _ _ hm)) _ _ _ he pd
  exact finalizedCheckpointAndSlotKept.trans pe (applyParentSuffix_finalizedAndSlotKept _ _ _ hs)

theorem processBlockHeader_finalizedAndSlotKept (s : GloasState P) (blk : JauneConsensus.Gloas.BeaconBlock P) :
    Ok (JauneConsensus.Gloas.processBlockHeader s blk) (finalizedCheckpointAndSlotKept.relation s) := by
  intro s' h
  rw [(processBlockHeader_post h).2.2]; exact ⟨rfl, rfl⟩

theorem applyWithdrawals_finalizedAndSlotKept (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.applyWithdrawals s ws) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.applyWithdrawals; gvcg

theorem updateNextWithdrawalIndex_finalizedAndSlotKept (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalIndex s ws) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalIndex; gvcg

theorem updateNextWithdrawalBuilderIndex_finalizedAndSlotKept (s : GloasState P) (n : U64) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex s n) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex; gvcg

theorem updateNextWithdrawalValidatorIndex_finalizedAndSlotKept (s : GloasState P) (ws : Array Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex s ws) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (applyWithdrawals_finalizedAndSlotKept _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (updateNextWithdrawalIndex_finalizedAndSlotKept _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (updateNextWithdrawalBuilderIndex_finalizedAndSlotKept _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (updateNextWithdrawalValidatorIndex_finalizedAndSlotKept _ _) $h; exact hh))

theorem processWithdrawals_finalizedAndSlotKept (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processWithdrawals s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processWithdrawals; gvcg
  all_goals exact updateNextWithdrawalValidatorIndex_finalizedAndSlotKept _ _

set_option maxHeartbeats 1000000 in
theorem processExecutionPayloadBid_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P)
    (sb : JauneConsensus.Gloas.SignedExecutionPayloadBid) :
    Ok (JauneConsensus.Gloas.processExecutionPayloadBid ctx s sb) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processExecutionPayloadBid; gvcg
  all_goals (apply ok_pure; rename_i hlast; cases hlast; exact ⟨rfl, rfl⟩)

theorem processRandao_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P) (body : JauneConsensus.Gloas.BeaconBlockBody P) :
    Ok (JauneConsensus.Gloas.processRandao ctx s body) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processRandao; gvcg

theorem processEth1Data_finalizedAndSlotKept (s : GloasState P) (body : JauneConsensus.Gloas.BeaconBlockBody P) :
    Ok (JauneConsensus.Gloas.processEth1Data s body) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processEth1Data; gvcg

set_option maxHeartbeats 2000000 in
theorem processSyncAggregate_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P) (sa : SyncAggregate P) :
    Ok (JauneConsensus.Gloas.processSyncAggregate ctx s sa) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processSyncAggregate; gvcg

theorem slashValidator_finalizedAndSlotKept (cfg : Config) (s : GloasState P) (i : ValidatorIndex)
    (wb : Option ValidatorIndex) :
    Ok (JauneConsensus.Gloas.slashValidator cfg s i wb) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.slashValidator; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (slashValidator_finalizedAndSlotKept _ _ _ _) $h; exact hh))

theorem processProposerSlashing_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P) (ps : ProposerSlashing) :
    Ok (JauneConsensus.Gloas.processProposerSlashing ctx s ps) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processProposerSlashing; gvcg
  all_goals exact slashValidator_finalizedAndSlotKept _ _ _ _

theorem processAttesterSlashing_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P)
    (as : JauneConsensus.Gloas.AttesterSlashing) :
    Ok (JauneConsensus.Gloas.processAttesterSlashing ctx s as) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processAttesterSlashing; gvcg

theorem processVoluntaryExit_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P) (sve : SignedVoluntaryExit) :
    Ok (JauneConsensus.Gloas.processVoluntaryExit ctx s sve) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processVoluntaryExit; gvcg
  all_goals exact fun x hx => initiateValidatorExit_finalizedAndSlotKept _ _ _ x hx

theorem processBlsToExecutionChange_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P)
    (sac : SignedBLSToExecutionChange) :
    Ok (JauneConsensus.Gloas.processBlsToExecutionChange ctx s sac) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processBlsToExecutionChange; gvcg

theorem processPayloadAttestation_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P)
    (pa : JauneConsensus.Gloas.PayloadAttestation P) :
    Ok (JauneConsensus.Gloas.processPayloadAttestation ctx s pa) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processPayloadAttestation; gvcg

section Attestation

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (increaseBalance_finalizedAndSlotKept _ _ _) $h; exact ((finalizedCheckpointAndSlotKept).trans (by split <;> exact ⟨rfl, rfl⟩) hh)))

set_option maxHeartbeats 2000000 in
theorem processAttestation_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P)
    (a : JauneConsensus.Gloas.Attestation P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processAttestation ctx s a ps) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processAttestation; gvcg

end Attestation

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processProposerSlashing_finalizedAndSlotKept _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processAttesterSlashing_finalizedAndSlotKept _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processAttestation_finalizedAndSlotKept _ _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processVoluntaryExit_finalizedAndSlotKept _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processBlsToExecutionChange_finalizedAndSlotKept _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (processPayloadAttestation_finalizedAndSlotKept _ _ _) $h; exact hh))

theorem processOperations_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P)
    (body : JauneConsensus.Gloas.BeaconBlockBody P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processOperations ctx s body ps) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processOperations; gvcg

/-- **A Gloas block keeps the finalized checkpoint and the slot.** -/
theorem processBlock_finalizedCheckpointAndSlotKept {ctx : Ctx} {s s' : GloasState P} {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') : FinalizedCheckpointAndSlotKept s s' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  exact finalizedCheckpointAndSlotKept.trans (processParentExecutionPayload_finalizedAndSlotKept _ _ _ _ h1)
    (finalizedCheckpointAndSlotKept.trans (processBlockHeader_finalizedAndSlotKept _ _ _ h2)
    (finalizedCheckpointAndSlotKept.trans (processWithdrawals_finalizedAndSlotKept _ _ h3)
    (finalizedCheckpointAndSlotKept.trans (processExecutionPayloadBid_finalizedAndSlotKept _ _ _ _ h4)
    (finalizedCheckpointAndSlotKept.trans (processRandao_finalizedAndSlotKept _ _ _ _ h5)
    (finalizedCheckpointAndSlotKept.trans (processEth1Data_finalizedAndSlotKept _ _ _ h6)
    (finalizedCheckpointAndSlotKept.trans (processOperations_finalizedAndSlotKept _ _ _ _ _ h7)
      (processSyncAggregate_finalizedAndSlotKept _ _ _ _ h8)))))))

/-- **A Gloas block preserves FinalizedNotAhead.** -/
theorem processBlock_finalizedNotAhead {ctx : Ctx} {s s' : GloasState P}
    {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') (hf : FinalizedNotAhead s) :
    FinalizedNotAhead s' :=
  (processBlock_finalizedCheckpointAndSlotKept h).finalizedNotAhead hf

end Block

/-! ## The Gloas epoch -/

/-- The slot is kept, and the finalized checkpoint is kept or has an epoch below `E`. -/
def FinalizedEpoch (E : Nat) (s s' : GloasState P) : Prop :=
  s'.slot = s.slot ∧
    (s'.finalized_checkpoint = s.finalized_checkpoint ∨ s'.finalized_checkpoint.epoch.toNat < E)

def finalizedEpoch (E : Nat) : StepRelation (GloasState P) where
  relation := FinalizedEpoch E
  refl _ := ⟨rfl, Or.inl rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, by
    rcases h₂.2 with h | h
    · rw [h]; exact h₁.2
    · exact Or.inr h⟩

theorem FinalizedCheckpointAndSlotKept.finalizedEpoch {E : Nat} {s s' : GloasState P} (h : FinalizedCheckpointAndSlotKept s s') : FinalizedEpoch E s s' :=
  ⟨h.2, Or.inl h.1⟩

/-- A finalization rule that fired (`all(bits) and cp.epoch + k == current_epoch`, with
`k ≥ 1`) finalizes a checkpoint of an epoch before the current one. -/
theorem finalizes_lt {ce k : U64} {cp : Checkpoint} {a : Bool} {lift : Fallible Bool} {site : String}
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
  | `(tactic| gstep_close) => `(tactic| exact (show FinalizedEpoch _ _ _ from ⟨rfl, Or.inl rfl⟩))

theorem weighJustificationAndFinalization_finalizedEpoch (s : GloasState P) (t p c : Gwei) :
    Ok (JauneConsensus.Gloas.weighJustificationAndFinalization s t p c)
      ((finalizedEpoch (currentEpoch s)).relation s) := by
  unfold JauneConsensus.Gloas.weighJustificationAndFinalization; jvcg
  all_goals
    refine StepRelation.ok_rebase _ ?_ (JoinPointOk2.call ‹_› _ _)
    rename_i hfin _ _ ha
    have hlt := finalizes_lt hfin ha (by
      first
      | (rw [u64Checked_toNat ‹u64Checked 3 = .ok _›]; decide)
      | (rw [u64Checked_toNat ‹u64Checked 2 = .ok _›]; decide)
      | decide)
    have hce := getCurrentEpoch_toNat ‹JauneConsensus.Gloas.getCurrentEpoch s = _›
    refine ⟨rfl, Or.inr ?_⟩
    dsimp only
    omega

end Weigh

section Epoch

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinalizedCheckpointAndSlotKept _ _ from ⟨rfl, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (increaseBalance_finalizedAndSlotKept _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (decreaseBalance_finalizedAndSlotKept _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (computeExitEpochAndUpdateChurn_finalizedAndSlotKept _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (initiateValidatorExit_finalizedAndSlotKept _ _ _) $h; exact hh))

theorem addValidatorToRegistry_finalizedAndSlotKept (s : GloasState P) (pk : BLSPubkey) (wc : Bytes32) (amount : Gwei) :
    Ok (JauneConsensus.Gloas.addValidatorToRegistry s pk wc amount) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.addValidatorToRegistry; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (addValidatorToRegistry_finalizedAndSlotKept _ _ _ _) $h; exact hh))

theorem applyPendingDeposit_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P) (d : PendingDeposit) :
    Ok (JauneConsensus.Gloas.applyPendingDeposit ctx s d) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.applyPendingDeposit; gvcg
  · exact addValidatorToRegistry_finalizedAndSlotKept _ _ _ _
  · exact increaseBalance_finalizedAndSlotKept _ _ _

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (applyPendingDeposit_finalizedAndSlotKept _ _ _) $h; exact hh))

theorem processInactivityUpdates_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processInactivityUpdates cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processInactivityUpdates; gvcg

theorem processRewardsAndPenalties_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processRewardsAndPenalties cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processRewardsAndPenalties; gvcg

theorem processRegistryUpdates_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processRegistryUpdates cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processRegistryUpdates; gvcg

theorem processSlashings_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processSlashings cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processSlashings; gvcg

theorem processEth1DataReset_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processEth1DataReset cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processEth1DataReset; gvcg

section PendingDeposits

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRelation.forIn_array_relation _ (fun x => x.2.2.2.2) ?_ _ _ $h; intro _ _; gvcg))

theorem processPendingDeposits_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processPendingDeposits ctx s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processPendingDeposits; gvcg

end PendingDeposits

theorem processPendingConsolidations_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processPendingConsolidations cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processPendingConsolidations; gvcg

theorem processBuilderPendingPayments_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processBuilderPendingPayments cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processBuilderPendingPayments; gvcg

theorem processEffectiveBalanceUpdates_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processEffectiveBalanceUpdates cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processEffectiveBalanceUpdates; gvcg

theorem processSlashingsReset_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processSlashingsReset cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processSlashingsReset; gvcg

theorem processRandaoMixesReset_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processRandaoMixesReset cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processRandaoMixesReset; gvcg

theorem processHistoricalSummariesUpdate_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processHistoricalSummariesUpdate cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processHistoricalSummariesUpdate; gvcg

theorem processParticipationFlagUpdates_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processParticipationFlagUpdates cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processParticipationFlagUpdates; gvcg

theorem processSyncCommitteeUpdates_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processSyncCommitteeUpdates ctx s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processSyncCommitteeUpdates; gvcg

theorem processProposerLookahead_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processProposerLookahead cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processProposerLookahead; gvcg

theorem processPtcWindow_finalizedAndSlotKept (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processPtcWindow cfg s) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.processPtcWindow; gvcg

end Epoch

section EpochFE

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinalizedEpoch _ _ _ from ⟨rfl, Or.inl rfl⟩))

theorem processJustificationAndFinalization_finalizedEpoch (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processJustificationAndFinalization cfg s)
      ((finalizedEpoch (currentEpoch s)).relation s) := by
  unfold JauneConsensus.Gloas.processJustificationAndFinalization; gvcg
  all_goals exact weighJustificationAndFinalization_finalizedEpoch _ _ _ _

/-- **The Gloas epoch step** keeps the slot, and keeps the finalized checkpoint or moves it to
an epoch before the current one. -/
theorem processEpoch_finalizedEpoch {ctx : Ctx} {s s' : GloasState P}
    (h : JauneConsensus.Gloas.processEpoch ctx s = .ok s') : FinalizedEpoch (currentEpoch s) s s' := by
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
  have f1 := processJustificationAndFinalization_finalizedEpoch _ _ _ h1
  have f : FinalizedCheckpointAndSlotKept x1 s' :=
    finalizedCheckpointAndSlotKept.trans (processInactivityUpdates_finalizedAndSlotKept _ _ _ h2)
    (finalizedCheckpointAndSlotKept.trans (processRewardsAndPenalties_finalizedAndSlotKept _ _ _ h3)
    (finalizedCheckpointAndSlotKept.trans (processRegistryUpdates_finalizedAndSlotKept _ _ _ h4)
    (finalizedCheckpointAndSlotKept.trans (processSlashings_finalizedAndSlotKept _ _ _ h5)
    (finalizedCheckpointAndSlotKept.trans (processEth1DataReset_finalizedAndSlotKept _ _ _ h6)
    (finalizedCheckpointAndSlotKept.trans (processPendingDeposits_finalizedAndSlotKept _ _ _ h7)
    (finalizedCheckpointAndSlotKept.trans (processPendingConsolidations_finalizedAndSlotKept _ _ _ h8)
    (finalizedCheckpointAndSlotKept.trans (processBuilderPendingPayments_finalizedAndSlotKept _ _ _ h9)
    (finalizedCheckpointAndSlotKept.trans (processEffectiveBalanceUpdates_finalizedAndSlotKept _ _ _ h10)
    (finalizedCheckpointAndSlotKept.trans (processSlashingsReset_finalizedAndSlotKept _ _ _ h11)
    (finalizedCheckpointAndSlotKept.trans (processRandaoMixesReset_finalizedAndSlotKept _ _ _ h12)
    (finalizedCheckpointAndSlotKept.trans (processHistoricalSummariesUpdate_finalizedAndSlotKept _ _ _ h13)
    (finalizedCheckpointAndSlotKept.trans (processParticipationFlagUpdates_finalizedAndSlotKept _ _ _ h14)
    (finalizedCheckpointAndSlotKept.trans (processSyncCommitteeUpdates_finalizedAndSlotKept _ _ _ h15)
    (finalizedCheckpointAndSlotKept.trans (processProposerLookahead_finalizedAndSlotKept _ _ _ h16)
      (processPtcWindow_finalizedAndSlotKept _ _ _ h)))))))))))))))
  exact (finalizedEpoch _).trans f1 f.finalizedEpoch

end EpochFE

theorem processSlot_finalizedAndSlotKept (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processSlot s) (finalizedCheckpointAndSlotKept.relation s) := by
  rw [processSlot_eq]
  intro s' h
  unfold processSlotAbstractedHashes at h
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
theorem slotIteration_finalizedNotAhead {st st1 st2 : GloasState P} {next : U64} (hI : FinalizedNotAhead st)
    (f1 : FinalizedCheckpointAndSlotKept st st1) (hnext : next.toNat = st.slot.toNat + 1)
    (h2 : st2 = st1 ∨ FinalizedEpoch (currentEpoch st1) st1 st2) :
    FinalizedNotAhead { st2 with slot := next } := by
  have hmono : currentEpoch st ≤ next.toNat / P.SLOTS_PER_EPOCH := by
    unfold currentEpoch; rw [hnext]; exact Nat.div_le_div_right (by omega)
  have hc1 : currentEpoch st1 = currentEpoch st := by unfold currentEpoch; rw [f1.2]
  have hf1 : st1.finalized_checkpoint = st.finalized_checkpoint := f1.1
  unfold FinalizedNotAhead at hI ⊢
  show st2.finalized_checkpoint.epoch.toNat ≤ next.toNat / P.SLOTS_PER_EPOCH
  rcases h2 with rfl | ⟨-, hf | hf⟩
  · rw [hf1]; omega
  · rw [hf, hf1]; omega
  · omega

/-- **Gloas `process_slots` preserves FinalizedNotAhead.** -/
theorem processSlots_finalizedNotAhead {ctx : Ctx} {s s' : GloasState P} {slot : U64}
    (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s') (hI : FinalizedNotAhead s) :
    FinalizedNotAhead s' := by
  unfold JauneConsensus.Gloas.processSlots JauneConsensus.Gloas.processSlotsWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine range_forIn_invariant FinalizedNotAhead (fun a b x hb hx => ?_) hout hI
  obtain ⟨st1, h1, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨next, hn, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨r, hr, hx⟩ := bind_eq_ok_iff.mp hx
  have f1 := processSlot_finalizedAndSlotKept _ _ h1
  have hnext : next.toNat = b.slot.toNat + 1 := by
    rw [U64.toNat_add? hn, f1.2]; rfl
  simp only [] at hx
  split at hx
  · obtain ⟨st2, he, hx⟩ := bind_eq_ok_iff.mp hx
    cases hx
    exact slotIteration_finalizedNotAhead hb f1 hnext (Or.inr (processEpoch_finalizedEpoch he))
  · cases hx
    exact slotIteration_finalizedNotAhead hb f1 hnext (Or.inl rfl)

section Apply

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinalizedCheckpointAndSlotKept _ _ from ⟨rfl, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) => `(tactic| (have hh := processBlock_finalizedCheckpointAndSlotKept $h; exact hh))

theorem applySignedBlock_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P) (b : JauneConsensus.Gloas.SignedBeaconBlock P)
    (v : Bool) :
    Ok (JauneConsensus.Gloas.applySignedBlockWith (JauneConsensus.Gloas.processBlock ctx)
      ctx.blsActive s b v) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.applySignedBlockWith; gvcg

end Apply

/-- **Gloas `state_transition` preserves FinalizedNotAhead.** -/
theorem stateTransition_finalizedNotAhead {ctx : Ctx} {s s' : GloasState P}
    {b : JauneConsensus.Gloas.SignedBeaconBlock P} {v : Bool}
    (h : JauneConsensus.Gloas.stateTransition ctx s b v = .ok s') (hI : FinalizedNotAhead s) :
    FinalizedNotAhead s' := by
  rw [JauneConsensus.Gloas.stateTransition_eq] at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  exact (applySignedBlock_finalizedAndSlotKept _ _ _ _ _ h).finalizedNotAhead (processSlots_finalizedNotAhead h1 hI)

/-! ## The fork-indexed state (the Fulu anchors) -/

section Forked

variable {f : ConsensusFork}

/-- The finalized checkpoint and the slot are unchanged (fork-indexed). -/
def FinalizedCheckpointAndSlotKeptForkIndexed (s s' : JauneConsensus.BeaconState P f) : Prop :=
  s'.finalized_checkpoint = s.finalized_checkpoint ∧ s'.slot = s.slot

def finalizedCheckpointAndSlotKeptForkIndexed : StepRelation (JauneConsensus.BeaconState P f) where
  relation := FinalizedCheckpointAndSlotKeptForkIndexed
  refl _ := ⟨rfl, rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem FinalizedCheckpointAndSlotKeptForkIndexed.finalizedNotAhead {s s' : JauneConsensus.BeaconState P f} (h : FinalizedCheckpointAndSlotKeptForkIndexed s s')
    (hf : FinalizedNotAheadForkIndexed s) : FinalizedNotAheadForkIndexed s' := by
  unfold FinalizedNotAheadForkIndexed at *; rw [h.1, h.2]; exact hf

section BlockF

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinalizedCheckpointAndSlotKeptForkIndexed _ _ from ⟨rfl, rfl⟩))

/-- Close a tail call `Ok (g st ..) (finSlotF.R base)` by `g`'s lemma, possibly after a record
update of the base. Extended below as the lemmas are proved. -/
syntax "ftail" : tactic
macro "ftail_of " t:term : tactic =>
  `(tactic| first
    | (with_reducible apply $t); done
    | ((with_reducible refine StepRelation.ok_rebase finalizedCheckpointAndSlotKeptForkIndexed ?_ $t); exact ⟨rfl, rfl⟩))
local macro_rules | `(tactic| gstep) => `(tactic| ftail)
local macro_rules | `(tactic| jstep) => `(tactic| ftail)

theorem increaseBalance_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.increaseBalance s i d) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.increaseBalance; gvcg

theorem decreaseBalance_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.decreaseBalance s i d) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.decreaseBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (increaseBalance_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (increaseBalance_finalizedAndSlotKeptForkIndexed _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (decreaseBalance_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (decreaseBalance_finalizedAndSlotKeptForkIndexed _ _ _))

theorem computeExitEpochAndUpdateChurn_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f)
    (b : Gwei) :
    Ok (JauneConsensus.computeExitEpochAndUpdateChurn cfg s b) (fun p => finalizedCheckpointAndSlotKeptForkIndexed.relation s p.1) := by
  unfold JauneConsensus.computeExitEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (computeExitEpochAndUpdateChurn_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (computeExitEpochAndUpdateChurn_finalizedAndSlotKeptForkIndexed _ _ _))

theorem computeConsolidationEpochAndUpdateChurn_finalizedAndSlotKeptForkIndexed (cfg : Config)
    (s : JauneConsensus.BeaconState P f) (b : Gwei) :
    Ok (JauneConsensus.computeConsolidationEpochAndUpdateChurn cfg s b)
      (fun p => finalizedCheckpointAndSlotKeptForkIndexed.relation s p.1) := by
  unfold JauneConsensus.computeConsolidationEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (computeConsolidationEpochAndUpdateChurn_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (computeConsolidationEpochAndUpdateChurn_finalizedAndSlotKeptForkIndexed _ _ _))

set_option maxHeartbeats 2000000 in
theorem initiateValidatorExit_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f)
    (i : ValidatorIndex) :
    Ok (JauneConsensus.initiateValidatorExit cfg s i) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.initiateValidatorExit; gvcg
  all_goals
    apply ok_pure
    have hp := ‹(pure (s, _) : Fallible (JauneConsensus.BeaconState P f × Epoch)) = Except.ok _›
    cases hp; exact ⟨rfl, rfl⟩

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (initiateValidatorExit_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (initiateValidatorExit_finalizedAndSlotKeptForkIndexed _ _ _))

theorem slashValidator_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f)
    (i : ValidatorIndex) (wb : Option ValidatorIndex) :
    Ok (JauneConsensus.slashValidator cfg s i wb) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.slashValidator; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (slashValidator_finalizedAndSlotKeptForkIndexed _ _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (slashValidator_finalizedAndSlotKeptForkIndexed _ _ _ _))

theorem queueExcessActiveBalance_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) (i : ValidatorIndex) :
    Ok (JauneConsensus.queueExcessActiveBalance s i) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.queueExcessActiveBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (queueExcessActiveBalance_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (queueExcessActiveBalance_finalizedAndSlotKeptForkIndexed _ _))

theorem switchToCompoundingValidator_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f)
    (i : ValidatorIndex) :
    Ok (JauneConsensus.switchToCompoundingValidator s i) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.switchToCompoundingValidator; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (switchToCompoundingValidator_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (switchToCompoundingValidator_finalizedAndSlotKeptForkIndexed _ _))

theorem setDepositRequestsStartIndex_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setDepositRequestsStartIndex s v) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.BeaconState.setDepositRequestsStartIndex; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (setDepositRequestsStartIndex_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setDepositRequestsStartIndex_finalizedAndSlotKeptForkIndexed _ _))

theorem setDepositBalanceToConsume_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setDepositBalanceToConsume s v) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.BeaconState.setDepositBalanceToConsume; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (setDepositBalanceToConsume_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setDepositBalanceToConsume_finalizedAndSlotKeptForkIndexed _ _))

theorem setExitBalanceToConsume_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setExitBalanceToConsume s v) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.BeaconState.setExitBalanceToConsume; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (setExitBalanceToConsume_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setExitBalanceToConsume_finalizedAndSlotKeptForkIndexed _ _))

theorem setEarliestExitEpoch_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setEarliestExitEpoch s v) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.BeaconState.setEarliestExitEpoch; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (setEarliestExitEpoch_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setEarliestExitEpoch_finalizedAndSlotKeptForkIndexed _ _))

theorem setConsolidationBalanceToConsume_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setConsolidationBalanceToConsume s v) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.BeaconState.setConsolidationBalanceToConsume; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (setConsolidationBalanceToConsume_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setConsolidationBalanceToConsume_finalizedAndSlotKeptForkIndexed _ _))

theorem setEarliestConsolidationEpoch_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setEarliestConsolidationEpoch s v) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.BeaconState.setEarliestConsolidationEpoch; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (setEarliestConsolidationEpoch_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setEarliestConsolidationEpoch_finalizedAndSlotKeptForkIndexed _ _))

theorem setPendingDeposits_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setPendingDeposits s v) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.BeaconState.setPendingDeposits; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (setPendingDeposits_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setPendingDeposits_finalizedAndSlotKeptForkIndexed _ _))

theorem setPendingPartialWithdrawals_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setPendingPartialWithdrawals s v) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.BeaconState.setPendingPartialWithdrawals; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (setPendingPartialWithdrawals_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setPendingPartialWithdrawals_finalizedAndSlotKeptForkIndexed _ _))

theorem setPendingConsolidations_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setPendingConsolidations s v) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.BeaconState.setPendingConsolidations; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (setPendingConsolidations_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setPendingConsolidations_finalizedAndSlotKeptForkIndexed _ _))

theorem setProposerLookahead_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) v :
    Ok (JauneConsensus.BeaconState.setProposerLookahead s v) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.BeaconState.setProposerLookahead; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (setProposerLookahead_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (setProposerLookahead_finalizedAndSlotKeptForkIndexed _ _))

theorem addValidatorToRegistry_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) (pk : BLSPubkey)
    (wc : Bytes32) (amount : Gwei) :
    Ok (JauneConsensus.addValidatorToRegistry s pk wc amount) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.addValidatorToRegistry; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (addValidatorToRegistry_finalizedAndSlotKeptForkIndexed _ _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (addValidatorToRegistry_finalizedAndSlotKeptForkIndexed _ _ _ _))

theorem applyDeposit_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f) (pk : BLSPubkey)
    (wc : Bytes32) (amount : Gwei) (sig : BLSSignature) :
    Ok (JauneConsensus.applyDeposit ctx s pk wc amount sig) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.applyDeposit; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (applyDeposit_finalizedAndSlotKeptForkIndexed _ _ _ _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (applyDeposit_finalizedAndSlotKeptForkIndexed _ _ _ _ _ _))

theorem processDeposit_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f) (d : Deposit) :
    Ok (JauneConsensus.processDeposit ctx s d) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processDeposit; gvcg

theorem processDepositRequest_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) (dr : DepositRequest) :
    Ok (JauneConsensus.processDepositRequest s dr) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processDepositRequest; gvcg

theorem processWithdrawalRequest_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f)
    (wr : WithdrawalRequest) :
    Ok (JauneConsensus.processWithdrawalRequest cfg s wr) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processWithdrawalRequest; gvcg

theorem processConsolidationRequest_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f)
    (cr : ConsolidationRequest) :
    Ok (JauneConsensus.processConsolidationRequest cfg s cr) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processConsolidationRequest; gvcg

theorem processBlsToExecutionChange_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (sac : SignedBLSToExecutionChange) :
    Ok (JauneConsensus.processBlsToExecutionChange ctx s sac) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processBlsToExecutionChange; gvcg

theorem processVoluntaryExit_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (sve : SignedVoluntaryExit) :
    Ok (JauneConsensus.processVoluntaryExit ctx s sve) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processVoluntaryExit; gvcg

theorem processProposerSlashing_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (ps : ProposerSlashing) :
    Ok (JauneConsensus.processProposerSlashing ctx s ps) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processProposerSlashing; gvcg

theorem processAttesterSlashing_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (as : AttesterSlashing P f) :
    Ok (JauneConsensus.processAttesterSlashing ctx s as) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processAttesterSlashing; gvcg

set_option maxHeartbeats 8000000 in
theorem processAttestation_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (a : Attestation P f) :
    Ok (JauneConsensus.processAttestation ctx s a) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processAttestation; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processDeposit_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processDeposit_finalizedAndSlotKeptForkIndexed _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processDepositRequest_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processDepositRequest_finalizedAndSlotKeptForkIndexed _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processWithdrawalRequest_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processWithdrawalRequest_finalizedAndSlotKeptForkIndexed _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processConsolidationRequest_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processConsolidationRequest_finalizedAndSlotKeptForkIndexed _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processBlsToExecutionChange_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processBlsToExecutionChange_finalizedAndSlotKeptForkIndexed _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processVoluntaryExit_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processVoluntaryExit_finalizedAndSlotKeptForkIndexed _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processProposerSlashing_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processProposerSlashing_finalizedAndSlotKeptForkIndexed _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processAttesterSlashing_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processAttesterSlashing_finalizedAndSlotKeptForkIndexed _ _ _))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processAttestation_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processAttestation_finalizedAndSlotKeptForkIndexed _ _ _))

set_option maxHeartbeats 8000000 in
theorem processOperations_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processOperations ctx s body) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processOperations; jvcg

theorem processBlockHeader_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) (blk : BeaconBlock P f) :
    Ok (JauneConsensus.processBlockHeader s blk) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processBlockHeader; gvcg

theorem processRandao_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processRandao ctx s body) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processRandao; gvcg

theorem processEth1Data_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processEth1Data s body) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processEth1Data; gvcg

theorem processWithdrawals_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) (pl : ExecutionPayload P) :
    Ok (JauneConsensus.processWithdrawals s pl) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processWithdrawals
  with_reducible apply ok_bind
  intro x hx
  rcases x with ⟨ex, n⟩
  jvcg

theorem processExecutionPayload_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (body : BeaconBlockBody P f) :
    Ok (JauneConsensus.processExecutionPayload ctx s body) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processExecutionPayload; gvcg

set_option maxHeartbeats 8000000 in
theorem processSyncAggregate_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f)
    (sa : SyncAggregate P) :
    Ok (JauneConsensus.processSyncAggregate ctx s sa) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processSyncAggregate; jvcg

/-- **A fork-indexed block keeps the finalized checkpoint and the slot.** -/
theorem processBlock_finalizedCheckpointAndSlotKeptForkIndexed {ctx : Ctx} {s s' : JauneConsensus.BeaconState P f}
    {blk : BeaconBlock P f} (h : JauneConsensus.processBlock ctx s blk = .ok s') :
    FinalizedCheckpointAndSlotKeptForkIndexed s s' := by
  unfold JauneConsensus.processBlock JauneConsensus.processBlockWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h⟩ := bind_eq_ok_iff.mp h
  exact finalizedCheckpointAndSlotKeptForkIndexed.trans (processBlockHeader_finalizedAndSlotKeptForkIndexed _ _ _ h1)
    (finalizedCheckpointAndSlotKeptForkIndexed.trans (processWithdrawals_finalizedAndSlotKeptForkIndexed _ _ _ h2)
    (finalizedCheckpointAndSlotKeptForkIndexed.trans (processExecutionPayload_finalizedAndSlotKeptForkIndexed _ _ _ _ h3)
    (finalizedCheckpointAndSlotKeptForkIndexed.trans (processRandao_finalizedAndSlotKeptForkIndexed _ _ _ _ h4)
    (finalizedCheckpointAndSlotKeptForkIndexed.trans (processEth1Data_finalizedAndSlotKeptForkIndexed _ _ _ h5)
    (finalizedCheckpointAndSlotKeptForkIndexed.trans (processOperations_finalizedAndSlotKeptForkIndexed _ _ _ _ h6)
      (processSyncAggregate_finalizedAndSlotKeptForkIndexed _ _ _ _ h))))))

/-- **A fork-indexed (Fulu) block preserves FinalizedNotAhead.** -/
theorem processBlock_finalizedNotAheadForkIndexed {ctx : Ctx} {s s' : JauneConsensus.BeaconState P f}
    {blk : BeaconBlock P f} (h : JauneConsensus.processBlock ctx s blk = .ok s')
    (hf : FinalizedNotAheadForkIndexed s) : FinalizedNotAheadForkIndexed s' :=
  (processBlock_finalizedCheckpointAndSlotKeptForkIndexed h).finalizedNotAhead hf


set_option maxHeartbeats 4000000 in
theorem processInactivityUpdates_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processInactivityUpdates cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processInactivityUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processInactivityUpdates_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processInactivityUpdates_finalizedAndSlotKeptForkIndexed _ _))

theorem processRewardsAndPenalties_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processRewardsAndPenalties cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processRewardsAndPenalties; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processRewardsAndPenalties_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processRewardsAndPenalties_finalizedAndSlotKeptForkIndexed _ _))

theorem processRegistryUpdatesElectra_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processRegistryUpdatesElectra cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processRegistryUpdatesElectra; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processRegistryUpdatesElectra_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processRegistryUpdatesElectra_finalizedAndSlotKeptForkIndexed _ _))

theorem processRegistryUpdatesDeneb_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processRegistryUpdatesDeneb cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processRegistryUpdatesDeneb; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processRegistryUpdatesDeneb_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processRegistryUpdatesDeneb_finalizedAndSlotKeptForkIndexed _ _))

theorem processRegistryUpdates_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processRegistryUpdates cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processRegistryUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processRegistryUpdates_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processRegistryUpdates_finalizedAndSlotKeptForkIndexed _ _))

set_option maxHeartbeats 4000000 in
theorem processSlashings_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processSlashings cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processSlashings; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processSlashings_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processSlashings_finalizedAndSlotKeptForkIndexed _ _))

theorem processEth1DataReset_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processEth1DataReset cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processEth1DataReset; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processEth1DataReset_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processEth1DataReset_finalizedAndSlotKeptForkIndexed _ _))

theorem applyPendingDeposit_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f) (d : PendingDeposit) :
    Ok (JauneConsensus.applyPendingDeposit ctx s d) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.applyPendingDeposit; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (applyPendingDeposit_finalizedAndSlotKeptForkIndexed _ _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (applyPendingDeposit_finalizedAndSlotKeptForkIndexed _ _ _))

section PendingDepositsF

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRelation.forIn_array_relation _ (fun x => x.2.2.2.2) ?_ _ _ $h; intro _ _; gvcg))

set_option maxHeartbeats 4000000 in
theorem processPendingDeposits_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processPendingDeposits ctx s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processPendingDeposits; gvcg

end PendingDepositsF

theorem processPendingConsolidations_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processPendingConsolidations cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processPendingConsolidations; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processPendingConsolidations_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processPendingConsolidations_finalizedAndSlotKeptForkIndexed _ _))

theorem processEffectiveBalanceUpdates_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processEffectiveBalanceUpdates cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processEffectiveBalanceUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processEffectiveBalanceUpdates_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processEffectiveBalanceUpdates_finalizedAndSlotKeptForkIndexed _ _))

theorem processSlashingsReset_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processSlashingsReset cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processSlashingsReset; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processSlashingsReset_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processSlashingsReset_finalizedAndSlotKeptForkIndexed _ _))

theorem processRandaoMixesReset_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processRandaoMixesReset cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processRandaoMixesReset; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processRandaoMixesReset_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processRandaoMixesReset_finalizedAndSlotKeptForkIndexed _ _))

theorem processHistoricalSummariesUpdate_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processHistoricalSummariesUpdate cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processHistoricalSummariesUpdate; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processHistoricalSummariesUpdate_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processHistoricalSummariesUpdate_finalizedAndSlotKeptForkIndexed _ _))

theorem processParticipationFlagUpdates_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processParticipationFlagUpdates cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processParticipationFlagUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processParticipationFlagUpdates_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processParticipationFlagUpdates_finalizedAndSlotKeptForkIndexed _ _))

theorem processSyncCommitteeUpdates_finalizedAndSlotKeptForkIndexed (ctx : Ctx) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processSyncCommitteeUpdates ctx s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processSyncCommitteeUpdates; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processSyncCommitteeUpdates_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processSyncCommitteeUpdates_finalizedAndSlotKeptForkIndexed _ _))

theorem processProposerLookahead_finalizedAndSlotKeptForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processProposerLookahead cfg s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  unfold JauneConsensus.processProposerLookahead; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processProposerLookahead_finalizedAndSlotKeptForkIndexed _ _) $h); exact hh))
local macro_rules | `(tactic| ftail) => `(tactic| ftail_of (processProposerLookahead_finalizedAndSlotKeptForkIndexed _ _))

end BlockF

/-- The slot is kept, and the finalized checkpoint is kept or has an epoch below `E`
(fork-indexed). -/
def FinalizedEpochForkIndexed (E : Nat) (s s' : JauneConsensus.BeaconState P f) : Prop :=
  s'.slot = s.slot ∧
    (s'.finalized_checkpoint = s.finalized_checkpoint ∨ s'.finalized_checkpoint.epoch.toNat < E)

def finalizedEpochForkIndexed (E : Nat) : StepRelation (JauneConsensus.BeaconState P f) where
  relation := FinalizedEpochForkIndexed E
  refl _ := ⟨rfl, Or.inl rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, by
    rcases h₂.2 with h | h
    · rw [h]; exact h₁.2
    · exact Or.inr h⟩

theorem FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch {E : Nat} {s s' : JauneConsensus.BeaconState P f} (h : FinalizedCheckpointAndSlotKeptForkIndexed s s') :
    FinalizedEpochForkIndexed E s s' :=
  ⟨h.2, Or.inl h.1⟩

theorem getCurrentEpochForkIndexed_toNat {s : JauneConsensus.BeaconState P f} {e : U64}
    (h : JauneConsensus.getCurrentEpoch s = .ok e) :
    e.toNat = s.slot.toNat / P.SLOTS_PER_EPOCH := by
  unfold JauneConsensus.getCurrentEpoch at h; exact computeEpochAtSlot_toNat h

section WeighF

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinalizedEpochForkIndexed _ _ _ from ⟨rfl, Or.inl rfl⟩))

set_option maxHeartbeats 4000000 in
theorem weighJustificationAndFinalization_finalizedEpochForkIndexed (s : JauneConsensus.BeaconState P f) (t p c : Gwei) :
    Ok (JauneConsensus.weighJustificationAndFinalization s t p c)
      ((finalizedEpochForkIndexed (s.slot.toNat / P.SLOTS_PER_EPOCH)).relation s) := by
  unfold JauneConsensus.weighJustificationAndFinalization; jvcg
  all_goals
    refine StepRelation.ok_rebase _ ?_ (JoinPointOk2.call ‹_› _ _)
    rename_i hfin _ _ ha
    have hlt := finalizes_lt hfin ha (by
      first
      | (rw [u64Checked_toNat ‹u64Checked 3 = .ok _›]; decide)
      | (rw [u64Checked_toNat ‹u64Checked 2 = .ok _›]; decide)
      | decide)
    have hce := getCurrentEpochForkIndexed_toNat ‹JauneConsensus.getCurrentEpoch s = _›
    refine ⟨rfl, Or.inr ?_⟩
    dsimp only
    omega

end WeighF

section EpochF

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinalizedEpochForkIndexed _ _ _ from ⟨rfl, Or.inl rfl⟩))

set_option maxHeartbeats 4000000 in
theorem processJustificationAndFinalization_finalizedEpochForkIndexed (cfg : Config) (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processJustificationAndFinalization cfg s)
      ((finalizedEpochForkIndexed (s.slot.toNat / P.SLOTS_PER_EPOCH)).relation s) := by
  unfold JauneConsensus.processJustificationAndFinalization; gvcg
  all_goals exact weighJustificationAndFinalization_finalizedEpochForkIndexed _ _ _ _

end EpochF

section EpochF2

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinalizedEpochForkIndexed _ _ _ from ⟨rfl, Or.inl rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processJustificationAndFinalization_finalizedEpochForkIndexed _ _) $h); exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processInactivityUpdates_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processRewardsAndPenalties_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processRegistryUpdates_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processSlashings_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processEth1DataReset_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processPendingDeposits_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processPendingConsolidations_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processEffectiveBalanceUpdates_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processSlashingsReset_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processRandaoMixesReset_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processHistoricalSummariesUpdate_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processParticipationFlagUpdates_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processSyncCommitteeUpdates_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| ((with_reducible have hh := StepRelation.of_ok (processProposerLookahead_finalizedAndSlotKeptForkIndexed _ _) $h); exact FinalizedCheckpointAndSlotKeptForkIndexed.finalizedEpoch hh))

/-- **The fork-indexed epoch step** keeps the slot, and keeps the finalized checkpoint or moves it
to an epoch before the current one. -/
theorem processEpoch_finalizedEpochForkIndexed {ctx : Ctx} {s s' : JauneConsensus.BeaconState P f}
    (h : JauneConsensus.processEpoch ctx s = .ok s') :
    FinalizedEpochForkIndexed (s.slot.toNat / P.SLOTS_PER_EPOCH) s s' := by
  unfold JauneConsensus.processEpoch at h
  dsimp only at h
  obtain ⟨x1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x6, h6, h⟩ := bind_eq_ok_iff.mp h
  have f1 := processJustificationAndFinalization_finalizedEpochForkIndexed _ _ _ h1
  have f6 : FinalizedCheckpointAndSlotKeptForkIndexed x1 x6 :=
    finalizedCheckpointAndSlotKeptForkIndexed.trans (processInactivityUpdates_finalizedAndSlotKeptForkIndexed _ _ _ h2)
    (finalizedCheckpointAndSlotKeptForkIndexed.trans (processRewardsAndPenalties_finalizedAndSlotKeptForkIndexed _ _ _ h3)
    (finalizedCheckpointAndSlotKeptForkIndexed.trans (processRegistryUpdates_finalizedAndSlotKeptForkIndexed _ _ _ h4)
    (finalizedCheckpointAndSlotKeptForkIndexed.trans (processSlashings_finalizedAndSlotKeptForkIndexed _ _ _ h5) (processEth1DataReset_finalizedAndSlotKeptForkIndexed _ _ _ h6))))
  have tail : ∀ x7 : JauneConsensus.BeaconState P f, FinalizedCheckpointAndSlotKeptForkIndexed x6 x7 →
      (do
        let state ← JauneConsensus.processEffectiveBalanceUpdates ctx.config x7
        let state ← JauneConsensus.processSlashingsReset ctx.config state
        let state ← JauneConsensus.processRandaoMixesReset ctx.config state
        let state ← JauneConsensus.processHistoricalSummariesUpdate ctx.config state
        let state ← JauneConsensus.processParticipationFlagUpdates ctx.config state
        let state ← JauneConsensus.processSyncCommitteeUpdates ctx state
        if f.atLeast ConsensusFork.fulu = true then JauneConsensus.processProposerLookahead ctx.config state
          else pure state) = .ok s' → FinalizedCheckpointAndSlotKeptForkIndexed x6 s' := by
    intro x7 f7 h
    obtain ⟨x8, h8, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x9, h9, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x10, h10, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x11, h11, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x12, h12, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x13, h13, h⟩ := bind_eq_ok_iff.mp h
    have f14 : FinalizedCheckpointAndSlotKeptForkIndexed x13 s' := by
      split at h
      · exact processProposerLookahead_finalizedAndSlotKeptForkIndexed _ _ _ h
      · cases h; exact finalizedCheckpointAndSlotKeptForkIndexed.refl _
    exact finalizedCheckpointAndSlotKeptForkIndexed.trans f7
      (finalizedCheckpointAndSlotKeptForkIndexed.trans (processEffectiveBalanceUpdates_finalizedAndSlotKeptForkIndexed _ _ _ h8)
      (finalizedCheckpointAndSlotKeptForkIndexed.trans (processSlashingsReset_finalizedAndSlotKeptForkIndexed _ _ _ h9)
      (finalizedCheckpointAndSlotKeptForkIndexed.trans (processRandaoMixesReset_finalizedAndSlotKeptForkIndexed _ _ _ h10)
      (finalizedCheckpointAndSlotKeptForkIndexed.trans (processHistoricalSummariesUpdate_finalizedAndSlotKeptForkIndexed _ _ _ h11)
      (finalizedCheckpointAndSlotKeptForkIndexed.trans (processParticipationFlagUpdates_finalizedAndSlotKeptForkIndexed _ _ _ h12)
      (finalizedCheckpointAndSlotKeptForkIndexed.trans (processSyncCommitteeUpdates_finalizedAndSlotKeptForkIndexed _ _ _ h13) f14))))))
  have f : FinalizedCheckpointAndSlotKeptForkIndexed x6 s' := by
    split at h
    · obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨z, hz, h⟩ := bind_eq_ok_iff.mp h
      exact tail z (finalizedCheckpointAndSlotKeptForkIndexed.trans (processPendingDeposits_finalizedAndSlotKeptForkIndexed _ _ _ hy)
        (processPendingConsolidations_finalizedAndSlotKeptForkIndexed _ _ _ hz)) h
    · exact tail x6 (finalizedCheckpointAndSlotKeptForkIndexed.refl _) h
  exact (finalizedEpochForkIndexed _).trans f1 (finalizedCheckpointAndSlotKeptForkIndexed.trans f6 f).finalizedEpoch

end EpochF2

theorem processSlot_finalizedAndSlotKeptForkIndexed (s : JauneConsensus.BeaconState P f) :
    Ok (JauneConsensus.processSlot s) (finalizedCheckpointAndSlotKeptForkIndexed.relation s) := by
  intro s' h
  unfold JauneConsensus.processSlot at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine ⟨?_, ?_⟩ <;> split <;> rfl

/-- **Fork-indexed `process_slots` preserves FinalizedNotAhead.** -/
theorem processSlots_finalizedNotAheadForkIndexed {ctx : Ctx} {s s' : JauneConsensus.BeaconState P f}
    {slot : U64} (h : JauneConsensus.processSlots ctx s slot = .ok s')
    (hI : FinalizedNotAheadForkIndexed s) : FinalizedNotAheadForkIndexed s' := by
  unfold JauneConsensus.processSlots JauneConsensus.processSlotsWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine range_forIn_invariant FinalizedNotAheadForkIndexed (fun a b x hb hx => ?_) hout hI
  obtain ⟨st1, h1, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨next, hn, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨r, hr, hx⟩ := bind_eq_ok_iff.mp hx
  have f1 := processSlot_finalizedAndSlotKeptForkIndexed _ _ h1
  have hnext : next.toNat = b.slot.toNat + 1 := by
    rw [U64.toNat_add? hn, f1.2]; rfl
  have hmono : b.slot.toNat / P.SLOTS_PER_EPOCH ≤ next.toNat / P.SLOTS_PER_EPOCH := by
    rw [hnext]; exact Nat.div_le_div_right (by omega)
  have hf1 : st1.finalized_checkpoint = b.finalized_checkpoint := f1.1
  have hs1 : st1.slot = b.slot := f1.2
  unfold FinalizedNotAheadForkIndexed at hb
  simp only [] at hx
  split at hx
  · obtain ⟨st2, he, hx⟩ := bind_eq_ok_iff.mp hx
    cases hx
    have fe := processEpoch_finalizedEpochForkIndexed he
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
  | `(tactic| gstep_close) => `(tactic| exact (show FinalizedCheckpointAndSlotKeptForkIndexed _ _ from ⟨rfl, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) => `(tactic| (have hh := processBlock_finalizedCheckpointAndSlotKeptForkIndexed $h; exact hh))

/-- **Fork-indexed `state_transition` preserves FinalizedNotAhead.** -/
theorem stateTransition_finalizedNotAheadForkIndexed {ctx : Ctx} {s s' : JauneConsensus.BeaconState P f}
    {b : SignedBeaconBlock P f} {v : Bool}
    (h : JauneConsensus.stateTransition ctx s b v = .ok s') (hI : FinalizedNotAheadForkIndexed s) :
    FinalizedNotAheadForkIndexed s' := by
  unfold JauneConsensus.stateTransition JauneConsensus.stateTransitionWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  have hI1 : FinalizedNotAheadForkIndexed s1 := processSlots_finalizedNotAheadForkIndexed (ctx := ctx) h1 hI
  refine FinalizedCheckpointAndSlotKeptForkIndexed.finalizedNotAhead ((?_ : Ok _ (finalizedCheckpointAndSlotKeptForkIndexed.relation s1)) _ h) hI1
  gvcg

end ApplyF

end Forked

/-! ## The crossing -/

theorem upgradedState_finalizedCheckpointAndSlotKept {cfg : Config} {pre : JauneConsensus.BeaconState P .fulu}
    {post : GloasState P} (h : JauneConsensus.Gloas.upgradedState cfg pre = .ok post) :
    post.finalized_checkpoint = pre.finalized_checkpoint ∧ post.slot = pre.slot := by
  unfold JauneConsensus.Gloas.upgradedState at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact ⟨rfl, rfl⟩

section Onboard

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show FinalizedCheckpointAndSlotKept _ _ from ⟨rfl, rfl⟩))

theorem addBuilderToRegistry_finalizedAndSlotKept (s : GloasState P) (pk : BLSPubkey) (v : U8) (a : ExecutionAddress)
    (amount : Gwei) (slot : Slot) :
    Ok (JauneConsensus.Gloas.addBuilderToRegistry s pk v a amount slot) (finalizedCheckpointAndSlotKept.relation s) := by
  unfold JauneConsensus.Gloas.addBuilderToRegistry; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (addBuilderToRegistry_finalizedAndSlotKept _ _ _ _ _ _) $h; exact hh))

theorem onboardBuilderDeposit_finalizedAndSlotKept (ctx : Ctx) (vp : Array BLSPubkey) (st : GloasState P)
    (pd : Array PendingDeposit) (d : PendingDeposit) :
    Ok (JauneConsensus.Gloas.onboardBuilderDeposit ctx vp (st, pd) d)
      (fun r => finalizedCheckpointAndSlotKept.relation st r.1) := by
  unfold JauneConsensus.Gloas.onboardBuilderDeposit; gvcg

end Onboard

theorem foldlM_onboard_finalizedAndSlotKept (ctx : Ctx) (vp : Array BLSPubkey) :
    ∀ (l : List PendingDeposit) (st : GloasState P) (pd : Array PendingDeposit) (out : GloasState P × Array PendingDeposit),
      l.foldlM (JauneConsensus.Gloas.onboardBuilderDeposit ctx vp) (st, pd) = .ok out →
      FinalizedCheckpointAndSlotKept st out.1
  | [], st, pd, out, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact finalizedCheckpointAndSlotKept.refl _
  | d :: l, st, pd, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨⟨st', pd'⟩, h1, h⟩ := bind_eq_ok_iff.mp h
    exact finalizedCheckpointAndSlotKept.trans (onboardBuilderDeposit_finalizedAndSlotKept ctx vp st pd d _ h1)
      (foldlM_onboard_finalizedAndSlotKept ctx vp l st' pd' out h)

theorem onboardBuildersFromPendingDeposits_finalizedAndSlotKept (ctx : Ctx) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.onboardBuildersFromPendingDeposits ctx s) (finalizedCheckpointAndSlotKept.relation s) := by
  intro s' h
  unfold JauneConsensus.Gloas.onboardBuildersFromPendingDeposits at h
  obtain ⟨⟨st, pd⟩, h1, h⟩ := bind_eq_ok_iff.mp h
  cases h
  rw [← Array.foldlM_toList] at h1
  exact foldlM_onboard_finalizedAndSlotKept ctx _ _ s #[] _ h1

/-- `upgrade_to_gloas` copies the finalized checkpoint and the slot. -/
theorem upgradeToGloas_finalizedCheckpointAndSlotKept {ctx : Ctx} {pre : JauneConsensus.BeaconState P .fulu}
    {post : GloasState P} (h : JauneConsensus.Gloas.upgradeToGloas ctx pre = .ok post) :
    post.finalized_checkpoint = pre.finalized_checkpoint ∧ post.slot = pre.slot := by
  unfold JauneConsensus.Gloas.upgradeToGloas at h
  obtain ⟨p0, h0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, _, h⟩ := bind_eq_ok_iff.mp h
  have e0 := upgradedState_finalizedCheckpointAndSlotKept h0
  have e1 := onboardBuildersFromPendingDeposits_finalizedAndSlotKept ctx _ _ h
  exact ⟨e1.1.trans e0.1, e1.2.trans e0.2⟩

/-- **`upgrade_to_gloas` preserves FinalizedNotAhead.** -/
theorem upgradeToGloas_finalizedNotAhead {ctx : Ctx} {pre : JauneConsensus.BeaconState P .fulu}
    {post : GloasState P} (h : JauneConsensus.Gloas.upgradeToGloas ctx pre = .ok post)
    (hI : FinalizedNotAheadForkIndexed pre) : FinalizedNotAhead post := by
  obtain ⟨e1, e2⟩ := upgradeToGloas_finalizedCheckpointAndSlotKept h
  unfold FinalizedNotAhead currentEpoch; unfold FinalizedNotAheadForkIndexed at hI
  rw [e1, e2]; exact hI

/-- **The crossing preserves FinalizedNotAhead**: the Fulu `process_slots` to the fork slot, then
`upgrade_to_gloas`. -/
theorem crossFromFulu_finalizedNotAhead {ctx : Ctx} {pre : JauneConsensus.BeaconState P .fulu}
    {post : GloasState P} (h : JauneConsensus.Gloas.crossFromFulu ctx pre = .ok post)
    (hI : FinalizedNotAheadForkIndexed pre) : FinalizedNotAhead post := by
  unfold JauneConsensus.Gloas.crossFromFulu at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨pre', hp, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    exact upgradeToGloas_finalizedNotAhead h (processSlots_finalizedNotAheadForkIndexed hp hI)
  · obtain ⟨pre', hp, h⟩ := bind_eq_ok_iff.mp h
    cases hp
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    exact upgradeToGloas_finalizedNotAhead h hI

end JauneConsensus.Facts.Gloas.Invariant
