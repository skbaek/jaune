import JauneConsensus.Facts.Gloas.InvariantsCrossing
import JauneConsensus.Facts.Gloas.BalanceFlowWitnesses
import JauneConsensus.Facts.Gloas.BuilderWitnesses

/-!
# Closed-state controls for the G3 invariants (goal `eip8282-gloas-cross-layer-v1`, G3a)

Each control is a closed minimal-preset state on which an invariant fails, run through the real
functions, showing what the invariant protects (design.md §5, "counterexample state without it").
Reused, not repeated: the G3-01 control is `Witnesses.g301_*` (`BuilderWitnesses.lean`: with a
duplicated pubkey, builder 1 can never be exited by its own address, B4's resolution clause), and
the G3-05 saturation witness is `B5Witnesses.saturation_witness` (pending 16 against balance 10:
`apply_withdrawals` saturates while the execution layer is credited 16, B5(i)).

* `g303_control`: G3-03 fails (a pending withdrawal names builder index 0 of an empty registry);
  a builder deposit then registers a new builder `K` at index 0, and the builder withdrawals
  debit `K` by the stale entry's 5 gwei: B5(ii) ("a bid this builder signed") fails for `K`.
* `g304_control`: G3-04 fails (exited, swept builder 0 still has a pending withdrawal of 5); a
  deposit for a new pubkey reuses slot 0, and the builder withdrawals debit the new builder by 5
  (B5(ii), slot reuse).
* `g306_control`: G3-06 fails (sweep index 5, one builder); the builders sweep rejects, so the
  chain cannot extend (non-vacuity, no B clause).
* `g307_control`: G3-07 fails (`L`'s live entry carries weight above the quorum); the epoch
  rotation appends `L`'s withdrawal and the parent-older-than-previous-epoch settlement appends it
  again: two pending withdrawals for one bid (B5(iii)).
-/

namespace JauneConsensus.Facts.Gloas.Invariant.Controls

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas JauneConsensus.Facts.Gloas.Invariant

/-- The minimal-preset Gloas state. -/
abbrev MinimalGloasState := JauneConsensus.Gloas.BeaconState Preset.minimal

/-- BLS off, minimal configuration. -/
def contextBlsOff : Context := { config := Config.minimal, blsActive := false }

/-- A pending withdrawal of 5 gwei to builder index 0. -/
def withdrawalOfFive : JauneConsensus.Gloas.BuilderPendingWithdrawal :=
  { fee_recipient := Witnesses.address ⟨7⟩, amount := U64.literal 5, builder_index := U64.zero }

/-- The new builder's deposit: a fresh pubkey with the builder prefix (BLS off). -/
def depositKey : JauneConsensus.Gloas.BuilderDepositRequest := Witnesses.depositRequest 9 Witnesses.builderPrefixWord 0xc0

/-- Register `depK`, then run the builder-withdrawals phase and apply it: the balances of the
registry after the registration and after the withdrawals. -/
def registerThenWithdraw (s : MinimalGloasState) : Fallible (Array U64 × Array U64) := do
  let s1 ← JauneConsensus.Gloas.processBuilderDepositRequest contextBlsOff s depositKey
  let (ws, _, _) ← JauneConsensus.Gloas.getBuilderWithdrawals s1 U64.zero #[]
  let s2 ← JauneConsensus.Gloas.applyWithdrawals s1 ws
  pure (s1.builders.toArray.map (·.balance), s2.builders.toArray.map (·.balance))

/-! ## G3-03 -/

/-- An empty registry with a pending withdrawal naming builder index 0. -/
def stateUnknownBuilderWithdrawal : MinimalGloasState := { BalanceFlowWitnesses.balanceFlowBase with
  builder_pending_withdrawals := ProgressiveListOnSpine.ofArray #[withdrawalOfFive] }

/-- **G3-03 control.** -/
theorem pendingReferencesInRange_control :
    ¬ PendingReferencesInRange stateUnknownBuilderWithdrawal ∧
    (registerThenWithdraw stateUnknownBuilderWithdrawal).toOption = some (#[U64.literal 1000000000], #[U64.literal 999999995]) := by
  refine ⟨fun h => ?_, by decide +kernel⟩
  have := h.1 withdrawalOfFive (by simp [stateUnknownBuilderWithdrawal, ProgressiveListOnSpine.ofArray])
  simp [stateUnknownBuilderWithdrawal, BalanceFlowWitnesses.balanceFlowBase, ProgressiveListOnSpine.empty] at this

/-! ## G3-04 -/

/-- Builder 0 exited at epoch 0 and swept (balance 0), with a pending withdrawal of 5. -/
def stateExitedSweptWithdrawal : MinimalGloasState := { BalanceFlowWitnesses.balanceFlowBase with
  builders := ProgressiveListOnSpine.ofArray #[Witnesses.builder 1 ⟨1⟩ U64.zero U64.zero U64.zero]
  builder_pending_withdrawals := ProgressiveListOnSpine.ofArray #[withdrawalOfFive] }

/-- **G3-04 control.** -/
theorem exitedHaveNoPending_control :
    ¬ ExitedHaveNoPending stateExitedSweptWithdrawal ∧
    (registerThenWithdraw stateExitedSweptWithdrawal).toOption = some (#[U64.literal 1000000000], #[U64.literal 999999995]) := by
  refine ⟨fun h => ?_, by decide +kernel⟩
  have := h 0 (Witnesses.builder 1 ⟨1⟩ U64.zero U64.zero U64.zero) rfl (by decide)
  revert this
  decide +kernel

/-! ## G3-06 -/

/-- One builder, sweep index 5. -/
def stateSweepIndexOutOfRange : MinimalGloasState := { BalanceFlowWitnesses.balanceFlowBase with
  builders := ProgressiveListOnSpine.ofArray #[Witnesses.builder 1 ⟨1⟩ (U64.literal 10) U64.zero FAR_FUTURE_EPOCH]
  next_withdrawal_builder_index := U64.literal 5 }

/-- **G3-06 control** (non-vacuity). -/
theorem nextBuilderIndexInRange_control :
    ¬ NextBuilderIndexInRange stateSweepIndexOutOfRange ∧
    (JauneConsensus.Gloas.getBuildersSweepWithdrawals stateSweepIndexOutOfRange U64.zero #[]).toOption = none := by
  refine ⟨fun h => ?_, by decide +kernel⟩
  have := h (by decide)
  revert this
  decide

/-! ## G3-07 -/

/-- `L`: builder 0's bid of 5 gwei at slot 0. -/
def latestBid : JauneConsensus.Gloas.ExecutionPayloadBid :=
  { BalanceFlowWitnesses.balanceFlowBase.latest_execution_payload_bid with
    fee_recipient := Witnesses.address ⟨7⟩, value := U64.literal 5, builder_index := U64.zero,
    slot := U64.zero }

/-- `L`'s entry (index 0, the previous epoch's first slot) with weight `10^9`, above the quorum
(`75 * 10^6` with no active validators). -/
def latestPayment : JauneConsensus.Gloas.BuilderPendingPayment :=
  { weight := U64.literal 1000000000, withdrawal := withdrawalOfFive, proposer_index := U64.zero }

/-- Slot 15 (the last slot of epoch 1), `L` at slot 0 (epoch 0), entry 0 weighed. -/
def stateLiveEntryAboveQuorum : MinimalGloasState := { BalanceFlowWitnesses.balanceFlowBase with
  slot := U64.literal 15
  builders := ProgressiveListOnSpine.ofArray #[Witnesses.builder 1 ⟨1⟩ (U64.literal 100) U64.zero FAR_FUTURE_EPOCH]
  latest_execution_payload_bid := latestBid
  builder_pending_payments := ⟨#[latestPayment] ++ Array.replicate 15 JauneConsensus.Gloas.BuilderPendingPayment.empty,
    by simp; rfl⟩ }

/-- **G3-07 control.** -/
theorem noLiveWeightOnLatestBid_control :
    ¬ NoLiveWeightOnLatestBid stateLiveEntryAboveQuorum ∧
    ((JauneConsensus.Gloas.processBuilderPendingPayments Config.minimal stateLiveEntryAboveQuorum).toOption.map
        (fun s1 => (directAppend s1).builder_pending_withdrawals.toArray.map (·.amount))) =
      some #[U64.literal 5, U64.literal 5] := by
  refine ⟨fun h => ?_, by decide +kernel⟩
  obtain ⟨E, hE, hw, _⟩ := h 0 (by decide +kernel)
  have : E = latestPayment := by
    have h0 : stateLiveEntryAboveQuorum.builder_pending_payments.toArray[0]? = some latestPayment := rfl
    rw [h0] at hE; exact (Option.some.inj hE).symm
  subst this
  exact absurd hw (by decide)

end JauneConsensus.Facts.Gloas.Invariant.Controls
