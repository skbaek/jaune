import JauneConsensus.Facts.Gloas.InvariantsCrossing
import JauneConsensus.Facts.Gloas.B5Witnesses
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

namespace JauneConsensus.Facts.Gloas.Inv.Controls

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas JauneConsensus.Facts.Gloas.Inv

/-- The minimal-preset Gloas state. -/
abbrev Sm := JauneConsensus.Gloas.BeaconState Preset.minimal

/-- BLS off, minimal configuration. -/
def ctxOff : Ctx := { cfg := Config.minimal, blsActive := false }

/-- A pending withdrawal of 5 gwei to builder index 0. -/
def w5 : JauneConsensus.Gloas.BuilderPendingWithdrawal :=
  { fee_recipient := Witnesses.addr ⟨7⟩, amount := U64.lit 5, builder_index := U64.zero }

/-- The new builder's deposit: a fresh pubkey with the builder prefix (BLS off). -/
def depK : JauneConsensus.Gloas.BuilderDepositRequest := Witnesses.dep 9 Witnesses.preB0 0xc0

/-- Register `depK`, then run the builder-withdrawals phase and apply it: the balances of the
registry after the registration and after the withdrawals. -/
def registerThenWithdraw (s : Sm) : M (Array U64 × Array U64) := do
  let s1 ← JauneConsensus.Gloas.processBuilderDepositRequest ctxOff s depK
  let (ws, _, _) ← JauneConsensus.Gloas.getBuilderWithdrawals s1 U64.zero #[]
  let s2 ← JauneConsensus.Gloas.applyWithdrawals s1 ws
  pure (s1.builders.toArray.map (·.balance), s2.builders.toArray.map (·.balance))

/-! ## G3-03 -/

/-- An empty registry with a pending withdrawal naming builder index 0. -/
def s03 : Sm := { B5Witnesses.b5Base with
  builder_pending_withdrawals := ProgressiveListS.ofArray #[w5] }

/-- **G3-03 control.** -/
theorem g303_control :
    ¬ PendingRefsInRange s03 ∧
    (registerThenWithdraw s03).toOption = some (#[U64.lit 1000000000], #[U64.lit 999999995]) := by
  refine ⟨fun h => ?_, by decide +kernel⟩
  have := h.1 w5 (by simp [s03, ProgressiveListS.ofArray])
  simp [s03, B5Witnesses.b5Base, ProgressiveListS.empty] at this

/-! ## G3-04 -/

/-- Builder 0 exited at epoch 0 and swept (balance 0), with a pending withdrawal of 5. -/
def s04 : Sm := { B5Witnesses.b5Base with
  builders := ProgressiveListS.ofArray #[Witnesses.bld 1 ⟨1⟩ U64.zero U64.zero U64.zero]
  builder_pending_withdrawals := ProgressiveListS.ofArray #[w5] }

/-- **G3-04 control.** -/
theorem g304_control :
    ¬ ExitedHaveNoPending s04 ∧
    (registerThenWithdraw s04).toOption = some (#[U64.lit 1000000000], #[U64.lit 999999995]) := by
  refine ⟨fun h => ?_, by decide +kernel⟩
  have := h 0 (Witnesses.bld 1 ⟨1⟩ U64.zero U64.zero U64.zero) rfl (by decide)
  revert this
  decide +kernel

/-! ## G3-06 -/

/-- One builder, sweep index 5. -/
def s06 : Sm := { B5Witnesses.b5Base with
  builders := ProgressiveListS.ofArray #[Witnesses.bld 1 ⟨1⟩ (U64.lit 10) U64.zero FAR_FUTURE_EPOCH]
  next_withdrawal_builder_index := U64.lit 5 }

/-- **G3-06 control** (non-vacuity). -/
theorem g306_control :
    ¬ NextBuilderIndexInRange s06 ∧
    (JauneConsensus.Gloas.getBuildersSweepWithdrawals s06 U64.zero #[]).toOption = none := by
  refine ⟨fun h => ?_, by decide +kernel⟩
  have := h (by decide)
  revert this
  decide

/-! ## G3-07 -/

/-- `L`: builder 0's bid of 5 gwei at slot 0. -/
def bid07 : JauneConsensus.Gloas.ExecutionPayloadBid :=
  { B5Witnesses.b5Base.latest_execution_payload_bid with
    fee_recipient := Witnesses.addr ⟨7⟩, value := U64.lit 5, builder_index := U64.zero,
    slot := U64.zero }

/-- `L`'s entry (index 0, the previous epoch's first slot) with weight `10^9`, above the quorum
(`75 * 10^6` with no active validators). -/
def pay07 : JauneConsensus.Gloas.BuilderPendingPayment :=
  { weight := U64.lit 1000000000, withdrawal := w5, proposer_index := U64.zero }

/-- Slot 15 (the last slot of epoch 1), `L` at slot 0 (epoch 0), entry 0 weighed. -/
def s07 : Sm := { B5Witnesses.b5Base with
  slot := U64.lit 15
  builders := ProgressiveListS.ofArray #[Witnesses.bld 1 ⟨1⟩ (U64.lit 100) U64.zero FAR_FUTURE_EPOCH]
  latest_execution_payload_bid := bid07
  builder_pending_payments := ⟨#[pay07] ++ Array.replicate 15 JauneConsensus.Gloas.BuilderPendingPayment.empty,
    by simp; rfl⟩ }

/-- **G3-07 control.** -/
theorem g307_control :
    ¬ NoLiveWeightOnLatestBid s07 ∧
    ((JauneConsensus.Gloas.processBuilderPendingPayments Config.minimal s07).toOption.map
        (fun s1 => (directAppend s1).builder_pending_withdrawals.toArray.map (·.amount))) =
      some #[U64.lit 5, U64.lit 5] := by
  refine ⟨fun h => ?_, by decide +kernel⟩
  obtain ⟨E, hE, hw, _⟩ := h 0 (by decide +kernel)
  have : E = pay07 := by
    have h0 : s07.builder_pending_payments.toArray[0]? = some pay07 := rfl
    rw [h0] at hE; exact (Option.some.inj hE).symm
  subst this
  exact absurd hw (by decide)

end JauneConsensus.Facts.Gloas.Inv.Controls
