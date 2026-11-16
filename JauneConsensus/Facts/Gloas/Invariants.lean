import JauneConsensus.Facts.Gloas.BuilderFrames
import JauneConsensus.Facts.Gloas.WithdrawalsBalanceFlow
import JauneConsensus.GloasTransition
import JauneConsensus.Facts.AnchorInvariantComposite

/-!
# The state-level EIP-8282 Gloas invariants G3-01 to G3-08 (goal `eip8282-gloas-cross-layer-v1`, G3a)

The frozen list is Plans `evidence/eip8282-gloas-cross-layer-v1/recon/design.md` §5 (rev 3.1).
Each invariant is a `Prop` on `Gloas.BeaconState P`, G3-02 a relation between a pre and a post
state. Notation as in §5:

* `pend s i` is `get_pending_balance_to_withdraw_for_builder(s, i)` (CL:1168-1178) read in `ℕ`:
  the sum of the amounts of the `builder_pending_withdrawals` and `builder_pending_payments`
  entries with builder index `i` (the spec's `uint64` sum raises on overflow; under G3-05 it
  never does, since the sum is at most a balance);
* `L` is `latest_execution_payload_bid`; `bidIndex s` is `L`'s window index: `SPE + L.slot % SPE`
  when `L.slot` is in the current epoch, `L.slot % SPE` when it is in the previous one, none
  otherwise (`L` evicted from the two-epoch window);
* `expo s i` is G3-05's exposure term: `L.value` if `L.builder_index = i`, `L.value > 0` and `L`'s
  payment entry is not live (`BidLive`: the entry at `L`'s window index carries `L`'s own
  withdrawal), else `0`.

This module also proves `InvFrame`, the frame of the fields the invariants read, for the
validator-side steps (the generator of `Step.lean` at a new relation), so that every such step
preserves every invariant at once (`InvFrame.pres_*`).
-/

namespace JauneConsensus.Facts.Gloas.Invariant

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

/-- The Gloas beacon state. -/
abbrev GloasState (P : Preset) := JauneConsensus.Gloas.BeaconState P

/-! ## Vocabulary -/

/-- One entry's contribution to `pend(·, i)`. -/
def withdrawalAmount (i : Nat) (w : JauneConsensus.Gloas.BuilderPendingWithdrawal) : Nat :=
  if w.builder_index.toNat = i then w.amount.toNat else 0

/-- The withdrawals' part of `pend`. -/
def pendingWithdrawalBalance (l : List JauneConsensus.Gloas.BuilderPendingWithdrawal) (i : Nat) : Nat :=
  (l.map (withdrawalAmount i)).sum

/-- The payments' part of `pend`. -/
def pendingPaymentBalance (l : List JauneConsensus.Gloas.BuilderPendingPayment) (i : Nat) : Nat :=
  (l.map (fun p => withdrawalAmount i p.withdrawal)).sum

/-- `pend(s, i)`: `get_pending_balance_to_withdraw_for_builder(s, i)` in `ℕ`. -/
def pendingBalance (s : GloasState P) (i : Nat) : Nat :=
  pendingWithdrawalBalance s.builder_pending_withdrawals.toArray.toList i +
    pendingPaymentBalance s.builder_pending_payments.toArray.toList i

/-- The current epoch, `state.slot // SLOTS_PER_EPOCH`. -/
def currentEpoch (s : GloasState P) : Nat := s.slot.toNat / P.SLOTS_PER_EPOCH

/-- `L`'s index in `builder_pending_payments`, when `L.slot` is in the current or the previous
epoch. -/
def bidIndex (s : GloasState P) : Option Nat :=
  let L := s.latest_execution_payload_bid
  if L.slot.toNat / P.SLOTS_PER_EPOCH = currentEpoch s then
    some (P.SLOTS_PER_EPOCH + L.slot.toNat % P.SLOTS_PER_EPOCH)
  else if L.slot.toNat / P.SLOTS_PER_EPOCH + 1 = currentEpoch s then
    some (L.slot.toNat % P.SLOTS_PER_EPOCH)
  else none

/-- The withdrawal a bid records (CL:2201-2212). -/
def bidWithdrawal (L : JauneConsensus.Gloas.ExecutionPayloadBid) :
    JauneConsensus.Gloas.BuilderPendingWithdrawal :=
  { fee_recipient := L.fee_recipient, amount := L.value, builder_index := L.builder_index }

/-- `L`'s payment entry is live: the entry at `L`'s window index carries `L`'s own withdrawal. -/
def BidLive (s : GloasState P) : Prop :=
  ∃ k E, bidIndex s = some k ∧ s.builder_pending_payments.toArray[k]? = some E ∧
    E.withdrawal = bidWithdrawal s.latest_execution_payload_bid

/-- `L` exposes builder `i`: `L.builder_index = i`, `L.value > 0`, and `L`'s entry is not live. -/
def Exposed (s : GloasState P) (i : Nat) : Prop :=
  s.latest_execution_payload_bid.builder_index.toNat = i ∧
    0 < s.latest_execution_payload_bid.value.toNat ∧ ¬ BidLive s

open Classical in
/-- G3-05's exposure term `expo(s, i)`. -/
noncomputable def exposure (s : GloasState P) (i : Nat) : Nat :=
  if Exposed s i then s.latest_execution_payload_bid.value.toNat else 0

/-- `builder.withdrawable_epoch ≤ epoch ∧ builder.balance = 0` (CL:2292). -/
def Reusable (b : JauneConsensus.Gloas.Builder) (epoch : Nat) : Prop :=
  b.withdrawable_epoch.toNat ≤ epoch ∧ b.balance = U64.zero

/-- A builder's identity: pubkey, version and execution address. -/
def SameIdentity (b b' : JauneConsensus.Gloas.Builder) : Prop :=
  b'.pubkey = b.pubkey ∧ b'.version = b.version ∧ b'.execution_address = b.execution_address

/-! ## The invariants (design.md §5, rev 3.1) -/

/-- **G3-01 BuilderPubkeysUnique.** `∀ i < j < len(builders), builders[i].pubkey ≠
builders[j].pubkey`. -/
def BuilderPubkeysUnique (s : GloasState P) : Prop :=
  ∀ (i j : Nat) (bi bj : JauneConsensus.Gloas.Builder), i < j → s.builders.toArray[i]? = some bi →
    s.builders.toArray[j]? = some bj → bi.pubkey ≠ bj.pubkey

/-- **G3-02 BuilderIdentityStable** (`BPres s s'`). `len` never shrinks, and every builder of `s`
keeps its pubkey, version and execution address in `s'`, unless it was reusable
(`withdrawable_epoch ≤ epoch ∧ balance = 0`, at the epoch of `s'`) and was overwritten by a fresh
record. -/
def BuilderIdentityStable (s s' : GloasState P) : Prop :=
  s.builders.toArray.size ≤ s'.builders.toArray.size ∧
    ∀ (i : Nat) (b : JauneConsensus.Gloas.Builder), s.builders.toArray[i]? = some b →
      ∃ b', s'.builders.toArray[i]? = some b' ∧
        (SameIdentity b b' ∨
          (Reusable b (currentEpoch s') ∧ b'.pubkey ≠ b.pubkey ∧
            b'.version = JauneConsensus.Gloas.PAYLOAD_BUILDER_VERSION))

/-- **G3-03 PendingRefsInRange.** Every `builder_pending_withdrawals[k].builder_index` and every
non-empty `builder_pending_payments[j].withdrawal.builder_index` is `< len(builders)`. -/
def PendingReferencesInRange (s : GloasState P) : Prop :=
  (∀ w ∈ s.builder_pending_withdrawals.toArray.toList,
      w.builder_index.toNat < s.builders.toArray.size) ∧
    ∀ p ∈ s.builder_pending_payments.toArray.toList,
      p ≠ JauneConsensus.Gloas.BuilderPendingPayment.empty →
        p.withdrawal.builder_index.toNat < s.builders.toArray.size

/-- **G3-04 ExitedHaveNoPending.** `∀ i < len(builders), builders[i].withdrawable_epoch ≠
FAR_FUTURE_EPOCH → pend(s, i) = 0`. -/
def ExitedHaveNoPending (s : GloasState P) : Prop :=
  ∀ (i : Nat) (b : JauneConsensus.Gloas.Builder), s.builders.toArray[i]? = some b →
    b.withdrawable_epoch ≠ FAR_FUTURE_EPOCH → pendingBalance s i = 0

/-- **G3-05 PendingCovered** (carried form, master decision eip8282-g3-05-carried-form): for
every builder `i`, `pend(s, i) + expo(s, i) ≤ balance(i)`. -/
def PendingCovered (s : GloasState P) : Prop :=
  ∀ (i : Nat) (b : JauneConsensus.Gloas.Builder), s.builders.toArray[i]? = some b →
    pendingBalance s i + exposure s i ≤ b.balance.toNat

/-- **G3-06 NextBuilderIndexInRange.** `len(builders) > 0 → next_withdrawal_builder_index <
len(builders)`. -/
def NextBuilderIndexInRange (s : GloasState P) : Prop :=
  0 < s.builders.toArray.size → s.next_withdrawal_builder_index.toNat < s.builders.toArray.size

/-- **G3-07 NoLiveWeightOnLatestBid** (design.md: LatestBidPaymentSlot, rev-3 form). With `L`
inside the two-epoch window, the entry `E` at `L`'s window index has `E.weight = 0` and is either
`L`'s own (`L.value > 0` and `E.withdrawal = ⟨L.fee_recipient, L.value, L.builder_index⟩`, any
proposer) or `BuilderPendingPayment.empty()`. -/
def NoLiveWeightOnLatestBid (s : GloasState P) : Prop :=
  ∀ k, bidIndex s = some k → ∃ E, s.builder_pending_payments.toArray[k]? = some E ∧
    E.weight = U64.zero ∧
    ((U64.zero < s.latest_execution_payload_bid.value ∧
        E.withdrawal = bidWithdrawal s.latest_execution_payload_bid) ∨
      E = JauneConsensus.Gloas.BuilderPendingPayment.empty)

/-- **G3-08 LatestBidCoherence.** `L.slot = latest_block_header.slot`;
`L.builder_index = BUILDER_INDEX_SELF_BUILD ∨ < len(builders)`; and `latest_block_hash` is
`L.parent_block_hash` (after a Gloas block) or `L.block_hash` (`upgrade_to_gloas`'s state). -/
def LatestBidCoherence (s : GloasState P) : Prop :=
  s.latest_execution_payload_bid.slot = s.latest_block_header.slot ∧
    (s.latest_execution_payload_bid.builder_index = JauneConsensus.Gloas.BUILDER_INDEX_SELF_BUILD ∨
      s.latest_execution_payload_bid.builder_index.toNat < s.builders.toArray.size) ∧
    (s.latest_block_hash = s.latest_execution_payload_bid.parent_block_hash ∨
      s.latest_block_hash = s.latest_execution_payload_bid.block_hash)

/-! ## Auxiliary invariants (not on the frozen list; used by the proofs and stated here) -/

/-- The builder of a paying `L` is not exiting (it was active at its bid, and no exit can be
initiated between a block and the next block's bid while `L` is its latest bid). Used by G3-04
(the direct append charges `L`'s builder) and G3-03 (`L`'s index is in range). -/
def LatestBidBuilderActive (s : GloasState P) : Prop :=
  U64.zero < s.latest_execution_payload_bid.value →
    ∃ b, s.builders.toArray[s.latest_execution_payload_bid.builder_index.toNat]? = some b ∧
      b.withdrawable_epoch = FAR_FUTURE_EPOCH

/-- The payments of the current epoch's later slots are empty (no bid has been made for them),
and so is the current slot's while the latest block is older than the slot (no block has been
processed at this slot). Used by G3-07 for a bid with value `0`, which writes no entry. -/
def FutureEmpty (s : GloasState P) : Prop :=
  (∀ j, j < P.SLOTS_PER_EPOCH → s.slot.toNat % P.SLOTS_PER_EPOCH < j →
    s.builder_pending_payments.toArray[P.SLOTS_PER_EPOCH + j]? =
      some JauneConsensus.Gloas.BuilderPendingPayment.empty) ∧
  (s.latest_block_header.slot.toNat < s.slot.toNat →
    s.builder_pending_payments.toArray[P.SLOTS_PER_EPOCH + s.slot.toNat % P.SLOTS_PER_EPOCH]? =
      some JauneConsensus.Gloas.BuilderPendingPayment.empty)

/-! ## The frame of the fields the invariants read -/

/-- Every field an invariant reads is unchanged. -/
def InvariantFrame (s s' : GloasState P) : Prop :=
  s'.builders = s.builders ∧ s'.builder_pending_payments = s.builder_pending_payments ∧
    s'.builder_pending_withdrawals = s.builder_pending_withdrawals ∧
    s'.latest_execution_payload_bid = s.latest_execution_payload_bid ∧
    s'.latest_block_hash = s.latest_block_hash ∧
    s'.latest_block_header.slot = s.latest_block_header.slot ∧ s'.slot = s.slot ∧
    s'.next_withdrawal_builder_index = s.next_withdrawal_builder_index

/-- `InvFrame` as a step relation. -/
def invariantFrame : StepRelation (GloasState P) where
  relation := InvariantFrame
  refl _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.1.trans h₁.2.2.2.2.1,
    h₂.2.2.2.2.2.1.trans h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.2.1.trans h₁.2.2.2.2.2.2.1,
    h₂.2.2.2.2.2.2.2.trans h₁.2.2.2.2.2.2.2⟩

theorem InvariantFrame.symm {s s' : GloasState P} (h : InvariantFrame s s') : InvariantFrame s' s :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm,
    h.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.symm⟩


/-! ## Join points

`gvcg` zeta-reduces `do` join points (`have __do_jp := k; e`), which copies the continuation into
each branch of every `if` before it: exponential in the number of conditionals (it times out on
`weigh_justification_and_finalization`). `jvcg` keeps a join point abstract instead: it proves
the continuation `k` once for an arbitrary state, then uses that fact at each call. -/

/-- A join point of arity 2 (`Unit`, state) relates every call's state to its result. -/
def JoinPointOk2 {σ α : Type} (rel : StepRelation σ) (g : α → σ) (jp : Unit → σ → Fallible α) : Prop :=
  ∀ u st, Ok (jp u st) (fun r => rel.relation st (g r))

/-- A join point of arity 3 (`Unit`, state, one more mutable variable). -/
def JoinPointOk3 {σ α γ : Type} (rel : StepRelation σ) (g : α → σ) (jp : Unit → σ → γ → Fallible α) : Prop :=
  ∀ u st c, Ok (jp u st c) (fun r => rel.relation st (g r))

theorem JoinPointOk2.call {σ α : Type} {rel : StepRelation σ} {g : α → σ} {jp : Unit → σ → Fallible α}
    (h : JoinPointOk2 rel g jp) (u : Unit) (st : σ) : Ok (jp u st) (fun r => rel.relation st (g r)) := h u st

theorem JoinPointOk3.call {σ α γ : Type} {rel : StepRelation σ} {g : α → σ} {jp : Unit → σ → γ → Fallible α}
    (h : JoinPointOk3 rel g jp) (u : Unit) (st : σ) (c : γ) : Ok (jp u st c) (fun r => rel.relation st (g r)) :=
  h u st c

theorem ok_joinPoint2 {σ α : Type} (rel : StepRelation σ) {s : σ} {g : α → σ} {k : Unit → σ → Fallible α}
    {e : (Unit → σ → Fallible α) → Fallible α} (hk : JoinPointOk2 rel g k)
    (he : ∀ jp, JoinPointOk2 rel g jp → Ok (e jp) (fun r => rel.relation s (g r))) :
    Ok (e k) (fun r => rel.relation s (g r)) := he k hk

theorem ok_joinPoint3 {σ α γ : Type} (rel : StepRelation σ) {s : σ} {g : α → σ} {k : Unit → σ → γ → Fallible α}
    {e : (Unit → σ → γ → Fallible α) → Fallible α} (hk : JoinPointOk3 rel g k)
    (he : ∀ jp, JoinPointOk3 rel g jp → Ok (e jp) (fun r => rel.relation s (g r))) :
    Ok (e k) (fun r => rel.relation s (g r)) := he k hk

open Lean Elab Tactic Meta in
/-- Abstract the join point at the head of `Ok (have __do_jp := k; e) Q`. -/
elab "jp_abs" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Ok 3 do throwError "jp_abs: goal is not `Ok _ _`"
  let c := (t.getArg! 1).headBeta
  let .letE n ty v b _ := c | throwError "jp_abs: no `have` at the head"
  unless n.eraseMacroScopes == `__do_jp do throwError "jp_abs: not a join point"
  let eS ← Term.exprToSyntax (Expr.lam n ty b .default)
  let vS ← Term.exprToSyntax v
  let α ← Term.exprToSyntax (t.getArg! 0)
  forallTelescope ty fun ys _ => do
    let tys ← ys.mapM fun y => do Term.exprToSyntax (← inferType y)
    if h : tys.size = 3 then
      let σ := tys[1]; let γ := tys[2]
      evalTactic (← `(tactic|
        (refine ok_joinPoint3 (σ := $σ) (γ := $γ) (α := $α) _ (k := $vS) (e := $eS) ?_ ?_
         rotate_left; intro _ _; rotate_left; unfold JoinPointOk3; intro _ _ _)))
    else if h : tys.size = 2 then
      let σ := tys[1]
      evalTactic (← `(tactic|
        (refine ok_joinPoint2 (σ := $σ) (α := $α) _ (k := $vS) (e := $eS) ?_ ?_
         rotate_left; intro _ _; rotate_left; unfold JoinPointOk2; intro _ _)))
    else throwError "jp_abs: arity {tys.size}"

/-- One join-point-aware generator step. -/
syntax "jstep" : tactic

macro_rules | `(tactic| jstep) => `(tactic| first
  | jp_abs
  | (refine StepRelation.ok_rebase _ ?_ (JoinPointOk3.call ?_ _ _ _) <;> first | assumption | gstep_close)
  | (refine StepRelation.ok_rebase _ ?_ (JoinPointOk2.call ?_ _ _) <;> first | assumption | gstep_close)
  | ok_head
  | with_reducible exact ok_throw
  | with_reducible exact ok_throw_bind
  | ((with_reducible apply ok_pure); gstep_close)
  | (with_reducible apply ok_bind; intro _ hx
     first | gstep_rebase hx | skip)
  | (with_reducible apply ok_ite <;> intro _)
  | (with_reducible apply ok_dite <;> intro _)
  | (set_option simprocs false in dsimp -zeta only)
  | (rename_i x _; is_small_inductive x; cases x; all_goals (set_option simprocs false in dsimp -zeta only))
  | split)

/-- The join-point-aware generator: `jstep` to a fixed point. -/
macro "jvcg" : tactic => `(tactic| repeat' jstep)

section Generator

local macro_rules
  | `(tactic| gstep_close) =>
    `(tactic| exact (show InvariantFrame _ _ from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))

theorem increaseBalance_invariantFrame (s : GloasState P) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.increaseBalance s i d) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.increaseBalance; gvcg

theorem decreaseBalance_invariantFrame (s : GloasState P) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.decreaseBalance s i d) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.decreaseBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (increaseBalance_invariantFrame _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (decreaseBalance_invariantFrame _ _ _) $h; exact hh))

theorem computeExitEpochAndUpdateChurn_invariantFrame (cfg : Config) (s : GloasState P) (b : Gwei) :
    Ok (JauneConsensus.Gloas.computeExitEpochAndUpdateChurn cfg s b)
      (fun p => invariantFrame.relation s p.1) := by
  unfold JauneConsensus.Gloas.computeExitEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (computeExitEpochAndUpdateChurn_invariantFrame _ _ _) $h; exact hh))

theorem initiateValidatorExit_invariantFrame (cfg : Config) (s : GloasState P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.initiateValidatorExit cfg s i) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.initiateValidatorExit; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (initiateValidatorExit_invariantFrame _ _ _) $h; exact hh))

theorem addValidatorToRegistry_invariantFrame (s : GloasState P) (pk : BLSPubkey) (wc : Bytes32)
    (amount : Gwei) :
    Ok (JauneConsensus.Gloas.addValidatorToRegistry s pk wc amount) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.addValidatorToRegistry; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (addValidatorToRegistry_invariantFrame _ _ _ _) $h; exact hh))

theorem applyPendingDeposit_invariantFrame (ctx : Context) (s : GloasState P) (d : PendingDeposit) :
    Ok (JauneConsensus.Gloas.applyPendingDeposit ctx s d) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.applyPendingDeposit; gvcg
  · exact addValidatorToRegistry_invariantFrame _ _ _ _
  · exact increaseBalance_invariantFrame _ _ _

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (applyPendingDeposit_invariantFrame _ _ _) $h; exact hh))

theorem processInactivityUpdates_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processInactivityUpdates cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processInactivityUpdates; gvcg

theorem processRewardsAndPenalties_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processRewardsAndPenalties cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processRewardsAndPenalties; gvcg

theorem processRegistryUpdates_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processRegistryUpdates cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processRegistryUpdates; gvcg

theorem processSlashings_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processSlashings cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processSlashings; gvcg

theorem processEth1DataReset_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processEth1DataReset cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processEth1DataReset; gvcg

section PendingDeposits

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRelation.forIn_array_relation _ (fun x => x.2.2.2.2) ?_ _ _ $h; intro _ _; gvcg))

theorem processPendingDeposits_invariantFrame (ctx : Context) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processPendingDeposits ctx s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processPendingDeposits; gvcg

end PendingDeposits

theorem processPendingConsolidations_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processPendingConsolidations cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processPendingConsolidations; gvcg

theorem processEffectiveBalanceUpdates_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processEffectiveBalanceUpdates cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processEffectiveBalanceUpdates; gvcg

theorem processSlashingsReset_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processSlashingsReset cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processSlashingsReset; gvcg

theorem processRandaoMixesReset_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processRandaoMixesReset cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processRandaoMixesReset; gvcg

theorem processHistoricalSummariesUpdate_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processHistoricalSummariesUpdate cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processHistoricalSummariesUpdate; gvcg

theorem processParticipationFlagUpdates_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processParticipationFlagUpdates cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processParticipationFlagUpdates; gvcg

theorem processSyncCommitteeUpdates_invariantFrame (ctx : Context) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processSyncCommitteeUpdates ctx s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processSyncCommitteeUpdates; gvcg

theorem processProposerLookahead_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processProposerLookahead cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processProposerLookahead; gvcg

theorem processPtcWindow_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processPtcWindow cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processPtcWindow; gvcg

theorem processRandao_invariantFrame (ctx : Context) (s : GloasState P)
    (body : JauneConsensus.Gloas.BeaconBlockBody P) :
    Ok (JauneConsensus.Gloas.processRandao ctx s body) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processRandao; gvcg

theorem processEth1Data_invariantFrame (s : GloasState P) (body : JauneConsensus.Gloas.BeaconBlockBody P) :
    Ok (JauneConsensus.Gloas.processEth1Data s body) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processEth1Data; gvcg

set_option maxHeartbeats 2000000 in
theorem processSyncAggregate_invariantFrame (ctx : Context) (s : GloasState P) (sa : SyncAggregate P) :
    Ok (JauneConsensus.Gloas.processSyncAggregate ctx s sa) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processSyncAggregate; gvcg

theorem weighJustificationAndFinalization_invariantFrame (s : GloasState P) (t p c : Gwei) :
    Ok (JauneConsensus.Gloas.weighJustificationAndFinalization s t p c) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.weighJustificationAndFinalization; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRelation.of_ok (weighJustificationAndFinalization_invariantFrame _ _ _ _) $h; exact hh))

theorem processJustificationAndFinalization_invariantFrame (cfg : Config) (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processJustificationAndFinalization cfg s) (invariantFrame.relation s) := by
  unfold JauneConsensus.Gloas.processJustificationAndFinalization; gvcg
  all_goals exact weighJustificationAndFinalization_invariantFrame _ _ _ _

open Jaune in
/-- `process_slot` with its two hashes abstracted (`processSlot_eq`): the proof then never
meets `hash_tree_root` of a state. -/
def processSlotAbstractedHashes (h₁ : GloasState P → Root) (h₂ : BeaconBlockHeader → Root) (state : GloasState P) :
    Fallible (GloasState P) := do
  let slotsPerHistoricalRoot ← u64 P.SLOTS_PER_HISTORICAL_ROOT "SLOTS_PER_HISTORICAL_ROOT"
  let i := (← state.slot.mod? slotsPerHistoricalRoot
    "process_slot: slot % SLOTS_PER_HISTORICAL_ROOT").toNat
  let previousStateRoot : Root := h₁ state
  let state := { state with
    state_roots := ← state.state_roots.set i previousStateRoot "process_slot: state_roots" }
  let state :=
    if Bytes32.beq state.latest_block_header.state_root (0 : Jaune.U256) then
      { state with latest_block_header :=
          { state.latest_block_header with state_root := previousStateRoot } }
    else state
  let previousBlockRoot : Root := h₂ state.latest_block_header
  let state := { state with
    block_roots := ← state.block_roots.set i previousBlockRoot "process_slot: block_roots" }
  let nextSlotIndex := (← (← state.slot.add? U64.one "process_slot: state.slot + 1").mod?
    slotsPerHistoricalRoot "process_slot: (state.slot + 1) % SLOTS_PER_HISTORICAL_ROOT").toNat
  pure { state with
    execution_payload_availability := ← state.execution_payload_availability.set nextSlotIndex
      false "process_slot: execution_payload_availability" }

theorem processSlot_eq (s : GloasState P) :
    JauneConsensus.Gloas.processSlot s = processSlotAbstractedHashes Ssz.hashTreeRoot Ssz.hashTreeRoot s := rfl

theorem processSlotAbstractedHashes_invariantFrame (h₁ : GloasState P → Root) (h₂ : BeaconBlockHeader → Root) (s : GloasState P) :
    Ok (processSlotAbstractedHashes h₁ h₂ s) (invariantFrame.relation s) := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> split <;> rfl

theorem processSlot_invariantFrame (s : GloasState P) :
    Ok (JauneConsensus.Gloas.processSlot s) (invariantFrame.relation s) := by
  rw [processSlot_eq]; exact processSlotAbstractedHashes_invariantFrame _ _ s

end Generator

end JauneConsensus.Facts.Gloas.Invariant
