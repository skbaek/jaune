import JauneConsensus.Facts.Gloas.WithdrawalsB5

/-!
# B5 function-level witnesses on closed minimal states (goal `eip8282-gloas-cross-layer-v1`, BF1)

statements.md §0.3 and B5's controls (3) and (4), all **F**: each payment fate is one function on a
closed minimal-preset state, and the G3-05 saturation witness is `apply_withdrawals` on a closed
state. No witness evaluates `hash_tree_root` of a state; each is checked by the kernel (`decide`
on an equation of `M` values, or `rfl`).

The base state `b5Base` has every field at its zero value (vectors filled to their preset
lengths); each witness overrides only the fields its function reads.
-/

namespace JauneConsensus.Facts.Gloas.B5Witnesses

open JauneConsensus JauneConsensus.Facts JauneConsensus.Gloas

/-- The minimal preset. -/
abbrev Pm : Preset := Preset.minimal

private def vrep {α : Type} (n : Nat) (x : α) : SszVector α n := ⟨Array.replicate n x, by simp⟩
private def lnil {α : Type} {n : Nat} : SszList α n := ⟨#[], by simp⟩
private def bvz (n : Nat) : Bitvector n := ⟨Array.replicate n false, by simp⟩

private def z32 : Root := 0
private def zAdr : ExecutionAddress := (0, 0)

private def zCheckpoint : Checkpoint := { epoch := U64.zero, root := z32 }

private def zHeader : BeaconBlockHeader :=
  { slot := U64.zero, proposer_index := U64.zero, parent_root := z32, state_root := z32,
    body_root := z32 }

private def zPubkey : BLSPubkey := vrep 48 0

private def zBid : ExecutionPayloadBid :=
  { parent_block_hash := z32, parent_block_root := z32, block_hash := z32, prev_randao := z32,
    fee_recipient := zAdr, gas_limit := U64.zero, builder_index := U64.zero, slot := U64.zero,
    value := U64.zero, execution_payment := U64.zero, blob_kzg_commitments := ProgressiveListS.empty,
    execution_requests_root := z32 }

/-- The empty `BuilderPendingPayment` value. -/
private def zPayment : BuilderPendingPayment := BuilderPendingPayment.empty

/-- Every field at its zero value. -/
def b5Base : Gloas.BeaconState Pm where
  genesis_time := U64.zero
  genesis_validators_root := z32
  slot := U64.zero
  fork := { previous_version := vrep 4 0, current_version := vrep 4 0, epoch := U64.zero }
  latest_block_header := zHeader
  block_roots := vrep _ z32
  state_roots := vrep _ z32
  historical_roots := lnil
  eth1_data := { deposit_root := z32, deposit_count := U64.zero, block_hash := z32 }
  eth1_data_votes := lnil
  eth1_deposit_index := U64.zero
  validators := ProgressiveListS.empty
  balances := ProgressiveListS.empty
  randao_mixes := vrep _ z32
  slashings := vrep _ U64.zero
  previous_epoch_participation := ProgressiveListS.empty
  current_epoch_participation := ProgressiveListS.empty
  justification_bits := bvz _
  previous_justified_checkpoint := zCheckpoint
  current_justified_checkpoint := zCheckpoint
  finalized_checkpoint := zCheckpoint
  inactivity_scores := ProgressiveListS.empty
  current_sync_committee := { pubkeys := vrep _ zPubkey, aggregate_pubkey := zPubkey }
  next_sync_committee := { pubkeys := vrep _ zPubkey, aggregate_pubkey := zPubkey }
  latest_block_hash := z32
  next_withdrawal_index := U64.zero
  next_withdrawal_validator_index := U64.zero
  historical_summaries := lnil
  deposit_requests_start_index := U64.zero
  deposit_balance_to_consume := U64.zero
  exit_balance_to_consume := U64.zero
  earliest_exit_epoch := U64.zero
  consolidation_balance_to_consume := U64.zero
  earliest_consolidation_epoch := U64.zero
  pending_deposits := ProgressiveListS.empty
  pending_partial_withdrawals := ProgressiveListS.empty
  pending_consolidations := ProgressiveListS.empty
  proposer_lookahead := vrep _ U64.zero
  builders := ProgressiveListS.empty
  next_withdrawal_builder_index := U64.zero
  execution_payload_availability := bvz _
  builder_pending_payments := vrep _ zPayment
  builder_pending_withdrawals := ProgressiveListS.empty
  latest_execution_payload_bid := zBid
  payload_expected_withdrawals := ProgressiveListS.empty
  ptc_window := vrep _ (vrep _ U64.zero)

/-! ## G3-05 saturation witness (control (4)) -/

/-- A builder with balance 10. -/
def satBuilder : Builder :=
  { pubkey := zPubkey, version := PAYLOAD_BUILDER_VERSION, execution_address := zAdr, balance := U64.lit 10,
    deposit_epoch := U64.zero, withdrawable_epoch := U64.zero }

/-- A withdrawal of 16 routed to builder 0 (`validator_index = 0 | 2^40`). -/
def satWithdrawal : Withdrawal :=
  { index := U64.zero, validator_index := U64.lit (2 ^ 40), address := zAdr, amount := U64.lit 16 }

def satState : Gloas.BeaconState Pm := { b5Base with builders := ProgressiveListS.ofArray #[satBuilder] }

/-- **G3-05 saturation witness.** Pending 16 against balance 10: `apply_withdrawals` saturates
the builder's balance at 0, so the B5(i) equation `balance' + routed = balance` fails
(`0 + 16 ≠ 10`) when G3-05's hypothesis (`routed ≤ balance`) fails. -/
theorem saturation_witness :
    (Gloas.applyWithdrawals satState #[satWithdrawal]).toOption.map
        (fun s => s.builders.toArray.map (·.balance)) = some #[U64.zero] ∧
    routedSum U64.zero [satWithdrawal] = 16 ∧ satBuilder.balance.toNat = 10 := by
  refine ⟨by decide +kernel, by decide, rfl⟩

/-! ## Payment fates (control (3)), each on one function -/

/-- The withdrawal a quorum payment carries: 5 gwei to builder 0. -/
def wQ : BuilderPendingWithdrawal := { fee_recipient := zAdr, amount := U64.lit 5, builder_index := U64.zero }
/-- The withdrawal a sub-quorum payment carries: 7 gwei to builder 1. -/
def wS : BuilderPendingWithdrawal := { fee_recipient := zAdr, amount := U64.lit 7, builder_index := U64.one }

/-- `payments[0]` has weight `10^9` (above the quorum), `payments[1]` weight 1 (below it). -/
def rotState : Gloas.BeaconState Pm :=
  { b5Base with builder_pending_payments :=
      ⟨(#[{ weight := U64.lit 1000000000, withdrawal := wQ, proposer_index := U64.zero },
          { weight := U64.one, withdrawal := wS, proposer_index := U64.zero }] : Array _) ++
        Array.replicate 14 zPayment, by simp; rfl⟩ }

/-- **quorum** and **droppedSubQuorum** (CL:1724-1731). With no active validator the total
active balance is one increment, so the quorum is `10^9 / 8 * 6 / 10 = 75 000 000`. At the
epoch rotation the live entry with weight `≥` quorum is appended to
`builder_pending_withdrawals` (quorum); the live entry with weight below it is not appended and
leaves `builder_pending_payments` (droppedSubQuorum): every payment is empty afterwards. -/
theorem quorum_and_dropped_witness :
    (Gloas.getBuilderPaymentQuorumThreshold rotState).toOption = some (U64.lit 75000000) ∧
    (Gloas.processBuilderPendingPayments Config.minimal rotState).toOption.map
        (fun s => (s.builder_pending_withdrawals.toArray,
          s.builder_pending_payments.toArray.all (· == zPayment))) =
      some (#[wQ], true) := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- The parent block's bid: value 5, builder 0. -/
def parentBid : ExecutionPayloadBid := { zBid with value := U64.lit 5, builder_index := U64.zero }

/-- A child at slot 9 (epoch 1) of a parent at slot 8 (epoch 1) whose payment `payments[8 + 0]`
is live. -/
def settleState : Gloas.BeaconState Pm :=
  { b5Base with
    slot := U64.lit 9
    latest_block_header := { zHeader with slot := U64.lit 8 }
    latest_execution_payload_bid := parentBid
    builder_pending_payments :=
      ⟨Array.replicate 8 zPayment ++
        #[{ weight := U64.zero, withdrawal := wQ, proposer_index := U64.zero }] ++
        Array.replicate 7 zPayment, by simp; rfl⟩ }

/-- **settled** (CL:1797-1804): a FULL parent in the current epoch settles its live payment: the
withdrawal is appended and the entry emptied. -/
theorem settled_witness :
    (Gloas.applyParentExecutionPayload { cfg := Config.minimal } settleState
        Gloas.ExecutionRequests.empty).toOption.map
      (fun s => (s.builder_pending_withdrawals.toArray,
        s.builder_pending_payments.toArray.all (· == zPayment))) =
      some (#[wQ], true) := by
  decide +kernel

/-- A child at slot 24 (epoch 3) of a parent at slot 8 (epoch 1): the parent's payment entry has
been evicted. -/
def directState : Gloas.BeaconState Pm :=
  { b5Base with
    slot := U64.lit 24
    latest_block_header := { zHeader with slot := U64.lit 8 }
    latest_execution_payload_bid := parentBid }

/-- **directAppend** (CL:1805-1814): a FULL parent older than the previous epoch has its bid's
payment appended directly, read from the bid (`fee_recipient`, `value`, `builder_index`). -/
theorem directAppend_witness :
    (Gloas.applyParentExecutionPayload { cfg := Config.minimal } directState
        Gloas.ExecutionRequests.empty).toOption.map
      (fun s => s.builder_pending_withdrawals.toArray) =
      some #[{ fee_recipient := zAdr, amount := U64.lit 5, builder_index := U64.zero }] := by
  decide +kernel

/-- An active payload builder with balance `10^10`. -/
def bidBuilder : Builder :=
  { pubkey := zPubkey, version := PAYLOAD_BUILDER_VERSION, execution_address := zAdr,
    balance := U64.lit 10000000000, deposit_epoch := U64.zero, withdrawable_epoch := FAR_FUTURE_EPOCH }

/-- Validator 0, the proposer of every slot (an exited validator, so `slash_validator` does not
need the exit churn). -/
def proposer0 : Validator :=
  { pubkey := zPubkey, withdrawal_credentials := z32, effective_balance := U64.lit 32000000000,
    slashed := false, activation_eligibility_epoch := U64.zero, activation_epoch := U64.zero,
    exit_epoch := U64.lit 5, withdrawable_epoch := U64.lit 10 }

/-- Slot 9 (epoch 1), finalized epoch 1, builder 0 active, validator 0 the proposer. -/
def bidState : Gloas.BeaconState Pm :=
  { b5Base with
    slot := U64.lit 9
    finalized_checkpoint := { zCheckpoint with epoch := U64.one }
    builders := ProgressiveListS.ofArray #[bidBuilder]
    validators := ProgressiveListS.ofArray #[proposer0]
    balances := ProgressiveListS.ofArray #[U64.lit 32000000000] }

/-- Builder 0's bid for slot 9, value 5 (BLS off: `bls = false`, statements.md §0.3). -/
def bid9msg : ExecutionPayloadBid :=
  { zBid with slot := U64.lit 9, value := U64.lit 5, builder_index := U64.zero, block_hash := 1 }

/-- Builder 0's signed bid for slot 9 (the signature is not checked at `bls = false`). -/
def bid9 : SignedExecutionPayloadBid := { message := bid9msg, signature := vrep 96 0 }

/-- The context of the witnesses: minimal configuration, BLS off. -/
def ctxOff : Ctx := { cfg := Config.minimal, blsActive := false }

/-- The live entry the bid records at `payments[SLOTS_PER_EPOCH + 9 % SLOTS_PER_EPOCH]`. -/
def bidEntry : BuilderPendingPayment :=
  { weight := U64.zero, withdrawal := wQ, proposer_index := U64.zero }

/-- **pendingAtEnd** (the one-block run): `process_execution_payload_bid` records the live payment
and nothing after it moves it; `builder_pending_withdrawals` is untouched. -/
theorem pendingAtEnd_witness :
    (Gloas.processExecutionPayloadBid ctxOff bidState bid9).toOption.map
      (fun s => (s.builder_pending_payments.toArray[9]?, s.builder_pending_withdrawals.toArray)) =
      some (some bidEntry, #[]) := by
  decide +kernel

/-- **clearedBySlash** (a self-slash in the bid's own block, CL:1579-1581): after the bid is
recorded, slashing its block's proposer (validator 0) empties the entry; nothing reaches
`builder_pending_withdrawals`. -/
theorem clearedBySlash_witness :
    (Gloas.processExecutionPayloadBid ctxOff bidState bid9 >>= fun s =>
        Gloas.slashValidator Config.minimal s U64.zero).toOption.map
      (fun s => (s.builder_pending_payments.toArray.all (· == zPayment),
        s.builder_pending_withdrawals.toArray)) =
      some (true, #[]) := by
  decide +kernel

end JauneConsensus.Facts.Gloas.B5Witnesses
