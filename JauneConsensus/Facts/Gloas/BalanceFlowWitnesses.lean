import JauneConsensus.Facts.Gloas.WithdrawalsBalanceFlow

/-!
# B5 function-level witnesses on closed minimal states (goal `eip8282-gloas-cross-layer-v1`, BF1)

statements.md §0.3 and B5's controls (3) and (4), all **F**: each payment fate is one function on a
closed minimal-preset state, and the G3-05 saturation witness is `apply_withdrawals` on a closed
state. No witness evaluates `hash_tree_root` of a state; each is checked by the kernel (`decide`
on an equation of `M` values, or `rfl`).

The base state `b5Base` has every field at its zero value (vectors filled to their preset
lengths); each witness overrides only the fields its function reads.
-/

namespace JauneConsensus.Facts.Gloas.BalanceFlowWitnesses

open JauneConsensus JauneConsensus.Facts JauneConsensus.Gloas

/-- The minimal preset. -/
abbrev MinimalPreset : Preset := Preset.minimal

private def replicateVector {α : Type} (n : Nat) (x : α) : Ssz.Vector α n := ⟨Array.replicate n x, by simp⟩
private def emptyList {α : Type} {n : Nat} : Ssz.List α n := ⟨#[], by simp⟩
private def zeroBitvector (n : Nat) : Bitvector n := ⟨Array.replicate n false, by simp⟩

private def zeroRoot : Root := 0
private def zeroAddress : ExecutionAddress := (0, 0)

private def zeroCheckpoint : Checkpoint := { epoch := U64.zero, root := zeroRoot }

private def zeroHeader : BeaconBlockHeader :=
  { slot := U64.zero, proposer_index := U64.zero, parent_root := zeroRoot, state_root := zeroRoot,
    body_root := zeroRoot }

private def zeroPubkey : BLSPubkey := replicateVector 48 0

private def zeroBid : ExecutionPayloadBid :=
  { parent_block_hash := zeroRoot, parent_block_root := zeroRoot, block_hash := zeroRoot, prev_randao := zeroRoot,
    fee_recipient := zeroAddress, gas_limit := U64.zero, builder_index := U64.zero, slot := U64.zero,
    value := U64.zero, execution_payment := U64.zero, blob_kzg_commitments := ProgressiveListOnSpine.empty,
    execution_requests_root := zeroRoot }

/-- The empty `BuilderPendingPayment` value. -/
private def zeroPayment : BuilderPendingPayment := BuilderPendingPayment.empty

/-- Every field at its zero value. -/
def balanceFlowBase : Gloas.BeaconState MinimalPreset where
  genesis_time := U64.zero
  genesis_validators_root := zeroRoot
  slot := U64.zero
  fork := { previous_version := replicateVector 4 0, current_version := replicateVector 4 0, epoch := U64.zero }
  latest_block_header := zeroHeader
  block_roots := replicateVector _ zeroRoot
  state_roots := replicateVector _ zeroRoot
  historical_roots := emptyList
  eth1_data := { deposit_root := zeroRoot, deposit_count := U64.zero, block_hash := zeroRoot }
  eth1_data_votes := emptyList
  eth1_deposit_index := U64.zero
  validators := ProgressiveListOnSpine.empty
  balances := ProgressiveListOnSpine.empty
  randao_mixes := replicateVector _ zeroRoot
  slashings := replicateVector _ U64.zero
  previous_epoch_participation := ProgressiveListOnSpine.empty
  current_epoch_participation := ProgressiveListOnSpine.empty
  justification_bits := zeroBitvector _
  previous_justified_checkpoint := zeroCheckpoint
  current_justified_checkpoint := zeroCheckpoint
  finalized_checkpoint := zeroCheckpoint
  inactivity_scores := ProgressiveListOnSpine.empty
  current_sync_committee := { pubkeys := replicateVector _ zeroPubkey, aggregate_pubkey := zeroPubkey }
  next_sync_committee := { pubkeys := replicateVector _ zeroPubkey, aggregate_pubkey := zeroPubkey }
  latest_block_hash := zeroRoot
  next_withdrawal_index := U64.zero
  next_withdrawal_validator_index := U64.zero
  historical_summaries := emptyList
  deposit_requests_start_index := U64.zero
  deposit_balance_to_consume := U64.zero
  exit_balance_to_consume := U64.zero
  earliest_exit_epoch := U64.zero
  consolidation_balance_to_consume := U64.zero
  earliest_consolidation_epoch := U64.zero
  pending_deposits := ProgressiveListOnSpine.empty
  pending_partial_withdrawals := ProgressiveListOnSpine.empty
  pending_consolidations := ProgressiveListOnSpine.empty
  proposer_lookahead := replicateVector _ U64.zero
  builders := ProgressiveListOnSpine.empty
  next_withdrawal_builder_index := U64.zero
  execution_payload_availability := zeroBitvector _
  builder_pending_payments := replicateVector _ zeroPayment
  builder_pending_withdrawals := ProgressiveListOnSpine.empty
  latest_execution_payload_bid := zeroBid
  payload_expected_withdrawals := ProgressiveListOnSpine.empty
  ptc_window := replicateVector _ (replicateVector _ U64.zero)

/-! ## G3-05 saturation witness (control (4)) -/

/-- A builder with balance 10. -/
def saturationBuilder : Builder :=
  { pubkey := zeroPubkey, version := PAYLOAD_BUILDER_VERSION, execution_address := zeroAddress, balance := U64.literal 10,
    deposit_epoch := U64.zero, withdrawable_epoch := U64.zero }

/-- A withdrawal of 16 routed to builder 0 (`validator_index = 0 | 2^40`). -/
def saturationWithdrawal : Withdrawal :=
  { index := U64.zero, validator_index := U64.literal (2 ^ 40), address := zeroAddress, amount := U64.literal 16 }

def saturationState : Gloas.BeaconState MinimalPreset := { balanceFlowBase with builders := ProgressiveListOnSpine.ofArray #[saturationBuilder] }

/-- **G3-05 saturation witness.** Pending 16 against balance 10: `apply_withdrawals` saturates
the builder's balance at 0, so the B5(i) equation `balance' + routed = balance` fails
(`0 + 16 ≠ 10`) when G3-05's hypothesis (`routed ≤ balance`) fails. -/
theorem saturation_witness :
    (Gloas.applyWithdrawals saturationState #[saturationWithdrawal]).toOption.map
        (fun s => s.builders.toArray.map (·.balance)) = some #[U64.zero] ∧
    routedSum U64.zero [saturationWithdrawal] = 16 ∧ saturationBuilder.balance.toNat = 10 := by
  refine ⟨by decide +kernel, by decide, rfl⟩

/-! ## Payment fates (control (3)), each on one function -/

/-- The withdrawal a quorum payment carries: 5 gwei to builder 0. -/
def quorumWithdrawal : BuilderPendingWithdrawal := { fee_recipient := zeroAddress, amount := U64.literal 5, builder_index := U64.zero }
/-- The withdrawal a sub-quorum payment carries: 7 gwei to builder 1. -/
def subQuorumWithdrawal : BuilderPendingWithdrawal := { fee_recipient := zeroAddress, amount := U64.literal 7, builder_index := U64.one }

/-- `payments[0]` has weight `10^9` (above the quorum), `payments[1]` weight 1 (below it). -/
def rotationState : Gloas.BeaconState MinimalPreset :=
  { balanceFlowBase with builder_pending_payments :=
      ⟨(#[{ weight := U64.literal 1000000000, withdrawal := quorumWithdrawal, proposer_index := U64.zero },
          { weight := U64.one, withdrawal := subQuorumWithdrawal, proposer_index := U64.zero }] : Array _) ++
        Array.replicate 14 zeroPayment, by simp; rfl⟩ }

/-- **quorum** and **droppedSubQuorum** (CL:1724-1731). With no active validator the total
active balance is one increment, so the quorum is `10^9 / 8 * 6 / 10 = 75 000 000`. At the
epoch rotation the live entry with weight `≥` quorum is appended to
`builder_pending_withdrawals` (quorum); the live entry with weight below it is not appended and
leaves `builder_pending_payments` (droppedSubQuorum): every payment is empty afterwards. -/
theorem quorum_and_dropped_witness :
    (Gloas.getBuilderPaymentQuorumThreshold rotationState).toOption = some (U64.literal 75000000) ∧
    (Gloas.processBuilderPendingPayments Config.minimal rotationState).toOption.map
        (fun s => (s.builder_pending_withdrawals.toArray,
          s.builder_pending_payments.toArray.all (· == zeroPayment))) =
      some (#[quorumWithdrawal], true) := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- The parent block's bid: value 5, builder 0. -/
def parentBid : ExecutionPayloadBid := { zeroBid with value := U64.literal 5, builder_index := U64.zero }

/-- A child at slot 9 (epoch 1) of a parent at slot 8 (epoch 1) whose payment `payments[8 + 0]`
is live. -/
def settleState : Gloas.BeaconState MinimalPreset :=
  { balanceFlowBase with
    slot := U64.literal 9
    latest_block_header := { zeroHeader with slot := U64.literal 8 }
    latest_execution_payload_bid := parentBid
    builder_pending_payments :=
      ⟨Array.replicate 8 zeroPayment ++
        #[{ weight := U64.zero, withdrawal := quorumWithdrawal, proposer_index := U64.zero }] ++
        Array.replicate 7 zeroPayment, by simp; rfl⟩ }

/-- **settled** (CL:1797-1804): a FULL parent in the current epoch settles its live payment: the
withdrawal is appended and the entry emptied. -/
theorem settled_witness :
    (Gloas.applyParentExecutionPayload { config := Config.minimal } settleState
        Gloas.ExecutionRequests.empty).toOption.map
      (fun s => (s.builder_pending_withdrawals.toArray,
        s.builder_pending_payments.toArray.all (· == zeroPayment))) =
      some (#[quorumWithdrawal], true) := by
  decide +kernel

/-- A child at slot 24 (epoch 3) of a parent at slot 8 (epoch 1): the parent's payment entry has
been evicted. -/
def directState : Gloas.BeaconState MinimalPreset :=
  { balanceFlowBase with
    slot := U64.literal 24
    latest_block_header := { zeroHeader with slot := U64.literal 8 }
    latest_execution_payload_bid := parentBid }

/-- **directAppend** (CL:1805-1814): a FULL parent older than the previous epoch has its bid's
payment appended directly, read from the bid (`fee_recipient`, `value`, `builder_index`). -/
theorem directAppend_witness :
    (Gloas.applyParentExecutionPayload { config := Config.minimal } directState
        Gloas.ExecutionRequests.empty).toOption.map
      (fun s => s.builder_pending_withdrawals.toArray) =
      some #[{ fee_recipient := zeroAddress, amount := U64.literal 5, builder_index := U64.zero }] := by
  decide +kernel

/-- An active payload builder with balance `10^10`. -/
def bidBuilder : Builder :=
  { pubkey := zeroPubkey, version := PAYLOAD_BUILDER_VERSION, execution_address := zeroAddress,
    balance := U64.literal 10000000000, deposit_epoch := U64.zero, withdrawable_epoch := FAR_FUTURE_EPOCH }

/-- Validator 0, the proposer of every slot (an exited validator, so `slash_validator` does not
need the exit churn). -/
def proposerZero : Validator :=
  { pubkey := zeroPubkey, withdrawal_credentials := zeroRoot, effective_balance := U64.literal 32000000000,
    slashed := false, activation_eligibility_epoch := U64.zero, activation_epoch := U64.zero,
    exit_epoch := U64.literal 5, withdrawable_epoch := U64.literal 10 }

/-- Slot 9 (epoch 1), finalized epoch 1, builder 0 active, validator 0 the proposer. -/
def bidState : Gloas.BeaconState MinimalPreset :=
  { balanceFlowBase with
    slot := U64.literal 9
    finalized_checkpoint := { zeroCheckpoint with epoch := U64.one }
    builders := ProgressiveListOnSpine.ofArray #[bidBuilder]
    validators := ProgressiveListOnSpine.ofArray #[proposerZero]
    balances := ProgressiveListOnSpine.ofArray #[U64.literal 32000000000] }

/-- Builder 0's bid for slot 9, value 5 (BLS off: `bls = false`, statements.md §0.3). -/
def bidMessageAtSlotNine : ExecutionPayloadBid :=
  { zeroBid with slot := U64.literal 9, value := U64.literal 5, builder_index := U64.zero, block_hash := 1 }

/-- Builder 0's signed bid for slot 9 (the signature is not checked at `bls = false`). -/
def bidAtSlotNine : SignedExecutionPayloadBid := { message := bidMessageAtSlotNine, signature := replicateVector 96 0 }

/-- The context of the witnesses: minimal configuration, BLS off. -/
def contextBlsOff : Context := { config := Config.minimal, blsActive := false }

/-- The live entry the bid records at `payments[SLOTS_PER_EPOCH + 9 % SLOTS_PER_EPOCH]`. -/
def bidEntry : BuilderPendingPayment :=
  { weight := U64.zero, withdrawal := quorumWithdrawal, proposer_index := U64.zero }

/-- **pendingAtEnd** (the one-block run): `process_execution_payload_bid` records the live payment
and nothing after it moves it; `builder_pending_withdrawals` is untouched. -/
theorem pendingAtEnd_witness :
    (Gloas.processExecutionPayloadBid contextBlsOff bidState bidAtSlotNine).toOption.map
      (fun s => (s.builder_pending_payments.toArray[9]?, s.builder_pending_withdrawals.toArray)) =
      some (some bidEntry, #[]) := by
  decide +kernel

/-- **clearedBySlash** (a self-slash in the bid's own block, CL:1579-1581): after the bid is
recorded, slashing its block's proposer (validator 0) empties the entry; nothing reaches
`builder_pending_withdrawals`. -/
theorem clearedBySlash_witness :
    (Gloas.processExecutionPayloadBid contextBlsOff bidState bidAtSlotNine >>= fun s =>
        Gloas.slashValidator Config.minimal s U64.zero).toOption.map
      (fun s => (s.builder_pending_payments.toArray.all (· == zeroPayment),
        s.builder_pending_withdrawals.toArray)) =
      some (true, #[]) := by
  decide +kernel

end JauneConsensus.Facts.Gloas.BalanceFlowWitnesses
