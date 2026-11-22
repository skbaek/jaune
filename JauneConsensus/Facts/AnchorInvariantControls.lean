import JauneConsensus.Facts.SlotEpochFrames

/-!
# Closed-State Anchor-Invariant Negative Controls (G1b Deliverable 4)

Inspectable closed-state negative controls on `BeaconState Preset.minimal .electra` demonstrating
that each new component of `CorpusAnchorInv` (`PendingConsolidationsDistinct` and
`BalancesMatchValidators`) is load-bearing and minimal for the cross-layer `S9` corpus:

1. **`pendingConsolidationsDistinct_negative_control` (`C-S9` clause-failure control):**
   Constructs a closed `BeaconState Preset.minimal .electra` satisfying `AnchorInv` and
   `BalancesMatchValidators` while violating `PendingConsolidationsDistinct` via a queued
   self-consolidation `⟨0, 0⟩`. `processPendingConsolidations Config.minimal` succeeds, dequeues
   `⟨0, 0⟩`, and leaves `balances[0] = 32_000_000_000` (`decreaseBalance` followed by
   `increaseBalance` at the same index), falsifying both the `C-S9` source-debit clause
   (`b' = bal - amount`, which would require `0`) and the `C-S9` target-credit clause
   (`tb' = tb + amount`, which would require `64_000_000_000`) of `consolidation_balance_moved`.

2. **`balancesMatchValidators_over_negative_control` (`D-S9` clause-failure control, `balances > validators`):**
   Constructs a closed `BeaconState Preset.minimal .electra` satisfying `AnchorInv` and
   `PendingConsolidationsDistinct` while violating `BalancesMatchValidators` via `validators = #[]`
   and `balances = #[99_000_000_000]`. `processPendingDeposits` with one finalized `GENESIS_SLOT`
   deposit of `32_000_000_000` Gwei succeeds, appends the new validator at index `0`, and calls
   `setOrAppendList state.balances 0 deposit.amount`: because `0 ≠ balances.length = 1`,
   `setOrAppendList` overwrites `balances[0]` to `32_000_000_000` instead of pushing, falsifying
   the `D-S9` new-validator balance-append clause (`s'.balances.toArray =
   state.balances.toArray.push deposit.amount`) of `applyPendingDeposit_newValidator_credit`.

3. **`balancesMatchValidators_under_blocks_step` (step-blocking control, `balances < validators`):**
   Constructs a closed `BeaconState Preset.minimal .electra` satisfying `AnchorInv` and
   `PendingConsolidationsDistinct` while violating `BalancesMatchValidators` via
   `validators = #[ctrlVal]` and `balances = #[]`. Every balance-touching pass on validator `0`
   (`processEffectiveBalanceUpdates`, `processPendingConsolidations`, and `processPendingDeposits`
   on a top-up deposit) fails with `Reject.index`.

Nothing here edits a spec definition.
-/

namespace JauneConsensus.Facts

open JauneConsensus

section NegativeControls

private def replicateVector {α : Type} (x : α) (n : Nat) : Ssz.Vector α n :=
  ⟨Array.replicate n x, Array.size_replicate⟩

private def emptySsz {α : Type} (n : Nat) : Ssz.List α n :=
  ⟨#[], Nat.zero_le n⟩

private def zeroBitvector (n : Nat) : Bitvector n :=
  ⟨Array.replicate n false, Array.size_replicate⟩

private def zeroPubkey : BLSPubkey := replicateVector 0 48
private def zeroSignature : BLSSignature := replicateVector 0 96
private def zeroVersion : Version := replicateVector 0 4

private def zeroFork : Fork :=
  { previous_version := zeroVersion, current_version := zeroVersion, epoch := U64.zero }

private def zeroHeader : BeaconBlockHeader :=
  { slot := U64.zero, proposer_index := U64.zero,
    parent_root := 0, state_root := 0, body_root := 0 }

private def zeroEth1Data : Eth1Data :=
  { deposit_root := 0, deposit_count := U64.zero, block_hash := 0 }

private def zeroCheckpoint : Checkpoint :=
  { epoch := U64.zero, root := 0 }

private def zeroSyncCommittee : SyncCommittee Preset.minimal :=
  { pubkeys := replicateVector zeroPubkey Preset.minimal.SYNC_COMMITTEE_SIZE,
    aggregate_pubkey := zeroPubkey }

private def zeroPayloadHeader : ExecutionPayloadHeader Preset.minimal :=
  { parent_hash := 0,
    fee_recipient := 0,
    state_root := 0,
    receipts_root := 0,
    logs_bloom := replicateVector 0 Preset.minimal.BYTES_PER_LOGS_BLOOM,
    prev_randao := 0,
    block_number := U64.zero,
    gas_limit := U64.zero,
    gas_used := U64.zero,
    timestamp := U64.zero,
    extra_data := emptySsz Preset.minimal.MAX_EXTRA_DATA_BYTES,
    base_fee_per_gas := UnsignedIntegerOfBytes.zero,
    block_hash := 0,
    transactions_root := 0,
    withdrawals_root := 0,
    blob_gas_used := U64.zero,
    excess_blob_gas := U64.zero }

/-- Base empty `BeaconState Preset.minimal .electra` satisfying `CorpusAnchorInv`. -/
def controlBaseState : BeaconState Preset.minimal .electra :=
  { genesis_time := U64.zero,
    genesis_validators_root := 0,
    slot := U64.zero,
    fork := zeroFork,
    latest_block_header := zeroHeader,
    block_roots := replicateVector 0 Preset.minimal.SLOTS_PER_HISTORICAL_ROOT,
    state_roots := replicateVector 0 Preset.minimal.SLOTS_PER_HISTORICAL_ROOT,
    historical_roots := emptySsz Preset.minimal.HISTORICAL_ROOTS_LIMIT,
    eth1_data := zeroEth1Data,
    eth1_data_votes := emptySsz
      (Preset.minimal.EPOCHS_PER_ETH1_VOTING_PERIOD * Preset.minimal.SLOTS_PER_EPOCH),
    eth1_deposit_index := U64.zero,
    validators := emptySsz Preset.minimal.VALIDATOR_REGISTRY_LIMIT,
    balances := emptySsz Preset.minimal.VALIDATOR_REGISTRY_LIMIT,
    randao_mixes := replicateVector 0 Preset.minimal.EPOCHS_PER_HISTORICAL_VECTOR,
    slashings := replicateVector U64.zero Preset.minimal.EPOCHS_PER_SLASHINGS_VECTOR,
    previous_epoch_participation := emptySsz Preset.minimal.VALIDATOR_REGISTRY_LIMIT,
    current_epoch_participation := emptySsz Preset.minimal.VALIDATOR_REGISTRY_LIMIT,
    justification_bits := zeroBitvector JUSTIFICATION_BITS_LENGTH,
    previous_justified_checkpoint := zeroCheckpoint,
    current_justified_checkpoint := zeroCheckpoint,
    finalized_checkpoint := { epoch := U64.one, root := 0 },
    inactivity_scores := emptySsz Preset.minimal.VALIDATOR_REGISTRY_LIMIT,
    current_sync_committee := zeroSyncCommittee,
    next_sync_committee := zeroSyncCommittee,
    latest_execution_payload_header := zeroPayloadHeader,
    next_withdrawal_index := U64.zero,
    next_withdrawal_validator_index := U64.zero,
    historical_summaries := emptySsz Preset.minimal.HISTORICAL_ROOTS_LIMIT,
    deposit_requests_start_index := U64.zero,
    deposit_balance_to_consume := U64.zero,
    exit_balance_to_consume := U64.zero,
    earliest_exit_epoch := U64.zero,
    consolidation_balance_to_consume := U64.zero,
    earliest_consolidation_epoch := U64.zero,
    pending_deposits := emptySsz Preset.minimal.PENDING_DEPOSITS_LIMIT,
    pending_partial_withdrawals := emptySsz Preset.minimal.PENDING_PARTIAL_WITHDRAWALS_LIMIT,
    pending_consolidations := emptySsz Preset.minimal.PENDING_CONSOLIDATIONS_LIMIT,
    proposer_lookahead := () }

/-- Unslashed withdrawable validator with `32 ETH` effective balance (`exit_epoch = 0`,
`withdrawable_epoch = 0`). -/
def controlValidator : Validator :=
  { pubkey := zeroPubkey,
    withdrawal_credentials := 0,
    effective_balance := U64.literal 32000000000,
    slashed := false,
    activation_eligibility_epoch := U64.zero,
    activation_epoch := U64.zero,
    exit_epoch := U64.zero,
    withdrawable_epoch := U64.zero }

/-- Finalized `GENESIS_SLOT` pending deposit of `32 ETH`. -/
def controlDeposit : PendingDeposit :=
  { pubkey := zeroPubkey,
    withdrawal_credentials := 0,
    amount := U64.literal 32000000000,
    signature := zeroSignature,
    slot := GENESIS_SLOT }

/-! ### Control 1: `PendingConsolidationsDistinct` is load-bearing for `C-S9` -/

/-- Closed state satisfying `AnchorInv` and `BalancesMatchValidators`, but with a self-consolidation
`⟨0, 0⟩` violating `PendingConsolidationsDistinct`. -/
def stateSelfConsolidation : BeaconState Preset.minimal .electra :=
  { controlBaseState with
    validators := ⟨#[controlValidator], by decide⟩,
    balances := ⟨#[U64.literal 32000000000], by decide⟩,
    pending_consolidations := ⟨#[{ source_index := U64.zero, target_index := U64.zero }], by decide⟩ }

/-- **`PendingConsolidationsDistinct` negative control (`C-S9`):**
`s_pc_self` satisfies `AnchorInv` and `BalancesMatchValidators` while violating
`PendingConsolidationsDistinct`. `processPendingConsolidations Config.minimal s_pc_self` succeeds,
dequeues `⟨0, 0⟩`, and leaves `balances[0] = 32_000_000_000`, falsifying both the `C-S9`
source-debit clause (`b' = bal - amount`) and target-credit clause (`tb' = tb + amount`) of
`consolidation_balance_moved`. -/
theorem pendingConsolidationsDistinct_negative_control :
    AnchorInvariant stateSelfConsolidation ∧
    BalancesMatchValidators stateSelfConsolidation ∧
    ¬ PendingConsolidationsDistinct stateSelfConsolidation ∧
    ∃ s_pc',
      processPendingConsolidations Config.minimal stateSelfConsolidation = .ok s_pc' ∧
      pendingConsolidationsList s_pc' = [] ∧
      s_pc'.balances.toArray[(U64.zero).toNat]? = some (U64.literal 32000000000) ∧
      (¬ ∃ b', s_pc'.balances.toArray[(U64.zero).toNat]? = some b' ∧
          b'.toNat = (U64.literal 32000000000).toNat -
            (if U64.literal 32000000000 < controlValidator.effective_balance
             then U64.literal 32000000000 else controlValidator.effective_balance).toNat) ∧
      (¬ ∃ tb tb',
          stateSelfConsolidation.balances.toArray[(U64.zero).toNat]? = some tb ∧
          s_pc'.balances.toArray[(U64.zero).toNat]? = some tb' ∧
          tb'.toNat = tb.toNat +
            (if U64.literal 32000000000 < controlValidator.effective_balance
             then U64.literal 32000000000 else controlValidator.effective_balance).toNat) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro l hl p hp
    have hl_eq : l = emptySsz Preset.minimal.PENDING_PARTIAL_WITHDRAWALS_LIMIT :=
      (Except.ok.inj hl).symm
    subst hl_eq
    nomatch hp
  · intro v hv hff
    have hv_eq : v = controlValidator := by
      simpa [stateSelfConsolidation] using hv
    subst hv_eq
    exact absurd hff (by decide)
  · unfold BalancesMatchValidators; decide
  · intro hpcd
    have hmem : ({ source_index := U64.zero, target_index := U64.zero } : PendingConsolidation) ∈
        pendingConsolidationsList stateSelfConsolidation := by
      rw [pendingConsolidationsList_eq_get rfl]
      exact List.Mem.head _
    exact hpcd _ hmem rfl
  · have hproc : ∃ s_pc',
        processPendingConsolidations Config.minimal stateSelfConsolidation = .ok s_pc' ∧
        pendingConsolidationsList s_pc' = [] ∧
        s_pc'.balances.toArray[(U64.zero).toNat]? = some (U64.literal 32000000000) :=
      ⟨_, rfl, by rw [pendingConsolidationsList_eq_get rfl]; rfl, rfl⟩
    obtain ⟨s_pc', hp, hpcl, hbal0⟩ := hproc
    refine ⟨s_pc', hp, hpcl, hbal0, ?_, ?_⟩
    · rintro ⟨b', hb', hsub⟩
      rw [hbal0] at hb'
      have hb'_eq : b' = U64.literal 32000000000 := (Option.some.inj hb').symm
      subst hb'_eq
      exact absurd hsub (by decide)
    · rintro ⟨tb, tb', htb, htb', hadd⟩
      have htb0 : stateSelfConsolidation.balances.toArray[(U64.zero).toNat]? = some (U64.literal 32000000000) := rfl
      rw [htb0] at htb
      rw [hbal0] at htb'
      have htb_eq : tb = U64.literal 32000000000 := (Option.some.inj htb).symm
      have htb'_eq : tb' = U64.literal 32000000000 := (Option.some.inj htb').symm
      subst htb_eq; subst htb'_eq
      exact absurd hadd (by decide)

/-! ### Control 2a: `BalancesMatchValidators` (`balances > validators`) is load-bearing for `D-S9` -/

/-- Closed state satisfying `AnchorInv` and `PendingConsolidationsDistinct`, but with
`validators = #[]` and `balances = #[99_000_000_000]` (`balances.size = 1 > 0 = validators.size`). -/
def stateBalancesMatchValidatorsOver : BeaconState Preset.minimal .electra :=
  { controlBaseState with
    validators := emptySsz Preset.minimal.VALIDATOR_REGISTRY_LIMIT,
    balances := ⟨#[U64.literal 99000000000], by decide⟩,
    pending_deposits := ⟨#[controlDeposit], by decide⟩ }

private theorem isValidDepositSignature_controlDeposit :
    isValidDepositSignature { config := Config.minimal, blsActive := false }
      controlDeposit.pubkey controlDeposit.withdrawal_credentials controlDeposit.amount
      controlDeposit.signature = .ok true := by
  have hver : versionOf Config.minimal.GENESIS_FORK_VERSION =
      .ok ⟨#[0x00, 0x00, 0x00, 0x01], by decide⟩ := rfl
  unfold isValidDepositSignature computeDomainDefault
  rw [hver]
  rfl

/-- **`BalancesMatchValidators` negative control (`D-S9`, `balances.size > validators.size`):**
`s_bm_over` satisfies `AnchorInv` and `PendingConsolidationsDistinct` while violating
`BalancesMatchValidators`. `processPendingDeposits { cfg := Config.minimal, blsActive := false }`
succeeds, dequeues `ctrlDeposit`, and appends 1 validator (`s_bm'.validators.toArray.size = 1`),
but `setOrAppendList` overwrites `balances[0]` instead of pushing, leaving
`s_bm'.balances.toArray = #[ctrlDeposit.amount] ≠ s_bm_over.balances.toArray.push ctrlDeposit.amount`
and falsifying the `D-S9` new-validator balance-append clause of
`applyPendingDeposit_newValidator_credit`. -/
theorem balancesMatchValidators_over_negative_control :
    AnchorInvariant stateBalancesMatchValidatorsOver ∧
    PendingConsolidationsDistinct stateBalancesMatchValidatorsOver ∧
    ¬ BalancesMatchValidators stateBalancesMatchValidatorsOver ∧
    ∃ s_bm',
      processPendingDeposits { config := Config.minimal, blsActive := false } stateBalancesMatchValidatorsOver = .ok s_bm' ∧
      pendingDepositsList s_bm' = [] ∧
      s_bm'.validators.toArray.size = 1 ∧
      s_bm'.balances.toArray = #[controlDeposit.amount] ∧
      s_bm'.balances.toArray ≠ stateBalancesMatchValidatorsOver.balances.toArray.push controlDeposit.amount := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro l hl p hp
    have hl_eq : l = emptySsz Preset.minimal.PENDING_PARTIAL_WITHDRAWALS_LIMIT :=
      (Except.ok.inj hl).symm
    subst hl_eq
    nomatch hp
  · intro v hv
    simp [stateBalancesMatchValidatorsOver, emptySsz] at hv
  · intro pc hpc
    rw [pendingConsolidationsList_eq_get rfl] at hpc
    nomatch hpc
  · unfold BalancesMatchValidators; decide
  · have hfind : findValidatorIndex stateBalancesMatchValidatorsOver controlDeposit.pubkey = none := by
      unfold findValidatorIndex
      simp [stateBalancesMatchValidatorsOver, emptySsz]
    have happly :
        applyPendingDeposit { config := Config.minimal, blsActive := false } stateBalancesMatchValidatorsOver controlDeposit =
          addValidatorToRegistry stateBalancesMatchValidatorsOver controlDeposit.pubkey controlDeposit.withdrawal_credentials
            controlDeposit.amount := by
      rw [applyPendingDeposit_eq]
      unfold classifyPendingDeposit
      rw [hfind]
      dsimp only
      rw [isValidDepositSignature_controlDeposit]
      rfl
    have hstep :
        pendingDepositsLoop { config := Config.minimal, blsActive := false }
          U64.one (U64.literal 64000000000) (U64.literal 8) U64.zero [controlDeposit]
          (U64.zero, 0, #[], false, stateBalancesMatchValidatorsOver) =
        (do
          let st ← addValidatorToRegistry stateBalancesMatchValidatorsOver controlDeposit.pubkey
            controlDeposit.withdrawal_credentials controlDeposit.amount
          pure (controlDeposit.amount, 1, #[], false, st)) := by
      unfold pendingDepositsLoop pendingDepositStep
      dsimp only
      rw [hfind]
      dsimp only
      have hc1 : (!ConsensusFork.electra.atLeast .fulu && decide (controlDeposit.slot > GENESIS_SLOT) &&
          decide (stateBalancesMatchValidatorsOver.eth1_deposit_index < U64.zero)) = false := by decide
      have hc2 : ¬ (controlDeposit.slot > U64.literal 8) := by decide
      have hc3 : ¬ (0 ≥ Preset.minimal.MAX_PENDING_DEPOSITS_PER_EPOCH) := by decide
      rw [hc1]
      simp only [Bool.false_eq_true, ite_false, hc2, hc3, pure_bind]
      have hadd : U64.zero.add? controlDeposit.amount "process_pending_deposits" =
          .ok controlDeposit.amount := rfl
      rw [hadd, ok_bind']
      have hc4 : decide (controlDeposit.amount > U64.literal 64000000000) = false := by decide
      rw [hc4]
      simp only [Bool.false_eq_true, ite_false]
      rw [happly]
      rfl
    have hreg : ∃ s_reg,
        addValidatorToRegistry stateBalancesMatchValidatorsOver controlDeposit.pubkey controlDeposit.withdrawal_credentials
          controlDeposit.amount = .ok s_reg ∧
        s_reg.validators.toArray.size = 1 ∧
        s_reg.balances.toArray = #[controlDeposit.amount] :=
      ⟨_, rfl, rfl, rfl⟩
    obtain ⟨s_reg, hreg_eq, hv_sz, hb_eq⟩ := hreg
    have hproc :
        processPendingDeposits { config := Config.minimal, blsActive := false } stateBalancesMatchValidatorsOver =
          (do
            let st ← s_reg.setPendingDeposits (emptySsz Preset.minimal.PENDING_DEPOSITS_LIMIT)
            st.setDepositBalanceToConsume U64.zero) := by
      rw [processPendingDeposits_eq]
      have he0 : getCurrentEpoch stateBalancesMatchValidatorsOver = .ok U64.zero := rfl
      have hne : U64.zero.add? U64.one "process_pending_deposits" = .ok U64.one := rfl
      have hdb : stateBalancesMatchValidatorsOver.depositBalanceToConsume = .ok U64.zero := rfl
      have hcl : getActivationExitChurnLimit Config.minimal stateBalancesMatchValidatorsOver =
          .ok (U64.literal 64000000000) := rfl
      have hav : U64.zero.add? (U64.literal 64000000000) "process_pending_deposits" =
          .ok (U64.literal 64000000000) := rfl
      have hfs : computeStartSlotAtEpoch Preset.minimal stateBalancesMatchValidatorsOver.finalized_checkpoint.epoch =
          .ok (U64.literal 8) := rfl
      have hrs : stateBalancesMatchValidatorsOver.depositRequestsStartIndex = .ok U64.zero := rfl
      have hpd : stateBalancesMatchValidatorsOver.pendingDeposits = .ok ⟨#[controlDeposit], by decide⟩ := rfl
      rw [he0, ok_bind', hne, ok_bind', hdb, ok_bind', hcl, ok_bind', hav, ok_bind',
          hfs, ok_bind', hrs, ok_bind', hpd, ok_bind']
      have hlist : (#[controlDeposit]).toList = [controlDeposit] := rfl
      rw [hlist, hstep, hreg_eq]
      rfl
    have hout : ∃ s_bm',
        (do
          let st ← s_reg.setPendingDeposits (emptySsz Preset.minimal.PENDING_DEPOSITS_LIMIT)
          st.setDepositBalanceToConsume U64.zero) = .ok s_bm' ∧
        pendingDepositsList s_bm' = [] ∧
        s_bm'.validators = s_reg.validators ∧
        s_bm'.balances = s_reg.balances :=
      ⟨_, rfl, rfl, rfl, rfl⟩
    obtain ⟨s_bm', hout_eq, hpdl, hv_s', hb_s'⟩ := hout
    refine ⟨s_bm', hproc.trans hout_eq, hpdl, ?_, ?_, ?_⟩
    · rw [hv_s']; exact hv_sz
    · rw [hb_s']; exact hb_eq
    · rw [hb_s', hb_eq]
      decide

/-! ### Control 2b: `BalancesMatchValidators` (`balances < validators`) is step-blocking -/

/-- Closed state satisfying `AnchorInv` and `PendingConsolidationsDistinct`, but with
`validators = #[ctrlValidator]` and `balances = #[]` (`balances.size = 0 < 1 = validators.size`). -/
def stateBalancesMatchValidatorsUnder : BeaconState Preset.minimal .electra :=
  { controlBaseState with
    validators := ⟨#[controlValidator], by decide⟩,
    balances := emptySsz Preset.minimal.VALIDATOR_REGISTRY_LIMIT,
    pending_deposits := ⟨#[controlDeposit], by decide⟩,
    pending_consolidations := ⟨#[{ source_index := U64.zero, target_index := U64.one }], by decide⟩ }

/-- **`BalancesMatchValidators` step-blocking control (`balances.size < validators.size`):**
`s_bm_under` satisfies `AnchorInv` and `PendingConsolidationsDistinct` while violating
`BalancesMatchValidators`, and causes `processEffectiveBalanceUpdates`,
`processPendingConsolidations`, and `applyPendingDepositOutcome ... (.topUp U64.zero)` (crediting a
top-up deposit for validator `0`) to fail with out-of-bounds balance reads. -/
theorem balancesMatchValidators_under_blocks_step :
    AnchorInvariant stateBalancesMatchValidatorsUnder ∧
    PendingConsolidationsDistinct stateBalancesMatchValidatorsUnder ∧
    ¬ BalancesMatchValidators stateBalancesMatchValidatorsUnder ∧
    (∃ e, processEffectiveBalanceUpdates Config.minimal stateBalancesMatchValidatorsUnder = .error e) ∧
    (∃ e, processPendingConsolidations Config.minimal stateBalancesMatchValidatorsUnder = .error e) ∧
    (∃ e, applyPendingDepositOutcome stateBalancesMatchValidatorsUnder controlDeposit (.topUp U64.zero) = .error e) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · intro l hl p hp
    have hl_eq : l = emptySsz Preset.minimal.PENDING_PARTIAL_WITHDRAWALS_LIMIT :=
      (Except.ok.inj hl).symm
    subst hl_eq
    nomatch hp
  · intro v hv hff
    have hv_eq : v = controlValidator := by
      simpa [stateBalancesMatchValidatorsUnder] using hv
    subst hv_eq
    exact absurd hff (by decide)
  · intro pc hpc
    rw [pendingConsolidationsList_eq_get rfl] at hpc
    have hpc_eq : pc = { source_index := U64.zero, target_index := U64.one } :=
      List.mem_singleton.mp hpc
    subst hpc_eq
    decide
  · unfold BalancesMatchValidators; decide

end NegativeControls

end JauneConsensus.Facts
