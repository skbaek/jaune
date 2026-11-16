import JauneConsensus.Facts.Operations

/-!
# Facts: what `process_deposit_request` does

About `JauneConsensus.processDepositRequest` (`JauneConsensus/Block.lean`), transcribed from
`v1.7.0-beta.4` `specs/electra/beacon-chain.md` (Electra: set `deposit_requests_start_index` when it
is unset, then append) and `specs/fulu/beacon-chain.md` (Fulu: append only). The function has no
early return: every request either becomes exactly one appended `PendingDeposit` carrying the
request's key, credentials, amount and signature and the state's slot, or the block is rejected
(the queue is at `PENDING_DEPOSITS_LIMIT`).

Nothing here edits a spec definition: `depositRequestPending` and `depositRequestStartIndex` are
new, built from the same fields the function reads.
-/

namespace JauneConsensus.Facts

open JauneConsensus

variable {P : Preset} {f : CFork}

/-- The `PendingDeposit` that `process_deposit_request` appends for `dr` at slot `slot`. -/
def depositRequestPending (dr : DepositRequest) (slot : Slot) : PendingDeposit :=
  { pubkey := dr.pubkey, withdrawal_credentials := dr.withdrawal_credentials, amount := dr.amount,
    signature := dr.signature, slot := slot }

/-- `deposit_requests_start_index` after `process_deposit_request`: before Fulu it is set to the
request's index when it was `UNSET_DEPOSIT_REQUESTS_START_INDEX`; otherwise it is unchanged. -/
def depositRequestStartIndex (f : CFork) (old : U64) (dr : DepositRequest) : U64 :=
  if !(f.atLeast .fulu) && old == UNSET_DEPOSIT_REQUESTS_START_INDEX then dr.index else old

/-- A gated write under the fork fact succeeds with the gated value. -/
theorem gated_write_eq {α : Type} {c : Bool} (h : c = true) (x : α) (site : String) :
    Gated.write c x site = .ok (Gated.mk h x) := by
  subst h; rfl

/-- `Gated.mk` after `Gated.get` is the identity. -/
theorem gated_mk_get {α : Type} {c : Bool} (h : c = true) (x : Gated c α) :
    Gated.mk h (Gated.get h x) = x := by
  subst h; rfl

/-- **The equation of `process_deposit_request`** (Electra and Fulu): it is the append of
`depositRequestPending dr state.slot` to the pending-deposit queue, with the start index updated as
`depositRequestStartIndex` says, and no other field changed. It fails exactly when the append does
(the queue is full). -/
theorem processDepositRequest_eq (h : f.atLeast .electra = true) (state : BeaconState P f)
    (dr : DepositRequest) :
    processDepositRequest state dr =
      (fun q => { state with
        deposit_requests_start_index := Gated.mk h
          (depositRequestStartIndex f (Gated.get h state.deposit_requests_start_index) dr)
        pending_deposits := Gated.mk h q }) <$>
        (Gated.get h state.pending_deposits).push (depositRequestPending dr state.slot)
          "process_deposit_request" := by
  unfold processDepositRequest depositRequestStartIndex depositRequestPending
  simp only [BeaconState.depositRequestsStartIndex, BeaconState.setDepositRequestsStartIndex,
    BeaconState.pendingDeposits, BeaconState.setPendingDeposits, gated_read_get h,
    gated_write_eq h, ok_bind']
  cases hq : (Gated.get h state.pending_deposits).push
      { pubkey := dr.pubkey, withdrawal_credentials := dr.withdrawal_credentials,
        amount := dr.amount, signature := dr.signature, slot := state.slot }
      "process_deposit_request" with
  | error e =>
    cases hfu : f.atLeast .fulu <;>
      cases hu : (Gated.get h state.deposit_requests_start_index ==
        UNSET_DEPOSIT_REQUESTS_START_INDEX) <;>
      simp only [Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, Bool.false_eq_true,
        ite_true, ite_false, pure_bind, hq] <;> rfl
  | ok q =>
    cases hfu : f.atLeast .fulu <;>
      cases hu : (Gated.get h state.deposit_requests_start_index ==
        UNSET_DEPOSIT_REQUESTS_START_INDEX) <;>
      simp only [hu, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
        Bool.false_eq_true, ite_true, ite_false, pure_bind, ok_bind', hq, gated_mk_get] <;> rfl

/-- `process_deposit_request` succeeds exactly when the pending-deposit queue has room for one
more entry. -/
theorem processDepositRequest_ok_iff (h : f.atLeast .electra = true) (state : BeaconState P f)
    (dr : DepositRequest) :
    (∃ s', processDepositRequest state dr = .ok s') ↔
      (Gated.get h state.pending_deposits).toArray.size + 1 ≤ P.PENDING_DEPOSITS_LIMIT := by
  rw [processDepositRequest_eq h]
  unfold SszList.push
  by_cases hs : (Gated.get h state.pending_deposits).toArray.size + 1 ≤ P.PENDING_DEPOSITS_LIMIT
  · simp only [hs, dite_true, iff_true]
    exact ⟨_, rfl⟩
  · simp only [hs, dite_false, iff_false]
    rintro ⟨s', hs'⟩
    cases hs'

/-- **D-S9 fate, one request**: on success, the pending-deposit queue is the old queue with
exactly `depositRequestPending dr state.slot` appended (the request's key, credentials, amount and
signature, at the state's slot). -/
theorem processDepositRequest_pending (h : f.atLeast .electra = true) {state s' : BeaconState P f}
    {dr : DepositRequest} (hp : processDepositRequest state dr = .ok s') :
    (Gated.get h s'.pending_deposits).toArray =
      (Gated.get h state.pending_deposits).toArray.push (depositRequestPending dr state.slot) := by
  rw [processDepositRequest_eq h] at hp
  unfold SszList.push at hp
  split at hp
  · cases hp
    simp only [Gated.get_mk]
  · cases hp

/-- On success the start index is `depositRequestStartIndex f old dr`: set to the request's index
before Fulu when it was unset, unchanged otherwise. -/
theorem processDepositRequest_startIndex (h : f.atLeast .electra = true)
    {state s' : BeaconState P f} {dr : DepositRequest} (hp : processDepositRequest state dr = .ok s') :
    Gated.get h s'.deposit_requests_start_index =
      depositRequestStartIndex f (Gated.get h state.deposit_requests_start_index) dr := by
  rw [processDepositRequest_eq h] at hp
  unfold SszList.push at hp
  split at hp
  · cases hp
    simp only [Gated.get_mk]
  · cases hp

/-- On success every field other than the pending-deposit queue and the start index is unchanged:
`process_deposit_request` credits nothing and touches no validator. -/
theorem processDepositRequest_frame (h : f.atLeast .electra = true)
    {state s' : BeaconState P f} {dr : DepositRequest} (hp : processDepositRequest state dr = .ok s') :
    s' = { state with
      deposit_requests_start_index := s'.deposit_requests_start_index
      pending_deposits := s'.pending_deposits } := by
  rw [processDepositRequest_eq h] at hp
  unfold SszList.push at hp
  split at hp
  · cases hp
    rfl
  · cases hp

/-! ## The deposit-requests loop of a block -/

/-- **Full specification of `foldDepositRequests`** (Electra and Fulu): on success, the
pending-deposit queue appends one `depositRequestPending dr state.slot` per request in order,
`deposit_requests_start_index` is the left fold of `depositRequestStartIndex f` over the requests,
and every other field of `BeaconState` (including `slot`, `validators`, `balances`,
`pending_consolidations`, `pending_partial_withdrawals`, `latest_execution_payload_header`, and
`latest_block_header`) is unchanged. -/
theorem foldDepositRequests_spec (h : f.atLeast .electra = true) :
    ∀ (drs : List DepositRequest) {state s' : BeaconState P f},
      foldDepositRequests state drs = .ok s' →
      (Gated.get h s'.pending_deposits).toArray =
        (Gated.get h state.pending_deposits).toArray ++
          (drs.map (depositRequestPending · state.slot)).toArray ∧
      Gated.get h s'.deposit_requests_start_index =
        drs.foldl (depositRequestStartIndex f) (Gated.get h state.deposit_requests_start_index) ∧
      s' = { state with
        deposit_requests_start_index := s'.deposit_requests_start_index
        pending_deposits := s'.pending_deposits } := by
  intro drs
  induction drs with
  | nil =>
    intro state s' hp
    cases hp
    exact ⟨by simp, rfl, rfl⟩
  | cons dr drs ih =>
    intro state s' hp
    unfold foldDepositRequests at hp
    rw [List.foldlM_cons] at hp
    cases h1 : processDepositRequest state dr with
    | error e => rw [h1] at hp; cases hp
    | ok s1 =>
      rw [h1] at hp
      obtain ⟨hq, hsi, hfr2⟩ := ih hp
      have hq1 := processDepositRequest_pending h h1
      have hsi1 := processDepositRequest_startIndex h h1
      have hfr1 := processDepositRequest_frame h h1
      have hslot1 : s1.slot = state.slot := by rw [hfr1]
      refine ⟨?_, ?_, ?_⟩
      · rw [hq, hq1, hslot1]
        apply Array.toList_inj.mp
        simp only [List.map_cons, Array.toList_append, Array.toList_push, List.append_assoc,
          List.singleton_append]
      · rw [hsi, List.foldl_cons, hsi1]
      · rw [hfr2, hfr1]

/-- **D-S9 fate, a block's requests**: on success the pending-deposit queue is the old queue
followed, positionally, by one `PendingDeposit` per request, each carrying that request's key,
credentials, amount and signature and the state's slot (the loop does not change the slot). -/
theorem foldDepositRequests_pending (h : f.atLeast .electra = true) :
    ∀ (drs : List DepositRequest) {state s' : BeaconState P f},
      foldDepositRequests state drs = .ok s' →
      (Gated.get h s'.pending_deposits).toArray =
        (Gated.get h state.pending_deposits).toArray ++
          (drs.map (depositRequestPending · state.slot)).toArray ∧
      s'.slot = state.slot ∧ s'.validators = state.validators ∧ s'.balances = state.balances := by
  intro drs state s' hp
  obtain ⟨hq, -, hfr⟩ := foldDepositRequests_spec h drs hp
  exact ⟨hq, by rw [hfr], by rw [hfr], by rw [hfr]⟩

/-- Named field projections preserved across `foldDepositRequests`. -/
theorem foldDepositRequests_frames (h : f.atLeast .electra = true)
    {drs : List DepositRequest} {state s' : BeaconState P f}
    (hp : foldDepositRequests state drs = .ok s') :
    s'.slot = state.slot ∧
    s'.validators = state.validators ∧
    s'.balances = state.balances ∧
    s'.pending_consolidations = state.pending_consolidations ∧
    s'.pending_partial_withdrawals = state.pending_partial_withdrawals ∧
    s'.latest_execution_payload_header = state.latest_execution_payload_header ∧
    s'.latest_block_header = state.latest_block_header := by
  obtain ⟨-, -, hfr⟩ := foldDepositRequests_spec h drs hp
  exact ⟨by rw [hfr], by rw [hfr], by rw [hfr], by rw [hfr], by rw [hfr], by rw [hfr], by rw [hfr]⟩

end JauneConsensus.Facts
