import JauneConsensus.Block

/-!
# The outcome of `process_withdrawal_request`, as a reusable characterization

About `JauneConsensus.processWithdrawalRequest` (`JauneConsensus/Block.lean`):
the one-request step lemma for the EIP-7002 cross-layer properties P1 and P2.
`classifyWithdrawalRequest` computes, with the same reads and the same checked
arithmetic as the function, which outcome a request has, without changing state;
`applyWithdrawalOutcome` carries out the state change of each outcome; the main
theorem says the function is their bind-composition.
-/

namespace JauneConsensus.Facts

variable {P : Preset} {f : CFork}

/-- Why `process_withdrawal_request` ignored a request: one constructor per early
return, in the code's order. The final partial gate
(`has_compounding_withdrawal_credential(validator) and
has_sufficient_effective_balance and has_excess_balance`) is split into its
three conjuncts, in order. -/
inductive WithdrawalIgnoreReason where
  /-- `len(state.pending_partial_withdrawals) == PENDING_PARTIAL_WITHDRAWALS_LIMIT
  and not is_full_exit_request`: "If partial withdrawal queue is full, only full
  exits are processed". -/
  | partialQueueFull
  /-- `withdrawal_request.validator_pubkey not in validator_pubkeys`: "If no
  validator with the given pubkey exists, return". -/
  | unknownPubkey
  /-- `not (has_correct_credential and is_correct_source_address)`: the validator
  lacks an execution withdrawal credential, or the request source is not the
  credential address (`validator.withdrawal_credentials[12:]`). -/
  | badCredentialOrSource
  /-- `not is_active_validator(validator, current_epoch)`. -/
  | notActive
  /-- `validator.exit_epoch != FAR_FUTURE_EPOCH`. -/
  | alreadyExiting
  /-- `current_epoch < validator.activation_epoch + SHARD_COMMITTEE_PERIOD`:
  "Verify the withdrawable epoch and exit epoch". -/
  | tooEarly
  /-- A full exit (`amount == FULL_EXIT_REQUEST_AMOUNT`) with
  `pending_balance_to_withdraw != 0`: the `return` past the
  `if pending_balance_to_withdraw == 0: initiate_validator_exit(state, index)`. -/
  | fullExitPendingBalance
  /-- A partial withdrawal whose validator lacks a compounding credential
  (`has_compounding_withdrawal_credential(validator)` is false). -/
  | notCompounding
  /-- A partial withdrawal with
  `validator.effective_balance < MIN_ACTIVATION_BALANCE` ("Only check min
  activation balance for partial withdrawals"). -/
  | insufficientEffectiveBalance
  /-- A partial withdrawal with
  `state.balances[validator_index] <= MIN_ACTIVATION_BALANCE +
  pending_balance_to_withdraw` (no excess balance). -/
  | noExcess
  deriving DecidableEq, Repr

/-- What `process_withdrawal_request` does to one request. -/
inductive WithdrawalOutcome where
  /-- The request is ignored, for exactly one reason. -/
  | ignored (r : WithdrawalIgnoreReason)
  /-- A full exit is initiated for the validator at `index`. -/
  | fullExit (index : ValidatorIndex)
  /-- A pending partial withdrawal of `toWithdraw` is appended for `index`. -/
  | partialWithdrawal (index : ValidatorIndex) (toWithdraw : Gwei)
  deriving DecidableEq, Repr

/-- Which outcome `process_withdrawal_request` gives `wr`, computed with the same
reads and the same checked arithmetic as the function. Changes no state. -/
def classifyWithdrawalRequest (cfg : Config) (state : BeaconState P f)
    (wr : WithdrawalRequest) : M WithdrawalOutcome := do
  let site := "process_withdrawal_request"
  let amount := wr.amount
  let isFullExit := amount == FULL_EXIT_REQUEST_AMOUNT
  if (← state.pendingPartialWithdrawals).length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT && !isFullExit then
    return .ignored .partialQueueFull
  let some index ← validatorIndexOf state wr.validator_pubkey | return .ignored .unknownPubkey
  let validator ← state.validators.get index.toNat site
  let hasCorrectCredential := hasExecutionWithdrawalCredential validator
  let isCorrectSource := validator.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes
  if !(hasCorrectCredential && isCorrectSource) then return .ignored .badCredentialOrSource
  let current ← getCurrentEpoch state
  if !isActiveValidator validator current then return .ignored .notActive
  if validator.exit_epoch != FAR_FUTURE_EPOCH then return .ignored .alreadyExiting
  if current < (← U64.add? validator.activation_epoch (← c64 cfg.SHARD_COMMITTEE_PERIOD) site) then
    return .ignored .tooEarly
  let pendingBalance ← getPendingBalanceToWithdraw state index
  if isFullExit then
    if pendingBalance == U64.zero then return .fullExit index
    return .ignored .fullExitPendingBalance
  let minAct ← c64 P.MIN_ACTIVATION_BALANCE
  let balance ← state.balances.get index.toNat site
  let sufficient := minAct ≤ validator.effective_balance
  let excess := (← U64.add? minAct pendingBalance site) < balance
  if hasCompoundingWithdrawalCredential validator && sufficient && excess then
    let avail ← U64.sub? (← U64.sub? balance minAct site) pendingBalance site
    let toWithdraw := if avail < amount then avail else amount
    return .partialWithdrawal index toWithdraw
  else if !(hasCompoundingWithdrawalCredential validator) then return .ignored .notCompounding
  else if !(decide (minAct ≤ validator.effective_balance)) then
    return .ignored .insufficientEffectiveBalance
  else return .ignored .noExcess

/-- The state change of each outcome: `ignored` is the identity, `fullExit`
initiates the exit, `partialWithdrawal` appends the pending entry. -/
def applyWithdrawalOutcome (cfg : Config) (state : BeaconState P f) (_wr : WithdrawalRequest) :
    WithdrawalOutcome → M (BeaconState P f)
  | .ignored _ => pure state
  | .fullExit index => initiateValidatorExit cfg state index
  | .partialWithdrawal index toWithdraw => do
    let site := "process_withdrawal_request"
    let (state, exitQueueEpoch) ← computeExitEpochAndUpdateChurn cfg state toWithdraw
    let withdrawable ← U64.add? exitQueueEpoch (← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY) site
    let pending ← (← state.pendingPartialWithdrawals).push
      { validator_index := index, amount := toWithdraw, withdrawable_epoch := withdrawable } site
    state.setPendingPartialWithdrawals pending

/-- `bind` on an `ok` result, as a rewrite: substitutes the value into the
continuation. (The core `pure_bind` simp lemma does not fire here because the
scrutinee is the `Except.ok` constructor, not `pure`.) -/
private theorem bind_ok_cons {α β ε : Type} (a : α) (k : α → Except ε β) :
    Bind.bind (Except.ok a) k = k a := rfl

/-- `bind` on an `error` result, as a rewrite. -/
private theorem bind_err_cons {α β ε : Type} (e : ε) (k : α → Except ε β) :
    Bind.bind (Except.error e) k = Except.error e := rfl

/-- Inversion for one `bind` layer: from a successful bind, the scrutinee
succeeded and the continuation did too. -/
private theorem bind_ok_inv {α β ε : Type} {m : Except ε α} {f : α → Except ε β}
    {y : β} (h : Bind.bind m f = .ok y) : ∃ a, m = .ok a ∧ f a = .ok y := by
  cases m with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => rw [bind_err_cons] at h; cases h

/-- Equational characterization: the function is classify-then-apply. -/
theorem processWithdrawalRequest_eq (cfg : Config) (state : BeaconState P f)
    (wr : WithdrawalRequest) :
    processWithdrawalRequest cfg state wr =
      classifyWithdrawalRequest cfg state wr >>= applyWithdrawalOutcome cfg state wr := by
  unfold processWithdrawalRequest classifyWithdrawalRequest applyWithdrawalOutcome
  dsimp only
  cases h1 : state.pendingPartialWithdrawals with
  | error e => rfl
  | ok q1 =>
    simp only [bind_ok_cons]
    cases hb1 : (q1.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) with
    | true => rfl
    | false =>
      cases h2 : validatorIndexOf state wr.validator_pubkey with
      | error e => rfl
      | ok v2 =>
        simp only [bind_ok_cons]
        cases v2 with
        | none => rfl
        | some index =>
          dsimp only
          cases h3 : state.validators.get (U64.toNat index)
            "process_withdrawal_request" with
          | error e => rfl
          | ok validator =>
            simp only [bind_ok_cons]
            cases hb3 : (!(hasExecutionWithdrawalCredential validator &&
              validator.withdrawal_credentials.toBytes.drop 12 ==
                wr.source_address.toBytes)) with
            | true => rfl
            | false =>
              cases h4 : getCurrentEpoch state with
              | error e => rfl
              | ok current =>
                simp only [bind_ok_cons]
                cases hb4 : (!isActiveValidator validator current) with
                | true => rfl
                | false =>
                  cases hb5 : (validator.exit_epoch != FAR_FUTURE_EPOCH) with
                  | true => rfl
                  | false =>
                    cases h5a : c64 cfg.SHARD_COMMITTEE_PERIOD with
                    | error e => rfl
                    | ok period =>
                      simp only [bind_ok_cons]
                      cases h5b : U64.add? validator.activation_epoch period
                        "process_withdrawal_request" with
                      | error e => rfl
                      | ok actSum =>
                        simp only [bind_ok_cons]
                        by_cases hc6 : (current < actSum)
                        · rw [ite_eq_left hc6, ite_eq_left hc6]
                          rfl
                        · rw [ite_eq_right hc6, ite_eq_right hc6]
                          cases h6 : getPendingBalanceToWithdraw state index with
                          | error e => rfl
                          | ok pendingBalance =>
                            simp only [bind_ok_cons]
                            cases hb7 : (wr.amount == FULL_EXIT_REQUEST_AMOUNT) with
                            | true =>
                              cases hb8 : (pendingBalance == U64.zero) with
                              | true => rfl
                              | false => rfl
                            | false =>
                              cases h7 : c64 P.MIN_ACTIVATION_BALANCE with
                              | error e => rfl
                              | ok minAct =>
                                simp only [bind_ok_cons]
                                cases h8 : state.balances.get (U64.toNat index)
                                  "process_withdrawal_request" with
                                | error e => rfl
                                | ok balance =>
                                  simp only [bind_ok_cons]
                                  cases h9 : U64.add? minAct pendingBalance
                                    "process_withdrawal_request" with
                                  | error e => rfl
                                  | ok sum =>
                                    simp only [bind_ok_cons]
                                    cases hc : hasCompoundingWithdrawalCredential
                                      validator with
                                    | false => rfl
                                    | true =>
                                      cases hd : decide
                                        (minAct ≤ validator.effective_balance) with
                                      | false => rfl
                                      | true =>
                                        cases he : decide (sum < balance) with
                                        | false => rfl
                                        | true =>
                                          cases h10 : U64.sub? balance minAct
                                            "process_withdrawal_request" with
                                          | error e => rfl
                                          | ok sub1 =>
                                            simp only [bind_ok_cons]
                                            cases h11 : U64.sub? sub1 pendingBalance
                                              "process_withdrawal_request" with
                                            | error e => rfl
                                            | ok avail => rfl

/-- An ignored request leaves the state unchanged. -/
theorem apply_ignored {cfg : Config} {state : BeaconState P f}
    {wr : WithdrawalRequest} {r : WithdrawalIgnoreReason} :
    applyWithdrawalOutcome cfg state wr (.ignored r) = pure state := rfl

/-- P1 step fact: a classifying `fullExit`/`partialWithdrawal` resolves the
request pubkey to `i` (first match, by `validatorIndexOf`'s `findIdx?`), and
the validator at `i` carries an execution withdrawal credential whose address
is the request source. -/
theorem classify_fullExit_or_partial_spec {cfg : Config} {state : BeaconState P f}
    {wr : WithdrawalRequest} {o : WithdrawalOutcome} {i : ValidatorIndex}
    (h : classifyWithdrawalRequest cfg state wr = .ok o)
    (ho : o = .fullExit i ∨ (∃ amt, o = .partialWithdrawal i amt)) :
    validatorIndexOf state wr.validator_pubkey = .ok (some i) ∧
    ∃ v, state.validators.get i.toNat "process_withdrawal_request" = .ok v ∧
      hasExecutionWithdrawalCredential v = true ∧
      v.withdrawal_credentials.toBytes.drop 12 = wr.source_address.toBytes := by
  rcases ho with rfl | ⟨amt, rfl⟩
  · unfold classifyWithdrawalRequest at h
    dsimp only at h
    obtain ⟨q1, h1ok, h1c⟩ := bind_ok_inv h
    by_cases hb1 : ((q1.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)
    · rw [ite_eq_left hb1] at h1c
      cases h1c
    · rw [ite_eq_right hb1] at h1c
      obtain ⟨v2, h2ok, h2c⟩ := bind_ok_inv h1c
      cases v2 with
      | none => cases h2c
      | some j =>
        dsimp only at h2c
        obtain ⟨validator, h3ok, h3c⟩ := bind_ok_inv h2c
        by_cases hb3 : ((!(hasExecutionWithdrawalCredential validator &&
          validator.withdrawal_credentials.toBytes.drop 12 ==
            wr.source_address.toBytes)) = true)
        · rw [ite_eq_left hb3] at h3c
          cases h3c
        · rw [ite_eq_right hb3] at h3c
          obtain ⟨current, h4ok, h4c⟩ := bind_ok_inv h3c
          by_cases hb4 : ((!isActiveValidator validator current) = true)
          · rw [ite_eq_left hb4] at h4c
            cases h4c
          · rw [ite_eq_right hb4] at h4c
            by_cases hb5 : ((validator.exit_epoch != FAR_FUTURE_EPOCH) = true)
            · rw [ite_eq_left hb5] at h4c
              cases h4c
            · rw [ite_eq_right hb5] at h4c
              obtain ⟨period, h5aok, h5ac⟩ := bind_ok_inv h4c
              obtain ⟨actSum, h5bok, h5bc⟩ := bind_ok_inv h5ac
              by_cases hc6 : (current < actSum)
              · rw [ite_eq_left hc6] at h5bc
                cases h5bc
              · rw [ite_eq_right hc6] at h5bc
                obtain ⟨pendingBalance, h6ok, h6c⟩ := bind_ok_inv h5bc
                by_cases hb7 : ((wr.amount == FULL_EXIT_REQUEST_AMOUNT) = true)
                · rw [ite_eq_left hb7] at h6c
                  by_cases hb8 : ((pendingBalance == U64.zero) = true)
                  · rw [ite_eq_left hb8] at h6c
                    cases h6c
                    have hXY : (hasExecutionWithdrawalCredential validator &&
                      validator.withdrawal_credentials.toBytes.drop 12 ==
                        wr.source_address.toBytes) = true := by
                      simpa using hb3
                    obtain ⟨hX, hY⟩ := Bool.and_eq_true_iff.mp hXY
                    exact ⟨h2ok, validator, h3ok, hX, beq_iff_eq.mp hY⟩
                  · rw [ite_eq_right hb8] at h6c
                    cases h6c
                · rw [ite_eq_right hb7] at h6c
                  obtain ⟨minAct, h7ok, h7c⟩ := bind_ok_inv h6c
                  obtain ⟨balance, h8ok, h8c⟩ := bind_ok_inv h7c
                  obtain ⟨sum, h9ok, h9c⟩ := bind_ok_inv h8c
                  by_cases hg : ((hasCompoundingWithdrawalCredential validator &&
                    decide (minAct ≤ validator.effective_balance) &&
                    decide (sum < balance)) = true)
                  · rw [ite_eq_left hg] at h9c
                    obtain ⟨sub1, h10ok, h10c⟩ := bind_ok_inv h9c
                    obtain ⟨avail, h11ok, h11c⟩ := bind_ok_inv h10c
                    cases h11c
                  · rw [ite_eq_right hg] at h9c
                    by_cases hr1 : ((!hasCompoundingWithdrawalCredential validator)
                      = true)
                    · rw [ite_eq_left hr1] at h9c
                      cases h9c
                    · rw [ite_eq_right hr1] at h9c
                      by_cases hr2 : ((!decide
                        (minAct ≤ validator.effective_balance)) = true)
                      · rw [ite_eq_left hr2] at h9c
                        cases h9c
                      · rw [ite_eq_right hr2] at h9c
                        cases h9c
  · unfold classifyWithdrawalRequest at h
    dsimp only at h
    obtain ⟨q1, h1ok, h1c⟩ := bind_ok_inv h
    by_cases hb1 : ((q1.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)
    · rw [ite_eq_left hb1] at h1c
      cases h1c
    · rw [ite_eq_right hb1] at h1c
      obtain ⟨v2, h2ok, h2c⟩ := bind_ok_inv h1c
      cases v2 with
      | none => cases h2c
      | some j =>
        dsimp only at h2c
        obtain ⟨validator, h3ok, h3c⟩ := bind_ok_inv h2c
        by_cases hb3 : ((!(hasExecutionWithdrawalCredential validator &&
          validator.withdrawal_credentials.toBytes.drop 12 ==
            wr.source_address.toBytes)) = true)
        · rw [ite_eq_left hb3] at h3c
          cases h3c
        · rw [ite_eq_right hb3] at h3c
          obtain ⟨current, h4ok, h4c⟩ := bind_ok_inv h3c
          by_cases hb4 : ((!isActiveValidator validator current) = true)
          · rw [ite_eq_left hb4] at h4c
            cases h4c
          · rw [ite_eq_right hb4] at h4c
            by_cases hb5 : ((validator.exit_epoch != FAR_FUTURE_EPOCH) = true)
            · rw [ite_eq_left hb5] at h4c
              cases h4c
            · rw [ite_eq_right hb5] at h4c
              obtain ⟨period, h5aok, h5ac⟩ := bind_ok_inv h4c
              obtain ⟨actSum, h5bok, h5bc⟩ := bind_ok_inv h5ac
              by_cases hc6 : (current < actSum)
              · rw [ite_eq_left hc6] at h5bc
                cases h5bc
              · rw [ite_eq_right hc6] at h5bc
                obtain ⟨pendingBalance, h6ok, h6c⟩ := bind_ok_inv h5bc
                by_cases hb7 : ((wr.amount == FULL_EXIT_REQUEST_AMOUNT) = true)
                · rw [ite_eq_left hb7] at h6c
                  by_cases hb8 : ((pendingBalance == U64.zero) = true)
                  · rw [ite_eq_left hb8] at h6c
                    cases h6c
                  · rw [ite_eq_right hb8] at h6c
                    cases h6c
                · rw [ite_eq_right hb7] at h6c
                  obtain ⟨minAct, h7ok, h7c⟩ := bind_ok_inv h6c
                  obtain ⟨balance, h8ok, h8c⟩ := bind_ok_inv h7c
                  obtain ⟨sum, h9ok, h9c⟩ := bind_ok_inv h8c
                  by_cases hg : ((hasCompoundingWithdrawalCredential validator &&
                    decide (minAct ≤ validator.effective_balance) &&
                    decide (sum < balance)) = true)
                  · rw [ite_eq_left hg] at h9c
                    obtain ⟨sub1, h10ok, h10c⟩ := bind_ok_inv h9c
                    obtain ⟨avail, h11ok, h11c⟩ := bind_ok_inv h10c
                    cases h11c
                    have hXY : (hasExecutionWithdrawalCredential validator &&
                      validator.withdrawal_credentials.toBytes.drop 12 ==
                        wr.source_address.toBytes) = true := by
                      simpa using hb3
                    obtain ⟨hX, hY⟩ := Bool.and_eq_true_iff.mp hXY
                    exact ⟨h2ok, validator, h3ok, hX, beq_iff_eq.mp hY⟩
                  · rw [ite_eq_right hg] at h9c
                    by_cases hr1 : ((!hasCompoundingWithdrawalCredential
                      validator) = true)
                    · rw [ite_eq_left hr1] at h9c
                      cases h9c
                    · rw [ite_eq_right hr1] at h9c
                      by_cases hr2 : ((!decide
                        (minAct ≤ validator.effective_balance)) = true)
                      · rw [ite_eq_left hr2] at h9c
                        cases h9c
                      · rw [ite_eq_right hr2] at h9c
                        cases h9c

/-- P2 step fact: a classifying `partialWithdrawal` withdraws
`min (balance − MIN_ACTIVATION_BALANCE − pending) wr.amount` (in `Nat`), with
`balance` and `pending` read from `state`, and the amount is nonzero (hence not
a full exit). -/
theorem classify_partial_amount {cfg : Config} {state : BeaconState P f}
    {wr : WithdrawalRequest} {i : ValidatorIndex} {amt : Gwei}
    (h : classifyWithdrawalRequest cfg state wr = .ok (.partialWithdrawal i amt)) :
    ∃ balance pending, state.balances.get i.toNat "process_withdrawal_request" = .ok balance ∧
      getPendingBalanceToWithdraw state i = .ok pending ∧
      amt.toNat = min (balance.toNat - P.MIN_ACTIVATION_BALANCE - pending.toNat) wr.amount.toNat ∧
      wr.amount ≠ U64.zero := by
  unfold classifyWithdrawalRequest at h
  dsimp only at h
  obtain ⟨q1, h1ok, h1c⟩ := bind_ok_inv h
  by_cases hb1 : ((q1.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
    !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)
  · rw [ite_eq_left hb1] at h1c
    cases h1c
  · rw [ite_eq_right hb1] at h1c
    obtain ⟨v2, h2ok, h2c⟩ := bind_ok_inv h1c
    cases v2 with
    | none => cases h2c
    | some j =>
      dsimp only at h2c
      obtain ⟨validator, h3ok, h3c⟩ := bind_ok_inv h2c
      by_cases hb3 : ((!(hasExecutionWithdrawalCredential validator &&
        validator.withdrawal_credentials.toBytes.drop 12 ==
          wr.source_address.toBytes)) = true)
      · rw [ite_eq_left hb3] at h3c
        cases h3c
      · rw [ite_eq_right hb3] at h3c
        obtain ⟨current, h4ok, h4c⟩ := bind_ok_inv h3c
        by_cases hb4 : ((!isActiveValidator validator current) = true)
        · rw [ite_eq_left hb4] at h4c
          cases h4c
        · rw [ite_eq_right hb4] at h4c
          by_cases hb5 : ((validator.exit_epoch != FAR_FUTURE_EPOCH) = true)
          · rw [ite_eq_left hb5] at h4c
            cases h4c
          · rw [ite_eq_right hb5] at h4c
            obtain ⟨period, h5aok, h5ac⟩ := bind_ok_inv h4c
            obtain ⟨actSum, h5bok, h5bc⟩ := bind_ok_inv h5ac
            by_cases hc6 : (current < actSum)
            · rw [ite_eq_left hc6] at h5bc
              cases h5bc
            · rw [ite_eq_right hc6] at h5bc
              obtain ⟨pendingBalance, h6ok, h6c⟩ := bind_ok_inv h5bc
              by_cases hb7 : ((wr.amount == FULL_EXIT_REQUEST_AMOUNT) = true)
              · rw [ite_eq_left hb7] at h6c
                by_cases hb8 : ((pendingBalance == U64.zero) = true)
                · rw [ite_eq_left hb8] at h6c
                  cases h6c
                · rw [ite_eq_right hb8] at h6c
                  cases h6c
              · rw [ite_eq_right hb7] at h6c
                obtain ⟨minAct, h7ok, h7c⟩ := bind_ok_inv h6c
                obtain ⟨balance, h8ok, h8c⟩ := bind_ok_inv h7c
                obtain ⟨sum, h9ok, h9c⟩ := bind_ok_inv h8c
                by_cases hg : ((hasCompoundingWithdrawalCredential validator &&
                  decide (minAct ≤ validator.effective_balance) &&
                  decide (sum < balance)) = true)
                · rw [ite_eq_left hg] at h9c
                  obtain ⟨sub1, h10ok, h10c⟩ := bind_ok_inv h9c
                  obtain ⟨avail, h11ok, h11c⟩ := bind_ok_inv h10c
                  cases h11c
                  refine ⟨balance, pendingBalance, h8ok, h6ok, ?_, ?_⟩
                  · have hMinAct : minAct.toNat = P.MIN_ACTIVATION_BALANCE :=
                      U64.toNat_ofNat? h7ok
                    have hAvail : avail.toNat = sub1.toNat - pendingBalance.toNat :=
                      U64.toNat_sub? h11ok
                    have hSub1 : sub1.toNat = balance.toNat - minAct.toNat :=
                      U64.toNat_sub? h10ok
                    rw [U64.toNat_min, hAvail, hSub1, hMinAct]
                  · intro hcon
                    have hcon' : wr.amount = FULL_EXIT_REQUEST_AMOUNT := hcon
                    exact absurd (U64.beq_eq_true_iff.mpr hcon') hb7
                · rw [ite_eq_right hg] at h9c
                  by_cases hr1 : ((!hasCompoundingWithdrawalCredential
                    validator) = true)
                  · rw [ite_eq_left hr1] at h9c
                    cases h9c
                  · rw [ite_eq_right hr1] at h9c
                    by_cases hr2 : ((!decide
                      (minAct ≤ validator.effective_balance)) = true)
                    · rw [ite_eq_left hr2] at h9c
                      cases h9c
                    · rw [ite_eq_right hr2] at h9c
                      cases h9c

/-- `fullExit` happens iff the amount is the full-exit amount, no earlier
reason fires, and no balance is already pending. -/
theorem classify_fullExit_iff {cfg : Config} {state : BeaconState P f}
    {wr : WithdrawalRequest} {i : ValidatorIndex} :
    classifyWithdrawalRequest cfg state wr = .ok (.fullExit i) ↔
      wr.amount = FULL_EXIT_REQUEST_AMOUNT ∧
      (∃ q, state.pendingPartialWithdrawals = .ok q) ∧
      validatorIndexOf state wr.validator_pubkey = .ok (some i) ∧
      (∃ v, state.validators.get i.toNat "process_withdrawal_request" = .ok v ∧
        hasExecutionWithdrawalCredential v = true ∧
        v.withdrawal_credentials.toBytes.drop 12 = wr.source_address.toBytes ∧
        (∃ current, getCurrentEpoch state = .ok current ∧
          isActiveValidator v current = true ∧
          v.exit_epoch = FAR_FUTURE_EPOCH ∧
          (∃ period, c64 cfg.SHARD_COMMITTEE_PERIOD = .ok period ∧
            (∃ actSum, U64.add? v.activation_epoch period
              "process_withdrawal_request" = .ok actSum ∧
              ¬ (current < actSum))))) ∧
      getPendingBalanceToWithdraw state i = .ok U64.zero := by
  constructor
  · intro h
    unfold classifyWithdrawalRequest at h
    dsimp only at h
    obtain ⟨q1, h1ok, h1c⟩ := bind_ok_inv h
    by_cases hb1 : ((q1.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)
    · rw [ite_eq_left hb1] at h1c
      cases h1c
    · rw [ite_eq_right hb1] at h1c
      obtain ⟨v2, h2ok, h2c⟩ := bind_ok_inv h1c
      cases v2 with
      | none => cases h2c
      | some j =>
        dsimp only at h2c
        obtain ⟨validator, h3ok, h3c⟩ := bind_ok_inv h2c
        by_cases hb3 : ((!(hasExecutionWithdrawalCredential validator &&
          validator.withdrawal_credentials.toBytes.drop 12 ==
            wr.source_address.toBytes)) = true)
        · rw [ite_eq_left hb3] at h3c
          cases h3c
        · rw [ite_eq_right hb3] at h3c
          obtain ⟨current, h4ok, h4c⟩ := bind_ok_inv h3c
          by_cases hb4 : ((!isActiveValidator validator current) = true)
          · rw [ite_eq_left hb4] at h4c
            cases h4c
          · rw [ite_eq_right hb4] at h4c
            by_cases hb5 : ((validator.exit_epoch != FAR_FUTURE_EPOCH) = true)
            · rw [ite_eq_left hb5] at h4c
              cases h4c
            · rw [ite_eq_right hb5] at h4c
              obtain ⟨period, h5aok, h5ac⟩ := bind_ok_inv h4c
              obtain ⟨actSum, h5bok, h5bc⟩ := bind_ok_inv h5ac
              by_cases hc6 : (current < actSum)
              · rw [ite_eq_left hc6] at h5bc
                cases h5bc
              · rw [ite_eq_right hc6] at h5bc
                obtain ⟨pendingBalance, h6ok, h6c⟩ := bind_ok_inv h5bc
                by_cases hb7 : ((wr.amount == FULL_EXIT_REQUEST_AMOUNT) = true)
                · rw [ite_eq_left hb7] at h6c
                  by_cases hb8 : ((pendingBalance == U64.zero) = true)
                  · rw [ite_eq_left hb8] at h6c
                    cases h6c
                    have hXY : (hasExecutionWithdrawalCredential validator &&
                      validator.withdrawal_credentials.toBytes.drop 12 ==
                        wr.source_address.toBytes) = true := by
                      simpa using hb3
                    obtain ⟨hX, hY⟩ := Bool.and_eq_true_iff.mp hXY
                    have hact : isActiveValidator validator current = true := by
                      simpa using hb4
                    have hb5' : ¬((!(validator.exit_epoch ==
                      FAR_FUTURE_EPOCH)) = true) := hb5
                    have hexit : validator.exit_epoch = FAR_FUTURE_EPOCH := by
                      have h2 : (validator.exit_epoch ==
                        FAR_FUTURE_EPOCH) = true := by simpa using hb5'
                      exact U64.beq_eq_true_iff.mp h2
                    have hpb : pendingBalance = U64.zero :=
                      U64.beq_eq_true_iff.mp hb8
                    have h6ok' : getPendingBalanceToWithdraw state i =
                        .ok U64.zero := hpb ▸ h6ok
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · exact U64.beq_eq_true_iff.mp hb7
                    · exact ⟨q1, h1ok⟩
                    · exact h2ok
                    · exact ⟨validator, h3ok, hX, beq_iff_eq.mp hY, current,
                        h4ok, hact, hexit, period, h5aok, actSum, h5bok,
                        hc6⟩
                    · exact h6ok'
                  · rw [ite_eq_right hb8] at h6c
                    cases h6c
                · rw [ite_eq_right hb7] at h6c
                  obtain ⟨minAct, h7ok, h7c⟩ := bind_ok_inv h6c
                  obtain ⟨balance, h8ok, h8c⟩ := bind_ok_inv h7c
                  obtain ⟨sum, h9ok, h9c⟩ := bind_ok_inv h8c
                  by_cases hg : ((hasCompoundingWithdrawalCredential validator &&
                    decide (minAct ≤ validator.effective_balance) &&
                    decide (sum < balance)) = true)
                  · rw [ite_eq_left hg] at h9c
                    obtain ⟨sub1, h10ok, h10c⟩ := bind_ok_inv h9c
                    obtain ⟨avail, h11ok, h11c⟩ := bind_ok_inv h10c
                    cases h11c
                  · rw [ite_eq_right hg] at h9c
                    by_cases hr1 : ((!hasCompoundingWithdrawalCredential
                      validator) = true)
                    · rw [ite_eq_left hr1] at h9c
                      cases h9c
                    · rw [ite_eq_right hr1] at h9c
                      by_cases hr2 : ((!decide
                        (minAct ≤ validator.effective_balance)) = true)
                      · rw [ite_eq_left hr2] at h9c
                        cases h9c
                      · rw [ite_eq_right hr2] at h9c
                        cases h9c
  · rintro ⟨hamt, hB, hlook, hD, hpend⟩
    obtain ⟨q, hq⟩ := hB
    obtain ⟨v, hget, hcred, hsrc, hE⟩ := hD
    obtain ⟨current, hcur, hact, hexit, hF⟩ := hE
    obtain ⟨period, h5a, hK2⟩ := hF
    obtain ⟨actSum, h5b, hnotearly⟩ := hK2
    have hnotfull : (!(FULL_EXIT_REQUEST_AMOUNT ==
      FULL_EXIT_REQUEST_AMOUNT)) = false := by decide
    have hbeqT : (FULL_EXIT_REQUEST_AMOUNT ==
      FULL_EXIT_REQUEST_AMOUNT) = true := U64.beq_eq_true_iff.mpr rfl
    have hY : (v.withdrawal_credentials.toBytes.drop 12 ==
      wr.source_address.toBytes) = true := by
      rw [hsrc]
      exact beq_self_eq_true _
    have hb8t : (U64.zero == U64.zero) = true := U64.beq_eq_true_iff.mpr rfl
    unfold classifyWithdrawalRequest
    dsimp only
    rw [hamt, hq, hlook]
    simp only [bind_ok_cons]
    rw [hget]
    rw [hcur]
    rw [h5a]
    simp only [bind_ok_cons]
    rw [h5b]
    simp only [hpend, bind_ok_cons]
    rw [ite_eq_right (show ¬((q.length ==
      P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(FULL_EXIT_REQUEST_AMOUNT == FULL_EXIT_REQUEST_AMOUNT)) = true) from by
      rw [hnotfull, Bool.and_false]; decide)]
    rw [ite_eq_right (show ¬((!(hasExecutionWithdrawalCredential v &&
      v.withdrawal_credentials.toBytes.drop 12 ==
        wr.source_address.toBytes)) = true) from by
      rw [hcred, hY]; decide)]
    rw [ite_eq_right (show ¬((!isActiveValidator v current) = true) from by
      rw [hact]; decide)]
    rw [ite_eq_right (show ¬(((v.exit_epoch !=
      FAR_FUTURE_EPOCH)) = true) from by rw [hexit]; decide)]
    rw [ite_eq_right hnotearly]
    rw [ite_eq_left hbeqT]
    rw [ite_eq_left hb8t]
    rfl

end JauneConsensus.Facts
