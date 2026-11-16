import JauneConsensus.Facts.DepositRequest
import JauneConsensus.Facts.ExpectedWithdrawals
import JauneConsensus.Facts.AnchorInv

/-!
# The outcome of `process_consolidation_request`, as a reusable characterization

About `JauneConsensus.processConsolidationRequest` and
`JauneConsensus.isValidSwitchToCompoundingRequest` (`JauneConsensus/Block.lean`), transcribed from
`v1.7.0-beta.4` `specs/electra/beacon-chain.md` (Fulu does not override either). In the shape of
`Facts/WithdrawalRequest.lean`: `classifyConsolidationRequest` computes, with the same reads and
the same checked arithmetic as the function and in the spec's order, which outcome a request has,
without changing state; `applyConsolidationOutcome` carries out the state change of each outcome;
`processConsolidationRequest_eq` says the function is their bind-composition. The per-outcome
lemmas then expose what the EIP-7251 cross-layer authorization (C-S9) needs: on a non-ignored
outcome the source key resolves to a validator whose withdrawal credential has an execution prefix
and carries the request's source address.

Nothing here edits a spec definition.
-/

namespace JauneConsensus.Facts

open JauneConsensus

variable {P : Preset} {f : CFork}

/-- Why `process_consolidation_request` ignored a request: one constructor per early return of
the consolidation path, in the spec's order. (The switch-to-compounding path is tried first; a
request it does not accept falls through to these checks.) -/
inductive ConsolidationIgnoreReason where
  /-- `consolidation_request.source_pubkey == consolidation_request.target_pubkey` (and the
  request is not a valid switch to compounding): "Verify that source != target, so a
  consolidation cannot be used as an exit". -/
  | sourceIsTarget
  /-- `len(state.pending_consolidations) == PENDING_CONSOLIDATIONS_LIMIT`. -/
  | queueFull
  /-- `get_consolidation_churn_limit(state) <= MIN_ACTIVATION_BALANCE`. -/
  | churnTooLow
  /-- `request_source_pubkey not in validator_pubkeys`. -/
  | unknownSource
  /-- `request_target_pubkey not in validator_pubkeys`. -/
  | unknownTarget
  /-- `not (has_execution_withdrawal_credential(source_validator) and
  source_validator.withdrawal_credentials[12:] == consolidation_request.source_address)`. -/
  | badSourceCredentialOrAddress
  /-- `not has_compounding_withdrawal_credential(target_validator)`. -/
  | targetNotCompounding
  /-- `not is_active_validator(source_validator, current_epoch)`. -/
  | sourceNotActive
  /-- `not is_active_validator(target_validator, current_epoch)`. -/
  | targetNotActive
  /-- `source_validator.exit_epoch != FAR_FUTURE_EPOCH`. -/
  | sourceExiting
  /-- `target_validator.exit_epoch != FAR_FUTURE_EPOCH`. -/
  | targetExiting
  /-- `current_epoch < source_validator.activation_epoch + SHARD_COMMITTEE_PERIOD`. -/
  | sourceTooEarly
  /-- `get_pending_balance_to_withdraw(state, source_index) > 0`. -/
  | sourcePendingWithdrawal
  deriving DecidableEq, Repr

/-- What `process_consolidation_request` does to one request. -/
inductive ConsolidationOutcome where
  /-- The request is ignored, for exactly one reason. -/
  | ignored (r : ConsolidationIgnoreReason)
  /-- `is_valid_switch_to_compounding_request` holds: the validator at `index` is switched to a
  compounding credential (`switch_to_compounding_validator`). -/
  | switchToCompounding (index : ValidatorIndex)
  /-- Every check passed: the source at `source` is set to exit and a pending consolidation from
  `source` to `target` is appended. -/
  | pendingConsolidation (source target : ValidatorIndex)
  deriving DecidableEq, Repr

/-- Which outcome `process_consolidation_request` gives `cr`, computed with the same reads and the
same checked arithmetic as the function, in the spec's order. Changes no state. -/
def classifyConsolidationRequest (cfg : Config) (state : BeaconState P f)
    (cr : ConsolidationRequest) : M ConsolidationOutcome := do
  let site := "process_consolidation_request"
  if ← isValidSwitchToCompoundingRequest state cr then
    let some sourceIndex ← validatorIndexOf state cr.source_pubkey
      | throw (.assert s!"{site}: validator_pubkeys.index")
    return .switchToCompounding sourceIndex
  if cr.source_pubkey == cr.target_pubkey then return .ignored .sourceIsTarget
  if (← state.pendingConsolidations).length == P.PENDING_CONSOLIDATIONS_LIMIT then
    return .ignored .queueFull
  if (← getConsolidationChurnLimit cfg state).toNat ≤ P.MIN_ACTIVATION_BALANCE then
    return .ignored .churnTooLow
  let some sourceIndex ← validatorIndexOf state cr.source_pubkey | return .ignored .unknownSource
  let some targetIndex ← validatorIndexOf state cr.target_pubkey | return .ignored .unknownTarget
  let source ← state.validators.get sourceIndex.toNat site
  let target ← state.validators.get targetIndex.toNat site
  if !(hasExecutionWithdrawalCredential source &&
      source.withdrawal_credentials.toBytes.drop 12 == cr.source_address.toBytes) then
    return .ignored .badSourceCredentialOrAddress
  if !hasCompoundingWithdrawalCredential target then return .ignored .targetNotCompounding
  let current ← getCurrentEpoch state
  if !isActiveValidator source current then return .ignored .sourceNotActive
  if !isActiveValidator target current then return .ignored .targetNotActive
  if source.exit_epoch != FAR_FUTURE_EPOCH then return .ignored .sourceExiting
  if target.exit_epoch != FAR_FUTURE_EPOCH then return .ignored .targetExiting
  if current < (← U64.add? source.activation_epoch (← c64 cfg.SHARD_COMMITTEE_PERIOD) site) then
    return .ignored .sourceTooEarly
  if U64.zero < (← getPendingBalanceToWithdraw state sourceIndex) then
    return .ignored .sourcePendingWithdrawal
  return .pendingConsolidation sourceIndex targetIndex

/-- The state change of each outcome: `ignored` is the identity, `switchToCompounding` is
`switch_to_compounding_validator`, `pendingConsolidation` charges the consolidation churn with the
source's effective balance, sets the source's exit and withdrawable epochs, and appends the
pending consolidation. -/
def applyConsolidationOutcome (cfg : Config) (state : BeaconState P f) (_cr : ConsolidationRequest) :
    ConsolidationOutcome → M (BeaconState P f)
  | .ignored _ => pure state
  | .switchToCompounding index => switchToCompoundingValidator state index
  | .pendingConsolidation sourceIndex targetIndex => do
    let site := "process_consolidation_request"
    let source ← state.validators.get sourceIndex.toNat site
    let (state, exitEpoch) ← computeConsolidationEpochAndUpdateChurn cfg state source.effective_balance
    let withdrawable ← U64.add? exitEpoch (← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY) site
    let source ← state.validators.get sourceIndex.toNat site
    let validators ← state.validators.set sourceIndex.toNat
      { source with exit_epoch := exitEpoch, withdrawable_epoch := withdrawable } site
    let state := { state with validators }
    let pending ← (← state.pendingConsolidations).push
      { source_index := sourceIndex, target_index := targetIndex } site
    state.setPendingConsolidations pending

/-- Equational characterization: the function is classify-then-apply. -/
theorem processConsolidationRequest_eq (cfg : Config) (state : BeaconState P f)
    (cr : ConsolidationRequest) :
    processConsolidationRequest cfg state cr =
      classifyConsolidationRequest cfg state cr >>= applyConsolidationOutcome cfg state cr := by
  unfold processConsolidationRequest classifyConsolidationRequest
  dsimp only
  cases h0 : isValidSwitchToCompoundingRequest state cr with
  | error e => rfl
  | ok b0 =>
    simp only [ok_bind']
    cases b0 with
    | true =>
      cases h0a : validatorIndexOf state cr.source_pubkey with
      | error e => rfl
      | ok v => cases v <;> rfl
    | false =>
      cases hb1 : (cr.source_pubkey == cr.target_pubkey) with
      | true => rfl
      | false =>
        cases h2 : state.pendingConsolidations with
        | error e => rfl
        | ok q =>
          simp only [ok_bind']
          cases hb2 : (q.length == P.PENDING_CONSOLIDATIONS_LIMIT) with
          | true => rfl
          | false =>
            cases h3 : getConsolidationChurnLimit cfg state with
            | error e => rfl
            | ok churn =>
              simp only [ok_bind']
              by_cases hc3 : churn.toNat ≤ P.MIN_ACTIVATION_BALANCE
              · rw [ite_eq_left hc3, ite_eq_left hc3]; rfl
              · rw [ite_eq_right hc3, ite_eq_right hc3]
                cases h4 : validatorIndexOf state cr.source_pubkey with
                | error e => rfl
                | ok vs =>
                  simp only [ok_bind']
                  cases vs with
                  | none => rfl
                  | some si =>
                    cases h5 : validatorIndexOf state cr.target_pubkey with
                    | error e => rfl
                    | ok vt =>
                      simp only [ok_bind']
                      cases vt with
                      | none => rfl
                      | some ti =>
                        dsimp only
                        cases h6 : state.validators.get si.toNat "process_consolidation_request" with
                        | error e => rfl
                        | ok source =>
                          simp only [ok_bind']
                          cases h7 : state.validators.get ti.toNat "process_consolidation_request" with
                          | error e => rfl
                          | ok target =>
                            simp only [ok_bind']
                            cases hb8 : (!(hasExecutionWithdrawalCredential source &&
                                source.withdrawal_credentials.toBytes.drop 12 ==
                                  cr.source_address.toBytes)) with
                            | true => rfl
                            | false =>
                              cases hb9 : (!hasCompoundingWithdrawalCredential target) with
                              | true => rfl
                              | false =>
                                cases h10 : getCurrentEpoch state with
                                | error e => rfl
                                | ok current =>
                                  simp only [ok_bind']
                                  cases hb11 : (!isActiveValidator source current) with
                                  | true => rfl
                                  | false =>
                                    cases hb12 : (!isActiveValidator target current) with
                                    | true => rfl
                                    | false =>
                                      cases hb13 : (source.exit_epoch != FAR_FUTURE_EPOCH) with
                                      | true => rfl
                                      | false =>
                                        cases hb14 : (target.exit_epoch != FAR_FUTURE_EPOCH) with
                                        | true => rfl
                                        | false =>
                                          cases h15 : c64 cfg.SHARD_COMMITTEE_PERIOD with
                                          | error e => rfl
                                          | ok period =>
                                            simp only [ok_bind']
                                            cases h16 : U64.add? source.activation_epoch period
                                              "process_consolidation_request" with
                                            | error e => rfl
                                            | ok actSum =>
                                              simp only [ok_bind']
                                              by_cases hc16 : current < actSum
                                              · rw [ite_eq_left hc16, ite_eq_left hc16]; rfl
                                              · rw [ite_eq_right hc16, ite_eq_right hc16]
                                                cases h17 : getPendingBalanceToWithdraw state si with
                                                | error e => rfl
                                                | ok pend =>
                                                  simp only [ok_bind']
                                                  by_cases hc17 : U64.zero < pend
                                                  · rw [ite_eq_left hc17, ite_eq_left hc17]; rfl
                                                  · rw [ite_eq_right hc17, ite_eq_right hc17]
                                                    simp only [Bool.false_eq_true, ite_false,
                                                      pure_bind, applyConsolidationOutcome, h6,
                                                      ok_bind']

/-- An ignored request leaves the state unchanged. -/
theorem applyConsolidation_ignored {cfg : Config} {state : BeaconState P f}
    {cr : ConsolidationRequest} {r : ConsolidationIgnoreReason} :
    applyConsolidationOutcome cfg state cr (.ignored r) = pure state := rfl

/-- A switch to compounding is `switch_to_compounding_validator` of the source. -/
theorem applyConsolidation_switch {cfg : Config} {state : BeaconState P f}
    {cr : ConsolidationRequest} {i : ValidatorIndex} :
    applyConsolidationOutcome cfg state cr (.switchToCompounding i) =
      switchToCompoundingValidator state i := rfl

/-- The function on a request whose classification is known is the outcome's state change. -/
theorem processConsolidationRequest_of_classify {cfg : Config} {state : BeaconState P f}
    {cr : ConsolidationRequest} {o : ConsolidationOutcome}
    (h : classifyConsolidationRequest cfg state cr = .ok o) :
    processConsolidationRequest cfg state cr = applyConsolidationOutcome cfg state cr o := by
  rw [processConsolidationRequest_eq, h]; rfl

/-- `==` on SSZ vectors of a lawful element type is equality. -/
theorem sszVector_beq_iff {α : Type} [BEq α] [LawfulBEq α] {n : Nat} {a b : SszVector α n} :
    (a == b) = true ↔ a = b := by
  show (a.toArray == b.toArray) = true ↔ a = b
  rw [beq_iff_eq]
  constructor
  · intro h
    cases a; cases b
    cases h
    rfl
  · intro h; rw [h]

/-! ## What a valid switch to compounding establishes -/

/-- What `is_valid_switch_to_compounding_request` returning `True` establishes, in the spec's
order: source and target keys are equal, the key resolves to `i` (first match), the validator at
`i` has credential address `cr.source_address` and the `0x01` (eth1) prefix, is active at the
current epoch, and has not initiated an exit. -/
def SwitchToCompoundingChecks (state : BeaconState P f) (cr : ConsolidationRequest)
    (i : ValidatorIndex) : Prop :=
  cr.source_pubkey = cr.target_pubkey ∧
  validatorIndexOf state cr.source_pubkey = .ok (some i) ∧
  ∃ v, state.validators.toArray[i.toNat]? = some v ∧
    v.withdrawal_credentials.toBytes.drop 12 = cr.source_address.toBytes ∧
    hasEth1WithdrawalCredential v = true ∧
    ∃ current, getCurrentEpoch state = .ok current ∧ isActiveValidator v current = true ∧
      v.exit_epoch = FAR_FUTURE_EPOCH

/-- `is_valid_switch_to_compounding_request` is true exactly when its checks hold, for the index
`validatorIndexOf` gives. -/
theorem isValidSwitch_true {state : BeaconState P f} {cr : ConsolidationRequest} :
    isValidSwitchToCompoundingRequest state cr = .ok true →
      ∃ i, SwitchToCompoundingChecks state cr i := by
  unfold isValidSwitchToCompoundingRequest SwitchToCompoundingChecks
  cases hb1 : (!(cr.source_pubkey == cr.target_pubkey)) with
  | true => intro h; cases h
  | false =>
    cases h2 : validatorIndexOf state cr.source_pubkey with
    | error e => intro h; cases h
    | ok vi =>
      simp only [ok_bind']
      cases vi with
      | none => intro h; cases h
      | some i =>
        dsimp only
        cases h3 : state.validators.get i.toNat "is_valid_switch_to_compounding_request" with
        | error e => intro h; cases h
        | ok v =>
          simp only [ok_bind']
          cases hb4 : (!(v.withdrawal_credentials.toBytes.drop 12 == cr.source_address.toBytes)) with
          | true => intro h; cases h
          | false =>
            cases hb5 : (!hasEth1WithdrawalCredential v) with
            | true => intro h; cases h
            | false =>
              cases h6 : getCurrentEpoch state with
              | error e => intro h; cases h
              | ok current =>
                simp only [ok_bind']
                cases hb7 : (!isActiveValidator v current) with
                | true => intro h; cases h
                | false =>
                  cases hb8 : (v.exit_epoch != FAR_FUTURE_EPOCH) with
                  | true => intro h; cases h
                  | false =>
                    intro _
                    simp only [beq_iff_eq, bne_eq_false_iff_eq, Bool.not_eq_eq_eq_not,
                      Bool.not_false] at hb1 hb4 hb5 hb7 hb8
                    exact ⟨i, sszVector_beq_iff.mp hb1, rfl, v, ssz_get_ok_iff.mp h3, hb4, hb5, current, rfl,
                      hb7, hb8⟩

/-! ## What a pending consolidation establishes -/

/-- Every check `process_consolidation_request` makes before appending a pending consolidation
from `s` to `t`, in the spec's order: the request is not a valid switch to compounding; source and
target keys differ; the queue has room; the consolidation churn exceeds `MIN_ACTIVATION_BALANCE`;
both keys resolve (first match) to `s` and `t`; the source has an execution (`0x01` or `0x02`)
credential whose address is `cr.source_address`; the target has a compounding (`0x02`) credential;
both are active and not exiting at the current epoch; the source has been active for
`SHARD_COMMITTEE_PERIOD`; and the source has no pending partial withdrawal balance. -/
def PendingConsolidationChecks (cfg : Config) (state : BeaconState P f)
    (cr : ConsolidationRequest) (s t : ValidatorIndex) : Prop :=
  isValidSwitchToCompoundingRequest state cr = .ok false ∧
  cr.source_pubkey ≠ cr.target_pubkey ∧
  (∃ q, state.pendingConsolidations = .ok q ∧ q.length ≠ P.PENDING_CONSOLIDATIONS_LIMIT) ∧
  (∃ churn, getConsolidationChurnLimit cfg state = .ok churn ∧
    P.MIN_ACTIVATION_BALANCE < churn.toNat) ∧
  validatorIndexOf state cr.source_pubkey = .ok (some s) ∧
  validatorIndexOf state cr.target_pubkey = .ok (some t) ∧
  ∃ vs vt, state.validators.toArray[s.toNat]? = some vs ∧
    state.validators.toArray[t.toNat]? = some vt ∧
    hasExecutionWithdrawalCredential vs = true ∧
    vs.withdrawal_credentials.toBytes.drop 12 = cr.source_address.toBytes ∧
    hasCompoundingWithdrawalCredential vt = true ∧
    ∃ current, getCurrentEpoch state = .ok current ∧
      isActiveValidator vs current = true ∧ isActiveValidator vt current = true ∧
      vs.exit_epoch = FAR_FUTURE_EPOCH ∧ vt.exit_epoch = FAR_FUTURE_EPOCH ∧
      (∃ period actSum, c64 cfg.SHARD_COMMITTEE_PERIOD = .ok period ∧
        U64.add? vs.activation_epoch period "process_consolidation_request" = .ok actSum ∧
        ¬ current < actSum) ∧
      (∃ pend, getPendingBalanceToWithdraw state s = .ok pend ∧ ¬ U64.zero < pend)

/-- The classification has the outcome its checks say: a switch only after
`is_valid_switch_to_compounding_request` is true, and a pending consolidation only after every
check of `PendingConsolidationChecks`. -/
theorem classifyConsolidation_spec {cfg : Config} {state : BeaconState P f} {cr : ConsolidationRequest}
    {o : ConsolidationOutcome} :
    classifyConsolidationRequest cfg state cr = .ok o →
      (∀ i, o = .switchToCompounding i →
        isValidSwitchToCompoundingRequest state cr = .ok true ∧
        validatorIndexOf state cr.source_pubkey = .ok (some i)) ∧
      (∀ s t, o = .pendingConsolidation s t → PendingConsolidationChecks cfg state cr s t) := by
  unfold classifyConsolidationRequest
  dsimp only
  cases h0 : isValidSwitchToCompoundingRequest state cr with
  | error e => intro h; cases h
  | ok b0 =>
    simp only [ok_bind']
    cases b0 with
    | true =>
      cases h0a : validatorIndexOf state cr.source_pubkey with
      | error e => intro h; cases h
      | ok v =>
        cases v with
        | none => intro h; cases h
        | some i =>
          intro h; cases h
          refine ⟨?_, ?_⟩
          · intro j hj; cases hj; exact ⟨rfl, rfl⟩
          · intro s t hst; cases hst
    | false =>
      cases hb1 : (cr.source_pubkey == cr.target_pubkey) with
      | true => intro h; cases h; exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
      | false =>
        cases h2 : state.pendingConsolidations with
        | error e => intro h; cases h
        | ok q =>
          simp only [ok_bind']
          cases hb2 : (q.length == P.PENDING_CONSOLIDATIONS_LIMIT) with
          | true => intro h; cases h; exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
          | false =>
            cases h3 : getConsolidationChurnLimit cfg state with
            | error e => intro h; cases h
            | ok churn =>
              simp only [ok_bind']
              by_cases hc3 : churn.toNat ≤ P.MIN_ACTIVATION_BALANCE
              · rw [ite_eq_left hc3]; intro h; cases h
                exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
              · rw [ite_eq_right hc3]
                cases h4 : validatorIndexOf state cr.source_pubkey with
                | error e => intro h; cases h
                | ok vs =>
                  simp only [ok_bind']
                  cases vs with
                  | none => intro h; cases h; exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
                  | some si =>
                    cases h5 : validatorIndexOf state cr.target_pubkey with
                    | error e => intro h; cases h
                    | ok vt =>
                      simp only [ok_bind']
                      cases vt with
                      | none =>
                        intro h; cases h; exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
                      | some ti =>
                        dsimp only
                        cases h6 : state.validators.get si.toNat "process_consolidation_request" with
                        | error e => intro h; cases h
                        | ok source =>
                          simp only [ok_bind']
                          cases h7 : state.validators.get ti.toNat "process_consolidation_request" with
                          | error e => intro h; cases h
                          | ok target =>
                            simp only [ok_bind']
                            cases hb8 : (!(hasExecutionWithdrawalCredential source &&
                                source.withdrawal_credentials.toBytes.drop 12 ==
                                  cr.source_address.toBytes)) with
                            | true =>
                              intro h; cases h; exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
                            | false =>
                              cases hb9 : (!hasCompoundingWithdrawalCredential target) with
                              | true =>
                                intro h; cases h
                                exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
                              | false =>
                                cases h10 : getCurrentEpoch state with
                                | error e => intro h; cases h
                                | ok current =>
                                  simp only [ok_bind']
                                  cases hb11 : (!isActiveValidator source current) with
                                  | true =>
                                    intro h; cases h
                                    exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
                                  | false =>
                                    cases hb12 : (!isActiveValidator target current) with
                                    | true =>
                                      intro h; cases h
                                      exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
                                    | false =>
                                      cases hb13 : (source.exit_epoch != FAR_FUTURE_EPOCH) with
                                      | true =>
                                        intro h; cases h
                                        exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
                                      | false =>
                                        cases hb14 : (target.exit_epoch != FAR_FUTURE_EPOCH) with
                                        | true =>
                                          intro h; cases h
                                          exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
                                        | false =>
                                          cases h15 : c64 cfg.SHARD_COMMITTEE_PERIOD with
                                          | error e => intro h; cases h
                                          | ok period =>
                                            simp only [ok_bind']
                                            cases h16 : U64.add? source.activation_epoch period
                                              "process_consolidation_request" with
                                            | error e => intro h; cases h
                                            | ok actSum =>
                                              simp only [ok_bind']
                                              by_cases hc16 : current < actSum
                                              · rw [ite_eq_left hc16]; intro h; cases h
                                                exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
                                              · rw [ite_eq_right hc16]
                                                cases h17 : getPendingBalanceToWithdraw state si with
                                                | error e => intro h; cases h
                                                | ok pend =>
                                                  simp only [ok_bind']
                                                  by_cases hc17 : U64.zero < pend
                                                  · rw [ite_eq_left hc17]; intro h; cases h
                                                    exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
                                                  · simp only [Bool.false_eq_true, ite_false,
                                                      ite_eq_right hc17]
                                                    intro h; cases h
                                                    refine ⟨(fun _ h => nomatch h), ?_⟩
                                                    intro s t hst
                                                    cases hst
                                                    have hne : cr.source_pubkey ≠ cr.target_pubkey := by
                                                      intro he
                                                      rw [sszVector_beq_iff.mpr he] at hb1
                                                      cases hb1
                                                    simp only [Bool.not_eq_false', beq_eq_false_iff_ne,
                                                      ne_eq, Bool.and_eq_true, beq_iff_eq] at hb2 hb8
                                                    simp only [Bool.not_eq_false'] at hb9 hb11 hb12
                                                    simp only [bne_eq_false_iff_eq] at hb13 hb14
                                                    exact ⟨h0, hne, ⟨q, h2, hb2⟩,
                                                      ⟨churn, h3, Nat.lt_of_not_le hc3⟩, h4, h5,
                                                      source, target, ssz_get_ok_iff.mp h6,
                                                      ssz_get_ok_iff.mp h7, hb8.1, hb8.2, hb9,
                                                      current, h10, hb11, hb12, hb13, hb14,
                                                      ⟨period, actSum, h15, h16, hc16⟩,
                                                      ⟨pend, h17, hc17⟩⟩

/-! ## Authorization (C-S9) -/

/-- **C-S9 authorization, one request**: whenever `process_consolidation_request` acts on a
request (any outcome other than an ignore), the request's source key resolves (first match) to a
validator index `i`, and the validator at `i` has an execution withdrawal credential (`0x01` or
`0x02`; the switch path requires `0x01`) whose address (`withdrawal_credentials[12:]`) is the
request's `source_address`. The outcome acts on `i`: it switches `i` to compounding or queues a
consolidation with source `i`. -/
theorem classifyConsolidation_authorized {cfg : Config} {state : BeaconState P f} {cr : ConsolidationRequest}
    {o : ConsolidationOutcome} (h : classifyConsolidationRequest cfg state cr = .ok o)
    (hno : ∀ r, o ≠ .ignored r) :
    ∃ i v, validatorIndexOf state cr.source_pubkey = .ok (some i) ∧
      state.validators.toArray[i.toNat]? = some v ∧
      hasExecutionWithdrawalCredential v = true ∧
      v.withdrawal_credentials.toBytes.drop 12 = cr.source_address.toBytes ∧
      (o = .switchToCompounding i ∨ ∃ t, o = .pendingConsolidation i t) := by
  have hs := classifyConsolidation_spec h
  cases o with
  | ignored r => exact absurd rfl (hno r)
  | switchToCompounding i =>
    obtain ⟨hvalid, hi⟩ := hs.1 i rfl
    obtain ⟨j, -, hj, v, hv, haddr, heth, -⟩ := isValidSwitch_true hvalid
    rw [hi] at hj
    cases hj
    refine ⟨i, v, hi, hv, ?_, haddr, .inl rfl⟩
    simp [hasExecutionWithdrawalCredential, heth]
  | pendingConsolidation si ti =>
    obtain ⟨-, -, -, -, hsi, -, vs, -, hvs, -, hex, haddr, -⟩ := hs.2 si ti rfl
    exact ⟨si, vs, hsi, hvs, hex, haddr, .inr ⟨ti, rfl⟩⟩

/-- **C-S9 authorization, negative form**: if the request's source key resolves to a validator
whose credential is not an execution credential carrying `cr.source_address`, the classification
is an ignore. -/
theorem classifyConsolidation_ignored_of_unauthorized {cfg : Config} {state : BeaconState P f}
    {cr : ConsolidationRequest} {o : ConsolidationOutcome} {i : ValidatorIndex} {v : Validator}
    (h : classifyConsolidationRequest cfg state cr = .ok o)
    (hi : validatorIndexOf state cr.source_pubkey = .ok (some i))
    (hv : state.validators.toArray[i.toNat]? = some v)
    (hbad : ¬ (hasExecutionWithdrawalCredential v = true ∧
      v.withdrawal_credentials.toBytes.drop 12 = cr.source_address.toBytes)) :
    ∃ r, o = .ignored r := by
  by_contra hno
  have hno' : ∀ r, o ≠ .ignored r := fun r hr => hno ⟨r, hr⟩
  obtain ⟨j, w, hj, hw, hex, haddr, -⟩ := classifyConsolidation_authorized h hno'
  rw [hi] at hj
  cases hj
  rw [hv] at hw
  cases hw
  exact hbad ⟨hex, haddr⟩

/-- **C-S9 negative control, as a theorem**: a request whose source credential does not carry the
request's source address (or is not an execution credential) leaves the state unchanged. -/
theorem processConsolidationRequest_unauthorized {cfg : Config} {state s' : BeaconState P f}
    {cr : ConsolidationRequest} {i : ValidatorIndex} {v : Validator}
    (hp : processConsolidationRequest cfg state cr = .ok s')
    (hi : validatorIndexOf state cr.source_pubkey = .ok (some i))
    (hv : state.validators.toArray[i.toNat]? = some v)
    (hbad : ¬ (hasExecutionWithdrawalCredential v = true ∧
      v.withdrawal_credentials.toBytes.drop 12 = cr.source_address.toBytes)) :
    s' = state := by
  rw [processConsolidationRequest_eq] at hp
  cases hc : classifyConsolidationRequest cfg state cr with
  | error e => rw [hc] at hp; cases hp
  | ok o =>
    obtain ⟨r, rfl⟩ := classifyConsolidation_ignored_of_unauthorized hc hi hv hbad
    rw [hc] at hp
    cases hp
    rfl

/-- Every ignore leaves the state unchanged: on an `ignored` classification the function
returns its input. -/
theorem processConsolidationRequest_ignored {cfg : Config} {state : BeaconState P f}
    {cr : ConsolidationRequest} {r : ConsolidationIgnoreReason}
    (h : classifyConsolidationRequest cfg state cr = .ok (.ignored r)) :
    processConsolidationRequest cfg state cr = .ok state := by
  rw [processConsolidationRequest_of_classify h]; rfl

/-! ## The state delta of a pending consolidation -/

/-- `compute_consolidation_epoch_and_update_churn` changes only the two consolidation-churn fields
(`consolidation_balance_to_consume`, `earliest_consolidation_epoch`). -/
theorem computeConsolidationEpoch_frame {cfg : Config} {state : BeaconState P f} {b : Gwei}
    {r : BeaconState P f × Epoch}
    (h : computeConsolidationEpochAndUpdateChurn cfg state b = .ok r) :
    ∃ a e, r.1 = { state with
      consolidation_balance_to_consume := a
      earliest_consolidation_epoch := e } := by
  unfold computeConsolidationEpochAndUpdateChurn at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals (first | (cases h; done) | (cases h; exact ⟨_, _, rfl⟩))

/-- **The state delta of a pending consolidation** (`applyConsolidationOutcome` on
`pendingConsolidation s t`): the consolidation churn is charged with the source's effective
balance (`compute_consolidation_epoch_and_update_churn`, which changes only the two
consolidation-churn fields), the source validator's `exit_epoch` becomes the returned epoch and
its `withdrawable_epoch` that epoch plus `MIN_VALIDATOR_WITHDRAWABILITY_DELAY`, and
`PendingConsolidation(source_index=s, target_index=t)` is appended. No balance, no other
validator, and no deposit or withdrawal queue changes. -/
theorem applyConsolidation_pending_spec {cfg : Config} {state s' : BeaconState P f}
    {cr : ConsolidationRequest} {s t : ValidatorIndex}
    (h : applyConsolidationOutcome cfg state cr (.pendingConsolidation s t) = .ok s') :
    s'.balances = state.balances ∧
    s'.pending_deposits = state.pending_deposits ∧
    s'.pending_partial_withdrawals = state.pending_partial_withdrawals ∧
    (∃ q q', state.pendingConsolidations = .ok q ∧ s'.pendingConsolidations = .ok q' ∧
      q'.toArray = q.toArray.push { source_index := s, target_index := t }) ∧
    ∃ src exitEpoch withdrawable, state.validators.toArray[s.toNat]? = some src ∧
      (∃ st1, computeConsolidationEpochAndUpdateChurn cfg state src.effective_balance =
        .ok (st1, exitEpoch)) ∧
      (∃ delay, c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY = .ok delay ∧
        U64.add? exitEpoch delay "process_consolidation_request" = .ok withdrawable) ∧
      ∀ j, s'.validators.toArray[j]? =
        if j = s.toNat then some { src with exit_epoch := exitEpoch, withdrawable_epoch := withdrawable }
        else state.validators.toArray[j]? := by
  unfold applyConsolidationOutcome at h
  dsimp only at h
  obtain ⟨src, hsrc, h⟩ := bind_ok_elim h
  obtain ⟨⟨st1, exitEpoch⟩, hr1, h⟩ := bind_ok_elim h
  dsimp only at h
  obtain ⟨delay, hdelay, h⟩ := bind_ok_elim h
  obtain ⟨withdrawable, hw, h⟩ := bind_ok_elim h
  obtain ⟨src', hsrc', h⟩ := bind_ok_elim h
  obtain ⟨vals, hvals, h⟩ := bind_ok_elim h
  obtain ⟨q, hq, h⟩ := bind_ok_elim h
  obtain ⟨q', hq', h⟩ := bind_ok_elim h
  obtain ⟨a, e, hst1⟩ := computeConsolidationEpoch_frame hr1
  simp only at hst1
  have hv1 : st1.validators = state.validators := by rw [hst1]
  have hb1 : st1.balances = state.balances := by rw [hst1]
  have hd1 : st1.pending_deposits = state.pending_deposits := by rw [hst1]
  have hp1 : st1.pending_partial_withdrawals = state.pending_partial_withdrawals := by rw [hst1]
  have hc1 : st1.pending_consolidations = state.pending_consolidations := by rw [hst1]
  unfold BeaconState.setPendingConsolidations at h
  obtain ⟨g, hg, h⟩ := bind_ok_elim h
  have hs' : s' = { { st1 with validators := vals } with pending_consolidations := g } :=
    (Except.ok.inj h).symm
  have hsrc0 := ssz_get_ok_iff.mp hsrc
  have hsrc1 := ssz_get_ok_iff.mp hsrc'
  rw [hv1, hsrc0] at hsrc1
  cases hsrc1
  have hq0 : state.pendingConsolidations = .ok q := by
    rw [← hq]; unfold BeaconState.pendingConsolidations; rw [← hc1]
  refine ⟨by rw [hs']; exact hb1, by rw [hs']; exact hd1, by rw [hs']; exact hp1,
    ⟨q, q', hq0, ?_, ?_⟩, src, exitEpoch, withdrawable, hsrc0,
    ⟨st1, hr1⟩, ⟨delay, hdelay, hw⟩, ?_⟩
  · rw [hs']
    exact gated_write_read hg
  · unfold SszList.push at hq'
    split at hq'
    · cases hq'; rfl
    · cases hq'
  · intro j
    rw [hs']
    show vals.toArray[j]? = _
    rw [hv1] at hvals
    unfold SszList.set at hvals
    split at hvals
    · cases hvals
      simp only [Array.getElem?_set]
      by_cases hj : j = s.toNat
      · subst hj; simp
      · simp [hj, Ne.symm hj]
    · cases hvals

/-! ## Switch-to-compounding delta, source/target distinctness, and fold trace -/

/-- `Gated.read` succeeds with the same value regardless of error-site label when it succeeds. -/
private theorem gated_read_ok_site {c : Bool} {α : Type} {g : Gated c α} {s1 s2 : String} {x : α}
    (h : Gated.read g s1 = .ok x) : Gated.read g s2 = .ok x := by
  cases c with
  | false => cases h
  | true => exact h

/-- A successful `validatorIndexOf` lookup names a registered validator carrying that pubkey. -/
theorem validatorIndexOf_some_pubkey {state : BeaconState P f} {pk : BLSPubkey}
    {i : ValidatorIndex} (h : validatorIndexOf state pk = .ok (some i)) :
    ∃ v, state.validators.toArray[i.toNat]? = some v ∧ v.pubkey = pk := by
  unfold validatorIndexOf at h
  cases hf : state.validators.toArray.findIdx? (·.pubkey == pk) with
  | none => rw [hf] at h; cases h
  | some idx =>
    rw [hf] at h
    obtain ⟨u, hu, heq⟩ := bind_ok_elim h
    cases heq
    have hidx : i.toNat = idx := U64.toNat_ofNat? hu
    rw [Array.findIdx?_eq_some_iff_getElem] at hf
    obtain ⟨hlt, hpk, -⟩ := hf
    refine ⟨state.validators.toArray[idx], ?_, sszVector_beq_iff.mp hpk⟩
    rw [hidx, Array.getElem?_eq_getElem hlt]

/-- Every accepted pending consolidation has distinct source and target validator indices:
`classifyConsolidationRequest` checks `cr.source_pubkey ≠ cr.target_pubkey` and resolves both keys
by first match (`validatorIndexOf`), so equal indices would force equal pubkeys. -/
theorem PendingConsolidationChecks.source_ne_target {cfg : Config} {state : BeaconState P f}
    {cr : ConsolidationRequest} {s t : ValidatorIndex}
    (h : PendingConsolidationChecks cfg state cr s t) :
    s ≠ t := by
  intro hst
  subst hst
  obtain ⟨-, hne, -, -, hs, ht, -⟩ := h
  obtain ⟨vs, hgs, hpks⟩ := validatorIndexOf_some_pubkey hs
  obtain ⟨vt, hgt, hpkt⟩ := validatorIndexOf_some_pubkey ht
  rw [hgs] at hgt
  cases hgt
  exact hne (hpks.symm.trans hpkt)

/-- The compounding withdrawal credential computed by `switchToCompoundingValidator`. -/
def compoundingWithdrawalCredentials (v : Validator) : Bytes32 :=
  Jaune.Bytes.toB256 (COMPOUNDING_WITHDRAWAL_PREFIX :: v.withdrawal_credentials.toBytes.drop 1)

/-- **State delta of `queue_excess_active_balance`**:
- Always preserves `validators`, `balances.toArray.size`, `slot`, `pending_consolidations`,
  `pending_partial_withdrawals`, `latest_execution_payload_header`, and `latest_block_header`;
- When `balance ≤ MIN_ACTIVATION_BALANCE`, returns `state` unchanged;
- When `MIN_ACTIVATION_BALANCE < balance`, sets `balances[index] := MIN_ACTIVATION_BALANCE` and
  appends one `PendingDeposit` with `amount = balance - MIN_ACTIVATION_BALANCE` and
  `slot = GENESIS_SLOT`. -/
theorem queueExcessActiveBalance_spec {state s' : BeaconState P f} {index : ValidatorIndex}
    (h : queueExcessActiveBalance state index = .ok s') :
    s'.validators = state.validators ∧
    s'.balances.toArray.size = state.balances.toArray.size ∧
    s'.slot = state.slot ∧
    s'.pending_consolidations = state.pending_consolidations ∧
    s'.pending_partial_withdrawals = state.pending_partial_withdrawals ∧
    s'.latest_execution_payload_header = state.latest_execution_payload_header ∧
    s'.latest_block_header = state.latest_block_header ∧
    ((s' = state ∧
        ∃ bal minAct, state.balances.toArray[index.toNat]? = some bal ∧
          c64 P.MIN_ACTIVATION_BALANCE = .ok minAct ∧ ¬ minAct < bal) ∨
      (∃ bal minAct excess v q q',
        state.balances.toArray[index.toNat]? = some bal ∧
        c64 P.MIN_ACTIVATION_BALANCE = .ok minAct ∧
        minAct < bal ∧
        U64.sub? bal minAct "queue_excess_active_balance" = .ok excess ∧
        state.validators.toArray[index.toNat]? = some v ∧
        state.pendingDeposits = .ok q ∧
        s'.pendingDeposits = .ok q' ∧
        q'.toArray = q.toArray.push
          { pubkey := v.pubkey
            withdrawal_credentials := v.withdrawal_credentials
            amount := excess
            signature := g2PointAtInfinitySignature
            slot := GENESIS_SLOT } ∧
        (∀ j, s'.balances.toArray[j]? =
          if j = index.toNat then some minAct else state.balances.toArray[j]?) ∧
        s' = { state with balances := s'.balances, pending_deposits := s'.pending_deposits })) := by
  unfold queueExcessActiveBalance at h
  dsimp only at h
  obtain ⟨bal, hbal, h⟩ := bind_ok_elim h
  obtain ⟨minAct, hmin, h⟩ := bind_ok_elim h
  have hbal0 := ssz_get_ok_iff.mp hbal
  by_cases hlt : minAct < bal
  · rw [ite_eq_left hlt] at h
    obtain ⟨excess, hex, h⟩ := bind_ok_elim h
    obtain ⟨bals, hbals, h⟩ := bind_ok_elim h
    obtain ⟨v, hv, h⟩ := bind_ok_elim h
    obtain ⟨q, hq, h⟩ := bind_ok_elim h
    obtain ⟨q', hq', h⟩ := bind_ok_elim h
    obtain ⟨g, hg, h⟩ := bind_ok_elim h
    cases h
    obtain ⟨hbi, hbset⟩ := set_ok hbals
    have hq0 : state.pendingDeposits = .ok q :=
      gated_read_ok_site hq
    have hq1 : ({ state with balances := bals, pending_deposits := g } : BeaconState P f).pendingDeposits = .ok q' := by
      unfold BeaconState.pendingDeposits
      exact gated_write_read hg
    refine ⟨rfl, by simp [hbset], rfl, rfl, rfl, rfl, rfl, .inr ⟨bal, minAct, excess, v, q, q',
      hbal0, hmin, hlt, hex, ssz_get_ok_iff.mp hv, hq0, hq1, push_ok hq', ?_, rfl⟩⟩
    intro j
    show bals.toArray[j]? = _
    rw [hbset, Array.getElem?_set]
    by_cases hj : j = index.toNat
    · subst hj; simp
    · simp [hj, Ne.symm hj]
  · rw [ite_eq_right hlt] at h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, .inl ⟨rfl, bal, minAct, hbal0, hmin, hlt⟩⟩

/-- **State delta of `switch_to_compounding_validator`**:
updates `validators[index].withdrawal_credentials` to `compoundingWithdrawalCredentials v`, keeps
`validators.toArray.size` and `balances.toArray.size` unchanged, preserves `slot`,
`pending_consolidations`, `pending_partial_withdrawals`, `latest_execution_payload_header`, and
`latest_block_header`, and applies `queueExcessActiveBalance` on the updated state (so
`pending_deposits` is either unchanged or appends one `GENESIS_SLOT` excess-balance entry). -/
theorem switchToCompoundingValidator_spec {state s' : BeaconState P f} {index : ValidatorIndex}
    (h : switchToCompoundingValidator state index = .ok s') :
    ∃ v mid,
      state.validators.toArray[index.toNat]? = some v ∧
      mid = { state with validators := mid.validators } ∧
      mid.validators.toArray.size = state.validators.toArray.size ∧
      (∀ j, mid.validators.toArray[j]? =
        if j = index.toNat then
          some { v with withdrawal_credentials := compoundingWithdrawalCredentials v }
        else state.validators.toArray[j]?) ∧
      queueExcessActiveBalance mid index = .ok s' ∧
      s'.validators = mid.validators ∧
      s'.balances.toArray.size = state.balances.toArray.size ∧
      s'.slot = state.slot ∧
      s'.pending_consolidations = state.pending_consolidations ∧
      s'.pending_partial_withdrawals = state.pending_partial_withdrawals ∧
      s'.latest_execution_payload_header = state.latest_execution_payload_header ∧
      s'.latest_block_header = state.latest_block_header := by
  unfold switchToCompoundingValidator at h
  dsimp only at h
  obtain ⟨v, hv, h⟩ := bind_ok_elim h
  obtain ⟨vals, hvals, h⟩ := bind_ok_elim h
  obtain ⟨hvi, hvset⟩ := set_ok hvals
  have hq := queueExcessActiveBalance_spec h
  refine ⟨v, { state with validators := vals }, ssz_get_ok_iff.mp hv, rfl,
    by simp [hvset], ?_, h, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2.1,
    hq.2.2.2.2.2.2.1⟩
  intro j
  show vals.toArray[j]? = _
  rw [hvset, Array.getElem?_set]
  by_cases hj : j = index.toNat
  · subst hj; simp [compoundingWithdrawalCredentials]
  · simp [hj, Ne.symm hj]

/-- The `PendingConsolidation` appended by a `ConsolidationOutcome`, if any. -/
def acceptedConsolidation : ConsolidationOutcome → Option PendingConsolidation
  | .pendingConsolidation s t => some { source_index := s, target_index := t }
  | _ => none

/-- Unified three-branch meaning of `classifyConsolidationRequest` + `applyConsolidationOutcome`
for a single consolidation request (`C-S9` / `D-S9` per-request outcome lemma). -/
theorem consolidationOutcome_means {cfg : Config} {state s' : BeaconState P f}
    {cr : ConsolidationRequest} {o : ConsolidationOutcome}
    (hc : classifyConsolidationRequest cfg state cr = .ok o)
    (ha : applyConsolidationOutcome cfg state cr o = .ok s') :
    (∀ r, o = .ignored r → s' = state) ∧
    (∀ i, o = .switchToCompounding i →
      SwitchToCompoundingChecks state cr i ∧
      switchToCompoundingValidator state i = .ok s') ∧
    (∀ s t, o = .pendingConsolidation s t →
      PendingConsolidationChecks cfg state cr s t ∧
      s ≠ t ∧
      applyConsolidationOutcome cfg state cr (.pendingConsolidation s t) = .ok s') := by
  have hs := classifyConsolidation_spec hc
  refine ⟨?_, ?_, ?_⟩
  · intro r hr; subst hr; cases ha; rfl
  · intro i hi; subst hi
    obtain ⟨hvalid, hidx⟩ := hs.1 i rfl
    obtain ⟨j, hj⟩ := isValidSwitch_true hvalid
    have hj_eq : j = i := by
      have hj_idx := hj.2.1
      rw [hidx] at hj_idx
      exact (Option.some.inj (Except.ok.inj hj_idx)).symm
    subst hj_eq
    exact ⟨hj, ha⟩
  · intro s t hst; subst hst
    have hp := hs.2 s t rfl
    exact ⟨hp, hp.source_ne_target, ha⟩

/-- Full record frame and validator-array size preservation of `applyConsolidationOutcome` on
`.pendingConsolidation s t`. -/
theorem applyConsolidation_pending_frame {cfg : Config} {state s' : BeaconState P f}
    {cr : ConsolidationRequest} {s t : ValidatorIndex}
    (h : applyConsolidationOutcome cfg state cr (.pendingConsolidation s t) = .ok s') :
    s' = { state with
      consolidation_balance_to_consume := s'.consolidation_balance_to_consume
      earliest_consolidation_epoch := s'.earliest_consolidation_epoch
      validators := s'.validators
      pending_consolidations := s'.pending_consolidations } ∧
    s'.validators.toArray.size = state.validators.toArray.size := by
  unfold applyConsolidationOutcome at h
  dsimp only at h
  obtain ⟨src, _, h⟩ := bind_ok_elim h
  obtain ⟨⟨st1, exitEpoch⟩, hr1, h⟩ := bind_ok_elim h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok_elim h
  obtain ⟨_, _, h⟩ := bind_ok_elim h
  obtain ⟨_, _, h⟩ := bind_ok_elim h
  obtain ⟨vals, hvals, h⟩ := bind_ok_elim h
  obtain ⟨_, _, h⟩ := bind_ok_elim h
  obtain ⟨_, _, h⟩ := bind_ok_elim h
  obtain ⟨a, e, hst1⟩ := computeConsolidationEpoch_frame hr1
  simp only at hst1
  unfold BeaconState.setPendingConsolidations at h
  obtain ⟨g, _, h⟩ := bind_ok_elim h
  cases h
  obtain ⟨_, hvset⟩ := set_ok hvals
  refine ⟨by rw [hst1], ?_⟩
  show vals.toArray.size = state.validators.toArray.size
  rw [hvset, Array.size_set, hst1]

/-- Frame and queue characterization for a single `processConsolidationRequest` call (Electra and
Fulu): preserves `slot`, `latest_execution_payload_header`, `latest_block_header`,
`pending_partial_withdrawals`, `validators.toArray.size`, and `balances.toArray.size`; appends
`acceptedConsolidation o` (with `source_index ≠ target_index`) to `pending_consolidations`; and
appends at most one `GENESIS_SLOT` entry to `pending_deposits`. -/
theorem processConsolidationRequest_frame_and_queues (h : f.atLeast .electra = true)
    {cfg : Config} {state s' : BeaconState P f} {cr : ConsolidationRequest}
    (hp : processConsolidationRequest cfg state cr = .ok s') :
    ∃ o extraDep,
      classifyConsolidationRequest cfg state cr = .ok o ∧
      applyConsolidationOutcome cfg state cr o = .ok s' ∧
      s'.slot = state.slot ∧
      s'.latest_execution_payload_header = state.latest_execution_payload_header ∧
      s'.latest_block_header = state.latest_block_header ∧
      s'.pending_partial_withdrawals = state.pending_partial_withdrawals ∧
      s'.validators.toArray.size = state.validators.toArray.size ∧
      s'.balances.toArray.size = state.balances.toArray.size ∧
      (∀ pc, acceptedConsolidation o = some pc → pc.source_index ≠ pc.target_index) ∧
      (Gated.get h s'.pending_consolidations).toArray.toList =
        (Gated.get h state.pending_consolidations).toArray.toList ++
          (acceptedConsolidation o).toList ∧
      (Gated.get h s'.pending_deposits).toArray.toList =
        (Gated.get h state.pending_deposits).toArray.toList ++ extraDep ∧
      (∀ d ∈ extraDep, d.slot = GENESIS_SLOT) := by
  rw [processConsolidationRequest_eq] at hp
  obtain ⟨o, hc, ha⟩ := bind_eq_ok_iff.mp hp
  have hm := consolidationOutcome_means hc ha
  cases o with
  | ignored r =>
    have heq := hm.1 r rfl
    subst heq
    exact ⟨.ignored r, [], hc, ha, rfl, rfl, rfl, rfl, rfl, rfl,
      (by intro _ h; cases h), (by simp [acceptedConsolidation]), (by simp),
      (by intro _ hd; cases hd)⟩
  | switchToCompounding i =>
    obtain ⟨_, hsw⟩ := hm.2.1 i rfl
    obtain ⟨v, mid, _, hmid_fr, hvsz, _, hqex, hv_eq, hbsz, hslot, hpc, hppw, hel, hlbh⟩ :=
      switchToCompoundingValidator_spec hsw
    have hmid_pd : mid.pending_deposits = state.pending_deposits := by rw [hmid_fr]
    have hq := queueExcessActiveBalance_spec hqex
    rcases hq.2.2.2.2.2.2.2 with ⟨heq, _⟩ | ⟨bal, minAct, excess, v', q, q', _, _, _, _, _,
        hq0, hq1, hpush, _, _⟩
    · refine ⟨.switchToCompounding i, [], hc, ha, hslot, hel, hlbh, hppw,
        (by rw [hv_eq, hvsz]), hbsz, (by intro _ h; cases h),
        (by simp [acceptedConsolidation, hpc]), ?_, (by intro _ hd; cases hd)⟩
      rw [heq, hmid_pd]
      simp
    · have hq0_get : q = Gated.get h mid.pending_deposits := by
        unfold BeaconState.pendingDeposits at hq0
        rw [gated_read_get h] at hq0
        exact (Except.ok.inj hq0).symm
      have hq1_get : q' = Gated.get h s'.pending_deposits := by
        unfold BeaconState.pendingDeposits at hq1
        rw [gated_read_get h] at hq1
        exact (Except.ok.inj hq1).symm
      let dep : PendingDeposit :=
        { pubkey := v'.pubkey
          withdrawal_credentials := v'.withdrawal_credentials
          amount := excess
          signature := g2PointAtInfinitySignature
          slot := GENESIS_SLOT }
      refine ⟨.switchToCompounding i, [dep], hc, ha, hslot, hel, hlbh, hppw,
        (by rw [hv_eq, hvsz]), hbsz, (by intro _ h; cases h),
        (by simp [acceptedConsolidation, hpc]), ?_, ?_⟩
      · rw [← hq1_get, hpush, hq0_get, hmid_pd, Array.toList_push]
      · intro d hd
        simp only [List.mem_singleton] at hd
        subst hd
        rfl
  | pendingConsolidation s t =>
    obtain ⟨_, hne, hpend⟩ := hm.2.2 s t rfl
    obtain ⟨hb_eq, hd_eq, hppw_eq, ⟨q, q', hq0, hq1, hpush⟩, _⟩ :=
      applyConsolidation_pending_spec hpend
    obtain ⟨hfr, hvsz⟩ := applyConsolidation_pending_frame hpend
    have hq0_get : q = Gated.get h state.pending_consolidations := by
      unfold BeaconState.pendingConsolidations at hq0
      rw [gated_read_get h] at hq0
      exact (Except.ok.inj hq0).symm
    have hq1_get : q' = Gated.get h s'.pending_consolidations := by
      unfold BeaconState.pendingConsolidations at hq1
      rw [gated_read_get h] at hq1
      exact (Except.ok.inj hq1).symm
    refine ⟨.pendingConsolidation s t, [], hc, ha,
      (by rw [hfr]), (by rw [hfr]), (by rw [hfr]), hppw_eq, hvsz, (by rw [hb_eq]),
      ?_, ?_, (by simp [hd_eq]), (by intro _ hd; cases hd)⟩
    · intro pc hpc
      simp only [acceptedConsolidation, Option.some.injEq] at hpc
      subst hpc
      exact hne
    · rw [← hq1_get, hpush, hq0_get, Array.toList_push]
      rfl

/-- **Aggregate frame and queue specification for `foldConsolidationRequests`** (Electra and Fulu):
on success across a list of requests `reqs`, there exist `outcomes` and `extraDeps` such that:
1. `outcomes.length = reqs.length`;
2. `pending_consolidations` appends `outcomes.filterMap acceptedConsolidation`, with distinct source
   and target indices for every appended entry;
3. `pending_deposits` appends `extraDeps`, all at `GENESIS_SLOT`;
4. `slot`, `latest_execution_payload_header`, `latest_block_header`, `pending_partial_withdrawals`,
   `validators.toArray.size`, and `balances.toArray.size` are preserved.

This aggregate conclusion does not relate `outcomes` pointwise to the classifier. For actual
per-request state traces, use `consolidationRequestTrace_spec` and
`consolidationRequestTrace_of_fold`; `processConsolidationRequest_eq` exposes each transition's
classification and application. -/
theorem foldConsolidationRequests_frames_and_queues (h : f.atLeast .electra = true)
    (cfg : Config) :
    ∀ (reqs : List ConsolidationRequest) {state s' : BeaconState P f},
      foldConsolidationRequests cfg state reqs = .ok s' →
      ∃ (outcomes : List ConsolidationOutcome) (extraDeps : List PendingDeposit),
        outcomes.length = reqs.length ∧
        s'.slot = state.slot ∧
        s'.latest_execution_payload_header = state.latest_execution_payload_header ∧
        s'.latest_block_header = state.latest_block_header ∧
        s'.pending_partial_withdrawals = state.pending_partial_withdrawals ∧
        s'.validators.toArray.size = state.validators.toArray.size ∧
        s'.balances.toArray.size = state.balances.toArray.size ∧
        (∀ pc ∈ outcomes.filterMap acceptedConsolidation, pc.source_index ≠ pc.target_index) ∧
        (Gated.get h s'.pending_consolidations).toArray.toList =
          (Gated.get h state.pending_consolidations).toArray.toList ++
            outcomes.filterMap acceptedConsolidation ∧
        (Gated.get h s'.pending_deposits).toArray.toList =
          (Gated.get h state.pending_deposits).toArray.toList ++ extraDeps ∧
        (∀ d ∈ extraDeps, d.slot = GENESIS_SLOT) := by
  intro reqs
  induction reqs with
  | nil =>
    intro state s' hp
    cases hp
    exact ⟨[], [], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      (by intro _ hm; cases hm), (by simp), (by simp), (by intro _ hm; cases hm)⟩
  | cons cr crs ih =>
    intro state s' hp
    unfold foldConsolidationRequests at hp
    rw [List.foldlM_cons] at hp
    obtain ⟨mid, h1, hrest⟩ := bind_eq_ok_iff.mp hp
    obtain ⟨o, extra1, _, _, hslot1, hel1, hlbh1, hppw1, hvsz1, hbsz1, hdist1, hpc1, hpd1,
      hgen1⟩ := processConsolidationRequest_frame_and_queues h h1
    obtain ⟨os, extra2, hlen, hslot2, hel2, hlbh2, hppw2, hvsz2, hbsz2, hdist2, hpc2, hpd2,
      hgen2⟩ := ih hrest
    refine ⟨o :: os, extra1 ++ extra2, by simp [hlen],
      hslot2.trans hslot1, hel2.trans hel1, hlbh2.trans hlbh1, hppw2.trans hppw1,
      hvsz2.trans hvsz1, hbsz2.trans hbsz1, ?_, ?_, ?_, ?_⟩
    · intro pc hpc
      simp only [List.filterMap_cons] at hpc
      cases ho : acceptedConsolidation o with
      | none => rw [ho] at hpc; exact hdist2 pc hpc
      | some pc0 =>
        rw [ho] at hpc
        rcases List.mem_cons.mp hpc with rfl | hmem
        · exact hdist1 pc ho
        · exact hdist2 pc hmem
    · rw [hpc2, hpc1, List.append_assoc]
      congr 1
      cases ho : acceptedConsolidation o <;> simp [ho]
    · rw [hpd2, hpd1, List.append_assoc]
    · intro d hd
      rcases List.mem_append.mp hd with hd1 | hd2
      · exact hgen1 d hd1
      · exact hgen2 d hd2

end JauneConsensus.Facts
