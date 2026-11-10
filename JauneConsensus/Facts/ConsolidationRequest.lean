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

end JauneConsensus.Facts
