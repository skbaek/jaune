import JauneConsensus.Facts.Gloas.BuilderAuth

/-!
# Builder/validator separation frames (goal `eip8282-gloas-cross-layer-v1`, B3 and B7)

Frozen statements rev 3.1, B3 and B7, function level:

* the builder requests write the builder registry only (`processBuilderDepositRequest_frame`,
  `processBuilderExitRequest_frame`);
* the validator paths leave the builder registry alone (`*_builders`), through U3's
  relation-parametric generator (`Step.lean`) at `builderFrame` (`Frame.lean`), with the new leaf
  rules registered below;
* `slash_validator` keeps the builders and the builder withdrawals and only clears builder
  payments (`slashValidator_builder_frame`, a second relation, `paymentsCleared`);
* the payment mutators (`settleBuilderPayment_frame`, `directAppend_frame`,
  `processBuilderPendingPayments_frame`).

Generator notes. `Step.lean`'s two pitfalls are respected: the relation `PaymentsCleared` is a
plain `def` (not reducible), and each leaf rule fixes the lemma's result type with `have` before
it meets the goal.
-/

namespace JauneConsensus.Facts.Gloas

open JauneConsensus JauneConsensus.Facts

variable {P : Preset}

/-! ## Builder requests write only the builder registry (B7) -/

/-- **B7.** `process_builder_deposit_request` changes nothing but `state.builders`: validators,
validator balances, `pending_deposits` and the builder queues are unchanged. -/
theorem processBuilderDepositRequest_frame {ctx : Ctx} {m m' : JauneConsensus.Gloas.BeaconState P}
    {r : JauneConsensus.Gloas.BuilderDepositRequest}
    (h : JauneConsensus.Gloas.processBuilderDepositRequest ctx m r = .ok m') :
    m'.validators = m.validators ∧ m'.balances = m.balances ∧
    m'.pending_deposits = m.pending_deposits ∧
    m'.builder_pending_payments = m.builder_pending_payments ∧
    m'.builder_pending_withdrawals = m.builder_pending_withdrawals ∧
    m' = { m with builders := m'.builders } := by
  have h0 := h
  rw [processBuilderDepositRequest_eq] at h0
  obtain ⟨o, hco, _⟩ := bind_eq_ok_iff.mp h0
  obtain ⟨hpre, hbad, htop, hreg⟩ := classifyBuilderDeposit_effect hco h
  have hm : m' = { m with builders := m'.builders } := by
    cases o with
    | ignoredPrefix => rw [hpre rfl]
    | ignoredBadSignature => rw [hbad rfl]
    | topUp j a reset => exact (htop j a reset rfl).choose_spec.choose_spec.2.2.2.2.2.2.2.2.2.2.2
    | register j a => exact (hreg j a rfl).choose_spec.choose_spec.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, hm⟩ <;> rw [hm]

/-- **B7.** `process_builder_exit_request` changes nothing but `state.builders`. -/
theorem processBuilderExitRequest_frame {cfg : Config} {m m' : JauneConsensus.Gloas.BeaconState P}
    {r : JauneConsensus.Gloas.BuilderExitRequest}
    (h : JauneConsensus.Gloas.processBuilderExitRequest cfg m r = .ok m') :
    m'.validators = m.validators ∧ m'.balances = m.balances ∧
    m'.pending_deposits = m.pending_deposits ∧
    m'.builder_pending_payments = m.builder_pending_payments ∧
    m'.builder_pending_withdrawals = m.builder_pending_withdrawals ∧
    m' = { m with builders := m'.builders } := by
  have h0 := h
  rw [processBuilderExitRequest_eq] at h0
  obtain ⟨o, hco, _⟩ := bind_eq_ok_iff.mp h0
  obtain ⟨hign, hini⟩ := classifyBuilderExit_effect hco h
  have hm : m' = { m with builders := m'.builders } := by
    cases o with
    | initiate i => exact (hini i rfl).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2
    | _ => rw [hign (fun _ h => by cases h)]
  refine ⟨?_, ?_, ?_, ?_, ?_, hm⟩ <;> rw [hm]

/-! ## Validator paths keep the builders (B3, B7) -/

theorem processDepositRequest_builderFrame (m : JauneConsensus.Gloas.BeaconState P)
    (dr : DepositRequest) :
    builderFrame.R m (JauneConsensus.Gloas.processDepositRequest m dr) := ⟨rfl, rfl, rfl⟩

/-- **B3/B7.** `process_deposit_request` keeps the builders. -/
theorem processDepositRequest_builders (m : JauneConsensus.Gloas.BeaconState P)
    (dr : DepositRequest) :
    (JauneConsensus.Gloas.processDepositRequest m dr).builders = m.builders := rfl

theorem processVoluntaryExit_builderFrame (ctx : Ctx) (s : JauneConsensus.Gloas.BeaconState P)
    (sve : SignedVoluntaryExit) :
    Ok (JauneConsensus.Gloas.processVoluntaryExit ctx s sve) (builderFrame.R s) := by
  unfold JauneConsensus.Gloas.processVoluntaryExit; gvcg
  all_goals exact initiateValidatorExit_builderFrame _ _ _

/-- **B3/B7.** `process_voluntary_exit` keeps the builders. -/
theorem processVoluntaryExit_builders {ctx : Ctx} {m m' : JauneConsensus.Gloas.BeaconState P}
    {sve : SignedVoluntaryExit} (h : JauneConsensus.Gloas.processVoluntaryExit ctx m sve = .ok m') :
    m'.builders = m.builders :=
  (processVoluntaryExit_builderFrame ctx m sve m' h).1

theorem processBlsToExecutionChange_builderFrame (ctx : Ctx)
    (s : JauneConsensus.Gloas.BeaconState P) (sac : SignedBLSToExecutionChange) :
    Ok (JauneConsensus.Gloas.processBlsToExecutionChange ctx s sac) (builderFrame.R s) := by
  unfold JauneConsensus.Gloas.processBlsToExecutionChange; gvcg

/-- **B3/B7.** `process_bls_to_execution_change` keeps the builders. -/
theorem processBlsToExecutionChange_builders {ctx : Ctx} {m m' : JauneConsensus.Gloas.BeaconState P}
    {sac : SignedBLSToExecutionChange}
    (h : JauneConsensus.Gloas.processBlsToExecutionChange ctx m sac = .ok m') :
    m'.builders = m.builders :=
  (processBlsToExecutionChange_builderFrame ctx m sac m' h).1

theorem addValidatorToRegistry_builderFrame (s : JauneConsensus.Gloas.BeaconState P)
    (pk : BLSPubkey) (wc : Bytes32) (amount : Gwei) :
    Ok (JauneConsensus.Gloas.addValidatorToRegistry s pk wc amount) (builderFrame.R s) := by
  unfold JauneConsensus.Gloas.addValidatorToRegistry; gvcg

macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (addValidatorToRegistry_builderFrame _ _ _ _) $h; exact hh))

theorem applyPendingDeposit_builderFrame (ctx : Ctx) (s : JauneConsensus.Gloas.BeaconState P)
    (d : PendingDeposit) :
    Ok (JauneConsensus.Gloas.applyPendingDeposit ctx s d) (builderFrame.R s) := by
  unfold JauneConsensus.Gloas.applyPendingDeposit; gvcg
  · exact addValidatorToRegistry_builderFrame _ _ _ _
  · exact increaseBalance_builderFrame _ _ _

macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (applyPendingDeposit_builderFrame _ _ _) $h; exact hh))

/-- Loops whose state is a `MProd` of mutable variables with the step's state last (four
mutable variables before it, as in `process_pending_deposits`). -/
macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRel.forIn_array_rel _ (fun x => x.2.2.2.2) ?_ _ _ $h; intro _ _; gvcg))

theorem processPendingDeposits_builderFrame (ctx : Ctx) (s : JauneConsensus.Gloas.BeaconState P) :
    Ok (JauneConsensus.Gloas.processPendingDeposits ctx s) (builderFrame.R s) := by
  unfold JauneConsensus.Gloas.processPendingDeposits; gvcg

/-- **B3/B7.** `process_pending_deposits` (Gloas, CL:1659-1714) keeps the builders. -/
theorem processPendingDeposits_builders {ctx : Ctx} {m m' : JauneConsensus.Gloas.BeaconState P}
    (h : JauneConsensus.Gloas.processPendingDeposits ctx m = .ok m') :
    m'.builders = m.builders :=
  (processPendingDeposits_builderFrame ctx m m' h).1

/-! ## `slash_validator` only clears builder payments -/

/-- The builders and builder withdrawals are unchanged; each builder payment is unchanged or
emptied. -/
def PaymentsCleared (s s' : JauneConsensus.Gloas.BeaconState P) : Prop :=
  s'.builders = s.builders ∧ s'.builder_pending_withdrawals = s.builder_pending_withdrawals ∧
    ∀ j : Nat, s'.builder_pending_payments.toArray[j]? = s.builder_pending_payments.toArray[j]? ∨
      s'.builder_pending_payments.toArray[j]? = some JauneConsensus.Gloas.BuilderPendingPayment.empty

/-- `PaymentsCleared` as a step relation. -/
def paymentsCleared : StepRel (JauneConsensus.Gloas.BeaconState P) where
  R := PaymentsCleared
  refl _ := ⟨rfl, rfl, fun _ => Or.inl rfl⟩
  trans {a b c} h₁ h₂ := by
    refine ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun j => ?_⟩
    rcases h₂.2.2 j with h | h
    · rw [h]; exact h₁.2.2 j
    · exact Or.inr h

theorem paymentsCleared_of_frame {s s' : JauneConsensus.Gloas.BeaconState P}
    (h : BuilderFrame s s') : PaymentsCleared s s' :=
  ⟨h.1, h.2.2, fun j => Or.inl (by rw [h.2.1])⟩

theorem paymentsCleared_map (s : JauneConsensus.Gloas.BeaconState P)
    (f : JauneConsensus.Gloas.BuilderPendingPayment → JauneConsensus.Gloas.BuilderPendingPayment)
    (hf : ∀ p, f p = p ∨ f p = JauneConsensus.Gloas.BuilderPendingPayment.empty) (h) :
    PaymentsCleared s { s with builder_pending_payments :=
      ⟨s.builder_pending_payments.toArray.map f, h⟩ } := by
  refine ⟨rfl, rfl, fun j => ?_⟩
  simp only [Array.getElem?_map]
  cases s.builder_pending_payments.toArray[j]? with
  | none => exact Or.inl rfl
  | some p =>
    rcases hf p with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])

macro_rules
  | `(tactic| gstep_close) =>
    `(tactic| exact (show PaymentsCleared _ _ from ⟨rfl, rfl, fun _ => Or.inl rfl⟩))
macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (increaseBalance_builderFrame _ _ _) $h; exact paymentsCleared_of_frame hh))
macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (decreaseBalance_builderFrame _ _ _) $h; exact paymentsCleared_of_frame hh))
macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (initiateValidatorExit_builderFrame _ _ _) $h; exact paymentsCleared_of_frame hh))

theorem slashValidator_paymentsCleared (cfg : Config) (s : JauneConsensus.Gloas.BeaconState P)
    (i : ValidatorIndex) (wb : Option ValidatorIndex) :
    Ok (JauneConsensus.Gloas.slashValidator cfg s i wb) (paymentsCleared.R s) := by
  unfold JauneConsensus.Gloas.slashValidator; gvcg
  all_goals
    apply ok_pure
    exact paymentsCleared_map _ _ (fun p => by
      by_cases hp : (p.proposer_index == i) = true <;> simp [hp]) _

/-- **B3/B7.** `slash_validator` (Gloas, CL:1549) keeps the builders and the builder withdrawals;
every builder payment is unchanged or emptied (the slashed proposer's). -/
theorem slashValidator_builder_frame {cfg : Config} {m m' : JauneConsensus.Gloas.BeaconState P}
    {i : ValidatorIndex} {wb : Option ValidatorIndex}
    (h : JauneConsensus.Gloas.slashValidator cfg m i wb = .ok m') :
    m'.builders = m.builders ∧ m'.builder_pending_withdrawals = m.builder_pending_withdrawals ∧
    ∀ j : Nat, m'.builder_pending_payments.toArray[j]? = m.builder_pending_payments.toArray[j]? ∨
      m'.builder_pending_payments.toArray[j]? =
        some JauneConsensus.Gloas.BuilderPendingPayment.empty :=
  slashValidator_paymentsCleared cfg m i wb m' h

/-- **B3.** `slash_validator` keeps the builders. -/
theorem slashValidator_builders {cfg : Config} {m m' : JauneConsensus.Gloas.BeaconState P}
    {i : ValidatorIndex} {wb : Option ValidatorIndex}
    (h : JauneConsensus.Gloas.slashValidator cfg m i wb = .ok m') : m'.builders = m.builders :=
  (slashValidator_builder_frame h).1

/-! ## Builder payment mutators (B7) -/

theorem sv_set_ok {α : Type} {n : Nat} {xs ys : SszVector α n} {i : Nat} {v : α}
    {site : String} (h : xs.set i v site = .ok ys) :
    ys.toArray[i]? = some v ∧ ∀ j, j ≠ i → ys.toArray[j]? = xs.toArray[j]? := by
  unfold SszVector.set at h
  split at h
  · rename_i hi
    cases h
    exact ⟨by simp [hi], fun j hj => by simp [Ne.symm hj]⟩
  · cases h

/-- **B7.** `settle_builder_payment` (CL:1538): the builders are unchanged; the entry's withdrawal
is appended to the builder withdrawals exactly when its amount is positive; the entry is
emptied and every other entry is unchanged. -/
theorem settleBuilderPayment_frame {m m' : JauneConsensus.Gloas.BeaconState P} {idx : U64}
    (h : JauneConsensus.Gloas.settleBuilderPayment m idx = .ok m') :
    m'.builders = m.builders ∧
    ∃ p, m.builder_pending_payments.toArray[idx.toNat]? = some p ∧
      (U64.zero < p.withdrawal.amount →
        m'.builder_pending_withdrawals = m.builder_pending_withdrawals.push p.withdrawal) ∧
      (¬ U64.zero < p.withdrawal.amount →
        m'.builder_pending_withdrawals = m.builder_pending_withdrawals) ∧
      m'.builder_pending_payments.toArray[idx.toNat]? =
        some JauneConsensus.Gloas.BuilderPendingPayment.empty ∧
      (∀ j, j ≠ idx.toNat →
        m'.builder_pending_payments.toArray[j]? = m.builder_pending_payments.toArray[j]?) := by
  unfold JauneConsensus.Gloas.settleBuilderPayment at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := bind_eq_ok_iff.mp h
  have hp' : m.builder_pending_payments.toArray[idx.toNat]? = some p := by
    unfold SszVector.get getAt at hp
    split at hp
    · rename_i x hx; cases hp; exact hx
    · cases hp
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  cases h
  by_cases hz : U64.zero < p.withdrawal.amount
  · rw [if_pos hz] at hv ⊢
    obtain ⟨h1, h2⟩ := sv_set_ok hv
    exact ⟨rfl, p, hp', fun _ => rfl, fun hn => absurd hz hn, h1, h2⟩
  · rw [if_neg hz] at hv ⊢
    obtain ⟨h1, h2⟩ := sv_set_ok hv
    exact ⟨rfl, p, hp', fun hn => absurd hn hz, fun _ => rfl, h1, h2⟩

/-- The direct append of `apply_parent_execution_payload` (CL:1803-1812, parent older than the
previous epoch): the parent bid's withdrawal is appended to the builder withdrawals. -/
def directAppend (state : JauneConsensus.Gloas.BeaconState P) : JauneConsensus.Gloas.BeaconState P :=
  let parentBid := state.latest_execution_payload_bid
  let w : JauneConsensus.Gloas.BuilderPendingWithdrawal :=
    { fee_recipient := parentBid.fee_recipient, amount := parentBid.value,
      builder_index := parentBid.builder_index }
  { state with builder_pending_withdrawals := state.builder_pending_withdrawals.push w }

/-- **B7.** The direct append keeps the builders and the builder payments, and appends exactly
the parent bid's withdrawal. -/
theorem directAppend_frame (m : JauneConsensus.Gloas.BeaconState P) :
    (directAppend m).builders = m.builders ∧
    (directAppend m).builder_pending_withdrawals = m.builder_pending_withdrawals.push
      ({ fee_recipient := m.latest_execution_payload_bid.fee_recipient,
         amount := m.latest_execution_payload_bid.value,
         builder_index := m.latest_execution_payload_bid.builder_index } :
        JauneConsensus.Gloas.BuilderPendingWithdrawal) ∧
    (directAppend m).builder_pending_payments = m.builder_pending_payments :=
  ⟨rfl, rfl, rfl⟩

end JauneConsensus.Facts.Gloas
