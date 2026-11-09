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


/-! ## `process_builder_pending_payments` (B7) -/

theorem forIn_list_pure_yield {α β : Type} (l : List α) (init : β)
    (body : α → β → M (ForInStep β)) (g : β → α → β)
    (hb : ∀ a b, body a b = .ok (.yield (g b a))) : forIn l init body = .ok (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, hb]
    exact ih (g init a)

theorem foldl_push_filter_toList {s : Spine} {α γ : Type} (C : α → Prop) [DecidablePred C]
    (f : α → γ) (l : List α) (init : ProgressiveListS s γ) :
    (l.foldl (fun w p => if C p then w.push (f p) else w) init).toArray.toList =
      init.toArray.toList ++ (l.filter (fun p => decide (C p))).map f := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    by_cases hc : C a
    · rw [List.foldl_cons, if_pos hc, ih]
      simp [ProgressiveListS.push, List.filter_cons, hc]
    · simp only [List.foldl_cons, hc, ↓reduceIte, ih, List.filter_cons, decide_false,
        Bool.false_eq_true]

/-- **B7.** `process_builder_pending_payments` (CL:1719): the builders are unchanged; the builder
withdrawals gain exactly the withdrawals of the previous epoch's payments whose weight reaches the
quorum, in order; the payments shift down by one epoch and the second half is emptied. -/
theorem processBuilderPendingPayments_frame {cfg : Config}
    {m m' : JauneConsensus.Gloas.BeaconState P}
    (h : JauneConsensus.Gloas.processBuilderPendingPayments cfg m = .ok m') :
    m'.builders = m.builders ∧
    ∃ q, JauneConsensus.Gloas.getBuilderPaymentQuorumThreshold m = .ok q ∧
      m'.builder_pending_withdrawals.toArray.toList =
        m.builder_pending_withdrawals.toArray.toList ++
          (((m.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH).toList.filter
            (fun p => decide (q ≤ p.weight))).map (·.withdrawal)) ∧
      m'.builder_pending_payments.toArray =
        m.builder_pending_payments.toArray.extract P.SLOTS_PER_EPOCH
            m.builder_pending_payments.toArray.size ++
          Array.replicate P.SLOTS_PER_EPOCH JauneConsensus.Gloas.BuilderPendingPayment.empty := by
  unfold JauneConsensus.Gloas.processBuilderPendingPayments at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  rw [← Array.forIn_toList,
    forIn_list_pure_yield _ _ _
      (fun w p => if q ≤ p.weight then w.push p.withdrawal else w)
      (by intro a b; by_cases hc : q ≤ a.weight <;> simp only [hc, ↓reduceIte] <;> rfl)] at hw
  cases hw
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  cases h
  unfold SszVector.ofArray at hv
  split at hv
  · cases hv
    exact ⟨rfl, q, hq, foldl_push_filter_toList _ _ _ _, rfl⟩
  · cases hv

/-! ## B7 controls on closed minimal states -/

/-- **B7 mutant (separation)**: `process_builder_deposit_request` that also credits validator 0
with the request's amount. -/
def processBuilderDepositRequestCredit (ctx : Ctx) (state : JauneConsensus.Gloas.BeaconState P)
    (request : JauneConsensus.Gloas.BuilderDepositRequest) : M (JauneConsensus.Gloas.BeaconState P) := do
  let state ← JauneConsensus.Gloas.processBuilderDepositRequest ctx state request
  JauneConsensus.Gloas.increaseBalance state U64.zero request.amount

/-- The B7 separation control state: one validator balance (zero), no builders. -/
def ctrlBalState (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    JauneConsensus.Gloas.BeaconState Preset.minimal :=
  { s with slot := U64.zero, builders := ⟨#[]⟩, balances := ⟨#[U64.zero]⟩ }

/-- **B7 separation control.** The real `process_builder_deposit_request` keeps the validator
balances (`processBuilderDepositRequest_frame`); the crediting mutant changes them on a closed
state. -/
theorem b7_separation_control (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    (∀ m', JauneConsensus.Gloas.processBuilderDepositRequest { cfg := Config.minimal }
      (ctrlBalState s) ctrlPrefixRequest = .ok m' → m'.balances = (ctrlBalState s).balances) ∧
    ∃ s', processBuilderDepositRequestCredit { cfg := Config.minimal } (ctrlBalState s)
      ctrlPrefixRequest = .ok s' ∧ s'.balances ≠ (ctrlBalState s).balances := by
  refine ⟨fun m' h => (processBuilderDepositRequest_frame h).2.1, ?_⟩
  refine ⟨{ ctrlBalState s with balances := ⟨#[U64.one]⟩ }, ?_, ?_⟩
  · unfold processBuilderDepositRequestCredit
    rw [processBuilderDepositRequest_ignores_prefix (by decide)]
    with_unfolding_all rfl
  · intro h
    have h2 := congrArg (fun l : ProgressiveListR Gwei => l.toArray[0]?) h
    simp [ctrlBalState] at h2
    exact absurd (congrArg U64.toNat h2) (by decide)

/-- The total builder balance. -/
def totalBuilderBalance (st : JauneConsensus.Gloas.BeaconState P) : Nat :=
  (st.builders.toArray.toList.map (·.balance.toNat)).sum

/-- The builder withdrawals' total amount (validator indices carrying `BUILDER_INDEX_FLAG`). -/
def builderWithdrawalTotal (ws : Array Withdrawal) : Nat :=
  ((ws.toList.filter (fun w => JauneConsensus.Gloas.isBuilderIndex w.validator_index)).map
    (·.amount.toNat)).sum

/-- **B7 mutant (conservation)**: `apply_withdrawals` that skips the builder deduction. -/
def applyWithdrawalsSkipBuilder (state : JauneConsensus.Gloas.BeaconState P)
    (withdrawals : Array Withdrawal) : M (JauneConsensus.Gloas.BeaconState P) := do
  let mut state := state
  for withdrawal in withdrawals do
    if JauneConsensus.Gloas.isBuilderIndex withdrawal.validator_index then
      pure ()
    else
      state ← JauneConsensus.Gloas.decreaseBalance state withdrawal.validator_index withdrawal.amount
  pure state

/-- One builder with balance 10. -/
def ctrlRichBuilder : JauneConsensus.Gloas.Builder :=
  { ctrlBuilder with balance := U64.lit 10 }

/-- The B7 conservation control state. -/
def ctrlWithdrawState (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    JauneConsensus.Gloas.BeaconState Preset.minimal :=
  { s with builders := ⟨#[ctrlRichBuilder]⟩ }

/-- One builder withdrawal of 3 for builder 0 (`validator_index = 0 | BUILDER_INDEX_FLAG`). -/
def ctrlBuilderWithdrawals : Array Withdrawal :=
  #[{ index := U64.zero, validator_index := U64.lit (2 ^ 40), address := JauneConsensus.Gloas.zeroAddress,
      amount := U64.lit 3 }]

/-- **B7 conservation control.** On a closed state with one builder (balance 10) and one builder
withdrawal of 3, the real `apply_withdrawals` conserves builder balance
(`post + withdrawn = pre`, 7 + 3 = 10); the mutant that skips the builder deduction does not
(10 + 3 ≠ 10). -/
theorem b7_conservation_control (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    (∃ s', JauneConsensus.Gloas.applyWithdrawals (ctrlWithdrawState s) ctrlBuilderWithdrawals = .ok s' ∧
      totalBuilderBalance s' + builderWithdrawalTotal ctrlBuilderWithdrawals =
        totalBuilderBalance (ctrlWithdrawState s)) ∧
    (∃ s', applyWithdrawalsSkipBuilder (ctrlWithdrawState s) ctrlBuilderWithdrawals = .ok s' ∧
      totalBuilderBalance s' + builderWithdrawalTotal ctrlBuilderWithdrawals ≠
        totalBuilderBalance (ctrlWithdrawState s)) := by
  have hpre : totalBuilderBalance (ctrlWithdrawState s) = 10 := by with_unfolding_all rfl
  have hw : builderWithdrawalTotal ctrlBuilderWithdrawals = 3 := by with_unfolding_all rfl
  have hpost : totalBuilderBalance { ctrlWithdrawState s with
      builders := ⟨#[{ ctrlRichBuilder with balance := U64.lit 7 }]⟩ } = 7 := by
    with_unfolding_all rfl
  refine ⟨⟨{ ctrlWithdrawState s with
      builders := ⟨#[{ ctrlRichBuilder with balance := U64.lit 7 }]⟩ }, ?_, ?_⟩,
    ⟨ctrlWithdrawState s, ?_, ?_⟩⟩
  · with_unfolding_all rfl
  · rw [hpost, hpre, hw]
  · with_unfolding_all rfl
  · rw [hpre, hw]; decide


/-! ## One builder request at one slot -/

/-- With at least two slots per epoch the current epoch is below `FAR_FUTURE_EPOCH` (the
`slotsPerEpoch` premise of `ValidJointG`), so `FAR_FUTURE_EPOCH <= epoch` never holds. -/
theorem not_far_le_epoch (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {slot e : U64}
    (h : computeEpochAtSlot P slot = .ok e) : ¬ FAR_FUTURE_EPOCH ≤ e := by
  unfold computeEpochAtSlot at h
  obtain ⟨d, hd, h⟩ := bind_eq_ok_iff.mp h
  have hdn : d.toNat = P.SLOTS_PER_EPOCH := U64.toNat_ofNat? hd
  have he : e.toNat = slot.toNat / d.toNat := U64.toNat_div? h
  have hs := U64.toNat_lt slot
  have hle : slot.toNat / P.SLOTS_PER_EPOCH ≤ slot.toNat / 2 :=
    Nat.div_le_div_left hspe (by decide)
  intro hf
  rw [U64.le_iff, FAR_FUTURE_EPOCH, U64.toNat_max, he, hdn] at hf
  omega

/-- What one builder deposit request does at slot `i`: nothing, a top-up of `i` (classified so),
or a registration at `i` (classified so), which needs `i` to be past the end or to hold an exited,
swept builder. -/
theorem processBuilderDepositRequest_at {ctx : Ctx} {st st' : JauneConsensus.Gloas.BeaconState P}
    {r : JauneConsensus.Gloas.BuilderDepositRequest}
    (h : JauneConsensus.Gloas.processBuilderDepositRequest ctx st r = .ok st') (i : Nat) :
    st'.slot = st.slot ∧ st.builders.toArray.size ≤ st'.builders.toArray.size ∧
    (st'.builders.toArray[i]? = st.builders.toArray[i]? ∨
     (∃ c c' reset, st.builders.toArray[i]? = some c ∧ st'.builders.toArray[i]? = some c' ∧
        classifyBuilderDeposit ctx.cfg ctx.blsActive st r = .ok (.topUp i r.amount reset) ∧
        c'.pubkey = c.pubkey ∧ c'.balance.toNat = c.balance.toNat + r.amount.toNat ∧
        (reset = false → c'.withdrawable_epoch = c.withdrawable_epoch) ∧
        (reset = true ↔ c.withdrawable_epoch ≠ FAR_FUTURE_EPOCH ∧ c.balance = U64.zero)) ∨
     (∃ addr e, classifyBuilderDeposit ctx.cfg ctx.blsActive st r = .ok (.register i r.amount) ∧
        computeEpochAtSlot P st.slot = .ok e ∧
        st'.builders.toArray[i]? = some (freshBuilder r.pubkey addr r.amount e) ∧
        (∀ x ∈ st.builders.toArray, x.pubkey ≠ r.pubkey) ∧
        (∀ c, st.builders.toArray[i]? = some c →
          c.withdrawable_epoch ≤ e ∧ c.balance = U64.zero))) := by
  have hslot : st'.slot = st.slot := by rw [(processBuilderDepositRequest_frame h).2.2.2.2.2]
  have h0 := h
  rw [processBuilderDepositRequest_eq] at h0
  obtain ⟨o, hco, _⟩ := bind_eq_ok_iff.mp h0
  obtain ⟨hpre, hbad, htop, hreg⟩ := classifyBuilderDeposit_effect hco h
  obtain ⟨_, htopm, _, hregm⟩ := classifyBuilderDeposit_meaning hco
  cases o with
  | ignoredPrefix => have := hpre rfl; subst this; exact ⟨hslot, le_refl _, Or.inl rfl⟩
  | ignoredBadSignature => have := hbad rfl; subst this; exact ⟨hslot, le_refl _, Or.inl rfl⟩
  | topUp j a reset =>
    obtain ⟨_, _, ha, hres⟩ := (htopm j a reset).mp rfl
    subst ha
    obtain ⟨c, c', hc, hc', hsz, hne, hpk, _, _, _, hbal, _, hres2, _⟩ := htop j r.amount reset rfl
    refine ⟨hslot, le_of_eq hsz.symm, ?_⟩
    by_cases hij : i = j
    · subst hij
      obtain ⟨b0, hb0, hr⟩ := hres
      rw [hc] at hb0; cases hb0
      exact Or.inr (Or.inl ⟨c, c', reset, hc, hc', hco, hpk, hbal, hres2, hr⟩)
    · exact Or.inl (hne i hij)
  | register j a =>
    obtain ⟨_, hall, _, ha, idx, hidx, hidxj⟩ := (hregm j a).mp rfl
    subst ha
    obtain ⟨addr, e, _, he, hat, hsz, hne, _⟩ := hreg j r.amount rfl
    refine ⟨hslot, hsz, ?_⟩
    by_cases hij : i = j
    · subst hij
      refine Or.inr (Or.inr ⟨addr, e, hco, he, hat, hall, fun c hc => ?_⟩)
      obtain ⟨e', he', hcase⟩ := getIndexForNewBuilder_spec hidx
      have hee : e' = e := by
        have : JauneConsensus.Gloas.getCurrentEpoch st = computeEpochAtSlot P st.slot := rfl
        rw [this, he] at he'; cases he'; rfl
      subst hee
      rcases hcase with hend | ⟨b, hb, hw, hz⟩
      · rw [← hidxj, hend] at hc; simp at hc
      · rw [hidxj, hc] at hb; cases hb; exact ⟨hw, hz⟩
    · exact Or.inl (hne i hij)

/-- What one builder exit request does at slot `i`: nothing, or (classified `initiate i`, after
the source check) `withdrawable_epoch := current_epoch + MIN_BUILDER_WITHDRAWABILITY_DELAY` on an
active builder, whose `withdrawable_epoch` was therefore `FAR_FUTURE_EPOCH`. -/
theorem processBuilderExitRequest_at {cfg : Config} {st st' : JauneConsensus.Gloas.BeaconState P}
    {r : JauneConsensus.Gloas.BuilderExitRequest}
    (h : JauneConsensus.Gloas.processBuilderExitRequest cfg st r = .ok st') (i : Nat) :
    st'.slot = st.slot ∧ st'.builders.toArray.size = st.builders.toArray.size ∧
    (st'.builders.toArray[i]? = st.builders.toArray[i]? ∨
     ∃ c w, st.builders.toArray[i]? = some c ∧
       st'.builders.toArray[i]? = some { c with withdrawable_epoch := w } ∧
       classifyBuilderExit cfg st r = .ok (.initiate i) ∧
       c.execution_address = r.source_address ∧ c.withdrawable_epoch = FAR_FUTURE_EPOCH) := by
  have hm := (processBuilderExitRequest_frame h).2.2.2.2.2
  have hslot : st'.slot = st.slot := by rw [hm]
  have h0 := h
  rw [processBuilderExitRequest_eq] at h0
  obtain ⟨o, hco, _⟩ := bind_eq_ok_iff.mp h0
  obtain ⟨hign, hini⟩ := classifyBuilderExit_effect hco h
  cases o with
  | initiate j =>
    obtain ⟨c, e, w, hc, _, _, hc', hsz, hne, _⟩ := hini j rfl
    refine ⟨hslot, hsz, ?_⟩
    by_cases hij : i = j
    · subst hij
      obtain ⟨_, _, _, _, _, hmi, _⟩ := classifyBuilderExit_meaning hco
      obtain ⟨b, bi, _, hb, _, hact, hsrc, _⟩ := (hmi i).mp rfl
      rw [hc] at hb; cases hb
      have hact' := hact
      rw [isActiveBuilder_of_get (m := st) (bi := bi) (b := c) (by
        rw [U64.toNat_ofNat? ‹U64.ofNat? i "BuilderIndex" = .ok bi›]; exact hc)] at hact'
      simp only [Except.ok.injEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hact'
      exact Or.inr ⟨c, w, hc, hc', hco, hsrc, hact'.2⟩
    · exact Or.inl (hne i hij)
  | _ =>
    rw [hign (fun _ h => by cases h)]
    exact ⟨rfl, rfl, Or.inl rfl⟩


/-! ## The builder-deposit and builder-exit loops (B3 writers, B1 register-then-top-up) -/

theorem foldlM_snoc_ok {α β : Type} {f : β → α → M β} {l : List α} {s0 st st' : β} {x : α}
    (hl : l.foldlM f s0 = .ok st) (hx : f st x = .ok st') : (l ++ [x]).foldlM f s0 = .ok st' := by
  rw [List.foldlM_append, hl]
  show List.foldlM f st [x] = .ok st'
  rw [List.foldlM_cons, hx]
  rfl

/-- A builder deposit in the list `rs`, reached from `s0` through the deposits before it, is a
top-up of builder `i` that resets its `withdrawable_epoch` (CL:2354-2358). -/
def TopUpResetIn (ctx : Ctx) (s0 : JauneConsensus.Gloas.BeaconState P)
    (rs : List JauneConsensus.Gloas.BuilderDepositRequest) (i : Nat) : Prop :=
  ∃ pre r post st, rs = pre ++ r :: post ∧
    pre.foldlM (JauneConsensus.Gloas.processBuilderDepositRequest ctx) s0 = .ok st ∧
    classifyBuilderDeposit ctx.cfg ctx.blsActive st r = .ok (.topUp i r.amount true)

theorem TopUpResetIn.snoc {ctx : Ctx} {s0 : JauneConsensus.Gloas.BeaconState P}
    {L : List JauneConsensus.Gloas.BuilderDepositRequest} {i : Nat} (h : TopUpResetIn ctx s0 L i)
    (x : JauneConsensus.Gloas.BuilderDepositRequest) : TopUpResetIn ctx s0 (L ++ [x]) i := by
  obtain ⟨pre, r, post, st, rfl, h1, h2⟩ := h
  exact ⟨pre, r, post ++ [x], st, by simp, h1, h2⟩

/-- The slot-`i` invariant of the deposit loop: builder `i` keeps its pubkey and
`withdrawable_epoch`, or a reset top-up of `i` happened, or `i` holds a different (fresh) builder
with `withdrawable_epoch = FAR_FUTURE_EPOCH`. -/
def DepositSlotInv (ctx : Ctx) (s0 : JauneConsensus.Gloas.BeaconState P)
    (L : List JauneConsensus.Gloas.BuilderDepositRequest) (i : Nat) (b : JauneConsensus.Gloas.Builder)
    (x : JauneConsensus.Gloas.BeaconState P) : Prop :=
  x.slot = s0.slot ∧ ∃ c, x.builders.toArray[i]? = some c ∧
    ((c.pubkey = b.pubkey ∧ c.withdrawable_epoch = b.withdrawable_epoch) ∨
      TopUpResetIn ctx s0 L i ∨
      (c.pubkey ≠ b.pubkey ∧ c.withdrawable_epoch = FAR_FUTURE_EPOCH))

theorem depositSlotInv_step (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx}
    {s0 st st' : JauneConsensus.Gloas.BeaconState P}
    {pre : List JauneConsensus.Gloas.BuilderDepositRequest} {r : JauneConsensus.Gloas.BuilderDepositRequest}
    {i : Nat} {b : JauneConsensus.Gloas.Builder}
    (hpre : pre.foldlM (JauneConsensus.Gloas.processBuilderDepositRequest ctx) s0 = .ok st)
    (hinv : DepositSlotInv ctx s0 pre i b st)
    (h : JauneConsensus.Gloas.processBuilderDepositRequest ctx st r = .ok st') :
    DepositSlotInv ctx s0 (pre ++ [r]) i b st' := by
  obtain ⟨hsl, c, hc, hcase⟩ := hinv
  obtain ⟨hsl', _, hat⟩ := processBuilderDepositRequest_at h i
  refine ⟨hsl'.trans hsl, ?_⟩
  have keep : ∀ c' : JauneConsensus.Gloas.Builder, c'.pubkey = c.pubkey →
      c'.withdrawable_epoch = c.withdrawable_epoch →
      ((c'.pubkey = b.pubkey ∧ c'.withdrawable_epoch = b.withdrawable_epoch) ∨
        TopUpResetIn ctx s0 (pre ++ [r]) i ∨
        (c'.pubkey ≠ b.pubkey ∧ c'.withdrawable_epoch = FAR_FUTURE_EPOCH)) := by
    intro c' hp hw
    rcases hcase with ⟨h1, h2⟩ | hR | ⟨h1, h2⟩
    · exact Or.inl ⟨hp.trans h1, hw.trans h2⟩
    · exact Or.inr (Or.inl (hR.snoc r))
    · exact Or.inr (Or.inr ⟨hp ▸ h1, hw.trans h2⟩)
  rcases hat with heq | ⟨c0, c', reset, hc0, hc', hcl, hpk, _, hres, _⟩ |
      ⟨addr, e, _, he, hat', hall, hreuse⟩
  · rw [heq]; exact ⟨c, hc, keep c rfl rfl⟩
  · rw [hc] at hc0; cases hc0
    refine ⟨c', hc', ?_⟩
    cases reset with
    | false => exact keep c' hpk (hres rfl)
    | true => exact Or.inr (Or.inl ⟨pre, r, [], st, rfl, hpre, hcl⟩)
  · refine ⟨_, hat', ?_⟩
    obtain ⟨hwle, _⟩ := hreuse c hc
    rcases hcase with ⟨h1, _⟩ | hR | ⟨_, h2⟩
    · refine Or.inr (Or.inr ⟨fun heqpk => ?_, rfl⟩)
      exact hall c (Array.mem_of_getElem? hc) (h1.trans heqpk.symm)
    · exact Or.inr (Or.inl (hR.snoc r))
    · rw [h2] at hwle
      exact absurd hwle (not_far_le_epoch hspe he)

theorem depositSlotInv_loop (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx}
    {s0 s1 : JauneConsensus.Gloas.BeaconState P} {i : Nat} {b : JauneConsensus.Gloas.Builder} :
    ∀ (rest pre : List JauneConsensus.Gloas.BuilderDepositRequest) (st : JauneConsensus.Gloas.BeaconState P),
      pre.foldlM (JauneConsensus.Gloas.processBuilderDepositRequest ctx) s0 = .ok st →
      DepositSlotInv ctx s0 pre i b st →
      rest.foldlM (JauneConsensus.Gloas.processBuilderDepositRequest ctx) st = .ok s1 →
      DepositSlotInv ctx s0 (pre ++ rest) i b s1 := by
  intro rest
  induction rest with
  | nil =>
    intro pre st _ hinv h
    cases h
    simpa using hinv
  | cons r rest ih =>
    intro pre st hpre hinv h
    rw [List.foldlM_cons] at h
    obtain ⟨st', h1, h2⟩ := bind_eq_ok_iff.mp h
    have := ih (pre ++ [r]) st' (foldlM_snoc_ok hpre h1) (depositSlotInv_step hspe hpre hinv h1) h2
    simpa using this

/-- **B3, the deposit loop.** Across a list of builder deposits, builder slot `i` keeps its pubkey
and `withdrawable_epoch`, or one of the deposits is a reset top-up of `i`, or `i` ends holding a
different builder with `withdrawable_epoch = FAR_FUTURE_EPOCH` (a fresh record on a reused
slot). Needs `2 <= SLOTS_PER_EPOCH` (`ValidJointG.slotsPerEpoch`). -/
theorem builderDeposits_slot (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx}
    {s0 s1 : JauneConsensus.Gloas.BeaconState P} {rs : List JauneConsensus.Gloas.BuilderDepositRequest}
    (h : rs.foldlM (JauneConsensus.Gloas.processBuilderDepositRequest ctx) s0 = .ok s1)
    {i : Nat} {b : JauneConsensus.Gloas.Builder} (hb : s0.builders.toArray[i]? = some b) :
    DepositSlotInv ctx s0 rs i b s1 := by
  have := depositSlotInv_loop hspe rs [] s0 rfl ⟨rfl, b, hb, Or.inl ⟨rfl, rfl⟩⟩ h
  simpa using this

/-- A builder exit in the list `es`, reached from `s1` through the exits before it, is classified
`initiate i` (so it passed the source check, `classifyBuilderExit_meaning`). -/
def ExitInitiateIn (cfg : Config) (s1 : JauneConsensus.Gloas.BeaconState P)
    (es : List JauneConsensus.Gloas.BuilderExitRequest) (i : Nat) : Prop :=
  ∃ pre e post st, es = pre ++ e :: post ∧
    pre.foldlM (JauneConsensus.Gloas.processBuilderExitRequest cfg) s1 = .ok st ∧
    classifyBuilderExit cfg st e = .ok (.initiate i)

theorem ExitInitiateIn.snoc {cfg : Config} {s1 : JauneConsensus.Gloas.BeaconState P}
    {L : List JauneConsensus.Gloas.BuilderExitRequest} {i : Nat} (h : ExitInitiateIn cfg s1 L i)
    (x : JauneConsensus.Gloas.BuilderExitRequest) : ExitInitiateIn cfg s1 (L ++ [x]) i := by
  obtain ⟨pre, r, post, st, rfl, h1, h2⟩ := h
  exact ⟨pre, r, post ++ [x], st, by simp, h1, h2⟩

/-- The slot-`i` invariant of the exit loop. -/
def ExitSlotInv (cfg : Config) (s1 : JauneConsensus.Gloas.BeaconState P)
    (L : List JauneConsensus.Gloas.BuilderExitRequest) (i : Nat) (c : JauneConsensus.Gloas.Builder)
    (x : JauneConsensus.Gloas.BeaconState P) : Prop :=
  x.slot = s1.slot ∧ ∃ c', x.builders.toArray[i]? = some c' ∧ c'.pubkey = c.pubkey ∧
    (c'.withdrawable_epoch = c.withdrawable_epoch ∨
      (c.withdrawable_epoch = FAR_FUTURE_EPOCH ∧ ExitInitiateIn cfg s1 L i))

theorem exitSlotInv_loop {cfg : Config} {s1 s2 : JauneConsensus.Gloas.BeaconState P} {i : Nat}
    {c : JauneConsensus.Gloas.Builder} :
    ∀ (rest pre : List JauneConsensus.Gloas.BuilderExitRequest) (st : JauneConsensus.Gloas.BeaconState P),
      pre.foldlM (JauneConsensus.Gloas.processBuilderExitRequest cfg) s1 = .ok st →
      ExitSlotInv cfg s1 pre i c st →
      rest.foldlM (JauneConsensus.Gloas.processBuilderExitRequest cfg) st = .ok s2 →
      ExitSlotInv cfg s1 (pre ++ rest) i c s2 := by
  intro rest
  induction rest with
  | nil =>
    intro pre st _ hinv h
    cases h
    simpa using hinv
  | cons r rest ih =>
    intro pre st hpre hinv h
    rw [List.foldlM_cons] at h
    obtain ⟨st', h1, h2⟩ := bind_eq_ok_iff.mp h
    have hstep : ExitSlotInv cfg s1 (pre ++ [r]) i c st' := by
      obtain ⟨hsl, c', hc', hpk, hcase⟩ := hinv
      obtain ⟨hsl', _, hat⟩ := processBuilderExitRequest_at h1 i
      refine ⟨hsl'.trans hsl, ?_⟩
      rcases hat with heq | ⟨c0, w, hc0, hc'', hcl, _, hfar⟩
      · rw [heq]
        refine ⟨c', hc', hpk, ?_⟩
        rcases hcase with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2.snoc r⟩
      · rw [hc'] at hc0; cases hc0
        refine ⟨_, hc'', hpk, Or.inr ⟨?_, ?_⟩⟩
        · rcases hcase with h | ⟨h1, _⟩
          · rw [← h]; exact hfar
          · exact h1
        · exact ⟨pre, r, [], st, rfl, hpre, hcl⟩
    simpa using ih (pre ++ [r]) st' (foldlM_snoc_ok hpre h1) hstep h2

/-- **B3, the exit loop.** Across a list of builder exits, builder slot `i` keeps its pubkey, and
its `withdrawable_epoch` is unchanged or it was `FAR_FUTURE_EPOCH` and one of the exits was
classified `initiate i`. -/
theorem builderExits_slot {cfg : Config} {s1 s2 : JauneConsensus.Gloas.BeaconState P}
    {es : List JauneConsensus.Gloas.BuilderExitRequest}
    (h : es.foldlM (JauneConsensus.Gloas.processBuilderExitRequest cfg) s1 = .ok s2)
    {i : Nat} {c : JauneConsensus.Gloas.Builder} (hc : s1.builders.toArray[i]? = some c) :
    ExitSlotInv cfg s1 es i c s2 := by
  have := exitSlotInv_loop es [] s1 rfl ⟨rfl, c, hc, rfl, Or.inl rfl⟩ h
  simpa using this


/-! ## B1: same-payload register then top-up -/

theorem firstMatch_of_first {bs : ProgressiveListR JauneConsensus.Gloas.Builder} {pk : BLSPubkey}
    {i : Nat} {b : JauneConsensus.Gloas.Builder} (hb : bs.toArray[i]? = some b) (hpk : b.pubkey = pk)
    (hfirst : ∀ j, j < i → ∀ b', bs.toArray[j]? = some b' → b'.pubkey ≠ pk) :
    firstMatch bs pk = some i := by
  unfold firstMatch
  rw [Array.findIdx?_eq_some_iff_getElem]
  have hi : i < bs.toArray.size := by
    rcases Nat.lt_or_ge i bs.toArray.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hb; cases hb
  refine ⟨hi, ?_, fun j hj hp => ?_⟩
  · rw [Array.getElem?_eq_getElem hi] at hb
    cases hb
    exact pubkey_beq_iff.mpr hpk
  · exact hfirst j hj _ (Array.getElem?_eq_getElem _) (pubkey_beq_iff.mp hp)

/-- The register-then-top-up invariant: slot `i` holds the fresh record with an accumulated
balance, and no earlier slot carries its pubkey. -/
def RegInv (m : JauneConsensus.Gloas.BeaconState P) (i : Nat) (fresh : JauneConsensus.Gloas.Builder)
    (acc : Nat) (x : JauneConsensus.Gloas.BeaconState P) : Prop :=
  x.slot = m.slot ∧ (∃ bal : U64, x.builders.toArray[i]? = some { fresh with balance := bal } ∧
      bal.toNat = acc) ∧
    ∀ j, j < i → ∀ b', x.builders.toArray[j]? = some b' → b'.pubkey ≠ fresh.pubkey

theorem regInv_step (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx}
    {m x x' : JauneConsensus.Gloas.BeaconState P} {i : Nat} {fresh : JauneConsensus.Gloas.Builder}
    (hfar : fresh.withdrawable_epoch = FAR_FUTURE_EPOCH) {acc : Nat}
    {r' : JauneConsensus.Gloas.BuilderDepositRequest} (hinv : RegInv m i fresh acc x)
    (h : JauneConsensus.Gloas.processBuilderDepositRequest ctx x r' = .ok x') :
    RegInv m i fresh (acc + if (r'.pubkey == fresh.pubkey &&
      JauneConsensus.Gloas.isBuilderWithdrawalCredential r'.withdrawal_credentials) = true
      then r'.amount.toNat else 0) x' := by
  obtain ⟨hsl, ⟨bal, hbi, hbal⟩, hfirst⟩ := hinv
  have hfm : firstMatch x.builders fresh.pubkey = some i := firstMatch_of_first hbi rfl hfirst
  have h0 := h
  rw [processBuilderDepositRequest_eq] at h0
  obtain ⟨o, hco, _⟩ := bind_eq_ok_iff.mp h0
  obtain ⟨hpre, hbad, htop, hreg⟩ := classifyBuilderDeposit_effect hco h
  have hslot : x'.slot = x.slot := by rw [(processBuilderDepositRequest_frame h).2.2.2.2.2]
  -- the earlier slots never gain `fresh.pubkey`
  have hfirst' : ∀ j, j < i → ∀ b', x'.builders.toArray[j]? = some b' → b'.pubkey ≠ fresh.pubkey := by
    intro j hj b' hb'
    obtain ⟨_, _, hat⟩ := processBuilderDepositRequest_at h j
    rcases hat with heq | ⟨c, c', _, hc, hc', _, hpk, _⟩ | ⟨addr, e, _, _, hat', hall, _⟩
    · rw [heq] at hb'; exact hfirst j hj b' hb'
    · rw [hc'] at hb'; cases hb'; rw [hpk]; exact hfirst j hj c hc
    · rw [hat'] at hb'; cases hb'
      intro hpk
      exact hall _ (Array.mem_of_getElem? hbi) hpk.symm
  refine ⟨hslot.trans hsl, ?_, hfirst'⟩
  rcases classifyBuilderDeposit_inv hco with ⟨hp, rfl⟩ | ⟨hp, j, c, hfmj, hc, rfl⟩ |
    ⟨hp, hfmn, _, _, ⟨_, rfl⟩ | ⟨_, _, idx, _, _, rfl⟩⟩
  · rw [hpre rfl]
    refine ⟨bal, hbi, ?_⟩
    simp [hp, hbal]
  · by_cases hpk : r'.pubkey = fresh.pubkey
    · rw [hpk, hfm] at hfmj; cases hfmj
      rw [hbi] at hc; cases hc
      obtain ⟨c0, c', hc0, hc', _, _, hpk', hver, hex, hdep, hb', _, hwe, _⟩ :=
        htop i r'.amount _ rfl
      rw [hbi] at hc0; cases hc0
      have hreset : ({ fresh with balance := bal }.withdrawable_epoch != FAR_FUTURE_EPOCH &&
          { fresh with balance := bal }.balance == U64.zero) = false := by
        simp [hfar]
      rw [hreset] at hwe
      have hwe' := hwe rfl
      refine ⟨c'.balance, ?_, ?_⟩
      · rw [hc']
        cases c'
        simp only at hpk' hver hex hdep hwe' ⊢
        rw [hpk', hver, hex, hdep, hwe']
      · rw [hb', hbal]
        simp [hpk, hp, pubkey_beq_iff.mpr rfl]
    · have hj : j ≠ i := by
        intro hji; subst hji
        obtain ⟨⟨b0, hb0, hpk0⟩, _⟩ := firstMatch_some hfmj
        rw [hbi] at hb0; cases hb0
        exact hpk hpk0.symm
      obtain ⟨_, _, _, _, _, hne, _⟩ := htop j r'.amount _ rfl
      refine ⟨bal, by rw [hne i (Ne.symm hj)]; exact hbi, ?_⟩
      have : (r'.pubkey == fresh.pubkey) = false := by
        cases hh : (r'.pubkey == fresh.pubkey) with
        | false => rfl
        | true => exact absurd (pubkey_beq_iff.mp hh) hpk
      simp [this, hbal]
  · rw [hbad rfl]
    refine ⟨bal, hbi, ?_⟩
    have hne : r'.pubkey ≠ fresh.pubkey := fun heq =>
      firstMatch_none_iff.mp hfmn _ (Array.mem_of_getElem? hbi) heq.symm
    have : (r'.pubkey == fresh.pubkey) = false := by
      cases hh : (r'.pubkey == fresh.pubkey) with
      | false => rfl
      | true => exact absurd (pubkey_beq_iff.mp hh) hne
    simp [this, hbal]
  · have hne : r'.pubkey ≠ fresh.pubkey := fun heq =>
      firstMatch_none_iff.mp hfmn _ (Array.mem_of_getElem? hbi) heq.symm
    have : (r'.pubkey == fresh.pubkey) = false := by
      cases hh : (r'.pubkey == fresh.pubkey) with
      | false => rfl
      | true => exact absurd (pubkey_beq_iff.mp hh) hne
    obtain ⟨_, _, hat⟩ := processBuilderDepositRequest_at h i
    rcases hat with heq | ⟨_, _, _, _, _, hcl, _⟩ | ⟨_, e, _, he, _, _, hreuse⟩
    · refine ⟨bal, by rw [heq]; exact hbi, ?_⟩
      simp [this, hbal]
    · rw [hco] at hcl; cases hcl
    · obtain ⟨hwle, _⟩ := hreuse _ hbi
      simp only [hfar] at hwle
      exact absurd hwle (not_far_le_epoch hspe he)

theorem regInv_loop (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx} {m s2 : JauneConsensus.Gloas.BeaconState P}
    {i : Nat} {fresh : JauneConsensus.Gloas.Builder} (hfar : fresh.withdrawable_epoch = FAR_FUTURE_EPOCH) :
    ∀ (rest : List JauneConsensus.Gloas.BuilderDepositRequest) (x : JauneConsensus.Gloas.BeaconState P)
      (acc : Nat), RegInv m i fresh acc x →
      rest.foldlM (JauneConsensus.Gloas.processBuilderDepositRequest ctx) x = .ok s2 →
      RegInv m i fresh (acc + ((rest.filter (fun r' => r'.pubkey == fresh.pubkey &&
        JauneConsensus.Gloas.isBuilderWithdrawalCredential r'.withdrawal_credentials)).map
          (·.amount.toNat)).sum) s2 := by
  intro rest
  induction rest with
  | nil => intro x acc hinv h; cases h; simpa using hinv
  | cons r' rest ih =>
    intro x acc hinv h
    rw [List.foldlM_cons] at h
    obtain ⟨x', h1, h2⟩ := bind_eq_ok_iff.mp h
    have := ih x' _ (regInv_step hspe hfar hinv h1) h2
    by_cases hc : (r'.pubkey == fresh.pubkey &&
        JauneConsensus.Gloas.isBuilderWithdrawalCredential r'.withdrawal_credentials) = true
    · simp only [hc, ↓reduceIte] at this
      simp only [List.filter_cons, hc, ↓reduceIte, List.map_cons, List.sum_cons]
      rwa [Nat.add_assoc] at this
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at this
      simpa [List.filter_cons, hc] using this

/-- **B1, same-payload register then top-up (F1).** A builder deposit classified `register i`
writes the fresh record at `i` (`m1`); after the later deposits of the same list, builder `i` is
that record with balance `amount + Σ amounts of the later 0xB0 deposits for its pubkey`: no
reset, no reuse of the slot, no change to any other field. Needs `2 <= SLOTS_PER_EPOCH`. -/
theorem register_then_topUp (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx}
    {m m1 m2 : JauneConsensus.Gloas.BeaconState P} {r : JauneConsensus.Gloas.BuilderDepositRequest}
    {rs : List JauneConsensus.Gloas.BuilderDepositRequest} {i : Nat} {a : U64}
    (hc : classifyBuilderDeposit ctx.cfg ctx.blsActive m r = .ok (.register i a))
    (h1 : JauneConsensus.Gloas.processBuilderDepositRequest ctx m r = .ok m1)
    (h2 : rs.foldlM (JauneConsensus.Gloas.processBuilderDepositRequest ctx) m1 = .ok m2) :
    ∃ addr e bal, Jaune.Bytes.toAdr? (r.withdrawal_credentials.toBytes.drop 12) = some addr ∧
      computeEpochAtSlot P m.slot = .ok e ∧
      m1.builders.toArray[i]? = some (freshBuilder r.pubkey addr r.amount e) ∧
      m2.builders.toArray[i]? = some { freshBuilder r.pubkey addr r.amount e with balance := bal } ∧
      bal.toNat = r.amount.toNat + ((rs.filter (fun r' => r'.pubkey == r.pubkey &&
        JauneConsensus.Gloas.isBuilderWithdrawalCredential r'.withdrawal_credentials)).map
          (·.amount.toNat)).sum := by
  obtain ⟨_, _, _, hregm⟩ := classifyBuilderDeposit_meaning hc
  obtain ⟨_, hall, _, ha, _⟩ := (hregm i a).mp rfl
  subst ha
  obtain ⟨_, _, _, hreg⟩ := classifyBuilderDeposit_effect hc h1
  obtain ⟨addr, e, haddr, he, hat, _, hne, _⟩ := hreg i r.amount rfl
  have hslot : m1.slot = m.slot := by rw [(processBuilderDepositRequest_frame h1).2.2.2.2.2]
  have hinv : RegInv m i (freshBuilder r.pubkey addr r.amount e) r.amount.toNat m1 := by
    refine ⟨hslot, ⟨r.amount, by rw [hat]; rfl, rfl⟩, fun j hj b' hb' => ?_⟩
    rw [hne j (Nat.ne_of_lt hj)] at hb'
    exact hall b' (Array.mem_of_getElem? hb')
  obtain ⟨_, ⟨bal, hbal2, hbaln⟩, _⟩ := regInv_loop hspe rfl rs m1 _ hinv h2
  exact ⟨addr, e, bal, haddr, he, hat, hbal2, hbaln⟩

end JauneConsensus.Facts.Gloas
