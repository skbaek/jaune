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

end JauneConsensus.Facts.Gloas
