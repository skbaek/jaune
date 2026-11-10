import JauneConsensus.Facts.ConsolidationRequest
import JauneConsensus.Epoch

/-!
# Facts: what `process_pending_deposits` and `apply_pending_deposit` do

About `JauneConsensus.applyPendingDeposit` and `JauneConsensus.processPendingDeposits`
(`JauneConsensus/Epoch.lean`), transcribed from `v1.7.0-beta.4` `specs/electra/beacon-chain.md`
(Fulu's override drops the Eth1-bridge break). In the shape of `Facts/WithdrawalRequest.lean`:

* `classifyPendingDeposit` reads, in the spec's order, which of the three outcomes of
  `apply_pending_deposit` a deposit has: a new validator (the key is unknown and the proof of
  possession verifies under Jaune's BLS), a top-up of the first validator with the key, or no
  credit (the key is unknown and the signature does not verify). `applyPendingDepositOutcome`
  carries each out, and `applyPendingDeposit_eq` says the function is their composition. The
  per-outcome lemmas state the credit: the amount credited is the deposit's amount.
* `classifyPendingDepositStep` reads, in the spec's order, what one iteration of the loop of
  `process_pending_deposits` does with a deposit: stop (the Eth1 bridge is not yet drained, before
  Fulu; the deposit is not finalized; the per-epoch count is reached; the churn is exhausted),
  apply it without consuming churn (its validator is withdrawn), postpone it (its validator is
  exiting), or apply it consuming churn. `pendingDepositsLoop` is the loop as a recursion over the
  queue, and `processPendingDeposits_eq` says the function is that loop between the spec's
  preamble and epilogue.

Nothing here edits a spec definition.
-/

namespace JauneConsensus.Facts

open JauneConsensus

variable {P : Preset} {f : CFork}

/-! ## `apply_pending_deposit` -/

/-- What `apply_pending_deposit` does with one deposit. -/
inductive PendingDepositOutcome where
  /-- The key is not a validator's and the proof of possession verifies: a validator is added
  with the deposit's key, credentials and amount. -/
  | newValidator
  /-- The key is the first validator with it, at `index`: its balance increases by the amount. -/
  | topUp (index : ValidatorIndex)
  /-- The key is not a validator's and the proof of possession does not verify: nothing is
  credited. -/
  | noCredit
  deriving DecidableEq, Repr

/-- Which outcome `apply_pending_deposit` gives `deposit`, with the same reads as the function, in
the spec's order. Changes no state. -/
def classifyPendingDeposit (ctx : Ctx) (state : BeaconState P f) (deposit : PendingDeposit) :
    M PendingDepositOutcome := do
  match findValidatorIndex state deposit.pubkey with
  | none =>
    if ← isValidDepositSignature ctx deposit.pubkey deposit.withdrawal_credentials deposit.amount
        deposit.signature then
      pure .newValidator
    else pure .noCredit
  | some i => pure (.topUp (← U64.ofNat? i "ValidatorIndex"))

/-- The state change of each outcome. -/
def applyPendingDepositOutcome (state : BeaconState P f) (deposit : PendingDeposit) :
    PendingDepositOutcome → M (BeaconState P f)
  | .newValidator =>
    addValidatorToRegistry state deposit.pubkey deposit.withdrawal_credentials deposit.amount
  | .topUp index => increaseBalance state index deposit.amount
  | .noCredit => pure state

/-- Equational characterization: `apply_pending_deposit` is classify-then-apply. -/
theorem applyPendingDeposit_eq (ctx : Ctx) (state : BeaconState P f) (deposit : PendingDeposit) :
    applyPendingDeposit ctx state deposit =
      classifyPendingDeposit ctx state deposit >>= applyPendingDepositOutcome state deposit := by
  unfold applyPendingDeposit classifyPendingDeposit
  cases findValidatorIndex state deposit.pubkey with
  | none =>
    dsimp only
    cases hs : isValidDepositSignature ctx deposit.pubkey deposit.withdrawal_credentials
        deposit.amount deposit.signature with
    | error e => rfl
    | ok b => cases b <;> rfl
  | some i =>
    dsimp only
    cases U64.ofNat? i "ValidatorIndex" <;> rfl

/-- No credit leaves the state unchanged. -/
theorem applyPendingDeposit_noCredit {state : BeaconState P f} {deposit : PendingDeposit} :
    applyPendingDepositOutcome state deposit .noCredit = pure state := rfl

/-- The signing check of a deposit's proof of possession, unfolded: under `ctx.blsActive` it is
`bls.Verify(pubkey, compute_signing_root(DepositMessage(pubkey, credentials, amount), domain),
signature)` with `domain = compute_domain(DOMAIN_DEPOSIT)` (genesis fork version, zero root). -/
theorem isValidDepositSignature_true {ctx : Ctx} {pk : BLSPubkey} {wc : Bytes32} {amount : U64}
    {sig : BLSSignature} (h : isValidDepositSignature ctx pk wc amount sig = .ok true) :
    ∃ domain, computeDomainDefault ctx.cfg DOMAIN_DEPOSIT = .ok domain ∧
      blsVerify ctx.blsActive pk
        (computeSigningRoot ({ pubkey := pk, withdrawal_credentials := wc, amount } : DepositMessage)
          domain) sig = true := by
  unfold isValidDepositSignature at h
  obtain ⟨domain, hd, h⟩ := bind_ok_elim h
  exact ⟨domain, hd, Except.ok.inj h⟩

/-- **D-S9, the new-validator outcome**: the key is no validator's, and the proof of possession
verifies (`is_valid_deposit_signature`, which under `ctx.blsActive` is Jaune's BLS
`Verify`). -/
theorem classifyPendingDeposit_newValidator {ctx : Ctx} {state : BeaconState P f}
    {deposit : PendingDeposit}
    (h : classifyPendingDeposit ctx state deposit = .ok .newValidator) :
    findValidatorIndex state deposit.pubkey = none ∧
    isValidDepositSignature ctx deposit.pubkey deposit.withdrawal_credentials deposit.amount
      deposit.signature = .ok true := by
  unfold classifyPendingDeposit at h
  cases hf : findValidatorIndex state deposit.pubkey with
  | none =>
    rw [hf] at h
    dsimp only at h
    obtain ⟨b, hb, h⟩ := bind_ok_elim h
    cases b
    · cases h
    · exact ⟨rfl, hb⟩
  | some i =>
    rw [hf] at h
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok_elim h
    cases h

/-- **D-S9, the no-credit outcome**: the key is no validator's and the proof of possession does
not verify. Nothing is credited: the state is unchanged (the deposit's ETH stays in the deposit
contract, with no validator). -/
theorem classifyPendingDeposit_noCredit {ctx : Ctx} {state : BeaconState P f}
    {deposit : PendingDeposit}
    (h : classifyPendingDeposit ctx state deposit = .ok .noCredit) :
    findValidatorIndex state deposit.pubkey = none ∧
    isValidDepositSignature ctx deposit.pubkey deposit.withdrawal_credentials deposit.amount
      deposit.signature = .ok false := by
  unfold classifyPendingDeposit at h
  cases hf : findValidatorIndex state deposit.pubkey with
  | none =>
    rw [hf] at h
    dsimp only at h
    obtain ⟨b, hb, h⟩ := bind_ok_elim h
    cases b
    · exact ⟨rfl, hb⟩
    · cases h
  | some i =>
    rw [hf] at h
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok_elim h
    cases h

/-- **D-S9, the top-up outcome**: the key is a validator's, and `index` is the first validator
with it. -/
theorem classifyPendingDeposit_topUp {ctx : Ctx} {state : BeaconState P f}
    {deposit : PendingDeposit} {index : ValidatorIndex}
    (h : classifyPendingDeposit ctx state deposit = .ok (.topUp index)) :
    findValidatorIndex state deposit.pubkey = some index.toNat := by
  unfold classifyPendingDeposit at h
  cases hf : findValidatorIndex state deposit.pubkey with
  | none =>
    rw [hf] at h
    dsimp only at h
    obtain ⟨b, hb, h⟩ := bind_ok_elim h
    cases b <;> cases h
  | some i =>
    rw [hf] at h
    dsimp only at h
    obtain ⟨j, hj, h⟩ := bind_ok_elim h
    cases h
    rw [U64.toNat_ofNat? hj]

/-! ## Balance mutators, elementwise -/

/-- `increase_balance` adds `d` (checked) at `i` and changes no other balance and no other
field. -/
theorem increaseBalance_spec {s s' : BeaconState P f} {i : ValidatorIndex} {d : Gwei}
    (h : increaseBalance s i d = .ok s') :
    ∃ b b', s.balances.toArray[i.toNat]? = some b ∧ U64.add? b d "increase_balance" = .ok b' ∧
      (∀ j, s'.balances.toArray[j]? =
        if j = i.toNat then some b' else s.balances.toArray[j]?) ∧
      s' = { s with balances := s'.balances } := by
  unfold increaseBalance at h
  obtain ⟨bals, hmod, h⟩ := bind_ok_elim h
  cases h
  unfold SszList.modify at hmod
  obtain ⟨b, hget, hmod⟩ := bind_ok_elim hmod
  obtain ⟨b', hadd, hset⟩ := bind_ok_elim hmod
  obtain ⟨hi, hbals⟩ := set_ok hset
  refine ⟨b, b', get_ok hget, hadd, ?_, rfl⟩
  intro j
  show bals.toArray[j]? = _
  rw [hbals, Array.getElem?_set]
  by_cases hj : j = i.toNat
  · subst hj; simp
  · simp [hj, Ne.symm hj]

/-- `decrease_balance` subtracts `d` at `i`, saturating at zero, and changes no other balance and
no other field. -/
theorem decreaseBalance_spec {s s' : BeaconState P f} {i : ValidatorIndex} {d : Gwei}
    (h : decreaseBalance s i d = .ok s') :
    ∃ b b', s.balances.toArray[i.toNat]? = some b ∧
      b'.toNat = (if b.toNat < d.toNat then 0 else b.toNat - d.toNat) ∧
      (∀ j, s'.balances.toArray[j]? =
        if j = i.toNat then some b' else s.balances.toArray[j]?) ∧
      s' = { s with balances := s'.balances } := by
  unfold decreaseBalance at h
  obtain ⟨bals, hmod, h⟩ := bind_ok_elim h
  cases h
  unfold SszList.modify at hmod
  obtain ⟨b, hget, hmod⟩ := bind_ok_elim hmod
  obtain ⟨b', hsub, hset⟩ := bind_ok_elim hmod
  obtain ⟨hi, hbals⟩ := set_ok hset
  refine ⟨b, b', get_ok hget, ?_, ?_, rfl⟩
  · dsimp only at hsub
    split at hsub
    · rename_i hlt
      cases hsub
      have : b.toNat < d.toNat := hlt
      simp [this, U64.toNat_zero]
    · rename_i hlt
      have : ¬ b.toNat < d.toNat := hlt
      simp only [this, ite_false]
      have := U64.toNat_sub? hsub
      omega
  · intro j
    show bals.toArray[j]? = _
    rw [hbals, Array.getElem?_set]
    by_cases hj : j = i.toNat
    · subst hj; simp
    · simp [hj, Ne.symm hj]

/-- **D-S9 credit, top-up**: a top-up credits exactly the deposit's amount to the first validator
with the key, and changes no other balance and no validator. -/
theorem applyPendingDeposit_topUp_credit {state s' : BeaconState P f} {deposit : PendingDeposit}
    {i : ValidatorIndex} (h : applyPendingDepositOutcome state deposit (.topUp i) = .ok s') :
    ∃ b b', state.balances.toArray[i.toNat]? = some b ∧
      b'.toNat = b.toNat + deposit.amount.toNat ∧
      (∀ j, s'.balances.toArray[j]? =
        if j = i.toNat then some b' else state.balances.toArray[j]?) ∧
      s'.validators = state.validators := by
  obtain ⟨b, b', hb, hadd, hj, hs'⟩ := increaseBalance_spec h
  refine ⟨b, b', hb, U64.toNat_add? hadd, hj, ?_⟩
  rw [hs']

/-- `set_or_append_list` at the list's length appends. -/
theorem setOrAppendList_at_length {α : Type} {n : Nat} {xs ys : SszList α n} {index : ValidatorIndex}
    {v : α} {site : String} (hi : index.toNat = xs.toArray.size)
    (h : setOrAppendList xs index v site = .ok ys) : ys.toArray = xs.toArray.push v := by
  unfold setOrAppendList at h
  have hb : (index.toNat == xs.length) = true := by
    simp only [SszList.length, hi, beq_self_eq_true]
  rw [ite_eq_left hb] at h
  exact push_ok h

/-- **D-S9 credit, new validator**: on a state whose balance list is as long as its registry, a
new validator is appended to the registry with the deposit's key and credentials, and the
deposit's amount is appended as its balance. -/
theorem applyPendingDeposit_newValidator_credit {state s' : BeaconState P f}
    {deposit : PendingDeposit}
    (hlen : state.balances.toArray.size = state.validators.toArray.size)
    (h : applyPendingDepositOutcome state deposit .newValidator = .ok s') :
    ∃ v, s'.validators.toArray = state.validators.toArray.push v ∧
      v.pubkey = deposit.pubkey ∧ v.withdrawal_credentials = deposit.withdrawal_credentials ∧
      s'.balances.toArray = state.balances.toArray.push deposit.amount := by
  unfold applyPendingDepositOutcome addValidatorToRegistry at h
  obtain ⟨index, hindex, h⟩ := bind_ok_elim h
  obtain ⟨v, hv, h⟩ := bind_ok_elim h
  obtain ⟨vals, hvals, h⟩ := bind_ok_elim h
  obtain ⟨bals, hbals, h⟩ := bind_ok_elim h
  obtain ⟨p1, -, h⟩ := bind_ok_elim h
  obtain ⟨p2, -, h⟩ := bind_ok_elim h
  obtain ⟨p3, -, h⟩ := bind_ok_elim h
  cases h
  have hix : index.toNat = state.validators.toArray.size := U64.toNat_ofNat? hindex
  unfold getValidatorFromDeposit at hv
  obtain ⟨maxEb, -, hv⟩ := bind_ok_elim hv
  obtain ⟨m, -, hv⟩ := bind_ok_elim hv
  obtain ⟨r, -, hv⟩ := bind_ok_elim hv
  obtain ⟨rounded, -, hv⟩ := bind_ok_elim hv
  cases hv
  exact ⟨_, setOrAppendList_at_length hix hvals, rfl, rfl,
    setOrAppendList_at_length (hix.trans hlen.symm) hbals⟩

/-! ## The loop of `process_pending_deposits` -/

/-- The loop state of `process_pending_deposits`, in the spec's variable order:
`processed_amount`, `next_deposit_index`, `deposits_to_postpone`, `is_churn_limit_reached`, and
the state. -/
abbrev PendingDepositsAcc (P : Preset) (f : CFork) :=
  U64 × Nat × Array PendingDeposit × Bool × BeaconState P f

/-- One iteration of the loop of `process_pending_deposits`, with the loop's `break`s as `done`
and its fall-through as `yield`, reading in the spec's order: the Eth1-bridge break (before
Fulu), the finality break, the per-epoch count break; then the validator's exit and withdrawable
epochs (when the key is known); then: a withdrawn validator's deposit is applied without
consuming churn; an exiting validator's deposit is postponed; otherwise the churn break, or the
deposit is applied consuming churn. -/
def pendingDepositStep (ctx : Ctx) (nextEpoch availableForProcessing : U64) (finalizedSlot : Slot)
    (requestsStart : U64) (deposit : PendingDeposit) (acc : PendingDepositsAcc P f) :
    M (ForInStep (PendingDepositsAcc P f)) := do
  let site := "process_pending_deposits"
  let processedAmount := acc.1
  let nextDepositIndex := acc.2.1
  let depositsToPostpone := acc.2.2.1
  let isChurnLimitReached := acc.2.2.2.1
  let state := acc.2.2.2.2
  if (!(f.atLeast .fulu) && decide (deposit.slot > GENESIS_SLOT) &&
      decide (state.eth1_deposit_index < requestsStart)) = true then
    return .done acc
  if deposit.slot > finalizedSlot then return .done acc
  if nextDepositIndex ≥ P.MAX_PENDING_DEPOSITS_PER_EPOCH then return .done acc
  let flags ← match findValidatorIndex state deposit.pubkey with
    | some i => do
      let validator ← state.validators.get i site
      pure (decide (validator.exit_epoch < FAR_FUTURE_EPOCH),
        decide (validator.withdrawable_epoch < nextEpoch))
    | none => pure (false, false)
  if flags.2 = true then
    let state ← applyPendingDeposit ctx state deposit
    return .yield (processedAmount, nextDepositIndex + 1, depositsToPostpone, isChurnLimitReached, state)
  else if flags.1 = true then
    return .yield (processedAmount, nextDepositIndex + 1, depositsToPostpone.push deposit,
      isChurnLimitReached, state)
  else
    let pa ← processedAmount.add? deposit.amount site
    if decide (pa > availableForProcessing) = true then
      return .done (processedAmount, nextDepositIndex, depositsToPostpone, true, state)
    let state ← applyPendingDeposit ctx state deposit
    return .yield (pa, nextDepositIndex + 1, depositsToPostpone, false, state)

/-- The loop as a recursion over the queue. -/
def pendingDepositsLoop (ctx : Ctx) (nextEpoch availableForProcessing : U64) (finalizedSlot : Slot)
    (requestsStart : U64) : List PendingDeposit → PendingDepositsAcc P f → M (PendingDepositsAcc P f)
  | [], acc => pure acc
  | d :: ds, acc => do
    match ← pendingDepositStep ctx nextEpoch availableForProcessing finalizedSlot requestsStart d acc with
    | .done a => pure a
    | .yield a => pendingDepositsLoop ctx nextEpoch availableForProcessing finalizedSlot requestsStart ds a

/-- A `for` loop over a list whose body agrees pointwise with `step` is the recursion of
`step`. -/
theorem forIn_list_eq_loop {α β : Type} (body step : α → β → M (ForInStep β))
    (hb : ∀ a b, body a b = step a b) (loop : List α → β → M β)
    (hnil : ∀ b, loop [] b = pure b)
    (hcons : ∀ a as b, loop (a :: as) b = (do
      match ← step a b with
      | .done b => pure b
      | .yield b => loop as b)) :
    ∀ (xs : List α) (b : β), forIn xs b body = loop xs b := by
  intro xs
  induction xs with
  | nil => intro b; rw [hnil]; rfl
  | cons a as ih =>
    intro b
    rw [List.forIn_cons, hcons, hb]
    cases step a b with
    | error e => rfl
    | ok r =>
      cases r with
      | done b' => rfl
      | yield b' => exact ih b'

/-- The recursion is the `for` loop of the step. -/
theorem pendingDepositsLoop_eq_forIn (ctx : Ctx) (nextEpoch availableForProcessing : U64)
    (finalizedSlot : Slot) (requestsStart : U64) (xs : List PendingDeposit)
    (acc : PendingDepositsAcc P f) :
    pendingDepositsLoop ctx nextEpoch availableForProcessing finalizedSlot requestsStart xs acc =
      forIn xs acc (pendingDepositStep ctx nextEpoch availableForProcessing finalizedSlot
        requestsStart) :=
  (forIn_list_eq_loop _ _ (fun _ _ => rfl) _ (fun _ => by rw [pendingDepositsLoop])
    (fun _ _ _ => by rw [pendingDepositsLoop]; apply bind_congr; intro r; cases r <;> rfl)
    xs acc).symm

/-- **The equation of `process_pending_deposits`**: the spec's preamble (next epoch, the churn
available for processing, the finalized slot, the requests start index, the queue), then
`pendingDepositsLoop` over the queue from `(0, 0, [], False, state)`, then the epilogue: the queue
becomes the unprocessed suffix followed by the postponed deposits, and the churn carried forward is
`available - processed` if the churn limit was reached and zero otherwise. -/
theorem processPendingDeposits_eq (ctx : Ctx) (state : BeaconState P f) :
    processPendingDeposits ctx state = (do
      let site := "process_pending_deposits"
      let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
      let availableForProcessing ← (← state.depositBalanceToConsume).add?
        (← getActivationExitChurnLimit ctx.cfg state) site
      let finalizedSlot ← computeStartSlotAtEpoch P state.finalized_checkpoint.epoch
      let requestsStart ← state.depositRequestsStartIndex
      let pending ← state.pendingDeposits
      let r ← pendingDepositsLoop ctx nextEpoch availableForProcessing finalizedSlot requestsStart
        pending.toArray.toList (U64.zero, 0, #[], false, state)
      let rest := pending.toArray.extract r.2.1 pending.length ++ r.2.2.1
      let st ← r.2.2.2.2.setPendingDeposits (← SszList.ofArray rest site)
      if r.2.2.2.1 = true then st.setDepositBalanceToConsume (← availableForProcessing.sub? r.1 site)
      else st.setDepositBalanceToConsume U64.zero) := by
  unfold processPendingDeposits
  dsimp only
  simp only [pendingDepositsLoop_eq_forIn, Array.forIn_toList]
  apply bind_congr; intro e0
  apply bind_congr; intro nextEpoch
  apply bind_congr; intro db
  apply bind_congr; intro cl
  apply bind_congr; intro avail
  apply bind_congr; intro finalizedSlot
  apply bind_congr; intro requestsStart
  apply bind_congr; intro pending
  congr 1
  congr 1
  funext d acc
  rcases acc with ⟨pa, idx, post, flag, st⟩
  unfold pendingDepositStep
  dsimp only
  by_cases h1 : (!f.atLeast CFork.fulu && decide (d.slot > GENESIS_SLOT) &&
      decide (st.eth1_deposit_index < requestsStart)) = true
  · rw [ite_eq_left h1, ite_eq_left h1]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : d.slot > finalizedSlot
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2]
      by_cases h3 : idx ≥ P.MAX_PENDING_DEPOSITS_PER_EPOCH
      · rw [ite_eq_left h3, ite_eq_left h3]
      · rw [ite_eq_right h3, ite_eq_right h3]
        cases hf : findValidatorIndex st d.pubkey with
        | none =>
          simp only [pure_bind, Bool.false_eq_true, ite_false]
          cases hadd : pa.add? d.amount "process_pending_deposits" with
          | error e => rfl
          | ok x =>
            simp only [ok_bind']
            by_cases hc : decide (x > avail) = true
            · rw [ite_eq_left hc, ite_eq_left hc, hc]
            · have hc' : decide (x > avail) = false := by simpa using hc
              rw [ite_eq_right hc, ite_eq_right hc, hc']
        | some i =>
          dsimp only
          cases hv : st.validators.get i "process_pending_deposits" with
          | error e => rfl
          | ok v =>
            simp only [ok_bind', pure_bind]
            by_cases hw : decide (v.withdrawable_epoch < nextEpoch) = true
            · rw [ite_eq_left hw, ite_eq_left hw]
            · rw [ite_eq_right hw, ite_eq_right hw]
              by_cases he : decide (v.exit_epoch < FAR_FUTURE_EPOCH) = true
              · rw [ite_eq_left he, ite_eq_left he]
              · rw [ite_eq_right he, ite_eq_right he]
                cases hadd : pa.add? d.amount "process_pending_deposits" with
                | error e => rfl
                | ok x =>
                  simp only [ok_bind']
                  by_cases hc : decide (x > avail) = true
                  · rw [ite_eq_left hc, ite_eq_left hc, hc]
                  · have hc' : decide (x > avail) = false := by simpa using hc
                    rw [ite_eq_right hc, ite_eq_right hc, hc']

/-! ## The outcomes of one iteration, as the spec reads them -/

/-- The validator reads of one iteration: with no validator for the key, neither flag; with the
first validator `v` for the key, `exited = v.exit_epoch < FAR_FUTURE_EPOCH` and
`withdrawn = v.withdrawable_epoch < next_epoch`. -/
def PendingDepositFlags (state : BeaconState P f) (deposit : PendingDeposit) (nextEpoch : U64)
    (exited withdrawn : Bool) : Prop :=
  match findValidatorIndex state deposit.pubkey with
  | none => exited = false ∧ withdrawn = false
  | some i => ∃ v, state.validators.toArray[i]? = some v ∧
      exited = decide (v.exit_epoch < FAR_FUTURE_EPOCH) ∧
      withdrawn = decide (v.withdrawable_epoch < nextEpoch)

/-- The three breaks that come before the validator reads, in the spec's order: the Eth1-bridge
break (before Fulu: a deposit request while `eth1_deposit_index < deposit_requests_start_index`),
the finality break (`deposit.slot > finalized_slot`), the per-epoch count break
(`next_deposit_index >= MAX_PENDING_DEPOSITS_PER_EPOCH`). -/
def PendingDepositEarlyBreak (f : CFork) (P : Preset) (finalizedSlot requestsStart : U64)
    (deposit : PendingDeposit) (nextDepositIndex : Nat) (state : BeaconState P f) : Prop :=
  (!(f.atLeast .fulu) && decide (deposit.slot > GENESIS_SLOT) &&
      decide (state.eth1_deposit_index < requestsStart)) = true ∨
    deposit.slot > finalizedSlot ∨ nextDepositIndex ≥ P.MAX_PENDING_DEPOSITS_PER_EPOCH

/-- **The outcomes of one iteration of `process_pending_deposits`**, with the loop state
`(processed, index, postponed, reached, state)`: exactly one of

1. an early break (bridge, finality, count): the loop stops, its state unchanged;
2. the validator is withdrawn: the deposit is applied (`apply_pending_deposit`) without consuming
   churn;
3. the validator is exiting and not withdrawn: the deposit is postponed;
4. otherwise, if `processed + amount > available`, the churn break: the loop stops with
   `is_churn_limit_reached` set;
5. otherwise the deposit is applied, consuming its amount of churn. -/
theorem pendingDepositStep_spec {ctx : Ctx} {nextEpoch avail : U64} {finalizedSlot : Slot}
    {requestsStart : U64} {d : PendingDeposit} {pa : U64} {idx : Nat} {post : Array PendingDeposit}
    {flag : Bool} {st : BeaconState P f} {r : ForInStep (PendingDepositsAcc P f)}
    (h : pendingDepositStep ctx nextEpoch avail finalizedSlot requestsStart d
      (pa, idx, post, flag, st) = .ok r) :
    (PendingDepositEarlyBreak f P finalizedSlot requestsStart d idx st ∧
      r = .done (pa, idx, post, flag, st)) ∨
    (¬ PendingDepositEarlyBreak f P finalizedSlot requestsStart d idx st ∧
      ((∃ ex s', PendingDepositFlags st d nextEpoch ex true ∧
          applyPendingDeposit ctx st d = .ok s' ∧ r = .yield (pa, idx + 1, post, flag, s')) ∨
       (PendingDepositFlags st d nextEpoch true false ∧
          r = .yield (pa, idx + 1, post.push d, flag, st)) ∨
       (∃ x, PendingDepositFlags st d nextEpoch false false ∧
          pa.add? d.amount "process_pending_deposits" = .ok x ∧ x > avail ∧
          r = .done (pa, idx, post, true, st)) ∨
       (∃ x s', PendingDepositFlags st d nextEpoch false false ∧
          pa.add? d.amount "process_pending_deposits" = .ok x ∧ ¬ x > avail ∧
          applyPendingDeposit ctx st d = .ok s' ∧ r = .yield (x, idx + 1, post, false, s')))) := by
  unfold pendingDepositStep at h
  dsimp only at h
  by_cases h1 : (!f.atLeast CFork.fulu && decide (d.slot > GENESIS_SLOT) &&
      decide (st.eth1_deposit_index < requestsStart)) = true
  · rw [ite_eq_left h1] at h
    exact .inl ⟨.inl h1, (Except.ok.inj h).symm⟩
  rw [ite_eq_right h1] at h
  by_cases h2 : d.slot > finalizedSlot
  · rw [ite_eq_left h2] at h
    exact .inl ⟨.inr (.inl h2), (Except.ok.inj h).symm⟩
  rw [ite_eq_right h2] at h
  by_cases h3 : idx ≥ P.MAX_PENDING_DEPOSITS_PER_EPOCH
  · rw [ite_eq_left h3] at h
    exact .inl ⟨.inr (.inr h3), (Except.ok.inj h).symm⟩
  rw [ite_eq_right h3] at h
  have hnb : ¬ PendingDepositEarlyBreak f P finalizedSlot requestsStart d idx st := by
    rintro (h | h | h) <;> contradiction
  refine .inr ⟨hnb, ?_⟩
  cases hf : findValidatorIndex st d.pubkey with
  | none =>
    rw [hf] at h
    obtain ⟨flags, hflags, h⟩ := bind_ok_elim h
    cases hflags
    have hF : PendingDepositFlags st d nextEpoch false false := by
      unfold PendingDepositFlags; rw [hf]; exact ⟨rfl, rfl⟩
    have hF' : PendingDepositFlags st d nextEpoch (false, false).1 (false, false).2 := hF
    clear hF
    have hF := hF'
    clear hF'
    generalize (false, false) = flags at h hF
    rcases flags with ⟨ex, wd⟩
    dsimp only at h hF
    cases wd with
    | true =>
      rw [ite_eq_left rfl] at h
      obtain ⟨s', hs', h⟩ := bind_ok_elim h
      exact .inl ⟨ex, s', hF, hs', (Except.ok.inj h).symm⟩
    | false =>
      rw [ite_eq_right (by decide)] at h
      cases ex with
      | true =>
        rw [ite_eq_left rfl] at h
        exact .inr (.inl ⟨hF, (Except.ok.inj h).symm⟩)
      | false =>
        rw [ite_eq_right (by decide)] at h
        obtain ⟨x, hx, h⟩ := bind_ok_elim h
        by_cases hc : decide (x > avail) = true
        · rw [ite_eq_left hc] at h
          exact .inr (.inr (.inl ⟨x, hF, hx, of_decide_eq_true hc, (Except.ok.inj h).symm⟩))
        · rw [ite_eq_right hc] at h
          obtain ⟨s', hs', h⟩ := bind_ok_elim h
          exact .inr (.inr (.inr ⟨x, s', hF, hx, fun hh => hc (decide_eq_true hh), hs',
            (Except.ok.inj h).symm⟩))
  | some i =>
    rw [hf] at h
    dsimp only at h
    obtain ⟨v, hv, h⟩ := bind_ok_elim h
    obtain ⟨flags, hflags, h⟩ := bind_ok_elim h
    cases hflags
    have hF : PendingDepositFlags st d nextEpoch
        (decide (v.exit_epoch < FAR_FUTURE_EPOCH), decide (v.withdrawable_epoch < nextEpoch)).1
        (decide (v.exit_epoch < FAR_FUTURE_EPOCH), decide (v.withdrawable_epoch < nextEpoch)).2 := by
      unfold PendingDepositFlags; rw [hf]; exact ⟨v, get_ok hv, rfl, rfl⟩
    generalize (decide (v.exit_epoch < FAR_FUTURE_EPOCH),
      decide (v.withdrawable_epoch < nextEpoch)) = flags at h hF
    rcases flags with ⟨ex, wd⟩
    dsimp only at h hF
    cases wd with
    | true =>
      rw [ite_eq_left rfl] at h
      obtain ⟨s', hs', h⟩ := bind_ok_elim h
      exact .inl ⟨ex, s', hF, hs', (Except.ok.inj h).symm⟩
    | false =>
      rw [ite_eq_right (by decide)] at h
      cases ex with
      | true =>
        rw [ite_eq_left rfl] at h
        exact .inr (.inl ⟨hF, (Except.ok.inj h).symm⟩)
      | false =>
        rw [ite_eq_right (by decide)] at h
        obtain ⟨x, hx, h⟩ := bind_ok_elim h
        by_cases hc : decide (x > avail) = true
        · rw [ite_eq_left hc] at h
          exact .inr (.inr (.inl ⟨x, hF, hx, of_decide_eq_true hc, (Except.ok.inj h).symm⟩))
        · rw [ite_eq_right hc] at h
          obtain ⟨s', hs', h⟩ := bind_ok_elim h
          exact .inr (.inr (.inr ⟨x, s', hF, hx, fun hh => hc (decide_eq_true hh), hs',
            (Except.ok.inj h).symm⟩))

/-! ## The fate of every deposit the loop reaches -/

/-- `IsMerge as bs cs`: `cs` is an order-preserving merge of `as` and `bs`, so every element of
`cs` is in exactly one of them. -/
inductive IsMerge {α : Type} : List α → List α → List α → Prop where
  | nil : IsMerge [] [] []
  | left {as bs cs : List α} (a : α) : IsMerge as bs cs → IsMerge (a :: as) bs (a :: cs)
  | right {as bs cs : List α} (b : α) : IsMerge as bs cs → IsMerge as (b :: bs) (b :: cs)

/-- **The loop, deposit by deposit**: on success, the loop reached the first `k` deposits of the
queue and split them, in order, into those it applied and those it postponed; the state is the
input state with `apply_pending_deposit` applied to the applied ones in order; the postponed ones
are appended to the postponement buffer; the index advanced by `k`; and if `k` is short of the
queue, the iteration at deposit `k` stopped the loop. -/
theorem pendingDepositsLoop_fate {ctx : Ctx} {nextEpoch avail : U64} {finalizedSlot : Slot}
    {requestsStart : U64} :
    ∀ (L : List PendingDeposit) (acc out : PendingDepositsAcc P f),
      pendingDepositsLoop ctx nextEpoch avail finalizedSlot requestsStart L acc = .ok out →
      ∃ k applied postponed, k ≤ L.length ∧ IsMerge applied postponed (L.take k) ∧
        List.foldlM (applyPendingDeposit ctx) acc.2.2.2.2 applied = .ok out.2.2.2.2 ∧
        out.2.2.1 = acc.2.2.1 ++ postponed.toArray ∧ out.2.1 = acc.2.1 + k ∧
        (∀ hk : k < L.length, ∃ accK,
          pendingDepositStep ctx nextEpoch avail finalizedSlot requestsStart (L[k]'hk) accK =
            .ok (.done out)) := by
  intro L
  induction L with
  | nil =>
    intro acc out h
    cases h
    exact ⟨0, [], [], le_refl _, .nil, rfl, by simp, rfl, fun hk => absurd hk (by simp)⟩
  | cons d ds ih =>
    intro acc out h
    rw [pendingDepositsLoop] at h
    obtain ⟨r, hr, h⟩ := bind_ok_elim h
    rcases acc with ⟨pa, idx, post, flag, st⟩
    have hspec := pendingDepositStep_spec hr
    cases r with
    | done a =>
      have hao : out = a := (Except.ok.inj h).symm
      subst hao
      have hst : out.2.2.2.2 = st ∧ out.2.2.1 = post ∧ out.2.1 = idx := by
        rcases hspec with ⟨-, hra⟩ | ⟨-, ⟨_, _, _, _, hra⟩ | ⟨_, hra⟩ | ⟨_, _, _, _, hra⟩ |
            ⟨_, _, _, _, _, _, hra⟩⟩ <;> cases hra <;> exact ⟨rfl, rfl, rfl⟩
      refine ⟨0, [], [], Nat.zero_le _, .nil, ?_, ?_, ?_, fun _ => ⟨_, hr⟩⟩
      · rw [hst.1]; rfl
      · rw [hst.2.1]; simp
      · rw [hst.2.2]; rfl
    | yield a =>
      obtain ⟨k, ap, pp, hk, hm, hfold, hpost, hidx, hstop⟩ := ih a out h
      refine ⟨k + 1, ?_⟩
      rcases hspec with ⟨-, hra⟩ | ⟨-, ⟨_, s', _, hs', hra⟩ | ⟨_, hra⟩ | ⟨_, _, _, _, hra⟩ |
          ⟨x, s', _, _, _, hs', hra⟩⟩
      · cases hra
      · cases hra
        refine ⟨d :: ap, pp, by simp; omega, .left d hm, ?_, hpost, by simp only at hidx ⊢; omega, ?_⟩
        · rw [List.foldlM_cons, hs']; exact hfold
        · intro hk'; exact hstop (by simp at hk'; omega)
      · cases hra
        refine ⟨ap, d :: pp, by simp; omega, .right d hm, hfold, ?_, by simp only at hidx ⊢; omega, ?_⟩
        · rw [hpost]; simp
        · intro hk'; exact hstop (by simp at hk'; omega)
      · cases hra
      · cases hra
        refine ⟨d :: ap, pp, by simp; omega, .left d hm, ?_, hpost, by simp only at hidx ⊢; omega, ?_⟩
        · rw [List.foldlM_cons, hs']; exact hfold
        · intro hk'; exact hstop (by simp at hk'; omega)

/-- `set_deposit_balance_to_consume` changes only that field. -/
theorem setDepositBalanceToConsume_fields {s s' : BeaconState P f} {v : Gwei}
    (h : s.setDepositBalanceToConsume v = .ok s') :
    s'.validators = s.validators ∧ s'.balances = s.balances ∧
      s'.pending_deposits = s.pending_deposits := by
  unfold BeaconState.setDepositBalanceToConsume at h
  obtain ⟨g, -, h⟩ := bind_ok_elim h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- **D-S9 fate, the epoch pass** (Electra and Fulu): on success, `process_pending_deposits`
reached the first `k` deposits of the queue and split them, in order, into the deposits it
applied (each through `apply_pending_deposit`, in order, from the input state: so each meets
exactly one of `PendingDepositOutcome`'s three outcomes) and the deposits it postponed; the new
queue is the unreached suffix followed by the postponed deposits; and the registry and balances
are those the applications produced. -/
theorem processPendingDeposits_fate (hE : f.atLeast .electra = true) {ctx : Ctx}
    {state s' : BeaconState P f} (hp : processPendingDeposits ctx state = .ok s') :
    ∃ k applied postponed mid,
      k ≤ (Gated.get hE state.pending_deposits).toArray.size ∧
      IsMerge applied postponed ((Gated.get hE state.pending_deposits).toArray.toList.take k) ∧
      List.foldlM (applyPendingDeposit ctx) state applied = .ok mid ∧
      (Gated.get hE s'.pending_deposits).toArray =
        (Gated.get hE state.pending_deposits).toArray.extract k
          (Gated.get hE state.pending_deposits).toArray.size ++ postponed.toArray ∧
      s'.validators = mid.validators ∧ s'.balances = mid.balances := by
  rw [processPendingDeposits_eq] at hp
  dsimp only at hp
  obtain ⟨e0, -, hp⟩ := bind_ok_elim hp
  obtain ⟨ne, -, hp⟩ := bind_ok_elim hp
  obtain ⟨db, -, hp⟩ := bind_ok_elim hp
  obtain ⟨cl, -, hp⟩ := bind_ok_elim hp
  obtain ⟨avail, -, hp⟩ := bind_ok_elim hp
  obtain ⟨fs, -, hp⟩ := bind_ok_elim hp
  obtain ⟨rs, -, hp⟩ := bind_ok_elim hp
  obtain ⟨pending, hpend, hp⟩ := bind_ok_elim hp
  have hpq : pending = Gated.get hE state.pending_deposits := by
    unfold BeaconState.pendingDeposits at hpend
    rw [gated_read_get hE] at hpend
    exact (Except.ok.inj hpend).symm
  subst hpq
  obtain ⟨out, hloop, hp⟩ := bind_ok_elim hp
  obtain ⟨k, ap, pp, hk, hm, hfold, hpost, hidx, -⟩ := pendingDepositsLoop_fate _ _ _ hloop
  obtain ⟨q, hq, hp⟩ := bind_ok_elim hp
  obtain ⟨st1, hst1, hp⟩ := bind_ok_elim hp
  have hfr : s'.validators = st1.validators ∧ s'.balances = st1.balances ∧
      s'.pending_deposits = st1.pending_deposits := by
    split at hp
    · obtain ⟨_, -, hp⟩ := bind_ok_elim hp
      exact setDepositBalanceToConsume_fields hp
    · exact setDepositBalanceToConsume_fields hp
  unfold BeaconState.setPendingDeposits at hst1
  obtain ⟨g, hg, hst1⟩ := bind_ok_elim hst1
  cases hst1
  refine ⟨k, ap, pp, out.2.2.2.2, by simpa using hk, hm, hfold, ?_, hfr.1, hfr.2.1⟩
  rw [hfr.2.2]
  have hgq : g = Gated.mk hE q := by
    rw [gated_write_eq hE] at hg; exact (Except.ok.inj hg).symm
  rw [hgq, Gated.get_mk]
  unfold SszList.ofArray at hq
  split at hq
  · cases hq
    show (Gated.get hE state.pending_deposits).toArray.extract out.2.1
      (Gated.get hE state.pending_deposits).length ++ out.2.2.1 = _
    simp only at hidx hpost
    rw [hpost, hidx, Nat.zero_add, Array.empty_append]
    rfl
  · cases hq

end JauneConsensus.Facts
