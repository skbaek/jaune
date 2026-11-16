import JauneConsensus.Block
import JauneConsensus.Facts.WithdrawalRequest
import JauneConsensus.Facts.Operations

/-!
# Order sensitivity of the withdrawal requests (W2e)

P2's negative controls, derived rather than assumed. W2c's `order_control` proves
that folding `[partial V, fullExit V]` differs from `[fullExit V, partial V]` under
three assumed intermediate-state premises (`h1pos`, `h2exit`, `hne`); here those
premises are derived from W2a's classification lemmas:

* (a) `partial_applied_pending_pos`: applying a classified partial withdrawal
  leaves a positive pending balance for the validator (the pushed tail entry
  increases the pending-balance sum by a nonzero amount);
* (b) `fullExit_applied_exit_ne`: applying a classified full exit leaves the
  validator's `exit_epoch` set (not `FAR_FUTURE_EPOCH`);
* (c) `order_sensitive`: the composed two-fold order-sensitivity theorem, with
  hypotheses about the pre-state only (both classifications, both applications
  from the pre-state, Electra or later, and a nonzero
  `MIN_VALIDATOR_WITHDRAWABILITY_DELAY`); it also derives that both requests
  carry the same pubkey. The second steps, the nonzero amount and the
  intermediate reads are derived, not assumed.

P2 control (ii): for each `WithdrawalIgnoreReason` constructor, a
sufficient-condition lemma naming the abstract state conditions under which
`classifyWithdrawalRequest` returns exactly that reason.
-/

namespace JauneConsensus.Facts

variable {P : Preset} {f : CFork}

/-- `bind` on an `ok` result, as a rewrite (cf `WithdrawalRequest.bind_ok_cons`,
which is private to that file). -/
private theorem bind_ok_cons {α β ε : Type} (a : α) (k : α → Except ε β) :
    Bind.bind (Except.ok a) k = k a := rfl

/-- Injection on `ok` results. Stated with `Except.ok` (not `pure`) so the
header elaborates; `Except.ok.inj` still fires on `pure`-headed hypotheses
by definitional unfolding. -/
private theorem ok_inj_of_pure {ε α : Type} {a b : α}
    (h : (Except.ok a : Except ε α) = Except.ok b) : a = b :=
  Except.ok.inj h

/-- `bind` on an `error` result, as a rewrite (cf `WithdrawalRequest.bind_err_cons`). -/
private theorem bind_err_cons {α β ε : Type} (e : ε) (k : α → Except ε β) :
    Bind.bind (Except.error e) k = Except.error e := rfl

/-- Inversion for one `bind` layer (cf `WithdrawalRequest.bind_ok_inv`). -/
private theorem bind_ok_inv {α β ε : Type} {m : Except ε α} {f : α → Except ε β}
    {y : β} (h : Bind.bind m f = .ok y) : ∃ a, m = .ok a ∧ f a = .ok y := by
  cases m with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => rw [bind_err_cons] at h; cases h

/-- A successful `getAt` read pins the `Option` read. -/
theorem getAt_some {α : Type} {arr : Array α} {i : Nat} {site : String} {x : α}
    (h : getAt arr i site = .ok x) : arr[i]? = some x := by
  unfold getAt at h
  cases harr : arr[i]? with
  | none => simp [harr] at h
  | some y =>
    simp only [harr] at h
    exact congrArg some (ok_inj_of_pure h)

/-- Reading back a `SszList.set` at the same index returns the stored value. -/
theorem SszList.get_set_eq {α : Type} {n : Nat} {xs : SszList α n} {i : Nat}
    {a : α} {site1 site2 : String} {w : SszList α n}
    (h : xs.set i a site1 = .ok w) : w.get i site2 = .ok a := by
  unfold SszList.set at h
  by_cases hle : i < xs.toArray.size
  · rw [dite_eq_left hle] at h
    have hww := ok_inj_of_pure h
    simp only [hww.symm]
    unfold SszList.get getAt
    dsimp only
    rw [Array.getElem?_set_self]
    rfl
  · rw [dite_eq_right hle] at h
    simp at h

/-- `FAR_FUTURE_EPOCH != FAR_FUTURE_EPOCH` is false. -/
private theorem far_bne_self_false :
    ((FAR_FUTURE_EPOCH != FAR_FUTURE_EPOCH) = false) := by
  decide

/-- A successful `getAt` read replays under another site string. -/
theorem getAt_resite {α : Type} {arr : Array α} {i : Nat} {s1 s2 : String}
    {x : α} (h : getAt arr i s1 = .ok x) : getAt arr i s2 = .ok x := by
  have e := getAt_some h
  unfold getAt
  rw [e]
  rfl

/-- Inequality of `BEq` values as a false `==` test. -/
private theorem beq_false_of_ne {α : Type} [BEq α] [LawfulBEq α] {a b : α}
    (h : a ≠ b) : ((a == b) = false) :=
  beq_eq_false_iff_ne.mpr h

/-- Inequality of `BEq` values as a true `!=` test. -/
private theorem bne_eq_true_of_ne {α : Type} [BEq α] [LawfulBEq α] {a b : α}
    (h : a ≠ b) : ((a != b) = true) :=
  bne_iff_ne.mpr h

/-- `FAR_FUTURE_EPOCH` as a natural number. -/
private theorem far_toNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 :=
  U64.toNat_max

/-- A successful withdrawable-epoch addition keeps the exit-queue epoch below
`FAR_FUTURE_EPOCH` when the delay is nonzero. -/
theorem exitEpoch_ne_far_of_add_ok {eqE delay wd : Epoch}
    (hwd : U64.add? eqE delay "initiate_validator_exit" = .ok wd)
    (hdn : delay ≠ U64.zero) : eqE ≠ FAR_FUTURE_EPOCH := by
  intro hcon
  have hwdnat := U64.toNat_add? hwd
  have hlt := U64.toNat_lt wd
  have hdnat : delay.toNat ≠ 0 :=
    fun z => hdn (U64.eq_zero_of_toNat_eq_zero z)
  rw [hcon, far_toNat] at hwdnat
  omega

/-! ## The churn mid-state and the pushed pending entry -/

/-- The mid-state of `computeExitEpochAndUpdateChurn` differs from the input only
in the two churn fields. -/
theorem computeExitEpoch_mid {cfg : Config} {s : BeaconState P f} {b : Gwei}
    {mid : BeaconState P f} {eqE : Epoch}
    (h : computeExitEpochAndUpdateChurn cfg s b = .ok (mid, eqE)) :
    ∃ r ee, mid = { s with exit_balance_to_consume := r, earliest_exit_epoch := ee } := by
  unfold computeExitEpochAndUpdateChurn at h
  obtain ⟨e0, hE0, h1⟩ := bind_ok_inv h
  obtain ⟨cur, hcur, h2⟩ := bind_ok_inv h1
  obtain ⟨actExit, hact, h3⟩ := bind_ok_inv h2
  obtain ⟨churn, hchurn, h4⟩ := bind_ok_inv h3
  dsimp only at h4
  by_cases hout : e0 < (if e0 < actExit then actExit else e0)
  · rw [ite_eq_left hout] at h4
    obtain ⟨tcA, htcA, h5A⟩ := bind_ok_inv h4
    have htcAv : tcA = churn := (ok_inj_of_pure htcA).symm
    subst htcAv
    by_cases hinA : tcA < b
    · rw [ite_eq_left hinA] at h5A
      obtain ⟨btpA, hbtpA, h6A⟩ := bind_ok_inv h5A
      obtain ⟨soA, hsoA, h7A⟩ := bind_ok_inv h6A
      obtain ⟨dqA, hdqA, h8A⟩ := bind_ok_inv h7A
      obtain ⟨addA, haddA, h9A⟩ := bind_ok_inv h8A
      obtain ⟨exA, hexA, h10A⟩ := bind_ok_inv h9A
      obtain ⟨mqA, hmqA, h11A⟩ := bind_ok_inv h10A
      obtain ⟨tcA2, htcA2, h12A⟩ := bind_ok_inv h11A
      obtain ⟨remA, hremA, h13A⟩ := bind_ok_inv h12A
      obtain ⟨w1A, hw1A, h14A⟩ := bind_ok_inv h13A
      obtain ⟨w2A, hw2A, h15A⟩ := bind_ok_inv h14A
      obtain ⟨hmidA, -⟩ := Prod.mk.inj (ok_inj_of_pure h15A)
      exact ⟨w1A, w2A, hmidA.symm⟩
    · rw [ite_eq_right hinA] at h5A
      obtain ⟨remA, hremA, h13A⟩ := bind_ok_inv h5A
      obtain ⟨w1A, hw1A, h14A⟩ := bind_ok_inv h13A
      obtain ⟨w2A, hw2A, h15A⟩ := bind_ok_inv h14A
      obtain ⟨hmidA, -⟩ := Prod.mk.inj (ok_inj_of_pure h15A)
      exact ⟨w1A, w2A, hmidA.symm⟩
  · rw [ite_eq_right hout] at h4
    obtain ⟨tcB, htcB, h5B⟩ := bind_ok_inv h4
    by_cases hinB : tcB < b
    · rw [ite_eq_left hinB] at h5B
      obtain ⟨btpB, hbtpB, h6B⟩ := bind_ok_inv h5B
      obtain ⟨soB, hsoB, h7B⟩ := bind_ok_inv h6B
      obtain ⟨dqB, hdqB, h8B⟩ := bind_ok_inv h7B
      obtain ⟨addB, haddB, h9B⟩ := bind_ok_inv h8B
      obtain ⟨exB, hexB, h10B⟩ := bind_ok_inv h9B
      obtain ⟨mqB, hmqB, h11B⟩ := bind_ok_inv h10B
      obtain ⟨tcB2, htcB2, h12B⟩ := bind_ok_inv h11B
      obtain ⟨remB, hremB, h13B⟩ := bind_ok_inv h12B
      obtain ⟨w1B, hw1B, h14B⟩ := bind_ok_inv h13B
      obtain ⟨w2B, hw2B, h15B⟩ := bind_ok_inv h14B
      obtain ⟨hmidB, -⟩ := Prod.mk.inj (ok_inj_of_pure h15B)
      exact ⟨w1B, w2B, hmidB.symm⟩
    · rw [ite_eq_right hinB] at h5B
      obtain ⟨remB, hremB, h12B⟩ := bind_ok_inv h5B
      obtain ⟨w1B, hw1B, h13B⟩ := bind_ok_inv h12B
      obtain ⟨w2B, hw2B, h14B⟩ := bind_ok_inv h13B
      obtain ⟨hmidB, -⟩ := Prod.mk.inj (ok_inj_of_pure h14B)
      exact ⟨w1B, w2B, hmidB.symm⟩

/-- Inversion of a successful partial-withdrawal application: the pending list
grows by exactly the classified entry, and the other touched fields are named. -/
theorem applyPartial_push {cfg : Config} {s : BeaconState P f}
    {wp : WithdrawalRequest} {V : ValidatorIndex} {amt : Gwei}
    {s1 : BeaconState P f}
    (happ : applyWithdrawalOutcome cfg s wp (.partialWithdrawal V amt) = .ok s1) :
    ∃ (sList pushed : SszList PendingPartialWithdrawal
        P.PENDING_PARTIAL_WITHDRAWALS_LIMIT) (wd : Epoch),
      s.pendingPartialWithdrawals = .ok sList ∧
      pushed.toArray = sList.toArray.push
          { validator_index := V, amount := amt, withdrawable_epoch := wd } ∧
      s1.pendingPartialWithdrawals = .ok pushed ∧
      s1.validators = s.validators ∧
      s1.slot = s.slot ∧
      sList.toArray.size + 1 ≤ P.PENDING_PARTIAL_WITHDRAWALS_LIMIT := by
  unfold applyWithdrawalOutcome at happ
  obtain ⟨me, hcomp, hrest⟩ := bind_ok_inv happ
  obtain ⟨mid, eqE⟩ := me
  obtain ⟨delay, hcd, hrest1⟩ := bind_ok_inv hrest
  obtain ⟨wd, hwd, hrest2⟩ := bind_ok_inv hrest1
  obtain ⟨midList, hmidread, hset⟩ := bind_ok_inv hrest2
  obtain ⟨pushed, hpushok, hsetrest⟩ := bind_ok_inv hset
  obtain ⟨r, ee, hmid⟩ := computeExitEpoch_mid hcomp
  have hseq : mid.pending_partial_withdrawals =
      s.pending_partial_withdrawals := by rw [hmid]
  have hcongr : s.pendingPartialWithdrawals =
      mid.pendingPartialWithdrawals := by
    unfold BeaconState.pendingPartialWithdrawals
    rw [hseq]
  have hsread : s.pendingPartialWithdrawals = .ok midList :=
    hcongr.trans hmidread
  by_cases hle : midList.toArray.size + 1 ≤ P.PENDING_PARTIAL_WITHDRAWALS_LIMIT
  · unfold SszList.push at hpushok
    rw [dite_eq_left hle] at hpushok
    have hparr : pushed.toArray = midList.toArray.push
        { validator_index := V, amount := amt, withdrawable_epoch := wd } :=
      (congrArg SszList.toArray (ok_inj_of_pure hpushok)).symm
    unfold BeaconState.setPendingPartialWithdrawals at hsetrest
    cases f with
    | deneb =>
      obtain ⟨wval, hwrite, hs1eq⟩ := bind_ok_inv hsetrest
      have hwriteF : Gated.write false pushed "pending_partial_withdrawals" =
          .ok wval := hwrite
      unfold Gated.write at hwriteF
      dsimp only at hwriteF
      simp at hwriteF
    | electra | fulu | gloas =>
      obtain ⟨wval, hwrite, hs1eq⟩ := bind_ok_inv hsetrest
      have hwriteT : Gated.write true pushed "pending_partial_withdrawals" =
          .ok wval := hwrite
      unfold Gated.write at hwriteT
      dsimp only at hwriteT
      have hwval : wval = pushed := (ok_inj_of_pure hwriteT).symm
      rw [hwval] at hs1eq
      have hs1 : s1 = { mid with pending_partial_withdrawals := pushed } :=
        (ok_inj_of_pure hs1eq).symm
      have hframeV : s1.validators = s.validators := by rw [hs1, hmid]
      have hframeS : s1.slot = s.slot := by rw [hs1, hmid]
      have hs1read : s1.pendingPartialWithdrawals = .ok pushed := by
        rw [hs1]
        unfold BeaconState.pendingPartialWithdrawals Gated.read
        rfl
      refine ⟨midList, pushed, wd, hsread, ?_, hs1read, hframeV, hframeS, hle⟩
      rw [hparr]
  · unfold SszList.push at hpushok
    rw [dite_eq_right hle] at hpushok
    simp at hpushok

/-- (a) A successfully applied partial withdrawal leaves a positive pending
balance for the validator: the pushed tail entry increases the pending-balance
sum by the nonzero amount. -/
theorem partial_applied_pending_pos {cfg : Config} {s : BeaconState P f}
    {wp : WithdrawalRequest} {V : ValidatorIndex} {amt : Gwei}
    {s1 : BeaconState P f}
    (hclass : classifyWithdrawalRequest cfg s wp = .ok (.partialWithdrawal V amt))
    (hamt : amt ≠ U64.zero)
    (happ : applyWithdrawalOutcome cfg s wp (.partialWithdrawal V amt) = .ok s1) :
    getPendingBalanceToWithdraw s1 V ≠ .ok U64.zero := by
  obtain ⟨sList, pushed, wd, hsread, hparr, hs1read, -, -, -⟩ :=
    applyPartial_push happ
  have hps1 : getPendingBalanceToWithdraw s1 V =
      pushed.toArray.foldlM (fun acc w => if w.validator_index == V then
        U64.add? acc w.amount "get_pending_balance_to_withdraw"
        else pure acc) U64.zero := by
    have hs1r : Gated.read s1.pending_partial_withdrawals
        "pending_partial_withdrawals" = .ok pushed := hs1read
    unfold getPendingBalanceToWithdraw
    rw [hs1r]
    simp only [bind_ok_cons]
  rw [hps1, hparr, Array.foldlM_push]
  intro hcon
  cases hfoldS : sList.toArray.foldlM (fun acc w => if w.validator_index == V then
      U64.add? acc w.amount "get_pending_balance_to_withdraw"
      else pure acc) U64.zero with
  | error e =>
    rw [hfoldS, bind_err_cons] at hcon
    cases hcon
  | ok old =>
    rw [hfoldS] at hcon
    have hstep : (if ({ validator_index := V, amount := amt, withdrawable_epoch := wd } :
        PendingPartialWithdrawal).validator_index
        == V then U64.add? old amt "get_pending_balance_to_withdraw"
        else pure old) = .ok U64.zero := hcon
    simp only [U64.beq_eq_true_iff] at hstep
    rw [ite_eq_left (show True from trivial)] at hstep
    have hn := U64.toNat_add? hstep
    have hz : U64.zero.toNat = 0 := rfl
    rw [hz] at hn
    have ha : amt.toNat ≠ 0 :=
      fun z => hamt (U64.eq_zero_of_toNat_eq_zero z)
    omega

/-! ## The exit application: the stored exit epoch -/

/-- Inversion of a successful full-exit application on a not-yet-exiting
validator: the state sets exactly the computed exit epoch (Electra path). -/
theorem initiateExit_sets_epoch {cfg : Config} {s : BeaconState P f}
    {V : ValidatorIndex} {s1 : BeaconState P f}
    (he : f.atLeast .electra = true)
    (h : initiateValidatorExit cfg s V = .ok s1)
    (vc : Validator)
    (hgetc : s.validators.get V.toNat "process_withdrawal_request" = .ok vc)
    (hexit : vc.exit_epoch = FAR_FUTURE_EPOCH) :
    ∃ (eqE delay wd : Epoch) (vl : SszList Validator P.VALIDATOR_REGISTRY_LIMIT),
      c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY = .ok delay ∧
      U64.add? eqE delay "initiate_validator_exit" = .ok wd ∧
      s1.validators.get V.toNat "initiate_validator_exit" =
        .ok { vc with exit_epoch := eqE, withdrawable_epoch := wd } := by
  unfold initiateValidatorExit at h
  obtain ⟨v', hgetv, h1⟩ := bind_ok_inv h
  have hgetv' : getAt s.validators.toArray V.toNat "initiate_validator_exit" =
      .ok v' := hgetv
  have hgetc' : getAt s.validators.toArray V.toNat "process_withdrawal_request" =
      .ok vc := hgetc
  have hvv : v' = vc :=
    Option.some.inj ((getAt_some hgetv').symm.trans (getAt_some hgetc'))
  rw [hvv] at h1
  have hcond : ¬ (((vc.exit_epoch != FAR_FUTURE_EPOCH)) = true) := by
    simp [hexit, far_bne_self_false]
  rw [ite_eq_right hcond, ite_eq_left he] at h1
  obtain ⟨me, hcomp, h2⟩ := bind_ok_inv h1
  obtain ⟨mid, eqE⟩ := me
  obtain ⟨delay, hcd, h3⟩ := bind_ok_inv h2
  obtain ⟨wd, hwd, h4⟩ := bind_ok_inv h3
  obtain ⟨vl, hset, h5⟩ := bind_ok_inv h4
  have hs1 : s1 = { mid with validators := vl } := (Except.ok.inj h5).symm
  have hback := SszList.get_set_eq (site1 := "initiate_validator_exit")
    (site2 := "initiate_validator_exit") hset
  exact ⟨eqE, delay, wd, vl, hcd, hwd, by rw [hs1]; exact hback⟩

/-- (b) A successfully applied full exit leaves the validator's `exit_epoch`
set: it is the computed exit-queue epoch, which the successful withdrawable
addition keeps below `FAR_FUTURE_EPOCH`. -/
theorem fullExit_applied_exit_ne {cfg : Config} {s : BeaconState P f}
    {wf : WithdrawalRequest} {V : ValidatorIndex} {s1 : BeaconState P f}
    (he : f.atLeast .electra = true)
    (hdelay : ∃ d, c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY = .ok d ∧
      d ≠ U64.zero)
    (hclass : classifyWithdrawalRequest cfg s wf = .ok (.fullExit V))
    (happ : applyWithdrawalOutcome cfg s wf (.fullExit V) = .ok s1) :
    ∃ v, s1.validators.get V.toNat "process_withdrawal_request" = .ok v ∧
      v.exit_epoch ≠ FAR_FUTURE_EPOCH := by
  have hiff := classify_fullExit_iff.mp hclass
  obtain ⟨hamt, hB, hlook, hD, hpend⟩ := hiff
  obtain ⟨vc, hgetc, hX, hY, hE⟩ := hD
  obtain ⟨cur, hcur, hact, hexit, hF⟩ := hE
  have happI : initiateValidatorExit cfg s V = .ok s1 := happ
  obtain ⟨eqE, delay, wd, vl, hcd, hwd, hread⟩ :=
    initiateExit_sets_epoch he happI vc hgetc hexit
  obtain ⟨d, hd, hdn⟩ := hdelay
  have hdd : delay = d := Except.ok.inj (hcd.symm.trans hd)
  subst hdd
  have hne : eqE ≠ FAR_FUTURE_EPOCH := exitEpoch_ne_far_of_add_ok hwd hdn
  have hreadP : s1.validators.get V.toNat "process_withdrawal_request" =
      .ok { vc with exit_epoch := eqE, withdrawable_epoch := wd } :=
    getAt_resite hread
  refine ⟨_, hreadP, ?_⟩
  have hexit' : ({ vc with exit_epoch := eqE, withdrawable_epoch := wd } :
      Validator).exit_epoch = eqE := rfl
  rw [hexit']
  exact hne

/-! ## The exit frame -/

/-- `initiateValidatorExit` leaves the pending-partial-withdrawals field and the
slot unchanged (Electra path; the early return is the identity). -/
theorem initiateValidatorExit_frame {cfg : Config}
    {s : BeaconState P f} {V : ValidatorIndex} {s2 : BeaconState P f}
    (he : f.atLeast .electra = true)
    (h : initiateValidatorExit cfg s V = .ok s2) :
    s2.pending_partial_withdrawals = s.pending_partial_withdrawals ∧
      s2.slot = s.slot := by
  unfold initiateValidatorExit at h
  obtain ⟨v, hgetv, h1⟩ := bind_ok_inv h
  by_cases hret : ((v.exit_epoch != FAR_FUTURE_EPOCH) = true)
  · rw [ite_eq_left hret] at h1
    have hs2 : s2 = s := (ok_inj_of_pure h1).symm
    subst hs2
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hret, ite_eq_left he] at h1
    obtain ⟨me, hcomp, h2⟩ := bind_ok_inv h1
    obtain ⟨mid, eqE⟩ := me
    obtain ⟨delay, hcd, h3⟩ := bind_ok_inv h2
    obtain ⟨wd, hwd, h4⟩ := bind_ok_inv h3
    obtain ⟨vl, hset, h5⟩ := bind_ok_inv h4
    have hs2 : s2 = { mid with validators := vl } := (ok_inj_of_pure h5).symm
    obtain ⟨r, ee, hmid⟩ := computeExitEpoch_mid hcomp
    refine ⟨?_, ?_⟩ <;> rw [hs2, hmid]

/-! ## P2 control (ii): per-reason witnesses -/

/-- The partial-queue-full reason fires when the queue is at its limit on a
non-exit request. -/
theorem classify_ignored_partialQueueFull {cfg : Config} {s : BeaconState P f}
    {wr : WithdrawalRequest}
    {q : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    (hq : s.pendingPartialWithdrawals = .ok q)
    (hfull : (q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true) :
    classifyWithdrawalRequest cfg s wr = .ok (.ignored .partialQueueFull) := by
  unfold classifyWithdrawalRequest
  dsimp only
  rw [hq]
  simp only [bind_ok_cons]
  rw [ite_eq_left hfull]
  rfl

/-- The unknown-pubkey reason fires when no validator carries the request key
(and the queue gate passes). -/
theorem classify_ignored_unknownPubkey {cfg : Config} {s : BeaconState P f}
    {wr : WithdrawalRequest}
    {q : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    (hq : s.pendingPartialWithdrawals = .ok q)
    (hempty : (q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = false)
    (hlook : validatorIndexOf s wr.validator_pubkey = .ok none) :
    classifyWithdrawalRequest cfg s wr = .ok (.ignored .unknownPubkey) := by
  unfold classifyWithdrawalRequest
  dsimp only
  rw [hq]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT && !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)) from by simp [hempty])]
  rw [hlook]
  simp only [bind_ok_cons]
  rfl

/-- The bad-credential-or-source reason fires when the validator lacks an
execution credential or the source is not the credential address. -/
theorem classify_ignored_badCredentialOrSource {cfg : Config}
    {s : BeaconState P f} {wr : WithdrawalRequest} {V : ValidatorIndex}
    {v : Validator}
    {q : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    (hq : s.pendingPartialWithdrawals = .ok q)
    (hempty : (q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = false)
    (hlook : validatorIndexOf s wr.validator_pubkey = .ok (some V))
    (hget : s.validators.get V.toNat "process_withdrawal_request" = .ok v)
    (hbad : (hasExecutionWithdrawalCredential v &&
      v.withdrawal_credentials.toBytes.drop 12 ==
        wr.source_address.toBytes) = false) :
    classifyWithdrawalRequest cfg s wr =
      .ok (.ignored .badCredentialOrSource) := by
  unfold classifyWithdrawalRequest
  dsimp only
  rw [hq, hlook]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT && !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)) from by simp [hempty])]
  rw [hget]
  simp only [bind_ok_cons]
  rw [ite_eq_left (show ((!((hasExecutionWithdrawalCredential v) && (v.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes))) = true) from by simp [hbad])]
  rfl

/-- The not-active reason fires for an inactive validator with good
credentials. -/
theorem classify_ignored_notActive {cfg : Config} {s : BeaconState P f}
    {wr : WithdrawalRequest} {V : ValidatorIndex} {v : Validator}
    {q : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    {cur : Epoch}
    (hq : s.pendingPartialWithdrawals = .ok q)
    (hempty : (q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = false)
    (hlook : validatorIndexOf s wr.validator_pubkey = .ok (some V))
    (hget : s.validators.get V.toNat "process_withdrawal_request" = .ok v)
    (hgood : (hasExecutionWithdrawalCredential v &&
      v.withdrawal_credentials.toBytes.drop 12 ==
        wr.source_address.toBytes) = true)
    (hcur : getCurrentEpoch s = .ok cur)
    (hact : (isActiveValidator v cur) = false) :
    classifyWithdrawalRequest cfg s wr = .ok (.ignored .notActive) := by
  unfold classifyWithdrawalRequest
  dsimp only
  rw [hq, hlook]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT && !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)) from by simp [hempty])]
  rw [hget]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((!((hasExecutionWithdrawalCredential v) && (v.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes))) = true)) from by simp [hgood])]
  rw [hcur]
  simp only [bind_ok_cons]
  rw [ite_eq_left (show (((!(isActiveValidator v cur))) = true) from by simp [hact])]
  rfl

/-- The already-exiting reason fires for an active validator whose exit is set. -/
theorem classify_ignored_alreadyExiting {cfg : Config} {s : BeaconState P f}
    {wr : WithdrawalRequest} {V : ValidatorIndex} {v : Validator}
    {q : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    {cur : Epoch}
    (hq : s.pendingPartialWithdrawals = .ok q)
    (hempty : (q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = false)
    (hlook : validatorIndexOf s wr.validator_pubkey = .ok (some V))
    (hget : s.validators.get V.toNat "process_withdrawal_request" = .ok v)
    (hgood : (hasExecutionWithdrawalCredential v &&
      v.withdrawal_credentials.toBytes.drop 12 ==
        wr.source_address.toBytes) = true)
    (hcur : getCurrentEpoch s = .ok cur)
    (hact : (isActiveValidator v cur) = true)
    (hexit : (v.exit_epoch != FAR_FUTURE_EPOCH) = true) :
    classifyWithdrawalRequest cfg s wr = .ok (.ignored .alreadyExiting) := by
  unfold classifyWithdrawalRequest
  dsimp only
  rw [hq, hlook]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT && !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)) from by simp [hempty])]
  rw [hget]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((!((hasExecutionWithdrawalCredential v) && (v.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes))) = true)) from by simp [hgood])]
  rw [hcur]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬((((!(isActiveValidator v cur))) = true)) from by simp [hact])]
  rw [ite_eq_left hexit]
  rfl

/-- The too-early reason fires for a non-exiting validator inside its
`SHARD_COMMITTEE_PERIOD`. -/
theorem classify_ignored_tooEarly {cfg : Config} {s : BeaconState P f}
    {wr : WithdrawalRequest} {V : ValidatorIndex} {v : Validator}
    {q : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    {cur period actSum : Epoch}
    (hq : s.pendingPartialWithdrawals = .ok q)
    (hempty : (q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = false)
    (hlook : validatorIndexOf s wr.validator_pubkey = .ok (some V))
    (hget : s.validators.get V.toNat "process_withdrawal_request" = .ok v)
    (hgood : (hasExecutionWithdrawalCredential v &&
      v.withdrawal_credentials.toBytes.drop 12 ==
        wr.source_address.toBytes) = true)
    (hcur : getCurrentEpoch s = .ok cur)
    (hact : (isActiveValidator v cur) = true)
    (hnoexit : (v.exit_epoch != FAR_FUTURE_EPOCH) = false)
    (hper : c64 cfg.SHARD_COMMITTEE_PERIOD = .ok period)
    (hsum : U64.add? v.activation_epoch period
      "process_withdrawal_request" = .ok actSum)
    (hlt : cur < actSum) :
    classifyWithdrawalRequest cfg s wr = .ok (.ignored .tooEarly) := by
  unfold classifyWithdrawalRequest
  dsimp only
  rw [hq, hlook]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT && !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)) from by simp [hempty])]
  rw [hget]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((!((hasExecutionWithdrawalCredential v) && (v.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes))) = true)) from by simp [hgood])]
  rw [hcur]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬((((!(isActiveValidator v cur))) = true)) from by simp [hact])]
  rw [ite_eq_right (show ¬((((v.exit_epoch != FAR_FUTURE_EPOCH)) = true)) from by simp [hnoexit])]
  rw [hper]
  simp only [bind_ok_cons]
  rw [hsum]
  simp only [bind_ok_cons]
  rw [ite_eq_left hlt]
  rfl

/-- The full-exit-with-pending-balance reason fires for a full exit while a
pending balance remains. -/
theorem classify_ignored_fullExitPendingBalance {cfg : Config}
    {s : BeaconState P f} {wr : WithdrawalRequest} {V : ValidatorIndex}
    {v : Validator}
    {q : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    {cur period actSum : Epoch} {pb : Gwei}
    (hq : s.pendingPartialWithdrawals = .ok q)
    (hempty : (q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = false)
    (hlook : validatorIndexOf s wr.validator_pubkey = .ok (some V))
    (hget : s.validators.get V.toNat "process_withdrawal_request" = .ok v)
    (hgood : (hasExecutionWithdrawalCredential v &&
      v.withdrawal_credentials.toBytes.drop 12 ==
        wr.source_address.toBytes) = true)
    (hcur : getCurrentEpoch s = .ok cur)
    (hact : (isActiveValidator v cur) = true)
    (hnoexit : (v.exit_epoch != FAR_FUTURE_EPOCH) = false)
    (hper : c64 cfg.SHARD_COMMITTEE_PERIOD = .ok period)
    (hsum : U64.add? v.activation_epoch period
      "process_withdrawal_request" = .ok actSum)
    (hearly : ¬ cur < actSum)
    (hpend : getPendingBalanceToWithdraw s V = .ok pb)
    (hfull : (wr.amount == FULL_EXIT_REQUEST_AMOUNT) = true)
    (hpb : (pb == U64.zero) = false) :
    classifyWithdrawalRequest cfg s wr =
      .ok (.ignored .fullExitPendingBalance) := by
  unfold classifyWithdrawalRequest
  dsimp only
  rw [hq, hlook]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT && !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)) from by simp [hempty])]
  rw [hget]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((!((hasExecutionWithdrawalCredential v) && (v.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes))) = true)) from by simp [hgood])]
  rw [hcur]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬((((!(isActiveValidator v cur))) = true)) from by simp [hact])]
  rw [ite_eq_right (show ¬((((v.exit_epoch != FAR_FUTURE_EPOCH)) = true)) from by simp [hnoexit])]
  rw [hper]
  simp only [bind_ok_cons]
  rw [hsum]
  simp only [bind_ok_cons]
  rw [ite_eq_right hearly]
  rw [hpend]
  simp only [bind_ok_cons]
  rw [ite_eq_left hfull]
  rw [ite_eq_right (show ¬((((pb == U64.zero)) = true)) from by simp [hpb])]
  rfl

/-- The not-compounding reason fires for a partial withdrawal whose validator
lacks a compounding credential (after the earlier gates pass). -/
theorem classify_ignored_notCompounding {cfg : Config} {s : BeaconState P f}
    {wr : WithdrawalRequest} {V : ValidatorIndex} {v : Validator}
    {q : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    {cur period actSum : Epoch} {pb minAct balance sum : Gwei}
    (hq : s.pendingPartialWithdrawals = .ok q)
    (hempty : (q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = false)
    (hlook : validatorIndexOf s wr.validator_pubkey = .ok (some V))
    (hget : s.validators.get V.toNat "process_withdrawal_request" = .ok v)
    (hgood : (hasExecutionWithdrawalCredential v &&
      v.withdrawal_credentials.toBytes.drop 12 ==
        wr.source_address.toBytes) = true)
    (hcur : getCurrentEpoch s = .ok cur)
    (hact : (isActiveValidator v cur) = true)
    (hnoexit : (v.exit_epoch != FAR_FUTURE_EPOCH) = false)
    (hper : c64 cfg.SHARD_COMMITTEE_PERIOD = .ok period)
    (hsum : U64.add? v.activation_epoch period
      "process_withdrawal_request" = .ok actSum)
    (hearly : ¬ cur < actSum)
    (hpend : getPendingBalanceToWithdraw s V = .ok pb)
    (hnofull : (wr.amount == FULL_EXIT_REQUEST_AMOUNT) = false)
    (hmin : c64 P.MIN_ACTIVATION_BALANCE = .ok minAct)
    (hbal : s.balances.get V.toNat "process_withdrawal_request" = .ok balance)
    (hsum2 : U64.add? minAct pb "process_withdrawal_request" = .ok sum)
    (hcomp : (hasCompoundingWithdrawalCredential v) = false) :
    classifyWithdrawalRequest cfg s wr = .ok (.ignored .notCompounding) := by
  unfold classifyWithdrawalRequest
  dsimp only
  rw [hq, hlook]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT && !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)) from by simp [hempty])]
  rw [hget]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((!((hasExecutionWithdrawalCredential v) && (v.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes))) = true)) from by simp [hgood])]
  rw [hcur]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬((((!(isActiveValidator v cur))) = true)) from by simp [hact])]
  rw [ite_eq_right (show ¬((((v.exit_epoch != FAR_FUTURE_EPOCH)) = true)) from by simp [hnoexit])]
  rw [hper]
  simp only [bind_ok_cons]
  rw [hsum]
  simp only [bind_ok_cons]
  rw [ite_eq_right hearly]
  rw [hpend]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬((((wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)) from by simp [hnofull])]
  rw [hmin, hbal]
  simp only [bind_ok_cons]
  rw [hsum2]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((((hasCompoundingWithdrawalCredential v) && (decide (minAct ≤ v.effective_balance)) && (decide (sum < balance)))) = true)) from by simp [hcomp])]
  rw [ite_eq_left (show (((!(hasCompoundingWithdrawalCredential v))) = true) from by simp [hcomp])]
  rfl

/-- The insufficient-effective-balance reason fires for a compounding partial
withdrawal below `MIN_ACTIVATION_BALANCE`. -/
theorem classify_ignored_insufficientEffectiveBalance {cfg : Config}
    {s : BeaconState P f} {wr : WithdrawalRequest} {V : ValidatorIndex}
    {v : Validator}
    {q : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    {cur period actSum : Epoch} {pb minAct balance sum : Gwei}
    (hq : s.pendingPartialWithdrawals = .ok q)
    (hempty : (q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = false)
    (hlook : validatorIndexOf s wr.validator_pubkey = .ok (some V))
    (hget : s.validators.get V.toNat "process_withdrawal_request" = .ok v)
    (hgood : (hasExecutionWithdrawalCredential v &&
      v.withdrawal_credentials.toBytes.drop 12 ==
        wr.source_address.toBytes) = true)
    (hcur : getCurrentEpoch s = .ok cur)
    (hact : (isActiveValidator v cur) = true)
    (hnoexit : (v.exit_epoch != FAR_FUTURE_EPOCH) = false)
    (hper : c64 cfg.SHARD_COMMITTEE_PERIOD = .ok period)
    (hsum : U64.add? v.activation_epoch period
      "process_withdrawal_request" = .ok actSum)
    (hearly : ¬ cur < actSum)
    (hpend : getPendingBalanceToWithdraw s V = .ok pb)
    (hnofull : (wr.amount == FULL_EXIT_REQUEST_AMOUNT) = false)
    (hmin : c64 P.MIN_ACTIVATION_BALANCE = .ok minAct)
    (hbal : s.balances.get V.toNat "process_withdrawal_request" = .ok balance)
    (hsum2 : U64.add? minAct pb "process_withdrawal_request" = .ok sum)
    (hcomp : (hasCompoundingWithdrawalCredential v) = true)
    (hsuff : (decide (minAct ≤ v.effective_balance)) = false) :
    classifyWithdrawalRequest cfg s wr =
      .ok (.ignored .insufficientEffectiveBalance) := by
  unfold classifyWithdrawalRequest
  dsimp only
  rw [hq, hlook]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT && !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)) from by simp [hempty])]
  rw [hget]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((!((hasExecutionWithdrawalCredential v) && (v.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes))) = true)) from by simp [hgood])]
  rw [hcur]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬((((!(isActiveValidator v cur))) = true)) from by simp [hact])]
  rw [ite_eq_right (show ¬((((v.exit_epoch != FAR_FUTURE_EPOCH)) = true)) from by simp [hnoexit])]
  rw [hper]
  simp only [bind_ok_cons]
  rw [hsum]
  simp only [bind_ok_cons]
  rw [ite_eq_right hearly]
  rw [hpend]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬((((wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)) from by simp [hnofull])]
  rw [hmin, hbal]
  simp only [bind_ok_cons]
  rw [hsum2]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((((hasCompoundingWithdrawalCredential v) && (decide (minAct ≤ v.effective_balance)) && (decide (sum < balance)))) = true)) from by simp [hcomp, hsuff])]
  rw [ite_eq_right (show ¬((((!(hasCompoundingWithdrawalCredential v))) = true)) from by simp [hcomp])]
  rw [ite_eq_left (show (((!(decide (minAct ≤ v.effective_balance)))) = true) from by simp [hsuff])]
  rfl

/-- The no-excess reason fires for a compounding partial withdrawal with
sufficient effective balance but no excess balance. -/
theorem classify_ignored_noExcess {cfg : Config} {s : BeaconState P f}
    {wr : WithdrawalRequest} {V : ValidatorIndex} {v : Validator}
    {q : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    {cur period actSum : Epoch} {pb minAct balance sum : Gwei}
    (hq : s.pendingPartialWithdrawals = .ok q)
    (hempty : (q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = false)
    (hlook : validatorIndexOf s wr.validator_pubkey = .ok (some V))
    (hget : s.validators.get V.toNat "process_withdrawal_request" = .ok v)
    (hgood : (hasExecutionWithdrawalCredential v &&
      v.withdrawal_credentials.toBytes.drop 12 ==
        wr.source_address.toBytes) = true)
    (hcur : getCurrentEpoch s = .ok cur)
    (hact : (isActiveValidator v cur) = true)
    (hnoexit : (v.exit_epoch != FAR_FUTURE_EPOCH) = false)
    (hper : c64 cfg.SHARD_COMMITTEE_PERIOD = .ok period)
    (hsum : U64.add? v.activation_epoch period
      "process_withdrawal_request" = .ok actSum)
    (hearly : ¬ cur < actSum)
    (hpend : getPendingBalanceToWithdraw s V = .ok pb)
    (hnofull : (wr.amount == FULL_EXIT_REQUEST_AMOUNT) = false)
    (hmin : c64 P.MIN_ACTIVATION_BALANCE = .ok minAct)
    (hbal : s.balances.get V.toNat "process_withdrawal_request" = .ok balance)
    (hsum2 : U64.add? minAct pb "process_withdrawal_request" = .ok sum)
    (hcomp : (hasCompoundingWithdrawalCredential v) = true)
    (hsuff : (decide (minAct ≤ v.effective_balance)) = true)
    (hexc : (decide (sum < balance)) = false) :
    classifyWithdrawalRequest cfg s wr = .ok (.ignored .noExcess) := by
  unfold classifyWithdrawalRequest
  dsimp only
  rw [hq, hlook]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT && !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)) from by simp [hempty])]
  rw [hget]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((!((hasExecutionWithdrawalCredential v) && (v.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes))) = true)) from by simp [hgood])]
  rw [hcur]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬((((!(isActiveValidator v cur))) = true)) from by simp [hact])]
  rw [ite_eq_right (show ¬((((v.exit_epoch != FAR_FUTURE_EPOCH)) = true)) from by simp [hnoexit])]
  rw [hper]
  simp only [bind_ok_cons]
  rw [hsum]
  simp only [bind_ok_cons]
  rw [ite_eq_right hearly]
  rw [hpend]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬((((wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true)) from by simp [hnofull])]
  rw [hmin, hbal]
  simp only [bind_ok_cons]
  rw [hsum2]
  simp only [bind_ok_cons]
  rw [ite_eq_right (show ¬(((((hasCompoundingWithdrawalCredential v) && (decide (minAct ≤ v.effective_balance)) && (decide (sum < balance)))) = true)) from by simp [hcomp, hsuff, hexc])]
  rw [ite_eq_right (show ¬((((!(hasCompoundingWithdrawalCredential v))) = true)) from by simp [hcomp])]
  rw [ite_eq_right (show ¬((((!(decide (minAct ≤ v.effective_balance)))) = true)) from by simp [hsuff])]
  rfl

/-! ## (c) The composed order-sensitivity theorem -/

/-- A classified partial withdrawal withdraws a nonzero amount: the excess gate
`MIN_ACTIVATION_BALANCE + pending < balance` makes the available amount
positive, and a partial request's amount is not the (zero) full-exit amount. -/
theorem classify_partial_amt_ne_zero {cfg : Config} {state : BeaconState P f}
    {wr : WithdrawalRequest} {i : ValidatorIndex} {amt : Gwei}
    (h : classifyWithdrawalRequest cfg state wr = .ok (.partialWithdrawal i amt)) :
    amt ≠ U64.zero := by
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
                  intro hz
                  have hn := congrArg U64.toNat hz
                  rw [U64.toNat_min] at hn
                  have hz0 : U64.zero.toNat = 0 := rfl
                  rw [hz0] at hn
                  have hAvail : avail.toNat = sub1.toNat - pendingBalance.toNat :=
                    U64.toNat_sub? h11ok
                  have hSub1 : sub1.toNat = balance.toNat - minAct.toNat :=
                    U64.toNat_sub? h10ok
                  have hSum : sum.toNat = minAct.toNat + pendingBalance.toNat :=
                    U64.toNat_add? h9ok
                  have hlt : sum.toNat < balance.toNat :=
                    U64.lt_iff.mp (of_decide_eq_true (Bool.and_eq_true_iff.mp hg).2)
                  have hamt : wr.amount.toNat ≠ 0 := fun z =>
                    hb7 (U64.beq_eq_true_iff.mpr (U64.eq_zero_of_toNat_eq_zero z))
                  omega
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

/-- With no pending balance for `V` before, a successfully applied partial of
`amt` for `V` leaves exactly `amt` pending for `V` (no overflow). -/
theorem pending_after_partial_of_zero {cfg : Config} {s : BeaconState P f}
    {wp : WithdrawalRequest} {V : ValidatorIndex} {amt : Gwei}
    {s1 : BeaconState P f}
    (hpend : getPendingBalanceToWithdraw s V = .ok U64.zero)
    (happ : applyWithdrawalOutcome cfg s wp (.partialWithdrawal V amt) = .ok s1) :
    getPendingBalanceToWithdraw s1 V = .ok amt := by
  obtain ⟨sList, pushed, wd, hsread, hparr, hs1read, -, -, -⟩ :=
    applyPartial_push happ
  have hs0 : sList.toArray.foldlM (fun acc w => if w.validator_index == V then
      U64.add? acc w.amount "get_pending_balance_to_withdraw"
      else pure acc) U64.zero = .ok U64.zero := by
    have hsr : Gated.read s.pending_partial_withdrawals
        "pending_partial_withdrawals" = .ok sList := hsread
    have h0 := hpend
    unfold getPendingBalanceToWithdraw at h0
    rw [hsr] at h0
    simpa only [bind_ok_cons] using h0
  have hps1 : getPendingBalanceToWithdraw s1 V =
      pushed.toArray.foldlM (fun acc w => if w.validator_index == V then
        U64.add? acc w.amount "get_pending_balance_to_withdraw"
        else pure acc) U64.zero := by
    have hs1r : Gated.read s1.pending_partial_withdrawals
        "pending_partial_withdrawals" = .ok pushed := hs1read
    unfold getPendingBalanceToWithdraw
    rw [hs1r]
    simp only [bind_ok_cons]
  rw [hps1, hparr, Array.foldlM_push, hs0, bind_ok_cons]
  have hv : (({ validator_index := V, amount := amt, withdrawable_epoch := wd } :
      PendingPartialWithdrawal).validator_index == V) = true :=
    U64.beq_eq_true_iff.mpr rfl
  rw [ite_eq_left hv]
  obtain ⟨x, hx⟩ := (U64.add?_ok_iff (a := U64.zero) (b := amt)
    (site := "get_pending_balance_to_withdraw")).mpr (by
      have := U64.toNat_lt amt
      have hz0 : U64.zero.toNat = 0 := rfl
      omega)
  have hxa : x = amt := U64.ext_toNat (by
    rw [U64.toNat_add? hx]
    have hz0 : U64.zero.toNat = 0 := rfl
    omega)
  rw [hx, hxa]

/-- `validatorIndexOf` reads only the validator registry. -/
theorem validatorIndexOf_congr {s s' : BeaconState P f}
    (h : s'.validators = s.validators) (p : BLSPubkey) :
    validatorIndexOf s' p = validatorIndexOf s p := by
  unfold validatorIndexOf
  rw [h]

/-- A successful `validatorIndexOf` lookup names a registered validator that
carries the looked-up pubkey. -/
theorem validatorIndexOf_pubkey {s : BeaconState P f} {p : BLSPubkey}
    {V : ValidatorIndex} {site : String}
    (h : validatorIndexOf s p = .ok (some V)) :
    ∃ v, s.validators.get V.toNat site = .ok v ∧ v.pubkey = p := by
  unfold validatorIndexOf at h
  cases hf : s.validators.toArray.findIdx? (·.pubkey == p) with
  | none =>
    rw [hf] at h
    cases h
  | some i =>
    rw [hf] at h
    obtain ⟨x, hx, hxe⟩ := bind_ok_inv h
    have hxV : x = V := Option.some.inj (ok_inj_of_pure hxe)
    have hi : x.toNat = i := U64.toNat_ofNat? hx
    rw [Array.findIdx?_eq_some_iff_getElem] at hf
    obtain ⟨hlt, hpk, -⟩ := hf
    refine ⟨s.validators.toArray[i], ?_, ?_⟩
    · show getAt s.validators.toArray V.toNat site = _
      unfold getAt
      rw [← hxV, hi, Array.getElem?_eq_getElem hlt]
      rfl
    · have hb : (s.validators.toArray[i].pubkey.toArray == p.toArray) = true := hpk
      exact SszVector.ext (beq_iff_eq.mp hb)

/-- (c) P2 negative control (i), order sensitivity. Take a validator `V`, a
partial withdrawal `wp` and a full exit `wf`, both classified against the same
pre-state `s` as requests for `V`, with both applications succeeding from `s`
(Electra or later, nonzero withdrawability delay). Then both requests carry
the same pubkey, and folding `[wp, wf]` from `s` differs from folding
`[wf, wp]`: in the first order the full exit is ignored (the partial left a
pending balance), so the result is the partial's state, whose registry is
`s`'s; in the second order the exit has set `V`'s `exit_epoch`, and every
successful outcome of the partial keeps that registry. -/
theorem order_sensitive {cfg : Config} {s s1 s2 : BeaconState P f}
    {wp wf : WithdrawalRequest} {V : ValidatorIndex} {amt : Gwei}
    (he : f.atLeast .electra = true)
    (hdelay : ∃ d, c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY = .ok d ∧
      d ≠ U64.zero)
    (hcp : classifyWithdrawalRequest cfg s wp = .ok (.partialWithdrawal V amt))
    (hcf : classifyWithdrawalRequest cfg s wf = .ok (.fullExit V))
    (hap : applyWithdrawalOutcome cfg s wp (.partialWithdrawal V amt) = .ok s1)
    (haf : applyWithdrawalOutcome cfg s wf (.fullExit V) = .ok s2) :
    wp.validator_pubkey = wf.validator_pubkey ∧
      foldWithdrawalRequests cfg s [wp, wf] ≠ foldWithdrawalRequests cfg s [wf, wp] := by
  obtain ⟨hamtF, -, hlookF, ⟨vc, hgetc, hX, hY, ⟨cur, hcur, hact, hexit,
    ⟨period, hper, ⟨actSum, hsum, hearly⟩⟩⟩⟩, hpend0⟩ := classify_fullExit_iff.mp hcf
  obtain ⟨_, _, _, -, -, hs1read, hvalid1, hslot1, -⟩ := applyPartial_push hap
  -- the pubkey pin
  have hlookP : validatorIndexOf s wp.validator_pubkey = .ok (some V) :=
    (classify_fullExit_or_partial_spec hcp (Or.inr ⟨amt, rfl⟩)).1
  have hpk : wp.validator_pubkey = wf.validator_pubkey := by
    obtain ⟨vp, hgp, hvp⟩ := validatorIndexOf_pubkey
      (site := "process_withdrawal_request") hlookP
    obtain ⟨vf, hgf, hvf⟩ := validatorIndexOf_pubkey
      (site := "process_withdrawal_request") hlookF
    have hpf : vp = vf := Except.ok.inj (hgp.symm.trans hgf)
    rw [← hvp, ← hvf, hpf]
  refine ⟨hpk, ?_⟩
  -- first order: the full exit after the partial is ignored
  have hamt0 : amt ≠ U64.zero := classify_partial_amt_ne_zero hcp
  have hpb1 : getPendingBalanceToWithdraw s1 V = .ok amt :=
    pending_after_partial_of_zero hpend0 hap
  have hcur1 : getCurrentEpoch s1 = .ok cur := by
    unfold getCurrentEpoch
    rw [hslot1]
    exact hcur
  have hget1 : s1.validators.get V.toNat "process_withdrawal_request" = .ok vc := by
    rw [hvalid1]
    exact hgetc
  have hlook1 : validatorIndexOf s1 wf.validator_pubkey = .ok (some V) := by
    rw [validatorIndexOf_congr hvalid1]
    exact hlookF
  have hfullB : (wf.amount == FULL_EXIT_REQUEST_AMOUNT) = true :=
    U64.beq_eq_true_iff.mpr hamtF
  have hc1 : classifyWithdrawalRequest cfg s1 wf =
      .ok (.ignored .fullExitPendingBalance) :=
    classify_ignored_fullExitPendingBalance hs1read (by simp [hfullB]) hlook1 hget1
      (by simp [hX, hY]) hcur1 hact (by rw [hexit]; exact far_bne_self_false)
      hper hsum hearly hpb1 hfullB
      (Bool.eq_false_iff.mpr (fun h => hamt0 (U64.beq_eq_true_iff.mp h)))
  have hp1 : processWithdrawalRequest cfg s wp = .ok s1 := by
    rw [processWithdrawalRequest_eq, hcp]
    exact hap
  have hp2 : processWithdrawalRequest cfg s1 wf = .ok s1 := by
    rw [processWithdrawalRequest_eq, hc1]
    rfl
  have hA : foldWithdrawalRequests cfg s [wp, wf] = .ok s1 := by
    unfold foldWithdrawalRequests
    simp only [List.foldlM_cons, hp1, ok_bind', hp2]
    rfl
  -- second order: the exit changes the registry, which the partial keeps
  obtain ⟨v2, hget2, hexit2⟩ := fullExit_applied_exit_ne he hdelay hcf haf
  have hvne : s2.validators ≠ s.validators := by
    intro heq
    rw [heq, hgetc] at hget2
    have hv : vc = v2 := Except.ok.inj hget2
    exact hexit2 (hv ▸ hexit)
  have hq1 : processWithdrawalRequest cfg s wf = .ok s2 := by
    rw [processWithdrawalRequest_eq, hcf]
    exact haf
  have hB : ∀ r, processWithdrawalRequest cfg s2 wp = .ok r →
      r.validators = s2.validators := by
    intro r hr
    rw [processWithdrawalRequest_eq] at hr
    obtain ⟨o, ho, hra⟩ := bind_ok_inv hr
    cases o with
    | ignored _ =>
      have hrs : s2 = r := Except.ok.inj hra
      rw [hrs]
    | fullExit j =>
      exfalso
      obtain ⟨_, _, -, -, -, hnz⟩ := classify_partial_amount hcp
      exact hnz (classify_fullExit_iff.mp ho).1
    | partialWithdrawal j a =>
      obtain ⟨_, _, _, -, -, -, hv, -, -⟩ := applyPartial_push hra
      exact hv
  have hBf : foldWithdrawalRequests cfg s [wf, wp] =
      processWithdrawalRequest cfg s2 wp := by
    unfold foldWithdrawalRequests
    simp only [List.foldlM_cons, List.foldlM_nil, hq1, ok_bind', bind_pure]
  rw [hA, hBf]
  intro heq
  have hr := hB s1 heq.symm
  exact hvne (hr.symm.trans hvalid1)

end JauneConsensus.Facts
