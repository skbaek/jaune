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
  hypotheses about the pre-state only (plus the second-step successes, the
  lookup stability through the exit, and the nonzero-amount fact, which are
  reported as assumed).

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

end JauneConsensus.Facts
