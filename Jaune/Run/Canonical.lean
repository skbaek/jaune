import Jaune.Run.Block

/-!
# Canonicality through the staged chain (goal `jaune-shape-and-names-v1`, W2 unit W2-C)

Every successful run of the staged chain leaves a canonical state: the top-level message run
(`Message.run`, read through `MessageRun.state`), the transaction (`B2.Transaction.run`), the
system calls, one body operation (`Body.step`), a run of operations (`Body.run`, `Body.fold`), the
importer's body (`Body.importer`, `applyBody`), and the block transition
(`E.stateTransitionCoreE`). These restate, over the staged definitions, the canonical family that
`Jaune.Transaction` states over the old chain (`processMessageCall_canonical`,
`processTransaction_canonical`, the system-call canonicals, `applyTransactions_canonical`,
`withdrawalsPass_canonical`, `requestsPass_canonical`, `applyBody_canonical`,
`stateTransitionCoreE_canonical`), and are proved without the bridges.

Where the new types differ the statement follows them:

* the message level has no output pair: `Message.run_canonical` concludes `run.state.Canonical`
  for the `MessageRun` (the old `processMessageCall_canonical` concluded it of the pair's state);
* the system calls return a `MessageRun`, so their canonicals conclude `run.state.Canonical`;
* the body's passes (`applyTransactions`, `withdrawalsPass`, `requestsPass`, `payRewards`) are
  operations of one step, so their canonicals are the one `Body.step_canonical` and its folds,
  which ask of the block environment only its original state (`benv.stat.Canonical`): the step
  reads the prefix's state in place of the environment's.

The Amsterdam preparation canonicals are proved here, publicly, over the public preparation
helpers of `Jaune.Transaction.Parts`; `Jaune.Transaction` uses them.

Staged under `Jaune.Staging` (the transaction under `Jaune.Staging.B2`, the block transition under
`Jaune.Staging.E`), beside the definitions they speak of.
-/

namespace Jaune.Staging

open Jaune

/-! ### The Amsterdam preparation -/

theorem chargeNewAuthorityAmsterdam_canonical {state : StateGasRules}
    {authority : Address} {devm : Devm} (h : devm.Canonical) :
    (chargeNewAuthorityAmsterdam state authority devm).Canonical := by
  unfold chargeNewAuthorityAmsterdam
  split
  · exact liftMachExecution_canonical h
  · exact h

theorem chargePaidAccountWriteAmsterdam_canonical
    {state : StateGasRules} {authority : Address} {devm : Devm}
    {paidWrites : AdrSet} (h : devm.Canonical) :
    (chargePaidAccountWriteAmsterdam state authority devm paidWrites).CanonicalOn
      (fun r => r.1.Canonical) := by
  unfold chargePaidAccountWriteAmsterdam
  split
  · exact h
  · exact Except.CanonicalOn.bind (chargeGas_canonical h) (fun _ hd => hd)

theorem chargeAuthBaseAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} {authority target : Address} {devm : Devm}
    {delegationSetFor : AdrSet} (h : devm.Canonical) :
    (chargeAuthBaseAmsterdam state msg authority target devm
      delegationSetFor).CanonicalOn (fun r => r.1.Canonical) := by
  unfold chargeAuthBaseAmsterdam
  split
  · exact h
  · dsimp only
    split
    · exact Except.CanonicalOn.bind (liftMachExecution_canonical h)
        (fun _ hd => hd)
    · exact h

theorem applyValidatedDelegationAmsterdam_canonical
    {state : StateGasRules} {msg : Msg} {authority target : Address}
    {devm : Devm} {paidWrites delegationSetFor : AdrSet}
    (h : devm.Canonical) :
    (applyValidatedDelegationAmsterdam state msg authority target devm
      paidWrites delegationSetFor).CanonicalOn (fun r => r.1.Canonical) := by
  unfold applyValidatedDelegationAmsterdam
  refine Except.CanonicalOn.bind (chargeNewAuthorityAmsterdam_canonical h)
    fun devm hdevm => ?_
  refine Except.CanonicalOn.bind
    (chargePaidAccountWriteAmsterdam_canonical hdevm) fun r hr => ?_
  obtain ⟨devm, paidWrites⟩ := r
  refine Except.CanonicalOn.bind
    (chargeAuthBaseAmsterdam_canonical hr) fun r hr => ?_
  obtain ⟨devm, delegationSetFor, codeToSet⟩ := r
  exact Devm.Canonical.incrNonce (Devm.Canonical.setCode hr authority codeToSet)
    authority

theorem setDelegationAmsterdamStep_canonical
    {state : StateGasRules} {msg : Msg} {auth : Authorization} {devm : Devm}
    {paidWrites delegationSetFor : AdrSet} (h : devm.Canonical) :
    (setDelegationAmsterdamStep state msg auth devm paidWrites
      delegationSetFor).CanonicalOn (fun r => r.1.Canonical) := by
  unfold setDelegationAmsterdamStep
  split
  · exact h
  · split
    · exact h
    · cases hr : recoverAuthority auth with
      | error error =>
        cases error <;> simp only <;> exact h
      | ok authority =>
        dsimp only
        have ha := addAccessedAddress_canonical (a := authority) h
        split
        · exact ha
        · split
          · exact ha
          · exact applyValidatedDelegationAmsterdam_canonical ha

theorem setDelegationAmsterdamLoop_canonical
    {state : StateGasRules} {msg : Msg} {auths : List Authorization} {devm : Devm}
    {paidWrites delegationSetFor : AdrSet} (h : devm.Canonical) :
    (setDelegationAmsterdamLoop state msg auths devm paidWrites
      delegationSetFor).CanonicalOn (fun r => r.1.Canonical) := by
  induction auths generalizing devm paidWrites delegationSetFor with
  | nil => exact h
  | cons auth auths ih =>
    unfold setDelegationAmsterdamLoop
    exact Except.CanonicalOn.bind (setDelegationAmsterdamStep_canonical h)
      (fun r hr => ih hr)

theorem setDelegationAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} {devm : Devm} (h : devm.Canonical) :
    (setDelegationAmsterdam state msg devm).Canonical := by
  unfold setDelegationAmsterdam
  exact Except.CanonicalOn.bind (setDelegationAmsterdamLoop_canonical h)
    (fun _ hr => hr)

theorem preparedTopLevelMessage_canonical {msg : Msg} {devm : Devm}
    (hm : msg.Canonical) (hd : devm.Canonical) :
    (preparedTopLevelMessage msg devm).Canonical := by
  exact ⟨⟨hd.1, hm.1.2⟩, hd.2⟩

theorem resolveTopLevelCallAmsterdam_canonical {msg : Msg}
    {devm : Devm} (hm : msg.Canonical) (hd : devm.Canonical) :
    (resolveTopLevelCallAmsterdam msg devm).CanonicalOn
      (fun r => r.1.Canonical ∧ r.2.Canonical) := by
  unfold resolveTopLevelCallAmsterdam
  rcases msg.benv.stat.rules.delegationCost devm msg.currentTarget
    with ⟨delegated, codeAddress, accessCost⟩
  refine Except.CanonicalOn.bind (chargeGas_canonical hd)
    fun charged hcharged => ?_
  have hfinished := completeDelegationAccess_canonical hcharged delegated codeAddress
  exact ⟨preparedTopLevelMessage_canonical hm hfinished, hfinished⟩

theorem dispatchTopLevelAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} {devm : Devm} (hm : msg.Canonical) (hd : devm.Canonical) :
    (dispatchTopLevelAmsterdam state msg devm).CanonicalOn
      (fun r => r.1.Canonical ∧ r.2.Canonical) := by
  unfold dispatchTopLevelAmsterdam
  split
  · dsimp only
    split
    · exact hd
    · split
      · exact Except.CanonicalOn.bind (liftMachExecution_canonical hd)
          (fun charged hcharged =>
            ⟨preparedTopLevelMessage_canonical hm hcharged, hcharged⟩)
      · exact ⟨preparedTopLevelMessage_canonical hm hd, hd⟩
  · dsimp only
    split
    · exact Except.CanonicalOn.bind (liftMachExecution_canonical hd)
        (fun _ hcharged => resolveTopLevelCallAmsterdam_canonical hm hcharged)
    · exact resolveTopLevelCallAmsterdam_canonical hm hd

theorem finishTopLevelAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} {devm : Devm} (hm : msg.Canonical) (hd : devm.Canonical) :
    (finishTopLevelAmsterdam state msg devm).CanonicalOn
      (fun r => r.1.Canonical ∧ r.2.Canonical) := by
  unfold finishTopLevelAmsterdam
  split
  · exact dispatchTopLevelAmsterdam_canonical hm hd
  · exact dispatchTopLevelAmsterdam_canonical hm
      (Devm.Canonical.of_world_eq hd rfl)

theorem prepareTopLevelAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} (hm : msg.Canonical) :
    (prepareTopLevelAmsterdam state msg).CanonicalOn
      (fun r => r.1.Canonical ∧ r.2.Canonical) := by
  unfold prepareTopLevelAmsterdam
  have hi := initDevm_canonical hm
  dsimp only
  split
  · exact finishTopLevelAmsterdam_canonical hm hi
  · exact Except.CanonicalOn.bind (setDelegationAmsterdam_canonical hi)
      (fun _ hd => finishTopLevelAmsterdam_canonical hm hd)

/-! ### The top-level message run -/

/-- A frame a canonical top-level message is prepared into is canonical. -/
theorem TopLevel.prepare_canonical {msg : Msg} (h : msg.Canonical) {f : Frame} {a : Nat}
    (hp : TopLevel.prepare msg = .ok (.frame f a)) : f.Canonical := by
  have amsterdam : ∀ (state : StateGasRules) (isCreate : Bool),
      TopLevel.prepare.amsterdam state msg isCreate = .ok (.frame f a) → f.Canonical := by
    intro state isCreate hp
    have hprep := prepareTopLevelAmsterdam_canonical (state := state) h
    unfold TopLevel.prepare.amsterdam at hp
    split at hp
    · cases hp
    · rename_i devm he
      exact absurd he (prepareTopLevelAmsterdam_error_ne_revert state msg devm)
    · cases hp
    · cases hp
    · rename_i prepared devm he
      rw [he] at hprep
      cases hp
      exact Frame.prepared_canonical hprep.2 hprep.1 isCreate
  unfold TopLevel.prepare at hp
  split at hp
  · unfold TopLevel.prepare.create at hp
    split at hp
    · split at hp
      · cases hp
      · cases hp
        exact Frame.ofTop_canonical h true
    · exact amsterdam _ _ hp
  · unfold TopLevel.prepare.call at hp
    split at hp
    · split at hp
      · cases hp
      · rename_i delegated refund hauth
        cases hp
        exact Frame.ofTop_canonical
          (TopLevel.resolveCodeDelegation_canonical (processMessageCall.authorize_canonical h hauth))
          false
    · exact amsterdam _ _ hp

/-- **A successful top-level message run leaves a canonical state**, for a frame and for a
refusal. -/
theorem Message.run_canonical {msg : Msg} (h : msg.Canonical) {run : MessageRun}
    (hp : Message.run msg = .ok run) : run.state.Canonical := by
  unfold Message.run at hp
  obtain ⟨prep, hprep, hp⟩ := Except.bind_eq_ok hp
  cases prep with
  | refused reason halted =>
    cases hp
    exact h.1.1
  | frame f a =>
    have hf := TopLevel.prepare_canonical h hprep
    dsimp only at hp
    split at hp
    · rename_i result he
      obtain ⟨r, hr, hp⟩ := Except.bind_eq_ok hp
      cases hp
      have hrun : Frame.runTop f = .ok r := by
        unfold Frame.runTop
        rw [he]
        exact hr
      exact (Frame.runTop_canonical hf hrun).1
    · rename_i evm he
      obtain ⟨r, hr, hp⟩ := Except.bind_eq_ok hp
      cases hp
      have hrun : Frame.runTop f = .ok r := by
        unfold Frame.runTop
        rw [he]
        exact hr
      exact (Frame.runTop_canonical hf hrun).1

/-! ### The transaction -/

/-- What the admission checks hand on is the block environment with the transaction begun. -/
theorem Transaction.check_benv {benv : Benv} {bout : BlockOutput} {tx : Transaction}
    {index : Nat} {checked : Transaction.Checked}
    (h : Transaction.check benv bout tx index = .ok checked) :
    checked.benv = benv.beginTransaction := by
  unfold Transaction.check at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases h
  rfl

/-- A prepared transaction's top-level message is canonical when the checked environment is. -/
theorem Transaction.prepare_canonical {checked : Transaction.Checked} {tx : Transaction}
    {index : Nat} (h : checked.benv.Canonical) {prepared : Transaction.Prepared}
    (hp : Transaction.prepare checked tx index = .ok prepared) : prepared.msg.Canonical := by
  unfold Transaction.prepare at hp
  obtain ⟨st, hst, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨msg, hmsg, hp⟩ := Except.bind_eq_ok hp
  cases hp
  have hstc : st.Canonical :=
    State.Canonical.subBal (State.Canonical.incrNonce h.1 _) (Option.toExcept_eq_ok hst)
  exact prepareMessage_canonical (by exact ⟨hstc, h.2⟩)
    (by exact TransientStorage.canonical_empty) hmsg

/-- Settlement keeps the message run's state canonical: the fee movements are balance credits,
then the self-destructs and the sweep only erase accounts. -/
theorem B2.Transaction.settle_canonical {prepared : Transaction.Prepared} {tx : Transaction}
    {index : Nat} {run : MessageRun} (h : run.state.Canonical) {p}
    (hp : B2.Transaction.settle prepared tx index run = .ok p) : State.Canonical p.1 := by
  unfold B2.Transaction.settle at hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact State.Canonical.sweepTouchedAccounts (State.Canonical.settleSelfdestructs
    (State.Canonical.addBal (State.Canonical.addBal h _ _) _ _) _ _) _ _

/-- **A successful transaction leaves a canonical state**: the fee movements go through
`incrNonce`/`subBal`/`addBal`, the call itself through `Message.run`, and settlement follows the
fork's SELFDESTRUCT rule. -/
theorem B2.processTransaction_canonical {benv : Benv} (h : benv.Canonical)
    {bout : BlockOutput} {tx : Transaction} {index : Nat} {p}
    (hp : B2.processTransaction benv bout tx index = .ok p) :
    State.Canonical p.1 := by
  unfold B2.processTransaction at hp
  obtain ⟨checked, hchecked, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨prepared, hprepared, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨run, hrun, hp⟩ := Except.bind_eq_ok hp
  have hb : checked.benv.Canonical := by
    rw [Transaction.check_benv hchecked]
    exact ⟨h.1, h.1⟩
  have hm := Transaction.prepare_canonical hb hprepared
  exact B2.Transaction.settle_canonical
    (Message.run_canonical hm (Except.mapError_eq_ok_iff.mp hrun)) hp

/-- Settlement into a transaction run keeps the message run's state canonical: the fee
movements are balance credits, then the self-destructs and the sweep only erase accounts. -/
theorem B2.Transaction.settleRun_canonical {checked : Transaction.Checked}
    {prepared : Transaction.Prepared} {tx : Transaction} {index : Nat} {run : MessageRun}
    (h : run.state.Canonical) {p}
    (hp : B2.Transaction.settleRun checked prepared tx index run = .ok p) :
    State.Canonical p.1.state := by
  unfold B2.Transaction.settleRun at hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact State.Canonical.sweepTouchedAccounts (State.Canonical.settleSelfdestructs
    (State.Canonical.addBal (State.Canonical.addBal h _ _) _ _) _ _) _ _

/-- **A successful transaction run leaves a canonical state**: the fee movements go through
`incrNonce`/`subBal`/`addBal`, the call itself through `Message.run`, and settlement follows the
fork's SELFDESTRUCT rule. -/
theorem B2.Transaction.run_canonical {benv : Benv} (h : benv.Canonical)
    {bout : BlockOutput} {tx : Transaction} {index : Nat} {p}
    (hp : B2.Transaction.run benv bout tx index = .ok p) :
    State.Canonical p.1.state := by
  unfold B2.Transaction.run at hp
  obtain ⟨checked, hchecked, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨prepared, hprepared, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨run, hrun, hp⟩ := Except.bind_eq_ok hp
  have hb : checked.benv.Canonical := by
    rw [Transaction.check_benv hchecked]
    exact ⟨h.1, h.1⟩
  have hm := Transaction.prepare_canonical hb hprepared
  exact B2.Transaction.settleRun_canonical
    (Message.run_canonical hm (Except.mapError_eq_ok_iff.mp hrun)) hp

/-! ### The system calls -/

/-- The single boundary all four system transactions share. -/
theorem processSystemTransaction_canonical {benv : Benv} (h : benv.Canonical)
    {target : Address} {code : ByteArray} {data : Bytes} {run : MessageRun}
    (hp : processSystemTransaction benv target code data = .ok run) :
    run.state.Canonical := by
  unfold processSystemTransaction at hp
  obtain ⟨run', hrun, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact Message.run_canonical
    (by exact ⟨⟨h.1, h.1⟩, TransientStorage.canonical_empty⟩) hrun

theorem processUncheckedSystemTransaction_canonical {benv : Benv}
    (h : benv.Canonical) {target : Address} {data : Bytes} {run : MessageRun}
    (hp : processUncheckedSystemTransaction benv target data = .ok run) :
    run.state.Canonical :=
  processSystemTransaction_canonical h hp

theorem processCheckedSystemTransaction_canonical {benv : Benv}
    (h : benv.Canonical) {target : Address} {data : Bytes} {run : MessageRun}
    (hp : processCheckedSystemTransaction benv target data = .ok run) :
    run.state.Canonical := by
  unfold processCheckedSystemTransaction at hp
  dsimp only at hp
  split at hp
  · obtain ⟨u, hu, hp⟩ := Except.bind_eq_ok hp
    nomatch hu
  · obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    split at hp
    · nomatch hp
    · cases hp
      exact processSystemTransaction_canonical h (Except.mapError_eq_ok_iff.mp hq)

/-- Every prefix of the request fold leaves a canonical state.

An induction on the contract list, so the proof does not grow when the list does. -/
theorem runRequestContracts_canonical (idx : Nat) :
    ∀ (rs : List (UInt8 × Address)) {benv : Benv}, benv.Canonical →
      ∀ {acc : List Bytes} {bal : BlockAccessListBuilder} {p},
        runRequestContracts idx rs benv acc bal = .ok p → State.Canonical p.1
  | [], _, h, _, _, _, hp => by cases hp; exact h.1
  | _ :: rs, benv, h, acc, bal, p, hp => by
    unfold runRequestContracts at hp
    obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    exact runRequestContracts_canonical idx rs
      (by exact ⟨processCheckedSystemTransaction_canonical h hq, h.2⟩) hp

theorem processGeneralPurposeRequestsAt_canonical {balIndex : Nat} {benv : Benv}
    (h : benv.Canonical) {bout : BlockOutput} {p}
    (hp : processGeneralPurposeRequestsAt balIndex benv bout = .ok p) :
    State.Canonical p.1 := by
  unfold processGeneralPurposeRequestsAt at hp
  obtain ⟨dr, _, hp⟩ := Except.bind_eq_ok hp
  dsimp only at hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact runRequestContracts_canonical _ _ h hq

theorem processGeneralPurposeRequests_canonical {benv : Benv}
    (h : benv.Canonical) {bout : BlockOutput} {p}
    (hp : processGeneralPurposeRequests benv bout = .ok p) :
    State.Canonical p.1 :=
  processGeneralPurposeRequestsAt_canonical h hp

theorem beaconRootsCall_canonical {rules : ForkRules} {benv : Benv}
    (h : benv.Canonical) {p} (hp : beaconRootsCall rules benv = .ok p) :
    State.Canonical p.1 := by
  unfold beaconRootsCall at hp
  split at hp
  · obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    cases hp
    exact processUncheckedSystemTransaction_canonical h (Except.mapError_eq_ok_iff.mp hq)
  · cases hp; exact h.1

theorem historyStorageCall_canonical {rules : ForkRules} {benv : Benv}
    (h : benv.Canonical) {bal : BlockAccessListBuilder} {p}
    (hp : historyStorageCall rules benv bal = .ok p) : State.Canonical p.1 := by
  unfold historyStorageCall at hp
  split at hp
  · obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
    obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    cases hp
    exact processUncheckedSystemTransaction_canonical h (Except.mapError_eq_ok_iff.mp hq)
  · cases hp; exact h.1

/-! ### The body -/

/-- Crediting balances in turn keeps a state canonical. -/
theorem State.Canonical.creditAll {state : State} (h : state.Canonical)
    (credits : List (Address × Nat)) : (creditAll credits state).Canonical := by
  unfold Jaune.Staging.creditAll
  induction credits generalizing state with
  | nil => exact h
  | cons c cs ih => exact ih (State.Canonical.addBal h _ _)

/-- **One body operation keeps the prefix's state canonical.** The step reads the prefix's state
in place of the block environment's, so of the environment only its original state is asked:
system calls, transactions, withdrawals, request calls and rewards preserve the invariant, and the
other operations leave the state alone. -/
theorem Body.step_canonical {benv : Benv} (hb : benv.stat.Canonical) {p : Body.Prefix}
    (hp : p.state.Canonical) {op : BodyOp} {r : OpRun} {q : Body.Prefix}
    (hs : Body.step benv p op = .ok (r, q)) : q.state.Canonical := by
  have he : (benv.withState p.state).Canonical := ⟨hp, hb⟩
  cases op with
  | systemCall address data index =>
    simp only [Body.step] at hs
    obtain ⟨d, _, hs⟩ := Except.bind_eq_ok hs
    obtain ⟨run, hrun, hs⟩ := Except.bind_eq_ok hs
    cases hs
    exact processUncheckedSystemTransaction_canonical he (Except.mapError_eq_ok_iff.mp hrun)
  | transaction tx index =>
    simp only [Body.step] at hs
    obtain ⟨⟨run, bout⟩, ht, hs⟩ := Except.bind_eq_ok hs
    cases hs
    exact B2.Transaction.run_canonical he ht
  | withdrawals ws index =>
    simp only [Body.step] at hs
    cases hs
    exact processWithdrawalsState_canonical hp ws
  | depositRequests =>
    simp only [Body.step] at hs
    obtain ⟨_, _, hs⟩ := Except.bind_eq_ok hs
    cases hs
    exact hp
  | requestCall type address index =>
    simp only [Body.step] at hs
    obtain ⟨run, hrun, hs⟩ := Except.bind_eq_ok hs
    cases hs
    exact processCheckedSystemTransaction_canonical he hrun
  | rewards coinbase minerReward credits =>
    simp only [Body.step] at hs
    cases hs
    exact State.Canonical.creditAll (State.Canonical.addBal hp _ _) credits
  | buildAccessList =>
    simp only [Body.step] at hs
    cases hs
    exact hp
  | checkAccessListLimit =>
    simp only [Body.step] at hs
    obtain ⟨_, _, hs⟩ := Except.bind_eq_ok hs
    cases hs
    exact hp

/-- A run of operations keeps the prefix's state canonical. -/
theorem Body.run_canonical {benv : Benv} (hb : benv.stat.Canonical) :
    ∀ (ops : List BodyOp) {p : Body.Prefix}, p.state.Canonical →
      ∀ {rs : List OpRun} {q : Body.Prefix}, Body.run benv p ops = .ok (rs, q) →
        q.state.Canonical
  | [], _, hp, _, _, hr => by cases hr; exact hp
  | op :: ops, p, hp, rs, q, hr => by
    simp only [Body.run] at hr
    obtain ⟨⟨r, p'⟩, hs, hr⟩ := Except.bind_eq_ok hr
    obtain ⟨⟨rs', q'⟩, hr', hr⟩ := Except.bind_eq_ok hr
    cases hr
    exact Body.run_canonical hb ops (Body.step_canonical hb hp hs) hr'

/-- A fold of operations keeps the prefix's state canonical. -/
theorem Body.fold_canonical {benv : Benv} (hb : benv.stat.Canonical) :
    ∀ (ops : List BodyOp) {p : Body.Prefix}, p.state.Canonical →
      ∀ {q : Body.Prefix}, Body.fold benv p ops = .ok q → q.state.Canonical
  | [], _, hp, _, hf => by cases hf; exact hp
  | op :: ops, p, hp, q, hf => by
    simp only [Body.fold] at hf
    obtain ⟨⟨r, p'⟩, hs, hf⟩ := Except.bind_eq_ok hf
    exact Body.fold_canonical hb ops (Body.step_canonical hb hp hs) hf

/-- The importer's body leaves a canonical state. -/
theorem Body.importer_canonical {benv : Benv} (h : benv.Canonical)
    {txs : List (Bytes ⊕ Transaction)} {ommers : List Header} {wds : List Withdrawal}
    {q : Body.Prefix} (hp : Body.importer benv txs ommers wds = .ok q) : q.state.Canonical := by
  unfold Body.importer at hp
  obtain ⟨decoded, _, hp⟩ := Except.bind_eq_ok hp
  exact Body.fold_canonical h.2 _ (by exact h.1) hp

/-- **A successful block body leaves a canonical state**: system calls, transactions,
withdrawals, general-purpose requests and the proof-of-work rewards all preserve the invariant,
whether each is run or gated off. -/
theorem applyBody_canonical {benv : Benv} (h : benv.Canonical)
    {txs : List (Bytes ⊕ Transaction)} {ommers : List Header} {wds : List Withdrawal} {p}
    (hp : applyBody benv txs ommers wds = .ok p) : State.Canonical p.1 := by
  unfold applyBody at hp
  cases hq : Body.importer benv txs ommers wds with
  | error e => rw [hq] at hp; cases hp
  | ok q =>
    rw [hq] at hp
    cases hp
    exact Body.importer_canonical h hq

/-! ### The block transition -/

/-- **Canonicality depends on the common execution body**, not on the resolver or the error
carrier. -/
theorem E.stateTransitionCoreE_canonical {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch : BlockChain} (h : ch.Canonical) {block : Block} {ch'}
    {checkOmmers : Unit → Except ε Unit}
    (hp : E.stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    ch'.Canonical := by
  unfold E.stateTransitionCoreE at hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact Body.importer_canonical (by exact ⟨h, h⟩) (Except.mapError_eq_ok_iff.mp hq)

end Jaune.Staging
