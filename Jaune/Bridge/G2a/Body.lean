import Jaune.Bridge.G2a.Phased
import Jaune.Bridge.G2a.Consumers
import Jaune.Run.Body
import Jaune.Run.BodyFacts

/-!
# W2 cut D: bridges for the body run (goal `jaune-shape-and-names-v1`, gate G2a, bridge)

Old side = `applyBody` and `stateTransitionCoreE` at `ba15f397` (`Jaune.Transaction`), unedited,
with cut B2's bridges (`Jaune.Bridge.G2a.Consumers`) for the system calls and the transaction. New
side = `Jaune.Run.Body`.

The importer now decodes the whole transaction list before the pre-execution system calls (goal
§5.1 decision 14); `applyBody` decoded it after them. The cut is bridged by a difference theorem:

* `Body.importerAfter` is the old order over `Body.step` (bridge only), and
  `applyBody_eq_importerAfter` proves it equal to `applyBody` on every input.
* `Except.bind_comm_or_both_error`: two independent computations commute in `Except` unless both
  fail, and then each order reports its own first failure.
* `applyBody_eq_of_not_split`, `applyBody_of_split`, `applyBody_ok_iff`, `applyBody_error_iff`:
  the new body equals the old one except when the pre-execution system calls fail *and* the decode
  fails (`DecodeOrderSplit`); there the old body reports the system call's error and the new one
  the decode's. A success is the same success, and an error is an error, in both orders.
* The same at the block transition (`stateTransitionCoreE_difference`).
-/

namespace Jaune.Bridge.G2a

open Jaune Jaune.Staging

/-! ### Generic: reordering two independent computations in `Except` -/

/-- Two computations whose results are only read afterwards commute in `Except`, unless both fail;
then each order reports the failure of the one it ran first. -/
theorem Except.bind_comm_or_both_error {ε α β γ : Type} (A : Except ε α) (B : Except ε β)
    (k : α → β → Except ε γ) :
    ((A >>= fun a => B >>= fun b => k a b) = (B >>= fun b => A >>= fun a => k a b)) ∨
      ∃ ea eb, A = .error ea ∧ B = .error eb := by
  cases A with
  | error ea =>
    cases B with
    | error eb => exact .inr ⟨ea, eb, rfl, rfl⟩
    | ok b => exact .inl rfl
  | ok a =>
    cases B with
    | error eb => exact .inl rfl
    | ok b => exact .inl rfl

/-! ### The transaction appends one receipt key -/

theorem processTransaction_receiptKeys {benv : Benv} {bout : BlockOutput} {tx : Transaction}
    {index : Nat} {q : State × BlockOutput}
    (h : B2.processTransaction benv bout tx index = .ok q) :
    q.2.receiptKeys = bout.receiptKeys ++ [Rlp.Item.toBytes (.bytes index.toBytes)] := by
  unfold B2.processTransaction at h
  obtain ⟨checked, hc, h⟩ := Except.bind_eq_ok h
  obtain ⟨prepared, hp, h⟩ := Except.bind_eq_ok h
  obtain ⟨run, _, h⟩ := Except.bind_eq_ok h
  have hcb : checked.bout.receiptKeys = bout.receiptKeys := by
    unfold Transaction.check at hc
    obtain ⟨_, hb, hc⟩ := Except.bind_eq_ok hc
    cases hb
    obtain ⟨_, _, hc⟩ := Except.bind_eq_ok hc
    obtain ⟨⟨_, _⟩, _, hc⟩ := Except.bind_eq_ok hc
    obtain ⟨⟨_, _, _, _⟩, _, hc⟩ := Except.bind_eq_ok hc
    cases hc
    rfl
  have hpb : prepared.bout = checked.bout := by
    unfold Transaction.prepare at hp
    obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
    obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
    cases hp
    rfl
  unfold B2.Transaction.settle at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases h
  simp [hpb, hcb, BlockOutput.withGasSettlement]

/-! `Body.fold_append` is in `Jaune.Run.BodyFacts`. -/

/-! ### The pre-execution system calls -/

@[simp] theorem Benv.withState_stat (benv : Benv) (s : State) : (benv.withState s).stat = benv.stat :=
  rfl

@[simp] theorem Benv.withState_state (benv : Benv) (s : State) : (benv.withState s).state = s := rfl

@[simp] theorem Benv.withState_self (benv : Benv) : benv.withState benv.state = benv := rfl

@[simp] theorem Benv.withState_withState (benv : Benv) (s t : State) :
    (benv.withState s).withState t = benv.withState t := rfl

@[simp] theorem Body.Prefix.state_init (s : State) : (Body.Prefix.init s).state = s := rfl

theorem fold_systemCall (benv : Benv) (p : Body.Prefix) (address : Address)
    (data : Except TransitionError Bytes) (index : Nat) (rest : List BodyOp) :
    Body.fold benv p (.systemCall address data index :: rest) =
      (do
        let d ← data
        let run ← (Staging.processUncheckedSystemTransaction (benv.withState p.state) address d).mapError
          (fun e => TransitionError.vm e.toEvmError)
        Body.fold benv
          { p with
            state := run.state
            accessList := p.accessList.incorporateSystem benv.stat.rules index p.state run.state
              (address :: run.accountReads.toList) run.storageReads.toList
              run.storageWrites.toList }
          rest) := by
  simp only [Body.fold, Body.step]
  cases data with
  | error e => rfl
  | ok d =>
    simp only [bind, Except.bind, pure, Except.pure, Except.mapError]
    cases Staging.processUncheckedSystemTransaction (benv.withState p.state) address d <;> rfl

theorem fold_preOps (benv : Benv) (rest : List BodyOp) :
    Body.fold benv (Body.Prefix.init benv.state) (Body.preOps benv ++ rest) =
      (do
        let ⟨stB, bal⟩ ← beaconRootsCall benv.stat.rules benv
        let ⟨stH, bal⟩ ← historyStorageCall benv.stat.rules (benv.withState stB) bal
        Body.fold benv
          (Body.Prefix.ofBlockOutput stH {BlockOutput.init with blockAccessListBuilder := bal})
          rest) := by
  simp only [← beaconRootsCall_eq, ← historyStorageCall_eq]
  unfold Body.preOps Staging.beaconRootsCall Staging.historyStorageCall
  cases hb : benv.stat.rules.systemCalls.beaconRoots <;>
    cases hh : benv.stat.rules.systemCalls.historyStorage <;>
    simp only [hb, hh, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append,
      List.singleton_append, fold_systemCall, Benv.withState_stat, Benv.withState_state,
      Benv.withState_self, Body.Prefix.state_init]
  all_goals
    cases benv.stat.blockHashes.getLast? <;>
    simp only [bind, Except.bind, pure, Except.pure, Except.mapError, Except.map, Option.toExcept,
      Benv.withState_self]
  all_goals first
    | rfl
    | (cases Staging.processUncheckedSystemTransaction benv beaconRootsAddress
          benv.stat.parentBeaconBlockRoot.toBytes with
        | error e => rfl
        | ok run =>
          first
            | rfl
            | (dsimp only
               split <;> rfl))
    | (cases Staging.processUncheckedSystemTransaction benv historyStorageAddress _ <;> rfl)

/-! ### The transactions -/

theorem fold_transactions (benv : Benv) :
    ∀ (l : List (Nat × Transaction)) (p : Body.Prefix) (rest : List BodyOp),
      Body.fold benv p (l.map (fun ⟨i, tx⟩ => BodyOp.transaction tx i) ++ rest) =
        (applyTransactions l (benv.withState p.state) p.toBlockOutput >>= fun q =>
          Body.fold benv (Body.Prefix.ofBlockOutput q.1.state q.2) rest)
  | [], p, rest => rfl
  | ⟨i, tx⟩ :: l, p, rest => by
    simp only [List.map_cons, List.cons_append, Body.fold, Body.step, applyTransactions,
      ← processTransaction_eq_b2, ← B2.Transaction.run_output]
    cases h : B2.Transaction.run (benv.withState p.state) p.toBlockOutput tx i with
    | error e => rfl
    | ok q =>
      obtain ⟨run, b⟩ := q
      simp only [bind, Except.bind, pure, Except.pure]
      rw [fold_transactions benv l]
      rfl

/-- `applyTransactions` keeps the block environment apart from its state. -/
theorem applyTransactions_benv (benv : Benv) :
    ∀ (l : List (Nat × Transaction)) (s : State) (bout : BlockOutput) {q},
      applyTransactions l (benv.withState s) bout = .ok q → q.1 = benv.withState q.1.state
  | [], s, bout, q, h => by cases h; rfl
  | ⟨i, tx⟩ :: l, s, bout, q, h => by
    unfold applyTransactions at h
    obtain ⟨⟨st, b⟩, _, h⟩ := Except.bind_eq_ok h
    exact applyTransactions_benv benv l st b h

/-- Each transaction `applyTransactions` runs appends one receipt key. -/
theorem applyTransactions_receiptKeys :
    ∀ (l : List (Nat × Transaction)) (benv : Benv) (bout : BlockOutput) {q},
      applyTransactions l benv bout = .ok q →
        q.2.receiptKeys.length = bout.receiptKeys.length + l.length
  | [], benv, bout, q, h => by cases h; rfl
  | ⟨i, tx⟩ :: l, benv, bout, q, h => by
    unfold applyTransactions at h
    obtain ⟨⟨st, b⟩, hq, h⟩ := Except.bind_eq_ok h
    rw [← processTransaction_eq_b2] at hq
    have hk := processTransaction_receiptKeys hq
    rw [applyTransactions_receiptKeys l _ b h]
    simp only at hk
    simp [hk]
    omega

/-! ### The requests -/

theorem fold_requestCalls (benv : Benv) (idx : Nat) :
    ∀ (contracts : List (UInt8 × Address)) (p : Body.Prefix) (rest : List BodyOp),
      Body.fold benv p (contracts.map (fun ⟨type, address⟩ => BodyOp.requestCall type address idx) ++
          rest) =
        (Staging.runRequestContracts idx contracts (benv.withState p.state) p.requests
            p.accessList >>= fun ⟨st, acc, bal⟩ =>
          Body.fold benv { p with state := st, requests := acc, accessList := bal } rest)
  | [], p, rest => rfl
  | ⟨type, address⟩ :: contracts, p, rest => by
    simp only [List.map_cons, List.cons_append, Body.fold, Body.step, Staging.runRequestContracts,
      Benv.withState_stat, Benv.withState_state, Benv.withState_withState]
    cases Staging.processCheckedSystemTransaction (benv.withState p.state) address [] with
    | error e => rfl
    | ok run =>
      simp only [bind, Except.bind, pure, Except.pure]
      exact fold_requestCalls benv idx contracts _ rest

theorem fold_requests (benv : Benv) (idx : Nat) (p : Body.Prefix) (rest : List BodyOp) :
    Body.fold benv p ((BodyOp.depositRequests :: benv.stat.rules.requests.map
        (fun ⟨type, address⟩ => BodyOp.requestCall type address idx)) ++ rest) =
      (Staging.processGeneralPurposeRequestsAt idx (benv.withState p.state) p.toBlockOutput >>=
        fun q => Body.fold benv (Body.Prefix.ofBlockOutput q.1 q.2) rest) := by
  simp only [List.cons_append, Body.fold, Body.step, Staging.processGeneralPurposeRequestsAt,
    Benv.withState_stat]
  cases parseDepositRequests p.toBlockOutput with
  | error e => rfl
  | ok d =>
    simp only [bind, Except.bind, pure, Except.pure]
    rw [fold_requestCalls]
    simp only [Body.Prefix.toBlockOutput]
    cases Staging.runRequestContracts idx benv.stat.rules.requests (benv.withState p.state)
      (if d.length > 0 then p.requests ++ [depositRequestType ++ d] else p.requests) p.accessList with
    | error e => rfl
    | ok r => rfl

/-! ### The post-execution operations -/

theorem withdrawalsPass_receiptKeys (rules : ForkRules) (benv : Benv) (bout : BlockOutput)
    (wds : List Withdrawal) : (withdrawalsPass rules benv bout wds).2.receiptKeys = bout.receiptKeys := by
  unfold withdrawalsPass
  split <;> rfl

theorem fold_withdrawalsOps (benv : Benv) (p : Body.Prefix) (n : Nat) (wds : List Withdrawal)
    (rest : List BodyOp) (hk : p.receiptKeys.length = n) :
    Body.fold benv p
        ((if benv.stat.rules.header.withdrawalsRoot then [BodyOp.withdrawals wds (n + 1)] else []) ++
          rest) =
      Body.fold benv
        (Body.Prefix.ofBlockOutput
          (withdrawalsPass benv.stat.rules (benv.withState p.state) p.toBlockOutput wds).1
          (withdrawalsPass benv.stat.rules (benv.withState p.state) p.toBlockOutput wds).2) rest := by
  subst hk
  unfold withdrawalsPass
  cases benv.stat.rules.header.withdrawalsRoot <;> rfl

theorem fold_requestsOps (benv : Benv) (p : Body.Prefix) (n : Nat) (rest : List BodyOp)
    (hk : p.receiptKeys.length = n) :
    Body.fold benv p
        ((if benv.stat.rules.header.requestsHash then
            BodyOp.depositRequests :: benv.stat.rules.requests.map
              (fun ⟨type, address⟩ => BodyOp.requestCall type address (n + 1))
          else []) ++ rest) =
      (requestsPass benv.stat.rules (benv.withState p.state) p.toBlockOutput >>= fun q =>
        Body.fold benv (Body.Prefix.ofBlockOutput q.1 q.2) rest) := by
  subst hk
  unfold requestsPass
  cases benv.stat.rules.header.requestsHash with
  | false => rfl
  | true =>
    simp only [if_true]
    rw [fold_requests, processGeneralPurposeRequests, ← processGeneralPurposeRequestsAt_eq]
    rfl

theorem payRewards_eq (pow : ProofOfWorkRules) (number : Nat) (coinbase : Address)
    (ommers : List Header) (st : State) :
    payRewards pow number coinbase ommers st =
      creditAll (ommers.map fun ommer =>
          (ommer.coinbase, (8 + ommer.number - number) * pow.blockReward / 8))
        (st.addBal coinbase (pow.blockReward + ommers.length * (pow.blockReward / 32)).toU256) := by
  simp only [payRewards, creditAll, List.foldl_map]

theorem fold_tailOps (benv : Benv) (p : Body.Prefix) (ommers : List Header) :
    Body.fold benv p
        ((match benv.stat.rules.proofOfWork with
          | none => []
          | some pow =>
            [BodyOp.rewards benv.stat.coinbase
              (pow.blockReward + ommers.length * (pow.blockReward / 32))
              (ommers.map fun ommer =>
                (ommer.coinbase, (8 + ommer.number - benv.stat.number) * pow.blockReward / 8))]) ++
          [BodyOp.buildAccessList, BodyOp.checkAccessListLimit]) =
      (do
        let stRewards := match benv.stat.rules.proofOfWork with
          | none => p.state
          | some pow => payRewards pow benv.stat.number benv.stat.coinbase ommers p.state
        let list := match benv.stat.rules.blockAccessListRules with
          | none => []
          | some _ => p.accessList.build
        checkBlockAccessListGasLimit benv.stat.rules benv.stat.blockGasLimit list
        .ok (Body.Prefix.ofBlockOutput stRewards {p.toBlockOutput with blockAccessList := list})) := by
  cases benv.stat.rules.proofOfWork with
  | none =>
    simp only [List.nil_append, Body.fold, Body.step, bind, Except.bind, pure, Except.pure]
    cases checkBlockAccessListGasLimit benv.stat.rules benv.stat.blockGasLimit
      (match benv.stat.rules.blockAccessListRules with
        | none => []
        | some _ => p.accessList.build) <;> rfl
  | some pow =>
    simp only [List.cons_append, List.nil_append, Body.fold, Body.step, payRewards_eq, bind,
      Except.bind, pure, Except.pure]
    cases checkBlockAccessListGasLimit benv.stat.rules benv.stat.blockGasLimit
      (match benv.stat.rules.blockAccessListRules with
        | none => []
        | some _ => p.accessList.build) <;> rfl

theorem fold_postOps (benv : Benv) (p : Body.Prefix) (n : Nat) (ommers : List Header)
    (wds : List Withdrawal) (hk : p.receiptKeys.length = n) :
    Body.fold benv p (Body.postOps benv n ommers wds) =
      (do
        let rules := benv.stat.rules
        let ⟨stWds, boutWds⟩ := withdrawalsPass rules (benv.withState p.state) p.toBlockOutput wds
        let ⟨stReq, boutReq⟩ ← requestsPass rules ((benv.withState p.state).withState stWds) boutWds
        let stRewards := match rules.proofOfWork with
          | none => stReq
          | some pow => payRewards pow benv.stat.number benv.stat.coinbase ommers stReq
        let list := match rules.blockAccessListRules with
          | none => []
          | some _ => boutReq.blockAccessListBuilder.build
        checkBlockAccessListGasLimit rules benv.stat.blockGasLimit list
        .ok (Body.Prefix.ofBlockOutput stRewards {boutReq with blockAccessList := list})) := by
  unfold Body.postOps
  simp only [List.append_assoc]
  rw [fold_withdrawalsOps benv p n wds _ hk, fold_requestsOps _ _ n _
    (by
      show (withdrawalsPass _ _ _ _).2.receiptKeys.length = n
      rw [withdrawalsPass_receiptKeys]; exact hk)]
  simp only [Body.Prefix.state_ofBlockOutput, Body.Prefix.toBlockOutput_ofBlockOutput,
    Benv.withState_withState]
  rcases withdrawalsPass benv.stat.rules (benv.withState p.state) p.toBlockOutput wds with ⟨stW, bW⟩
  dsimp only
  cases requestsPass benv.stat.rules (benv.withState stW) bW with
  | error e => rfl
  | ok a =>
    simp only [bind, Except.bind]
    refine (fold_tailOps benv _ ommers).trans ?_
    simp only [bind, Except.bind]
    rfl

/-! ### The old order over the steps -/

/-- The old order over `Body.step`: the pre-execution system calls, then the decode, then the rest.
Bridge only. -/
def Body.importerAfter (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
    (wds : List Withdrawal) : Except TransitionError Body.Prefix := do
  let p ← Body.fold benv (Body.Prefix.init benv.state) (Body.preOps benv)
  let decoded ← txs.mapM (decodeTransaction benv.stat.rules)
  Body.fold benv p (Body.transactionOps decoded ++ Body.postOps benv decoded.length ommers wds)

/-- **`applyBody` is the old order over the steps**, on every input, through the output map. -/
theorem applyBody_eq_importerAfter (benv : Benv) (txs : List (Bytes ⊕ Transaction))
    (ommers : List Header) (wds : List Withdrawal) :
    applyBody benv txs ommers wds = Body.Prefix.output <$> Body.importerAfter benv txs ommers wds := by
  unfold Body.importerAfter applyBody
  have hpre := fold_preOps benv []
  simp only [List.append_nil] at hpre
  rw [hpre]
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Benv.withState_stat,
    Benv.withState_withState, Benv.withState_state]
  cases beaconRootsCall benv.stat.rules benv with
  | error e => rfl
  | ok r1 =>
    obtain ⟨stB, balB⟩ := r1
    simp only []
    cases historyStorageCall benv.stat.rules (benv.withState stB) balB with
    | error e => rfl
    | ok r2 =>
      obtain ⟨stH, balH⟩ := r2
      simp only [Body.fold, pure, Except.pure]
      cases txs.mapM (decodeTransaction benv.stat.rules) with
      | error e => rfl
      | ok decoded =>
        simp only [Body.transactionOps, fold_transactions, Body.Prefix.state_ofBlockOutput,
          Body.Prefix.toBlockOutput_ofBlockOutput, bind, Except.bind]
        cases hq : applyTransactions decoded.putIndex (benv.withState stH)
          {BlockOutput.init with blockAccessListBuilder := balH} with
        | error e => rfl
        | ok q =>
          have hb := applyTransactions_benv benv _ _ _ hq
          have hk := applyTransactions_receiptKeys _ _ _ hq
          obtain ⟨b, o⟩ := q
          simp only at hb hk
          simp only [BlockOutput.init, List.length_nil, Nat.zero_add, length_putIndex] at hk
          rw [hb]
          simp only [Body.Prefix.state_ofBlockOutput, Benv.withState_state]
          rw [fold_postOps benv _ decoded.length ommers wds hk]
          simp only [Body.Prefix.state_ofBlockOutput, Body.Prefix.toBlockOutput_ofBlockOutput]
          rcases withdrawalsPass benv.stat.rules (benv.withState b.state) o wds with ⟨stW, bW⟩
          simp only [bind, Except.bind, Benv.withState_withState]
          cases requestsPass benv.stat.rules (benv.withState stW) bW with
          | error e => rfl
          | ok r =>
            cases benv.stat.rules.blockAccessListRules
            · simp only []
              cases checkBlockAccessListGasLimit benv.stat.rules benv.stat.blockGasLimit [] <;> rfl
            · simp only []
              cases checkBlockAccessListGasLimit benv.stat.rules benv.stat.blockGasLimit
                r.2.blockAccessListBuilder.build <;> rfl

/-! ### The difference theorem for the decode order (decision 14) -/

/-- The old body's pre-execution system calls: the beacon-roots call, then the history-storage
call, as `applyBody` at `ba15f397` runs them. -/
def preCalls (benv : Benv) : Except TransitionError (State × BlockAccessListBuilder) := do
  let ⟨stB, bal⟩ ← beaconRootsCall benv.stat.rules benv
  historyStorageCall benv.stat.rules (benv.withState stB) bal

/-- The decode of the whole transaction list. -/
def decodeAll (benv : Benv) (txs : List (Bytes ⊕ Transaction)) :
    Except TransitionError (List Transaction) :=
  txs.mapM (decodeTransaction benv.stat.rules)

/-- **The decode-order split**: the inputs on which the old and the new order can differ. The
pre-execution system calls fail (in Jaune only with a fault, or the history call's internal "block
hashes is empty", which `validateHeader` makes unreachable at the block transition) *and* the
transaction list does not decode. -/
def DecodeOrderSplit (benv : Benv) (txs : List (Bytes ⊕ Transaction)) : Prop :=
  (∃ e, preCalls benv = .error e) ∧ ∃ e, decodeAll benv txs = .error e

theorem fold_preOps_eq (benv : Benv) :
    Body.fold benv (Body.Prefix.init benv.state) (Body.preOps benv) =
      (fun (r : State × BlockAccessListBuilder) =>
        Body.Prefix.ofBlockOutput r.1 {BlockOutput.init with blockAccessListBuilder := r.2}) <$>
        preCalls benv := by
  have h := fold_preOps benv []
  simp only [List.append_nil] at h
  rw [h]
  unfold preCalls
  cases beaconRootsCall benv.stat.rules benv with
  | error e => rfl
  | ok r1 =>
    obtain ⟨stB, balB⟩ := r1
    simp only [bind, Except.bind]
    cases historyStorageCall benv.stat.rules (benv.withState stB) balB <;> rfl

theorem importer_eq (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
    (wds : List Withdrawal) :
    Body.importer benv txs ommers wds =
      (decodeAll benv txs >>= fun d =>
        Body.fold benv (Body.Prefix.init benv.state) (Body.preOps benv) >>= fun p =>
          Body.fold benv p (Body.transactionOps d ++ Body.postOps benv d.length ommers wds)) := by
  unfold Body.importer Body.ops decodeAll
  simp only [List.append_assoc, Body.fold_append]

theorem importerAfter_eq (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
    (wds : List Withdrawal) :
    Body.importerAfter benv txs ommers wds =
      (Body.fold benv (Body.Prefix.init benv.state) (Body.preOps benv) >>= fun p =>
        decodeAll benv txs >>= fun d =>
          Body.fold benv p (Body.transactionOps d ++ Body.postOps benv d.length ommers wds)) := rfl

/-- Off the split, the new importer is the old order over the steps. -/
theorem importer_eq_importerAfter_of_not_split {benv : Benv} {txs : List (Bytes ⊕ Transaction)}
    (h : ¬ DecodeOrderSplit benv txs) (ommers : List Header) (wds : List Withdrawal) :
    Body.importer benv txs ommers wds = Body.importerAfter benv txs ommers wds := by
  rw [importer_eq, importerAfter_eq]
  rcases Except.bind_comm_or_both_error
      (Body.fold benv (Body.Prefix.init benv.state) (Body.preOps benv)) (decodeAll benv txs)
      (fun p d => Body.fold benv p (Body.transactionOps d ++ Body.postOps benv d.length ommers wds))
    with hc | ⟨ea, eb, ha, hb⟩
  · exact hc.symm
  · refine absurd ⟨?_, eb, hb⟩ h
    rw [fold_preOps_eq] at ha
    cases hp : preCalls benv with
    | error e => exact ⟨e, rfl⟩
    | ok r => rw [hp] at ha; cases ha

/-- **Difference theorem, part 1 (equality off the split).** Wherever the pre-execution system
calls succeed or the transaction list decodes, the new body is the old body, through the output
map, on the whole result. -/
theorem applyBody_eq_of_not_split {benv : Benv} {txs : List (Bytes ⊕ Transaction)}
    (h : ¬ DecodeOrderSplit benv txs) (ommers : List Header) (wds : List Withdrawal) :
    Staging.applyBody benv txs ommers wds = applyBody benv txs ommers wds := by
  rw [applyBody_eq_importerAfter, Staging.applyBody, importer_eq_importerAfter_of_not_split h]

/-- **Difference theorem, part 2 (on the split).** When the pre-execution system calls fail with
`eSys` and the decode fails with `eDec`, the old body reports `eSys` (its system calls ran first)
and the new body reports `eDec` (its decode ran first). -/
theorem applyBody_of_split {benv : Benv} {txs : List (Bytes ⊕ Transaction)}
    {eSys eDec : TransitionError} (hs : preCalls benv = .error eSys)
    (hd : decodeAll benv txs = .error eDec) (ommers : List Header) (wds : List Withdrawal) :
    applyBody benv txs ommers wds = .error eSys ∧
      Staging.applyBody benv txs ommers wds = .error eDec := by
  have hA : Body.fold benv (Body.Prefix.init benv.state) (Body.preOps benv) = .error eSys := by
    rw [fold_preOps_eq, hs]; rfl
  constructor
  · rw [applyBody_eq_importerAfter, importerAfter_eq, hA]; rfl
  · rw [Staging.applyBody, importer_eq, hd]; rfl

/-- **Difference theorem, part 3 (successes agree).** The new body succeeds with `r` exactly when
the old body does. -/
theorem applyBody_ok_iff (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
    (wds : List Withdrawal) (r : State × BlockOutput) :
    Staging.applyBody benv txs ommers wds = .ok r ↔ applyBody benv txs ommers wds = .ok r := by
  by_cases h : DecodeOrderSplit benv txs
  · obtain ⟨⟨eSys, hs⟩, eDec, hd⟩ := h
    obtain ⟨h1, h2⟩ := applyBody_of_split hs hd ommers wds
    rw [h1, h2]
    constructor <;> intro h <;> cases h
  · rw [applyBody_eq_of_not_split h]

/-- **Difference theorem, part 4 (errors agree as errors).** The new body fails exactly when the
old body does. -/
theorem applyBody_error_iff (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
    (wds : List Withdrawal) :
    (∃ e, Staging.applyBody benv txs ommers wds = .error e) ↔
      ∃ e, applyBody benv txs ommers wds = .error e := by
  by_cases h : DecodeOrderSplit benv txs
  · obtain ⟨⟨eSys, hs⟩, eDec, hd⟩ := h
    obtain ⟨h1, h2⟩ := applyBody_of_split hs hd ommers wds
    exact ⟨fun _ => ⟨eSys, h1⟩, fun _ => ⟨eDec, h2⟩⟩
  · rw [applyBody_eq_of_not_split h]

/-- **Difference theorem, part 5 (where they differ).** The two bodies differ only on the split. -/
theorem split_of_applyBody_ne {benv : Benv} {txs : List (Bytes ⊕ Transaction)}
    {ommers : List Header} {wds : List Withdrawal}
    (h : Staging.applyBody benv txs ommers wds ≠ applyBody benv txs ommers wds) :
    DecodeOrderSplit benv txs :=
  Classical.byContradiction fun hn => h (applyBody_eq_of_not_split hn ommers wds)

/-- The importer's prefix is the old body's result through the output map, for every success. -/
theorem importer_ok_iff (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
    (wds : List Withdrawal) (q : Body.Prefix) :
    Body.importer benv txs ommers wds = .ok q ↔ applyBody benv txs ommers wds = .ok q.output := by
  rw [← applyBody_ok_iff, Staging.applyBody]
  cases Body.importer benv txs ommers wds with
  | error e => constructor <;> intro h <;> cases h
  | ok q' =>
    constructor
    · intro h; cases h; rfl
    · intro h
      have : q'.output = q.output := by injection h
      rw [Body.Prefix.output_injective this]

/-! ### The difference theorem at the block transition -/

/-- The block transition, given its body. `stateTransitionCoreE` (old) and
`Staging.stateTransitionCoreE` (new) are this with `applyBody` and `Staging.applyBody`. Bridge
only. -/
def stateTransitionCoreWith {ε : Type}
    (body : Benv → List (Bytes ⊕ Transaction) → List Header → List Withdrawal →
      Except TransitionError (State × BlockOutput))
    (embed : TransitionError → ε) (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except ε Unit) : Except ε BlockChain := do
  Except.mapError embed (validateHeader f.ruleSet ch block.header)
  checkOmmers ()
  let ⟨st, bout⟩ ← Except.mapError embed
    (body (initBenv f ch block.header) block.transactions block.ommers block.withdrawals)
  Except.mapError (embed ∘ TransitionError.block) <|
    stateTransitionChecks bout block.header (getTransactionsRoot bout) st.root (getReceiptRoot bout)
      (logsBloom bout.blockLogs) (getWithdrawalsRoot bout)
      (if f.ruleSet.header.requestsHash then some (computeRequestsHash bout.requests) else none)
  Except.mapError (embed ∘ TransitionError.block) <| blockAccessListCheck f.ruleSet bout block.header
  .ok ⟨appendBlock ch.blocks block, st, ch.chainId⟩

theorem stateTransitionCoreE_eq_with {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) :
    stateTransitionCoreE embed f ch block checkOmmers =
      stateTransitionCoreWith applyBody embed f ch block checkOmmers := rfl

theorem staged_stateTransitionCoreE_eq_with {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) :
    Staging.stateTransitionCoreE embed f ch block checkOmmers =
      stateTransitionCoreWith Staging.applyBody embed f ch block checkOmmers := rfl

/-- The block's decode-order split: the header and the ommers pass, and the body's inputs are on
the split. -/
def BlockDecodeOrderSplit {ε : Type} (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except ε Unit) : Prop :=
  validateHeader f.ruleSet ch block.header = .ok () ∧ checkOmmers () = .ok () ∧
    DecodeOrderSplit (initBenv f ch block.header) block.transactions

/-- **Difference theorem at the block transition, part 1.** Off the split the new block transition
is the old one, on the whole result. -/
theorem stateTransitionCoreE_eq_of_not_split {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit)
    (h : ¬ BlockDecodeOrderSplit f ch block checkOmmers) :
    Staging.stateTransitionCoreE embed f ch block checkOmmers =
      stateTransitionCoreE embed f ch block checkOmmers := by
  rw [stateTransitionCoreE_eq_with, staged_stateTransitionCoreE_eq_with]
  unfold stateTransitionCoreWith
  cases hv : validateHeader f.ruleSet ch block.header with
  | error e => rfl
  | ok u =>
    cases ho : checkOmmers () with
    | error e => simp only [bind, Except.bind, Except.mapError, hv]
    | ok u' =>
      by_cases hs : DecodeOrderSplit (initBenv f ch block.header) block.transactions
      · exact absurd ⟨hv, ho, hs⟩ h
      · rw [applyBody_eq_of_not_split hs]

/-- **Difference theorem at the block transition, part 2.** On the split the old block transition
reports the system calls' error and the new one the decode's, both through `embed`. -/
theorem stateTransitionCoreE_of_split {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit)
    (hv : validateHeader f.ruleSet ch block.header = .ok ()) (ho : checkOmmers () = .ok ())
    {eSys eDec : TransitionError} (hs : preCalls (initBenv f ch block.header) = .error eSys)
    (hd : decodeAll (initBenv f ch block.header) block.transactions = .error eDec) :
    stateTransitionCoreE embed f ch block checkOmmers = .error (embed eSys) ∧
      Staging.stateTransitionCoreE embed f ch block checkOmmers = .error (embed eDec) := by
  obtain ⟨h1, h2⟩ := applyBody_of_split hs hd block.ommers block.withdrawals
  rw [stateTransitionCoreE_eq_with, staged_stateTransitionCoreE_eq_with]
  unfold stateTransitionCoreWith
  simp only [bind, Except.bind, Except.mapError, hv, ho, h1, h2, and_self]

/-- **Difference theorem at the block transition, part 3.** A success is the same success, and an
error is an error, in both orders. -/
theorem stateTransitionCoreE_ok_iff {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) (r : BlockChain) :
    Staging.stateTransitionCoreE embed f ch block checkOmmers = .ok r ↔
      stateTransitionCoreE embed f ch block checkOmmers = .ok r := by
  by_cases h : BlockDecodeOrderSplit f ch block checkOmmers
  · obtain ⟨hv, ho, ⟨eSys, hs⟩, eDec, hd⟩ := h
    obtain ⟨h1, h2⟩ := stateTransitionCoreE_of_split embed f ch block checkOmmers hv ho hs hd
    rw [h1, h2]
    constructor <;> intro h <;> cases h
  · rw [stateTransitionCoreE_eq_of_not_split embed f ch block checkOmmers h]

theorem stateTransitionCoreE_error_iff {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) :
    (∃ e, Staging.stateTransitionCoreE embed f ch block checkOmmers = .error e) ↔
      ∃ e, stateTransitionCoreE embed f ch block checkOmmers = .error e := by
  by_cases h : BlockDecodeOrderSplit f ch block checkOmmers
  · obtain ⟨hv, ho, ⟨eSys, hs⟩, eDec, hd⟩ := h
    obtain ⟨h1, h2⟩ := stateTransitionCoreE_of_split embed f ch block checkOmmers hv ho hs hd
    exact ⟨fun _ => ⟨_, h1⟩, fun _ => ⟨_, h2⟩⟩
  · rw [stateTransitionCoreE_eq_of_not_split embed f ch block checkOmmers h]

end Jaune.Bridge.G2a
