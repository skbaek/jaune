import Jaune.Bridge.G2a.Old.T8n
import Jaune.T8n
import Jaune.Bridge.G2a.Body

/-!
# The transition tool's body over the body steps (goal `jaune-shape-and-names-v1`, W2 cut D)

The transition tool (`t8n`) runs a body its own way, over the same `Body.step` as the importer
(`Jaune.Run.Body`), with every guard of `T8n.runBlockchain` (W2 design revision 3, §3.3-t8n):

1. the history-storage call when `sys.historyStorage`, with the last window hash or zero; then the
   beacon-roots call when `sys.beaconRoots`. This is t8n's own order, history before beacon, kept
   as it is (the importer runs beacon first);
2. the tolerant transaction loop (`foldTransactions`): a transaction that does not parse, or that
   `processTransaction` rejects with a non-operational error, is recorded and its prefix dropped,
   and each accepted transaction runs at the count accepted before it;
3. the rewards when a reward is resolved (`payT8nRewards`' amounts), then the withdrawals when
   `header.withdrawalsRoot`, at the accepted count plus one;
4. when `header.requestsHash`, the deposit requests and the request calls as one group: a block
   rejection returns the prefix at the group's start with the rejection;
5. the access-list build, then its item limit: a block rejection returns the built prefix with the
   rejection; any other error propagates.

Staged under `Jaune.Staging.T8n`; `runBlockchain_eq` and `runStateTest_eq` prove these equal to
`T8n.runBlockchain` and `T8n.runStateTest`, on every input and the whole result. Adapter class,
because `T8n.Outcome` lives in the transition tool's adapter.
-/

namespace Jaune.Staging.T8n

open Jaune Jaune.Staging Jaune.T8n Jaune.Bridge.G2a

/-- The reject-and-continue transaction loop over the transaction step. -/
def foldTransactions (benv : Benv) :
    List (Nat × TransactionParse Transaction) → Body.Prefix → List Rejection → List Transaction →
      Except TransitionError (Body.Prefix × List Rejection × List Transaction)
  | [], p, rej, inc => .ok ⟨p, rej, inc⟩
  | ⟨i, .error e⟩ :: rest, p, rej, inc =>
    foldTransactions benv rest p (rej ++ [⟨i, .parse e⟩]) inc
  | ⟨i, .ok tx⟩ :: rest, p, rej, inc =>
    match Body.step benv p (.transaction tx inc.length) with
    | .ok ⟨_, q⟩ => foldTransactions benv rest q rej (inc ++ [tx])
    | .error err =>
      if operational err then .error err
      else foldTransactions benv rest p (rej ++ [⟨i, .execution err⟩]) inc

/-- State-test mode: exactly one transaction from the empty prefix, nothing else. -/
def runStateTest (benv : Benv) (txs : List (TransactionParse Transaction)) :
    Except TransitionError Outcome := do
  let selected := match txs with | [] => [] | t :: _ => [⟨0, t⟩]
  let ⟨p, rej, inc⟩ ← foldTransactions benv selected (Body.Prefix.init benv.state) [] []
  .ok ⟨p.state, p.toBlockOutput, rej, none, inc⟩

/-- t8n's pre-execution system calls, in its order: history storage (with the last window hash,
or zero for an empty window), then beacon roots. -/
def preOps (benv : Benv) : List BodyOp :=
  (if benv.stat.rules.systemCalls.historyStorage then
    [.systemCall historyStorageAddress (.ok (benv.stat.blockHashes.getLast?.getD 0).toBytes) 0]
  else []) ++
  (if benv.stat.rules.systemCalls.beaconRoots then
    [.systemCall beaconRootsAddress (.ok benv.stat.parentBeaconBlockRoot.toBytes) 0]
  else [])

/-- The rewards (when resolved), then the withdrawals at the accepted count plus one. -/
def postOps (benv : Benv) (accepted : Nat) (wds : List Withdrawal) (reward : Option Nat)
    (ommers : List T8nOmmer) : List BodyOp :=
  (match reward with
    | none => []
    | some r =>
      [.rewards benv.stat.coinbase (r + ommers.length * (r / 32))
        (ommers.map fun ommer => (ommer.address, (8 - ommer.delta) * r / 8))]) ++
  (if benv.stat.rules.header.withdrawalsRoot then [.withdrawals wds (accepted + 1)] else [])

/-- The request group at the accepted count plus one. -/
def requestOps (benv : Benv) (accepted : Nat) : List BodyOp :=
  .depositRequests :: benv.stat.rules.requests.map fun ⟨type, address⟩ =>
    .requestCall type address (accepted + 1)

/-- **The transition tool's body** in blockchain mode. -/
def runBlockchain (benv : Benv) (txs : List (TransactionParse Transaction))
    (wds : List Withdrawal) (reward : Option Nat := none) (ommers : List T8nOmmer := []) :
    Except TransitionError Outcome := do
  let p ← Body.fold benv (Body.Prefix.init benv.state) (preOps benv)
  let ⟨p, rej, inc⟩ ← foldTransactions benv txs.putIndex p [] []
  let p ← Body.fold benv p (postOps benv inc.length wds reward ommers)
  let requests :=
    if benv.stat.rules.header.requestsHash then Body.fold benv p (requestOps benv inc.length)
    else .ok p
  match requests with
  | .ok q => do
    let ⟨_, q⟩ ← Body.step benv q .buildAccessList
    match Body.step benv q .checkAccessListLimit with
    | .ok _ => .ok ⟨q.state, q.toBlockOutput, rej, none, inc⟩
    | .error (.block reason) => .ok ⟨q.state, q.toBlockOutput, rej, some reason, inc⟩
    | .error err => .error err
  | .error (.block reason) => .ok ⟨p.state, p.toBlockOutput, rej, some reason, inc⟩
  | .error err => .error err

/-! ### Bridges -/

@[simp] theorem _root_.Jaune.Staging.Body.Prefix.toBlockOutput_blockAccessListBuilder
    (p : Body.Prefix) : p.toBlockOutput.blockAccessListBuilder = p.accessList := rfl

theorem fold_requestOps (benv : Benv) (p : Body.Prefix) (n : Nat) :
    Body.fold benv p (requestOps benv n) =
      (fun r => Body.Prefix.ofBlockOutput r.1 r.2) <$>
        Jaune.processGeneralPurposeRequestsAt (n + 1) (benv.withState p.state) p.toBlockOutput := by
  have h := fold_requests benv (n + 1) p []
  simp only [List.append_nil] at h
  rw [← processGeneralPurposeRequestsAt_eq]
  refine h.trans ?_
  cases Staging.processGeneralPurposeRequestsAt (n + 1) (benv.withState p.state) p.toBlockOutput <;>
    rfl

theorem foldTransactions_eq (benv : Benv) :
    ∀ (l : List (Nat × TransactionParse Transaction)) (p : Body.Prefix) (rej : List Rejection)
      (inc : List Transaction),
      Jaune.T8n.foldTransactions l (benv.withState p.state) p.toBlockOutput rej inc =
        (fun r => (benv.withState r.1.state, r.1.toBlockOutput, r.2.1, r.2.2)) <$>
          foldTransactions benv l p rej inc
  | [], p, rej, inc => rfl
  | ⟨i, .error e⟩ :: rest, p, rej, inc => by
    simp only [Jaune.T8n.foldTransactions, foldTransactions]
    exact foldTransactions_eq benv rest p _ inc
  | ⟨i, .ok tx⟩ :: rest, p, rej, inc => by
    simp only [Jaune.T8n.foldTransactions, foldTransactions, Body.step, ← processTransaction_eq_b2, ← B2.Transaction.run_output]
    cases B2.Transaction.run (benv.withState p.state) p.toBlockOutput tx inc.length with
    | error err =>
      simp only [Functor.map, Except.map, bind, Except.bind]
      split
      · rfl
      · exact foldTransactions_eq benv rest p _ inc
    | ok q =>
      obtain ⟨run, b⟩ := q
      simp only [bind, Except.bind, pure, Except.pure]
      have := foldTransactions_eq benv rest (Body.Prefix.ofBlockOutput run.state b) rej (inc ++ [tx])
      simp only [Body.Prefix.state_ofBlockOutput, Body.Prefix.toBlockOutput_ofBlockOutput] at this
      exact this

theorem runStateTest_eq (benv : Benv) (txs : List (TransactionParse Transaction)) :
    runStateTest benv txs = Jaune.T8n.runStateTest benv txs := by
  unfold runStateTest Jaune.T8n.runStateTest
  cases txs with
  | nil => rfl
  | cons t rest =>
    have h := foldTransactions_eq benv [⟨0, t⟩] (Body.Prefix.init benv.state) [] []
    simp only [Body.Prefix.state_init, Benv.withState_self] at h
    dsimp only
    rw [show (BlockOutput.init) = (Body.Prefix.init benv.state).toBlockOutput from rfl, h]
    cases foldTransactions benv [⟨0, t⟩] (Body.Prefix.init benv.state) [] [] <;> rfl

theorem foldTransactions_eq_withState (benv : Benv) (l : List (Nat × TransactionParse Transaction))
    (s : State) (b : BlockOutput) :
    Jaune.T8n.foldTransactions l (benv.withState s) b [] [] =
      (fun r => (benv.withState r.1.state, r.1.toBlockOutput, r.2.1, r.2.2)) <$>
        foldTransactions benv l (Body.Prefix.ofBlockOutput s b) [] [] :=
  foldTransactions_eq benv l (Body.Prefix.ofBlockOutput s b) [] []

theorem payT8nRewards_eq (r : Nat) (coinbase : Address) (ommers : List T8nOmmer) (st : State) :
    payT8nRewards r coinbase ommers st =
      creditAll (ommers.map fun ommer => (ommer.address, (8 - ommer.delta) * r / 8))
        (st.addBal coinbase (r + ommers.length * (r / 32)).toU256) := by
  simp only [payT8nRewards, creditAll, List.foldl_map]

/-- The tail of `T8n.runBlockchain` after the pre-execution calls (copied from it, with the block
environment `benv.withState s` and the builder `bal` those calls produced) is the new driver's tail
from the corresponding prefix. -/
theorem runBlockchain_tail_eq (benv : Benv) (txs : List (TransactionParse Transaction))
    (wds : List Withdrawal) (reward : Option Nat) (ommers : List T8nOmmer) (s : State)
    (bal : BlockAccessListBuilder) :
    (do
      let ⟨benv', bout, rej, inc⟩ ← Jaune.T8n.foldTransactions txs.putIndex (benv.withState s)
        {BlockOutput.init with blockAccessListBuilder := bal} [] []
      let benv' := match reward with
        | none => benv'
        | some r => benv'.withState (payT8nRewards r benv'.stat.coinbase ommers benv'.state)
      let postIndex := inc.length + 1
      let ⟨benv', bout⟩ := if benv.stat.rules.header.withdrawalsRoot then
          let ⟨stWds, bout⟩ := processWithdrawals benv' bout wds
          let balWds := bout.blockAccessListBuilder.incorporateSystem benv.stat.rules postIndex
            benv'.state stWds (wds.map Withdrawal.address) [] []
          (benv'.withState stWds, {bout with blockAccessListBuilder := balWds})
        else (benv', bout)
      let requests := if benv.stat.rules.header.requestsHash then
          Jaune.processGeneralPurposeRequestsAt postIndex benv' bout
        else .ok ⟨benv'.state, bout⟩
      match requests with
      | .ok ⟨st, bout'⟩ =>
        let list := match benv.stat.rules.blockAccessListRules with
          | none => []
          | some _ => bout'.blockAccessListBuilder.build
        let bout' := {bout' with blockAccessList := list}
        match checkBlockAccessListGasLimit benv.stat.rules benv'.stat.blockGasLimit list with
        | .ok () => .ok ⟨st, bout', rej, none, inc⟩
        | .error (.block reason) => .ok ⟨st, bout', rej, some reason, inc⟩
        | .error err => .error err
      | .error (.block reason) => .ok ⟨benv'.state, bout, rej, some reason, inc⟩
      | .error err => .error err : Except TransitionError Outcome) =
    (do
      let ⟨p, rej, inc⟩ ← foldTransactions benv txs.putIndex
        (Body.Prefix.ofBlockOutput s {BlockOutput.init with blockAccessListBuilder := bal}) [] []
      let p ← Body.fold benv p (postOps benv inc.length wds reward ommers)
      let requests :=
        if benv.stat.rules.header.requestsHash then Body.fold benv p (requestOps benv inc.length)
        else .ok p
      match requests with
      | .ok q => do
        let ⟨_, q⟩ ← Body.step benv q .buildAccessList
        match Body.step benv q .checkAccessListLimit with
        | .ok _ => .ok ⟨q.state, q.toBlockOutput, rej, none, inc⟩
        | .error (.block reason) => .ok ⟨q.state, q.toBlockOutput, rej, some reason, inc⟩
        | .error err => .error err
      | .error (.block reason) => .ok ⟨p.state, p.toBlockOutput, rej, some reason, inc⟩
      | .error err => .error err) := by
  rw [foldTransactions_eq_withState]
  cases foldTransactions benv txs.putIndex
      (Body.Prefix.ofBlockOutput s {BlockOutput.init with blockAccessListBuilder := bal}) [] [] with
  | error e => rfl
  | ok r =>
    obtain ⟨q, rej, inc⟩ := r
    simp only [Functor.map, Except.map, bind, Except.bind]
    cases reward <;> cases hw : benv.stat.rules.header.withdrawalsRoot <;>
      cases hr : benv.stat.rules.header.requestsHash <;>
      simp only [postOps, hw, hr, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil,
        List.cons_append, Body.fold, Body.step, payT8nRewards_eq, pure, Except.pure, fold_requestOps,
        Benv.withState_stat, Benv.withState_state, Benv.withState_withState, processWithdrawals,
        BlockOutput.withWithdrawalsTrie, Body.Prefix.toBlockOutput, Body.Prefix.ofBlockOutput,
        Functor.map, Except.map]
    all_goals
      rcases benv.stat.rules.blockAccessListRules with _ | v <;> simp only [bind, Except.bind]
    all_goals
      repeat
        first
        | rfl
        | (split <;> rename_i heq <;> rw [heq] <;> try simp only [])
        | (rename_i _ err hne; cases err <;> first | rfl | exact absurd rfl (hne _))

/-- **The t8n bridge.** The transition tool's body over the body steps is `T8n.runBlockchain`, on
every input and the whole result: t8n's order (history before beacon) is unchanged, so the bridge
is equality. -/
theorem runBlockchain_eq (benv : Benv) (txs : List (TransactionParse Transaction))
    (wds : List Withdrawal) (reward : Option Nat) (ommers : List T8nOmmer) :
    runBlockchain benv txs wds reward ommers = Jaune.T8n.runBlockchain benv txs wds reward ommers := by
  unfold runBlockchain Jaune.T8n.runBlockchain preOps
  simp only [processUncheckedSystemTransaction_eq]
  cases hh : benv.stat.rules.systemCalls.historyStorage <;>
    cases hb : benv.stat.rules.systemCalls.beaconRoots <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil, fold_systemCall,
      List.singleton_append, List.cons_append, Body.fold, Body.Prefix.state_init,
      Benv.withState_self]
  · exact (runBlockchain_tail_eq benv txs wds reward ommers benv.state {}).symm
  · simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Except.mapError,
      Benv.withState_stat, Benv.withState_state]
    cases Staging.processUncheckedSystemTransaction benv beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toBytes with
    | error e => rfl
    | ok run =>
      exact (runBlockchain_tail_eq benv txs wds reward ommers run.state _).symm
  · simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Except.mapError,
      Benv.withState_stat, Benv.withState_state]
    cases Staging.processUncheckedSystemTransaction benv historyStorageAddress
      (benv.stat.blockHashes.getLast?.getD 0).toBytes with
    | error e => rfl
    | ok run =>
      exact (runBlockchain_tail_eq benv txs wds reward ommers run.state _).symm
  · simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Except.mapError,
      Benv.withState_stat, Benv.withState_state]
    cases Staging.processUncheckedSystemTransaction benv historyStorageAddress
      (benv.stat.blockHashes.getLast?.getD 0).toBytes with
    | error e => rfl
    | ok run =>
      simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Except.mapError,
        Benv.withState_stat, Benv.withState_state, Body.step, render,
        processUncheckedSystemTransaction_eq, Body.Prefix.state_init]
      cases Staging.processUncheckedSystemTransaction (benv.withState run.state) beaconRootsAddress
        benv.stat.parentBeaconBlockRoot.toBytes with
      | error e => rfl
      | ok run' =>
        exact (runBlockchain_tail_eq benv txs wds reward ommers run'.state _).symm

end Jaune.Staging.T8n
