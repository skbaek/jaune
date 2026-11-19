import Jaune.T8n
import Jaune.Bridge.G2a.Old.Body
import Jaune.Bridge.G2a.Body

/-!
# The transition tool's old drivers (goal `jaune-shape-and-names-v1`, gate G2a, old side)

`T8n.foldTransactions`, `T8n.runStateTest` and `T8n.runBlockchain` as they stood before the t8n
cut (W2 cut D), copied byte for byte from `Jaune/T8n.lean` at `ba15f397` (the G0b pattern: the
drivers are cut in place, because `T8n.run` and the guards in `T8n.lean` call them). Adapter class,
because `T8n.Outcome` lives in the transition tool's adapter. Deleted with the old side after the
gate's tag.

The bridges (moved here from `Jaune.Run.BodyT8n`): `runBlockchain_eq` and `runStateTest_eq` prove the
cut drivers equal to these, on every input and the whole result.
-/

namespace Jaune.Bridge.G2a.Old.T8n

open Jaune
open Jaune.T8n (TransactionParse Rejection Outcome operational T8nOmmer payT8nRewards)

/-- The reject-and-continue fold: the one piece of control flow a transition
tool needs that a block importer must not have. Every arm calls
`processTransaction` unchanged, and a rejected transaction is rolled back by
not threading its state.

A rejected transaction leaves no trace in the block: each accepted transaction
is processed at the count of transactions accepted before it, so the ones that
follow a rejection take the position it would have had, in the transactions
trie, the receipts trie and the block-level access list alike. Rejections are
still reported under their position in the input. This is the target's rule
since ethereum/execution-specs#3849 (rejected transactions are numbered out)
and #3361 (the body lists only accepted transactions). -/
def foldTransactions :
    List (Nat × TransactionParse Transaction) → Benv → BlockOutput → List Rejection → List Transaction →
    Except TransitionError (Benv × BlockOutput × List Rejection × List Transaction)
  | [], benv, bout, rej, inc => .ok ⟨benv, bout, rej, inc⟩
  | ⟨i, .error e⟩ :: rest, benv, bout, rej, inc =>
    foldTransactions rest benv bout (rej ++ [⟨i, .parse e⟩]) inc
  | ⟨i, .ok tx⟩ :: rest, benv, bout, rej, inc =>
    match processTransaction benv bout tx inc.length with
    | .ok ⟨st, bout'⟩ => foldTransactions rest (benv.withState st) bout' rej (inc ++ [tx])
    | .error err =>
      if operational err then .error err
      else foldTransactions rest benv bout (rej ++ [⟨i, .execution err⟩]) inc

/-- State-test mode: exactly one transaction, no system operations, no
withdrawals, no requests. -/
def runStateTest (benv : Benv) (txs : List (TransactionParse Transaction)) :
    Except TransitionError Outcome := do
  let selected := match txs with | [] => [] | t :: _ => [⟨0, t⟩]
  let ⟨benv, bout, rej, inc⟩ ← foldTransactions selected benv .init [] []
  .ok ⟨benv.state, bout, rej, none, inc⟩

/-- Blockchain mode: the target's `_run_blockchain_test`, step for step, each
fork-dependent step gated by the rule data that stands for the target's
`has_*` flag: the history-storage call (`sys.historyStorage`), the
beacon-roots call (`sys.beaconRoots`), the withdrawals
(`header.withdrawalsRoot`) and the request pass (`header.requestsHash`).

Block rewards (`reward`, from `resolveReward`) are paid after the transactions
and before the withdrawals, as the target pays them; they are `none` under
proof of stake, so of the runnable forks only London pays one. `ommers` is
`env.ommers`.

EIP-7928 (goal C): the two pre-execution system calls are incorporated into
the block-level access list at index 0, each transaction at its index plus one
inside `processTransaction`, and the post-execution operations -- withdrawals,
then each request call -- at the count of accepted transactions plus
one (the driver sets the index once, before withdrawals; Appendix E item 2 of
the goal, as renumbered by ethereum/execution-specs#3849). The list is built
after the requests and the item rule is applied to it; a violation is the
`blockException` of a result that still carries the list, as the target
assigns `block_output.block_access_list` before validating it. -/
def runBlockchain (benv : Benv) (txs : List (TransactionParse Transaction)) (wds : List Withdrawal)
    (reward : Option Nat := none) (ommers : List T8nOmmer := []) :
    Except TransitionError Outcome := do
  let rules := benv.stat.rules
  -- The parent hash the history-storage system transaction records. The
  -- target reads `block_hashes[-1]` and raises `IndexError` out of the whole
  -- tool when the window is empty, which is the shape every state test
  -- arrives in once the framework has declined to pass `--state-test` to an
  -- external binary. There is no reference behaviour to match on that input,
  -- so this records the zero hash and continues; on every input the target
  -- can process at all, the window is non-empty and this is its last entry.
  let lastHash := benv.stat.blockHashes.getLast?.getD 0
  let ⟨benv, bal⟩ ← if rules.systemCalls.historyStorage then do
      let ⟨stHistory, outHistory⟩ ←
        Except.mapError TransitionError.vm <|
          processUncheckedSystemTransaction benv historyStorageAddress lastHash.toBytes
      let bal := ({} : BlockAccessListBuilder).incorporateSystem rules 0 benv.state stHistory
        (historyStorageAddress :: outHistory.accountReads.toList)
        outHistory.storageReads.toList outHistory.storageWrites.toList
      pure (benv.withState stHistory, bal)
    else pure (benv, ({} : BlockAccessListBuilder))
  let ⟨benv, bal⟩ ← if rules.systemCalls.beaconRoots then do
      let ⟨stBeacon, outBeacon⟩ ←
        Except.mapError TransitionError.vm <|
          processUncheckedSystemTransaction benv beaconRootsAddress
            benv.stat.parentBeaconBlockRoot.toBytes
      let bal := bal.incorporateSystem rules 0 benv.state stBeacon
        (beaconRootsAddress :: outBeacon.accountReads.toList)
        outBeacon.storageReads.toList outBeacon.storageWrites.toList
      pure (benv.withState stBeacon, bal)
    else pure (benv, bal)
  let ⟨benv, bout, rej, inc⟩ ← foldTransactions txs.putIndex benv {BlockOutput.init with blockAccessListBuilder := bal} [] []
  let benv := match reward with
    | none => benv
    | some r => benv.withState (payT8nRewards r benv.stat.coinbase ommers benv.state)
  let postIndex := inc.length + 1
  let ⟨benv, bout⟩ := if rules.header.withdrawalsRoot then
      let ⟨stWds, bout⟩ := processWithdrawals benv bout wds
      let balWds := bout.blockAccessListBuilder.incorporateSystem rules postIndex benv.state stWds
        (wds.map Withdrawal.address) [] []
      (benv.withState stWds, {bout with blockAccessListBuilder := balWds})
    else (benv, bout)
  let requests := if rules.header.requestsHash then
      processGeneralPurposeRequestsAt postIndex benv bout
    else .ok ⟨benv.state, bout⟩
  match requests with
  | .ok ⟨st, bout'⟩ =>
    let list := match rules.blockAccessListRules with
      | none => []
      | some _ => bout'.blockAccessListBuilder.build
    let bout' := {bout' with blockAccessList := list}
    match checkBlockAccessListGasLimit rules benv.stat.blockGasLimit list with
    | .ok () => .ok ⟨st, bout', rej, none, inc⟩
    | .error (.block reason) => .ok ⟨st, bout', rej, some reason, inc⟩
    | .error err => .error err
  | .error (.block reason) =>
    -- The target raises `InvalidBlock` out of the step and builds its result
    -- from whatever the block environment and block output already hold.
    .ok ⟨benv.state, bout, rej, some reason, inc⟩
  | .error err => .error err

section

open Jaune.Staging Jaune.Bridge.G2a

/-! ### Bridges -/

@[simp] private theorem toBlockOutput_blockAccessListBuilder
    (p : Staging.Body.Prefix) : p.toBlockOutput.blockAccessListBuilder = p.accessList := rfl

theorem fold_requestOps (benv : Benv) (p : Staging.Body.Prefix) (n : Nat) :
    Staging.Body.fold benv p (Jaune.T8n.requestOps benv n) =
      (fun r => Staging.Body.Prefix.ofBlockOutput r.1 r.2) <$>
        Jaune.processGeneralPurposeRequestsAt (n + 1) (benv.withState p.state) p.toBlockOutput := by
  have h := fold_requests benv (n + 1) p []
  simp only [List.append_nil] at h
  rw [← processGeneralPurposeRequestsAt_eq]
  refine h.trans ?_
  cases Staging.processGeneralPurposeRequestsAt (n + 1) (benv.withState p.state) p.toBlockOutput <;>
    rfl

theorem foldTransactions_eq (benv : Benv) :
    ∀ (l : List (Nat × TransactionParse Transaction)) (p : Staging.Body.Prefix) (rej : List Rejection)
      (inc : List Transaction),
      Jaune.Bridge.G2a.Old.T8n.foldTransactions l (benv.withState p.state) p.toBlockOutput rej inc =
        (fun r => (benv.withState r.1.state, r.1.toBlockOutput, r.2.1, r.2.2)) <$>
          Jaune.T8n.foldTransactions benv l p rej inc
  | [], p, rej, inc => rfl
  | ⟨i, .error e⟩ :: rest, p, rej, inc => by
    simp only [Jaune.Bridge.G2a.Old.T8n.foldTransactions, Jaune.T8n.foldTransactions]
    exact foldTransactions_eq benv rest p _ inc
  | ⟨i, .ok tx⟩ :: rest, p, rej, inc => by
    simp only [Jaune.Bridge.G2a.Old.T8n.foldTransactions, Jaune.T8n.foldTransactions, Staging.Body.step, ← processTransaction_eq_b2, ← Staging.B2.Transaction.run_output]
    cases Staging.B2.Transaction.run (benv.withState p.state) p.toBlockOutput tx inc.length with
    | error err =>
      simp only [Functor.map, Except.map, bind, Except.bind]
      split
      · rfl
      · exact foldTransactions_eq benv rest p _ inc
    | ok q =>
      obtain ⟨run, b⟩ := q
      simp only [bind, Except.bind, pure, Except.pure]
      have := foldTransactions_eq benv rest (Staging.Body.Prefix.ofBlockOutput run.state b) rej (inc ++ [tx])
      simp only [Staging.Body.Prefix.state_ofBlockOutput, Staging.Body.Prefix.toBlockOutput_ofBlockOutput] at this
      exact this

theorem runStateTest_eq (benv : Benv) (txs : List (TransactionParse Transaction)) :
    Jaune.T8n.runStateTest benv txs = Jaune.Bridge.G2a.Old.T8n.runStateTest benv txs := by
  unfold Jaune.T8n.runStateTest Jaune.Bridge.G2a.Old.T8n.runStateTest
  cases txs with
  | nil => rfl
  | cons t rest =>
    have h := foldTransactions_eq benv [⟨0, t⟩] (Staging.Body.Prefix.init benv.state) [] []
    simp only [Body.Prefix.state_init, Benv.withState_self] at h
    dsimp only
    rw [show (BlockOutput.init) = (Staging.Body.Prefix.init benv.state).toBlockOutput from rfl, h]
    cases Jaune.T8n.foldTransactions benv [⟨0, t⟩] (Staging.Body.Prefix.init benv.state) [] [] <;> rfl

theorem foldTransactions_eq_withState (benv : Benv) (l : List (Nat × TransactionParse Transaction))
    (s : State) (b : BlockOutput) :
    Jaune.Bridge.G2a.Old.T8n.foldTransactions l (benv.withState s) b [] [] =
      (fun r => (benv.withState r.1.state, r.1.toBlockOutput, r.2.1, r.2.2)) <$>
        Jaune.T8n.foldTransactions benv l (Staging.Body.Prefix.ofBlockOutput s b) [] [] :=
  foldTransactions_eq benv l (Staging.Body.Prefix.ofBlockOutput s b) [] []

theorem payT8nRewards_eq (r : Nat) (coinbase : Address) (ommers : List T8nOmmer) (st : State) :
    payT8nRewards r coinbase ommers st =
      Staging.creditAll (ommers.map fun ommer => (ommer.address, (8 - ommer.delta) * r / 8))
        (st.addBal coinbase (r + ommers.length * (r / 32)).toU256) := by
  simp only [payT8nRewards, Staging.creditAll, List.foldl_map]

/-- The tail of `T8n.runBlockchain` after the pre-execution calls (copied from it, with the block
environment `benv.withState s` and the builder `bal` those calls produced) is the new driver's tail
from the corresponding prefix. -/
theorem runBlockchain_tail_eq (benv : Benv) (txs : List (TransactionParse Transaction))
    (wds : List Withdrawal) (reward : Option Nat) (ommers : List T8nOmmer) (s : State)
    (bal : BlockAccessListBuilder) :
    (do
      let ⟨benv', bout, rej, inc⟩ ← Jaune.Bridge.G2a.Old.T8n.foldTransactions txs.putIndex (benv.withState s)
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
      let ⟨p, rej, inc⟩ ← Jaune.T8n.foldTransactions benv txs.putIndex
        (Staging.Body.Prefix.ofBlockOutput s {BlockOutput.init with blockAccessListBuilder := bal}) [] []
      let p ← Staging.Body.fold benv p (Jaune.T8n.postOps benv inc.length wds reward ommers)
      let requests :=
        if benv.stat.rules.header.requestsHash then Staging.Body.fold benv p (Jaune.T8n.requestOps benv inc.length)
        else .ok p
      match requests with
      | .ok q => do
        let ⟨_, q⟩ ← Staging.Body.step benv q .buildAccessList
        match Staging.Body.step benv q .checkAccessListLimit with
        | .ok _ => .ok ⟨q.state, q.toBlockOutput, rej, none, inc⟩
        | .error (.block reason) => .ok ⟨q.state, q.toBlockOutput, rej, some reason, inc⟩
        | .error err => .error err
      | .error (.block reason) => .ok ⟨p.state, p.toBlockOutput, rej, some reason, inc⟩
      | .error err => .error err) := by
  rw [foldTransactions_eq_withState]
  cases Jaune.T8n.foldTransactions benv txs.putIndex
      (Staging.Body.Prefix.ofBlockOutput s {BlockOutput.init with blockAccessListBuilder := bal}) [] [] with
  | error e => rfl
  | ok r =>
    obtain ⟨q, rej, inc⟩ := r
    simp only [Functor.map, Except.map, bind, Except.bind]
    cases reward <;> cases hw : benv.stat.rules.header.withdrawalsRoot <;>
      cases hr : benv.stat.rules.header.requestsHash <;>
      simp only [Jaune.T8n.postOps, hw, hr, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil,
        List.cons_append, Staging.Body.fold, Staging.Body.step, payT8nRewards_eq, pure, Except.pure, fold_requestOps,
        Benv.withState_stat, Benv.withState_state, Benv.withState_withState, processWithdrawals,
        BlockOutput.withWithdrawalsTrie, Staging.Body.Prefix.toBlockOutput, Staging.Body.Prefix.ofBlockOutput,
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
    Jaune.T8n.runBlockchain benv txs wds reward ommers = Jaune.Bridge.G2a.Old.T8n.runBlockchain benv txs wds reward ommers := by
  unfold Jaune.T8n.runBlockchain Jaune.Bridge.G2a.Old.T8n.runBlockchain Jaune.T8n.preOps
  simp only [processUncheckedSystemTransaction_eq]
  cases hh : benv.stat.rules.systemCalls.historyStorage <;>
    cases hb : benv.stat.rules.systemCalls.beaconRoots <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil, fold_systemCall,
      List.singleton_append, List.cons_append, Staging.Body.fold, Body.Prefix.state_init,
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
        Benv.withState_stat, Benv.withState_state, Staging.Body.step, render,
        processUncheckedSystemTransaction_eq, Body.Prefix.state_init]
      cases Staging.processUncheckedSystemTransaction (benv.withState run.state) beaconRootsAddress
        benv.stat.parentBeaconBlockRoot.toBytes with
      | error e => rfl
      | ok run' =>
        exact (runBlockchain_tail_eq benv txs wds reward ommers run'.state _).symm

end

end Jaune.Bridge.G2a.Old.T8n
