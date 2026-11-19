import Jaune.T8n
import Jaune.Bridge.G2a.Old.Body

/-!
# The transition tool's old drivers (goal `jaune-shape-and-names-v1`, gate G2a, old side)

`T8n.foldTransactions`, `T8n.runStateTest` and `T8n.runBlockchain` as they stood before the t8n
cut (W2 cut D), copied byte for byte from `Jaune/T8n.lean` at `ba15f397` (the G0b pattern: the
drivers are cut in place, because `T8n.run` and the guards in `T8n.lean` call them). Adapter class,
because `T8n.Outcome` lives in the transition tool's adapter. Deleted with the old side after the
gate's tag.
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

end Jaune.Bridge.G2a.Old.T8n
