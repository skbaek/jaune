import Jaune.Run.Settle
import Jaune.Run.SystemCall

/-!
# The body is a run of operations (goal `jaune-shape-and-names-v1`, W2 cut D)

A block body is a run: a list of operations, each a step from one prefix of the body to the next.

* `Body.Prefix` is what a body has produced so far: the state, and what `BlockOutput` carried (the
  gas counters, the transaction, receipt and withdrawal tries, the receipt keys, the logs, the
  request bytes, the block-access-list builder and the built list).
* `BodyOp` is one operation: an unchecked system call, a transaction, the withdrawals, the deposit
  requests parsed from the receipts, one checked request call, the proof-of-work rewards, building
  the block access list, and its item limit.
* `Body.step` runs one operation against the block environment (whose state is the prefix's),
  `Body.run` runs a list and keeps each operation's record (`OpRun`), and `Body.fold` runs a list
  and keeps only the prefix.
* `Body.importer` is the block importer's body (`apply_body`). It decodes the whole transaction
  list first, before the pre-execution system calls (goal §5.1 decision 14), then runs, in order,
  the beacon-roots call, the history-storage call, the transactions, the withdrawals, the deposit
  requests and the request calls, the rewards, the access-list build and its item limit, each
  gated by its rule.

The transition tool's body is its own driver over the same `Body.step`
(`T8n.runBlockchain`, `Jaune.T8n`). The transaction step is cut B2's `processTransaction` and the system calls
are cut B2's (`Jaune.Run.Settle`, `Jaune.Run.SystemCall`), which still read and write a
`BlockOutput`; the step passes the prefix through `Body.Prefix.toBlockOutput` and back.

Staged under `Jaune.Staging`; the bridges, including the difference theorem for the decode order,
are in gate G2a's bridge modules.
-/

namespace Jaune.Staging

open Jaune

/-! ### The prefix -/

/-- What a block body has produced so far: the state and `BlockOutput`'s carrier. -/
structure Body.Prefix : Type where
  state : State
  /-- Execution gas used by the block (`BlockOutput.blockGasUsed`). -/
  executionGasUsed : Nat
  /-- Amsterdam's state gas used by the block (`BlockOutput.blockStateGasUsed`). -/
  stateGasUsed : Nat
  /-- Sender-facing gas after refunds, for the receipts. -/
  cumulativeGasUsed : Nat
  blobGasUsed : Nat
  transactionsTrie : Std.TreeMap Bytes Transaction compare
  receiptsTrie : Std.TreeMap Bytes (Fin 5 × Receipt) compare
  receiptKeys : List Bytes
  /-- The block's logs (`BlockOutput.blockLogs`). -/
  logs : List Log
  withdrawalsTrie : Std.TreeMap Bytes Withdrawal compare
  requests : List Bytes
  /-- EIP-7928: the block-level access-list builder (`BlockOutput.blockAccessListBuilder`). -/
  accessList : BlockAccessListBuilder
  /-- EIP-7928: the built list (`BlockOutput.blockAccessList`). -/
  builtAccessList : BlockAccessList

namespace Body.Prefix

/-- The block output a prefix carries. -/
def toBlockOutput (p : Body.Prefix) : BlockOutput :=
  { blockGasUsed := p.executionGasUsed
    blockStateGasUsed := p.stateGasUsed
    cumulativeGasUsed := p.cumulativeGasUsed
    transactionsTrie := p.transactionsTrie
    receiptsTrie := p.receiptsTrie
    receiptKeys := p.receiptKeys
    blockLogs := p.logs
    withdrawalsTrie := p.withdrawalsTrie
    blobGasUsed := p.blobGasUsed
    requests := p.requests
    blockAccessListBuilder := p.accessList
    blockAccessList := p.builtAccessList }

/-- The prefix of a state and a block output. -/
def ofBlockOutput (state : State) (bout : BlockOutput) : Body.Prefix :=
  { state := state
    executionGasUsed := bout.blockGasUsed
    stateGasUsed := bout.blockStateGasUsed
    cumulativeGasUsed := bout.cumulativeGasUsed
    blobGasUsed := bout.blobGasUsed
    transactionsTrie := bout.transactionsTrie
    receiptsTrie := bout.receiptsTrie
    receiptKeys := bout.receiptKeys
    logs := bout.blockLogs
    withdrawalsTrie := bout.withdrawalsTrie
    requests := bout.requests
    accessList := bout.blockAccessListBuilder
    builtAccessList := bout.blockAccessList }

/-- The empty prefix over a state. -/
def init (state : State) : Body.Prefix := ofBlockOutput state BlockOutput.init

/-- The body's result as the importer returned it: the state and the block output. -/
def output (p : Body.Prefix) : State × BlockOutput := (p.state, p.toBlockOutput)

@[simp] theorem toBlockOutput_ofBlockOutput (state : State) (bout : BlockOutput) :
    (ofBlockOutput state bout).toBlockOutput = bout := rfl

@[simp] theorem state_ofBlockOutput (state : State) (bout : BlockOutput) :
    (ofBlockOutput state bout).state = state := rfl

@[simp] theorem ofBlockOutput_toBlockOutput (p : Body.Prefix) :
    ofBlockOutput p.state p.toBlockOutput = p := rfl

theorem output_injective : Function.Injective output := by
  intro p q h
  have h1 : p.state = q.state := congrArg Prod.fst h
  have h2 : p.toBlockOutput = q.toBlockOutput := congrArg Prod.snd h
  rw [← ofBlockOutput_toBlockOutput p, ← ofBlockOutput_toBlockOutput q, h1, h2]

end Body.Prefix

/-! ### Operations -/

/-- One operation of a block body. -/
inductive BodyOp : Type where
  /-- An unchecked system call to `address` with `data` (whose failure fails the body before the
  call), incorporated into the block access list at `index`. -/
  | systemCall (address : Address) (data : Except TransitionError Bytes) (index : Nat)
  /-- A transaction at `index`. -/
  | transaction (tx : Transaction) (index : Nat)
  /-- The withdrawals, incorporated into the block access list at `index`. -/
  | withdrawals (ws : List Withdrawal) (index : Nat)
  /-- The deposit requests parsed from the receipts so far (EIP-6110). -/
  | depositRequests
  /-- A checked request call of request type `type` to `address`, incorporated at `index`. -/
  | requestCall (type : UInt8) (address : Address) (index : Nat)
  /-- Proof-of-work rewards: `minerReward` to `coinbase`, then each credit in turn. -/
  | rewards (coinbase : Address) (minerReward : Nat) (credits : List (Address × Nat))
  /-- Build the block access list from the builder. -/
  | buildAccessList
  /-- The block access list's item limit (`validate_block_access_list_gas_limit`). -/
  | checkAccessListLimit

/-- What one operation produced, beside the next prefix. -/
inductive OpRun : Type where
  | systemCall (index : Nat) (address : Address) (run : MessageRun)
  | transaction (run : B2.TransactionRun)
  | withdrawals (index : Nat) (ws : List Withdrawal)
  | depositRequests (requests : Bytes)
  | requestCall (index : Nat) (type : UInt8) (address : Address) (run : MessageRun)
  | rewards (coinbase : Address) (minerReward : Nat) (credits : List (Address × Nat))
  | buildAccessList (list : BlockAccessList)
  | checkAccessListLimit

/-- Credit each `(address, amount)` in turn (`create_ether`). -/
def creditAll (credits : List (Address × Nat)) (state : State) : State :=
  credits.foldl (fun acc c => acc.addBal c.1 c.2.toU256) state

/-- One operation from a prefix, against the block environment `benv` (whose own state the step
does not read: the prefix's state stands in for it). -/
def Body.step (benv : Benv) (p : Body.Prefix) : BodyOp → Except TransitionError (OpRun × Body.Prefix)
  | .systemCall address data index => do
    let data ← data
    let run ← (processUncheckedSystemTransaction (benv.withState p.state) address data).mapError
      (fun e => TransitionError.vm e.toEvmError)
    pure (.systemCall index address run,
      { p with
        state := run.state
        accessList := p.accessList.incorporateSystem benv.stat.rules index p.state run.state
          (address :: run.accountReads.toList) run.storageReads.toList run.storageWrites.toList })
  | .transaction tx index => do
    let ⟨run, bout⟩ ← B2.Transaction.run (benv.withState p.state) p.toBlockOutput tx index
    pure (.transaction run, Body.Prefix.ofBlockOutput run.state bout)
  | .withdrawals ws index =>
    let state := processWithdrawalsState p.state ws
    pure (.withdrawals index ws,
      { p with
        state := state
        withdrawalsTrie := processWithdrawalsTrie p.withdrawalsTrie ws
        accessList := p.accessList.incorporateSystem benv.stat.rules index p.state state
          (ws.map Withdrawal.address) [] [] })
  | .depositRequests => do
    let deposits ← parseDepositRequests p.toBlockOutput
    pure (.depositRequests deposits,
      { p with
        requests :=
          if deposits.length > 0 then p.requests ++ [depositRequestType ++ deposits]
          else p.requests })
  | .requestCall type address index => do
    let run ← processCheckedSystemTransaction (benv.withState p.state) address []
    pure (.requestCall index type address run,
      { p with
        state := run.state
        requests :=
          if run.returnData.length > 0 then p.requests ++ [[type] ++ run.returnData]
          else p.requests
        accessList := match benv.stat.rules.blockAccessListRules with
          | none => p.accessList
          | some _ => p.accessList.incorporate index p.state run.state
              (address :: run.accountReads.toList) run.storageReads.toList
              run.storageWrites.toList })
  | .rewards coinbase minerReward credits =>
    pure (.rewards coinbase minerReward credits,
      { p with state := creditAll credits (p.state.addBal coinbase minerReward.toU256) })
  | .buildAccessList =>
    let list := match benv.stat.rules.blockAccessListRules with
      | none => []
      | some _ => p.accessList.build
    pure (.buildAccessList list, { p with builtAccessList := list })
  | .checkAccessListLimit => do
    checkBlockAccessListGasLimit benv.stat.rules benv.stat.blockGasLimit p.builtAccessList
    pure (.checkAccessListLimit, p)

/-- A list of operations, keeping each operation's record. -/
def Body.run (benv : Benv) : Body.Prefix → List BodyOp →
    Except TransitionError (List OpRun × Body.Prefix)
  | p, [] => pure ([], p)
  | p, op :: ops => do
    let ⟨r, q⟩ ← Body.step benv p op
    let ⟨rs, q'⟩ ← Body.run benv q ops
    pure (r :: rs, q')

/-- A list of operations, keeping only the prefix: the runner. -/
def Body.fold (benv : Benv) : Body.Prefix → List BodyOp → Except TransitionError Body.Prefix
  | p, [] => pure p
  | p, op :: ops => do
    let ⟨_, q⟩ ← Body.step benv p op
    Body.fold benv q ops

/-! ### The importer's operations -/

/-- The importer's pre-execution system calls at index 0: the beacon-roots call (EIP-4788) when
`sys.beaconRoots`, then the history-storage call (EIP-2935) when `sys.historyStorage`, whose data
is the parent hash (an empty window is an internal fault). -/
def Body.preOps (benv : Benv) : List BodyOp :=
  let rules := benv.stat.rules
  (if rules.systemCalls.beaconRoots then
    [.systemCall beaconRootsAddress (.ok benv.stat.parentBeaconBlockRoot.toBytes) 0]
  else []) ++
  (if rules.systemCalls.historyStorage then
    [.systemCall historyStorageAddress
      ((benv.stat.blockHashes.getLast?.toExcept
        (TransitionError.internal (.invariant (.text "block hashes is empty")))).map
          (·.toBytes)) 0]
  else [])

/-- The transactions, each at its position. -/
def Body.transactionOps (txs : List Transaction) : List BodyOp :=
  txs.putIndex.map fun ⟨i, tx⟩ => .transaction tx i

/-- The importer's post-execution operations, for `n` transactions: the withdrawals at `n + 1`
when `header.withdrawalsRoot`; the deposit requests and each request call at `n + 1` when
`header.requestsHash`; the rewards under proof of work (`payRewards`' amounts); then the
access-list build and its item limit. -/
def Body.postOps (benv : Benv) (n : Nat) (ommers : List Header) (wds : List Withdrawal) :
    List BodyOp :=
  let rules := benv.stat.rules
  (if rules.header.withdrawalsRoot then [.withdrawals wds (n + 1)] else []) ++
  (if rules.header.requestsHash then
    .depositRequests :: rules.requests.map fun ⟨type, address⟩ => .requestCall type address (n + 1)
  else []) ++
  (match rules.proofOfWork with
    | none => []
    | some pow =>
      [.rewards benv.stat.coinbase (pow.blockReward + ommers.length * (pow.blockReward / 32))
        (ommers.map fun ommer =>
          (ommer.coinbase, (8 + ommer.number - benv.stat.number) * pow.blockReward / 8))]) ++
  [.buildAccessList, .checkAccessListLimit]

/-- The importer's operations for the decoded transactions. -/
def Body.ops (benv : Benv) (txs : List Transaction) (ommers : List Header)
    (wds : List Withdrawal) : List BodyOp :=
  Body.preOps benv ++ Body.transactionOps txs ++ Body.postOps benv txs.length ommers wds

/-- **The importer's body** (`apply_body`): decode the whole transaction list, then run the
operations from the empty prefix over the block's pre-state. -/
def Body.importer (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
    (wds : List Withdrawal) : Except TransitionError Body.Prefix := do
  let decoded ← txs.mapM (decodeTransaction benv.stat.rules)
  Body.fold benv (Body.Prefix.init benv.state) (Body.ops benv decoded ommers wds)

/-- The importer's body with `applyBody`'s result type: the prefix through `Body.Prefix.output`. -/
def applyBody (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
    (wds : List Withdrawal) : Except TransitionError (State × BlockOutput) :=
  Body.Prefix.output <$> Body.importer benv txs ommers wds

/-! ### The block transition over the new body -/

/-- `stateTransitionCoreE` with the importer's body in place of `applyBody`: header validation,
the ommer check, the body, then the commitment checks and the access-list check, as before. Cut E
restructures this into the block run; here only the body changed. -/
def stateTransitionCoreE {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except ε Unit) : Except ε BlockChain := do
  let rules := f.ruleSet
  Except.mapError embed (validateHeader rules ch block.header)
  checkOmmers ()
  let benv : Benv := initBlockEnvironment f ch block.header
  let ⟨st, bout⟩ ← Except.mapError embed
    (applyBody benv block.transactions block.ommers block.withdrawals)
  let blockStateRoot : U256 := st.root
  let transactionsRoot : U256 := getTransactionsRoot bout
  let receiptRoot : U256 := getReceiptRoot bout
  let blockLogsBloom : Bytes := logsBloom bout.blockLogs
  let withdrawalsRoot : U256 := getWithdrawalsRoot bout
  let requestsHash :=
    if rules.header.requestsHash then some (computeRequestsHash bout.requests) else none
  Except.mapError (embed ∘ TransitionError.block) <|
    stateTransitionChecks bout block.header
      transactionsRoot blockStateRoot receiptRoot
      blockLogsBloom withdrawalsRoot requestsHash
  Except.mapError (embed ∘ TransitionError.block) <|
    blockAccessListCheck rules bout block.header
  .ok ⟨appendBlock ch.blocks block, st, ch.chainId⟩

end Jaune.Staging
