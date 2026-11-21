import Jaune.Run.Transaction

section
open Jaune
namespace Jaune
/-- Request-producing calls require code and a successful settlement. -/
def processCheckedSystemRun (block : BlockContext) (state : State)
    (target : Address) (data : Bytes) : Except TransitionError SystemRun := do
  let code := state.getCode target
  if code.isEmpty then
    .error <| .block <| .systemContractEmpty <| .text
      s!"system contract address {target.toHex} holds no code"
  let run ← (processSystemRun block state target code data).mapError
    (fun fault => TransitionError.vm fault.toEvmError)
  match run.settlement.error with
  | some halt => .error <| .block <| .systemContractCallFailed target halt
  | none => .ok run
end Jaune
end

section
open Jaune
namespace Jaune
def processCheckedSystemTransaction (block : BlockContext) (state : State)
    (target : Address) (data : Bytes) : Except TransitionError TopLevel.Settlement :=
  (processCheckedSystemRun block state target data).map SystemRun.settlement
end Jaune
end

section
open Jaune
namespace Jaune
/-- What one accepted operation records, beside its next prefix. -/
inductive BodyOperationRun where
  | systemCall (index : Nat) (address : Address) (run : SystemRun)
  | transaction (run : TransactionRun)
  | withdrawals (index : Nat) (ws : List Withdrawal)
  | depositRequests (requests : Bytes)
  | requestCall (index : Nat) (type : UInt8) (address : Address) (run : SystemRun)
  | rewards (coinbase : Address) (minerReward : Nat) (credits : List (Address × Nat))
  | buildAccessList (list : BlockAccessList)
  | checkAccessListLimit
end Jaune
end

section
open Jaune
namespace Jaune.Body
/-- Execute one operation from the prefix state, in the block `block`. The streaming runner
discards the operation record, while the recording runner keeps it. -/
@[inline] def stepWith {α : Type} (observe : BodyOperationRun → Jaune.Body.Prefix → α)
    (block : BlockContext) (p : Jaune.Body.Prefix) : BodyOperation → Except TransitionError α
  | .systemCall address data index => do
    let data ← data
    let message ← (processSystemRun block p.state address (p.state.getCode address) data).mapError
      (fun fault => TransitionError.vm fault.toEvmError)
    let run := message.settlement
    pure <| observe (.systemCall index address message) { p with
      state := run.state
      blockAccessListBuilder := p.blockAccessListBuilder.incorporateSystem block.rules index p.state run.state
        (address :: run.accountReads.toList) run.storageReads.toList run.storageWrites.toList }
  | .transaction tx index => do
    let (run, bout) ← Transaction.run block p.state p.toBlockOutput tx index
    pure <| observe (.transaction run) (Jaune.Body.Prefix.ofBlockOutput run.state bout)
  | .withdrawals ws index =>
    let state := processWithdrawalsState p.state ws
    pure <| observe (.withdrawals index ws) { p with
      state
      withdrawalsTrie := processWithdrawalsTrie p.withdrawalsTrie ws
      blockAccessListBuilder := p.blockAccessListBuilder.incorporateSystem block.rules index p.state state
        (ws.map Withdrawal.address) [] [] }
  | .depositRequests => do
    let deposits ← parseDepositRequests p.toBlockOutput
    pure <| observe (.depositRequests deposits) { p with
      requests := if deposits.length > 0 then p.requests ++ [depositRequestType ++ deposits] else p.requests }
  | .requestCall type address index => do
    let message ← processCheckedSystemRun block p.state address []
    let run := message.settlement
    pure <| observe (.requestCall index type address message) { p with
      state := run.state
      requests := if run.returnData.length > 0 then p.requests ++ [[type] ++ run.returnData] else p.requests
      blockAccessListBuilder := match block.rules.blockAccessListRules with
        | none => p.blockAccessListBuilder
        | some _ => p.blockAccessListBuilder.incorporate index p.state run.state
            (address :: run.accountReads.toList) run.storageReads.toList run.storageWrites.toList }
  | .rewards coinbase minerReward credits =>
    pure <| observe (.rewards coinbase minerReward credits)
      { p with state := creditAll credits (p.state.addBalance coinbase minerReward.toU256) }
  | .buildAccessList =>
    let list := match block.rules.blockAccessListRules with
      | none => []
      | some _ => p.blockAccessListBuilder.build
    pure <| observe (.buildAccessList list) { p with blockAccessList := list }
  | .checkAccessListLimit => do
    checkBlockAccessListGasLimit block.rules block.gasLimit p.blockAccessList
    pure (observe .checkAccessListLimit p)
end Jaune.Body
end

section
open Jaune
namespace Jaune.Body
/-- The streaming step holds only the next prefix. -/
def step (block : BlockContext) (p : Jaune.Body.Prefix) (op : BodyOperation) :
    Except TransitionError Jaune.Body.Prefix :=
  stepWith (fun _ next => next) block p op
end Jaune.Body
end

section
open Jaune
namespace Jaune.Body
/-- Keep the record of the same operation executed by the streaming step. -/
def stepRun (block : BlockContext) (p : Jaune.Body.Prefix) (op : BodyOperation) :
    Except TransitionError (BodyOperationRun × Jaune.Body.Prefix) :=
  stepWith Prod.mk block p op
end Jaune.Body
end

section
open Jaune
namespace Jaune.Body
theorem stepRun_prefix (block : BlockContext) (p : Jaune.Body.Prefix) (op : BodyOperation) :
    (stepRun block p op).map Prod.snd = step block p op := by
  cases op <;> simp only [stepRun, step, stepWith]
  case systemCall address data index =>
    cases data with
    | error => rfl
    | ok bytes =>
      simp only [bind, Except.bind]
      cases processSystemRun block p.state address (p.state.getCode address) bytes <;> rfl
  case transaction tx index =>
    cases Transaction.run block p.state p.toBlockOutput tx index <;> rfl
  case depositRequests => cases parseDepositRequests p.toBlockOutput <;> rfl
  case requestCall type address index =>
    cases processCheckedSystemRun block p.state address [] <;> rfl
  case checkAccessListLimit =>
    cases checkBlockAccessListGasLimit block.rules block.gasLimit p.blockAccessList <;> rfl
  all_goals rfl
end Jaune.Body
end

section
open Jaune
namespace Jaune.Body
/-- The executed operations in order, together with their final prefix. -/
def run (block : BlockContext) : Jaune.Body.Prefix → List BodyOperation →
    Except TransitionError (List BodyOperationRun × Jaune.Body.Prefix)
  | p, [] => .ok ([], p)
  | p, op :: ops => do
    let (record, next) ← stepRun block p op
    let (records, final) ← run block next ops
    pure (record :: records, final)
end Jaune.Body
end

section
open Jaune
namespace Jaune.Body
/-- The importer's pre-execution system calls at index 0: the beacon-roots call (EIP-4788) when
`systemCalls.beaconRoots`, then the history-storage call (EIP-2935) when
`systemCalls.historyStorage`, whose data is the parent hash (an empty window is an internal
fault). -/
def preExecutionOperations (block : BlockContext) : List BodyOperation :=
  let rules := block.rules
  (if rules.systemCalls.beaconRoots then
    [.systemCall beaconRootsAddress (.ok block.parentBeaconBlockRoot.toBytes) 0]
  else []) ++
  (if rules.systemCalls.historyStorage then
    [.systemCall historyStorageAddress
      ((block.blockHashes.getLast?.toExcept
        (TransitionError.internal (.invariant (.text "block hashes is empty")))).map
          (·.toBytes)) 0]
  else [])
end Jaune.Body
end

section
open Jaune
namespace Jaune.Body
/-- The withdrawals at `index`, when the header commits to them. -/
def withdrawalOperations (block : BlockContext) (index : Nat) (withdrawals : List Withdrawal) : List BodyOperation :=
  if block.rules.header.withdrawalsRoot then [.withdrawals withdrawals index] else []
end Jaune.Body
end

section
open Jaune
namespace Jaune.Body
/-- Deposit requests follow the receipts, followed by configured request-producing calls. -/
def requestOperations (block : BlockContext) (index : Nat) : List BodyOperation :=
  if block.rules.header.requestsHash then
    .depositRequests :: block.rules.requests.map fun ⟨kind, address⟩ => .requestCall kind address index
  else []
end Jaune.Body
end

section
open Jaune
namespace Jaune.Body
/-- The proof-of-work rewards, then the access-list build and its item limit. -/
def finalOperations (block : BlockContext) (ommers : List Header) : List BodyOperation :=
  (match block.rules.proofOfWork with
   | none => []
   | some pow =>
     [.rewards block.coinbase (pow.blockReward + ommers.length * (pow.blockReward / 32))
       (ommers.map fun ommer =>
         (ommer.coinbase, (8 + ommer.number - block.number) * pow.blockReward / 8))]) ++
  [.buildAccessList, .checkAccessListLimit]
end Jaune.Body
end

section
open Jaune
namespace Jaune.Body
/-- The importer's post-execution operations, for `n` transactions. -/
def postExecutionOperations (block : BlockContext) (n : Nat) (ommers : List Header) (wds : List Withdrawal) :
    List BodyOperation :=
  withdrawalOperations block (n + 1) wds ++ (requestOperations block (n + 1) ++ finalOperations block ommers)
end Jaune.Body
end

section
open Jaune
namespace Jaune.Body
/-- The importer's operations for the decoded transactions. -/
def operations (block : BlockContext) (txs : List Jaune.Transaction) (ommers : List Header)
    (wds : List Withdrawal) : List BodyOperation :=
  preExecutionOperations block ++ Jaune.Body.transactionOperations txs ++ postExecutionOperations block txs.length ommers wds
end Jaune.Body
end

section
open Jaune
namespace Jaune.Body
/-- Decode before executing the importer operations, including pre-execution system calls, from
the empty prefix over the block's prestate. -/
def importer (block : BlockContext) (state : State) (txs : List (Bytes ⊕ Jaune.Transaction))
    (ommers : List Header) (wds : List Withdrawal) : Except TransitionError Jaune.Body.Prefix := do
  let decoded ← txs.mapM (decodeTransaction block.rules)
  (operations block decoded ommers wds).foldlM (step block) (Jaune.Body.Prefix.init state)
end Jaune.Body
end

section
open Jaune
namespace Jaune
/-- The importer's body with the result type of `apply_body`: the final prefix's state and
block output. -/
def applyBody (block : BlockContext) (state : State) (txs : List (Bytes ⊕ Jaune.Transaction))
    (ommers : List Header) (wds : List Withdrawal) : Except TransitionError (State × BlockOutput) :=
  Jaune.Body.Prefix.output <$> Body.importer block state txs ommers wds
end Jaune
end
