import Jaune.Run.CheckedMessage
import Jaune.Run.Block

namespace Jaune.Checked

open Jaune

/-- The admitted transaction's settlement inputs and the entry to Checked message preparation. -/
structure Transaction.Prepared where
  bout : BlockOutput
  sender : Address
  effectiveGasPrice : Nat
  txBlobGasUsed : Nat
  calldataFloorGasCost : Nat
  input : TopLevel.Input

/-- Charge the sender and build the typed top-level input. The transaction-start world is
captured before the fee debit and nonce increment. -/
def Transaction.prepare (block : BlockContext) (originalState : State)
    (admitted : Jaune.Transaction.Admitted) (tx : Jaune.Transaction) :
    Except TransitionError Transaction.Prepared := do
  let benv := admitted.benv
  let sender := admitted.sender
  let effectiveGasPrice := admitted.effectiveGasPrice
  let rules := block.rules
  let blobGasFee :=
    if tx.isEip4844 then calculateDataFee rules.blob block.excessBlobGas tx else 0
  let effectiveGasFee := tx.gasLimit * effectiveGasPrice
  let allocation := allocateEvmGas rules tx.gasLimit admitted.intrinsicGas
  let state := benv.state.incrNonce sender
  let state ← (state.subBal sender (effectiveGasFee + blobGasFee).toU256).toExcept
    (TransitionError.internal (.invariant (.text "balance underflow")))
  let target := tx.type.to?
  let ⟨recipient, calldata, code⟩ : Address × Bytes × ByteArray := match target with
    | none => (computeContractAddress sender (state.getNonce sender - 1), [], .mk (.mk tx.data))
    | some address => (address, tx.data, state.getCode address)
  let message : Message := {
    context := {
      caller := sender, recipient, value := tx.value.toU256, calldata, code, depthLeft := 1024
      isStatic := false, block
      tx := {
        origin := sender
        gasPrice := effectiveGasPrice
        blobVersionedHashes := admitted.blobVersionedHashes
        originalState } }
    kind := if target.isNone then .create else .call
    codeAddress := target
    target
    gas := allocation.executionGas
    stateGasGrant := allocation.stateGasReservoir
    transfersValue := true
    disablePrecompiles := false }
  let accessListAddresses : AdrSet :=
    if rules.transactionRules.warmCoinbase then .ofList (block.coinbase :: tx.accessList.map Prod.fst)
    else .ofList (tx.accessList.map Prod.fst)
  let accessedAddresses := accessListAddresses.insertMany (rules.precompiles ++ [sender, recipient])
  let accessedStorageKeys : KeySet :=
    .ofList (tx.accessList.map fun (address, keys) => keys.map (address, ·)).flatten
  let world : World := ⟨state, .empty, benv.storageWrites⟩
  let checkpoint := message.initialCheckpoint world accessedAddresses accessedStorageKeys
    benv.createdAccounts .emptyWithCapacity
  pure ⟨admitted.bout, sender, effectiveGasPrice, admitted.txBlobGasUsed, admitted.calldataFloorGasCost,
    ⟨message, checkpoint, tx.authorizationList⟩⟩

/-- The typed message execution and the settled observations of a signed transaction. -/
structure TransactionRun where
  index : Nat
  transaction : Jaune.Transaction
  sender : Address
  intrinsicGas : Nat
  blobGasUsed : Nat
  effectiveGasPrice : Nat
  entry : TopLevel.Input
  message : TopLevel.Run
  gasSettlement : TransactionGasSettlement
  state : State
  receipt : Fin 5 × Receipt
  storageWrites : KeySet

/-- Settle gas and account effects, then record the receipt and block access list. -/
def Transaction.settleRun (admitted : Jaune.Transaction.Admitted) (prepared : Transaction.Prepared)
    (tx : Jaune.Transaction) (index : Nat) (run : TopLevel.Run) :
    Except TransitionError (TransactionRun × BlockOutput) := do
  let refund ← run.refundCounter.mapError (fun fault => TransitionError.vm fault.toEvmError)
  let bout := prepared.bout
  let block := prepared.input.message.context.block
  let sender := prepared.sender
  let effects := run.settlement prepared.input
  let gas := settleTransactionGas block.rules tx.gasLimit prepared.calldataFloorGasCost
    effects.gasLeft effects.stateGasLeft refund effects.stateGasUsed
  let gasRefundAmount := gas.gasLeft * prepared.effectiveGasPrice
  let priorityFeePerGas := prepared.effectiveGasPrice - block.baseFeePerGas
  let transactionFee := gas.gasUsed * priorityFeePerGas
  let state := effects.state.addBal sender gasRefundAmount.toU256
  let writes := effects.storageWrites.clearIfEmpty state sender
  let state := state.addBal block.coinbase transactionFee.toU256
  let writes := writes.clearIfEmpty state block.coinbase
  let deletions := effects.accountsToDelete.toList
  let writes := deletions.foldl (fun writes address => writes.eraseAddress address) writes
  let state := settleSelfdestructs block.rules deletions state
  let state := sweepTouchedAccounts block.rules effects.touchedAccounts.toList state
  let bout := bout.withGasSettlement gas prepared.txBlobGasUsed
  let receipt := makeReceipt tx effects.error bout.cumulativeGasUsed effects.logs
  let receiptKey := Rlp.Item.toBytes (.bytes index.toBytes)
  let bal := match block.rules.blockAccessListRules with
    | none => bout.blockAccessListBuilder
    | some _ => bout.blockAccessListBuilder.incorporate (index + 1) admitted.benv.state state
        (sender :: block.coinbase :: effects.accountReads.toList)
        effects.storageReads.toList writes.toList
  let bout := {bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie := bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ effects.logs
    blockAccessListBuilder := bal}
  pure (⟨index, tx, admitted.sender, admitted.intrinsicGas, prepared.txBlobGasUsed,
    admitted.effectiveGasPrice, prepared.input, run, gas, state, receipt, writes⟩, bout)

/-- Admit, prepare, execute and settle a signed transaction through the Checked message entry. -/
def Transaction.run (benv : Benv) (bout : BlockOutput) (tx : Jaune.Transaction) (index : Nat) :
    Except TransitionError (TransactionRun × BlockOutput) := do
  let admitted ← Jaune.Transaction.admit benv bout tx index
  let prepared ← prepare admitted.benv.stat.toBlockContext admitted.benv.stat.origState admitted tx
  let message ← (TopLevel.runNative prepared.input).mapError
    (fun fault => TransitionError.vm fault.toEvmError)
  settleRun admitted prepared tx index message

/-- Request-producing calls require code and a successful settlement. -/
def processCheckedSystemRun (block : BlockContext) (state : State) (createdAccounts : AdrSet)
    (target : Address) (data : Bytes) : Except TransitionError SystemRun := do
  let code := state.getCode target
  if code.isEmpty then
    .error <| .block <| .systemContractEmpty <| .text
      s!"system contract address {target.toHex} holds no code"
  let run ← (processSystemRun block state createdAccounts target code data).mapError
    (fun fault => TransitionError.vm fault.toEvmError)
  match run.settlement.error with
  | some halt => .error <| .block <| .systemContractCallFailed target halt
  | none => .ok run

def processCheckedSystemTransaction (block : BlockContext) (state : State) (createdAccounts : AdrSet)
    (target : Address) (data : Bytes) : Except TransitionError TopLevel.Settlement :=
  (processCheckedSystemRun block state createdAccounts target data).map SystemRun.settlement

/-- What one accepted operation records, beside its next prefix. -/
inductive OpRun where
  | systemCall (index : Nat) (address : Address) (run : SystemRun)
  | transaction (run : TransactionRun)
  | withdrawals (index : Nat) (ws : List Withdrawal)
  | depositRequests (requests : Bytes)
  | requestCall (index : Nat) (type : UInt8) (address : Address) (run : SystemRun)
  | rewards (coinbase : Address) (minerReward : Nat) (credits : List (Address × Nat))
  | buildAccessList (list : BlockAccessList)
  | checkAccessListLimit

namespace Body

/-- Execute one operation from the prefix state. The streaming runner discards the operation
record, while the recording runner keeps it. -/
@[inline] def stepWith {α : Type} (observe : OpRun → Jaune.Body.Prefix → α)
    (benv : Benv) (p : Jaune.Body.Prefix) : BodyOp → Except TransitionError α
  | .systemCall address data index => do
    let data ← data
    let message ← (processSystemRun benv.stat.toBlockContext p.state benv.createdAccounts
      address (p.state.getCode address) data).mapError (fun fault => TransitionError.vm fault.toEvmError)
    let run := message.settlement
    pure <| observe (.systemCall index address message) { p with
      state := run.state
      blockAccessListBuilder := p.blockAccessListBuilder.incorporateSystem benv.stat.rules index p.state run.state
        (address :: run.accountReads.toList) run.storageReads.toList run.storageWrites.toList }
  | .transaction tx index => do
    let (run, bout) ← Transaction.run (benv.withState p.state) p.toBlockOutput tx index
    pure <| observe (.transaction run) (Jaune.Body.Prefix.ofBlockOutput run.state bout)
  | .withdrawals ws index =>
    let state := processWithdrawalsState p.state ws
    pure <| observe (.withdrawals index ws) { p with
      state
      withdrawalsTrie := processWithdrawalsTrie p.withdrawalsTrie ws
      blockAccessListBuilder := p.blockAccessListBuilder.incorporateSystem benv.stat.rules index p.state state
        (ws.map Withdrawal.address) [] [] }
  | .depositRequests => do
    let deposits ← parseDepositRequests p.toBlockOutput
    pure <| observe (.depositRequests deposits) { p with
      requests := if deposits.length > 0 then p.requests ++ [depositRequestType ++ deposits] else p.requests }
  | .requestCall type address index => do
    let message ← processCheckedSystemRun benv.stat.toBlockContext p.state benv.createdAccounts address []
    let run := message.settlement
    pure <| observe (.requestCall index type address message) { p with
      state := run.state
      requests := if run.returnData.length > 0 then p.requests ++ [[type] ++ run.returnData] else p.requests
      blockAccessListBuilder := match benv.stat.rules.blockAccessListRules with
        | none => p.blockAccessListBuilder
        | some _ => p.blockAccessListBuilder.incorporate index p.state run.state
            (address :: run.accountReads.toList) run.storageReads.toList run.storageWrites.toList }
  | .rewards coinbase minerReward credits =>
    pure <| observe (.rewards coinbase minerReward credits)
      { p with state := creditAll credits (p.state.addBal coinbase minerReward.toU256) }
  | .buildAccessList =>
    let list := match benv.stat.rules.blockAccessListRules with
      | none => []
      | some _ => p.blockAccessListBuilder.build
    pure <| observe (.buildAccessList list) { p with blockAccessList := list }
  | .checkAccessListLimit => do
    checkBlockAccessListGasLimit benv.stat.rules benv.stat.blockGasLimit p.blockAccessList
    pure (observe .checkAccessListLimit p)

/-- The streaming step holds only the next prefix. -/
def step (benv : Benv) (p : Jaune.Body.Prefix) (op : BodyOp) : Except TransitionError Jaune.Body.Prefix :=
  stepWith (fun _ next => next) benv p op

/-- Keep the record of the same operation executed by the streaming step. -/
def stepRun (benv : Benv) (p : Jaune.Body.Prefix) (op : BodyOp) :
    Except TransitionError (OpRun × Jaune.Body.Prefix) :=
  stepWith Prod.mk benv p op

theorem stepRun_prefix (benv : Benv) (p : Jaune.Body.Prefix) (op : BodyOp) :
    (stepRun benv p op).map Prod.snd = step benv p op := by
  cases op <;> simp only [stepRun, step, stepWith]
  case systemCall address data index =>
    cases data with
    | error => rfl
    | ok bytes =>
      simp only [bind, Except.bind]
      cases processSystemRun benv.stat.toBlockContext p.state benv.createdAccounts
        address (p.state.getCode address) bytes <;> rfl
  case transaction tx index =>
    cases Transaction.run (benv.withState p.state) p.toBlockOutput tx index <;> rfl
  case depositRequests => cases parseDepositRequests p.toBlockOutput <;> rfl
  case requestCall type address index =>
    cases processCheckedSystemRun benv.stat.toBlockContext p.state benv.createdAccounts address [] <;> rfl
  case checkAccessListLimit =>
    cases checkBlockAccessListGasLimit benv.stat.rules benv.stat.blockGasLimit p.blockAccessList <;> rfl
  all_goals rfl

/-- The executed operations in order, together with their final prefix. -/
def run (benv : Benv) : Jaune.Body.Prefix → List BodyOp →
    Except TransitionError (List OpRun × Jaune.Body.Prefix)
  | p, [] => .ok ([], p)
  | p, op :: ops => do
    let (record, next) ← stepRun benv p op
    let (records, final) ← run benv next ops
    pure (record :: records, final)

/-- Decode before executing the importer operations, including pre-execution system calls. -/
def importer (benv : Benv) (txs : List (Bytes ⊕ Jaune.Transaction)) (ommers : List Header)
    (wds : List Withdrawal) : Except TransitionError Jaune.Body.Prefix := do
  let decoded ← txs.mapM (decodeTransaction benv.stat.rules)
  (Jaune.Body.ops benv decoded ommers wds).foldlM (step benv) (Jaune.Body.Prefix.init benv.state)

end Body

/-- A block's decoded transactions and ordered Checked operations over its parent. -/
structure BlockRun where
  fork : Fork
  parent : BlockChain
  block : Block
  transactions : List Jaune.Transaction
  ops : List OpRun
  final : Jaune.Body.Prefix

def BlockRun.benv (run : BlockRun) : Benv :=
  initBlockEnvironment run.fork run.parent run.block.header

def BlockRun.run (fork : Fork) (parent : BlockChain) (block : Block) : Except TransitionError BlockRun := do
  let benv := initBlockEnvironment fork parent block.header
  let decoded ← block.transactions.mapM (decodeTransaction benv.stat.rules)
  let (ops, final) ← Body.run benv (Jaune.Body.Prefix.init benv.state)
    (Jaune.Body.ops benv decoded block.ommers block.withdrawals)
  pure ⟨fork, parent, block, decoded, ops, final⟩

/-- Validate the header and ommers, execute the Checked body, then check its commitments. -/
def stateTransitionCoreE {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) :
    Except ε BlockChain := do
  Except.mapError embed (validateHeader f.ruleSet ch block.header)
  checkOmmers ()
  let q ← Except.mapError embed
    (Body.importer (initBlockEnvironment f ch block.header) block.transactions block.ommers block.withdrawals)
  Except.mapError (embed ∘ TransitionError.block) <|
    Block.check block.header (Block.Commitments.ofPrefix f.ruleSet q)
  .ok ⟨appendBlock ch.blocks block, q.state, ch.chainId⟩

end Jaune.Checked
