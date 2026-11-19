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
def processCheckedSystemTransaction (block : BlockContext) (state : State) (createdAccounts : AdrSet)
    (target : Address) (data : Bytes) : Except TransitionError TopLevel.Settlement := do
  let code := state.getCode target
  if code.isEmpty then
    .error <| .block <| .systemContractEmpty <| .text
      s!"system contract address {target.toHex} holds no code"
  let run ← (processSystemTransaction block state createdAccounts target code data).mapError
    (fun fault => TransitionError.vm fault.toEvmError)
  match run.error with
  | some halt => .error <| .block <| .systemContractCallFailed target halt
  | none => .ok run

namespace Body

/-- Record the prefix after one body operation. Every execution starts from the prefix state. -/
def step (benv : Benv) (p : Jaune.Body.Prefix) : BodyOp → Except TransitionError Jaune.Body.Prefix
  | .systemCall address data index => do
    let data ← data
    let run ← (processSystemTransaction benv.stat.toBlockContext p.state benv.createdAccounts
      address (p.state.getCode address) data).mapError (fun fault => TransitionError.vm fault.toEvmError)
    pure { p with
      state := run.state
      blockAccessListBuilder := p.blockAccessListBuilder.incorporateSystem benv.stat.rules index p.state run.state
        (address :: run.accountReads.toList) run.storageReads.toList run.storageWrites.toList }
  | .transaction tx index => do
    let (run, bout) ← Transaction.run (benv.withState p.state) p.toBlockOutput tx index
    pure (Jaune.Body.Prefix.ofBlockOutput run.state bout)
  | .withdrawals ws index =>
    let state := processWithdrawalsState p.state ws
    pure { p with
      state
      withdrawalsTrie := processWithdrawalsTrie p.withdrawalsTrie ws
      blockAccessListBuilder := p.blockAccessListBuilder.incorporateSystem benv.stat.rules index p.state state
        (ws.map Withdrawal.address) [] [] }
  | .depositRequests => do
    let deposits ← parseDepositRequests p.toBlockOutput
    pure { p with
      requests := if deposits.length > 0 then p.requests ++ [depositRequestType ++ deposits] else p.requests }
  | .requestCall type address index => do
    let run ← processCheckedSystemTransaction benv.stat.toBlockContext p.state benv.createdAccounts address []
    pure { p with
      state := run.state
      requests := if run.returnData.length > 0 then p.requests ++ [[type] ++ run.returnData] else p.requests
      blockAccessListBuilder := match benv.stat.rules.blockAccessListRules with
        | none => p.blockAccessListBuilder
        | some _ => p.blockAccessListBuilder.incorporate index p.state run.state
            (address :: run.accountReads.toList) run.storageReads.toList run.storageWrites.toList }
  | .rewards coinbase minerReward credits =>
    pure { p with state := creditAll credits (p.state.addBal coinbase minerReward.toU256) }
  | .buildAccessList =>
    let list := match benv.stat.rules.blockAccessListRules with
      | none => []
      | some _ => p.blockAccessListBuilder.build
    pure { p with blockAccessList := list }
  | .checkAccessListLimit => do
    checkBlockAccessListGasLimit benv.stat.rules benv.stat.blockGasLimit p.blockAccessList
    pure p

/-- Decode before executing the importer operations, including pre-execution system calls. -/
def importer (benv : Benv) (txs : List (Bytes ⊕ Jaune.Transaction)) (ommers : List Header)
    (wds : List Withdrawal) : Except TransitionError Jaune.Body.Prefix := do
  let decoded ← txs.mapM (decodeTransaction benv.stat.rules)
  (Jaune.Body.ops benv decoded ommers wds).foldlM (step benv) (Jaune.Body.Prefix.init benv.state)

end Body

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
