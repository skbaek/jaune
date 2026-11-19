import Jaune.Run.CheckedMessage
import Jaune.Run.Transaction

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

end Jaune.Checked
