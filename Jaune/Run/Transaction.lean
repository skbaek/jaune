import Jaune.Run.Message
import Jaune.Run.Prefix

section
open Jaune
namespace Jaune
/-- The block's execution, state and blob gas allowances against the transaction's limits. -/
def checkTransactionGasLimits (block : BlockContext) (blockOut : BlockOutput) (tx : Jaune.Transaction) :
    Except TransactionValidationError Nat :=
  let executionGasAvailable := block.gasLimit - blockOut.blockGasUsed
  let blobGasAvailable := block.rules.blob.max - blockOut.blobGasUsed
  let executionGasRequired :=
    match block.rules.stateGas with
    | none => tx.gasLimit
    | some _ => min (block.rules.tx.maxGas.getD tx.gasLimit) tx.gasLimit
  if executionGasRequired > executionGasAvailable then
    .error <| .gasAllowanceExceeded <| .text
      s!"transaction execution gas = {executionGasRequired} > \
         block execution gas available = {executionGasAvailable}"
  else
    match block.rules.stateGas with
    | some _ =>
      let stateGasAvailable :=
        block.gasLimit - blockOut.blockStateGasUsed
      if tx.gasLimit > stateGasAvailable then
        .error <| .gasAllowanceExceeded <| .text
          s!"transaction state gas = {tx.gasLimit} > \
             block state gas available = {stateGasAvailable}"
      else
        let txBlobGasUsed := getTotalBlobGas tx
        if txBlobGasUsed > blobGasAvailable then
          .error <| .type3BlobCountExceeded <| .text
            s!"blob gas used = {txBlobGasUsed} > \
               blob gas available = {blobGasAvailable}"
        else .ok txBlobGasUsed
    | none =>
      let txBlobGasUsed := getTotalBlobGas tx
      if txBlobGasUsed > blobGasAvailable then
        .error <| .type3BlobCountExceeded <| .text
          s!"blob gas used = {txBlobGasUsed} > \
             blob gas available = {blobGasAvailable}"
      else .ok txBlobGasUsed
end Jaune
end

section
open Jaune
namespace Jaune
/-- The fee caps against the block's base fee. -/
def checkTransactionGasFee (block : BlockContext) (tx : Jaune.Transaction) :
    Except TransactionValidationError (Nat × Nat) :=
  match tx.type with
  | .legacy gasPrice _ =>
    checkTransactionLegacyGasFee block.baseFeePerGas tx.gasLimit gasPrice
  | .eip2930 _ gasPrice _ _ =>
    checkTransactionLegacyGasFee block.baseFeePerGas tx.gasLimit gasPrice
  | .eip1559 _ maxPriorityFee maxFee _ _ =>
    checkTransactionDynamicGasFee block.baseFeePerGas tx.gasLimit maxPriorityFee maxFee
  | .eip4844 _ maxPriorityFee maxFee _ _ _ _ =>
    checkTransactionDynamicGasFee block.baseFeePerGas tx.gasLimit maxPriorityFee maxFee
  | .eip7702 _ maxPriorityFee maxFee _ _ _ =>
    checkTransactionDynamicGasFee block.baseFeePerGas tx.gasLimit maxPriorityFee maxFee
end Jaune
end

section
open Jaune
namespace Jaune
/-- A blob transaction's hashes, their count and versions, and its blob fee cap. -/
def checkTransactionBlobData (block : BlockContext) (tx : Jaune.Transaction) (maxGasFee : Nat) :
    Except TransactionValidationError (Nat × List Hash32) :=
  match tx.type with
  | .eip4844 _ _ _ _ _ maxBlobFee blobHashes => do
    if blobHashes.isEmpty then
      .error <| .type3ZeroBlobs <| .text "no blob hashes in type-3 transaction"
    checkTransactionBlobCount block.rules.tx blobHashes
    if List.any blobHashes (λ bvh => bvh.toBytes.head? ≠ some versionedHashVersionKzg) then
      .error <| .type3InvalidBlobVersionedHash <| .text
        s!"a blob versioned hash has \
           a version byte other than {versionedHashVersionKzg}"
    else
      let blobGasPrice := getBaseFeePerBlobGas block.rules.blob block.excessBlobGas
      if maxBlobFee < blobGasPrice then
        .error <| .insufficientMaxFeePerBlobGas <|
          .text "insufficient max fee per blob gas"
      else
        .ok ⟨maxGasFee + getTotalBlobGas tx * maxBlobFee, blobHashes⟩
  | _ => .ok ⟨maxGasFee, []⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- EIP-155 chain check. A legacy `v` below 35 or encoding a chain identifier wider than 64 bits
is left to `recoverSender`, which refuses it as a bad signature. -/
def checkTransactionChainId (block : BlockContext) (tx : Jaune.Transaction) :
    Except TransactionValidationError Unit :=
  match tx.type with
  | .legacy _ _ =>
    if tx.v < 35 || 2 ^ 64 ≤ (tx.v - 35) / 2 || (tx.v - 35) / 2 = block.chainId.toNat then .ok ()
    else .error <| .invalidChainId <| .text
      s!"transaction chain ID = {(tx.v - 35) / 2}"
  | .eip2930 chainId _ _ _
  | .eip1559 chainId _ _ _ _
  | .eip4844 chainId _ _ _ _ _ _
  | .eip7702 chainId _ _ _ _ _ =>
    if chainId = block.chainId then .ok ()
    else .error <| .invalidChainId <| .text s!"transaction chain ID = {chainId}"
end Jaune
end

section
open Jaune
namespace Jaune
/-- The whole admission check against the block and the transaction-start state. -/
def checkTransaction (block : BlockContext) (state : State) (blockOut : BlockOutput)
    (tx : Jaune.Transaction) : Except TransitionError (Address × Nat × List Hash32 × Nat) := do
  let txBlobGasUsed ←
    Except.mapError .transaction (checkTransactionGasLimits block blockOut tx)
  Except.mapError TransitionError.transaction (checkTransactionChainId block tx)
  let senderAddress ←
    Except.mapError .senderRecovery (recoverSender block.chainId tx)
  let senderAccount := state.get senderAddress
  let ⟨effectiveGasPrice, maxGasFee⟩ ←
    Except.mapError .transaction (checkTransactionGasFee block tx)
  let ⟨maxGasFee, blobVersionedHashes⟩ ←
    Except.mapError .transaction (checkTransactionBlobData block tx maxGasFee)
  Except.mapError TransitionError.transaction (checkTransactionReceiver tx)
  Except.mapError TransitionError.transaction (checkTransactionAuthorizationList tx)
  Except.mapError TransitionError.transaction
    (checkTransactionSenderAccountFor block.rules senderAccount tx maxGasFee)
  .ok ⟨senderAddress, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- The sender the Amsterdam intrinsic-cost formula needs before `checkTransaction` runs; the chain
identifier is compared first, as the pinned `process_transaction` does. -/
def recoverValidationSender (block : BlockContext) (tx : Jaune.Transaction) :
    Except TransitionError Address :=
  match block.rules.stateGas with
  | none => .ok 0
  | some _ => do
    Except.mapError TransitionError.transaction (checkTransactionChainId block tx)
    Except.mapError (fun e => TransitionError.senderRecovery e) (recoverSender block.chainId tx)
end Jaune
end

section
open Jaune
namespace Jaune
/-- What a transaction's admission checks establish. -/
structure Transaction.Admitted where
  /-- The block output with the transaction entered in the transaction trie. -/
  blockOutput : BlockOutput
  sender : Address
  effectiveGasPrice : Nat
  blobVersionedHashes : List Hash32
  txBlobGasUsed : Nat
  intrinsicGas : Nat
  calldataFloorGasCost : Nat
end Jaune
end

section
open Jaune
namespace Jaune
/-- Enter the transaction in the transaction trie (before validation, as the trie counts every
candidate), then run the admission checks on the transaction-start state. -/
def Transaction.admit (block : BlockContext) (state : State) (bout : BlockOutput)
    (tx : Jaune.Transaction) (index : Nat) : Except TransitionError Transaction.Admitted := do
  let bout ← .ok {bout with
    transactionsTrie := bout.transactionsTrie.insert (Rlp.Item.bytes index.toBytes).toBytes tx}
  let validationSender : Address ← recoverValidationSender block tx
  let ⟨intrinsicGas, calldataFloorGasCost⟩ ←
    Except.mapError TransitionError.transaction (validateTransaction block.rules tx validationSender)
  let ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩ ←
    checkTransaction block state bout tx
  pure ⟨bout, sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed, intrinsicGas,
    calldataFloorGasCost⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- The admitted transaction's settlement inputs and the entry to Checked message preparation. -/
structure Transaction.Prepared where
  blockOutput : BlockOutput
  sender : Address
  effectiveGasPrice : Nat
  txBlobGasUsed : Nat
  calldataFloorGasCost : Nat
  input : TopLevel.Input
end Jaune
end

section
open Jaune
namespace Jaune
/-- Charge the sender and build the typed top-level input. The transaction-start world is
captured before the fee debit and nonce increment. -/
def Transaction.prepare (block : BlockContext) (originalState : State)
    (admitted : Transaction.Admitted) (tx : Jaune.Transaction) :
    Except TransitionError Transaction.Prepared := do
  let sender := admitted.sender
  let effectiveGasPrice := admitted.effectiveGasPrice
  let rules := block.rules
  let blobGasFee :=
    if tx.isEip4844 then calculateDataFee rules.blob block.excessBlobGas tx else 0
  let effectiveGasFee := tx.gasLimit * effectiveGasPrice
  let allocation := allocateEvmGas rules tx.gasLimit admitted.intrinsicGas
  let state := originalState.incrementNonce sender
  let state ← (state.subtractBalance sender (effectiveGasFee + blobGasFee).toU256).toExcept
    (TransitionError.internal (.invariant (.text "balance underflow")))
  let target := tx.type.to?
  let ⟨recipient, calldata, code⟩ : Address × Bytes × ByteArray := match target with
    | none => (computeContractAddress sender (state.getNonce sender - 1), [], .mk (.mk tx.data))
    | some address => (address, tx.data, state.getCode address)
  let message : Message := {
    context := {
      caller := sender, recipient := recipient, value := tx.value.toU256, calldata := calldata, code := code, depthLeft := 1024
      isStatic := false, block := block
      tx := {
        origin := sender
        gasPrice := effectiveGasPrice
        blobVersionedHashes := admitted.blobVersionedHashes
        originalState } }
    kind := if target.isNone then .create else .call
    codeAddress := target
    target := target
    gas := allocation.executionGas
    stateGasGrant := allocation.stateGasReservoir
    transfersValue := true
    disablePrecompiles := false }
  let accessListAddresses : AddressSet :=
    if rules.transactionRules.warmCoinbase then .ofList (block.coinbase :: tx.accessList.map Prod.fst)
    else .ofList (tx.accessList.map Prod.fst)
  let accessedAddresses := accessListAddresses.insertMany (rules.precompiles ++ [sender, recipient])
  let accessedStorageKeys : KeySet :=
    .ofList (tx.accessList.map fun (address, keys) => keys.map (address, ·)).flatten
  let world : World := ⟨state, .empty, .emptyWithCapacity⟩
  let checkpoint := message.initialCheckpoint world accessedAddresses accessedStorageKeys
    .emptyWithCapacity .emptyWithCapacity
  pure ⟨admitted.blockOutput, sender, effectiveGasPrice, admitted.txBlobGasUsed, admitted.calldataFloorGasCost,
    ⟨message, checkpoint, tx.authorizationList⟩⟩
end Jaune
end

section
open Jaune
namespace Jaune
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
end Jaune
end

section
open Jaune
namespace Jaune
/-- Settle gas and account effects, then record the receipt and block access list. -/
def Transaction.settleRun (admitted : Transaction.Admitted) (prepared : Transaction.Prepared)
    (tx : Jaune.Transaction) (index : Nat) (run : TopLevel.Run) :
    Except TransitionError (TransactionRun × BlockOutput) := do
  let refund ← run.refundCounter.mapError (fun fault => TransitionError.vm fault.toEvmError)
  let bout := prepared.blockOutput
  let block := prepared.input.message.context.block
  let sender := prepared.sender
  let effects := run.settlement prepared.input
  let gas := settleTransactionGas block.rules tx.gasLimit prepared.calldataFloorGasCost
    effects.gasLeft effects.stateGasLeft refund effects.stateGasUsed
  let gasRefundAmount := gas.gasLeft * prepared.effectiveGasPrice
  let priorityFeePerGas := prepared.effectiveGasPrice - block.baseFeePerGas
  let transactionFee := gas.gasUsed * priorityFeePerGas
  let state := effects.state.addBalance sender gasRefundAmount.toU256
  let writes := effects.storageWrites.clearIfEmpty state sender
  let state := state.addBalance block.coinbase transactionFee.toU256
  let writes := writes.clearIfEmpty state block.coinbase
  let deletions := effects.accountsToDelete.toList
  let writes := deletions.foldl (fun writes address => writes.eraseAddress address) writes
  let state := settleSelfDestructs block.rules deletions state
  let state := sweepTouchedAccounts block.rules effects.touchedAccounts.toList state
  let bout := bout.withGasSettlement gas prepared.txBlobGasUsed
  let receipt := makeReceipt tx effects.error bout.cumulativeGasUsed effects.logs
  let receiptKey := Rlp.Item.toBytes (.bytes index.toBytes)
  let bal := match block.rules.blockAccessListRules with
    | none => bout.blockAccessListBuilder
    | some _ => bout.blockAccessListBuilder.incorporate (index + 1)
        prepared.input.message.context.tx.originalState state
        (sender :: block.coinbase :: effects.accountReads.toList)
        effects.storageReads.toList writes.toList
  let bout := {bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie := bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ effects.logs
    blockAccessListBuilder := bal}
  pure (⟨index, tx, admitted.sender, admitted.intrinsicGas, prepared.txBlobGasUsed,
    admitted.effectiveGasPrice, prepared.input, run, gas, state, receipt, writes⟩, bout)
end Jaune
end

section
open Jaune
namespace Jaune
/-- Admit, prepare, execute and settle a signed transaction through the Checked message entry.
The transaction starts on `state`, which becomes its original state. -/
def Transaction.run (block : BlockContext) (state : State) (bout : BlockOutput) (tx : Jaune.Transaction)
    (index : Nat) : Except TransitionError (TransactionRun × BlockOutput) := do
  let admitted ← admit block state bout tx index
  let prepared ← prepare block state admitted tx
  let message ← (TopLevel.run prepared.input).mapError
    (fun fault => TransitionError.vm fault.toEvmError)
  settleRun admitted prepared tx index message
end Jaune
end
