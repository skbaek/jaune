import Jaune.Run.Transaction
import Jaune.Run.Fields

/-!
# The transaction settles its message run (goal `jaune-shape-and-names-v1`, W2 cut B2)

`processTransaction` is check, prepare, the top-level message run, settle, and the settlement reads
the `MessageRun` itself through its functions (`Jaune.Run.Fields`): no output record crosses from
the message call to the settlement. The refund counter is read first; its fault (a negative
substate refund) is a virtual-machine error of the transaction, as before.

Cut A's `Transaction.settle` and `processTransaction` (`Jaune.Run.Transaction`) took the rendered
output; these supersede them. Because those names are already staged, these are staged one level
deeper, in `Jaune.Staging.B2`; at the switch they take the final names `Transaction.settle` and
`processTransaction`, and cut A's two definitions go with the old side. The bridges are in
`Jaune.Bridge.G2a.Consumers`.
-/

namespace Jaune.Staging.B2

open Jaune Jaune.Staging

/-- Settle a transaction after its message run: read the run's refund counter, then refund the
sender, pay the coinbase, erase the writes of emptied and deleted accounts, settle the
self-destructs, sweep the touched empty accounts, record the gas, the receipt and the logs, and
incorporate the block access list at `index + 1`. -/
def Transaction.settle (prepared : Transaction.Prepared) (tx : Transaction) (index : Nat)
    (run : MessageRun) : Except TransitionError (State × BlockOutput) := do
  let benv := prepared.benv
  let bout := prepared.bout
  let sender := prepared.sender
  let effectiveGasPrice := prepared.effectiveGasPrice
  let txBlobGasUsed := prepared.txBlobGasUsed
  let calldataFloorGasCost := prepared.calldataFloorGasCost
  let refundCounter : Nat ←
    run.refundCounter.mapError (fun e => TransitionError.vm e.toEvmError)
  let settlement :=
    settleTransactionGas benv.stat.rules tx.gasLimit calldataFloorGasCost
      run.gasLeft run.stateGasLeft refundCounter run.stateGasUsed
  let gasRefundAmount : Nat :=
    settlement.gasLeft * effectiveGasPrice
  let priorityFeePerGas := effectiveGasPrice - benv.stat.baseFeePerGas
  let transactionFee := settlement.gasUsed * priorityFeePerGas
  let state := run.state.addBal sender gasRefundAmount.toU256
  let storageWrites :=
    if (state.get sender).isEmpty then run.storageWrites.eraseAddress sender
    else run.storageWrites
  let state := state.addBal benv.stat.coinbase transactionFee.toU256
  let storageWrites :=
    if (state.get benv.stat.coinbase).isEmpty then storageWrites.eraseAddress benv.stat.coinbase
    else storageWrites
  let storageWrites := run.accountsToDelete.toList.foldl
    (fun writes a => writes.eraseAddress a) storageWrites
  let state := settleSelfdestructs benv.stat.rules
    run.accountsToDelete.toList state
  -- EIP-161: `destroy_touched_empty_accounts` (Spurious Dragon to Gray Glacier).
  let state := sweepTouchedAccounts benv.stat.rules
    run.touchedAccounts.toList state
  let bout ← .ok (bout.withGasSettlement settlement txBlobGasUsed)
  let receipt :=
    makeReceipt tx run.error bout.cumulativeGasUsed run.logs
  let receiptKey : Bytes := Rlp.Item.toBytes <| .bytes index.toBytes
  let bout ← .ok {bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie := bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ run.logs}
  -- EIP-7928: `incorporate_tx_into_block` at `index + 1`, after the
  -- self-destruct settlement: surviving explicit storage writes and account
  -- changes, plus reads and the transaction-level ones --
  -- the sender (`check_transaction`, `update_sender_state`, the refund) and
  -- the coinbase (`disburse_gas_fees` credits it even a zero fee).
  let bal := match benv.stat.rules.blockAccessListRules with
    | none => bout.blockAccessListBuilder
    | some _ => bout.blockAccessListBuilder.incorporate (index + 1) benv.state state
        (sender :: benv.stat.coinbase :: run.accountReads.toList)
        run.storageReads.toList storageWrites.toList
  .ok ⟨state, {bout with blockAccessListBuilder := bal}⟩

/-- One transaction: check, prepare, the top-level message run, settle. -/
def processTransaction (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Except TransitionError (State × BlockOutput) := do
  let checked ← Transaction.check benv bout tx index
  let prepared ← Transaction.prepare checked tx index
  let run ← (Message.run prepared.msg).mapError (fun e => TransitionError.vm e.toEvmError)
  Transaction.settle prepared tx index run

/-- The successful phases of one transaction. The block output is threaded separately, so a
record can be read independently of earlier entries in the block's tries. -/
structure TransactionRun where
  index : Nat
  transaction : Transaction
  sender : Address
  intrinsicGas : Nat
  blobGasUsed : Nat
  effectiveGasPrice : Nat
  message : MessageRun
  gasSettlement : TransactionGasSettlement
  state : State
  receipt : Fin 5 × Receipt
  /-- The writes left after fees, account deletions and settlement. -/
  storageWrites : KeySet

/-- Settle a prepared transaction, keeping the observations beside the updated block output. -/
def Transaction.settleRun (checked : Transaction.Checked) (prepared : Transaction.Prepared)
    (tx : Transaction) (index : Nat) (run : MessageRun) :
    Except TransitionError (TransactionRun × BlockOutput) := do
  let benv := prepared.benv
  let bout := prepared.bout
  let sender := prepared.sender
  let effectiveGasPrice := prepared.effectiveGasPrice
  let txBlobGasUsed := prepared.txBlobGasUsed
  let calldataFloorGasCost := prepared.calldataFloorGasCost
  let refundCounter : Nat ←
    run.refundCounter.mapError (fun e => TransitionError.vm e.toEvmError)
  let settlement :=
    settleTransactionGas benv.stat.rules tx.gasLimit calldataFloorGasCost
      run.gasLeft run.stateGasLeft refundCounter run.stateGasUsed
  let gasRefundAmount : Nat :=
    settlement.gasLeft * effectiveGasPrice
  let priorityFeePerGas := effectiveGasPrice - benv.stat.baseFeePerGas
  let transactionFee := settlement.gasUsed * priorityFeePerGas
  let state := run.state.addBal sender gasRefundAmount.toU256
  let storageWrites :=
    if (state.get sender).isEmpty then run.storageWrites.eraseAddress sender
    else run.storageWrites
  let state := state.addBal benv.stat.coinbase transactionFee.toU256
  let storageWrites :=
    if (state.get benv.stat.coinbase).isEmpty then storageWrites.eraseAddress benv.stat.coinbase
    else storageWrites
  let storageWrites := run.accountsToDelete.toList.foldl
    (fun writes a => writes.eraseAddress a) storageWrites
  let state := settleSelfdestructs benv.stat.rules
    run.accountsToDelete.toList state
  -- EIP-161: `destroy_touched_empty_accounts` (Spurious Dragon to Gray Glacier).
  let state := sweepTouchedAccounts benv.stat.rules
    run.touchedAccounts.toList state
  let bout ← .ok (bout.withGasSettlement settlement txBlobGasUsed)
  let receipt :=
    makeReceipt tx run.error bout.cumulativeGasUsed run.logs
  let receiptKey : Bytes := Rlp.Item.toBytes <| .bytes index.toBytes
  let bout ← .ok {bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie := bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ run.logs}
  -- EIP-7928: `incorporate_tx_into_block` at `index + 1`, after the
  -- self-destruct settlement: surviving explicit storage writes and account
  -- changes, plus reads and the transaction-level ones --
  -- the sender (`check_transaction`, `update_sender_state`, the refund) and
  -- the coinbase (`disburse_gas_fees` credits it even a zero fee).
  let bal := match benv.stat.rules.blockAccessListRules with
    | none => bout.blockAccessListBuilder
    | some _ => bout.blockAccessListBuilder.incorporate (index + 1) benv.state state
        (sender :: benv.stat.coinbase :: run.accountReads.toList)
        run.storageReads.toList storageWrites.toList
  .ok (⟨index, tx, checked.sender, checked.intrinsicGas, prepared.txBlobGasUsed, checked.effectiveGasPrice,
    run, settlement, state, receipt, storageWrites⟩, {bout with blockAccessListBuilder := bal})

/-- Execute one transaction and keep its message, gas settlement and receipt. -/
def Transaction.run (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Except TransitionError (TransactionRun × BlockOutput) := do
  let checked ← Transaction.check benv bout tx index
  let prepared ← Transaction.prepare checked tx index
  let message ← (Message.run prepared.msg).mapError (fun e => TransitionError.vm e.toEvmError)
  Transaction.settleRun checked prepared tx index message

/-- Erasing the transaction record preserves both failure and the entire successful output. -/
theorem Transaction.run_output (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    (fun pair => (pair.1.state, pair.2)) <$> Transaction.run benv bout tx index =
      processTransaction benv bout tx index := by
  unfold Transaction.run processTransaction
  simp only [map_bind]
  refine bind_congr fun checked => bind_congr fun prepared => bind_congr fun message => ?_
  unfold Transaction.settleRun Transaction.settle
  simp only [map_bind]
  exact bind_congr fun _ => rfl

end Jaune.Staging.B2
