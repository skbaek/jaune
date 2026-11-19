import Jaune.Run.Body
import Jaune.Bridge.G2a.Old.Body

section
open Jaune
namespace Jaune
/-- `stateTransitionCoreE` with the importer's body in place of `applyBody`: header validation,
the ommer check, the body, then the commitment checks and the access-list check, as before. Cut E
restructures this into the block run; here only the body changed. -/
def Bridge.G2a.Phased.stateTransitionCoreE {ε : Type} (embed : TransitionError → ε)
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
end Jaune
end

section
open Jaune
namespace Jaune
/-- What a top-level message run hands the transaction. A frame's result is rendered by
`Frame.output` (with its authorization refund) or, with state gas, by `Frame.outputAmsterdam`. A
refusal without state gas reports the message's state with a collision halt; with state gas it is
`settleTopLevelPreparationFailure`'s halt. -/
def Bridge.G2a.Phased.MessageRun.output (run : TopLevelRun) : Except EvmError (State × Bridge.G2a.Old.MessageCallOutput) :=
  match run.preparation, run.result with
  | .frame f authorizationRefund, some r =>
    match run.entry.benv.stat.rules.stateGas with
    | none => Jaune.Bridge.G2a.Old.Frame.output f authorizationRefund r
    | some _ => Jaune.Bridge.G2a.Old.Frame.outputAmsterdam f r
  | .frame _ _, none =>
    -- Unreachable: `Message.run` records a result for every frame (`Message.run_result`). A
    -- breach is an internal invariant failure and fails closed.
    .error (.internal (.invariant (.text "message run: a frame without a result")))
  | .refused reason halted, _ =>
    match run.entry.benv.stat.rules.stateGas with
    | none =>
      .ok ⟨run.entry.benv.state,
        { gasLeft := 0, refundCounter := 0, logs := [],
          accountsToDelete := .emptyWithCapacity,
          error := .some (.halt reason), returnData := [] }⟩
    | some _ => Bridge.G2a.Old.settleTopLevelPreparationFailure run.entry (.halt reason) halted
end Jaune
end

section
open Jaune
namespace Jaune
/-- The top-level message call: the run, then what it hands the transaction. -/
def Bridge.G2a.Phased.processMessageCall (msg : Msg) : Except EvmError (State × Bridge.G2a.Old.MessageCallOutput) := do
  let run ← (TopLevel.run msg).mapError Fault.toEvmError
  Bridge.G2a.Phased.MessageRun.output run
end Jaune
end

section
open Jaune
namespace Jaune
/-- Settle a transaction after its message run: read the run's refund counter, then refund the
sender, pay the coinbase, erase the writes of emptied and deleted accounts, settle the
self-destructs, sweep the touched empty accounts, record the gas, the receipt and the logs, and
incorporate the block access list at `index + 1`. -/
def Bridge.G2a.Phased.B2.Transaction.settle (prepared : Transaction.Prepared) (tx : Transaction) (index : Nat)
    (run : TopLevelRun) : Except TransitionError (State × BlockOutput) := do
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
    run.storageWrites.clearIfEmpty state sender
  let state := state.addBal benv.stat.coinbase transactionFee.toU256
  let storageWrites :=
    storageWrites.clearIfEmpty state benv.stat.coinbase
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
end Jaune
end

section
open Jaune
namespace Jaune
/-- One transaction: check, prepare, the top-level message run, settle. -/
def Bridge.G2a.Phased.B2.processTransaction (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Except TransitionError (State × BlockOutput) := do
  let checked ← Transaction.admit benv bout tx index
  let prepared ← Transaction.prepare checked tx index
  let run ← (TopLevel.run prepared.msg).mapError (fun e => TransitionError.vm e.toEvmError)
  Bridge.G2a.Phased.B2.Transaction.settle prepared tx index run
end Jaune
end

section
open Jaune
namespace Jaune
/-- Erasing the transaction record preserves both failure and the entire successful output. -/
theorem Bridge.G2a.Phased.B2.Transaction.run_output (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    (fun pair => (pair.1.state, pair.2)) <$> Transaction.run benv bout tx index =
      Bridge.G2a.Phased.B2.processTransaction benv bout tx index := by
  unfold Transaction.run Bridge.G2a.Phased.B2.processTransaction
  simp only [map_bind]
  refine bind_congr fun checked => bind_congr fun prepared => bind_congr fun message => ?_
  unfold Transaction.settleRun Bridge.G2a.Phased.B2.Transaction.settle
  simp only [map_bind]
  exact bind_congr fun _ => rfl
end Jaune
end

section
open Jaune
namespace Jaune
/-- Settle a transaction after its message call: refund the sender, pay the coinbase, erase the
writes of emptied and deleted accounts, settle the self-destructs, sweep the touched empty
accounts, then record the gas, the receipt and the logs, and incorporate the block access list at
`index + 1`. -/
def Bridge.G2a.Phased.Transaction.settle (prepared : Transaction.Prepared) (tx : Transaction) (index : Nat)
    (state : State) (txOutput : Bridge.G2a.Old.MessageCallOutput) :
    Except TransitionError (State × BlockOutput) := do
  let benv := prepared.benv
  let bout := prepared.bout
  let sender := prepared.sender
  let effectiveGasPrice := prepared.effectiveGasPrice
  let txBlobGasUsed := prepared.txBlobGasUsed
  let calldataFloorGasCost := prepared.calldataFloorGasCost
  let refundCounter : Nat ←
    (Int.toNat? txOutput.refundCounter).toExcept
      (TransitionError.internal (.invariant (.text "refund counter is negative")))
  let settlement :=
    settleTransactionGas benv.stat.rules tx.gasLimit calldataFloorGasCost
      txOutput.gasLeft txOutput.stateGasLeft refundCounter txOutput.stateGasUsed
  let gasRefundAmount : Nat :=
    settlement.gasLeft * effectiveGasPrice
  let priorityFeePerGas := effectiveGasPrice - benv.stat.baseFeePerGas
  let transactionFee := settlement.gasUsed * priorityFeePerGas
  let state := state.addBal sender gasRefundAmount.toU256
  let storageWrites :=
    txOutput.storageWrites.clearIfEmpty state sender
  let state := state.addBal benv.stat.coinbase transactionFee.toU256
  let storageWrites :=
    storageWrites.clearIfEmpty state benv.stat.coinbase
  let storageWrites := txOutput.accountsToDelete.toList.foldl
    (fun writes a => writes.eraseAddress a) storageWrites
  let state := settleSelfdestructs benv.stat.rules
    txOutput.accountsToDelete.toList state
  -- EIP-161: `destroy_touched_empty_accounts` (Spurious Dragon to Gray Glacier).
  let state := sweepTouchedAccounts benv.stat.rules
    txOutput.touchedAccounts.toList state
  let bout ← .ok (bout.withGasSettlement settlement txBlobGasUsed)
  let receipt :=
    makeReceipt tx txOutput.error bout.cumulativeGasUsed txOutput.logs
  let receiptKey : Bytes := Rlp.Item.toBytes <| .bytes index.toBytes
  let bout ← .ok {bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie := bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ txOutput.logs}
  -- EIP-7928: `incorporate_tx_into_block` at `index + 1`, after the
  -- self-destruct settlement: surviving explicit storage writes and account
  -- changes, plus reads and the transaction-level ones --
  -- the sender (`check_transaction`, `update_sender_state`, the refund) and
  -- the coinbase (`disburse_gas_fees` credits it even a zero fee).
  let bal := match benv.stat.rules.blockAccessListRules with
    | none => bout.blockAccessListBuilder
    | some _ => bout.blockAccessListBuilder.incorporate (index + 1) benv.state state
        (sender :: benv.stat.coinbase :: txOutput.accountReads.toList)
        txOutput.storageReads.toList storageWrites.toList
  .ok ⟨state, {bout with blockAccessListBuilder := bal}⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- One transaction: check, prepare, the top-level message call, settle. -/
def Bridge.G2a.Phased.processTransaction (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Except TransitionError (State × BlockOutput) := do
  let checked ← Transaction.admit benv bout tx index
  let prepared ← Transaction.prepare checked tx index
  let ⟨state, output⟩ ← Except.mapError TransitionError.vm (Bridge.G2a.Phased.processMessageCall prepared.msg)
  Bridge.G2a.Phased.Transaction.settle prepared tx index state output
end Jaune
end
