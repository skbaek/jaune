import Jaune.TraceTransaction
import Jaune.Bridge.G2a.Old.Transaction
import Jaune.Run.Trace
import Jaune.Bridge.G2a.Consumers

/-!
# The old trace drivers (goal `jaune-shape-and-names-v1`, gate G2a, adapter-class old side)

The bridge at the traced transaction's value: the staged traced transaction returns today's
`processTransaction` result. The old drivers of `Jaune.TraceTransaction` move here at the switch.
-/

section
open Jaune
namespace Jaune
/-- Trace the public Amsterdam top-level message operation. Preparation
failure returns its existing result without inventing an entered code frame;
transaction routing must still record that run's terminal outcome. The prepared
frame is traced like any top-level frame: its checkpoint is the prepared state. -/
def Bridge.G2a.Old.TraceTransaction.runTopLevelAmsterdam {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (state : StateGasRules) (msg : Msg) (isCreate : Bool) (runId : String) :
    m (TraceTransaction.Certified (Bridge.G2a.Old.processTopLevelAmsterdam state msg isCreate)) := do
  match hprep : prepareTopLevelAmsterdam state msg with
  | .error ⟨error, devm⟩ =>
    pure ⟨Bridge.G2a.Old.settleTopLevelPreparationFailure msg error devm, by
      simp only [Bridge.G2a.Old.processTopLevelAmsterdam, hprep]⟩
  | .ok ⟨preparedMsg, devm⟩ =>
    let frame : Frame := ⟨Message.ofTop preparedMsg isCreate, Frame.State.ofDevm devm⟩
    let result ← Trace.runFrame sink frame runId
    let value : Except EvmError (State × Bridge.G2a.Old.MessageCallOutput) := do
      let r ← result.value.mapError Fault.toEvmError
      Bridge.G2a.Old.Frame.outputAmsterdam frame r
    pure ⟨value, by simp only [Bridge.G2a.Old.processTopLevelAmsterdam, hprep, value, result.erases]; rfl⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- The successful return of the actual monadic driver projects to the public
operation, including preparation errors and precompile/transfer boundaries. -/
theorem Bridge.G2a.Old.TraceTransaction.runTopLevelAmsterdam_erasure {state : StateGasRules} {msg : Msg} {isCreate : Bool}
    (result : TraceTransaction.Certified (Bridge.G2a.Old.processTopLevelAmsterdam state msg isCreate)) :
    result.value = Bridge.G2a.Old.processTopLevelAmsterdam state msg isCreate := result.erases
end Jaune
end

section
open Jaune
namespace Jaune
def Bridge.G2a.Old.TraceTransaction.runMessageCreate {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (msg : Msg) (runId : String) :
    m (TraceTransaction.Certified (Bridge.G2a.Old.processMessageCall.create msg)) := do
  match hfork : msg.benv.stat.rules.stateGas with
  | some state =>
    let result ← Bridge.G2a.Old.TraceTransaction.runTopLevelAmsterdam sink state msg true runId
    pure ⟨result.value, by
      simpa only [Bridge.G2a.Old.processMessageCall.create, hfork] using result.erases⟩
  | none =>
    if hcollision : accountHasCodeOrNonce msg.benv.state msg.currentTarget then
      pure ⟨.ok ⟨msg.benv.state, {
        gasLeft := 0, refundCounter := 0, logs := [],
        accountsToDelete := .emptyWithCapacity,
        error := some (.halt (.addressCollision .none)), returnData := [] }⟩, by
          simp only [Bridge.G2a.Old.processMessageCall.create, hfork, hcollision, ↓reduceIte]
          rfl⟩
    else
      let frame := Frame.ofTop msg true
      let result ← Trace.runFrame sink frame runId
      let value : Except EvmError (State × Bridge.G2a.Old.MessageCallOutput) := do
        let r ← result.value.mapError Fault.toEvmError
        Bridge.G2a.Old.Frame.output frame 0 r
      pure ⟨value, by
        simp only [Bridge.G2a.Old.processMessageCall.create, hfork, hcollision, value, result.erases, frame]
        rfl⟩
end Jaune
end

section
open Jaune
namespace Jaune
def Bridge.G2a.Old.TraceTransaction.runMessageCall {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (msg : Msg) (runId : String) :
    m (TraceTransaction.Certified (Bridge.G2a.Old.processMessageCall.call msg)) := do
  match hfork : msg.benv.stat.rules.stateGas with
  | some state =>
    let result ← Bridge.G2a.Old.TraceTransaction.runTopLevelAmsterdam sink state msg false runId
    pure ⟨result.value, by
      simpa only [Bridge.G2a.Old.processMessageCall.call, hfork] using result.erases⟩
  | none =>
    match hauth : TopLevel.applyAuthorizations msg with
    | .error error =>
      pure ⟨.error error, by simp only [Bridge.G2a.Old.processMessageCall.call, hfork, hauth]; rfl⟩
    | .ok ⟨delegated, refund⟩ =>
      authorizationRefund refund
      let frame := Frame.ofTop (TopLevel.resolveCodeDelegation delegated) false
      let result ← Trace.runFrame sink frame runId
      let value : Except EvmError (State × Bridge.G2a.Old.MessageCallOutput) := do
        let r ← result.value.mapError Fault.toEvmError
        Bridge.G2a.Old.Frame.output frame refund r
      pure ⟨value, by
        simp only [Bridge.G2a.Old.processMessageCall.call, hfork, hauth, value, result.erases, frame]
        rfl⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- Trace the exact message operation invoked by `processTransaction`. -/
def Bridge.G2a.Old.TraceTransaction.runMessage {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (msg : Msg) (runId : String) :
    m (TraceTransaction.Certified (Bridge.G2a.Old.processMessageCall msg)) := do
  if htarget : msg.target.isNone then
    let result ← Bridge.G2a.Old.TraceTransaction.runMessageCreate sink msg runId
    pure ⟨result.value, by
      simpa [Bridge.G2a.Old.processMessageCall, htarget] using result.erases⟩
  else
    let result ← Bridge.G2a.Old.TraceTransaction.runMessageCall sink authorizationRefund msg runId
    pure ⟨result.value, by
      simpa [Bridge.G2a.Old.processMessageCall, htarget] using result.erases⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- Values crossing the existing transaction's execution boundary. -/
structure Bridge.G2a.Old.TraceTransaction.PreparedTransaction where
  benv : Benv
  bout : BlockOutput
  sender : Address
  effectiveGasPrice : Nat
  txBlobGasUsed : Nat
  calldataFloorGasCost : Nat
  msg : Msg
end Jaune
end

section
open Jaune
namespace Jaune
def Bridge.G2a.Old.TraceTransaction.prepareTransaction (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Except TransitionError Bridge.G2a.Old.TraceTransaction.PreparedTransaction := do
  let benv := benv.beginTransaction
  let bout ← .ok {bout with
    transactionsTrie := bout.transactionsTrie.insert (Rlp.Item.bytes index.toBytes).toBytes tx}
  let validationSender : Address ← recoverValidationSender benv tx
  let ⟨intrinsicGas, calldataFloorGasCost⟩ ←
    Except.mapError TransitionError.transaction
      (validateTransaction benv.stat.rules tx validationSender)
  let ⟨
    sender,
    effectiveGasPrice,
    blobVersionedHashes,
    txBlobGasUsed
  ⟩ ← checkTransaction benv bout tx
  let blobGasFee :=
    if tx.isEip4844
    then calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
    else 0
  let effectiveGasFee := tx.gasLimit * effectiveGasPrice
  let allocation := allocateEvmGas benv.stat.rules tx.gasLimit intrinsicGas
  let state : State := benv.state.incrNonce sender
  let state ← (state.subBal sender (effectiveGasFee + blobGasFee).toU256).toExcept
    (TransitionError.internal (.invariant (.text "balance underflow")))
  -- EIP-3651 (Shanghai) warms the coinbase; before it only the access list is
  -- pre-warmed.
  let preaccessedAddresses : AdrSet :=
    if benv.stat.rules.transactionRules.warmCoinbase then
    .ofList (benv.stat.coinbase :: tx.accessList.map Prod.fst)
    else .ofList (tx.accessList.map Prod.fst)
  let preaccessedStorageKeys : KeySet :=
    .ofList (tx.accessList.map <| λ ⟨adr, keys⟩ => keys.map (⟨adr, ·⟩)).flatten
  let tenv : Tenv := {
    transientStorage := .empty
    stat := {
      origin := sender
      gasPrice := effectiveGasPrice
      gas := allocation.executionGas
      stateGasReservoir := allocation.stateGasReservoir
      accessListAddresses := preaccessedAddresses
      accessListStorageKeys := preaccessedStorageKeys
      blobVersionedHashes := blobVersionedHashes
      auths := tx.authorizationList
      indexInBlock := index
      txHash := transactionHash tx
    }
  }
  let msg ← prepareMessage {benv with state := state} tenv tx
  pure ⟨benv, bout, sender, effectiveGasPrice, txBlobGasUsed, calldataFloorGasCost, msg⟩
end Jaune
end

section
open Jaune
namespace Jaune
def Bridge.G2a.Old.TraceTransaction.finishTransaction (prepared : Bridge.G2a.Old.TraceTransaction.PreparedTransaction) (tx : Transaction) (index : Nat)
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
/-- The local preparation/settlement split is exactly the public pipeline. -/
theorem Bridge.G2a.Old.TraceTransaction.processTransaction_eq (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Jaune.Bridge.G2a.Old.processTransaction benv bout tx index = (do
      let prepared ← Bridge.G2a.Old.TraceTransaction.prepareTransaction benv bout tx index
      let ⟨state, output⟩ ← Except.mapError TransitionError.vm (Jaune.Bridge.G2a.Old.processMessageCall prepared.msg)
      Bridge.G2a.Old.TraceTransaction.finishTransaction prepared tx index state output) := by
  simp only [Jaune.Bridge.G2a.Old.processTransaction, Bridge.G2a.Old.TraceTransaction.prepareTransaction, Bridge.G2a.Old.TraceTransaction.finishTransaction,
    bind_assoc, pure_bind]
  rfl
end Jaune
end

section
open Jaune
namespace Jaune
/-- Transaction result plus the observed message output needed by a trace
summary. A validation/preparation rejection can have no message output. -/
structure Bridge.G2a.Old.TraceTransaction.TransactionResult (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat)
    extends TraceTransaction.Certified (Jaune.Bridge.G2a.Old.processTransaction benv bout tx index) where
  messageOutput : Option Bridge.G2a.Old.MessageCallOutput
end Jaune
end

section
open Jaune
namespace Jaune
/-- Execute one real transaction with synchronous instruction observations.
Validation, fee/nonce preparation, message execution, gas/receipt settlement,
SELFDESTRUCT and block-access bookkeeping are connected to the public pipeline
by the certificate. The original transaction executor is never run a second time. -/
def Bridge.G2a.Old.TraceTransaction.runTransaction {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) (runId : String) :
    m (Bridge.G2a.Old.TraceTransaction.TransactionResult benv bout tx index) := do
  match hprep : Bridge.G2a.Old.TraceTransaction.prepareTransaction benv bout tx index with
  | .error error =>
    pure {
      value := .error error
      messageOutput := none
      erases := by
        rw [Bridge.G2a.Old.TraceTransaction.processTransaction_eq, hprep]
        rfl }
  | .ok prepared =>
    let message ← Bridge.G2a.Old.TraceTransaction.runMessage sink authorizationRefund prepared.msg runId
    let value : Except TransitionError (State × BlockOutput) := do
      let ⟨state, output⟩ ← Except.mapError TransitionError.vm message.value
      Bridge.G2a.Old.TraceTransaction.finishTransaction prepared tx index state output
    let observed := match message.value with
      | .error _ => none
      | .ok ⟨_, output⟩ => some output
    pure {
      value := value
      messageOutput := observed
      erases := by
        rw [Bridge.G2a.Old.TraceTransaction.processTransaction_eq, hprep]
        simp only [value, message.erases]
        rfl }
end Jaune
end

section
open Jaune
namespace Jaune
/-- Universal execution projection of the actual transaction trace driver. -/
theorem Bridge.G2a.Old.TraceTransaction.runTransaction_erasure {benv : Benv} {bout : BlockOutput} {tx : Transaction} {index : Nat}
    (result : Bridge.G2a.Old.TraceTransaction.TransactionResult benv bout tx index) :
    result.value = Jaune.Bridge.G2a.Old.processTransaction benv bout tx index := result.erases
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.TraceTransaction.runTransaction_id_erasure (sink : Trace.Sink Id)
    (authorizationRefund : Nat → Id Unit) (benv : Benv)
    (bout : BlockOutput) (tx : Transaction) (index : Nat) (runId : String) :
    (Bridge.G2a.Old.TraceTransaction.runTransaction sink authorizationRefund benv bout tx index runId).value =
      Jaune.Bridge.G2a.Old.processTransaction benv bout tx index :=
  (Bridge.G2a.Old.TraceTransaction.runTransaction sink authorizationRefund benv bout tx index runId).erases
end Jaune
end

namespace Jaune

/-- **Bridge at the traced transaction's value.** For every monad, sink and input, the value the
staged traced transaction returns is today's `processTransaction` result, and so the value
`Jaune.TraceTransaction.runTransaction` returns. -/
theorem Bridge.G2a.TraceTransaction.runTransaction_value_eq {benv : Benv} {bout : BlockOutput} {tx : Transaction}
    {index : Nat} (result : TraceTransaction.TransactionResult benv bout tx index)
    (old : Jaune.Bridge.G2a.Old.TraceTransaction.TransactionResult benv bout tx index) :
    result.value = old.value := by
  rw [result.erases, Bridge.G2a.Phased.B2.Transaction.run_output, old.erases, Bridge.G2a.processTransaction_eq_b2]

end Jaune
