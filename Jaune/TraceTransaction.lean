import Jaune.MessageCall.Trace
import Jaune.Transaction

/-!
Transaction-side tracing, kept outside the core executor's import closure.
Each traced message operation runs the top frame with `Trace.runFrame` and
renders its settled result exactly as `processMessageCall` does, so its
certificate is the public operation itself.
-/
namespace Jaune.TraceTransaction
open Jaune

/-- Successful monadic observations carry the value of the existing pure
boundary. The expected value appears only in a type and an erased proof. -/
structure Certified {α : Type} (expected : α) where
  value : α
  erases : value = expected

/-- Trace the public Amsterdam top-level message operation. Preparation
failure returns its existing result without inventing an entered code frame;
transaction routing must still record that run's terminal outcome. The prepared
frame is traced like any top-level frame: its checkpoint is the prepared state. -/
def runTopLevelAmsterdam {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (state : StateGasRules) (msg : Msg) (isCreate : Bool) (runId : String) :
    m (Certified (processTopLevelAmsterdam state msg isCreate)) := do
  match hprep : prepareTopLevelAmsterdam state msg with
  | .error ⟨error, devm⟩ =>
    pure ⟨settleTopLevelPreparationFailure msg error devm, by
      simp only [processTopLevelAmsterdam, hprep]⟩
  | .ok ⟨preparedMsg, devm⟩ =>
    let frame : Frame := ⟨Message.ofLegacy preparedMsg isCreate, Frame.State.ofDevm devm⟩
    let result ← Trace.runFrame sink frame runId
    let value : Except EvmError (State × MsgCallOutput) := do
      let r ← result.value.mapError Fault.toEvmError
      frame.outputAmsterdam r
    pure ⟨value, by simp only [processTopLevelAmsterdam, hprep, value, result.erases]; rfl⟩

/-- The successful return of the actual monadic driver projects to the public
operation, including preparation errors and precompile/transfer boundaries. -/
theorem runTopLevelAmsterdam_erasure {state : StateGasRules} {msg : Msg} {isCreate : Bool}
    (result : Certified (processTopLevelAmsterdam state msg isCreate)) :
    result.value = processTopLevelAmsterdam state msg isCreate := result.erases

def runMessageCreate {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (msg : Msg) (runId : String) :
    m (Certified (processMessageCall.create msg)) := do
  match hfork : msg.benv.stat.rules.stateGas with
  | some state =>
    let result ← runTopLevelAmsterdam sink state msg true runId
    pure ⟨result.value, by
      simpa only [processMessageCall.create, hfork] using result.erases⟩
  | none =>
    if hcollision : accountHasCodeOrNonce msg.benv.state msg.currentTarget then
      pure ⟨.ok ⟨msg.benv.state, {
        gasLeft := 0, refundCounter := 0, logs := [],
        accountsToDelete := .emptyWithCapacity,
        error := some (.halt (.addressCollision .none)), returnData := [] }⟩, by
          simp only [processMessageCall.create, hfork, hcollision, ↓reduceIte]
          rfl⟩
    else
      let frame := Frame.ofTop msg true
      let result ← Trace.runFrame sink frame runId
      let value : Except EvmError (State × MsgCallOutput) := do
        let r ← result.value.mapError Fault.toEvmError
        frame.output 0 r
      pure ⟨value, by
        simp only [processMessageCall.create, hfork, hcollision, value, result.erases, frame]
        rfl⟩

def runMessageCall {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (msg : Msg) (runId : String) :
    m (Certified (processMessageCall.call msg)) := do
  match hfork : msg.benv.stat.rules.stateGas with
  | some state =>
    let result ← runTopLevelAmsterdam sink state msg false runId
    pure ⟨result.value, by
      simpa only [processMessageCall.call, hfork] using result.erases⟩
  | none =>
    match hauth : processMessageCall.authorize msg with
    | .error error =>
      pure ⟨.error error, by simp only [processMessageCall.call, hfork, hauth]; rfl⟩
    | .ok ⟨delegated, refund⟩ =>
      authorizationRefund refund
      let frame := Frame.ofTop delegated.resolveCodeDelegation false
      let result ← Trace.runFrame sink frame runId
      let value : Except EvmError (State × MsgCallOutput) := do
        let r ← result.value.mapError Fault.toEvmError
        frame.output refund r
      pure ⟨value, by
        simp only [processMessageCall.call, hfork, hauth, value, result.erases, frame]
        rfl⟩

/-- Trace the exact message operation invoked by `processTransaction`. -/
def runMessage {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (msg : Msg) (runId : String) :
    m (Certified (processMessageCall msg)) := do
  if htarget : msg.target.isNone then
    let result ← runMessageCreate sink msg runId
    pure ⟨result.value, by
      simpa [processMessageCall, htarget] using result.erases⟩
  else
    let result ← runMessageCall sink authorizationRefund msg runId
    pure ⟨result.value, by
      simpa [processMessageCall, htarget] using result.erases⟩

/-- Values crossing the existing transaction's execution boundary. -/
structure PreparedTransaction where
  benv : Benv
  bout : BlockOutput
  sender : Address
  effectiveGasPrice : Nat
  txBlobGasUsed : Nat
  calldataFloorGasCost : Nat
  msg : Msg

def prepareTransaction (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Except TransitionError PreparedTransaction := do
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
      txHash := getTxHash tx
    }
  }
  let msg ← prepareMessage {benv with state := state} tenv tx
  pure ⟨benv, bout, sender, effectiveGasPrice, txBlobGasUsed, calldataFloorGasCost, msg⟩

def finishTransaction (prepared : PreparedTransaction) (tx : Transaction) (index : Nat)
    (state : State) (txOutput : MsgCallOutput) :
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
    if (state.get sender).isEmpty then txOutput.storageWrites.eraseAddress sender
    else txOutput.storageWrites
  let state := state.addBal benv.stat.coinbase transactionFee.toU256
  let storageWrites :=
    if (state.get benv.stat.coinbase).isEmpty then storageWrites.eraseAddress benv.stat.coinbase
    else storageWrites
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

/-- The local preparation/settlement split is exactly the public pipeline. -/
theorem processTransaction_eq (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Jaune.processTransaction benv bout tx index = (do
      let prepared ← prepareTransaction benv bout tx index
      let ⟨state, output⟩ ← Except.mapError TransitionError.vm (Jaune.processMessageCall prepared.msg)
      finishTransaction prepared tx index state output) := by
  simp only [Jaune.processTransaction, prepareTransaction, finishTransaction,
    bind_assoc, pure_bind]
  rfl

/-- Transaction result plus the observed message output needed by a trace
summary. A validation/preparation rejection can have no message output. -/
structure TransactionResult (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat)
    extends Certified (Jaune.processTransaction benv bout tx index) where
  messageOutput : Option MsgCallOutput

/-- Execute one real transaction with synchronous instruction observations.
Validation, fee/nonce preparation, message execution, gas/receipt settlement,
SELFDESTRUCT and block-access bookkeeping are connected to the public pipeline
by the certificate. The original transaction executor is never run a second time. -/
def runTransaction {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) (runId : String) :
    m (TransactionResult benv bout tx index) := do
  match hprep : prepareTransaction benv bout tx index with
  | .error error =>
    pure {
      value := .error error
      messageOutput := none
      erases := by
        rw [processTransaction_eq, hprep]
        rfl }
  | .ok prepared =>
    let message ← runMessage sink authorizationRefund prepared.msg runId
    let value : Except TransitionError (State × BlockOutput) := do
      let ⟨state, output⟩ ← Except.mapError TransitionError.vm message.value
      finishTransaction prepared tx index state output
    let observed := match message.value with
      | .error _ => none
      | .ok ⟨_, output⟩ => some output
    pure {
      value := value
      messageOutput := observed
      erases := by
        rw [processTransaction_eq, hprep]
        simp only [value, message.erases]
        rfl }

/-- Universal execution projection of the actual transaction trace driver. -/
theorem runTransaction_erasure {benv : Benv} {bout : BlockOutput} {tx : Transaction} {index : Nat}
    (result : TransactionResult benv bout tx index) :
    result.value = Jaune.processTransaction benv bout tx index := result.erases

theorem runTransaction_id_erasure (sink : Trace.Sink Id)
    (authorizationRefund : Nat → Id Unit) (benv : Benv)
    (bout : BlockOutput) (tx : Transaction) (index : Nat) (runId : String) :
    (runTransaction sink authorizationRefund benv bout tx index runId).value =
      Jaune.processTransaction benv bout tx index :=
  (runTransaction sink authorizationRefund benv bout tx index runId).erases

/-! ### EIP-161: the sweep runs in transaction settlement

`processTransaction_eq` makes `finishTransaction` the public settlement, so
these checks pin that `processTransaction` sweeps the touched accounts its
message call reports: an account holding only storage is erased under Gray
Glacier and kept under Prague. -/

private def sweepGuardAdr : Address := 0x2000

private def sweepGuardSurvives (fork : Fork) : Bool :=
  let state := State.setStorVal .empty sweepGuardAdr 1 1
  let benv : Benv := { (default : Benv) with
    state := state
    stat := { (default : BenvStat) with fork := fork, origState := state } }
  let prepared : PreparedTransaction :=
    ⟨benv, .init, 0x5000, 0, 0, 0, default⟩
  let tx : Transaction := {
    nonce := 0
    gasLimit := 0
    value := 0
    data := []
    v := 27
    r := []
    s := []
    type := .legacy 0 (some 0) }
  let out : MsgCallOutput := {
    gasLeft := 0
    refundCounter := 0
    logs := []
    accountsToDelete := .emptyWithCapacity
    error := none
    returnData := []
    touchedAccounts := (.emptyWithCapacity : AdrSet).insert sweepGuardAdr }
  match finishTransaction prepared tx 0 state out with
  | .ok (post, _) => post[sweepGuardAdr]?.isSome
  | .error _ => true

#guard !sweepGuardSurvives .grayGlacier
#guard sweepGuardSurvives .prague

end Jaune.TraceTransaction
