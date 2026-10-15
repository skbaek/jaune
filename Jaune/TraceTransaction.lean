import Jaune.Trace
import Jaune.Transaction

/-!
Transaction-side tracing, kept outside the core executor's import closure.
The local pure frame boundary exposes the existing private operation through
a public definitional equation. It is the specification for the traced
prepared-frame driver, not a second execution used to certify its result.
-/
namespace Jaune.TraceTransaction
open Jaune

def preparedFrame (frame : Frame) (prepared : Devm) :
    Except (EvmError × State × AdrSet × Tra) Devm :=
  match frame.inner.benvAfterTransfer with
  | .error e => frame.settleMsg (.error e)
  | .ok benv =>
    let inner := frame.inner.withBenv benv
    let dyna :=
      ((prepared.withState benv.state).withStorageWrites benv.storageWrites).withCreatedAccounts
        benv.createdAccounts
    let evm : Evm := {pc := 0, sta := initSevm inner, dyna := dyna}
    let raw :=
      match inner.codeAddress with
      | none => exec evm
      | some adr =>
        if !inner.disablePrecompiles && inner.benv.stat.rules.isPrecomp adr then
          executePrecomp evm adr
        else exec evm
    frame.settle raw

/-- Prepared entry has already performed the transaction's authorization and
state-gas setup. It must not go through ordinary `Frame.enter` again. -/
def preparedEntry (frame : Frame) (prepared : Devm) : FrameEntry :=
  match frame.inner.benvAfterTransfer with
  | .error e => .done (frame.settleMsg (.error e))
  | .ok benv =>
    let inner := frame.inner.withBenv benv
    let dyna :=
      ((prepared.withState benv.state).withStorageWrites benv.storageWrites).withCreatedAccounts
        benv.createdAccounts
    let evm : Evm := {pc := 0, sta := initSevm inner, dyna := dyna}
    match inner.codeAddress with
    | none => .run evm
    | some adr =>
      if !inner.disablePrecompiles && inner.benv.stat.rules.isPrecomp adr then
        .done (frame.settle (executePrecomp evm adr))
      else .run evm

theorem preparedFrame_eq (frame : Frame) (prepared : Devm) :
    preparedFrame frame prepared =
      match preparedEntry frame prepared with
      | .done result => result
      | .run evm => frame.settle (Jaune.exec evm) := by
  cases hb : frame.inner.benvAfterTransfer with
  | error error => simp only [preparedFrame, preparedEntry, hb]
  | ok benv =>
    simp only [preparedFrame, preparedEntry, hb]
    cases hc : (frame.inner.withBenv benv).codeAddress with
    | none => rfl
    | some adr =>
      simp only
      split <;> rfl

/-- Successful monadic observations carry the value of the existing pure
boundary. The expected value appears only in a type and an erased proof. -/
structure Certified {α : Type} (expected : α) where
  value : α
  erases : value = expected

/-- The actual prepared-frame production driver. Precompiles and transfer
failures emit zero-instruction entry/settlement pairs; code uses `Trace.exec`.
Only the traced execution runs. -/
def runPreparedFrame {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (frame : Frame) (prepared : Devm) (runId : String) :
    m (Certified (preparedFrame frame prepared)) := do
  let context : Trace.Context := ⟨runId, 0, 1⟩
  match hentry : preparedEntry frame prepared with
  | .done settled =>
    sink (.entered context frame (.done settled))
    sink (.settled context frame settled)
    pure ⟨settled, by simp only [preparedFrame_eq, hentry]⟩
  | .run evm =>
    sink (.entered context frame (.run evm))
    let result ← Trace.exec sink evm context 1
    let settled := frame.settle result.value
    sink (.settled context frame settled)
    pure ⟨settled, by simp only [preparedFrame_eq, hentry, settled, result.erases]⟩

def messageOutputAmsterdam (msg : Msg) (evm : Devm) :
    Except EvmError (State × MsgCallOutput) := do
  let refundCounter ←
    if evm.error.isNone then
      (Int.toNat? evm.refundCounter).toExcept
        (EvmError.internal (.invariant (.text "refund counter is negative")))
    else .ok 0
  let logs := if evm.error.isNone then evm.logs else []
  let accountsToDelete :=
    if evm.error.isNone then evm.accountsToDelete else .emptyWithCapacity
  let stateGasUsed :=
    Int.ofNat msg.stateGasGrant - Int.ofNat evm.stateGasLeft +
      Int.ofNat evm.mach.stateGas.spilled +
      Int.ofNat evm.mach.stateGas.committedSpill
  .ok ⟨evm.state, {
    accountReads := evm.meta.accountReads
    storageReads := evm.meta.storageReads
    storageWrites := evm.world.storageWrites
    gasLeft := evm.gasLeft
    refundCounter := refundCounter
    logs := logs
    accountsToDelete := accountsToDelete
    error := evm.error
    returnData := evm.output
    stateGasLeft := evm.stateGasLeft
    stateGasUsed := stateGasUsed
  }⟩

def topLevelAmsterdam (state : StateGasRules) (msg : Msg)
    (frameOf : Msg → Frame) : Except EvmError (State × MsgCallOutput) :=
  match prepareTopLevelAmsterdam state msg with
  | .error ⟨error, devm⟩ =>
    settleTopLevelPreparationFailure msg error devm
  | .ok ⟨msg, devm⟩ => do
    let evm ← Except.bimap Prod.fst id
      (preparedFrame (frameOf msg) devm)
    messageOutputAmsterdam msg evm

/-- This equation checks the private prepared-frame and output boundary
through the public API without depending on generated private names. -/
theorem topLevelAmsterdam_eq (state : StateGasRules) (msg : Msg)
    (frameOf : Msg → Frame) :
    topLevelAmsterdam state msg frameOf =
      Jaune.processTopLevelAmsterdam state msg frameOf := rfl

/-- Trace the public Amsterdam top-level message operation. Preparation
failure returns its existing result without inventing an entered code frame;
transaction routing must still record that run's terminal outcome. -/
def runTopLevelAmsterdam {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (state : StateGasRules) (msg : Msg) (frameOf : Msg → Frame) (runId : String) :
    m (Certified (Jaune.processTopLevelAmsterdam state msg frameOf)) := do
  match hprep : prepareTopLevelAmsterdam state msg with
  | .error ⟨error, devm⟩ =>
    pure ⟨settleTopLevelPreparationFailure msg error devm, by
      simp only [← topLevelAmsterdam_eq, topLevelAmsterdam, hprep]⟩
  | .ok ⟨preparedMsg, devm⟩ =>
    let result ← runPreparedFrame sink (frameOf preparedMsg) devm runId
    let value : Except EvmError (State × MsgCallOutput) := do
      let evm ← Except.bimap Prod.fst id result.value
      messageOutputAmsterdam preparedMsg evm
    pure ⟨value, by
      simp only [← topLevelAmsterdam_eq, topLevelAmsterdam, hprep, value,
        result.erases]⟩

/-- The successful return of the actual monadic driver projects to the public
operation, including preparation errors and precompile/transfer boundaries. -/
theorem runTopLevelAmsterdam_erasure {state : StateGasRules} {msg : Msg}
    {frameOf : Msg → Frame}
    (result : Certified (Jaune.processTopLevelAmsterdam state msg frameOf)) :
    result.value = Jaune.processTopLevelAmsterdam state msg frameOf := result.erases

/-- Shared rendering of the pre-Amsterdam settled message result. The
transaction's authorization refund is separate from the frame-local counter. -/
def legacyOutput (authorizationRefund : Nat)
    (result : Except (EvmError × State × AdrSet × Tra) Devm) :
    Except EvmError (State × MsgCallOutput) := do
  let evm ← Except.bimap Prod.fst id result
  let refund ←
    if evm.error.isNone then
      (Int.toNat? evm.refundCounter).toExcept
        (EvmError.internal (.invariant (.text "refund counter is negative")))
    else .ok 0
  let logs := if evm.error.isNone then evm.logs else []
  let accountsToDelete :=
    if evm.error.isNone then evm.accountsToDelete else .emptyWithCapacity
  pure ⟨evm.state, {
    gasLeft := evm.gasLeft, refundCounter := authorizationRefund + refund,
    logs := logs, accountsToDelete := accountsToDelete,
    error := evm.error, returnData := evm.output }⟩

def runMessageCreate {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (msg : Msg) (runId : String) :
    m (Certified (Jaune.processMessageCall.create msg)) := do
  match hfork : msg.benv.stat.rules.stateGas with
  | some state =>
    let result ← runTopLevelAmsterdam sink state msg Frame.ofCreate runId
    pure ⟨result.value, by
      simpa only [Jaune.processMessageCall.create, hfork] using result.erases⟩
  | none =>
    if hcollision : accountHasCodeOrNonce msg.benv.state msg.currentTarget then
      pure ⟨.ok ⟨msg.benv.state, {
        gasLeft := 0, refundCounter := 0, logs := [],
        accountsToDelete := .emptyWithCapacity,
        error := some (.halt (.addressCollision .none)), returnData := [] }⟩, by
          simp only [Jaune.processMessageCall.create, hfork, hcollision, ↓reduceIte]
          rfl⟩
    else
      let result ← Trace.runFrame sink (Frame.ofCreate msg) runId
      pure ⟨legacyOutput 0 result.value, by
        simp [legacyOutput, result.erases, Jaune.processMessageCall.create,
          hfork, hcollision, Jaune.processCreateMessage]
        rfl⟩

/-- Authorization processing before the ordinary call frame. -/
def legacyAuthorization (msg : Msg) : Except EvmError (Msg × Nat) :=
  if msg.tenv.stat.auths.isEmpty then .ok ⟨msg, 0⟩ else do
    let ⟨delegated, refund⟩ ← setDelegation msg
    pure ⟨delegated, refund.toNat⟩

def resolveLegacyDelegation (msg : Msg) : Msg :=
  match getDelegatedCodeAddress msg.code with
  | none => msg
  | some address =>
    { msg with
      disablePrecompiles := true
      accessedAddresses := msg.accessedAddresses.insert address
      code := msg.benv.state.getCode address
      codeAddress := some address }

theorem legacyCall_eq (msg : Msg) (hfork : msg.benv.stat.rules.stateGas = none) :
    Jaune.processMessageCall.call msg =
      (legacyAuthorization msg >>= fun pair =>
        legacyOutput pair.2 (Jaune.processMessage (resolveLegacyDelegation pair.1))) := by
  simp only [Jaune.processMessageCall.call, hfork, legacyAuthorization,
    legacyOutput, resolveLegacyDelegation]
  split
  · rfl
  · cases setDelegation msg <;> rfl

def runMessageCall {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (msg : Msg) (runId : String) :
    m (Certified (Jaune.processMessageCall.call msg)) := do
  match hfork : msg.benv.stat.rules.stateGas with
  | some state =>
    let result ← runTopLevelAmsterdam sink state msg Frame.ofCall runId
    pure ⟨result.value, by
      simpa only [Jaune.processMessageCall.call, hfork] using result.erases⟩
  | none =>
    match hauth : legacyAuthorization msg with
    | .error error =>
      pure ⟨.error error, by
        rw [legacyCall_eq msg hfork, hauth]
        rfl⟩
    | .ok ⟨delegated, refund⟩ =>
      let result ← Trace.runFrame sink (Frame.ofCall (resolveLegacyDelegation delegated)) runId
      pure ⟨legacyOutput refund result.value, by
        rw [legacyCall_eq msg hfork, hauth]
        simp only [result.erases, Jaune.processMessage]
        rfl⟩

/-- Trace the exact message operation invoked by `processTransaction`. -/
def runMessage {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (msg : Msg) (runId : String) :
    m (Certified (Jaune.processMessageCall msg)) := do
  if htarget : msg.target.isNone then
    let result ← runMessageCreate sink msg runId
    pure ⟨result.value, by
      simpa [Jaune.processMessageCall, htarget] using result.erases⟩
  else
    let result ← runMessageCall sink msg runId
    pure ⟨result.value, by
      simpa [Jaune.processMessageCall, htarget] using result.erases⟩

/-- Values crossing the existing transaction's execution boundary. -/
structure PreparedTransaction where
  benv : Benv
  bout : BlockOutput
  sender : Adr
  effectiveGasPrice : Nat
  txBlobGasUsed : Nat
  calldataFloorGasCost : Nat
  msg : Msg

def prepareTransaction (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) :
    Except TransitionError PreparedTransaction := do
  let benv := benv.beginTransaction
  let bout ← .ok {bout with
    transactionsTrie := bout.transactionsTrie.insert (BLT.bytes index.toBytes).toBytes tx}
  let validationSender : Adr ← recoverValidationSender benv tx
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
    if tx.isTypeThree
    then calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
    else 0
  let effectiveGasFee := tx.gas * effectiveGasPrice
  let allocation := allocateEvmGas benv.stat.rules tx.gas intrinsicGas
  let state : State := benv.state.incrNonce sender
  let state ← (state.subBal sender (effectiveGasFee + blobGasFee).toB256).toExcept
    (TransitionError.internal (.invariant (.text "balance underflow")))
  let preaccessedAddresses : AdrSet :=
    .ofList (benv.stat.coinbase :: tx.accessList.map Prod.fst)
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
      auths := tx.auths
      indexInBlock := index
      txHash := getTxHash tx
    }
  }
  let msg ← prepareMessage {benv with state := state} tenv tx
  pure ⟨benv, bout, sender, effectiveGasPrice, txBlobGasUsed, calldataFloorGasCost, msg⟩

def finishTransaction (prepared : PreparedTransaction) (tx : Tx) (index : Nat)
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
    settleTransactionGas benv.stat.rules tx.gas calldataFloorGasCost
      txOutput.gasLeft txOutput.stateGasLeft refundCounter txOutput.stateGasUsed
  let gasRefundAmount : Nat :=
    settlement.gasLeft * effectiveGasPrice
  let priorityFeePerGas := effectiveGasPrice - benv.stat.baseFeePerGas
  let transactionFee := settlement.gasUsed * priorityFeePerGas
  let state := state.addBal sender gasRefundAmount.toB256
  let storageWrites :=
    if (state.get sender).Empty then txOutput.storageWrites.eraseAddress sender
    else txOutput.storageWrites
  let state := state.addBal benv.stat.coinbase transactionFee.toB256
  let storageWrites :=
    if (state.get benv.stat.coinbase).Empty then storageWrites.eraseAddress benv.stat.coinbase
    else storageWrites
  let storageWrites := txOutput.accountsToDelete.toList.foldl
    (fun writes a => writes.eraseAddress a) storageWrites
  let state := settleSelfdestructs benv.stat.rules
    txOutput.accountsToDelete.toList state
  let bout ← .ok (bout.withGasSettlement settlement txBlobGasUsed)
  let receipt :=
    makeReceipt tx txOutput.error bout.cumulativeGasUsed txOutput.logs
  let receiptKey : Bytes := BLT.toBytes <| .bytes index.toBytes
  let bout ← .ok {bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie := bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ txOutput.logs}
  -- EIP-7928: `incorporate_tx_into_block` at `index + 1`, after the
  -- self-destruct settlement: surviving explicit storage writes and account
  -- changes, plus reads and the transaction-level ones --
  -- the sender (`check_transaction`, `update_sender_state`, the refund) and
  -- the coinbase (`disburse_gas_fees` credits it even a zero fee).
  let bal := match benv.stat.rules.bal with
    | none => bout.bal
    | some _ => bout.bal.incorporate (index + 1) benv.state state
        (sender :: benv.stat.coinbase :: txOutput.accountReads.toList)
        txOutput.storageReads.toList storageWrites.toList
  .ok ⟨state, {bout with bal := bal}⟩

/-- The local preparation/settlement split is exactly the public pipeline. -/
theorem processTransaction_eq (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) :
    Jaune.processTransaction benv bout tx index = (do
      let prepared ← prepareTransaction benv bout tx index
      let ⟨state, output⟩ ← Except.mapError TransitionError.vm (Jaune.processMessageCall prepared.msg)
      finishTransaction prepared tx index state output) := by
  simp only [Jaune.processTransaction, prepareTransaction, finishTransaction,
    bind_assoc, pure_bind]
  rfl

/-- Transaction result plus the observed message output needed by a trace
summary. A validation/preparation rejection can have no message output. -/
structure TransactionResult (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat)
    extends Certified (Jaune.processTransaction benv bout tx index) where
  messageOutput : Option MsgCallOutput

/-- Execute one real transaction with synchronous instruction observations.
Validation, fee/nonce preparation, message execution, gas/receipt settlement,
SELFDESTRUCT and block-access bookkeeping are connected to the public pipeline
by the certificate. The original transaction executor is never run a second time. -/
def runTransaction {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) (runId : String) :
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
    let message ← runMessage sink prepared.msg runId
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
theorem runTransaction_erasure {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (result : TransactionResult benv bout tx index) :
    result.value = Jaune.processTransaction benv bout tx index := result.erases

theorem runTransaction_id_erasure (sink : Trace.Sink Id) (benv : Benv)
    (bout : BlockOutput) (tx : Tx) (index : Nat) (runId : String) :
    (runTransaction sink benv bout tx index runId).value =
      Jaune.processTransaction benv bout tx index :=
  (runTransaction sink benv bout tx index runId).erases

end Jaune.TraceTransaction
