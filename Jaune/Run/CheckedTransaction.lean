import Jaune.MessageCall.CheckedContext
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

end Jaune.Checked
