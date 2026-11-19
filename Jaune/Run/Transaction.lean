import Jaune.Run.Message

/-!
# Transaction admission and preparation

`Transaction.admit` begins the transaction, inserts it into the block's
transaction trie, and runs the admission checks. `Transaction.prepare`
charges the fee, increments the sender's nonce, and builds the transaction
environment and top-level message. `Jaune.Run.Settle` composes these phases
with message execution and transaction settlement.
-/

namespace Jaune

open Jaune

/-! ### The phases -/

/-- What a transaction's admission checks establish. -/
structure Transaction.Admitted : Type where
  /-- The block environment with the transaction begun. -/
  benv : Benv
  /-- The block output with the transaction entered in the transaction trie. -/
  bout : BlockOutput
  sender : Address
  effectiveGasPrice : Nat
  blobVersionedHashes : List U256
  txBlobGasUsed : Nat
  intrinsicGas : Nat
  calldataFloorGasCost : Nat

/-- Begin the transaction, enter it in the transaction trie (before validation, as the trie
counts every candidate), and run the admission checks. -/
def Transaction.admit (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Except TransitionError Transaction.Admitted := do
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
  pure ⟨benv, bout, sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed, intrinsicGas,
    calldataFloorGasCost⟩

/-- What crosses from a prepared transaction to its settlement: the checked environment and
output, the values settlement reads, and the top-level message. -/
structure Transaction.Prepared : Type where
  benv : Benv
  bout : BlockOutput
  sender : Address
  effectiveGasPrice : Nat
  txBlobGasUsed : Nat
  calldataFloorGasCost : Nat
  msg : Msg

/-- Charge the fee and bump the sender's nonce, then build the transaction environment and the
top-level message. -/
def Transaction.prepare (checked : Transaction.Admitted) (tx : Transaction) (index : Nat) :
    Except TransitionError Transaction.Prepared := do
  let benv := checked.benv
  let sender := checked.sender
  let effectiveGasPrice := checked.effectiveGasPrice
  let blobGasFee :=
    if tx.isEip4844
    then calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
    else 0
  let effectiveGasFee := tx.gasLimit * effectiveGasPrice
  let allocation := allocateEvmGas benv.stat.rules tx.gasLimit checked.intrinsicGas
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
      blobVersionedHashes := checked.blobVersionedHashes
      auths := tx.authorizationList
      indexInBlock := index
      txHash := transactionHash tx
    }
  }
  let msg ← prepareMessage {benv with state := state} tenv tx
  pure ⟨benv, checked.bout, sender, effectiveGasPrice, checked.txBlobGasUsed,
    checked.calldataFloorGasCost, msg⟩



end Jaune
