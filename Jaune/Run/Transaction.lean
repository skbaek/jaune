import Jaune.Run.Message

/-!
# The transaction in phases (goal `jaune-shape-and-names-v1`, W2 cut A)

A transaction runs in four phases:

1. `Transaction.check`: begin the transaction, enter it in the block's transaction trie, and run
   the admission checks (`recoverValidationSender`, `validateTransaction`, `checkTransaction`).
2. `Transaction.prepare`: charge the fee and bump the sender's nonce, build the transaction
   environment and the top-level message (`prepareMessage`).
3. The top-level message call (`processMessageCall`, the run of `Jaune.Run.Message`).
4. `Transaction.settle`: refund the sender, pay the coinbase, apply the deletions and the sweep,
   write the receipt and incorporate the block access list, in today's order.

`processTransaction` is their composition. This split was a local copy in the tracer
(`TraceTransaction.prepareTransaction`/`finishTransaction`); here it is the definition. Also here,
public: the transaction validators and block-access-list helpers whose earlier copies in
`Jaune.Transaction` were private, and `stateTransitionUsing_run`. Staged under `Jaune.Staging`
until the switch commit; the bridges are in `Jaune.Bridge.G2a.Run`.
-/

namespace Jaune.Staging

open Jaune

/-! ### Transaction validators, public -/

/-- Enforce an optional transaction gas cap. -/
def checkTransactionGasLimit (limit : Option Nat) (gas : Nat) :
    Except TxValidationError Unit :=
  match limit with
  | none => .ok ()
  | some maxGas =>
    if gas > maxGas then
      .error <| .transactionGasLimitExceeded <| .text
        s!"transaction gas = {gas} > \
           maximum = {maxGas}"
    else
      .ok ()

/-- A dynamic-fee transaction's priority fee is at most its maximum fee. -/
def checkTransactionPriorityFeeRelation (tx : Transaction) :
    Except TxValidationError Unit :=
  let check (priorityFee maxFee : Nat) :=
    if maxFee < priorityFee then
      .error <| .priorityGreaterThanMaxFee <| .text
        s!"priority fee = {priorityFee} > max fee = {maxFee}"
    else .ok ()
  match tx.type with
  | .eip1559 _ priorityFee maxFee _ _
  | .eip4844 _ priorityFee maxFee _ _ _ _
  | .eip7702 _ priorityFee maxFee _ _ _ => check priorityFee maxFee
  | _ => .ok ()

/-- A blob transaction carries at least one blob, within the fork's count, each hash with the KZG
version byte. -/
def checkTransactionBlobShape (rules : ForkRules) (tx : Transaction) :
    Except TxValidationError Unit := do
  match tx.type with
  | .eip4844 _ _ _ _ _ _ blobHashes =>
    if blobHashes.isEmpty then
      .error <| .type3ZeroBlobs <| .text "no blob hashes in type-3 transaction"
    checkTransactionBlobCount rules.tx blobHashes
    if List.any blobHashes
        (fun hash => hash.toBytes.head? ≠ some versionedHashVersionKzg) then
      .error <| .type3InvalidBlobVersionedHash <| .text
        s!"a blob versioned hash has a version byte other than \
           {versionedHashVersionKzg}"
  | _ => .ok ()

/-! ### Block-access-list helpers, public -/

/-- Replace the entry at `idx` or append: only the final value per index is kept
(`add_storage_write`, `add_balance_change`, `add_code_change`). -/
def BlockAccessListAccount.upsert {α : Type} (l : List (Nat × α)) (idx : Nat) (v : α) :
    List (Nat × α) :=
  if l.any (·.1 = idx) then l.map (fun c => if c.1 = idx then (idx, v) else c)
  else l ++ [(idx, v)]

/-- The value a slot had at the start of block-access index `idx`: captured on first visit. -/
def BlockAccessListBuilder.startStorage (b : BlockAccessListBuilder) (idx : Nat)
    (address : Address) (slot value : U256) : BlockAccessListBuilder × U256 :=
  let atIndex := b.indexStartStorage.getD idx .empty
  let atAddress := atIndex.getD address .empty
  match atAddress.get? slot with
  | some start => (b, start)
  | none =>
    let atAddress := atAddress.insert slot value
    let atIndex := atIndex.insert address atAddress
    ({b with indexStartStorage := b.indexStartStorage.insert idx atIndex}, value)

/-! ### The configured block transition -/

/-- A configured block transition that succeeds found the active fork and the scheduled
transition's success. -/
theorem stateTransitionUsing_run {cfg : ChainConfig} {ch ch' : BlockChain}
    {block : Block} (h : stateTransitionUsing cfg ch block = .ok ch') :
    ∃ f, cfg.forkAt block.header.number block.header.timestamp = .ok f ∧
      stateTransitionScheduledE cfg f ch block = .ok (.ok ch') := by
  unfold stateTransitionUsing at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨f, hf, h⟩ := Except.bind_eq_ok h
  refine ⟨f, Except.mapError_eq_ok_iff.mp hf, ?_⟩
  cases hs : stateTransitionScheduledE cfg f ch block with
  | error e => rw [hs] at h; cases h
  | ok r =>
    rw [hs] at h
    have hr : r = .ok ch' := Except.mapError_eq_ok_iff.mp h
    rw [hr]

/-! ### The phases -/

/-- What a transaction's admission checks establish. -/
structure Transaction.Checked : Type where
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
def Transaction.check (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Except TransitionError Transaction.Checked := do
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
def Transaction.prepare (checked : Transaction.Checked) (tx : Transaction) (index : Nat) :
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
      txHash := getTxHash tx
    }
  }
  let msg ← prepareMessage {benv with state := state} tenv tx
  pure ⟨benv, checked.bout, sender, effectiveGasPrice, checked.txBlobGasUsed,
    checked.calldataFloorGasCost, msg⟩

/-- Settle a transaction after its message call: refund the sender, pay the coinbase, erase the
writes of emptied and deleted accounts, settle the self-destructs, sweep the touched empty
accounts, then record the gas, the receipt and the logs, and incorporate the block access list at
`index + 1`. -/
def Transaction.settle (prepared : Transaction.Prepared) (tx : Transaction) (index : Nat)
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

/-- One transaction: check, prepare, the top-level message call, settle. -/
def processTransaction (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Except TransitionError (State × BlockOutput) := do
  let checked ← Transaction.check benv bout tx index
  let prepared ← Transaction.prepare checked tx index
  let ⟨state, output⟩ ← Except.mapError TransitionError.vm (processMessageCall prepared.msg)
  Transaction.settle prepared tx index state output

end Jaune.Staging
