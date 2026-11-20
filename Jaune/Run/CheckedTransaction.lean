import Jaune.Run.CheckedMessage
import Jaune.Run.Prefix
import Jaune.Run.Body

namespace Jaune.Checked

open Jaune

/-! ### The block record and transaction admission

Decision 13 at the runner: a block is run against its `BlockContext` and the state of the body's
prefix; the state a transaction starts on is passed explicitly and becomes the transaction
record's `originalState`. Nothing here carries a block environment. -/

/-- The block record a block's frames read, from its fork, its parent chain and its header. -/
def initBlockContext (fork : Fork) (chain : BlockChain) (header : Header) : BlockContext :=
  { fork
    chainId := chain.chainId
    gasLimit := header.gasLimit
    blockHashes := BlockChain.recentBlockHashes chain
    coinbase := header.coinbase
    number := header.number
    -- Absent before London and Cancun respectively, where nothing that reads them is reachable.
    baseFeePerGas := header.baseFeePerGas.getD 0
    timestamp := header.timestamp.toU256
    -- Before the merge `DIFFICULTY` reads the header's difficulty instead of `prevRandao`.
    prevRandao :=
      match fork.ruleSet.proofOfWork with
      | some _ => Nat.toU256 header.difficulty
      | none => header.prevRandao
    excessBlobGas := header.excessBlobGas.getD 0
    parentBeaconBlockRoot := header.parentBeaconBlockRoot.getD 0
    slotNumber := header.slotNumber.getD 0 }

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

/-- A blob transaction's hashes, their count and versions, and its blob fee cap. -/
def checkTransactionBlobData (block : BlockContext) (tx : Jaune.Transaction) (maxGasFee : Nat) :
    Except TransactionValidationError (Nat × List U256) :=
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

/-- The whole admission check against the block and the transaction-start state. -/
def checkTransaction (block : BlockContext) (state : State) (blockOut : BlockOutput)
    (tx : Jaune.Transaction) : Except TransitionError (Address × Nat × List U256 × Nat) := do
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

/-- The sender the Amsterdam intrinsic-cost formula needs before `checkTransaction` runs; the chain
identifier is compared first, as the pinned `process_transaction` does. -/
def recoverValidationSender (block : BlockContext) (tx : Jaune.Transaction) :
    Except TransitionError Address :=
  match block.rules.stateGas with
  | none => .ok 0
  | some _ => do
    Except.mapError TransitionError.transaction (checkTransactionChainId block tx)
    Except.mapError (fun e => TransitionError.senderRecovery e) (recoverSender block.chainId tx)

/-- What a transaction's admission checks establish. -/
structure Transaction.Admitted where
  /-- The block output with the transaction entered in the transaction trie. -/
  bout : BlockOutput
  sender : Address
  effectiveGasPrice : Nat
  blobVersionedHashes : List U256
  txBlobGasUsed : Nat
  intrinsicGas : Nat
  calldataFloorGasCost : Nat

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
    (admitted : Transaction.Admitted) (tx : Jaune.Transaction) :
    Except TransitionError Transaction.Prepared := do
  let sender := admitted.sender
  let effectiveGasPrice := admitted.effectiveGasPrice
  let rules := block.rules
  let blobGasFee :=
    if tx.isEip4844 then calculateDataFee rules.blob block.excessBlobGas tx else 0
  let effectiveGasFee := tx.gasLimit * effectiveGasPrice
  let allocation := allocateEvmGas rules tx.gasLimit admitted.intrinsicGas
  let state := originalState.incrNonce sender
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
  let world : World := ⟨state, .empty, .emptyWithCapacity⟩
  let checkpoint := message.initialCheckpoint world accessedAddresses accessedStorageKeys
    .emptyWithCapacity .emptyWithCapacity
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
def Transaction.settleRun (admitted : Transaction.Admitted) (prepared : Transaction.Prepared)
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

/-- Admit, prepare, execute and settle a signed transaction through the Checked message entry.
The transaction starts on `state`, which becomes its original state. -/
def Transaction.run (block : BlockContext) (state : State) (bout : BlockOutput) (tx : Jaune.Transaction)
    (index : Nat) : Except TransitionError (TransactionRun × BlockOutput) := do
  let admitted ← admit block state bout tx index
  let prepared ← prepare block state admitted tx
  let message ← (TopLevel.runNative prepared.input).mapError
    (fun fault => TransitionError.vm fault.toEvmError)
  settleRun admitted prepared tx index message

/-- Request-producing calls require code and a successful settlement. -/
def processCheckedSystemRun (block : BlockContext) (state : State)
    (target : Address) (data : Bytes) : Except TransitionError SystemRun := do
  let code := state.getCode target
  if code.isEmpty then
    .error <| .block <| .systemContractEmpty <| .text
      s!"system contract address {target.toHex} holds no code"
  let run ← (processSystemRun block state target code data).mapError
    (fun fault => TransitionError.vm fault.toEvmError)
  match run.settlement.error with
  | some halt => .error <| .block <| .systemContractCallFailed target halt
  | none => .ok run

def processCheckedSystemTransaction (block : BlockContext) (state : State)
    (target : Address) (data : Bytes) : Except TransitionError TopLevel.Settlement :=
  (processCheckedSystemRun block state target data).map SystemRun.settlement

/-- What one accepted operation records, beside its next prefix. -/
inductive OpRun where
  | systemCall (index : Nat) (address : Address) (run : SystemRun)
  | transaction (run : TransactionRun)
  | withdrawals (index : Nat) (ws : List Withdrawal)
  | depositRequests (requests : Bytes)
  | requestCall (index : Nat) (type : UInt8) (address : Address) (run : SystemRun)
  | rewards (coinbase : Address) (minerReward : Nat) (credits : List (Address × Nat))
  | buildAccessList (list : BlockAccessList)
  | checkAccessListLimit

namespace Body

/-- Execute one operation from the prefix state, in the block `block`. The streaming runner
discards the operation record, while the recording runner keeps it. -/
@[inline] def stepWith {α : Type} (observe : OpRun → Jaune.Body.Prefix → α)
    (block : BlockContext) (p : Jaune.Body.Prefix) : BodyOp → Except TransitionError α
  | .systemCall address data index => do
    let data ← data
    let message ← (processSystemRun block p.state address (p.state.getCode address) data).mapError
      (fun fault => TransitionError.vm fault.toEvmError)
    let run := message.settlement
    pure <| observe (.systemCall index address message) { p with
      state := run.state
      blockAccessListBuilder := p.blockAccessListBuilder.incorporateSystem block.rules index p.state run.state
        (address :: run.accountReads.toList) run.storageReads.toList run.storageWrites.toList }
  | .transaction tx index => do
    let (run, bout) ← Transaction.run block p.state p.toBlockOutput tx index
    pure <| observe (.transaction run) (Jaune.Body.Prefix.ofBlockOutput run.state bout)
  | .withdrawals ws index =>
    let state := processWithdrawalsState p.state ws
    pure <| observe (.withdrawals index ws) { p with
      state
      withdrawalsTrie := processWithdrawalsTrie p.withdrawalsTrie ws
      blockAccessListBuilder := p.blockAccessListBuilder.incorporateSystem block.rules index p.state state
        (ws.map Withdrawal.address) [] [] }
  | .depositRequests => do
    let deposits ← parseDepositRequests p.toBlockOutput
    pure <| observe (.depositRequests deposits) { p with
      requests := if deposits.length > 0 then p.requests ++ [depositRequestType ++ deposits] else p.requests }
  | .requestCall type address index => do
    let message ← processCheckedSystemRun block p.state address []
    let run := message.settlement
    pure <| observe (.requestCall index type address message) { p with
      state := run.state
      requests := if run.returnData.length > 0 then p.requests ++ [[type] ++ run.returnData] else p.requests
      blockAccessListBuilder := match block.rules.blockAccessListRules with
        | none => p.blockAccessListBuilder
        | some _ => p.blockAccessListBuilder.incorporate index p.state run.state
            (address :: run.accountReads.toList) run.storageReads.toList run.storageWrites.toList }
  | .rewards coinbase minerReward credits =>
    pure <| observe (.rewards coinbase minerReward credits)
      { p with state := creditAll credits (p.state.addBal coinbase minerReward.toU256) }
  | .buildAccessList =>
    let list := match block.rules.blockAccessListRules with
      | none => []
      | some _ => p.blockAccessListBuilder.build
    pure <| observe (.buildAccessList list) { p with blockAccessList := list }
  | .checkAccessListLimit => do
    checkBlockAccessListGasLimit block.rules block.gasLimit p.blockAccessList
    pure (observe .checkAccessListLimit p)

/-- The streaming step holds only the next prefix. -/
def step (block : BlockContext) (p : Jaune.Body.Prefix) (op : BodyOp) :
    Except TransitionError Jaune.Body.Prefix :=
  stepWith (fun _ next => next) block p op

/-- Keep the record of the same operation executed by the streaming step. -/
def stepRun (block : BlockContext) (p : Jaune.Body.Prefix) (op : BodyOp) :
    Except TransitionError (OpRun × Jaune.Body.Prefix) :=
  stepWith Prod.mk block p op

theorem stepRun_prefix (block : BlockContext) (p : Jaune.Body.Prefix) (op : BodyOp) :
    (stepRun block p op).map Prod.snd = step block p op := by
  cases op <;> simp only [stepRun, step, stepWith]
  case systemCall address data index =>
    cases data with
    | error => rfl
    | ok bytes =>
      simp only [bind, Except.bind]
      cases processSystemRun block p.state address (p.state.getCode address) bytes <;> rfl
  case transaction tx index =>
    cases Transaction.run block p.state p.toBlockOutput tx index <;> rfl
  case depositRequests => cases parseDepositRequests p.toBlockOutput <;> rfl
  case requestCall type address index =>
    cases processCheckedSystemRun block p.state address [] <;> rfl
  case checkAccessListLimit =>
    cases checkBlockAccessListGasLimit block.rules block.gasLimit p.blockAccessList <;> rfl
  all_goals rfl

/-- The executed operations in order, together with their final prefix. -/
def run (block : BlockContext) : Jaune.Body.Prefix → List BodyOp →
    Except TransitionError (List OpRun × Jaune.Body.Prefix)
  | p, [] => .ok ([], p)
  | p, op :: ops => do
    let (record, next) ← stepRun block p op
    let (records, final) ← run block next ops
    pure (record :: records, final)

/-- The importer's pre-execution system calls at index 0: the beacon-roots call (EIP-4788) when
`systemCalls.beaconRoots`, then the history-storage call (EIP-2935) when
`systemCalls.historyStorage`, whose data is the parent hash (an empty window is an internal
fault). -/
def preOps (block : BlockContext) : List BodyOp :=
  let rules := block.rules
  (if rules.systemCalls.beaconRoots then
    [.systemCall beaconRootsAddress (.ok block.parentBeaconBlockRoot.toBytes) 0]
  else []) ++
  (if rules.systemCalls.historyStorage then
    [.systemCall historyStorageAddress
      ((block.blockHashes.getLast?.toExcept
        (TransitionError.internal (.invariant (.text "block hashes is empty")))).map
          (·.toBytes)) 0]
  else [])

/-- The withdrawals at `index`, when the header commits to them. -/
def withdrawalOps (block : BlockContext) (index : Nat) (withdrawals : List Withdrawal) : List BodyOp :=
  if block.rules.header.withdrawalsRoot then [.withdrawals withdrawals index] else []

/-- Deposit requests follow the receipts, followed by configured request-producing calls. -/
def requestOps (block : BlockContext) (index : Nat) : List BodyOp :=
  if block.rules.header.requestsHash then
    .depositRequests :: block.rules.requests.map fun ⟨kind, address⟩ => .requestCall kind address index
  else []

/-- The proof-of-work rewards, then the access-list build and its item limit. -/
def finishOps (block : BlockContext) (ommers : List Header) : List BodyOp :=
  (match block.rules.proofOfWork with
   | none => []
   | some pow =>
     [.rewards block.coinbase (pow.blockReward + ommers.length * (pow.blockReward / 32))
       (ommers.map fun ommer =>
         (ommer.coinbase, (8 + ommer.number - block.number) * pow.blockReward / 8))]) ++
  [.buildAccessList, .checkAccessListLimit]

/-- The importer's post-execution operations, for `n` transactions. -/
def postOps (block : BlockContext) (n : Nat) (ommers : List Header) (wds : List Withdrawal) :
    List BodyOp :=
  withdrawalOps block (n + 1) wds ++ (requestOps block (n + 1) ++ finishOps block ommers)

/-- The importer's operations for the decoded transactions. -/
def ops (block : BlockContext) (txs : List Jaune.Transaction) (ommers : List Header)
    (wds : List Withdrawal) : List BodyOp :=
  preOps block ++ Jaune.Body.transactionOps txs ++ postOps block txs.length ommers wds

/-- Decode before executing the importer operations, including pre-execution system calls, from
the empty prefix over the block's prestate. -/
def importer (block : BlockContext) (state : State) (txs : List (Bytes ⊕ Jaune.Transaction))
    (ommers : List Header) (wds : List Withdrawal) : Except TransitionError Jaune.Body.Prefix := do
  let decoded ← txs.mapM (decodeTransaction block.rules)
  (ops block decoded ommers wds).foldlM (step block) (Jaune.Body.Prefix.init state)

end Body

/-- The importer's body with the result type of `apply_body`: the final prefix's state and
block output. -/
def applyBody (block : BlockContext) (state : State) (txs : List (Bytes ⊕ Jaune.Transaction))
    (ommers : List Header) (wds : List Withdrawal) : Except TransitionError (State × BlockOutput) :=
  Jaune.Body.Prefix.output <$> Body.importer block state txs ommers wds

/-- A block's decoded transactions and ordered Checked operations over its parent. -/
structure BlockRun where
  fork : Fork
  parent : BlockChain
  block : Block
  transactions : List Jaune.Transaction
  ops : List OpRun
  final : Jaune.Body.Prefix

/-- The block record the run's frames read. -/
def BlockRun.context (run : BlockRun) : BlockContext :=
  initBlockContext run.fork run.parent run.block.header

def BlockRun.run (fork : Fork) (parent : BlockChain) (block : Block) : Except TransitionError BlockRun := do
  let context := initBlockContext fork parent block.header
  let decoded ← block.transactions.mapM (decodeTransaction context.rules)
  let (ops, final) ← Body.run context (Jaune.Body.Prefix.init parent.state)
    (Body.ops context decoded block.ommers block.withdrawals)
  pure ⟨fork, parent, block, decoded, ops, final⟩

/-- Validate the header and ommers, execute the Checked body, then check its commitments. -/
def stateTransitionCoreE {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) :
    Except ε BlockChain := do
  Except.mapError embed (validateHeader f.ruleSet ch block.header)
  checkOmmers ()
  let q ← Except.mapError embed
    (Body.importer (initBlockContext f ch block.header) ch.state block.transactions block.ommers
      block.withdrawals)
  Except.mapError (embed ∘ TransitionError.block) <|
    Block.check block.header (Block.Commitments.ofPrefix f.ruleSet q)
  .ok ⟨appendBlock ch.blocks block, q.state, ch.chainId⟩

end Jaune.Checked
