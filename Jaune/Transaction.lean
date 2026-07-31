import Jaune.Sufficiency
-- `List.IsChain` itself is Batteries; its infix/suffix closure lemmas, which
-- the retained-history predicate below reasons with, are Mathlib's.
import Mathlib.Data.List.Chain

namespace Jaune

open Jaune

/-!
# Transaction, block, and chain processing

This module holds every declaration that consumes the interpreter driver
defined in `Jaune.Execution`, starting at `processMessageCall.create`, together
with the transaction, block, and chain-level machinery built on top of it. It
was split out of `Jaune.Execution` verbatim so that `Jaune.Sufficiency` can sit
between the driver and its first consumer.
-/

/- `private` declarations do not cross module boundaries, so the two `#guard`
helpers that the moved text shares with `Jaune.Execution` are restated here
rather than being made public. Keep them in step with their counterparts at
`Jaune/Execution.lean:1219`. -/

private def errOf {α : Type} : Except String α → String
  | .error e => e
  | .ok _ => "unexpected success"

private def hasTag {α : Type} (tag : String) (e : Except String α) : Bool :=
  hasErrorType (errOf e) tag

def processMessageCall.create (msg : Msg) :
  Except String (State × MsgCallOutput) := do
  let benv := msg.benv
  let isCollision : Bool :=
    accountHasCodeOrNonce benv.state msg.currentTarget || accountHasStorage benv.state msg.currentTarget
  if isCollision then
    return ⟨benv.state, ⟨0, 0, [], .emptyWithCapacity, "AddressCollision", []⟩⟩
  else
    let evm ← Except.bimap (fun e => EvmError.render e.1) id (processCreateMessage msg)
    let logs := if evm.error.isNone then evm.logs else []
    let accountsToDelete := if evm.error.isNone then evm.accountsToDelete else .emptyWithCapacity
    let refundCounter ←
      if evm.error.isNone then
       (Int.toNat? evm.refundCounter).toExcept "ERROR : refund counter is negative"
      else
        .ok 0
    .ok ⟨
      evm.state,
      {
        gasLeft := evm.gasLeft,
        refundCounter := refundCounter
        logs := logs,
        accountsToDelete := accountsToDelete,
        error := evm.error,
        returnData := evm.output
      }
    ⟩

def processMessageCall.call (msg : Msg) :
  Except String (State × MsgCallOutput) := do
  let (⟨msgDelegation, refundDelegation⟩ : Msg × Nat) ←
    if msg.tenv.stat.auths.isEmpty then
      .ok (⟨msg, 0⟩ : Msg × Nat)
    else do
      let ⟨msgDelegation, setDelegationValue⟩ ← setDelegation msg
      .ok ⟨msgDelegation, setDelegationValue.toNat⟩
  let msgPc :=
    match getDelegatedCodeAddress msgDelegation.code with
    | none => msgDelegation
    | some dca =>
      {
        msgDelegation with
        disablePrecompiles := true,
        accessedAddresses := msgDelegation.accessedAddresses.insert dca,
        code := msgDelegation.benv.state.getCode dca,
        codeAddress := some dca
      }
  let evm ← Except.bimap (fun e => EvmError.render e.1) id (processMessage msgPc)
  let refundProcessMessage ←
    if evm.error.isNone then
      (Int.toNat? evm.refundCounter).toExcept "ERROR : refund counter is negative"
    else
      .ok 0
  let logs := if evm.error.isNone then evm.logs else []
  let accountsToDelete := if evm.error.isNone then evm.accountsToDelete else .emptyWithCapacity
  .ok ⟨
    evm.state,
    {
      gasLeft := evm.gasLeft,
      refundCounter := refundDelegation + refundProcessMessage
      logs := logs,
      accountsToDelete := accountsToDelete,
      error := evm.error,
      returnData := evm.output
    }
  ⟩

def processMessageCall (msg : Msg) :
    Except String (State × MsgCallOutput) := do
  if msg.target.isNone then
    processMessageCall.create msg
  else
    processMessageCall.call msg

def Tx.isTypeThree (tx : Tx) : Bool :=
  match tx.type with
  | .three _ _ _ _ _ _ _ => true
  | _ => false

def calculateTotalBlobGas (tx: Tx) : Nat :=
  match tx.type with
  | .three _ _ _ _ _ _ blobHashes => gasPerBlob * blobHashes.length
  | _ => 0

structure Receipt : Type where
  succeeded : Bool
  gasUsed : Nat
  bloom : Bytes
  logs : List Log

structure BlockOutput : Type where
  blockGasUsed : Nat
  transactionsTrie : Std.TreeMap Bytes Tx compare
  receiptsTrie : Std.TreeMap Bytes (Fin 5 × Receipt) compare
  receiptKeys : List Bytes
  blockLogs : List Log
  withdrawalsTrie : Std.TreeMap Bytes Withdrawal compare
  blobGasUsed : Nat
  requests : List Bytes

-- The following helpers keep the checks in the same order, with the same
-- returned payloads and error strings, as the monolithic transaction checker.
-- Splitting the executable stages makes successful runs easier to invert in
-- proofs without unfolding the whole checker at once.

def checkTransactionGasLimits
    (benv : Benv) (blockOut : BlockOutput) (tx : Tx) :
    Except String Nat :=
  let gasAvailable := benv.stat.blockGasLimit - blockOut.blockGasUsed
  let blobGasAvailable := benv.stat.rules.blob.max - blockOut.blobGasUsed
  if tx.gas > gasAvailable then
    .error
      s!"{gasAllowanceExceededTag} : transaction gas = {tx.gas} > \
         block gas available = {gasAvailable}"
  else
    let txBlobGasUsed := calculateTotalBlobGas tx
    if txBlobGasUsed > blobGasAvailable then
      .error
        s!"{type3BlobCountExceededTag} : blob gas used = {txBlobGasUsed} > \
           blob gas available = {blobGasAvailable}"
    else
      .ok txBlobGasUsed

def checkTransactionDynamicGasFee
    (baseFeePerGas gas maxPriorityFee maxFee : Nat) :
    Except String (Nat × Nat) :=
  if maxFee < maxPriorityFee then
    .error
      s!"{priorityGreaterThanMaxFeeTag} : priority fee = {maxPriorityFee} > \
         max fee = {maxFee}"
  else if maxFee < baseFeePerGas then
    .error
      s!"{insufficientMaxFeePerGasTag} : max fee = {maxFee} < \
         base fee = {baseFeePerGas}"
  else
    let maxGasFee := gas * maxFee
    if maxGasFee > B256.max.toNat then
      .error
        s!"{gasPriceProductOverflowTag} : gas * max fee = {maxGasFee} > \
           2^256 - 1"
    else
      let priorityFeePerGas := min maxPriorityFee (maxFee - baseFeePerGas)
      .ok ⟨priorityFeePerGas + baseFeePerGas, maxGasFee⟩

def checkTransactionLegacyGasFee
    (baseFeePerGas gas gasPrice : Nat) :
    Except String (Nat × Nat) :=
  if gasPrice < baseFeePerGas then
    .error
      s!"{insufficientMaxFeePerGasTag} : gas price = {gasPrice} < \
         base fee = {baseFeePerGas}"
  else
    let maxGasFee := gas * gasPrice
    if maxGasFee > B256.max.toNat then
      .error
        s!"{gasPriceProductOverflowTag} : gas * gas price = {maxGasFee} > \
           2^256 - 1"
    else
      .ok ⟨gasPrice, maxGasFee⟩

def checkTransactionGasFee (benv : Benv) (tx : Tx) :
    Except String (Nat × Nat) :=
  match tx.type with
  | .zero gasPrice _ =>
    checkTransactionLegacyGasFee benv.stat.baseFeePerGas tx.gas gasPrice
  | .one _ gasPrice _ _ =>
    checkTransactionLegacyGasFee benv.stat.baseFeePerGas tx.gas gasPrice
  | .two _ maxPriorityFee maxFee _ _ =>
    checkTransactionDynamicGasFee benv.stat.baseFeePerGas tx.gas
      maxPriorityFee maxFee
  | .three _ maxPriorityFee maxFee _ _ _ _ =>
    checkTransactionDynamicGasFee benv.stat.baseFeePerGas tx.gas
      maxPriorityFee maxFee
  | .four _ maxPriorityFee maxFee _ _ _ =>
    checkTransactionDynamicGasFee benv.stat.baseFeePerGas tx.gas
      maxPriorityFee maxFee

/-- Enforce the fork's per-transaction blob-count limit, when one is active. -/
def checkTransactionBlobCount (limits : TransactionLimits)
    (blobHashes : List B256) : Except String Unit :=
  match limits.maxBlobCount with
  | none => .ok ()
  | some maxBlobCount =>
    if blobHashes.length > maxBlobCount then
      .error
        s!"{type3BlobCountLimitExceededTag} : transaction has \
           {blobHashes.length} blobs > maximum = {maxBlobCount}"
    else
      .ok ()

def checkTransactionBlobData
    (benv : Benv) (tx : Tx) (maxGasFee : Nat) :
    Except String (Nat × List B256) :=
  match tx.type with
  | .three _ _ _ _ _ maxBlobFee blobHashes => do
    if blobHashes.isEmpty then
      .error s!"{type3ZeroBlobsTag} : no blob hashes in type-3 transaction"
    checkTransactionBlobCount benv.stat.rules.tx blobHashes
    -- P0.6 item 3: the version byte is read through the total `head?`, never a
    -- partial index into the fixed 32-byte hash encoding.
    if List.any blobHashes (λ bvh => bvh.toBytes.head? ≠ some versionedHashVersionKzg) then
      .error
        s!"{type3InvalidBlobVersionedHashTag} : a blob versioned hash has \
           a version byte other than {versionedHashVersionKzg}"
    else
      let blobGasPrice :=
        calculateBlobGasPrice benv.stat.rules.blob benv.stat.excessBlobGas
      if maxBlobFee < blobGasPrice then
        .error "InsufficientMaxFeePerBlobGasError : insufficient max fee per blob gas"
      else
        .ok ⟨maxGasFee + calculateTotalBlobGas tx * maxBlobFee, blobHashes⟩
  | _ => .ok ⟨maxGasFee, []⟩

def checkTransactionReceiver (tx : Tx) : Except String Unit :=
  if tx.isTypeThree then
    if tx.type.receiver?.isNone then
      .error
        s!"{type3ContractCreationTag} : type-3 transactions cannot create contracts"
    else
      .ok ()
  else
    .ok ()

def checkTransactionAuthorizationList (tx : Tx) : Except String Unit :=
  match tx.type with
  | .four _ _ _ _ _ [] =>
    .error s!"{emptyAuthorizationListTag} : empty authorization list"
  | _ => .ok ()

def checkTransactionChainId (benv : Benv) (tx : Tx) : Except String Unit :=
  match tx.type with
  | .zero _ _ =>
    if tx.v < 35 || (tx.v - 35) / 2 = benv.stat.chainId.toNat then .ok ()
    else .error s!"{invalidChainIdTag} : transaction chain ID = {(tx.v - 35) / 2}"
  | .one chainId _ _ _
  | .two chainId _ _ _ _
  | .three chainId _ _ _ _ _ _
  | .four chainId _ _ _ _ _ =>
    if chainId = benv.stat.chainId then .ok ()
    else .error s!"{invalidChainIdTag} : transaction chain ID = {chainId}"

def checkTransactionSenderCode (senderAccount : Acct) :
    Except String Unit :=
  if ¬ (senderAccount.code.isEmpty ∨ isValidDelegation senderAccount.code) then
    .error s!"{senderNotEoaTag} : sender has non-delegation code"
  else
    .ok ()

def checkTransactionSenderAccount
    (senderAccount : Acct) (tx : Tx) (maxGasFee : Nat) :
    Except String Unit :=
  if senderAccount.nonce > tx.nonce then
    .error
      s!"{nonceMismatchTooLowTag} : transaction nonce = {tx.nonce.toNat} < \
         sender nonce = {senderAccount.nonce.toNat}"
  else if senderAccount.nonce < tx.nonce then
    .error
      s!"{nonceMismatchTooHighTag} : transaction nonce = {tx.nonce.toNat} > \
         sender nonce = {senderAccount.nonce.toNat}"
  else if senderAccount.bal.toNat < maxGasFee + tx.value then
    .error
      s!"{insufficientAccountFundsTag} : sender balance = \
         {senderAccount.bal.toNat} < max gas fee = {maxGasFee} + \
         transaction value = {tx.value}"
  else
    checkTransactionSenderCode senderAccount

def checkTransaction (benv : Benv) (blockOut : BlockOutput) (tx : Tx) :
    Except String (Adr × Nat × List B256 × Nat) := do
  let txBlobGasUsed ← checkTransactionGasLimits benv blockOut tx
  checkTransactionChainId benv tx
  let senderAddress ← recoverSender benv.stat.chainId tx
  let senderAccount := benv.state.get senderAddress
  let ⟨effectiveGasPrice, maxGasFee⟩ ← checkTransactionGasFee benv tx
  let ⟨maxGasFee, blobVersionedHashes⟩ ←
    checkTransactionBlobData benv tx maxGasFee
  checkTransactionReceiver tx
  checkTransactionAuthorizationList tx
  checkTransactionSenderAccount senderAccount tx maxGasFee
  .ok ⟨
    senderAddress,
    effectiveGasPrice,
    blobVersionedHashes,
    txBlobGasUsed
  ⟩

def calculateIntrinsicCost (tx: Tx) : Nat × Nat :=
  -- `foldl` (tail-recursive) rather than `(map …).sum`: the latter's
  -- non-tail-recursive `List.map` overflows the stack on large calldata
  -- (e.g. the 1.2 MB inputs in the EIP-2537 stress fixtures).
  let tokensInCalldata : Nat :=
    tx.data.foldl (fun acc x => acc + (if x = 0 then 1 else 4)) 0
  let callDataFloorGasCost : Nat :=
    tokensInCalldata * floorCalldataCost + txBaseCost
  let dataCost : Nat :=
    tokensInCalldata * standardCallDataTokenCost
  let createCost : Nat :=
      match tx.type.receiver? with
      | none => txCreateCost + initCodeCost (tx.data).length
      | some _ => 0
  let accessListCost : Nat :=
    let accessList :=
      match tx.type with
      | .zero _ _ => []
      | .one _ _ _ accessList => accessList
      | .two _ _ _ _ accessList => accessList
      | .three _ _ _ _ accessList _ _ => accessList
      | .four _ _ _ _ accessList _ => accessList
    let accessItemCost : (Adr × List B256) → Nat
      | ⟨_, keys⟩ =>
        txAccessListAddressCost + keys.length * txAccessListStorageKeyCost
    (accessList.map accessItemCost).sum
  let authCost : Nat :=
    match tx.type with
    | .four _ _ _ _ _ auths => perEmptyAccountCost * auths.length
    | _ => 0
  ⟨
    txBaseCost + dataCost + createCost + accessListCost + authCost,
    callDataFloorGasCost
  ⟩

def checkInitcodeSize (code : CodeLimits) (receiver : Option Adr)
    (dataLength : Nat) : Except String Unit :=
  if receiver.isNone && dataLength > code.maxInitCodeSize then
    .error
      s!"{initcodeSizeExceededTag} : initcode is {dataLength} bytes, \
         exceeding the {code.maxInitCodeSize}-byte maximum"
  else
    .ok ()

/-- Enforce the fork's per-transaction gas cap, when one is active. -/
def checkTransactionGasCap (limits : TransactionLimits) (gas : Nat) :
    Except String Unit :=
  match limits.maxGas with
  | none => .ok ()
  | some maxGas =>
    if gas > maxGas then
      .error
        s!"{transactionGasLimitExceededTag} : transaction gas = {gas} > \
           maximum = {maxGas}"
    else
      .ok ()

def validateTransaction (rules : ForkRules) (tx : Tx) :
    Except String (Nat × Nat) := do
  let ⟨intrinsicGas, callDataFloorGasCost⟩ := calculateIntrinsicCost tx
  if max intrinsicGas callDataFloorGasCost > tx.gas
  then
    .error
      s!"{intrinsicGasTooLowTag} : transaction gas = {tx.gas} < \
         max intrinsic/calldata floor cost = \
         {max intrinsicGas callDataFloorGasCost}"
  match rules.tx.maxGas with
  | none =>
    -- Keep Prague's established error precedence byte-for-byte: before Osaka
    -- this build checked the nonce before initcode size. The validity set is
    -- the same as EELS, while multiply-invalid legacy fixtures retain their
    -- existing diagnostic identity.
    if tx.nonce = UInt64.max then
      .error s!"{nonceIsMaxTag} : transaction nonce is 2^64 - 1"
    checkInitcodeSize rules.code tx.type.receiver? tx.data.length
  | some _ =>
    -- Osaka follows EELS: initcode, EIP-7825 gas cap, then nonce.
    checkInitcodeSize rules.code tx.type.receiver? tx.data.length
    checkTransactionGasCap rules.tx tx.gas
    if tx.nonce = UInt64.max then
      .error s!"{nonceIsMaxTag} : transaction nonce is 2^64 - 1"
  .ok ⟨intrinsicGas, callDataFloorGasCost⟩

def prepareMessage (benv: Benv) (tenv: Tenv) (tx: Tx) :
  Except String Msg := do
  let ⟨currentTarget, msgData, code, codeAddress⟩ :
    Adr × Bytes × ByteArray × Option Adr :=
    match tx.type.receiver? with
    | none => ⟨
        computeContractAddress
          tenv.stat.origin
          (benv.state.getNonce tenv.stat.origin - 1),
        [],
        .mk (.mk tx.data),
        none
      ⟩
    | some target => ⟨
        target,
        tx.data,
        benv.state.getCode target,
        target
      ⟩
  -- EIP-2929 pre-warms every precompile, so the set comes from the active
  -- rules rather than from a literal run of addresses: at Osaka that is what
  -- makes a call to P256VERIFY cost warm access like the other seventeen.
  let accessedAddresses : AdrSet :=
    tenv.stat.accessListAddresses.insertMany
      (benv.stat.rules.precompiles ++ [tenv.stat.origin, currentTarget])
  .ok {
    benv := benv,
    tenv := tenv,
    caller := tenv.stat.origin,
    target := tx.type.receiver?,
    gas := tenv.stat.gas,
    value := tx.value.toB256,
    data := msgData,
    code := code,
    depth := 1024,
    currentTarget := currentTarget,
    codeAddress := codeAddress
    shouldTransferValue := true,
    isStatic := false,
    accessedAddresses := accessedAddresses,
    accessedStorageKeys := tenv.stat.accessListStorageKeys,
    disablePrecompiles := false
  }

def calculateDataFee (blob : BlobSchedule) (excess_blob_gas: Nat) (tx: Tx) :
    Nat :=
  calculateTotalBlobGas tx * calculateBlobGasPrice blob excess_blob_gas

def getTxHash (tx : Tx) : B256 := tx.toBLT.toBytes.keccak

def Receipt.toBLT (r : Receipt) : BLT :=
  .list [
    .bytes (if r.succeeded then [0x01] else []),
    .bytes r.gasUsed.toBytesPack,
    .bytes r.bloom,
    .list (r.logs.map Log.toBLT)
  ]

def makeReceipt
  (tx: Tx)
  (error: Option String)
  (gasUsed: Nat)
  (logs: List Log) : Fin 5 × Receipt :=
  let receipt : Receipt := {
    succeeded := error.isNone,
    gasUsed := gasUsed,
    bloom := logsBloom logs,
    logs := logs
  }
  let head : Fin 5 :=
    match tx.type with
    | .zero _ _ => 0
    | .one _ _ _ _ => 1
    | .two _ _ _ _ _ => 2
    | .three _ _ _ _ _ _ _ => 3
    | .four _ _ _ _ _ _ => 4
  ⟨head, receipt⟩

def BlockOutput.init : BlockOutput :=
  {
    blockGasUsed := 0
    transactionsTrie := .empty
    receiptsTrie := .empty
    receiptKeys := []
    blockLogs := []
    withdrawalsTrie := .empty
    blobGasUsed := 0
    requests := []
  }

---------------- TRANSACTION-REJECTION REGRESSION CHECKS ----------------

-- These checks exercise the real producer functions, not merely the fixture
-- classifier.  They pin the validation order and the distinctions that used
-- to be hidden behind `InvalidTransaction` and `NonceMismatchError`.

private def fixtureTestTx : Tx :=
  {
    nonce := 0
    gas := txBaseCost
    value := 0
    data := []
    v := 27
    r := []
    s := []
    type := .zero 10 (some 0)
  }

private def fixtureTestBenv (blockGasLimit : Nat := 10000000) : Benv :=
  {
    state := .empty
    createdAccounts := .emptyWithCapacity
    stat := {
      rules := pragueRules
      chainId := 1
      origState := .empty
      blockGasLimit := blockGasLimit
      blockHashes := []
      coinbase := 0
      number := 1
      baseFeePerGas := 1
      time := 0
      prevRandao := 0
      excessBlobGas := 0
      parentBeaconBlockRoot := 0
    }
  }

private def fixtureTestAccount
    (nonce : UInt64) (bal : B256) (code : ByteArray := .empty) : Acct :=
  { nonce := nonce, bal := bal, stor := .empty, code := code }

#guard hasTag intrinsicGasTooLowTag <|
  validateTransaction pragueRules {fixtureTestTx with gas := txBaseCost - 1}
#guard hasTag nonceIsMaxTag <|
  validateTransaction pragueRules {fixtureTestTx with nonce := UInt64.max}
#guard hasTag initcodeSizeExceededTag <|
  checkInitcodeSize pragueRules.code none (pragueRules.code.maxInitCodeSize + 1)

-- EIP-7825 is inclusive at `2 ^ 24`, and absent at Prague.
#guard (checkTransactionGasCap osakaRules.tx (2 ^ 24 - 1)).toOption.isSome
#guard (checkTransactionGasCap osakaRules.tx (2 ^ 24)).toOption.isSome
#guard hasTag transactionGasLimitExceededTag <|
  checkTransactionGasCap osakaRules.tx (2 ^ 24 + 1)
#guard (checkTransactionGasCap pragueRules.tx (2 ^ 24 + 1)).toOption.isSome
#guard hasTag transactionGasLimitExceededTag <|
  validateTransaction osakaRules {fixtureTestTx with gas := 2 ^ 24 + 1}

-- The initcode bound comes from the rules record, not from a global: a smaller
-- limit rejects an initcode the Prague limit accepts, at the same boundary.
private def guardTightCodeLimits : CodeLimits :=
  { maxCodeSize := 100, maxInitCodeSize := 200 }

#guard (checkInitcodeSize pragueRules.code none 200).toOption.isSome
#guard (checkInitcodeSize guardTightCodeLimits none 200).toOption.isSome
#guard hasTag initcodeSizeExceededTag <|
  checkInitcodeSize guardTightCodeLimits none 201
-- A non-creation transaction is unaffected by the limit under either schedule.
#guard (checkInitcodeSize guardTightCodeLimits (some 0) 100000).toOption.isSome

#guard hasTag priorityGreaterThanMaxFeeTag <|
  checkTransactionDynamicGasFee 1 1 2 1
#guard hasTag insufficientMaxFeePerGasTag <|
  checkTransactionDynamicGasFee 2 1 1 1
#guard hasTag gasPriceProductOverflowTag <|
  checkTransactionDynamicGasFee 0 2 0 (2 ^ 255)
#guard hasTag gasPriceProductOverflowTag <|
  checkTransactionLegacyGasFee 0 2 (2 ^ 255)

#guard hasTag gasAllowanceExceededTag <|
  checkTransactionGasLimits (fixtureTestBenv txBaseCost) .init
    {fixtureTestTx with gas := txBaseCost + 1}
#guard hasTag type3BlobCountExceededTag <|
  checkTransactionGasLimits fixtureTestBenv .init
    { fixtureTestTx with
      type := .three 1 1 10 0 [] 1 (List.replicate 10 0) }
#guard hasTag type3ZeroBlobsTag <|
  checkTransactionBlobData fixtureTestBenv
    {fixtureTestTx with type := .three 1 1 10 0 [] 1 []} 10
#guard (checkTransactionBlobCount osakaRules.tx
  (List.replicate 5 (0 : B256))).toOption.isSome
#guard (checkTransactionBlobCount osakaRules.tx
  (List.replicate 6 (0 : B256))).toOption.isSome
#guard hasTag type3BlobCountLimitExceededTag <|
  checkTransactionBlobCount osakaRules.tx (List.replicate 7 (0 : B256))
#guard (checkTransactionBlobCount pragueRules.tx
  (List.replicate 7 (0 : B256))).toOption.isSome
#guard hasTag type3InvalidBlobVersionedHashTag <|
  checkTransactionBlobData fixtureTestBenv
    {fixtureTestTx with type := .three 1 1 10 0 [] 1 [0]} 10

#guard hasTag nonceMismatchTooLowTag <|
  checkTransactionSenderAccount (fixtureTestAccount 2 100) fixtureTestTx 0
#guard hasTag nonceMismatchTooHighTag <|
  checkTransactionSenderAccount (fixtureTestAccount 0 100)
    {fixtureTestTx with nonce := 1} 0
#guard hasTag insufficientAccountFundsTag <|
  checkTransactionSenderAccount (fixtureTestAccount 0 0) fixtureTestTx 1
#guard hasTag senderNotEoaTag <|
  checkTransactionSenderAccount
    (fixtureTestAccount 0 100 (ByteArray.mk #[0x01])) fixtureTestTx 0


def processTransaction
  (benv: Benv) (bout : BlockOutput)
  (tx: Tx) (index : Nat) : Except String (State × BlockOutput) := do
  -- NOTE: linearized into a straight `let ← .ok (…)` / `let := …` chain
  -- (no `mut`/`for`) so the block inverts cleanly with `of_bind_eq_ok` and the
  -- `bout` bookkeeping stays opaque.  Definitionally equal to the previous
  -- `mut`/`for` form except that the final account-deletion `for` is expressed
  -- as `foldl`, which agrees because `destroyAccount` commutes over the
  -- distinct addresses of the `accountsToDelete` set.
  let benv := benv.beginTransaction
  let bout ← .ok {bout with
    transactionsTrie := bout.transactionsTrie.insert (BLT.bytes index.toBytes).toBytes tx}
  let ⟨intrinsicGas, calldataFloorGasCost⟩ ←
    validateTransaction benv.stat.rules tx
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
  let gas := tx.gas - intrinsicGas
  let state : State := benv.state.incrNonce sender
  let state ← (state.subBal sender (effectiveGasFee + blobGasFee).toB256).toExcept
    "ERROR : balance underflow"
  let preaccessedAddresses : AdrSet :=
    .ofList (benv.stat.coinbase :: tx.accessList.map Prod.fst)
  let preaccessedStorageKeys : KeySet :=
    .ofList (tx.accessList.map <| λ ⟨adr, keys⟩ => keys.map (⟨adr, ·⟩)).flatten
  let tenv : Tenv := {
    transientStorage := .empty
    stat := {
      origin := sender
      gasPrice := effectiveGasPrice
      gas := gas
      accessListAddresses := preaccessedAddresses
      accessListStorageKeys := preaccessedStorageKeys
      blobVersionedHashes := blobVersionedHashes
      auths := tx.auths
      indexInBlock := index
      txHash := getTxHash tx
    }
  }
  let msg ← prepareMessage {benv with state := state} tenv tx
  let ⟨state, txOutput⟩ ← processMessageCall msg
  let txGasUsedBeforeRefund := tx.gas - txOutput.gasLeft
  let refundCounter : Nat ←
    (Int.toNat? txOutput.refundCounter).toExcept "ERROR : refund counter is negative"
  let txGasRefund : Nat :=
    min (txGasUsedBeforeRefund / 5) refundCounter
  let txGasUsedAfterRefund : Nat :=
    max (txGasUsedBeforeRefund - txGasRefund) calldataFloorGasCost
  let txGasLeft :=
    tx.gas - txGasUsedAfterRefund
  let gasRefundAmount : Nat :=
    txGasLeft * effectiveGasPrice
  let priorityFeePerGas := effectiveGasPrice - benv.stat.baseFeePerGas
  let transactionFee := txGasUsedAfterRefund * priorityFeePerGas
  let state := state.addBal sender gasRefundAmount.toB256
  let state := state.addBal benv.stat.coinbase transactionFee.toB256
  let state := txOutput.accountsToDelete.toList.foldl destroyAccount state
  let bout ← .ok {bout with
    blockGasUsed := bout.blockGasUsed + txGasUsedAfterRefund,
    blobGasUsed := bout.blobGasUsed + txBlobGasUsed}
  let receipt :=
    makeReceipt tx txOutput.error bout.blockGasUsed txOutput.logs
  let receiptKey : Bytes := BLT.toBytes <| .bytes index.toBytes
  let bout ← .ok {bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie := bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ txOutput.logs}
  .ok ⟨state, bout⟩

def BlockOutput.withWithdrawalsTrie
    (bo : BlockOutput) (tr : Std.TreeMap Bytes Withdrawal compare) : BlockOutput :=
  {bo with withdrawalsTrie := tr}

def processWithdrawalsTrie (tr : Std.TreeMap Bytes Withdrawal compare)
    (wds : List Withdrawal) : Std.TreeMap Bytes Withdrawal compare :=
  List.foldl
    (λ acc ⟨i, wd⟩ => acc.insert (BLT.toBytes <| .bytes i.toBytes) wd)
    tr
    wds.putIndex

def processWithdrawalsState (st : State) (wds : List Withdrawal) : State :=
  List.foldl
    (λ acc wd => acc.addBal wd.recipient (wd.amount * (10 ^ 9).toB256))
    st
    wds

def processWithdrawals
  (benv : Benv) (bout : BlockOutput) (wds : List Withdrawal) : State × BlockOutput :=
  let trie := processWithdrawalsTrie bout.withdrawalsTrie wds
  let state := processWithdrawalsState benv.state wds
  ⟨state, bout.withWithdrawalsTrie trie⟩

-- Access lists, blob hashes, and authorization tuples arrive inside typed
-- transactions, so their fields are untrusted in exactly the way withdrawal
-- fields are: every shape must be checked before any truncating conversion,
-- and a wrong list shape is a different reason from an oversized scalar.

def BLT.toExStrStorageKey : BLT → Except String B256
  | .bytes xs => xs.toRlpHash "access list storage key"
  | .list _ =>
    .error <| rlpStructureError "access list storage key"
      "expected a byte-string item"

def BLT.toExStrAccessItem : BLT → Except String (Adr × List B256)
  | .list [.bytes ar, .list ksr] => do
    let a ← ar.toRlpAdr "access list address"
    let ks ← List.mapM BLT.toExStrStorageKey ksr
    .ok ⟨a, ks⟩
  | _ =>
    .error <| rlpStructureError "access list item"
      "expected [address, [storage key, ...]]"

def BLT.toExStrAccessList : BLT → Except String AccessList
  | .list rs => List.mapM BLT.toExStrAccessItem rs
  | .bytes _ =>
    .error <| rlpStructureError "access list" "expected a list item"

def BLT.toExStrBlobHash : BLT → Except String B256
  | .bytes xs => xs.toRlpHash "blob versioned hash"
  | .list _ =>
    .error <| rlpStructureError "blob versioned hash"
      "expected a byte-string item"

def BLT.toExStrAuth : BLT → Except String Auth
  | .list [
      .bytes chainId,
      .bytes address,
      .bytes nonce,
      .bytes yParity,
      .bytes r,
      .bytes s
    ] => do
      let chainId ← chainId.toRlpB256 "authorization chainId"
      let address ← address.toRlpAdr "authorization address"
      let nonce ← nonce.toRlpB64 "authorization nonce"
      let yParity ← yParity.toRlpNat "authorization yParity" 32
      let r ← r.toRlpB256 "authorization r"
      let s ← s.toRlpB256 "authorization s"
      .ok {
        chainId := chainId
        address := address
        nonce := nonce
        yParity := yParity
        r := r
        s := s
      }
  | _ =>
    .error <| rlpStructureError "authorization"
      "expected a list of six byte-string fields"

/-- Strict authorisation-decoder soundness. -/
theorem BLT.toExStrAuth_wireWellFormed {blt : BLT} {a : Auth}
    (h : blt.toExStrAuth = .ok a) : a.WireWellFormed := by
  unfold BLT.toExStrAuth at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    exact Bytes.toRlpNat_lt_two_pow_256 (by assumption)
  · exact absurd h (by simp)

def Bytes.toExStrTx : Bytes → Except String Tx
  | [] =>
    .error <| rlpStructureError "typed transaction"
      "cannot decode an empty byte string"
  | x :: xs =>
    -- Every scalar is bounded before conversion: `Bytes.toUInt64` truncates modulo
    -- 2^64, so it may only see bytes returned by a strict decoder. Signature
    -- scalars keep their minimally encoded bytes once validated, so signing
    -- and trie bytes are unchanged for valid transactions.
    match x, Bytes.toBLT? xs with
    | 0x01, some (.list [
        .bytes chainId,
        .bytes nonce,
        .bytes gasPrice,
        .bytes gas,
        .bytes receiver,
        .bytes value,
        .bytes data,
        accessList,
        .bytes yParity,
        .bytes r,
        .bytes s
      ]) => do
      let chainId ← chainId.toRlpB64 "type-1 transaction chainId"
      let nonce ← nonce.toRlpB64 "type-1 transaction nonce"
      let gasPrice ← gasPrice.toRlpNat "type-1 transaction gasPrice" 32
      let gas ← gas.toRlpNat "type-1 transaction gas" 32
      let receiver ← receiver.toRlpReceiver "type-1 transaction receiver"
      let value ← value.toRlpNat "type-1 transaction value" 32
      let accessList ← accessList.toExStrAccessList
      let yParity ← yParity.toRlpNat "type-1 transaction yParity" 32
      let _ ← r.toRlpB256 "type-1 transaction r"
      let _ ← s.toRlpB256 "type-1 transaction s"
      .ok {
        nonce := nonce,
        gas := gas,
        value := value,
        data := data,
        v := yParity,
        r := r,
        s := s,
        type := .one chainId gasPrice receiver accessList
      }
    | 0x01, _ =>
      .error <| rlpStructureError "type-1 transaction"
        "expected a list of eleven fields"
    | 0x02, some (.list [
        .bytes chainId,
        .bytes nonce,
        .bytes maxPriorityFee,
        .bytes maxFee,
        .bytes gas,
        .bytes receiver,
        .bytes value,
        .bytes data,
        accessList,
        .bytes yParity,
        .bytes r,
        .bytes s
      ]) => do
      let chainId ← chainId.toRlpB64 "type-2 transaction chainId"
      let nonce ← nonce.toRlpB64 "type-2 transaction nonce"
      let maxPriorityFee ← maxPriorityFee.toRlpNat "type-2 transaction maxPriorityFee" 32
      let maxFee ← maxFee.toRlpNat "type-2 transaction maxFee" 32
      let gas ← gas.toRlpNat "type-2 transaction gas" 32
      let receiver ← receiver.toRlpReceiver "type-2 transaction receiver"
      let value ← value.toRlpNat "type-2 transaction value" 32
      let accessList ← accessList.toExStrAccessList
      let yParity ← yParity.toRlpNat "type-2 transaction yParity" 32
      let _ ← r.toRlpB256 "type-2 transaction r"
      let _ ← s.toRlpB256 "type-2 transaction s"
      .ok {
        nonce := nonce,
        gas := gas,
        value := value,
        data := data,
        v := yParity,
        r := r,
        s := s,
        type := .two chainId maxPriorityFee maxFee receiver accessList
      }
    | 0x02, _ =>
      .error <| rlpStructureError "type-2 transaction"
        "expected a list of twelve fields"
    | 0x03, some (.list [
        .bytes chainId,
        .bytes nonce,
        .bytes maxPriorityFee,
        .bytes maxFee,
        .bytes gas,
        .bytes receiver,
        .bytes value,
        .bytes data,
        accessList,
        .bytes maxBlobFee,
        .list blobHashes,
        .bytes yParity,
        .bytes r,
        .bytes s
      ]) => do
      let chainId ← chainId.toRlpB64 "type-3 transaction chainId"
      let nonce ← nonce.toRlpB64 "type-3 transaction nonce"
      let maxPriorityFee ← maxPriorityFee.toRlpNat "type-3 transaction maxPriorityFee" 32
      let maxFee ← maxFee.toRlpNat "type-3 transaction maxFee" 32
      let gas ← gas.toRlpNat "type-3 transaction gas" 32
      -- A type-3 receiver is a mandatory address at the RLP level; the
      -- semantic contract-creation rejection downstream remains as defense
      -- in depth for transactions that arrive already decoded.  Empty is the
      -- official type-3 contract-creation failure, while a nonempty value of
      -- any width other than twenty bytes remains an RLP shape failure.
      if receiver.isEmpty then
        .error
          s!"{type3ContractCreationTag} : type-3 transaction receiver is empty"
      let receiver ← receiver.toRlpAdr "type-3 transaction receiver"
      let value ← value.toRlpNat "type-3 transaction value" 32
      let accessList ← accessList.toExStrAccessList
      let maxBlobFee ← maxBlobFee.toRlpNat "type-3 transaction maxBlobFee" 32
      let blobHashes ← List.mapM BLT.toExStrBlobHash blobHashes
      let yParity ← yParity.toRlpNat "type-3 transaction yParity" 32
      let _ ← r.toRlpB256 "type-3 transaction r"
      let _ ← s.toRlpB256 "type-3 transaction s"
      .ok {
        nonce := nonce,
        gas := gas,
        value := value,
        data := data,
        v := yParity,
        r := r,
        s := s,
        type :=
          .three chainId maxPriorityFee maxFee receiver accessList
            maxBlobFee blobHashes
      }
    | 0x03, _ =>
      .error <| rlpStructureError "type-3 transaction"
        "expected a list of fourteen fields"
    | 0x04, some (.list [
        .bytes chainId,
        .bytes nonce,
        .bytes maxPriorityFee,
        .bytes maxFee,
        .bytes gas,
        .bytes receiver,
        .bytes value,
        .bytes data,
        accessList,
        .list auths,
        .bytes yParity,
        .bytes r,
        .bytes s
      ]) => do
      let chainId ← chainId.toRlpB64 "type-4 transaction chainId"
      let nonce ← nonce.toRlpB64 "type-4 transaction nonce"
      let maxPriorityFee ← maxPriorityFee.toRlpNat "type-4 transaction maxPriorityFee" 32
      let maxFee ← maxFee.toRlpNat "type-4 transaction maxFee" 32
      let gas ← gas.toRlpNat "type-4 transaction gas" 32
      if receiver.isEmpty then
        .error s!"{type4ContractCreationTag} : type-4 transaction receiver is empty"
      let receiver ← receiver.toRlpAdr "type-4 transaction receiver"
      let value ← value.toRlpNat "type-4 transaction value" 32
      let accessList ← accessList.toExStrAccessList
      let auths ← List.mapM BLT.toExStrAuth auths
      let yParity ← yParity.toRlpNat "type-4 transaction yParity" 32
      let _ ← r.toRlpB256 "type-4 transaction r"
      let _ ← s.toRlpB256 "type-4 transaction s"
      .ok {
        nonce := nonce,
        gas := gas,
        value := value,
        data := data,
        v := yParity,
        r := r,
        s := s,
        type := .four chainId maxPriorityFee maxFee receiver accessList auths
      }
    | 0x04, _ =>
      .error <| rlpStructureError "type-4 transaction"
        "expected a list of thirteen fields"
    | x, _ => .error s!"ERROR : type-{x} txs do not exist, decoding failed"

/-- Strict typed-transaction-decoder soundness. Every transaction the typed
envelope decoder produces satisfies `Tx.WireWellFormed`, for each of the four
implemented envelope types. Together with `BLT.toExStrTx_legacy_wireWellFormed`
below this is what makes the structural predicate a lift of the decoders. -/
theorem Bytes.toExStrTx_wireWellFormed {xs : Bytes} {tx : Tx}
    (h : xs.toExStrTx = .ok tx) : tx.WireWellFormed := by
  unfold Bytes.toExStrTx at h
  split at h
  · exact absurd h (by simp)
  · split at h
    -- type 1 (EIP-2930)
    · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first
          | exact Bytes.toRlpNat_lt_two_pow_256 (by assumption)
          | exact Bytes.toRlpB256_eq_ok (by assumption)
    · exact absurd h (by simp)
    -- type 2 (EIP-1559)
    · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first
          | exact Bytes.toRlpNat_lt_two_pow_256 (by assumption)
          | exact Bytes.toRlpB256_eq_ok (by assumption)
    · exact absurd h (by simp)
    -- type 3 (EIP-4844). The mandatory-receiver guard is a join point, so the
    -- chain has to be split at it before the remaining binds peel.
    · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
      dsimp only at h
      split at h
      · obtain ⟨_, herr, _⟩ := Except.bind_eq_ok h
        exact absurd herr (by simp)
      · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first
            | exact Bytes.toRlpNat_lt_two_pow_256 (by assumption)
            | exact Bytes.toRlpB256_eq_ok (by assumption)
    · exact absurd h (by simp)
    -- type 4 (EIP-7702)
    · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
      dsimp only at h
      split at h
      · obtain ⟨_, herr, _⟩ := Except.bind_eq_ok h
        exact absurd herr (by simp)
      · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?auths⟩
        case auths =>
          intro a ha
          obtain ⟨blt, hblt⟩ := List.mapM_except_eq_ok_mem (by assumption) a ha
          exact BLT.toExStrAuth_wireWellFormed hblt
        all_goals
          first
            | exact Bytes.toRlpNat_lt_two_pow_256 (by assumption)
            | exact Bytes.toRlpB256_eq_ok (by assumption)
    · exact absurd h (by simp)
    · exact absurd h (by simp)

def decodeTx : Bytes ⊕ Tx → Except String Tx
  | .inl xs => xs.toExStrTx
  | .inr tx => .ok tx


def processSystemTransactionTenv (benv : Benv) : Tenv :=
  {
    transientStorage := .empty,
    stat := {
      origin := systemAddress,
      gasPrice := benv.stat.baseFeePerGas,
      gas := systemTransactionGas,
      accessListAddresses := .emptyWithCapacity
      accessListStorageKeys := .emptyWithCapacity
      blobVersionedHashes := [],
      auths := [],
      indexInBlock := none,
      txHash := none
    }
  }

def processSystemTransactionMsg (benv : Benv) (tenv : Tenv)
    (target : Adr) (data : Bytes) (code : ByteArray) : Msg :=
  {
    benv := benv,
    tenv := tenv,
    caller := systemAddress,
    target := target,
    gas := systemTransactionGas,
    value := 0,
    data := data,
    code := code,
    depth := 1024,
    currentTarget := target,
    codeAddress := target,
    shouldTransferValue := false,
    isStatic := false,
    accessedAddresses := .emptyWithCapacity,
    accessedStorageKeys := .emptyWithCapacity,
    disablePrecompiles := false
  }

-- The single boundary shared by all four system transactions (beacon roots,
-- history storage, withdrawal requests, consolidation requests), so each takes
-- its own input state as the original state.
def processSystemTransaction (benv : Benv)
  (target : Adr) (code : ByteArray) (data : Bytes) :
  Except String (State × MsgCallOutput) := do
  let benv := benv.beginTransaction
  let txEnv : Tenv := processSystemTransactionTenv benv
  let systemTxMsg : Msg :=
    processSystemTransactionMsg benv txEnv target data code
  processMessageCall systemTxMsg

def extractDepositData (data : Bytes) : Except String Bytes := do
  if data.length != depositEventLength then
    .error s!"{depositEventLayoutTag} : invalid deposit event data length"
  if data.sliceToNat 0 32 ≠ pubkeyOffset then
    .error s!"{depositEventLayoutTag} : invalid pubkey offset in deposit log"
  if data.sliceToNat 32 32 ≠ withdrawalCredentialsOffset then
    .error s!"{depositEventLayoutTag} : invalid withdrawal credentials offset in deposit log"
  if data.sliceToNat 64 32 ≠ amountOffset then
    .error s!"{depositEventLayoutTag} : invalid amount offset in deposit log"
  if data.sliceToNat 96 32 ≠ signatureOffset then
    .error s!"{depositEventLayoutTag} : invalid signature offset in deposit log"
  if data.sliceToNat 128 32 ≠ indexOffset then
    .error s!"{depositEventLayoutTag} : invalid index offset in deposit log"
  if data.sliceToNat pubkeyOffset 32 ≠ pubkeySize then
    .error s!"{depositEventLayoutTag} : invalid pubkey size in deposit log"
  let pubkey : Bytes := data.slice! (pubkeyOffset + 32) pubkeySize
  if data.sliceToNat withdrawalCredentialsOffset 32 ≠ withdrawalCredentialsSize then
    .error s!"{depositEventLayoutTag} : invalid withdrawal credentials size in deposit log"
  let withdrawalCredentials : Bytes :=
    data.slice! (withdrawalCredentialsOffset + 32) withdrawalCredentialsSize
  if data.sliceToNat amountOffset 32 ≠ amountSize then
    .error s!"{depositEventLayoutTag} : invalid amount size in deposit log"
  let amount : Bytes := data.slice! (amountOffset + 32) amountSize
  if data.sliceToNat signatureOffset 32 ≠ signatureSize then
    .error s!"{depositEventLayoutTag} : invalid signature size in deposit log"
  let signature : Bytes := data.slice! (signatureOffset + 32) signatureSize
  if data.sliceToNat indexOffset 32 ≠ indexSize then
    .error s!"{depositEventLayoutTag} : invalid index size in deposit log"
  let index : Bytes := data.slice! (indexOffset + 32) indexSize
  .ok (pubkey ++ withdrawalCredentials ++ amount ++ signature ++ index)

def parseDepositRequests
  (bout : BlockOutput) : Except String Bytes := do
  let mut depositRequests : Bytes := []
  for key in bout.receiptKeys do
    let ⟨_, receipt⟩  ←
      bout.receiptsTrie[key]?.toExcept "ERROR : receipt not found"
    for log in receipt.logs do
      if (
        log.address = depositContractAddress ∧
        log.topics[0]? = some depositEventSignatureHash
      ) then
        let request ← extractDepositData log.data
        depositRequests := depositRequests ++ request
  .ok depositRequests

def processUncheckedSystemTransaction
  (benv : Benv) (target : Adr) (data : Bytes) :
  Except String (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  processSystemTransaction benv target systemContractCode data

def processCheckedSystemTransaction
  (benv : Benv) (target : Adr) (data : Bytes) :
  Except String (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  if systemContractCode.isEmpty then
    .error s!"InvalidBlock : System contract address {target.toHex} does not contain code"
  let ⟨state, systemTxOutput⟩ ←
    processSystemTransaction benv target systemContractCode data
  -- P0.6 item 3: the failure text is extracted by the total match, never by a
  -- partial projection out of the optional error field.
  match systemTxOutput.error with
  | some err =>
    .error s!"{systemContractCallFailedTag} : system contract ({target.toHex}) call failed: \
      {err}"
  | none => .ok ⟨state, systemTxOutput⟩

def processGeneralPurposeRequests
  (benv : Benv) (bout : BlockOutput) :
  Except String (State × BlockOutput) := do
  let depositRequests ← parseDepositRequests bout
  let mut requestsFromExecution : List Bytes := bout.requests
  if depositRequests.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [depositRequestType ++ depositRequests]
  let ⟨state, withdrawalOutput⟩  ←
    processCheckedSystemTransaction benv
      withdrawalRequestPredeployAddress
      []
  let benv := {benv with state := state}
  if withdrawalOutput.returnData.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [withdrawalRequestType ++ withdrawalOutput.returnData]
  let ⟨state, consolidationOutput⟩  ←
    processCheckedSystemTransaction benv
      consolidationRequestPredeployAddress
      []
  if consolidationOutput.returnData.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [consolidationRequestType ++ consolidationOutput.returnData]
  .ok ⟨state, {bout with requests := requestsFromExecution}⟩

def applyTransactions :
    List (Nat × Tx) → Benv → BlockOutput → Except String (Benv × BlockOutput)
  | [], benv, bout => .ok (benv, bout)
  | ⟨i, tx⟩ :: txis, benv , bout => do
    let ⟨st, bout'⟩ ← processTransaction benv bout tx i
    applyTransactions txis (benv.withState st) bout'

def applyBody
  (benv : Benv) (txs : List (Bytes ⊕ Tx)) (wds : List Withdrawal) :
  Except String (State × BlockOutput) := do
  let ⟨stBeacon, _⟩ ←
    processUncheckedSystemTransaction benv
      beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toBytes
  let benvBeacon : Benv := benv.withState stBeacon
  let lastHash ←
     benvBeacon.stat.blockHashes.getLast?.toExcept "ERROR : block hashes is empty"
  let ⟨stHistory, _⟩ ←
    processUncheckedSystemTransaction benvBeacon
      historyStorageAddress
      lastHash.toBytes
  let benvHistory := benvBeacon.withState stHistory
  let ⟨benvTxs, boutTxs⟩ ←
    applyTransactions (← txs.mapM decodeTx).putIndex benvHistory .init
  let ⟨stWds, boutWds⟩ :=
    processWithdrawals benvTxs boutTxs wds
  processGeneralPurposeRequests (benvTxs.withState stWds) boutWds

def getLast256BlockHashes (chain : BlockChain) : List B256 :=
  match chain.blocks.reverse.take 255 with
  | [] => []
  | block :: blocks =>
    let hash : B256 := (Header.toBLT block.header).toBytes.keccak
    let hashes : List B256 :=
      (block :: blocks).map <| fun x => x.header.parentHash
    (hash :: hashes).reverse

--------------- RETAINED HISTORY ---------------

-- P0.2's history half. `getLast256BlockHashes` recomputes only the tip's own
-- header hash and reads every other entry out of a retained block's
-- `parentHash` field, so the ancestry `BLOCKHASH` reports is only as
-- trustworthy as those fields. The predicates below say exactly what has to
-- hold of a snapshot's retained suffix for the lookup to be correct, and the
-- theorems after them prove it is -- for a full window, for an early chain,
-- and at the truncated boundary.

/-- Two adjacent retained blocks: consecutive numbering and an authenticated
parent-hash link. This carries clauses (1) and (2) of the design report's
`RetainedHistoryValid`; clause (2) is what makes the `BLOCKHASH` window
provable at all, because every entry below the tip *is* one of these fields. -/
def Block.Links (prev next : Block) : Prop :=
  next.header.number = prev.header.number + 1 ∧
  next.header.parentHash = prev.header.hash

instance (prev next : Block) : Decidable (Block.Links prev next) := by
  unfold Block.Links; infer_instance

/-- The retained window a snapshot's execution actually reads, oldest-first:
the 255 newest blocks. `appendBlock` keeps exactly that many, so for a chain
built by state transitions this is the whole block list. -/
def BlockChain.retained (chain : BlockChain) : List Block :=
  (chain.blocks.reverse.take 255).reverse

/-- A snapshot's retained history is valid when its blocks are consecutively
numbered and hash-linked, their headers are wire-representable, and it covers
enough ancestry for the `BLOCKHASH` window: either 255 blocks are retained, or
the chain still begins at block zero. The last clause is the design report's
"retention of at least `min 255 n`" written in terms of the oldest retained
header, which is the form the window proof consumes. -/
def BlockChain.RetainedHistoryValid (chain : BlockChain) : Prop :=
  chain.blocks.IsChain Block.Links ∧
  (∀ b ∈ chain.blocks, b.header.WireWellFormed) ∧
  (255 ≤ chain.blocks.length ∨ ∀ b ∈ chain.blocks.head?, b.header.number = 0)

instance (chain : BlockChain) : Decidable (chain.RetainedHistoryValid) := by
  unfold BlockChain.RetainedHistoryValid; infer_instance

/-- The shape of the hash list, stated once so no later proof has to unfold
the `match`: the retained blocks' `parentHash` fields, oldest-first, followed
by the tip's own recomputed header hash. -/
theorem getLast256BlockHashes_eq {chain : BlockChain} {b : Block} {bs : List Block}
    (hN : chain.blocks.reverse.take 255 = b :: bs) :
    getLast256BlockHashes chain
      = chain.retained.map (fun x => x.header.parentHash) ++ [b.header.hash] := by
  unfold getLast256BlockHashes BlockChain.retained
  rw [hN]
  simp [Header.hash, List.map_reverse]

/-- Below the tip, every entry is a retained block's `parentHash` field. -/
theorem getLast256BlockHashes_getD_lt {chain : BlockChain} {b : Block}
    {bs : List Block} (hN : chain.blocks.reverse.take 255 = b :: bs) {j : Nat}
    (hj : j < chain.retained.length) :
    (getLast256BlockHashes chain).getD j 0
      = chain.retained[j].header.parentHash := by
  rw [getLast256BlockHashes_eq hN, List.getD,
    List.getElem?_append_left (by simpa using hj),
    List.getElem?_eq_getElem (by simpa using hj)]
  simp

/-- The last entry is the tip's own recomputed header hash. -/
theorem getLast256BlockHashes_getD_last {chain : BlockChain} {b : Block}
    {bs : List Block} (hN : chain.blocks.reverse.take 255 = b :: bs) :
    (getLast256BlockHashes chain).getD chain.retained.length 0 = b.header.hash := by
  rw [getLast256BlockHashes_eq hN, List.getD,
    List.getElem?_append_right (by simp)]
  simp

/-- Consecutive numbering in closed form: the `i`th retained block sits `i`
above the oldest one. -/
theorem Block.isChain_number {l : List Block} (h : l.IsChain Block.Links) :
    ∀ {i : Nat} (hi : i < l.length) (h0 : 0 < l.length),
      l[i].header.number = l[0].header.number + i := by
  intro i
  induction i with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro hi h0
    have hlink := (List.isChain_iff_getElem.mp h) n (by omega)
    rw [hlink.1, ih (by omega) h0]
    omega

/-- The authenticated link: every retained block's `parentHash` is the true
header hash of the block below it. -/
theorem Block.isChain_parentHash {l : List Block} (h : l.IsChain Block.Links)
    {i : Nat} (hi : i + 1 < l.length) :
    l[i + 1].header.parentHash = l[i].header.hash :=
  ((List.isChain_iff_getElem.mp h) i hi).2

/-- Consecutive numbering makes the height a key: a retained history holds at
most one block per height. -/
theorem Block.isChain_number_inj {l : List Block} (h : l.IsChain Block.Links)
    {x y : Block} (hx : x ∈ l) (hy : y ∈ l)
    (hn : x.header.number = y.header.number) : x = y := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  have h0 : 0 < l.length := by omega
  have hxi := Block.isChain_number h hi h0
  have hyj := Block.isChain_number h hj h0
  have hij : i = j := by omega
  subst hij; rfl

/-- A newest-first window, read back oldest-first, is a suffix. -/
theorem Block.take_reverse_suffix (l : List Block) (n : Nat) :
    (l.reverse.take n).reverse <:+ l := by
  have h : l.reverse.take n <+: l.reverse := List.take_prefix _ _
  simpa using List.reverse_prefix.mp (by simpa using h)

/-- The retained window is a suffix of the block list. -/
theorem BlockChain.retained_suffix (chain : BlockChain) :
    chain.retained <:+ chain.blocks :=
  Block.take_reverse_suffix _ _

/-- A nonempty list's newest-first window is headed by its last element. -/
theorem Block.take_reverse_eq_cons {l : List Block} {x : Block} {n : Nat}
    (hn : 0 < n) (h : l.getLast? = some x) :
    ∃ bs, l.reverse.take n = x :: bs := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hr : l.reverse.head? = some x := by
    rw [List.head?_reverse]; exact h
  match hl : l.reverse with
  | [] => rw [hl] at hr; simp at hr
  | y :: ys =>
    rw [hl] at hr
    simp only [List.head?_cons, Option.some.injEq] at hr
    subst hr
    exact ⟨ys.take m, rfl⟩

/-- A nonempty chain's retained window is headed, newest-first, by its tip. -/
theorem BlockChain.take_reverse_eq_cons {chain : BlockChain} {tip : Block}
    (h : chain.blocks.getLast? = some tip) :
    ∃ bs, chain.blocks.reverse.take 255 = tip :: bs :=
  Block.take_reverse_eq_cons (by omega) h

theorem BlockChain.retained_length (chain : BlockChain) :
    chain.retained.length = min 255 chain.blocks.length := by
  unfold BlockChain.retained
  simp

/-- Below the retention bound nothing is dropped, so the oldest retained block
is the chain's own first block. -/
theorem BlockChain.retained_eq_blocks {chain : BlockChain}
    (h : chain.blocks.length ≤ 255) : chain.retained = chain.blocks := by
  unfold BlockChain.retained
  rw [List.take_of_length_le (by simpa using h)]
  simp

/-- The `BLOCKHASH` window theorem.

For a snapshot with valid retained history and a child block being executed at
`number = tip.number + 1`, every height the opcode admits --
`blockNumber < number ≤ blockNumber + 256` -- resolves to an authenticated
ancestry hash: either the true header keccak of a retained block at exactly
that height, or, one step below the oldest retained block, that block's own
`parentHash`. The second case is what makes the list reach 256 entries from
255 retained blocks; it is the only entry whose subject the snapshot no longer
carries, and it is authenticated by the retained header that names it.

Both truncated and early-chain windows are covered: with 255 blocks retained
the window's lower end is exactly the oldest retained block's parent, and
below the retention bound the chain still starts at block zero, so no admitted
height falls off the list and the index never truncates. -/
theorem getLast256BlockHashes_window {chain : BlockChain}
    (hv : chain.RetainedHistoryValid) {tip : Block}
    (htip : chain.blocks.getLast? = some tip) {number blockNumber : Nat}
    (hnum : number = tip.header.number + 1)
    (hlo : blockNumber < number) (hhi : number ≤ blockNumber + 256) :
    (∃ b ∈ chain.retained, b.header.number = blockNumber ∧
        (getLast256BlockHashes chain).getD
          ((getLast256BlockHashes chain).length - (number - blockNumber)) 0
            = b.header.hash) ∨
      (∃ oldest ∈ chain.retained.head?, blockNumber + 1 = oldest.header.number ∧
        (getLast256BlockHashes chain).getD
          ((getLast256BlockHashes chain).length - (number - blockNumber)) 0
            = oldest.header.parentHash) := by
  obtain ⟨bs, hN⟩ := BlockChain.take_reverse_eq_cons htip
  have hEq := getLast256BlockHashes_eq hN
  have hRdef : chain.retained = (tip :: bs).reverse := by
    unfold BlockChain.retained; rw [hN]
  have hm : chain.retained.length = bs.length + 1 := by rw [hRdef]; simp
  have h0 : 0 < chain.retained.length := by omega
  have hchain : chain.retained.IsChain Block.Links :=
    hv.1.suffix chain.retained_suffix
  have hlast? : chain.retained.getLast? = some tip := by
    rw [hRdef, List.getLast?_reverse]; rfl
  have hlast : chain.retained[chain.retained.length - 1] = tip := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast?
    exact Option.some.inj hlast?
  have htipnum : tip.header.number
      = chain.retained[0].header.number + (chain.retained.length - 1) := by
    have hnum0 :=
      Block.isChain_number hchain (i := chain.retained.length - 1) (by omega) h0
    rw [hlast] at hnum0
    exact hnum0
  have hhead : chain.retained.head? = some chain.retained[0] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
  have hlen1 : (getLast256BlockHashes chain).length = chain.retained.length + 1 := by
    rw [getLast256BlockHashes_eq hN]; simp
  -- Coverage: no admitted height falls below the oldest retained block's own
  -- parent. With a full window that is the arithmetic of 255 retained blocks;
  -- below it, the chain still starts at block zero.
  have hcov : chain.retained[0].header.number ≤ blockNumber + 1 := by
    rcases Nat.lt_or_ge chain.blocks.length 255 with hlen | hlen
    · have hret : chain.retained = chain.blocks :=
        chain.retained_eq_blocks (by omega)
      have hzero := hv.2.2.resolve_left (by omega) chain.retained[0]
        (by rw [← hret]; exact hhead)
      omega
    · have h255 : chain.retained.length = 255 := by
        rw [chain.retained_length]; omega
      omega
  rcases Nat.lt_or_ge blockNumber chain.retained[0].header.number with hc | hc
  · -- The truncated boundary: the entry is the oldest retained block's own
    -- authenticated `parentHash`, and it is the only such entry.
    right
    refine ⟨chain.retained[0], hhead, by omega, ?_⟩
    have hidx : (getLast256BlockHashes chain).length - (number - blockNumber) = 0 := by
      omega
    rw [hidx, getLast256BlockHashes_getD_lt hN h0]
  · -- A height the window still retains a block for.
    left
    obtain ⟨k, hk⟩ : ∃ k, blockNumber = chain.retained[0].header.number + k :=
      ⟨blockNumber - chain.retained[0].header.number, by omega⟩
    have hidx : (getLast256BlockHashes chain).length - (number - blockNumber)
        = k + 1 := by omega
    rcases Nat.lt_or_ge (k + 1) chain.retained.length with hlt | hge
    · refine ⟨chain.retained[k], List.getElem_mem (by omega), ?_, ?_⟩
      · have := Block.isChain_number hchain (i := k) (by omega) h0
        omega
      · rw [hidx, getLast256BlockHashes_getD_lt hN hlt,
          Block.isChain_parentHash hchain hlt]
    · have hkeq : k + 1 = chain.retained.length := by omega
      refine ⟨tip, hlast ▸ List.getElem_mem (by omega), by omega, ?_⟩
      rw [hidx, hkeq, getLast256BlockHashes_getD_last hN]

/-- The consumer form of the window theorem: whenever the requested height is
one the retained history still holds a block for, `BLOCKHASH` returns that
block's true header keccak -- never a stale, defaulted, or off-by-one entry. -/
theorem getLast256BlockHashes_of_mem_retained {chain : BlockChain}
    (hv : chain.RetainedHistoryValid) {tip b : Block}
    (htip : chain.blocks.getLast? = some tip) (hb : b ∈ chain.retained)
    {number : Nat} (hnum : number = tip.header.number + 1)
    (hlo : b.header.number < number) (hhi : number ≤ b.header.number + 256) :
    (getLast256BlockHashes chain).getD
      ((getLast256BlockHashes chain).length - (number - b.header.number)) 0
        = b.header.hash := by
  have hchain : chain.retained.IsChain Block.Links :=
    hv.1.suffix chain.retained_suffix
  rcases getLast256BlockHashes_window hv htip hnum hlo hhi with
    ⟨b', hb', hnum', hval⟩ | ⟨oldest, hold, hnum', _⟩
  · rw [hval, Block.isChain_number_inj hchain hb' hb hnum']
  · -- The boundary entry names a height *below* every retained block, so it
    -- cannot be the height of one.
    exfalso
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have h0 : 0 < chain.retained.length := by omega
    have hhead : chain.retained.head? = some chain.retained[0] := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
    rw [hhead, Option.mem_def, Option.some.injEq] at hold
    subst hold
    have := Block.isChain_number hchain hi h0
    omega

def computeRequestsHash (requests : List Bytes) : B256 :=
  -- EIP-7685 commits the SHA-256 digest of each type-prefixed request, then
  -- hashes their concatenation once more.  This is deliberately not the EVM
  -- Keccak primitive used by transaction and trie commitments.
  let hashes := requests.map (fun r => r.sha256.toBytes)
  Bytes.sha256 <| List.flatten hashes

def State.root (w : State) : B256 :=
  let keyVals := (List.map accountToKeyVal w.toList)
  let finalNTB : NTB := Std.TreeMap.ofList keyVals _
  trie finalNTB

def stateTransitionChecks (bout : BlockOutput) (header : Header)
    (transactionsRoot blockStateRoot receiptRoot : B256)
    (blockLogsBloom : Bytes) (withdrawalsRoot requestsHash : B256) :
    Except String Unit := do
  if bout.blockGasUsed ≠ header.gasUsed then
    .error
      s!"{gasUsedMismatchTag} : computed block gas used = {bout.blockGasUsed} ≠ \
         header block gas used = {header.gasUsed}"
  if transactionsRoot ≠ header.txsRoot then
    .error
      s!"{transactionsRootTag} : computed transactions root = {transactionsRoot} \
         ≠ header transactions root = {header.txsRoot}"
  if blockStateRoot ≠ header.stateRoot then
    .error
      s!"{stateRootTag} : computed state root = {blockStateRoot} ≠ \
         header state root = {header.stateRoot}"
  if receiptRoot ≠ header.receiptRoot then
    .error
      s!"{receiptsRootTag} : computed receipts root = {receiptRoot} ≠ \
         header receipts root = {header.receiptRoot}"
  if blockLogsBloom ≠ header.bloom then
    .error
      s!"{logBloomTag} : computed logs bloom ≠ header logs bloom"
  if withdrawalsRoot ≠ header.withdrawalsRoot then
    .error
      s!"{withdrawalsRootTag} : computed withdrawals root = {withdrawalsRoot} ≠ \
         header withdrawals root = {header.withdrawalsRoot}"
  if bout.blobGasUsed ≠ header.blobGasUsed then
    .error
      s!"{blobGasUsedTag} : computed blob gas used = {bout.blobGasUsed} ≠ \
         header blob gas used = {header.blobGasUsed}"
  if some requestsHash ≠ header.requestsHash then
    .error
      s!"{requestsHashTag} : computed requests hash = {requestsHash} ≠ \
         header requests hash = {header.requestsHash}"

def initBenvStat (rules : ForkRules) (chain : BlockChain) (header : Header) :
    BenvStat :=
  {
    rules := rules,
    chainId := chain.chainId,
    origState := chain.state,
    blockGasLimit := header.gasLimit,
    blockHashes := getLast256BlockHashes chain,
    coinbase := header.coinbase,
    number := header.number,
    baseFeePerGas := header.baseFeePerGas,
    time := header.timestamp.toB256,
    prevRandao := header.prevRandao,
    excessBlobGas := header.excessBlobGas,
    parentBeaconBlockRoot := header.parentBeaconBlockRoot
  }

def initBenv (rules : ForkRules) (chain : BlockChain) (header : Header) : Benv :=
  {
    state := chain.state,
    createdAccounts := .emptyWithCapacity,
    stat := initBenvStat rules chain header
  }

def getTransactionsRoot (bout : BlockOutput) : B256 :=
  let aux (arg : Bytes × Tx) : (Bytes × Bytes) :=
    let txPrefix : Bytes :=
      match arg.snd.type with
      | .zero _ _ => []
      | .one _ _ _ _ => [0x01]
      | .two _ _ _ _ _ => [0x02]
      | .three _ _ _ _ _ _ _ => [0x03]
      | .four _ _ _ _ _ _ => [0x04]
    ⟨arg.fst.toNibbles, txPrefix ++ arg.snd.toBLT.toBytes⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.transactionsTrie.toList) _

def getReceiptRoot (bout : BlockOutput) : B256 :=
  let aux : (Bytes × Fin 5 × Receipt) → (Bytes × Bytes)
    | ⟨key, type, receipt⟩ => ⟨key.toNibbles, type.val.toBytes ++ receipt.toBLT.toBytes⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.receiptsTrie.toList) _

def getWithdrawalsRoot (bout : BlockOutput) : B256 :=
  let aux (arg : Bytes × Withdrawal) : Bytes × Bytes :=
    ⟨arg.fst.toNibbles, arg.snd.toBLT.toBytes⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.withdrawalsTrie.toList) _

def stateTransitionOmmersCheck (ommers : List Header) : Except String Unit := do
  if ¬ommers.isEmpty then do
    .error
      s!"{ommersOverParisTag} : block body contains {ommers.length} ommer(s), \
         which is impossible after Paris"

def appendBlock (blks : List Block) (blk : Block) : List Block :=
  (blk :: blks.reverse.take 254).reverse

/-- Retention, measured: the 254 newest blocks kept, oldest-first, then the
new one. -/
theorem appendBlock_eq (blks : List Block) (blk : Block) :
    appendBlock blks blk = (blks.reverse.take 254).reverse ++ [blk] := by
  unfold appendBlock
  simp

theorem appendBlock_getLast? (blks : List Block) (blk : Block) :
    (appendBlock blks blk).getLast? = some blk := by
  rw [appendBlock_eq]
  simp

theorem appendBlock_ne_nil (blks : List Block) (blk : Block) :
    appendBlock blks blk ≠ [] := by
  rw [appendBlock_eq]
  simp

/-- Retained-history validity is preserved by an append that links to the tip.

This is the whole reason the checked transition never has to re-derive
ancestry: the child's `validateHeader` already established both halves of
`Block.Links` against the parent header, and the canonical envelope already
established the child header's wire well-formedness. -/
theorem BlockChain.retainedHistoryValid_appendBlock {chain chain' : BlockChain}
    {tip blk : Block}
    (hv : chain.RetainedHistoryValid) (htip : chain.blocks.getLast? = some tip)
    (hlink : Block.Links tip blk) (hwire : blk.header.WireWellFormed)
    (hb : chain'.blocks = appendBlock chain.blocks blk) :
    chain'.RetainedHistoryValid := by
  have hsuf : (chain.blocks.reverse.take 254).reverse <:+ chain.blocks :=
    Block.take_reverse_suffix _ _
  have hblocks : chain'.blocks = (chain.blocks.reverse.take 254).reverse ++ [blk] := by
    rw [hb, appendBlock_eq]
  obtain ⟨kept, hkept⟩ := Block.take_reverse_eq_cons (n := 254) (by omega) htip
  have hkeptlast : ((chain.blocks.reverse.take 254).reverse).getLast? = some tip := by
    rw [List.getLast?_reverse, hkept]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hblocks]
    refine (hv.1.suffix hsuf).append (List.IsChain.singleton _) ?_
    intro x hx y hy
    rw [hkeptlast, Option.mem_def, Option.some.injEq] at hx
    rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hx; subst hy
    exact hlink
  · rw [hblocks]
    intro b hb
    rcases List.mem_append.mp hb with h | h
    · exact hv.2.1 b (hsuf.subset h)
    · rw [List.mem_singleton.mp h]; exact hwire
  · -- Coverage: either the append filled the window, or the chain still
    -- begins where it began.
    rcases Nat.lt_or_ge chain.blocks.length 254 with hlen | hlen
    · right
      have hne : chain.blocks ≠ [] := by
        intro h; rw [h] at htip; simp at htip
      obtain ⟨x, xs, hcb⟩ : ∃ x xs, chain.blocks = x :: xs := by
        cases hc : chain.blocks with
        | nil => exact absurd hc hne
        | cons y ys => exact ⟨y, ys, rfl⟩
      have hall : (chain.blocks.reverse.take 254).reverse = chain.blocks := by
        rw [List.take_of_length_le (by simpa using Nat.le_of_lt hlen)]
        simp
      have hzero := hv.2.2.resolve_left (by omega)
      rw [hblocks, hall, hcb]
      intro b hb
      simp only [List.cons_append, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hb
      subst hb
      exact hzero _ (by rw [hcb]; rfl)
    · left
      rw [hblocks]
      simp only [List.length_append, List.length_reverse, List.length_take,
        List.length_cons, List.length_nil]
      omega

/-- The block state transition under an explicit rule set.

This is the whole implementation; every other state-transition entry point
below only decides *which* rules to hand it. -/
def stateTransitionWith (rules : ForkRules) (ch : BlockChain) (block : Block) :
  Except String BlockChain := do
  validateHeader rules ch block.header
  stateTransitionOmmersCheck block.ommers
  let benv : Benv := initBenv rules ch block.header
  let ⟨st, bout⟩ ← applyBody benv block.txs block.wds
  let blockStateRoot : B256 := st.root
  let transactionsRoot : B256 := getTransactionsRoot bout
  let receiptRoot : B256 := getReceiptRoot bout
  let blockLogsBloom : Bytes := logsBloom bout.blockLogs
  let withdrawalsRoot : B256 := getWithdrawalsRoot bout
  let requestsHash := computeRequestsHash bout.requests
  stateTransitionChecks bout block.header
    transactionsRoot blockStateRoot receiptRoot
    blockLogsBloom withdrawalsRoot requestsHash
  .ok ⟨appendBlock ch.blocks block, st, ch.chainId⟩

/-- The block state transition at an explicitly named fork.

This is the entry point for static fixture suites, which state their fork
rather than deriving it. A fork whose rules this build does not implement
fails here with `UnsupportedForkError`; it never falls back to Prague. -/
def stateTransitionAt (f : Fork) (ch : BlockChain) (block : Block) :
    Except String BlockChain := do
  stateTransitionWith (← f.rules) ch block

/-- Whether a configuration's declared chain identity agrees with a snapshot's.

P0.1: a configuration can be a perfectly valid, perfectly usable schedule and
still name a different chain than the snapshot it is handed. This is separate
from `ChainConfig.validate`, which never inspects `chainId` at all, and it is
the outer context channel, not a verdict about any candidate block -- a
contradictory caller context is not evidence that a block is invalid.
Declared here, downstream of `Jaune/Fork.lean`, because this is the first
module where `BlockChain` exists alongside `ChainConfig` (design report §6).
Neither configured entry point below may proceed past a mismatch: this check
runs first in both, and it never repairs a mismatch by preferring one side. -/
def ChainConfig.checkChainId (cfg : ChainConfig) (chain : BlockChain) :
    Except ChainContextError Unit :=
  if cfg.chainId = chain.chainId then
    .ok ()
  else
    .error (.chainIdMismatch cfg.chainId chain.chainId)

/-- The block state transition on a configured chain, deriving the active fork
from the block's timestamp and the chain's activation schedule.

Checks the configuration against the snapshot's chain identity before doing
anything else -- P0.1's fix -- then proceeds exactly as before. -/
def stateTransitionUsing (cfg : ChainConfig) (ch : BlockChain) (block : Block) :
    Except String BlockChain := do
  Except.mapError ChainContextError.render (cfg.checkChainId ch)
  stateTransitionWith (← cfg.rulesAt block.header.timestamp) ch block

/-- The Prague state transition.

Retained with its original name, type, and behaviour. Prague is permanent
supported protocol, not scaffolding, and downstream proofs state their results
about this name. -/
def stateTransition (ch : BlockChain) (block : Block) :
  Except String BlockChain :=
  stateTransitionWith pragueRules ch block

def BLT.toExStrWithdrawal : BLT → Except String Withdrawal
  | .list [
      .bytes globalIndex,
      .bytes validatorIndex,
      .bytes recipient,
      .bytes amount
    ] => do
    -- Check every untrusted field before constructing the withdrawal. In
    -- particular, `Bytes.toUInt64` truncates modulo 2^64, so it may only see the
    -- byte string returned by the at-most-eight-byte decoder.
    let globalIndex ← globalIndex.toRlpB64 "withdrawal globalIndex"
    let validatorIndex ← validatorIndex.toRlpB64 "withdrawal validatorIndex"
    let recipient ← recipient.toRlpAdr "withdrawal recipient"
    -- EIP-4895: `amount` is a 64-bit Gwei scalar on the wire, even though the
    -- `Withdrawal` field stores it as 256 bits for balance arithmetic.
    let amount ← amount.toRlpB64 "withdrawal amount"
    .ok {
      globalIndex := globalIndex,
      validatorIndex := validatorIndex,
      recipient := recipient,
      amount := amount.toNat.toB256
    }
  | _ =>
    .error <| rlpStructureError "withdrawal"
      "expected a list of four byte-string fields"

/-- Strict withdrawal-decoder soundness: the amount a decoded withdrawal
carries always fits its 64-bit wire type, even though the field is 256 bits
wide. -/
theorem BLT.toExStrWithdrawal_wireWellFormed {blt : BLT} {w : Withdrawal}
    (h : blt.toExStrWithdrawal = .ok w) : w.WireWellFormed := by
  unfold BLT.toExStrWithdrawal at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    exact UInt64.toNat_toB256_high _
  · exact absurd h (by simp)

def BLT.toExStrTx : BLT → Except String Tx
  | .list [
      .bytes nonce,
      .bytes gasPrice,
      .bytes gas,
      .bytes receiver,
      .bytes value,
      .bytes data,
      .bytes v,
      .bytes r,
      .bytes s
    ] => do
    let nonce ← nonce.toRlpB64 "legacy transaction nonce"
    let gasPrice ← gasPrice.toRlpNat "legacy transaction gasPrice" 32
    let gas ← gas.toRlpNat "legacy transaction gas" 32
    let receiver ← receiver.toRlpReceiver "legacy transaction receiver"
    let value ← value.toRlpNat "legacy transaction value" 32
    let v ← v.toRlpNat "legacy transaction v" 32
    -- Validate signature scalars before sender recovery, but retain their
    -- minimally encoded byte representation so valid legacy signing and
    -- encoding behavior is unchanged.
    let _ ← r.toRlpB256 "legacy transaction r"
    let _ ← s.toRlpB256 "legacy transaction s"
    .ok {
      nonce := nonce,
      gas := gas
      value := value,
      data := data,
      v := v,
      r := r,
      s := s,
      type := .zero gasPrice receiver
    }
  | .list _ =>
    .error <| rlpStructureError "legacy transaction"
      "expected a list of nine byte-string fields"
  | .bytes xs => xs.toExStrTx

/-- Strict legacy-transaction-decoder soundness. A *list*-shaped transaction
item is the legacy route, so what it yields is both wire-well-formed and of
legacy type -- which is exactly `TxEntry.WireWellFormed` on the decoded side of
a block body's transaction slot. The typed route reaches this decoder only
through a byte string, and never produces a `.zero` transaction. -/
theorem BLT.toExStrTx_list_wireWellFormed {bs : List BLT} {tx : Tx}
    (h : (BLT.list bs).toExStrTx = .ok tx) :
    Tx.WireWellFormed tx ∧ tx.type.isLegacy = true := by
  unfold BLT.toExStrTx at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩ <;>
      first
        | exact Bytes.toRlpNat_lt_two_pow_256 (by assumption)
        | exact Bytes.toRlpB256_eq_ok (by assumption)
  · exact absurd h (by simp)
  · exact absurd (by assumption : BLT.list bs = BLT.bytes _) (by simp)

def BLT.toExStrBlock : BLT → Except String Block
  | BLT.list [
      HeaderBLT,
      .list TxBLTs,
      .list OmmerBLTs,
      .list WithdrawalBLTs
    ] => do
    let header ← HeaderBLT.toExStrHeader
    let aux : BLT → Except String (Bytes ⊕ Tx)
      | blt@(.list _) => blt.toExStrTx <&> .inr
      | .bytes xs => .ok <| .inl xs
    let txs ← List.mapM aux TxBLTs
    let ommers ← List.mapM BLT.toExStrHeader OmmerBLTs
    let withdrawals ← List.mapM BLT.toExStrWithdrawal WithdrawalBLTs
    .ok {
      header := header,
      txs := txs,
      ommers := ommers,
      wds := withdrawals
    }
  | .list [_, .list _, .list _] =>
    .error
      s!"{rlpWithdrawalsNotReadTag} : post-Shanghai block body omits the withdrawals list"
  | _ =>
    .error <| rlpStructureError "block"
      "expected [header, transactions, ommers, withdrawals] lists"

/-- Strict block-decoder soundness: a decoded block is structurally canonical
componentwise. Note what this deliberately does *not* say about a byte-string
transaction slot -- it stays opaque here, and is decoded at the existing point
inside `applyBody`, so the staged typed-transaction rule (design report §7) is
preserved and no error precedence moves. -/
theorem BLT.toExStrBlock_rlpCanonical {blt : BLT} {b : Block}
    (h : blt.toExStrBlock = .ok b) : b.RlpCanonical := by
  unfold BLT.toExStrBlock at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨BLT.toExStrHeader_wireWellFormed (by assumption), ?_, ?_, ?_⟩
    · intro o ho
      obtain ⟨blt', hblt'⟩ := List.mapM_except_eq_ok_mem (by assumption) o ho
      exact BLT.toExStrHeader_wireWellFormed hblt'
    · intro w hw
      obtain ⟨blt', hblt'⟩ := List.mapM_except_eq_ok_mem (by assumption) w hw
      exact BLT.toExStrWithdrawal_wireWellFormed hblt'
    · intro e he
      obtain ⟨blt', hblt'⟩ := List.mapM_except_eq_ok_mem (by assumption) e he
      cases blt' with
      | bytes ys =>
        simp only [Except.ok.injEq] at hblt'
        subst hblt'
        trivial
      | list ls =>
        obtain ⟨tx, htx, he'⟩ := Except.bind_eq_ok hblt'
        simp only [Except.ok.injEq] at he'
        subst he'
        exact BLT.toExStrTx_list_wireWellFormed htx
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-
rlpToBlock is equivalent to json_to_block from execution-specs.
why does it accept the RLP bytes as input, and not the whole JSON?
the justification is that json_to_block expects the RLP bytes to be
always available, and always uses *only* the RLP bytes to obtain the
block, ignoring everything else in the JSON (the code path that deals
with nonexistent RLP bytes exists, but is unreachable). its return
type also omits the RLP bytes, since this is identical to the input.
-/
def rlpToBlock (rlp : Bytes) : Except String (Block × B256) := do
  let block_blt ← (Bytes.toBLT? rlp).toExcept <|
    rlpStructureError "block RLP" "cannot decode the outer RLP item"
  let block ← block_blt.toExStrBlock
  let canonicalRlp := block.toBLT.toBytes
  if rlp ≠ canonicalRlp then
    .error
      s!"{rlpRoundTripTag} : decoded block does not re-encode byte-for-byte"
  .ok ⟨block, (Header.toBLT block.header).toBytes.keccak⟩

--------------- THE CANONICAL OUTER-BLOCK ENVELOPE ---------------

/-- The hash `rlpToBlock` returns is always the keccak of the decoded header's
canonical encoding. It is therefore *derivable* from the decoded block and was
never independent evidence, which is why the import core below takes an
envelope instead of a separate hash argument. -/
theorem rlpToBlock_headerHash {raw : Bytes} {block : Block} {hash : B256}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) :
    hash = (Header.toBLT block.header).toBytes.keccak := by
  unfold rlpToBlock at h
  repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, herr, _⟩ := Except.bind_eq_ok h
    exact absurd herr (by simp)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- A successful strict decode proves the decoded block re-encodes to exactly
the bytes supplied -- P0.3's first acceptance criterion. -/
theorem rlpToBlock_canonical {raw : Bytes} {block : Block} {hash : B256}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) : block.toBLT.toBytes = raw := by
  unfold rlpToBlock at h
  repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, herr, _⟩ := Except.bind_eq_ok h
    exact absurd herr (by simp)
  · rename_i hne
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact (not_not.mp hne).symm

/-- A successful strict decode is structurally sound. -/
theorem rlpToBlock_rlpCanonical {raw : Bytes} {block : Block} {hash : B256}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) : block.RlpCanonical := by
  unfold rlpToBlock at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨b, hb, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, herr, _⟩ := Except.bind_eq_ok h
    exact absurd herr (by simp)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact BLT.toExStrBlock_rlpCanonical hb

/-- A canonical outer block: the bytes a peer supplied, the block the strict
decoder produced from them, and the two pieces of evidence that make the pair
trustworthy -- that the block *is* the strict decoder's image of those bytes,
and that it re-encodes to them byte for byte.

The constructor is private. The only ways to obtain one are the strict decoder
(`CanonicalBlock.ofRlp?`) and the evidence-taking smart constructor
(`CanonicalBlock.ofDecode`), which demands the decoder equation itself, so a
caller cannot fabricate the evidence fields. Eliminators are exported:
`raw`, `block`, `headerHash`, `rawSize`, and the theorems below.

`raw` is retained rather than reconstructed because EIP-7934 depends on the
*supplied* size; re-encoding is evidence of canonicality, never a substitute
for the size observation (fixed decision 4). -/
structure CanonicalBlock : Type where
  private mk ::
  /-- The original RLP bytes. -/
  raw : Bytes
  /-- The block the strict decoder produced from `raw`. -/
  block : Block
  /-- Strict-decoder-image evidence. -/
  decoded :
    rlpToBlock raw = .ok ⟨block, (Header.toBLT block.header).toBytes.keccak⟩
  /-- Exact re-encoding evidence. -/
  canonical : block.toBLT.toBytes = raw

/-- The checked smart constructor: an envelope may only be built from the
strict decoder's own equation. -/
def CanonicalBlock.ofDecode {raw : Bytes} {block : Block} {hash : B256}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) : CanonicalBlock :=
  { raw := raw
    block := block
    decoded := by rw [rlpToBlock_headerHash h] at h; exact h
    canonical := rlpToBlock_canonical h }

/-- Strict decode of untrusted bytes into the envelope. The diagnostic on the
failure side is exactly the one `rlpToBlock` produces; this constructor adds no
second decoder and no second vocabulary. -/
def CanonicalBlock.ofRlp? (raw : Bytes) : Option CanonicalBlock :=
  match h : rlpToBlock raw with
  | .ok ⟨_, _⟩ => some (CanonicalBlock.ofDecode h)
  | .error _ => none

/-- The block header hash, *derived* from the envelope. -/
def CanonicalBlock.headerHash (cb : CanonicalBlock) : B256 :=
  (Header.toBLT cb.block.header).toBytes.keccak

/-- The authoritative original RLP size, the one EIP-7934 observes. -/
def CanonicalBlock.rawSize (cb : CanonicalBlock) : Nat := cb.raw.length

/-- Envelope inversion for downstream proofs: an envelope is exactly a
successful `rlpToBlock`. Stated so a client never has to unfold the structure
or the decoder. -/
theorem CanonicalBlock.rlpToBlock_eq (cb : CanonicalBlock) :
    rlpToBlock cb.raw = .ok ⟨cb.block, cb.headerHash⟩ := cb.decoded

/-- Structural soundness of the envelope. -/
theorem CanonicalBlock.rlpCanonical (cb : CanonicalBlock) :
    cb.block.RlpCanonical :=
  rlpToBlock_rlpCanonical cb.decoded

/-- The envelope's re-encoding, as an eliminator. -/
theorem CanonicalBlock.toBytes_eq (cb : CanonicalBlock) :
    cb.block.toBLT.toBytes = cb.raw := cb.canonical

theorem CanonicalBlock.rawSize_eq (cb : CanonicalBlock) :
    cb.rawSize = cb.raw.length := rfl

/-- Introduction: strict decode succeeds exactly when an envelope exists, and
the envelope it yields carries those very bytes and that very block. -/
theorem CanonicalBlock.ofRlp?_eq_some {raw : Bytes} {block : Block} {hash : B256}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) :
    ∃ cb : CanonicalBlock,
      CanonicalBlock.ofRlp? raw = some cb ∧ cb.raw = raw ∧ cb.block = block := by
  unfold CanonicalBlock.ofRlp?
  split
  · rename_i f s hb
    rw [h] at hb
    simp only [Except.ok.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨_, rfl, rfl, rfl⟩
  · rename_i err herr
    rw [h] at herr
    exact absurd herr (by simp)

theorem CanonicalBlock.ofRlp?_eq_none {raw : Bytes} {err : String}
    (h : rlpToBlock raw = .error err) : CanonicalBlock.ofRlp? raw = none := by
  unfold CanonicalBlock.ofRlp?
  split
  · rename_i b hb
    rw [h] at hb
    exact absurd hb (by simp)
  · rfl

--------------- CHECKED SEMANTIC CONSTRUCTORS ---------------

-- The open `Header`/`Tx`/`Withdrawal`/`Block` records stay exactly as they
-- are, for proofs and for negative construction. What follows is the *checked*
-- ingress beside them: one wrapper per record, each with a private
-- constructor and a decidable admission test, so a hand-built value is
-- certified against the very predicate the strict decoder establishes -- never
-- trimmed, normalised, or defaulted into shape (fixed decision 1).

/-- A header certified wire-well-formed. -/
structure CheckedHeader : Type where
  private mk ::
  val : Header
  wireWellFormed : val.WireWellFormed

/-- Certify a hand-built header, or refuse it. -/
def CheckedHeader.ofHeader? (h : Header) : Option CheckedHeader :=
  if hw : h.WireWellFormed then some ⟨h, hw⟩ else none

/-- Certification from the strict decoder, with no second test. -/
def CheckedHeader.ofDecode {blt : BLT} {h : Header}
    (hd : blt.toExStrHeader = .ok h) : CheckedHeader :=
  ⟨h, BLT.toExStrHeader_wireWellFormed hd⟩

/-- A withdrawal certified wire-well-formed. -/
structure CheckedWithdrawal : Type where
  private mk ::
  val : Withdrawal
  wireWellFormed : val.WireWellFormed

def CheckedWithdrawal.ofWithdrawal? (w : Withdrawal) : Option CheckedWithdrawal :=
  if hw : w.WireWellFormed then some ⟨w, hw⟩ else none

def CheckedWithdrawal.ofDecode {blt : BLT} {w : Withdrawal}
    (hd : blt.toExStrWithdrawal = .ok w) : CheckedWithdrawal :=
  ⟨w, BLT.toExStrWithdrawal_wireWellFormed hd⟩

/-- A certified block-body transaction slot.

Its decoded side carries a wire-well-formed *legacy* transaction; its opaque
side carries typed envelope bytes, which stay undecoded until the existing
decode point inside `applyBody`, so no error precedence moves. There is no
third shape: a decoded *typed* transaction can never be a slot, because a
typed transaction's canonical block encoding is its envelope byte followed by
its payload rather than the legacy list. Admitting one is precisely the
`.inr Tx` trust bypass P0.3 removes; `Tx.toTypedEnvelope?` is the way a
hand-built typed transaction becomes a slot. -/
structure TxEnvelope : Type where
  private mk ::
  entry : Bytes ⊕ Tx
  wellFormed : TxEntry.WireWellFormed entry

/-- The opaque typed slot. Nothing is decoded here. -/
def TxEnvelope.ofTypedBytes (bs : Bytes) : TxEnvelope := ⟨.inl bs, trivial⟩

/-- The decoded legacy slot, from the strict decoder's own equation. -/
def TxEnvelope.ofLegacyDecode {ls : List BLT} {tx : Tx}
    (h : (BLT.list ls).toExStrTx = .ok tx) : TxEnvelope :=
  ⟨.inr tx, BLT.toExStrTx_list_wireWellFormed h⟩

/-- The raw compatibility constructor: it carries no evidence, so it validates
once, here, rather than leaving a slot to be trusted later. -/
def TxEnvelope.ofEntry? (e : Bytes ⊕ Tx) : Option TxEnvelope :=
  if h : TxEntry.WireWellFormed e then some ⟨e, h⟩ else none

/-- The envelope byte a typed transaction is carried under; `none` for legacy,
which has no envelope. -/
def TxType.envelopeByte : TxType → Option UInt8
  | .zero _ _ => none
  | .one _ _ _ _ => some 0x01
  | .two _ _ _ _ _ => some 0x02
  | .three _ _ _ _ _ _ _ => some 0x03
  | .four _ _ _ _ _ _ => some 0x04

/-- A hand-built typed transaction's route into a block body: its envelope
byte followed by its payload. Placing the same record directly as a decoded
slot would re-encode it through the legacy list, corrupting both the
transactions trie and the signing hash -- which is why that route does not
exist. Legacy transactions have no envelope and are refused here; they enter
as decoded slots through `TxEnvelope.ofEntry?`. -/
def Tx.toTypedEnvelope? (tx : Tx) : Option TxEnvelope :=
  tx.type.envelopeByte.map fun b => TxEnvelope.ofTypedBytes (b :: tx.toBLT.toBytes)

/-- A block certified structurally canonical componentwise. -/
structure CheckedBlock : Type where
  private mk ::
  val : Block
  rlpCanonical : val.RlpCanonical

def CheckedBlock.ofBlock? (b : Block) : Option CheckedBlock :=
  if h : b.RlpCanonical then some ⟨b, h⟩ else none

/-- Assemble a block from already-certified parts. No admission test is needed
because every part carries its own. -/
def CheckedBlock.ofParts (header : CheckedHeader) (txs : List TxEnvelope)
    (ommers : List CheckedHeader) (wds : List CheckedWithdrawal) : CheckedBlock :=
  { val :=
      { header := header.val
        txs := txs.map TxEnvelope.entry
        ommers := ommers.map CheckedHeader.val
        wds := wds.map CheckedWithdrawal.val }
    rlpCanonical := by
      refine ⟨header.wireWellFormed, ?_, ?_, ?_⟩
      · intro o ho
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp ho
        exact c.wireWellFormed
      · intro w hw
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hw
        exact c.wireWellFormed
      · intro e he
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp he
        exact c.wellFormed }

/-- Every canonical outer block is a checked block. -/
def CanonicalBlock.toChecked (cb : CanonicalBlock) : CheckedBlock :=
  ⟨cb.block, cb.rlpCanonical⟩

theorem CanonicalBlock.toChecked_val (cb : CanonicalBlock) :
    cb.toChecked.val = cb.block := rfl

/-- P0.3's trust bypass, discharged rather than relocated.

`decodeTx (.inr tx) = .ok tx` still holds -- revalidating a decoder-produced
legacy transaction late in `applyBody` is exactly what the plan forbids -- but
on the checked path it is no longer an *assumption*. Every decoded slot of a
canonical outer block is a wire-well-formed legacy transaction, so what
`decodeTx` returns there is certified, and the ingress side can no longer be
handed an uncertified `.inr Tx` at all. -/
theorem CanonicalBlock.decodeTx_inr {cb : CanonicalBlock} {tx : Tx}
    (h : Sum.inr tx ∈ cb.block.txs) :
    decodeTx (.inr tx) = .ok tx ∧
      Tx.WireWellFormed tx ∧ tx.type.isLegacy = true :=
  ⟨rfl, cb.rlpCanonical.2.2.2 _ h⟩

/-- The state transition on a canonical outer block.

Definitionally the raw core applied to the envelope's block, so every result
about `stateTransitionWith` transfers to it by `rfl` and no proof has to be
restated. What it adds is at the type level: a caller of this entry point
cannot supply a block that no strict decode ever produced. -/
def stateTransitionCanonical (rules : ForkRules) (ch : BlockChain)
    (cb : CanonicalBlock) :
    Except String BlockChain :=
  stateTransitionWith rules ch cb.block

theorem stateTransitionCanonical_eq (rules : ForkRules) (ch : BlockChain)
    (cb : CanonicalBlock) :
    stateTransitionCanonical rules ch cb = stateTransitionWith rules ch cb.block :=
  rfl

--------------- THE CHECKED CHAIN SNAPSHOT ---------------

-- P0.2. A `BlockChain` is a freely constructible triple, so nothing stops a
-- caller pairing a real tip with an unrelated world. The tip header's
-- `stateRoot` is the authenticated identity of the prestate every child
-- executes from, and `initBenv` reads `chain.state` directly, so without that
-- link "the state transition from this chain tip" is not a statement about
-- anything. What follows is the checked snapshot the expensive checks are
-- paid for once, and the proof-carrying constructors that carry the witness
-- forward instead of recomputing it (fixed decision 2).

/-- The snapshot's world commits to its own tip header. -/
def BlockChain.TipStateAgrees (chain : BlockChain) : Prop :=
  ∀ tip ∈ chain.blocks.getLast?, chain.state.root = tip.header.stateRoot

instance (chain : BlockChain) : Decidable chain.TipStateAgrees := by
  unfold BlockChain.TipStateAgrees; infer_instance

/-- Everything an executable snapshot must satisfy, in the order the checker
tests it (design report §5): nonempty history, canonical execution state,
valid retained ancestry, and only then the tip/root comparison that costs a
trie root. The conjunction is right-nested in exactly that order, so the
derived decision procedure short-circuits in it -- and because nonemptiness
comes first, tip/root agreement is never vacuously true on an empty chain. -/
def BlockChain.ValidContext (chain : BlockChain) : Prop :=
  chain.blocks ≠ [] ∧ chain.Canonical ∧
    chain.RetainedHistoryValid ∧ chain.TipStateAgrees

instance (chain : BlockChain) : Decidable chain.ValidContext := by
  unfold BlockChain.ValidContext; infer_instance

/-- A chain snapshot that is safe to execute from, with its tip named
explicitly.

The explicit `tip` and `tip_is_last` are what keep every consumer total: no
partial projection, no defaulting lookup, no `Fin` arithmetic, and
nonemptiness comes free. The constructor is private; the only routes in are
`BlockChain.check` (which pays for the checks), `CheckedBlockChain.ofEvidence`
(which demands them as proofs), and the transition/genesis constructors built
on it. -/
structure CheckedBlockChain : Type where
  private mk ::
  /-- The snapshot itself. -/
  val : BlockChain
  /-- Its tip block, named rather than projected. -/
  tip : Block
  /-- The tip really is the last block. -/
  tip_is_last : val.blocks.getLast? = some tip
  /-- Its retained ancestry supports `BLOCKHASH`. -/
  retainedHistory : val.RetainedHistoryValid
  /-- Its world carries no noncanonical entry. -/
  canonicalState : val.state.Canonical
  /-- Its world is the one the tip header commits to. -/
  tipStateRoot : val.state.root = tip.header.stateRoot

/-- The proof-carrying constructor. Nothing is computed here: every field is
evidence, so a caller that already holds the witness -- a successful checked
transition, for instance -- pays no trie root to package its result. -/
def CheckedBlockChain.ofEvidence (chain : BlockChain) (tip : Block)
    (htip : chain.blocks.getLast? = some tip)
    (hhist : chain.RetainedHistoryValid) (hcanon : chain.state.Canonical)
    (hroot : chain.state.root = tip.header.stateRoot) : CheckedBlockChain :=
  ⟨chain, tip, htip, hhist, hcanon, hroot⟩

theorem CheckedBlockChain.ofEvidence_val {chain : BlockChain} {tip : Block}
    {htip hhist hcanon hroot} :
    (CheckedBlockChain.ofEvidence chain tip htip hhist hcanon hroot).val
      = chain := rfl

theorem CheckedBlockChain.ofEvidence_tip {chain : BlockChain} {tip : Block}
    {htip hhist hcanon hroot} :
    (CheckedBlockChain.ofEvidence chain tip htip hhist hcanon hroot).tip
      = tip := rfl

/-- Package a snapshot whose context has already been decided. -/
def CheckedBlockChain.ofValidContext {chain : BlockChain}
    (h : chain.ValidContext) : CheckedBlockChain :=
  CheckedBlockChain.ofEvidence chain (chain.blocks.getLast h.1)
    (List.getLast?_eq_some_getLast h.1) h.2.2.1 h.2.1
    (h.2.2.2 _ (List.getLast?_eq_some_getLast h.1))

/-- The defensive checker, in the frozen order: nonempty history, canonical
state, valid retained ancestry, then the state root computed once and compared
with the tip's. A snapshot that fails any of them yields no checked value at
all, so there is nothing for a caller to ignore. -/
def BlockChain.check (chain : BlockChain) : Option CheckedBlockChain :=
  if h : chain.ValidContext then
    some (CheckedBlockChain.ofValidContext h)
  else
    none

theorem BlockChain.check_isSome_iff {chain : BlockChain} :
    chain.check.isSome = true ↔ chain.ValidContext := by
  unfold BlockChain.check
  split <;> simp_all

theorem BlockChain.check_eq_none {chain : BlockChain} (h : ¬ chain.ValidContext) :
    chain.check = none := by
  unfold BlockChain.check
  split
  · exact absurd (by assumption) h
  · rfl

/-- Every checked snapshot satisfies the context its checker tests for; the
two routes in agree on what they mean. -/
theorem CheckedBlockChain.validContext (cc : CheckedBlockChain) :
    cc.val.ValidContext := by
  refine ⟨?_, cc.canonicalState, cc.retainedHistory, ?_⟩
  · intro h
    have ht := cc.tip_is_last
    rw [h] at ht
    simp at ht
  · intro t ht
    rw [cc.tip_is_last, Option.mem_def, Option.some.injEq] at ht
    rw [← ht]
    exact cc.tipStateRoot

theorem CheckedBlockChain.check_val (cc : CheckedBlockChain) :
    cc.val.check.isSome = true :=
  BlockChain.check_isSome_iff.mpr cc.validContext

/-- The snapshot's key: the hash of the tip header it is proved to end with.
Total, because the tip is a field rather than a lookup -- which is what lets
`ChainStore` derive every key instead of accepting one. -/
def CheckedBlockChain.tipHash (cc : CheckedBlockChain) : B256 :=
  cc.tip.header.hash

/-- Genesis: the only route from a canonical genesis envelope and a parsed
prestate to a checked snapshot. It demands what `Main.lean` never checked --
that the prestate is canonical and that its root is the one the genesis header
commits to -- and it demands that genesis be block zero, which is what makes
the retained-history coverage clause true of the chain it starts. -/
def CheckedBlockChain.ofGenesis (cb : CanonicalBlock) (state : State)
    (chainId : UInt64) (hnum : cb.block.header.number = 0)
    (hcanon : state.Canonical) (hroot : state.root = cb.block.header.stateRoot) :
    CheckedBlockChain :=
  CheckedBlockChain.ofEvidence ⟨[cb.block], state, chainId⟩ cb.block rfl
    ⟨List.IsChain.singleton _,
      by
        intro b hb
        rw [List.mem_singleton.mp hb]
        exact cb.rlpCanonical.1,
      Or.inr (by
        intro b hb
        rw [Option.mem_def, List.head?_cons, Option.some.injEq] at hb
        rw [← hb]
        exact hnum)⟩
    hcanon hroot

theorem CheckedBlockChain.ofGenesis_val {cb : CanonicalBlock} {state : State}
    {chainId : UInt64} {hnum hcanon hroot} :
    (CheckedBlockChain.ofGenesis cb state chainId hnum hcanon hroot).val
      = ⟨[cb.block], state, chainId⟩ := rfl

theorem CheckedBlockChain.ofGenesis_tip {cb : CanonicalBlock} {state : State}
    {chainId : UInt64} {hnum hcanon hroot} :
    (CheckedBlockChain.ofGenesis cb state chainId hnum hcanon hroot).tip
      = cb.block := rfl

/-- The decidable form, for a caller that does not want to case on the three
conditions itself. The proof-taking `ofGenesis` above is what the fixture
runner uses, so that the prestate's root is computed exactly once. -/
def CheckedBlockChain.ofGenesis? (cb : CanonicalBlock) (state : State)
    (chainId : UInt64) : Option CheckedBlockChain :=
  if h : cb.block.header.number = 0 ∧ state.Canonical ∧
      state.root = cb.block.header.stateRoot then
    some (CheckedBlockChain.ofGenesis cb state chainId h.1 h.2.1 h.2.2)
  else
    none

theorem CheckedBlockChain.ofGenesis?_eq_some {cb : CanonicalBlock} {state : State}
    {chainId : UInt64} {cc : CheckedBlockChain}
    (h : CheckedBlockChain.ofGenesis? cb state chainId = some cc) :
    cc.val = ⟨[cb.block], state, chainId⟩ ∧ cc.tip = cb.block := by
  unfold CheckedBlockChain.ofGenesis? at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

--------------- THE CONFIGURED CHAIN ---------------

/-- A configured chain: a validated schedule, a checked snapshot, and the
evidence that they name the same chain.

P0.1 item 4. The three facts a configured entry point would otherwise recheck
on every call -- schedule usability, snapshot integrity, chain-ID agreement --
are established once, here, before any candidate bytes exist. The raw
configured wrappers keep checking on every call, because they carry no
proof. -/
structure ConfiguredChain : Type where
  private mk ::
  config : ChainConfig
  chain : CheckedBlockChain
  validSchedule : config.Valid
  chainId_eq : config.chainId = chain.val.chainId

/-- The checked constructor: the only route to a configured chain. -/
def ConfiguredChain.of? (cfg : ChainConfig) (cc : CheckedBlockChain) :
    Option ConfiguredChain :=
  if h : cfg.Valid ∧ cfg.chainId = cc.val.chainId then
    some ⟨cfg, cc, h.1, h.2⟩
  else
    none

theorem ConfiguredChain.of?_eq_some {cfg : ChainConfig} {cc : CheckedBlockChain}
    {pc : ConfiguredChain} (h : ConfiguredChain.of? cfg cc = some pc) :
    pc.config = cfg ∧ pc.chain = cc := by
  unfold ConfiguredChain.of? at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

/-- A configured chain never disagrees with itself: the chain-ID check the raw
configured entry points perform is redundant on this path, by construction. -/
theorem ConfiguredChain.checkChainId_eq_ok (pc : ConfiguredChain) :
    pc.config.checkChainId pc.chain.val = .ok () := by
  unfold ChainConfig.checkChainId
  rw [if_pos pc.chainId_eq]

/-- Check EIP-7934 against the authoritative original RLP byte length.

This deliberately takes evidence, not a decoded `Block`: re-encoding would
discard the distinction between the bytes a peer supplied and a reconstructed
canonical value. The block-import path performs its existing strict decode and
byte-for-byte canonical round trip before treating this as a consensus
rejection. -/
def checkBlockRlpSize (limits : BlockLimits) (rawSize : Nat) :
    Except String Unit :=
  match limits.maxRlpSize with
  | none => .ok ()
  | some maxRlpSize =>
    if rawSize > maxRlpSize then
      .error
        s!"{blockRlpSizeExceededTag} : original block RLP is {rawSize} bytes > \
           maximum = {maxRlpSize}"
    else
      .ok ()

#guard (checkBlockRlpSize osakaRules.block (8388608 - 1)).toOption.isSome
#guard (checkBlockRlpSize osakaRules.block 8388608).toOption.isSome
#guard hasTag blockRlpSizeExceededTag <|
  checkBlockRlpSize osakaRules.block (8388608 + 1)
#guard (checkBlockRlpSize pragueRules.block (8388608 + 1)).toOption.isSome

--------------- STRICT BLOCK/LEGACY DECODER REGRESSION CHECKS ---------------

private def withdrawalDecoderVector
    (globalIndex validatorIndex recipient amount : Bytes) : BLT :=
  .list [.bytes globalIndex, .bytes validatorIndex, .bytes recipient, .bytes amount]

private def legacyDecoderVector
    (nonce gasPrice gas receiver value v r s : Bytes) : BLT :=
  .list [
    .bytes nonce, .bytes gasPrice, .bytes gas, .bytes receiver, .bytes value,
    .bytes [], .bytes v, .bytes r, .bytes s
  ]

private def nineByteScalar : Bytes := 0x01 :: List.replicate 8 0x00
private def thirtyThreeByteScalar : Bytes := 0x01 :: List.replicate 32 0x00
private def testRecipient : Bytes := List.replicate 20 0x11

-- Both withdrawal index positions reject nine bytes at the field boundary;
-- neither can reach the truncating `Bytes.toUInt64` conversion unchecked.
#guard hasTag rlpFieldOverflow64Tag <|
  BLT.toExStrWithdrawal <|
    withdrawalDecoderVector nineByteScalar [] testRecipient []
#guard hasTag rlpFieldOverflow64Tag <|
  BLT.toExStrWithdrawal <|
    withdrawalDecoderVector [] nineByteScalar testRecipient []
#guard (BLT.toExStrWithdrawal <|
  withdrawalDecoderVector [] [] testRecipient []).toOption.isSome
#guard hasTag rlpFixedWidthTag <|
  BLT.toExStrWithdrawal <|
    withdrawalDecoderVector [] [] (List.replicate 21 0x11) []
-- The amount is a 64-bit Gwei scalar (EIP-4895): the exact eight-byte maximum
-- decodes, and nine bytes are rejected at the field boundary rather than
-- surfacing later as a state-root mismatch.
#guard (BLT.toExStrWithdrawal <|
  withdrawalDecoderVector [] [] testRecipient (List.replicate 8 0xFF)
  ).toOption.map (fun wd => wd.amount.toNat) = some (2 ^ 64 - 1)
#guard hasTag rlpFieldOverflow64Tag <|
  BLT.toExStrWithdrawal <|
    withdrawalDecoderVector [] [] testRecipient nineByteScalar

-- A canonical legacy transaction preserves its signing/re-encoding bytes.
private def canonicalLegacyVector : BLT :=
  legacyDecoderVector [0x01] [0x02] [0x52, 0x08] testRecipient [] [0x1b] [0x01] [0x02]

#guard
  (BLT.toExStrTx canonicalLegacyVector).toOption.map (fun tx => tx.toBLT.toBytes)
    == some canonicalLegacyVector.toBytes

-- Every legacy scalar is bounded before conversion or sender recovery.
#guard hasTag rlpFieldOverflow64Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector nineByteScalar [] [] [] [] [] [] []
#guard hasTag rlpFieldOverflow256Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] thirtyThreeByteScalar [] [] [] [] [] []
#guard hasTag rlpFieldOverflow256Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] [] thirtyThreeByteScalar [] [] [] [] []
#guard hasTag rlpFieldOverflow256Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] [] [] [] thirtyThreeByteScalar [] [] []
#guard hasTag rlpFieldOverflow256Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] [] [] [] [] thirtyThreeByteScalar [] []
#guard hasTag rlpFieldOverflow256Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] [] [] [] [] [] thirtyThreeByteScalar []
#guard hasTag rlpFieldOverflow256Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] [] [] [] [] [] [] thirtyThreeByteScalar
#guard hasTag rlpFixedWidthTag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] [] [] (List.replicate 21 0x11) [] [] [] []

-- The two block-list failures with dedicated meanings are separated before
-- header decoding; arbitrary non-list input remains a structure error.
#guard hasTag rlpWithdrawalsNotReadTag <|
  BLT.toExStrBlock (.list [.bytes [], .list [], .list []])
#guard hasTag rlpStructureTag <| BLT.toExStrBlock (.bytes [])

--------- STRICT TYPED-TRANSACTION DECODER REGRESSION CHECKS ----------

-- A typed transaction is its type byte followed by the RLP encoding of its
-- payload list. Each negative vector below is a one-field mutation of its
-- type's positive vector, so the failing field is unambiguous.

private def typedTxVector (type : UInt8) (fields : List BLT) : Bytes :=
  type :: BLT.toBytes (.list fields)

private def testStorageKey : Bytes := List.replicate 32 0x22
private def testBlobHash : Bytes := 0x01 :: List.replicate 31 0x33
-- Thirty-two bytes with a nonzero leading byte: a canonical full-width
-- scalar, usable for `r`/`s` at the transaction and authorization level.
private def fullWidthScalar : Bytes := 0x01 :: List.replicate 31 0x00

private def accessListOf (adr key : Bytes) : BLT :=
  .list [.list [.bytes adr, .list [.bytes key]]]

private def authOf (chainId adr nonce r s : Bytes) : BLT :=
  .list [.bytes chainId, .bytes adr, .bytes nonce, .bytes [0x01], .bytes r, .bytes s]

private def type1Vector (chainId nonce receiver r : Bytes) (accessList : BLT) : Bytes :=
  typedTxVector 0x01 [
    .bytes chainId, .bytes nonce, .bytes [0x0a], .bytes [0x52, 0x08], .bytes receiver,
    .bytes [], .bytes [], accessList, .bytes [0x01], .bytes r, .bytes [0x02]
  ]

private def type2Vector (maxFee receiver s : Bytes) : Bytes :=
  typedTxVector 0x02 [
    .bytes [0x01], .bytes [0x01], .bytes [0x01], .bytes maxFee, .bytes [0x52, 0x08],
    .bytes receiver, .bytes [], .bytes [], .list [], .bytes [0x01], .bytes [0x01], .bytes s
  ]

private def type3Vector (nonce receiver blobHash : Bytes) : Bytes :=
  typedTxVector 0x03 [
    .bytes [0x01], .bytes nonce, .bytes [0x01], .bytes [0x0a], .bytes [0x52, 0x08],
    .bytes receiver, .bytes [], .bytes [], .list [], .bytes [0x01],
    .list [.bytes blobHash], .bytes [0x01], .bytes [0x01], .bytes [0x02]
  ]

private def type4Vector (receiver : Bytes) (auth : BLT) : Bytes :=
  typedTxVector 0x04 [
    .bytes [0x01], .bytes [0x01], .bytes [0x01], .bytes [0x0a], .bytes [0x52, 0x08],
    .bytes receiver, .bytes [], .bytes [], .list [], .list [auth],
    .bytes [0x01], .bytes [0x01], .bytes [0x02]
  ]

private def goodAuth : BLT :=
  authOf [0x01] testRecipient [0x01] fullWidthScalar fullWidthScalar

-- One positive vector per type: it decodes, and it re-encodes to the exact
-- input bytes, so trie bytes for valid transactions are unchanged.
private def reencodes (type : UInt8) (v : Bytes) : Bool :=
  (Bytes.toExStrTx v).toOption.map (fun tx => type :: tx.toBLT.toBytes) == some v

#guard reencodes 0x01 <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf testRecipient testStorageKey)
#guard reencodes 0x02 <| type2Vector [0x0a] testRecipient [0x02]
#guard reencodes 0x03 <| type3Vector [0x01] testRecipient testBlobHash
#guard reencodes 0x04 <| type4Vector testRecipient goodAuth

-- An authorization signature scalar below 2^248 encodes canonically in fewer
-- than thirty-two bytes. It must re-encode minimally: a fixed 32-byte
-- re-encoding diverges from the canonical bytes for ~0.8% of valid
-- authorizations, corrupting the type-4 signing hash and transactions trie.
private def shortWidthScalar : Bytes := 0x01 :: List.replicate 30 0x00

#guard reencodes 0x04 <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] shortWidthScalar fullWidthScalar
#guard reencodes 0x04 <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] fullWidthScalar shortWidthScalar
#guard reencodes 0x04 <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] [0x01] [0x02]

-- A type-1/type-2 receiver may be empty, meaning contract creation...
#guard (Bytes.toExStrTx (type2Vector [0x0a] [] [0x02])).toOption.isSome
-- ...but an empty type-3 receiver is the semantic contract-creation identity;
-- nonempty 19/21-byte receivers still fail as malformed RLP fields.
#guard hasTag type3ContractCreationTag <|
  Bytes.toExStrTx <| type3Vector [0x01] [] testBlobHash
#guard hasTag rlpFixedWidthTag <|
  Bytes.toExStrTx <| type3Vector [0x01] (List.replicate 19 0x11) testBlobHash
#guard hasTag rlpFixedWidthTag <| Bytes.toExStrTx <|
  type1Vector [0x01] [0x01] (List.replicate 21 0x11) [0x01] (.list [])
#guard hasTag rlpFixedWidthTag <|
  Bytes.toExStrTx <| type4Vector (List.replicate 19 0x11) goodAuth

-- Oversized scalars are overflows at the field boundary, not truncations.
#guard hasTag rlpFieldOverflow64Tag <| Bytes.toExStrTx <|
  type1Vector [0x01] nineByteScalar testRecipient [0x01] (.list [])
#guard hasTag rlpFieldOverflow64Tag <| Bytes.toExStrTx <|
  type1Vector nineByteScalar [0x01] testRecipient [0x01] (.list [])
#guard hasTag rlpFieldOverflow64Tag <|
  Bytes.toExStrTx <| type3Vector nineByteScalar testRecipient testBlobHash
#guard hasTag rlpFieldOverflow256Tag <|
  Bytes.toExStrTx <| type2Vector thirtyThreeByteScalar testRecipient [0x02]
-- The two fields the deleted `reverse.takeD 32` pattern used to truncate.
#guard hasTag rlpFieldOverflow256Tag <| Bytes.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient thirtyThreeByteScalar (.list [])
#guard hasTag rlpFieldOverflow256Tag <|
  Bytes.toExStrTx <| type2Vector [0x0a] testRecipient thirtyThreeByteScalar

-- Access lists: exact address and storage-key widths, and both list shapes.
#guard hasTag rlpFixedWidthTag <| Bytes.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf (List.replicate 21 0x11) testStorageKey)
#guard hasTag rlpFixedWidthTag <| Bytes.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf testRecipient (List.replicate 33 0x22))
#guard hasTag rlpFixedWidthTag <| Bytes.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf testRecipient (List.replicate 31 0x22))
#guard hasTag rlpStructureTag <| Bytes.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01] (.list [.bytes []])
#guard hasTag rlpStructureTag <| Bytes.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01] (.bytes [])

-- Blob versioned hashes: exactly thirty-two bytes, both sides.
#guard hasTag rlpFixedWidthTag <| Bytes.toExStrTx <|
  type3Vector [0x01] testRecipient (0x01 :: List.replicate 32 0x33)
#guard hasTag rlpFixedWidthTag <|
  Bytes.toExStrTx <| type3Vector [0x01] testRecipient (List.replicate 31 0x33)

-- Authorizations: exact address width, a uint256 chainId, bounded nonce and
-- r/s, and the six-field list shape.
#guard hasTag rlpFixedWidthTag <| Bytes.toExStrTx <| type4Vector testRecipient <|
  authOf [0x01] (List.replicate 21 0x11) [0x01] fullWidthScalar fullWidthScalar
#guard (Bytes.toExStrTx <| type4Vector testRecipient <|
  authOf nineByteScalar testRecipient [0x01] fullWidthScalar fullWidthScalar).toOption.isSome
#guard hasTag rlpFieldOverflow64Tag <| Bytes.toExStrTx <| type4Vector testRecipient <|
  authOf [0x01] testRecipient nineByteScalar fullWidthScalar fullWidthScalar
#guard hasTag rlpFieldOverflow256Tag <| Bytes.toExStrTx <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] thirtyThreeByteScalar fullWidthScalar
#guard hasTag rlpFieldOverflow256Tag <| Bytes.toExStrTx <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] fullWidthScalar thirtyThreeByteScalar
#guard hasTag rlpStructureTag <| Bytes.toExStrTx <|
  type4Vector testRecipient (.list [.bytes [0x01], .bytes testRecipient])

-- A wrong list shape for a known type byte is a structure error; an unknown
-- type byte keeps its own failure; empty input is a structure error.
#guard hasTag rlpStructureTag <| Bytes.toExStrTx (0x01 :: BLT.toBytes (.bytes []))
#guard hasTag rlpStructureTag <| Bytes.toExStrTx (0x02 :: BLT.toBytes (.list []))
#guard hasTag rlpStructureTag <| Bytes.toExStrTx []
#guard ¬ hasTag rlpStructureTag (Bytes.toExStrTx [0x05])
#guard (Bytes.toExStrTx [0x05]).toOption.isNone

/-- Block import from a canonical outer-block envelope, under an explicit rule
set. This is the checked import core; every public import path below is a
named raw compatibility wrapper that validates its bytes and then calls it.

Both quantities the previous three-argument shape received as *independent*
parameters are now derived from the envelope: the header hash is
`cb.headerHash`, computed from the decoded header, and the EIP-7934 size is
`cb.rawSize`, the length of the bytes the peer actually supplied. That shape's
first act was to reject a block whose recomputed header hash differed from the
supplied one, a comparison that was tautological at every call site (design
report §3.4); with the envelope there is nothing left to compare, so the check
is *removed* rather than preserved as a no-op.

Check precedence is unchanged. Strict decode and the byte-for-byte round trip
are harness prerequisites, discharged before an envelope can exist at all;
among consensus checks EIP-7934 is first, before `stateTransitionWith` reaches
header validation, exactly as EELS. The two failure channels are unchanged:
`.error` is a harness-level failure, `.inr` is a block this chain rejects. -/
def addBlockToChainCanonical (rules : ForkRules) (chain : BlockChain)
    (cb : CanonicalBlock) :
    Except String (BlockChain ⊕ String) := do
  match checkBlockRlpSize rules.block cb.rawSize with
  | .error err => return .inr err
  | .ok () => pure ()
  let chain ←
    match stateTransitionWith rules chain cb.block with
    | .error err => return (.inr err)
    | .ok chain => .ok chain
  .ok (.inl chain)

/-- Block import under an explicit rule set: the raw compatibility wrapper.

It carries no evidence, so it validates on every call (fixed decision 2) --
strict decode plus the exact round trip -- and hands the checked core an
envelope built from that decode alone. -/
def addBlockToChainWith (rules : ForkRules) (chain : BlockChain)
    (blockRlp : Bytes) : Except String (BlockChain ⊕ String) := do
  match h : rlpToBlock blockRlp with
  | .error err => .error err
  | .ok ⟨_, _⟩ => addBlockToChainCanonical rules chain (CanonicalBlock.ofDecode h)

/-- Block import at an explicitly named fork, for static fixture suites.

An unimplemented fork fails on the `.error` channel: it is a limitation of this
build, not a verdict that the block is invalid, and must never be recorded as
one. -/
def addBlockToChainAt (f : Fork) (chain : BlockChain) (blockRlp : Bytes) :
    Except String (BlockChain ⊕ String) := do
  addBlockToChainWith (← f.rules) chain blockRlp

/-- Block import on a configured chain, deriving the active fork from the
block's own timestamp and the chain's activation schedule.

Checks schedule usability and chain identity before touching the candidate
bytes at all -- P0.1 and P0.5's frozen ordering (design report §3.3): a
contradictory or unusable configuration is a context failure regardless of
what the caller supplied as a block, so it must not depend on decoding
succeeding first. The era a decoded timestamp falls in is checked after
decode, inside `cfg.rulesAt` below, because no timestamp exists before
decode. -/
def addBlockToChainUsing (cfg : ChainConfig) (chain : BlockChain)
    (blockRlp : Bytes) : Except String (BlockChain ⊕ String) := do
  cfg.validate
  Except.mapError ChainContextError.render (cfg.checkChainId chain)
  match h : rlpToBlock blockRlp with
  | .error err => .error err
  | .ok ⟨block, _⟩ =>
    let rules ← cfg.rulesAt block.header.timestamp
    addBlockToChainCanonical rules chain (CanonicalBlock.ofDecode h)

/-- Prague block import.

Retained with its original name, type, and behaviour; downstream proofs state
their results about this name. -/
def addBlockToChain (chain : BlockChain) (blockRlp : Bytes) :
  Except String (BlockChain ⊕ String) :=
  addBlockToChainWith pragueRules chain blockRlp

--------------- IMPORT BRIDGE AND INVERSION LEMMAS ---------------

-- Stated entirely over `rlpToBlock`, `checkBlockRlpSize` and
-- `stateTransitionWith`. A downstream proof client -- Blanc, in practice --
-- can invert an import with these and never unfold `CanonicalBlock`,
-- `addBlockToChainCanonical`, or the raw wrapper's dependent match.

/-- A raw import whose bytes do not strictly decode fails on the outer channel
with exactly the decoder's own diagnostic. -/
theorem addBlockToChainWith_decode_error {rules : ForkRules} {chain : BlockChain}
    {blockRlp : Bytes} {err : String} (h : rlpToBlock blockRlp = .error err) :
    addBlockToChainWith rules chain blockRlp = .error err := by
  unfold addBlockToChainWith
  split
  · rename_i e he
    rw [h] at he
    simp only [Except.error.injEq] at he
    exact he ▸ rfl
  · rename_i b s hb
    rw [h] at hb
    exact absurd hb (by simp)

/-- A raw import whose bytes strictly decode is the checked core on the
envelope that decode produces. This is the bridge: the wrapper adds
validation, and nothing else. -/
theorem addBlockToChainWith_eq_canonical {rules : ForkRules} {chain : BlockChain}
    {blockRlp : Bytes} {block : Block} {hash : B256}
    (h : rlpToBlock blockRlp = .ok ⟨block, hash⟩) :
    addBlockToChainWith rules chain blockRlp
      = addBlockToChainCanonical rules chain (CanonicalBlock.ofDecode h) := by
  unfold addBlockToChainWith
  split
  · rename_i e he
    rw [h] at he
    exact absurd he (by simp)
  · rename_i f s hb
    rw [h] at hb
    simp only [Except.ok.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rfl

/-- Full inversion of a successful raw import: strict decode, then EIP-7934
against the *supplied* byte length, then the transition -- in that order. -/
theorem addBlockToChainWith_eq_ok_inl {rules : ForkRules}
    {chain chain' : BlockChain} {blockRlp : Bytes}
    (h : addBlockToChainWith rules chain blockRlp = .ok (.inl chain')) :
    ∃ block hash,
      rlpToBlock blockRlp = .ok ⟨block, hash⟩ ∧
      checkBlockRlpSize rules.block blockRlp.length = .ok () ∧
      stateTransitionWith rules chain block = .ok chain' := by
  unfold addBlockToChainWith at h
  split at h
  · exact absurd h (by simp)
  · rename_i block hash hd
    refine ⟨block, hash, hd, ?_⟩
    unfold addBlockToChainCanonical at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h
    · rename_i hsize
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h
      · rename_i hstw
        simp only [Bind.bind, Except.bind, Except.ok.injEq, Sum.inl.injEq] at h
        exact ⟨hsize, h ▸ hstw⟩

---------------- FORK ARCHITECTURE CHECKS ----------------

-- The Prague entry points are not merely *compatible* with the rules-explicit
-- core at Prague: they are that core, for every input. `rfl` is the point --
-- an equality on sample data would leave room for a wrapper that diverges
-- somewhere else, and downstream proofs state their results about these names.

example (ch : BlockChain) (block : Block) :
    stateTransition ch block = stateTransitionWith pragueRules ch block := rfl

example (ch : BlockChain) (block : Block) :
    stateTransitionAt .prague ch block = stateTransition ch block := rfl

example (chain : BlockChain) (blockRlp : Bytes) :
    addBlockToChain chain blockRlp
      = addBlockToChainWith pragueRules chain blockRlp := rfl

example (chain : BlockChain) (blockRlp : Bytes) :
    addBlockToChainAt .prague chain blockRlp = addBlockToChain chain blockRlp :=
  rfl

-- A block whose fork this build cannot run is refused, and refused *before*
-- anything is decoded or executed, so an unimplemented fork can never be
-- mistaken for a rule this build actually applied.

private def guardEmptyChain : BlockChain :=
  { blocks := [], state := .empty, chainId := 1 }

private def guardTestHeader : Header := {
  parentHash := 0
  ommersHash := emptyOmmerHash
  coinbase := 0
  stateRoot := 0
  txsRoot := 0
  receiptRoot := 0
  bloom := List.replicate 256 (0 : UInt8)
  difficulty := 0
  number := 1
  gasLimit := 30000000
  gasUsed := 0
  timestamp := 0
  extraData := []
  prevRandao := 0
  nonce := 0
  baseFeePerGas := 7
  withdrawalsRoot := 0
  blobGasUsed := 0
  excessBlobGas := 0
  parentBeaconBlockRoot := 0
  requestsHash := none
}

private def guardBlockAt (timestamp : Nat) : Block :=
  {
    header := { guardTestHeader with timestamp := timestamp }
    txs := []
    ommers := []
    wds := []
  }

-- EIP-7918 uses a strict price comparison. At the 16-wei equality boundary
-- the ordinary target subtraction still applies; one wei above it activates
-- the reserve branch. Prague has no reserve branch at the same inputs.
private def guardBlobParent (baseFee blobGasUsed : Nat) : Header :=
  { guardTestHeader with
    baseFeePerGas := baseFee
    blobGasUsed := blobGasUsed
    excessBlobGas := 0 }

#guard calculateExcessBlobGas osakaBlobSchedule
  (guardBlobParent 16 osakaBlobSchedule.target) = 0
#guard calculateExcessBlobGas osakaBlobSchedule
  (guardBlobParent 17 osakaBlobSchedule.target) = 262144
#guard calculateExcessBlobGas pragueBlobSchedule
  (guardBlobParent 17 pragueBlobSchedule.target) = 0
-- The early below-target return wins even in the reserve-price regime.
#guard calculateExcessBlobGas osakaBlobSchedule
  (guardBlobParent 1000000 (osakaBlobSchedule.target - 1)) = 0
-- Immediately above target, the ordinary branch subtracts the exact target.
#guard calculateExcessBlobGas osakaBlobSchedule
  (guardBlobParent 16 (osakaBlobSchedule.target + gasPerBlob)) = gasPerBlob

-- A BPO fork moves the target, so the same parent implies a different child
-- excess blob gas at each of the three schedules. With `baseFeePerGas = 16`
-- EIP-7918's reserve branch stays inactive, so what is being compared here is
-- the target alone.
#guard calculateExcessBlobGas osakaBlobSchedule
  (guardBlobParent 16 (21 * 131072)) = 1966080
#guard calculateExcessBlobGas bpo1BlobSchedule
  (guardBlobParent 16 (21 * 131072)) = 1441792
#guard calculateExcessBlobGas bpo2BlobSchedule
  (guardBlobParent 16 (21 * 131072)) = 917504

-- Each fork's own target is its below-target boundary: one gas below it the
-- excess resets to zero, and at it the subtraction is exact.
#guard calculateExcessBlobGas bpo1BlobSchedule
  (guardBlobParent 16 (bpo1BlobSchedule.target - 1)) = 0
#guard calculateExcessBlobGas bpo1BlobSchedule
  (guardBlobParent 16 bpo1BlobSchedule.target) = 0
#guard calculateExcessBlobGas bpo1BlobSchedule
  (guardBlobParent 16 (bpo1BlobSchedule.target + gasPerBlob)) = gasPerBlob
#guard calculateExcessBlobGas bpo2BlobSchedule
  (guardBlobParent 16 (bpo2BlobSchedule.target - 1)) = 0
#guard calculateExcessBlobGas bpo2BlobSchedule
  (guardBlobParent 16 (bpo2BlobSchedule.target + gasPerBlob)) = gasPerBlob
-- Osaka is above its own target where BPO1 is still below its larger one.
#guard calculateExcessBlobGas osakaBlobSchedule
  (guardBlobParent 16 (bpo1BlobSchedule.target - 1)) = 524287

-- EIP-7892 keeps every BPO ratio at two thirds, so the reserve branch itself
-- is schedule-independent even though the branch it replaces is not.
#guard [osakaBlobSchedule, bpo1BlobSchedule, bpo2BlobSchedule].map
    (fun blob => calculateExcessBlobGas blob (guardBlobParent 17 (21 * 131072)))
  = [917504, 917504, 917504]

-- Every declared fork now runs; none is refused for want of rules. This chain
-- has no parent block, so each verdict is a header failure instead.
#guard Fork.all.all (fun f => ¬ hasTag unsupportedForkTag
  (stateTransitionAt f guardEmptyChain (guardBlockAt 0)))
#guard Fork.all.all (fun f => ¬ hasTag unsupportedForkTag
  (addBlockToChainAt f guardEmptyChain (guardBlockAt 0).toBLT.toBytes))

-- A one-block chain whose parent is the only input to the child's expected
-- excess blob gas. Everything the header checks before that rule is satisfied
-- by construction, so a mismatch here is reported as the blob rule it is.
private def guardParentHeader : Header :=
  { guardTestHeader with
    number := 0
    baseFeePerGas := 16
    blobGasUsed := 21 * 131072 }

private def guardParentChain : BlockChain :=
  { blocks := [{ header := guardParentHeader, txs := [], ommers := [], wds := [] }]
    state := .empty
    chainId := 1 }

private def guardChildBlock (timestamp excessBlobGas : Nat) : Block :=
  { header := { guardTestHeader with
      number := guardParentHeader.number + 1
      timestamp := timestamp
      excessBlobGas := excessBlobGas
      parentHash := (Header.toBLT guardParentHeader).toBytes.keccak }
    txs := []
    ommers := []
    wds := [] }

-- P0.2, the history half: `RetainedHistoryValid` has teeth, and is decided
-- rather than assumed. A genesis-rooted chain whose blocks are consecutively
-- numbered and hash-linked passes; break either half of the link, or start a
-- short chain above block zero, and it fails.

private def guardHistoryChain (blocks : List Block) : BlockChain :=
  { blocks := blocks, state := .empty, chainId := 1 }

private def guardParentBlock : Block :=
  { header := guardParentHeader, txs := [], ommers := [], wds := [] }

private def guardHistoryChild : Block := guardChildBlock 1 1966080

#guard (guardHistoryChain [guardParentBlock]).RetainedHistoryValid
#guard (guardHistoryChain [guardParentBlock, guardHistoryChild]).RetainedHistoryValid
-- A short chain that does not begin at block zero cannot cover the window.
#guard ¬ (guardHistoryChain [guardHistoryChild]).RetainedHistoryValid
-- A broken parent-hash link, with the numbering left intact.
#guard ¬ (guardHistoryChain [guardParentBlock,
  { guardHistoryChild with
      header := { guardHistoryChild.header with parentHash := 0 } }]).RetainedHistoryValid
-- A broken number, with the hash link left intact.
#guard ¬ (guardHistoryChain [guardParentBlock,
  { guardHistoryChild with
      header := { guardHistoryChild.header with number := 5 } }]).RetainedHistoryValid
-- A header that no strict decode could have produced (a short bloom).
#guard ¬ (guardHistoryChain [{ guardParentBlock with
  header := { guardParentHeader with bloom := [] } }]).RetainedHistoryValid

-- Retention, as measured in design report §3.6: `appendBlock` keeps exactly
-- 255 blocks, and the hash list it feeds reaches 256 entries because the
-- oldest retained block contributes its `parentHash` as well.
#guard (appendBlock (List.replicate 300 guardParentBlock) guardHistoryChild).length = 255
#guard (appendBlock (List.replicate 3 guardParentBlock) guardHistoryChild).length = 4
#guard (getLast256BlockHashes
  (guardHistoryChain (List.replicate 300 guardParentBlock))).length = 256
#guard (getLast256BlockHashes
  (guardHistoryChain [guardParentBlock, guardHistoryChild])).length = 3
#guard (getLast256BlockHashes (guardHistoryChain [])).length = 0

-- P0.2, the snapshot half. A snapshot whose world is not the one its tip
-- header commits to is refused by the checker, before any candidate header or
-- body is looked at; so is an empty one, which must never pass vacuously.
-- Only the checked value carries a tip hash, and it is derived, not supplied.

private def guardCheckedBlock : Block :=
  { header := { guardParentHeader with stateRoot := State.root (Std.TreeMap.empty : State) }
    txs := [], ommers := [], wds := [] }

private def guardCheckedChain : BlockChain :=
  { blocks := [guardCheckedBlock], state := .empty, chainId := 1 }

#guard guardCheckedChain.check.isSome
-- The genesis header of the history guards commits to root 0, which no state
-- has: a real tip with an unrelated world.
#guard (guardHistoryChain [guardParentBlock]).check.isNone
#guard { guardCheckedChain with blocks := [] : BlockChain }.check.isNone
-- Retained history is part of the context, so a snapshot that fails it fails
-- the checker even when its tip and root agree.
#guard { guardCheckedChain with
  blocks := [guardCheckedBlock, guardCheckedBlock] : BlockChain }.check.isNone
#guard guardCheckedChain.check.map CheckedBlockChain.tipHash
  = some guardCheckedBlock.header.hash
-- The configured pair demands a validated schedule and an agreeing identity.
#guard guardCheckedChain.check.map
  (fun cc => (ConfiguredChain.of? mainnetChainConfig cc).isSome) = some true
#guard guardCheckedChain.check.map
  (fun cc => (ConfiguredChain.of? ⟨7, mainnetChainConfig.activations⟩ cc).isSome)
    = some false
#guard guardCheckedChain.check.map
  (fun cc => (ConfiguredChain.of? ⟨1, []⟩ cc).isSome) = some false

-- The explicit API applies the fork it is given, and only that fork accepts
-- its own expected value.
#guard ¬ hasTag excessBlobGasTag
  (stateTransitionAt .osaka guardParentChain (guardChildBlock 1 1966080))
#guard hasTag excessBlobGasTag <|
  stateTransitionAt .bpo1 guardParentChain (guardChildBlock 1 1966080)
#guard ¬ hasTag excessBlobGasTag
  (stateTransitionAt .bpo1 guardParentChain (guardChildBlock 1 1441792))
#guard ¬ hasTag excessBlobGasTag
  (stateTransitionAt .bpo2 guardParentChain (guardChildBlock 1 917504))

-- A configured chain selects rules from the block's own timestamp. Between
-- these blocks nothing differs but the timestamp, and it alone decides which
-- schedule the header is judged against: the block immediately before an
-- activation still runs the old rules, and the activation block itself already
-- runs the new ones.

private def guardChainSchedule : ChainConfig :=
  ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 100⟩, ⟨.bpo1, 200⟩, ⟨.bpo2, 300⟩]

#guard ¬ hasTag excessBlobGasTag
  (stateTransitionUsing guardChainSchedule guardParentChain
    (guardChildBlock 199 1966080))
#guard hasTag excessBlobGasTag <|
  stateTransitionUsing guardChainSchedule guardParentChain
    (guardChildBlock 200 1966080)
#guard ¬ hasTag excessBlobGasTag
  (stateTransitionUsing guardChainSchedule guardParentChain
    (guardChildBlock 200 1441792))
#guard hasTag excessBlobGasTag <|
  stateTransitionUsing guardChainSchedule guardParentChain
    (guardChildBlock 299 917504)
#guard ¬ hasTag excessBlobGasTag
  (stateTransitionUsing guardChainSchedule guardParentChain
    (guardChildBlock 300 917504))

-- Across a sequence of blocks crossing all three activations, one fixed
-- expectation is correct exactly on the segment whose schedule produced it.
-- Prague and Osaka share a target, so the first BPO boundary is the first
-- place the sequence changes.
#guard [0, 99, 100, 199, 200, 299, 300, 400].map (fun timestamp =>
    !hasTag excessBlobGasTag
      (stateTransitionUsing guardChainSchedule guardParentChain
        (guardChildBlock timestamp 1441792)))
  = [false, false, false, false, true, true, false, false]

-- Selecting rules from the schedule is the same thing as naming the fork the
-- schedule selects -- including the expected value quoted in the diagnostic.
#guard errOf (stateTransitionUsing guardChainSchedule guardParentChain
    (guardChildBlock 250 0))
  = errOf (stateTransitionAt .bpo1 guardParentChain (guardChildBlock 250 0))
#guard errOf (stateTransitionUsing guardChainSchedule guardParentChain
    (guardChildBlock 350 0))
  = errOf (stateTransitionAt .bpo2 guardParentChain (guardChildBlock 350 0))
#guard errOf (stateTransitionUsing guardChainSchedule guardParentChain
    (guardChildBlock 250 0))
  ≠ errOf (stateTransitionAt .osaka guardParentChain (guardChildBlock 250 0))

-- Block import agrees with the state transition on which fork a timestamp
-- selects, and a transition label is just another way to write the schedule.
-- A rejected block reports on the `.inr` channel, so its verdict is read from
-- there rather than from the harness-failure channel.
private def importErrOf : Except String (BlockChain ⊕ String) → String
  | .error err => err
  | .ok (.inr err) => err
  | .ok (.inl _) => "unexpected import"

private def guardOsakaToBpo1Config : ChainConfig :=
  (⟨.osaka, .bpo1, 15000⟩ : ForkTransition).chainConfig 1

private def guardChildRlp (timestamp excessBlobGas : Nat) : Bytes :=
  (guardChildBlock timestamp excessBlobGas).toBLT.toBytes

#guard hasErrorType (importErrOf (addBlockToChainUsing guardOsakaToBpo1Config
  guardParentChain (guardChildRlp 15000 0))) excessBlobGasTag
#guard importErrOf (addBlockToChainUsing guardOsakaToBpo1Config guardParentChain
    (guardChildRlp 15000 0))
  = importErrOf (addBlockToChainAt .bpo1 guardParentChain
    (guardChildRlp 15000 0))
#guard importErrOf (addBlockToChainUsing guardOsakaToBpo1Config guardParentChain
    (guardChildRlp 14999 0))
  = importErrOf (addBlockToChainAt .osaka guardParentChain
    (guardChildRlp 14999 0))
#guard importErrOf (addBlockToChainUsing guardOsakaToBpo1Config guardParentChain
    (guardChildRlp 15000 0))
  ≠ importErrOf (addBlockToChainUsing guardOsakaToBpo1Config guardParentChain
    (guardChildRlp 14999 0))

-- A Prague-only configuration is the Prague wrapper, at every timestamp.
#guard errOf (stateTransitionUsing (ChainConfig.pragueOnly 1) guardEmptyChain
    (guardBlockAt 0))
  = errOf (stateTransition guardEmptyChain (guardBlockAt 0))
#guard errOf (stateTransitionUsing (ChainConfig.pragueOnly 1) guardEmptyChain
    (guardBlockAt 999999999))
  = errOf (stateTransition guardEmptyChain (guardBlockAt 999999999))

-- An unusable schedule fails before it selects anything.
#guard hasTag invalidChainConfigTag <|
  stateTransitionUsing (ChainConfig.mk 1 []) guardEmptyChain (guardBlockAt 0)

-- P0.1 acceptance evidence: configured success cannot happen across
-- contradictory chain identities, and a successful configured transition
-- preserves the identity it started with.

theorem stateTransitionUsing_success_chainId_eq
    {cfg : ChainConfig} {ch : BlockChain} {block : Block} {ch' : BlockChain}
    (h : stateTransitionUsing cfg ch block = .ok ch') :
    cfg.chainId = ch.chainId := by
  by_contra hne
  simp [stateTransitionUsing, ChainConfig.checkChainId, hne, Except.mapError,
    Bind.bind, Except.bind] at h

/-- Every successful `stateTransitionWith` copies the input snapshot's chain
identity into its output unconditionally -- the shared fact both configured
entry points' preservation theorems reduce to. -/
theorem stateTransitionWith_preserves_chainId
    {rules : ForkRules} {ch : BlockChain} {block : Block} {ch' : BlockChain}
    (h : stateTransitionWith rules ch block = .ok ch') :
    ch'.chainId = ch.chainId := by
  unfold stateTransitionWith at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨st, bout⟩, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq] at h
  rw [← h]

theorem stateTransitionUsing_preserves_chainId
    {cfg : ChainConfig} {ch : BlockChain} {block : Block} {ch' : BlockChain}
    (h : stateTransitionUsing cfg ch block = .ok ch') :
    ch'.chainId = ch.chainId := by
  unfold stateTransitionUsing at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨rules, _, h⟩ := Except.bind_eq_ok h
  exact stateTransitionWith_preserves_chainId h

/-- A same-ID configured transition is exactly the rule-selected core: the
identity check Step 2 adds is a no-op whenever the caller's IDs already agree,
so no previously-agreeing caller observes any behavioral change. -/
theorem stateTransitionUsing_eq_of_chainId_eq
    {cfg : ChainConfig} {ch : BlockChain} {block : Block}
    (heq : cfg.chainId = ch.chainId) :
    stateTransitionUsing cfg ch block
      = (cfg.rulesAt block.header.timestamp).bind
          (fun rules => stateTransitionWith rules ch block) := by
  unfold stateTransitionUsing ChainConfig.checkChainId
  simp [heq, Except.mapError, Bind.bind, Except.bind]

theorem addBlockToChainUsing_success_chainId_eq
    {cfg : ChainConfig} {chain : BlockChain} {blockRlp : Bytes} {chain' : BlockChain}
    (h : addBlockToChainUsing cfg chain blockRlp = .ok (.inl chain')) :
    cfg.chainId = chain.chainId := by
  unfold addBlockToChainUsing at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  by_contra hne
  simp [ChainConfig.checkChainId, hne, Except.mapError, Bind.bind, Except.bind] at h

theorem addBlockToChainUsing_preserves_chainId
    {cfg : ChainConfig} {chain : BlockChain} {blockRlp : Bytes} {chain' : BlockChain}
    (h : addBlockToChainUsing cfg chain blockRlp = .ok (.inl chain')) :
    chain'.chainId = chain.chainId := by
  unfold addBlockToChainUsing at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  split at h
  · exact absurd h (by simp)
  · obtain ⟨rules, _, h⟩ := Except.bind_eq_ok h
    unfold addBlockToChainCanonical at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h
      · rename_i hstw
        simp only [Bind.bind, Except.bind, Except.ok.injEq, Sum.inl.injEq] at h
        exact stateTransitionWith_preserves_chainId (h ▸ hstw)

-- P0.1 negative guards: config ID 7 against a chain ID 1 snapshot, matching
-- the acceptance evidence's own example. The mismatch is a context failure on
-- the outer channel -- never `.inr`, so never scored as an invalid block --
-- and it fires before decoding even touches the candidate bytes: `[0xFF]` is
-- not valid block RLP at all, yet `addBlockToChainUsing` still reports the
-- mismatch rather than a decode error, because the check runs first.
private def guardMismatchConfig : ChainConfig := ChainConfig.mk 7 [⟨.prague, 0⟩]

#guard hasTag chainIdMismatchTag <|
  stateTransitionUsing guardMismatchConfig guardEmptyChain (guardBlockAt 0)
#guard errOf (stateTransitionUsing guardMismatchConfig guardEmptyChain (guardBlockAt 0))
  = ChainContextError.render (.chainIdMismatch 7 1)
#guard hasTag chainIdMismatchTag <|
  addBlockToChainUsing guardMismatchConfig guardParentChain [0xFF]
#guard importErrOf (addBlockToChainUsing guardMismatchConfig guardParentChain [0xFF])
  = ChainContextError.render (.chainIdMismatch 7 1)
-- The same malformed bytes, past a matching-ID configuration, fail on the
-- ordinary decode path instead -- confirming the mismatch guard above is what
-- changed the verdict, not something incidental to the garbage input.
#guard hasTag rlpStructureTag <|
  addBlockToChainUsing guardOsakaToBpo1Config guardParentChain [0xFF]

--------- TYPED SEMANTIC REASONS: TRANSACTION, BLOCK, IMPORT ---------

-- Declarations, renderers, and golden guards only; no producer is migrated
-- here and no rendered message changes. Step 10 moves the producers.
--
-- Placement is frozen by `scripts/report-integrity-design.md` section 6:
-- every transition and import entry point is in this module, so the two
-- validation vocabularies and the three failure sums belong here. Their tag
-- constants stay where they are declared, in `Jaune/Machine.lean`, and this
-- module reads them; a tag and the constructor that renders under it are
-- pinned to each other by the golden guards below.

/-- Why a transaction is not admissible in the block that contains it.

One constructor per reason in the transaction-rejection vocabulary, which is
already one producer per reason and one official fixture identity per reason.
Nonce direction, intrinsic gas, and the 256-bit gas-price product stay
distinct for exactly the reason the vocabulary keeps them distinct. -/
inductive TxValidationError : Type
  | gasPriceProductOverflow (detail : ErrorDetail)
  | gasAllowanceExceeded (detail : ErrorDetail)
  | initcodeSizeExceeded (detail : ErrorDetail)
  | insufficientAccountFunds (detail : ErrorDetail)
  | insufficientMaxFeePerGas (detail : ErrorDetail)
  | transactionGasLimitExceeded (detail : ErrorDetail)
  | intrinsicGasTooLow (detail : ErrorDetail)
  | invalidChainId (detail : ErrorDetail)
  | nonceIsMax (detail : ErrorDetail)
  | nonceMismatchTooHigh (detail : ErrorDetail)
  | nonceMismatchTooLow (detail : ErrorDetail)
  | priorityGreaterThanMaxFee (detail : ErrorDetail)
  | senderNotEoa (detail : ErrorDetail)
  | type3BlobCountExceeded (detail : ErrorDetail)
  | type3BlobCountLimitExceeded (detail : ErrorDetail)
  | type3ContractCreation (detail : ErrorDetail)
  | type3InvalidBlobVersionedHash (detail : ErrorDetail)
  | type3ZeroBlobs (detail : ErrorDetail)
  | type4ContractCreation (detail : ErrorDetail)
  | emptyAuthorizationList (detail : ErrorDetail)
deriving DecidableEq, Repr

/-- The tag a transaction-rejection reason renders under. -/
def TxValidationError.tag : TxValidationError → String
  | .gasPriceProductOverflow _ => gasPriceProductOverflowTag
  | .gasAllowanceExceeded _ => gasAllowanceExceededTag
  | .initcodeSizeExceeded _ => initcodeSizeExceededTag
  | .insufficientAccountFunds _ => insufficientAccountFundsTag
  | .insufficientMaxFeePerGas _ => insufficientMaxFeePerGasTag
  | .transactionGasLimitExceeded _ => transactionGasLimitExceededTag
  | .intrinsicGasTooLow _ => intrinsicGasTooLowTag
  | .invalidChainId _ => invalidChainIdTag
  | .nonceIsMax _ => nonceIsMaxTag
  | .nonceMismatchTooHigh _ => nonceMismatchTooHighTag
  | .nonceMismatchTooLow _ => nonceMismatchTooLowTag
  | .priorityGreaterThanMaxFee _ => priorityGreaterThanMaxFeeTag
  | .senderNotEoa _ => senderNotEoaTag
  | .type3BlobCountExceeded _ => type3BlobCountExceededTag
  | .type3BlobCountLimitExceeded _ => type3BlobCountLimitExceededTag
  | .type3ContractCreation _ => type3ContractCreationTag
  | .type3InvalidBlobVersionedHash _ => type3InvalidBlobVersionedHashTag
  | .type3ZeroBlobs _ => type3ZeroBlobsTag
  | .type4ContractCreation _ => type4ContractCreationTag
  | .emptyAuthorizationList _ => emptyAuthorizationListTag

/-- The diagnostic payload of a transaction-rejection reason. -/
def TxValidationError.detail : TxValidationError → ErrorDetail
  | .gasPriceProductOverflow d | .gasAllowanceExceeded d
  | .initcodeSizeExceeded d | .insufficientAccountFunds d
  | .insufficientMaxFeePerGas d | .transactionGasLimitExceeded d
  | .intrinsicGasTooLow d | .invalidChainId d | .nonceIsMax d
  | .nonceMismatchTooHigh d | .nonceMismatchTooLow d
  | .priorityGreaterThanMaxFee d | .senderNotEoa d
  | .type3BlobCountExceeded d | .type3BlobCountLimitExceeded d
  | .type3ContractCreation d | .type3InvalidBlobVersionedHash d
  | .type3ZeroBlobs d | .type4ContractCreation d
  | .emptyAuthorizationList d => d

/-- The one renderer for `TxValidationError`. -/
def TxValidationError.render (e : TxValidationError) : String :=
  renderTagged e.tag e.detail

/-- Every transaction-rejection reason, for the completeness guards. -/
def TxValidationError.all : List TxValidationError :=
  [ .gasPriceProductOverflow .none, .gasAllowanceExceeded .none,
    .initcodeSizeExceeded .none, .insufficientAccountFunds .none,
    .insufficientMaxFeePerGas .none, .transactionGasLimitExceeded .none,
    .intrinsicGasTooLow .none, .invalidChainId .none, .nonceIsMax .none,
    .nonceMismatchTooHigh .none, .nonceMismatchTooLow .none,
    .priorityGreaterThanMaxFee .none, .senderNotEoa .none,
    .type3BlobCountExceeded .none, .type3BlobCountLimitExceeded .none,
    .type3ContractCreation .none, .type3InvalidBlobVersionedHash .none,
    .type3ZeroBlobs .none, .type4ContractCreation .none,
    .emptyAuthorizationList .none ]

/-- Why a header or a post-transition check rejects a block.

One constructor per reason in the block-rejection vocabulary. A bare
"some consensus rule failed" is exactly what let a block be rejected for the
wrong reason and still be scored as a pass, which is why each reason is its
own constructor here as it is its own tag there. -/
inductive BlockValidationError : Type
  | gasLimitTooBig (detail : ErrorDetail)
  | gasLimitAdjustment (detail : ErrorDetail)
  | gasUsedOverflow (detail : ErrorDetail)
  | gasUsedMismatch (detail : ErrorDetail)
  | timestampOlderThanParent (detail : ErrorDetail)
  | blockNumber (detail : ErrorDetail)
  | baseFeePerGas (detail : ErrorDetail)
  | difficultyOverParis (detail : ErrorDetail)
  | ommersOverParis (detail : ErrorDetail)
  | extraDataTooBig (detail : ErrorDetail)
  | unknownParent (detail : ErrorDetail)
  | unknownParentZero (detail : ErrorDetail)
  | stateRoot (detail : ErrorDetail)
  | transactionsRoot (detail : ErrorDetail)
  | receiptsRoot (detail : ErrorDetail)
  | logBloom (detail : ErrorDetail)
  | withdrawalsRoot (detail : ErrorDetail)
  | headerNonce (detail : ErrorDetail)
  | excessBlobGas (detail : ErrorDetail)
  | blobGasUsed (detail : ErrorDetail)
  | requestsHash (detail : ErrorDetail)
  | depositEventLayout (detail : ErrorDetail)
  | systemContractCallFailed (detail : ErrorDetail)
  | blockRlpSizeExceeded (detail : ErrorDetail)
deriving DecidableEq, Repr

/-- The tag a block-rejection reason renders under. -/
def BlockValidationError.tag : BlockValidationError → String
  | .gasLimitTooBig _ => gasLimitTooBigTag
  | .gasLimitAdjustment _ => gasLimitAdjustmentTag
  | .gasUsedOverflow _ => gasUsedOverflowTag
  | .gasUsedMismatch _ => gasUsedMismatchTag
  | .timestampOlderThanParent _ => timestampOlderThanParentTag
  | .blockNumber _ => blockNumberTag
  | .baseFeePerGas _ => baseFeePerGasTag
  | .difficultyOverParis _ => difficultyOverParisTag
  | .ommersOverParis _ => ommersOverParisTag
  | .extraDataTooBig _ => extraDataTooBigTag
  | .unknownParent _ => unknownParentTag
  | .unknownParentZero _ => unknownParentZeroTag
  | .stateRoot _ => stateRootTag
  | .transactionsRoot _ => transactionsRootTag
  | .receiptsRoot _ => receiptsRootTag
  | .logBloom _ => logBloomTag
  | .withdrawalsRoot _ => withdrawalsRootTag
  | .headerNonce _ => headerNonceTag
  | .excessBlobGas _ => excessBlobGasTag
  | .blobGasUsed _ => blobGasUsedTag
  | .requestsHash _ => requestsHashTag
  | .depositEventLayout _ => depositEventLayoutTag
  | .systemContractCallFailed _ => systemContractCallFailedTag
  | .blockRlpSizeExceeded _ => blockRlpSizeExceededTag

/-- The diagnostic payload of a block-rejection reason. -/
def BlockValidationError.detail : BlockValidationError → ErrorDetail
  | .gasLimitTooBig d | .gasLimitAdjustment d | .gasUsedOverflow d
  | .gasUsedMismatch d | .timestampOlderThanParent d | .blockNumber d
  | .baseFeePerGas d | .difficultyOverParis d | .ommersOverParis d
  | .extraDataTooBig d | .unknownParent d | .unknownParentZero d
  | .stateRoot d | .transactionsRoot d | .receiptsRoot d | .logBloom d
  | .withdrawalsRoot d | .headerNonce d | .excessBlobGas d
  | .blobGasUsed d | .requestsHash d | .depositEventLayout d
  | .systemContractCallFailed d | .blockRlpSizeExceeded d => d

/-- The one renderer for `BlockValidationError`. -/
def BlockValidationError.render (e : BlockValidationError) : String :=
  renderTagged e.tag e.detail

/-- Every block-rejection reason, for the completeness guards. -/
def BlockValidationError.all : List BlockValidationError :=
  [ .gasLimitTooBig .none, .gasLimitAdjustment .none, .gasUsedOverflow .none,
    .gasUsedMismatch .none, .timestampOlderThanParent .none,
    .blockNumber .none, .baseFeePerGas .none, .difficultyOverParis .none,
    .ommersOverParis .none, .extraDataTooBig .none, .unknownParent .none,
    .unknownParentZero .none, .stateRoot .none, .transactionsRoot .none,
    .receiptsRoot .none, .logBloom .none, .withdrawalsRoot .none,
    .headerNonce .none, .excessBlobGas .none, .blobGasUsed .none,
    .requestsHash .none, .depositEventLayout .none,
    .systemContractCallFailed .none, .blockRlpSizeExceeded .none ]

/-- Why an import could not be attempted, or could not be trusted.

The outer channel. None of these is a verdict about the candidate block, and
none may ever be scored as an expected consensus rejection: a contradictory
caller context, an unimplemented era, a harness fault, or a broken internal
invariant all mean the question was not answered, not that the answer was
"invalid". -/
inductive ImportFailure : Type
  /-- The configuration, or its pairing with the snapshot, is unusable. -/
  | context (reason : ChainContextError)
  /-- The input is outside the domain this build implements. -/
  | support (reason : SupportError)
  /-- The surrounding harness could not supply what the import needs. -/
  | harness (detail : ErrorDetail)
  /-- A stated invariant of this build did not hold. -/
  | internal (reason : InternalError)
deriving DecidableEq, Repr

/-- The one renderer for `ImportFailure`. -/
def ImportFailure.render : ImportFailure → String
  | .context reason => reason.render
  | .support reason => reason.render
  | .harness detail => renderTagged internalErrorTag detail
  | .internal reason => reason.render

/-- Why a candidate block is rejected.

The inner channel: every arm is a consensus verdict about the candidate, and
every arm carries a reason with an official fixture identity. The `decode`
arm exists because the audited ordering treats some strict-decode failures as
block rejection rather than as ingress failure; Step 10 assigns each decode
reason to this arm or to `RawImportFailure.strictDecode` deliberately, reason
by reason, and never by inheriting today's nesting. -/
inductive BlockRejection : Type
  | transaction (reason : TxValidationError)
  | block (reason : BlockValidationError)
  | decode (reason : DecodeError)
deriving DecidableEq, Repr

/-- The one renderer for `BlockRejection`. -/
def BlockRejection.render : BlockRejection → String
  | .transaction reason => reason.render
  | .block reason => reason.render
  | .decode reason => reason.render

/-- The result of an import that was actually attempted: an extended chain, or
a rejected candidate.

Parameterised in the chain representation so that the compatibility wrapper
and the checked core share one shape. Step 6 introduces the checked snapshot
and instantiates this at it; until then it is instantiated at `BlockChain`. -/
abbrev ImportOutcome (chain : Type) : Type := chain ⊕ BlockRejection

/-- Why an import from raw bytes could not produce an outcome at all.

Ingress failure is explicit here rather than nested inside the operational
channel by accident. -/
inductive RawImportFailure : Type
  | strictDecode (reason : DecodeError)
  | operational (reason : ImportFailure)
deriving DecidableEq, Repr

/-- The one renderer for `RawImportFailure`. -/
def RawImportFailure.render : RawImportFailure → String
  | .strictDecode reason => reason.render
  | .operational reason => reason.render

-- Golden guards. Each vocabulary is pinned constructor-by-constructor to the
-- tag it renders under, so a migrated producer cannot silently change an
-- externally observed message or route a reason to the wrong identity.
#guard TxValidationError.all.length = 20
#guard TxValidationError.all.eraseDups.length = 20
#guard TxValidationError.all.map TxValidationError.tag = transactionExceptionTags
#guard (TxValidationError.all.map TxValidationError.tag).eraseDups.length = 20
#guard TxValidationError.render (.nonceMismatchTooHigh .none)
  = "NonceMismatchTooHighError"
#guard TxValidationError.render (.intrinsicGasTooLow (.text "needs 21000, has 20999"))
  = "IntrinsicGasTooLowError : needs 21000, has 20999"

#guard BlockValidationError.all.length = 24
#guard BlockValidationError.all.eraseDups.length = 24
#guard BlockValidationError.all.map BlockValidationError.tag = blockExceptionTags
#guard (BlockValidationError.all.map BlockValidationError.tag).eraseDups.length = 24
#guard BlockValidationError.render (.stateRoot .none) = "StateRootError"
#guard BlockValidationError.render (.blockRlpSizeExceeded (.text "1 byte over the limit"))
  = "BlockRlpSizeExceededError : 1 byte over the limit"

#guard ImportFailure.render (.context .emptySchedule)
  = "InvalidChainConfigError : the activation schedule is empty"
#guard ImportFailure.render (.context (.chainIdMismatch 7 1))
  = "ChainIdMismatchError : the configuration names chain 7, but the snapshot \
     is chain 1"
#guard ImportFailure.render (.support (.unsupportedEra 100 200))
  = "UnsupportedEraError : timestamp 100 precedes the earliest era this \
     configuration supports, which begins at 200"
#guard ImportFailure.render (.harness (.text "lastblockhash names no imported snapshot"))
  = "ERROR : lastblockhash names no imported snapshot"
#guard ImportFailure.render (.internal (.invariant (.text "receipt not found")))
  = "ERROR : receipt not found"

#guard BlockRejection.render (.transaction (.senderNotEoa .none)) = "SenderNotEoaError"
#guard BlockRejection.render (.block (.logBloom .none)) = "LogBloomError"
#guard BlockRejection.render (.decode (.roundTrip .none)) = "RlpRoundTripError"

#guard RawImportFailure.render (.strictDecode (.rlpStructure .none))
  = "RlpStructureError"
#guard RawImportFailure.render (.operational (.support (.unsupportedFork .osaka)))
  = "UnsupportedForkError : fork Osaka is a declared protocol fork whose \
     execution rules are not implemented in this build"

-- No block-rejection or transaction-rejection tag is readable as the broad
-- category it replaces, and the two vocabularies do not overlap. These are the
-- constructor-level restatements of the distinctness facts the tag lists
-- already carry, and they are what makes exhaustive matching a faithful
-- replacement for prefix matching.
#guard (TxValidationError.all.map TxValidationError.tag).all fun t =>
  ¬ (BlockValidationError.all.map BlockValidationError.tag).contains t

--------------- CANONICALITY THROUGH EXECUTION (P0.4, STEP 4) ---------------

-- Checkpoint 3: canonicality through message-call processing, transaction
-- processing, system transactions, withdrawals, the block body, and the raw
-- successful block transition. Every lemma states the success channel; the
-- error channel at this layer carries no state.

theorem processMessageCall.create_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : processMessageCall.create msg = .ok p) :
    State.Canonical p.1 := by
  unfold processMessageCall.create at hp
  dsimp only at hp
  split at hp
  · cases hp
    exact h.1.1
  · obtain ⟨evm, hevm, hp⟩ := Except.bind_eq_ok hp
    have hcan := processCreateMessage_ok_canonical h (Except.bimap_id_eq_ok hevm)
    split at hp <;>
      (obtain ⟨rc, _, hp⟩ := Except.bind_eq_ok hp
       cases hp
       exact hcan.1)

theorem processMessageCall.call_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : processMessageCall.call msg = .ok p) :
    State.Canonical p.1 := by
  unfold processMessageCall.call at hp
  dsimp only at hp
  split at hp
  · -- no authorizations: the join point receives the message unchanged
    obtain ⟨x0, hx0, hp⟩ := Except.bind_eq_ok hp
    cases hx0
    dsimp only at hp
    split at hp <;>
      (obtain ⟨evm, hevm, hp⟩ := Except.bind_eq_ok hp
       have hcan := processMessage_ok_canonical (by exact h)
         (Except.bimap_id_eq_ok hevm)
       split at hp <;>
         (obtain ⟨rc, _, hp⟩ := Except.bind_eq_ok hp
          cases hp
          exact hcan.1))
  · -- delegation processed first
    obtain ⟨w, hw, hp⟩ := Except.bind_eq_ok hp
    have hwc := setDelegation_canonical h hw
    obtain ⟨wm, wv⟩ := w
    obtain ⟨x0, hx0, hp⟩ := Except.bind_eq_ok hp
    cases hx0
    dsimp only at hp
    split at hp <;>
      (obtain ⟨evm, hevm, hp⟩ := Except.bind_eq_ok hp
       have hcan := processMessage_ok_canonical (by exact hwc)
         (Except.bimap_id_eq_ok hevm)
       split at hp <;>
         (obtain ⟨rc, _, hp⟩ := Except.bind_eq_ok hp
          cases hp
          exact hcan.1))

/-- A successful message call leaves a canonical state, for both the create
and the call route. -/
theorem processMessageCall_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : processMessageCall msg = .ok p) : State.Canonical p.1 := by
  unfold processMessageCall at hp
  split at hp
  · exact processMessageCall.create_canonical h hp
  · exact processMessageCall.call_canonical h hp

theorem prepareMessage_canonical {benv : Benv} {tenv : Tenv} {tx : Tx}
    (hb : benv.Canonical) (ht : tenv.Canonical) {msg : Msg}
    (hm : prepareMessage benv tenv tx = .ok msg) : msg.Canonical := by
  unfold prepareMessage at hm
  cases hm
  exact ⟨hb, ht⟩

/-- A successful transaction leaves a canonical state: the fee movements go
through `incrNonce`/`subBal`/`addBal`, the call itself through
`processMessageCall`, and settlement folds `destroyAccount`. -/
theorem processTransaction_canonical {benv : Benv} (h : benv.Canonical)
    {bout : BlockOutput} {tx : Tx} {index : Nat} {p}
    (hp : processTransaction benv bout tx index = .ok p) :
    State.Canonical p.1 := by
  unfold processTransaction at hp
  obtain ⟨b1, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨ig, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨ck, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨st1, hst1, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨msg, hmsg, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨rc, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨b2, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨b3, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  have hst1c : st1.Canonical :=
    State.Canonical.subBal
      (by exact State.Canonical.incrNonce (by exact h.1) _)
      (Option.toExcept_eq_ok hst1)
  have hmsgc : msg.Canonical :=
    prepareMessage_canonical (by exact ⟨hst1c, h.1⟩)
      (by exact Tra.canonical_empty) hmsg
  have hqc := processMessageCall_canonical hmsgc hq
  exact State.Canonical.foldl_destroyAccount
    (State.Canonical.addBal (State.Canonical.addBal hqc _ _) _ _)

theorem processWithdrawalsState_canonical {st : State} (h : st.Canonical)
    (wds : List Withdrawal) : (processWithdrawalsState st wds).Canonical := by
  unfold processWithdrawalsState
  induction wds generalizing st with
  | nil => exact h
  | cons w l ih => exact ih (State.Canonical.addBal h _ _)

/-- The single boundary all four system transactions share. -/
theorem processSystemTransaction_canonical {benv : Benv} (h : benv.Canonical)
    {target : Adr} {code : ByteArray} {data : Bytes} {p}
    (hp : processSystemTransaction benv target code data = .ok p) :
    State.Canonical p.1 := by
  unfold processSystemTransaction at hp
  exact processMessageCall_canonical
    (by exact ⟨⟨h.1, h.1⟩, Tra.canonical_empty⟩) hp

theorem processUncheckedSystemTransaction_canonical {benv : Benv}
    (h : benv.Canonical) {target : Adr} {data : Bytes} {p}
    (hp : processUncheckedSystemTransaction benv target data = .ok p) :
    State.Canonical p.1 :=
  processSystemTransaction_canonical h hp

theorem processCheckedSystemTransaction_canonical {benv : Benv}
    (h : benv.Canonical) {target : Adr} {data : Bytes} {p}
    (hp : processCheckedSystemTransaction benv target data = .ok p) :
    State.Canonical p.1 := by
  unfold processCheckedSystemTransaction at hp
  dsimp only at hp
  split at hp
  · obtain ⟨u, hu, hp⟩ := Except.bind_eq_ok hp
    nomatch hu
  · obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    obtain ⟨qs, qo⟩ := q
    dsimp only at hp
    split at hp
    · nomatch hp
    · cases hp
      exact processSystemTransaction_canonical h hq

theorem processGeneralPurposeRequests_canonical {benv : Benv}
    (h : benv.Canonical) {bout : BlockOutput} {p}
    (hp : processGeneralPurposeRequests benv bout = .ok p) :
    State.Canonical p.1 := by
  unfold processGeneralPurposeRequests at hp
  obtain ⟨dr, _, hp⟩ := Except.bind_eq_ok hp
  dsimp only at hp
  split at hp <;>
    (obtain ⟨q1, hq1, hp⟩ := Except.bind_eq_ok hp
     obtain ⟨q1s, q1o⟩ := q1
     dsimp only at hp
     split at hp <;>
       (obtain ⟨q2, hq2, hp⟩ := Except.bind_eq_ok hp
        obtain ⟨q2s, q2o⟩ := q2
        dsimp only at hp
        split at hp <;>
          (cases hp
           exact processCheckedSystemTransaction_canonical
             (by exact ⟨processCheckedSystemTransaction_canonical h hq1, h.2⟩)
             hq2)))

theorem applyTransactions_canonical :
    ∀ (txis : List (Nat × Tx)) {benv : Benv}, benv.Canonical →
      ∀ {bout : BlockOutput} {p},
        applyTransactions txis benv bout = .ok p → p.1.Canonical
  | [], _, h, _, _, hp => by cases hp; exact h
  | txi :: txis, benv, h, bout, p, hp => by
    unfold applyTransactions at hp
    obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    exact applyTransactions_canonical txis
      (by exact ⟨processTransaction_canonical h hq, h.2⟩) hp

/-- A successful block body leaves a canonical state: system transactions,
ordinary transactions, withdrawals, and general-purpose requests all
preserve the invariant. -/
theorem applyBody_canonical {benv : Benv} (h : benv.Canonical)
    {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal} {p}
    (hp : applyBody benv txs wds = .ok p) : State.Canonical p.1 := by
  unfold applyBody at hp
  obtain ⟨q1, hq1, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨lh, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q2, hq2, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨txsD, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q3, hq3, hp⟩ := Except.bind_eq_ok hp
  have hb1 : q1.1.Canonical :=
    processUncheckedSystemTransaction_canonical h hq1
  have hb2 : q2.1.Canonical :=
    processUncheckedSystemTransaction_canonical (by exact ⟨hb1, h.2⟩) hq2
  have hb3 : q3.1.Canonical :=
    applyTransactions_canonical _ (by exact ⟨hb2, h.2⟩) hq3
  exact processGeneralPurposeRequests_canonical
    (by exact ⟨processWithdrawalsState_canonical hb3.1 _, hb3.2⟩) hp

/-- **Raw successful block transition preserves canonicality.** The output
chain's execution state is the body's final state, and its original state is
the input chain's. -/
theorem stateTransitionWith_canonical {rules : ForkRules} {ch : BlockChain}
    (h : ch.Canonical) {block : Block} {ch'}
    (hp : stateTransitionWith rules ch block = .ok ch') : ch'.Canonical := by
  unfold stateTransitionWith at hp
  obtain ⟨u1, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨u2, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨u3, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact applyBody_canonical (by exact ⟨h, h⟩) hq

theorem stateTransitionAt_canonical {f : Fork} {ch : BlockChain}
    (h : ch.Canonical) {block : Block} {ch'}
    (hp : stateTransitionAt f ch block = .ok ch') : ch'.Canonical := by
  unfold stateTransitionAt at hp
  obtain ⟨r, _, hp⟩ := Except.bind_eq_ok hp
  exact stateTransitionWith_canonical h hp

theorem stateTransition_canonical {ch : BlockChain} (h : ch.Canonical)
    {block : Block} {ch'} (hp : stateTransition ch block = .ok ch') :
    ch'.Canonical :=
  stateTransitionWith_canonical h hp

/-- Configured successful transition preserves canonicality. -/
theorem stateTransitionUsing_canonical {cfg : ChainConfig} {ch : BlockChain}
    (h : ch.Canonical) {block : Block} {ch'}
    (hp : stateTransitionUsing cfg ch block = .ok ch') : ch'.Canonical := by
  unfold stateTransitionUsing at hp
  obtain ⟨u1, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨r, _, hp⟩ := Except.bind_eq_ok hp
  exact stateTransitionWith_canonical h hp

--------------- THE CHECKED TRANSITION (P0.2, STEP 6) ---------------

-- What the raw transition already establishes, read back out of it. Nothing
-- here re-executes or recomputes anything: `validateHeader` has already
-- compared the child's parent hash and number against the parent header, and
-- `stateTransitionChecks` has already compared the computed post-state root
-- against the child header's. Those two comparisons are exactly the halves of
-- a checked snapshot's witness the transition does not otherwise carry, so
-- the checked core constructs its output from them rather than paying for a
-- second trie root.

-- `validateHeader` is a `do` block of guards, so its elaboration is a nest of
-- join points under `have`-bound continuations. Zeta-expanding all of them at
-- once duplicates each continuation twice per level, and the resulting term is
-- large enough to exhaust `simp`'s step budget -- which is a limit that may
-- not be raised. Peeling one binder at a time keeps the shared term small.
private theorem letFun_apply {α : Sort u} {β : α → Sort v} (a : α)
    (f : (x : α) → β x) : letFun a f = f a := rfl

/-- Header validation establishes both halves of `Block.Links` against the
chain's tip. -/
theorem validateHeader_links {rules : ForkRules} {chain : BlockChain}
    {header : Header} {tip : Block} (htip : chain.blocks.getLast? = some tip)
    (h : validateHeader rules chain header = .ok ()) :
    header.parentHash = tip.header.hash ∧
      header.number = tip.header.number + 1 := by
  unfold validateHeader at h
  obtain ⟨parent, hpar, h⟩ := Except.bind_eq_ok h
  rw [htip] at hpar
  simp only [Option.toExcept, Except.ok.injEq] at hpar
  subst hpar
  dsimp only at h
  by_cases hph : header.parentHash = tip.header.hash
  · rw [if_neg (by simpa [Header.hash] using hph)] at h
    refine ⟨hph, ?_⟩
    obtain ⟨bf, hbf, h⟩ := Except.bind_eq_ok h
    by_cases h1 : header.excessBlobGas ≠ calculateExcessBlobGas rules.blob tip.header
    · rw [if_pos h1] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    rw [if_neg h1] at h
    by_cases h2 : header.gasUsed > header.gasLimit
    · rw [if_pos h2] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    rw [if_neg h2] at h
    by_cases h3 : bf ≠ header.baseFeePerGas
    · rw [if_pos h3] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    rw [if_neg h3] at h
    by_cases h4 : header.timestamp ≤ tip.header.timestamp
    · rw [if_pos h4] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    rw [if_neg h4] at h
    by_cases h5 : header.number ≠ tip.header.number + 1
    · rw [if_pos h5] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    · simpa using h5
  · exfalso
    rw [if_pos (by simpa [Header.hash] using hph)] at h
    by_cases hz : header.parentHash = 0
    · rw [if_pos hz] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    · rw [if_neg hz] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)

/-- The block checks establish the computed post-state root against the child
header's own -- which is exactly the tip/root agreement the resulting snapshot
needs, already paid for. -/
theorem stateTransitionChecks_stateRoot {bout : BlockOutput} {header : Header}
    {transactionsRoot blockStateRoot receiptRoot : B256} {blockLogsBloom : Bytes}
    {withdrawalsRoot requestsHash : B256}
    (h : stateTransitionChecks bout header transactionsRoot blockStateRoot
      receiptRoot blockLogsBloom withdrawalsRoot requestsHash = .ok ()) :
    blockStateRoot = header.stateRoot := by
  unfold stateTransitionChecks at h
  dsimp only at h
  by_cases h1 : bout.blockGasUsed ≠ header.gasUsed
  · rw [if_pos h1] at h
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
    exact absurd hb (by simp)
  rw [if_neg h1] at h
  by_cases h2 : transactionsRoot ≠ header.txsRoot
  · rw [if_pos h2] at h
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
    exact absurd hb (by simp)
  rw [if_neg h2] at h
  by_cases h3 : blockStateRoot ≠ header.stateRoot
  · rw [if_pos h3] at h
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
    exact absurd hb (by simp)
  · simpa using h3

/-- Inversion of a successful raw transition: header validation passed, the
result's blocks are the parent's with this block appended, and its state is
the one the child header commits to. -/
theorem stateTransitionWith_eq_ok {rules : ForkRules} {ch ch' : BlockChain}
    {block : Block} (h : stateTransitionWith rules ch block = .ok ch') :
    validateHeader rules ch block.header = .ok () ∧
      ch'.blocks = appendBlock ch.blocks block ∧
      ch'.state.root = block.header.stateRoot := by
  unfold stateTransitionWith at h
  obtain ⟨u1, hvh, h⟩ := Except.bind_eq_ok h
  obtain ⟨u2, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨q, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨u3, hchk, h⟩ := Except.bind_eq_ok h
  cases u1
  cases u3
  cases h
  exact ⟨hvh, rfl, stateTransitionChecks_stateRoot hchk⟩

/-- The whole output witness of a successful transition from a checked
snapshot, assembled from what the transition already established: `Step 4`'s
canonicality preservation, header validation's parent link, the checked
envelope's wire well-formedness, and the block checks' own state-root
comparison. No root is recomputed. -/
theorem BlockChain.validContext_of_transition {rules : ForkRules}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionWith rules cc.val cb.block = .ok ch') :
    ch'.blocks.getLast? = some cb.block ∧ ch'.RetainedHistoryValid ∧
      ch'.state.Canonical ∧ ch'.state.root = cb.block.header.stateRoot := by
  obtain ⟨hvh, hblocks, hroot⟩ := stateTransitionWith_eq_ok h
  obtain ⟨hph, hnum⟩ := validateHeader_links cc.tip_is_last hvh
  refine ⟨?_, ?_, stateTransitionWith_canonical cc.canonicalState h, hroot⟩
  · rw [hblocks]; exact appendBlock_getLast? _ _
  · exact BlockChain.retainedHistoryValid_appendBlock cc.retainedHistory
      cc.tip_is_last ⟨hnum, hph⟩ cb.rlpCanonical.1 hblocks

--------------- CHECKED TRANSITION AND IMPORT CORES ---------------

/-- The checked transition core: it accepts only a checked snapshot and a
canonical envelope, and it is definitionally the raw core on their values, so
every existing result about `stateTransitionWith` transfers by `rfl`. Its
output witness is `CheckedBlockChain.ofTransition` below. -/
def stateTransitionChecked (rules : ForkRules) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    Except String BlockChain :=
  stateTransitionWith rules cc.val cb.block

theorem stateTransitionChecked_eq (rules : ForkRules) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    stateTransitionChecked rules cc cb
      = stateTransitionWith rules cc.val cb.block := rfl

/-- The checked output of a successful checked transition.

This is the P0.2 fast path: the returned snapshot's four facts are proofs, not
computations, so a repeated client pays exactly one state-root computation --
the one `stateTransitionChecks` already performed on the child -- and never a
second one on the parent. -/
def CheckedBlockChain.ofTransition {rules : ForkRules} {cc : CheckedBlockChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionChecked rules cc cb = .ok ch') : CheckedBlockChain :=
  CheckedBlockChain.ofEvidence ch' cb.block
    (BlockChain.validContext_of_transition h).1
    (BlockChain.validContext_of_transition h).2.1
    (BlockChain.validContext_of_transition h).2.2.1
    (BlockChain.validContext_of_transition h).2.2.2

theorem CheckedBlockChain.ofTransition_val {rules : ForkRules}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionChecked rules cc cb = .ok ch') :
    (CheckedBlockChain.ofTransition h).val = ch' := rfl

theorem CheckedBlockChain.ofTransition_tip {rules : ForkRules}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionChecked rules cc cb = .ok ch') :
    (CheckedBlockChain.ofTransition h).tip = cb.block := rfl

/-- Inversion of the checked import core, mirroring the raw wrapper's. -/
theorem addBlockToChainCanonical_eq_ok_inl {rules : ForkRules}
    {chain chain' : BlockChain} {cb : CanonicalBlock}
    (h : addBlockToChainCanonical rules chain cb = .ok (.inl chain')) :
    checkBlockRlpSize rules.block cb.rawSize = .ok () ∧
      stateTransitionWith rules chain cb.block = .ok chain' := by
  unfold addBlockToChainCanonical at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h
  · rename_i hsize
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h
    · rename_i hstw
      simp only [Bind.bind, Except.bind, Except.ok.injEq, Sum.inl.injEq] at h
      exact ⟨hsize, h ▸ hstw⟩

/-- The checked import core: a checked snapshot in, and on the accepting
channel a snapshot whose witness is `CheckedBlockChain.ofImport`. The
validation order is the frozen one, unchanged -- this is the raw checked core
with a checked input type. -/
def addBlockToChainChecked (rules : ForkRules) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    Except String (BlockChain ⊕ String) :=
  addBlockToChainCanonical rules cc.val cb

/-- The checked output of a successful checked import. -/
def CheckedBlockChain.ofImport {rules : ForkRules} {cc : CheckedBlockChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : addBlockToChainChecked rules cc cb = .ok (.inl ch')) : CheckedBlockChain :=
  CheckedBlockChain.ofTransition
    (rules := rules) (cc := cc) (cb := cb)
    (addBlockToChainCanonical_eq_ok_inl h).2

theorem CheckedBlockChain.ofImport_val {rules : ForkRules} {cc : CheckedBlockChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : addBlockToChainChecked rules cc cb = .ok (.inl ch')) :
    (CheckedBlockChain.ofImport h).val = ch' := rfl

theorem CheckedBlockChain.ofImport_tip {rules : ForkRules} {cc : CheckedBlockChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : addBlockToChainChecked rules cc cb = .ok (.inl ch')) :
    (CheckedBlockChain.ofImport h).tip = cb.block := rfl

--------------- CONFIGURED CHECKED ENTRY POINTS ---------------

/-- The configured checked transition. The chain-ID check the raw configured
entry point performs is discharged by the pair's own witness rather than
repeated, and the snapshot is not rechecked at all; what remains is the rule
lookup, which is the only part that depends on the candidate's timestamp. -/
def stateTransitionConfigured (pc : ConfiguredChain) (cb : CanonicalBlock) :
    Except String BlockChain := do
  stateTransitionWith (← pc.config.rulesAt cb.block.header.timestamp)
    pc.chain.val cb.block

/-- The configured checked path agrees with the raw configured entry point on
every input: what it drops is exactly the check its witness already carries. -/
theorem stateTransitionConfigured_eq (pc : ConfiguredChain) (cb : CanonicalBlock) :
    stateTransitionConfigured pc cb
      = stateTransitionUsing pc.config pc.chain.val cb.block := by
  unfold stateTransitionConfigured stateTransitionUsing
  rw [pc.checkChainId_eq_ok]
  rfl

/-- The checked output of a successful configured checked transition. -/
def CheckedBlockChain.ofConfiguredTransition {pc : ConfiguredChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionConfigured pc cb = .ok ch') : CheckedBlockChain :=
  CheckedBlockChain.ofEvidence ch' cb.block
    (by
      obtain ⟨_, _, hst⟩ := Except.bind_eq_ok h
      exact (BlockChain.validContext_of_transition (cc := pc.chain) hst).1)
    (by
      obtain ⟨_, _, hst⟩ := Except.bind_eq_ok h
      exact (BlockChain.validContext_of_transition (cc := pc.chain) hst).2.1)
    (by
      obtain ⟨_, _, hst⟩ := Except.bind_eq_ok h
      exact (BlockChain.validContext_of_transition (cc := pc.chain) hst).2.2.1)
    (by
      obtain ⟨_, _, hst⟩ := Except.bind_eq_ok h
      exact (BlockChain.validContext_of_transition (cc := pc.chain) hst).2.2.2)

--------------- CHECKED/RAW BRIDGES (FOR STEP 11) ---------------

-- Stated so a downstream proof client can move between the raw names its
-- theorems are written about and the checked ones, without unfolding either
-- structure.

theorem stateTransitionChecked_eq_raw (rules : ForkRules) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    stateTransitionChecked rules cc cb
      = stateTransitionCanonical rules cc.val cb := rfl

theorem addBlockToChainChecked_eq_raw (rules : ForkRules) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    addBlockToChainChecked rules cc cb
      = addBlockToChainCanonical rules cc.val cb := rfl

/-- A raw import of bytes into a checked snapshot's value is the checked
import of the envelope those bytes decode to. -/
theorem addBlockToChainWith_eq_checked {rules : ForkRules} {cc : CheckedBlockChain}
    {blockRlp : Bytes} {block : Block} {hash : B256}
    (h : rlpToBlock blockRlp = .ok ⟨block, hash⟩) :
    addBlockToChainWith rules cc.val blockRlp
      = addBlockToChainChecked rules cc (CanonicalBlock.ofDecode h) :=
  addBlockToChainWith_eq_canonical h

/-- Any snapshot a checked value carries passes the checker, so a raw client
that checks first and a checked client that never rechecks agree on which
snapshots are executable. -/
theorem BlockChain.check_eq_some_of_checked (cc : CheckedBlockChain) :
    cc.val.check.isSome = true := cc.check_val

--------------- WIRE-STRUCTURAL PREDICATE BOUNDARY CHECKS ---------------

-- The structural predicates are decidable by finite inspection, so their
-- boundaries are checked by evaluation rather than asserted. Each pair below
-- is the exact wire width the strict decoder enforces: the widest accepted
-- value, then one step past it.

#guard decide (Header.WireWellFormed guardTestHeader)
#guard ¬ decide
  (Header.WireWellFormed { guardTestHeader with bloom := List.replicate 255 0 })
#guard ¬ decide
  (Header.WireWellFormed { guardTestHeader with bloom := List.replicate 257 0 })
#guard decide
  (Header.WireWellFormed { guardTestHeader with difficulty := 2 ^ 256 - 1 })
#guard ¬ decide
  (Header.WireWellFormed { guardTestHeader with difficulty := 2 ^ 256 })
#guard decide
  (Header.WireWellFormed { guardTestHeader with gasLimit := 2 ^ 256 - 1 })
#guard ¬ decide (Header.WireWellFormed { guardTestHeader with gasLimit := 2 ^ 256 })
#guard decide
  (Header.WireWellFormed { guardTestHeader with blobGasUsed := 2 ^ 64 - 1 })
#guard ¬ decide
  (Header.WireWellFormed { guardTestHeader with blobGasUsed := 2 ^ 64 })
#guard decide
  (Header.WireWellFormed { guardTestHeader with excessBlobGas := 2 ^ 64 - 1 })
#guard ¬ decide
  (Header.WireWellFormed { guardTestHeader with excessBlobGas := 2 ^ 64 })

private def wireGuardWithdrawal (amount : B256) : Withdrawal :=
  { globalIndex := 0, validatorIndex := 0, recipient := 0, amount := amount }

-- EIP-4895's 64-bit Gwei amount, at its exact boundary in the 256-bit field.
#guard decide
  (Withdrawal.WireWellFormed (wireGuardWithdrawal (2 ^ 64 - 1 : Nat).toB256))
#guard ¬ decide
  (Withdrawal.WireWellFormed (wireGuardWithdrawal (2 ^ 64 : Nat).toB256))

-- A decoder-produced legacy transaction is structurally certifiable; the same
-- record with a noncanonical or overwide signature scalar, or an overwide
-- value, is not.
#guard (BLT.toExStrTx canonicalLegacyVector).toOption.map
  (fun tx => decide tx.WireWellFormed) = some true
#guard (BLT.toExStrTx canonicalLegacyVector).toOption.map
  (fun tx => decide (Tx.WireWellFormed { tx with r := 0x00 :: tx.r })) = some false
#guard (BLT.toExStrTx canonicalLegacyVector).toOption.map
  (fun tx => decide (Tx.WireWellFormed { tx with s := List.replicate 33 0x01 }))
    = some false
#guard (BLT.toExStrTx canonicalLegacyVector).toOption.map
  (fun tx => decide (Tx.WireWellFormed { tx with value := 2 ^ 256 })) = some false

-- P0.3's headline negative case. A decoded legacy transaction is a legitimate
-- decoded block-body slot; a *typed* transaction is not, because a typed
-- transaction's canonical block encoding is its envelope byte followed by its
-- payload, never the legacy list. This is what forecloses a direct trusted
-- `.inr Tx` on the checked path.
#guard (BLT.toExStrTx canonicalLegacyVector).toOption.map
  (fun tx => decide (TxEntry.WireWellFormed (.inr tx))) = some true
#guard (Bytes.toExStrTx
    (type1Vector [0x01] [0x01] testRecipient [0x01] (.list []))).toOption.map
  (fun tx => decide (TxEntry.WireWellFormed (.inr tx))) = some false
#guard (Bytes.toExStrTx (type2Vector [0x0a] testRecipient [0x02])).toOption.map
  (fun tx => decide (TxEntry.WireWellFormed (.inr tx))) = some false

--------------- CHECKED-CONSTRUCTOR AND ENVELOPE CHECKS ---------------

-- A checked constructor admits what the decoder would produce and refuses
-- everything else outright. It never trims, normalises, or defaults a
-- hand-built value into shape.
#guard (CheckedHeader.ofHeader? guardTestHeader).isSome
#guard (CheckedHeader.ofHeader? { guardTestHeader with bloom := [] }).isNone
#guard (CheckedHeader.ofHeader? { guardTestHeader with gasUsed := 2 ^ 256 }).isNone
#guard (CheckedHeader.ofHeader?
  { guardTestHeader with excessBlobGas := 2 ^ 64 }).isNone
#guard (CheckedWithdrawal.ofWithdrawal?
  (wireGuardWithdrawal (2 ^ 64 - 1 : Nat).toB256)).isSome
#guard (CheckedWithdrawal.ofWithdrawal?
  (wireGuardWithdrawal (2 ^ 64 : Nat).toB256)).isNone

-- A decoded legacy transaction is a legitimate block-body slot and has no
-- typed envelope; a typed transaction is the exact mirror image. This is the
-- pair of facts that leaves no direct trusted `.inr Tx` anywhere on the
-- checked path.
#guard (BLT.toExStrTx canonicalLegacyVector).toOption.map
  (fun tx => (TxEnvelope.ofEntry? (.inr tx)).isSome) = some true
#guard (BLT.toExStrTx canonicalLegacyVector).toOption.map
  (fun tx => (Tx.toTypedEnvelope? tx).isSome) = some false
#guard (Bytes.toExStrTx (type2Vector [0x0a] testRecipient [0x02])).toOption.map
  (fun tx => (TxEnvelope.ofEntry? (.inr tx)).isSome) = some false
#guard (Bytes.toExStrTx (type2Vector [0x0a] testRecipient [0x02])).toOption.map
  (fun tx => (Tx.toTypedEnvelope? tx).isSome) = some true

-- ...and the typed route reproduces the exact envelope bytes it came from, so
-- commitment bytes are unchanged for a transaction that makes the round trip
-- through the checked constructor rather than the decoder.
private def typedEnvelopeBytes? (bs : Bytes) : Option Bytes :=
  (Bytes.toExStrTx bs).toOption.bind fun tx =>
    (Tx.toTypedEnvelope? tx).bind fun env =>
      match env.entry with
      | .inl ys => some ys
      | .inr _ => none

#guard typedEnvelopeBytes?
  (type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf testRecipient testStorageKey))
    = some (type1Vector [0x01] [0x01] testRecipient [0x01]
        (accessListOf testRecipient testStorageKey))
#guard typedEnvelopeBytes? (type2Vector [0x0a] testRecipient [0x02])
  = some (type2Vector [0x0a] testRecipient [0x02])
#guard typedEnvelopeBytes? (type3Vector [0x01] testRecipient testBlobHash)
  = some (type3Vector [0x01] testRecipient testBlobHash)
#guard typedEnvelopeBytes? (type4Vector testRecipient goodAuth)
  = some (type4Vector testRecipient goodAuth)

-- A block carrying a *typed* transaction as a decoded slot cannot be
-- certified: its canonical encoding is not the legacy list it would be
-- re-encoded through.
#guard (CheckedBlock.ofBlock? (guardBlockAt 0)).isSome
#guard (Bytes.toExStrTx (type2Vector [0x0a] testRecipient [0x02])).toOption.map
  (fun tx => (CheckedBlock.ofBlock? { guardBlockAt 0 with txs := [.inr tx] }).isSome)
    = some false
#guard (BLT.toExStrTx canonicalLegacyVector).toOption.map
  (fun tx => (CheckedBlock.ofBlock? { guardBlockAt 0 with txs := [.inr tx] }).isSome)
    = some true
#guard (CheckedBlock.ofBlock?
  { guardBlockAt 0 with header := { guardTestHeader with bloom := [] } }).isNone

-- The envelope exists exactly for bytes that strictly decode and re-encode,
-- and the size it reports is the supplied one.
#guard (CanonicalBlock.ofRlp? (guardBlockAt 0).toBLT.toBytes).isSome
#guard (CanonicalBlock.ofRlp? [0xFF]).isNone
#guard (CanonicalBlock.ofRlp? (guardBlockAt 0).toBLT.toBytes).map
  CanonicalBlock.rawSize = some (guardBlockAt 0).toBLT.toBytes.length
#guard (CanonicalBlock.ofRlp? (guardBlockAt 0).toBLT.toBytes).map
  CanonicalBlock.headerHash
    = some (Header.toBLT (guardBlockAt 0).header).toBytes.keccak

end Jaune
