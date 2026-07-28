import Elevm.Sufficiency

/-!
# Transaction, block, and chain processing

This module holds every declaration that consumes the interpreter driver
defined in `Elevm.Execution`, starting at `processMessageCall.create`, together
with the transaction, block, and chain-level machinery built on top of it. It
was split out of `Elevm.Execution` verbatim so that `Elevm.Sufficiency` can sit
between the driver and its first consumer.
-/

/- `private` declarations do not cross module boundaries, so the two `#guard`
helpers that the moved text shares with `Elevm.Execution` are restated here
rather than being made public. Keep them in step with their counterparts at
`Elevm/Execution.lean:1219`. -/

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
    let evm ← Except.bimap Prod.fst id (processCreateMessage msg)
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
  let evm ← Except.bimap Prod.fst id (processMessage msgPc)
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

def Tx.isTypeFour (tx : Tx) : Bool :=
  match tx.type with
  | .four _ _ _ _ _ _ => true
  | _ => false

-- calculate_total_blob_gas
def calculateTotalBlobGas (tx: Tx) : Nat :=
  match tx.type with
  | .three _ _ _ _ _ _ blobHashes => gasPerBlob * blobHashes.length
  | _ => 0

structure Receipt : Type where
  succeeded : Bool
  gasUsed : Nat
  bloom : B8L
  logs : List Log

structure BlockOutput : Type where
  blockGasUsed : Nat
  transactionsTrie : Std.TreeMap B8L Tx compare
  receiptsTrie : Std.TreeMap B8L (Fin 5 × Receipt) compare
  receiptKeys : List B8L
  blockLogs : List Log
  withdrawalsTrie : Std.TreeMap B8L Withdrawal compare
  blobGasUsed : Nat
  requests : List B8L

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
    if List.any blobHashes (λ bvh => bvh.toB8L[0]! ≠ versionedHashVersionKzg) then
      .error
        s!"{type3InvalidBlobVersionedHashTag} : a blob versioned hash has \
           a version byte other than {versionedHashVersionKzg}"
    else
      let blobGasPrice :=
        calculate_blob_gas_price benv.stat.rules.blob benv.stat.excessBlobGas
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

-- check_transaction
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

-- validate_transaction
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
    if tx.nonce = B64.max then
      .error s!"{nonceIsMaxTag} : transaction nonce is 2^64 - 1"
    checkInitcodeSize rules.code tx.type.receiver? tx.data.length
  | some _ =>
    -- Osaka follows EELS: initcode, EIP-7825 gas cap, then nonce.
    checkInitcodeSize rules.code tx.type.receiver? tx.data.length
    checkTransactionGasCap rules.tx tx.gas
    if tx.nonce = B64.max then
      .error s!"{nonceIsMaxTag} : transaction nonce is 2^64 - 1"
  .ok ⟨intrinsicGas, callDataFloorGasCost⟩

def prepareMessage (benv: Benv) (tenv: Tenv) (tx: Tx) :
  Except String Msg := do
  let ⟨currentTarget, msgData, code, codeAddress⟩ :
    Adr × B8L × ByteArray × Option Adr :=
    match tx.type.receiver? with
    | none => ⟨
        compute_contract_address
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

-- calculate_data_fee
def calculate_data_fee (blob : BlobSchedule) (excess_blob_gas: Nat) (tx: Tx) :
    Nat :=
  calculateTotalBlobGas tx * calculate_blob_gas_price blob excess_blob_gas

def getTxHash (tx : Tx) : B256 := tx.toBLT.toB8L.keccak

def Receipt.toStrings (r : Receipt) : List String :=
  fork "RECEIPT" [
    [s!"SUCCEEDED: {r.succeeded}"],
    [s!"GAS USED: {r.gasUsed}"],
    fork "BLOOM" [r.bloom.toHex.chunks 64],
    fork "LOGS" (r.logs.map Log.toStrings)
  ]

instance : ToString Receipt where
  toString := String.joinln ∘ Receipt.toStrings

def Receipt.toBLT (r : Receipt) : BLT :=
  .list [
    .b8s (if r.succeeded then [0x01] else []),
    .b8s r.gasUsed.toB8LPack,
    .b8s r.bloom,
    .list (r.logs.map Log.toBLT)
  ]

-- make_receipt
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
    (nonce : B64) (bal : B256) (code : ByteArray := .empty) : Acct :=
  { nonce := nonce, bal := bal, stor := .empty, code := code }

#guard hasTag intrinsicGasTooLowTag <|
  validateTransaction pragueRules {fixtureTestTx with gas := txBaseCost - 1}
#guard hasTag nonceIsMaxTag <|
  validateTransaction pragueRules {fixtureTestTx with nonce := B64.max}
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


-- process_transaction
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
    transactionsTrie := bout.transactionsTrie.insert (BLT.b8s index.toB8L).toB8L tx}
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
    then calculate_data_fee benv.stat.rules.blob benv.stat.excessBlobGas tx
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
  let receiptKey : B8L := BLT.toB8L <| .b8s index.toB8L
  let bout ← .ok {bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie := bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ txOutput.logs}
  .ok ⟨state, bout⟩

def BlockOutput.withWithdrawalsTrie
    (bo : BlockOutput) (tr : Std.TreeMap B8L Withdrawal compare) : BlockOutput :=
  {bo with withdrawalsTrie := tr}

def processWithdrawalsTrie (tr : Std.TreeMap B8L Withdrawal compare)
    (wds : List Withdrawal) : Std.TreeMap B8L Withdrawal compare :=
  List.foldl
    (λ acc ⟨i, wd⟩ => acc.insert (BLT.toB8L <| .b8s i.toB8L) wd)
    tr
    wds.putIndex

def processWithdrawalsState (st : State) (wds : List Withdrawal) : State :=
  List.foldl
    (λ acc wd => acc.addBal wd.recipient (wd.amount * (10 ^ 9).toB256))
    st
    wds

-- def process_withdrawal
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
  | .b8s xs => xs.toRlpHash "access list storage key"
  | .list _ =>
    .error <| rlpStructureError "access list storage key"
      "expected a byte-string item"

def BLT.toExStrAccessItem : BLT → Except String (Adr × List B256)
  | .list [.b8s ar, .list ksr] => do
    let a ← ar.toRlpAdr "access list address"
    let ks ← List.mapM BLT.toExStrStorageKey ksr
    .ok ⟨a, ks⟩
  | _ =>
    .error <| rlpStructureError "access list item"
      "expected [address, [storage key, ...]]"

def BLT.toExStrAccessList : BLT → Except String AccessList
  | .list rs => List.mapM BLT.toExStrAccessItem rs
  | .b8s _ =>
    .error <| rlpStructureError "access list" "expected a list item"

def BLT.toExStrBlobHash : BLT → Except String B256
  | .b8s xs => xs.toRlpHash "blob versioned hash"
  | .list _ =>
    .error <| rlpStructureError "blob versioned hash"
      "expected a byte-string item"

def BLT.toExStrAuth : BLT → Except String Auth
  | .list [
      .b8s chainId,
      .b8s address,
      .b8s nonce,
      .b8s yParity,
      .b8s r,
      .b8s s
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

def B8L.toExStrTx : B8L → Except String Tx
  | [] =>
    .error <| rlpStructureError "typed transaction"
      "cannot decode an empty byte string"
  | x :: xs =>
    -- Every scalar is bounded before conversion: `B8L.toB64` truncates modulo
    -- 2^64, so it may only see bytes returned by a strict decoder. Signature
    -- scalars keep their minimally encoded bytes once validated, so signing
    -- and trie bytes are unchanged for valid transactions.
    match x, B8L.toBLT? xs with
    | 0x01, some (.list [
        .b8s chainId,
        .b8s nonce,
        .b8s gasPrice,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .b8s yParity,
        .b8s r,
        .b8s s
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
        .b8s chainId,
        .b8s nonce,
        .b8s maxPriorityFee,
        .b8s maxFee,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .b8s yParity,
        .b8s r,
        .b8s s
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
        .b8s chainId,
        .b8s nonce,
        .b8s maxPriorityFee,
        .b8s maxFee,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .b8s maxBlobFee,
        .list blobHashes,
        .b8s yParity,
        .b8s r,
        .b8s s
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
        .b8s chainId,
        .b8s nonce,
        .b8s maxPriorityFee,
        .b8s maxFee,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .list auths,
        .b8s yParity,
        .b8s r,
        .b8s s
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

def decodeTx : B8L ⊕ Tx → Except String Tx
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
    (target : Adr) (data : B8L) (code : ByteArray) : Msg :=
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

-- process_system_transaction
-- The single boundary shared by all four system transactions (beacon roots,
-- history storage, withdrawal requests, consolidation requests), so each takes
-- its own input state as the original state.
def processSystemTransaction (benv : Benv)
  (target : Adr) (code : ByteArray) (data : B8L) :
  Except String (State × MsgCallOutput) := do
  let benv := benv.beginTransaction
  let txEnv : Tenv := processSystemTransactionTenv benv
  let systemTxMsg : Msg :=
    processSystemTransactionMsg benv txEnv target data code
  processMessageCall systemTxMsg

def extractDepositData (data : B8L) : Except String B8L := do
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
  let pubkey : B8L := data.slice! (pubkeyOffset + 32) pubkeySize
  if data.sliceToNat withdrawalCredentialsOffset 32 ≠ withdrawalCredentialsSize then
    .error s!"{depositEventLayoutTag} : invalid withdrawal credentials size in deposit log"
  let withdrawalCredentials : B8L :=
    data.slice! (withdrawalCredentialsOffset + 32) withdrawalCredentialsSize
  if data.sliceToNat amountOffset 32 ≠ amountSize then
    .error s!"{depositEventLayoutTag} : invalid amount size in deposit log"
  let amount : B8L := data.slice! (amountOffset + 32) amountSize
  if data.sliceToNat signatureOffset 32 ≠ signatureSize then
    .error s!"{depositEventLayoutTag} : invalid signature size in deposit log"
  let signature : B8L := data.slice! (signatureOffset + 32) signatureSize
  if data.sliceToNat indexOffset 32 ≠ indexSize then
    .error s!"{depositEventLayoutTag} : invalid index size in deposit log"
  let index : B8L := data.slice! (indexOffset + 32) indexSize
  .ok (pubkey ++ withdrawalCredentials ++ amount ++ signature ++ index)

-- parse_deposit_requests
def parseDepositRequests
  (bout : BlockOutput) : Except String B8L := do
  let mut depositRequests : B8L := []
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
  (benv : Benv) (target : Adr) (data : B8L) :
  Except String (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  processSystemTransaction benv target systemContractCode data

def processCheckedSystemTransaction
  (benv : Benv) (target : Adr) (data : B8L) :
  Except String (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  if systemContractCode.isEmpty then
    .error s!"InvalidBlock : System contract address {target.toHex} does not contain code"
  let ⟨state, systemTxOutput⟩ ←
    processSystemTransaction benv target systemContractCode data
  if systemTxOutput.error.isSome then
    .error s!"{systemContractCallFailedTag} : system contract ({target.toHex}) call failed: \
      {systemTxOutput.error.get!}"
  .ok ⟨state, systemTxOutput⟩

def processGeneralPurposeRequests
  (benv : Benv) (bout : BlockOutput) :
  Except String (State × BlockOutput) := do
  let depositRequests ← parseDepositRequests bout
  let mut requestsFromExecution : List B8L := bout.requests
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
  (benv : Benv) (txs : List (B8L ⊕ Tx)) (wds : List Withdrawal) :
  Except String (State × BlockOutput) := do
  cprint "\n================================ BEACON ROOTS TX ================================\n"
  let ⟨stBeacon, _⟩ ←
    processUncheckedSystemTransaction benv
      beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toB8L
  let benvBeacon : Benv := benv.withState stBeacon
  cprint "\n================================ HISTORY STORAGE TX ================================\n"
  let lastHash ←
     benvBeacon.stat.blockHashes.getLast?.toExcept "ERROR : block hashes is empty"
  let ⟨stHistory, _⟩ ←
    processUncheckedSystemTransaction benvBeacon
      historyStorageAddress
      lastHash.toB8L
  let benvHistory := benvBeacon.withState stHistory
  cprint "\n================================ MAIN TXS ================================\n"
  let ⟨benvTxs, boutTxs⟩ ←
    applyTransactions (← txs.mapM decodeTx).putIndex benvHistory .init
  cprint s!"\nSTATE AFTER TEST TXS :"
  cprint s!"{benvTxs.state}"
  cprint "\n================================ PROCESS WITHDRAWALS ================================\n"
  let ⟨stWds, boutWds⟩ :=
    processWithdrawals benvTxs boutTxs wds
  cprint "\n================================ PROCESS GENERAL PURPOSE REQUESTS ================================\n"
  processGeneralPurposeRequests (benvTxs.withState stWds) boutWds

-- get_last256_block_hashes
def getLast256BlockHashes (chain : BlockChain) : List B256 :=
  match chain.blocks.reverse.take 255 with
  | [] => []
  | block :: blocks =>
    let hash : B256 := (Header.toBLT block.header).toB8L.keccak
    let hashes : List B256 :=
      (block :: blocks).map <| fun x => x.header.parentHash
    (hash :: hashes).reverse

def computeRequestsHash (requests : List B8L) : B256 :=
  -- EIP-7685 commits the SHA-256 digest of each type-prefixed request, then
  -- hashes their concatenation once more.  This is deliberately not the EVM
  -- Keccak primitive used by transaction and trie commitments.
  let hashes := requests.map (fun r => r.sha256.toB8L)
  B8L.sha256 <| List.flatten hashes

def State.root (w : State) : B256 :=
  let keyVals := (List.map toKeyVal w.toList)
  let finalNTB : NTB := Std.TreeMap.ofList keyVals _
  trie finalNTB

def stateTransitionChecks (bout : BlockOutput) (header : Header)
    (transactionsRoot blockStateRoot receiptRoot : B256)
    (blockLogsBloom : B8L) (withdrawalsRoot requestsHash : B256) :
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
  let aux (arg : B8L × Tx) : (B8L × B8L) :=
    let txPrefix : B8L :=
      match arg.snd.type with
      | .zero _ _ => []
      | .one _ _ _ _ => [0x01]
      | .two _ _ _ _ _ => [0x02]
      | .three _ _ _ _ _ _ _ => [0x03]
      | .four _ _ _ _ _ _ => [0x04]
    ⟨arg.fst.toB4s, txPrefix ++ arg.snd.toBLT.toB8L⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.transactionsTrie.toList) _

def getReceiptRoot (bout : BlockOutput) : B256 :=
  let aux : (B8L × Fin 5 × Receipt) → (B8L × B8L)
    | ⟨key, type, receipt⟩ => ⟨key.toB4s, type.val.toB8L ++ receipt.toBLT.toB8L⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.receiptsTrie.toList) _

def getWithdrawalsRoot (bout : BlockOutput) : B256 :=
  let aux (arg : B8L × Withdrawal) : B8L × B8L :=
    ⟨arg.fst.toB4s, arg.snd.toBLT.toB8L⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.withdrawalsTrie.toList) _

def stateTransitionOmmersCheck (ommers : List Header) : Except String Unit := do
  if ¬ommers.isEmpty then do
    .error
      s!"{ommersOverParisTag} : block body contains {ommers.length} ommer(s), \
         which is impossible after Paris"

def appendBlock (blks : List Block) (blk : Block) : List Block :=
  (blk :: blks.reverse.take 254).reverse

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
  let blockLogsBloom : B8L := logsBloom bout.blockLogs
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

/-- The block state transition on a configured chain, deriving the active fork
from the block's timestamp and the chain's activation schedule. -/
def stateTransitionUsing (cfg : ChainConfig) (ch : BlockChain) (block : Block) :
    Except String BlockChain := do
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
      .b8s globalIndex,
      .b8s validatorIndex,
      .b8s recipient,
      .b8s amount
    ] => do
    -- Check every untrusted field before constructing the withdrawal. In
    -- particular, `B8L.toB64` truncates modulo 2^64, so it may only see the
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

def BLT.toExStrTx : BLT → Except String Tx
  | .list [
      .b8s nonce,
      .b8s gasPrice,
      .b8s gas,
      .b8s receiver,
      .b8s value,
      .b8s data,
      .b8s v,
      .b8s r,
      .b8s s
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
  | .b8s xs => xs.toExStrTx

def BLT.toExStrBlock : BLT → Except String Block
  | BLT.list [
      HeaderBLT,
      .list TxBLTs,
      .list OmmerBLTs,
      .list WithdrawalBLTs
    ] => do
    let header ← HeaderBLT.toExStrHeader
    let aux : BLT → Except String (B8L ⊕ Tx)
      | blt@(.list _) => blt.toExStrTx <&> .inr
      | .b8s xs => .ok <| .inl xs
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

/-
rlpToBlock is equivalent to json_to_block from execution-specs.
why does it accept the RLP bytes as input, and not the whole JSON?
the justification is that json_to_block expects the RLP bytes to be
always available, and always uses *only* the RLP bytes to obtain the
block, ignoring everything else in the JSON (the code path that deals
with nonexistent RLP bytes exists, but is unreachable). its return
type also omits the RLP bytes, since this is identical to the input.
-/
def rlpToBlock (rlp : B8L) : Except String (Block × B256) := do
  let block_blt ← (B8L.toBLT? rlp).toExcept <|
    rlpStructureError "block RLP" "cannot decode the outer RLP item"
  let block ← block_blt.toExStrBlock
  let canonicalRlp := block.toBLT.toB8L
  if rlp ≠ canonicalRlp then
    .error
      s!"{rlpRoundTripTag} : decoded block does not re-encode byte-for-byte"
  .ok ⟨block, (Header.toBLT block.header).toB8L.keccak⟩

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
    (globalIndex validatorIndex recipient amount : B8L) : BLT :=
  .list [.b8s globalIndex, .b8s validatorIndex, .b8s recipient, .b8s amount]

private def legacyDecoderVector
    (nonce gasPrice gas receiver value v r s : B8L) : BLT :=
  .list [
    .b8s nonce, .b8s gasPrice, .b8s gas, .b8s receiver, .b8s value,
    .b8s [], .b8s v, .b8s r, .b8s s
  ]

private def nineByteScalar : B8L := 0x01 :: List.replicate 8 0x00
private def thirtyThreeByteScalar : B8L := 0x01 :: List.replicate 32 0x00
private def testRecipient : B8L := List.replicate 20 0x11

-- Both withdrawal index positions reject nine bytes at the field boundary;
-- neither can reach the truncating `B8L.toB64` conversion unchecked.
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
  (BLT.toExStrTx canonicalLegacyVector).toOption.map (fun tx => tx.toBLT.toB8L)
    == some canonicalLegacyVector.toB8L

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
  BLT.toExStrBlock (.list [.b8s [], .list [], .list []])
#guard hasTag rlpStructureTag <| BLT.toExStrBlock (.b8s [])

--------- STRICT TYPED-TRANSACTION DECODER REGRESSION CHECKS ----------

-- A typed transaction is its type byte followed by the RLP encoding of its
-- payload list. Each negative vector below is a one-field mutation of its
-- type's positive vector, so the failing field is unambiguous.

private def typedTxVector (type : B8) (fields : List BLT) : B8L :=
  type :: BLT.toB8L (.list fields)

private def testStorageKey : B8L := List.replicate 32 0x22
private def testBlobHash : B8L := 0x01 :: List.replicate 31 0x33
-- Thirty-two bytes with a nonzero leading byte: a canonical full-width
-- scalar, usable for `r`/`s` at the transaction and authorization level.
private def fullWidthScalar : B8L := 0x01 :: List.replicate 31 0x00

private def accessListOf (adr key : B8L) : BLT :=
  .list [.list [.b8s adr, .list [.b8s key]]]

private def authOf (chainId adr nonce r s : B8L) : BLT :=
  .list [.b8s chainId, .b8s adr, .b8s nonce, .b8s [0x01], .b8s r, .b8s s]

private def type1Vector (chainId nonce receiver r : B8L) (accessList : BLT) : B8L :=
  typedTxVector 0x01 [
    .b8s chainId, .b8s nonce, .b8s [0x0a], .b8s [0x52, 0x08], .b8s receiver,
    .b8s [], .b8s [], accessList, .b8s [0x01], .b8s r, .b8s [0x02]
  ]

private def type2Vector (maxFee receiver s : B8L) : B8L :=
  typedTxVector 0x02 [
    .b8s [0x01], .b8s [0x01], .b8s [0x01], .b8s maxFee, .b8s [0x52, 0x08],
    .b8s receiver, .b8s [], .b8s [], .list [], .b8s [0x01], .b8s [0x01], .b8s s
  ]

private def type3Vector (nonce receiver blobHash : B8L) : B8L :=
  typedTxVector 0x03 [
    .b8s [0x01], .b8s nonce, .b8s [0x01], .b8s [0x0a], .b8s [0x52, 0x08],
    .b8s receiver, .b8s [], .b8s [], .list [], .b8s [0x01],
    .list [.b8s blobHash], .b8s [0x01], .b8s [0x01], .b8s [0x02]
  ]

private def type4Vector (receiver : B8L) (auth : BLT) : B8L :=
  typedTxVector 0x04 [
    .b8s [0x01], .b8s [0x01], .b8s [0x01], .b8s [0x0a], .b8s [0x52, 0x08],
    .b8s receiver, .b8s [], .b8s [], .list [], .list [auth],
    .b8s [0x01], .b8s [0x01], .b8s [0x02]
  ]

private def goodAuth : BLT :=
  authOf [0x01] testRecipient [0x01] fullWidthScalar fullWidthScalar

-- One positive vector per type: it decodes, and it re-encodes to the exact
-- input bytes, so trie bytes for valid transactions are unchanged.
private def reencodes (type : B8) (v : B8L) : Bool :=
  (B8L.toExStrTx v).toOption.map (fun tx => type :: tx.toBLT.toB8L) == some v

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
private def shortWidthScalar : B8L := 0x01 :: List.replicate 30 0x00

#guard reencodes 0x04 <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] shortWidthScalar fullWidthScalar
#guard reencodes 0x04 <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] fullWidthScalar shortWidthScalar
#guard reencodes 0x04 <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] [0x01] [0x02]

-- A type-1/type-2 receiver may be empty, meaning contract creation...
#guard (B8L.toExStrTx (type2Vector [0x0a] [] [0x02])).toOption.isSome
-- ...but an empty type-3 receiver is the semantic contract-creation identity;
-- nonempty 19/21-byte receivers still fail as malformed RLP fields.
#guard hasTag type3ContractCreationTag <|
  B8L.toExStrTx <| type3Vector [0x01] [] testBlobHash
#guard hasTag rlpFixedWidthTag <|
  B8L.toExStrTx <| type3Vector [0x01] (List.replicate 19 0x11) testBlobHash
#guard hasTag rlpFixedWidthTag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] (List.replicate 21 0x11) [0x01] (.list [])
#guard hasTag rlpFixedWidthTag <|
  B8L.toExStrTx <| type4Vector (List.replicate 19 0x11) goodAuth

-- Oversized scalars are overflows at the field boundary, not truncations.
#guard hasTag rlpFieldOverflow64Tag <| B8L.toExStrTx <|
  type1Vector [0x01] nineByteScalar testRecipient [0x01] (.list [])
#guard hasTag rlpFieldOverflow64Tag <| B8L.toExStrTx <|
  type1Vector nineByteScalar [0x01] testRecipient [0x01] (.list [])
#guard hasTag rlpFieldOverflow64Tag <|
  B8L.toExStrTx <| type3Vector nineByteScalar testRecipient testBlobHash
#guard hasTag rlpFieldOverflow256Tag <|
  B8L.toExStrTx <| type2Vector thirtyThreeByteScalar testRecipient [0x02]
-- The two fields the deleted `reverse.takeD 32` pattern used to truncate.
#guard hasTag rlpFieldOverflow256Tag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient thirtyThreeByteScalar (.list [])
#guard hasTag rlpFieldOverflow256Tag <|
  B8L.toExStrTx <| type2Vector [0x0a] testRecipient thirtyThreeByteScalar

-- Access lists: exact address and storage-key widths, and both list shapes.
#guard hasTag rlpFixedWidthTag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf (List.replicate 21 0x11) testStorageKey)
#guard hasTag rlpFixedWidthTag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf testRecipient (List.replicate 33 0x22))
#guard hasTag rlpFixedWidthTag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf testRecipient (List.replicate 31 0x22))
#guard hasTag rlpStructureTag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01] (.list [.b8s []])
#guard hasTag rlpStructureTag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01] (.b8s [])

-- Blob versioned hashes: exactly thirty-two bytes, both sides.
#guard hasTag rlpFixedWidthTag <| B8L.toExStrTx <|
  type3Vector [0x01] testRecipient (0x01 :: List.replicate 32 0x33)
#guard hasTag rlpFixedWidthTag <|
  B8L.toExStrTx <| type3Vector [0x01] testRecipient (List.replicate 31 0x33)

-- Authorizations: exact address width, a uint256 chainId, bounded nonce and
-- r/s, and the six-field list shape.
#guard hasTag rlpFixedWidthTag <| B8L.toExStrTx <| type4Vector testRecipient <|
  authOf [0x01] (List.replicate 21 0x11) [0x01] fullWidthScalar fullWidthScalar
#guard (B8L.toExStrTx <| type4Vector testRecipient <|
  authOf nineByteScalar testRecipient [0x01] fullWidthScalar fullWidthScalar).toOption.isSome
#guard hasTag rlpFieldOverflow64Tag <| B8L.toExStrTx <| type4Vector testRecipient <|
  authOf [0x01] testRecipient nineByteScalar fullWidthScalar fullWidthScalar
#guard hasTag rlpFieldOverflow256Tag <| B8L.toExStrTx <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] thirtyThreeByteScalar fullWidthScalar
#guard hasTag rlpFieldOverflow256Tag <| B8L.toExStrTx <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] fullWidthScalar thirtyThreeByteScalar
#guard hasTag rlpStructureTag <| B8L.toExStrTx <|
  type4Vector testRecipient (.list [.b8s [0x01], .b8s testRecipient])

-- A wrong list shape for a known type byte is a structure error; an unknown
-- type byte keeps its own failure; empty input is a structure error.
#guard hasTag rlpStructureTag <| B8L.toExStrTx (0x01 :: BLT.toB8L (.b8s []))
#guard hasTag rlpStructureTag <| B8L.toExStrTx (0x02 :: BLT.toB8L (.list []))
#guard hasTag rlpStructureTag <| B8L.toExStrTx []
#guard ¬ hasTag rlpStructureTag (B8L.toExStrTx [0x05])
#guard (B8L.toExStrTx [0x05]).toOption.isNone

/-- Block import from an already-decoded block, under an explicit rule set.

Split out so that a configured chain can read the block's timestamp to select
its rules without decoding the RLP a second time. The two failure channels are
unchanged: `.error` is a harness-level failure, `.inr` is a block this chain
rejects. -/
private def addBlockToChainCore (rules : ForkRules) (chain : BlockChain)
    (block : Block) (blockHeaderHash : B256) (rawRlpSize : Nat) :
    Except String (BlockChain ⊕ String) := do
  cprint "\nSTATE BEFORE TRANSITION :"
  cprint s!"{chain.state}"
  if (Header.toBLT block.header).toB8L.keccak ≠ blockHeaderHash then do
    .error "ERROR : incorrect block header hash"
  -- Strict decode/round-trip and the independent header-hash evidence above
  -- are harness prerequisites. Among consensus checks EIP-7934 is first,
  -- before `stateTransitionWith` reaches header validation, exactly as EELS.
  match checkBlockRlpSize rules.block rawRlpSize with
  | .error err => return .inr err
  | .ok () => pure ()
  let chain ←
    match stateTransitionWith rules chain block with
    | .error err => return (.inr err)
    | .ok chain => .ok chain
  cprint s!"\nSTATE AFTER TRANSITION :"
  cprint s!"{chain.state}"
  .ok (.inl chain)

/-- Block import under an explicit rule set. -/
def addBlockToChainWith (rules : ForkRules) (chain : BlockChain)
    (blockRlp : B8L) : Except String (BlockChain ⊕ String) := do
  let ⟨block, blockHeaderHash⟩ ← rlpToBlock blockRlp
  addBlockToChainCore rules chain block blockHeaderHash blockRlp.length

/-- Block import at an explicitly named fork, for static fixture suites.

An unimplemented fork fails on the `.error` channel: it is a limitation of this
build, not a verdict that the block is invalid, and must never be recorded as
one. -/
def addBlockToChainAt (f : Fork) (chain : BlockChain) (blockRlp : B8L) :
    Except String (BlockChain ⊕ String) := do
  addBlockToChainWith (← f.rules) chain blockRlp

/-- Block import on a configured chain, deriving the active fork from the
block's own timestamp and the chain's activation schedule. -/
def addBlockToChainUsing (cfg : ChainConfig) (chain : BlockChain)
    (blockRlp : B8L) : Except String (BlockChain ⊕ String) := do
  let ⟨block, blockHeaderHash⟩ ← rlpToBlock blockRlp
  let rules ← cfg.rulesAt block.header.timestamp
  addBlockToChainCore rules chain block blockHeaderHash blockRlp.length

/-- Prague block import.

Retained with its original name, type, and behaviour; downstream proofs state
their results about this name. -/
def addBlockToChain (chain : BlockChain) (blockRlp : B8L) :
  Except String (BlockChain ⊕ String) :=
  addBlockToChainWith pragueRules chain blockRlp

---------------- FORK ARCHITECTURE CHECKS ----------------

-- The Prague entry points are not merely *compatible* with the rules-explicit
-- core at Prague: they are that core, for every input. `rfl` is the point --
-- an equality on sample data would leave room for a wrapper that diverges
-- somewhere else, and downstream proofs state their results about these names.

example (ch : BlockChain) (block : Block) :
    stateTransition ch block = stateTransitionWith pragueRules ch block := rfl

example (ch : BlockChain) (block : Block) :
    stateTransitionAt .prague ch block = stateTransition ch block := rfl

example (chain : BlockChain) (blockRlp : B8L) :
    addBlockToChain chain blockRlp
      = addBlockToChainWith pragueRules chain blockRlp := rfl

example (chain : BlockChain) (blockRlp : B8L) :
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
  bloom := List.replicate 256 (0 : B8)
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
  (addBlockToChainAt f guardEmptyChain (guardBlockAt 0).toBLT.toB8L))

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
      parentHash := (Header.toBLT guardParentHeader).toB8L.keccak }
    txs := []
    ommers := []
    wds := [] }

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

private def guardChildRlp (timestamp excessBlobGas : Nat) : B8L :=
  (guardChildBlock timestamp excessBlobGas).toBLT.toB8L

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
