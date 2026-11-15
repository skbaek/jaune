-- Check/Transaction.lean : executable checks of `Jaune/Transaction.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/Transaction.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.Transaction
import Jaune.Check.Machine

namespace Jaune

open Jaune

#guard TransitionError.render (.internal (.invariant (.text "balance underflow")))
  = "ERROR : balance underflow"
#guard TransitionError.render (.vm (.crypto (.pointCompression .none)))
  = "bCompress failed"
#guard (TransitionError.split (.internal (.assertion .none))).isLeft
#guard (TransitionError.split (.vm .revert)).isLeft
#guard (TransitionError.split (.decode (.roundTrip .none))).isRight
#guard (TransitionError.split (.senderRecovery (.invalidSignature .none))).isRight

-- Golden guards. Each vocabulary is pinned constructor-by-constructor to the
-- tag it renders under, so a migrated producer cannot silently change an
-- externally observed message or route a reason to the wrong identity.
#guard TxValidationError.all.length = 22
#guard TxValidationError.all.eraseDups.length = 22
#guard TxValidationError.all.map TxValidationError.tag = transactionExceptionTags
#guard (TxValidationError.all.map TxValidationError.tag).eraseDups.length = 22
#guard TxValidationError.render
    (.insufficientMaxFeePerBlobGas (.text "insufficient max fee per blob gas"))
  = "InsufficientMaxFeePerBlobGasError : insufficient max fee per blob gas"
#guard TxValidationError.render (.nonceMismatchTooHigh .none)
  = "NonceMismatchTooHighError"
#guard TxValidationError.render (.intrinsicGasTooLow (.text "needs 21000, has 20999"))
  = "IntrinsicGasTooLowError : needs 21000, has 20999"

#guard BlockValidationError.all.length = 32
#guard BlockValidationError.all.eraseDups.length = 32
#guard BlockValidationError.all.map BlockValidationError.tag = blockExceptionTags
#guard (BlockValidationError.all.map BlockValidationError.tag).eraseDups.length = 32
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
#guard BlockRejection.render (.senderRecovery (.invalidSignature (.text "bad v")))
  = "InvalidSignatureError : bad v"

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

-- The empty list hashes to `keccak(rlp [])`, which is `emptyOmmerHash`.
#guard BlockAccessList.hash [] = emptyOmmerHash
#guard BlockAccessList.encode [] = [0xC0]
#guard BlockAccessList.itemCount [] = 0

-- `canonicalise` on the shapes the corpus's two format cases take: a reversed
-- pair is re-sorted, an exact duplicate collapses, and a canonical list is a
-- fixed point -- while two entries at one address with different content are
-- both kept, so a content defect can never pass as a format defect.
private def guardBalHi : BalAccountChanges :=
  { address := beaconRootsAddress, storageChanges := [], storageReads := [],
    balanceChanges := [], nonceChanges := [(1, 1)], codeChanges := [] }
private def guardBalLo : BalAccountChanges :=
  { address := historyStorageAddress, storageChanges := [], storageReads := [0x200b],
    balanceChanges := [], nonceChanges := [], codeChanges := [] }
private def guardBalLo' : BalAccountChanges := { guardBalLo with storageReads := [0x200c] }
#guard compare historyStorageAddress beaconRootsAddress = .lt
#guard BlockAccessList.encode (BlockAccessList.canonicalise [guardBalHi, guardBalLo]) =
  BlockAccessList.encode [guardBalLo, guardBalHi]
#guard BlockAccessList.encode (BlockAccessList.canonicalise [guardBalLo, guardBalHi, guardBalHi]) =
  BlockAccessList.encode [guardBalLo, guardBalHi]
#guard BlockAccessList.encode (BlockAccessList.canonicalise [guardBalLo, guardBalHi]) =
  BlockAccessList.encode [guardBalLo, guardBalHi]
#guard BlockAccessList.encode (BlockAccessList.canonicalise [guardBalLo, guardBalLo', guardBalHi]) =
  BlockAccessList.encode [guardBalLo, guardBalLo', guardBalHi]
#guard BlockAccessList.encode (BlockAccessList.canonicalise []) = [0xC0]

-- The `none` state-gas lanes -- `Xinst`'s legacy call and create paths and the
-- legacy top-level dispatch -- record no access-list reads. That is sound only
-- while every supported fork with a block-level access list also meters state
-- gas, so those lanes are never taken under `bal` rules; this pins it.
#guard Fork.supported.all fun f =>
  match f.rules? with
  | some r => !r.bal.isSome || r.stateGas.isSome
  | none => true

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
      fork := .prague
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

private def fixtureAmsterdamBenv (blockGasLimit : Nat := 30000000)
    (state : State := .empty) (origState : State := .empty) : Benv :=
  let base := fixtureTestBenv blockGasLimit
  { base with
    state := state
    stat := {base.stat with fork := .amsterdam, origState := origState}
  }

private def fixtureAmsterdamMsg (state origState : State)
    (target : Option Adr) (currentTarget : Adr) (value gas grant : Nat)
    (accessed : AdrSet := .emptyWithCapacity) : Msg :=
  { (default : Msg) with
    benv := fixtureAmsterdamBenv (state := state) (origState := origState)
    tenv := { (default : Tenv) with stat := {
      (default : TenvStat) with
      origin := 1
      gas := gas
      stateGasReservoir := grant
    }}
    caller := 1
    target := target
    currentTarget := currentTarget
    gas := gas
    value := value.toB256
    codeAddress := target
    code := state.getCode currentTarget
    depth := 1024
    shouldTransferValue := true
    accessedAddresses := accessed
    stateGasGrant := grant
  }

private def delegationChargeGuard (doRepeat : Bool) :
    Option (Nat × Nat × Nat × Nat) :=
  let msg := fixtureAmsterdamMsg .empty .empty (some 2) 2 0 20000 300000
  let initial := initDevm msg
  match applyValidatedDelegationAmsterdam amsterdamStateGasRules msg 5 6
      initial .emptyWithCapacity .emptyWithCapacity with
  | .error _ => none
  | .ok ⟨once, paid, setFor⟩ =>
    if doRepeat then
      match applyValidatedDelegationAmsterdam amsterdamStateGasRules msg 5 7
          once paid setFor with
      | .error _ => none
      | .ok ⟨twice, _, _⟩ =>
        some ⟨once.gasLeft, once.stateGasLeft,
          twice.gasLeft, twice.stateGasLeft⟩
    else some ⟨once.gasLeft, once.stateGasLeft, 0, 0⟩

private def prepareCreateGuard (collision : Bool) :
    Option (Nat × Nat × Option SettledHalt) :=
  let address : Adr := 9
  let account := fixtureTestAccount 1 0
  let state := if collision then State.set .empty address account else .empty
  let msg := fixtureAmsterdamMsg state state none address 0 20000 200000
  match prepareTopLevelAmsterdam amsterdamStateGasRules msg with
  | .ok ⟨_, devm⟩ => some ⟨devm.gasLeft, devm.stateGasLeft, none⟩
  | .error ⟨error, devm⟩ =>
    match settleTopLevelPreparationFailure msg error devm with
    | .ok ⟨_, output⟩ =>
      some ⟨output.gasLeft, output.stateGasLeft, output.error⟩
    | .error _ => none

private def delegatedDispatchGuard (warm : Bool) :
    Option (Nat × Nat × Option Adr) :=
  let target : Adr := 10
  let delegate : Adr := 11
  let delegation :=
    (eoaDelegationMarker ++ delegate.toBytes).toByteArray
  let state :=
    (State.set .empty target (fixtureTestAccount 0 0 delegation)).set
      delegate (fixtureTestAccount 0 0 (.mk (.mk [0x00])))
  let accessed : AdrSet :=
    if warm then ({target, delegate} : AdrSet) else {target}
  let msg := fixtureAmsterdamMsg state state (some target) target 0
    10000 0 accessed
  match prepareTopLevelAmsterdam amsterdamStateGasRules msg with
  | .error _ => none
  | .ok ⟨prepared, devm⟩ =>
    some ⟨devm.gasLeft, devm.stateGasLeft, prepared.codeAddress⟩

/-! The W5 value tables.  These evaluate the production definitions and pin
the split that downstream t8n vectors observe. -/

private def plainAmsterdamTransfer : Tx :=
  {fixtureTestTx with gas := 30000000, value := 1, type := .zero 10 (some 2)}

private def fixtureTestAuth : Auth :=
  {chainId := 0, address := 0, nonce := 0, yParity := 0, r := 0, s := 0}

#guard calculateIntrinsicCost amsterdamRules plainAmsterdamTransfer 1
  = ⟨21000, 21000⟩
#guard calculateIntrinsicCost amsterdamRules
    {plainAmsterdamTransfer with type := .zero 10 (some 1)} 1
  = ⟨12000, 12000⟩
#guard calculateIntrinsicCost amsterdamRules
    {fixtureTestTx with gas := 30000000, type := .zero 10 none} 1
  = ⟨24000, 24000⟩
#guard calculateIntrinsicCost amsterdamRules
    {fixtureTestTx with gas := 30000000, type := .one 1 10 (some 2) [(3, [4])]} 1
  = ⟨23228, 18328⟩
#guard (calculateIntrinsicCost amsterdamRules
    {fixtureTestTx with gas := 30000000, type := .four 1 1 10 2 [] [fixtureTestAuth]} 1).1
  = 12000 + 3000 + 7816

private def amsterdamTxMaxGas : Nat :=
  amsterdamRules.tx.maxGas.getD 0

#guard (validateTransaction amsterdamRules
    {plainAmsterdamTransfer with gas := amsterdamTxMaxGas + 1} 1).toOption.isSome
#guard allocateEvmGas amsterdamRules (amsterdamTxMaxGas + 100) 21000
  = ⟨amsterdamTxMaxGas - 21000, 100⟩

#guard settleTransactionGas pragueRules 1000 0 100 777 100 999
  = ⟨800, 200, 800, 0⟩
#guard settleTransactionGas amsterdamRules 1000 600 100 200 100 50
  = ⟨600, 400, 650, 50⟩
#guard settleTransactionGas amsterdamRules 1000 0 100 200 1000 (-50)
  = ⟨560, 440, 700, 0⟩

#guard delegationChargeGuard false =
  some ⟨11000, 81210, 0, 0⟩
-- The second write to one authority pays neither ACCOUNT_WRITE nor AUTH_BASE.
#guard delegationChargeGuard true =
  some ⟨11000, 81210, 11000, 81210⟩
#guard prepareCreateGuard false = some ⟨20000, 16400, none⟩
#guard prepareCreateGuard true =
  some ⟨0, 200000, some (.halt (.addressCollision .none))⟩

-- Storage-only top-level creation deploys and wipes storage in both lanes;
-- code and nonce remain independent collision controls.
private def legacyStorageOnlyCreateGuard : Bool :=
  let address : Adr := 12
  let state := State.setStorVal .empty address 1 1
  let msg : Msg :=
    {(default : Msg) with
      benv := {(default : Benv) with state := state}
      target := none, currentTarget := address, gas := 20000, depth := 1024}
  match processMessageCall.create msg with
  | .ok ⟨post, output⟩ =>
    output.error.isNone && (post.get address).stor.isEmpty && (post.get address).nonce == 1
  | .error _ => false

private def amsterdamStorageOnlyCreateGuard : Bool :=
  let address : Adr := 13
  let state := State.setStorVal .empty address 1 1
  let msg := fixtureAmsterdamMsg state state none address 0 20000 200000
  match processMessageCall.create msg with
  | .ok ⟨post, output⟩ =>
    output.error.isNone && (post.get address).stor.isEmpty && (post.get address).nonce == 1
  | .error _ => false

private def legacyCreateCollisionGuard (code : Bool) : Bool :=
  let address : Adr := 14
  let state :=
    if code then State.setCode .empty address (.mk (.mk [0x00]))
    else State.set .empty address (fixtureTestAccount 1 0)
  let msg : Msg :=
    {(default : Msg) with
      benv := {(default : Benv) with state := state}
      target := none, currentTarget := address, gas := 20000, depth := 1024}
  match processMessageCall.create msg with
  | .ok ⟨_, output⟩ =>
    output.gasLeft == 0 && output.error == some (.halt (.addressCollision .none))
  | .error _ => false

private def amsterdamCreateCollisionGuard (code : Bool) : Bool :=
  let address : Adr := 15
  let state :=
    if code then State.setCode .empty address (.mk (.mk [0x00]))
    else State.set .empty address (fixtureTestAccount 1 0)
  let msg := fixtureAmsterdamMsg state state none address 0 20000 200000
  match prepareTopLevelAmsterdam amsterdamStateGasRules msg with
  | .error ⟨.halt (.addressCollision .none), _⟩ => true
  | _ => false

#guard legacyStorageOnlyCreateGuard
#guard amsterdamStorageOnlyCreateGuard
#guard legacyCreateCollisionGuard true
#guard legacyCreateCollisionGuard false
#guard amsterdamCreateCollisionGuard true
#guard amsterdamCreateCollisionGuard false
#guard delegatedDispatchGuard false = some ⟨7000, 0, some 11⟩
#guard delegatedDispatchGuard true = some ⟨9900, 0, some 11⟩
-- Constructor-level matcher for the transaction-validation boundary guards.
private def txvFails {α : Type} (p : TxValidationError → Bool) :
    Except TxValidationError α → Bool
  | .error e => p e
  | .ok _ => false

#guard txvFails (fun | .intrinsicGasTooLow _ => true | _ => false) <|
  validateTransaction pragueRules {fixtureTestTx with gas := txBaseCost - 1} 0
#guard txvFails (fun | .nonceIsMax _ => true | _ => false) <|
  validateTransaction pragueRules {fixtureTestTx with nonce := UInt64.max} 0
#guard txvFails (fun | .initcodeSizeExceeded _ => true | _ => false) <|
  checkInitcodeSize pragueRules.code none (pragueRules.code.maxInitCodeSize + 1)

-- EIP-8037 admits the total-cap boundary, rejects the next unit, and
-- leaves EIP-7825 as the independent execution bound in `allocateEvmGas`.
#guard (validateTransaction amsterdamRules
    {plainAmsterdamTransfer with gas := 2 ^ 32 - 1} 1).toOption.isSome
#guard txvFails (fun | .transactionGasLimitExceeded _ => true | _ => false) <|
  validateTransaction amsterdamRules
    {plainAmsterdamTransfer with gas := 2 ^ 32} 1
#guard (checkTransactionTotalGasCap bpo2Rules.tx (2 ^ 32)).toOption.isSome

-- EIP-7825 is inclusive at `2 ^ 24`, and absent at Prague.
#guard (checkTransactionGasCap osakaRules.tx (2 ^ 24 - 1)).toOption.isSome
#guard (checkTransactionGasCap osakaRules.tx (2 ^ 24)).toOption.isSome
#guard txvFails (fun | .transactionGasLimitExceeded _ => true | _ => false) <|
  checkTransactionGasCap osakaRules.tx (2 ^ 24 + 1)
#guard (checkTransactionGasCap pragueRules.tx (2 ^ 24 + 1)).toOption.isSome
#guard txvFails (fun | .transactionGasLimitExceeded _ => true | _ => false) <|
  validateTransaction osakaRules {fixtureTestTx with gas := 2 ^ 24 + 1} 0

-- The initcode bound comes from the rules record, not from a global: a smaller
-- limit rejects an initcode the Prague limit accepts, at the same boundary.
private def guardTightCodeLimits : CodeLimits :=
  { maxCodeSize := 100, maxInitCodeSize := 200 }

#guard (checkInitcodeSize pragueRules.code none 200).toOption.isSome
#guard (checkInitcodeSize guardTightCodeLimits none 200).toOption.isSome
#guard txvFails (fun | .initcodeSizeExceeded _ => true | _ => false) <|
  checkInitcodeSize guardTightCodeLimits none 201

-- EIP-7954 (goal C, G5): the creation-transaction data check reads Amsterdam's
-- raised limit through `rules.code` -- inclusive at 0x20000 -- while BPO2's
-- 0xC000 limit is unchanged.
#guard (checkInitcodeSize amsterdamRules.code none 0x20000).toOption.isSome
#guard txvFails (fun | .initcodeSizeExceeded _ => true | _ => false) <|
  checkInitcodeSize amsterdamRules.code none (0x20000 + 1)
#guard (checkInitcodeSize bpo2Rules.code none 0xC000).toOption.isSome
#guard txvFails (fun | .initcodeSizeExceeded _ => true | _ => false) <|
  checkInitcodeSize bpo2Rules.code none (0xC000 + 1)
#guard (checkInitcodeSize amsterdamRules.code (some 0x1234) (0x20000 + 1)).toOption.isSome
-- A non-creation transaction is unaffected by the limit under either schedule.
#guard (checkInitcodeSize guardTightCodeLimits (some 0) 100000).toOption.isSome

#guard txvFails (fun | .priorityGreaterThanMaxFee _ => true | _ => false) <|
  checkTransactionDynamicGasFee 1 1 2 1
#guard txvFails (fun | .insufficientMaxFeePerGas _ => true | _ => false) <|
  checkTransactionDynamicGasFee 2 1 1 1
#guard txvFails (fun | .gasPriceProductOverflow _ => true | _ => false) <|
  checkTransactionDynamicGasFee 0 2 0 (2 ^ 255)
#guard txvFails (fun | .gasPriceProductOverflow _ => true | _ => false) <|
  checkTransactionLegacyGasFee 0 2 (2 ^ 255)

#guard txvFails (fun | .gasAllowanceExceeded _ => true | _ => false) <|
  checkTransactionGasLimits (fixtureTestBenv txBaseCost) .init
    {fixtureTestTx with gas := txBaseCost + 1}

private def amsterdamCapacityTx : Tx :=
  {plainAmsterdamTransfer with gas := amsterdamTxMaxGas + 50}

private def amsterdamCapacityBenv : Benv :=
  fixtureAmsterdamBenv (amsterdamTxMaxGas + 100)

private def amsterdamCapacityOutput : BlockOutput :=
  {BlockOutput.init with blockGasUsed := 100, blockStateGasUsed := 50}

#guard (checkTransactionGasLimits amsterdamCapacityBenv
    amsterdamCapacityOutput amsterdamCapacityTx).toOption.isSome
#guard txvFails (fun | .gasAllowanceExceeded _ => true | _ => false) <|
  checkTransactionGasLimits amsterdamCapacityBenv
    {amsterdamCapacityOutput with blockGasUsed := 101} amsterdamCapacityTx
#guard txvFails (fun | .gasAllowanceExceeded _ => true | _ => false) <|
  checkTransactionGasLimits amsterdamCapacityBenv
    {amsterdamCapacityOutput with blockStateGasUsed := 51} amsterdamCapacityTx

#guard txvFails (fun | .type3BlobCountExceeded _ => true | _ => false) <|
  checkTransactionGasLimits fixtureTestBenv .init
    { fixtureTestTx with
      type := .three 1 1 10 0 [] 1 (List.replicate 10 0) }
#guard txvFails (fun | .type3ZeroBlobs _ => true | _ => false) <|
  checkTransactionBlobData fixtureTestBenv
    {fixtureTestTx with type := .three 1 1 10 0 [] 1 []} 10
#guard (checkTransactionBlobCount osakaRules.tx
  (List.replicate 5 (0 : B256))).toOption.isSome
#guard (checkTransactionBlobCount osakaRules.tx
  (List.replicate 6 (0 : B256))).toOption.isSome
#guard txvFails (fun | .type3BlobCountLimitExceeded _ => true | _ => false) <|
  checkTransactionBlobCount osakaRules.tx (List.replicate 7 (0 : B256))
#guard (checkTransactionBlobCount pragueRules.tx
  (List.replicate 7 (0 : B256))).toOption.isSome
#guard txvFails (fun | .type3InvalidBlobVersionedHash _ => true | _ => false) <|
  checkTransactionBlobData fixtureTestBenv
    {fixtureTestTx with type := .three 1 1 10 0 [] 1 [0]} 10
-- The blob-fee rejection renders its exact observed golden message.
#guard txvFails
    (fun e => e.render ==
      "InsufficientMaxFeePerBlobGasError : insufficient max fee per blob gas") <|
  checkTransactionBlobData fixtureTestBenv
    {fixtureTestTx with type := .three 1 1 10 0 [] 0 [(1 : B256) <<< 248]} 10

#guard txvFails (fun | .nonceMismatchTooLow _ => true | _ => false) <|
  checkTransactionSenderAccount (fixtureTestAccount 2 100) fixtureTestTx 0
#guard txvFails (fun | .nonceMismatchTooHigh _ => true | _ => false) <|
  checkTransactionSenderAccount (fixtureTestAccount 0 100)
    {fixtureTestTx with nonce := 1} 0
#guard txvFails (fun | .insufficientAccountFunds _ => true | _ => false) <|
  checkTransactionSenderAccount (fixtureTestAccount 0 0) fixtureTestTx 1
#guard txvFails (fun | .senderNotEoa _ => true | _ => false) <|
  checkTransactionSenderAccount
    (fixtureTestAccount 0 100 (ByteArray.mk #[0x01])) fixtureTestTx 0

#guard (processSystemTransactionTenv
    fixtureAmsterdamBenv).stat.stateGasReservoir
  = amsterdamStateGasRules.systemReservoir
#guard (processSystemTransactionMsg fixtureAmsterdamBenv
    (processSystemTransactionTenv fixtureAmsterdamBenv) 1 [] .empty).stateGasGrant
  = amsterdamStateGasRules.systemReservoir

--------------- GAS-LIMIT BOUNDARY CHECKS ----------------

-- Constructor-level matcher for the block-validation boundary guards.
private def blkFails {α : Type} (p : BlockValidationError → Bool) :
    Except BlockValidationError α → Bool
  | .error e => p e
  | .ok _ => false

-- The absolute bound, at its exact boundary. These are the real numbers from
-- `bcInvalidHeaderTest/GasLimitHigherThan2p63m1.json`, whose genesis gas limit
-- is `2 ^ 63 - 1` and whose block claims `2 ^ 63`. Note the parent-relative
-- window *accepts* that block -- one step up from a parent of `2 ^ 63 - 1` is
-- well within a delta of `(2 ^ 63 - 1) / 1024` -- so the absolute bound is the
-- only rule that rejects it, and it must be the one that reports.
#guard blkFails (fun | .gasLimitTooBig _ => true | _ => false)
  (checkGasLimit (2 ^ 63) (2 ^ 63 - 1))
#guard ¬ blkFails (fun | .gasLimitAdjustment _ => true | _ => false)
  (checkGasLimit (2 ^ 63) (2 ^ 63 - 1))
-- One below the bound, same parent: accepted. This is the maximum gas limit any
-- valid block in the corpus carries, so the bound may not be one lower.
#guard (checkGasLimit (2 ^ 63 - 1) (2 ^ 63 - 1)).toOption.isSome
-- Far above the bound, where the window would also reject: still too big.
#guard blkFails (fun | .gasLimitTooBig _ => true | _ => false)
  (checkGasLimit (2 ^ 64) 3141592)

-- The parent-relative window and the minimum, each at its boundary, all
-- reporting the adjustment rule rather than the absolute one.
#guard (checkGasLimit 3141592 3141592).toOption.isSome              -- unchanged
#guard blkFails (fun | .gasLimitAdjustment _ => true | _ => false)
  (checkGasLimit (3141592 + 3067) 3141592)
#guard (checkGasLimit (3141592 + 3066) 3141592).toOption.isSome     -- just inside
#guard blkFails (fun | .gasLimitAdjustment _ => true | _ => false)
  (checkGasLimit (3141592 - 3067) 3141592)
#guard (checkGasLimit (3141592 - 3066) 3141592).toOption.isSome     -- just inside
#guard blkFails (fun | .gasLimitAdjustment _ => true | _ => false)
  (checkGasLimit 4999 5000)                                         -- below minimum
#guard (checkGasLimit gasLimitMinimum 5000).toOption.isSome

#guard (checkBlockRlpSize osakaRules.block (8388608 - 1)).toOption.isSome
#guard (checkBlockRlpSize osakaRules.block 8388608).toOption.isSome
#guard blkFails (fun | .blockRlpSizeExceeded _ => true | _ => false) <|
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

-- Constructor-level guard matchers: the discriminant is now the typed reason,
-- so these boundary checks match constructors instead of reading rendered
-- text back through a prefix classifier.
private def decFails {α : Type} (p : DecodeError → Bool) :
    Except DecodeError α → Bool
  | .error e => p e
  | .ok _ => false

private def txFails {α : Type} (p : TransitionError → Bool) :
    Except TransitionError α → Bool
  | .error e => p e
  | .ok _ => false

private def txDecFails {α : Type} (p : DecodeError → Bool) :
    Except TransitionError α → Bool :=
  txFails fun e => match e with | .decode d => p d | _ => false

private def isFixedWidthD : DecodeError → Bool
  | .fixedWidth _ => true | _ => false
private def isOverflow64D : DecodeError → Bool
  | .fieldOverflow64 _ => true | _ => false
private def isOverflow256D : DecodeError → Bool
  | .fieldOverflow256 _ => true | _ => false
private def isStructureD : DecodeError → Bool
  | .rlpStructure _ => true | _ => false
private def isWithdrawalsNotReadD : DecodeError → Bool
  | .withdrawalsNotRead _ => true | _ => false
private def txPreForkFails {α : Type} (type : Nat) : Except TransitionError α → Bool :=
  txFails fun e => match e with | .transaction (.typePreFork t _) => t == type | _ => false

-- Both withdrawal index positions reject nine bytes at the field boundary;
-- neither can reach the truncating `Bytes.toUInt64` conversion unchecked.
#guard decFails isOverflow64D <|
  BLT.toExWithdrawal <|
    withdrawalDecoderVector nineByteScalar [] testRecipient []
#guard decFails isOverflow64D <|
  BLT.toExWithdrawal <|
    withdrawalDecoderVector [] nineByteScalar testRecipient []
#guard (BLT.toExWithdrawal <|
  withdrawalDecoderVector [] [] testRecipient []).toOption.isSome
#guard decFails isFixedWidthD <|
  BLT.toExWithdrawal <|
    withdrawalDecoderVector [] [] (List.replicate 21 0x11) []
-- The amount is a 64-bit Gwei scalar (EIP-4895): the exact eight-byte maximum
-- decodes, and nine bytes are rejected at the field boundary rather than
-- surfacing later as a state-root mismatch.
#guard (BLT.toExWithdrawal <|
  withdrawalDecoderVector [] [] testRecipient (List.replicate 8 0xFF)
  ).toOption.map (fun wd => wd.amount.toNat) = some (2 ^ 64 - 1)
#guard decFails isOverflow64D <|
  BLT.toExWithdrawal <|
    withdrawalDecoderVector [] [] testRecipient nineByteScalar

-- A canonical legacy transaction preserves its signing/re-encoding bytes.
private def canonicalLegacyVector : BLT :=
  legacyDecoderVector [0x01] [0x02] [0x52, 0x08] testRecipient [] [0x1b] [0x01] [0x02]

#guard
  (BLT.toExTx canonicalLegacyVector).toOption.map (fun tx => tx.toBLT.toBytes)
    == some canonicalLegacyVector.toBytes

-- Every legacy scalar is bounded before conversion or sender recovery.
#guard txDecFails isOverflow64D <|
  BLT.toExTx <|
    legacyDecoderVector nineByteScalar [] [] [] [] [] [] []
#guard txDecFails isOverflow256D <|
  BLT.toExTx <|
    legacyDecoderVector [] thirtyThreeByteScalar [] [] [] [] [] []
#guard txDecFails isOverflow256D <|
  BLT.toExTx <|
    legacyDecoderVector [] [] thirtyThreeByteScalar [] [] [] [] []
#guard txDecFails isOverflow256D <|
  BLT.toExTx <|
    legacyDecoderVector [] [] [] [] thirtyThreeByteScalar [] [] []
#guard txDecFails isOverflow256D <|
  BLT.toExTx <|
    legacyDecoderVector [] [] [] [] [] thirtyThreeByteScalar [] []
#guard txDecFails isOverflow256D <|
  BLT.toExTx <|
    legacyDecoderVector [] [] [] [] [] [] thirtyThreeByteScalar []
#guard txDecFails isOverflow256D <|
  BLT.toExTx <|
    legacyDecoderVector [] [] [] [] [] [] [] thirtyThreeByteScalar
#guard txDecFails isFixedWidthD <|
  BLT.toExTx <|
    legacyDecoderVector [] [] [] (List.replicate 21 0x11) [] [] [] []

-- The two block-list failures with dedicated meanings are separated before
-- header decoding; arbitrary non-list input remains a structure error.
#guard decFails isWithdrawalsNotReadD <|
  BLT.toExBlock (.list [.bytes [], .list [], .list []])
#guard decFails isStructureD <| BLT.toExBlock (.bytes [])

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
  (Bytes.toExTx v).toOption.map (fun tx => type :: tx.toBLT.toBytes) == some v

#guard reencodes 0x01 <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf testRecipient testStorageKey)
#guard reencodes 0x02 <| type2Vector [0x0a] testRecipient [0x02]
#guard reencodes 0x03 <| type3Vector [0x01] testRecipient testBlobHash
#guard reencodes 0x04 <| type4Vector testRecipient goodAuth

-- S5 admission through `decodeTx`: the envelope type must fit the rules'
-- `maxType`, and a too-new envelope fails with `typePreFork` naming its type
-- (the block is invalid, as EELS's own decode failure makes it; the decode
-- channel until goal U11a). Byzantium admits
-- only legacy; Berlin adds type 1; London type 2; Cancun type 3; Prague
-- (maxType 4) everything the decoder produces.
#guard txPreForkFails 1 <| decodeTx byzantiumRules (.inl
  (type1Vector [0x01] [0x01] testRecipient [0x01] (.list [])))
#guard (decodeTx berlinRules (.inl
  (type1Vector [0x01] [0x01] testRecipient [0x01] (.list [])))).toOption.isSome
#guard txPreForkFails 2 <| decodeTx berlinRules (.inl
  (type2Vector [0x0a] testRecipient [0x02]))
#guard (decodeTx londonRules (.inl
  (type2Vector [0x0a] testRecipient [0x02]))).toOption.isSome
#guard txPreForkFails 3 <| decodeTx londonRules (.inl
  (type3Vector [0x01] testRecipient testBlobHash))
#guard (decodeTx cancunRules (.inl
  (type3Vector [0x01] testRecipient testBlobHash))).toOption.isSome
#guard txPreForkFails 4 <| decodeTx cancunRules (.inl
  (type4Vector testRecipient goodAuth))
#guard (decodeTx pragueRules (.inl
  (type4Vector testRecipient goodAuth))).toOption.isSome

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
#guard (Bytes.toExTx (type2Vector [0x0a] [] [0x02])).toOption.isSome
-- ...but an empty type-3 receiver is the semantic contract-creation identity;
-- nonempty 19/21-byte receivers still fail as malformed RLP fields.
#guard txFails (fun e => match e with
    | .transaction (.type3ContractCreation _) => true | _ => false) <|
  Bytes.toExTx <| type3Vector [0x01] [] testBlobHash
#guard txDecFails isFixedWidthD <|
  Bytes.toExTx <| type3Vector [0x01] (List.replicate 19 0x11) testBlobHash
#guard txDecFails isFixedWidthD <| Bytes.toExTx <|
  type1Vector [0x01] [0x01] (List.replicate 21 0x11) [0x01] (.list [])
#guard txDecFails isFixedWidthD <|
  Bytes.toExTx <| type4Vector (List.replicate 19 0x11) goodAuth

-- Oversized scalars are overflows at the field boundary, not truncations.
#guard txDecFails isOverflow64D <| Bytes.toExTx <|
  type1Vector [0x01] nineByteScalar testRecipient [0x01] (.list [])
#guard txDecFails isOverflow64D <| Bytes.toExTx <|
  type1Vector nineByteScalar [0x01] testRecipient [0x01] (.list [])
#guard txDecFails isOverflow64D <|
  Bytes.toExTx <| type3Vector nineByteScalar testRecipient testBlobHash
#guard txDecFails isOverflow256D <|
  Bytes.toExTx <| type2Vector thirtyThreeByteScalar testRecipient [0x02]
-- The two fields the deleted `reverse.takeD 32` pattern used to truncate.
#guard txDecFails isOverflow256D <| Bytes.toExTx <|
  type1Vector [0x01] [0x01] testRecipient thirtyThreeByteScalar (.list [])
#guard txDecFails isOverflow256D <|
  Bytes.toExTx <| type2Vector [0x0a] testRecipient thirtyThreeByteScalar

-- Access lists: exact address and storage-key widths, and both list shapes.
#guard txDecFails isFixedWidthD <| Bytes.toExTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf (List.replicate 21 0x11) testStorageKey)
#guard txDecFails isFixedWidthD <| Bytes.toExTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf testRecipient (List.replicate 33 0x22))
#guard txDecFails isFixedWidthD <| Bytes.toExTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf testRecipient (List.replicate 31 0x22))
#guard txDecFails isStructureD <| Bytes.toExTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01] (.list [.bytes []])
#guard txDecFails isStructureD <| Bytes.toExTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01] (.bytes [])

-- Blob versioned hashes: exactly thirty-two bytes, both sides.
#guard txDecFails isFixedWidthD <| Bytes.toExTx <|
  type3Vector [0x01] testRecipient (0x01 :: List.replicate 32 0x33)
#guard txDecFails isFixedWidthD <|
  Bytes.toExTx <| type3Vector [0x01] testRecipient (List.replicate 31 0x33)

-- Authorizations: exact address width, a uint256 chainId, bounded nonce and
-- r/s, and the six-field list shape.
#guard txDecFails isFixedWidthD <| Bytes.toExTx <| type4Vector testRecipient <|
  authOf [0x01] (List.replicate 21 0x11) [0x01] fullWidthScalar fullWidthScalar
#guard (Bytes.toExTx <| type4Vector testRecipient <|
  authOf nineByteScalar testRecipient [0x01] fullWidthScalar fullWidthScalar).toOption.isSome
#guard txDecFails isOverflow64D <| Bytes.toExTx <| type4Vector testRecipient <|
  authOf [0x01] testRecipient nineByteScalar fullWidthScalar fullWidthScalar
#guard txDecFails isOverflow256D <| Bytes.toExTx <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] thirtyThreeByteScalar fullWidthScalar
#guard txDecFails isOverflow256D <| Bytes.toExTx <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] fullWidthScalar thirtyThreeByteScalar
#guard txDecFails isStructureD <| Bytes.toExTx <|
  type4Vector testRecipient (.list [.bytes [0x01], .bytes testRecipient])

-- A wrong list shape for a known type byte is a structure error; an unknown
-- type byte keeps its own failure; empty input is a structure error.
#guard txDecFails isStructureD <| Bytes.toExTx (0x01 :: BLT.toBytes (.bytes []))
#guard txDecFails isStructureD <| Bytes.toExTx (0x02 :: BLT.toBytes (.list []))
#guard txDecFails isStructureD <| Bytes.toExTx []
#guard ¬ txDecFails isStructureD (Bytes.toExTx [0x05])
#guard (Bytes.toExTx [0x05]).toOption.isNone
-- The unknown-type reason is the fail-closed internal one, never a decode or
-- rejection identity a fixture could score.
#guard txFails (fun e => match e with | .internal _ => true | _ => false)
  (Bytes.toExTx [0x05])

---------------- FORK ARCHITECTURE CHECKS ----------------

-- The Prague entry points are not merely *compatible* with the rules-explicit
-- core at Prague: they are that core, for every input. `rfl` is the point --
-- an equality on sample data would leave room for a wrapper that diverges
-- somewhere else, and downstream proofs state their results about these names.

example (ch : BlockChain) (block : Block) :
    stateTransition ch block = stateTransitionAt .prague ch block := rfl

example (ch : BlockChain) (block : Block) :
    stateTransitionAt .prague ch block = stateTransition ch block := rfl

example (chain : BlockChain) (blockRlp : Bytes) :
    addBlockToChain chain blockRlp
      = addBlockToChainAt .prague chain blockRlp := rfl

example (chain : BlockChain) (blockRlp : Bytes) :
    addBlockToChainAt .prague chain blockRlp = addBlockToChain chain blockRlp :=
  rfl

-- A block whose fork a build cannot run would be refused *before* anything is
-- decoded or executed, so an unimplemented fork could never be mistaken for a
-- rule the build actually applied. Eight forks are in that state here:
-- `Fork.rules` refuses them, and the guards below record that the support
-- channel answers through exactly those declared labels.

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
  baseFeePerGas := some 7
  withdrawalsRoot := some 0
  blobGasUsed := some 0
  excessBlobGas := some 0
  parentBeaconBlockRoot := some 0
  requestsHash := none
  blockAccessListHash := none
  slotNumber := none
}

private def guardBlockAt (timestamp : Nat) : Block :=
  {
    header := { guardTestHeader with timestamp := timestamp }
    txs := []
    ommers := []
    wds := []
  }

/-- The no-parent probe block carrying exactly the fork-dependent header fields
the rules define: a Prague-shaped header would fail field presence under
London/Paris rules before reaching the invariant the sweeps below pin. The
five fields are `checkHeaderShape`'s five, so a fork the shape rules out is
shaped out here too -- and a new fork-dependent field fails the next sweep
loudly rather than riding along as `some`. -/
private def guardBlockAtRules (rules : ForkRules) (timestamp : Nat) : Block :=
  {
    header := { guardTestHeader with
      timestamp := timestamp
      baseFeePerGas :=
        if rules.header.baseFee then guardTestHeader.baseFeePerGas else none
      withdrawalsRoot :=
        if rules.header.withdrawalsRoot then guardTestHeader.withdrawalsRoot
        else none
      blobGasUsed :=
        if rules.header.blobGas then guardTestHeader.blobGasUsed else none
      excessBlobGas :=
        if rules.header.blobGas then guardTestHeader.excessBlobGas else none
      parentBeaconBlockRoot :=
        if rules.header.parentBeaconBlockRoot then
          guardTestHeader.parentBeaconBlockRoot
        else none }
    txs := []
    ommers := []
    wds := []
  }

-- S8 0x44 (unit U5): `DIFFICULTY` source selection at environment
-- construction. Under proof of work the opcode reads the header's difficulty;
-- post-merge it reads `prevRandao`, so Prague is unaffected.
#guard (initBenvStat .byzantium guardEmptyChain
  { guardTestHeader with difficulty := 19 }).prevRandao = Nat.toB256 19
#guard (initBenvStat .prague guardEmptyChain
  { guardTestHeader with difficulty := 19 }).prevRandao = 0

-- EIP-7918 uses a strict price comparison. At the 16-wei equality boundary
-- the ordinary target subtraction still applies; one wei above it activates
-- the reserve branch. Prague has no reserve branch at the same inputs.
private def guardBlobParent (baseFee blobGasUsed : Nat) : Header :=
  { guardTestHeader with
    baseFeePerGas := some baseFee
    blobGasUsed := some blobGasUsed
    excessBlobGas := some 0 }

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

-- (U11a shaped this same probe block by fork identity as `guardShapedBlock`;
-- the merge keeps the rules-driven `guardBlockAtRules` above, which reuses
-- `guardTestHeader`'s reviewed values and is pinned to `guardHeader16`, and
-- drops the fork-driven duplicate.)

-- Every fork this build runs reaches execution; none is refused for want of
-- rules. Each probe block carries exactly the fork-dependent fields its rules
-- define (`guardBlockAtRules`), so field presence passes and each verdict is
-- the fail-closed no-parent invariant on the outer operational channel --
-- never a support failure.
#guard Fork.supported.all (fun f =>
  match f.rules with
  | .error _ => false
  | .ok rules =>
    match addBlockToChainAtE f guardEmptyChain
        (guardBlockAtRules rules 0).toBLT.toBytes with
    | .error (.support _) => false
    | _ => true)
#guard Fork.supported.all (fun f =>
  match f.rules with
  | .error _ => false
  | .ok rules =>
    match stateTransitionE f guardEmptyChain (guardBlockAtRules rules 0) with
    | .error (.internal _) => true
    | _ => false)

-- The complement, at the same entry point and on the same chain, is empty:
-- every declared fork now resolves to its existing rule record. Goal A's
-- guard here asserted that
-- Amsterdam was refused on the support channel before any block was examined;
-- it was rewritten to say that Amsterdam reaches execution like every other
-- supported fork when Amsterdam resolved. The later historical waves moved
-- that refusal boundary to the five pre-Berlin forks; this candidate resolves
-- their records too. This snapshot is not a conformance claim.
#guard (match addBlockToChainAtE .amsterdam guardEmptyChain
    (guardBlockAt 0).toBLT.toBytes with
  | .error (.support _) => false
  | _ => true)

-- A one-block chain whose parent is the only input to the child's expected
-- excess blob gas. Everything the header checks before that rule is satisfied
-- by construction, so a mismatch here is reported as the blob rule it is.
private def guardParentHeader : Header :=
  { guardTestHeader with
    number := 0
    baseFeePerGas := some 16
    blobGasUsed := some (21 * 131072) }

private def guardParentChain : BlockChain :=
  { blocks := [{ header := guardParentHeader, txs := [], ommers := [], wds := [] }]
    state := .empty
    chainId := 1 }

private def guardChildBlock (timestamp excessBlobGas : Nat) : Block :=
  { header := { guardTestHeader with
      number := guardParentHeader.number + 1
      timestamp := timestamp
      excessBlobGas := some excessBlobGas
      parentHash := (Header.toBLT guardParentHeader).toBytes.keccak }
    txs := []
    ommers := []
    wds := [] }

---------------- HEADER FIELD PRESENCE (EIP-7928, EIP-7843) ----------------

-- The two Amsterdam header fields are optional in *shape* and mandatory by
-- *rule*. What follows pins both halves: the wire shapes the codec accepts and
-- rejects, that a header without them is byte-identical to what it always was,
-- and that `validateHeader` enforces presence in both directions -- keyed on
-- rule data, so a caller-built record decides for itself and the rule is
-- testable before `amsterdamRules` exists.

private def guardBalHash : B256 := 0x1111111111111111111111111111111111111111111111111111111111111111
private def guardRequestsHash : B256 := 0x2222222222222222222222222222222222222222222222222222222222222222

/-- A header with all three optional fields, as an Amsterdam block carries it. -/
private def guardHeader23 : Header :=
  { guardTestHeader with
      requestsHash := some guardRequestsHash
      blockAccessListHash := some guardBalHash
      slotNumber := some 4096 }

/-- The same header as the supported chain carries it: the requests hash only. -/
private def guardHeader21 : Header :=
  { guardTestHeader with requestsHash := some guardRequestsHash }

private def bltFields : BLT → Nat
  | .list l => l.length
  | .bytes _ => 0

-- The encoder emits the current forks' widths: 20, 21 or 23 fields. (A
-- requests hash with a block-access-list hash and no slot number would emit
-- 22; the decoder refuses that width below.)
#guard bltFields (Header.toBLT guardTestHeader) = 20
#guard bltFields (Header.toBLT guardHeader21) = 21
#guard bltFields (Header.toBLT guardHeader23) = 23

-- Round trips at both live widths. `Except DecodeError Header` carries no
-- `BEq`, so the comparison goes through the decoded value.
private def roundTrips (h : Header) : Bool :=
  match (Header.toBLT h).toExHeader with
  | .ok h' => (Header.toBLT h').toBytes == (Header.toBLT h).toBytes
  | .error _ => false

#guard roundTrips guardHeader21
#guard roundTrips guardHeader23
#guard roundTrips guardTestHeader
-- The round trip preserves the two new fields specifically, not merely the
-- encoding: a decoder that dropped them would still re-encode to 21 fields.
#guard (match (Header.toBLT guardHeader23).toExHeader with
  | .ok h => h.blockAccessListHash == some guardBalHash
      && h.slotNumber == some 4096
      && h.requestsHash == some guardRequestsHash
  | .error _ => false)
#guard (match (Header.toBLT guardHeader21).toExHeader with
  | .ok h => h.blockAccessListHash.isNone && h.slotNumber.isNone
      && h.requestsHash == some guardRequestsHash
  | .error _ => false)

-- 22 fields is refused, and refused as a *structure* error naming the widths.
private def guardHeader22BLT : BLT :=
  match Header.toBLT guardHeader23 with
  | .list l => .list (l.take 22)
  | b => b

#guard bltFields guardHeader22BLT = 22
#guard guardHeader22BLT.toExHeader.toOption.isNone
#guard (match guardHeader22BLT.toExHeader with
  | .error e => e.render ==
      "RlpHeaderWidthError : header : expected 15, 16, 17, 20, 21 or 23 fields, but found 22"
  | .ok _ => false)

-- A 24-field header is refused for the same reason, so the rule is "these
-- three widths" and not "at most 23".
#guard (match (Header.toBLT guardHeader23) with
  | .list l => (BLT.list (l ++ [BLT.bytes []])).toExHeader.toOption.isNone
  | _ => false)

/-- A header carrying the five pre-Prague fork fields and neither Amsterdam
field encodes exactly as it did before any of those fields was optional.

`rfl` on an arbitrary header and arbitrary field values, so this is a fact about
*every* 20- or 21-field header rather than about a sample -- which is what makes
"no Prague, Osaka, BPO1 or BPO2 block's hash moved" a structural claim and not a
test result. The right-hand side is the encoder's body as it stood before the
Amsterdam fields existed. -/
example (h : Header) (baseFee : Nat) (withdrawalsRoot : B256)
    (blobGasUsed excessBlobGas : Nat) (parentBeaconBlockRoot : B256) :
    Header.toBLT { h with
        baseFeePerGas := some baseFee, withdrawalsRoot := some withdrawalsRoot
        blobGasUsed := some blobGasUsed, excessBlobGas := some excessBlobGas
        parentBeaconBlockRoot := some parentBeaconBlockRoot
        blockAccessListHash := none, slotNumber := none }
      = BLT.list ([
          BLT.bytes h.parentHash.toBytes,
          BLT.bytes h.ommersHash.toBytes,
          BLT.bytes h.coinbase.toBytes,
          BLT.bytes h.stateRoot.toBytes,
          BLT.bytes h.txsRoot.toBytes,
          BLT.bytes h.receiptRoot.toBytes,
          BLT.bytes h.bloom,
          BLT.bytes h.difficulty.toBytes,
          BLT.bytes h.number.toBytes,
          BLT.bytes h.gasLimit.toBytes,
          BLT.bytes h.gasUsed.toBytes,
          BLT.bytes h.timestamp.toBytes,
          BLT.bytes h.extraData,
          BLT.bytes h.prevRandao.toBytes,
          BLT.bytes h.nonce.toBytes,
          BLT.bytes baseFee.toBytes,
          BLT.bytes withdrawalsRoot.toBytes,
          BLT.bytes blobGasUsed.toBytes,
          BLT.bytes excessBlobGas.toBytes,
          BLT.bytes parentBeaconBlockRoot.toBytes
        ] ++
          match h.requestsHash with
          | none => []
          | some rh => [BLT.bytes rh.toBytes]) := rfl

/-- Therefore the identity of every such header is unchanged. -/
example (h : Header) (baseFee : Nat) (withdrawalsRoot : B256)
    (blobGasUsed excessBlobGas : Nat) (parentBeaconBlockRoot : B256) :
    Header.hash { h with
        baseFeePerGas := some baseFee, withdrawalsRoot := some withdrawalsRoot
        blobGasUsed := some blobGasUsed, excessBlobGas := some excessBlobGas
        parentBeaconBlockRoot := some parentBeaconBlockRoot
        blockAccessListHash := none, slotNumber := none }
      = (BLT.list ([
          BLT.bytes h.parentHash.toBytes, BLT.bytes h.ommersHash.toBytes,
          BLT.bytes h.coinbase.toBytes, BLT.bytes h.stateRoot.toBytes,
          BLT.bytes h.txsRoot.toBytes, BLT.bytes h.receiptRoot.toBytes,
          BLT.bytes h.bloom, BLT.bytes h.difficulty.toBytes,
          BLT.bytes h.number.toBytes, BLT.bytes h.gasLimit.toBytes,
          BLT.bytes h.gasUsed.toBytes, BLT.bytes h.timestamp.toBytes,
          BLT.bytes h.extraData, BLT.bytes h.prevRandao.toBytes,
          BLT.bytes h.nonce.toBytes, BLT.bytes baseFee.toBytes,
          BLT.bytes withdrawalsRoot.toBytes, BLT.bytes blobGasUsed.toBytes,
          BLT.bytes excessBlobGas.toBytes,
          BLT.bytes parentBeaconBlockRoot.toBytes
        ] ++
          match h.requestsHash with
          | none => []
          | some rh => [BLT.bytes rh.toBytes])).toBytes.keccak := rfl

-- The presence rule, both directions, on a real parent chain so that every
-- other header check has already passed and the presence rule is what decides.

private def guardChildBlockWith (header : Header) : Block :=
  { header := header, txs := [], ommers := [], wds := [] }

/-- The rules of the fork defining both header fields: since goal C that fork
exists, and `Fork.rules?` names it. (Goal A built this record by hand from
`bpo2Rules` because `amsterdamRules` did not exist yet; a bare header-flag
update of BPO2 is now refused by `ForkRules.Valid`, which ties the
`blockAccessListHash` flag to the presence of `bal` rules.) `ValidRules.check`
accepts it, so it is a usable record and not a strawman. -/
private def guardBothFieldsRules : ForkRules := amsterdamRules

#guard Fork.amsterdam.rules? = some guardBothFieldsRules

#guard (ValidRules.check guardBothFieldsRules).toOption.isSome

-- `baseFeePerGas := 14` is what this parent's gas usage makes expected, so
-- every other header rule passes and the presence rule is the only one left to
-- decide. A guard that failed on the base fee would prove nothing about
-- presence.
private def guardChild21 : Block :=
  guardChildBlockWith
    { (guardChildBlock 1 917504).header with
        baseFeePerGas := some 14
        requestsHash := some guardRequestsHash }

private def guardChild23 : Block :=
  guardChildBlockWith
    { (guardChildBlock 1 917504).header with
        baseFeePerGas := some 14
        requestsHash := some guardRequestsHash
        blockAccessListHash := some guardBalHash
        slotNumber := some 4096 }

private def presenceFails {α : Type} : Except TransitionError α → Bool
  | .error (.block (.headerFieldPresence _)) => true
  | _ => false

-- BPO2 defines neither field, so a 23-field header is rejected -- by the
-- presence rule, not by some earlier check that happens to fire first.
#guard presenceFails (validateHeader bpo2Rules guardParentChain guardChild23.header)
-- and its 21-field sibling passes every header check.
#guard (validateHeader bpo2Rules guardParentChain guardChild21.header).toOption.isSome

-- Under rules that define both fields the answers invert, on the very same
-- two headers. That is what makes this a rule and not a constant.
#guard presenceFails
  (validateHeader guardBothFieldsRules guardParentChain guardChild21.header)
#guard (validateHeader guardBothFieldsRules guardParentChain
  guardChild23.header).toOption.isSome

-- The reason names the field and the direction, so a failure is readable
-- without reading this file.
#guard (match validateHeader bpo2Rules guardParentChain guardChild23.header with
  | .error e => e.render.startsWith "HeaderFieldPresenceError : blockAccessListHash is present"
  | .ok _ => false)
#guard (match validateHeader guardBothFieldsRules guardParentChain
    guardChild21.header with
  | .error e => e.render.startsWith "HeaderFieldPresenceError : blockAccessListHash is absent"
  | .ok _ => false)

-- One field at a time: each flag is independent of the other.
#guard presenceFails (validateHeader
  { bpo2Rules with header := { bpo2Rules.header with slotNumber := true } }
  guardParentChain guardChild21.header)
#guard presenceFails (validateHeader
  { bpo2Rules with header := { bpo2Rules.header with blockAccessListHash := true } }
  guardParentChain guardChild21.header)

---------------- HEADER SHAPES BEFORE PRAGUE (design S3) ----------------

-- The five pre-Prague fork fields are optional in shape on the same terms as
-- the newer ones. Each historical width encodes, decodes and round-trips; the
-- in-between widths are refused; and `validateHeader` ties each field's
-- presence to `rules.header` in both directions. These guards call
-- `validateHeader` with a historical record directly: nothing here makes a
-- historical fork reachable through `Fork.rules?`.

/-- Byzantium through Berlin: no fork-dependent field. -/
private def guardHeader15 : Header :=
  { guardTestHeader with
      baseFeePerGas := none, withdrawalsRoot := none, blobGasUsed := none
      excessBlobGas := none, parentBeaconBlockRoot := none }

/-- London through Paris: the base fee. -/
private def guardHeader16 : Header :=
  { guardHeader15 with baseFeePerGas := some 7 }

-- The rules-shaped probe headers for London and Paris are this header: one
-- shaping, not two. Both start from `guardTestHeader` and touch the same five
-- fields, so pinning those five (and the base-fee value) is exact.
private def guardShapedIs16 (rules : ForkRules) : Bool :=
  (guardBlockAtRules rules 0).header.baseFeePerGas == some 7
    && (guardBlockAtRules rules 0).header.withdrawalsRoot.isNone
    && (guardBlockAtRules rules 0).header.blobGasUsed.isNone
    && (guardBlockAtRules rules 0).header.excessBlobGas.isNone
    && (guardBlockAtRules rules 0).header.parentBeaconBlockRoot.isNone

#guard guardShapedIs16 londonRules
#guard guardShapedIs16 parisRules

-- The fork-relative body decoder: three elements decode with no withdrawals
-- under London rules, stay `withdrawalsNotRead` under Shanghai rules, and a
-- four-element body decodes the same under both.
#guard (match BLT.toExBlockAt londonRules
    (.list [Header.toBLT guardHeader16, .list [], .list []]) with
  | .ok b => b.wds.isEmpty
  | .error _ => false)
#guard decFails isWithdrawalsNotReadD <| BLT.toExBlockAt shanghaiRules
  (.list [Header.toBLT guardHeader16, .list [], .list []])
#guard (match BLT.toExBlockAt londonRules
    (.list [Header.toBLT guardHeader16, .list [], .list [], .list []]) with
  | .ok b => b.wds.isEmpty
  | .error _ => false)
-- The fork-relative encoding is the canonical one from Shanghai on.
#guard ((guardBlockAt 0).toBLTAt pragueRules).toBytes
  == (guardBlockAt 0).toBLT.toBytes
-- A London probe block round-trips through the fork-relative decoder.
#guard (match rlpToBlockEAt londonRules
    ((guardBlockAtRules londonRules 0).toBLTAt londonRules).toBytes with
  | .ok ⟨b, _⟩ => b.wds.isEmpty
  | .error _ => false)

/-- Shanghai: the withdrawals root. -/
private def guardHeader17 : Header :=
  { guardHeader16 with withdrawalsRoot := some 0 }

#guard bltFields (Header.toBLT guardHeader15) = 15
#guard bltFields (Header.toBLT guardHeader16) = 16
#guard bltFields (Header.toBLT guardHeader17) = 17
#guard roundTrips guardHeader15
#guard roundTrips guardHeader16
#guard roundTrips guardHeader17
-- The round trip keeps presence, not merely the encoding.
#guard (match (Header.toBLT guardHeader16).toExHeader with
  | .ok h => h.baseFeePerGas == some 7 && h.withdrawalsRoot.isNone
      && h.blobGasUsed.isNone && h.parentBeaconBlockRoot.isNone
  | .error _ => false)
#guard (match (Header.toBLT guardHeader17).toExHeader with
  | .ok h => h.withdrawalsRoot == some 0 && h.excessBlobGas.isNone
  | .error _ => false)
#guard (match (Header.toBLT guardTestHeader).toExHeader with
  | .ok h => h.blobGasUsed == some 0 && h.excessBlobGas == some 0
      && h.parentBeaconBlockRoot == some 0 && h.requestsHash.isNone
  | .error _ => false)

-- The nesting makes an incoherent record encode as the longest coherent
-- prefix it carries: a withdrawals root without a base fee is not emitted, and
-- neither is half of Cancun's triple. No 18- or 19-field encoding exists.
#guard bltFields (Header.toBLT { guardHeader15 with withdrawalsRoot := some 0 }) = 15
#guard bltFields (Header.toBLT { guardHeader17 with blobGasUsed := some 0 }) = 17
#guard bltFields (Header.toBLT
  { guardHeader17 with blobGasUsed := some 0, excessBlobGas := some 0 }) = 17

-- 18 and 19 fields are refused on input, as header-width errors naming the
-- width (`INCORRECT_BLOCK_FORMAT`; structure errors until goal U11a).
private def guardHeaderPrefixBLT (n : Nat) : BLT :=
  match Header.toBLT guardTestHeader with
  | .list l => .list (l.take n)
  | b => b

#guard (match (guardHeaderPrefixBLT 18).toExHeader with
  | .error e => e.render ==
      "RlpHeaderWidthError : header : expected 15, 16, 17, 20, 21 or 23 fields, but found 18"
  | .ok _ => false)
#guard (match (guardHeaderPrefixBLT 19).toExHeader with
  | .error e => e.render ==
      "RlpHeaderWidthError : header : expected 15, 16, 17, 20, 21 or 23 fields, but found 19"
  | .ok _ => false)
-- and 14 is refused as a malformed list.
#guard (guardHeaderPrefixBLT 14).toExHeader.toOption.isNone

/-- A one-block chain ending at `parent`. -/
private def guardChainAt (parent : Header) : BlockChain :=
  { blocks := [{ header := parent, txs := [], ommers := [], wds := [] }]
    state := .empty
    chainId := 1 }

/-- `child` placed directly after `parent`: number, parent hash and a later
timestamp, so that only the rule under test can decide. -/
private def guardChildAfter (parent child : Header) : Header :=
  { child with
      number := parent.number + 1
      timestamp := parent.timestamp + 1
      parentHash := parent.hash }

/-- `guardChildAfter` under proof-of-work rules: the parent's difficulty is 0
and the child is one second later, so the expected difficulty is the floor
`minimumDifficulty` for every bomb delay (block 1 is far below each). -/
private def guardPowChildAfter (parent child : Header) : Header :=
  { guardChildAfter parent child with difficulty := minimumDifficulty }

private def guardParent15 : Header := { guardHeader15 with number := 0 }
private def guardParent16 : Header := { guardHeader16 with number := 0 }
private def guardParent17 : Header := { guardHeader17 with number := 0 }

private def baseFeeFails {α : Type} : Except TransitionError α → Bool
  | .error (.block (.baseFeePerGas _)) => true
  | _ => false

private def gasLimitFails {α : Type} : Except TransitionError α → Bool
  | .error (.block (.gasLimitAdjustment _)) => true
  | _ => false

-- Presence, both directions, for each pre-Prague field. A Berlin-shaped header
-- passes under Berlin's rules and fails under London's; a London-shaped one the
-- reverse; and so on up to Cancun. The reason names the field.
#guard (validateHeader berlinRules (guardChainAt guardParent15)
  (guardPowChildAfter guardParent15 guardHeader15)).toOption.isSome
#guard (match validateHeader londonRules (guardChainAt guardParent15)
    (guardChildAfter guardParent15 guardHeader15) with
  | .error e => e.render.startsWith "HeaderFieldPresenceError : baseFeePerGas is absent"
  | .ok _ => false)
#guard (match validateHeader berlinRules (guardChainAt guardParent15)
    (guardChildAfter guardParent15 { guardHeader16 with baseFeePerGas := some initialBaseFee }) with
  | .error e => e.render.startsWith "HeaderFieldPresenceError : baseFeePerGas is present"
  | .ok _ => false)
#guard (match validateHeader parisRules (guardChainAt guardParent16)
    (guardChildAfter guardParent16 guardHeader17) with
  | .error e => e.render.startsWith "HeaderFieldPresenceError : withdrawalsRoot is present"
  | .ok _ => false)
#guard (match validateHeader shanghaiRules (guardChainAt guardParent16)
    (guardChildAfter guardParent16 guardHeader16) with
  | .error e => e.render.startsWith "HeaderFieldPresenceError : withdrawalsRoot is absent"
  | .ok _ => false)
#guard (match validateHeader shanghaiRules (guardChainAt guardParent17)
    (guardChildAfter guardParent17 guardTestHeader) with
  | .error e => e.render.startsWith "HeaderFieldPresenceError : blobGasUsed is present"
  | .ok _ => false)
#guard (match validateHeader cancunRules (guardChainAt guardParent17)
    (guardChildAfter guardParent17 guardHeader17) with
  | .error e => e.render.startsWith "HeaderFieldPresenceError : blobGasUsed is absent"
  | .ok _ => false)
-- The beacon root separately from the blob pair: a record carrying the pair
-- but not the root.
#guard (match validateHeader cancunRules (guardChainAt guardParent17)
    (guardChildAfter guardParent17
      { guardHeader17 with blobGasUsed := some 0, excessBlobGas := some 0 }) with
  | .error e => e.render.startsWith "HeaderFieldPresenceError : parentBeaconBlockRoot is absent"
  | .ok _ => false)
-- A Prague-shaped header under Prague's rules is not touched by the new checks.
#guard (validateHeader bpo2Rules guardParentChain guardChild21.header).toOption.isSome

-- A parent without a base fee selects `INITIAL_BASE_FEE`; header validation
-- separately checks the doubled parent gas limit. The quantified success
-- theorem below covers that gas check; retain the existing fee-path checks.
private def guardLondonFirst (baseFee gasLimit : Nat) : Header :=
  guardPowChildAfter guardParent15
    { guardHeader16 with baseFeePerGas := some baseFee, gasLimit := gasLimit }

#guard (validateHeader londonRules (guardChainAt guardParent15)
  (guardLondonFirst initialBaseFee 60000000)).toOption.isSome
#guard baseFeeFails (validateHeader londonRules (guardChainAt guardParent15)
  (guardLondonFirst 7 60000000))
-- Every later London block runs the update rule and its gas-limit check.
#guard gasLimitFails (validateHeader londonRules (guardChainAt guardParent16)
  (guardChildAfter guardParent16 { guardHeader16 with gasLimit := 60000000 }))
-- Before London the gas-limit check runs although no base fee is computed.
#guard gasLimitFails (validateHeader berlinRules (guardChainAt guardParent15)
  (guardChildAfter guardParent15 { guardHeader15 with gasLimit := 60000000 }))

-- Cancun's first block (EELS `cancun/vm/gas.py`, keyed on the parent header's
-- class): a parent without the blob fields counts them as zero.
#guard calculateExcessBlobGas cancunRules.blob guardParent17 = 0
#guard (validateHeader cancunRules (guardChainAt guardParent17)
  (guardChildAfter guardParent17 guardTestHeader)).toOption.isSome
#guard (match validateHeader cancunRules (guardChainAt guardParent17)
    (guardChildAfter guardParent17 { guardTestHeader with excessBlobGas := some 1 }) with
  | .error (.block (.excessBlobGas _)) => true
  | _ => false)

-- `initBenvStat` reads an absent field as zero.
#guard (initBenvStat .prague (guardChainAt guardParent15) guardHeader15).baseFeePerGas = 0
#guard (initBenvStat .prague (guardChainAt guardParent15) guardHeader15).excessBlobGas = 0
#guard (initBenvStat .prague (guardChainAt guardParent15) guardHeader15).parentBeaconBlockRoot = 0

------------------- PRE-MERGE CONSENSUS (U7) --------------------

-- `calculateBlockDifficulty` against EELS `calculate_block_difficulty`
-- (`byzantium/fork.py`, `gray_glacier/fork.py`; values computed by those
-- functions at the pinned t8n target). Byzantium at its activation block with
-- a parent carrying ommers (the `2 -` arm), a slow block (negative
-- adjustment) and a very slow one (the `-99` floor), each with the bomb's
-- `2 ^ 11` term at delay 3M; the minimum floor; Gray Glacier at its own
-- activation block with delay 11.4M (no bomb term), and a small parent.
#guard calculateBlockDifficulty 3000000 4370000 1500000013 1500000000
  3000000000000000 true = 3001464843752048
#guard calculateBlockDifficulty 3000000 4370000 1500000100 1500000000
  3000000000000000 false = 2985351562502048
#guard calculateBlockDifficulty 3000000 4370000 1500002000 1500000000
  3000000000000000 false = 2854980468752048
#guard calculateBlockDifficulty 3000000 1 1 0 0 false = 131072
#guard calculateBlockDifficulty 11400000 15050000 1655000005 1655000000
  12000000000000000 false = 12005876554869184
#guard calculateBlockDifficulty 11400000 1000 1010 1000 200000 true = 200097
-- The rule data feeds it: Byzantium's delay is the 3M above.
private def guardByzantiumActivationParent : Header :=
  { guardHeader15 with
      timestamp := 1500000000
      difficulty := 3000000000000000
      ommersHash := 0 }

#guard byzantiumRules.pow.map (fun pow => expectedDifficulty pow
    { guardHeader15 with number := 4370000, timestamp := 1500000013 }
    guardByzantiumActivationParent)
  = some 3001464843752048

-- A Byzantium-shaped chain: genesis `g`, its child `p`, and a block `b` on
-- `p` that names `o` -- a second child of `g`, mined by another coinbase --
-- as its one ommer.
private def guardPowCoinbase : Adr := 0xc0
private def guardOmmerCoinbase : Adr := 0x0e

private def guardPowAt (parent : Header) (timestamp : Nat) (coinbase : Adr) : Header :=
  let child : Header :=
    { guardHeader15 with
        number := parent.number + 1, timestamp := timestamp,
        parentHash := parent.hash, coinbase := coinbase }
  { child with difficulty := match byzantiumRules.pow with
      | some pow => expectedDifficulty pow child parent
      | none => 0 }

private def guardPowGenesis : Header :=
  { guardHeader15 with number := 0, difficulty := 131072 }
private def guardPowParent : Header := guardPowAt guardPowGenesis 5 guardPowCoinbase
private def guardPowOmmer : Header := guardPowAt guardPowGenesis 6 guardOmmerCoinbase
private def guardPowBlockWith (ommers : List Header) : Header :=
  { guardPowAt guardPowParent 20 guardPowCoinbase with
      ommersHash := ommersListHash ommers }
private def guardPowChain : BlockChain :=
  { blocks := [guardPowGenesis, guardPowParent].map
      (fun h => { header := h, txs := [], ommers := [], wds := [] })
    state := .empty
    chainId := 1 }

private def ommersRejected : Except TransitionError Unit → Bool
  | .error (.block (.invalidOmmers _)) => true
  | _ => false

#guard ommersListHash [] = emptyOmmerHash
-- The difficulty the chain needs: a block within 9 seconds of its parent
-- raises the parent's by 1/2048.
#guard guardPowParent.difficulty = 131072 + 131072 / 2048
#guard (validateHeader byzantiumRules guardPowChain (guardPowBlockWith [guardPowOmmer])).toOption.isSome
#guard (match validateHeader byzantiumRules guardPowChain
    { guardPowBlockWith [guardPowOmmer] with difficulty := 131072 } with
  | .error (.block (.invalidDifficulty _)) => true
  | _ => false)
-- Proof of work accepts what proof of stake refuses: a nonzero nonce (the seal
-- is not checked) and a nonempty ommers hash.
#guard (validateHeader byzantiumRules guardPowChain
    { guardPowBlockWith [guardPowOmmer] with nonce := 42, prevRandao := 7 }).toOption.isSome
-- The ommer is accepted; each rule refuses its own violation.
#guard (checkBlockOmmers byzantiumRules guardPowChain
    (guardPowBlockWith [guardPowOmmer]) [guardPowOmmer]).toOption.isSome
#guard (checkBlockOmmers byzantiumRules guardPowChain
    (guardPowBlockWith []) []).toOption.isSome
#guard ommersRejected (validateOmmers byzantiumRules guardPowChain
    (guardPowBlockWith []) [guardPowOmmer])                       -- list hash
#guard ommersRejected (validateOmmers byzantiumRules guardPowChain
    (guardPowBlockWith [guardPowOmmer, guardPowOmmer])
    [guardPowOmmer, guardPowOmmer])                               -- duplicate
#guard ommersRejected (validateOmmers byzantiumRules guardPowChain
    (guardPowBlockWith [guardPowParent]) [guardPowParent])         -- canonical
#guard ommersRejected (validateOmmers byzantiumRules guardPowChain
    (guardPowBlockWith [{ guardPowOmmer with difficulty := 1 }])
    [{ guardPowOmmer with difficulty := 1 }])                      -- its header
#guard ommersRejected (validateOmmers byzantiumRules guardPowChain
    (guardPowBlockWith [guardPowGenesis]) [guardPowGenesis])       -- number 0
-- Three valid-looking ommers are too many (the count is checked after each
-- ommer's own header, as in EELS).
private def guardPowOmmerN (ts : Nat) : Header :=
  guardPowAt guardPowGenesis ts guardOmmerCoinbase
#guard ommersRejected (validateOmmers byzantiumRules guardPowChain
    (guardPowBlockWith [guardPowOmmerN 6, guardPowOmmerN 7, guardPowOmmerN 8])
    [guardPowOmmerN 6, guardPowOmmerN 7, guardPowOmmerN 8])
#guard (validateOmmers byzantiumRules guardPowChain
    (guardPowBlockWith [guardPowOmmerN 6, guardPowOmmerN 7])
    [guardPowOmmerN 6, guardPowOmmerN 7]).toOption.isSome
-- Depth: on a line of eight blocks (numbers 0 to 7), a block numbered 8 may
-- name a second child of block 1 (age 6, its parent among the seven most
-- recent blocks), but not a second child of genesis (age 7).
private def guardPowLine : Nat → List Header
  | 0 => [guardPowGenesis]
  | n + 1 =>
    let l := guardPowLine n
    l ++ [guardPowAt (l.getLastD guardPowGenesis) (5 * (n + 1)) guardPowCoinbase]

private def guardPowLineChain : BlockChain :=
  { guardPowChain with
      blocks := (guardPowLine 7).map
        (fun h => { header := h, txs := [], ommers := [], wds := [] }) }

private def guardPowLineBlockWith (ommers : List Header) : Header :=
  { guardPowAt ((guardPowLine 7).getLastD guardPowGenesis) 40 guardPowCoinbase with
      ommersHash := ommersListHash ommers }

private def guardPowLineOmmer (parentNumber : Nat) : Header :=
  guardPowAt ((guardPowLine 7).getD parentNumber guardPowGenesis)
    (5 * parentNumber + 1) guardOmmerCoinbase

#guard (validateOmmers byzantiumRules guardPowLineChain
    (guardPowLineBlockWith [guardPowLineOmmer 1]) [guardPowLineOmmer 1]).toOption.isSome
#guard ommersRejected (validateOmmers byzantiumRules guardPowLineChain
    (guardPowLineBlockWith [guardPowLineOmmer 0]) [guardPowLineOmmer 0])
-- After Paris the old rule is untouched: any ommer is refused as over Paris.
#guard (match checkBlockOmmers pragueRules guardPowChain
    (guardPowBlockWith [guardPowOmmer]) [guardPowOmmer] with
  | .error (.block (.ommersOverParis _)) => true
  | _ => false)

-- The rewards (EELS `pay_rewards`, Byzantium's 3 ETH): the miner gets
-- `3 + 3/32` ETH for one ommer, and the age-1 ommer's miner `7/8` of 3 ETH.
#guard (payRewards { blockReward := 3 * 10 ^ 18, bombDelay := 3000000 } 2
    guardPowCoinbase [guardPowOmmer] .empty).bal guardPowCoinbase
  = (3093750000000000000 : Nat).toB256
#guard (payRewards { blockReward := 3 * 10 ^ 18, bombDelay := 3000000 } 2
    guardPowCoinbase [guardPowOmmer] .empty).bal guardOmmerCoinbase
  = (2625000000000000000 : Nat).toB256
-- Age 2 pays 6/8; no ommer pays the miner the bare block reward.
#guard (payRewards { blockReward := 2 * 10 ^ 18, bombDelay := 5000000 } 3
    guardPowCoinbase [guardPowOmmer] .empty).bal guardOmmerCoinbase
  = (1500000000000000000 : Nat).toB256
#guard (payRewards { blockReward := 2 * 10 ^ 18, bombDelay := 5000000 } 3
    guardPowCoinbase [] .empty).bal guardPowCoinbase
  = (2 * 10 ^ 18 : Nat).toB256

-- The whole Byzantium body on that block: the two system calls, the
-- withdrawals and the request pass are gated off, so the state the body
-- leaves is exactly the input state plus the rewards -- two accounts.
private def guardPowBenv : Benv :=
  initBenv .byzantium guardPowChain (guardPowBlockWith [guardPowOmmer])

#guard (match applyBody guardPowBenv [] [guardPowOmmer] [] with
  | .ok ⟨st, bout⟩ =>
      st.bal guardPowCoinbase == (3093750000000000000 : Nat).toB256 &&
      st.bal guardOmmerCoinbase == (2625000000000000000 : Nat).toB256 &&
      st.toList.length == 2 && bout.requests.isEmpty
  | .error _ => false)
-- The two system-call gates, observed: with a storage-writing contract at
-- both system addresses and no block hashes, Byzantium's body leaves both
-- contracts' storage empty and never asks for a parent hash, while Cancun's
-- runs the beacon-roots call and still never asks for one (its history call
-- is gated off too).
private def guardSysCode : ByteArray := ⟨#[0x60, 0x01, 0x60, 0x00, 0x55, 0x00]⟩

private def guardSysBenv (benv : Benv) : Benv :=
  { benv with
      state := (State.setCode .empty beaconRootsAddress guardSysCode).setCode
        historyStorageAddress guardSysCode
      stat := { benv.stat with blockHashes := [] } }

#guard (match applyBody (guardSysBenv guardPowBenv) [] [guardPowOmmer] [] with
  | .ok ⟨st, _⟩ => (st.get beaconRootsAddress).stor.isEmpty &&
      (st.get historyStorageAddress).stor.isEmpty
  | .error _ => false)
#guard (match applyBody (guardSysBenv (initBenv .cancun guardPowChain guardTestHeader))
    [] [] [] with
  | .ok ⟨st, _⟩ => !(st.get beaconRootsAddress).stor.isEmpty &&
      (st.get historyStorageAddress).stor.isEmpty
  | .error _ => false)

-- Under Prague's rules the same body runs every step: the request pass calls
-- the request contracts, which this chain has not deployed.
#guard (match applyBody (initBenv .prague guardPowChain (guardPowBlockWith []))
    [] [guardPowOmmer] [] with
  | .error (.block (.systemContractEmpty _)) => true
  | _ => false)

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

-- Constructor-level matchers for the transition and import boundary guards.
private def transitionBlobVerdict {α : Type} : Except TransitionError α → Bool
  | .error (.block (.excessBlobGas _)) => true
  | _ => false

/-- The verdict of a typed import, with the accepted chain erased: exactly the
part of the outcome the boundary guards compare, on a carrier that has
decidable equality. -/
private def verdictOf : Except ImportFailure (ImportOutcome BlockChain) →
    Option (ImportFailure ⊕ BlockRejection)
  | .error f => some (.inl f)
  | .ok (.inr r) => some (.inr r)
  | .ok (.inl _) => none

/-- Guard-only golden probe: the rendered text a legacy adapter reports on its
error channel. Used by the `#guard` renderer goldens below and by nothing
else; classification never reads it. -/
private def errorText? {α : Type} : Except String α → Option String
  | .error e => some e
  | .ok _ => none

/-- The rule set an explicit fork or a schedule selects, applied through the
typed transition core: what the fork-selection boundary guards compare. -/
private def transitionAtE (f : Fork) (ch : BlockChain) (block : Block) :
    Except TransitionError BlockChain :=
  stateTransitionE f ch block

private def transitionUsingE (cfg : ChainConfig) (ch : BlockChain)
    (block : Block) : Except TransitionError BlockChain :=
  match cfg.forkAt block.header.number block.header.timestamp with
  | .error _ => .error (.internal (.assertion .none))
  | .ok f => stateTransitionE f ch block

-- The explicit API applies the fork it is given, and only that fork accepts
-- its own expected value.
#guard ¬ transitionBlobVerdict
  (transitionAtE .osaka guardParentChain (guardChildBlock 1 1966080))
#guard transitionBlobVerdict <|
  transitionAtE .bpo1 guardParentChain (guardChildBlock 1 1966080)
#guard ¬ transitionBlobVerdict
  (transitionAtE .bpo1 guardParentChain (guardChildBlock 1 1441792))
#guard ¬ transitionBlobVerdict
  (transitionAtE .bpo2 guardParentChain (guardChildBlock 1 917504))

-- A configured chain selects rules from the block's own timestamp. Between
-- these blocks nothing differs but the timestamp, and it alone decides which
-- schedule the header is judged against: the block immediately before an
-- activation still runs the old rules, and the activation block itself already
-- runs the new ones.

private def guardChainSchedule : ChainConfig :=
  ChainConfig.mk 1 [.atTime .prague 0, .atTime .osaka 100, .atTime .bpo1 200, .atTime .bpo2 300]

#guard ¬ transitionBlobVerdict
  (transitionUsingE guardChainSchedule guardParentChain
    (guardChildBlock 199 1966080))
#guard transitionBlobVerdict <|
  transitionUsingE guardChainSchedule guardParentChain
    (guardChildBlock 200 1966080)
#guard ¬ transitionBlobVerdict
  (transitionUsingE guardChainSchedule guardParentChain
    (guardChildBlock 200 1441792))
#guard transitionBlobVerdict <|
  transitionUsingE guardChainSchedule guardParentChain
    (guardChildBlock 299 917504)
#guard ¬ transitionBlobVerdict
  (transitionUsingE guardChainSchedule guardParentChain
    (guardChildBlock 300 917504))

-- Across a sequence of blocks crossing all three activations, one fixed
-- expectation is correct exactly on the segment whose schedule produced it.
-- Prague and Osaka share a target, so the first BPO boundary is the first
-- place the sequence changes.
#guard [0, 99, 100, 199, 200, 299, 300, 400].map (fun timestamp =>
    !transitionBlobVerdict
      (transitionUsingE guardChainSchedule guardParentChain
        (guardChildBlock timestamp 1441792)))
  = [false, false, false, false, true, true, false, false]

-- Selecting rules from the schedule is the same thing as naming the fork the
-- schedule selects -- including the expected value quoted in the diagnostic,
-- compared here through the legacy adapters' rendered goldens.
#guard errorText? (stateTransitionUsing guardChainSchedule guardParentChain
    (guardChildBlock 250 0))
  = errorText? (stateTransitionAt .bpo1 guardParentChain (guardChildBlock 250 0))
#guard errorText? (stateTransitionUsing guardChainSchedule guardParentChain
    (guardChildBlock 350 0))
  = errorText? (stateTransitionAt .bpo2 guardParentChain (guardChildBlock 350 0))
#guard errorText? (stateTransitionUsing guardChainSchedule guardParentChain
    (guardChildBlock 250 0))
  ≠ errorText? (stateTransitionAt .osaka guardParentChain (guardChildBlock 250 0))

-- Block import agrees with the state transition on which fork a timestamp
-- selects, and a transition label is just another way to write the schedule.
-- A rejected block reports on the typed rejection channel, and the verdicts
-- are compared as constructors.
private def guardOsakaToBpo1Config : ChainConfig :=
  (⟨.osaka, .bpo1, .byTimestamp 15000⟩ : ForkTransition).chainConfig 1

private def guardChildRlp (timestamp excessBlobGas : Nat) : Bytes :=
  (guardChildBlock timestamp excessBlobGas).toBLT.toBytes

#guard (match verdictOf (addBlockToChainUsingE guardOsakaToBpo1Config
    guardParentChain (guardChildRlp 15000 0)) with
  | some (.inr (.block (.excessBlobGas _))) => true
  | _ => false)
#guard verdictOf (addBlockToChainUsingE guardOsakaToBpo1Config guardParentChain
    (guardChildRlp 15000 0))
  = verdictOf (addBlockToChainAtE .bpo1 guardParentChain
    (guardChildRlp 15000 0))
#guard verdictOf (addBlockToChainUsingE guardOsakaToBpo1Config guardParentChain
    (guardChildRlp 14999 0))
  = verdictOf (addBlockToChainAtE .osaka guardParentChain
    (guardChildRlp 14999 0))
#guard verdictOf (addBlockToChainUsingE guardOsakaToBpo1Config guardParentChain
    (guardChildRlp 15000 0))
  ≠ verdictOf (addBlockToChainUsingE guardOsakaToBpo1Config guardParentChain
    (guardChildRlp 14999 0))

-- A Prague-only configuration is the Prague wrapper, at every timestamp.
#guard errorText? (stateTransitionUsing (ChainConfig.pragueOnly 1) guardEmptyChain
    (guardBlockAt 0))
  = errorText? (stateTransition guardEmptyChain (guardBlockAt 0))
#guard errorText? (stateTransitionUsing (ChainConfig.pragueOnly 1) guardEmptyChain
    (guardBlockAt 999999999))
  = errorText? (stateTransition guardEmptyChain (guardBlockAt 999999999))

-- An unusable schedule fails before it selects anything, with the exact
-- context golden.
#guard errorText?
    (stateTransitionUsing (ChainConfig.mk 1 []) guardEmptyChain (guardBlockAt 0))
  = some (ChainContextError.render .emptySchedule)

-- P0.1 negative guards: config ID 7 against a chain ID 1 snapshot, matching
-- the acceptance evidence's own example. The mismatch is a context failure on
-- the outer channel -- never `.inr`, so never scored as an invalid block --
-- and it fires before decoding even touches the candidate bytes: `[0xFF]` is
-- not valid block RLP at all, yet `addBlockToChainUsing` still reports the
-- mismatch rather than a decode error, because the check runs first.
private def guardMismatchConfig : ChainConfig := ChainConfig.mk 7 [.atTime .prague 0]

#guard errorText?
    (stateTransitionUsing guardMismatchConfig guardEmptyChain (guardBlockAt 0))
  = some (ChainContextError.render (.chainIdMismatch 7 1))
#guard verdictOf (addBlockToChainUsingE guardMismatchConfig guardParentChain [0xFF])
  = some (.inl (.context (.chainIdMismatch 7 1)))
-- The same malformed bytes, past a matching-ID configuration, are rejected on
-- the ordinary decode channel instead -- confirming the mismatch guard above
-- is what changed the verdict, not something incidental to the garbage input.
#guard verdictOf (addBlockToChainUsingE guardOsakaToBpo1Config guardParentChain [0xFF])
  = some (.inr (.decode
      (DecodeError.structure "block RLP" "cannot decode the outer RLP item")))

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
  (Header.WireWellFormed { guardTestHeader with blobGasUsed := some (2 ^ 64 - 1) })
#guard ¬ decide
  (Header.WireWellFormed { guardTestHeader with blobGasUsed := some (2 ^ 64) })
#guard decide
  (Header.WireWellFormed { guardTestHeader with excessBlobGas := some (2 ^ 64 - 1) })
#guard ¬ decide
  (Header.WireWellFormed { guardTestHeader with excessBlobGas := some (2 ^ 64) })

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
#guard (BLT.toExTx canonicalLegacyVector).toOption.map
  (fun tx => decide tx.WireWellFormed) = some true
#guard (BLT.toExTx canonicalLegacyVector).toOption.map
  (fun tx => decide (Tx.WireWellFormed { tx with r := 0x00 :: tx.r })) = some false
#guard (BLT.toExTx canonicalLegacyVector).toOption.map
  (fun tx => decide (Tx.WireWellFormed { tx with s := List.replicate 33 0x01 }))
    = some false
#guard (BLT.toExTx canonicalLegacyVector).toOption.map
  (fun tx => decide (Tx.WireWellFormed { tx with value := 2 ^ 256 })) = some false

-- P0.3's headline negative case. A decoded legacy transaction is a legitimate
-- decoded block-body slot; a *typed* transaction is not, because a typed
-- transaction's canonical block encoding is its envelope byte followed by its
-- payload, never the legacy list. This is what forecloses a direct trusted
-- `.inr Tx` on the checked path.
#guard (BLT.toExTx canonicalLegacyVector).toOption.map
  (fun tx => decide (TxEntry.WireWellFormed (.inr tx))) = some true
#guard (Bytes.toExTx
    (type1Vector [0x01] [0x01] testRecipient [0x01] (.list []))).toOption.map
  (fun tx => decide (TxEntry.WireWellFormed (.inr tx))) = some false
#guard (Bytes.toExTx (type2Vector [0x0a] testRecipient [0x02])).toOption.map
  (fun tx => decide (TxEntry.WireWellFormed (.inr tx))) = some false

--------------- CHECKED-CONSTRUCTOR AND ENVELOPE CHECKS ---------------

-- A checked constructor admits what the decoder would produce and refuses
-- everything else outright. It never trims, normalises, or defaults a
-- hand-built value into shape.
#guard (CheckedHeader.ofHeader? guardTestHeader).isSome
#guard (CheckedHeader.ofHeader? { guardTestHeader with bloom := [] }).isNone
#guard (CheckedHeader.ofHeader? { guardTestHeader with gasUsed := 2 ^ 256 }).isNone
#guard (CheckedHeader.ofHeader?
  { guardTestHeader with excessBlobGas := some (2 ^ 64) }).isNone
#guard (CheckedWithdrawal.ofWithdrawal?
  (wireGuardWithdrawal (2 ^ 64 - 1 : Nat).toB256)).isSome
#guard (CheckedWithdrawal.ofWithdrawal?
  (wireGuardWithdrawal (2 ^ 64 : Nat).toB256)).isNone

-- A decoded legacy transaction is a legitimate block-body slot and has no
-- typed envelope; a typed transaction is the exact mirror image. This is the
-- pair of facts that leaves no direct trusted `.inr Tx` anywhere on the
-- checked path.
#guard (BLT.toExTx canonicalLegacyVector).toOption.map
  (fun tx => (TxEnvelope.ofEntry? (.inr tx)).isSome) = some true
#guard (BLT.toExTx canonicalLegacyVector).toOption.map
  (fun tx => (Tx.toTypedEnvelope? tx).isSome) = some false
#guard (Bytes.toExTx (type2Vector [0x0a] testRecipient [0x02])).toOption.map
  (fun tx => (TxEnvelope.ofEntry? (.inr tx)).isSome) = some false
#guard (Bytes.toExTx (type2Vector [0x0a] testRecipient [0x02])).toOption.map
  (fun tx => (Tx.toTypedEnvelope? tx).isSome) = some true

-- ...and the typed route reproduces the exact envelope bytes it came from, so
-- commitment bytes are unchanged for a transaction that makes the round trip
-- through the checked constructor rather than the decoder.
private def typedEnvelopeBytes? (bs : Bytes) : Option Bytes :=
  (Bytes.toExTx bs).toOption.bind fun tx =>
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
#guard (Bytes.toExTx (type2Vector [0x0a] testRecipient [0x02])).toOption.map
  (fun tx => (CheckedBlock.ofBlock? { guardBlockAt 0 with txs := [.inr tx] }).isSome)
    = some false
#guard (BLT.toExTx canonicalLegacyVector).toOption.map
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

--------------- AMSTERDAM FAILURE-ORDER REGRESSIONS ---------------

-- These guards pin failure precedence and warming at the metering switch.
-- They deliberately exercise `Rinst.runCore`, all four `Xinst.step` CALL
-- variants, and the private top-level dispatch boundary rather than a pricing
-- helper in isolation.
private def orderingGuardMessage (fork : Fork) (gas : Nat) : Msg :=
  let state := State.setBal .empty (0x1000 : Adr) 100
  { (default : Msg) with
    benv := { (default : Benv) with
      state := state
      stat := { (default : BenvStat) with fork := fork, origState := state } }
    caller := 0x1000
    target := some 0x1000
    currentTarget := 0x1000
    gas := gas
    depth := 8 }

private def orderingGuardSummary (r : Execution) :
    String × Nat × List Nat × Bool × Bool :=
  let (status, d) := match r with
    | .ok d => ("ok", d)
    | .error (e, d) => (e.render, d)
  (status, d.gasLeft, d.stack.map B256.toNat,
    d.accessedAddresses.contains (0x2000 : Adr),
    d.accessedAddresses.contains (0x3000 : Adr))

private def orderingGuardTstore
    (fork : Fork) (gas : Nat) (stack : List B256) :=
  let msg := { orderingGuardMessage fork gas with isStatic := true }
  orderingGuardSummary
    (Rinst.runCore 0 ((initDevm msg).withStack stack) (initSevm msg) .tstore)

-- Amsterdam follows `storage.py.tstore`: the static error precedes stack
-- access and charging. The `none` lane retains the pre-Amsterdam order.
#guard orderingGuardTstore .amsterdam 0 [] =
  ("WriteInStaticContext", 0, [], false, false)
#guard orderingGuardTstore .amsterdam 99 [1, 2] =
  ("WriteInStaticContext", 99, [1, 2], false, false)
#guard orderingGuardTstore .amsterdam 100 [1, 2] =
  ("WriteInStaticContext", 100, [1, 2], false, false)
#guard orderingGuardTstore .prague 0 [] =
  ("StackUnderflowError", 0, [], false, false)
#guard orderingGuardTstore .prague 99 [1, 2] =
  ("OutOfGasError", 99, [], false, false)

private def orderingGuardDelegatedMessage (gas : Nat) : Msg :=
  let code := (eoaDelegationMarker ++ (0x3000 : Adr).toBytes).toByteArray
  (orderingGuardMessage .amsterdam gas).setCode 0x2000 code

private def orderingGuardCall
    (gas : Nat) (x : Xinst) (stack : List B256) :=
  let msg := orderingGuardDelegatedMessage gas
  let d := (initDevm msg).withStack stack
  match Xinst.step (initSevm msg) d x with
  | .done r => orderingGuardSummary r
  | .spawn _ _ => ("spawn", 0, [], false, false)

-- The first check may warm the direct code address. The second includes the
-- delegated access price and must fail before the delegated address is warmed.
#guard orderingGuardCall 2999 .staticcall [0, 0x2000, 0, 0, 0, 0] =
  ("OutOfGasError", 2999, [], false, false)
#guard orderingGuardCall 3000 .call [0, 0x2000, 0, 0, 0, 0, 0] =
  ("OutOfGasError", 3000, [], true, false)
#guard orderingGuardCall 3000 .callcode [0, 0x2000, 0, 0, 0, 0, 0] =
  ("OutOfGasError", 3000, [], true, false)
#guard orderingGuardCall 3000 .delegatecall [0, 0x2000, 0, 0, 0, 0] =
  ("OutOfGasError", 3000, [], true, false)
#guard orderingGuardCall 3000 .staticcall [0, 0x2000, 0, 0, 0, 0] =
  ("OutOfGasError", 3000, [], true, false)
#guard (orderingGuardCall 6000 .staticcall [0, 0x2000, 0, 0, 0, 0]).1 =
  "spawn"

private def orderingGuardTopLevel (gas : Nat) : String × Nat × Bool × Bool :=
  let msg := { orderingGuardDelegatedMessage gas with
    target := some 0x2000
    currentTarget := 0x2000 }
  let devm := addAccessedAddress (initDevm msg) 0x2000
  match resolveTopLevelCallAmsterdam msg devm with
  | .error (e, d) =>
    (e.render, d.gasLeft,
      d.accessedAddresses.contains (0x2000 : Adr),
      d.accessedAddresses.contains (0x3000 : Adr))
  | .ok (_, d) =>
    ("ok", d.gasLeft,
      d.accessedAddresses.contains (0x2000 : Adr),
      d.accessedAddresses.contains (0x3000 : Adr))

-- Top-level dispatch has the same boundary: a cold delegated access priced at
-- 3,000 with only 2,999 gas leaves the already-warm recipient as the sole one.
#guard orderingGuardTopLevel 2999 = ("OutOfGasError", 2999, true, false)

--------------- EIP-7928 BLOCK-LEVEL ACCESS LIST REGRESSIONS (G6) ---------------

-- The builder against the pinned `update_builder_from_tx` on synthetic states,
-- and the frame merge against the pinned snapshot's shared read sets. The
-- pipeline's index assignment -- 0 for the two pre-execution system calls,
-- `i + 1` for the `i`-th transaction, `n + 1` for withdrawals and each request
-- call -- is what `applyBody` and `processTransaction` pass; the builder below
-- is shown to file each incorporation under the index it is given, and the
-- Glamsterdam corpus's multi-transaction blocks are the end-to-end evidence.

private def balGuardA : Adr := 0x1000
private def balGuardB : Adr := 0x2000
private def balGuardPre : State :=
  ((State.setBal .empty balGuardA 100).setStorVal balGuardA 1 7).setStorVal balGuardA 2 9

/-- The built list without its code changes, which carry no `DecidableEq`. -/
private def balGuardView (b : BalBuilder) :
    List (Adr × List (B256 × List (Nat × B256)) × List B256 × List (Nat × B256) ×
      List (Nat × UInt64)) :=
  b.build.map fun c =>
    (c.address, c.storageChanges, c.storageReads, c.balanceChanges, c.nonceChanges)

-- A slot written back to its original value is no change and -- because
-- `SSTORE` recorded it -- surfaces as a read.
#guard balGuardView (({} : BalBuilder).incorporate 1 balGuardPre balGuardPre
    [balGuardA] [(balGuardA, 1)] [(balGuardA, 1)]) ==
  [(balGuardA, [], [1], [], [])]

-- A slot both read and written appears only among the changes.
#guard balGuardView (({} : BalBuilder).incorporate 1 balGuardPre
    (balGuardPre.setStorVal balGuardA 1 8) [balGuardA] [(balGuardA, 1)] [(balGuardA, 1)]) ==
  [(balGuardA, [(1, [(1, 8)])], [], [], [])]

-- Two calls at one index net against the index start, not against each other:
-- the restored slot remains a read and the account entry remains present.
#guard
  let st0 := balGuardPre
  let st1 := st0.setStorVal balGuardA 1 8
  let st2 := st1.setStorVal balGuardA 1 7
  let b := ({} : BalBuilder).incorporate 0 st0 st1 [balGuardA] [(balGuardA, 1)] [(balGuardA, 1)]
  let b := b.incorporate 0 st1 st2 [balGuardA] [(balGuardA, 1)] [(balGuardA, 1)]
  balGuardView b == [(balGuardA, [], [1], [], [])]

-- Removing a later same-index slot change preserves that slot's earlier index
-- entry, and its read remains excluded because it is still a change overall.
#guard
  let st0 := balGuardPre
  let st1 := st0.setStorVal balGuardA 1 8
  let st2 := st1.setStorVal balGuardA 1 9
  let st3 := st2.setStorVal balGuardA 1 8
  let b := ({} : BalBuilder).incorporate 1 st0 st1 [balGuardA] [(balGuardA, 1)] [(balGuardA, 1)]
  let b := b.incorporate 2 st1 st2 [balGuardA] [(balGuardA, 1)] [(balGuardA, 1)]
  let b := b.incorporate 2 st2 st3 [balGuardA] [(balGuardA, 1)] [(balGuardA, 1)]
  balGuardView b == [(balGuardA, [(1, [(1, 8)])], [], [], [])]

-- Full forwarding cancels only its own balance entry, while half forwarding
-- retains its final balance and the preceding balance and slot entries.
#guard
  let st0 := balGuardPre
  let stPrior := ((st0.setBal balGuardB 9).setStorVal balGuardA 1 8).setBal balGuardA 110
  let stCredited := stPrior.setBal balGuardA 160
  let stForwarded := stCredited.setBal balGuardA 110
  let stHalf := stCredited.setBal balGuardA 135
  let full := ({} : BalBuilder).incorporate 1 st0 stPrior [balGuardA, balGuardB] [(balGuardA, 1)] [(balGuardA, 1)]
  let full := full.incorporate 2 stPrior stCredited [balGuardA] [] []
  let full := full.incorporate 2 stCredited stForwarded [balGuardA] [] []
  let half := ({} : BalBuilder).incorporate 1 st0 stPrior [balGuardA, balGuardB] [(balGuardA, 1)] [(balGuardA, 1)]
  let half := half.incorporate 2 stPrior stCredited [balGuardA] [] []
  let half := half.incorporate 2 stCredited stHalf [balGuardA] [] []
  balGuardView full ==
      [(balGuardA, [(1, [(1, 8)])], [], [(1, 110)], []), (balGuardB, [], [], [(1, 9)], [])] ∧
    balGuardView half ==
      [(balGuardA, [(1, [(1, 8)])], [], [(1, 110), (2, 135)], []),
       (balGuardB, [], [], [(1, 9)], [])]

-- Nonce and code use the same index-start rule. Restoring both leaves the
-- touched account present without either stale change.
#guard
  let st0 := balGuardPre
  let changed : Acct := {nonce := 1, bal := 0, stor := .empty, code := .mk (.mk [0x00])}
  let st1 := st0.set balGuardB changed
  let st2 := st1.set balGuardB .nil
  let b := ({} : BalBuilder).incorporate 0 st0 st1 [balGuardB] [] []
  let b := b.incorporate 0 st1 st2 [balGuardB] [] []
  match b.build with
  | [c] => c.address == balGuardB && c.storageChanges.isEmpty && c.storageReads.isEmpty &&
      c.balanceChanges.isEmpty && c.nonceChanges.isEmpty && c.codeChanges.isEmpty
  | _ => false

-- Three transactions, then withdrawals, each incorporated under its own index
-- against the block's cumulative state, after a system call at index 0.
#guard
  let st0 := balGuardPre
  let stSys := st0.setStorVal balGuardB 3 4
  let st1 := stSys.setBal balGuardA 90
  let st2 := st1.setBal balGuardA 80
  let st3 := st2.setBal balGuardA 70
  let st4 := st3.setBal balGuardA 170
  let b := ({} : BalBuilder).incorporate 0 st0 stSys [balGuardB] [] [(balGuardB, 3)]
  let b := b.incorporate 1 stSys st1 [balGuardA] [] []
  let b := b.incorporate 2 st1 st2 [balGuardA] [] []
  let b := b.incorporate 3 st2 st3 [balGuardA] [] []
  let b := b.incorporate 4 st3 st4 [balGuardA] [] []
  balGuardView b ==
    [(balGuardA, [], [], [(1, 90), (2, 80), (3, 70), (4, 170)], []),
     (balGuardB, [(3, [(0, 4)])], [], [], [])]

-- A created-then-self-destructed account has no surviving storage writes;
-- the slots `SSTORE` recorded remain reads
-- (the pinned `destroyStorage` conversion).
#guard balGuardView (({} : BalBuilder).incorporate 1 balGuardPre balGuardPre
    [balGuardB] [(balGuardB, 5)] []) ==
  [(balGuardB, [], [5], [], [])]

-- A failed child's reads survive the merge into its parent.
#guard
  let parent := initDevm (orderingGuardMessage .amsterdam 100000)
  let child := (parent.balReadAccount amsterdamRules balGuardB)
    |>.balReadStorage amsterdamRules balGuardB 5
  let merged := incorporateChildAmsterdamOnError parent child []
  merged.meta.accountReads.contains balGuardB ∧
    merged.meta.storageReads.contains (balGuardB, 5) ∧
    ¬ parent.meta.accountReads.contains balGuardB

-- The item rule: `items > gasLimit / itemCost` rejects; at the limit it admits.
private def balGuardList (n : Nat) : BlockAccessList :=
  [{ address := balGuardA, storageChanges := [], storageReads := (List.range n).map (·.toB256),
     balanceChanges := [], nonceChanges := [], codeChanges := [] }]
#guard (balGuardList 2).itemCount = 3
#guard checkBlockAccessListGasLimit amsterdamRules 6000 (balGuardList 2) matches .ok _
#guard checkBlockAccessListGasLimit amsterdamRules 6000 (balGuardList 3)
  matches .error (.block (.blockAccessListGasLimit _))
#guard checkBlockAccessListGasLimit bpo2Rules 6000 (balGuardList 3) matches .ok _

/-! ### EIP-161: touched accounts and the end-of-transaction sweep

Concrete checks of the three EELS touch sites and of the sweep, under Gray
Glacier (the last rule set that sweeps) against Prague (which does not). Jaune
never stores an empty storage-less account, so "exists and is empty" is an
account holding only storage: `touchE`, and 0x03 for the RIPEMD-160 quirk. -/

private def touchParent : Adr := 0x1000
private def touchE : Adr := 0x2000
private def touchC : Adr := 0x4000

/-- `CALL(gas, to, 0, 0, 0, 0, 0)`, then `POP` the success word. -/
private def touchCall (dest gas : Nat) : List UInt8 :=
  [0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0,
   0x61, (dest / 256).toUInt8, (dest % 256).toUInt8,
   0x61, (gas / 256).toUInt8, (gas % 256).toUInt8, 0xF1, 0x50]

private def touchRevert : List UInt8 := [0x60, 0, 0x60, 0, 0xFD]

private def touchState (parentCode cCode : List UInt8) : State :=
  let st := (State.setStorVal .empty touchE 1 1).setStorVal ripemd160Address 1 1
  let st := State.setCode st touchParent ⟨parentCode.toArray⟩
  State.setCode st touchC ⟨cCode.toArray⟩

private def touchMsg (fork : Fork) (parentCode cCode : List UInt8) : Msg :=
  let state := touchState parentCode cCode
  { (default : Msg) with
    benv := { (default : Benv) with
      state := state
      stat := { (default : BenvStat) with fork := fork, origState := state } }
    caller := 0x5000
    target := some touchParent
    currentTarget := touchParent
    codeAddress := some touchParent
    code := ⟨parentCode.toArray⟩
    gas := 200000
    depth := 8 }

/-- The transaction-level touched set `processMessageCall` reports. -/
private def touchedOf (fork : Fork) (parentCode : List UInt8)
    (cCode : List UInt8 := []) : Option (List Adr) :=
  match processMessageCall (touchMsg fork parentCode cCode) with
  | .ok (_, out) => some out.touchedAccounts.toList
  | .error _ => none

-- A successful child's empty target is touched; Prague records nothing.
#guard touchedOf .grayGlacier (touchCall 0x2000 1000 ++ [0x00]) = some [touchE]
#guard touchedOf .prague (touchCall 0x2000 1000 ++ [0x00]) = some []
-- A zero `SELFDESTRUCT` credit to the storage-only `touchE` (U6b,
-- `settle.eraseEmptyOnModify`): before Paris `modify_state` keeps it, storage
-- and all, and the beneficiary touch hands it to the sweep; from Paris the
-- credit erases it at once and nothing is touched. Reported as (`touchE` still
-- present, its slot 1, the touched set).
private def touchSelfdestruct (fork : Fork) : Option (Bool × B256 × List Adr) :=
  match processMessageCall (touchMsg fork [0x61, 0x20, 0x00, 0xFF] []) with
  | .ok (state, out) =>
    some (state[touchE]?.isSome, (state.get touchE).stor.get 1, out.touchedAccounts.toList)
  | .error _ => none
#guard touchSelfdestruct .berlin = some (true, 1, [touchE])
#guard touchSelfdestruct .grayGlacier = some (true, 1, [touchE])
#guard touchSelfdestruct .paris = some (false, 0, [])
#guard touchSelfdestruct .prague = some (false, 0, [])
-- A failed child's touches die with it ...
#guard touchedOf .grayGlacier (touchCall 0x4000 50000 ++ [0x00])
    (touchCall 0x2000 1000 ++ touchRevert) = some []
-- ... except 0x03: the quirk keeps a touch of RIPEMD-160 made inside the
-- failed child,
#guard touchedOf .grayGlacier (touchCall 0x4000 50000 ++ [0x00])
    (touchCall 0x03 1000 ++ touchRevert) = some [ripemd160Address]
-- and a failed call to 0x03 itself (out of gas) still touches it.
#guard touchedOf .grayGlacier (touchCall 0x03 1 ++ [0x00]) = some [ripemd160Address]
#guard touchedOf .prague (touchCall 0x03 1 ++ [0x00]) = some []
-- A failed transaction keeps no touch at all.
#guard touchedOf .grayGlacier (touchCall 0x2000 1000 ++ touchRevert) = some []

-- The sweep erases a touched account that is still empty, keeps a touched
-- account that is not, and is the identity without `touchedSweep`.
#guard (sweepTouchedAccounts grayGlacierRules [touchE, touchParent]
    (touchState [0x00] []))[touchE]?.isNone
#guard (sweepTouchedAccounts grayGlacierRules [touchE, touchParent]
    (touchState [0x00] []))[touchParent]?.isSome
#guard (sweepTouchedAccounts pragueRules [touchE] (touchState [0x00] []))[touchE]?.isSome

/-- `CALL(gas, to, value, 0, 0, 0, 0)`, then `POP` the success word. -/
private def touchCallValue (dest gas value : Nat) : List UInt8 :=
  [0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0, 0x60, value.toUInt8,
   0x61, (dest / 256).toUInt8, (dest % 256).toUInt8,
   0x61, (gas / 256).toUInt8, (gas % 256).toUInt8, 0xF1, 0x50]

/-- U6b end to end: the parent (funded with 1 wei) calls `touchC`, which
self-destructs to the storage-only `touchE` with a zero balance, and then
sends `touchE` 1 wei; the transaction's sweep follows. Before Paris the kept
`touchE` is funded before the sweep, so it survives with its storage; from
Paris the zero credit already erased it, so the 1 wei lands in a fresh
account. Reported as (`touchE`'s balance, its slot 1). -/
private def touchSelfdestructThenFund (fork : Fork) : Option (B256 × B256) :=
  let parentCode := touchCall 0x4000 50000 ++ touchCallValue 0x2000 1000 1 ++ [0x00]
  let msg := touchMsg fork parentCode [0x61, 0x20, 0x00, 0xFF]
  let msg := { msg with benv := msg.benv.setBal touchParent 1 }
  match processMessageCall msg with
  | .ok (state, out) =>
    let state := sweepTouchedAccounts msg.benv.stat.rules out.touchedAccounts.toList state
    some ((state.get touchE).bal, (state.get touchE).stor.get 1)
  | .error _ => none
#guard touchSelfdestructThenFund .berlin = some (1, 1)
#guard touchSelfdestructThenFund .grayGlacier = some (1, 1)
#guard touchSelfdestructThenFund .paris = some (1, 0)
#guard touchSelfdestructThenFund .prague = some (1, 0)

end Jaune

