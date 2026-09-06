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
distinct for exactly the reason the vocabulary keeps them distinct.

Step 10 grew the vocabulary from the twenty tags of the Step-1 census to
twenty-one: `checkTransactionBlobData`'s EIP-4844 blob-fee rejection always
rendered under its own `InsufficientMaxFeePerBlobGasError` spelling -- a
fixture-observed message in the committed golden set -- but carried it as a
bare literal outside every tag table, so the census could not see it. The
constructor pins that producer to its tag like every other reason; its
official fixture identity is the shared `INSUFFICIENT_MAX_FEE_PER_GAS`. -/
inductive TxValidationError : Type
  | gasPriceProductOverflow (detail : ErrorDetail)
  | gasAllowanceExceeded (detail : ErrorDetail)
  | initcodeSizeExceeded (detail : ErrorDetail)
  | insufficientAccountFunds (detail : ErrorDetail)
  | insufficientMaxFeePerGas (detail : ErrorDetail)
  | insufficientMaxFeePerBlobGas (detail : ErrorDetail)
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
  | .insufficientMaxFeePerBlobGas _ => insufficientMaxFeePerBlobGasTag
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
  | .insufficientMaxFeePerGas d | .insufficientMaxFeePerBlobGas d
  | .transactionGasLimitExceeded d
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
    .insufficientMaxFeePerGas .none, .insufficientMaxFeePerBlobGas .none,
    .transactionGasLimitExceeded .none,
    .intrinsicGasTooLow .none, .invalidChainId .none, .nonceIsMax .none,
    .nonceMismatchTooHigh .none, .nonceMismatchTooLow .none,
    .priorityGreaterThanMaxFee .none, .senderNotEoa .none,
    .type3BlobCountExceeded .none, .type3BlobCountLimitExceeded .none,
    .type3ContractCreation .none, .type3InvalidBlobVersionedHash .none,
    .type3ZeroBlobs .none, .type4ContractCreation .none,
    .emptyAuthorizationList .none ]

/-- `B256` carries no `Repr` of its own; the block-rejection type below derives
one, and its `blockAccessListHash` reason now carries a hash as data. Rendered
through the hex `ToString`, which is how every hash prints elsewhere. -/
instance : Repr B256 where
  reprPrec h _ := .text (toString h)

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
  /-- A mandatory request-producing system contract holds no code when the
  block must call it. The pinned `process_checked_system_transaction` raises
  `InvalidBlock` before attempting the call; the corpus names it
  `BlockException.SYSTEM_CONTRACT_EMPTY`. (Goal D, DP-2.) -/
  | systemContractEmpty (detail : ErrorDetail)
  | blockRlpSizeExceeded (detail : ErrorDetail)
  /-- A fork-dependent header field is present when the rules do not define
  it, or absent when they do. -/
  | headerFieldPresence (detail : ErrorDetail)
  /-- EIP-7928: the computed block-level access list's hash differs from the
  header's `blockAccessListHash`. The one reason consensus can observe: the
  block carries only the hash. `computed` is the hash of the list this
  candidate built, carried as data so that the fixture runner's refinement
  below never reads a rendered message. -/
  | blockAccessListHash (computed : B256) (detail : ErrorDetail)
  /-- EIP-7928: the block-level access list a fixture publishes as its
  verification aid is not the computed one in content. Never produced by the
  block pipeline -- only the fixture runner, which alone has the published
  list, refines a `blockAccessListHash` rejection into this one when the
  header's hash is consistent with that list, so that the corpus's two
  identities `INVALID_BLOCK_ACCESS_LIST` and `INVALID_BAL_HASH` are answered
  for the reason each names. -/
  | blockAccessListContent (detail : ErrorDetail)
  /-- EIP-7928: the published list has exactly the computed content in a
  non-canonical arrangement -- accounts out of order or an entry duplicated
  -- which a client comparing the delivered list rejects as malformed.
  Runner-refined, like `blockAccessListContent`: the header's hash is
  consistent with the published list and `BlockAccessList.canonicalise` of
  it hashes to the computed hash. -/
  | blockAccessListFormat (detail : ErrorDetail)
  /-- EIP-7928: the list holds more items than `gasLimit / itemCost`. -/
  | blockAccessListGasLimit (detail : ErrorDetail)
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
  | .systemContractEmpty _ => systemContractEmptyTag
  | .blockRlpSizeExceeded _ => blockRlpSizeExceededTag
  | .headerFieldPresence _ => headerFieldPresenceTag
  | .blockAccessListHash _ _ => blockAccessListHashTag
  | .blockAccessListContent _ => blockAccessListContentTag
  | .blockAccessListFormat _ => blockAccessListFormatTag
  | .blockAccessListGasLimit _ => blockAccessListGasLimitTag

/-- The diagnostic payload of a block-rejection reason. -/
def BlockValidationError.detail : BlockValidationError → ErrorDetail
  | .gasLimitTooBig d | .gasLimitAdjustment d | .gasUsedOverflow d
  | .gasUsedMismatch d | .timestampOlderThanParent d | .blockNumber d
  | .baseFeePerGas d | .difficultyOverParis d | .ommersOverParis d
  | .extraDataTooBig d | .unknownParent d | .unknownParentZero d
  | .stateRoot d | .transactionsRoot d | .receiptsRoot d | .logBloom d
  | .withdrawalsRoot d | .headerNonce d | .excessBlobGas d
  | .blobGasUsed d | .requestsHash d | .depositEventLayout d
  | .systemContractCallFailed d | .systemContractEmpty d | .blockRlpSizeExceeded d
  | .headerFieldPresence d
  | .blockAccessListContent d | .blockAccessListFormat d
  | .blockAccessListGasLimit d => d
  | .blockAccessListHash _ d => d

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
    .systemContractCallFailed .none, .systemContractEmpty .none,
    .blockRlpSizeExceeded .none,
    .headerFieldPresence .none, .blockAccessListHash emptyOmmerHash .none,
    .blockAccessListContent .none, .blockAccessListFormat .none,
    .blockAccessListGasLimit .none ]

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
  /-- The virtual machine propagated a failure no frame settlement may absorb
  -- a cryptographic or internal reason on the typed VM carrier. A Step-10
  extension to the Step-1 skeleton: the VM's error channel is typed `EvmError`,
  and what escapes settlement is an operational failure of this build, never a
  candidate verdict, so it belongs on this channel and fails closed. -/
  | vm (reason : EvmError)
deriving DecidableEq, Repr

/-- The one renderer for `ImportFailure`. -/
def ImportFailure.render : ImportFailure → String
  | .context reason => reason.render
  | .support reason => reason.render
  | .harness detail => renderTagged internalErrorTag detail
  | .internal reason => reason.render
  | .vm reason => reason.render

/-- A failed configured rules lookup is an operational import failure on the
matching channel: context stays context, support stays support. -/
def ImportFailure.ofLookup : RulesLookupError → ImportFailure
  | .context reason => .context reason
  | .support reason => .support reason

@[simp] theorem ImportFailure.render_ofLookup (e : RulesLookupError) :
    (ImportFailure.ofLookup e).render = e.render := by
  cases e <;> rfl

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
  /-- Sender recovery outside the VM rejected the transaction's signature.
  A Step-10 extension to the Step-1 skeleton: the four fixture-observed
  `InvalidSignatureError` diagnostics ride the candidate-rejection channel and
  classify as `SENDER_NOT_EOA`, so the typed rejection needs an arm for the
  `CryptoError` carrier `recoverSender` produces. Only its
  `.invalidSignature` reason maps to a fixture identity; the other
  cryptographic reasons fail closed. -/
  | senderRecovery (reason : CryptoError)
deriving DecidableEq, Repr

/-- The one renderer for `BlockRejection`. -/
def BlockRejection.render : BlockRejection → String
  | .transaction reason => reason.render
  | .block reason => reason.render
  | .decode reason => reason.render
  | .senderRecovery reason => reason.render

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

/-- Everything the block state transition can fail with, before the import
layer splits it into a candidate verdict and an operational failure.

This is the working carrier of the transition body -- `validateHeader`, the
ommers check, `applyBody` with its transaction pipeline, and the
post-transition checks all construct or propagate one of these -- so it is a
plain union rather than a channelled sum; `TransitionError.split` below is the
single place each arm is assigned to the outer or the inner import channel,
per the Step-1 producer/channel matrix. -/
inductive TransitionError : Type
  /-- Strict decode of a typed transaction envelope inside `applyBody` failed.
  Deliberate channel decision (design report §8): every strict decode reason
  is a candidate verdict -- the audited fixture ordering scores them as block
  exceptions -- so this arm splits to `BlockRejection.decode`. -/
  | decode (reason : DecodeError)
  /-- A transaction in the body is inadmissible. Splits to
  `BlockRejection.transaction`. -/
  | transaction (reason : TxValidationError)
  /-- A header or post-transition consensus check failed. Splits to
  `BlockRejection.block`. -/
  | block (reason : BlockValidationError)
  /-- Sender recovery rejected a transaction signature outside the VM. Splits
  to `BlockRejection.senderRecovery`. -/
  | senderRecovery (reason : CryptoError)
  /-- The virtual machine propagated a failure that no frame settlement may
  absorb -- a cryptographic or internal reason on the typed VM carrier. Not a
  candidate verdict: splits to the outer failure channel. -/
  | vm (reason : EvmError)
  /-- A transaction/block-layer invariant of this build did not hold. Never a
  candidate verdict: splits to the outer failure channel. -/
  | internal (reason : InternalError)
deriving DecidableEq, Repr

/-- The one renderer for `TransitionError`: pure delegation, so every rendered
diagnostic is byte-for-byte its reason's own. -/
def TransitionError.render : TransitionError → String
  | .decode reason => reason.render
  | .transaction reason => reason.render
  | .block reason => reason.render
  | .senderRecovery reason => reason.render
  | .vm reason => reason.render
  | .internal reason => reason.render

/-- The channel split of the Step-1 producer/channel matrix, in one place:
which transition failures are verdicts about the candidate block
(`BlockRejection`, the inner import channel) and which mean the question was
not answered (`ImportFailure`, the outer channel). Internal and VM-propagated
failures can never read as an expected consensus rejection (fixed decision
7); every decode, transaction, block, and sender-recovery reason is the
candidate's own rejection. -/
def TransitionError.split : TransitionError → ImportFailure ⊕ BlockRejection
  | .decode reason => .inr (.decode reason)
  | .transaction reason => .inr (.transaction reason)
  | .block reason => .inr (.block reason)
  | .senderRecovery reason => .inr (.senderRecovery reason)
  | .vm reason => .inl (.vm reason)
  | .internal reason => .inl (.internal reason)

/-- Rendering commutes with the channel split: whichever channel a reason is
assigned to, its diagnostic is unchanged. -/
theorem TransitionError.render_split (e : TransitionError) :
    (match e.split with
      | .inl f => f.render
      | .inr r => r.render) = e.render := by
  cases e <;> rfl

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
#guard TxValidationError.all.length = 21
#guard TxValidationError.all.eraseDups.length = 21
#guard TxValidationError.all.map TxValidationError.tag = transactionExceptionTags
#guard (TxValidationError.all.map TxValidationError.tag).eraseDups.length = 21
#guard TxValidationError.render
    (.insufficientMaxFeePerBlobGas (.text "insufficient max fee per blob gas"))
  = "InsufficientMaxFeePerBlobGasError : insufficient max fee per blob gas"
#guard TxValidationError.render (.nonceMismatchTooHigh .none)
  = "NonceMismatchTooHighError"
#guard TxValidationError.render (.intrinsicGasTooLow (.text "needs 21000, has 20999"))
  = "IntrinsicGasTooLowError : needs 21000, has 20999"

#guard BlockValidationError.all.length = 30
#guard BlockValidationError.all.eraseDups.length = 30
#guard BlockValidationError.all.map BlockValidationError.tag = blockExceptionTags
#guard (BlockValidationError.all.map BlockValidationError.tag).eraseDups.length = 30
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

/-! ### Amsterdam top-level preparation

The dual-gas fork prices state-dependent transaction dispatch in the top
frame, before bytecode starts.  The preparation machine therefore carries the
real top-frame meters and world.  A successful delegation phase commits its
state gas; a later preparation failure restores the transaction-entry
reservoir and world. -/

private abbrev AmsterdamDelegationResult := Devm × AdrSet × AdrSet

private def chargeNewAuthorityAmsterdam (state : StateGasRules)
    (authority : Adr) (devm : Devm) : Execution :=
  if devm.state.get authority = .nil then
    chargeStateGas state.newAccount devm
  else .ok devm

private def chargePaidAccountWriteAmsterdam (state : StateGasRules)
    (authority : Adr) (devm : Devm) (paidWrites : AdrSet) :
    Except (EvmError × Devm) (Devm × AdrSet) :=
  if paidWrites.contains authority then
    .ok ⟨devm, paidWrites⟩
  else do
    let devm ← chargeGas state.accountWrite devm
    .ok ⟨devm, paidWrites.insert authority⟩

private def chargeAuthBaseAmsterdam (state : StateGasRules) (msg : Msg)
    (authority target : Adr) (devm : Devm) (delegationSetFor : AdrSet) :
    Except (EvmError × Devm) (Devm × AdrSet × ByteArray) :=
  if target = 0 then
    .ok ⟨devm, delegationSetFor, .empty⟩
  else do
    let delegatedBeforeTx :=
      isValidDelegation (msg.benv.stat.origState.getCode authority)
    let devm ←
      if ¬ delegatedBeforeTx && ¬ delegationSetFor.contains authority then
        chargeStateGas state.authBase devm
      else .ok devm
    .ok ⟨devm, delegationSetFor.insert authority,
      (eoaDelegationMarker ++ target.toBytes).toByteArray⟩

private def applyValidatedDelegationAmsterdam (state : StateGasRules)
    (msg : Msg) (authority target : Adr) (devm : Devm)
    (paidWrites delegationSetFor : AdrSet) :
    Except (EvmError × Devm) AmsterdamDelegationResult := do
  let devm ← chargeNewAuthorityAmsterdam state authority devm
  let (⟨devm, paidWrites⟩ : Devm × AdrSet) ←
    chargePaidAccountWriteAmsterdam state authority devm paidWrites
  let (⟨devm, delegationSetFor, codeToSet⟩ :
      Devm × AdrSet × ByteArray) ←
    chargeAuthBaseAmsterdam state msg authority target devm delegationSetFor
  let devm := (devm.setCode authority codeToSet).incrNonce authority
  .ok ⟨devm, paidWrites, delegationSetFor⟩

private def setDelegationAmsterdamStep (state : StateGasRules) (msg : Msg)
    (auth : Auth) (devm : Devm) (paidWrites delegationSetFor : AdrSet) :
    Except (EvmError × Devm) AmsterdamDelegationResult := do
  if auth.chainId != msg.benv.stat.chainId.toB256 && auth.chainId != 0 then
    .ok ⟨devm, paidWrites, delegationSetFor⟩
  else if auth.nonce = UInt64.max then
    .ok ⟨devm, paidWrites, delegationSetFor⟩
  else
    match recoverAuthority auth with
    | .error (.invalidSignature _) =>
      .ok ⟨devm, paidWrites, delegationSetFor⟩
    | .error err => .error ⟨.crypto err, devm⟩
    | .ok authority =>
      -- Recovery warms the authority even when a later validity check skips
      -- the tuple, and `get_account(authority)` reads it (EIP-7928).
      let devm := addAccessedAddress devm authority
      let devm := devm.balReadAccount msg.benv.stat.rules authority
      let authorityAccount := devm.state.get authority
      if ¬ (authorityAccount.code.isEmpty ∨
          isValidDelegation authorityAccount.code) then
        .ok ⟨devm, paidWrites, delegationSetFor⟩
      else if authorityAccount.nonce != auth.nonce then
        .ok ⟨devm, paidWrites, delegationSetFor⟩
      else
        applyValidatedDelegationAmsterdam state msg authority auth.address
          devm paidWrites delegationSetFor

private def setDelegationAmsterdamLoop (state : StateGasRules) (msg : Msg) :
    List Auth → Devm → AdrSet → AdrSet →
      Except (EvmError × Devm) AmsterdamDelegationResult
  | [], devm, paidWrites, delegationSetFor =>
    .ok ⟨devm, paidWrites, delegationSetFor⟩
  | auth :: auths, devm, paidWrites, delegationSetFor => do
    let ⟨devm, paidWrites, delegationSetFor⟩ ←
      setDelegationAmsterdamStep state msg auth devm paidWrites delegationSetFor
    setDelegationAmsterdamLoop state msg auths devm paidWrites delegationSetFor

private def setDelegationAmsterdam (state : StateGasRules) (msg : Msg)
    (devm : Devm) : Execution := do
  let paidWrites := {msg.caller}
  let paidWrites :=
    if msg.target.isNone || msg.value != 0 then
      paidWrites.insert msg.currentTarget
    else paidWrites
  let ⟨devm, _, _⟩ ← setDelegationAmsterdamLoop state msg
    msg.tenv.stat.auths devm paidWrites .emptyWithCapacity
  .ok devm

private def preparedTopLevelMsg (msg : Msg) (devm : Devm) : Msg :=
  { msg with
    benv := {
      msg.benv with
      state := devm.state
      createdAccounts := devm.createdAccounts
    }
    tenv := {msg.tenv with transientStorage := devm.transientStorage}
    accessedAddresses := devm.accessedAddresses
    accessedStorageKeys := devm.accessedStorageKeys
  }

private def resolveTopLevelCallAmsterdam (msg : Msg) (devm : Devm) :
    Except (EvmError × Devm) (Msg × Devm) := do
  let ⟨delegated, codeAddress, accessCost⟩ :=
    msg.benv.stat.rules.gas.delegationCost devm msg.currentTarget
  let devm ← chargeGas accessCost devm
  let ⟨code, devm⟩ := completeDelegationAccess devm delegated codeAddress
  -- `create_evm`: `get_account(code_address)` is a read (EIP-7928).
  let devm := devm.balReadAccount msg.benv.stat.rules codeAddress
  let msg := preparedTopLevelMsg msg devm
  .ok ⟨{
    msg with
    codeAddress := some codeAddress
    code := code
    disablePrecompiles := delegated
  }, devm⟩

private def dispatchTopLevelAmsterdam (state : StateGasRules) (msg : Msg)
    (devm : Devm) : Except (EvmError × Devm) (Msg × Devm) := do
  -- `create_evm` reads the current target on both branches --
  -- `account_deployable`/`get_pre_state_account` for a creation,
  -- `resolve_delegated_code_address`'s `get_account(recipient)` for a call
  -- (EIP-7928).
  let devm := devm.balReadAccount msg.benv.stat.rules msg.currentTarget
  if msg.target.isNone then
    let isCollision :=
      accountHasCodeOrNonce devm.state msg.currentTarget ||
        accountHasStorage devm.state msg.currentTarget
    if isCollision then
      .error ⟨.halt (.addressCollision .none), devm⟩
    else do
      let devm ←
        if msg.benv.stat.origState.get msg.currentTarget = .nil then
          chargeStateGas state.newAccount devm
        else .ok devm
      .ok ⟨preparedTopLevelMsg msg devm, devm⟩
  else do
    let devm ←
      if msg.value != 0 && ¬ AccountExists devm.state msg.currentTarget then
        chargeStateGas state.newAccount devm
      else .ok devm
    resolveTopLevelCallAmsterdam msg devm

private def finishTopLevelAmsterdam (state : StateGasRules) (msg : Msg)
    (devm : Devm) : Except (EvmError × Devm) (Msg × Devm) :=
  let devm :=
    if msg.tenv.stat.auths.isEmpty then devm else devm.commitStateGas
  dispatchTopLevelAmsterdam state msg devm

private def prepareTopLevelAmsterdam (state : StateGasRules) (msg : Msg) :
    Except (EvmError × Devm) (Msg × Devm) := do
  let devm := initDevm msg
  let devm ←
    if msg.tenv.stat.auths.isEmpty then .ok devm
    else setDelegationAmsterdam state msg devm
  finishTopLevelAmsterdam state msg devm

/-- Enter the existing total interpreter with the machine prepared above.
Only the ordinary `Frame.enter` initialization is replaced: transfer,
precompile dispatch, execution, and frame settlement remain shared. -/
private def runPreparedTopFrame (frame : Frame) (prepared : Devm) :
    Except (EvmError × State × AdrSet × Tra) Devm :=
  match frame.inner.benvAfterTransfer with
  | .error e => frame.settleMsg (.error e)
  | .ok benv =>
    let inner := frame.inner.withBenv benv
    let dyna :=
      (prepared.withState benv.state).withCreatedAccounts benv.createdAccounts
    let evm : Evm := {pc := 0, sta := initSevm inner, dyna := dyna}
    let raw :=
      match inner.codeAddress with
      | none => exec evm
      | some adr =>
        if !inner.disablePrecompiles && inner.benv.stat.rules.isPrecomp adr then
          executePrecomp evm adr
        else exec evm
    frame.settle raw

private def msgCallOutputAmsterdam (msg : Msg) (evm : Devm) :
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
    gasLeft := evm.gasLeft
    refundCounter := refundCounter
    logs := logs
    accountsToDelete := accountsToDelete
    error := evm.error
    returnData := evm.output
    stateGasLeft := evm.stateGasLeft
    stateGasUsed := stateGasUsed
  }⟩

private def settleTopLevelPreparationFailure (msg : Msg) (error : EvmError)
    (devm : Devm) : Except EvmError (State × MsgCallOutput) :=
  match error with
  | .halt reason =>
    let devm :=
      (devm.rollback msg.benv.state msg.tenv.transientStorage)
        |>.restoreStateGasToEntry msg.stateGasGrant
        |>.forfeitRemainingGas
    -- The reads the preparation recorded before it halted -- the authorities
    -- of every processed tuple, the recipient once dispatch loaded it -- stay
    -- in the block-level access list: `incorporate_tx_into_block` runs for a
    -- halted transaction too, and a read survives the rollback (EIP-7928).
    .ok ⟨msg.benv.state, {
      accountReads := devm.meta.accountReads
      storageReads := devm.meta.storageReads
      gasLeft := devm.gasLeft
      refundCounter := 0
      logs := []
      accountsToDelete := .emptyWithCapacity
      error := some (.halt reason)
      returnData := []
      stateGasLeft := devm.stateGasLeft
      stateGasUsed := 0
    }⟩
  | .revert => .error .revert
  | .crypto reason => .error (.crypto reason)
  | .internal reason => .error (.internal reason)

private def processTopLevelAmsterdam (state : StateGasRules) (msg : Msg)
    (frameOf : Msg → Frame) : Except EvmError (State × MsgCallOutput) :=
  match prepareTopLevelAmsterdam state msg with
  | .error ⟨error, devm⟩ =>
    settleTopLevelPreparationFailure msg error devm
  | .ok ⟨msg, devm⟩ => do
    let evm ← Except.bimap Prod.fst id
      (runPreparedTopFrame (frameOf msg) devm)
    msgCallOutputAmsterdam msg evm

def processMessageCall.create (msg : Msg) :
  Except EvmError (State × MsgCallOutput) := do
  match msg.benv.stat.rules.stateGas with
  | none =>
    let benv := msg.benv
    let isCollision : Bool :=
      accountHasCodeOrNonce benv.state msg.currentTarget ||
        accountHasStorage benv.state msg.currentTarget
    if isCollision then
      return ⟨benv.state,
        { gasLeft := 0, refundCounter := 0, logs := [],
          accountsToDelete := .emptyWithCapacity,
          error := .some (.halt (.addressCollision .none)), returnData := [] }⟩
    else
      let evm ← Except.bimap Prod.fst id (processCreateMessage msg)
      let logs := if evm.error.isNone then evm.logs else []
      let accountsToDelete :=
        if evm.error.isNone then evm.accountsToDelete else .emptyWithCapacity
      let refundCounter ←
        if evm.error.isNone then
         (Int.toNat? evm.refundCounter).toExcept
           (EvmError.internal (.invariant (.text "refund counter is negative")))
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
  | some state =>
    processTopLevelAmsterdam state msg Frame.ofCreate

def processMessageCall.call (msg : Msg) :
  Except EvmError (State × MsgCallOutput) := do
  match msg.benv.stat.rules.stateGas with
  | none =>
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
        (Int.toNat? evm.refundCounter).toExcept
          (EvmError.internal (.invariant (.text "refund counter is negative")))
      else
        .ok 0
    let logs := if evm.error.isNone then evm.logs else []
    let accountsToDelete :=
      if evm.error.isNone then evm.accountsToDelete else .emptyWithCapacity
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
  | some state =>
    processTopLevelAmsterdam state msg Frame.ofCall

def processMessageCall (msg : Msg) :
    Except EvmError (State × MsgCallOutput) := do
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

/-! ### EIP-7928: the block-level access list (goal C, fixed decisions 2–4)

A block-scoped builder beside `BlockOutput`, fed once per incorporation --
each pre-execution system call at index 0, the `i`-th transaction at `i + 1`,
the withdrawals batch and each request-producing system call at `n + 1` --
with the *diff* of the incorporated state against the block's cumulative state
(net-zero filtered by construction: a write of the value already there is not
a change) and with the read sets the interpreter recorded (`Meta.accountReads`,
`Meta.storageReads`), which survive reverts. `build` then produces the pinned
canonical form -- accounts by address, slots by number, changes by index, a
slot among the changes excluded from the reads, an account with nothing but
reads still present -- and `hash` is `keccak256(rlp(list))` in the pinned
dataclass field order `address, storageChanges, storageReads, balanceChanges,
nonceChanges, codeChanges`. Nothing under `rules.bal = none` touches any of
this: `BlockOutput.bal` stays `{}` and `blockAccessList` stays `[]`. -/

/-- One account's accumulated changes and reads (`AccountData` at the pin).
Slots live in ordered maps so that `build` needs no sort of its own; the change
lists are appended in block-access-index order and sorted again at build. -/
structure BalAccount : Type where
  storageChanges : Std.TreeMap B256 (List (Nat × B256)) compare := .empty
  storageReads : Std.TreeMap B256 Unit compare := .empty
  balanceChanges : List (Nat × B256) := []
  nonceChanges : List (Nat × UInt64) := []
  codeChanges : List (Nat × ByteArray) := []

/-- `BlockAccessListBuilder` at the pin: address ↦ its data. The block access
index is not stored here; every incorporation names its own. -/
structure BalBuilder : Type where
  accounts : Std.TreeMap Adr BalAccount compare := .empty

namespace BalAccount

/-- Replace the entry at `idx` or append: only the final value per index is
kept (`add_storage_write`, `add_balance_change`, `add_code_change`). -/
private def upsert {α : Type} (l : List (Nat × α)) (idx : Nat) (v : α) : List (Nat × α) :=
  if l.any (·.1 = idx) then l.map (fun c => if c.1 = idx then (idx, v) else c)
  else l ++ [(idx, v)]

def addStorageWrite (acc : BalAccount) (slot : B256) (idx : Nat) (v : B256) : BalAccount :=
  {acc with storageChanges :=
    acc.storageChanges.insert slot (upsert (acc.storageChanges.getD slot []) idx v)}

def addStorageRead (acc : BalAccount) (slot : B256) : BalAccount :=
  {acc with storageReads := acc.storageReads.insert slot ()}

def addBalanceChange (acc : BalAccount) (idx : Nat) (v : B256) : BalAccount :=
  {acc with balanceChanges := upsert acc.balanceChanges idx v}

/-- `add_nonce_change` keeps the highest nonce per index. -/
def addNonceChange (acc : BalAccount) (idx : Nat) (n : UInt64) : BalAccount :=
  {acc with nonceChanges :=
    match acc.nonceChanges.find? (·.1 = idx) with
    | some ⟨_, old⟩ => if old < n then upsert acc.nonceChanges idx n else acc.nonceChanges
    | none => acc.nonceChanges ++ [(idx, n)]}

def addCodeChange (acc : BalAccount) (idx : Nat) (code : ByteArray) : BalAccount :=
  {acc with codeChanges := upsert acc.codeChanges idx code}

end BalAccount

namespace BalBuilder

/-- `ensure_account`/`add_touched_account`: an entry with nothing in it. -/
def ensure (b : BalBuilder) (a : Adr) : BalBuilder :=
  if b.accounts.contains a then b else {accounts := b.accounts.insert a {}}

def modify (b : BalBuilder) (a : Adr) (f : BalAccount → BalAccount) : BalBuilder :=
  {accounts := b.accounts.insert a (f (b.accounts.getD a {}))}

/-- `update_builder_from_tx`: the incorporated state's writes as a diff against
the block's cumulative state (`pre`), recorded at `idx`; then the merge of the
read sets. An address whose account differs in balance, nonce or code, or
whose storage differs at a slot, records that change with the post value; a
value written back to its original is no change, and -- because `SLOAD` and
`SSTORE` recorded the slot -- surfaces as a read. -/
def incorporate (b : BalBuilder) (idx : Nat) (pre post : State)
    (accountReads : List Adr) (storageReads : List (Adr × B256)) : BalBuilder :=
  let addrs : List Adr := (pre.keys ++ post.keys).eraseDups
  let b := addrs.foldl (init := b) fun b a =>
    let acPre := pre.get a
    let acPost := post.get a
    let b := if acPre.bal ≠ acPost.bal then b.modify a (·.addBalanceChange idx acPost.bal) else b
    let b := if acPre.nonce ≠ acPost.nonce then b.modify a (·.addNonceChange idx acPost.nonce) else b
    let b :=
      if acPre.code.data ≠ acPost.code.data then b.modify a (·.addCodeChange idx acPost.code)
      else b
    let slots : List B256 := (acPre.stor.keys ++ acPost.stor.keys).eraseDups
    slots.foldl (init := b) fun b k =>
      if acPre.stor.get k ≠ acPost.stor.get k then
        b.modify a (·.addStorageWrite k idx (acPost.stor.get k))
      else b
  let b := storageReads.foldl (init := b) fun b ⟨a, k⟩ => b.modify a (·.addStorageRead k)
  accountReads.foldl (init := b) fun b a => b.ensure a

end BalBuilder

/-- `AccountChanges` at the pin, in its dataclass field order. -/
structure BalAccountChanges : Type where
  address : Adr
  storageChanges : List (B256 × List (Nat × B256))
  storageReads : List B256
  balanceChanges : List (Nat × B256)
  nonceChanges : List (Nat × UInt64)
  codeChanges : List (Nat × ByteArray)

/-- The built list: `BlockAccessList` at the pin. -/
abbrev BlockAccessList : Type := List BalAccountChanges

private def sortByIndex {α : Type} (l : List (Nat × α)) : List (Nat × α) :=
  l.mergeSort (fun x y => x.1 ≤ y.1)

/-- `_build_from_builder`: accounts by address, slots by number, changes by
index, and a slot that appears among the changes excluded from the reads. -/
def BalBuilder.build (b : BalBuilder) : BlockAccessList :=
  b.accounts.toList.map fun ⟨a, acc⟩ =>
    { address := a
      storageChanges := acc.storageChanges.toList.map fun ⟨slot, cs⟩ => (slot, sortByIndex cs)
      storageReads := (acc.storageReads.toList.map Prod.fst).filter
        (fun k => ¬ acc.storageChanges.contains k)
      balanceChanges := sortByIndex acc.balanceChanges
      nonceChanges := sortByIndex acc.nonceChanges
      codeChanges := sortByIndex acc.codeChanges }

/-- RLP of an unsigned integer: minimal big-endian bytes, `0` as the empty
string -- how the pinned `rlp.encode` writes `U256`, `U64` and `Uint`. -/
private def natBLT (n : Nat) : BLT := .bytes n.toBytes

def BalAccountChanges.toBLT (c : BalAccountChanges) : BLT :=
  .list [
    .bytes c.address.toBytes,
    .list (c.storageChanges.map fun ⟨slot, cs⟩ =>
      .list [natBLT slot.toNat,
             .list (cs.map fun ⟨i, v⟩ => .list [natBLT i, natBLT v.toNat])]),
    .list (c.storageReads.map fun k => natBLT k.toNat),
    .list (c.balanceChanges.map fun ⟨i, v⟩ => .list [natBLT i, natBLT v.toNat]),
    .list (c.nonceChanges.map fun ⟨i, n⟩ => .list [natBLT i, natBLT n.toNat]),
    .list (c.codeChanges.map fun ⟨i, code⟩ => .list [natBLT i, .bytes code.toList]) ]

def BlockAccessList.toBLT (l : BlockAccessList) : BLT := .list (l.map BalAccountChanges.toBLT)

/-- `rlp.encode(block_access_list)`. -/
def BlockAccessList.encode (l : BlockAccessList) : Bytes := l.toBLT.toBytes

/-- `hash_block_access_list`. -/
def BlockAccessList.hash (l : BlockAccessList) : B256 := l.encode.keccak

/-- `validate_block_access_list_gas_limit`'s count: every address, plus every
unique storage slot across its changes and reads (the reads already exclude
the changed slots at build time). -/
def BlockAccessList.itemCount (l : BlockAccessList) : Nat :=
  l.foldl (fun n c => n + 1 + c.storageChanges.length + c.storageReads.length) 0

-- The empty list hashes to `keccak(rlp [])`, which is `emptyOmmerHash`.
#guard BlockAccessList.hash [] = emptyOmmerHash
#guard BlockAccessList.encode [] = [0xC0]
#guard BlockAccessList.itemCount [] = 0

/-- A delivered list's canonical re-arrangement: accounts in address order,
adjacent exact duplicates collapsed, every entry's own content untouched. The
fixture runner compares its hash with the computed list's to tell a published
list that is right in content but wrong in form (the corpus's
`INCORRECT_BLOCK_FORMAT`: accounts reversed, an account duplicated) from one
whose content is wrong (`INVALID_BLOCK_ACCESS_LIST`). Consensus never calls
it: the block carries only the hash, and a built list is already canonical. -/
def BlockAccessList.canonicalise (l : BlockAccessList) : BlockAccessList :=
  dedupAdjacent (l.mergeSort fun a b => (compare a.address b.address).isLE)
where
  dedupAdjacent : BlockAccessList → BlockAccessList
    | a :: b :: rest =>
      if a.toBLT.toBytes = b.toBLT.toBytes then dedupAdjacent (b :: rest)
      else a :: dedupAdjacent (b :: rest)
    | l => l

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

structure BlockOutput : Type where
  blockGasUsed : Nat
  /-- State-gas usage is an independent block-capacity dimension under
  Amsterdam. The default keeps every legacy construction source-compatible. -/
  blockStateGasUsed : Nat := 0
  /-- Sender-facing gas after refunds, accumulated for receipt encoding. -/
  cumulativeGasUsed : Nat := 0
  transactionsTrie : Std.TreeMap Bytes Tx compare
  receiptsTrie : Std.TreeMap Bytes (Fin 5 × Receipt) compare
  receiptKeys : List Bytes
  blockLogs : List Log
  withdrawalsTrie : Std.TreeMap Bytes Withdrawal compare
  blobGasUsed : Nat
  requests : List Bytes
  /-- EIP-7928: the block-level access-list builder, fed at every incorporation
  under `rules.bal = some _`; untouched otherwise. Defaulted so that every
  `BlockOutput` literal keeps elaborating. -/
  bal : BalBuilder := {}
  /-- EIP-7928: the built list, set once by `applyBody` after the requests. -/
  blockAccessList : BlockAccessList := []

/-- The legacy block-accounting relation promised by fixed decision 8: sender
and execution gas advance together, and the independent state-gas dimension
stays empty. -/
def BlockOutput.LegacyGasAccounting (bout : BlockOutput) : Prop :=
  bout.cumulativeGasUsed = bout.blockGasUsed ∧ bout.blockStateGasUsed = 0

instance {bout : BlockOutput} : Decidable bout.LegacyGasAccounting := by
  unfold BlockOutput.LegacyGasAccounting
  infer_instance

-- The following helpers keep the checks in the same order, with the same
-- returned payloads and error strings, as the monolithic transaction checker.
-- Splitting the executable stages makes successful runs easier to invert in
-- proofs without unfolding the whole checker at once.

def checkTransactionGasLimits
    (benv : Benv) (blockOut : BlockOutput) (tx : Tx) :
    Except TxValidationError Nat :=
  let executionGasAvailable := benv.stat.blockGasLimit - blockOut.blockGasUsed
  let blobGasAvailable := benv.stat.rules.blob.max - blockOut.blobGasUsed
  let executionGasRequired :=
    match benv.stat.rules.stateGas with
    | none => tx.gas
    | some _ => min (benv.stat.rules.tx.maxGas.getD tx.gas) tx.gas
  if executionGasRequired > executionGasAvailable then
    .error <| .gasAllowanceExceeded <| .text
      s!"transaction execution gas = {executionGasRequired} > \
         block execution gas available = {executionGasAvailable}"
  else
    match benv.stat.rules.stateGas with
    | some _ =>
      let stateGasAvailable :=
        benv.stat.blockGasLimit - blockOut.blockStateGasUsed
      if tx.gas > stateGasAvailable then
        .error <| .gasAllowanceExceeded <| .text
          s!"transaction state gas = {tx.gas} > \
             block state gas available = {stateGasAvailable}"
      else
        let txBlobGasUsed := calculateTotalBlobGas tx
        if txBlobGasUsed > blobGasAvailable then
          .error <| .type3BlobCountExceeded <| .text
            s!"blob gas used = {txBlobGasUsed} > \
               blob gas available = {blobGasAvailable}"
        else .ok txBlobGasUsed
    | none =>
      let txBlobGasUsed := calculateTotalBlobGas tx
      if txBlobGasUsed > blobGasAvailable then
        .error <| .type3BlobCountExceeded <| .text
          s!"blob gas used = {txBlobGasUsed} > \
             blob gas available = {blobGasAvailable}"
      else .ok txBlobGasUsed

def checkTransactionDynamicGasFee
    (baseFeePerGas gas maxPriorityFee maxFee : Nat) :
    Except TxValidationError (Nat × Nat) :=
  if maxFee < maxPriorityFee then
    .error <| .priorityGreaterThanMaxFee <| .text
      s!"priority fee = {maxPriorityFee} > \
         max fee = {maxFee}"
  else if maxFee < baseFeePerGas then
    .error <| .insufficientMaxFeePerGas <| .text
      s!"max fee = {maxFee} < \
         base fee = {baseFeePerGas}"
  else
    let maxGasFee := gas * maxFee
    if maxGasFee > B256.max.toNat then
      .error <| .gasPriceProductOverflow <| .text
        s!"gas * max fee = {maxGasFee} > \
           2^256 - 1"
    else
      let priorityFeePerGas := min maxPriorityFee (maxFee - baseFeePerGas)
      .ok ⟨priorityFeePerGas + baseFeePerGas, maxGasFee⟩

def checkTransactionLegacyGasFee
    (baseFeePerGas gas gasPrice : Nat) :
    Except TxValidationError (Nat × Nat) :=
  if gasPrice < baseFeePerGas then
    .error <| .insufficientMaxFeePerGas <| .text
      s!"gas price = {gasPrice} < \
         base fee = {baseFeePerGas}"
  else
    let maxGasFee := gas * gasPrice
    if maxGasFee > B256.max.toNat then
      .error <| .gasPriceProductOverflow <| .text
        s!"gas * gas price = {maxGasFee} > \
           2^256 - 1"
    else
      .ok ⟨gasPrice, maxGasFee⟩

def checkTransactionGasFee (benv : Benv) (tx : Tx) :
    Except TxValidationError (Nat × Nat) :=
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
    (blobHashes : List B256) : Except TxValidationError Unit :=
  match limits.maxBlobCount with
  | none => .ok ()
  | some maxBlobCount =>
    if blobHashes.length > maxBlobCount then
      .error <| .type3BlobCountLimitExceeded <| .text
        s!"transaction has \
           {blobHashes.length} blobs > maximum = {maxBlobCount}"
    else
      .ok ()

def checkTransactionBlobData
    (benv : Benv) (tx : Tx) (maxGasFee : Nat) :
    Except TxValidationError (Nat × List B256) :=
  match tx.type with
  | .three _ _ _ _ _ maxBlobFee blobHashes => do
    if blobHashes.isEmpty then
      .error <| .type3ZeroBlobs <| .text "no blob hashes in type-3 transaction"
    checkTransactionBlobCount benv.stat.rules.tx blobHashes
    -- P0.6 item 3: the version byte is read through the total `head?`, never a
    -- partial index into the fixed 32-byte hash encoding.
    if List.any blobHashes (λ bvh => bvh.toBytes.head? ≠ some versionedHashVersionKzg) then
      .error <| .type3InvalidBlobVersionedHash <| .text
        s!"a blob versioned hash has \
           a version byte other than {versionedHashVersionKzg}"
    else
      let blobGasPrice :=
        calculateBlobGasPrice benv.stat.rules.blob benv.stat.excessBlobGas
      if maxBlobFee < blobGasPrice then
        .error <| .insufficientMaxFeePerBlobGas <|
          .text "insufficient max fee per blob gas"
      else
        .ok ⟨maxGasFee + calculateTotalBlobGas tx * maxBlobFee, blobHashes⟩
  | _ => .ok ⟨maxGasFee, []⟩

def checkTransactionReceiver (tx : Tx) : Except TxValidationError Unit :=
  if tx.isTypeThree then
    if tx.type.receiver?.isNone then
      .error <| .type3ContractCreation <|
        .text "type-3 transactions cannot create contracts"
    else
      .ok ()
  else
    .ok ()

def checkTransactionAuthorizationList (tx : Tx) : Except TxValidationError Unit :=
  match tx.type with
  | .four _ _ _ _ _ [] =>
    .error <| .emptyAuthorizationList <| .text "empty authorization list"
  | _ => .ok ()

def checkTransactionChainId (benv : Benv) (tx : Tx) : Except TxValidationError Unit :=
  match tx.type with
  | .zero _ _ =>
    if tx.v < 35 || (tx.v - 35) / 2 = benv.stat.chainId.toNat then .ok ()
    else .error <| .invalidChainId <| .text
      s!"transaction chain ID = {(tx.v - 35) / 2}"
  | .one chainId _ _ _
  | .two chainId _ _ _ _
  | .three chainId _ _ _ _ _ _
  | .four chainId _ _ _ _ _ =>
    if chainId = benv.stat.chainId then .ok ()
    else .error <| .invalidChainId <| .text s!"transaction chain ID = {chainId}"

def checkTransactionSenderCode (senderAccount : Acct) :
    Except TxValidationError Unit :=
  if ¬ (senderAccount.code.isEmpty ∨ isValidDelegation senderAccount.code) then
    .error <| .senderNotEoa <| .text "sender has non-delegation code"
  else
    .ok ()

def checkTransactionSenderAccount
    (senderAccount : Acct) (tx : Tx) (maxGasFee : Nat) :
    Except TxValidationError Unit :=
  if senderAccount.nonce > tx.nonce then
    .error <| .nonceMismatchTooLow <| .text
      s!"transaction nonce = {tx.nonce.toNat} < \
         sender nonce = {senderAccount.nonce.toNat}"
  else if senderAccount.nonce < tx.nonce then
    .error <| .nonceMismatchTooHigh <| .text
      s!"transaction nonce = {tx.nonce.toNat} > \
         sender nonce = {senderAccount.nonce.toNat}"
  else if senderAccount.bal.toNat < maxGasFee + tx.value then
    .error <| .insufficientAccountFunds <| .text
      s!"sender balance = \
         {senderAccount.bal.toNat} < max gas fee = {maxGasFee} + \
         transaction value = {tx.value}"
  else
    checkTransactionSenderCode senderAccount

/-- The whole transaction admission check. Its carrier is the transition union
because it joins two typed channels: every rule above is a
`TxValidationError`, while sender recovery reports on the cryptographic
channel and is the one reason here that is not a validation rule. -/
def checkTransaction (benv : Benv) (blockOut : BlockOutput) (tx : Tx) :
    Except TransitionError (Adr × Nat × List B256 × Nat) := do
  let txBlobGasUsed ←
    Except.mapError .transaction (checkTransactionGasLimits benv blockOut tx)
  Except.mapError TransitionError.transaction (checkTransactionChainId benv tx)
  let senderAddress ←
    Except.mapError .senderRecovery (recoverSender benv.stat.chainId tx)
  let senderAccount := benv.state.get senderAddress
  let ⟨effectiveGasPrice, maxGasFee⟩ ←
    Except.mapError .transaction (checkTransactionGasFee benv tx)
  let ⟨maxGasFee, blobVersionedHashes⟩ ←
    Except.mapError .transaction (checkTransactionBlobData benv tx maxGasFee)
  Except.mapError TransitionError.transaction (checkTransactionReceiver tx)
  Except.mapError TransitionError.transaction (checkTransactionAuthorizationList tx)
  Except.mapError TransitionError.transaction
    (checkTransactionSenderAccount senderAccount tx maxGasFee)
  .ok ⟨
    senderAddress,
    effectiveGasPrice,
    blobVersionedHashes,
    txBlobGasUsed
  ⟩

/-- The transaction's intrinsic cost and its calldata floor.

The five numbers this formula reads that Amsterdam reprices arrive through
`gas` rather than through the globals that used to hold them: the base cost,
the two access-list components, the calldata floor token, and the per-
authorisation intrinsic. `standardCallDataTokenCost` and `initCodeCost` are
untouched by Amsterdam and stay global.

`createCost` reads `gas.createAccess`, the same field the `CREATE` opcodes
read: at Prague the creation transaction's recipient cost and the opcode's
base cost are one number, and EIP-8037 moves both together. -/
def calculateIntrinsicCost (rules : ForkRules) (tx : Tx) (sender : Adr) : Nat × Nat :=
  -- `foldl` (tail-recursive) rather than `(map …).sum`: the latter's
  -- non-tail-recursive `List.map` overflows the stack on large calldata
  -- (e.g. the 1.2 MB inputs in the EIP-2537 stress fixtures).
  let tokensInCalldata : Nat :=
    tx.data.foldl (fun acc x => acc + (if x = 0 then 1 else 4)) 0
  let floorTokensInCalldata : Nat :=
    match rules.stateGas with
    | none => tokensInCalldata
    | some _ => tx.data.length * standardCallDataTokenCost
  let dataCost : Nat :=
    tokensInCalldata * standardCallDataTokenCost
  let recipientCost : Nat :=
      match tx.type.receiver? with
      | none => rules.gas.createAccess
      | some recipient =>
        match rules.stateGas with
        | none => 0
        | some state =>
          if recipient = sender then 0
          else rules.gas.coldAccountAccess + if tx.value = 0 then 0 else state.txValueCost
  let initCost : Nat :=
    if tx.type.receiver?.isNone then initCodeCost tx.data.length else 0
  let accessList :=
    match tx.type with
    | .zero _ _ => []
    | .one _ _ _ accessList => accessList
    | .two _ _ _ _ accessList => accessList
    | .three _ _ _ _ accessList _ _ => accessList
    | .four _ _ _ _ accessList _ => accessList
  let accessListCost : Nat :=
    let accessList :=
      accessList
    let accessItemCost : (Adr × List B256) → Nat
      | ⟨_, keys⟩ =>
        rules.gas.txAccessListAddress + keys.length * rules.gas.txAccessListStorageKey
    let executionCost := (accessList.map accessItemCost).sum
    match rules.stateGas with
    | none => executionCost
    | some state =>
      let floorTokens := accessList.foldl (fun acc item =>
        acc + state.accessListAddressFloorTokens
          + item.2.length * state.accessListStorageKeyFloorTokens) 0
      executionCost + floorTokens * rules.gas.floorTokenCost
  let accessListFloorTokens : Nat :=
    match rules.stateGas with
    | none => 0
    | some state => accessList.foldl (fun acc item =>
        acc + state.accessListAddressFloorTokens
          + item.2.length * state.accessListStorageKeyFloorTokens) 0
  let authCost : Nat :=
    match tx.type with
    | .four _ _ _ _ _ auths => rules.gas.perAuthIntrinsic * auths.length
    | _ => 0
  let baseExecutionGas := rules.gas.txBase + recipientCost
  let floorBaseGas :=
    match rules.stateGas with
    | none => rules.gas.txBase
    | some _ => baseExecutionGas
  let callDataFloorGasCost :=
    (floorTokensInCalldata + accessListFloorTokens) * rules.gas.floorTokenCost
      + floorBaseGas
  ⟨
    baseExecutionGas + initCost + dataCost + accessListCost + authCost,
    callDataFloorGasCost
  ⟩

def checkInitcodeSize (code : CodeLimits) (receiver : Option Adr)
    (dataLength : Nat) : Except TxValidationError Unit :=
  if receiver.isNone && dataLength > code.maxInitCodeSize then
    .error <| .initcodeSizeExceeded <| .text
      s!"initcode is {dataLength} bytes, \
         exceeding the {code.maxInitCodeSize}-byte maximum"
  else
    .ok ()

/-- Enforce the fork's per-transaction gas cap, when one is active. -/
def checkTransactionGasCap (limits : TransactionLimits) (gas : Nat) :
    Except TxValidationError Unit :=
  match limits.maxGas with
  | none => .ok ()
  | some maxGas =>
    if gas > maxGas then
      .error <| .transactionGasLimitExceeded <| .text
        s!"transaction gas = {gas} > \
           maximum = {maxGas}"
    else
      .ok ()

private def checkTransactionPriorityFeeRelation (tx : Tx) :
    Except TxValidationError Unit :=
  let check (priorityFee maxFee : Nat) :=
    if maxFee < priorityFee then
      .error <| .priorityGreaterThanMaxFee <| .text
        s!"priority fee = {priorityFee} > max fee = {maxFee}"
    else .ok ()
  match tx.type with
  | .two _ priorityFee maxFee _ _
  | .three _ priorityFee maxFee _ _ _ _
  | .four _ priorityFee maxFee _ _ _ => check priorityFee maxFee
  | _ => .ok ()

private def checkTransactionBlobShape (rules : ForkRules) (tx : Tx) :
    Except TxValidationError Unit := do
  match tx.type with
  | .three _ _ _ _ _ _ blobHashes =>
    if blobHashes.isEmpty then
      .error <| .type3ZeroBlobs <| .text "no blob hashes in type-3 transaction"
    checkTransactionBlobCount rules.tx blobHashes
    if List.any blobHashes
        (fun hash => hash.toBytes.head? ≠ some versionedHashVersionKzg) then
      .error <| .type3InvalidBlobVersionedHash <| .text
        s!"a blob versioned hash has a version byte other than \
           {versionedHashVersionKzg}"
  | _ => .ok ()

def validateTransaction (rules : ForkRules) (tx : Tx) (sender : Adr) :
    Except TxValidationError (Nat × Nat) := do
  match rules.stateGas with
  | none =>
    let ⟨intrinsicGas, callDataFloorGasCost⟩ :=
      calculateIntrinsicCost rules tx sender
    if max intrinsicGas callDataFloorGasCost > tx.gas then
      .error <| .intrinsicGasTooLow <| .text
        s!"transaction gas = {tx.gas} < \
           max intrinsic/calldata floor cost = \
           {max intrinsicGas callDataFloorGasCost}"
    match rules.tx.maxGas with
    | none =>
      -- Keep Prague's established error precedence byte-for-byte.
      if tx.nonce = UInt64.max then
        .error <| .nonceIsMax <| .text "transaction nonce is 2^64 - 1"
      checkInitcodeSize rules.code tx.type.receiver? tx.data.length
    | some _ =>
      -- Osaka keeps its EIP-7825 whole-transaction cap.
      checkInitcodeSize rules.code tx.type.receiver? tx.data.length
      checkTransactionGasCap rules.tx tx.gas
      if tx.nonce = UInt64.max then
        .error <| .nonceIsMax <| .text "transaction nonce is 2^64 - 1"
    .ok ⟨intrinsicGas, callDataFloorGasCost⟩
  | some _ =>
    -- Amsterdam follows the pinned source order. The structural checks moved
    -- here so their reason precedes intrinsic affordability on multiply-
    -- invalid inputs; the whole-transaction EIP-7825 cap is not applied.
    if tx.nonce = UInt64.max then
      .error <| .nonceIsMax <| .text "transaction nonce is 2^64 - 1"
    checkInitcodeSize rules.code tx.type.receiver? tx.data.length
    checkTransactionPriorityFeeRelation tx
    checkTransactionBlobShape rules tx
    checkTransactionReceiver tx
    checkTransactionAuthorizationList tx
    let ⟨intrinsicGas, callDataFloorGasCost⟩ :=
      calculateIntrinsicCost rules tx sender
    if intrinsicGas > tx.gas then
      .error <| .intrinsicGasTooLow <| .text
        s!"transaction gas = {tx.gas} < intrinsic execution gas = \
           {intrinsicGas}"
    if callDataFloorGasCost > tx.gas then
      .error <| .intrinsicGasTooLow <| .text
        s!"transaction gas = {tx.gas} < intrinsic calldata floor = \
           {callDataFloorGasCost}"
    match rules.tx.maxGas with
    | none => pure ()
    | some maxGas =>
      if intrinsicGas > maxGas then
        .error <| .intrinsicGasTooLow <| .text
          s!"intrinsic execution gas = {intrinsicGas} > maximum = {maxGas}"
      if callDataFloorGasCost > maxGas then
        .error <| .intrinsicGasTooLow <| .text
          s!"intrinsic calldata floor = {callDataFloorGasCost} > maximum = {maxGas}"
    .ok ⟨intrinsicGas, callDataFloorGasCost⟩

/-- The pinned Amsterdam split of post-intrinsic gas into the top frame's
execution grant and its state-gas reservoir. -/
structure EvmGasAllocation : Type where
  executionGas : Nat
  stateGasReservoir : Nat
deriving DecidableEq, Repr

def allocateEvmGas (rules : ForkRules) (txGas intrinsicGas : Nat) :
    EvmGasAllocation :=
  let evmGas := txGas - intrinsicGas
  match rules.stateGas with
  | none => ⟨evmGas, 0⟩
  | some _ =>
    let executionBudget := rules.tx.maxGas.getD txGas - intrinsicGas
    let executionGas := min executionBudget evmGas
    ⟨executionGas, evmGas - executionGas⟩

/-- Gas figures produced once, then consumed by sender refund, block
accounting, and receipt construction. -/
structure TransactionGasSettlement : Type where
  gasUsed : Nat
  gasLeft : Nat
  executionGasUsed : Nat
  stateGasUsed : Nat
deriving DecidableEq, Repr

def settleTransactionGas (rules : ForkRules) (txGas calldataFloor gasLeft
    stateGasLeft refundCounter : Nat) (netStateGasUsed : Int) :
    TransactionGasSettlement :=
  match rules.stateGas with
  | none =>
    let gasUsedBeforeRefund := txGas - gasLeft
    let gasRefund := min (gasUsedBeforeRefund / 5) refundCounter
    let gasUsed := max (gasUsedBeforeRefund - gasRefund) calldataFloor
    ⟨gasUsed, txGas - gasUsed, gasUsed, 0⟩
  | some _ =>
    let gasUsedBeforeRefund := txGas - gasLeft - stateGasLeft
    let gasRefund := min (gasUsedBeforeRefund / 5) refundCounter
    let gasUsed := max (gasUsedBeforeRefund - gasRefund) calldataFloor
    let stateGasUsed := Int.toNat netStateGasUsed
    let executionGasUsed :=
      max (gasUsedBeforeRefund - stateGasUsed) calldataFloor
    ⟨gasUsed, txGas - gasUsed, executionGasUsed, stateGasUsed⟩

/-- On every legacy fork the block execution counter and sender-facing
counter advance together, while the state dimension remains zero. -/
theorem settleTransactionGas_none_invariants {rules : ForkRules}
    (h : rules.stateGas = none) (txGas calldataFloor gasLeft stateGasLeft
      refundCounter : Nat) (netStateGasUsed : Int) :
    let settlement := settleTransactionGas rules txGas calldataFloor gasLeft
      stateGasLeft refundCounter netStateGasUsed
    settlement.executionGasUsed = settlement.gasUsed ∧
      settlement.stateGasUsed = 0 := by
  simp [settleTransactionGas, h]

/-- The actual block-counter update performed after transaction settlement. -/
def BlockOutput.withGasSettlement (bout : BlockOutput)
    (settlement : TransactionGasSettlement) (txBlobGasUsed : Nat) : BlockOutput :=
  {bout with
    blockGasUsed := bout.blockGasUsed + settlement.executionGasUsed
    blockStateGasUsed := bout.blockStateGasUsed + settlement.stateGasUsed
    cumulativeGasUsed := bout.cumulativeGasUsed + settlement.gasUsed
    blobGasUsed := bout.blobGasUsed + txBlobGasUsed}

/-- A settlement whose execution and sender counters agree and whose state
counter is zero preserves the legacy `BlockOutput` relation. -/
theorem BlockOutput.LegacyGasAccounting.withGasSettlement
    {bout : BlockOutput} (hb : bout.LegacyGasAccounting)
    {settlement : TransactionGasSettlement}
    (hs : settlement.executionGasUsed = settlement.gasUsed ∧
      settlement.stateGasUsed = 0) (txBlobGasUsed : Nat) :
    (bout.withGasSettlement settlement txBlobGasUsed).LegacyGasAccounting := by
  unfold BlockOutput.LegacyGasAccounting at hb ⊢
  simp only [BlockOutput.withGasSettlement]
  omega

def prepareMessage (benv: Benv) (tenv: Tenv) (tx: Tx) :
  Except TransitionError Msg := do
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
    stateGasGrant := tenv.stat.stateGasReservoir
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
  (error: Option SettledHalt)
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
    blockStateGasUsed := 0
    cumulativeGasUsed := 0
    transactionsTrie := .empty
    receiptsTrie := .empty
    receiptKeys := []
    blockLogs := []
    withdrawalsTrie := .empty
    blobGasUsed := 0
    requests := []
  }

theorem BlockOutput.init_legacyGasAccounting :
    BlockOutput.init.LegacyGasAccounting := by
  simp [BlockOutput.init, BlockOutput.LegacyGasAccounting]

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

/-- The sender the Amsterdam intrinsic-cost formula needs before
`checkTransaction` runs. The pinned `process_transaction` compares the
transaction's own chain identifier with the block's (`WrongChainIdError`)
*before* `check_transaction` recovers the sender, so a legacy transaction
signed for another chain is refused for its chain identifier, not for its
signature; the check is repeated here ahead of recovery for that reason (the
`none` lane keeps its own order inside `checkTransaction`). -/
private def recoverValidationSender (benv : Benv) (tx : Tx) :
    Except TransitionError Adr :=
  match benv.stat.rules.stateGas with
  | none => .ok 0
  | some _ => do
    Except.mapError TransitionError.transaction (checkTransactionChainId benv tx)
    Except.mapError (fun e => TransitionError.senderRecovery e)
      (recoverSender benv.stat.chainId tx)

/-- Amsterdam SELFDESTRUCT settlement clears account data but preserves the
beneficiary-independent balance retained by EIP-6780. -/
def clearAccountPreservingBalance (state : State) (address : Adr) : State :=
  let account := state.get address
  state.set address {account with nonce := 0, code := .empty, stor := .empty}

/-- Select the fork's SELFDESTRUCT settlement semantics once, outside the
transaction proof's monadic spine. -/
def settleSelfdestructs (rules : ForkRules) (addresses : List Adr)
    (state : State) : State :=
  match rules.stateGas with
  | none => addresses.foldl destroyAccount state
  | some _ => addresses.foldl clearAccountPreservingBalance state


def processTransaction
  (benv: Benv) (bout : BlockOutput)
  (tx: Tx) (index : Nat) : Except TransitionError (State × BlockOutput) := do
  -- NOTE: linearized into a straight `let ← .ok (…)` / `let := …` chain
  -- (no `mut`/`for`) so the block inverts cleanly with `of_bind_eq_ok` and the
  -- `bout` bookkeeping stays opaque.  Definitionally equal to the previous
  -- `mut`/`for` form except that the final account-deletion `for` is expressed
  -- as `foldl`, which agrees because `destroyAccount` commutes over the
  -- distinct addresses of the `accountsToDelete` set.
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
  let ⟨state, txOutput⟩ ← Except.mapError TransitionError.vm (processMessageCall msg)
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
  let state := state.addBal benv.stat.coinbase transactionFee.toB256
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
  -- self-destruct settlement: the transaction's writes as a diff against the
  -- block's cumulative state, plus its reads and the transaction-level ones --
  -- the sender (`check_transaction`, `update_sender_state`, the refund) and
  -- the coinbase (`disburse_gas_fees` credits it even a zero fee).
  let bal := match benv.stat.rules.bal with
    | none => bout.bal
    | some _ => bout.bal.incorporate (index + 1) benv.state state
        (sender :: benv.stat.coinbase :: txOutput.accountReads.toList)
        txOutput.storageReads.toList
  .ok ⟨state, {bout with bal := bal}⟩

/-- Under a legacy schedule, the real transaction producer preserves the
legacy block-counter relation through its settlement and receipt updates. -/
theorem processTransaction_legacyGasAccounting {benv : Benv}
    (hnone : benv.stat.rules.stateGas = none) {bout : BlockOutput}
    (hb : bout.LegacyGasAccounting) {tx : Tx} {index : Nat} {p}
    (hp : processTransaction benv bout tx index = .ok p) :
    p.2.LegacyGasAccounting := by
  unfold processTransaction at hp
  obtain ⟨b1, hb1, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨validationSender, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨ig, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨ck, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨st1, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨msg, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨rc, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨b2, hb2, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨b3, hb3, hp⟩ := Except.bind_eq_ok hp
  simp only [Except.ok.injEq] at hb1 hb2 hb3
  have hb1' : b1.LegacyGasAccounting := by
    rw [← hb1]
    exact hb
  have hb2' : b2.LegacyGasAccounting := by
    rw [← hb2]
    exact BlockOutput.LegacyGasAccounting.withGasSettlement hb1'
      (settleTransactionGas_none_invariants hnone _ _ _ _ _ _) _
  have hb3' : b3.LegacyGasAccounting := by
    rw [← hb3]
    exact hb2'
  cases hp
  exact hb3'

def BlockOutput.withWithdrawalsTrie
    (bo : BlockOutput) (tr : Std.TreeMap Bytes Withdrawal compare) : BlockOutput :=
  {bo with withdrawalsTrie := tr}

theorem BlockOutput.LegacyGasAccounting.withWithdrawalsTrie
    {bout : BlockOutput} (hb : bout.LegacyGasAccounting)
    (tr : Std.TreeMap Bytes Withdrawal compare) :
    (bout.withWithdrawalsTrie tr).LegacyGasAccounting := hb

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

theorem processWithdrawals_legacyGasAccounting {benv : Benv}
    {bout : BlockOutput} (hb : bout.LegacyGasAccounting)
    (wds : List Withdrawal) :
    (processWithdrawals benv bout wds).2.LegacyGasAccounting := by
  unfold processWithdrawals
  exact hb.withWithdrawalsTrie _

-- Access lists, blob hashes, and authorization tuples arrive inside typed
-- transactions, so their fields are untrusted in exactly the way withdrawal
-- fields are: every shape must be checked before any truncating conversion,
-- and a wrong list shape is a different reason from an oversized scalar.

def BLT.toExStorageKey : BLT → Except DecodeError B256
  | .bytes xs => xs.toRlpHash "access list storage key"
  | .list _ =>
    .error <| DecodeError.structure "access list storage key"
      "expected a byte-string item"

def BLT.toExAccessItem : BLT → Except DecodeError (Adr × List B256)
  | .list [.bytes ar, .list ksr] => do
    let a ← ar.toRlpAdr "access list address"
    let ks ← List.mapM BLT.toExStorageKey ksr
    .ok ⟨a, ks⟩
  | _ =>
    .error <| DecodeError.structure "access list item"
      "expected [address, [storage key, ...]]"

def BLT.toExAccessList : BLT → Except DecodeError AccessList
  | .list rs => List.mapM BLT.toExAccessItem rs
  | .bytes _ =>
    .error <| DecodeError.structure "access list" "expected a list item"

def BLT.toExBlobHash : BLT → Except DecodeError B256
  | .bytes xs => xs.toRlpHash "blob versioned hash"
  | .list _ =>
    .error <| DecodeError.structure "blob versioned hash"
      "expected a byte-string item"

def BLT.toExAuth : BLT → Except DecodeError Auth
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
    .error <| DecodeError.structure "authorization"
      "expected a list of six byte-string fields"

/-- Strict authorisation-decoder soundness. -/
theorem BLT.toExAuth_wireWellFormed {blt : BLT} {a : Auth}
    (h : blt.toExAuth = .ok a) : a.WireWellFormed := by
  unfold BLT.toExAuth at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    exact Bytes.toRlpNat_lt_two_pow_256 (by assumption)
  · exact absurd h (by simp)

/-- The strict field decoders, lifted to the transaction-decode carrier. Every
per-field reason stays a `DecodeError`; this wrapper only names the channel. -/
private def dec {α : Type} : Except DecodeError α → Except TransitionError α :=
  Except.mapError TransitionError.decode

private theorem dec_eq_ok {α : Type} {x : Except DecodeError α} {a : α}
    (h : dec x = .ok a) : x = .ok a := Except.mapError_eq_ok_iff.mp h

def Bytes.toExTx : Bytes → Except TransitionError Tx
  | [] =>
    .error <| .decode <| DecodeError.structure "typed transaction"
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
      let chainId ← dec <| chainId.toRlpB64 "type-1 transaction chainId"
      let nonce ← dec <| nonce.toRlpB64 "type-1 transaction nonce"
      let gasPrice ← dec <| gasPrice.toRlpNat "type-1 transaction gasPrice" 32
      let gas ← dec <| gas.toRlpNat "type-1 transaction gas" 32
      let receiver ← dec <| receiver.toRlpReceiver "type-1 transaction receiver"
      let value ← dec <| value.toRlpNat "type-1 transaction value" 32
      let accessList ← dec accessList.toExAccessList
      let yParity ← dec <| yParity.toRlpNat "type-1 transaction yParity" 32
      let _ ← dec <| r.toRlpB256 "type-1 transaction r"
      let _ ← dec <| s.toRlpB256 "type-1 transaction s"
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
      .error <| .decode <| DecodeError.structure "type-1 transaction"
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
      let chainId ← dec <| chainId.toRlpB64 "type-2 transaction chainId"
      let nonce ← dec <| nonce.toRlpB64 "type-2 transaction nonce"
      let maxPriorityFee ← dec <| maxPriorityFee.toRlpNat "type-2 transaction maxPriorityFee" 32
      let maxFee ← dec <| maxFee.toRlpNat "type-2 transaction maxFee" 32
      let gas ← dec <| gas.toRlpNat "type-2 transaction gas" 32
      let receiver ← dec <| receiver.toRlpReceiver "type-2 transaction receiver"
      let value ← dec <| value.toRlpNat "type-2 transaction value" 32
      let accessList ← dec accessList.toExAccessList
      let yParity ← dec <| yParity.toRlpNat "type-2 transaction yParity" 32
      let _ ← dec <| r.toRlpB256 "type-2 transaction r"
      let _ ← dec <| s.toRlpB256 "type-2 transaction s"
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
      .error <| .decode <| DecodeError.structure "type-2 transaction"
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
      let chainId ← dec <| chainId.toRlpB64 "type-3 transaction chainId"
      let nonce ← dec <| nonce.toRlpB64 "type-3 transaction nonce"
      let maxPriorityFee ← dec <| maxPriorityFee.toRlpNat "type-3 transaction maxPriorityFee" 32
      let maxFee ← dec <| maxFee.toRlpNat "type-3 transaction maxFee" 32
      let gas ← dec <| gas.toRlpNat "type-3 transaction gas" 32
      -- A type-3 receiver is a mandatory address at the RLP level; the
      -- semantic contract-creation rejection downstream remains as defense
      -- in depth for transactions that arrive already decoded.  Empty is the
      -- official type-3 contract-creation failure, while a nonempty value of
      -- any width other than twenty bytes remains an RLP shape failure.
      if receiver.isEmpty then
        .error <| .transaction <| .type3ContractCreation <|
          .text "type-3 transaction receiver is empty"
      let receiver ← dec <| receiver.toRlpAdr "type-3 transaction receiver"
      let value ← dec <| value.toRlpNat "type-3 transaction value" 32
      let accessList ← dec accessList.toExAccessList
      let maxBlobFee ← dec <| maxBlobFee.toRlpNat "type-3 transaction maxBlobFee" 32
      let blobHashes ← dec <| List.mapM BLT.toExBlobHash blobHashes
      let yParity ← dec <| yParity.toRlpNat "type-3 transaction yParity" 32
      let _ ← dec <| r.toRlpB256 "type-3 transaction r"
      let _ ← dec <| s.toRlpB256 "type-3 transaction s"
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
      .error <| .decode <| DecodeError.structure "type-3 transaction"
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
      let chainId ← dec <| chainId.toRlpB64 "type-4 transaction chainId"
      let nonce ← dec <| nonce.toRlpB64 "type-4 transaction nonce"
      let maxPriorityFee ← dec <| maxPriorityFee.toRlpNat "type-4 transaction maxPriorityFee" 32
      let maxFee ← dec <| maxFee.toRlpNat "type-4 transaction maxFee" 32
      let gas ← dec <| gas.toRlpNat "type-4 transaction gas" 32
      if receiver.isEmpty then
        .error <| .transaction <| .type4ContractCreation <|
          .text "type-4 transaction receiver is empty"
      let receiver ← dec <| receiver.toRlpAdr "type-4 transaction receiver"
      let value ← dec <| value.toRlpNat "type-4 transaction value" 32
      let accessList ← dec accessList.toExAccessList
      let auths ← dec <| List.mapM BLT.toExAuth auths
      let yParity ← dec <| yParity.toRlpNat "type-4 transaction yParity" 32
      let _ ← dec <| r.toRlpB256 "type-4 transaction r"
      let _ ← dec <| s.toRlpB256 "type-4 transaction s"
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
      .error <| .decode <| DecodeError.structure "type-4 transaction"
        "expected a list of thirteen fields"
    -- An unknown envelope type has no reviewed fixture identity
    -- (`TYPE_NOT_SUPPORTED` is outside this build's vocabulary), and its
    -- message has carried the internal tag since inception -- it was never
    -- classifiable. It stays a typed internal reason and fails closed; naming
    -- the identity would be an explicit vocabulary extension, not a default.
    | x, _ =>
      .error <| .internal <| .invariant <|
        .text s!"type-{x} txs do not exist, decoding failed"

/-- Strict typed-transaction-decoder soundness. Every transaction the typed
envelope decoder produces satisfies `Tx.WireWellFormed`, for each of the four
implemented envelope types. Together with `BLT.toExLegacyTx_wireWellFormed`
below this is what makes the structural predicate a lift of the decoders. -/
theorem Bytes.toExTx_wireWellFormed {xs : Bytes} {tx : Tx}
    (h : xs.toExTx = .ok tx) : tx.WireWellFormed := by
  unfold Bytes.toExTx at h
  split at h
  · exact absurd h (by simp)
  · split at h
    -- type 1 (EIP-2930)
    · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first
          | exact Bytes.toRlpNat_lt_two_pow_256 (dec_eq_ok (by assumption))
          | exact Bytes.toRlpB256_eq_ok (dec_eq_ok (by assumption))
    · exact absurd h (by simp)
    -- type 2 (EIP-1559)
    · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first
          | exact Bytes.toRlpNat_lt_two_pow_256 (dec_eq_ok (by assumption))
          | exact Bytes.toRlpB256_eq_ok (dec_eq_ok (by assumption))
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
            | exact Bytes.toRlpNat_lt_two_pow_256 (dec_eq_ok (by assumption))
            | exact Bytes.toRlpB256_eq_ok (dec_eq_ok (by assumption))
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
          obtain ⟨blt, hblt⟩ :=
            List.mapM_except_eq_ok_mem (dec_eq_ok (by assumption)) a ha
          exact BLT.toExAuth_wireWellFormed hblt
        all_goals
          first
            | exact Bytes.toRlpNat_lt_two_pow_256 (dec_eq_ok (by assumption))
            | exact Bytes.toRlpB256_eq_ok (dec_eq_ok (by assumption))
    · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- Decode a block-body transaction slot: opaque typed-envelope bytes through
the strict envelope decoder, an already-decoded legacy slot as itself. The
`.inr` arm is not a bypass on the checked path: `CanonicalBlock.decodeTx_inr`
certifies what it returns there. -/
def decodeTx : Bytes ⊕ Tx → Except TransitionError Tx
  | .inl xs => xs.toExTx
  | .inr tx => .ok tx


def processSystemTransactionTenv (benv : Benv) : Tenv :=
  {
    transientStorage := .empty,
    stat := {
      origin := systemAddress,
      gasPrice := benv.stat.baseFeePerGas,
      gas := systemTransactionGas,
      stateGasReservoir :=
        match benv.stat.rules.stateGas with
        | none => 0
        | some state => state.systemReservoir
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
    accessedAddresses :=
      match benv.stat.rules.stateGas with
      | none => .emptyWithCapacity
      | some _ =>
        (.emptyWithCapacity : AdrSet).insertMany
          (benv.stat.rules.precompiles ++ [systemAddress, target]),
    accessedStorageKeys := .emptyWithCapacity,
    disablePrecompiles := false
    stateGasGrant := tenv.stat.stateGasReservoir
  }

#guard (processSystemTransactionTenv
    fixtureAmsterdamBenv).stat.stateGasReservoir
  = amsterdamStateGasRules.systemReservoir
#guard (processSystemTransactionMsg fixtureAmsterdamBenv
    (processSystemTransactionTenv fixtureAmsterdamBenv) 1 [] .empty).stateGasGrant
  = amsterdamStateGasRules.systemReservoir

-- The single boundary shared by all four system transactions (beacon roots,
-- history storage, withdrawal requests, consolidation requests), so each takes
-- its own input state as the original state.
def processSystemTransaction (benv : Benv)
  (target : Adr) (code : ByteArray) (data : Bytes) :
  Except EvmError (State × MsgCallOutput) := do
  let benv := benv.beginTransaction
  let txEnv : Tenv := processSystemTransactionTenv benv
  let systemTxMsg : Msg :=
    processSystemTransactionMsg benv txEnv target data code
  processMessageCall systemTxMsg

def extractDepositData (data : Bytes) : Except BlockValidationError Bytes := do
  if data.length != depositEventLength then
    .error (.depositEventLayout (.text "invalid deposit event data length"))
  if data.sliceToNat 0 32 ≠ pubkeyOffset then
    .error (.depositEventLayout (.text "invalid pubkey offset in deposit log"))
  if data.sliceToNat 32 32 ≠ withdrawalCredentialsOffset then
    .error (.depositEventLayout (.text "invalid withdrawal credentials offset in deposit log"))
  if data.sliceToNat 64 32 ≠ amountOffset then
    .error (.depositEventLayout (.text "invalid amount offset in deposit log"))
  if data.sliceToNat 96 32 ≠ signatureOffset then
    .error (.depositEventLayout (.text "invalid signature offset in deposit log"))
  if data.sliceToNat 128 32 ≠ indexOffset then
    .error (.depositEventLayout (.text "invalid index offset in deposit log"))
  if data.sliceToNat pubkeyOffset 32 ≠ pubkeySize then
    .error (.depositEventLayout (.text "invalid pubkey size in deposit log"))
  let pubkey : Bytes := data.slice! (pubkeyOffset + 32) pubkeySize
  if data.sliceToNat withdrawalCredentialsOffset 32 ≠ withdrawalCredentialsSize then
    .error (.depositEventLayout (.text "invalid withdrawal credentials size in deposit log"))
  let withdrawalCredentials : Bytes :=
    data.slice! (withdrawalCredentialsOffset + 32) withdrawalCredentialsSize
  if data.sliceToNat amountOffset 32 ≠ amountSize then
    .error (.depositEventLayout (.text "invalid amount size in deposit log"))
  let amount : Bytes := data.slice! (amountOffset + 32) amountSize
  if data.sliceToNat signatureOffset 32 ≠ signatureSize then
    .error (.depositEventLayout (.text "invalid signature size in deposit log"))
  let signature : Bytes := data.slice! (signatureOffset + 32) signatureSize
  if data.sliceToNat indexOffset 32 ≠ indexSize then
    .error (.depositEventLayout (.text "invalid index size in deposit log"))
  let index : Bytes := data.slice! (indexOffset + 32) indexSize
  .ok (pubkey ++ withdrawalCredentials ++ amount ++ signature ++ index)

def parseDepositRequests
  (bout : BlockOutput) : Except TransitionError Bytes := do
  let mut depositRequests : Bytes := []
  for key in bout.receiptKeys do
    let ⟨_, receipt⟩  ←
      bout.receiptsTrie[key]?.toExcept
        (TransitionError.internal (.invariant (.text "receipt not found")))
    for log in receipt.logs do
      if (
        log.address = depositContractAddress ∧
        log.topics[0]? = some depositEventSignatureHash
      ) then
        let request ← Except.mapError TransitionError.block (extractDepositData log.data)
        depositRequests := depositRequests ++ request
  .ok depositRequests

def processUncheckedSystemTransaction
  (benv : Benv) (target : Adr) (data : Bytes) :
  Except EvmError (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  processSystemTransaction benv target systemContractCode data

def processCheckedSystemTransaction
  (benv : Benv) (target : Adr) (data : Bytes) :
  Except TransitionError (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  -- A mis-provisioned chain: the mandatory system contract holds no code. The
  -- pinned `process_checked_system_transaction` raises `InvalidBlock` here,
  -- before attempting the call, and the corpus names the reason
  -- `BlockException.SYSTEM_CONTRACT_EMPTY`; it is a block rejection with its
  -- own typed reason and its own fixture identity. (Until goal D this arm was
  -- a fail-closed *internal* invariant, with the note that the identity was
  -- "outside this build's reviewed vocabulary" and "unobserved in every
  -- corpus"; the Glamsterdam devnet transition corpus observes it in the four
  -- `deploy_after_fork` cases of `eip8282_…/test_contract_deployment.py`, so
  -- the reason is rewritten to the block channel -- goal D, packet DP-2,
  -- owner-approved.)
  if systemContractCode.isEmpty then
    .error <| .block <| .systemContractEmpty <| .text
      s!"system contract address {target.toHex} holds no code"
  let ⟨state, systemTxOutput⟩ ←
    Except.mapError TransitionError.vm
      (processSystemTransaction benv target systemContractCode data)
  -- P0.6 item 3: the failure text is extracted by the total match, never by a
  -- partial projection out of the optional error field.
  match systemTxOutput.error with
  | some err =>
    .error <| .block <| .systemContractCallFailed <| .text
      s!"system contract ({target.toHex}) call failed: \
      {err.render}"
  | none => .ok ⟨state, systemTxOutput⟩

/-- Call each request-producing system contract in turn, threading the state.

Structural recursion on the contract list rather than a loop, so that the
invariant proofs are an induction on that list instead of a fixed number of
nested case splits -- which is what makes adding Amsterdam's two contracts a
change to data and to nothing else. Each contract's non-empty return data is
appended prefixed with its own type byte, and the state each call produces is
what the next call runs against. -/
def runRequestContracts (idx : Nat) :
    List (UInt8 × Adr) → Benv → List Bytes → BalBuilder →
      Except TransitionError (State × List Bytes × BalBuilder)
  | [], benv, acc, bal => .ok ⟨benv.state, acc, bal⟩
  | ⟨requestType, address⟩ :: rest, benv, acc, bal => do
    let ⟨state, output⟩ ← processCheckedSystemTransaction benv address []
    let acc :=
      if output.returnData.length > 0 then
        acc ++ [[requestType] ++ output.returnData]
      else
        acc
    -- EIP-7928: each checked call incorporates its own writes and reads at
    -- the post-execution index; `create_evm` read the contract's account.
    let bal := match benv.stat.rules.bal with
      | none => bal
      | some _ => bal.incorporate idx benv.state state
          (address :: output.accountReads.toList) output.storageReads.toList
    runRequestContracts idx rest (benv.withState state) acc bal

/-- Run the block's request-producing system contracts and collect their output.

The contracts come from `rules.requests` -- an ordered list of
`(type byte, address)` pairs -- and this is a fold over it rather than a
sequence of named calls. The order is the rule: the request bytes are
concatenated in call order and hashed into `requestsHash`, so calling the same
contracts in a different order is a different block. Amsterdam appends two more
entries (EIP-8282's builder deposit and exit), and appending to a list is the
whole change; nothing here learns their names.

The receipt-derived deposit request stays where it is, ahead of the fold and
outside the list. It is parsed out of the block's logs rather than produced by
a system call, so it is not one of these contracts -- which is also why the
rule data does not carry a type-0 entry.

`pragueRules.requests` reproduces exactly the two calls, in the order, this
function made before the list existed: `pragueRules_requests` in
`Jaune/Machine.lean` states that by `rfl`, and a `#guard` below runs it. -/
def processGeneralPurposeRequestsAt (balIndex : Nat)
  (benv : Benv) (bout : BlockOutput) :
  Except TransitionError (State × BlockOutput) := do
  let depositRequests ← parseDepositRequests bout
  let seeded : List Bytes :=
    if depositRequests.length > 0 then
      bout.requests ++ [depositRequestType ++ depositRequests]
    else
      bout.requests
  let ⟨state, allRequests, bal⟩ ←
    runRequestContracts balIndex benv.stat.rules.requests benv seeded bout.bal
  .ok ⟨state, {bout with requests := allRequests, bal := bal}⟩

/-- The block pipeline's request pass. EIP-7928: post-execution operations use
index `n + 1`, `n` the number of transactions -- one receipt key each, since a
block whose transaction is rejected is itself rejected. The transition tool,
whose driver counts the transactions it was handed, calls
`processGeneralPurposeRequestsAt` with its own count. -/
def processGeneralPurposeRequests (benv : Benv) (bout : BlockOutput) :
    Except TransitionError (State × BlockOutput) :=
  processGeneralPurposeRequestsAt (bout.receiptKeys.length + 1) benv bout

theorem processGeneralPurposeRequests_legacyGasAccounting {benv : Benv}
    {bout : BlockOutput} (hb : bout.LegacyGasAccounting) {p}
    (hp : processGeneralPurposeRequests benv bout = .ok p) :
    p.2.LegacyGasAccounting := by
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact hb

def applyTransactions :
    List (Nat × Tx) → Benv → BlockOutput → Except TransitionError (Benv × BlockOutput)
  | [], benv, bout => .ok (benv, bout)
  | ⟨i, tx⟩ :: txis, benv , bout => do
    let ⟨st, bout'⟩ ← processTransaction benv bout tx i
    applyTransactions txis (benv.withState st) bout'

/-- The actual transaction-list fold preserves the legacy block counters at
every successful iteration. -/
theorem applyTransactions_legacyGasAccounting :
    ∀ (txis : List (Nat × Tx)) {benv : Benv},
      benv.stat.rules.stateGas = none →
      ∀ {bout : BlockOutput} {p}, bout.LegacyGasAccounting →
        applyTransactions txis benv bout = .ok p → p.2.LegacyGasAccounting
  | [], _, _, _, _, hb, hp => by cases hp; exact hb
  | txi :: txis, benv, hnone, bout, p, hb, hp => by
    unfold applyTransactions at hp
    obtain ⟨⟨st, bout'⟩, hq, hp⟩ := Except.bind_eq_ok hp
    exact applyTransactions_legacyGasAccounting txis
      (benv := benv.withState st) hnone
      (processTransaction_legacyGasAccounting hnone hb hq) hp

/-- Starting from the producer's real initializer discharges the initial
legacy relation required by the iteration theorem. -/
theorem applyTransactions_init_legacyGasAccounting
    (txis : List (Nat × Tx)) {benv : Benv}
    (hnone : benv.stat.rules.stateGas = none) {p}
    (hp : applyTransactions txis benv .init = .ok p) :
    p.2.LegacyGasAccounting :=
  applyTransactions_legacyGasAccounting txis hnone
    BlockOutput.init_legacyGasAccounting hp

/-- EIP-7928: incorporate one pre-execution or post-execution system operation
-- a system call's writes and reads plus the contract account `create_evm`
read, or the withdrawals batch's credits plus each recipient `create_ether`
read -- at `idx`, under rules that carry a block-level access list. -/
def BalBuilder.incorporateSystem (bal : BalBuilder) (rules : ForkRules) (idx : Nat)
    (pre post : State) (accountReads : List Adr) (storageReads : List (Adr × B256)) :
    BalBuilder :=
  match rules.bal with
  | none => bal
  | some _ => bal.incorporate idx pre post accountReads storageReads

/-- `validate_block_access_list_gas_limit`, inside `apply_body` before any
header comparison: `items > gasLimit // itemCost` is a block rejection. -/
def checkBlockAccessListGasLimit (rules : ForkRules) (blockGasLimit : Nat)
    (list : BlockAccessList) : Except TransitionError Unit :=
  match rules.bal with
  | none => .ok ()
  | some r =>
    if list.itemCount > blockGasLimit / r.itemCost then
      .error <| .block <| .blockAccessListGasLimit <| .text
        s!"block access list holds {list.itemCount} items, exceeding \
           gasLimit / itemCost = {blockGasLimit / r.itemCost}"
    else .ok ()

def applyBody
  (benv : Benv) (txs : List (Bytes ⊕ Tx)) (wds : List Withdrawal) :
  Except TransitionError (State × BlockOutput) := do
  let ⟨stBeacon, outBeacon⟩ ←
    Except.mapError TransitionError.vm <|
      processUncheckedSystemTransaction benv
        beaconRootsAddress
        benv.stat.parentBeaconBlockRoot.toBytes
  -- EIP-7928: the two pre-execution system calls incorporate at index 0.
  let bal := BalBuilder.incorporateSystem {} benv.stat.rules 0 benv.state stBeacon
    (beaconRootsAddress :: outBeacon.accountReads.toList) outBeacon.storageReads.toList
  let benvBeacon : Benv := benv.withState stBeacon
  let lastHash ←
     benvBeacon.stat.blockHashes.getLast?.toExcept
       (TransitionError.internal (.invariant (.text "block hashes is empty")))
  let ⟨stHistory, outHistory⟩ ←
    Except.mapError TransitionError.vm <|
      processUncheckedSystemTransaction benvBeacon
        historyStorageAddress
        lastHash.toBytes
  let bal := bal.incorporateSystem benv.stat.rules 0 benvBeacon.state stHistory
    (historyStorageAddress :: outHistory.accountReads.toList) outHistory.storageReads.toList
  let benvHistory := benvBeacon.withState stHistory
  let ⟨benvTxs, boutTxs⟩ ←
    applyTransactions (← txs.mapM decodeTx).putIndex benvHistory {BlockOutput.init with bal := bal}
  let ⟨stWds, boutWds⟩ :=
    processWithdrawals benvTxs boutTxs wds
  -- EIP-7928: the withdrawals batch is one incorporation at `n + 1`; every
  -- recipient is read by `create_ether` whatever the amount.
  let balWds := boutWds.bal.incorporateSystem benv.stat.rules
    (boutTxs.receiptKeys.length + 1) benvTxs.state stWds (wds.map Withdrawal.recipient) []
  let boutWds := {boutWds with bal := balWds}
  let ⟨stReq, boutReq⟩ ← processGeneralPurposeRequests (benvTxs.withState stWds) boutWds
  -- `build_block_access_list`, then the item rule -- before any header check.
  let list := match benv.stat.rules.bal with
    | none => []
    | some _ => boutReq.bal.build
  checkBlockAccessListGasLimit benv.stat.rules benv.stat.blockGasLimit list
  .ok ⟨stReq, {boutReq with blockAccessList := list}⟩

/-- A successful legacy block body starts from `BlockOutput.init`, preserves
the relation through every transaction, and keeps it through withdrawals and
the request pass. -/
theorem applyBody_legacyGasAccounting {benv : Benv}
    (hnone : benv.stat.rules.stateGas = none)
    {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal} {p}
    (hp : applyBody benv txs wds = .ok p) : p.2.LegacyGasAccounting := by
  unfold applyBody at hp
  obtain ⟨q1, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q2, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨txsD, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  -- The initial output is `.init` with the two system calls' access-list
  -- incorporation; the relation reads none of that.
  have hqLegacy : q.2.LegacyGasAccounting :=
    applyTransactions_legacyGasAccounting txsD.putIndex
      (benv := (benv.withState q1.1).withState q2.1) hnone
      (by simp [BlockOutput.LegacyGasAccounting, BlockOutput.init]) hq
  obtain ⟨benvTxs, boutTxs⟩ := q
  dsimp only at hp hqLegacy
  rcases hw : processWithdrawals benvTxs boutTxs wds with ⟨stWds, boutWds⟩
  simp only [hw] at hp
  have hwLegacy := processWithdrawals_legacyGasAccounting
    (benv := benvTxs) hqLegacy wds
  simp only [hw] at hwLegacy
  -- The withdrawals' access-list incorporation, the request pass, the item
  -- rule and the built list touch no gas counter.
  obtain ⟨q', hq', hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  let balWds := boutWds.bal.incorporateSystem benv.stat.rules
    (boutTxs.receiptKeys.length + 1) benvTxs.state stWds (wds.map Withdrawal.recipient) []
  have hreq := processGeneralPurposeRequests_legacyGasAccounting
    (bout := {boutWds with bal := balWds}) hwLegacy hq'
  exact hreq

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

/-- The absolute upper bound on a block gas limit. A gas limit is a 63-bit
quantity: `2 ^ 63` and above is out of range no matter what the parent's limit
was, which is why the fixtures name it separately from a limit that merely
moved too far from its parent. -/
def gasLimitMaximum : Nat := 2 ^ 63

/-- Check a block's gas limit against the absolute bound and against its
parent, reporting *which* rule failed.

Relocated from `Jaune/Execution.lean` by Step 10, with `calculateBaseFeePerGas`
and `validateHeader` below: their reasons are `BlockValidationError`
constructors, whose frozen home is this module (design report §6), and their
only consumer is `stateTransitionAt`'s core here -- the same
producer-follows-type relocation Step 9 recorded for the BLS decoders.

The absolute bound is tested first, and that order is the point: a limit just
above `2 ^ 63` can still sit inside the parent-relative window (it does exactly
that when the parent's limit is `2 ^ 63 - 1`), so testing the window first would
report the adjustment rule for a block whose real defect is an out-of-range gas
limit -- the right verdict for the wrong reason. -/
def checkGasLimit (gasLimit parentGasLimit : Nat) :
    Except BlockValidationError Unit := do
  if gasLimit ≥ gasLimitMaximum then
    .error <| .gasLimitTooBig <| .text
      s!"gas limit = {gasLimit} ≥ \
         absolute maximum = {gasLimitMaximum}"
  let maxAdjustmentDelta := parentGasLimit / gasLimitAdjustmentFactor
  if gasLimit ≥ parentGasLimit + maxAdjustmentDelta then
    .error <| .gasLimitAdjustment <| .text
      s!"gas limit = {gasLimit} ≥ parent gas limit \
         = {parentGasLimit} + max adjustment delta = {maxAdjustmentDelta}"
  if gasLimit ≤ parentGasLimit - maxAdjustmentDelta then
    .error <| .gasLimitAdjustment <| .text
      s!"gas limit = {gasLimit} ≤ parent gas limit \
         = {parentGasLimit} - max adjustment delta = {maxAdjustmentDelta}"
  if gasLimit < gasLimitMinimum then
    .error <| .gasLimitAdjustment <| .text
      s!"gas limit = {gasLimit} < \
         minimum = {gasLimitMinimum}"

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

def calculateBaseFeePerGas
  (blockGasLimit parentGasLimit parentGasUsed parentBaseFeePerGas : Nat) :
  Except BlockValidationError Nat := do
  let parentGasTarget := parentGasLimit / elasticityMultiplier
  checkGasLimit blockGasLimit parentGasLimit
  if parentGasUsed = parentGasTarget
  then .ok parentBaseFeePerGas
  else
    if parentGasUsed > parentGasTarget
    then
      let gasUsedDelta := parentGasUsed - parentGasTarget
      let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
      let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
      let baseFeePerGasDelta :=
        max (targetFeeGasDelta / baseFeeMaxChangeDenominator) 1
      .ok <| parentBaseFeePerGas + baseFeePerGasDelta
    else
      let gasUsedDelta := parentGasTarget - parentGasUsed
      let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
      let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
      let baseFeePerGasDelta :=
        targetFeeGasDelta / baseFeeMaxChangeDenominator
      .ok <| parentBaseFeePerGas - baseFeePerGasDelta

def validateHeader (rules : ForkRules) (chain : BlockChain) (header : Header) :
  Except TransitionError Unit := do
  -- An empty snapshot names no parent to validate against. The runner can
  -- never supply one (a checked snapshot is nonempty by construction), so
  -- this is a caller-context invariant breach, typed internal and fail-closed
  -- -- never a candidate verdict. Step 10 replaced the untagged legacy string
  -- "No parent block found" here; the arm is unobserved in every corpus.
  let parent ← chain.blocks.getLast?.toExcept
    (.internal (.invariant (.text "no parent block found")))
  let blockParentHash := (Header.toBLT parent.header).toBytes.keccak
  -- Parentage is settled first. Every check below reads the parent's header, so
  -- a block naming a parent this chain does not end with is not a block with a
  -- bad timestamp or a bad base fee -- it is a block that cannot be placed at
  -- all, and reporting any later rule for it would name the wrong defect. The
  -- all-zero hash is called out separately because it names no block at all,
  -- rather than naming some block this chain has not got.
  if header.parentHash ≠ blockParentHash then do
    if header.parentHash = 0 then
      .error <| .block <| .unknownParentZero <| .text
        s!"parent hash is the all-zero hash, \
           which names no block"
    .error <| .block <| .unknownParent <| .text
      s!"parent hash = {header.parentHash} names no known \
         block; this chain ends at {blockParentHash}"
  let expectedBaseFeePerGas ←
    Except.mapError TransitionError.block <|
      calculateBaseFeePerGas
        header.gasLimit
        parent.header.gasLimit
        parent.header.gasUsed
        parent.header.baseFeePerGas
  if header.excessBlobGas ≠ calculateExcessBlobGas rules.blob parent.header then do
    .error <| .block <| .excessBlobGas <| .text
      s!"excess blob gas = {header.excessBlobGas} ≠ \
         expected = {calculateExcessBlobGas rules.blob parent.header}"
  if header.gasUsed > header.gasLimit then do
    .error <| .block <| .gasUsedOverflow <| .text
      s!"gas used = {header.gasUsed} > \
         gas limit = {header.gasLimit}"
  if expectedBaseFeePerGas ≠ header.baseFeePerGas then do
    .error <| .block <| .baseFeePerGas <| .text
      s!"base fee per gas = {header.baseFeePerGas} ≠ \
         expected = {expectedBaseFeePerGas}"
  if header.timestamp ≤ parent.header.timestamp then do
    .error <| .block <| .timestampOlderThanParent <| .text
      s!"timestamp = {header.timestamp} ≤ \
         parent timestamp = {parent.header.timestamp}"
  if header.number ≠ parent.header.number + 1 then do
    .error <| .block <| .blockNumber <| .text
      s!"number = {header.number} ≠ \
         parent number + 1 = {parent.header.number + 1}"
  if header.extraData.length > 32 then do
    .error <| .block <| .extraDataTooBig <| .text
      s!"extra data is {header.extraData.length} bytes, \
         exceeding the 32-byte maximum"
  if header.difficulty ≠ 0 then do
    .error <| .block <| .difficultyOverParis <| .text
      s!"difficulty = {header.difficulty} ≠ 0, \
         which is impossible after Paris"
  if header.nonce ≠ 0 then do
    .error <| .block <| .headerNonce <| .text
      s!"nonce = {header.nonce} ≠ 0, \
         which is impossible after Paris"
  if header.ommersHash ≠ emptyOmmerHash then do
    .error <| .block <| .ommersOverParis <| .text
      s!"ommers hash = {header.ommersHash} ≠ \
         empty-list hash = {emptyOmmerHash}, which is impossible after Paris"
  -- A header carries exactly the fork-dependent fields its rules define, in
  -- both directions. Absent-when-required and present-when-undefined are the
  -- same rule and the same reason: the wire form of a header is fixed by the
  -- fork, so a block whose header is a different shape is not a block of this
  -- fork at all. Keyed on `rules.header`, never on the fork identity, so a
  -- caller-supplied record decides for itself -- which is what makes the rule
  -- testable before `amsterdamRules` exists.
  if header.blockAccessListHash.isSome ≠ rules.header.blockAccessListHash then do
    .error <| .block <| .headerFieldPresence <| .text
      s!"blockAccessListHash is \
         {if header.blockAccessListHash.isSome then "present" else "absent"}, \
         but these rules \
         {if rules.header.blockAccessListHash then "require" else "do not define"} \
         it"
  if header.slotNumber.isSome ≠ rules.header.slotNumber then do
    .error <| .block <| .headerFieldPresence <| .text
      s!"slotNumber is \
         {if header.slotNumber.isSome then "present" else "absent"}, \
         but these rules \
         {if rules.header.slotNumber then "require" else "do not define"} it"

def stateTransitionChecks (bout : BlockOutput) (header : Header)
    (transactionsRoot blockStateRoot receiptRoot : B256)
    (blockLogsBloom : Bytes) (withdrawalsRoot requestsHash : B256) :
    Except BlockValidationError Unit := do
  let totalBlockGasUsed := max bout.blockGasUsed bout.blockStateGasUsed
  if totalBlockGasUsed ≠ header.gasUsed then
    .error <| .gasUsedMismatch <| .text
      s!"computed block gas used = {totalBlockGasUsed} ≠ \
         header block gas used = {header.gasUsed}"
  if transactionsRoot ≠ header.txsRoot then
    .error <| .transactionsRoot <| .text
      s!"computed transactions root = {transactionsRoot} \
         ≠ header transactions root = {header.txsRoot}"
  if blockStateRoot ≠ header.stateRoot then
    .error <| .stateRoot <| .text
      s!"computed state root = {blockStateRoot} ≠ \
         header state root = {header.stateRoot}"
  if receiptRoot ≠ header.receiptRoot then
    .error <| .receiptsRoot <| .text
      s!"computed receipts root = {receiptRoot} ≠ \
         header receipts root = {header.receiptRoot}"
  if blockLogsBloom ≠ header.bloom then
    .error <| .logBloom <| .text
      s!"computed logs bloom ≠ header logs bloom"
  if withdrawalsRoot ≠ header.withdrawalsRoot then
    .error <| .withdrawalsRoot <| .text
      s!"computed withdrawals root = {withdrawalsRoot} ≠ \
         header withdrawals root = {header.withdrawalsRoot}"
  if bout.blobGasUsed ≠ header.blobGasUsed then
    .error <| .blobGasUsed <| .text
      s!"computed blob gas used = {bout.blobGasUsed} ≠ \
         header blob gas used = {header.blobGasUsed}"
  if some requestsHash ≠ header.requestsHash then
    .error <| .requestsHash <| .text
      s!"computed requests hash = {requestsHash} ≠ \
         header requests hash = {header.requestsHash}"

/-- EIP-7928: the header's `blockAccessListHash` against the computed list, the
last of the pinned `execute_block` comparisons -- after `requestsHash` -- and
only under rules that carry a block-level access list. -/
def blockAccessListCheck (rules : ForkRules) (bout : BlockOutput) (header : Header) :
    Except BlockValidationError Unit :=
  match rules.bal with
  | none => .ok ()
  | some _ =>
    let hash := bout.blockAccessList.hash
    if some hash ≠ header.blockAccessListHash then
      .error <| .blockAccessListHash hash <| .text
        s!"computed block access list hash = {hash} ≠ \
           header block access list hash = {header.blockAccessListHash}"
    else .ok ()

def initBenvStat (fork : Fork) (chain : BlockChain) (header : Header) :
    BenvStat :=
  {
    fork := fork,
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
    parentBeaconBlockRoot := header.parentBeaconBlockRoot,
    -- EIP-7843: absent before Amsterdam, where nothing reads it.
    slotNumber := header.slotNumber.getD 0
  }

def initBenv (fork : Fork) (chain : BlockChain) (header : Header) : Benv :=
  {
    state := chain.state,
    createdAccounts := .emptyWithCapacity,
    stat := initBenvStat fork chain header
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

def stateTransitionOmmersCheck (ommers : List Header) :
    Except BlockValidationError Unit := do
  if ¬ommers.isEmpty then do
    .error <| .ommersOverParis <| .text
      s!"block body contains {ommers.length} ommer(s), \
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

/-- The block state transition at an explicitly named fork: the typed
canonical core. Every other state-transition entry point below only decides
*which* fork to hand it, and the retained stringly names are renderer adapters
over this one function.

It takes a `Fork` rather than a `ForkRules` because the machine it builds
carries a fork (`BenvStat.fork`): there is no rule record to hand it that is
not some fork's, so the parameter says exactly what the caller can choose. -/
def stateTransitionE (f : Fork) (ch : BlockChain) (block : Block) :
  Except TransitionError BlockChain := do
  let rules := f.ruleSet
  validateHeader rules ch block.header
  Except.mapError TransitionError.block (stateTransitionOmmersCheck block.ommers)
  let benv : Benv := initBenv f ch block.header
  let ⟨st, bout⟩ ← applyBody benv block.txs block.wds
  let blockStateRoot : B256 := st.root
  let transactionsRoot : B256 := getTransactionsRoot bout
  let receiptRoot : B256 := getReceiptRoot bout
  let blockLogsBloom : Bytes := logsBloom bout.blockLogs
  let withdrawalsRoot : B256 := getWithdrawalsRoot bout
  let requestsHash := computeRequestsHash bout.requests
  Except.mapError TransitionError.block <|
    stateTransitionChecks bout block.header
      transactionsRoot blockStateRoot receiptRoot
      blockLogsBloom withdrawalsRoot requestsHash
  Except.mapError TransitionError.block <| blockAccessListCheck rules bout block.header
  .ok ⟨appendBlock ch.blocks block, st, ch.chainId⟩

/-- Legacy renderer adapter over `stateTransitionE`, byte-identical on every
input, and the entry point for static fixture suites, which state their fork
rather than deriving it.

Named `stateTransitionWith` and taking a `ForkRules` until goal
`jaune-forks-by-construction-v1`. Once a machine carries a `Fork`, the
rules-taking adapter and this one had the same domain, so the duplicate layer
was retired into this name rather than kept as a synonym; there is no longer a
rules-taking entry point that could be handed a record no fork realises. The
`UnsupportedForkError` route this function used to take for an unimplemented
fork is gone with it -- `Fork.ruleSet` is total -- and the vocabulary is
retained where `Fork.rules` still renders it. -/
def stateTransitionAt (f : Fork) (ch : BlockChain) (block : Block) :
  Except String BlockChain :=
  (stateTransitionE f ch block).mapError TransitionError.render

/-- The adapter adds rendering and nothing else. -/
theorem stateTransitionAt_eq_ok_iff {f : Fork} {ch ch' : BlockChain}
    {block : Block} :
    stateTransitionAt f ch block = .ok ch'
      ↔ stateTransitionE f ch block = .ok ch' :=
  Except.mapError_eq_ok_iff

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
  stateTransitionAt
    (← Except.mapError RulesLookupError.render (cfg.forkAt block.header.timestamp))
    ch block

/-- The Prague state transition.

Retained with its original name, type, and behaviour. Prague is permanent
supported protocol, not scaffolding, and downstream proofs state their results
about this name. -/
def stateTransition (ch : BlockChain) (block : Block) :
  Except String BlockChain :=
  stateTransitionAt .prague ch block

def BLT.toExWithdrawal : BLT → Except DecodeError Withdrawal
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
    .error <| DecodeError.structure "withdrawal"
      "expected a list of four byte-string fields"

/-- Strict withdrawal-decoder soundness: the amount a decoded withdrawal
carries always fits its 64-bit wire type, even though the field is 256 bits
wide. -/
theorem BLT.toExWithdrawal_wireWellFormed {blt : BLT} {w : Withdrawal}
    (h : blt.toExWithdrawal = .ok w) : w.WireWellFormed := by
  unfold BLT.toExWithdrawal at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    exact UInt64.toNat_toB256_high _
  · exact absurd h (by simp)

/-- The strict legacy-transaction decoder over the nine-field list shape. Split
out of the slot decoder so the block decoder can consume it on the pure decode
carrier: a legacy list produces only decode reasons, while the byte-string
route (`Bytes.toExTx`) can also produce typed rejections. -/
def BLT.toExLegacyTx : List BLT → Except DecodeError Tx
  | [
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
  | _ =>
    .error <| DecodeError.structure "legacy transaction"
      "expected a list of nine byte-string fields"

/-- A transaction slot as a standalone value: a legacy list through the strict
legacy decoder, typed-envelope bytes through the strict envelope decoder. -/
def BLT.toExTx : BLT → Except TransitionError Tx
  | .list ls => dec (BLT.toExLegacyTx ls)
  | .bytes xs => xs.toExTx

/-- Strict legacy-transaction-decoder soundness. A *list*-shaped transaction
item is the legacy route, so what it yields is both wire-well-formed and of
legacy type -- which is exactly `TxEntry.WireWellFormed` on the decoded side of
a block body's transaction slot. The typed route never reaches this decoder,
and never produces a `.zero` transaction. -/
theorem BLT.toExLegacyTx_wireWellFormed {bs : List BLT} {tx : Tx}
    (h : BLT.toExLegacyTx bs = .ok tx) :
    Tx.WireWellFormed tx ∧ tx.type.isLegacy = true := by
  unfold BLT.toExLegacyTx at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩ <;>
      first
        | exact Bytes.toRlpNat_lt_two_pow_256 (by assumption)
        | exact Bytes.toRlpB256_eq_ok (by assumption)
  · exact absurd h (by simp)

def BLT.toExBlock : BLT → Except DecodeError Block
  | BLT.list [
      HeaderBLT,
      .list TxBLTs,
      .list OmmerBLTs,
      .list WithdrawalBLTs
    ] => do
    let header ← HeaderBLT.toExHeader
    let aux : BLT → Except DecodeError (Bytes ⊕ Tx)
      | .list ls => BLT.toExLegacyTx ls <&> .inr
      | .bytes xs => .ok <| .inl xs
    let txs ← List.mapM aux TxBLTs
    let ommers ← List.mapM BLT.toExHeader OmmerBLTs
    let withdrawals ← List.mapM BLT.toExWithdrawal WithdrawalBLTs
    .ok {
      header := header,
      txs := txs,
      ommers := ommers,
      wds := withdrawals
    }
  | .list [_, .list _, .list _] =>
    .error <| .withdrawalsNotRead <|
      .text "post-Shanghai block body omits the withdrawals list"
  | _ =>
    .error <| DecodeError.structure "block"
      "expected [header, transactions, ommers, withdrawals] lists"

/-- Strict block-decoder soundness: a decoded block is structurally canonical
componentwise. Note what this deliberately does *not* say about a byte-string
transaction slot -- it stays opaque here, and is decoded at the existing point
inside `applyBody`, so the staged typed-transaction rule (design report §7) is
preserved and no error precedence moves. -/
theorem BLT.toExBlock_rlpCanonical {blt : BLT} {b : Block}
    (h : blt.toExBlock = .ok b) : b.RlpCanonical := by
  unfold BLT.toExBlock at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨BLT.toExHeader_wireWellFormed (by assumption), ?_, ?_, ?_⟩
    · intro o ho
      obtain ⟨blt', hblt'⟩ := List.mapM_except_eq_ok_mem (by assumption) o ho
      exact BLT.toExHeader_wireWellFormed hblt'
    · intro w hw
      obtain ⟨blt', hblt'⟩ := List.mapM_except_eq_ok_mem (by assumption) w hw
      exact BLT.toExWithdrawal_wireWellFormed hblt'
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
        exact BLT.toExLegacyTx_wireWellFormed htx
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
def rlpToBlockE (rlp : Bytes) : Except DecodeError (Block × B256) := do
  let block_blt ← (Bytes.toBLT? rlp).toExcept <|
    DecodeError.structure "block RLP" "cannot decode the outer RLP item"
  let block ← block_blt.toExBlock
  let canonicalRlp := block.toBLT.toBytes
  if rlp ≠ canonicalRlp then
    .error <| .roundTrip <|
      .text "decoded block does not re-encode byte-for-byte"
  .ok ⟨block, (Header.toBLT block.header).toBytes.keccak⟩

/-- Legacy renderer adapter over `rlpToBlockE`, byte-identical on every input.
Retained by name and type because Blanc's protected
`addBlockToChain_preserves_solvent` quantifies over exactly this equation, and
the canonical envelope's evidence field is stated with it. -/
def rlpToBlock (rlp : Bytes) : Except String (Block × B256) :=
  (rlpToBlockE rlp).mapError DecodeError.render

/-- The adapter adds rendering and nothing else: success is the typed core's
success. This is the bridge every string-level client inverts through. -/
theorem rlpToBlock_eq_ok_iff {rlp : Bytes} {p : Block × B256} :
    rlpToBlock rlp = .ok p ↔ rlpToBlockE rlp = .ok p :=
  Except.mapError_eq_ok_iff

--------------- THE CANONICAL OUTER-BLOCK ENVELOPE ---------------

/-- The hash `rlpToBlock` returns is always the keccak of the decoded header's
canonical encoding. It is therefore *derivable* from the decoded block and was
never independent evidence, which is why the import core below takes an
envelope instead of a separate hash argument. -/
theorem rlpToBlock_headerHash {raw : Bytes} {block : Block} {hash : B256}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) :
    hash = (Header.toBLT block.header).toBytes.keccak := by
  rw [rlpToBlock_eq_ok_iff] at h
  unfold rlpToBlockE at h
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
  rw [rlpToBlock_eq_ok_iff] at h
  unfold rlpToBlockE at h
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
  rw [rlpToBlock_eq_ok_iff] at h
  unfold rlpToBlockE at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨b, hb, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, herr, _⟩ := Except.bind_eq_ok h
    exact absurd herr (by simp)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact BLT.toExBlock_rlpCanonical hb

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
    (hd : blt.toExHeader = .ok h) : CheckedHeader :=
  ⟨h, BLT.toExHeader_wireWellFormed hd⟩

/-- A withdrawal certified wire-well-formed. -/
structure CheckedWithdrawal : Type where
  private mk ::
  val : Withdrawal
  wireWellFormed : val.WireWellFormed

def CheckedWithdrawal.ofWithdrawal? (w : Withdrawal) : Option CheckedWithdrawal :=
  if hw : w.WireWellFormed then some ⟨w, hw⟩ else none

def CheckedWithdrawal.ofDecode {blt : BLT} {w : Withdrawal}
    (hd : blt.toExWithdrawal = .ok w) : CheckedWithdrawal :=
  ⟨w, BLT.toExWithdrawal_wireWellFormed hd⟩

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
    (h : BLT.toExLegacyTx ls = .ok tx) : TxEnvelope :=
  ⟨.inr tx, BLT.toExLegacyTx_wireWellFormed h⟩

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

Definitionally the typed core applied to the envelope's block, so every result
about `stateTransitionE` transfers to it by `rfl` and no proof has to be
restated. What it adds is at the type level: a caller of this entry point
cannot supply a block that no strict decode ever produced. -/
def stateTransitionCanonical (f : Fork) (ch : BlockChain)
    (cb : CanonicalBlock) :
    Except TransitionError BlockChain :=
  stateTransitionE f ch cb.block

theorem stateTransitionCanonical_eq (f : Fork) (ch : BlockChain)
    (cb : CanonicalBlock) :
    stateTransitionCanonical f ch cb = stateTransitionE f ch cb.block :=
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

/-- The snapshot's committed state root, read from the tip header rather than
rebuilt from the world -- the same trade `tipHash` makes, for the same reason:
`tipStateRoot` is already the proof that the two agree, so recomputing
`val.state.root` here would rebuild the whole trie to learn something the
structure carries. -/
def CheckedBlockChain.stateRoot (cc : CheckedBlockChain) : B256 :=
  cc.tip.header.stateRoot

/-- The field read is the trie rebuild. This is `tipStateRoot` under the
accessor's name, and it is what licenses a consumer to compare against
`stateRoot` where it would otherwise have called `State.root`. -/
theorem CheckedBlockChain.stateRoot_eq (cc : CheckedBlockChain) :
    cc.stateRoot = cc.val.state.root := cc.tipStateRoot.symm

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
    Except BlockValidationError Unit :=
  match limits.maxRlpSize with
  | none => .ok ()
  | some maxRlpSize =>
    if rawSize > maxRlpSize then
      .error <| .blockRlpSizeExceeded <| .text
        s!"original block RLP is {rawSize} bytes > \
           maximum = {maxRlpSize}"
    else
      .ok ()

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
among consensus checks EIP-7934 is first, before `stateTransitionAt` reaches
header validation, exactly as EELS. The two failure channels are unchanged:
`.error` is a harness-level failure, `.inr` is a block this chain rejects. -/
def addBlockToChainCanonicalE (f : Fork) (chain : BlockChain)
    (cb : CanonicalBlock) : Except ImportFailure (ImportOutcome BlockChain) :=
  match checkBlockRlpSize f.ruleSet.block cb.rawSize with
  | .error err => .ok (.inr (.block err))
  | .ok () =>
    match stateTransitionE f chain cb.block with
    | .error e =>
      match e.split with
      | .inl failure => .error failure
      | .inr rejection => .ok (.inr rejection)
    | .ok chain' => .ok (.inl chain')

/-- Collapse a typed import result onto the legacy stringly channels: the
operational failure renders on the outer `.error`, the candidate rejection on
the inner `.inr`. This is the single renderer every legacy import adapter
goes through. -/
def ImportOutcome.renderLegacy :
    Except ImportFailure (ImportOutcome BlockChain) →
    Except String (BlockChain ⊕ String)
  | .error failure => .error failure.render
  | .ok (.inl chain) => .ok (.inl chain)
  | .ok (.inr rejection) => .ok (.inr rejection.render)

/-- Legacy renderer adapter over the canonical-envelope import core. -/
def addBlockToChainCanonical (f : Fork) (chain : BlockChain)
    (cb : CanonicalBlock) :
    Except String (BlockChain ⊕ String) :=
  ImportOutcome.renderLegacy (addBlockToChainCanonicalE f chain cb)

/-- Block import from raw bytes under an explicit rule set: the typed core of
the raw compatibility wrapper. It carries no evidence, so it validates on
every call (fixed decision 2) -- strict decode plus the exact round trip --
and hands the checked core an envelope built from that decode alone.

Channel decision, per the Step-1 producer/channel matrix: every strict decode
failure of the candidate bytes is a *candidate rejection* (`.inr .decode`),
because the audited fixture ordering scores each of the seven decode reasons
as a block exception. The legacy wrapper's old habit of reporting them on the
outer channel was the accidental nesting design report §8 names, and is
deliberately not preserved. `RawImportFailure.strictDecode` therefore retains
no producer on this path; it remains the declared ingress channel for a
future decoder whose failures are *not* candidate verdicts. -/
def addBlockToChainAtE (f : Fork) (chain : BlockChain)
    (blockRlp : Bytes) : Except ImportFailure (ImportOutcome BlockChain) :=
  match h : rlpToBlockE blockRlp with
  | .error reason => .ok (.inr (.decode reason))
  | .ok ⟨_, _⟩ =>
    addBlockToChainCanonicalE f chain
      (CanonicalBlock.ofDecode (rlpToBlock_eq_ok_iff.mpr h))

/-- Legacy renderer adapter over `addBlockToChainAtE`. Retained by type:
Blanc's protected `addBlockToChain_preserves_solvent` is its Prague instance.
Same rendered diagnostics; the decode-failure channel moved from the outer
`.error` to the inner `.inr` deliberately (see the core's docstring and the
Step-10 report).

Named `addBlockToChainWith` and taking a `ForkRules` until goal
`jaune-forks-by-construction-v1`; with a machine carrying a `Fork` the
rules-taking adapter and the fork-taking one had the same domain, and the
duplicate layer was retired into this name. The `.support` channel this
function used to route an unimplemented fork through is gone with it:
`Fork.ruleSet` is total. -/
def addBlockToChainAt (f : Fork) (chain : BlockChain) (blockRlp : Bytes) :
    Except String (BlockChain ⊕ String) :=
  ImportOutcome.renderLegacy (addBlockToChainAtE f chain blockRlp)

/-- Typed block import on a configured chain, deriving the active fork from
the block's own timestamp and the chain's activation schedule.

Checks schedule usability and chain identity before touching the candidate
bytes at all -- P0.1 and P0.5's frozen ordering (design report §3.3): a
contradictory or unusable configuration is a context failure regardless of
what the caller supplied as a block, so it must not depend on decoding
succeeding first. The era a decoded timestamp falls in is checked after
decode, inside `cfg.rulesAt` below, because no timestamp exists before
decode. -/
def addBlockToChainUsingE (cfg : ChainConfig) (chain : BlockChain)
    (blockRlp : Bytes) : Except ImportFailure (ImportOutcome BlockChain) := do
  Except.mapError ImportFailure.context cfg.validate
  Except.mapError ImportFailure.context (cfg.checkChainId chain)
  match h : rlpToBlockE blockRlp with
  | .error reason => .ok (.inr (.decode reason))
  | .ok ⟨block, _⟩ =>
    let fork ←
      Except.mapError ImportFailure.ofLookup
        (cfg.forkAt block.header.timestamp)
    addBlockToChainCanonicalE fork chain
      (CanonicalBlock.ofDecode (rlpToBlock_eq_ok_iff.mpr h))

/-- Legacy renderer adapter over `addBlockToChainUsingE`. -/
def addBlockToChainUsing (cfg : ChainConfig) (chain : BlockChain)
    (blockRlp : Bytes) : Except String (BlockChain ⊕ String) :=
  ImportOutcome.renderLegacy (addBlockToChainUsingE cfg chain blockRlp)

/-- Prague block import.

Retained with its original name, type, and behaviour; downstream proofs state
their results about this name. -/
def addBlockToChain (chain : BlockChain) (blockRlp : Bytes) :
  Except String (BlockChain ⊕ String) :=
  addBlockToChainAt .prague chain blockRlp

--------------- IMPORT BRIDGE AND INVERSION LEMMAS ---------------

-- Stated entirely over `rlpToBlock`, `checkBlockRlpSize` and
-- `stateTransitionAt`. A downstream proof client -- Blanc, in practice --
-- can invert an import with these and never unfold `CanonicalBlock`,
-- `addBlockToChainCanonical`, or the raw wrapper's dependent match.

/-- A raw import whose bytes do not strictly decode *rejects the candidate*
with exactly the decoder's own diagnostic. Before Step 10 the same diagnostic
rode the outer harness channel -- the accidental nesting design report §8
records -- so the channel here is a deliberate move, and the rendered message
is unchanged. -/
theorem addBlockToChainAt_decode_error {f : Fork} {chain : BlockChain}
    {blockRlp : Bytes} {err : String} (h : rlpToBlock blockRlp = .error err) :
    addBlockToChainAt f chain blockRlp = .ok (.inr err) := by
  unfold rlpToBlock at h
  rw [Except.mapError_eq_error_iff] at h
  obtain ⟨reason, hre, rfl⟩ := h
  unfold addBlockToChainAt addBlockToChainAtE
  split
  · rename_i e he
    rw [hre] at he
    cases he
    rfl
  · rename_i b hs hb
    rw [hre] at hb
    exact absurd hb (by simp)

/-- A raw import whose bytes strictly decode is the checked core on the
envelope that decode produces. This is the bridge: the wrapper adds
validation, and nothing else. -/
theorem addBlockToChainAt_eq_canonical {f : Fork} {chain : BlockChain}
    {blockRlp : Bytes} {block : Block} {hash : B256}
    (h : rlpToBlock blockRlp = .ok ⟨block, hash⟩) :
    addBlockToChainAt f chain blockRlp
      = addBlockToChainCanonical f chain (CanonicalBlock.ofDecode h) := by
  have hE := rlpToBlock_eq_ok_iff.mp h
  unfold addBlockToChainAt addBlockToChainAtE
  split
  · rename_i e he
    rw [hE] at he
    exact absurd he (by simp)
  · rename_i f sh hb
    rw [hE] at hb
    simp only [Except.ok.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rfl

/-- Inversion of the typed canonical-envelope import core. -/
theorem addBlockToChainCanonicalE_eq_ok_inl {f : Fork}
    {chain chain' : BlockChain} {cb : CanonicalBlock}
    (h : addBlockToChainCanonicalE f chain cb = .ok (.inl chain')) :
    checkBlockRlpSize f.ruleSet.block cb.rawSize = .ok () ∧
      stateTransitionE f chain cb.block = .ok chain' := by
  unfold addBlockToChainCanonicalE at h
  split at h
  · simp at h
  · rename_i u hsize
    split at h
    · split at h <;> simp_all
    · rename_i hst
      simp only [Except.ok.injEq, Sum.inl.injEq] at h
      exact ⟨hsize, h ▸ hst⟩

/-- Full inversion of a successful raw import: strict decode, then EIP-7934
against the *supplied* byte length, then the transition -- in that order.
Stated over the legacy names, so a downstream stringly client (Blanc) can
invert an import without unfolding the typed core. -/
theorem addBlockToChainAt_eq_ok_inl {f : Fork}
    {chain chain' : BlockChain} {blockRlp : Bytes}
    (h : addBlockToChainAt f chain blockRlp = .ok (.inl chain')) :
    ∃ block hash,
      rlpToBlock blockRlp = .ok ⟨block, hash⟩ ∧
      checkBlockRlpSize f.ruleSet.block blockRlp.length = .ok () ∧
      stateTransitionAt f chain block = .ok chain' := by
  unfold addBlockToChainAt at h
  cases hE : addBlockToChainAtE f chain blockRlp with
  | error failure =>
    rw [hE] at h; exact absurd h (by simp [ImportOutcome.renderLegacy])
  | ok outcome =>
    rw [hE] at h
    cases outcome with
    | inr r => exact absurd h (by simp [ImportOutcome.renderLegacy])
    | inl ch =>
      simp only [ImportOutcome.renderLegacy, Except.ok.injEq, Sum.inl.injEq] at h
      subst h
      unfold addBlockToChainAtE at hE
      split at hE
      · exact absurd hE (by simp)
      · rename_i block hash hd
        obtain ⟨hsize, hst⟩ := addBlockToChainCanonicalE_eq_ok_inl hE
        exact ⟨block, hash, rlpToBlock_eq_ok_iff.mpr hd, hsize,
          stateTransitionAt_eq_ok_iff.mpr hst⟩

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
-- rule the build actually applied. No fork is in that state here: `Fork.ruleSet`
-- is total, and the guards below record that the support channel is
-- unreachable through any declared label.

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

-- Every fork this build runs reaches execution; none is refused for want of
-- rules. This chain has no parent block, so each verdict is the fail-closed
-- no-parent invariant on the outer operational channel -- never a support
-- failure.
#guard Fork.supported.all (fun f =>
  match addBlockToChainAtE f guardEmptyChain (guardBlockAt 0).toBLT.toBytes with
  | .error (.support _) => false
  | _ => true)
#guard Fork.supported.all (fun f =>
  match f.rules with
  | .error _ => false
  | .ok _ =>
    match stateTransitionE f guardEmptyChain (guardBlockAt 0) with
    | .error (.internal _) => true
    | _ => false)

-- The complement, at the same entry point and on the same chain, is vacuous
-- by construction: `Fork.ruleSet` is total, so `Fork.unimplemented_eq_nil` is a
-- theorem and this guard records today's list rather than establishing it.
-- Goal A's guard here asserted that Amsterdam was refused on
-- the support channel before any block was examined; it is rewritten to say
-- that Amsterdam reaches execution like every other fork (the no-parent
-- invariant, never a support failure), and that the support channel is
-- unreachable through any declared label.
#guard Fork.unimplemented = []
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

-- The encoder emits exactly 20, 21 or 23 fields. 22 is not merely rejected on
-- input -- it is unreachable on output, because the three options nest.
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
      "RlpStructureError : header : expected 20, 21 or 23 fields, but found 22"
  | .ok _ => false)

-- A 24-field header is refused for the same reason, so the rule is "these
-- three widths" and not "at most 23".
#guard (match (Header.toBLT guardHeader23) with
  | .list l => (BLT.list (l ++ [BLT.bytes []])).toExHeader.toOption.isNone
  | _ => false)

/-- A header carrying neither Amsterdam field encodes exactly as it did before
those fields existed.

`rfl` on an arbitrary header, so this is a fact about *every* 20- or 21-field
header rather than about a sample -- which is what makes "no Prague, Osaka,
BPO1 or BPO2 block's hash moved" a structural claim and not a test result. The
right-hand side is the encoder's body as it stood before this change. -/
example (h : Header) :
    Header.toBLT { h with blockAccessListHash := none, slotNumber := none }
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
          BLT.bytes h.baseFeePerGas.toBytes,
          BLT.bytes h.withdrawalsRoot.toBytes,
          BLT.bytes h.blobGasUsed.toBytes,
          BLT.bytes h.excessBlobGas.toBytes,
          BLT.bytes h.parentBeaconBlockRoot.toBytes
        ] ++
          match h.requestsHash with
          | none => []
          | some rh => [BLT.bytes rh.toBytes]) := rfl

/-- Therefore the identity of every such header is unchanged. -/
example (h : Header) :
    Header.hash { h with blockAccessListHash := none, slotNumber := none }
      = (BLT.list ([
          BLT.bytes h.parentHash.toBytes, BLT.bytes h.ommersHash.toBytes,
          BLT.bytes h.coinbase.toBytes, BLT.bytes h.stateRoot.toBytes,
          BLT.bytes h.txsRoot.toBytes, BLT.bytes h.receiptRoot.toBytes,
          BLT.bytes h.bloom, BLT.bytes h.difficulty.toBytes,
          BLT.bytes h.number.toBytes, BLT.bytes h.gasLimit.toBytes,
          BLT.bytes h.gasUsed.toBytes, BLT.bytes h.timestamp.toBytes,
          BLT.bytes h.extraData, BLT.bytes h.prevRandao.toBytes,
          BLT.bytes h.nonce.toBytes, BLT.bytes h.baseFeePerGas.toBytes,
          BLT.bytes h.withdrawalsRoot.toBytes, BLT.bytes h.blobGasUsed.toBytes,
          BLT.bytes h.excessBlobGas.toBytes,
          BLT.bytes h.parentBeaconBlockRoot.toBytes
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
        baseFeePerGas := 14
        requestsHash := some guardRequestsHash }

private def guardChild23 : Block :=
  guardChildBlockWith
    { (guardChildBlock 1 917504).header with
        baseFeePerGas := 14
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
  { bpo2Rules with header := { blockAccessListHash := false, slotNumber := true } }
  guardParentChain guardChild21.header)
#guard presenceFails (validateHeader
  { bpo2Rules with header := { blockAccessListHash := true, slotNumber := false } }
  guardParentChain guardChild21.header)

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
  match cfg.forkAt block.header.timestamp with
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
  ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 100⟩, ⟨.bpo1, 200⟩, ⟨.bpo2, 300⟩]

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
  (⟨.osaka, .bpo1, 15000⟩ : ForkTransition).chainConfig 1

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

/-- Every successful `stateTransitionAt` copies the input snapshot's chain
identity into its output unconditionally -- the shared fact both configured
entry points' preservation theorems reduce to. -/
theorem stateTransitionAt_preserves_chainId
    {f : Fork} {ch : BlockChain} {block : Block} {ch' : BlockChain}
    (h : stateTransitionAt f ch block = .ok ch') :
    ch'.chainId = ch.chainId := by
  rw [stateTransitionAt_eq_ok_iff] at h
  unfold stateTransitionE at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨st, bout⟩, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
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
  exact stateTransitionAt_preserves_chainId h

/-- A same-ID configured transition is exactly the rule-selected core: the
identity check Step 2 adds is a no-op whenever the caller's IDs already agree,
so no previously-agreeing caller observes any behavioral change. -/
theorem stateTransitionUsing_eq_of_chainId_eq
    {cfg : ChainConfig} {ch : BlockChain} {block : Block}
    (heq : cfg.chainId = ch.chainId) :
    stateTransitionUsing cfg ch block
      = (Except.mapError RulesLookupError.render
          (cfg.forkAt block.header.timestamp)).bind
          (fun f => stateTransitionAt f ch block) := by
  unfold stateTransitionUsing ChainConfig.checkChainId
  simp [heq, Except.mapError, Bind.bind, Except.bind]

theorem addBlockToChainUsing_success_chainId_eq
    {cfg : ChainConfig} {chain : BlockChain} {blockRlp : Bytes} {chain' : BlockChain}
    (h : addBlockToChainUsing cfg chain blockRlp = .ok (.inl chain')) :
    cfg.chainId = chain.chainId := by
  unfold addBlockToChainUsing addBlockToChainUsingE at h
  by_contra hne
  cases hv : cfg.validate with
  | error e =>
    rw [hv] at h
    simp [Except.mapError, Bind.bind, Except.bind,
      ImportOutcome.renderLegacy] at h
  | ok u =>
    cases u
    rw [hv] at h
    simp [ChainConfig.checkChainId, hne, Except.mapError, Bind.bind,
      Except.bind, ImportOutcome.renderLegacy] at h

theorem addBlockToChainUsing_preserves_chainId
    {cfg : ChainConfig} {chain : BlockChain} {blockRlp : Bytes} {chain' : BlockChain}
    (h : addBlockToChainUsing cfg chain blockRlp = .ok (.inl chain')) :
    chain'.chainId = chain.chainId := by
  unfold addBlockToChainUsing at h
  cases hE : addBlockToChainUsingE cfg chain blockRlp with
  | error f => rw [hE] at h; simp [ImportOutcome.renderLegacy] at h
  | ok outcome =>
    rw [hE] at h
    cases outcome with
    | inr r => simp [ImportOutcome.renderLegacy] at h
    | inl ch =>
      simp only [ImportOutcome.renderLegacy, Except.ok.injEq, Sum.inl.injEq] at h
      subst h
      unfold addBlockToChainUsingE at hE
      obtain ⟨_, _, hE⟩ := Except.bind_eq_ok hE
      obtain ⟨_, _, hE⟩ := Except.bind_eq_ok hE
      split at hE
      · simp at hE
      · obtain ⟨rules, _, hE⟩ := Except.bind_eq_ok hE
        obtain ⟨_, hst⟩ := addBlockToChainCanonicalE_eq_ok_inl hE
        exact stateTransitionAt_preserves_chainId
          (stateTransitionAt_eq_ok_iff.mpr hst)

-- P0.1 negative guards: config ID 7 against a chain ID 1 snapshot, matching
-- the acceptance evidence's own example. The mismatch is a context failure on
-- the outer channel -- never `.inr`, so never scored as an invalid block --
-- and it fires before decoding even touches the candidate bytes: `[0xFF]` is
-- not valid block RLP at all, yet `addBlockToChainUsing` still reports the
-- mismatch rather than a decode error, because the check runs first.
private def guardMismatchConfig : ChainConfig := ChainConfig.mk 7 [⟨.prague, 0⟩]

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


--------------- CANONICALITY THROUGH EXECUTION (P0.4, STEP 4) ---------------

-- Checkpoint 3: canonicality through message-call processing, transaction
-- processing, system transactions, withdrawals, the block body, and the raw
-- successful block transition. Every lemma states the success channel; the
-- error channel at this layer carries no state.

private theorem chargeNewAuthorityAmsterdam_canonical {state : StateGasRules}
    {authority : Adr} {devm : Devm} (h : devm.Canonical) :
    (chargeNewAuthorityAmsterdam state authority devm).Canonical := by
  unfold chargeNewAuthorityAmsterdam
  split
  · exact liftMachExecution_canonical h
  · exact h

private theorem chargePaidAccountWriteAmsterdam_canonical
    {state : StateGasRules} {authority : Adr} {devm : Devm}
    {paidWrites : AdrSet} (h : devm.Canonical) :
    (chargePaidAccountWriteAmsterdam state authority devm paidWrites).CanonicalOn
      (fun r => r.1.Canonical) := by
  unfold chargePaidAccountWriteAmsterdam
  split
  · exact h
  · exact Except.CanonicalOn.bind (chargeGas_canonical h) (fun _ hd => hd)

private theorem chargeAuthBaseAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} {authority target : Adr} {devm : Devm}
    {delegationSetFor : AdrSet} (h : devm.Canonical) :
    (chargeAuthBaseAmsterdam state msg authority target devm
      delegationSetFor).CanonicalOn (fun r => r.1.Canonical) := by
  unfold chargeAuthBaseAmsterdam
  split
  · exact h
  · dsimp only
    split
    · exact Except.CanonicalOn.bind (liftMachExecution_canonical h)
        (fun _ hd => hd)
    · exact h

private theorem applyValidatedDelegationAmsterdam_canonical
    {state : StateGasRules} {msg : Msg} {authority target : Adr}
    {devm : Devm} {paidWrites delegationSetFor : AdrSet}
    (h : devm.Canonical) :
    (applyValidatedDelegationAmsterdam state msg authority target devm
      paidWrites delegationSetFor).CanonicalOn (fun r => r.1.Canonical) := by
  unfold applyValidatedDelegationAmsterdam
  refine Except.CanonicalOn.bind (chargeNewAuthorityAmsterdam_canonical h)
    fun devm hdevm => ?_
  refine Except.CanonicalOn.bind
    (chargePaidAccountWriteAmsterdam_canonical hdevm) fun r hr => ?_
  obtain ⟨devm, paidWrites⟩ := r
  refine Except.CanonicalOn.bind
    (chargeAuthBaseAmsterdam_canonical hr) fun r hr => ?_
  obtain ⟨devm, delegationSetFor, codeToSet⟩ := r
  exact Devm.Canonical.incrNonce (Devm.Canonical.setCode hr authority codeToSet)
    authority

private theorem setDelegationAmsterdamStep_canonical
    {state : StateGasRules} {msg : Msg} {auth : Auth} {devm : Devm}
    {paidWrites delegationSetFor : AdrSet} (h : devm.Canonical) :
    (setDelegationAmsterdamStep state msg auth devm paidWrites
      delegationSetFor).CanonicalOn (fun r => r.1.Canonical) := by
  unfold setDelegationAmsterdamStep
  split
  · exact h
  · split
    · exact h
    · cases hr : recoverAuthority auth with
      | error error =>
        cases error <;> simp only <;> exact h
      | ok authority =>
        dsimp only
        have ha := addAccessedAddress_canonical (a := authority) h
        split
        · exact ha
        · split
          · exact ha
          · exact applyValidatedDelegationAmsterdam_canonical ha

private theorem setDelegationAmsterdamLoop_canonical
    {state : StateGasRules} {msg : Msg} {auths : List Auth} {devm : Devm}
    {paidWrites delegationSetFor : AdrSet} (h : devm.Canonical) :
    (setDelegationAmsterdamLoop state msg auths devm paidWrites
      delegationSetFor).CanonicalOn (fun r => r.1.Canonical) := by
  induction auths generalizing devm paidWrites delegationSetFor with
  | nil => exact h
  | cons auth auths ih =>
    unfold setDelegationAmsterdamLoop
    exact Except.CanonicalOn.bind (setDelegationAmsterdamStep_canonical h)
      (fun r hr => ih hr)

private theorem setDelegationAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} {devm : Devm} (h : devm.Canonical) :
    (setDelegationAmsterdam state msg devm).Canonical := by
  unfold setDelegationAmsterdam
  exact Except.CanonicalOn.bind (setDelegationAmsterdamLoop_canonical h)
    (fun _ hr => hr)

private theorem preparedTopLevelMsg_canonical {msg : Msg} {devm : Devm}
    (hm : msg.Canonical) (hd : devm.Canonical) :
    (preparedTopLevelMsg msg devm).Canonical := by
  exact ⟨⟨hd.1, hm.1.2⟩, hd.2⟩

private theorem resolveTopLevelCallAmsterdam_canonical {msg : Msg}
    {devm : Devm} (hm : msg.Canonical) (hd : devm.Canonical) :
    (resolveTopLevelCallAmsterdam msg devm).CanonicalOn
      (fun r => r.1.Canonical ∧ r.2.Canonical) := by
  unfold resolveTopLevelCallAmsterdam
  rcases msg.benv.stat.rules.gas.delegationCost devm msg.currentTarget
    with ⟨delegated, codeAddress, accessCost⟩
  refine Except.CanonicalOn.bind (chargeGas_canonical hd)
    fun charged hcharged => ?_
  have hfinished := completeDelegationAccess_canonical hcharged delegated codeAddress
  exact ⟨preparedTopLevelMsg_canonical hm hfinished, hfinished⟩

private theorem dispatchTopLevelAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} {devm : Devm} (hm : msg.Canonical) (hd : devm.Canonical) :
    (dispatchTopLevelAmsterdam state msg devm).CanonicalOn
      (fun r => r.1.Canonical ∧ r.2.Canonical) := by
  unfold dispatchTopLevelAmsterdam
  split
  · dsimp only
    split
    · exact hd
    · split
      · exact Except.CanonicalOn.bind (liftMachExecution_canonical hd)
          (fun charged hcharged =>
            ⟨preparedTopLevelMsg_canonical hm hcharged, hcharged⟩)
      · exact ⟨preparedTopLevelMsg_canonical hm hd, hd⟩
  · dsimp only
    split
    · exact Except.CanonicalOn.bind (liftMachExecution_canonical hd)
        (fun _ hcharged => resolveTopLevelCallAmsterdam_canonical hm hcharged)
    · exact resolveTopLevelCallAmsterdam_canonical hm hd

private theorem finishTopLevelAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} {devm : Devm} (hm : msg.Canonical) (hd : devm.Canonical) :
    (finishTopLevelAmsterdam state msg devm).CanonicalOn
      (fun r => r.1.Canonical ∧ r.2.Canonical) := by
  unfold finishTopLevelAmsterdam
  split
  · exact dispatchTopLevelAmsterdam_canonical hm hd
  · exact dispatchTopLevelAmsterdam_canonical hm
      (Devm.Canonical.of_world_eq hd rfl)

private theorem prepareTopLevelAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} (hm : msg.Canonical) :
    (prepareTopLevelAmsterdam state msg).CanonicalOn
      (fun r => r.1.Canonical ∧ r.2.Canonical) := by
  unfold prepareTopLevelAmsterdam
  have hi := initDevm_canonical hm
  dsimp only
  split
  · exact finishTopLevelAmsterdam_canonical hm hi
  · exact Except.CanonicalOn.bind (setDelegationAmsterdam_canonical hi)
      (fun _ hd => finishTopLevelAmsterdam_canonical hm hd)

private theorem runPreparedTopFrame_canonicalSettle {frame : Frame}
    {prepared : Devm} (hf : frame.Canonical) (hp : prepared.Canonical) :
    (runPreparedTopFrame frame prepared).CanonicalSettle := by
  unfold runPreparedTopFrame
  rcases hbt : frame.inner.benvAfterTransfer with e | benv
  · exact Frame.settleMsg_canonicalSettle hf
      (Msg.benvAfterTransfer_error_canonical hf.2 hbt)
  · have hb := Msg.benvAfterTransfer_ok_canonical hf.2 hbt
    have hi := Msg.Canonical.withBenv hf.2 hb
    have hd :
        ((prepared.withState benv.state).withCreatedAccounts
          benv.createdAccounts).Canonical :=
      Devm.Canonical.of_world_eq (hp.withState hb.1) rfl
    let evm : Evm := {
      pc := 0
      sta := initSevm (frame.inner.withBenv benv)
      dyna := (prepared.withState benv.state).withCreatedAccounts
        benv.createdAccounts
    }
    have hevm : evm.Canonical := ⟨initSevm_canonical hi, hd⟩
    dsimp only
    split
    · exact Frame.settle_canonicalSettle hf (exec_canonical hevm)
    · split
      · exact Frame.settle_canonicalSettle hf
          (executePrecomp_canonical hevm.2 _)
      · exact Frame.settle_canonicalSettle hf (exec_canonical hevm)

private theorem processTopLevelAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} (hm : msg.Canonical) (frameOf : Msg → Frame)
    (hframe : ∀ {prepared : Msg}, prepared.Canonical →
      (frameOf prepared).Canonical) {p}
    (hp : processTopLevelAmsterdam state msg frameOf = .ok p) :
    State.Canonical p.1 := by
  unfold processTopLevelAmsterdam at hp
  have hprepare := prepareTopLevelAmsterdam_canonical (state := state) hm
  cases hprep : prepareTopLevelAmsterdam state msg with
  | error failure =>
    rw [hprep] at hp hprepare
    obtain ⟨error, devm⟩ := failure
    cases error with
    | halt reason =>
      simp only [settleTopLevelPreparationFailure] at hp
      cases hp
      exact hm.1.1
    | revert =>
      simp only [settleTopLevelPreparationFailure] at hp
      cases hp
    | crypto reason =>
      simp only [settleTopLevelPreparationFailure] at hp
      cases hp
    | internal reason =>
      simp only [settleTopLevelPreparationFailure] at hp
      cases hp
  | ok prepared =>
    rw [hprep] at hp hprepare
    obtain ⟨preparedMsg, preparedDevm⟩ := prepared
    obtain ⟨evm, hevm, hp⟩ := Except.bind_eq_ok hp
    have hrun := runPreparedTopFrame_canonicalSettle
      (hframe hprepare.1) hprepare.2
    rw [Except.bimap_id_eq_ok hevm] at hrun
    unfold msgCallOutputAmsterdam at hp
    split at hp <;>
      (obtain ⟨refundCounter, _, hp⟩ := Except.bind_eq_ok hp
       cases hp
       exact hrun.1)

theorem processMessageCall.create_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : processMessageCall.create msg = .ok p) :
    State.Canonical p.1 := by
  unfold processMessageCall.create at hp
  dsimp only at hp
  split at hp
  · split at hp <;>
      first
      | (cases hp; exact h.1.1)
      | (obtain ⟨evm, hevm, hp⟩ := Except.bind_eq_ok hp
         have hcan := processCreateMessage_ok_canonical h
           (Except.bimap_id_eq_ok hevm)
         split at hp <;>
           (obtain ⟨rc, _, hp⟩ := Except.bind_eq_ok hp
            cases hp
            exact hcan.1))
  · exact processTopLevelAmsterdam_canonical h Frame.ofCreate
      (fun hm => Frame.canonical_ofCreate hm) hp

theorem processMessageCall.call_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : processMessageCall.call msg = .ok p) :
    State.Canonical p.1 := by
  unfold processMessageCall.call at hp
  dsimp only at hp
  split at hp
  · split at hp <;>
      first
      | (-- no authorizations: the join point receives the message unchanged
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
               exact hcan.1)))
      | (-- delegation processed first
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
               exact hcan.1)))
  · exact processTopLevelAmsterdam_canonical h Frame.ofCall
      (fun hm => Frame.canonical_ofCall hm) hp

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

theorem State.Canonical.clearAccountPreservingBalance {state : State}
    (h : state.Canonical) (address : Adr) :
    (clearAccountPreservingBalance state address).Canonical := by
  unfold Jaune.clearAccountPreservingBalance
  exact State.Canonical.set h address Stor.canonical_empty

theorem State.Canonical.settleSelfdestructs {state : State}
    (h : state.Canonical) (rules : ForkRules) (addresses : List Adr) :
    (settleSelfdestructs rules addresses state).Canonical := by
  unfold Jaune.settleSelfdestructs
  split
  · exact State.Canonical.foldl_destroyAccount h
  · induction addresses generalizing state with
    | nil => exact h
    | cons address addresses ih =>
      exact ih (State.Canonical.clearAccountPreservingBalance h address)

/-- A successful transaction leaves a canonical state: the fee movements go
through `incrNonce`/`subBal`/`addBal`, the call itself through
`processMessageCall`, and settlement follows the fork's SELFDESTRUCT rule. -/
theorem processTransaction_canonical {benv : Benv} (h : benv.Canonical)
    {bout : BlockOutput} {tx : Tx} {index : Nat} {p}
    (hp : processTransaction benv bout tx index = .ok p) :
    State.Canonical p.1 := by
  unfold processTransaction at hp
  obtain ⟨b1, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨validationSender, _, hp⟩ := Except.bind_eq_ok hp
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
  have hqc := processMessageCall_canonical hmsgc (Except.mapError_eq_ok_iff.mp hq)
  exact State.Canonical.settleSelfdestructs
    (State.Canonical.addBal (State.Canonical.addBal hqc _ _) _ _) _ _

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
      exact processSystemTransaction_canonical h (Except.mapError_eq_ok_iff.mp hq)

/-- Every prefix of the request fold leaves a canonical state.

An induction on the contract list, so the proof does not grow when the list
does: Amsterdam's two extra contracts are covered by the same argument. -/
theorem runRequestContracts_canonical (idx : Nat) :
    ∀ (rs : List (UInt8 × Adr)) {benv : Benv}, benv.Canonical →
      ∀ {acc : List Bytes} {bal : BalBuilder} {p},
        runRequestContracts idx rs benv acc bal = .ok p → State.Canonical p.1
  | [], _, h, _, _, _, hp => by cases hp; exact h.1
  | _ :: rs, benv, h, acc, bal, p, hp => by
    unfold runRequestContracts at hp
    obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    exact runRequestContracts_canonical idx rs
      (by exact ⟨processCheckedSystemTransaction_canonical h hq, h.2⟩) hp

theorem processGeneralPurposeRequests_canonical {benv : Benv}
    (h : benv.Canonical) {bout : BlockOutput} {p}
    (hp : processGeneralPurposeRequests benv bout = .ok p) :
    State.Canonical p.1 := by
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at hp
  obtain ⟨dr, _, hp⟩ := Except.bind_eq_ok hp
  dsimp only at hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact runRequestContracts_canonical _ _ h hq

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
    processUncheckedSystemTransaction_canonical h (Except.mapError_eq_ok_iff.mp hq1)
  have hb2 : q2.1.Canonical :=
    processUncheckedSystemTransaction_canonical (by exact ⟨hb1, h.2⟩)
      (Except.mapError_eq_ok_iff.mp hq2)
  have hb3 : q3.1.Canonical :=
    applyTransactions_canonical _ (by exact ⟨hb2, h.2⟩) hq3
  obtain ⟨benvTxs, boutTxs⟩ := q3
  dsimp only at hp hb3
  -- The withdrawals pass is a pair literal; the access-list incorporation,
  -- the item rule and the built list carry no state.
  simp only [processWithdrawals] at hp
  obtain ⟨q4, hq4, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  have hc := processGeneralPurposeRequests_canonical
    (benv := benvTxs.withState (processWithdrawalsState benvTxs.state wds))
    ⟨processWithdrawalsState_canonical hb3.1 _, hb3.2⟩ hq4
  exact hc

/-- **Raw successful block transition preserves canonicality.** The output
chain's execution state is the body's final state, and its original state is
the input chain's. -/
theorem stateTransitionAt_canonical {f : Fork} {ch : BlockChain}
    (h : ch.Canonical) {block : Block} {ch'}
    (hp : stateTransitionAt f ch block = .ok ch') : ch'.Canonical := by
  rw [stateTransitionAt_eq_ok_iff] at hp
  unfold stateTransitionE at hp
  obtain ⟨u1, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨u2, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨u3, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨u4, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact applyBody_canonical (by exact ⟨h, h⟩) hq

theorem stateTransition_canonical {ch : BlockChain} (h : ch.Canonical)
    {block : Block} {ch'} (hp : stateTransition ch block = .ok ch') :
    ch'.Canonical :=
  stateTransitionAt_canonical (f := .prague) h hp

/-- Configured successful transition preserves canonicality. -/
theorem stateTransitionUsing_canonical {cfg : ChainConfig} {ch : BlockChain}
    (h : ch.Canonical) {block : Block} {ch'}
    (hp : stateTransitionUsing cfg ch block = .ok ch') : ch'.Canonical := by
  unfold stateTransitionUsing at hp
  obtain ⟨u1, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨r, _, hp⟩ := Except.bind_eq_ok hp
  exact stateTransitionAt_canonical (f := r) h hp

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
  by_cases h1 : max bout.blockGasUsed bout.blockStateGasUsed ≠ header.gasUsed
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
theorem stateTransitionAt_eq_ok {f : Fork} {ch ch' : BlockChain}
    {block : Block} (h : stateTransitionAt f ch block = .ok ch') :
    validateHeader f.ruleSet ch block.header = .ok () ∧
      ch'.blocks = appendBlock ch.blocks block ∧
      ch'.state.root = block.header.stateRoot := by
  rw [stateTransitionAt_eq_ok_iff] at h
  unfold stateTransitionE at h
  obtain ⟨u1, hvh, h⟩ := Except.bind_eq_ok h
  obtain ⟨u2, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨q, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨u3, hchk, h⟩ := Except.bind_eq_ok h
  obtain ⟨u4, _, h⟩ := Except.bind_eq_ok h
  cases u1
  cases u3
  cases u4
  cases h
  exact ⟨hvh, rfl,
    stateTransitionChecks_stateRoot (Except.mapError_eq_ok_iff.mp hchk)⟩

/-- The whole output witness of a successful transition from a checked
snapshot, assembled from what the transition already established: `Step 4`'s
canonicality preservation, header validation's parent link, the checked
envelope's wire well-formedness, and the block checks' own state-root
comparison. No root is recomputed. -/
theorem BlockChain.validContext_of_transition {f : Fork}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionAt f cc.val cb.block = .ok ch') :
    ch'.blocks.getLast? = some cb.block ∧ ch'.RetainedHistoryValid ∧
      ch'.state.Canonical ∧ ch'.state.root = cb.block.header.stateRoot := by
  obtain ⟨hvh, hblocks, hroot⟩ := stateTransitionAt_eq_ok h
  obtain ⟨hph, hnum⟩ := validateHeader_links cc.tip_is_last hvh
  refine ⟨?_, ?_, stateTransitionAt_canonical (f := f) cc.canonicalState h, hroot⟩
  · rw [hblocks]; exact appendBlock_getLast? _ _
  · exact BlockChain.retainedHistoryValid_appendBlock cc.retainedHistory
      cc.tip_is_last ⟨hnum, hph⟩ cb.rlpCanonical.1 hblocks

--------------- CHECKED TRANSITION AND IMPORT CORES ---------------

/-- The checked transition core: it accepts only a checked snapshot and a
canonical envelope, and it is definitionally the typed core on their values,
so every result about `stateTransitionE` transfers by `rfl`. Its output
witness is `CheckedBlockChain.ofTransition` below. -/
def stateTransitionChecked (f : Fork) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    Except TransitionError BlockChain :=
  stateTransitionE f cc.val cb.block

theorem stateTransitionChecked_eq (f : Fork) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    stateTransitionChecked f cc cb
      = stateTransitionE f cc.val cb.block := rfl

/-- The checked output of a successful checked transition.

This is the P0.2 fast path: the returned snapshot's four facts are proofs, not
computations, so a repeated client pays exactly one state-root computation --
the one `stateTransitionChecks` already performed on the child -- and never a
second one on the parent. -/
def CheckedBlockChain.ofTransition {f : Fork} {cc : CheckedBlockChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionChecked f cc cb = .ok ch') : CheckedBlockChain :=
  CheckedBlockChain.ofEvidence ch' cb.block
    (BlockChain.validContext_of_transition
      (stateTransitionAt_eq_ok_iff.mpr h)).1
    (BlockChain.validContext_of_transition
      (stateTransitionAt_eq_ok_iff.mpr h)).2.1
    (BlockChain.validContext_of_transition
      (stateTransitionAt_eq_ok_iff.mpr h)).2.2.1
    (BlockChain.validContext_of_transition
      (stateTransitionAt_eq_ok_iff.mpr h)).2.2.2

theorem CheckedBlockChain.ofTransition_val {f : Fork}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionChecked f cc cb = .ok ch') :
    (CheckedBlockChain.ofTransition h).val = ch' := rfl

theorem CheckedBlockChain.ofTransition_tip {f : Fork}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionChecked f cc cb = .ok ch') :
    (CheckedBlockChain.ofTransition h).tip = cb.block := rfl

/-- Inversion of the legacy canonical-envelope import adapter, stated over the
legacy transition name for stringly clients. -/
theorem addBlockToChainCanonical_eq_ok_inl {f : Fork}
    {chain chain' : BlockChain} {cb : CanonicalBlock}
    (h : addBlockToChainCanonical f chain cb = .ok (.inl chain')) :
    checkBlockRlpSize f.ruleSet.block cb.rawSize = .ok () ∧
      stateTransitionAt f chain cb.block = .ok chain' := by
  unfold addBlockToChainCanonical at h
  cases hE : addBlockToChainCanonicalE f chain cb with
  | error f => rw [hE] at h; exact absurd h (by simp [ImportOutcome.renderLegacy])
  | ok outcome =>
    rw [hE] at h
    cases outcome with
    | inr r => exact absurd h (by simp [ImportOutcome.renderLegacy])
    | inl ch =>
      simp only [ImportOutcome.renderLegacy, Except.ok.injEq, Sum.inl.injEq] at h
      subst h
      obtain ⟨hsize, hst⟩ := addBlockToChainCanonicalE_eq_ok_inl hE
      exact ⟨hsize, stateTransitionAt_eq_ok_iff.mpr hst⟩

/-- The checked import core: a checked snapshot in, and on the accepting
channel a snapshot whose witness is `CheckedBlockChain.ofImport`. The
validation order is the frozen one, unchanged -- this is the typed canonical
core with a checked input type, and it is the two-level shape P0.7 prescribes:
`Except ImportFailure (CheckedBlockChain-producing outcome ⊕ BlockRejection)`. -/
def addBlockToChainChecked (f : Fork) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) :=
  addBlockToChainCanonicalE f cc.val cb

/-- The checked output of a successful checked import. -/
def CheckedBlockChain.ofImport {f : Fork} {cc : CheckedBlockChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : addBlockToChainChecked f cc cb = .ok (.inl ch')) : CheckedBlockChain :=
  CheckedBlockChain.ofTransition
    (f := f) (cc := cc) (cb := cb)
    (addBlockToChainCanonicalE_eq_ok_inl h).2

theorem CheckedBlockChain.ofImport_val {f : Fork} {cc : CheckedBlockChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : addBlockToChainChecked f cc cb = .ok (.inl ch')) :
    (CheckedBlockChain.ofImport h).val = ch' := rfl

theorem CheckedBlockChain.ofImport_tip {f : Fork} {cc : CheckedBlockChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : addBlockToChainChecked f cc cb = .ok (.inl ch')) :
    (CheckedBlockChain.ofImport h).tip = cb.block := rfl

--------------- CONFIGURED CHECKED ENTRY POINTS ---------------

/-- The configured checked transition. The chain-ID check the raw configured
entry point performs is discharged by the pair's own witness rather than
repeated, and the snapshot is not rechecked at all; what remains is the rule
lookup, which is the only part that depends on the candidate's timestamp. -/
def stateTransitionConfigured (pc : ConfiguredChain) (cb : CanonicalBlock) :
    Except RulesLookupError (Except TransitionError BlockChain) := do
  let f ← pc.config.forkAt cb.block.header.timestamp
  .ok (stateTransitionE f pc.chain.val cb.block)

/-- The configured checked path agrees with the raw configured entry point on
every input, through the renderer: what it drops is exactly the check its
witness already carries. Replaces the pre-Step-10 same-carrier equation. -/
theorem stateTransitionConfigured_eq (pc : ConfiguredChain) (cb : CanonicalBlock) :
    (match stateTransitionConfigured pc cb with
      | .error e => .error e.render
      | .ok r => r.mapError TransitionError.render)
      = stateTransitionUsing pc.config pc.chain.val cb.block := by
  unfold stateTransitionConfigured stateTransitionUsing
  rw [pc.checkChainId_eq_ok]
  simp only [bind, Except.bind, Except.mapError]
  cases hr : pc.config.forkAt cb.block.header.timestamp <;>
    simp [Except.mapError, stateTransitionAt]

/-- The checked output of a successful configured checked transition. -/
def CheckedBlockChain.ofConfiguredTransition {pc : ConfiguredChain}
    {cb : CanonicalBlock} {r : Except TransitionError BlockChain} {ch' : BlockChain}
    (h : stateTransitionConfigured pc cb = .ok r) (hr : r = .ok ch') :
    CheckedBlockChain :=
  CheckedBlockChain.ofEvidence ch' cb.block
    (by
      obtain ⟨f, _, hst⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at hst
      exact (BlockChain.validContext_of_transition (cc := pc.chain)
        (stateTransitionAt_eq_ok_iff.mpr (hst ▸ hr))).1)
    (by
      obtain ⟨f, _, hst⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at hst
      exact (BlockChain.validContext_of_transition (cc := pc.chain)
        (stateTransitionAt_eq_ok_iff.mpr (hst ▸ hr))).2.1)
    (by
      obtain ⟨f, _, hst⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at hst
      exact (BlockChain.validContext_of_transition (cc := pc.chain)
        (stateTransitionAt_eq_ok_iff.mpr (hst ▸ hr))).2.2.1)
    (by
      obtain ⟨f, _, hst⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at hst
      exact (BlockChain.validContext_of_transition (cc := pc.chain)
        (stateTransitionAt_eq_ok_iff.mpr (hst ▸ hr))).2.2.2)

--------------- CHECKED/RAW BRIDGES (FOR STEP 11) ---------------

-- Stated so a downstream proof client can move between the raw names its
-- theorems are written about and the checked ones, without unfolding either
-- structure.

theorem stateTransitionChecked_eq_raw (f : Fork) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    stateTransitionChecked f cc cb
      = stateTransitionCanonical f cc.val cb := rfl

theorem addBlockToChainChecked_eq_raw (f : Fork) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    addBlockToChainChecked f cc cb
      = addBlockToChainCanonicalE f cc.val cb := rfl

/-- A raw typed import of bytes into a checked snapshot's value is the checked
import of the envelope those bytes decode to. -/
theorem addBlockToChainAtE_eq_checked {f : Fork} {cc : CheckedBlockChain}
    {blockRlp : Bytes} {block : Block} {hash : B256}
    (h : rlpToBlock blockRlp = .ok ⟨block, hash⟩) :
    addBlockToChainAtE f cc.val blockRlp
      = addBlockToChainChecked f cc (CanonicalBlock.ofDecode h) := by
  have hE := rlpToBlock_eq_ok_iff.mp h
  unfold addBlockToChainAtE addBlockToChainChecked
  split
  · rename_i e he
    rw [hE] at he
    exact absurd he (by simp)
  · rename_i f sh hb
    rw [hE] at hb
    simp only [Except.ok.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rfl

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
  { guardTestHeader with excessBlobGas := 2 ^ 64 }).isNone
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
    [balGuardA] [(balGuardA, 1)]) ==
  [(balGuardA, [], [1], [], [])]

-- A slot both read and written appears only among the changes.
#guard balGuardView (({} : BalBuilder).incorporate 1 balGuardPre
    (balGuardPre.setStorVal balGuardA 1 8) [balGuardA] [(balGuardA, 1)]) ==
  [(balGuardA, [(1, [(1, 8)])], [], [], [])]

-- Three transactions, then withdrawals, each incorporated under its own index
-- against the block's cumulative state, after a system call at index 0.
#guard
  let st0 := balGuardPre
  let stSys := st0.setStorVal balGuardB 3 4
  let st1 := stSys.setBal balGuardA 90
  let st2 := st1.setBal balGuardA 80
  let st3 := st2.setBal balGuardA 70
  let st4 := st3.setBal balGuardA 170
  let b := ({} : BalBuilder).incorporate 0 st0 stSys [balGuardB] []
  let b := b.incorporate 1 stSys st1 [balGuardA] []
  let b := b.incorporate 2 st1 st2 [balGuardA] []
  let b := b.incorporate 3 st2 st3 [balGuardA] []
  let b := b.incorporate 4 st3 st4 [balGuardA] []
  balGuardView b ==
    [(balGuardA, [], [], [(1, 90), (2, 80), (3, 70), (4, 170)], []),
     (balGuardB, [(3, [(0, 4)])], [], [], [])]

-- A created-then-self-destructed account leaves no state behind, so its
-- storage writes are no diff, and the slots `SSTORE` recorded are reads
-- (the pinned `destroyStorage` conversion).
#guard balGuardView (({} : BalBuilder).incorporate 1 balGuardPre balGuardPre
    [balGuardB] [(balGuardB, 5)]) ==
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

end Jaune
