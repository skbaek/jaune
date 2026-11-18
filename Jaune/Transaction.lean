import Jaune.Transaction.Parts
import Jaune.Sufficiency
import Jaune.MessageCall.Canonical
-- `List.IsChain` itself is Batteries; its infix/suffix closure lemmas, which
-- the retained-history predicate below reasons with, are Mathlib's.
import Mathlib.Data.List.Chain

namespace Jaune

open Jaune

/-!
# Transaction, block, and chain processing

This module holds every declaration that consumes the message-call driver
(`Frame.runTop`, `Jaune.MessageCall`), starting at `processMessageCall.create`,
together with the transaction, block, and chain-level machinery built on top of
it. It was split out of `Jaune.Execution` so that `Jaune.Sufficiency` could sit
between the driver and its first consumer.
-/

--------- TYPED SEMANTIC REASONS: TRANSACTION, BLOCK, IMPORT ---------

-- Declarations and renderers only (golden guards: `Jaune/Check/Transaction.lean`);
-- no producer moves here, no rendered message changes; Step 10 moves them.
--
-- Placement is frozen by `scripts/report-integrity-design.md` section 6:
-- every transition and import entry point is in this module, so the two
-- validation vocabularies and the three failure sums belong here. Their tag
-- constants stay where they are declared, in `Jaune/Machine.lean`, and this
-- module reads them; a tag and the constructor that renders under it are
-- pinned to each other by the golden guards in `Jaune/Check/Transaction.lean`.

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
  /-- A typed transaction whose type number exceeds the fork's `maxType`. -/
  | typePreFork (txType : Nat) (detail : ErrorDetail)
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
  | .typePreFork _ _ => typePreForkTag

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
  | .emptyAuthorizationList d | .typePreFork _ d => d

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
    .emptyAuthorizationList .none, .typePreFork 3 .none ]

/-- `B256` carries no `Repr` of its own; the block-rejection type below derives
one, and its `blockAccessListHash` reason now carries a hash as data. Rendered
through the hex `ToString`, which is how every hash prints elsewhere. -/
instance : Repr U256 where
  reprPrec h _ := .text (toString h)

/-- `Address` carries no `Repr` of its own either; the block-rejection type
below derives one, and its `systemContractCallFailed` reason carries the
contract's address as data. Rendered through the hex `ToString`, which is how
every address prints elsewhere. -/
instance : Repr Address where
  reprPrec a _ := .text (toString a)

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
  /-- Before Paris: a difficulty other than `calculateBlockDifficulty`'s. -/
  | invalidDifficulty (detail : ErrorDetail)
  /-- Before Paris: the block's ommers break a rule of `validateOmmers`. -/
  | invalidOmmers (detail : ErrorDetail)
  /-- Before Paris: an ommer's own header fails `validateHeader` against its
  retained parent, for `reason`. Rendered under the `invalidOmmers` tag, with
  the ommer's reason rendered in the detail text, by `detail` below: the
  specification returns the cause and only the renderer writes text (goal
  `jaune-shape-and-names-v1`, 3.2). -/
  | invalidOmmerHeader (reason : BlockValidationError)
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
  /-- A mandatory request-producing system call to `target` settled with
  `halt` (an exceptional halt or a revert). The pinned
  `process_checked_system_transaction` raises `InvalidBlock`; the corpus names
  it `BlockException.SYSTEM_CONTRACT_CALL_FAILED`, and it renders under the
  `systemContractCallFailed` tag, with the address and the halt written by
  `detail` below: the specification returns the cause and only the renderer
  writes text (goal `jaune-shape-and-names-v1`, 3.2). -/
  | systemContractCallFailed (target : Address) (halt : SettledHalt)
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
  | blockAccessListHash (computed : U256) (detail : ErrorDetail)
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
  | .invalidDifficulty _ => invalidDifficultyTag
  | .invalidOmmers _ => invalidOmmersTag
  | .invalidOmmerHeader _ => invalidOmmersTag
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
  | .systemContractCallFailed _ _ => systemContractCallFailedTag
  | .systemContractEmpty _ => systemContractEmptyTag
  | .blockRlpSizeExceeded _ => blockRlpSizeExceededTag
  | .headerFieldPresence _ => headerFieldPresenceTag
  | .blockAccessListHash _ _ => blockAccessListHashTag
  | .blockAccessListContent _ => blockAccessListContentTag
  | .blockAccessListFormat _ => blockAccessListFormatTag
  | .blockAccessListGasLimit _ => blockAccessListGasLimitTag

/-- The diagnostic payload of a block-rejection reason. The two structured
causes are written out here, and nowhere in the specification functions that
return them. -/
def BlockValidationError.detail : BlockValidationError → ErrorDetail
  | .gasLimitTooBig d | .gasLimitAdjustment d | .gasUsedOverflow d
  | .gasUsedMismatch d | .timestampOlderThanParent d | .blockNumber d
  | .baseFeePerGas d | .difficultyOverParis d | .ommersOverParis d
  | .invalidDifficulty d | .invalidOmmers d
  | .extraDataTooBig d | .unknownParent d | .unknownParentZero d
  | .stateRoot d | .transactionsRoot d | .receiptsRoot d | .logBloom d
  | .withdrawalsRoot d | .headerNonce d | .excessBlobGas d
  | .blobGasUsed d | .requestsHash d | .depositEventLayout d
  | .systemContractEmpty d | .blockRlpSizeExceeded d
  | .headerFieldPresence d
  | .blockAccessListContent d | .blockAccessListFormat d
  | .blockAccessListGasLimit d => d
  | .blockAccessListHash _ d => d
  | .invalidOmmerHeader reason =>
    .text s!"ommer header is invalid: {renderTagged reason.tag reason.detail}"
  | .systemContractCallFailed target halt =>
    .text s!"system contract ({target.toHex}) call failed: \
      {halt.render}"

/-- The one renderer for `BlockValidationError`. -/
def BlockValidationError.render (e : BlockValidationError) : String :=
  renderTagged e.tag e.detail

/-- Every block-rejection reason, for the completeness guards: one
representative per tag. `invalidOmmerHeader` renders under the `invalidOmmers`
tag, so it is not listed again. -/
def BlockValidationError.all : List BlockValidationError :=
  [ .gasLimitTooBig .none, .gasLimitAdjustment .none, .gasUsedOverflow .none,
    .gasUsedMismatch .none, .timestampOlderThanParent .none,
    .blockNumber .none, .baseFeePerGas .none, .difficultyOverParis .none,
    .ommersOverParis .none, .invalidDifficulty .none, .invalidOmmers .none,
    .extraDataTooBig .none, .unknownParent .none,
    .unknownParentZero .none, .stateRoot .none, .transactionsRoot .none,
    .receiptsRoot .none, .logBloom .none, .withdrawalsRoot .none,
    .headerNonce .none, .excessBlobGas .none, .blobGasUsed .none,
    .requestsHash .none, .depositEventLayout .none,
    .systemContractCallFailed default .revert, .systemContractEmpty .none,
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

/-! ### Amsterdam top-level preparation

The dual-gas fork prices state-dependent transaction dispatch in the top
frame, before bytecode starts.  The preparation machine therefore carries the
real top-frame meters and world.  A successful delegation phase commits its
state gas; a later preparation failure restores the transaction-entry
reservoir and world. -/

private abbrev AmsterdamDelegationResult := Devm × AdrSet × AdrSet

private def chargeNewAuthorityAmsterdam (state : StateGasRules)
    (authority : Address) (devm : Devm) : Execution :=
  if ¬ AccountExists devm.state authority then
    chargeStateGas state.newAccount devm
  else .ok devm

private def chargePaidAccountWriteAmsterdam (state : StateGasRules)
    (authority : Address) (devm : Devm) (paidWrites : AdrSet) :
    Except (EvmError × Devm) (Devm × AdrSet) :=
  if paidWrites.contains authority then
    .ok ⟨devm, paidWrites⟩
  else do
    let devm ← chargeGas state.accountWrite devm
    .ok ⟨devm, paidWrites.insert authority⟩

private def chargeAuthBaseAmsterdam (state : StateGasRules) (msg : Msg)
    (authority target : Address) (devm : Devm) (delegationSetFor : AdrSet) :
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

def applyValidatedDelegationAmsterdam (state : StateGasRules)
    (msg : Msg) (authority target : Address) (devm : Devm)
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
    (auth : Authorization) (devm : Devm) (paidWrites delegationSetFor : AdrSet) :
    Except (EvmError × Devm) AmsterdamDelegationResult := do
  if auth.chainId != msg.benv.stat.chainId.toU256 && auth.chainId != 0 then
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
    List Authorization → Devm → AdrSet → AdrSet →
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
      storageWrites := devm.world.storageWrites
    }
    tenv := {msg.tenv with transientStorage := devm.transientStorage}
    accessedAddresses := devm.accessedAddresses
    accessedStorageKeys := devm.accessedStorageKeys
  }

def resolveTopLevelCallAmsterdam (msg : Msg) (devm : Devm) :
    Except (EvmError × Devm) (Msg × Devm) := do
  let ⟨delegated, codeAddress, accessCost⟩ :=
    msg.benv.stat.rules.delegationCost devm msg.currentTarget
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
      accountHasCodeOrNonce devm.state msg.currentTarget
    if isCollision then
      .error ⟨.halt (.addressCollision .none), devm⟩
    else do
      let devm ←
        if (msg.benv.stat.origState.get msg.currentTarget).isEmpty then
          chargeStateGas state.newAccount devm
        else .ok devm
      .ok ⟨preparedTopLevelMsg msg devm, devm⟩
  else do
    let devm ←
      if msg.value != 0 && decide (devm.state.get msg.currentTarget).isEmpty then
        chargeStateGas state.newAccount devm
      else .ok devm
    resolveTopLevelCallAmsterdam msg devm

private def finishTopLevelAmsterdam (state : StateGasRules) (msg : Msg)
    (devm : Devm) : Except (EvmError × Devm) (Msg × Devm) :=
  let devm :=
    if msg.tenv.stat.auths.isEmpty then devm else devm.commitStateGas
  dispatchTopLevelAmsterdam state msg devm

/-- Build the machine a top-level Amsterdam message call starts from: the
initial `Devm`, then the authorization tuples of an EIP-7702 transaction, then
the state-gas commit and the creation/call dispatch that `create_evm` performs.
Amsterdam-only: the pre-Amsterdam lane (`rules.stateGas = none`) never reaches
it, and `processTopLevelAmsterdam` is its only caller outside the guards. -/
def prepareTopLevelAmsterdam (state : StateGasRules) (msg : Msg) :
    Except (EvmError × Devm) (Msg × Devm) := do
  let devm := initDevm msg
  let devm ←
    if msg.tenv.stat.auths.isEmpty then .ok devm
    else setDelegationAmsterdam state msg devm
  finishTopLevelAmsterdam state msg devm

/-- Top-level resolution warms the delegate without a nested-call surcharge. -/
def Msg.resolveCodeDelegation (msg : Msg) : Msg :=
  match msg.benv.stat.rules.delegatedCodeAddress msg.code with
  | none => msg
  | some address =>
    { msg with
      disablePrecompiles := true
      accessedAddresses := msg.accessedAddresses.insert address
      code := msg.benv.state.getCode address
      codeAddress := some address }

theorem Msg.resolveCodeDelegation_disabled (msg : Msg)
    (h : msg.benv.stat.rules.delegationEnabled = false) :
    msg.resolveCodeDelegation = msg := by
  simp only [resolveCodeDelegation, ForkRules.delegatedCodeAddress_disabled h msg.code]

theorem Msg.resolveCodeDelegation_enabled (msg : Msg)
    (h : msg.benv.stat.rules.delegationEnabled = true) :
    msg.resolveCodeDelegation =
      (match getDelegatedCodeAddress msg.code with
      | none => msg
      | some address =>
        { msg with
          disablePrecompiles := true
          accessedAddresses := msg.accessedAddresses.insert address
          code := msg.benv.state.getCode address
          codeAddress := some address }) := by
  simp only [resolveCodeDelegation, ForkRules.delegatedCodeAddress_enabled h]

theorem Msg.resolveCodeDelegation_canonical {msg : Msg} (h : msg.Canonical) :
    msg.resolveCodeDelegation.Canonical := by
  unfold resolveCodeDelegation
  split <;> exact h

/-! ### The top-level message call on the four-part chain

The pre-frame steps are kept: the pre-Amsterdam collision test for a creation, the ordinary
authorization and delegation resolution for a call, and under Amsterdam the preparation with
its failure settlement. The frame then runs by `Frame.runTop` and its `Frame.Result` is rendered
by `Frame.output` or `Frame.outputAmsterdam`. -/

/-- Ordinary top-level authorization follows the active fork's delegation rule. -/
def processMessageCall.authorize (msg : Msg) : Except EvmError (Msg × Nat) :=
  if !msg.benv.stat.rules.delegationEnabled || msg.tenv.stat.auths.isEmpty then
    .ok ⟨msg, 0⟩
  else do
    let ⟨delegated, refund⟩ ← setDelegation msg
    .ok ⟨delegated, refund.toNat⟩

theorem processMessageCall.authorize_disabled (msg : Msg)
    (h : msg.benv.stat.rules.delegationEnabled = false) :
    authorize msg = .ok ⟨msg, 0⟩ := by
  simp only [authorize, h, Bool.not_false, Bool.true_or, ↓reduceIte]

theorem processMessageCall.authorize_enabled (msg : Msg)
    (h : msg.benv.stat.rules.delegationEnabled = true) :
    authorize msg =
      (if msg.tenv.stat.auths.isEmpty then .ok ⟨msg, 0⟩ else do
        let ⟨delegated, refund⟩ ← setDelegation msg
        .ok ⟨delegated, refund.toNat⟩) := by
  simp only [authorize, h, Bool.not_true, Bool.false_or]

/-- The ordinary top-level authorization leaves a message with a code address: an
unchanged message keeps its own, and `setDelegation` fails closed without one. -/
theorem processMessageCall.authorize_codeAddress {msg : Msg} {q : Msg × Nat}
    (h : authorize msg = .ok q) (hc : msg.codeAddress ≠ none) :
    q.1.codeAddress ≠ none := by
  unfold authorize at h
  split at h
  · cases h; exact hc
  · obtain ⟨pair, hpair, h⟩ := Except.bind_eq_ok h
    cases h
    unfold setDelegation at hpair
    obtain ⟨⟨m, r⟩, -, hpair⟩ := Except.bind_eq_ok hpair
    dsimp only at hpair
    split at hpair
    · simp [bind, Except.bind] at hpair
    · rename_i ca hca
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hpair
      subst hpair
      simp [hca]

theorem processMessageCall.authorize_canonical {msg : Msg}
    (h : msg.Canonical) {p} (hp : authorize msg = .ok p) :
    p.1.Canonical := by
  unfold authorize at hp
  split at hp
  · cases hp; exact h
  · obtain ⟨pair, hpair, hp⟩ := Except.bind_eq_ok hp
    cases hp
    exact setDelegation_canonical h hpair

/-- Settle a top-level Amsterdam message call whose preparation failed before
the interpreter was entered: a halt forfeits the remaining gas and reports the
pre-call state with the reads preparation had already recorded, while every
other error propagates unchanged. The machine's world is not read: the reported
state is the message's. Amsterdam-only, and reached only from
`processTopLevelAmsterdam`'s error branch. -/
def settleTopLevelPreparationFailure (msg : Msg) (error : EvmError)
    (devm : Devm) : Except EvmError (State × MsgCallOutput) :=
  match error with
  | .halt reason =>
    let devm := (devm.restoreStateGasToEntry msg.stateGasGrant).forfeitRemainingGas
    -- The reads the preparation recorded before it halted -- the authorities
    -- of every processed tuple, the recipient once dispatch loaded it -- stay
    -- in the block-level access list: `incorporate_tx_into_block` runs for a
    -- halted transaction too, and a read survives the rollback (EIP-7928).
    .ok ⟨msg.benv.state, {
      accountReads := devm.meta.accountReads
      storageReads := devm.meta.storageReads
      storageWrites := msg.benv.storageWrites
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

/-- Run one top-level Amsterdam message call: prepare the machine, settle a
preparation failure, or run the top frame whose checkpoint is the prepared state
and render its result. Amsterdam-only. -/
def processTopLevelAmsterdam (state : StateGasRules) (msg : Msg) (isCreate : Bool) :
    Except EvmError (State × MsgCallOutput) :=
  match prepareTopLevelAmsterdam state msg with
  | .error ⟨error, devm⟩ => settleTopLevelPreparationFailure msg error devm
  | .ok ⟨msg, devm⟩ => do
    let f : Frame := ⟨Message.ofTop msg isCreate, Frame.State.ofDevm devm⟩
    let r ← (Frame.runTop f).mapError Fault.toEvmError
    f.outputAmsterdam r

def processMessageCall.create (msg : Msg) :
    Except EvmError (State × MsgCallOutput) := do
  match msg.benv.stat.rules.stateGas with
  | none =>
    if accountHasCodeOrNonce msg.benv.state msg.currentTarget then
      return ⟨msg.benv.state,
        { gasLeft := 0, refundCounter := 0, logs := [],
          accountsToDelete := .emptyWithCapacity,
          error := .some (.halt (.addressCollision .none)), returnData := [] }⟩
    else
      let f := Frame.ofTop msg true
      let r ← (Frame.runTop f).mapError Fault.toEvmError
      f.output 0 r
  | some state => processTopLevelAmsterdam state msg true

def processMessageCall.call (msg : Msg) :
    Except EvmError (State × MsgCallOutput) := do
  match msg.benv.stat.rules.stateGas with
  | none =>
    let ⟨delegated, authorizationRefund⟩ ← processMessageCall.authorize msg
    let f := Frame.ofTop delegated.resolveCodeDelegation false
    let r ← (Frame.runTop f).mapError Fault.toEvmError
    f.output authorizationRefund r
  | some state => processTopLevelAmsterdam state msg false

def processMessageCall (msg : Msg) :
    Except EvmError (State × MsgCallOutput) := do
  if msg.target.isNone then
    processMessageCall.create msg
  else
    processMessageCall.call msg

def Transaction.isEip4844 (tx : Transaction) : Bool :=
  match tx.type with
  | .eip4844 _ _ _ _ _ _ _ => true
  | _ => false

def getTotalBlobGas (tx: Transaction) : Nat :=
  match tx.type with
  | .eip4844 _ _ _ _ _ _ blobHashes => Gas.perBlob * blobHashes.length
  | _ => 0

structure Receipt : Type where
  status : Bool
  cumulativeGasUsed : Nat
  logsBloom : Bytes
  logs : List Log

/-! ### EIP-7928: the block-level access list (goal C, fixed decisions 2–4)

A block-scoped builder beside `BlockOutput`, fed once per incorporation --
each pre-execution system call at index 0, the `i`-th transaction at `i + 1`,
the withdrawals batch and each request-producing system call at `n + 1` --
with account-field changes and explicit surviving storage writes, netted
against the state at the start of that index, and with the read sets the
interpreter recorded (`Meta.accountReads`,
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
structure BlockAccessListAccount : Type where
  storageChanges : Std.TreeMap U256 (List (Nat × U256)) compare := .empty
  storageReads : Std.TreeMap U256 Unit compare := .empty
  balanceChanges : List (Nat × U256) := []
  nonceChanges : List (Nat × UInt64) := []
  codeChanges : List (Nat × ByteArray) := []

private structure BlockAccessListIndexStartAccount : Type where
  balance : U256
  nonce : UInt64
  code : ByteArray

/-- `BlockAccessListBuilder` at the pin: address ↦ its data. Per-index start
values are captured only for fields that change, so calls sharing an index net
against the first value at that index without retaining whole state snapshots. -/
structure BlockAccessListBuilder : Type where
  accounts : Std.TreeMap Address BlockAccessListAccount compare := .empty
  indexStartAccounts : Std.TreeMap Nat (Std.TreeMap Address BlockAccessListIndexStartAccount compare) compare := .empty
  indexStartStorage :
    Std.TreeMap Nat (Std.TreeMap Address (Std.TreeMap U256 U256 compare) compare) compare := .empty

namespace BlockAccessListAccount

/-- Replace the entry at `idx` or append: only the final value per index is
kept (`add_storage_write`, `add_balance_change`, `add_code_change`). -/
private def upsert {α : Type} (l : List (Nat × α)) (idx : Nat) (v : α) : List (Nat × α) :=
  if l.any (·.1 = idx) then l.map (fun c => if c.1 = idx then (idx, v) else c)
  else l ++ [(idx, v)]

def addStorageWrite (acc : BlockAccessListAccount) (slot : U256) (idx : Nat) (v : U256) : BlockAccessListAccount :=
  {acc with storageChanges :=
    acc.storageChanges.insert slot (upsert (acc.storageChanges.getD slot []) idx v)}

def addStorageRead (acc : BlockAccessListAccount) (slot : U256) : BlockAccessListAccount :=
  {acc with storageReads := acc.storageReads.insert slot ()}

def removeStorageWrite (acc : BlockAccessListAccount) (slot : U256) (idx : Nat) : BlockAccessListAccount :=
  let changes := (acc.storageChanges.getD slot []).filter (fun c => c.1 != idx)
  {acc with storageChanges :=
    if changes.isEmpty then acc.storageChanges.erase slot
    else acc.storageChanges.insert slot changes}

def addBalanceChange (acc : BlockAccessListAccount) (idx : Nat) (v : U256) : BlockAccessListAccount :=
  {acc with balanceChanges := upsert acc.balanceChanges idx v}

def removeBalanceChange (acc : BlockAccessListAccount) (idx : Nat) : BlockAccessListAccount :=
  {acc with balanceChanges := acc.balanceChanges.filter (fun c => c.1 != idx)}

/-- `add_nonce_change` keeps the highest nonce per index. -/
def addNonceChange (acc : BlockAccessListAccount) (idx : Nat) (n : UInt64) : BlockAccessListAccount :=
  {acc with nonceChanges :=
    match acc.nonceChanges.find? (·.1 = idx) with
    | some ⟨_, old⟩ => if old < n then upsert acc.nonceChanges idx n else acc.nonceChanges
    | none => acc.nonceChanges ++ [(idx, n)]}

def removeNonceChange (acc : BlockAccessListAccount) (idx : Nat) : BlockAccessListAccount :=
  {acc with nonceChanges := acc.nonceChanges.filter (fun c => c.1 != idx)}

def addCodeChange (acc : BlockAccessListAccount) (idx : Nat) (code : ByteArray) : BlockAccessListAccount :=
  {acc with codeChanges := upsert acc.codeChanges idx code}

def removeCodeChange (acc : BlockAccessListAccount) (idx : Nat) : BlockAccessListAccount :=
  {acc with codeChanges := acc.codeChanges.filter (fun c => c.1 != idx)}

end BlockAccessListAccount

namespace BlockAccessListBuilder

/-- `ensure_account`/`add_touched_account`: an entry with nothing in it. -/
def ensure (b : BlockAccessListBuilder) (a : Address) : BlockAccessListBuilder :=
  if b.accounts.contains a then b else {b with accounts := b.accounts.insert a {}}

def modify (b : BlockAccessListBuilder) (a : Address) (f : BlockAccessListAccount → BlockAccessListAccount) : BlockAccessListBuilder :=
  {b with accounts := b.accounts.insert a (f (b.accounts.getD a {}))}

private def startAccount (b : BlockAccessListBuilder) (idx : Nat) (address : Address) (account : Account) :
    BlockAccessListBuilder × BlockAccessListIndexStartAccount :=
  let atIndex := b.indexStartAccounts.getD idx .empty
  match atIndex.get? address with
  | some start => (b, start)
  | none =>
    let start : BlockAccessListIndexStartAccount :=
      {balance := account.balance, nonce := account.nonce, code := account.code}
    ({b with indexStartAccounts := b.indexStartAccounts.insert idx (atIndex.insert address start)}, start)

private def startStorage (b : BlockAccessListBuilder) (idx : Nat) (address : Address) (slot value : U256) :
    BlockAccessListBuilder × U256 :=
  let atIndex := b.indexStartStorage.getD idx .empty
  let atAddress := atIndex.getD address .empty
  match atAddress.get? slot with
  | some start => (b, start)
  | none =>
    let atAddress := atAddress.insert slot value
    let atIndex := atIndex.insert address atAddress
    ({b with indexStartStorage := b.indexStartStorage.insert idx atIndex}, value)

/-- `update_builder_from_tx`: the incorporated state's writes against values
captured at the start of `idx`, then the merge of the read sets. An address or
slot restored by a later operation sharing `idx` removes only that index's
change, leaving changes from other indices and the recorded reads intact. -/
def incorporate (b : BlockAccessListBuilder) (idx : Nat) (pre post : State)
    (accountReads : List Address) (storageReads storageWrites : List (Address × U256)) : BlockAccessListBuilder :=
  let addrs : List Address := (pre.keys ++ post.keys).eraseDups
  let b := addrs.foldl (init := b) fun b a =>
    let acPre := pre.get a
    let acPost := post.get a
    let accountChanged :=
      acPre.balance ≠ acPost.balance || acPre.nonce ≠ acPost.nonce || acPre.code.data ≠ acPost.code.data
    let ⟨b, acStart⟩ :=
      if accountChanged then b.startAccount idx a acPre
      else (b, {balance := acPre.balance, nonce := acPre.nonce, code := acPre.code})
    let b :=
      if acStart.balance ≠ acPost.balance then b.modify a (·.addBalanceChange idx acPost.balance)
      else if accountChanged then b.modify a (·.removeBalanceChange idx) else b
    let b :=
      if acStart.nonce ≠ acPost.nonce then b.modify a (·.addNonceChange idx acPost.nonce)
      else if accountChanged then b.modify a (·.removeNonceChange idx) else b
    let b :=
      if acStart.code.data ≠ acPost.code.data then b.modify a (·.addCodeChange idx acPost.code)
      else if accountChanged then b.modify a (·.removeCodeChange idx) else b
    b
  -- Only explicit writes participate. Storage clearing is not a write of zero
  -- to every old slot. Even a same-value write visits the index-start cache,
  -- so another system operation at this index can remove an earlier change.
  let b := storageWrites.foldl (init := b) fun b ⟨a, k⟩ =>
    let ⟨b, startValue⟩ := b.startStorage idx a k ((pre.get a).storage.get k)
    let value := (post.get a).storage.get k
    if startValue ≠ value then b.modify a (·.addStorageWrite k idx value)
    else b.modify a (·.removeStorageWrite k idx)
  let b := storageReads.foldl (init := b) fun b ⟨a, k⟩ => b.modify a (·.addStorageRead k)
  accountReads.foldl (init := b) fun b a => b.ensure a

end BlockAccessListBuilder

/-- `AccountChanges` at the pin, in its dataclass field order. -/
structure BlockAccessListAccountChanges : Type where
  address : Address
  storageChanges : List (U256 × List (Nat × U256))
  storageReads : List U256
  balanceChanges : List (Nat × U256)
  nonceChanges : List (Nat × UInt64)
  codeChanges : List (Nat × ByteArray)

/-- The built list: `BlockAccessList` at the pin. -/
abbrev BlockAccessList : Type := List BlockAccessListAccountChanges

private def sortByIndex {α : Type} (l : List (Nat × α)) : List (Nat × α) :=
  l.mergeSort (fun x y => x.1 ≤ y.1)

/-- `_build_from_builder`: accounts by address, slots by number, changes by
index, and a slot that appears among the changes excluded from the reads. -/
def BlockAccessListBuilder.build (b : BlockAccessListBuilder) : BlockAccessList :=
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
private def natRlpItem (n : Nat) : Rlp.Item := .bytes n.toBytes

def BlockAccessListAccountChanges.toRlpItem (c : BlockAccessListAccountChanges) : Rlp.Item :=
  .list [
    .bytes c.address.toBytes,
    .list (c.storageChanges.map fun ⟨slot, cs⟩ =>
      .list [natRlpItem slot.toNat,
             .list (cs.map fun ⟨i, v⟩ => .list [natRlpItem i, natRlpItem v.toNat])]),
    .list (c.storageReads.map fun k => natRlpItem k.toNat),
    .list (c.balanceChanges.map fun ⟨i, v⟩ => .list [natRlpItem i, natRlpItem v.toNat]),
    .list (c.nonceChanges.map fun ⟨i, n⟩ => .list [natRlpItem i, natRlpItem n.toNat]),
    .list (c.codeChanges.map fun ⟨i, code⟩ => .list [natRlpItem i, .bytes code.toList]) ]

def BlockAccessList.toRlpItem (l : BlockAccessList) : Rlp.Item := .list (l.map BlockAccessListAccountChanges.toRlpItem)

/-- `rlp.encode(block_access_list)`. -/
def BlockAccessList.encode (l : BlockAccessList) : Bytes := l.toRlpItem.toBytes

/-- `hash_block_access_list`. -/
def BlockAccessList.hash (l : BlockAccessList) : U256 := l.encode.keccak

/-- `validate_block_access_list_gas_limit`'s count: every address, plus every
unique storage slot across its changes and reads (the reads already exclude
the changed slots at build time). -/
def BlockAccessList.itemCount (l : BlockAccessList) : Nat :=
  l.foldl (fun n c => n + 1 + c.storageChanges.length + c.storageReads.length) 0

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
      if a.toRlpItem.toBytes = b.toRlpItem.toBytes then dedupAdjacent (b :: rest)
      else a :: dedupAdjacent (b :: rest)
    | l => l

structure BlockOutput : Type where
  blockGasUsed : Nat
  /-- State-gas usage is an independent block-capacity dimension under
  Amsterdam. The default keeps every legacy construction source-compatible. -/
  blockStateGasUsed : Nat := 0
  /-- Sender-facing gas after refunds, accumulated for receipt encoding. -/
  cumulativeGasUsed : Nat := 0
  transactionsTrie : Std.TreeMap Bytes Transaction compare
  receiptsTrie : Std.TreeMap Bytes (Fin 5 × Receipt) compare
  receiptKeys : List Bytes
  blockLogs : List Log
  withdrawalsTrie : Std.TreeMap Bytes Withdrawal compare
  blobGasUsed : Nat
  requests : List Bytes
  /-- EIP-7928: the block-level access-list builder, fed at every incorporation
  under `rules.bal = some _`; untouched otherwise. Defaulted so that every
  `BlockOutput` literal keeps elaborating. -/
  blockAccessListBuilder : BlockAccessListBuilder := {}
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
    (benv : Benv) (blockOut : BlockOutput) (tx : Transaction) :
    Except TxValidationError Nat :=
  let executionGasAvailable := benv.stat.blockGasLimit - blockOut.blockGasUsed
  let blobGasAvailable := benv.stat.rules.blob.max - blockOut.blobGasUsed
  let executionGasRequired :=
    match benv.stat.rules.stateGas with
    | none => tx.gasLimit
    | some _ => min (benv.stat.rules.tx.maxGas.getD tx.gasLimit) tx.gasLimit
  if executionGasRequired > executionGasAvailable then
    .error <| .gasAllowanceExceeded <| .text
      s!"transaction execution gas = {executionGasRequired} > \
         block execution gas available = {executionGasAvailable}"
  else
    match benv.stat.rules.stateGas with
    | some _ =>
      let stateGasAvailable :=
        benv.stat.blockGasLimit - blockOut.blockStateGasUsed
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
    if maxGasFee > U256.max.toNat then
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
    if maxGasFee > U256.max.toNat then
      .error <| .gasPriceProductOverflow <| .text
        s!"gas * gas price = {maxGasFee} > \
           2^256 - 1"
    else
      .ok ⟨gasPrice, maxGasFee⟩

def checkTransactionGasFee (benv : Benv) (tx : Transaction) :
    Except TxValidationError (Nat × Nat) :=
  match tx.type with
  | .legacy gasPrice _ =>
    checkTransactionLegacyGasFee benv.stat.baseFeePerGas tx.gasLimit gasPrice
  | .eip2930 _ gasPrice _ _ =>
    checkTransactionLegacyGasFee benv.stat.baseFeePerGas tx.gasLimit gasPrice
  | .eip1559 _ maxPriorityFee maxFee _ _ =>
    checkTransactionDynamicGasFee benv.stat.baseFeePerGas tx.gasLimit
      maxPriorityFee maxFee
  | .eip4844 _ maxPriorityFee maxFee _ _ _ _ =>
    checkTransactionDynamicGasFee benv.stat.baseFeePerGas tx.gasLimit
      maxPriorityFee maxFee
  | .eip7702 _ maxPriorityFee maxFee _ _ _ =>
    checkTransactionDynamicGasFee benv.stat.baseFeePerGas tx.gasLimit
      maxPriorityFee maxFee

/-- Enforce the fork's per-transaction blob-count limit, when one is active. -/
def checkTransactionBlobCount (limits : TransactionLimits)
    (blobHashes : List U256) : Except TxValidationError Unit :=
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
    (benv : Benv) (tx : Transaction) (maxGasFee : Nat) :
    Except TxValidationError (Nat × List U256) :=
  match tx.type with
  | .eip4844 _ _ _ _ _ maxBlobFee blobHashes => do
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
        getBaseFeePerBlobGas benv.stat.rules.blob benv.stat.excessBlobGas
      if maxBlobFee < blobGasPrice then
        .error <| .insufficientMaxFeePerBlobGas <|
          .text "insufficient max fee per blob gas"
      else
        .ok ⟨maxGasFee + getTotalBlobGas tx * maxBlobFee, blobHashes⟩
  | _ => .ok ⟨maxGasFee, []⟩

def checkTransactionReceiver (tx : Transaction) : Except TxValidationError Unit :=
  if tx.isEip4844 then
    if tx.type.to?.isNone then
      .error <| .type3ContractCreation <|
        .text "type-3 transactions cannot create contracts"
    else
      .ok ()
  else
    .ok ()

def checkTransactionAuthorizationList (tx : Transaction) : Except TxValidationError Unit :=
  match tx.type with
  | .eip7702 _ _ _ _ _ [] =>
    .error <| .emptyAuthorizationList <| .text "empty authorization list"
  | _ => .ok ()

/-- A legacy `v` that encodes a chain identifier wider than 64 bits never names
the chain: sender recovery refuses it as a bad signature. -/
theorem recoverSender_error_of_wide_legacy_v (chainId : UInt64) (tx : Transaction)
    {gasPrice : Nat} {receiver : Option Address}
    (htype : tx.type = .legacy gasPrice receiver) (hwide : 2 ^ 64 ≤ (tx.v - 35) / 2) :
    ∃ d, recoverSender chainId tx = .error (.invalidSignature d) := by
  have hc := chainId.toNat_lt_size
  have hsize : UInt64.size = 2 ^ 64 := rfl
  have h1 : tx.v ≠ 27 ∧ tx.v ≠ 28 := by omega
  have h2 : ¬ (tx.v = 35 + chainId.toNat * 2 ∨ tx.v = 36 + chainId.toNat * 2) := by omega
  unfold recoverSender
  simp only [bind, Except.bind, htype]
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · cases hs : tx.signingHash with
      | none => exact ⟨_, rfl⟩
      | some hash =>
        simp [Option.toExcept, h1, h2, Except.assert]

/-- EIP-155 chain check. A legacy `v` below 35 or encoding a chain identifier
wider than 64 bits is left to `recoverSender`, which refuses it as a bad
signature (`recoverSender_error_of_wide_legacy_v`), the pinned `chain_id`'s
`InvalidSignatureError("bad v")`. -/
def checkTransactionChainId (benv : Benv) (tx : Transaction) : Except TxValidationError Unit :=
  match tx.type with
  | .legacy _ _ =>
    if tx.v < 35 || 2 ^ 64 ≤ (tx.v - 35) / 2 || (tx.v - 35) / 2 = benv.stat.chainId.toNat then .ok ()
    else .error <| .invalidChainId <| .text
      s!"transaction chain ID = {(tx.v - 35) / 2}"
  | .eip2930 chainId _ _ _
  | .eip1559 chainId _ _ _ _
  | .eip4844 chainId _ _ _ _ _ _
  | .eip7702 chainId _ _ _ _ _ =>
    if chainId = benv.stat.chainId then .ok ()
    else .error <| .invalidChainId <| .text s!"transaction chain ID = {chainId}"

def checkTransactionSenderCode (senderAccount : Account) :
    Except TxValidationError Unit :=
  if ¬ (senderAccount.code.isEmpty ∨ isValidDelegation senderAccount.code) then
    .error <| .senderNotEoa <| .text "sender has non-delegation code"
  else
    .ok ()

def checkTransactionSenderAccount
    (senderAccount : Account) (tx : Transaction) (maxGasFee : Nat) :
    Except TxValidationError Unit :=
  if senderAccount.nonce > tx.nonce then
    .error <| .nonceMismatchTooLow <| .text
      s!"transaction nonce = {tx.nonce.toNat} < \
         sender nonce = {senderAccount.nonce.toNat}"
  else if senderAccount.nonce < tx.nonce then
    .error <| .nonceMismatchTooHigh <| .text
      s!"transaction nonce = {tx.nonce.toNat} > \
         sender nonce = {senderAccount.nonce.toNat}"
  else if senderAccount.balance.toNat < maxGasFee + tx.value then
    .error <| .insufficientAccountFunds <| .text
      s!"sender balance = \
         {senderAccount.balance.toNat} < max gas fee = {maxGasFee} + \
         transaction value = {tx.value}"
  else
    checkTransactionSenderCode senderAccount

/-- Fork-aware sender code admission, retaining the raw EIP-7702 helper. -/
def checkTransactionSenderCodeFor (rules : ForkRules) (senderAccount : Account) :
    Except TxValidationError Unit :=
  if rules.delegationEnabled then checkTransactionSenderCode senderAccount
  else if senderAccount.code.isEmpty then .ok ()
  else .error <| .senderNotEoa <| .text "sender has non-delegation code"

/-- Keep nonce, funds and existing code failures ahead of historical code admission. -/
def checkTransactionSenderAccountFor (rules : ForkRules)
    (senderAccount : Account) (tx : Transaction) (maxGasFee : Nat) :
    Except TxValidationError Unit := do
  checkTransactionSenderAccount senderAccount tx maxGasFee
  checkTransactionSenderCodeFor rules senderAccount

theorem checkTransactionSenderCodeFor_enabled {rules : ForkRules}
    (h : rules.delegationEnabled = true) (senderAccount : Account) :
    checkTransactionSenderCodeFor rules senderAccount =
      checkTransactionSenderCode senderAccount := by
  simp only [checkTransactionSenderCodeFor, h, ↓reduceIte]

theorem checkTransactionSenderCodeFor_disabled {rules : ForkRules}
    (h : rules.delegationEnabled = false) (senderAccount : Account) :
    checkTransactionSenderCodeFor rules senderAccount =
      (if senderAccount.code.isEmpty then .ok ()
       else .error (.senderNotEoa (.text "sender has non-delegation code"))) := by
  simp only [checkTransactionSenderCodeFor, h, Bool.false_eq_true, ↓reduceIte]

theorem checkTransactionSenderAccountFor_enabled {rules : ForkRules}
    (h : rules.delegationEnabled = true) (senderAccount : Account) (tx : Transaction)
    (maxGasFee : Nat) :
    checkTransactionSenderAccountFor rules senderAccount tx maxGasFee =
      checkTransactionSenderAccount senderAccount tx maxGasFee := by
  unfold checkTransactionSenderAccountFor
  rw [checkTransactionSenderCodeFor_enabled h]
  unfold checkTransactionSenderAccount
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · unfold checkTransactionSenderCode
        split <;> rfl

theorem checkTransactionSenderAccountFor_error (rules : ForkRules)
    (senderAccount : Account) (tx : Transaction) (maxGasFee : Nat) (error : TxValidationError)
    (h : checkTransactionSenderAccount senderAccount tx maxGasFee = .error error) :
    checkTransactionSenderAccountFor rules senderAccount tx maxGasFee = .error error := by
  simp only [checkTransactionSenderAccountFor, h, Bind.bind, Except.bind]

/-- The whole transaction admission check. Its carrier is the transition union
because it joins two typed channels: every rule above is a
`TxValidationError`, while sender recovery reports on the cryptographic
channel and is the one reason here that is not a validation rule. -/
def checkTransaction (benv : Benv) (blockOut : BlockOutput) (tx : Transaction) :
    Except TransitionError (Address × Nat × List U256 × Nat) := do
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
    (checkTransactionSenderAccountFor benv.stat.rules senderAccount tx maxGasFee)
  .ok ⟨
    senderAddress,
    effectiveGasPrice,
    blobVersionedHashes,
    txBlobGasUsed
  ⟩

/-- Prague's intrinsic-cost switches: 16-gas nonzero bytes, calldata floor on,
coinbase pre-warmed. -/
@[simp] theorem pragueRules_txr_dataNonZero : pragueRules.transactionRules.dataNonZero = 16 := rfl
@[simp] theorem pragueRules_txr_calldataFloor : pragueRules.transactionRules.calldataFloor = true := rfl
@[simp] theorem pragueRules_txr_warmCoinbase : pragueRules.transactionRules.warmCoinbase = true := rfl

/-- The transaction's intrinsic cost and its calldata floor.

The five numbers this formula reads that Amsterdam reprices arrive through
`gas` rather than through the globals that used to hold them: the base cost,
the two access-list components, the calldata floor token, and the per-
authorisation intrinsic. `standardCallDataTokenCost` and `initCodeCost` are
untouched by Amsterdam and stay global.

`createCost` reads `gas.createAccess`, the same field the `CREATE` opcodes
read: at Prague the creation transaction's recipient cost and the opcode's
base cost are one number, and EIP-8037 moves both together. -/
def Transaction.intrinsicGas (rules : ForkRules) (tx : Transaction) (sender : Address) : Nat × Nat :=
  -- `foldl` (tail-recursive) rather than `(map …).sum`: the latter's
  -- non-tail-recursive `List.map` overflows the stack on large calldata
  -- (e.g. the 1.2 MB inputs in the EIP-2537 stress fixtures).
  let tokensInCalldata : Nat :=
    tx.data.foldl (fun acc x => acc + (if x = 0 then 1 else 4)) 0
  let floorTokensInCalldata : Nat :=
    match rules.stateGas with
    | none => tokensInCalldata
    | some _ => tx.data.length * Gas.standardTokenCost
  -- `TX_DATA_COST_PER_NON_ZERO`: 68 before EIP-2028 (Istanbul), 16 after.
  -- Zero bytes stay 4. At Prague `dataNonZero = 16`, so this agrees with the
  -- old `tokensInCalldata * standardCallDataTokenCost` on every input.
  let dataCost : Nat :=
    tx.data.foldl
      (fun acc x => acc + (if x = 0 then Gas.standardTokenCost else rules.transactionRules.dataNonZero)) 0
  let recipientCost : Nat :=
      match tx.type.to? with
      | none => rules.gas.createAccess
      | some recipient =>
        match rules.stateGas with
        | none => 0
        | some state =>
          if recipient = sender then 0
          else rules.gas.coldAccountAccess + if tx.value = 0 then 0 else state.txValueCost
  -- EIP-3860 (Shanghai): initcode is metered per word only once
  -- `creation.initCodeLimit` activates. Dormant (zero) before.
  let initCost : Nat :=
    if rules.creation.initCodeLimit then
      if tx.type.to?.isNone then initcodeCost tx.data.length else 0
    else 0
  let accessList :=
    match tx.type with
    | .legacy _ _ => []
    | .eip2930 _ _ _ accessList => accessList
    | .eip1559 _ _ _ _ accessList => accessList
    | .eip4844 _ _ _ _ accessList _ _ => accessList
    | .eip7702 _ _ _ _ accessList _ => accessList
  let accessListCost : Nat :=
    let accessList :=
      accessList
    let accessItemCost : (Address × List U256) → Nat
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
    | .eip7702 _ _ _ _ _ auths => rules.gas.perAuthorizationIntrinsic * auths.length
    | _ => 0
  let baseExecutionGas := rules.gas.txBase + recipientCost
  let floorBaseGas :=
    match rules.stateGas with
    | none => rules.gas.txBase
    | some _ => baseExecutionGas
  -- EIP-7623's calldata floor (Prague): absent (zero) while
  -- `txr.calldataFloor` is off, so the `max` with intrinsic is the intrinsic.
  let callDataFloorGasCost :=
    if rules.transactionRules.calldataFloor then
      (floorTokensInCalldata + accessListFloorTokens) * rules.gas.floorTokenCost
        + floorBaseGas
    else 0
  ⟨
    baseExecutionGas + initCost + dataCost + accessListCost + authCost,
    callDataFloorGasCost
  ⟩

def checkInitcodeSize (code : CodeLimits) (receiver : Option Address)
    (dataLength : Nat) : Except TxValidationError Unit :=
  if receiver.isNone && dataLength > code.maxInitCodeSize then
    .error <| .initcodeSizeExceeded <| .text
      s!"initcode is {dataLength} bytes, \
         exceeding the {code.maxInitCodeSize}-byte maximum"
  else
    .ok ()

/-- EIP-3860 (Shanghai): the initcode size bound is enforced only once
`creation.initCodeLimit` activates; before that the limit field is dormant.
At Prague it is always on, so this is `checkInitcodeSize` there. -/
def checkInitcodeLimit (rules : ForkRules) (receiver : Option Address)
    (dataLength : Nat) : Except TxValidationError Unit :=
  if rules.creation.initCodeLimit then
    checkInitcodeSize rules.code receiver dataLength
  else
    .ok ()

/-- Prague enforces the initcode bound: its creation limit is on. -/
@[simp] theorem pragueRules_creation_initCodeLimit :
    pragueRules.creation.initCodeLimit = true := rfl

private def checkTransactionGasLimit (limit : Option Nat) (gas : Nat) :
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

/-- Enforce the pre-Amsterdam whole-transaction EIP-7825 cap. -/
def checkTransactionGasCap (limits : TransactionLimits) (gas : Nat) :
    Except TxValidationError Unit :=
  checkTransactionGasLimit limits.maxGas gas

/-- Enforce Amsterdam's separate EIP-8037 total transaction gas cap. -/
def checkTransactionTotalGasCap (limits : TransactionLimits) (gas : Nat) :
    Except TxValidationError Unit :=
  checkTransactionGasLimit limits.maxTotalGas gas

private def checkTransactionPriorityFeeRelation (tx : Transaction) :
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

private def checkTransactionBlobShape (rules : ForkRules) (tx : Transaction) :
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

def validateTransaction (rules : ForkRules) (tx : Transaction) (sender : Address) :
    Except TxValidationError (Nat × Nat) := do
  match rules.stateGas with
  | none =>
    let ⟨intrinsicGas, callDataFloorGasCost⟩ :=
      Transaction.intrinsicGas rules tx sender
    if max intrinsicGas callDataFloorGasCost > tx.gasLimit then
      .error <| .intrinsicGasTooLow <| .text
        s!"transaction gas = {tx.gasLimit} < \
           max intrinsic/calldata floor cost = \
           {max intrinsicGas callDataFloorGasCost}"
    match rules.tx.maxGas with
    | none =>
      -- Keep Prague's established error precedence byte-for-byte.
      if tx.nonce = UInt64.max then
        .error <| .nonceIsMax <| .text "transaction nonce is 2^64 - 1"
      checkInitcodeLimit rules tx.type.to? tx.data.length
    | some _ =>
      -- Osaka keeps its EIP-7825 whole-transaction cap.
      checkInitcodeLimit rules tx.type.to? tx.data.length
      checkTransactionGasCap rules.tx tx.gasLimit
      if tx.nonce = UInt64.max then
        .error <| .nonceIsMax <| .text "transaction nonce is 2^64 - 1"
    .ok ⟨intrinsicGas, callDataFloorGasCost⟩
  | some _ =>
    -- Amsterdam follows the pinned source order. The structural checks moved
    -- here so their reason precedes intrinsic affordability on multiply-
    -- invalid inputs; the whole-transaction EIP-7825 cap is not applied.
    if tx.nonce = UInt64.max then
      .error <| .nonceIsMax <| .text "transaction nonce is 2^64 - 1"
    checkInitcodeLimit rules tx.type.to? tx.data.length
    checkTransactionTotalGasCap rules.tx tx.gasLimit
    checkTransactionPriorityFeeRelation tx
    checkTransactionBlobShape rules tx
    checkTransactionReceiver tx
    checkTransactionAuthorizationList tx
    let ⟨intrinsicGas, callDataFloorGasCost⟩ :=
      Transaction.intrinsicGas rules tx sender
    if intrinsicGas > tx.gasLimit then
      .error <| .intrinsicGasTooLow <| .text
        s!"transaction gas = {tx.gasLimit} < intrinsic execution gas = \
           {intrinsicGas}"
    if callDataFloorGasCost > tx.gasLimit then
      .error <| .intrinsicGasTooLow <| .text
        s!"transaction gas = {tx.gasLimit} < intrinsic calldata floor = \
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

/-- Without a state-gas dimension the intrinsic cost does not read the sender:
its only use is the Amsterdam recipient check. -/
theorem Transaction.intrinsicGas_sender_congr_none {rules : ForkRules}
    {tx : Transaction} {s1 s2 : Address} (hsg : rules.stateGas = none) :
    Transaction.intrinsicGas rules tx s1 = Transaction.intrinsicGas rules tx s2 := by
  unfold Transaction.intrinsicGas
  rw [hsg]

/-- Without a state-gas dimension validation does not read the sender. -/
theorem validateTransaction_sender_congr_none {rules : ForkRules}
    {tx : Transaction} {s1 s2 : Address} (hsg : rules.stateGas = none) :
    validateTransaction rules tx s1 = validateTransaction rules tx s2 := by
  unfold validateTransaction
  rw [hsg]
  rw [Transaction.intrinsicGas_sender_congr_none hsg]

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
    let gasRefund := min (gasUsedBeforeRefund / rules.settlement.refundQuotient) refundCounter
    let gasUsed := max (gasUsedBeforeRefund - gasRefund) calldataFloor
    ⟨gasUsed, txGas - gasUsed, gasUsed, 0⟩
  | some _ =>
    let gasUsedBeforeRefund := txGas - gasLeft - stateGasLeft
    let gasRefund := min (gasUsedBeforeRefund / rules.settlement.refundQuotient) refundCounter
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

/-- The refund cap is monotone in the quotient: a larger divisor (London's 5
over the pre-London 2) caps the refund at no more. -/
theorem gasRefund_mono_quotient {used refundCounter q₁ q₂ : Nat}
    (h : q₁ ≤ q₂) (hpos : 0 < q₁) :
    min (used / q₂) refundCounter ≤ min (used / q₁) refundCounter := by
  have hdiv : used / q₂ ≤ used / q₁ := Nat.div_le_div_left h hpos
  omega

/-- Prague keeps the historical fifth: its settlement quotient is 5. -/
@[simp] theorem pragueRules_settle_refundQuotient :
    pragueRules.settlement.refundQuotient = 5 := rfl

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

def prepareMessage (benv: Benv) (tenv: Tenv) (tx: Transaction) :
  Except TransitionError Msg := do
  let ⟨currentTarget, msgData, code, codeAddress⟩ :
    Address × Bytes × ByteArray × Option Address :=
    match tx.type.to? with
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
    target := tx.type.to?,
    gas := tenv.stat.gas,
    value := tx.value.toU256,
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

def calculateDataFee (blob : BlobSchedule) (excess_blob_gas: Nat) (tx: Transaction) :
    Nat :=
  getTotalBlobGas tx * getBaseFeePerBlobGas blob excess_blob_gas

def getTxHash (tx : Transaction) : U256 := tx.toRlpItem.toBytes.keccak

def Receipt.toRlpItem (r : Receipt) : Rlp.Item :=
  .list [
    .bytes (if r.status then [0x01] else []),
    .bytes r.cumulativeGasUsed.toBytesPack,
    .bytes r.logsBloom,
    .list (r.logs.map Log.toRlpItem)
  ]

def makeReceipt
  (tx: Transaction)
  (error: Option SettledHalt)
  (gasUsed: Nat)
  (logs: List Log) : Fin 5 × Receipt :=
  let receipt : Receipt := {
    status := error.isNone,
    cumulativeGasUsed := gasUsed,
    logsBloom := logsBloom logs,
    logs := logs
  }
  let head : Fin 5 :=
    match tx.type with
    | .legacy _ _ => 0
    | .eip2930 _ _ _ _ => 1
    | .eip1559 _ _ _ _ _ => 2
    | .eip4844 _ _ _ _ _ _ _ => 3
    | .eip7702 _ _ _ _ _ _ => 4
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

/-- The sender the Amsterdam intrinsic-cost formula needs before
`checkTransaction` runs. The pinned `process_transaction` compares the
transaction's own chain identifier with the block's (`WrongChainIdError`)
*before* `check_transaction` recovers the sender, so a legacy transaction
signed for another chain is refused for its chain identifier, not for its
signature; the check is repeated here ahead of recovery for that reason (the
`none` lane keeps its own order inside `checkTransaction`). -/
def recoverValidationSender (benv : Benv) (tx : Transaction) :
    Except TransitionError Address :=
  match benv.stat.rules.stateGas with
  | none => .ok 0
  | some _ => do
    Except.mapError TransitionError.transaction (checkTransactionChainId benv tx)
    Except.mapError (fun e => TransitionError.senderRecovery e)
      (recoverSender benv.stat.chainId tx)

/-- Without a state-gas dimension the validation sender is not recovered. -/
theorem recoverValidationSender_of_stateGas_none {benv : Benv} (tx : Transaction)
    (h : benv.stat.rules.stateGas = none) : recoverValidationSender benv tx = .ok 0 := by
  unfold recoverValidationSender
  rw [h]

/-- Amsterdam SELFDESTRUCT settlement clears account data but preserves the
beneficiary-independent balance retained by EIP-6780. -/
def clearAccountPreservingBalance (state : State) (address : Address) : State :=
  let account := state.get address
  state.set address {account with nonce := 0, code := .empty, storage := .empty}

/-- Select the fork's SELFDESTRUCT settlement semantics once, outside the
transaction proof's monadic spine. -/
def settleSelfdestructs (rules : ForkRules) (addresses : List Address)
    (state : State) : State :=
  match rules.stateGas with
  | none => addresses.foldl destroyAccount state
  | some _ => addresses.foldl clearAccountPreservingBalance state

def processTransaction
  (benv: Benv) (bout : BlockOutput)
  (tx: Transaction) (index : Nat) : Except TransitionError (State × BlockOutput) := do
  -- NOTE: linearized into a straight `let ← .ok (…)` / `let := …` chain
  -- (no `mut`/`for`) so the block inverts cleanly with `of_bind_eq_ok` and the
  -- `bout` bookkeeping stays opaque.  Definitionally equal to the previous
  -- `mut`/`for` form except that the final account-deletion `for` is expressed
  -- as `foldl`, which agrees because `destroyAccount` commutes over the
  -- distinct addresses of the `accountsToDelete` set.
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
  let ⟨state, txOutput⟩ ← Except.mapError TransitionError.vm (processMessageCall msg)
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

/-- Under a legacy schedule, the real transaction producer preserves the
legacy block-counter relation through its settlement and receipt updates. -/
theorem processTransaction_legacyGasAccounting {benv : Benv}
    (hnone : benv.stat.rules.stateGas = none) {bout : BlockOutput}
    (hb : bout.LegacyGasAccounting) {tx : Transaction} {index : Nat} {p}
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
    (λ acc ⟨i, wd⟩ => acc.insert (Rlp.Item.toBytes <| .bytes i.toBytes) wd)
    tr
    wds.putIndex

def processWithdrawalsState (st : State) (wds : List Withdrawal) : State :=
  List.foldl
    (λ acc wd => acc.addBal wd.address (wd.amount * (10 ^ 9).toU256))
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

def Rlp.Item.toExceptStorageKey : Rlp.Item → Except DecodeError U256
  | .bytes xs => xs.toRlpHash "access list storage key"
  | .list _ =>
    .error <| DecodeError.structure "access list storage key"
      "expected a byte-string item"

def Rlp.Item.toExceptAccessItem : Rlp.Item → Except DecodeError (Address × List U256)
  | .list [.bytes ar, .list ksr] => do
    let a ← ar.toRlpAddress "access list address"
    let ks ← List.mapM Rlp.Item.toExceptStorageKey ksr
    .ok ⟨a, ks⟩
  | _ =>
    .error <| DecodeError.structure "access list item"
      "expected [address, [storage key, ...]]"

def Rlp.Item.toExceptAccessList : Rlp.Item → Except DecodeError AccessList
  | .list rs => List.mapM Rlp.Item.toExceptAccessItem rs
  | .bytes _ =>
    .error <| DecodeError.structure "access list" "expected a list item"

def Rlp.Item.toExceptBlobHash : Rlp.Item → Except DecodeError U256
  | .bytes xs => xs.toRlpHash "blob versioned hash"
  | .list _ =>
    .error <| DecodeError.structure "blob versioned hash"
      "expected a byte-string item"

def Rlp.Item.toExceptAuthorization : Rlp.Item → Except DecodeError Authorization
  | .list [
      .bytes chainId,
      .bytes address,
      .bytes nonce,
      .bytes yParity,
      .bytes r,
      .bytes s
    ] => do
      let chainId ← chainId.toRlpU256 "authorization chainId"
      let address ← address.toRlpAddress "authorization address"
      let nonce ← nonce.toRlpUInt64 "authorization nonce"
      let yParity ← yParity.toRlpNat "authorization yParity" 32
      let r ← r.toRlpU256 "authorization r"
      let s ← s.toRlpU256 "authorization s"
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
theorem Rlp.Item.toExceptAuthorization_wireWellFormed {blt : Rlp.Item} {a : Authorization}
    (h : blt.toExceptAuthorization = .ok a) : a.WireWellFormed := by
  unfold Rlp.Item.toExceptAuthorization at h
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

def Bytes.toExceptTransaction : Bytes → Except TransitionError Transaction
  | [] =>
    .error <| .decode <| DecodeError.structure "typed transaction"
      "cannot decode an empty byte string"
  | x :: xs =>
    -- Every scalar is bounded before conversion: `Bytes.toUInt64` truncates modulo
    -- 2^64, so it may only see bytes returned by a strict decoder. Signature
    -- scalars keep their minimally encoded bytes once validated, so signing
    -- and trie bytes are unchanged for valid transactions.
    match x, Bytes.toRlpItem? xs with
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
      let chainId ← dec <| chainId.toRlpUInt64 "type-1 transaction chainId"
      let nonce ← dec <| nonce.toRlpUInt64 "type-1 transaction nonce"
      let gasPrice ← dec <| gasPrice.toRlpNat "type-1 transaction gasPrice" 32
      let gas ← dec <| gas.toRlpNat "type-1 transaction gas" 32
      let receiver ← dec <| receiver.toRlpReceiver "type-1 transaction receiver"
      let value ← dec <| value.toRlpNat "type-1 transaction value" 32
      let accessList ← dec accessList.toExceptAccessList
      let yParity ← dec <| yParity.toRlpNat "type-1 transaction yParity" 32
      let _ ← dec <| r.toRlpU256 "type-1 transaction r"
      let _ ← dec <| s.toRlpU256 "type-1 transaction s"
      .ok {
        nonce := nonce,
        gasLimit := gas,
        value := value,
        data := data,
        v := yParity,
        r := r,
        s := s,
        type := .eip2930 chainId gasPrice receiver accessList
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
      let chainId ← dec <| chainId.toRlpUInt64 "type-2 transaction chainId"
      let nonce ← dec <| nonce.toRlpUInt64 "type-2 transaction nonce"
      let maxPriorityFee ← dec <| maxPriorityFee.toRlpNat "type-2 transaction maxPriorityFee" 32
      let maxFee ← dec <| maxFee.toRlpNat "type-2 transaction maxFee" 32
      let gas ← dec <| gas.toRlpNat "type-2 transaction gas" 32
      let receiver ← dec <| receiver.toRlpReceiver "type-2 transaction receiver"
      let value ← dec <| value.toRlpNat "type-2 transaction value" 32
      let accessList ← dec accessList.toExceptAccessList
      let yParity ← dec <| yParity.toRlpNat "type-2 transaction yParity" 32
      let _ ← dec <| r.toRlpU256 "type-2 transaction r"
      let _ ← dec <| s.toRlpU256 "type-2 transaction s"
      .ok {
        nonce := nonce,
        gasLimit := gas,
        value := value,
        data := data,
        v := yParity,
        r := r,
        s := s,
        type := .eip1559 chainId maxPriorityFee maxFee receiver accessList
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
      let chainId ← dec <| chainId.toRlpUInt64 "type-3 transaction chainId"
      let nonce ← dec <| nonce.toRlpUInt64 "type-3 transaction nonce"
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
      let receiver ← dec <| receiver.toRlpAddress "type-3 transaction receiver"
      let value ← dec <| value.toRlpNat "type-3 transaction value" 32
      let accessList ← dec accessList.toExceptAccessList
      let maxBlobFee ← dec <| maxBlobFee.toRlpNat "type-3 transaction maxBlobFee" 32
      let blobHashes ← dec <| List.mapM Rlp.Item.toExceptBlobHash blobHashes
      let yParity ← dec <| yParity.toRlpNat "type-3 transaction yParity" 32
      let _ ← dec <| r.toRlpU256 "type-3 transaction r"
      let _ ← dec <| s.toRlpU256 "type-3 transaction s"
      .ok {
        nonce := nonce,
        gasLimit := gas,
        value := value,
        data := data,
        v := yParity,
        r := r,
        s := s,
        type :=
          .eip4844 chainId maxPriorityFee maxFee receiver accessList
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
      let chainId ← dec <| chainId.toRlpUInt64 "type-4 transaction chainId"
      let nonce ← dec <| nonce.toRlpUInt64 "type-4 transaction nonce"
      let maxPriorityFee ← dec <| maxPriorityFee.toRlpNat "type-4 transaction maxPriorityFee" 32
      let maxFee ← dec <| maxFee.toRlpNat "type-4 transaction maxFee" 32
      let gas ← dec <| gas.toRlpNat "type-4 transaction gas" 32
      if receiver.isEmpty then
        .error <| .transaction <| .type4ContractCreation <|
          .text "type-4 transaction receiver is empty"
      let receiver ← dec <| receiver.toRlpAddress "type-4 transaction receiver"
      let value ← dec <| value.toRlpNat "type-4 transaction value" 32
      let accessList ← dec accessList.toExceptAccessList
      let auths ← dec <| List.mapM Rlp.Item.toExceptAuthorization auths
      let yParity ← dec <| yParity.toRlpNat "type-4 transaction yParity" 32
      let _ ← dec <| r.toRlpU256 "type-4 transaction r"
      let _ ← dec <| s.toRlpU256 "type-4 transaction s"
      .ok {
        nonce := nonce,
        gasLimit := gas,
        value := value,
        data := data,
        v := yParity,
        r := r,
        s := s,
        type := .eip7702 chainId maxPriorityFee maxFee receiver accessList auths
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
theorem Bytes.toExceptTransaction_wireWellFormed {xs : Bytes} {tx : Transaction}
    (h : xs.toExceptTransaction = .ok tx) : tx.WireWellFormed := by
  unfold Bytes.toExceptTransaction at h
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
          | exact Bytes.toRlpU256_eq_ok (dec_eq_ok (by assumption))
    · exact absurd h (by simp)
    -- type 2 (EIP-1559)
    · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first
          | exact Bytes.toRlpNat_lt_two_pow_256 (dec_eq_ok (by assumption))
          | exact Bytes.toRlpU256_eq_ok (dec_eq_ok (by assumption))
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
            | exact Bytes.toRlpU256_eq_ok (dec_eq_ok (by assumption))
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
          exact Rlp.Item.toExceptAuthorization_wireWellFormed hblt
        all_goals
          first
            | exact Bytes.toRlpNat_lt_two_pow_256 (dec_eq_ok (by assumption))
            | exact Bytes.toRlpU256_eq_ok (dec_eq_ok (by assumption))
    · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- S5 admission: a decoded transaction is admissible only when its type
number fits the rules (`tx.type.index ≤ rules.txr.maxType`). A typed envelope
from a later fork fails here with its own transaction reason, `typePreFork`
-- EELS's own decode of those bytes fails under the earlier fork, so the block
is invalid rather than internally unclassifiable, and the fixture vocabulary
names the reason per type (`TYPE_3_TX_PRE_FORK`, `TYPE_4_TX_PRE_FORK`; goal
U11a moved it off the decode channel to carry that identity). Pre-London
needs nothing more: fees are unchanged because the base fee is 0 there. -/
def checkTransactionTypeAdmitted (rules : ForkRules) (tx : Transaction) :
    Except TransitionError Unit :=
  if tx.type.index ≤ rules.transactionRules.maxType then .ok ()
  else
    .error <| .transaction <| .typePreFork tx.type.index <| .text
      s!"type-{tx.type.index} transaction needs maxType ≥ {tx.type.index}, \
         these rules admit at most {rules.transactionRules.maxType}"

/-- Decode a block-body transaction slot: opaque typed-envelope bytes through
the strict envelope decoder plus the S5 admission check, an already-decoded
legacy slot as itself. The `.inr` arm is not a bypass on the checked path:
`CanonicalBlock.decodeTx_inr` certifies what it returns there, and every
certified slot is legacy, which every `maxType` admits. -/
def decodeTransaction (rules : ForkRules) : Bytes ⊕ Transaction → Except TransitionError Transaction
  | .inl xs => do
    let tx ← xs.toExceptTransaction
    checkTransactionTypeAdmitted rules tx
    .ok tx
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
    (target : Address) (data : Bytes) (code : ByteArray) : Msg :=
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

-- The single boundary shared by all four system transactions (beacon roots,
-- history storage, withdrawal requests, consolidation requests), so each takes
-- its own input state as the original state.
def processSystemTransaction (benv : Benv)
  (target : Address) (code : ByteArray) (data : Bytes) :
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
  (benv : Benv) (target : Address) (data : Bytes) :
  Except EvmError (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  processSystemTransaction benv target systemContractCode data

def processCheckedSystemTransaction
  (benv : Benv) (target : Address) (data : Bytes) :
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
  -- P0.6 item 3: the halt is extracted by the total match, never by a partial
  -- projection out of the optional error field. The rejection carries the
  -- halt itself; `BlockValidationError.detail` writes its text (3.2).
  match systemTxOutput.error with
  | some halt => .error <| .block <| .systemContractCallFailed target halt
  | none => .ok ⟨state, systemTxOutput⟩

/-- Call each request-producing system contract in turn, threading the state.

Structural recursion on the contract list rather than a loop, so that the
invariant proofs are an induction on that list instead of a fixed number of
nested case splits -- which is what makes adding Amsterdam's two contracts a
change to data and to nothing else. Each contract's non-empty return data is
appended prefixed with its own type byte, and the state each call produces is
what the next call runs against. -/
def runRequestContracts (idx : Nat) :
    List (UInt8 × Address) → Benv → List Bytes → BlockAccessListBuilder →
      Except TransitionError (State × List Bytes × BlockAccessListBuilder)
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
    let bal := match benv.stat.rules.blockAccessListRules with
      | none => bal
      | some _ => bal.incorporate idx benv.state state
          (address :: output.accountReads.toList) output.storageReads.toList output.storageWrites.toList
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
`Jaune/Machine.lean` states that by `rfl`; a `Jaune/Check/Fork.lean` `#guard` runs it. -/
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
    runRequestContracts balIndex benv.stat.rules.requests benv seeded bout.blockAccessListBuilder
  .ok ⟨state, {bout with requests := allRequests, blockAccessListBuilder := bal}⟩

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
    List (Nat × Transaction) → Benv → BlockOutput → Except TransitionError (Benv × BlockOutput)
  | [], benv, bout => .ok (benv, bout)
  | ⟨i, tx⟩ :: txis, benv , bout => do
    let ⟨st, bout'⟩ ← processTransaction benv bout tx i
    applyTransactions txis (benv.withState st) bout'

/-- The actual transaction-list fold preserves the legacy block counters at
every successful iteration. -/
theorem applyTransactions_legacyGasAccounting :
    ∀ (txis : List (Nat × Transaction)) {benv : Benv},
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
    (txis : List (Nat × Transaction)) {benv : Benv}
    (hnone : benv.stat.rules.stateGas = none) {p}
    (hp : applyTransactions txis benv .init = .ok p) :
    p.2.LegacyGasAccounting :=
  applyTransactions_legacyGasAccounting txis hnone
    BlockOutput.init_legacyGasAccounting hp

/-- EIP-7928: incorporate one pre-execution or post-execution system operation
-- a system call's writes and reads plus the contract account `create_evm`
read, or the withdrawals batch's credits plus each recipient `create_ether`
read -- at `idx`, under rules that carry a block-level access list. -/
def BlockAccessListBuilder.incorporateSystem (bal : BlockAccessListBuilder) (rules : ForkRules) (idx : Nat)
    (pre post : State) (accountReads : List Address)
    (storageReads storageWrites : List (Address × U256)) :
    BlockAccessListBuilder :=
  match rules.blockAccessListRules with
  | none => bal
  | some _ => bal.incorporate idx pre post accountReads storageReads storageWrites

/-- `validate_block_access_list_gas_limit`, inside `apply_body` before any
header comparison: `items > gasLimit // itemCost` is a block rejection. -/
def checkBlockAccessListGasLimit (rules : ForkRules) (blockGasLimit : Nat)
    (list : BlockAccessList) : Except TransitionError Unit :=
  match rules.blockAccessListRules with
  | none => .ok ()
  | some r =>
    if list.itemCount > blockGasLimit / r.itemCost then
      .error <| .block <| .blockAccessListGasLimit <| .text
        s!"block access list holds {list.itemCount} items, exceeding \
           gasLimit / itemCost = {blockGasLimit / r.itemCost}"
    else .ok ()

/-- EIP-4788's pre-execution beacon-roots call (Cancun on), with its
block-level access-list incorporation at index 0; under rules without
`sys.beaconRoots` the identity: the state as given and an empty builder. -/
def beaconRootsCall (rules : ForkRules) (benv : Benv) :
    Except TransitionError (State × BlockAccessListBuilder) :=
  if rules.systemCalls.beaconRoots then do
    let ⟨st, out⟩ ←
      Except.mapError TransitionError.vm <|
        processUncheckedSystemTransaction benv
          beaconRootsAddress
          benv.stat.parentBeaconBlockRoot.toBytes
    .ok ⟨st, BlockAccessListBuilder.incorporateSystem {} rules 0 benv.state st
      (beaconRootsAddress :: out.accountReads.toList) out.storageReads.toList
      out.storageWrites.toList⟩
  else .ok ⟨benv.state, {}⟩

/-- EIP-2935's pre-execution history-storage call (Prague on), incorporated at
index 0; under rules without `sys.historyStorage` the identity. -/
def historyStorageCall (rules : ForkRules) (benv : Benv) (bal : BlockAccessListBuilder) :
    Except TransitionError (State × BlockAccessListBuilder) :=
  if rules.systemCalls.historyStorage then do
    let lastHash ←
       benv.stat.blockHashes.getLast?.toExcept
         (TransitionError.internal (.invariant (.text "block hashes is empty")))
    let ⟨st, out⟩ ←
      Except.mapError TransitionError.vm <|
        processUncheckedSystemTransaction benv
          historyStorageAddress
          lastHash.toBytes
    .ok ⟨st, bal.incorporateSystem rules 0 benv.state st
      (historyStorageAddress :: out.accountReads.toList) out.storageReads.toList
      out.storageWrites.toList⟩
  else .ok ⟨benv.state, bal⟩

/-- EIP-4895's withdrawals (Shanghai on), gated by `header.withdrawalsRoot`:
the credits, the withdrawals trie, and -- EIP-7928 -- one incorporation at
`n + 1`, every recipient read by `create_ether` whatever the amount. Under
rules without the field the identity. -/
def withdrawalsPass (rules : ForkRules) (benv : Benv) (bout : BlockOutput)
    (wds : List Withdrawal) : State × BlockOutput :=
  if rules.header.withdrawalsRoot then
    let ⟨stWds, boutWds⟩ := processWithdrawals benv bout wds
    let balWds := boutWds.blockAccessListBuilder.incorporateSystem rules
      (bout.receiptKeys.length + 1) benv.state stWds (wds.map Withdrawal.address) [] []
    ⟨stWds, {boutWds with blockAccessListBuilder := balWds}⟩
  else ⟨benv.state, bout⟩

/-- EIP-7685's request pass (Prague on), deposit-log parsing included, gated by
`header.requestsHash`; under rules without the field the identity. -/
def requestsPass (rules : ForkRules) (benv : Benv) (bout : BlockOutput) :
    Except TransitionError (State × BlockOutput) :=
  if rules.header.requestsHash then processGeneralPurposeRequests benv bout
  else .ok ⟨benv.state, bout⟩

/-- `pay_rewards`, Byzantium through Gray Glacier: the block reward plus
`reward / 32` per ommer to the block's coinbase, then to each ommer's coinbase
`(8 - age) * reward / 8`, where `age = number - ommer.number`. Written
`(8 + ommer.number - number)`, which is the same number for every age
`validateOmmers` admits (1 to 6). Each credit is `create_ether`, which is
`State.addBal`. The reward is minted: no account is debited. -/
def payRewards (pow : ProofOfWorkRules) (number : Nat) (coinbase : Address)
    (ommers : List Header) (st : State) : State :=
  let minerReward := pow.blockReward + ommers.length * (pow.blockReward / 32)
  ommers.foldl
    (fun acc ommer =>
      acc.addBal ommer.coinbase ((8 + ommer.number - number) * pow.blockReward / 8).toU256)
    (st.addBal coinbase minerReward.toU256)

/-- `apply_body`, every fork from Byzantium on, with each fork-dependent step
gated by rule data and the identity where its rule is off: the beacon-roots
call (`sys.beaconRoots`), the history-storage call (`sys.historyStorage`), the
withdrawals (`header.withdrawalsRoot`), the request pass with its deposit-log
parsing (`header.requestsHash`), and the proof-of-work rewards
(`pow = some _`), paid last. `ommers` is the block's ommer list, the EELS
pre-merge signature; after Paris `checkBlockOmmers` has already required it
empty and nothing reads it.

The rewards are not incorporated into a block-level access list: no fork
carries both `pow = some _` and `bal = some _`. -/
def applyBody
  (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
  (wds : List Withdrawal) :
  Except TransitionError (State × BlockOutput) := do
  let rules := benv.stat.rules
  -- EIP-7928: the two pre-execution system calls incorporate at index 0.
  let ⟨stBeacon, bal⟩ ← beaconRootsCall rules benv
  let benvBeacon : Benv := benv.withState stBeacon
  let ⟨stHistory, bal⟩ ← historyStorageCall rules benvBeacon bal
  let benvHistory := benvBeacon.withState stHistory
  let ⟨benvTxs, boutTxs⟩ ←
    applyTransactions (← txs.mapM (decodeTransaction benvHistory.stat.rules)).putIndex benvHistory {BlockOutput.init with blockAccessListBuilder := bal}
  let ⟨stWds, boutWds⟩ := withdrawalsPass rules benvTxs boutTxs wds
  let ⟨stReq, boutReq⟩ ← requestsPass rules (benvTxs.withState stWds) boutWds
  let stRewards := match rules.proofOfWork with
    | none => stReq
    | some pow => payRewards pow benv.stat.number benv.stat.coinbase ommers stReq
  -- `build_block_access_list`, then the item rule -- before any header check.
  let list := match rules.blockAccessListRules with
    | none => []
    | some _ => boutReq.blockAccessListBuilder.build
  checkBlockAccessListGasLimit rules benv.stat.blockGasLimit list
  .ok ⟨stRewards, {boutReq with blockAccessList := list}⟩

theorem withdrawalsPass_legacyGasAccounting {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} (hb : bout.LegacyGasAccounting) (wds : List Withdrawal) :
    (withdrawalsPass rules benv bout wds).2.LegacyGasAccounting := by
  unfold withdrawalsPass
  split
  · exact processWithdrawals_legacyGasAccounting (benv := benv) hb wds
  · exact hb

theorem requestsPass_legacyGasAccounting {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} (hb : bout.LegacyGasAccounting) {p}
    (hp : requestsPass rules benv bout = .ok p) : p.2.LegacyGasAccounting := by
  unfold requestsPass at hp
  split at hp
  · exact processGeneralPurposeRequests_legacyGasAccounting hb hp
  · cases hp; exact hb

/-- A successful legacy block body starts from `BlockOutput.init`, preserves
the relation through every transaction, and keeps it through withdrawals,
the request pass and the rewards, each of which is the identity on the gas
counters whether its rule is on or off. -/
theorem applyBody_legacyGasAccounting {benv : Benv}
    (hnone : benv.stat.rules.stateGas = none)
    {txs : List (Bytes ⊕ Transaction)} {ommers : List Header} {wds : List Withdrawal} {p}
    (hp : applyBody benv txs ommers wds = .ok p) : p.2.LegacyGasAccounting := by
  unfold applyBody at hp
  obtain ⟨q1, _, hp⟩ := Except.bind_eq_ok hp
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
  have hwLegacy := withdrawalsPass_legacyGasAccounting
    (rules := benv.stat.rules) (benv := benvTxs) hqLegacy wds
  rcases hw : withdrawalsPass benv.stat.rules benvTxs boutTxs wds with ⟨stWds, boutWds⟩
  simp only [hw] at hp hwLegacy
  -- The request pass, the rewards, the item rule and the built list touch no
  -- gas counter.
  obtain ⟨q', hq', hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact requestsPass_legacyGasAccounting (p := q') hwLegacy hq'

def BlockChain.recentBlockHashes (chain : BlockChain) : List U256 :=
  match chain.blocks.reverse.take 255 with
  | [] => []
  | block :: blocks =>
    let hash : U256 := (Header.toRlpItem block.header).toBytes.keccak
    let hashes : List U256 :=
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
    BlockChain.recentBlockHashes chain
      = chain.retained.map (fun x => x.header.parentHash) ++ [b.header.hash] := by
  unfold BlockChain.recentBlockHashes BlockChain.retained
  rw [hN]
  simp [Header.hash, List.map_reverse]

/-- Below the tip, every entry is a retained block's `parentHash` field. -/
theorem getLast256BlockHashes_getD_lt {chain : BlockChain} {b : Block}
    {bs : List Block} (hN : chain.blocks.reverse.take 255 = b :: bs) {j : Nat}
    (hj : j < chain.retained.length) :
    (BlockChain.recentBlockHashes chain).getD j 0
      = chain.retained[j].header.parentHash := by
  rw [getLast256BlockHashes_eq hN, List.getD,
    List.getElem?_append_left (by simpa using hj),
    List.getElem?_eq_getElem (by simpa using hj)]
  simp

/-- The last entry is the tip's own recomputed header hash. -/
theorem getLast256BlockHashes_getD_last {chain : BlockChain} {b : Block}
    {bs : List Block} (hN : chain.blocks.reverse.take 255 = b :: bs) :
    (BlockChain.recentBlockHashes chain).getD chain.retained.length 0 = b.header.hash := by
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
        (BlockChain.recentBlockHashes chain).getD
          ((BlockChain.recentBlockHashes chain).length - (number - blockNumber)) 0
            = b.header.hash) ∨
      (∃ oldest ∈ chain.retained.head?, blockNumber + 1 = oldest.header.number ∧
        (BlockChain.recentBlockHashes chain).getD
          ((BlockChain.recentBlockHashes chain).length - (number - blockNumber)) 0
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
  have hlen1 : (BlockChain.recentBlockHashes chain).length = chain.retained.length + 1 := by
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
    have hidx : (BlockChain.recentBlockHashes chain).length - (number - blockNumber) = 0 := by
      omega
    rw [hidx, getLast256BlockHashes_getD_lt hN h0]
  · -- A height the window still retains a block for.
    left
    obtain ⟨k, hk⟩ : ∃ k, blockNumber = chain.retained[0].header.number + k :=
      ⟨blockNumber - chain.retained[0].header.number, by omega⟩
    have hidx : (BlockChain.recentBlockHashes chain).length - (number - blockNumber)
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
    (BlockChain.recentBlockHashes chain).getD
      ((BlockChain.recentBlockHashes chain).length - (number - b.header.number)) 0
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

def computeRequestsHash (requests : List Bytes) : U256 :=
  -- EIP-7685 commits the SHA-256 digest of each type-prefixed request, then
  -- hashes their concatenation once more.  This is deliberately not the EVM
  -- Keccak primitive used by transaction and trie commitments.
  let hashes := requests.map (fun r => r.sha256.toBytes)
  Bytes.sha256 <| List.flatten hashes

def State.root (w : State) : U256 :=
  let keyVals := (List.map accountToKeyValue w.toList)
  let finalNTB : TrieBuilder := Std.TreeMap.ofList keyVals _
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

/-- One header field's presence against the rule that defines it, in both
directions; see `validateHeader`. -/
def checkHeaderFieldPresence (name : String) (present defined : Bool) :
    Except TransitionError Unit :=
  if present ≠ defined then
    .error <| .block <| .headerFieldPresence <| .text
      s!"{name} is {if present then "present" else "absent"}, \
         but these rules {if defined then "require" else "do not define"} it"
  else .ok ()

/-- The pre-Prague fork-dependent header fields against `rules.header`, in
both directions: London's base fee, Shanghai's withdrawals root, and Cancun's
blob-gas pair and parent beacon block root. In EELS a header of the wrong
shape fails to decode as the fork's `Header` class at all, before any rule
reads a field, so these run first. The newer fields keep their place at the
end of `validateHeader`. -/
def checkHeaderShape (rules : ForkRules) (header : Header) :
    Except TransitionError Unit := do
  checkHeaderFieldPresence "baseFeePerGas"
    header.baseFeePerGas.isSome rules.header.baseFee
  checkHeaderFieldPresence "withdrawalsRoot"
    header.withdrawalsRoot.isSome rules.header.withdrawalsRoot
  checkHeaderFieldPresence "blobGasUsed"
    header.blobGasUsed.isSome rules.header.blobGas
  checkHeaderFieldPresence "excessBlobGas"
    header.excessBlobGas.isSome rules.header.blobGas
  checkHeaderFieldPresence "parentBeaconBlockRoot"
    header.parentBeaconBlockRoot.isSome rules.header.parentBeaconBlockRoot

/-- The base fee a child header must carry, or `none` for a child whose rules
define no base fee.

Three cases, keyed on header shape. A child without the field runs only the
gas-limit check (EELS Berlin `validate_header`). A child with the field whose
parent lacks it receives `INITIAL_BASE_FEE`; this helper does not check gas
limits in that arm. `validateHeader` separately checks the child's gas limit
against twice the actual parent's limit before calling this helper.
`expectedBaseFee_first` records the initial-fee arm;
`parent_baseFee_none_iff` ties the parent's missing field to its rules when
its header shape is checked. `ChainConfig.ShapeCoherent` supplies that shape
condition at configured chain heads. Otherwise the EIP-1559 update rule,
which includes the gas-limit check. -/
def expectedBaseFee (header parent : Header) :
    Except BlockValidationError (Option Nat) :=
  match header.baseFeePerGas, parent.baseFeePerGas with
  | none, _ => do
    checkGasLimit header.gasLimit parent.gasLimit
    .ok none
  | some _, none => .ok (some initialBaseFee)
  | some _, some parentBaseFee =>
    some <$> calculateBaseFeePerGas
      header.gasLimit parent.gasLimit parent.gasUsed parentBaseFee

/-- The separate activation gas check uses the actual parent's elastic limit;
fee calculation itself retains its unconditional initial-fee arm. -/
def checkFirstFeeGasLimit (header parent : Header) : Except BlockValidationError Unit :=
  if header.baseFeePerGas.isSome && parent.baseFeePerGas.isNone then
    checkGasLimit header.gasLimit (elasticityMultiplier * parent.gasLimit)
  else .ok ()

/-- `MINIMUM_DIFFICULTY`, Byzantium through Gray Glacier. -/
def minimumDifficulty : Nat := 131072

/-- `MAX_OMMER_DEPTH`, Byzantium through Gray Glacier. -/
def maxOmmerDepth : Nat := 6

/-- `calculate_block_difficulty`, Byzantium through Gray Glacier.

The function body is byte-identical in every EELS fork module from Byzantium
to Gray Glacier; only the module constant `BOMB_DELAY_BLOCKS` differs, which
is why it is a parameter here and `PowRules.bombDelay` in the rule data. Both
divisions are Python floor divisions; `Int.fdiv` is that division (the
numerators can be negative only in the bomb term, and the divisor is
positive). The time delta is a natural number because `validateHeader` has
already rejected a timestamp no later than the parent's. -/
def calculateBlockDifficulty (bombDelay : Nat)
    (number timestamp parentTimestamp parentDifficulty : Nat)
    (parentHasOmmers : Bool) : Nat :=
  let adjust : Int :=
    max ((if parentHasOmmers then 2 else 1) - ((timestamp - parentTimestamp) / 9 : Nat))
      (-99)
  let offset : Int := ((parentDifficulty / 2048 : Nat) : Int) * adjust
  let difficulty : Int := (parentDifficulty : Int) + offset
  let bombPeriods : Int := Int.fdiv ((number : Int) - bombDelay) 100000 - 2
  let difficulty : Int :=
    if 0 ≤ bombPeriods then difficulty + 2 ^ bombPeriods.toNat else difficulty
  (max difficulty (minimumDifficulty : Int)).toNat

/-- The difficulty a child header must carry under proof-of-work rules: the
parent's difficulty and timestamp, and whether the parent carried ommers. -/
def expectedDifficulty (pow : ProofOfWorkRules) (header parent : Header) : Nat :=
  calculateBlockDifficulty pow.bombDelay header.number header.timestamp
    parent.timestamp parent.difficulty (parent.ommersHash != emptyOmmerHash)

/-- The consensus-specific header rules, after every rule the two regimes
share.

Under proof of stake (`rules.pow = none`, Paris on) the three EIP-3675
constants: difficulty 0, nonce 0 and the empty-list ommers hash. Under proof
of work (`rules.pow = some _`) the difficulty must be
`calculateBlockDifficulty`'s; the ommers hash is compared with the ommer list
by `validateOmmers`, which sees the body.

**The proof-of-work seal is not checked.** EELS `validate_header` ends with
`validate_proof_of_work`: ethash `hashimoto_light` over the header's
`mixHash` (here `prevRandao`) and `nonce`, against a target derived from the
difficulty. Jaune omits it, as a named boundary (the fixtures' `NoProof` seal
engine): any `mixHash`/`nonce` pair is accepted, for blocks and for ommers.
Nothing in execution reads either field before Paris, so the omission widens
only the set of accepted headers -- every history Jaune accepts with a valid
seal is accepted, and some with an invalid seal are accepted too. Recorded in
`TRUSTED.md`. -/
def checkConsensusFields (rules : ForkRules) (header parent : Header) :
    Except TransitionError Unit := do
  match rules.proofOfWork with
  | none =>
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
  | some pow =>
    if header.difficulty ≠ expectedDifficulty pow header parent then do
      .error <| .block <| .invalidDifficulty <| .text
        s!"difficulty = {header.difficulty} ≠ \
           expected = {expectedDifficulty pow header parent}"

def validateHeader (rules : ForkRules) (chain : BlockChain) (header : Header) :
  Except TransitionError Unit := do
  checkHeaderShape rules header
  -- An empty snapshot names no parent to validate against. The runner can
  -- never supply one (a checked snapshot is nonempty by construction), so
  -- this is a caller-context invariant breach, typed internal and fail-closed
  -- -- never a candidate verdict. Step 10 replaced the untagged legacy string
  -- "No parent block found" here; the arm is unobserved in every corpus.
  let parent ← chain.blocks.getLast?.toExcept
    (.internal (.invariant (.text "no parent block found")))
  let blockParentHash := (Header.toRlpItem parent.header).toBytes.keccak
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
  -- The first fee-bearing header uses the elastic parent gas limit. Keep
  -- this validation separate from the initial-fee calculation itself.
  Except.mapError TransitionError.block (checkFirstFeeGasLimit header parent.header)
  let expectedBaseFeePerGas ←
    Except.mapError TransitionError.block <|
      expectedBaseFee header parent.header
  -- Read only where the header carries the field; `checkHeaderShape` has
  -- already tied its presence to the rules.
  if header.excessBlobGas.any (· != calcExcessBlobGas rules.blob parent.header)
  then do
    .error <| .block <| .excessBlobGas <| .text
      s!"excess blob gas = {header.excessBlobGas.getD 0} ≠ \
         expected = {calcExcessBlobGas rules.blob parent.header}"
  if header.gasUsed > header.gasLimit then do
    .error <| .block <| .gasUsedOverflow <| .text
      s!"gas used = {header.gasUsed} > \
         gas limit = {header.gasLimit}"
  if expectedBaseFeePerGas ≠ header.baseFeePerGas then do
    .error <| .block <| .baseFeePerGas <| .text
      s!"base fee per gas = {header.baseFeePerGas.getD 0} ≠ \
         expected = {expectedBaseFeePerGas.getD 0}"
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
  -- Proof of stake's three constants, or proof of work's difficulty (the
  -- seal is a named boundary; see `checkConsensusFields`).
  checkConsensusFields rules header parent.header
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
    (transactionsRoot blockStateRoot receiptRoot : U256)
    (blockLogsBloom : Bytes) (withdrawalsRoot : U256) (requestsHash : Option U256) :
    Except BlockValidationError Unit := do
  let totalBlockGasUsed := max bout.blockGasUsed bout.blockStateGasUsed
  if totalBlockGasUsed ≠ header.gasUsed then
    .error <| .gasUsedMismatch <| .text
      s!"computed block gas used = {totalBlockGasUsed} ≠ \
         header block gas used = {header.gasUsed}"
  if transactionsRoot ≠ header.transactionsRoot then
    .error <| .transactionsRoot <| .text
      s!"computed transactions root = {transactionsRoot} \
         ≠ header transactions root = {header.transactionsRoot}"
  if blockStateRoot ≠ header.stateRoot then
    .error <| .stateRoot <| .text
      s!"computed state root = {blockStateRoot} ≠ \
         header state root = {header.stateRoot}"
  if receiptRoot ≠ header.receiptsRoot then
    .error <| .receiptsRoot <| .text
      s!"computed receipts root = {receiptRoot} ≠ \
         header receipts root = {header.receiptsRoot}"
  if blockLogsBloom ≠ header.logsBloom then
    .error <| .logBloom <| .text
      s!"computed logs bloom ≠ header logs bloom"
  -- Compared only where the header carries the field; `validateHeader` has
  -- already tied its presence to the rules.
  if header.withdrawalsRoot.any (· != withdrawalsRoot) then
    .error <| .withdrawalsRoot <| .text
      s!"computed withdrawals root = {withdrawalsRoot} ≠ \
         header withdrawals root = {header.withdrawalsRoot.getD 0}"
  if header.blobGasUsed.any (· != bout.blobGasUsed) then
    .error <| .blobGasUsed <| .text
      s!"computed blob gas used = {bout.blobGasUsed} ≠ \
         header blob gas used = {header.blobGasUsed.getD 0}"
  -- `requestsHash` is `none` exactly under rules without the field (before
  -- Prague), where the header must not carry one either.
  if requestsHash ≠ header.requestsHash then
    .error <| .requestsHash <| .text
      s!"computed requests hash = {requestsHash.getD 0} ≠ \
         header requests hash = {header.requestsHash}"

/-- EIP-7928: the header's `blockAccessListHash` against the computed list, the
last of the pinned `execute_block` comparisons -- after `requestsHash` -- and
only under rules that carry a block-level access list. -/
def blockAccessListCheck (rules : ForkRules) (bout : BlockOutput) (header : Header) :
    Except BlockValidationError Unit :=
  match rules.blockAccessListRules with
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
    blockHashes := BlockChain.recentBlockHashes chain,
    coinbase := header.coinbase,
    number := header.number,
    -- Absent before London and Cancun respectively, where nothing that reads
    -- them is reachable: `BASEFEE`, `BLOBBASEFEE` and blob transactions are
    -- gated off, and base fee 0 is EELS Berlin's fee rule exactly.
    baseFeePerGas := header.baseFeePerGas.getD 0,
    time := header.timestamp.toU256,
    -- S8 0x44 (unit U5): before the merge there is no RANDAO, so `DIFFICULTY`
    -- reads the header's difficulty instead of `prevRandao`. The opcode keeps
    -- reading this field unchanged; the selection lives here, at environment
    -- construction. Post-merge (`pow = none`) it is the header's `prevRandao`
    -- as before, so every reachable (refused-history) machine is unaffected.
    prevRandao :=
      match fork.ruleSet.proofOfWork with
      | some _ => Nat.toU256 header.difficulty
      | none => header.prevRandao,
    excessBlobGas := header.excessBlobGas.getD 0,
    parentBeaconBlockRoot := header.parentBeaconBlockRoot.getD 0,
    -- EIP-7843: absent before Amsterdam, where nothing reads it.
    slotNumber := header.slotNumber.getD 0
  }

def initBenv (fork : Fork) (chain : BlockChain) (header : Header) : Benv :=
  {
    state := chain.state,
    createdAccounts := .emptyWithCapacity,
    stat := initBenvStat fork chain header
  }

def getTransactionsRoot (bout : BlockOutput) : U256 :=
  let aux (arg : Bytes × Transaction) : (Bytes × Bytes) :=
    let txPrefix : Bytes :=
      match arg.snd.type with
      | .legacy _ _ => []
      | .eip2930 _ _ _ _ => [0x01]
      | .eip1559 _ _ _ _ _ => [0x02]
      | .eip4844 _ _ _ _ _ _ _ => [0x03]
      | .eip7702 _ _ _ _ _ _ => [0x04]
    ⟨arg.fst.toNibbles, txPrefix ++ arg.snd.toRlpItem.toBytes⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.transactionsTrie.toList) _

def getReceiptRoot (bout : BlockOutput) : U256 :=
  let aux : (Bytes × Fin 5 × Receipt) → (Bytes × Bytes)
    | ⟨key, type, receipt⟩ => ⟨key.toNibbles, type.val.toBytes ++ receipt.toRlpItem.toBytes⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.receiptsTrie.toList) _

def getWithdrawalsRoot (bout : BlockOutput) : U256 :=
  let aux (arg : Bytes × Withdrawal) : Bytes × Bytes :=
    ⟨arg.fst.toNibbles, arg.snd.toRlpItem.toBytes⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.withdrawalsTrie.toList) _

def stateTransitionOmmersCheck (ommers : List Header) :
    Except BlockValidationError Unit := do
  if ¬ommers.isEmpty then do
    .error <| .ommersOverParis <| .text
      s!"block body contains {ommers.length} ommer(s), \
         which is impossible after Paris"

/-- The hash a header's `ommersHash` commits to: the keccak of the RLP list
of the ommer headers. `emptyOmmerHash` is its value on the empty list. -/
def ommersListHash (ommers : List Header) : U256 :=
  (Rlp.Item.list (ommers.map Header.toRlpItem)).toBytes.keccak

private def ommersFail (msg : String) : Except TransitionError Unit :=
  .error <| .block <| .invalidOmmers <| .text msg

/-- Number and retained canonical parent checks precede ommer rule lookup.
The full header check below authenticates the parent's exact hash. -/
def ommerParent (chain : BlockChain) (header ommer : Header) :
    Except TransitionError Block := do
  if ommer.number < 1 ∨ ommer.number ≥ header.number then
    .error <| .block <| .invalidOmmers <| .text
      s!"ommer number = {ommer.number} is not between 1 and \
      block number = {header.number}"
  (chain.blocks.find? (·.header.number + 1 = ommer.number)).toExcept
    (TransitionError.block <| .invalidOmmers <| .text
      s!"ommer number = {ommer.number} has no retained parent")

/-- Validate an ommer against its retained parent, preserving the existing
ommer diagnostic and internal-error channels. A block-rejection reason of the
ommer's own header is returned as the cause of `invalidOmmerHeader`, not
rendered here (3.2). -/
def validateOmmerWithParent (rules : ForkRules) (chain : BlockChain)
    (ommer : Header) (parent : Block) : Except TransitionError Unit :=
  match validateHeader rules { chain with blocks := [parent] } ommer with
  | .ok () => .ok ()
  | .error (.block e) => .error <| .block <| .invalidOmmerHeader e
  | .error e => .error e

/-- Static ommer validation: the caller's explicit rules govern every header. -/
def validateOmmerHeader (rules : ForkRules) (chain : BlockChain)
    (header ommer : Header) : Except TransitionError Unit := do
  let parent ← ommerParent chain header ommer
  validateOmmerWithParent rules chain ommer parent

private def validateOmmerHeadersE {ε : Type}
    (check : Header → Except ε Unit) : List Header → Except ε Unit
  | [] => .ok ()
  | o :: os => do check o; validateOmmerHeadersE check os

/-- The containing block's list restrictions, after individual headers pass. -/
def validateOmmerList (chain : BlockChain) (header : Header)
    (ommers : List Header) : Except TransitionError Unit := do
  if ommers.length > 2 then
    ommersFail s!"block body contains {ommers.length} ommers, more than 2"
  let hashes := ommers.map Header.hash
  if hashes.eraseDups.length ≠ hashes.length then
    ommersFail "an ommer is listed twice"
  let recent := (chain.blocks.reverse.take (maxOmmerDepth + 1)).map (·.header)
  let recentHashes := recent.map Header.hash
  let recentOmmerHashes :=
    ((chain.blocks.reverse.take (maxOmmerDepth + 1)).flatMap (·.ommers)).map Header.hash
  let blockHash := header.hash
  for ommer in ommers do
    let ommerHash := ommer.hash
    if ommerHash = blockHash then
      ommersFail s!"ommer {ommerHash} is the block itself"
    if recentHashes.contains ommerHash then
      ommersFail s!"ommer {ommerHash} is a recent canonical block"
    if recentOmmerHashes.contains ommerHash then
      ommersFail s!"ommer {ommerHash} is already an ommer of a recent block"
    let age := header.number - ommer.number
    if age < 1 ∨ age > maxOmmerDepth then
      ommersFail s!"ommer {ommerHash} is {age} blocks old, \
        outside 1 to {maxOmmerDepth}"
    if ¬ recentHashes.contains ommer.parentHash then
      ommersFail s!"ommer {ommerHash} has a parent outside the recent canonical blocks"
    if ommer.parentHash = header.parentHash then
      ommersFail s!"ommer {ommerHash} is a sibling of the block"

/-- One ommer algorithm with a typed per-header resolver. Hash validation
precedes header lookup; list eligibility follows it. -/
def validateOmmersWith {ε : Type} (embed : TransitionError → ε)
    (check : Header → Except ε Unit) (chain : BlockChain) (header : Header)
    (ommers : List Header) : Except ε Unit := do
  if ommersListHash ommers ≠ header.ommersHash then
    Except.mapError embed <| ommersFail
      s!"ommers hash = {header.ommersHash} ≠ \
      hash of the ommer list = {ommersListHash ommers}"
  validateOmmerHeadersE check ommers
  Except.mapError embed (validateOmmerList chain header ommers)

/-- Static EELS-ordered ommer validation. Every header uses the explicit rules
while count, uniqueness, ancestry and age remain containing-block checks. -/
def validateOmmers (rules : ForkRules) (chain : BlockChain) (header : Header)
    (ommers : List Header) : Except TransitionError Unit :=
  validateOmmersWith id (validateOmmerHeader rules chain header) chain header ommers

/-- The block's ommers against its rules: after Paris the list must be empty
(`stateTransitionOmmersCheck`, unchanged); before it, `validateOmmers`. -/
def checkBlockOmmers (rules : ForkRules) (chain : BlockChain) (header : Header)
    (ommers : List Header) : Except TransitionError Unit :=
  match rules.proofOfWork with
  | none => Except.mapError TransitionError.block (stateTransitionOmmersCheck ommers)
  | some _ => validateOmmers rules chain header ommers

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

/-- Shared typed transition algorithm. The caller supplies only the ommer
check and a typed embedding for transition failures; header validation and
execution remain common to static and scheduled callers. The ommer action is
suspended until after the containing header has passed. -/
def stateTransitionCoreE {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except ε Unit) : Except ε BlockChain := do
  let rules := f.ruleSet
  Except.mapError embed (validateHeader rules ch block.header)
  checkOmmers ()
  let benv : Benv := initBenv f ch block.header
  let ⟨st, bout⟩ ← Except.mapError embed
    (applyBody benv block.transactions block.ommers block.withdrawals)
  let blockStateRoot : U256 := st.root
  let transactionsRoot : U256 := getTransactionsRoot bout
  let receiptRoot : U256 := getReceiptRoot bout
  let blockLogsBloom : Bytes := logsBloom bout.blockLogs
  let withdrawalsRoot : U256 := getWithdrawalsRoot bout
  let requestsHash :=
    if rules.header.requestsHash then some (computeRequestsHash bout.requests) else none
  Except.mapError (embed ∘ TransitionError.block) <|
    stateTransitionChecks bout block.header
      transactionsRoot blockStateRoot receiptRoot
      blockLogsBloom withdrawalsRoot requestsHash
  Except.mapError (embed ∘ TransitionError.block) <|
    blockAccessListCheck rules bout block.header
  .ok ⟨appendBlock ch.blocks block, st, ch.chainId⟩

private theorem transition_mapError_id {α : Type} (r : Except TransitionError α) :
    r.mapError id = r := by
  cases r <;> rfl

private theorem transition_mapError_bind {ε ε' α β : Type}
    (g : ε → ε') (r : Except ε α) (k : α → Except ε β) :
    (r.bind k).mapError g = (r.mapError g).bind (fun a => (k a).mapError g) := by
  cases r <;> rfl

private theorem transition_mapError_comp {ε ε' ε'' α : Type}
    (g : ε → ε') (g' : ε' → ε'') (r : Except ε α) :
    (r.mapError g).mapError g' = r.mapError (g' ∘ g) := by
  cases r <;> rfl

private theorem validateOmmerHeadersE_mapError {ε : Type}
    (embed : TransitionError → ε) (check : Header → Except TransitionError Unit)
    (ommers : List Header) :
    validateOmmerHeadersE (fun o => (check o).mapError embed) ommers =
      (validateOmmerHeadersE check ommers).mapError embed := by
  induction ommers with
  | nil => rfl
  | cons o os ih =>
    simp only [validateOmmerHeadersE, bind, transition_mapError_bind, ih]

private theorem validateOmmersWith_mapError {ε : Type}
    (embed : TransitionError → ε) (check : Header → Except TransitionError Unit)
    (chain : BlockChain) (header : Header) (ommers : List Header) :
    validateOmmersWith embed (fun o => (check o).mapError embed) chain header ommers =
      (validateOmmersWith id check chain header ommers).mapError embed := by
  unfold validateOmmersWith
  split <;> simp only [bind, transition_mapError_bind, transition_mapError_id,
    validateOmmerHeadersE_mapError]

/-- Embedding the static transition's error type commutes with the whole
algorithm, including failures. This is the constant-action specialization used
by a single-fork schedule. -/
theorem stateTransitionCoreE_mapError {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except TransitionError Unit) :
    stateTransitionCoreE embed f ch block
      (fun u => (checkOmmers u).mapError embed) =
      (stateTransitionCoreE id f ch block checkOmmers).mapError embed := by
  simp only [stateTransitionCoreE, transition_mapError_id, Function.id_comp, bind,
    transition_mapError_bind, transition_mapError_comp]
  rfl

/-- The static transition uses one explicitly named fork for both the block
and every ommer. It does not consult an activation schedule. -/
def stateTransitionE (f : Fork) (ch : BlockChain) (block : Block) :
  Except TransitionError BlockChain :=
  stateTransitionCoreE id f ch block
    (fun _ => checkBlockOmmers f.ruleSet ch block.header block.ommers)

/-- Scheduled ommer validation uses the ommer's own number and timestamp,
then validates against its actual retained parent. Lookup failures and candidate
failures remain distinct constructors. -/
def validateOmmerHeaderScheduledE (cfg : ChainConfig) (chain : BlockChain)
    (header ommer : Header) : Except (RulesLookupError ⊕ TransitionError) Unit := do
  let parent ← (ommerParent chain header ommer).mapError Sum.inr
  let f ← (cfg.forkAt ommer.number ommer.timestamp).mapError Sum.inl
  if f.ruleSet.proofOfWork.isNone then
    .error <| .inr <| .block <| .invalidOmmers <| .text
      "ommer's own scheduled fork does not permit proof of work"
  (validateOmmerWithParent f.ruleSet chain ommer parent).mapError Sum.inr

/-- Containing rules still decide whether ommers are allowed at all; after
Paris no resolver is consulted. The list's other restrictions are shared. -/
def checkBlockOmmersScheduledE (cfg : ChainConfig) (rules : ForkRules)
    (chain : BlockChain) (header : Header) (ommers : List Header) :
    Except (RulesLookupError ⊕ TransitionError) Unit :=
  match rules.proofOfWork with
  | none => (stateTransitionOmmersCheck ommers).mapError (Sum.inr ∘ TransitionError.block)
  | some _ => validateOmmersWith Sum.inr
      (validateOmmerHeaderScheduledE cfg chain header) chain header ommers

private def splitScheduled {α : Type} :
    Except (RulesLookupError ⊕ TransitionError) α →
      Except RulesLookupError (Except TransitionError α)
  | .error (.inl e) => .error e
  | .error (.inr e) => .ok (.error e)
  | .ok a => .ok (.ok a)

/-- A configured transition after the containing fork has been selected. Chain
identity and containing-fork lookup belong to the caller; every ommer lookup
stays on the outer typed channel. -/
def stateTransitionScheduledE (cfg : ChainConfig) (f : Fork)
    (ch : BlockChain) (block : Block) :
    Except RulesLookupError (Except TransitionError BlockChain) :=
  splitScheduled <| stateTransitionCoreE Sum.inr f ch block
    (fun _ => checkBlockOmmersScheduledE cfg f.ruleSet ch block.header block.ommers)

private theorem validateOmmerHeaderScheduledE_single (chainId : UInt64) (f : Fork)
    (chain : BlockChain) (header ommer : Header) (hp : f.ruleSet.proofOfWork.isNone = false) :
    validateOmmerHeaderScheduledE (ChainConfig.single chainId f) chain header ommer =
      (validateOmmerHeader f.ruleSet chain header ommer).mapError Sum.inr := by
  simp only [validateOmmerHeaderScheduledE, validateOmmerHeader, bind,
    ChainConfig.single_forkAt, Except.mapError, Except.bind,
    hp, Bool.false_eq_true, ↓reduceIte]
  cases ommerParent chain header ommer <;> rfl

private theorem checkBlockOmmersScheduledE_single (chainId : UInt64) (f : Fork)
    (chain : BlockChain) (header : Header) (ommers : List Header) :
    checkBlockOmmersScheduledE (ChainConfig.single chainId f) f.ruleSet chain header ommers =
      (checkBlockOmmers f.ruleSet chain header ommers).mapError Sum.inr := by
  unfold checkBlockOmmersScheduledE checkBlockOmmers
  cases hp : f.ruleSet.proofOfWork with
  | none => simp only [transition_mapError_comp]
  | some p =>
    simp only [validateOmmers]
    have hh : validateOmmerHeaderScheduledE (ChainConfig.single chainId f) chain header =
        (fun o => (validateOmmerHeader f.ruleSet chain header o).mapError Sum.inr) := by
      funext o
      exact validateOmmerHeaderScheduledE_single chainId f chain header o (by simp [hp])
    rw [hh, validateOmmersWith_mapError]

/-- All results, including every transition error, agree with the static core
under a constant schedule. No ommer lookup can fail on that schedule. -/
theorem stateTransitionScheduledE_single (chainId : UInt64) (f : Fork)
    (ch : BlockChain) (block : Block) :
    stateTransitionScheduledE (ChainConfig.single chainId f) f ch block =
      .ok (stateTransitionE f ch block) := by
  unfold stateTransitionScheduledE stateTransitionE
  simp only [checkBlockOmmersScheduledE_single]
  rw [stateTransitionCoreE_mapError]
  cases stateTransitionCoreE id f ch block
    (fun _ => checkBlockOmmers f.ruleSet ch block.header block.ommers) <;> rfl

/-- With no proof-of-work ommers, configured and static cores agree on all
results for any schedule: the containing list prohibition runs first. -/
theorem stateTransitionScheduledE_of_pow_none (cfg : ChainConfig) (f : Fork)
    (ch : BlockChain) (block : Block) (hp : f.ruleSet.proofOfWork = none) :
    stateTransitionScheduledE cfg f ch block = .ok (stateTransitionE f ch block) := by
  unfold stateTransitionScheduledE stateTransitionE
  have ho : checkBlockOmmersScheduledE cfg f.ruleSet ch block.header block.ommers =
      (checkBlockOmmers f.ruleSet ch block.header block.ommers).mapError Sum.inr := by
    simp only [checkBlockOmmersScheduledE, checkBlockOmmers, hp, transition_mapError_comp]
  simp only [ho]
  rw [stateTransitionCoreE_mapError]
  cases stateTransitionCoreE id f ch block
    (fun _ => checkBlockOmmers f.ruleSet ch block.header block.ommers) <;> rfl

theorem stateTransitionScheduledE_eq_ok_iff {cfg : ChainConfig} {f : Fork}
    {ch ch' : BlockChain} {block : Block} :
    stateTransitionScheduledE cfg f ch block = .ok (.ok ch') ↔
      stateTransitionCoreE Sum.inr f ch block
        (fun _ => checkBlockOmmersScheduledE cfg f.ruleSet ch block.header block.ommers)
        = .ok ch' := by
  unfold stateTransitionScheduledE
  cases stateTransitionCoreE Sum.inr f ch block
      (fun _ => checkBlockOmmersScheduledE cfg f.ruleSet ch block.header block.ommers) with
  | error e => cases e <;> simp [splitScheduled]
  | ok a => simp [splitScheduled]

theorem stateTransitionCoreE_header {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (h : stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    validateHeader f.ruleSet ch block.header = .ok () := by
  unfold stateTransitionCoreE at h
  obtain ⟨u, hu, _⟩ := Except.bind_eq_ok h
  cases u
  exact Except.mapError_eq_ok_iff.mp hu

/-- Error embeddings and ommer resolution cannot change the chain identity
copied by any successful execution of the common algorithm. -/
theorem stateTransitionCoreE_preserves_chainId {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (h : stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    ch'.chainId = ch.chainId := by
  unfold stateTransitionCoreE at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨st, bout⟩, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases h
  rfl

/-- Legacy renderer adapter over `stateTransitionE`, byte-identical on every
input, and the entry point for static fixture suites, which state their fork
rather than deriving it.

Named `stateTransitionWith` and taking a `ForkRules` until goal
`jaune-forks-by-construction-v1`. Once a machine carries a `Fork`, the
rules-taking adapter and this one had the same domain, so the duplicate layer
was retired into this name rather than kept as a synonym; there is no longer a
rules-taking entry point that could be handed a record no fork realises. The
`UnsupportedForkError` vocabulary remains where `Fork.rules` renders an
absent record. Earlier historical waves used that route for pre-Berlin
forks; this candidate resolves their records too. -/
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
from the block's number and timestamp and the chain's activation schedule.

Checks the configuration against the snapshot's chain identity before doing
anything else -- P0.1's fix -- then proceeds exactly as before. -/
def stateTransitionUsing (cfg : ChainConfig) (ch : BlockChain) (block : Block) :
    Except String BlockChain := do
  Except.mapError ChainContextError.render (cfg.checkChainId ch)
  let f ← Except.mapError RulesLookupError.render
    (cfg.forkAt block.header.number block.header.timestamp)
  match stateTransitionScheduledE cfg f ch block with
  | .error e => .error e.render
  | .ok r => r.mapError TransitionError.render

private theorem stateTransitionUsing_run {cfg : ChainConfig} {ch ch' : BlockChain}
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

/-- The Prague state transition.

Retained with its original name, type, and behaviour. Prague is permanent
supported protocol, not scaffolding, and downstream proofs state their results
about this name. -/
def stateTransition (ch : BlockChain) (block : Block) :
  Except String BlockChain :=
  stateTransitionAt .prague ch block

def Rlp.Item.toExceptWithdrawal : Rlp.Item → Except DecodeError Withdrawal
  | .list [
      .bytes globalIndex,
      .bytes validatorIndex,
      .bytes recipient,
      .bytes amount
    ] => do
    -- Check every untrusted field before constructing the withdrawal. In
    -- particular, `Bytes.toUInt64` truncates modulo 2^64, so it may only see the
    -- byte string returned by the at-most-eight-byte decoder.
    let globalIndex ← globalIndex.toRlpUInt64 "withdrawal globalIndex"
    let validatorIndex ← validatorIndex.toRlpUInt64 "withdrawal validatorIndex"
    let recipient ← recipient.toRlpAddress "withdrawal recipient"
    -- EIP-4895: `amount` is a 64-bit Gwei scalar on the wire, even though the
    -- `Withdrawal` field stores it as 256 bits for balance arithmetic.
    let amount ← amount.toRlpUInt64 "withdrawal amount"
    .ok {
      index := globalIndex,
      validatorIndex := validatorIndex,
      address := recipient,
      amount := amount.toNat.toU256
    }
  | _ =>
    .error <| DecodeError.structure "withdrawal"
      "expected a list of four byte-string fields"

/-- Strict withdrawal-decoder soundness: the amount a decoded withdrawal
carries always fits its 64-bit wire type, even though the field is 256 bits
wide. -/
theorem Rlp.Item.toExceptWithdrawal_wireWellFormed {blt : Rlp.Item} {w : Withdrawal}
    (h : blt.toExceptWithdrawal = .ok w) : w.WireWellFormed := by
  unfold Rlp.Item.toExceptWithdrawal at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    exact UInt64.toNat_toU256_high _
  · exact absurd h (by simp)

/-- The strict legacy-transaction decoder over the nine-field list shape. Split
out of the slot decoder so the block decoder can consume it on the pure decode
carrier: a legacy list produces only decode reasons, while the byte-string
route (`Bytes.toExTx`) can also produce typed rejections. -/
def Rlp.Item.toExceptLegacyTransaction : List Rlp.Item → Except DecodeError Transaction
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
    let nonce ← nonce.toRlpUInt64 "legacy transaction nonce"
    let gasPrice ← gasPrice.toRlpNat "legacy transaction gasPrice" 32
    let gas ← gas.toRlpNat "legacy transaction gas" 32
    let receiver ← receiver.toRlpReceiver "legacy transaction receiver"
    let value ← value.toRlpNat "legacy transaction value" 32
    let v ← v.toRlpNat "legacy transaction v" 32
    -- Validate signature scalars before sender recovery, but retain their
    -- minimally encoded byte representation so valid legacy signing and
    -- encoding behavior is unchanged.
    let _ ← r.toRlpU256 "legacy transaction r"
    let _ ← s.toRlpU256 "legacy transaction s"
    .ok {
      nonce := nonce,
      gasLimit := gas
      value := value,
      data := data,
      v := v,
      r := r,
      s := s,
      type := .legacy gasPrice receiver
    }
  | _ =>
    .error <| DecodeError.structure "legacy transaction"
      "expected a list of nine byte-string fields"

/-- A transaction slot as a standalone value: a legacy list through the strict
legacy decoder, typed-envelope bytes through the strict envelope decoder. -/
def Rlp.Item.toExceptTransaction : Rlp.Item → Except TransitionError Transaction
  | .list ls => dec (Rlp.Item.toExceptLegacyTransaction ls)
  | .bytes xs => xs.toExceptTransaction

/-- Strict legacy-transaction-decoder soundness. A *list*-shaped transaction
item is the legacy route, so what it yields is both wire-well-formed and of
legacy type -- which is exactly `TxEntry.WireWellFormed` on the decoded side of
a block body's transaction slot. The typed route never reaches this decoder,
and never produces a `.zero` transaction. -/
theorem Rlp.Item.toExceptLegacyTransaction_wireWellFormed {bs : List Rlp.Item} {tx : Transaction}
    (h : Rlp.Item.toExceptLegacyTransaction bs = .ok tx) :
    Transaction.WireWellFormed tx ∧ tx.type.isLegacy = true := by
  unfold Rlp.Item.toExceptLegacyTransaction at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩ <;>
      first
        | exact Bytes.toRlpNat_lt_two_pow_256 (by assumption)
        | exact Bytes.toRlpU256_eq_ok (by assumption)
  · exact absurd h (by simp)

def Rlp.Item.toExceptBlock : Rlp.Item → Except DecodeError Block
  | Rlp.Item.list [
      HeaderBLT,
      .list TxBLTs,
      .list OmmerBLTs,
      .list WithdrawalBLTs
    ] => do
    let header ← HeaderBLT.toExceptHeader
    let aux : Rlp.Item → Except DecodeError (Bytes ⊕ Transaction)
      | .list ls => Rlp.Item.toExceptLegacyTransaction ls <&> .inr
      | .bytes xs => .ok <| .inl xs
    let txs ← List.mapM aux TxBLTs
    let ommers ← List.mapM Rlp.Item.toExceptHeader OmmerBLTs
    let withdrawals ← List.mapM Rlp.Item.toExceptWithdrawal WithdrawalBLTs
    .ok {
      header := header,
      transactions := txs,
      ommers := ommers,
      withdrawals := withdrawals
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
theorem Rlp.Item.toExceptBlock_rlpCanonical {blt : Rlp.Item} {b : Block}
    (h : blt.toExceptBlock = .ok b) : b.RlpCanonical := by
  unfold Rlp.Item.toExceptBlock at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨Rlp.Item.toExceptHeader_wireWellFormed (by assumption), ?_, ?_, ?_⟩
    · intro o ho
      obtain ⟨blt', hblt'⟩ := List.mapM_except_eq_ok_mem (by assumption) o ho
      exact Rlp.Item.toExceptHeader_wireWellFormed hblt'
    · intro w hw
      obtain ⟨blt', hblt'⟩ := List.mapM_except_eq_ok_mem (by assumption) w hw
      exact Rlp.Item.toExceptWithdrawal_wireWellFormed hblt'
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
        exact Rlp.Item.toExceptLegacyTransaction_wireWellFormed htx
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
def rlpToBlockE (rlp : Bytes) : Except DecodeError (Block × U256) := do
  let block_blt ← (Bytes.toRlpItem? rlp).toExcept <|
    DecodeError.structure "block RLP" "cannot decode the outer RLP item"
  let block ← block_blt.toExceptBlock
  let canonicalRlp := block.toRlpItem.toBytes
  if rlp ≠ canonicalRlp then
    .error <| .roundTrip <|
      .text "decoded block does not re-encode byte-for-byte"
  .ok ⟨block, (Header.toRlpItem block.header).toBytes.keccak⟩

/-- Legacy renderer adapter over `rlpToBlockE`, byte-identical on every input.
Retained by name and type because Blanc's protected
`addBlockToChain_preserves_solvent` quantifies over exactly this equation, and
the canonical envelope's evidence field is stated with it. -/
def rlpToBlock (rlp : Bytes) : Except String (Block × U256) :=
  (rlpToBlockE rlp).mapError DecodeError.render

/-- The adapter adds rendering and nothing else: success is the typed core's
success. This is the bridge every string-level client inverts through. -/
theorem rlpToBlock_eq_ok_iff {rlp : Bytes} {p : Block × U256} :
    rlpToBlock rlp = .ok p ↔ rlpToBlockE rlp = .ok p :=
  Except.mapError_eq_ok_iff

---------------- FORK-RELATIVE WIRE DECODER ---------------

/-- The fork-relative wire encoding of a block body: the withdrawals element
rides along from Shanghai, so a pre-Shanghai body encodes three elements, not
four. `Block.toBLT` stays the canonical four-element encoding the proven
paths hash and compare through; this is the shape the fork's own fixtures
carry. Under Shanghai rules and later it is `Block.toBLT`, definitionally. -/
def Block.toRlpItemAt (rules : ForkRules) (b : Block) : Rlp.Item :=
  if rules.header.withdrawalsRoot then b.toRlpItem
  else .list [Header.toRlpItem b.header, .list (b.transactions.map BytesOrTransactionToRlpItem),
    .list (b.ommers.map Header.toRlpItem)]

/-- The fork-relative strict body decoder: a three-element body decodes with
no withdrawals exactly when the rules do not carry them, and is the
`withdrawalsNotRead` error `BLT.toExBlock` reports when they do. A
four-element body decodes through `BLT.toExBlock` under every fork, so the
post-Shanghai shape and every error it reports are shared, not duplicated. -/
def Rlp.Item.toExceptBlockAt (rules : ForkRules) : Rlp.Item → Except DecodeError Block
  | .list [HeaderBLT, .list TxBLTs, .list OmmerBLTs] =>
    if rules.header.withdrawalsRoot then
      .error (.withdrawalsNotRead (.text
        "post-Shanghai block body omits the withdrawals list"))
    else Rlp.Item.toExceptBlock
      (.list [HeaderBLT, .list TxBLTs, .list OmmerBLTs, .list []])
  | blt => blt.toExceptBlock

/-- The fork-relative strict block decoder: `rlpToBlockE` on the fork's own
wire shape. The round trip compares against the fork-relative encoding, so a
pre-Shanghai three-element body re-encodes to itself; under Shanghai rules
and later the comparison -- and every success and failure -- is
`rlpToBlockE`'s. `rlpToBlockE` itself is untouched: the proven envelope keeps
its equation. -/
def rlpToBlockEAt (rules : ForkRules) (rlp : Bytes) :
    Except DecodeError (Block × U256) := do
  let block_blt ← (Bytes.toRlpItem? rlp).toExcept <|
    DecodeError.structure "block RLP" "cannot decode the outer RLP item"
  let block ← block_blt.toExceptBlockAt rules
  let canonicalRlp := (block.toRlpItemAt rules).toBytes
  if rlp ≠ canonicalRlp then
    .error <| .roundTrip <|
      .text "decoded block does not re-encode byte-for-byte"
  .ok ⟨block, (Header.toRlpItem block.header).toBytes.keccak⟩

--------------- THE CANONICAL OUTER-BLOCK ENVELOPE ---------------

/-- The hash `rlpToBlock` returns is always the keccak of the decoded header's
canonical encoding. It is therefore *derivable* from the decoded block and was
never independent evidence, which is why the import core below takes an
envelope instead of a separate hash argument. -/
theorem rlpToBlock_headerHash {raw : Bytes} {block : Block} {hash : U256}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) :
    hash = (Header.toRlpItem block.header).toBytes.keccak := by
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
theorem rlpToBlock_canonical {raw : Bytes} {block : Block} {hash : U256}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) : block.toRlpItem.toBytes = raw := by
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
theorem rlpToBlock_rlpCanonical {raw : Bytes} {block : Block} {hash : U256}
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
    exact Rlp.Item.toExceptBlock_rlpCanonical hb

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
    rlpToBlock raw = .ok ⟨block, (Header.toRlpItem block.header).toBytes.keccak⟩
  /-- Exact re-encoding evidence. -/
  canonical : block.toRlpItem.toBytes = raw

/-- The checked smart constructor: an envelope may only be built from the
strict decoder's own equation. -/
def CanonicalBlock.ofDecode {raw : Bytes} {block : Block} {hash : U256}
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
def CanonicalBlock.headerHash (cb : CanonicalBlock) : U256 :=
  (Header.toRlpItem cb.block.header).toBytes.keccak

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
    cb.block.toRlpItem.toBytes = cb.raw := cb.canonical

theorem CanonicalBlock.rawSize_eq (cb : CanonicalBlock) :
    cb.rawSize = cb.raw.length := rfl

/-- Introduction: strict decode succeeds exactly when an envelope exists, and
the envelope it yields carries those very bytes and that very block. -/
theorem CanonicalBlock.ofRlp?_eq_some {raw : Bytes} {block : Block} {hash : U256}
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
def CheckedHeader.ofDecode {blt : Rlp.Item} {h : Header}
    (hd : blt.toExceptHeader = .ok h) : CheckedHeader :=
  ⟨h, Rlp.Item.toExceptHeader_wireWellFormed hd⟩

/-- A withdrawal certified wire-well-formed. -/
structure CheckedWithdrawal : Type where
  private mk ::
  val : Withdrawal
  wireWellFormed : val.WireWellFormed

def CheckedWithdrawal.ofWithdrawal? (w : Withdrawal) : Option CheckedWithdrawal :=
  if hw : w.WireWellFormed then some ⟨w, hw⟩ else none

def CheckedWithdrawal.ofDecode {blt : Rlp.Item} {w : Withdrawal}
    (hd : blt.toExceptWithdrawal = .ok w) : CheckedWithdrawal :=
  ⟨w, Rlp.Item.toExceptWithdrawal_wireWellFormed hd⟩

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
  entry : Bytes ⊕ Transaction
  wellFormed : TxEntry.WireWellFormed entry

/-- The opaque typed slot. Nothing is decoded here. -/
def TxEnvelope.ofTypedBytes (bs : Bytes) : TxEnvelope := ⟨.inl bs, trivial⟩

/-- The decoded legacy slot, from the strict decoder's own equation. -/
def TxEnvelope.ofLegacyDecode {ls : List Rlp.Item} {tx : Transaction}
    (h : Rlp.Item.toExceptLegacyTransaction ls = .ok tx) : TxEnvelope :=
  ⟨.inr tx, Rlp.Item.toExceptLegacyTransaction_wireWellFormed h⟩

/-- The raw compatibility constructor: it carries no evidence, so it validates
once, here, rather than leaving a slot to be trusted later. -/
def TxEnvelope.ofEntry? (e : Bytes ⊕ Transaction) : Option TxEnvelope :=
  if h : TxEntry.WireWellFormed e then some ⟨e, h⟩ else none

/-- The envelope byte a typed transaction is carried under; `none` for legacy,
which has no envelope. -/
def TransactionType.envelopeByte : TransactionType → Option UInt8
  | .legacy _ _ => none
  | .eip2930 _ _ _ _ => some 0x01
  | .eip1559 _ _ _ _ _ => some 0x02
  | .eip4844 _ _ _ _ _ _ _ => some 0x03
  | .eip7702 _ _ _ _ _ _ => some 0x04

/-- A hand-built typed transaction's route into a block body: its envelope
byte followed by its payload. Placing the same record directly as a decoded
slot would re-encode it through the legacy list, corrupting both the
transactions trie and the signing hash -- which is why that route does not
exist. Legacy transactions have no envelope and are refused here; they enter
as decoded slots through `TxEnvelope.ofEntry?`. -/
def Transaction.toTypedEnvelope? (tx : Transaction) : Option TxEnvelope :=
  tx.type.envelopeByte.map fun b => TxEnvelope.ofTypedBytes (b :: tx.toRlpItem.toBytes)

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
        transactions := txs.map TxEnvelope.entry
        ommers := ommers.map CheckedHeader.val
        withdrawals := wds.map CheckedWithdrawal.val }
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

`decodeTx rules (.inr tx) = .ok tx` still holds -- revalidating a
decoder-produced legacy transaction late in `applyBody` is exactly what the
plan forbids -- but
on the checked path it is no longer an *assumption*. Every decoded slot of a
canonical outer block is a wire-well-formed legacy transaction, so what
`decodeTx` returns there is certified, and the ingress side can no longer be
handed an uncertified `.inr Tx` at all. -/
theorem CanonicalBlock.decodeTx_inr {cb : CanonicalBlock} {tx : Transaction}
    (rules : ForkRules)
    (h : Sum.inr tx ∈ cb.block.transactions) :
    decodeTransaction rules (.inr tx) = .ok tx ∧
      Transaction.WireWellFormed tx ∧ tx.type.isLegacy = true :=
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
def CheckedBlockChain.tipHash (cc : CheckedBlockChain) : U256 :=
  cc.tip.header.hash

/-- The snapshot's committed state root, read from the tip header rather than
rebuilt from the world -- the same trade `tipHash` makes, for the same reason:
`tipStateRoot` is already the proof that the two agree, so recomputing
`val.state.root` here would rebuild the whole trie to learn something the
structure carries. -/
def CheckedBlockChain.stateRoot (cc : CheckedBlockChain) : U256 :=
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
  rw [ite_eq_left pc.chainId_eq]

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

/-- Canonical-envelope configured import after the containing fork lookup.
Size rejection precedes the shared transition. Ommer lookup failures are
operational import failures and can never become scored block rejections. -/
def addBlockToChainScheduledCanonicalE (cfg : ChainConfig) (f : Fork)
    (chain : BlockChain) (cb : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) :=
  match checkBlockRlpSize f.ruleSet.block cb.rawSize with
  | .error err => .ok (.inr (.block err))
  | .ok () =>
    match stateTransitionScheduledE cfg f chain cb.block with
    | .error e => .error (ImportFailure.ofLookup e)
    | .ok (.error e) =>
      match e.split with
      | .inl failure => .error failure
      | .inr rejection => .ok (.inr rejection)
    | .ok (.ok chain') => .ok (.inl chain')

/-- A scheduled ommer lookup failure stays operational at the import boundary. -/
theorem addBlockToChainScheduledCanonicalE_lookup_error {cfg : ChainConfig} {f : Fork}
    {chain : BlockChain} {cb : CanonicalBlock} {e : RulesLookupError}
    (hsize : checkBlockRlpSize f.ruleSet.block cb.rawSize = .ok ())
    (hlookup : stateTransitionScheduledE cfg f chain cb.block = .error e) :
    addBlockToChainScheduledCanonicalE cfg f chain cb = .error (ImportFailure.ofLookup e) := by
  simp only [addBlockToChainScheduledCanonicalE, hsize, hlookup]

theorem addBlockToChainScheduledCanonicalE_eq_ok_inl {cfg : ChainConfig} {f : Fork}
    {chain chain' : BlockChain} {cb : CanonicalBlock}
    (h : addBlockToChainScheduledCanonicalE cfg f chain cb = .ok (.inl chain')) :
    checkBlockRlpSize f.ruleSet.block cb.rawSize = .ok () ∧
      stateTransitionScheduledE cfg f chain cb.block = .ok (.ok chain') := by
  unfold addBlockToChainScheduledCanonicalE at h
  split at h
  · simp at h
  · rename_i u hsize
    split at h
    · simp at h
    · split at h <;> simp_all
    · rename_i ch hst
      simp only [Except.ok.injEq, Sum.inl.injEq] at h
      exact ⟨hsize, h ▸ hst⟩

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
duplicate layer was retired into this name. Its `.support` channel remains
for an absent rule record. Earlier historical waves used that route for
pre-Berlin forks; this candidate resolves their records too. -/
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
decode, inside `cfg.forkAt` below, because no number or timestamp exists before
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
        (cfg.forkAt block.header.number block.header.timestamp)
    addBlockToChainScheduledCanonicalE cfg fork chain
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
    {blockRlp : Bytes} {block : Block} {hash : U256}
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
  unfold stateTransitionE stateTransitionCoreE at h
  simp only [transition_mapError_id, Function.id_comp] at h
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
  obtain ⟨f, _, hs⟩ := stateTransitionUsing_run h
  exact stateTransitionCoreE_preserves_chainId (stateTransitionScheduledE_eq_ok_iff.mp hs)

/-- A same-ID configured transition is exactly the rule-selected core: the
identity check Step 2 adds is a no-op whenever the caller's IDs already agree,
so no previously-agreeing caller observes any behavioral change. -/
theorem stateTransitionUsing_eq_of_chainId_eq
    {cfg : ChainConfig} {ch : BlockChain} {block : Block}
    (heq : cfg.chainId = ch.chainId) :
    stateTransitionUsing cfg ch block
      = (Except.mapError RulesLookupError.render
          (cfg.forkAt block.header.number block.header.timestamp)).bind
          (fun f =>
            match stateTransitionScheduledE cfg f ch block with
            | .error e => .error e.render
            | .ok r => r.mapError TransitionError.render) := by
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
        obtain ⟨_, hst⟩ := addBlockToChainScheduledCanonicalE_eq_ok_inl hE
        exact stateTransitionCoreE_preserves_chainId
          (stateTransitionScheduledE_eq_ok_iff.mp hst)

--------------- CANONICALITY THROUGH EXECUTION (P0.4, STEP 4) ---------------

-- Checkpoint 3: canonicality through message-call processing, transaction
-- processing, system transactions, withdrawals, the block body, and the raw
-- successful block transition. Every lemma states the success channel; the
-- error channel at this layer carries no state.

private theorem chargeNewAuthorityAmsterdam_canonical {state : StateGasRules}
    {authority : Address} {devm : Devm} (h : devm.Canonical) :
    (chargeNewAuthorityAmsterdam state authority devm).Canonical := by
  unfold chargeNewAuthorityAmsterdam
  split
  · exact liftMachExecution_canonical h
  · exact h

private theorem chargePaidAccountWriteAmsterdam_canonical
    {state : StateGasRules} {authority : Address} {devm : Devm}
    {paidWrites : AdrSet} (h : devm.Canonical) :
    (chargePaidAccountWriteAmsterdam state authority devm paidWrites).CanonicalOn
      (fun r => r.1.Canonical) := by
  unfold chargePaidAccountWriteAmsterdam
  split
  · exact h
  · exact Except.CanonicalOn.bind (chargeGas_canonical h) (fun _ hd => hd)

private theorem chargeAuthBaseAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} {authority target : Address} {devm : Devm}
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
    {state : StateGasRules} {msg : Msg} {authority target : Address}
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
    {state : StateGasRules} {msg : Msg} {auth : Authorization} {devm : Devm}
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
    {state : StateGasRules} {msg : Msg} {auths : List Authorization} {devm : Devm}
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
  rcases msg.benv.stat.rules.delegationCost devm msg.currentTarget
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

/-! ### The prepared top-level state -/

private theorem liftMachExecution_ok_meta {core : Mach → Footprint.Outcome Mach Unit} {d d' : Devm}
    (h : liftMachExecution core d = .ok d') : d'.meta = d.meta := by
  simp only [liftMachExecution, liftMach, Footprint.toExecution, Footprint.liftOutcome] at h
  rcases hc : core d.mach with ⟨err, view⟩ | ⟨u, view⟩ <;> rw [hc] at h <;>
    simp only [Except.ok.injEq, reduceCtorEq] at h
  · cases h; rfl

/-- A machine whose output and stored error are a fresh frame's. -/
private def Fresh (d : Devm) : Prop := d.meta.output = [] ∧ d.meta.error = none

private theorem Fresh.of_meta {d d' : Devm} (h : Fresh d) (hm : d'.meta = d.meta) : Fresh d' := by
  unfold Fresh; rw [hm]; exact h

private theorem Fresh.chargeStateGas {a : Nat} {d d' : Devm} (h : Fresh d)
    (hc : Jaune.chargeStateGas a d = .ok d') : Fresh d' := h.of_meta (liftMachExecution_ok_meta hc)

private theorem Fresh.chargeGas {a : Nat} {d d' : Devm} (h : Fresh d)
    (hc : Jaune.chargeGas a d = .ok d') : Fresh d' := h.of_meta (liftMachExecution_ok_meta hc)

private theorem Fresh.balReadAccount {d : Devm} (h : Fresh d) (r : ForkRules) (a : Address) :
    Fresh (d.balReadAccount r a) := by
  unfold Devm.balReadAccount; split <;> exact h

private theorem Fresh.addAccessedAddress {d : Devm} (h : Fresh d) (a : Address) :
    Fresh (addAccessedAddress d a) := h

private theorem Fresh.setCode {d : Devm} (h : Fresh d) (a : Address) (c : ByteArray) :
    Fresh (d.setCode a c) := h

private theorem Fresh.incrNonce {d : Devm} (h : Fresh d) (a : Address) : Fresh (d.incrNonce a) := h

private theorem Fresh.commitStateGas {d : Devm} (h : Fresh d) : Fresh d.commitStateGas := h

private theorem chargeNewAuthorityAmsterdam_fresh {state : StateGasRules} {a : Address} {d d' : Devm}
    (h : Fresh d) (hc : chargeNewAuthorityAmsterdam state a d = .ok d') : Fresh d' := by
  unfold chargeNewAuthorityAmsterdam at hc
  split at hc
  · exact h.chargeStateGas hc
  · cases hc; exact h

private theorem chargePaidAccountWriteAmsterdam_fresh {state : StateGasRules} {a : Address} {d : Devm}
    {s : AdrSet} {p : Devm × AdrSet} (h : Fresh d)
    (hc : chargePaidAccountWriteAmsterdam state a d s = .ok p) : Fresh p.1 := by
  unfold chargePaidAccountWriteAmsterdam at hc
  split at hc
  · cases hc; exact h
  · obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
    cases hc; exact h.chargeGas h1

private theorem chargeAuthBaseAmsterdam_fresh {state : StateGasRules} {msg : Msg} {a t : Address}
    {d : Devm} {s : AdrSet} {p : Devm × AdrSet × ByteArray} (h : Fresh d)
    (hc : chargeAuthBaseAmsterdam state msg a t d s = .ok p) : Fresh p.1 := by
  unfold chargeAuthBaseAmsterdam at hc
  split at hc
  · cases hc; exact h
  · dsimp only at hc
    split at hc
    · obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
      cases hc; exact h.chargeStateGas h1
    · obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
      cases h1; cases hc; exact h

private theorem applyValidatedDelegationAmsterdam_fresh {state : StateGasRules} {msg : Msg}
    {a t : Address} {d : Devm} {s1 s2 : AdrSet} {p : AmsterdamDelegationResult} (h : Fresh d)
    (hc : applyValidatedDelegationAmsterdam state msg a t d s1 s2 = .ok p) : Fresh p.1 := by
  unfold applyValidatedDelegationAmsterdam at hc
  obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
  obtain ⟨⟨d2, w2⟩, h2, hc⟩ := Except.bind_eq_ok hc
  obtain ⟨⟨d3, w3, c3⟩, h3, hc⟩ := Except.bind_eq_ok hc
  cases hc
  exact (((chargeAuthBaseAmsterdam_fresh (chargePaidAccountWriteAmsterdam_fresh
    (chargeNewAuthorityAmsterdam_fresh h h1) h2) h3).setCode _ _).incrNonce _)

private theorem setDelegationAmsterdamStep_fresh {state : StateGasRules} {msg : Msg}
    {auth : Authorization} {d : Devm} {s1 s2 : AdrSet} {p : AmsterdamDelegationResult}
    (h : Fresh d) (hc : setDelegationAmsterdamStep state msg auth d s1 s2 = .ok p) :
    Fresh p.1 := by
  unfold setDelegationAmsterdamStep at hc
  split at hc
  · cases hc; exact h
  · split at hc
    · cases hc; exact h
    · split at hc
      · cases hc; exact h
      · simp only [reduceCtorEq] at hc
      · rename_i authority _
        have hD := (h.addAccessedAddress authority).balReadAccount msg.benv.stat.rules authority
        dsimp only at hc
        generalize Devm.balReadAccount msg.benv.stat.rules authority
          (addAccessedAddress d authority) = D at hD hc
        split at hc
        · cases hc; exact hD
        · split at hc
          · cases hc; exact hD
          · exact applyValidatedDelegationAmsterdam_fresh hD hc

private theorem setDelegationAmsterdamLoop_fresh {state : StateGasRules} {msg : Msg} :
    ∀ (auths : List Authorization) {d : Devm} {s1 s2 : AdrSet} {p : AmsterdamDelegationResult},
      Fresh d → setDelegationAmsterdamLoop state msg auths d s1 s2 = .ok p → Fresh p.1
  | [], _, _, _, _, h, hc => by cases hc; exact h
  | auth :: auths, d, s1, s2, p, h, hc => by
    unfold setDelegationAmsterdamLoop at hc
    obtain ⟨⟨d1, w1, w2⟩, h1, hc⟩ := Except.bind_eq_ok hc
    exact setDelegationAmsterdamLoop_fresh auths (setDelegationAmsterdamStep_fresh h h1) hc

private theorem resolveTopLevelCallAmsterdam_fresh {msg : Msg} {d : Devm} {p : Msg × Devm} (h : Fresh d)
    (hc : resolveTopLevelCallAmsterdam msg d = .ok p) : Fresh p.2 := by
  unfold resolveTopLevelCallAmsterdam at hc
  obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
  cases hc
  show Fresh (Devm.balReadAccount _ _ _)
  refine Fresh.balReadAccount ?_ _ _
  show Fresh (completeDelegationAccess _ _ _).2
  unfold completeDelegationAccess
  dsimp only
  split
  · exact (h.chargeGas h1).addAccessedAddress _
  · exact h.chargeGas h1

private theorem prepared_fresh {state : StateGasRules} {msg : Msg} {p : Msg × Devm}
    (h : prepareTopLevelAmsterdam state msg = .ok p) : Fresh p.2 := by
  have key : ∀ d1, Fresh d1 → finishTopLevelAmsterdam state msg d1 = .ok p → Fresh p.2 := by
    intro d1 hd1 h
    unfold finishTopLevelAmsterdam dispatchTopLevelAmsterdam at h
    have hd2 : Fresh (if msg.tenv.stat.auths.isEmpty then d1 else d1.commitStateGas) := by
      split
      · exact hd1
      · exact hd1.commitStateGas
    generalize (if msg.tenv.stat.auths.isEmpty then d1 else d1.commitStateGas) = d2 at hd2 h
    have hd3 := hd2.balReadAccount msg.benv.stat.rules msg.currentTarget
    dsimp only at h
    split at h
    · split at h
      · simp only [reduceCtorEq] at h
      · split at h <;> obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h <;> cases h
        · exact hd3.chargeStateGas h4
        · cases h4; exact hd3
    · split at h <;> obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h
      · exact resolveTopLevelCallAmsterdam_fresh (hd3.chargeStateGas h4) h
      · cases h4; exact resolveTopLevelCallAmsterdam_fresh hd3 h
  have h0 : Fresh (initDevm msg) := ⟨rfl, rfl⟩
  unfold prepareTopLevelAmsterdam at h
  dsimp only at h
  split at h
  · obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
    cases h1
    exact key _ h0 h
  · obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
    unfold setDelegationAmsterdam at h1
    obtain ⟨⟨d2, w1, w2⟩, h2, h1⟩ := Except.bind_eq_ok h1
    cases h1
    exact key _ (setDelegationAmsterdamLoop_fresh _ h0 h2) h


/-- The prepared message carries its machine's world, created accounts and accessed sets. -/
private def Coh (m : Msg) (d : Devm) : Prop :=
  m.benv.state = d.state ∧ m.benv.storageWrites = d.world.storageWrites ∧
    m.tenv.transientStorage = d.transientStorage ∧ m.benv.createdAccounts = d.createdAccounts ∧
    m.accessedAddresses = d.accessedAddresses ∧ m.accessedStorageKeys = d.accessedStorageKeys

private theorem prepared_coh {state : StateGasRules} {msg : Msg} {p : Msg × Devm}
    (h : prepareTopLevelAmsterdam state msg = .ok p) : Coh p.1 p.2 := by
  have hcall : ∀ {d : Devm} {p : Msg × Devm}, resolveTopLevelCallAmsterdam msg d = .ok p →
      Coh p.1 p.2 := by
    intro d p hc
    unfold resolveTopLevelCallAmsterdam at hc
    obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
    cases hc
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have key : ∀ d1, finishTopLevelAmsterdam state msg d1 = .ok p → Coh p.1 p.2 := by
    intro d1 h
    unfold finishTopLevelAmsterdam dispatchTopLevelAmsterdam at h
    generalize (if msg.tenv.stat.auths.isEmpty then d1 else d1.commitStateGas) = d2 at h
    dsimp only at h
    split at h
    · split at h
      · simp only [reduceCtorEq] at h
      · split at h <;> obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h <;> cases h <;>
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split at h <;> obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h <;> exact hcall h
  unfold prepareTopLevelAmsterdam at h
  dsimp only at h
  split at h <;> obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h <;> exact key _ h

/-- **The prepared top-level state.** What Amsterdam's preparation hands the top frame stores no
output and no settled error, and the prepared message carries its world, created accounts and
accessed sets. So the top frame over it, whose checkpoint is this state, starts from it exactly
(`Frame.State.toDevm_ofDevm`), and the prepared message is coherent with it. -/
theorem prepareTopLevelAmsterdam_prepared {state : StateGasRules} {msg : Msg} {p : Msg × Devm}
    (h : prepareTopLevelAmsterdam state msg = .ok p) :
    p.2.output = [] ∧ p.2.error = none ∧ p.1.benv.state = p.2.state ∧
      p.1.benv.storageWrites = p.2.world.storageWrites ∧
      p.1.tenv.transientStorage = p.2.transientStorage ∧
      p.1.benv.createdAccounts = p.2.createdAccounts ∧
      p.1.accessedAddresses = p.2.accessedAddresses ∧
      p.1.accessedStorageKeys = p.2.accessedStorageKeys :=
  ⟨(prepared_fresh h).1, (prepared_fresh h).2, prepared_coh h⟩

/-- **The prepared top-level message.** Amsterdam's preparation keeps the message's target; a
creation keeps its code address, and a call leaves with one (`resolveTopLevelCallAmsterdam`). -/
theorem prepareTopLevelAmsterdam_message {state : StateGasRules} {msg : Msg} {p : Msg × Devm}
    (h : prepareTopLevelAmsterdam state msg = .ok p) :
    p.1.target = msg.target ∧ (msg.target = none → p.1.codeAddress = msg.codeAddress) ∧
      (msg.target ≠ none → p.1.codeAddress ≠ none) := by
  have hcall : ∀ {d : Devm} {p : Msg × Devm}, resolveTopLevelCallAmsterdam msg d = .ok p →
      p.1.target = msg.target ∧ p.1.codeAddress ≠ none := by
    intro d p hc
    unfold resolveTopLevelCallAmsterdam at hc
    obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
    cases hc
    exact ⟨rfl, by simp⟩
  have key : ∀ d1, finishTopLevelAmsterdam state msg d1 = .ok p →
      p.1.target = msg.target ∧ (msg.target = none → p.1.codeAddress = msg.codeAddress) ∧
        (msg.target ≠ none → p.1.codeAddress ≠ none) := by
    intro d1 h
    unfold finishTopLevelAmsterdam dispatchTopLevelAmsterdam at h
    generalize (if msg.tenv.stat.auths.isEmpty then d1 else d1.commitStateGas) = d2 at h
    dsimp only at h
    split at h
    · rename_i hnone
      have ht : msg.target = none := Option.isNone_iff_eq_none.mp hnone
      split at h
      · simp only [reduceCtorEq] at h
      · split at h <;> obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h <;> cases h <;>
          exact ⟨rfl, fun _ => rfl, fun hne => absurd ht hne⟩
    · rename_i hsome
      have ht : msg.target ≠ none := fun e => hsome (by simp [e])
      split at h <;> obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h <;>
        exact ⟨(hcall h).1, fun e => absurd e ht, fun _ => (hcall h).2⟩
  unfold prepareTopLevelAmsterdam at h
  dsimp only at h
  split at h <;> obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h <;> exact key _ h

private theorem frameOutput_canonical {f : Frame} {a : Nat} {r : Frame.Result}
    (hw : (f.worldAfter r).Canonical) {p} (hp : f.output a r = .ok p) : State.Canonical p.1 := by
  unfold Frame.output at hp
  obtain ⟨refund, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact hw.1

private theorem frameOutputAmsterdam_canonical {f : Frame} {r : Frame.Result}
    (hw : (f.worldAfter r).Canonical) {p} (hp : f.outputAmsterdam r = .ok p) :
    State.Canonical p.1 := by
  unfold Frame.outputAmsterdam at hp
  obtain ⟨refund, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact hw.1

private theorem runTopOutput_canonical {f : Frame} (hf : f.Canonical)
    {k : Frame.Result → Except EvmError (State × MsgCallOutput)}
    (hk : ∀ r, (f.worldAfter r).Canonical → ∀ p, k r = .ok p → State.Canonical p.1) {p}
    (hp : ((Frame.runTop f).mapError Fault.toEvmError >>= k) = .ok p) :
    State.Canonical p.1 := by
  obtain ⟨r, hr, hp⟩ := Except.bind_eq_ok hp
  cases hrun : Frame.runTop f with
  | error e => rw [hrun] at hr; cases hr
  | ok r' =>
    rw [hrun] at hr
    cases hr
    exact hk r (Frame.runTop_canonical hf hrun) p hp

private theorem processTopLevelAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} (hm : msg.Canonical) (isCreate : Bool) {p}
    (hp : processTopLevelAmsterdam state msg isCreate = .ok p) :
    State.Canonical p.1 := by
  unfold processTopLevelAmsterdam at hp
  have hprepare := prepareTopLevelAmsterdam_canonical (state := state) hm
  cases hprep : prepareTopLevelAmsterdam state msg with
  | error failure =>
    rw [hprep] at hp
    obtain ⟨error, devm⟩ := failure
    cases error <;> simp only [settleTopLevelPreparationFailure] at hp <;> cases hp
    exact hm.1.1
  | ok prepared =>
    rw [hprep] at hp hprepare
    obtain ⟨preparedMsg, preparedDevm⟩ := prepared
    exact runTopOutput_canonical
      (Frame.prepared_canonical hprepare.2 hprepare.1 isCreate)
      (fun _ hw _ hk => frameOutputAmsterdam_canonical hw hk) hp

theorem processMessageCall.create_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : processMessageCall.create msg = .ok p) :
    State.Canonical p.1 := by
  unfold processMessageCall.create at hp
  dsimp only at hp
  split at hp
  · split at hp
    · cases hp; exact h.1.1
    · exact runTopOutput_canonical (Frame.ofTop_canonical h true)
        (fun _ hw _ hk => frameOutput_canonical hw hk) hp
  · exact processTopLevelAmsterdam_canonical h true hp

theorem processMessageCall.call_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : processMessageCall.call msg = .ok p) :
    State.Canonical p.1 := by
  unfold processMessageCall.call at hp
  dsimp only at hp
  split at hp
  · obtain ⟨pair, hpair, hp⟩ := Except.bind_eq_ok hp
    obtain ⟨delegated, refund⟩ := pair
    have hm := processMessageCall.authorize_canonical h hpair
    exact runTopOutput_canonical
      (Frame.ofTop_canonical (Msg.resolveCodeDelegation_canonical hm) false)
      (fun _ hw _ hk => frameOutput_canonical hw hk) hp
  · exact processTopLevelAmsterdam_canonical h false hp

/-- A successful message call leaves a canonical state, for both the create
and the call route. -/
theorem processMessageCall_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : processMessageCall msg = .ok p) : State.Canonical p.1 := by
  unfold processMessageCall at hp
  split at hp
  · exact processMessageCall.create_canonical h hp
  · exact processMessageCall.call_canonical h hp

theorem prepareMessage_canonical {benv : Benv} {tenv : Tenv} {tx : Transaction}
    (hb : benv.Canonical) (ht : tenv.Canonical) {msg : Msg}
    (hm : prepareMessage benv tenv tx = .ok msg) : msg.Canonical := by
  unfold prepareMessage at hm
  cases hm
  exact ⟨hb, ht⟩

theorem State.Canonical.clearAccountPreservingBalance {state : State}
    (h : state.Canonical) (address : Address) :
    (clearAccountPreservingBalance state address).Canonical := by
  unfold Jaune.clearAccountPreservingBalance
  exact State.Canonical.set h address Storage.canonical_empty

theorem State.Canonical.settleSelfdestructs {state : State}
    (h : state.Canonical) (rules : ForkRules) (addresses : List Address) :
    (settleSelfdestructs rules addresses state).Canonical := by
  unfold Jaune.settleSelfdestructs
  split
  · exact State.Canonical.foldl_destroyAccount h
  · induction addresses generalizing state with
    | nil => exact h
    | cons address addresses ih =>
      exact ih (State.Canonical.clearAccountPreservingBalance h address)

/-- The EIP-161 sweep only erases accounts, so it keeps a state canonical. -/
theorem State.Canonical.sweepTouchedAccounts {state : State}
    (h : state.Canonical) (rules : ForkRules) (addresses : List Address) :
    (sweepTouchedAccounts rules addresses state).Canonical := by
  unfold Jaune.sweepTouchedAccounts
  split
  · induction addresses generalizing state with
    | nil => exact h
    | cons address addresses ih =>
      simp only [List.foldl_cons]
      apply ih
      split
      · exact h.destroyAccount address
      · exact h
  · exact h

/-- A successful transaction leaves a canonical state: the fee movements go
through `incrNonce`/`subBal`/`addBal`, the call itself through
`processMessageCall`, and settlement follows the fork's SELFDESTRUCT rule. -/
theorem processTransaction_canonical {benv : Benv} (h : benv.Canonical)
    {bout : BlockOutput} {tx : Transaction} {index : Nat} {p}
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
      (by exact TransientStorage.canonical_empty) hmsg
  have hqc := processMessageCall_canonical hmsgc (Except.mapError_eq_ok_iff.mp hq)
  exact State.Canonical.sweepTouchedAccounts (State.Canonical.settleSelfdestructs
    (State.Canonical.addBal (State.Canonical.addBal hqc _ _) _ _) _ _) _ _

theorem processWithdrawalsState_canonical {st : State} (h : st.Canonical)
    (wds : List Withdrawal) : (processWithdrawalsState st wds).Canonical := by
  unfold processWithdrawalsState
  induction wds generalizing st with
  | nil => exact h
  | cons w l ih => exact ih (State.Canonical.addBal h _ _)

/-- The single boundary all four system transactions share. -/
theorem processSystemTransaction_canonical {benv : Benv} (h : benv.Canonical)
    {target : Address} {code : ByteArray} {data : Bytes} {p}
    (hp : processSystemTransaction benv target code data = .ok p) :
    State.Canonical p.1 := by
  unfold processSystemTransaction at hp
  exact processMessageCall_canonical
    (by exact ⟨⟨h.1, h.1⟩, TransientStorage.canonical_empty⟩) hp

theorem processUncheckedSystemTransaction_canonical {benv : Benv}
    (h : benv.Canonical) {target : Address} {data : Bytes} {p}
    (hp : processUncheckedSystemTransaction benv target data = .ok p) :
    State.Canonical p.1 :=
  processSystemTransaction_canonical h hp

theorem processCheckedSystemTransaction_canonical {benv : Benv}
    (h : benv.Canonical) {target : Address} {data : Bytes} {p}
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
    ∀ (rs : List (UInt8 × Address)) {benv : Benv}, benv.Canonical →
      ∀ {acc : List Bytes} {bal : BlockAccessListBuilder} {p},
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
    ∀ (txis : List (Nat × Transaction)) {benv : Benv}, benv.Canonical →
      ∀ {bout : BlockOutput} {p},
        applyTransactions txis benv bout = .ok p → p.1.Canonical
  | [], _, h, _, _, hp => by cases hp; exact h
  | txi :: txis, benv, h, bout, p, hp => by
    unfold applyTransactions at hp
    obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    exact applyTransactions_canonical txis
      (by exact ⟨processTransaction_canonical h hq, h.2⟩) hp

theorem beaconRootsCall_canonical {rules : ForkRules} {benv : Benv}
    (h : benv.Canonical) {p} (hp : beaconRootsCall rules benv = .ok p) :
    State.Canonical p.1 := by
  unfold beaconRootsCall at hp
  split at hp
  · obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    cases hp
    exact processUncheckedSystemTransaction_canonical h (Except.mapError_eq_ok_iff.mp hq)
  · cases hp; exact h.1

theorem historyStorageCall_canonical {rules : ForkRules} {benv : Benv}
    (h : benv.Canonical) {bal : BlockAccessListBuilder} {p}
    (hp : historyStorageCall rules benv bal = .ok p) : State.Canonical p.1 := by
  unfold historyStorageCall at hp
  split at hp
  · obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
    obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    cases hp
    exact processUncheckedSystemTransaction_canonical h (Except.mapError_eq_ok_iff.mp hq)
  · cases hp; exact h.1

theorem withdrawalsPass_canonical {rules : ForkRules} {benv : Benv}
    (h : benv.state.Canonical) {bout : BlockOutput} (wds : List Withdrawal) :
    (withdrawalsPass rules benv bout wds).1.Canonical := by
  unfold withdrawalsPass
  split
  · exact processWithdrawalsState_canonical h wds
  · exact h

theorem requestsPass_canonical {rules : ForkRules} {benv : Benv}
    (h : benv.Canonical) {bout : BlockOutput} {p}
    (hp : requestsPass rules benv bout = .ok p) : State.Canonical p.1 := by
  unfold requestsPass at hp
  split at hp
  · exact processGeneralPurposeRequests_canonical h hp
  · cases hp; exact h.1

/-- The rewards are balance credits, so they preserve canonicality. -/
theorem payRewards_canonical {st : State} (h : st.Canonical) (pow : ProofOfWorkRules)
    (number : Nat) (coinbase : Address) (ommers : List Header) :
    (payRewards pow number coinbase ommers st).Canonical := by
  unfold payRewards
  dsimp only
  generalize hs : st.addBal coinbase _ = st'
  have h' : st'.Canonical := hs ▸ State.Canonical.addBal h _ _
  clear hs h
  induction ommers generalizing st' with
  | nil => exact h'
  | cons o os ih => exact ih _ (State.Canonical.addBal h' _ _)

/-- A successful block body leaves a canonical state: system transactions,
ordinary transactions, withdrawals, general-purpose requests and the
proof-of-work rewards all preserve the invariant, whether each is run or
gated off. -/
theorem applyBody_canonical {benv : Benv} (h : benv.Canonical)
    {txs : List (Bytes ⊕ Transaction)} {ommers : List Header} {wds : List Withdrawal} {p}
    (hp : applyBody benv txs ommers wds = .ok p) : State.Canonical p.1 := by
  unfold applyBody at hp
  obtain ⟨q1, hq1, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q2, hq2, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨txsD, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q3, hq3, hp⟩ := Except.bind_eq_ok hp
  have hb1 : q1.1.Canonical := beaconRootsCall_canonical h hq1
  have hb2 : q2.1.Canonical :=
    historyStorageCall_canonical (benv := benv.withState q1.1) (by exact ⟨hb1, h.2⟩) hq2
  have hb3 : q3.1.Canonical :=
    applyTransactions_canonical _ (by exact ⟨hb2, h.2⟩) hq3
  obtain ⟨benvTxs, boutTxs⟩ := q3
  dsimp only at hp hb3
  have hw := withdrawalsPass_canonical (rules := benv.stat.rules) (bout := boutTxs) hb3.1 wds
  rcases hwp : withdrawalsPass benv.stat.rules benvTxs boutTxs wds with ⟨stWds, boutWds⟩
  simp only [hwp] at hp hw
  -- The access-list incorporation, the item rule and the built list carry no
  -- state.
  obtain ⟨q4, hq4, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  have hc := requestsPass_canonical
    (benv := benvTxs.withState stWds) ⟨hw, hb3.2⟩ hq4
  dsimp only
  split
  · exact hc
  · exact payRewards_canonical hc _ _ _ _

/-- Canonicality depends on the common execution body, not the resolver or
its error carrier. -/
theorem stateTransitionCoreE_canonical {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch : BlockChain} (h : ch.Canonical) {block : Block} {ch'}
    {checkOmmers : Unit → Except ε Unit}
    (hp : stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    ch'.Canonical := by
  unfold stateTransitionCoreE at hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact applyBody_canonical (by exact ⟨h, h⟩) (Except.mapError_eq_ok_iff.mp hq)

/-- **Raw successful block transition preserves canonicality.** The output
chain's execution state is the body's final state, and its original state is
the input chain's. -/
theorem stateTransitionAt_canonical {f : Fork} {ch : BlockChain}
    (h : ch.Canonical) {block : Block} {ch'}
    (hp : stateTransitionAt f ch block = .ok ch') : ch'.Canonical := by
  rw [stateTransitionAt_eq_ok_iff] at hp
  unfold stateTransitionE stateTransitionCoreE at hp
  simp only [transition_mapError_id, Function.id_comp] at hp
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
  obtain ⟨f, _, hs⟩ := stateTransitionUsing_run hp
  exact stateTransitionCoreE_canonical h (stateTransitionScheduledE_eq_ok_iff.mp hs)

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
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨parent, hpar, h⟩ := Except.bind_eq_ok h
  rw [htip] at hpar
  simp only [Option.toExcept, Except.ok.injEq] at hpar
  subst hpar
  dsimp only at h
  by_cases hph : header.parentHash = tip.header.hash
  · rw [ite_eq_right (by simpa [Header.hash] using hph)] at h
    refine ⟨hph, ?_⟩
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    obtain ⟨bf, hbf, h⟩ := Except.bind_eq_ok h
    by_cases h1 : (header.excessBlobGas.any
        (· != calcExcessBlobGas rules.blob tip.header)) = true
    · rw [ite_eq_left h1] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    rw [ite_eq_right h1] at h
    by_cases h2 : header.gasUsed > header.gasLimit
    · rw [ite_eq_left h2] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    rw [ite_eq_right h2] at h
    by_cases h3 : bf ≠ header.baseFeePerGas
    · rw [ite_eq_left h3] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    rw [ite_eq_right h3] at h
    by_cases h4 : header.timestamp ≤ tip.header.timestamp
    · rw [ite_eq_left h4] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    rw [ite_eq_right h4] at h
    by_cases h5 : header.number ≠ tip.header.number + 1
    · rw [ite_eq_left h5] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    · simpa using h5
  · exfalso
    rw [ite_eq_left (by simpa [Header.hash] using hph)] at h
    by_cases hz : header.parentHash = 0
    · rw [ite_eq_left hz] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    · rw [ite_eq_right hz] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)

/-- A successful first fee-bearing header passed the complete gas-limit
check against the elastic limit of its actual retained parent. -/
theorem validateHeader_firstFee_gasLimit {rules : ForkRules} {chain : BlockChain}
    {header : Header} {parent : Block}
    (htip : chain.blocks.getLast? = some parent)
    (h : validateHeader rules chain header = .ok ())
    (hb : header.baseFeePerGas.isSome = true) (hp : parent.header.baseFeePerGas = none) :
    checkGasLimit header.gasLimit (elasticityMultiplier * parent.header.gasLimit) = .ok () := by
  have hph := (validateHeader_links htip h).1
  unfold validateHeader at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨p, hpar, h⟩ := Except.bind_eq_ok h
  rw [htip] at hpar
  simp only [Option.toExcept, Except.ok.injEq] at hpar
  subst hpar
  dsimp only at h
  rw [ite_eq_right (by simpa only [Header.hash, not_not] using hph)] at h
  obtain ⟨u, hgas, _⟩ := Except.bind_eq_ok h
  cases u
  have hg := Except.mapError_eq_ok_iff.mp hgas
  simpa only [checkFirstFeeGasLimit, hb, hp, Option.isNone_none, Bool.and_self,
    ↓reduceIte] using hg

/-- The block checks establish the computed post-state root against the child
header's own -- which is exactly the tip/root agreement the resulting snapshot
needs, already paid for. -/
theorem stateTransitionChecks_stateRoot {bout : BlockOutput} {header : Header}
    {transactionsRoot blockStateRoot receiptRoot : U256} {blockLogsBloom : Bytes}
    {withdrawalsRoot : U256} {requestsHash : Option U256}
    (h : stateTransitionChecks bout header transactionsRoot blockStateRoot
      receiptRoot blockLogsBloom withdrawalsRoot requestsHash = .ok ()) :
    blockStateRoot = header.stateRoot := by
  unfold stateTransitionChecks at h
  dsimp only at h
  by_cases h1 : max bout.blockGasUsed bout.blockStateGasUsed ≠ header.gasUsed
  · rw [ite_eq_left h1] at h
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
    exact absurd hb (by simp)
  rw [ite_eq_right h1] at h
  by_cases h2 : transactionsRoot ≠ header.transactionsRoot
  · rw [ite_eq_left h2] at h
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
    exact absurd hb (by simp)
  rw [ite_eq_right h2] at h
  by_cases h3 : blockStateRoot ≠ header.stateRoot
  · rw [ite_eq_left h3] at h
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
    exact absurd hb (by simp)
  · simpa using h3

/-- Success inversion shared by static and scheduled transitions. -/
theorem stateTransitionCoreE_eq_ok {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (h : stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    validateHeader f.ruleSet ch block.header = .ok () ∧
      ch'.blocks = appendBlock ch.blocks block ∧
      ch'.state.root = block.header.stateRoot := by
  unfold stateTransitionCoreE at h
  obtain ⟨u1, hvh, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨q, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨u3, hchk, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases u1
  cases u3
  cases h
  exact ⟨Except.mapError_eq_ok_iff.mp hvh, rfl,
    stateTransitionChecks_stateRoot (Except.mapError_eq_ok_iff.mp hchk)⟩

/-- The checked output witness is derived from checks already performed by
the common algorithm, with no second root computation. -/
theorem BlockChain.validContext_of_scheduled {cfg : ChainConfig} {f : Fork}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionScheduledE cfg f cc.val cb.block = .ok (.ok ch')) :
    ch'.blocks.getLast? = some cb.block ∧ ch'.RetainedHistoryValid ∧
      ch'.state.Canonical ∧ ch'.state.root = cb.block.header.stateRoot := by
  have hc := stateTransitionScheduledE_eq_ok_iff.mp h
  obtain ⟨hvh, hblocks, hroot⟩ := stateTransitionCoreE_eq_ok hc
  obtain ⟨hph, hnum⟩ := validateHeader_links cc.tip_is_last hvh
  refine ⟨?_, ?_, stateTransitionCoreE_canonical cc.canonicalState hc, hroot⟩
  · rw [hblocks]; exact appendBlock_getLast? _ _
  · exact BlockChain.retainedHistoryValid_appendBlock cc.retainedHistory
      cc.tip_is_last ⟨hnum, hph⟩ cb.rlpCanonical.1 hblocks

/-- Inversion of a successful raw transition: header validation passed, the
result's blocks are the parent's with this block appended, and its state is
the one the child header commits to. -/
theorem stateTransitionAt_eq_ok {f : Fork} {ch ch' : BlockChain}
    {block : Block} (h : stateTransitionAt f ch block = .ok ch') :
    validateHeader f.ruleSet ch block.header = .ok () ∧
      ch'.blocks = appendBlock ch.blocks block ∧
      ch'.state.root = block.header.stateRoot := by
  rw [stateTransitionAt_eq_ok_iff] at h
  unfold stateTransitionE stateTransitionCoreE at h
  simp only [transition_mapError_id, Function.id_comp] at h
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
  let f ← pc.config.forkAt cb.block.header.number cb.block.header.timestamp
  stateTransitionScheduledE pc.config f pc.chain.val cb.block

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
  cases hr : pc.config.forkAt cb.block.header.number cb.block.header.timestamp <;> simp

theorem ConfiguredChain.validContext_of_transition {pc : ConfiguredChain}
    {cb : CanonicalBlock} {r : Except TransitionError BlockChain} {ch' : BlockChain}
    (h : stateTransitionConfigured pc cb = .ok r) (hr : r = .ok ch') :
    ch'.blocks.getLast? = some cb.block ∧ ch'.RetainedHistoryValid ∧
      ch'.state.Canonical ∧ ch'.state.root = cb.block.header.stateRoot := by
  obtain ⟨f, _, hst⟩ := Except.bind_eq_ok h
  rw [hr] at hst
  exact BlockChain.validContext_of_scheduled (cc := pc.chain) hst

/-- The checked output of a successful configured checked transition. -/
def CheckedBlockChain.ofConfiguredTransition {pc : ConfiguredChain}
    {cb : CanonicalBlock} {r : Except TransitionError BlockChain} {ch' : BlockChain}
    (h : stateTransitionConfigured pc cb = .ok r) (hr : r = .ok ch') :
    CheckedBlockChain :=
  CheckedBlockChain.ofEvidence ch' cb.block
    (ConfiguredChain.validContext_of_transition h hr).1
    (ConfiguredChain.validContext_of_transition h hr).2.1
    (ConfiguredChain.validContext_of_transition h hr).2.2.1
    (ConfiguredChain.validContext_of_transition h hr).2.2.2

/-- Checked configured import with its already-selected containing fork.
The caller retains the schedule for individual ommer validation. -/
def addBlockToChainScheduledChecked (cfg : ChainConfig) (f : Fork)
    (cc : CheckedBlockChain) (cb : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) :=
  addBlockToChainScheduledCanonicalE cfg f cc.val cb

/-- Build the scheduled import's output witness from its successful checks. -/
def CheckedBlockChain.ofScheduledImport {cfg : ChainConfig} {f : Fork}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : addBlockToChainScheduledChecked cfg f cc cb = .ok (.inl ch')) :
    CheckedBlockChain :=
  CheckedBlockChain.ofEvidence ch' cb.block
    (BlockChain.validContext_of_scheduled
      (addBlockToChainScheduledCanonicalE_eq_ok_inl h).2).1
    (BlockChain.validContext_of_scheduled
      (addBlockToChainScheduledCanonicalE_eq_ok_inl h).2).2.1
    (BlockChain.validContext_of_scheduled
      (addBlockToChainScheduledCanonicalE_eq_ok_inl h).2).2.2.1
    (BlockChain.validContext_of_scheduled
      (addBlockToChainScheduledCanonicalE_eq_ok_inl h).2).2.2.2

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
    {blockRlp : Bytes} {block : Block} {hash : U256}
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

namespace ChainConfig

/-- The proof-of-work mint of one block under rules `pow`: what `payRewards` credits. -/
def rewardTotal (pow : ProofOfWorkRules) (number : Nat) (ommers : List Header) : Nat :=
  (pow.blockReward + ommers.length * (pow.blockReward / 32)) +
    (ommers.map fun o => (8 + o.number - number) * pow.blockReward / 8).sum

/-- The mint the configured schedule's fork pays for `block` (0 from Paris on). -/
def rewardAt (cfg : ChainConfig) (block : Block) : Nat :=
  match cfg.forkAt block.header.number block.header.timestamp with
  | .ok f => match f.ruleSet.proofOfWork with
    | some pow => rewardTotal pow block.header.number block.ommers
    | none => 0
  | .error _ => 0

theorem rewardAt_eq_zero {cfg : ChainConfig} {block : Block} {f : Fork}
    (h : cfg.forkAt block.header.number block.header.timestamp = .ok f)
    (hpos : f.ruleSet.proofOfWork = none) : cfg.rewardAt block = 0 := by
  simp only [rewardAt, h, hpos]

theorem single_prague_rewardAt (chainId : UInt64) (block : Block) :
    (single chainId .prague).rewardAt block = 0 := rfl

end ChainConfig

private theorem checkHeaderFieldPresence_eq {name : String} {present defined : Bool}
    (h : checkHeaderFieldPresence name present defined = .ok ()) : present = defined := by
  unfold checkHeaderFieldPresence at h
  split at h
  · cases h
  · rename_i heq
    exact not_not.mp heq

theorem checkHeaderShape_baseFee {rules : ForkRules} {header : Header}
    (h : checkHeaderShape rules header = .ok ()) :
    header.baseFeePerGas.isSome = rules.header.baseFee := by
  unfold checkHeaderShape at h
  obtain ⟨u, hb, _⟩ := Except.bind_eq_ok h
  cases u
  exact checkHeaderFieldPresence_eq hb

theorem checkHeaderShape_blobGas {rules : ForkRules} {header : Header}
    (h : checkHeaderShape rules header = .ok ()) :
    header.excessBlobGas.isSome = rules.header.blobGas ∧
      header.blobGasUsed.isSome = rules.header.blobGas := by
  unfold checkHeaderShape at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨u, hu, h⟩ := Except.bind_eq_ok h
  obtain ⟨v, hv, _⟩ := Except.bind_eq_ok h
  cases u
  cases v
  exact ⟨checkHeaderFieldPresence_eq hv, checkHeaderFieldPresence_eq hu⟩

/-- The first London block carries the initial fee when its parent carries no fee. -/
theorem expectedBaseFee_first {header parent : Header}
    (hb : header.baseFeePerGas.isSome = true) (hp : parent.baseFeePerGas = none) :
    expectedBaseFee header parent = .ok (some initialBaseFee) := by
  cases hh : header.baseFeePerGas with
  | none => simp only [hh, Option.isSome_none, Bool.false_eq_true] at hb
  | some fee => simp only [expectedBaseFee, hh, hp]

theorem parent_baseFee_none_iff {rules₀ : ForkRules} {parent : Header}
    (hp : checkHeaderShape rules₀ parent = .ok ()) :
    parent.baseFeePerGas = none ↔ rules₀.header.baseFee = false := by
  have hshape := checkHeaderShape_baseFee hp
  rw [← hshape]
  cases parent.baseFeePerGas <;> simp only [Option.isSome_none, Option.isSome_some,
    reduceCtorEq]

/-- Every configured step of a single-fork schedule is that fork's fixed-fork step. -/
theorem stateTransitionUsing_single {chainId : UInt64} {f : Fork} {ch : BlockChain}
    {block : Block} (hid : chainId = ch.chainId) :
    stateTransitionUsing (ChainConfig.single chainId f) ch block =
      stateTransitionAt f ch block := by
  rw [stateTransitionUsing_eq_of_chainId_eq hid, ChainConfig.single_forkAt]
  simp only [Except.mapError, Except.bind, stateTransitionScheduledE_single,
    stateTransitionAt]

/-- A successful step leaves the new block as the chain's last block. -/
theorem stateTransitionE_getLast {f : Fork} {ch ch' : BlockChain} {block : Block}
    (h : stateTransitionE f ch block = .ok ch') :
    ch'.blocks.getLast? = some block := by
  have hb := (stateTransitionAt_eq_ok (stateTransitionAt_eq_ok_iff.mpr h)).2.1
  rw [hb, appendBlock_getLast?]

/-- Header-shape coherence of the chain head with its scheduled fork. -/
def ChainConfig.ShapeCoherent (cfg : ChainConfig) (ch : BlockChain) : Prop :=
  ∀ b, ch.blocks.getLast? = some b →
    ∃ f, cfg.forkAt b.header.number b.header.timestamp = .ok f ∧
      checkHeaderShape f.ruleSet b.header = .ok ()

theorem stateTransitionUsing_shapeCoherent {cfg : ChainConfig} {ch ch' : BlockChain}
    {block : Block} (h : stateTransitionUsing cfg ch block = .ok ch') :
    cfg.ShapeCoherent ch' := by
  obtain ⟨f, hf, hrun⟩ := stateTransitionUsing_run h
  intro b hb
  have hc := stateTransitionScheduledE_eq_ok_iff.mp hrun
  have hblocks := (stateTransitionCoreE_eq_ok hc).2.1
  rw [hblocks, appendBlock_getLast?] at hb
  cases hb
  refine ⟨f, hf, ?_⟩
  have hv := stateTransitionCoreE_header hc
  unfold validateHeader at hv
  obtain ⟨u, hshape, _⟩ := Except.bind_eq_ok hv
  cases u
  exact hshape

/-- Successful header validation advances number and timestamp independently
of how the caller selected the rules. -/
theorem validateHeader_succ {rules : ForkRules} {ch : BlockChain} {header : Header}
    (h : validateHeader rules ch header = .ok ()) :
    ∃ parent, ch.blocks.getLast? = some parent ∧
      header.number = parent.header.number + 1 ∧
      parent.header.timestamp < header.timestamp := by
  have hv := h
  have hv0 := hv
  unfold validateHeader at hv
  obtain ⟨_, _, hv⟩ := Except.bind_eq_ok hv
  obtain ⟨parent, hpar, hv⟩ := Except.bind_eq_ok hv
  have hlast : ch.blocks.getLast? = some parent := by
    cases hh : ch.blocks.getLast? with
    | none => simp only [hh, Option.toExcept, reduceCtorEq] at hpar
    | some p =>
      simpa only [hh, Option.toExcept, Except.ok.injEq, Option.some.injEq] using hpar
  obtain ⟨hph, hnum⟩ := validateHeader_links hlast hv0
  refine ⟨parent, hlast, hnum, ?_⟩
  dsimp only at hv
  rw [ite_eq_right (by simpa only [Header.hash, not_not] using hph)] at hv
  obtain ⟨_, _, hv⟩ := Except.bind_eq_ok hv
  obtain ⟨bf, _, hv⟩ := Except.bind_eq_ok hv
  by_cases h1 : (header.excessBlobGas.any
      (· != calcExcessBlobGas rules.blob parent.header)) = true
  · rw [ite_eq_left h1] at hv
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok hv
    cases hb
  rw [ite_eq_right h1] at hv
  by_cases h2 : header.gasUsed > header.gasLimit
  · rw [ite_eq_left h2] at hv
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok hv
    cases hb
  rw [ite_eq_right h2] at hv
  by_cases h3 : bf ≠ header.baseFeePerGas
  · rw [ite_eq_left h3] at hv
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok hv
    cases hb
  rw [ite_eq_right h3] at hv
  by_cases h4 : header.timestamp ≤ parent.header.timestamp
  · rw [ite_eq_left h4] at hv
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok hv
    cases hb
  · omega

/-- A successful block step extends the chain by one block number and a later timestamp. -/
theorem stateTransitionE_header_succ {f : Fork} {ch ch' : BlockChain} {block : Block}
    (h : stateTransitionE f ch block = .ok ch') :
    ∃ parent, ch.blocks.getLast? = some parent ∧
      block.header.number = parent.header.number + 1 ∧
      parent.header.timestamp < block.header.timestamp := by
  exact validateHeader_succ (stateTransitionCoreE_header h)

/-- The configured fork is no earlier than the parent's scheduled fork. -/
theorem stateTransitionUsing_fork_mono {cfg : ChainConfig} {ch ch' : BlockChain}
    {block parent : Block} {f₀ : Fork}
    (hlast : ch.blocks.getLast? = some parent)
    (h₀ : cfg.forkAt parent.header.number parent.header.timestamp = .ok f₀)
    (h : stateTransitionUsing cfg ch block = .ok ch') :
    ∃ f, cfg.forkAt block.header.number block.header.timestamp = .ok f ∧
      f₀.index ≤ f.index ∧
      stateTransitionScheduledE cfg f ch block = .ok (.ok ch') := by
  obtain ⟨f, hf, hrun⟩ := stateTransitionUsing_run h
  obtain ⟨tip, htip, hnum, htime⟩ := validateHeader_succ
    (stateTransitionCoreE_header (stateTransitionScheduledE_eq_ok_iff.mp hrun))
  rw [hlast] at htip
  cases htip
  exact ⟨f, hf, ChainConfig.forkAt_index_mono (by omega) (by omega) h₀ hf, hrun⟩

/-- On a selected proof-of-stake fork, the original static-success conclusion
is valid for any schedule; no uniformity premise is added to the frozen theorem. -/
theorem stateTransitionUsing_fork_mono_static_of_pow_none
    {cfg : ChainConfig} {ch ch' : BlockChain} {block parent : Block} {f₀ : Fork}
    (hlast : ch.blocks.getLast? = some parent)
    (h₀ : cfg.forkAt parent.header.number parent.header.timestamp = .ok f₀)
    (h : stateTransitionUsing cfg ch block = .ok ch') :
    ∃ f, cfg.forkAt block.header.number block.header.timestamp = .ok f ∧
      f₀.index ≤ f.index ∧
      (f.ruleSet.proofOfWork = none → stateTransitionE f ch block = .ok ch') := by
  obtain ⟨f, hf, hm, hs⟩ := stateTransitionUsing_fork_mono hlast h₀ h
  refine ⟨f, hf, hm, ?_⟩
  intro hp
  rw [stateTransitionScheduledE_of_pow_none cfg f ch block hp] at hs
  exact Except.ok.inj hs

/-- Schedule shape coherence identifies the fee activation by rule flags,
including schedules which skip forks. The actual parent and successful shared
validation supply the elastic gas-limit bound, with no hardcoded height. -/
theorem stateTransitionScheduledE_firstFee_gasLimit
    {cfg : ChainConfig} {f f₀ : Fork} {ch ch' : BlockChain} {block parent : Block}
    (hshape : cfg.ShapeCoherent ch) (hlast : ch.blocks.getLast? = some parent)
    (h₀ : cfg.forkAt parent.header.number parent.header.timestamp = .ok f₀)
    (hfee₀ : f₀.ruleSet.header.baseFee = false) (hfee : f.ruleSet.header.baseFee = true)
    (h : stateTransitionScheduledE cfg f ch block = .ok (.ok ch')) :
    checkGasLimit block.header.gasLimit
      (elasticityMultiplier * parent.header.gasLimit) = .ok () := by
  obtain ⟨fp, hfp, hp⟩ := hshape parent hlast
  rw [h₀] at hfp
  cases hfp
  have hv := stateTransitionCoreE_header (stateTransitionScheduledE_eq_ok_iff.mp h)
  have hc : checkHeaderShape f.ruleSet block.header = .ok () := by
    unfold validateHeader at hv
    obtain ⟨u, hu, _⟩ := Except.bind_eq_ok hv
    cases u
    exact hu
  exact validateHeader_firstFee_gasLimit hlast hv
    ((checkHeaderShape_baseFee hc).trans hfee)
    ((parent_baseFee_none_iff hp).mpr hfee₀)

end Jaune
