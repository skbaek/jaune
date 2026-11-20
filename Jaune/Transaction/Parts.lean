import Mathlib.Data.List.Chain
import Jaune.GasFacts
import Jaune.MessageCall.Records

/-! # Shared transaction and block processing -/

namespace Jaune

open Jaune

--------- TYPED SEMANTIC REASONS: TRANSACTION, BLOCK, IMPORT ---------

-- Declarations and renderers only (golden guards: `Jaune/Check/Transaction.lean`);
-- no producer moves here, no rendered message changes; Step 10 moves them.
--
-- The transaction and block entry points in `Jaune.Transaction` use these
-- shared failure types. Their original placement is recorded in
-- `scripts/report-integrity-design.md` section 6. The tag constants live in
-- `Jaune/Machine.lean`. The golden guards in `Jaune/Check/Transaction.lean`
-- pin the tags to their constructors.

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
inductive TransactionValidationError : Type
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
  /-- A typed transaction whose type byte is not supported (decision 16). -/
  | typeNotSupported (txType : Nat) (detail : ErrorDetail)
deriving DecidableEq, Repr

/-- The tag a transaction-rejection reason renders under. -/
def TransactionValidationError.tag : TransactionValidationError → String
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
  | .typeNotSupported _ _ => typeNotSupportedTag

/-- The diagnostic payload of a transaction-rejection reason. -/
def TransactionValidationError.detail : TransactionValidationError → ErrorDetail
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
  | .emptyAuthorizationList d | .typePreFork _ d | .typeNotSupported _ d => d

/-- The one renderer for `TransactionValidationError`. -/
def TransactionValidationError.render (e : TransactionValidationError) : String :=
  renderTagged e.tag e.detail

/-- Every transaction-rejection reason, for the completeness guards. -/
def TransactionValidationError.all : List TransactionValidationError :=
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
    .emptyAuthorizationList .none, .typePreFork 3 .none,
    .typeNotSupported 5 .none ]

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
  | transaction (reason : TransactionValidationError)
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
  | transaction (reason : TransactionValidationError)
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

structure BlockAccessListIndexStartAccount : Type where
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
def upsert {α : Type} (l : List (Nat × α)) (idx : Nat) (v : α) : List (Nat × α) :=
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

def startAccount (b : BlockAccessListBuilder) (idx : Nat) (address : Address) (account : Account) :
    BlockAccessListBuilder × BlockAccessListIndexStartAccount :=
  let atIndex := b.indexStartAccounts.getD idx .empty
  match atIndex.get? address with
  | some start => (b, start)
  | none =>
    let start : BlockAccessListIndexStartAccount :=
      {balance := account.balance, nonce := account.nonce, code := account.code}
    ({b with indexStartAccounts := b.indexStartAccounts.insert idx (atIndex.insert address start)}, start)

def startStorage (b : BlockAccessListBuilder) (idx : Nat) (address : Address) (slot value : U256) :
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

def checkTransactionDynamicGasFee
    (baseFeePerGas gas maxPriorityFee maxFee : Nat) :
    Except TransactionValidationError (Nat × Nat) :=
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
    Except TransactionValidationError (Nat × Nat) :=
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

/-- Enforce the fork's per-transaction blob-count limit, when one is active. -/
def checkTransactionBlobCount (limits : TransactionLimits)
    (blobHashes : List U256) : Except TransactionValidationError Unit :=
  match limits.maxBlobCount with
  | none => .ok ()
  | some maxBlobCount =>
    if blobHashes.length > maxBlobCount then
      .error <| .type3BlobCountLimitExceeded <| .text
        s!"transaction has \
           {blobHashes.length} blobs > maximum = {maxBlobCount}"
    else
      .ok ()

def checkTransactionReceiver (tx : Transaction) : Except TransactionValidationError Unit :=
  if tx.isEip4844 then
    if tx.type.to?.isNone then
      .error <| .type3ContractCreation <|
        .text "type-3 transactions cannot create contracts"
    else
      .ok ()
  else
    .ok ()

def checkTransactionAuthorizationList (tx : Transaction) : Except TransactionValidationError Unit :=
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

def checkTransactionSenderCode (senderAccount : Account) :
    Except TransactionValidationError Unit :=
  if ¬ (senderAccount.code.isEmpty ∨ isValidDelegation senderAccount.code) then
    .error <| .senderNotEoa <| .text "sender has non-delegation code"
  else
    .ok ()

def checkTransactionSenderAccount
    (senderAccount : Account) (tx : Transaction) (maxGasFee : Nat) :
    Except TransactionValidationError Unit :=
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
    Except TransactionValidationError Unit :=
  if rules.delegationEnabled then checkTransactionSenderCode senderAccount
  else if senderAccount.code.isEmpty then .ok ()
  else .error <| .senderNotEoa <| .text "sender has non-delegation code"

/-- Keep nonce, funds and existing code failures ahead of historical code admission. -/
def checkTransactionSenderAccountFor (rules : ForkRules)
    (senderAccount : Account) (tx : Transaction) (maxGasFee : Nat) :
    Except TransactionValidationError Unit := do
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
    (senderAccount : Account) (tx : Transaction) (maxGasFee : Nat) (error : TransactionValidationError)
    (h : checkTransactionSenderAccount senderAccount tx maxGasFee = .error error) :
    checkTransactionSenderAccountFor rules senderAccount tx maxGasFee = .error error := by
  simp only [checkTransactionSenderAccountFor, h, Bind.bind, Except.bind]

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
    (dataLength : Nat) : Except TransactionValidationError Unit :=
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
    (dataLength : Nat) : Except TransactionValidationError Unit :=
  if rules.creation.initCodeLimit then
    checkInitcodeSize rules.code receiver dataLength
  else
    .ok ()

/-- Prague enforces the initcode bound: its creation limit is on. -/
@[simp] theorem pragueRules_creation_initCodeLimit :
    pragueRules.creation.initCodeLimit = true := rfl

def checkTransactionGasLimit (limit : Option Nat) (gas : Nat) :
    Except TransactionValidationError Unit :=
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
    Except TransactionValidationError Unit :=
  checkTransactionGasLimit limits.maxGas gas

/-- Enforce Amsterdam's separate EIP-8037 total transaction gas cap. -/
def checkTransactionTotalGasCap (limits : TransactionLimits) (gas : Nat) :
    Except TransactionValidationError Unit :=
  checkTransactionGasLimit limits.maxTotalGas gas

def checkTransactionPriorityFeeRelation (tx : Transaction) :
    Except TransactionValidationError Unit :=
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

def checkTransactionBlobShape (rules : ForkRules) (tx : Transaction) :
    Except TransactionValidationError Unit := do
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
    Except TransactionValidationError (Nat × Nat) := do
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

def calculateDataFee (blob : BlobSchedule) (excess_blob_gas: Nat) (tx: Transaction) :
    Nat :=
  getTotalBlobGas tx * getBaseFeePerBlobGas blob excess_blob_gas

def transactionHash (tx : Transaction) : U256 := tx.toRlpItem.toBytes.keccak

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
    -- Decision 16 (W2-T): an unknown envelope type byte (anything outside
    -- `0x01`-`0x04`, including `0x00`, `0x05`-`0x7F` and `0x80`-`0xFF`) is a
    -- block rejection (`typeNotSupported`), matching EELS `TransactionTypeError`
    -- and geth `ErrTxTypeNotSupported`.
    | x, _ =>
      .error <| .transaction <| .typeNotSupported x.toNat <|
        .text s!"type-{x} transactions do not exist (EIP-2718), the block is invalid"

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

/-- Decision 16: any typed-envelope slot whose first byte is not `0x01`-`0x04`
is rejected with `TransactionValidationError.typeNotSupported`. -/
theorem Bytes.toExceptTransaction_unknown_typeNotSupported {x : UInt8} (xs : Bytes)
    (hx : x ≠ 0x01 ∧ x ≠ 0x02 ∧ x ≠ 0x03 ∧ x ≠ 0x04) :
    Bytes.toExceptTransaction (x :: xs) =
      .error (.transaction (.typeNotSupported x.toNat
        (.text s!"type-{x} transactions do not exist (EIP-2718), the block is invalid"))) := by
  unfold Bytes.toExceptTransaction
  dsimp only
  split <;> first | rfl | (exfalso; simp_all)

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

/-- Decision 16 lifted to `decodeTransaction`: any byte-string slot with an unknown
first byte fails with `typeNotSupported`, independent of fork rules. -/
theorem decodeTransaction_unknown_typeNotSupported (rules : ForkRules) {x : UInt8} (xs : Bytes)
    (hx : x ≠ 0x01 ∧ x ≠ 0x02 ∧ x ≠ 0x03 ∧ x ≠ 0x04) :
    decodeTransaction rules (.inl (x :: xs)) =
      .error (.transaction (.typeNotSupported x.toNat
        (.text s!"type-{x} transactions do not exist (EIP-2718), the block is invalid"))) := by
  simp only [decodeTransaction, Bytes.toExceptTransaction_unknown_typeNotSupported xs hx,
    bind, Except.bind]

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

def BlockChain.recentBlockHashes (chain : BlockChain) : List U256 :=
  match chain.blocks.reverse.take 255 with
  | [] => []
  | block :: blocks =>
    let hash : U256 := (Header.toRlpItem block.header).toBytes.keccak
    let hashes : List U256 :=
      (block :: blocks).map <| fun x => x.header.parentHash
    (hash :: hashes).reverse

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

def appendBlock (blks : List Block) (blk : Block) : List Block :=
  (blk :: blks.reverse.take 254).reverse

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

theorem processWithdrawalsState_canonical {st : State} (h : st.Canonical)
    (wds : List Withdrawal) : (processWithdrawalsState st wds).Canonical := by
  unfold processWithdrawalsState
  induction wds generalizing st with
  | nil => exact h
  | cons w l ih => exact ih (State.Canonical.addBal h _ _)

end Jaune
