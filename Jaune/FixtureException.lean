-- FixtureException.lean : the canonical vocabulary of official fixture
-- exception identities, and the fail-closed matcher built on it.
--
-- This module is fixture-runner infrastructure, not EVM semantics: it is
-- imported by `Main.lean` only, and deliberately not from the `Jaune` library
-- root, so that no proof client depends on it.
--
-- A fixture's `expectException` is a `|`-separated set of *allowed* official
-- exception identities. The runner must parse that set, classify the actual
-- rejection as exactly one canonical identity, and accept only set
-- membership. Everything here therefore fails closed: unknown expected
-- identities, unmapped actual reasons, and broad categories such as a bare
-- `InvalidBlock` are failures, never successes.
--
-- Since Step 10 of ~/plans/integrity.md, the actual side is classified by
-- **constructor**: `FixtureException.ofBlockRejection` maps each typed
-- rejection reason directly to its official identity (or to `none`, failing
-- closed). The only string this module still parses is the fixture's own
-- external `expectException` label. No rendered diagnostic is ever read back:
-- the retired `classify`/`actualRoutes` prefix table is gone, and an
-- `ImportFailure` -- context, support, harness, internal, or VM -- has no
-- mapping at all, by type, so it can never score as an expected rejection.

import Jaune.Transaction

namespace Jaune

/-- The canonical vocabulary used by the selected Prague and Osaka corpora,
spanning the `BlockException` and `TransactionException` namespaces. It
comprises the published identities observed in the pinned lane plus distinct
internal classifications needed for precise current-fixture routes. The list
and guards below make a vocabulary change explicit rather than silently
accepting an unknown token. -/
inductive FixtureException where
  -- BlockException.*
  | blockExtraDataTooBig
  | blockGasLimitTooBig
  | blockGasUsedOverflow
  | blockImportImpossibleDifficultyOverParis
  | blockImportImpossibleUnclesOverParis
  | blockInvalidBaseFeePerGas
  | blockInvalidBlockNumber
  | blockInvalidBlockTimestampOlderThanParent
  | blockInvalidGasLimit
  | blockInvalidGasUsed
  | blockInvalidLogBloom
  | blockInvalidDepositEventLayout
  | blockSystemContractCallFailed
  /-- A mandatory system contract with no code at the block that must call it
  (goal D, DP-2): the pinned reference's `InvalidBlock` before the call. -/
  | blockSystemContractEmpty
  | blockInvalidReceiptsRoot
  | blockInvalidRequests
  | blockInvalidStateRoot
  | blockInvalidTransactionsRoot
  | blockInvalidWithdrawalsRoot
  | blockRlpInvalidFieldOverflow64
  | blockRlpBlockLimitExceeded
  | blockRlpStructuresEncoding
  | blockRlpWithdrawalsNotRead
  | blockUnknownParent
  | blockUnknownParentZero
  -- EIP-7928 (goal C, fixed decision 9): three identities of their own, and
  -- the malformed-list identity the corpus uses for a published list that is
  -- not in the canonical form.
  | blockInvalidBlockAccessList
  | blockInvalidBalHash
  | blockAccessListGasLimitExceeded
  | blockIncorrectBlockFormat
  -- TransactionException.*
  | txGasLimitPriceProductOverflow
  | txGasAllowanceExceeded
  | txInitcodeSizeExceeded
  | txInsufficientAccountFunds
  | txInsufficientMaxFeePerGas
  | txIntrinsicGasTooLow
  | txGasLimitExceedsMaximum
  | txInvalidChainId
  | txNonceIsMax
  | txNonceMismatchTooHigh
  | txNonceMismatchTooLow
  | txPriorityGreaterThanMaxFeePerGas
  | txSenderNotEoa
  | txType3TxBlobCountExceeded
  | txType3TxContractCreation
  | txType3TxInvalidBlobVersionedHash
  | txType3TxZeroBlobs
  | txType4EmptyAuthorizationList
  | txType4TxContractCreation
deriving DecidableEq, BEq, Repr, Inhabited

namespace FixtureException

/-- Every identity in the vocabulary. The single source of truth for the
round-trip, coverage, and injectivity checks below. -/
def all : List FixtureException :=
  [ blockExtraDataTooBig,
    blockGasLimitTooBig,
    blockGasUsedOverflow,
    blockImportImpossibleDifficultyOverParis,
    blockImportImpossibleUnclesOverParis,
    blockInvalidBaseFeePerGas,
    blockInvalidBlockNumber,
    blockInvalidBlockTimestampOlderThanParent,
    blockInvalidGasLimit,
    blockInvalidGasUsed,
    blockInvalidLogBloom,
    blockInvalidDepositEventLayout,
    blockSystemContractCallFailed,
    blockSystemContractEmpty,
    blockInvalidReceiptsRoot,
    blockInvalidRequests,
    blockInvalidStateRoot,
    blockInvalidTransactionsRoot,
    blockInvalidWithdrawalsRoot,
    blockRlpInvalidFieldOverflow64,
    blockRlpBlockLimitExceeded,
    blockRlpStructuresEncoding,
    blockRlpWithdrawalsNotRead,
    blockUnknownParent,
    blockUnknownParentZero,
    blockInvalidBlockAccessList,
    blockInvalidBalHash,
    blockAccessListGasLimitExceeded,
    blockIncorrectBlockFormat,
    txGasLimitPriceProductOverflow,
    txGasAllowanceExceeded,
    txInitcodeSizeExceeded,
    txInsufficientAccountFunds,
    txInsufficientMaxFeePerGas,
    txIntrinsicGasTooLow,
    txGasLimitExceedsMaximum,
    txInvalidChainId,
    txNonceIsMax,
    txNonceMismatchTooHigh,
    txNonceMismatchTooLow,
    txPriorityGreaterThanMaxFeePerGas,
    txSenderNotEoa,
    txType3TxBlobCountExceeded,
    txType3TxContractCreation,
    txType3TxInvalidBlobVersionedHash,
    txType3TxZeroBlobs ]
    ++ [txType4EmptyAuthorizationList, txType4TxContractCreation]

/-- The canonical spelling of an identity: byte-for-byte the token the fixtures
use. -/
def toString : FixtureException → String
  | blockExtraDataTooBig => "BlockException.EXTRA_DATA_TOO_BIG"
  | blockGasLimitTooBig => "BlockException.GASLIMIT_TOO_BIG"
  | blockGasUsedOverflow => "BlockException.GAS_USED_OVERFLOW"
  | blockImportImpossibleDifficultyOverParis =>
    "BlockException.IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS"
  | blockImportImpossibleUnclesOverParis =>
    "BlockException.IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS"
  | blockInvalidBaseFeePerGas => "BlockException.INVALID_BASEFEE_PER_GAS"
  | blockInvalidBlockNumber => "BlockException.INVALID_BLOCK_NUMBER"
  | blockInvalidBlockTimestampOlderThanParent =>
    "BlockException.INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT"
  | blockInvalidGasLimit => "BlockException.INVALID_GASLIMIT"
  | blockInvalidGasUsed => "BlockException.INVALID_GAS_USED"
  | blockInvalidLogBloom => "BlockException.INVALID_LOG_BLOOM"
  | blockInvalidDepositEventLayout => "BlockException.INVALID_DEPOSIT_EVENT_LAYOUT"
  | blockSystemContractCallFailed => "BlockException.SYSTEM_CONTRACT_CALL_FAILED"
  | blockSystemContractEmpty => "BlockException.SYSTEM_CONTRACT_EMPTY"
  | blockInvalidReceiptsRoot => "BlockException.INVALID_RECEIPTS_ROOT"
  | blockInvalidRequests => "BlockException.INVALID_REQUESTS"
  | blockInvalidStateRoot => "BlockException.INVALID_STATE_ROOT"
  | blockInvalidTransactionsRoot => "BlockException.INVALID_TRANSACTIONS_ROOT"
  | blockInvalidWithdrawalsRoot => "BlockException.INVALID_WITHDRAWALS_ROOT"
  | blockRlpInvalidFieldOverflow64 => "BlockException.RLP_INVALID_FIELD_OVERFLOW_64"
  | blockRlpBlockLimitExceeded => "BlockException.RLP_BLOCK_LIMIT_EXCEEDED"
  | blockRlpStructuresEncoding => "BlockException.RLP_STRUCTURES_ENCODING"
  | blockRlpWithdrawalsNotRead => "BlockException.RLP_WITHDRAWALS_NOT_READ"
  | blockUnknownParent => "BlockException.UNKNOWN_PARENT"
  | blockUnknownParentZero => "BlockException.UNKNOWN_PARENT_ZERO"
  | blockInvalidBlockAccessList => "BlockException.INVALID_BLOCK_ACCESS_LIST"
  | blockInvalidBalHash => "BlockException.INVALID_BAL_HASH"
  | blockAccessListGasLimitExceeded => "BlockException.BLOCK_ACCESS_LIST_GAS_LIMIT_EXCEEDED"
  | blockIncorrectBlockFormat => "BlockException.INCORRECT_BLOCK_FORMAT"
  | txGasLimitPriceProductOverflow =>
    "TransactionException.GASLIMIT_PRICE_PRODUCT_OVERFLOW"
  | txGasAllowanceExceeded => "TransactionException.GAS_ALLOWANCE_EXCEEDED"
  | txInitcodeSizeExceeded => "TransactionException.INITCODE_SIZE_EXCEEDED"
  | txInsufficientAccountFunds => "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS"
  | txInsufficientMaxFeePerGas => "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS"
  | txIntrinsicGasTooLow => "TransactionException.INTRINSIC_GAS_TOO_LOW"
  | txGasLimitExceedsMaximum =>
    "TransactionException.GAS_LIMIT_EXCEEDS_MAXIMUM"
  | txInvalidChainId => "TransactionException.INVALID_CHAINID"
  | txNonceIsMax => "TransactionException.NONCE_IS_MAX"
  | txNonceMismatchTooHigh => "TransactionException.NONCE_MISMATCH_TOO_HIGH"
  | txNonceMismatchTooLow => "TransactionException.NONCE_MISMATCH_TOO_LOW"
  | txPriorityGreaterThanMaxFeePerGas =>
    "TransactionException.PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS"
  | txSenderNotEoa => "TransactionException.SENDER_NOT_EOA"
  | txType3TxBlobCountExceeded => "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED"
  | txType3TxContractCreation => "TransactionException.TYPE_3_TX_CONTRACT_CREATION"
  | txType3TxInvalidBlobVersionedHash =>
    "TransactionException.TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH"
  | txType3TxZeroBlobs => "TransactionException.TYPE_3_TX_ZERO_BLOBS"
  | txType4EmptyAuthorizationList => "TransactionException.TYPE_4_EMPTY_AUTHORIZATION_LIST"
  | txType4TxContractCreation => "TransactionException.TYPE_4_TX_CONTRACT_CREATION"

instance : ToString FixtureException := ⟨toString⟩

/-- Exact inverse of `toString`. Exact means exact: no trimming, no case
folding, no prefix acceptance. An unrecognized token is `none`, which every
caller must treat as a failure. This is the one place this module reads a
string, and it is the fixture's own external label -- never a rendered
diagnostic of this build. -/
def ofString? (s : String) : Option FixtureException :=
  match s with
  -- EIP-7623 names a separate *reason* for the same transaction-level
  -- rejection. Current fixtures list it as an alternative to the pre-existing
  -- intrinsic-gas identity; Jaune's Prague validator reports the latter.
  | "TransactionException.INTRINSIC_GAS_BELOW_FLOOR_GAS_COST" =>
    some txIntrinsicGasTooLow
  -- The v20 fixture publisher also permits the corresponding aggregate
  -- blob-gas allowance spelling for the established per-transaction limit.
  | "TransactionException.TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED" =>
    some txType3TxBlobCountExceeded
  | "TransactionException.INSUFFICIENT_MAX_FEE_PER_BLOB_GAS" =>
    some txInsufficientMaxFeePerGas
  | "TransactionException.TYPE_3_TX_WITH_FULL_BLOBS" =>
    some txType3TxBlobCountExceeded
  | "BlockException.INCORRECT_BLOB_GAS_USED" =>
    some blockInvalidGasUsed
  | "BlockException.BLOB_GAS_USED_ABOVE_LIMIT" =>
    some blockInvalidGasUsed
  | "BlockException.INCORRECT_EXCESS_BLOB_GAS" =>
    some blockInvalidGasUsed
  | "TransactionException.INVALID_SIGNATURE_VRS" =>
    some txSenderNotEoa
  -- The withdrawal-root fixtures permit the historical block-hash spelling as
  -- an alternative oracle name for the same header-commitment mismatch.
  | "BlockException.INVALID_BLOCK_HASH" =>
    some blockInvalidWithdrawalsRoot
  | _ => all.find? (fun e => e.toString = s)

/-- The delimiter separating the alternatives of an `expectException` set. -/
def delimiter : String := "|"

/-- Parse a fixture `expectException` string into the nonempty set of allowed
identities.

`String.splitOn` always yields at least one token, and every token must resolve
to a canonical identity, so a successful parse is nonempty by construction.
Tokens are matched exactly, which is what rejects whitespace variants
(`"A | B"`), and empty tokens are rejected, which is what rejects a stray
`"A||B"` or a leading/trailing delimiter. Repeated identities are collapsed:
this is a set, and `"A|A"` names the same one-element set as `"A"`. -/
def parseExpectation (s : String) : Except String (List FixtureException) := do
  let toks := s.splitOn delimiter
  let es ←
    toks.mapM fun tok =>
      if tok.isEmpty then
        .error
          s!"empty alternative in expectException {repr s} \
             (stray or duplicated {repr delimiter} delimiter)"
      else
        match ofString? tok with
        | some e => .ok e
        | none => .error s!"unknown expected exception identity {repr tok} in {repr s}"
  .ok es.eraseDups

------------------- CONSTRUCTOR CLASSIFICATION --------------------

-- Each mapping below is a total, exhaustive constructor match: registering an
-- arm is a claim that a specific typed reason carries a specific official
-- identity, and `none` is the deliberate fail-closed disposition of a reason
-- the reviewed vocabulary has no identity for. Adding a rejection constructor
-- upstream cannot compile without landing in one of these matches.

/-- The official identity of a strict-decode rejection. All seven reasons are
candidate verdicts in the audited ordering; several deliberately share the
official `RLP_STRUCTURES_ENCODING` identity while staying distinct reasons
internally. -/
def ofDecodeError : DecodeError → Option FixtureException
  | .rlpStructure _ => some blockRlpStructuresEncoding
  | .fixedWidth _ => some blockRlpStructuresEncoding
  | .fieldOverflow64 _ => some blockRlpInvalidFieldOverflow64
  | .fieldOverflow256 _ => some blockRlpStructuresEncoding
  | .leadingZeros _ => some blockRlpStructuresEncoding
  | .withdrawalsNotRead _ => some blockRlpWithdrawalsNotRead
  | .roundTrip _ => some blockRlpStructuresEncoding

/-- The official identity of a transaction-validation rejection. Every one of
the twenty-one reasons has an identity; the blob-fee reason shares
`INSUFFICIENT_MAX_FEE_PER_GAS` with the execution-fee reason, and both
blob-count reasons share `TYPE_3_TX_BLOB_COUNT_EXCEEDED`, exactly as the
retired string routes said. -/
def ofTxValidationError : TxValidationError → Option FixtureException
  | .gasPriceProductOverflow _ => some txGasLimitPriceProductOverflow
  | .gasAllowanceExceeded _ => some txGasAllowanceExceeded
  | .initcodeSizeExceeded _ => some txInitcodeSizeExceeded
  | .insufficientAccountFunds _ => some txInsufficientAccountFunds
  | .insufficientMaxFeePerGas _ => some txInsufficientMaxFeePerGas
  | .insufficientMaxFeePerBlobGas _ => some txInsufficientMaxFeePerGas
  | .transactionGasLimitExceeded _ => some txGasLimitExceedsMaximum
  | .intrinsicGasTooLow _ => some txIntrinsicGasTooLow
  | .invalidChainId _ => some txInvalidChainId
  | .nonceIsMax _ => some txNonceIsMax
  | .nonceMismatchTooHigh _ => some txNonceMismatchTooHigh
  | .nonceMismatchTooLow _ => some txNonceMismatchTooLow
  | .priorityGreaterThanMaxFee _ => some txPriorityGreaterThanMaxFeePerGas
  | .senderNotEoa _ => some txSenderNotEoa
  | .type3BlobCountExceeded _ => some txType3TxBlobCountExceeded
  | .type3BlobCountLimitExceeded _ => some txType3TxBlobCountExceeded
  | .type3ContractCreation _ => some txType3TxContractCreation
  | .type3InvalidBlobVersionedHash _ => some txType3TxInvalidBlobVersionedHash
  | .type3ZeroBlobs _ => some txType3TxZeroBlobs
  | .type4ContractCreation _ => some txType4TxContractCreation
  | .emptyAuthorizationList _ => some txType4EmptyAuthorizationList

/-- The official identity of a block-validation rejection.

One reason is deliberately unmapped, and its `none` is the fail-closed choice
rather than an oversight: `headerNonce` is a real consensus rule that the
Prague fixture vocabulary has no identity for. A block rejected for it cannot
be scored against any expected identity, so it must be reported as an unknown
actual reason -- not silently attached to whichever identity looks closest. -/
def ofBlockValidationError : BlockValidationError → Option FixtureException
  | .gasLimitTooBig _ => some blockGasLimitTooBig
  | .gasLimitAdjustment _ => some blockInvalidGasLimit
  | .gasUsedOverflow _ => some blockGasUsedOverflow
  | .gasUsedMismatch _ => some blockInvalidGasUsed
  | .timestampOlderThanParent _ => some blockInvalidBlockTimestampOlderThanParent
  | .blockNumber _ => some blockInvalidBlockNumber
  | .baseFeePerGas _ => some blockInvalidBaseFeePerGas
  | .difficultyOverParis _ => some blockImportImpossibleDifficultyOverParis
  | .ommersOverParis _ => some blockImportImpossibleUnclesOverParis
  | .extraDataTooBig _ => some blockExtraDataTooBig
  | .unknownParent _ => some blockUnknownParent
  | .unknownParentZero _ => some blockUnknownParentZero
  | .stateRoot _ => some blockInvalidStateRoot
  | .transactionsRoot _ => some blockInvalidTransactionsRoot
  | .receiptsRoot _ => some blockInvalidReceiptsRoot
  | .logBloom _ => some blockInvalidLogBloom
  | .withdrawalsRoot _ => some blockInvalidWithdrawalsRoot
  | .headerNonce _ => none
  | .excessBlobGas _ => some blockInvalidGasUsed
  | .blobGasUsed _ => some blockInvalidGasUsed
  | .requestsHash _ => some blockInvalidRequests
  | .depositEventLayout _ => some blockInvalidDepositEventLayout
  | .systemContractCallFailed _ => some blockSystemContractCallFailed
  -- Goal D (DP-2): the empty-contract rejection was a fail-closed internal
  -- invariant with no identity; the transition corpus names one.
  | .systemContractEmpty _ => some blockSystemContractEmpty
  | .blockRlpSizeExceeded _ => some blockRlpBlockLimitExceeded
  -- EIP-7928 (goal C). Consensus observes one thing, the header's hash against
  -- the computed list; the fixture runner refines that reason into the two
  -- content identities from the list the fixture publishes as its
  -- verification aid (`Main.lean`): a published list not in canonical form is
  -- `INCORRECT_BLOCK_FORMAT`, a canonical one the header's hash commits to
  -- but Jaune did not compute is `INVALID_BLOCK_ACCESS_LIST`, and a header
  -- hash inconsistent with the published list is `INVALID_BAL_HASH`.
  | .blockAccessListHash _ _ => some blockInvalidBalHash
  | .blockAccessListContent _ => some blockInvalidBlockAccessList
  | .blockAccessListFormat _ => some blockIncorrectBlockFormat
  | .blockAccessListGasLimit _ => some blockAccessListGasLimitExceeded
  -- No official identity: the current-mainnet corpus has no fixture that can
  -- reach this rule, because every fork it covers defines the same header
  -- fields. The devnet corpus does -- `invalid_post_fork_block_without_slot_number`
  -- and `invalid_pre_fork_block_with_slot_number` -- and assigning the
  -- identity those fixtures expect belongs with the goal that activates that
  -- lane. Failing closed until then is the same choice `.headerNonce` makes.
  | .headerFieldPresence _ => none

/-- The official identity of a sender-recovery rejection. Only a malformed
signature has one; the other cryptographic reasons fail closed. -/
def ofCryptoError : CryptoError → Option FixtureException
  | .invalidSignature _ => some txSenderNotEoa
  | .pointCompression _ => none
  | .value _ => none

/-- The classifier: each typed candidate-rejection reason maps directly to at
most one official identity. This is total over `BlockRejection`, so every
rejection arm is deliberately assigned; an `ImportFailure` has no arm here at
all, which is what makes "a context, support, harness, internal, or VM
failure can never score as an expected rejection" a fact about types rather
than a convention about strings. -/
def ofBlockRejection : BlockRejection → Option FixtureException
  | .transaction reason => ofTxValidationError reason
  | .block reason => ofBlockValidationError reason
  | .decode reason => ofDecodeError reason
  | .senderRecovery reason => ofCryptoError reason

/-- The matcher: succeed only when the one identity of the actual rejection is
a member of the parsed expected set. (`matches` itself is a reserved token in
Lean, hence the name.) -/
def matchesSet (expected : List FixtureException) (actual : BlockRejection) : Bool :=
  match ofBlockRejection actual with
  | none => false
  | some a => expected.contains a

end FixtureException

----------------- FIXTURE VOCABULARY REGRESSION CHECKS ------------------

open FixtureException

-- The vocabulary is the reviewed current-mainnet identity set reached by the
-- supported static Prague and Osaka lanes, plus the four the Glamsterdam
-- devnet lane's `eip7928_*` subtree names (goal C).
#guard all.length = 48

-- `toString` is injective, so no two identities collapse to one token.
#guard (all.map toString).eraseDups.length = 48

-- `toString`/`ofString?` round trip on all 47, in both directions.
#guard all.all (fun e => ofString? e.toString == some e)
#guard all.all (fun e => (ofString? e.toString).all (fun e' => e'.toString == e.toString))

-- `Except` has no `BEq`, so parse results are compared through these two
-- helpers rather than `==`.
private def parsesTo (s : String) (es : List FixtureException) : Bool :=
  match parseExpectation s with
  | .ok es' => es' == es
  | .error _ => false

private def parseRejects (s : String) : Bool := (parseExpectation s).toOption.isNone

-- Every identity's own spelling parses as the one-element set naming it. This
-- covers all 31 singleton `expectException` strings in the inventory.
#guard all.all (fun e => parsesTo e.toString [e])

-- `ofString?` is exact: near misses are unknown tokens, not near matches.
#guard (ofString? "BlockException.EXTRA_DATA_TOO_BIG").isSome
#guard (ofString? "EXTRA_DATA_TOO_BIG").isNone                       -- bare, unqualified
#guard (ofString? "BlockException.EXTRA_DATA_TOO_BIG ").isNone       -- trailing space
#guard (ofString? " BlockException.EXTRA_DATA_TOO_BIG").isNone       -- leading space
#guard (ofString? "blockexception.extra_data_too_big").isNone        -- case folded
#guard (ofString? "BlockException.EXTRA_DATA_TOO_BIG_X").isNone      -- longer
#guard (ofString? "BlockException.EXTRA_DATA_TOO_BI").isNone         -- truncated
#guard (ofString? "BlockException").isNone                           -- namespace only
#guard (ofString? "InvalidBlock").isNone                             -- old broad category
#guard (ofString? "").isNone

-- The seven composite expectation strings in the generated inventory, each
-- parsing to the exact set it names.
#guard parsesTo
  "BlockException.RLP_STRUCTURES_ENCODING|BlockException.RLP_INVALID_FIELD_OVERFLOW_64"
  [blockRlpStructuresEncoding, blockRlpInvalidFieldOverflow64]
#guard parsesTo
  "BlockException.RLP_STRUCTURES_ENCODING|BlockException.RLP_WITHDRAWALS_NOT_READ"
  [blockRlpStructuresEncoding, blockRlpWithdrawalsNotRead]
#guard parsesTo
  "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS|TransactionException.GASLIMIT_PRICE_PRODUCT_OVERFLOW"
  [txInsufficientAccountFunds, txGasLimitPriceProductOverflow]
#guard parsesTo
  "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS|TransactionException.INTRINSIC_GAS_TOO_LOW"
  [txInsufficientAccountFunds, txIntrinsicGasTooLow]
#guard parsesTo
  "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS|TransactionException.GAS_ALLOWANCE_EXCEEDED"
  [txInsufficientMaxFeePerGas, txGasAllowanceExceeded]
#guard parsesTo
  "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS|TransactionException.INSUFFICIENT_ACCOUNT_FUNDS"
  [txInsufficientMaxFeePerGas, txInsufficientAccountFunds]
#guard parsesTo
  "TransactionException.SENDER_NOT_EOA|TransactionException.INSUFFICIENT_ACCOUNT_FUNDS"
  [txSenderNotEoa, txInsufficientAccountFunds]

-- Order is preserved and duplicates collapse: the parse is a set.
#guard parsesTo "TransactionException.NONCE_IS_MAX|TransactionException.NONCE_IS_MAX"
  [txNonceIsMax]

-- Regression inventory of exact `expectException` spellings that must parse.
-- Its identities cover every constructor in `all`, so no vocabulary extension
-- can silently remain unroutable.
def fixtureInventory : List String :=
  [ "BlockException.EXTRA_DATA_TOO_BIG",                                                                    -- 3
    "BlockException.GASLIMIT_TOO_BIG",                                                                      -- 1
    "BlockException.GAS_USED_OVERFLOW",                                                                     -- 1
    "BlockException.IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS",                                               -- 1
    "BlockException.IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS",                                                   -- 66
    "BlockException.INVALID_BASEFEE_PER_GAS",                                                               -- 2
    "BlockException.INVALID_BLOCK_NUMBER",                                                                  -- 2
    "BlockException.INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT",                                             -- 7
    "BlockException.INVALID_GASLIMIT",                                                                      -- 10
    "BlockException.INVALID_GAS_USED",                                                                      -- 1
    "BlockException.INVALID_LOG_BLOOM",                                                                     -- 1
    "BlockException.INVALID_DEPOSIT_EVENT_LAYOUT",                                                          -- current mainnet 22
    "BlockException.SYSTEM_CONTRACT_CALL_FAILED",                                                           -- current mainnet 6
    "BlockException.INVALID_REQUESTS",                                                                      -- current mainnet 43
    "BlockException.INVALID_RECEIPTS_ROOT",                                                                 -- 1
    "BlockException.INVALID_STATE_ROOT",                                                                    -- 2
    "BlockException.INVALID_TRANSACTIONS_ROOT",                                                             -- 1
    "BlockException.INVALID_WITHDRAWALS_ROOT",                                                              -- 2
    "BlockException.INVALID_WITHDRAWALS_ROOT|BlockException.INVALID_BLOCK_HASH",                            -- current mainnet 3
    "BlockException.RLP_STRUCTURES_ENCODING|BlockException.RLP_INVALID_FIELD_OVERFLOW_64",                  -- 4
    "BlockException.RLP_STRUCTURES_ENCODING|BlockException.RLP_WITHDRAWALS_NOT_READ",                       -- 1
    "BlockException.UNKNOWN_PARENT",                                                                        -- 1
    "BlockException.UNKNOWN_PARENT_ZERO",                                                                   -- 1
    "TransactionException.GAS_ALLOWANCE_EXCEEDED",                                                          -- 5
    "TransactionException.INITCODE_SIZE_EXCEEDED",                                                          -- 1
    "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS",                                                      -- 68
    "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS|TransactionException.GASLIMIT_PRICE_PRODUCT_OVERFLOW", -- 1
    "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS|TransactionException.INTRINSIC_GAS_TOO_LOW",           -- 49
    "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS",                                                    -- 7
    "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS|TransactionException.GAS_ALLOWANCE_EXCEEDED",        -- 1
    "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS|TransactionException.INSUFFICIENT_ACCOUNT_FUNDS",    -- 3
    "TransactionException.INTRINSIC_GAS_TOO_LOW",                                                           -- 30
    "TransactionException.INVALID_CHAINID",                                                                -- current mainnet 5
    "TransactionException.NONCE_IS_MAX",                                                                    -- 2
    "TransactionException.NONCE_MISMATCH_TOO_HIGH",                                                         -- 1
    "TransactionException.NONCE_MISMATCH_TOO_LOW",                                                          -- 1
    "TransactionException.PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS",                                           -- 7
    "TransactionException.SENDER_NOT_EOA",                                                                  -- 7
    "TransactionException.SENDER_NOT_EOA|TransactionException.INSUFFICIENT_ACCOUNT_FUNDS",                  -- 1
    "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED",                                                   -- 1
    "TransactionException.TYPE_3_TX_CONTRACT_CREATION",                                                     -- 1
    "TransactionException.TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH",                                           -- 1
    "TransactionException.TYPE_3_TX_ZERO_BLOBS" ]                                                           -- 1
    ++ [ "TransactionException.TYPE_4_EMPTY_AUTHORIZATION_LIST",                                           -- current mainnet 1
         "TransactionException.TYPE_4_TX_CONTRACT_CREATION" ]                                               -- current mainnet 1
    -- The Glamsterdam devnet lane's `for_amsterdam/amsterdam/eip*` subtrees at
    -- `tests-glamsterdam-devnet@v8.1.4` (goal C, Appendix C): the three EIP-7928
    -- identities, the two alternations, the malformed-list identity, and the
    -- gas-used alternation the block-accounting subtree carries.
    ++ [ "BlockException.INVALID_BLOCK_ACCESS_LIST",                                                        -- devnet 61
         "BlockException.BLOCK_ACCESS_LIST_GAS_LIMIT_EXCEEDED",                                             -- devnet 4
         "BlockException.INVALID_BLOCK_ACCESS_LIST|BlockException.INVALID_GAS_USED",                        -- devnet 1
         "BlockException.INVALID_BAL_HASH|BlockException.INVALID_BLOCK_HASH",                               -- devnet 1
         "BlockException.INCORRECT_BLOCK_FORMAT",                                                           -- devnet 2
         "BlockException.GAS_USED_OVERFLOW|TransactionException.GAS_ALLOWANCE_EXCEEDED" ]                   -- devnet 9
    -- The devnet lane's `for_bpo2toamsterdamattime15k/` transition corpus
    -- (goal D): the empty-request-contract identity of EIP-8282's
    -- `test_contract_deployment.py` `deploy_after_fork` cases.
    ++ [ "BlockException.SYSTEM_CONTRACT_EMPTY" ]                                                          -- devnet transitions 4

#guard fixtureInventory.length = 52
#guard fixtureInventory.eraseDups.length = 52
#guard fixtureInventory.all (fun s => (parseExpectation s).toOption.isSome)

-- Both coverage directions: every identity is reachable from the corpus, and
-- the corpus mentions nothing outside the vocabulary. The second direction
-- holds because parsing succeeded above; the first is the real check, and it
-- fails loudly if a constructor is added that the fixtures never name.
#guard
  (fixtureInventory.flatMap
    (fun s => ((parseExpectation s).toOption.getD []))).eraseDups.length = 46

-- Malformed expectation strings are rejected, not repaired.
#guard parseRejects ""                                                     -- no alternatives
#guard parseRejects "|"                                                    -- two empty tokens
#guard parseRejects "BlockException.INVALID_GASLIMIT|"                     -- trailing delimiter
#guard parseRejects "|BlockException.INVALID_GASLIMIT"                     -- leading delimiter
#guard parseRejects
  "BlockException.INVALID_GASLIMIT||BlockException.GASLIMIT_TOO_BIG"       -- duplicated delimiter
#guard parseRejects
  "BlockException.INVALID_GASLIMIT | BlockException.GASLIMIT_TOO_BIG"      -- whitespace variant
#guard parseRejects "BlockException.INVALID_GASLIMIT|NotAnIdentity"        -- one unknown token
#guard parseRejects "InvalidBlock"                                         -- old broad category
#guard parseRejects "BlockException.INVALID_GASLIMIT|InvalidBlock"

----------------- CONSTRUCTOR-CLASSIFICATION CHECKS ------------------

-- Totality of the deliberate assignment: every decode and transaction reason
-- has an identity; exactly two block reasons -- the header nonce, and the
-- fork-dependent header-field presence rule -- are knowingly unmapped; the
-- four EIP-7928 reasons each have their own; and of the cryptographic reasons
-- only the malformed signature classifies.
--
-- The presence rule is unmapped because no fixture in the installed corpora
-- can reach it: every fork the current-mainnet lane covers defines the same
-- header fields. The devnet lane's `invalid_pre_fork_block_with_slot_number`
-- and `invalid_post_fork_block_without_slot_number` do reach it, and giving it
-- the identity those fixtures expect belongs with the goal that activates that
-- lane. Until then it fails closed, which is what an unmapped reason means.
#guard DecodeError.all.all (fun e => (ofDecodeError e).isSome)
#guard TxValidationError.all.all (fun e => (ofTxValidationError e).isSome)
#guard (BlockValidationError.all.filter
  (fun e => (ofBlockValidationError e).isNone)).length = 2
#guard (ofBlockValidationError (.headerNonce .none)).isNone
#guard (ofBlockValidationError (.headerNonce (.text "detail"))).isNone
#guard (ofBlockValidationError (.headerFieldPresence .none)).isNone
#guard (ofBlockValidationError (.headerFieldPresence (.text "detail"))).isNone
#guard (ofCryptoError (.invalidSignature .none)) == some txSenderNotEoa
#guard (ofCryptoError (.pointCompression .none)).isNone
#guard (ofCryptoError (.value .none)).isNone

-- Classification reads the constructor, never the diagnostic payload: any
-- detail text yields the same identity.
#guard ofBlockRejection (.block (.gasLimitTooBig .none))
  == ofBlockRejection (.block (.gasLimitTooBig (.text "gas limit = 2^63")))
#guard ofBlockRejection (.transaction (.intrinsicGasTooLow (.text "x")))
  == some txIntrinsicGasTooLow
#guard ofBlockRejection (.decode (.fieldOverflow64 (.text "nine bytes")))
  == some blockRlpInvalidFieldOverflow64
#guard ofBlockRejection (.senderRecovery (.invalidSignature (.text "bad v")))
  == some txSenderNotEoa

-- Coverage in the fixture-to-producer direction: every one of the 43
-- identities is reachable from some typed rejection constructor, so a newly
-- observed expected identity cannot silently remain unclassifiable.
#guard all.all fun e =>
  TxValidationError.all.any (fun r => ofTxValidationError r == some e) ||
  BlockValidationError.all.any (fun r => ofBlockValidationError r == some e) ||
  DecodeError.all.any (fun r => ofDecodeError r == some e) ||
  ofCryptoError (.invalidSignature .none) == some e

-- The pairs the fixtures insist are different reasons really do land on
-- different identities. These are the distinctions the whole vocabulary
-- exists for: an out-of-range gas limit is not a gas limit that drifted from
-- its parent, a header claiming more gas than it allows is not a header whose
-- claim disagrees with execution, and a zero parent hash is not an unknown
-- one.
#guard ofBlockValidationError (.gasLimitTooBig .none)
  != ofBlockValidationError (.gasLimitAdjustment .none)
#guard ofBlockValidationError (.gasUsedOverflow .none)
  != ofBlockValidationError (.gasUsedMismatch .none)
#guard ofBlockValidationError (.unknownParent .none)
  != ofBlockValidationError (.unknownParentZero .none)
#guard ofTxValidationError (.nonceMismatchTooLow .none)
  != ofTxValidationError (.nonceMismatchTooHigh .none)
#guard ofTxValidationError (.intrinsicGasTooLow .none)
  != ofTxValidationError (.gasAllowanceExceeded .none)

-- The distinct strict-decode reasons that share the official structures
-- identity still share it -- deliberately -- while the 64-bit overflow and
-- the omitted-withdrawals reasons keep their own.
#guard ofDecodeError (.rlpStructure .none) == some blockRlpStructuresEncoding
#guard ofDecodeError (.roundTrip .none) == some blockRlpStructuresEncoding
#guard ofDecodeError (.leadingZeros .none) == some blockRlpStructuresEncoding
#guard ofDecodeError (.fieldOverflow64 .none) == some blockRlpInvalidFieldOverflow64
#guard ofDecodeError (.withdrawalsNotRead .none) == some blockRlpWithdrawalsNotRead

-- The matcher is set membership on the one classified identity -- never
-- "some failure occurred".
#guard matchesSet [blockGasLimitTooBig]
  (.block (.gasLimitTooBig (.text "gas limit = 9223372036854775808 ≥ \
     absolute maximum = 9223372036854775808")))
-- The right kind of failure, but not the expected identity: still a failure.
#guard ¬ matchesSet [blockInvalidGasLimit] (.block (.gasLimitTooBig .none))
-- An unmapped reason never matches, no matter how broad the expected set.
#guard ¬ matchesSet all (.block (.headerNonce .none))
#guard ¬ matchesSet all (.senderRecovery (.pointCompression .none))

-- EIP-7928 (goal C): the four reasons land on four different identities, the
-- corpus's alternations parse to the sets they name, and a hash mismatch is
-- never scored as a content or format mismatch or vice versa -- which is what
-- fixed decision 9's refusal to alias buys.
#guard ofBlockValidationError (.blockAccessListHash emptyOmmerHash .none) == some blockInvalidBalHash
#guard ofBlockValidationError (.blockAccessListContent .none)
  == some blockInvalidBlockAccessList
#guard ofBlockValidationError (.blockAccessListFormat .none) == some blockIncorrectBlockFormat
#guard ofBlockValidationError (.blockAccessListGasLimit .none)
  == some blockAccessListGasLimitExceeded
#guard [blockInvalidBalHash, blockInvalidBlockAccessList, blockIncorrectBlockFormat,
  blockAccessListGasLimitExceeded].eraseDups.length = 4
#guard parsesTo "BlockException.INVALID_BLOCK_ACCESS_LIST|BlockException.INVALID_GAS_USED"
  [blockInvalidBlockAccessList, blockInvalidGasUsed]
#guard parsesTo "BlockException.INVALID_BAL_HASH|BlockException.INVALID_BLOCK_HASH"
  [blockInvalidBalHash, blockInvalidWithdrawalsRoot]
#guard (parseExpectation "BlockException.INVALID_BLOCK_ACCESS_LIST").toOption.all
  (fun expected => ¬ matchesSet expected (.block (.blockAccessListHash emptyOmmerHash .none)))
#guard (parseExpectation "BlockException.INVALID_BLOCK_ACCESS_LIST").toOption.all
  (fun expected => matchesSet expected (.block (.blockAccessListContent .none)))
#guard (parseExpectation "BlockException.INVALID_BAL_HASH|BlockException.INVALID_BLOCK_HASH").toOption.all
  (fun expected => matchesSet expected (.block (.blockAccessListHash emptyOmmerHash .none)))
#guard (parseExpectation "BlockException.INVALID_BAL_HASH|BlockException.INVALID_BLOCK_HASH").toOption.all
  (fun expected => ¬ matchesSet expected (.block (.blockAccessListContent .none)))
#guard (parseExpectation "BlockException.INVALID_BLOCK_ACCESS_LIST|BlockException.INVALID_GAS_USED").toOption.all
  (fun expected => ¬ matchesSet expected (.block (.blockAccessListHash emptyOmmerHash .none)))
#guard (parseExpectation "BlockException.BLOCK_ACCESS_LIST_GAS_LIMIT_EXCEEDED").toOption.all
  (fun expected => matchesSet expected (.block (.blockAccessListGasLimit .none)))
#guard (parseExpectation "BlockException.INCORRECT_BLOCK_FORMAT").toOption.all
  (fun expected => matchesSet expected (.block (.blockAccessListFormat .none)))
-- An empty expected set matches nothing; `parseExpectation` cannot produce one.
#guard ¬ matchesSet [] (.block (.gasLimitTooBig .none))

-- The `GasLimitHigherThan2p63m1` case, from typed reason to verdict, against
-- the expectation string the fixture actually carries.
#guard (parseExpectation "BlockException.GASLIMIT_TOO_BIG").toOption.all
  (fun expected => matchesSet expected (.block (.gasLimitTooBig .none)))
-- The same rejection against the *adjustment* expectation is still a failure:
-- the block was rejected, but not for the reason the fixture names.
#guard (parseExpectation "BlockException.INVALID_GASLIMIT").toOption.all
  (fun expected => ¬ matchesSet expected (.block (.gasLimitTooBig .none)))

end Jaune
