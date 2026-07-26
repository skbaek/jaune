-- FixtureException.lean : the canonical vocabulary of official fixture
-- exception identities, and the fail-closed matcher built on it.
--
-- This module is fixture-runner infrastructure, not EVM semantics: it is
-- imported by `Main.lean` only, and deliberately not from the `Elevm` library
-- root, so that no proof client depends on it.
--
-- A fixture's `expectException` is a `|`-separated set of *allowed* official
-- exception identities. The runner must parse that set, classify the actual
-- error as exactly one canonical identity, and accept only set membership.
-- Everything here therefore fails closed: unknown expected identities, unknown
-- actual errors, and broad categories such as a bare `InvalidBlock` are
-- failures, never successes. There is deliberately no `contains`, no suffix
-- match, and no "any RLP error is good enough" fallback -- those are what let a
-- block be rejected for the wrong reason and still be scored as a pass.

import Elevm.Execution

/-- One official exception identity from the Prague fixture corpus.

The corpus vocabulary was generated from the fixtures rather than assumed: at
the time of writing the selected Prague cases contain 296 expected-invalid
blocks, 38 distinct `expectException` strings, and exactly these 35 individual
identities, spanning the `BlockException` and `TransactionException`
namespaces. `FixtureException.all` and the `#guard`s below pin those counts, so
corpus drift shows up as a build failure rather than as a silently accepted
unknown token. -/
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
  | blockInvalidReceiptsRoot
  | blockInvalidStateRoot
  | blockInvalidTransactionsRoot
  | blockInvalidWithdrawalsRoot
  | blockRlpInvalidFieldOverflow64
  | blockRlpStructuresEncoding
  | blockRlpWithdrawalsNotRead
  | blockUnknownParent
  | blockUnknownParentZero
  -- TransactionException.*
  | txGasLimitPriceProductOverflow
  | txGasAllowanceExceeded
  | txInitcodeSizeExceeded
  | txInsufficientAccountFunds
  | txInsufficientMaxFeePerGas
  | txIntrinsicGasTooLow
  | txNonceIsMax
  | txNonceMismatchTooHigh
  | txNonceMismatchTooLow
  | txPriorityGreaterThanMaxFeePerGas
  | txSenderNotEoa
  | txType3TxBlobCountExceeded
  | txType3TxContractCreation
  | txType3TxInvalidBlobVersionedHash
  | txType3TxZeroBlobs
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
    blockInvalidReceiptsRoot,
    blockInvalidStateRoot,
    blockInvalidTransactionsRoot,
    blockInvalidWithdrawalsRoot,
    blockRlpInvalidFieldOverflow64,
    blockRlpStructuresEncoding,
    blockRlpWithdrawalsNotRead,
    blockUnknownParent,
    blockUnknownParentZero,
    txGasLimitPriceProductOverflow,
    txGasAllowanceExceeded,
    txInitcodeSizeExceeded,
    txInsufficientAccountFunds,
    txInsufficientMaxFeePerGas,
    txIntrinsicGasTooLow,
    txNonceIsMax,
    txNonceMismatchTooHigh,
    txNonceMismatchTooLow,
    txPriorityGreaterThanMaxFeePerGas,
    txSenderNotEoa,
    txType3TxBlobCountExceeded,
    txType3TxContractCreation,
    txType3TxInvalidBlobVersionedHash,
    txType3TxZeroBlobs ]

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
  | blockInvalidReceiptsRoot => "BlockException.INVALID_RECEIPTS_ROOT"
  | blockInvalidStateRoot => "BlockException.INVALID_STATE_ROOT"
  | blockInvalidTransactionsRoot => "BlockException.INVALID_TRANSACTIONS_ROOT"
  | blockInvalidWithdrawalsRoot => "BlockException.INVALID_WITHDRAWALS_ROOT"
  | blockRlpInvalidFieldOverflow64 => "BlockException.RLP_INVALID_FIELD_OVERFLOW_64"
  | blockRlpStructuresEncoding => "BlockException.RLP_STRUCTURES_ENCODING"
  | blockRlpWithdrawalsNotRead => "BlockException.RLP_WITHDRAWALS_NOT_READ"
  | blockUnknownParent => "BlockException.UNKNOWN_PARENT"
  | blockUnknownParentZero => "BlockException.UNKNOWN_PARENT_ZERO"
  | txGasLimitPriceProductOverflow =>
    "TransactionException.GASLIMIT_PRICE_PRODUCT_OVERFLOW"
  | txGasAllowanceExceeded => "TransactionException.GAS_ALLOWANCE_EXCEEDED"
  | txInitcodeSizeExceeded => "TransactionException.INITCODE_SIZE_EXCEEDED"
  | txInsufficientAccountFunds => "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS"
  | txInsufficientMaxFeePerGas => "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS"
  | txIntrinsicGasTooLow => "TransactionException.INTRINSIC_GAS_TOO_LOW"
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

instance : ToString FixtureException := ⟨toString⟩

/-- Exact inverse of `toString`. Exact means exact: no trimming, no case
folding, no prefix acceptance. An unrecognized token is `none`, which every
caller must treat as a failure. -/
def ofString? (s : String) : Option FixtureException :=
  match s with
  -- EIP-7623 names a separate *reason* for the same transaction-level
  -- rejection. Current fixtures list it as an alternative to the pre-existing
  -- intrinsic-gas identity; ELeVM's Prague validator reports the latter.
  | "TransactionException.INTRINSIC_GAS_BELOW_FLOOR_GAS_COST" =>
    some txIntrinsicGasTooLow
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

/-- A registered route from an actual internal error to the one canonical
identity it means.

The `String` is an error *tag*: it matches an actual error either exactly, or
as a prefix ending at the fixed `" : "` delimiter, so a producer may keep
detailed internal text after the tag. This is `hasErrorType`, the same
convention the rest of the executable already uses. -/
abbrev ActualRoute : Type := String × FixtureException

/-- Classify an actual error using an explicit route table.

Recognizes *only* explicitly registered exact messages or tag-prefixes; there is
no substring, suffix, or category fallback. An unregistered error is `none` and
must fail the fixture rather than be waved through. -/
def classifyWith (routes : List ActualRoute) (err : String) : Option FixtureException :=
  (routes.find? (fun r => hasErrorType err r.fst)).map Prod.snd

/-- The routes from ELeVM's actual errors to canonical identities.

Registering a route is a claim that a specific producer raises a specific
official identity. The header, post-transition, transaction-validation and RLP
producers are now precise enough for that claim. In particular, nonce direction,
intrinsic gas, the 256-bit gas-price product, and each type-3 rule have distinct
tags rather than sharing a broad `InvalidTransaction` string. The three RLP
identities are exact here: a 64-bit scalar overflow has its own route, omission
of the post-Shanghai withdrawals component has its own route, and the remaining
strict structural/canonical encoding failures route to structures encoding.

Four block tags are deliberately absent, and their absence is the fail-closed
choice rather than an oversight: `headerNonceTag`, `excessBlobGasTag`,
`blobGasUsedTag` and `requestsHashTag` are real consensus rules that the Prague
fixture vocabulary has no identity for. A block rejected for one of them cannot
be scored against any expected identity, so it must be reported as an unknown
actual error -- not silently attached to whichever identity looks closest. -/
def actualRoutes : List ActualRoute :=
  [ (gasLimitTooBigTag, blockGasLimitTooBig),
    (gasLimitAdjustmentTag, blockInvalidGasLimit),
    (gasUsedOverflowTag, blockGasUsedOverflow),
    (gasUsedMismatchTag, blockInvalidGasUsed),
    (timestampOlderThanParentTag, blockInvalidBlockTimestampOlderThanParent),
    (blockNumberTag, blockInvalidBlockNumber),
    (baseFeePerGasTag, blockInvalidBaseFeePerGas),
    (difficultyOverParisTag, blockImportImpossibleDifficultyOverParis),
    (ommersOverParisTag, blockImportImpossibleUnclesOverParis),
    (extraDataTooBigTag, blockExtraDataTooBig),
    (unknownParentTag, blockUnknownParent),
    (unknownParentZeroTag, blockUnknownParentZero),
    (stateRootTag, blockInvalidStateRoot),
    (transactionsRootTag, blockInvalidTransactionsRoot),
    (receiptsRootTag, blockInvalidReceiptsRoot),
    (logBloomTag, blockInvalidLogBloom),
    (withdrawalsRootTag, blockInvalidWithdrawalsRoot),
    (rlpFieldOverflow64Tag, blockRlpInvalidFieldOverflow64),
    (rlpWithdrawalsNotReadTag, blockRlpWithdrawalsNotRead),
    (rlpStructureTag, blockRlpStructuresEncoding),
    (rlpFixedWidthTag, blockRlpStructuresEncoding),
    (rlpFieldOverflow256Tag, blockRlpStructuresEncoding),
    (rlpLeadingZerosTag, blockRlpStructuresEncoding),
    (rlpRoundTripTag, blockRlpStructuresEncoding),
    (gasPriceProductOverflowTag, txGasLimitPriceProductOverflow),
    (gasAllowanceExceededTag, txGasAllowanceExceeded),
    (initcodeSizeExceededTag, txInitcodeSizeExceeded),
    (insufficientAccountFundsTag, txInsufficientAccountFunds),
    (insufficientMaxFeePerGasTag, txInsufficientMaxFeePerGas),
    (intrinsicGasTooLowTag, txIntrinsicGasTooLow),
    (nonceIsMaxTag, txNonceIsMax),
    (nonceMismatchTooHighTag, txNonceMismatchTooHigh),
    (nonceMismatchTooLowTag, txNonceMismatchTooLow),
    (priorityGreaterThanMaxFeeTag, txPriorityGreaterThanMaxFeePerGas),
    (senderNotEoaTag, txSenderNotEoa),
    (type3BlobCountExceededTag, txType3TxBlobCountExceeded),
    (type3ContractCreationTag, txType3TxContractCreation),
    (type3InvalidBlobVersionedHashTag, txType3TxInvalidBlobVersionedHash),
    (type3ZeroBlobsTag, txType3TxZeroBlobs) ]

/-- The block tags with no fixture identity, listed so the coverage checks can
assert that every block tag is either routed or knowingly unrouted. -/
def unroutedBlockTags : List String :=
  [ headerNonceTag, excessBlobGasTag, blobGasUsedTag, requestsHashTag ]

/-- Classify an actual error against the registered routes. -/
def classify (err : String) : Option FixtureException :=
  classifyWith actualRoutes err

/-- The matcher: succeed only when the one identity classified from the actual
error is a member of the parsed expected set. (`matches` itself is a reserved
token in Lean, hence the name.) -/
def matchesSet (expected : List FixtureException) (actual : String) : Bool :=
  match classify actual with
  | none => false
  | some a => expected.contains a

/-- The string-level matcher, with the diagnostics the runner needs on failure:
both the raw actual error and its canonical reading (or the fact that it has
none). Returns the matched identity so a caller can report *which* alternative
was hit. -/
def matchesExpectation (expected actual : String) : Except String FixtureException := do
  let es ← parseExpectation expected
  match classify actual with
  | none =>
    .error s!"unknown actual error {repr actual} : it maps to no canonical \
              exception identity, expected one of {es.map toString}"
  | some a =>
    if es.contains a then
      .ok a
    else
      .error s!"exception mismatch : actual {repr actual} is {a.toString}, \
                expected one of {es.map toString}"

end FixtureException

----------------- FIXTURE VOCABULARY REGRESSION CHECKS ------------------

open FixtureException

-- The vocabulary is exactly the generated Prague inventory: 35 identities.
#guard all.length = 35

-- `toString` is injective, so no two identities collapse to one token.
#guard (all.map toString).eraseDups.length = 35

-- `toString`/`ofString?` round trip on all 35, in both directions.
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

-- Every distinct `expectException` string in the generated Prague inventory,
-- with its plan-writing-time occurrence count. 296 expected-invalid blocks
-- across 38 strings; the whole table must parse, and its identities must be
-- exactly the 35 in `all` -- no unused constructor, no unroutable token.
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
    "BlockException.INVALID_RECEIPTS_ROOT",                                                                 -- 1
    "BlockException.INVALID_STATE_ROOT",                                                                    -- 2
    "BlockException.INVALID_TRANSACTIONS_ROOT",                                                             -- 1
    "BlockException.INVALID_WITHDRAWALS_ROOT",                                                              -- 2
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

#guard fixtureInventory.length = 38
#guard fixtureInventory.eraseDups.length = 38
#guard fixtureInventory.all (fun s => (parseExpectation s).toOption.isSome)

-- Both coverage directions: every identity is reachable from the corpus, and
-- the corpus mentions nothing outside the vocabulary. The second direction
-- holds because parsing succeeded above; the first is the real check, and it
-- fails loudly if a constructor is added that the fixtures never name.
#guard
  (fixtureInventory.flatMap
    (fun s => ((parseExpectation s).toOption.getD []))).eraseDups.length = 35

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

-- The classifier's route semantics, exercised against a synthetic table: the
-- real `actualRoutes` is still empty by design.
private def sampleRoutes : List ActualRoute :=
  [ ("InvalidGasLimitAbsolute", blockGasLimitTooBig),
    ("InvalidGasLimitAdjustment", blockInvalidGasLimit) ]

-- An exact message, and a tag-prefix ending at the fixed " : " delimiter.
#guard classifyWith sampleRoutes "InvalidGasLimitAbsolute" == some blockGasLimitTooBig
#guard classifyWith sampleRoutes "InvalidGasLimitAbsolute : gasLimit = 2^63"
  == some blockGasLimitTooBig
#guard classifyWith sampleRoutes "InvalidGasLimitAdjustment : delta too large"
  == some blockInvalidGasLimit

-- A registered tag is not a substring or suffix matcher, and the delimiter is
-- fixed: only " : " opens the detail text.
#guard (classifyWith sampleRoutes "InvalidGasLimitAbsolute: gasLimit").isNone
#guard (classifyWith sampleRoutes "InvalidGasLimitAbsoluteX").isNone
#guard (classifyWith sampleRoutes "Error: InvalidGasLimitAbsolute").isNone
#guard (classifyWith sampleRoutes "wrapped InvalidGasLimitAbsolute : detail").isNone

-- The strict block-RLP routes are one-to-one at the producer boundary. In
-- particular, the two withdrawal-index overflows cannot be confused with the
-- later re-encoding invariant, and an omitted withdrawals list cannot be
-- mistaken for an arbitrary malformed list.
#guard classify
  s!"{rlpFieldOverflow64Tag} : withdrawal globalIndex scalar is 9 bytes"
    == some blockRlpInvalidFieldOverflow64
#guard classify
  s!"{rlpWithdrawalsNotReadTag} : post-Shanghai block body omits the withdrawals list"
    == some blockRlpWithdrawalsNotRead
#guard classify
  s!"{rlpStructureTag} : block : expected four items"
    == some blockRlpStructuresEncoding
#guard classify
  s!"{rlpRoundTripTag} : decoded block does not re-encode byte-for-byte"
    == some blockRlpStructuresEncoding
#guard (classifyWith sampleRoutes "").isNone

-- Unregistered errors do not classify. In particular the old broad strings the
-- current oracle accepts must never become an identity by themselves.
#guard (classifyWith sampleRoutes "InvalidBlock").isNone
#guard (classifyWith sampleRoutes "InvalidBlock : some detail").isNone
#guard (classifyWith sampleRoutes "InvalidTransaction").isNone
#guard (classifyWith sampleRoutes "DecodingError : unexpected list length").isNone
#guard (classifyWith sampleRoutes "EncodingError").isNone

-- The real route table is complete, but `classify` still recognizes nothing it
-- has not been told about.
#guard (classify "InvalidBlock").isNone
#guard (classify "InvalidTransaction").isNone
#guard (classify "InvalidTransaction : some detail").isNone
#guard (classify "RlpError : arbitrary malformed input").isNone
#guard (classify "InvalidGasLimitAbsolute").isNone

-- Each route key is a real producer tag and is registered once. Several
-- distinct structural/canonical RLP failures intentionally share the official
-- `RLP_STRUCTURES_ENCODING` identity, but a single actual tag still has only
-- one canonical reading.
def routedRlpTags : List String :=
  [ rlpFieldOverflow64Tag, rlpWithdrawalsNotReadTag, rlpStructureTag,
    rlpFixedWidthTag, rlpFieldOverflow256Tag, rlpLeadingZerosTag,
    rlpRoundTripTag ]

#guard actualRoutes.length = 39
#guard (actualRoutes.map Prod.fst).eraseDups.length = 39
#guard (actualRoutes.map Prod.snd).eraseDups.length = 35
#guard actualRoutes.all fun r =>
  blockExceptionTags.contains r.fst || routedRlpTags.contains r.fst ||
    transactionExceptionTags.contains r.fst
#guard routedRlpTags.length = 7
#guard routedRlpTags.eraseDups.length = 7
#guard routedRlpTags.all fun t => (actualRoutes.map Prod.fst).contains t
#guard transactionExceptionTags.length = 15
#guard transactionExceptionTags.eraseDups.length = 15
#guard transactionExceptionTags.all fun t => (actualRoutes.map Prod.fst).contains t

-- Coverage in the fixture-to-producer direction: every one of the 35
-- identities generated from the Prague corpus has at least one actual route.
-- A newly observed expected identity therefore cannot silently remain
-- unclassifiable.
#guard all.all fun e => actualRoutes.any fun r => r.snd == e

-- Coverage in the producer-to-fixture direction: each registered actual prefix
-- occurs once and classifies to exactly its declared identity, both bare and
-- with detail after the fixed delimiter.
#guard actualRoutes.all fun r =>
  (actualRoutes.filter fun r' => hasErrorType r.fst r'.fst).length = 1
#guard actualRoutes.all fun r =>
  (actualRoutes.filter fun r' =>
    hasErrorType s!"{r.fst} : producer detail" r'.fst).length = 1
#guard actualRoutes.all fun r =>
  classify r.fst == some r.snd &&
    classify s!"{r.fst} : producer detail" == some r.snd

-- Every block tag is either routed or knowingly unrouted -- a new rejection
-- reason cannot be added without landing in one list or the other.
#guard unroutedBlockTags.length = 4
#guard unroutedBlockTags.all fun t => blockExceptionTags.contains t
#guard blockExceptionTags.all fun t =>
  (actualRoutes.map Prod.fst).contains t || unroutedBlockTags.contains t
#guard unroutedBlockTags.all fun t => ¬ (actualRoutes.map Prod.fst).contains t

-- Every producer tag classifies to its own identity, bare and with detail.
#guard classify gasLimitTooBigTag == some blockGasLimitTooBig
#guard classify s!"{gasLimitTooBigTag} : gas limit = 9223372036854775808 ≥ \
  absolute maximum = 9223372036854775808" == some blockGasLimitTooBig
#guard classify gasLimitAdjustmentTag == some blockInvalidGasLimit
#guard classify s!"{gasLimitAdjustmentTag} : detail" == some blockInvalidGasLimit
#guard classify s!"{unknownParentTag} : detail" == some blockUnknownParent
#guard classify s!"{unknownParentZeroTag} : detail" == some blockUnknownParentZero
#guard classify s!"{gasUsedOverflowTag} : detail" == some blockGasUsedOverflow
#guard classify s!"{gasUsedMismatchTag} : detail" == some blockInvalidGasUsed
#guard classify s!"{ommersOverParisTag} : detail"
  == some blockImportImpossibleUnclesOverParis
#guard classify s!"{difficultyOverParisTag} : detail"
  == some blockImportImpossibleDifficultyOverParis
#guard classify s!"{stateRootTag} : detail" == some blockInvalidStateRoot

-- Every transaction producer reaches its exact official identity. The full
-- route-table checks above cover all fifteen; these representatives pin the
-- distinctions that previously shared broad strings.
#guard classify s!"{intrinsicGasTooLowTag} : detail" == some txIntrinsicGasTooLow
#guard classify s!"{nonceIsMaxTag} : detail" == some txNonceIsMax
#guard classify s!"{nonceMismatchTooLowTag} : detail" == some txNonceMismatchTooLow
#guard classify s!"{nonceMismatchTooHighTag} : detail" == some txNonceMismatchTooHigh
#guard classify s!"{gasPriceProductOverflowTag} : detail"
  == some txGasLimitPriceProductOverflow
#guard classify s!"{type3ZeroBlobsTag} : detail" == some txType3TxZeroBlobs
#guard classify s!"{type3BlobCountExceededTag} : detail"
  == some txType3TxBlobCountExceeded
#guard classify s!"{type3ContractCreationTag} : detail"
  == some txType3TxContractCreation
#guard classify s!"{type3InvalidBlobVersionedHashTag} : detail"
  == some txType3TxInvalidBlobVersionedHash

-- The pairs the fixtures insist are different reasons really do land on
-- different identities. These are the distinctions the whole step exists for:
-- an out-of-range gas limit is not a gas limit that drifted from its parent,
-- a header claiming more gas than it allows is not a header whose claim
-- disagrees with execution, and a zero parent hash is not an unknown one.
#guard classify gasLimitTooBigTag != classify gasLimitAdjustmentTag
#guard classify gasUsedOverflowTag != classify gasUsedMismatchTag
#guard classify unknownParentTag != classify unknownParentZeroTag
#guard classify nonceMismatchTooLowTag != classify nonceMismatchTooHighTag
#guard classify intrinsicGasTooLowTag != classify gasAllowanceExceededTag

-- The knowingly unrouted rules classify to nothing, so a block rejected for one
-- of them fails loudly instead of borrowing a neighbouring identity.
#guard unroutedBlockTags.all fun t => (classify t).isNone
#guard unroutedBlockTags.all fun t => (classify s!"{t} : detail").isNone

-- Strict RLP failures are routed, but broad legacy decoder categories remain
-- unclassifiable.
#guard classify rlpStructureTag == some blockRlpStructuresEncoding
#guard classify rlpFieldOverflow64Tag == some blockRlpInvalidFieldOverflow64
#guard (classify "DecodingError").isNone
#guard (classify "EncodingError").isNone

-- The matcher is set membership on the one classified identity -- never
-- "some failure occurred". Shown against the synthetic table so the semantics
-- are pinned before `actualRoutes` is filled in.
private def matchesWith (routes : List ActualRoute)
  (expected : List FixtureException) (actual : String) : Bool :=
  match classifyWith routes actual with
  | none => false
  | some a => expected.contains a

#guard matchesWith sampleRoutes [blockGasLimitTooBig] "InvalidGasLimitAbsolute"
#guard matchesWith sampleRoutes [blockInvalidGasLimit, blockGasLimitTooBig]
  "InvalidGasLimitAbsolute : detail"
-- The right kind of failure, but not the expected identity: still a failure.
#guard ¬ matchesWith sampleRoutes [blockInvalidGasLimit] "InvalidGasLimitAbsolute"
-- An unclassifiable error never matches, no matter how broad the expected set.
#guard ¬ matchesWith sampleRoutes all "InvalidBlock"
#guard ¬ matchesWith sampleRoutes all "InvalidBlock : gas limit is wrong"
-- An empty expected set matches nothing; `parseExpectation` cannot produce one.
#guard ¬ matchesWith sampleRoutes [] "InvalidGasLimitAbsolute"

-- The real route table, end to end. An unregistered error still matches
-- nothing, however broad the expected set.
#guard ¬ matchesSet all "InvalidGasLimitAbsolute"
#guard ¬ matchesSet all "InvalidBlock : gas limit is wrong"

-- The `GasLimitHigherThan2p63m1` case, from producer to verdict: the real error
-- text `checkGasLimit` raises for that fixture's numbers, matched against the
-- expectation string the fixture actually carries.
#guard matchesSet [blockGasLimitTooBig]
  s!"{gasLimitTooBigTag} : gas limit = 9223372036854775808 ≥ \
     absolute maximum = 9223372036854775808"
#guard
  (matchesExpectation "BlockException.GASLIMIT_TOO_BIG"
    s!"{gasLimitTooBigTag} : gas limit = 9223372036854775808 ≥ \
       absolute maximum = 9223372036854775808").toOption
  == some blockGasLimitTooBig
-- The same rejection against the *adjustment* expectation is still a failure:
-- the block was rejected, but not for the reason the fixture names.
#guard (matchesExpectation "BlockException.INVALID_GASLIMIT"
  s!"{gasLimitTooBigTag} : detail").toOption.isNone

-- `matchesExpectation` fails closed on every channel: unknown expected token,
-- unknown actual error, and a classified-but-unexpected identity.
#guard (matchesExpectation "NotAnIdentity" "InvalidGasLimitAbsolute").toOption.isNone
#guard (matchesExpectation "BlockException.GASLIMIT_TOO_BIG" "InvalidBlock").toOption.isNone
#guard (matchesExpectation "BlockException.GASLIMIT_TOO_BIG" "").toOption.isNone
