-- Check/Machine.lean : executable checks of `Jaune/Machine.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/Machine.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.Machine

namespace Jaune

open Jaune _root_.Nat

-- Regression for the key-sensitive hash above. These four keys share one
-- address but each sets a different 64-bit limb, so the old address-only hash
-- collided them into a single bucket.
private def keyHashRegressionKeys : List (Address × U256) :=
  let a : Address := (0x1234 : Address)
  [ (a, Nat.toU256 1),
    (a, Nat.toU256 (2 ^ 64)),
    (a, Nat.toU256 (2 ^ 128)),
    (a, Nat.toU256 (2 ^ 192)) ]

-- distinct keys at one address must not all hash to the same value
#guard (keyHashRegressionKeys.map (fun p => hash p)).eraseDups.length = 4

-- a KeySet built from many same-address keys must still find each key
#guard
  let s : KeySet := .ofList keyHashRegressionKeys
  s.size = 4 && keyHashRegressionKeys.all s.contains

def transactionExceptionTags : List String :=
  [ gasPriceProductOverflowTag, gasAllowanceExceededTag,
    initcodeSizeExceededTag, insufficientAccountFundsTag,
    insufficientMaxFeePerGasTag, insufficientMaxFeePerBlobGasTag,
    transactionGasLimitExceededTag,
    intrinsicGasTooLowTag, invalidChainIdTag, nonceIsMaxTag, nonceMismatchTooHighTag,
    nonceMismatchTooLowTag,
    priorityGreaterThanMaxFeeTag, senderNotEoaTag,
    type3BlobCountExceededTag, type3BlobCountLimitExceededTag,
    type3ContractCreationTag,
    type3InvalidBlobVersionedHashTag, type3ZeroBlobsTag,
    type4ContractCreationTag, emptyAuthorizationListTag, typePreForkTag ]

#guard transactionExceptionTags.length = 22
#guard transactionExceptionTags.eraseDups.length = 22
#guard transactionExceptionTags.all fun t =>
  (transactionExceptionTags.filter fun u => t.isPrefixOf u).length = 1

/-- Every block-rejection tag. The single source of truth for the distinctness
checks and the whole-list constructor/tag pin. -/
def blockExceptionTags : List String :=
  [ gasLimitTooBigTag, gasLimitAdjustmentTag, gasUsedOverflowTag,
    gasUsedMismatchTag, timestampOlderThanParentTag, blockNumberTag,
    baseFeePerGasTag, difficultyOverParisTag, ommersOverParisTag,
    invalidDifficultyTag, invalidOmmersTag,
    extraDataTooBigTag, unknownParentTag, unknownParentZeroTag,
    stateRootTag, transactionsRootTag, receiptsRootTag, logBloomTag,
    withdrawalsRootTag, headerNonceTag, excessBlobGasTag, blobGasUsedTag,
    requestsHashTag, depositEventLayoutTag, systemContractCallFailedTag,
    systemContractEmptyTag,
    blockRlpSizeExceededTag, headerFieldPresenceTag, blockAccessListHashTag,
    blockAccessListContentTag, blockAccessListFormatTag,
    blockAccessListGasLimitTag ]

-- The tags are distinct, and none is a prefix of another, so no rendered
-- reason can be read as another by any " : "-delimited reader -- and none is
-- the broad category the vocabulary replaced.
#guard blockExceptionTags.length = 32
#guard blockExceptionTags.eraseDups.length = 32
#guard blockExceptionTags.all fun t =>
  (blockExceptionTags.filter fun u => t.isPrefixOf u).length = 1
#guard blockExceptionTags.all fun t => t ≠ "InvalidBlock"

-- Golden guards, one representative per renderer constructor. Each pins the
-- exact rendered bytes of a message this executable emits today.
#guard DecodeError.all.map DecodeError.tag
  = [ "RlpStructureError", "RlpFixedWidthError", "RlpFieldOverflow64Error",
      "RlpFieldOverflow256Error", "RlpLeadingZerosError",
      "RlpWithdrawalsNotReadError", "RlpRoundTripError", "RlpHeaderWidthError" ]
#guard DecodeError.all.length = 8
#guard DecodeError.render (.rlpStructure (.text "withdrawals : expected a list"))
  = "RlpStructureError : withdrawals : expected a list"
#guard DecodeError.render (.fixedWidth (.text "root must be exactly 32 bytes, but is 31"))
  = "RlpFixedWidthError : root must be exactly 32 bytes, but is 31"
#guard DecodeError.render (.fieldOverflow64 .none) = "RlpFieldOverflow64Error"
#guard DecodeError.render (.fieldOverflow256 .none) = "RlpFieldOverflow256Error"
#guard DecodeError.render (.leadingZeros .none) = "RlpLeadingZerosError"
#guard DecodeError.render (.withdrawalsNotRead .none) = "RlpWithdrawalsNotReadError"
#guard DecodeError.render (.roundTrip .none) = "RlpRoundTripError"
#guard DecodeError.render (.headerWidth .none) = "RlpHeaderWidthError"

#guard ExceptionalHalt.all.map ExceptionalHalt.tag
  = [ "StackUnderflowError", "StackOverflowError", "OutOfGasError",
      "ModexpInputLimitExceeded", "InvalidOpcode", "InvalidJumpDestError",
      "StackDepthLimitError", "WriteInStaticContext", "OutOfBoundsRead",
      "InvalidParameter", "InvalidContractPrefix", "AddressCollision",
      "KZGProofError" ]
#guard ExceptionalHalt.all.length = 13
#guard ExceptionalHalt.all.eraseDups.length = 13
#guard ExceptionalHalt.render (.outOfGas .none) = "OutOfGasError"
#guard ExceptionalHalt.render (.invalidParameter (.text "invalid field element"))
  = "InvalidParameter : invalid field element"
#guard ExceptionalHalt.render (.writeInStaticContext (.text "SSTORE"))
  = "WriteInStaticContext : SSTORE"

#guard CryptoError.render (.invalidSignature .none) = "InvalidSignatureError"
#guard CryptoError.render (.invalidSignature (.text "bad s"))
  = "InvalidSignatureError : bad s"
#guard CryptoError.render (.pointCompression .none) = "bCompress failed"
#guard CryptoError.render (.value .none) = "ValueError"

#guard InternalError.render (.assertion .none) = "AssertionError"
#guard InternalError.render (.invariant (.text "refund counter is negative"))
  = "ERROR : refund counter is negative"
#guard InternalError.render (.invariant (.text "block hashes is empty"))
  = "ERROR : block hashes is empty"

#guard EvmError.render .revert = "Revert"
#guard EvmError.render (.halt (.stackUnderflow .none)) = "StackUnderflowError"
#guard EvmError.render (.crypto (.value .none)) = "ValueError"
#guard EvmError.render (.internal (.assertion .none)) = "AssertionError"

#guard SettledHalt.render .revert = "Revert"
#guard SettledHalt.render (.halt (.outOfGas .none)) = "OutOfGasError"
#guard SettledHalt.render (.halt (.invalidJumpDest .none)) = "InvalidJumpDestError"
#guard SettledHalt.render (.halt (.addressCollision .none)) = "AddressCollision"

-- The eight decode tags the typed reasons render under are exactly the eight
-- the strict decoders emit today, in the order the vocabulary declares them.
#guard DecodeError.all.map DecodeError.tag
  = [ rlpStructureTag, rlpFixedWidthTag, rlpFieldOverflow64Tag,
      rlpFieldOverflow256Tag, rlpLeadingZerosTag, rlpWithdrawalsNotReadTag,
      rlpRoundTripTag, rlpHeaderWidthTag ]

-- The EIP-8024 decode tables at every boundary the jump-destination argument
-- depends on (goal C, Appendix D), against the pinned `decode_single` and
-- `decode_pair`.
#guard decodeSingle 0x00 = some 145
#guard decodeSingle 0x5A = some 235
#guard decodeSingle 0x80 = some 17
#guard decodeSingle 0xFF = some 144
#guard decodeSingle 0x5B = none
#guard decodeSingle 0x5F = none
#guard decodeSingle 0x60 = none
#guard decodeSingle 0x7F = none
#guard decodePair 0x00 = some (9, 16)
#guard decodePair 0x51 = some (14, 15)
#guard decodePair 0x80 = some (1, 16)
#guard decodePair 0xFF = some (1, 22)
#guard decodePair 0x52 = none
#guard decodePair 0x5B = none
#guard decodePair 0x7F = none
-- Every accepted single decodes into `17 ≤ n ≤ 235`; every accepted pair into
-- `1 ≤ n ≤ 14` and `n < m ≤ 30 - n`; the forbidden ranges are exactly
-- `0x5B–0x7F` and `0x52–0x7F`, and both contain `JUMPDEST` and `PUSH1`–`PUSH32`.
#guard (List.range 256).all fun x =>
  match decodeSingle x.toUInt8 with
  | none => 0x5B ≤ x ∧ x ≤ 0x7F
  | some n => (x < 0x5B ∨ 0x80 ≤ x) ∧ 17 ≤ n ∧ n ≤ 235
#guard (List.range 256).all fun x =>
  match decodePair x.toUInt8 with
  | none => 0x52 ≤ x ∧ x ≤ 0x7F
  | some (n, m) => (x < 0x52 ∨ 0x80 ≤ x) ∧ 1 ≤ n ∧ n ≤ 14 ∧ n < m ∧ m ≤ 30 - n
#guard (decodeSingle 0x5B).isNone ∧ (decodePair 0x5B).isNone -- JUMPDEST
#guard (List.range' 0x60 32).all fun x =>
  (decodeSingle x.toUInt8).isNone ∧ (decodePair x.toUInt8).isNone -- PUSH1–PUSH32
-- Sizing and the zero-filled immediate, fork-independently.
#guard ByteArray.getOp ⟨#[0xE6, 0x80]⟩ 0 matches some (.next (.dupn 0x80))
#guard ByteArray.getOp ⟨#[0xE7, 0x00]⟩ 0 matches some (.next (.swapn 0x00))
#guard ByteArray.getOp ⟨#[0xE8, 0xFF]⟩ 0 matches some (.next (.exchange 0xFF))
#guard ByteArray.getOp ⟨#[0xE6]⟩ 0 matches some (.next (.dupn 0x00))
#guard ByteArray.getOp ⟨#[0x4B]⟩ 0 matches some (.next (.plain .slotnum))

-- Reference points computed from the pinned EELS `taylor_exponential`
-- (execution-specs 4198b9c5…, byte-identical at the current-mainnet source
-- commit 87aba1a3…). The committed differential grid is
-- scripts/vectors/fake-exp.json, checked by scripts/check-fake-exp.sh.
#guard fakeExponential 1 0 5007716 = 1                    -- numerator zero
#guard fakeExponential 1 1 5007716 = 1
#guard fakeExponential 1 5007715 5007716 = 2
#guard fakeExponential 1 5007716 5007716 = 2              -- e^1
#guard fakeExponential 1 (3 * 5007716) 5007716 = 20       -- e^3
#guard fakeExponential 1 (10 * 5007716) 5007716 = 22026   -- e^10
#guard fakeExponential 2 5 1 = 287                        -- 2e^5
#guard fakeExponential 1 50 1 = 5184612586559446279969    -- e^50
-- The maximum *feasible* corpus excess, 0xe760000 = 1851 blobs' worth of gas,
-- against all three canonical fraction values (Prague and Osaka share one).
#guard fakeExponential 1 0xe760000 5007716 = 1098342643171911460576
#guard fakeExponential 1 0xe760000 8346193 = 4211562125831
#guard fakeExponential 1 0xe760000 11684671 = 1041019391

-- Kernel reduction of both instances (a `rw`-built instance fails this).
example : decide ({ Account.nil with balance := 1 } = .nil) = false ∧
    decide (Account.nil = .nil) = true ∧ decide (Storage.empty = .empty) = true := by
  decide +kernel

#guard transferTopic = Bytes.keccak "Transfer(address,address,uint256)".toUTF8.toList

#guard List.exchange [1, 2, 3, 4] 1 3 = some [1, 4, 3, 2]
#guard List.exchange [1, 2, 3, 4] 0 4 = none
#guard List.exchange ([] : List Nat) 0 0 = none

-- Regression for the transaction-scoped `origState` reset (finding 3.8). Slot
-- `(a, k)` already holds a nonzero value in the block prestate. The first
-- transaction sees that prestate value as its original value and overwrites the
-- slot; the second must then see the *first transaction's output* -- its own
-- input -- as the original value. Reusing the block prestate here is what made
-- `SSTORE` charge a dirty-update 100 rather than a clean-update 2900, the
-- 2,800-gas deficit of `extcodehashEmptySuicide`.
private def origStateRegressionOrigVals : U256 × U256 :=
  let a : Address := (0x5678 : Address)
  let k : U256 := Nat.toU256 7
  let prestate : State := State.setStorVal .empty a k (Nat.toU256 11)
  let benv0 : Benv := {(default : Benv) with state := prestate}
  -- transaction 1: open the boundary, read the original value, write the slot
  let benv1 : Benv := benv0.beginTransaction
  let orig1 : U256 := (benv1.stat.origState.get a).storage.get k
  let benv1 : Benv := benv1.setStorVal a k (Nat.toU256 22)
  -- transaction 2: open the boundary, read the original value
  let benv2 : Benv := benv1.beginTransaction
  let orig2 : U256 := (benv2.stat.origState.get a).storage.get k
  ⟨orig1, orig2⟩

#guard origStateRegressionOrigVals = ⟨Nat.toU256 11, Nat.toU256 22⟩

-- The same slot, with the boundary opened only once per block, is the defect:
-- the second transaction would have kept reading the block prestate value 11.
#guard origStateRegressionOrigVals.2 ≠ origStateRegressionOrigVals.1

-- EIP-7939 `CLZ` guards.

-- The counted quantity is `256 - x.bit_length()`, so every limb boundary and
-- both extremes are pinned rather than left to the fixture corpus.
#guard U256.leadingZeros (Nat.toU256 0) = 256
#guard U256.leadingZeros (Nat.toU256 1) = 255
#guard U256.leadingZeros (Nat.toU256 2) = 254
#guard U256.leadingZeros (Nat.toU256 3) = 254
#guard U256.leadingZeros (Nat.toU256 255) = 248
#guard U256.leadingZeros (Nat.toU256 256) = 247
#guard U256.leadingZeros (Nat.toU256 (2 ^ 63)) = 192
#guard U256.leadingZeros (Nat.toU256 (2 ^ 64)) = 191
#guard U256.leadingZeros (Nat.toU256 (2 ^ 127)) = 128
#guard U256.leadingZeros (Nat.toU256 (2 ^ 128)) = 127
#guard U256.leadingZeros (Nat.toU256 (2 ^ 191)) = 64
#guard U256.leadingZeros (Nat.toU256 (2 ^ 192)) = 63
#guard U256.leadingZeros (Nat.toU256 (2 ^ 255)) = 0
#guard U256.leadingZeros U256.max = 0
-- A power of two and the all-ones word below it are the two words with the
-- same bit length, so they must count the same number of leading zeros.
#guard (List.range 256).all
  (fun n => U256.leadingZeros (Nat.toU256 (2 ^ n)) = 255 - n)
#guard (List.range 256).all
  (fun n => U256.leadingZeros (Nat.toU256 (2 ^ (n + 1) - 1)) = 255 - n)

private def guardSevmAt (fork : Fork) : Sevm :=
  { (default : Sevm) with
    benvStat := { (default : BenvStat) with fork := fork } }

private def guardClz (fork : Fork) (gasLeft : Nat) (stack : List U256) :
    Execution :=
  PlainOp.runCore 0 (((default : Devm).withGasLeft gasLeft).withStack stack)
    (guardSevmAt fork) .clz

private def guardClzErr (e : Execution) : String :=
  match e with
  | .error ⟨err, _⟩ => err.render
  | .ok _ => "unexpected success"

-- Under Osaka the opcode pops one word, charges `LOW`, and pushes the count.
#guard (guardClz .osaka 100 [0]).toOption.map Devm.stack
  = some [Nat.toU256 256]
#guard (guardClz .osaka 100 [1]).toOption.map Devm.stack
  = some [Nat.toU256 255]
#guard (guardClz .osaka 100 [U256.max]).toOption.map Devm.stack
  = some [Nat.toU256 0]
#guard (guardClz .osaka 100 [0]).toOption.map Devm.gasLeft = some (100 - Gas.low)
#guard Gas.low = 5

-- The rest of the stack is untouched and only the top word is consumed.
#guard (guardClz .osaka 100 [0, 7]).toOption.map Devm.stack
  = some [Nat.toU256 256, Nat.toU256 7]

-- Under Prague 0x1E is an unassigned byte, so it is an invalid instruction
-- whatever the stack and gas hold -- not a stack or gas failure, and not a
-- silent success.
#guard guardClzErr (guardClz .prague 100 [0]) = "InvalidOpcode"
#guard guardClzErr (guardClz .prague 100 []) = "InvalidOpcode"
#guard guardClzErr (guardClz .prague 0 [0]) = "InvalidOpcode"

-- EIP-7843 `SLOTNUM` (goal C, G3): under Amsterdam it charges `BASE` (2) and
-- pushes the block environment's slot number zero-extended to 256 bits; under
-- BPO2 the byte 0x4B is unassigned, so it is an invalid instruction whatever
-- the stack and gas hold.
private def guardSlotnum (fork : Fork) (slot : UInt64) (gasLeft : Nat)
    (stack : List U256) : Execution :=
  PlainOp.runCore 0 (((default : Devm).withGasLeft gasLeft).withStack stack)
    { guardSevmAt fork with
      benvStat := { (default : BenvStat) with fork := fork, slotNumber := slot } }
    .slotnum

#guard Gas.base = 2
#guard (guardSlotnum .amsterdam 12345 100 []).toOption.map Devm.stack
  = some [Nat.toU256 12345]
#guard (guardSlotnum .amsterdam 12345 100 []).toOption.map Devm.gasLeft
  = some (100 - Gas.base)
#guard (guardSlotnum .amsterdam (2 ^ 64 - 1) 100 [7]).toOption.map Devm.stack
  = some [Nat.toU256 (2 ^ 64 - 1), Nat.toU256 7]
#guard (guardSlotnum .amsterdam 0 2 []).toOption.map Devm.gasLeft = some 0
#guard guardClzErr (guardSlotnum .amsterdam 12345 1 []) = "OutOfGasError"
#guard guardClzErr (guardSlotnum .bpo2 12345 100 []) = "InvalidOpcode"
#guard guardClzErr (guardSlotnum .bpo2 12345 0 []) = "InvalidOpcode"
#guard guardClzErr (guardSlotnum .prague 0 100 [1]) = "InvalidOpcode"
-- `UInt8.toRinst` decodes 0x4B at every fork and round-trips its mnemonic.
#guard (0x4B : UInt8).toPlainOp matches some .slotnum
#guard ((0x4B : UInt8).toPlainOp.map PlainOp.toString) = some "SLOTNUM"
#guard (0x4B : UInt8).toOpClass matches .plain

-- Under Osaka the same two degenerate inputs reach the real failures instead.
#guard guardClzErr (guardClz .osaka 100 []) = "StackUnderflowError"
#guard guardClzErr (guardClz .osaka (Gas.low - 1) [0]) = "OutOfGasError"
#guard (guardClz .osaka Gas.low [0]).toOption.map Devm.gasLeft = some 0

/-! Design S1: the access shape at the account- and slot-access arms. Under the
flat (pre-EIP-2929) schedule each family charges its own fixed price and leaves
the accessed sets untouched; under EIP-2929 the same arm charges the cold price
and records the access. Each opcode gets a flat row and a Prague row on the same
input, so an arm that ignored the shape fails one of the two. -/
private def guardAccess (fork : Fork) (r : PlainOp) (stack : List U256) :
    Execution :=
  PlainOp.runCore 0 (((default : Devm).withGasLeft 10000).withStack stack)
    (guardSevmAt fork) r

private def guardAccessCharge (fork : Fork) (r : PlainOp) (stack : List U256) :
    Option Nat :=
  (guardAccess fork r stack).toOption.map (10000 - ·.gasLeft)

private def guardAccessWarmed (fork : Fork) (r : PlainOp) (x : U256) : Option Bool :=
  (guardAccess fork r [x]).toOption.map fun d =>
    decide (x.toAddress ∈ d.accessedAddresses) ||
      decide (((default : Sevm).currentTarget, x) ∈ d.accessedStorageKeys)

#guard guardAccessCharge .byzantium .balance [0x1000] = some 400
#guard guardAccessCharge .istanbul .balance [0x1000] = some 700
#guard guardAccessCharge .prague .balance [0x1000] = some 2600
#guard guardAccessCharge .byzantium .extcodesize [0x1000] = some 700
#guard guardAccessCharge .prague .extcodesize [0x1000] = some 2600
#guard guardAccessCharge .petersburg .extcodehash [0x1000] = some 400
#guard guardAccessCharge .istanbul .extcodehash [0x1000] = some 700
#guard guardAccessCharge .prague .extcodehash [0x1000] = some 2600
#guard guardAccessCharge .byzantium .sload [7] = some 200
#guard guardAccessCharge .istanbul .sload [7] = some 800
#guard guardAccessCharge .prague .sload [7] = some 2100
-- `EXTCODECOPY` of zero bytes: the access price alone (`[address, memory
-- offset, code offset, size]`, top first).
#guard guardAccessCharge .byzantium .extcodecopy [0x1000, 0, 0, 0] = some 700
#guard guardAccessCharge .prague .extcodecopy [0x1000, 0, 0, 0] = some 2600
-- The flat shape records nothing; EIP-2929 records the cold access.
#guard guardAccessWarmed .byzantium .balance 0x1000 = some false
#guard guardAccessWarmed .prague .balance 0x1000 = some true
#guard guardAccessWarmed .byzantium .extcodesize 0x1000 = some false
#guard guardAccessWarmed .prague .extcodesize 0x1000 = some true
#guard guardAccessWarmed .istanbul .extcodehash 0x1000 = some false
#guard guardAccessWarmed .prague .extcodehash 0x1000 = some true
#guard guardAccessWarmed .byzantium .sload 7 = some false
#guard guardAccessWarmed .prague .sload 7 = some true
-- S8 opcode availability (unit U5): each of the eleven `OpcodeRules` flags
-- gates its opcodes exactly as `clz` gates `CLZ`. Under rules without the fork
-- the byte is an invalid instruction whatever the stack and gas hold (not a
-- stack or gas failure, and no gas is charged); under Prague, where all eleven
-- flags are on, each runs its Prague body.
private def guardRinst (fork : Fork) (gasLeft : Nat) (stack : List U256)
    (r : PlainOp) : Execution :=
  PlainOp.runCore 0 (((default : Devm).withGasLeft gasLeft).withStack stack)
    (guardSevmAt fork) r

-- EIP-145 shifts: Byzantium has none of them.
#guard guardClzErr (guardRinst .byzantium 100 [1, 7] .shl) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 100 [1, 7] .shr) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 100 [1, 7] .sar) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 100 [] .shl) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 0 [1, 7] .shl) = "InvalidOpcode"
-- Under Prague each shifts: the top word is the shift amount.
#guard (guardRinst .prague 100 [1, 7] .shl).toOption.map Devm.stack
  = some [Nat.toU256 14]
#guard (guardRinst .prague 100 [1, 7] .shr).toOption.map Devm.stack
  = some [Nat.toU256 3]
#guard (guardRinst .prague 100 [1, 7] .sar).toOption.map Devm.stack
  = some [Nat.toU256 3]
#guard (guardRinst .prague 100 [1, 7] .shl).toOption.map Devm.gasLeft
  = some (100 - Gas.veryLow)
-- EIP-1052 `EXTCODEHASH`, EIP-1344 `CHAINID`, EIP-1884 `SELFBALANCE`,
-- EIP-3198 `BASEFEE`: Constantinople/Istanbul/London each add theirs, so
-- Byzantium has none and Prague has all.
#guard guardClzErr (guardRinst .byzantium 100000 [27] .extcodehash)
  = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 100 [] .chainid) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 100 [] .selfbalance) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 100 [] .basefee) = "InvalidOpcode"
#guard (guardRinst .prague 100000 [27] .extcodehash).toOption.map Devm.stack
  = some [Nat.toU256 0]
#guard (guardRinst .prague 100 [] .chainid).toOption.map Devm.stack
  = some [Nat.toU256 0]
#guard (guardRinst .prague 100 [] .selfbalance).toOption.map Devm.stack
  = some [Nat.toU256 0]
#guard (guardRinst .prague 100 [] .basefee).toOption.map Devm.stack
  = some [Nat.toU256 0]
-- EIP-4844 `BLOBHASH`/`BLOBBASEFEE`: Cancun only.
#guard guardClzErr (guardRinst .shanghai 100 [5] .blobhash) = "InvalidOpcode"
#guard guardClzErr (guardRinst .shanghai 100 [] .blobbasefee) = "InvalidOpcode"
#guard (guardRinst .prague 100 [5] .blobhash).toOption.map Devm.stack
  = some [Nat.toU256 0]
#guard (guardRinst .prague 100 [5] .blobhash).toOption.map Devm.gasLeft
  = some (100 - Gas.hashOpcodeGas)
#guard (guardRinst .prague 100 [] .blobbasefee).toOption.isSome = true
-- EIP-1153 transient storage and EIP-5656 `MCOPY`: Cancun only.
#guard guardClzErr (guardRinst .shanghai 100 [7] .tload) = "InvalidOpcode"
#guard guardClzErr (guardRinst .shanghai 100 [7, 8] .tstore) = "InvalidOpcode"
#guard guardClzErr (guardRinst .shanghai 100 [0, 0, 0] .mcopy) = "InvalidOpcode"
#guard (guardRinst .prague 100 [7] .tload).toOption.map Devm.stack
  = some [Nat.toU256 0]
#guard (guardRinst .prague 100 [7, 8] .tstore).toOption.map Devm.stack
  = some []
#guard (guardRinst .prague 100000 [0, 0, 32] .mcopy).toOption.isSome = true

-- P0.6 item 2: an out-of-range jump destination is *semantically* unjumpable.
-- The read is total and proof-indexed; out of range means `false`, never a
-- host-level partial read. In range, behaviour is unchanged.
#guard jumpable ⟨#[0x5B]⟩ 0 = true
#guard jumpable ⟨#[0x5B]⟩ 1 = false
#guard jumpable ⟨#[0x5B]⟩ (2 ^ 64) = false
#guard jumpable ⟨#[]⟩ 0 = false

example : jumpdestOk ⟨#[0x60, 0x5b, 0x5b]⟩ 1 = false := by decide +kernel

example : jumpdestOk ⟨#[0x60, 0x5b, 0x5b]⟩ 2 = true := by decide +kernel

example :
    [jumpdestOk ⟨#[0x60, 0x5b, 0x5b]⟩ 1,
      jumpdestOk ⟨#[0x60, 0x5b, 0x5b]⟩ 2] = [false, true] := by decide +kernel

-- Stack-access immediates are visited as ordinary bytes by the pinned walk.
-- JUMPDEST remains a destination; a following PUSH still skips its data.
#guard pinnedJumpDestsFrom ⟨#[0xE6, 0x5B]⟩ 0 = [1]
#guard pinnedJumpDestsFrom ⟨#[0xE8, 0x5B]⟩ 0 = [1]
#guard pinnedJumpDestsFrom ⟨#[0xE6, 0x80, 0x5B]⟩ 0 = [2]
#guard pinnedJumpDestsFrom ⟨#[0xE8, 0x00, 0x5B]⟩ 0 = [2]
-- 0x7F is PUSH32, which eats the
-- JUMPDEST behind it: the set is empty on both walks and for `jumpable`.
#guard pinnedJumpDestsFrom ⟨#[0xE7, 0x7F, 0x5B]⟩ 0 = []
#guard (List.range 3).filter (jumpable ⟨#[0xE7, 0x7F, 0x5B]⟩) = []
#guard pinnedJumpDestsFrom ⟨#[0xE7, 0x5B, 0x5B]⟩ 0 = [1, 2]
#guard pinnedJumpDestsFrom ⟨#[0x60, 0x5B, 0x5B]⟩ 0 = [2]
#guard pinnedJumpDestsFrom ⟨#[0xE6]⟩ 0 = []
#guard jumpable ⟨#[0xE6, 0x5B]⟩ 1 = true
#guard jumpable ⟨#[0xE8, 0x5B]⟩ 1 = true
#guard jumpable ⟨#[0xE6, 0x80, 0x5B]⟩ 2 = true
#guard jumpable ⟨#[0xE6, 0x80, 0x5B]⟩ 1 = false
#guard jumpable ⟨#[0xE8, 0x00, 0x5B]⟩ 2 = true
#guard jumpable ⟨#[0xE8, 0x00, 0x5B]⟩ 1 = false
#guard (List.range 3).filter (jumpable ⟨#[0xE7, 0x5B, 0x5B]⟩) = [1, 2]
#guard (List.range 3).filter (jumpable ⟨#[0x60, 0x5B, 0x5B]⟩) = [2]

/-! ### Site table: the account-access sites, at both metering shapes

G3 of `jaune-amsterdam-metering-v1`. For each site the interpreter reads a
repriced number at, one guard reproducing today's Prague number and one
reproducing the pinned target's Amsterdam number, both through the same
expression the arm evaluates. A repricing that reached only one of the two
shapes fails here.

`gasWarmAccess` is a global on both sides on purpose: no fork moves it, so the
warm rows say "still 100" rather than restating a rule that did not change. -/

private def guardAdr : Address := 0x1000
private def guardCold : AdrSet := .emptyWithCapacity
private def guardWarm : AdrSet := guardCold.insert guardAdr

private def pragueGas : GasSchedule := pragueRules.gas
private def amsterdamGas : GasSchedule := amsterdamRules.gas

-- `accessCost`, the shape `BALANCE`, `EXTCODE*` and the whole CALL family read.
#guard pragueGas.accessCost guardAdr guardCold = 2600
#guard amsterdamGas.accessCost guardAdr guardCold = 3000
#guard pragueGas.accessCost guardAdr guardWarm = 100
#guard amsterdamGas.accessCost guardAdr guardWarm = 100
-- and the sibling is the old function at Prague, definitionally.
#guard pragueGas.accessCost guardAdr guardCold = accessCost guardAdr guardCold
#guard pragueGas.accessCost guardAdr guardWarm = accessCost guardAdr guardWarm

-- `EXTCODESIZE` / `EXTCODECOPY`: the access half plus EIP-8038's code-reading
-- surcharge, which is `0` at Prague and 100 at Amsterdam.
#guard pragueGas.coldAccountAccess + pragueGas.codeReadSurcharge = 2600
#guard amsterdamGas.coldAccountAccess + amsterdamGas.codeReadSurcharge = 3100
#guard Gas.warmStorageReadCost + pragueGas.codeReadSurcharge = 100
#guard Gas.warmStorageReadCost + amsterdamGas.codeReadSurcharge = 200

-- `EXTCODEHASH` takes the repriced access and no surcharge.
#guard pragueGas.coldAccountAccess = 2600
#guard amsterdamGas.coldAccountAccess = 3000

-- The value-bearing call surcharge and the `CREATE`/`CREATE2` base, the other
-- two numbers goal A left on the globals for this goal to route.
#guard pragueGas.callValue = 9000
#guard amsterdamGas.callValue = 11300
#guard pragueGas.createAccess = 32000
#guard amsterdamGas.createAccess = 12000
#guard pragueGas.callValue = Gas.callValue
#guard pragueGas.createAccess = Gas.create

-- The stipend a value-bearing call hands its child is covered by the surcharge
-- at both shapes. This is the inequality the Sufficiency family needs, checked
-- as data here so a repricing that broke it fails before any proof does.
#guard Gas.callStipend < pragueGas.callValue
#guard Gas.callStipend < amsterdamGas.callValue

/-! ### Site table: `SSTORE` over the (original, current, new) lattice

The arm's two shapes charge different *terms*, not just different numbers, so
the rows below name the terms. Prague's are the globals it has always used;
Amsterdam's come from the two records and are computed by the sibling
definitions the arm calls, so a guard here is a guard on the code path.

`amsterdamState` is the vehicle's state-gas record; a vehicle without one would
not be a metering vehicle, and the `Option` match is discharged by `rfl`. -/

private def amsterdamState : StateGasRules := amsterdamStateGasRules

-- Prague: the whole cost of a first-time set of a zero slot, cold, is the
-- cold-load charge plus `gasStorageSet`; an update to a non-zero slot is the
-- cold-load charge plus the difference; a change to an already-warm slot that
-- is not the first this transaction costs the warm access alone.
#guard Gas.coldSloadCost + Gas.sstoreSetGas = 22100
#guard Gas.coldSloadCost + (Gas.sreset - Gas.coldSloadCost) = 5000
#guard Gas.warmStorageReadCost = 100

-- Amsterdam: access plus `STORAGE_WRITE` on the slot's first change, and
-- nothing but the access otherwise. EIP-8038 re-derives the lattice above as
-- exactly these two terms.
#guard sstoreAmsterdamGasCost amsterdamState 1 0 0 true = 2100 + 10000
#guard sstoreAmsterdamGasCost amsterdamState 1 0 0 false = 100 + 10000
#guard sstoreAmsterdamGasCost amsterdamState 2 1 1 true = 2100 + 10000
#guard sstoreAmsterdamGasCost amsterdamState 2 1 1 false = 100 + 10000
-- current ≠ original: the write was already paid for this transaction.
#guard sstoreAmsterdamGasCost amsterdamState 3 1 2 true = 2100
#guard sstoreAmsterdamGasCost amsterdamState 3 1 2 false = 100
-- new = current: no change at all, so no write either.
#guard sstoreAmsterdamGasCost amsterdamState 1 1 1 true = 2100
#guard sstoreAmsterdamGasCost amsterdamState 1 1 1 false = 100

-- The state dimension: a first-time set of a *zero* slot creates state and
-- pays `STORAGE_SET`; nothing else does.
#guard sstoreAmsterdamStateGas amsterdamState 1 0 0 = 97920
#guard sstoreAmsterdamStateGas amsterdamState 2 1 1 = 0
#guard sstoreAmsterdamStateGas amsterdamState 3 1 2 = 0
#guard sstoreAmsterdamStateGas amsterdamState 0 0 0 = 0
-- and the same slot cleared again in the same transaction refills it.
#guard sstoreAmsterdamStateRefund amsterdamState 0 0 1 = 97920
#guard sstoreAmsterdamStateRefund amsterdamState 0 1 1 = 0
#guard sstoreAmsterdamStateRefund amsterdamState 1 0 0 = 0

-- Refunds. The clear refund is the one number both shapes take from
-- `GasSchedule`, at each fork's own value; the restore refund is
-- `gasStorageSet - gasWarmAccess` at Prague and `STORAGE_WRITE` at Amsterdam.
#guard sstoreNewRefundCounter pragueGas 0 1 1 0 = 4800
#guard sstoreAmsterdamRefundCounter amsterdamGas amsterdamState 0 1 1 0 = 11616
#guard sstoreNewRefundCounter pragueGas 1 1 0 0
  = -4800 + (5000 - 2100 - 100)
#guard sstoreAmsterdamRefundCounter amsterdamGas amsterdamState 1 1 0 0
  = -11616 + 10000
#guard sstoreNewRefundCounter pragueGas 0 0 1 0 = 20000 - 100
#guard sstoreAmsterdamRefundCounter amsterdamGas amsterdamState 0 0 1 0 = 10000
#guard sstoreNewRefundCounter pragueGas 1 1 1 0 = 0
#guard sstoreAmsterdamRefundCounter amsterdamGas amsterdamState 1 1 1 0 = 0

end Jaune

