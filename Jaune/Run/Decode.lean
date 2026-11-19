import Jaune.Transaction.Parts

/-!
# Unknown transaction type: an invalid block (goal `jaune-shape-and-names-v1`, W2-T, decision 16)

The typed-envelope decoder and the block-body slot decoder, staged. One arm changes: a byte-string
slot whose first byte is not an admitted transaction type -- any byte other than `0x01`-`0x04`,
including `0x00`, `0x05`-`0x7F` and `0x80`-`0xFF` (so the `0xC0`-`0xFE` range EELS reads as a
legacy list) -- is a block rejection, `transactionTypeNotSupported`, instead of the old
`.internal (.invariant _)` failure. EIP-2718 puts a type byte in `[0, 0x7f]` and makes a legacy
transaction the RLP list, not a byte string; geth's `decodeTyped` rejects every other byte with
`ErrTxTypeNotSupported`, and EELS raises `TransactionTypeError` (an `InvalidTransaction`, so the
block is invalid) for an unknown type byte. Every other slot decodes as before, through the old
decoder.

The reason reuses `TransactionValidationError.typePreFork`, carrying the type byte: EELS has one exception
for a type the fork does not know, whether a later fork defines it or none does
(`TransactionTypeError` in every fork's `decode_transaction`), and `typePreFork` is the
transaction reason Jaune already gives that exception for the types 1-4. Its fixture identity is
none (fail closed), as for every `typePreFork` outside 1-4: the fixture vocabulary has no
`TransactionException.TYPE_NOT_SUPPORTED` yet.

Staged under `Jaune.Staging` until the switch commit; the difference theorem is in
`Jaune.Bridge.G2a.Decode`.
-/

namespace Jaune.Staging

open Jaune

/-- The bytes the envelope decoder reads as a transaction type (EIP-2930, EIP-1559, EIP-4844,
EIP-7702). -/
def isTransactionType (x : UInt8) : Bool := x == 0x01 || x == 0x02 || x == 0x03 || x == 0x04

/-- The rejection for a typed slot whose first byte is no transaction type: `typePreFork`
carrying the byte (EEST `TransactionException.TYPE_NOT_SUPPORTED`, geth
`ErrTxTypeNotSupported`, EELS `TransactionTypeError`). -/
def transactionTypeNotSupported (type : UInt8) : TransitionError :=
  .transaction <| .typePreFork type.toNat <|
    .text s!"type-{type} transactions do not exist (EIP-2718), the block is invalid"

/-- The strict typed-envelope decoder. A slot whose first byte is a transaction type goes through
the old decoder (`Jaune.Bytes.toExceptTransaction`), unchanged; any other first byte is the block
rejection `transactionTypeNotSupported`. The guard sends every byte that reaches the old decoder's
internal-error arm to the rejection instead, so that arm is unreachable from here; the switch
commit, which may edit the old definition, replaces that arm by this rejection and drops the
guard. -/
def Bytes.toExceptTransaction : Bytes → Except TransitionError Transaction
  | [] => Jaune.Bytes.toExceptTransaction []
  | x :: xs =>
    if isTransactionType x then Jaune.Bytes.toExceptTransaction (x :: xs)
    else .error (transactionTypeNotSupported x)

/-- Decode a block-body transaction slot: the old `decodeTransaction` over the staged envelope
decoder. -/
def decodeTransaction (rules : ForkRules) : Bytes ⊕ Transaction → Except TransitionError Transaction
  | .inl xs => do
    let tx ← Bytes.toExceptTransaction xs
    checkTransactionTypeAdmitted rules tx
    .ok tx
  | .inr tx => .ok tx

end Jaune.Staging
