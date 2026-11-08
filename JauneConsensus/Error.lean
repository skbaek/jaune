/-!
# Typed rejection for the consensus layer

Every failure path of the Python specification (`ethereum/consensus-specs` `v1.6.1`) is a
value of `Reject` in the model: an `assert`, an index out of range, `uint64` overflow and
underflow, division by zero, a list limit, an SSZ decoding error, or a cryptographic check.
The consensus layer computes in `M := Except Reject`; there is no default read and no
wrapping arithmetic in the spec layer (goal `jaune-consensus-electra-fulu-v1`, outcome O5).

The `String` payloads are diagnostic site labels only. No semantic branch ever inspects them;
a caller that needs to distinguish failures matches on the constructor.
-/

namespace JauneConsensus

/-- Why an SSZ byte string failed to decode (`ssz/simple-serialize.md`, "Deserialization":
offsets out of order or out of range, scope not aligned or with extra bytes, more elements
than a limit allows, a missing bitlist delimiter, a non-boolean byte, an illegal type). -/
inductive DecodeError where
  /-- The scope has the wrong length for a fixed-size type. -/
  | length (expected actual : Nat)
  /-- The scope is not a whole number of fixed-size elements. -/
  | alignment (elemSize actual : Nat)
  /-- An offset is out of range, out of order, or the first offset does not match the fixed part. -/
  | offset (site : String)
  /-- More elements than the type's limit admits. -/
  | limit (limit actual : Nat)
  /-- A boolean byte other than `0x00` or `0x01`. -/
  | boolean (byte : UInt8)
  /-- A bitlist whose last byte is zero (no length-delimiting bit), or an empty bitlist scope. -/
  | delimiter
  /-- Bits set beyond the length of a bitvector. -/
  | padding
  /-- An illegal type (`ssz/simple-serialize.md`, "Illegal types"), for example `Vector[T, 0]`. -/
  | illegalType (site : String)
  /-- A union or compatible-union selector outside the type's options. -/
  | selector (sel : UInt8)
  deriving Repr, BEq, DecidableEq

/-- The typed rejection. Every pyspec failure maps to exactly one constructor. -/
inductive Reject where
  /-- A pyspec `assert` failed. -/
  | assert (site : String)
  /-- An index outside a sequence (Python `IndexError`). -/
  | index (site : String) (index size : Nat)
  /-- Typed unsigned arithmetic left its range upwards (remerkleable raises). -/
  | overflow (site : String)
  /-- Typed unsigned arithmetic left its range downwards (remerkleable raises). -/
  | underflow (site : String)
  /-- Division or modulus by zero (Python `ZeroDivisionError`). -/
  | divByZero (site : String)
  /-- A push or construction past a list limit, or `merkleize` input beyond its limit. -/
  | limit (site : String) (limit actual : Nat)
  /-- An SSZ byte string failed to decode. -/
  | decode (why : DecodeError)
  /-- A cryptographic check failed (invalid point, invalid signature encoding, ...). -/
  | crypto (site : String)
  deriving Repr, BEq

/-- The consensus-layer monad: a computation that either yields a value or rejects with a
typed reason. -/
abbrev M := Except Reject

/-- pyspec `assert cond`. -/
@[inline] def require (cond : Bool) (site : String) : M Unit :=
  if cond then pure () else throw (.assert site)

/-- A read at `i` of an array, rejecting with `Reject.index` when out of range (pyspec
`seq[i]`, which raises `IndexError`). -/
@[inline] def getAt {α : Type} (xs : Array α) (i : Nat) (site : String) : M α :=
  match xs[i]? with
  | some x => pure x
  | none => throw (.index site i xs.size)

end JauneConsensus
