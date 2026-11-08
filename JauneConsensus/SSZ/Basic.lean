import JauneConsensus.UInt
import JauneConsensus.SSZ.Merkle

/-!
# SSZ: basic types, bitfields, vectors and lists

Transcribed from `ssz/simple-serialize.md` (`consensus-specs` `v1.6.1`). One type class `Ssz`
carries, for each SSZ type, the four functions the specification defines on it:
`is_variable_size` (as `fixedSize?`), `serialize`, deserialization, and `hash_tree_root`.
Every type is implemented once; the runners and the spec layer share these instances.

Deserialization enforces the hardening the specification lists ("Deserialization": offsets out
of order or out of range, mismatching first offset, scope not aligned or with extra bytes, more
elements than a limit, a missing bitlist delimiter) plus the value checks of each basic type
(a boolean byte in `{0, 1}`, a bitvector with no bits set beyond its length) and the illegal
types (`Vector[T, 0]`, `Bitvector[0]`). Each failure is a typed `Reject.decode`.

Representations carry their SSZ invariants in their types: `SszVector α n` has exactly `n`
elements and `SszList α n` at most `n`, so `hash_tree_root` never meets the `merkleize` limit
error that the specification raises for oversized input.
-/

namespace JauneConsensus
open Jaune

/-- The SSZ functions of a type (`ssz/simple-serialize.md`). -/
class Ssz (α : Type) where
  /-- `none` iff the type is variable-size ("Variable-size and fixed-size"); otherwise the
  length of every serialization. -/
  fixedSize? : Option Nat
  /-- Basic types (`uintN`, `byte`, `boolean`) are packed into chunks by `pack`. -/
  isBasic : Bool := false
  /-- `serialize(value)` ("Serialization"). -/
  serialize : α → Bytes
  /-- Deserialization of a whole scope: the input is exactly the object's bytes. -/
  deserialize : Bytes → M α
  /-- `hash_tree_root(value)` ("Merkleization"). -/
  hashTreeRoot : α → B256

export Ssz (serialize deserialize hashTreeRoot)

/-- `is_variable_size`. -/
@[inline] def Ssz.isVariableSize (α : Type) [Ssz α] : Bool := (Ssz.fixedSize? α).isNone

private def decodeErr {α : Type} (e : DecodeError) : M α := throw (.decode e)

/-! ## Basic types -/

/-- `boolean` ("Serialization", `boolean`): `0x01` for `True`, `0x00` for `False`. Decoding
admits exactly those two bytes. -/
instance : Ssz Bool where
  fixedSize? := some 1
  isBasic := true
  serialize b := [if b then 1 else 0]
  deserialize
    | [b] => if b = 0 then pure false else if b = 1 then pure true else decodeErr (.boolean b)
    | bs => decodeErr (.length 1 bs.length)
  hashTreeRoot b := chunkOf [if b then 1 else 0]

/-- `byte`: 8-bit opaque data, serialized and hashed as `uint8`. -/
instance : Ssz UInt8 where
  fixedSize? := some 1
  isBasic := true
  serialize b := [b]
  deserialize
    | [b] => pure b
    | bs => decodeErr (.length 1 bs.length)
  hashTreeRoot b := chunkOf [b]

theorem leNat_lt : ∀ bs : Bytes, leNat bs < 2 ^ (8 * bs.length)
  | [] => by simp [leNat]
  | b :: bs => by
    have hb := b.toNat_lt
    have ih := leNat_lt bs
    show b.toNat + 256 * leNat bs < 2 ^ (8 * (bs.length + 1))
    rw [Nat.mul_succ, Nat.pow_add, show (2 : Nat) ^ 8 = 256 from rfl]
    omega

/-- `uint64` ("Serialization", `uintN`): `value.to_bytes(8, "little")`. -/
instance : Ssz U64 where
  fixedSize? := some 8
  isBasic := true
  serialize x := leBytes 8 x.toNat
  deserialize bs :=
    if h : bs.length = 8 then pure (U64.ofNatLt (leNat bs) (by have := leNat_lt bs; rw [h] at this; exact this))
    else decodeErr (.length 8 bs.length)
  hashTreeRoot x := chunkOf (leBytes 8 x.toNat)

/-- `uintN` for `N = 8 * n` ("Serialization", `uintN`): `value.to_bytes(n, "little")`. -/
instance {n : Nat} : Ssz (UIntN n) where
  fixedSize? := some n
  isBasic := true
  serialize x := leBytes n x.toNat
  deserialize bs :=
    if h : bs.length = n then pure ⟨leNat bs, h ▸ leNat_lt bs⟩ else decodeErr (.length n bs.length)
  hashTreeRoot x := chunkOf (leBytes n x.toNat)

/-! ## Offsets and composite serialization -/

/-- A part of a composite serialization: a fixed-size element in place, or a variable-size
element whose offset sits in the fixed part. -/
inductive Part where
  | fixed (b : Bytes)
  | var (b : Bytes)

/-- "Vectors, containers, progressive containers, lists, progressive lists": the fixed parts
(with `uint32` offsets interleaved for variable-size parts) followed by the variable parts.
The specification's assertion that the total length is below `2^32` holds for every value whose
lists respect their limits in the consensus types; the serialization itself is total. -/
def serializeParts (ps : List Part) : Bytes :=
  let fixedLen := ps.foldl (fun n p => n + match p with
    | .fixed b => b.length
    | .var _ => BYTES_PER_LENGTH_OFFSET) 0
  let rec go : List Part → Nat → List Bytes → List Bytes → Bytes
    | [], _, fixedAcc, varAcc => (fixedAcc.reverse ++ varAcc.reverse).flatten
    | .fixed b :: rest, off, fixedAcc, varAcc => go rest off (b :: fixedAcc) varAcc
    | .var b :: rest, off, fixedAcc, varAcc =>
      go rest (off + b.length) (leBytes BYTES_PER_LENGTH_OFFSET off :: fixedAcc) (b :: varAcc)
  go ps fixedLen [] []

/-- The parts of a homogeneous sequence. -/
@[inline] def seqParts {α : Type} [Ssz α] (xs : List α) : List Part :=
  match Ssz.fixedSize? α with
  | some _ => xs.map fun x => .fixed (serialize x)
  | none => xs.map fun x => .var (serialize x)

/-- Read the `uint32` offset at byte `pos`. -/
@[inline] def readOffset (bs : Bytes) (pos : Nat) : Nat := leNat ((bs.drop pos).take 4)

/-- Slice `[a, b)`. -/
@[inline] def slice (bs : Bytes) (a b : Nat) : Bytes := (bs.drop a).take (b - a)

/-- Check that `offsets` are non-decreasing and at most `scope`, then cut the variable parts:
element `i` spans `[offsets[i], offsets[i+1])` and the last one ends at `scope`. -/
def cutVariable (bs : Bytes) (scope : Nat) : List Nat → M (List Bytes)
  | [] => pure []
  | [o] => if o ≤ scope then pure [slice bs o scope] else decodeErr (.offset "offset beyond scope")
  | o :: o' :: rest => do
    if o' < o then decodeErr (.offset "offsets out of order")
    else
      let tl ← cutVariable bs scope (o' :: rest)
      pure (slice bs o o' :: tl)

/-- Deserialize a homogeneous sequence from a whole scope. `count? = some n` is a vector of
exactly `n` elements; `none` is a list of at most `limit` elements. -/
def deserializeSeq {α : Type} [Ssz α] (bs : Bytes) (count? : Option Nat) (limit : Nat) :
    M (Array α) := do
  let scope := bs.length
  match Ssz.fixedSize? α with
  | some size =>
    if size = 0 then decodeErr (.illegalType "zero-size element")
    else if scope % size ≠ 0 then decodeErr (.alignment size scope)
    else
      let count := scope / size
      match count? with
      | some n => if count ≠ n then decodeErr (.length (n * size) scope) else pure ()
      | none => if count > limit then decodeErr (.limit limit count) else pure ()
      let elems ← (splitEvery size count bs).mapM (deserialize (α := α))
      pure elems.toArray
  | none =>
    if scope = 0 then
      match count? with
      | some n => if n = 0 then pure #[] else decodeErr (.offset "empty scope for a vector")
      | none => pure #[]
    else if scope < BYTES_PER_LENGTH_OFFSET then decodeErr (.offset "scope shorter than an offset")
    else
      let first := readOffset bs 0
      if first % BYTES_PER_LENGTH_OFFSET ≠ 0 ∨ first = 0 then
        decodeErr (.offset "first offset not a positive multiple of the offset size")
      else if first > scope then decodeErr (.offset "first offset beyond scope")
      else
        let count := first / BYTES_PER_LENGTH_OFFSET
        match count? with
        | some n => if count ≠ n then decodeErr (.offset "first offset does not match the vector length") else pure ()
        | none => if count > limit then decodeErr (.limit limit count) else pure ()
        let offsets := (List.range count).map fun i => readOffset bs (BYTES_PER_LENGTH_OFFSET * i)
        let parts ← cutVariable bs scope offsets
        let elems ← parts.mapM (deserialize (α := α))
        pure elems.toArray

/-- `hash_tree_root` of a sequence: packed for basic elements, element roots otherwise, into a
tree sized for `chunkLimit` chunks. -/
def seqRootDepth {α : Type} [Ssz α] (xs : List α) (depth : Nat) : B256 :=
  if Ssz.isBasic α then merkleizeDepth (pack (xs.flatMap serialize)) depth
  else merkleizeDepth (xs.map hashTreeRoot) depth

/-- `chunk_count` of `Vector[T, N]` and `List[T, N]` ("Merkleization"): `(N * size_of(B) + 31)
// 32` for a basic `B`, and `N` for a composite element. -/
def seqChunkCount (α : Type) [Ssz α] (n : Nat) : Nat :=
  if Ssz.isBasic α then
    match Ssz.fixedSize? α with
    | some size => (n * size + 31) / 32
    | none => n
  else n

/-! ## Vectors and lists -/

/-- `Vector[T, N]`: exactly `N` elements. -/
structure SszVector (α : Type) (n : Nat) where
  toArray : Array α
  size_eq : toArray.size = n

/-- `List[T, N]`: at most `N` elements. -/
structure SszList (α : Type) (n : Nat) where
  toArray : Array α
  size_le : toArray.size ≤ n

theorem SszVector.ext {α : Type} {n : Nat} :
    ∀ {a b : SszVector α n}, a.toArray = b.toArray → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem SszList.ext {α : Type} {n : Nat} :
    ∀ {a b : SszList α n}, a.toArray = b.toArray → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance {α : Type} {n : Nat} [DecidableEq α] : DecidableEq (SszVector α n) := fun a b =>
  if h : a.toArray = b.toArray then isTrue (SszVector.ext h) else isFalse (fun e => h (e ▸ rfl))

instance {α : Type} {n : Nat} [DecidableEq α] : DecidableEq (SszList α n) := fun a b =>
  if h : a.toArray = b.toArray then isTrue (SszList.ext h) else isFalse (fun e => h (e ▸ rfl))

/-- `Vector[T, N]` ("Serialization" as a sequence; "Merkleization": `merkleize(pack(value))`
for basic `T`, `merkleize([hash_tree_root(e) for e in value])` otherwise). `N = 0` is an
illegal type and never decodes. -/
instance {α : Type} {n : Nat} [Ssz α] : Ssz (SszVector α n) where
  fixedSize? := (Ssz.fixedSize? α).map (n * ·)
  serialize v := serializeParts (seqParts v.toArray.toList)
  deserialize bs := do
    if n = 0 then decodeErr (.illegalType "Vector[T, 0]")
    else
      let xs ← deserializeSeq (α := α) bs (some n) n
      if h : xs.size = n then pure ⟨xs, h⟩
      else decodeErr (.length n xs.size)
  hashTreeRoot v := seqRootDepth v.toArray.toList (depthOf (seqChunkCount α n))

/-- `List[T, N]` ("Merkleization": `mix_in_length(merkleize(pack(value), limit=chunk_count),
len(value))` for basic `T`, and with element roots otherwise). -/
instance {α : Type} {n : Nat} [Ssz α] : Ssz (SszList α n) where
  fixedSize? := none
  serialize v := serializeParts (seqParts v.toArray.toList)
  deserialize bs := do
    let xs ← deserializeSeq (α := α) bs none n
    if h : xs.size ≤ n then pure ⟨xs, h⟩
    else decodeErr (.limit n xs.size)
  hashTreeRoot v :=
    mixInLength (seqRootDepth v.toArray.toList (depthOf (seqChunkCount α n))) v.toArray.size

/-! ## Bitfields -/

/-- The eight bits of a byte, least significant first. -/
def byteBits (b : UInt8) : List Bool :=
  (List.range 8).map fun i => (b >>> i.toUInt8) &&& 1 = 1

/-- Pack bits into bytes, bit `i` at position `i % 8` of byte `i / 8`; the last byte is
zero-padded (the `array[i // 8] |= value[i] << (i % 8)` loop). -/
def bitsToBytes (bits : List Bool) : Bytes :=
  let rec go : Nat → List Bool → Bytes
    | 0, _ => []
    | _ + 1, [] => []
    | fuel + 1, bs =>
      let byte := (bs.take 8).zipIdx.foldl
        (fun acc (b, i) => if b then acc ||| ((1 : UInt8) <<< i.toUInt8) else acc) 0
      byte :: go fuel (bs.drop 8)
  go bits.length bits

/-- Bits of a byte string, least significant bit of the first byte first. -/
def bytesToBits (bs : Bytes) : List Bool := bs.flatMap byteBits

/-- Bit length of a nonzero byte: the index of its highest set bit, plus one. -/
def byteBitLength (b : UInt8) : Nat := Nat.log2 b.toNat + 1

/-- `Bitvector[N]`: exactly `N` bits. -/
structure Bitvector (n : Nat) where
  bits : Array Bool
  size_eq : bits.size = n

/-- `Bitlist[N]`: at most `N` bits. -/
structure Bitlist (n : Nat) where
  bits : Array Bool
  size_le : bits.size ≤ n

theorem Bitvector.ext {n : Nat} : ∀ {a b : Bitvector n}, a.bits = b.bits → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem Bitlist.ext {n : Nat} : ∀ {a b : Bitlist n}, a.bits = b.bits → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance {n : Nat} : DecidableEq (Bitvector n) := fun a b =>
  if h : a.bits = b.bits then isTrue (Bitvector.ext h) else isFalse (fun e => h (e ▸ rfl))

instance {n : Nat} : DecidableEq (Bitlist n) := fun a b =>
  if h : a.bits = b.bits then isTrue (Bitlist.ext h) else isFalse (fun e => h (e ▸ rfl))

/-- `chunk_count` of `Bitvector[N]` and `Bitlist[N]`: `(N + 255) // 256`. -/
def bitsChunkCount (n : Nat) : Nat := (n + 255) / 256

/-- `Bitvector[N]` ("Serialization", `Bitvector[N]`; "Merkleization":
`merkleize(pack_bits(value), limit=chunk_count(type))`). Decoding requires exactly
`(N + 7) // 8` bytes and no bit set at or beyond index `N`; `N = 0` is illegal. -/
instance {n : Nat} : Ssz (Bitvector n) where
  fixedSize? := some ((n + 7) / 8)
  serialize v := bitsToBytes v.bits.toList
  deserialize bs :=
    if n = 0 then decodeErr (.illegalType "Bitvector[0]")
    else if bs.length ≠ (n + 7) / 8 then decodeErr (.length ((n + 7) / 8) bs.length)
    else
      let all := bytesToBits bs
      if (all.drop n).any id then decodeErr .padding
      else
        let bits := (all.take n).toArray
        if h : bits.size = n then pure ⟨bits, h⟩ else decodeErr (.length n bits.size)
  hashTreeRoot v := merkleizeDepth (pack (bitsToBytes v.bits.toList)) (depthOf (bitsChunkCount n))

/-- `Bitlist[N]` ("Serialization", `Bitlist[N]`: the bits followed by a delimiting `1` bit;
"Merkleization": `mix_in_length(merkleize(pack_bits(value), limit=chunk_count(type)),
len(value))`). Decoding requires a nonempty scope whose last byte is nonzero, and at most `N`
bits before the delimiter. -/
instance {n : Nat} : Ssz (Bitlist n) where
  fixedSize? := none
  serialize v := bitsToBytes (v.bits.toList ++ [true])
  deserialize bs :=
    match bs.getLast? with
    | none => decodeErr .delimiter
    | some last =>
      if last = 0 then decodeErr .delimiter
      else
        let len := 8 * (bs.length - 1) + (byteBitLength last - 1)
        if len > n then decodeErr (.limit n len)
        else
          let bits := ((bytesToBits bs).take len).toArray
          if h : bits.size ≤ n then pure ⟨bits, h⟩ else decodeErr (.limit n bits.size)
  hashTreeRoot v :=
    mixInLength (merkleizeDepth (pack (bitsToBytes v.bits.toList)) (depthOf (bitsChunkCount n)))
      v.bits.size

end JauneConsensus
