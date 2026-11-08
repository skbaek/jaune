import Jaune.Types
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

/-- A decoding scope as an array, so offsets and slices are read by index (linear decoding;
`Bytes` is a list). -/
abbrev Scope := Array UInt8

/-- The bytes `[a, b)` of a scope (Python `bs[a:b]`). -/
@[inline] def slice (bs : Scope) (a b : Nat) : Bytes := (bs.extract a b).toList

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
  /-- `false` only for an absent fork-gated container field (`Gated false T`), which has no
  bytes and no Merkle leaf. -/
  present : Bool := true
  /-- Fast path: `deserialize (slice bs a b)`, which a type may read in place from the scope
  instead of through a list (`deserializeAt_eq`). Not part of the specification. -/
  deserializeAt : Scope → Nat → Nat → M α := fun bs a b => deserialize (slice bs a b)
  deserializeAt_eq : ∀ bs a b, deserializeAt bs a b = deserialize (slice bs a b) := by
    intros; rfl
  /-- Fast path: `acc ++ serialize x` built as an array (`serializeTo_eq`). Not part of the
  specification. -/
  serializeTo : α → Array UInt8 → Array UInt8 := fun x acc => acc ++ (serialize x).toArray
  serializeTo_eq : ∀ x acc, (serializeTo x acc).toList = acc.toList ++ serialize x := by
    intros; simp

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

private theorem uint8At_eq (e : Array UInt8) :
    (if h : e.size = 1 then pure e[0] else decodeErr (.length 1 e.size) : M UInt8) =
      (match e.toList with
       | [b] => pure b
       | bs => decodeErr (.length 1 bs.length)) := by
  rcases e with ⟨l⟩
  match l with
  | [] => rfl
  | [x] => rfl
  | _ :: _ :: _ => simp

/-- `byte`: 8-bit opaque data, serialized and hashed as `uint8`. -/
instance : Ssz UInt8 where
  fixedSize? := some 1
  isBasic := true
  serialize b := [b]
  deserialize
    | [b] => pure b
    | bs => decodeErr (.length 1 bs.length)
  hashTreeRoot b := chunkOf [b]
  deserializeAt bs a c :=
    let e := bs.extract a c
    if h : e.size = 1 then pure e[0] else decodeErr (.length 1 e.size)
  deserializeAt_eq bs a c := uint8At_eq (bs.extract a c)
  serializeTo b acc := acc.push b
  serializeTo_eq b acc := by simp

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

/-- `Bytes.toB256.go` over the bytes `[i, i + n)` of a scope, read by index (no list). -/
def b256GoAt (bs : Scope) : Nat → Nat → UInt64 → UInt64 → UInt64 → UInt64 → B256
  | 0, _, l3, l2, l1, l0 => ⟨⟨l3, l2⟩, ⟨l1, l0⟩⟩
  | n + 1, i, l3, l2, l1, l0 =>
    match bs[i]? with
    | some b => b256GoAt bs n (i + 1) ((l3 <<< 8) ||| (l2 >>> 56)) ((l2 <<< 8) ||| (l1 >>> 56))
        ((l1 <<< 8) ||| (l0 >>> 56)) ((l0 <<< 8) ||| b.toUInt64)
    | none => ⟨⟨l3, l2⟩, ⟨l1, l0⟩⟩

theorem b256GoAt_eq (bs : Scope) : ∀ (n i : Nat) (l3 l2 l1 l0 : UInt64),
    b256GoAt bs n i l3 l2 l1 l0 = Bytes.toB256.go l3 l2 l1 l0 ((bs.toList.drop i).take n)
  | 0, _, _, _, _, _ => by simp [b256GoAt, Bytes.toB256.go]; rfl
  | n + 1, i, l3, l2, l1, l0 => by
    unfold b256GoAt
    by_cases h : i < bs.size
    · rw [Array.getElem?_eq_getElem h, List.drop_eq_getElem_cons (by simpa using h)]
      simp only [List.take_succ_cons, Bytes.toB256.go, Array.getElem_toList]
      exact b256GoAt_eq bs n (i + 1) _ _ _ _
    · rw [Array.getElem?_eq_none (by omega), List.drop_eq_nil_of_le (by simpa using h)]
      simp [Bytes.toB256.go]; rfl

theorem slice_eq_take_drop (bs : Scope) (a c : Nat) :
    slice bs a c = (bs.toList.drop a).take (c - a) := by
  simp [slice, Array.toList_extract, List.extract]

theorem length_slice (bs : Scope) (a c : Nat) : (slice bs a c).length = min c bs.size - a := by
  simp [slice]; omega

/-- `Bytes32` / `Root` as a chunk: 32 bytes in order; its root is itself ("Merkleization":
`merkleize(pack(value))` of a 32-byte vector is the single chunk). -/
instance : Ssz B256 where
  fixedSize? := some 32
  serialize x := x.toBytes
  deserialize bs :=
    if bs.length = 32 then pure (Bytes.toB256 bs) else decodeErr (.length 32 bs.length)
  hashTreeRoot x := x
  deserializeAt bs a c :=
    if min c bs.size - a = 32 then pure (b256GoAt bs 32 a 0 0 0 0)
    else decodeErr (.length 32 (min c bs.size - a))
  deserializeAt_eq bs a c := by
    simp only [length_slice]
    split
    · rename_i h
      rw [b256GoAt_eq, Bytes.toB256, slice_eq_take_drop]
      have e : (bs.toList.drop a).take 32 = (bs.toList.drop a).take (c - a) := by
        rw [List.take_eq_take_iff]; simp; omega
      rw [e]
    · rfl

/-- `ExecutionAddress` (`Bytes20`) is Jaune's `Adr`: 20 bytes in order, hashed as one
right-padded chunk. -/
instance : Ssz Adr where
  fixedSize? := some 20
  serialize a := a.toBytes
  deserialize bs :=
    match Bytes.toAdr? bs with
    | some a => pure a
    | none => decodeErr (.length 20 bs.length)
  hashTreeRoot a := chunkOf a.toBytes

/-! ## Fork-gated fields -/

/-- A container field a fork introduced: `Gated true T` is `T`; `Gated false T` is an absent
field. For a concrete fork the gate reduces by `rfl`. -/
def Gated : Bool → Type → Type
  | true, α => α
  | false, _ => Unit

/-- The absent field: no bytes (`fixedSize? = some 0`), no Merkle leaf (`present = false`). -/
def absentSsz : Ssz Unit where
  fixedSize? := some 0
  serialize _ := []
  deserialize
    | [] => pure ()
    | bs => decodeErr (.length 0 bs.length)
  hashTreeRoot _ := zeroChunk
  present := false

instance instSszGated {α : Type} [h : Ssz α] : {c : Bool} → Ssz (Gated c α)
  | true => h
  | false => absentSsz

instance instBEqGated {α : Type} [h : BEq α] : {c : Bool} → BEq (Gated c α)
  | true => h
  | false => ⟨fun _ _ => true⟩

instance instDecidableEqGated {α : Type} [h : DecidableEq α] : {c : Bool} → DecidableEq (Gated c α)
  | true => h
  | false => fun a b => isTrue (by cases a; cases b; rfl)

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

/-- Read the `uint32` offset at byte `pos`. Callers check `pos + 4 ≤ bs.size` first. -/
@[inline] def readOffset (bs : Scope) (pos : Nat) : Nat := leNat (slice bs pos (pos + 4))

/-- Check that `offsets` are non-decreasing and at most `scope`, then cut the variable parts:
element `i` spans `[offsets[i], offsets[i+1])` and the last one ends at `scope`. -/
def cutVariable (bs : Scope) (scope : Nat) : List Nat → M (List Bytes)
  | [] => pure []
  | [o] => if o ≤ scope then pure [slice bs o scope] else decodeErr (.offset "offset beyond scope")
  | o :: o' :: rest => do
    if o' < o then decodeErr (.offset "offsets out of order")
    else
      let tl ← cutVariable bs scope (o' :: rest)
      pure (slice bs o o' :: tl)

/-- Deserialize a homogeneous sequence from a whole scope. `count? = some n` is a vector of
exactly `n` elements; `none` is a list of at most `limit` elements. -/
def deserializeSeqWith {α : Type} [Ssz α] (readFixed : Scope → Nat → Nat → M α) (bs : Bytes)
    (count? : Option Nat) (limit : Nat) : M (Array α) := do
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
      let arr : Scope := bs.toArray
      let elems ← (List.range count).mapM fun i => readFixed arr (size * i) (size * (i + 1))
      pure elems.toArray
  | none =>
    if scope = 0 then
      match count? with
      | some n => if n = 0 then pure #[] else decodeErr (.offset "empty scope for a vector")
      | none => pure #[]
    else if scope < BYTES_PER_LENGTH_OFFSET then decodeErr (.offset "scope shorter than an offset")
    else
      let arr : Scope := bs.toArray
      let first := readOffset arr 0
      if first % BYTES_PER_LENGTH_OFFSET ≠ 0 ∨ first = 0 then
        decodeErr (.offset "first offset not a positive multiple of the offset size")
      else if first > scope then decodeErr (.offset "first offset beyond scope")
      else
        let count := first / BYTES_PER_LENGTH_OFFSET
        match count? with
        | some n => if count ≠ n then decodeErr (.offset "first offset does not match the vector length") else pure ()
        | none => if count > limit then decodeErr (.limit limit count) else pure ()
        let offsets := (List.range count).map fun i => readOffset arr (BYTES_PER_LENGTH_OFFSET * i)
        let parts ← cutVariable arr scope offsets
        let elems ← parts.mapM (deserialize (α := α))
        pure elems.toArray

/-- Deserialize a homogeneous sequence from a whole scope (the specification's reading: each
fixed-size element from its slice). -/
def deserializeSeq {α : Type} [Ssz α] (bs : Bytes) (count? : Option Nat) (limit : Nat) :
    M (Array α) :=
  deserializeSeqWith (fun arr a b => deserialize (α := α) (slice arr a b)) bs count? limit

/-- `deserializeSeq` reading fixed-size elements in place (`Ssz.deserializeAt`). -/
def deserializeSeqFast {α : Type} [Ssz α] (bs : Bytes) (count? : Option Nat) (limit : Nat) :
    M (Array α) :=
  deserializeSeqWith (Ssz.deserializeAt (α := α)) bs count? limit

theorem deserializeSeqFast_eq {α : Type} [Ssz α] (bs : Bytes) (count? : Option Nat)
    (limit : Nat) : deserializeSeqFast (α := α) bs count? limit = deserializeSeq bs count? limit := by
  have : (Ssz.deserializeAt (α := α)) = fun arr a b => deserialize (α := α) (slice arr a b) := by
    funext arr a b; exact Ssz.deserializeAt_eq arr a b
  simp only [deserializeSeqFast, deserializeSeq, this]

theorem serializeParts_go_fixed {α : Type} (s : α → Bytes) : ∀ (xs : List α) (off : Nat)
    (facc : List Bytes),
    serializeParts.go (xs.map fun x => Part.fixed (s x)) off facc [] =
      (facc.reverse ++ xs.map s).flatten
  | [], _, _ => by simp [serializeParts.go]
  | x :: xs, off, facc => by
    simp only [List.map, serializeParts.go]
    rw [serializeParts_go_fixed s xs off (s x :: facc)]
    simp

/-- A sequence of fixed-size parts serializes to the concatenation of its parts. -/
theorem serializeParts_fixed {α : Type} (s : α → Bytes) (xs : List α) :
    serializeParts (xs.map fun x => Part.fixed (s x)) = xs.flatMap s := by
  simp [serializeParts, serializeParts_go_fixed, List.flatMap]

theorem foldl_serializeTo {α : Type} [Ssz α] : ∀ (xs : List α) (acc : Array UInt8),
    (xs.foldl (fun acc x => Ssz.serializeTo x acc) acc).toList = acc.toList ++ xs.flatMap serialize
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl]
    rw [foldl_serializeTo xs, Ssz.serializeTo_eq]
    simp

/-- The serialization of a homogeneous sequence, fixed-size elements appended into one array
(`Ssz.serializeTo`); equal to `serializeParts (seqParts xs)` (`serializeSeq_eq`). -/
def serializeSeq {α : Type} [Ssz α] (xs : Array α) : Bytes :=
  match Ssz.fixedSize? α with
  | some _ => (xs.foldl (fun acc x => Ssz.serializeTo x acc) #[]).toList
  | none => serializeParts (seqParts xs.toList)

theorem serializeSeq_eq {α : Type} [Ssz α] (xs : Array α) :
    serializeSeq xs = serializeParts (seqParts xs.toList) := by
  unfold serializeSeq seqParts
  split
  · rw [← Array.foldl_toList, foldl_serializeTo, serializeParts_fixed]; simp
  · rfl

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

instance {α : Type} {n : Nat} [BEq α] : BEq (SszVector α n) := ⟨fun a b => a.toArray == b.toArray⟩
instance {α : Type} {n : Nat} [BEq α] : BEq (SszList α n) := ⟨fun a b => a.toArray == b.toArray⟩

/-- `Vector[T, N]` ("Serialization" as a sequence; "Merkleization": `merkleize(pack(value))`
for basic `T`, `merkleize([hash_tree_root(e) for e in value])` otherwise). `N = 0` is an
illegal type and never decodes. -/
instance {α : Type} {n : Nat} [Ssz α] : Ssz (SszVector α n) where
  fixedSize? := (Ssz.fixedSize? α).map (n * ·)
  serialize v := serializeSeq v.toArray
  deserialize bs := do
    if n = 0 then decodeErr (.illegalType "Vector[T, 0]")
    else
      let xs ← deserializeSeqFast (α := α) bs (some n) n
      if h : xs.size = n then pure ⟨xs, h⟩
      else decodeErr (.length n xs.size)
  hashTreeRoot v := seqRootDepth v.toArray.toList (depthOf (seqChunkCount α n))

/-- `List[T, N]` ("Merkleization": `mix_in_length(merkleize(pack(value), limit=chunk_count),
len(value))` for basic `T`, and with element roots otherwise). -/
instance {α : Type} {n : Nat} [Ssz α] : Ssz (SszList α n) where
  fixedSize? := none
  serialize v := serializeSeq v.toArray
  deserialize bs := do
    let xs ← deserializeSeqFast (α := α) bs none n
    if h : xs.size ≤ n then pure ⟨xs, h⟩
    else decodeErr (.limit n xs.size)
  hashTreeRoot v :=
    mixInLength (seqRootDepth v.toArray.toList (depthOf (seqChunkCount α n))) v.toArray.size

/-- The vector instance's serialization and decoding are the specification's readings
(`serializeParts (seqParts ...)`, `deserializeSeq`); the instance runs the fast paths. -/
theorem SszVector.serialize_eq {α : Type} {n : Nat} [Ssz α] (v : SszVector α n) :
    serialize v = serializeParts (seqParts v.toArray.toList) := serializeSeq_eq _

theorem SszVector.deserialize_eq {α : Type} {n : Nat} [Ssz α] (bs : Bytes) :
    (deserialize bs : M (SszVector α n)) =
      (if n = 0 then throw (.decode (.illegalType "Vector[T, 0]"))
       else do
        let xs ← deserializeSeq (α := α) bs (some n) n
        if h : xs.size = n then pure ⟨xs, h⟩ else throw (.decode (.length n xs.size))) := by
  show (if n = 0 then _ else _) = _
  simp only [deserializeSeqFast_eq]; rfl

theorem SszList.serialize_eq {α : Type} {n : Nat} [Ssz α] (v : SszList α n) :
    serialize v = serializeParts (seqParts v.toArray.toList) := serializeSeq_eq _

theorem SszList.deserialize_eq {α : Type} {n : Nat} [Ssz α] (bs : Bytes) :
    (deserialize bs : M (SszList α n)) =
      (do
        let xs ← deserializeSeq (α := α) bs none n
        if h : xs.size ≤ n then pure ⟨xs, h⟩ else throw (.decode (.limit n xs.size))) := by
  show (do let xs ← deserializeSeqFast (α := α) bs none n; _) = _
  simp only [deserializeSeqFast_eq]; rfl

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
