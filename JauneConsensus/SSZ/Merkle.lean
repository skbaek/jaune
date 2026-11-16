import Jaune.Hash
import JauneConsensus.Error
import JauneConsensus.Crypto.Sha256Pair

/-!
# SSZ Merkleization helpers

Transcribed from `ssz/simple-serialize.md` (`consensus-specs` `v1.6.1`), section
"Merkleization". The hash is SHA-256 (`specs/phase0/beacon-chain.md`, "Crypto": `hash` is
SHA-256), and the model uses Jaune's own `Bytes.sha256` (`Jaune/Hash.lean`, proved equal to
FIPS 180-4 in `Jaune/SHA256Spec.lean`). There is no second SHA-256.

A chunk (`Bytes32`) is a `B256` whose big-endian byte image `B256.toBytes` is the chunk's 32
bytes in order, so `Bytes.toB256` and `B256.toBytes` are the chunk codec.

Padding to `next_pow_of_two(limit)` is virtual: an absent right subtree at height `h` is the
precomputed root of `2^h` zero chunks (`zeroHash h`), so a list with limit `2^40` never
materializes its padding.
-/

namespace JauneConsensus
open Jaune

/-- `BYTES_PER_CHUNK` (`ssz/simple-serialize.md`, "Constants"). -/
def BYTES_PER_CHUNK : Nat := 32
/-- `BYTES_PER_LENGTH_OFFSET`. -/
def BYTES_PER_LENGTH_OFFSET : Nat := 4
/-- `BITS_PER_BYTE`. -/
def BITS_PER_BYTE : Nat := 8

/-- `hash(a + b)` for two chunks: SHA-256 of their 64-byte concatenation, computed by
`Crypto.hashPair` (one message block written into an array, then the constant padding block),
which is proved equal to Jaune's `Bytes.sha256` (`hashPair_eq`). -/
@[inline] def hashPair (a b : B256) : B256 := Crypto.hashPair a b

theorem hashPair_eq (a b : B256) : hashPair a b = Bytes.sha256 (a.toBytes ++ b.toBytes) :=
  Crypto.hashPair_eq a b

/-- The zero chunk `Bytes32()`. -/
def zeroChunk : B256 := Bytes.toB256 (List.replicate 32 0)

/-- Root of a complete binary tree of `2^h` zero chunks. -/
def zeroHash : Nat → B256
  | 0 => zeroChunk
  | h + 1 => let z := zeroHash h; hashPair z z

/-- `zeroHash h` for `h ≤ 64`, computed once. -/
def zeroHashTable : Array B256 := (List.range 65).toArray.map zeroHash

/-- `zeroHash h`, read from the table when it covers `h`. The fallback recomputes the same
value, so this equals `zeroHash h` for every `h` (`zeroHashAt_eq`). -/
@[inline] def zeroHashAt (h : Nat) : B256 :=
  match zeroHashTable[h]? with
  | some z => z
  | none => zeroHash h

theorem zeroHashAt_eq (h : Nat) : zeroHashAt h = zeroHash h := by
  unfold zeroHashAt
  split
  · rename_i z hz
    simp only [zeroHashTable, Array.getElem?_map, List.getElem?_toArray,
      Option.map_eq_some_iff] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.mp ha
    simp
  · rfl

/-- Little-endian encoding of `v mod 256^n` in `n` bytes (`int.to_bytes(n, "little")`). -/
def leBytes : Nat → Nat → Bytes
  | 0, _ => []
  | n + 1, v => (v % 256).toUInt8 :: leBytes n (v / 256)

/-- Little-endian decoding (`int.from_bytes(bs, "little")`). -/
def leNat : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

theorem length_leBytes (n v : Nat) : (leBytes n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [leBytes, ih]

/-- A chunk from at most 32 bytes, right-padded with zero bytes. -/
def chunkOf (bs : Bytes) : B256 := Bytes.toB256 (bs ++ List.replicate (32 - bs.length) 0)

/-- Split into `n`-byte pieces; the last piece may be shorter. Total by fuel. -/
def splitEvery (n : Nat) : Nat → Bytes → List Bytes
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, bs => bs.take n :: splitEvery n fuel (bs.drop n)

/-- `pack(values)` given the concatenated serialization: right-pad to a multiple of
`BYTES_PER_CHUNK` and partition into chunks. Empty input yields no chunks. -/
def pack (serialized : Bytes) : List B256 :=
  (splitEvery BYTES_PER_CHUNK serialized.length serialized).map chunkOf

/-- `next_pow_of_two(i)` as a depth: the least `d` with `i ≤ 2^d` (0 and 1 map to 0). -/
def depthOf (i : Nat) : Nat := if i ≤ 1 then 0 else Nat.log2 (i - 1) + 1

/-- One level up the tree: hash adjacent pairs, padding an odd tail with the zero root of the
current height. -/
def pairUp (z : B256) : List B256 → List B256
  | [] => []
  | [a] => [hashPair a z]
  | a :: b :: rest => hashPair a b :: pairUp z rest

/-- The hash of a pair, reusing a remembered `(a, b, hash a b)` when the pair repeats. -/
@[inline] def hashPairMemo (m : Option (B256 × B256 × B256)) (a b : B256) : B256 :=
  match m with
  | some (a', b', h') => if a' = a ∧ b' = b then h' else hashPair a b
  | none => hashPair a b

/-- A remembered pair is correct: its third component is the hash of the first two. -/
def MemoOk : Option (B256 × B256 × B256) → Prop
  | some (a, b, h) => h = hashPair a b
  | none => True

theorem hashPairMemo_eq {m : Option (B256 × B256 × B256)} (hm : MemoOk m) (a b : B256) :
    hashPairMemo m a b = hashPair a b := by
  match m, hm with
  | some (a', b', h'), hm =>
    simp only [hashPairMemo]
    split
    · rename_i h; obtain ⟨rfl, rfl⟩ := h; exact hm
    · rfl
  | none, _ => rfl

/-- `pairUp` as a tail-recursive loop that reuses the previous pair's hash when adjacent pairs
repeat (long runs of equal chunks, such as zero roots or unchanged RANDAO mixes, hash once per
run). Equal to `pairUp` (`pairUpFast_eq`). -/
def pairUpGo (z : B256) : Option (B256 × B256 × B256) → List B256 → List B256 → List B256
  | _, acc, [] => acc.reverse
  | m, acc, [a] => (hashPairMemo m a z :: acc).reverse
  | m, acc, a :: b :: rest =>
    let h := hashPairMemo m a b
    pairUpGo z (some (a, b, h)) (h :: acc) rest

theorem pairUpGo_eq (z : B256) : ∀ (xs : List B256) (m : Option (B256 × B256 × B256))
    (acc : List B256), MemoOk m → pairUpGo z m acc xs = acc.reverse ++ pairUp z xs
  | [], m, acc, _ => by simp [pairUpGo, pairUp]
  | [a], m, acc, hm => by simp [pairUpGo, pairUp, hashPairMemo_eq hm]
  | a :: b :: rest, m, acc, hm => by
    simp only [pairUpGo, pairUp]
    rw [pairUpGo_eq z rest _ _ (by simp [MemoOk, hashPairMemo_eq hm])]
    simp [hashPairMemo_eq hm]

/-- `pairUp` computed by `pairUpGo`. -/
def pairUpFast (z : B256) (xs : List B256) : List B256 := pairUpGo z none [] xs

theorem pairUpFast_eq (z : B256) (xs : List B256) : pairUpFast z xs = pairUp z xs := by
  simp [pairUpFast, pairUpGo_eq z xs none [] trivial]

/-- Merkleize `chunks` into a tree of depth `depth`, starting at height `level`. The caller
guarantees `chunks.length ≤ 2^depth`. -/
def merkleizeAt : (depth level : Nat) → List B256 → B256
  | depth, level, [] => zeroHashAt (level + depth)
  | 0, _, c :: _ => c
  | depth + 1, level, cs => merkleizeAt depth (level + 1) (pairUpFast (zeroHashAt level) cs)

/-- Merkleize `chunks` padded virtually to `2^depth` leaves. -/
@[inline] def merkleizeDepth (chunks : List B256) (depth : Nat) : B256 :=
  merkleizeAt depth 0 chunks

/-- `merkleize(chunks, limit=None)` (`ssz/simple-serialize.md`, "Merkleization"): pad to
`next_pow_of_two(len(chunks))`, or with a limit to `next_pow_of_two(limit)`, raising when
`limit < len(chunks)`. -/
def merkleize (chunks : List B256) (limit : Option Nat := none) : M B256 :=
  match limit with
  | none => pure (merkleizeDepth chunks (depthOf chunks.length))
  | some l =>
    if l < chunks.length then throw (.limit "merkleize" l chunks.length)
    else pure (merkleizeDepth chunks (depthOf l))

/-- `mix_in_length(root, length)`: `hash(root + uint256(length).to_bytes(32, "little"))`. -/
def mixInLength (root : B256) (length : Nat) : B256 :=
  hashPair root (Bytes.toB256 (leBytes 32 length))

/-- `mix_in_selector(root, selector)`: `hash(root + uint8(selector) right-padded to a chunk)`. -/
def mixInSelector (root : B256) (selector : Nat) : B256 :=
  hashPair root (chunkOf (leBytes 1 selector))

/-! Anchors. The root of two zero chunks is SHA-256 of 64 zero bytes, which is also the root
of an empty `Bitlist[N]` for `N ≤ 256` (`mix_in_length(Bytes32(), 0)`). -/

#guard some (zeroHash 1).toBytes = Hex.toBytes
  "f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
#guard (chunkOf [0xde, 0x01]).toBytes = [0xde, 0x01] ++ List.replicate 30 0
#guard depthOf 0 = 0 ∧ depthOf 1 = 0 ∧ depthOf 2 = 1 ∧ depthOf 3 = 2 ∧ depthOf 4 = 2 ∧
  depthOf 5 = 3 ∧ depthOf 9 = 4

end JauneConsensus
