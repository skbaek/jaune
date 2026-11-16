import Jaune.SHA256Spec

/-!
# SHA-256 of two 32-byte roots, for merkleization

SSZ merkleization (`ssz/simple-serialize.md`, `merkleize`) hashes pairs of 32-byte chunks:
`hash(a + b)` with `a`, `b` each a `Bytes32`. Jaune's general `Bytes.sha256` takes a `List UInt8`
and walks it, which dominates the cost of a state root. `hashPair a b` computes the same digest
for exactly this shape:

* the 64-byte message is one block, written straight into an array (`pairBlock`, no list) and
  compressed by the kernel's `consumeChunk`;
* the padding of a 64-byte message is a constant second block (`0x80`, 55 zero bytes, the bit
  length 512), whose sixty-four-entry message schedule is a constant, `padSchedule`, computed
  once; the second compression runs the FIPS 180-4 rounds over it directly.

`hashPair_eq` proves `hashPair a b = Bytes.sha256 (a.toBytes ++ b.toBytes)` for all `a`, `b`, by
way of the FIPS 180-4 transcription in `Jaune/SHA256Spec.lean` (`Bytes.sha256_eq_fips`,
`SHA256.consumeChunk_eq`). Nothing here is assumed or checked only by testing; the differential
`#guard`s below are a falsifier run in addition to the theorem.

This module is not wired into the SSZ layer; swapping it into merkleization is the SSZ owner's
decision.
-/

namespace JauneConsensus.Crypto

open Jaune Jaune.SHA256

/-- The padding block of a 64-byte message (FIPS 180-4 §5.1.1): `0x80`, `k = 55` zero bytes
(`padZeros 64`), and the bit length `8 * 64 = 512` as a 64-bit big-endian integer. -/
def padBlock : Array UInt8 :=
  ⟨(0x80 : UInt8) :: (List.replicate 55 (0x00 : UInt8) ++ UInt64.toBytes (512 : Nat).toUInt64)⟩

/-- The FIPS 180-4 §6.2.2 compression with its message schedule given rather than computed:
`FIPS.compress H M` is `compressScheduled H (FIPS.schedule M)` by definition. -/
def compressScheduled (H : Vector UInt32 8) (W : Array UInt32) : Vector UInt32 8 :=
  let v : FIPS.Vars :=
    (List.range 64).foldl (FIPS.step W)
      { a := H[0], b := H[1], c := H[2], d := H[3],
        e := H[4], f := H[5], g := H[6], h := H[7] }
  #v[ H[0] + v.a, H[1] + v.b, H[2] + v.c, H[3] + v.d,
      H[4] + v.e, H[5] + v.f, H[6] + v.g, H[7] + v.h ]

theorem compress_eq_compressScheduled (H : Vector UInt32 8) (M : Vector UInt32 16) :
    FIPS.compress H M = compressScheduled H (FIPS.schedule M) := rfl

/-- The message schedule of the constant padding block, computed once. -/
def padSchedule : Array UInt32 := FIPS.schedule (FIPS.toWords padBlock.toList)

/-! ### The message block, written straight into an array

`B256.toBytes` builds the 32 bytes as nested list appends. `pairBlock` pushes the same bytes, in
the same order and by the same shifts and truncations (`UInt16.toBytes`, `UInt32.toBytes`,
`UInt64.toBytes`), into one 64-slot array. -/

@[inline] def push16 (acc : Array UInt8) (x : UInt16) : Array UInt8 :=
  (acc.push (x >>> 8).toUInt8).push x.toUInt8

@[inline] def push32 (acc : Array UInt8) (x : UInt32) : Array UInt8 :=
  push16 (push16 acc (x >>> 16).toUInt16) x.toUInt16

@[inline] def push64 (acc : Array UInt8) (x : UInt64) : Array UInt8 :=
  push32 (push32 acc (x >>> 32).toUInt32) x.toUInt32

/-- The 64-byte message block `a ++ b` as an array. -/
def pairBlock (a b : B256) : Array UInt8 :=
  push64 (push64 (push64 (push64 (push64 (push64 (push64 (push64
    (Array.emptyWithCapacity 64) a.1.1) a.1.2) a.2.1) a.2.2) b.1.1) b.1.2) b.2.1) b.2.2

theorem push16_toList (acc : Array UInt8) (x : UInt16) :
    (push16 acc x).toList = acc.toList ++ UInt16.toBytes x := by
  simp [push16, UInt16.toBytes]

theorem push32_toList (acc : Array UInt8) (x : UInt32) :
    (push32 acc x).toList = acc.toList ++ UInt32.toBytes x := by
  simp [push32, push16_toList, UInt32.toBytes]

theorem push64_toList (acc : Array UInt8) (x : UInt64) :
    (push64 acc x).toList = acc.toList ++ UInt64.toBytes x := by
  simp [push64, push32_toList, UInt64.toBytes]

theorem pairBlock_toList (a b : B256) : (pairBlock a b).toList = a.toBytes ++ b.toBytes := by
  simp [pairBlock, push64_toList, B256.toBytes, B128.toBytes]

/-- `hash(a + b)` for two `Bytes32`: the message block, written straight into an array, through
the kernel's compression, then the constant padding block over its precomputed schedule. -/
def hashPair (a b : B256) : B256 :=
  let H1 := consumeChunk initChunk (pairBlock a b)
  let H := compressScheduled H1 padSchedule
  B32s.toB256 H[0] H[1] H[2] H[3] H[4] H[5] H[6] H[7]

/-- The same digest with both blocks through the kernel's `consumeChunk` (no precomputed
schedule). Kept as the intermediate step of the proof and as a benchmark point. -/
def hashPairKernel (a b : B256) : B256 :=
  let H := consumeChunk (consumeChunk initChunk ⟨a.toBytes ++ b.toBytes⟩) padBlock
  B32s.toB256 H[0] H[1] H[2] H[3] H[4] H[5] H[6] H[7]

theorem length_toBytes_pair (a b : B256) : (a.toBytes ++ b.toBytes).length = 64 := by
  simp [B256.toBytes, B128.toBytes, UInt64.toBytes, UInt32.toBytes, UInt16.toBytes]

theorem hashPairKernel_eq (a b : B256) :
    hashPairKernel a b = Bytes.sha256 (a.toBytes ++ b.toBytes) := by
  have hm := length_toBytes_pair a b
  rw [Bytes.sha256_eq_fips, FIPS.hash, FIPS.hashWords, FIPS.pad, hm,
    blocks_append_64 _ _ hm, blocks_of_length_64 _ (by rfl)]
  simp only [List.foldl_cons, List.foldl_nil]
  unfold hashPairKernel
  rw [consumeChunk_eq, consumeChunk_eq, initChunk_eq]
  rfl

theorem hashPair_eq_hashPairKernel (a b : B256) : hashPair a b = hashPairKernel a b := by
  unfold hashPair hashPairKernel
  rw [consumeChunk_eq _ padBlock, consumeChunk_eq _ (pairBlock a b), pairBlock_toList,
    consumeChunk_eq _ ⟨a.toBytes ++ b.toBytes⟩]
  rfl

/-- **`hashPair` is SHA-256 of the 64-byte concatenation**, for every pair of roots. -/
theorem hashPair_eq (a b : B256) : hashPair a b = Bytes.sha256 (a.toBytes ++ b.toBytes) :=
  (hashPair_eq_hashPairKernel a b).trans (hashPairKernel_eq a b)

/-! ## Differential falsifier (in addition to the theorem) -/

private def b256Eq (x y : B256) : Bool := x.toBytes == y.toBytes

private def sample (k : Nat) : B256 := (k * 0x9e3779b97f4a7c15f39cc0605cedc834 + k ^ 7).toB256

#guard (List.range 64).all fun k =>
  b256Eq (hashPair (sample k) (sample (k + 1000))) (Bytes.sha256 ((sample k).toBytes ++ (sample (k + 1000)).toBytes))
-- the zero pair: SHA-256 of 64 zero bytes (`zero_hashes[1]` in SSZ merkleization)
#guard b256Eq (hashPair 0 0) 0xf5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b

end JauneConsensus.Crypto
