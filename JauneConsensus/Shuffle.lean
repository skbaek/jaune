import Jaune.Hash
import JauneConsensus.Error

/-!
# Swap-or-not shuffle

`specs/phase0/beacon-chain.md`, `compute_shuffled_index` (unchanged through Fulu), with its helpers
`uint_to_bytes` and `bytes_to_uint64` (`ENDIANNESS = 'little'`) and `hash` = SHA-256, which is
Jaune's `Bytes.sha256` (proved equal to FIPS 180-4 by `Bytes.sha256_eq_fips`). `Bytes32` is
Jaune's `B256`, serialized big-end first by `B256.toBytes` (byte `i` of the root is byte `i` of the
digest).

`SHUFFLE_ROUND_COUNT` is a preset value (`presets/minimal/phase0.yaml`: 10;
`presets/mainnet/phase0.yaml`: 90), passed explicitly until the preset record exists.

Failure fidelity (outcome O5). `index` and `index_count` are `uint64`; the model takes them as
`Nat` and rejects a value outside `[0, 2^64)` as the `uint64` constructor would. pyspec computes
`pivot + index_count - index` in `uint64`, so the sum `pivot + index_count` raises when it reaches
`2^64` (possible when `index_count > 2^63`); the model rejects there with `Reject.overflow`.
The subtraction cannot underflow because `index < index_count`. `% index_count` cannot divide by
zero after the `assert`. The whole-list shuffle is not part of the semantics.
-/

namespace JauneConsensus

open Jaune

/-- `uint_to_bytes(uintN(n))`: the `width`-byte little-endian encoding of `n` (`n < 256^width` at
every call site). -/
def uintToBytes (width n : Nat) : Bytes :=
  (List.range width).map (fun i => (n / 256 ^ i % 256).toUInt8)

/-- `int.from_bytes(data, 'little')`. -/
def bytesToUint (data : Bytes) : Nat :=
  data.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- `hash(data)`: SHA-256, as bytes. -/
def hashBytes (data : Bytes) : Bytes := (Bytes.sha256 data).toBytes

/-- One round of `compute_shuffled_index`, from `index` (spec loop body). Requires
`index < indexCount`, which every round preserves. -/
def shuffleRound (seed : B256) (indexCount : Nat) (currentRound : Nat) (index : Nat) : M Nat := do
  let roundByte := uintToBytes 1 currentRound
  let pivot := bytesToUint ((hashBytes (seed.toBytes ++ roundByte)).take 8) % indexCount
  -- `pivot + index_count - index` in `uint64`
  if pivot + indexCount ≥ 2 ^ 64 then throw (.overflow "compute_shuffled_index: pivot + index_count")
  let flip := (pivot + indexCount - index) % indexCount
  let position := max index flip
  let source := hashBytes (seed.toBytes ++ roundByte ++ uintToBytes 4 (position / 256))
  let byte ← getAt source.toArray (position % 256 / 8) "compute_shuffled_index: source"
  let bit := (byte.toNat >>> (position % 8)) % 2
  pure (if bit == 1 then flip else index)

/-- `compute_shuffled_index(index, index_count, seed)`. -/
def computeShuffledIndex (shuffleRoundCount : Nat) (index indexCount : Nat) (seed : B256) :
    M Nat := do
  if index ≥ 2 ^ 64 || indexCount ≥ 2 ^ 64 then throw (.overflow "compute_shuffled_index: uint64")
  require (index < indexCount) "compute_shuffled_index: index < index_count"
  (List.range shuffleRoundCount).foldlM (fun i r => shuffleRound seed indexCount r i) index

-- The only `count = 10` mapping of the first minimal seed
-- (`phase0/shuffling/core/shuffle/shuffle_0x23bc..._10`, 10 rounds).
private def seed23 : B256 :=
  0x23bcd11624a07465b1c2fc1a0fe52996daae4bf87b0fb6bed45926096c644843

#guard ((List.range 10).mapM (fun i => computeShuffledIndex 10 i 10 seed23)).toOption ==
  some [6, 9, 2, 7, 8, 3, 0, 1, 4, 5]
#guard (computeShuffledIndex 10 10 10 seed23).toBool == false
#guard (computeShuffledIndex 10 0 0 seed23).toBool == false

end JauneConsensus
