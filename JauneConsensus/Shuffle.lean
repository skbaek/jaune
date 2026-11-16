import JauneConsensus.Helpers

/-!
# Swap-or-not shuffle

`specs/phase0/beacon-chain.md`, `compute_shuffled_index` (unchanged through Fulu), with its helpers
`uint_to_bytes` and `bytes_to_uint64` (`ENDIANNESS = 'little'`) and `hash` = SHA-256, which is
Jaune's `Bytes.sha256` (proved equal to FIPS 180-4 by `Bytes.sha256_eq_fips`). `Bytes32` is
Jaune's `B256`, serialized big-end first by `B256.toBytes` (byte `i` of the root is byte `i` of the
digest).

`SHUFFLE_ROUND_COUNT` is the preset's (`presets/minimal/phase0.yaml`: 10;
`presets/mainnet/phase0.yaml`: 90), read from the generated `Preset` record.

Failure fidelity (outcome O5). `index` and `index_count` are `U64`, and every typed operation is
the checked one: `pivot + index_count` rejects when it reaches `2^64` (possible when
`index_count > 2^63`), `uint32(position // 256)` rejects when `position ≥ 2^40`, and
`uint8(current_round)` rejects a round count above 256. The subtraction cannot underflow because
`index < index_count`, and `% index_count` cannot divide by zero after the `assert`; both still go
through the checked operations. The whole-list shuffle is not part of the semantics.
-/

namespace JauneConsensus

open Jaune

/-- One round of `compute_shuffled_index` (the spec's loop body), from `index`. -/
def shuffleRound (seed : B256) (indexCount : U64) (currentRound : Nat) (index : U64) : M U64 := do
  let round : U8 ← UIntN.ofNat? currentRound "compute_shuffled_index: uint8(current_round)"
  let roundByte := uintToBytes 1 round.toNat
  let pivot ← (← bytesToUint64 ((hashBytes (seed.toBytes ++ roundByte)).take 8)).mod? indexCount
    "compute_shuffled_index: % index_count"
  let flip ← (← (← pivot.add? indexCount "compute_shuffled_index: pivot + index_count").sub?
    index "compute_shuffled_index: - index").mod? indexCount "compute_shuffled_index: % index_count"
  let position := if index.toNat ≥ flip.toNat then index else flip
  let block : U32 ← UIntN.ofNat? (← position.div? (U64.lit 256) "position // 256").toNat
    "compute_shuffled_index: uint32(position // 256)"
  let source := hashBytes (seed.toBytes ++ roundByte ++ uintToBytes 4 block.toNat)
  let byte ← getAt source.toArray (position.toNat % 256 / 8) "compute_shuffled_index: source"
  let bit := (byte.toNat >>> (position.toNat % 8)) % 2
  pure (if bit == 1 then flip else index)

/-- `compute_shuffled_index(index, index_count, seed)`. -/
def computeShuffledIndex (P : Preset) (index indexCount : U64) (seed : B256) : M U64 := do
  require (index < indexCount) "compute_shuffled_index: index < index_count"
  (List.range P.SHUFFLE_ROUND_COUNT).foldlM (fun i r => shuffleRound seed indexCount r i) index

-- The only `count = 10` mapping of the first minimal seed
-- (`phase0/shuffling/core/shuffle/shuffle_0x23bc..._10`, 10 rounds).
private def seed23 : B256 :=
  0x23bcd11624a07465b1c2fc1a0fe52996daae4bf87b0fb6bed45926096c644843

-- Test literals; every one used below is under `2^64`, so `ofNat?` accepts it.
private def n64 (n : Nat) : U64 :=
  match U64.ofNat? n with
  | .ok x => x
  | .error _ => U64.max

#guard ((List.range 10).mapM (fun i => computeShuffledIndex .minimal (n64 i) (n64 10) seed23)).toOption.map
  (·.map U64.toNat) == some [6, 9, 2, 7, 8, 3, 0, 1, 4, 5]
#guard (computeShuffledIndex .minimal (n64 10) (n64 10) seed23).toBool == false
#guard (computeShuffledIndex .minimal (n64 0) (n64 0) seed23).toBool == false
-- `pivot + index_count` overflows `uint64` for a count above `2^63` (pyspec raises)
#guard match computeShuffledIndex .minimal (n64 0) (n64 (2 ^ 63 + 5)) seed23 with
  | .error (.overflow _) => true
  | _ => false

end JauneConsensus
