import Jaune.Hash
import JauneConsensus.UInt
import JauneConsensus.Preset
import JauneConsensus.Config

/-!
# Container-free helper functions (phase0 through Fulu)

The math, crypto and misc helpers of `specs/<fork>/beacon-chain.md` that need no container or
state, each mirroring its pyspec function, with that function's name and file cited and its
operation order kept. They compute in `M` (outcome O5): typed `uint64` arithmetic goes through the
checked `U64` operations, which reject exactly where remerkleable raises; Python `int` arithmetic
is `Nat`; a sequence read out of range is `Reject.index`.

Shared types: `Bytes32` and `Root` are Jaune's `B256` (byte `i` is `B256.toBytes`'s byte `i`);
`bytes` is Jaune's `Bytes`; `hash` is Jaune's `Bytes.sha256`.
-/

namespace JauneConsensus

open Jaune

/-! ## Constants (`specs/phase0/beacon-chain.md`, "Misc" and "Withdrawal prefixes") -/

/-- `UINT64_MAX = uint64(2**64 - 1)` -/
def UINT64_MAX : U64 := U64.max
/-- `UINT64_MAX_SQRT = uint64(4294967295)` -/
def UINT64_MAX_SQRT : U64 := U64.lit 4294967295
/-- `GENESIS_SLOT = Slot(0)` -/
def GENESIS_SLOT : U64 := U64.zero
/-- `GENESIS_EPOCH = Epoch(0)` -/
def GENESIS_EPOCH : U64 := U64.zero
/-- `FAR_FUTURE_EPOCH = Epoch(2**64 - 1)` -/
def FAR_FUTURE_EPOCH : U64 := U64.max
/-- `BLS_WITHDRAWAL_PREFIX = Bytes1('0x00')` -/
def BLS_WITHDRAWAL_PREFIX : UInt8 := 0x00
/-- `ETH1_ADDRESS_WITHDRAWAL_PREFIX = Bytes1('0x01')` -/
def ETH1_ADDRESS_WITHDRAWAL_PREFIX : UInt8 := 0x01
/-- `COMPOUNDING_WITHDRAWAL_PREFIX = Bytes1('0x02')` (`specs/electra/beacon-chain.md`) -/
def COMPOUNDING_WITHDRAWAL_PREFIX : UInt8 := 0x02
/-- `VERSIONED_HASH_VERSION_KZG = Bytes1('0x01')` (`specs/deneb/beacon-chain.md`) -/
def VERSIONED_HASH_VERSION_KZG : UInt8 := 0x01

/-- A preset or config value as `uint64`. The generated records hold `Nat`; the spec types these
variables `uint64` (or a `uint64` alias), so the conversion rejects a value outside the type. -/
@[inline] def u64 (n : Nat) (site : String) : M U64 := U64.ofNat? n site

/-! ## Math (`specs/phase0/beacon-chain.md`, "Math") -/

/-- `integer_squareroot(n)`: the largest `x` with `x**2 <= n`. Newton iteration exactly as the
spec writes it; terminates because `x` strictly decreases. -/
def integerSquareroot (n : U64) : M U64 :=
  if n == UINT64_MAX then pure UINT64_MAX_SQRT else do
  let x := n
  let y ← (← x.add? U64.one "integer_squareroot: x + 1").div? (U64.lit 2) "integer_squareroot"
  loop x y
where
  loop (x y : U64) : M U64 :=
    if h : y < x then do
      let x' := y
      let q ← n.div? x' "integer_squareroot: n // x"
      let y' ← (← x'.add? q "integer_squareroot: x + n // x").div? (U64.lit 2) "integer_squareroot"
      loop x' y'
    else pure x
  termination_by x.toNat
  decreasing_by exact h

/-- `xor(bytes_1, bytes_2)`: bytewise exclusive-or of two `Bytes32`. -/
def xor (bytes1 bytes2 : B256) : B256 := B256.xor bytes1 bytes2

/-- `uint_to_bytes(uintN(n))`: the `width`-byte little-endian (`ENDIANNESS = 'little'`)
encoding of `n` (`n < 256^width` where the caller's type guarantees it). -/
def uintToBytes (width n : Nat) : Bytes :=
  (List.range width).map (fun i => (n / 256 ^ i % 256).toUInt8)

/-- `int.from_bytes(data, 'little')`. -/
def bytesToUint (data : Bytes) : Nat :=
  data.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- `bytes_to_uint64(data) = uint64(int.from_bytes(data, ENDIANNESS))`: rejects a value outside
`uint64` (possible only when `data` is longer than eight bytes). -/
def bytesToUint64 (data : Bytes) : M U64 := U64.ofNat? (bytesToUint data) "bytes_to_uint64"

/-- `saturating_sub(a, b)` on Python `int`: `a - b if a > b else 0`. -/
def saturatingSub (a b : Nat) : Nat := if a > b then a - b else 0

/-! ## Crypto (`specs/phase0/beacon-chain.md`, "Crypto") -/

/-- `hash(data)`: SHA-256. -/
def hash (data : Bytes) : B256 := Bytes.sha256 data

/-- `hash(data)` as bytes (for slicing, as the spec does with `hash(...)[a:b]`). -/
def hashBytes (data : Bytes) : Bytes := (hash data).toBytes

/-- Big-endian bytes to `B256` (a `Bytes32` built from 32 bytes). -/
def B256.ofBytes (bs : Bytes) : B256 :=
  (bs.foldl (fun (n : Nat) (b : UInt8) => 256 * n + b.toNat) 0).toB256

/-- `Bytes32` equality. -/
def B256.beq (a b : B256) : Bool := a.toBytes == b.toBytes

/-! ## Predicates -/

/-- `is_valid_merkle_branch(leaf, branch, depth, index, root)` (`specs/phase0/beacon-chain.md`).
A `branch` shorter than `depth` raises `IndexError` in pyspec: `Reject.index`. -/
def isValidMerkleBranch (leaf : B256) (branch : List B256) (depth index : U64) (root : B256) :
    M Bool := do
  let br := branch.toArray
  let mut value := leaf
  for i in List.range depth.toNat do
    let b ← getAt br i "is_valid_merkle_branch: branch[i]"
    if index.toNat / 2 ^ i % 2 == 1 then
      value := hash (b.toBytes ++ value.toBytes)
    else
      value := hash (value.toBytes ++ b.toBytes)
  pure (B256.beq value root)

/-- `is_compounding_withdrawal_credential(withdrawal_credentials)`
(`specs/electra/beacon-chain.md`): `withdrawal_credentials[:1] == COMPOUNDING_WITHDRAWAL_PREFIX`. -/
def isCompoundingWithdrawalCredential (withdrawalCredentials : B256) : Bool :=
  withdrawalCredentials.toBytes.take 1 == [COMPOUNDING_WITHDRAWAL_PREFIX]

/-! ## Misc (`specs/phase0/beacon-chain.md`, "Misc") -/

/-- `compute_epoch_at_slot(slot) = Epoch(slot // SLOTS_PER_EPOCH)`. -/
def computeEpochAtSlot (P : Preset) (slot : U64) : M U64 := do
  slot.div? (← u64 P.SLOTS_PER_EPOCH "SLOTS_PER_EPOCH") "compute_epoch_at_slot"

/-- `compute_start_slot_at_epoch(epoch) = Slot(epoch * SLOTS_PER_EPOCH)`. -/
def computeStartSlotAtEpoch (P : Preset) (epoch : U64) : M U64 := do
  epoch.mul? (← u64 P.SLOTS_PER_EPOCH "SLOTS_PER_EPOCH") "compute_start_slot_at_epoch"

/-- `compute_activation_exit_epoch(epoch) = Epoch(epoch + 1 + MAX_SEED_LOOKAHEAD)`. -/
def computeActivationExitEpoch (P : Preset) (epoch : U64) : M U64 := do
  let e ← epoch.add? U64.one "compute_activation_exit_epoch: epoch + 1"
  e.add? (← u64 P.MAX_SEED_LOOKAHEAD "MAX_SEED_LOOKAHEAD") "compute_activation_exit_epoch"

/-! ## Altair misc (`specs/altair/beacon-chain.md`, "Misc") -/

/-- `add_flag(flags, flag_index)`: `flag = ParticipationFlags(2**flag_index)`, which rejects when
`flag_index ≥ 8`; then `flags | flag`. -/
def addFlag (flags : U8) (flagIndex : Nat) : M U8 := do
  let flag : U8 ← UIntN.ofNat? (2 ^ flagIndex) "add_flag: ParticipationFlags(2**flag_index)"
  UIntN.ofNat? (flags.toNat ||| flag.toNat) "add_flag: flags | flag"

/-- `has_flag(flags, flag_index)`: `flags & flag == flag`. -/
def hasFlag (flags : U8) (flagIndex : Nat) : M Bool := do
  let flag : U8 ← UIntN.ofNat? (2 ^ flagIndex) "has_flag: ParticipationFlags(2**flag_index)"
  pure (flags.toNat &&& flag.toNat == flag.toNat)

/-! ## Deneb misc (`specs/deneb/beacon-chain.md`, "Misc") -/

/-- `kzg_commitment_to_versioned_hash(kzg_commitment)`:
`VERSIONED_HASH_VERSION_KZG + hash(kzg_commitment)[1:]`. The commitment is the 48-byte
`KZGCommitment`; its length is the SSZ type's guarantee. -/
def kzgCommitmentToVersionedHash (kzgCommitment : Bytes) : B256 :=
  B256.ofBytes (VERSIONED_HASH_VERSION_KZG :: (hashBytes kzgCommitment).drop 1)

/-! ## Fulu misc (`specs/fulu/beacon-chain.md`, "Misc") -/

/-- The zero root `Bytes32()` (also `Root()`). -/
def zeroRoot : B256 := Bytes.toB256 (List.replicate 32 0)

/-- `BlobParameters(epoch, max_blobs_per_block)`. -/
structure BlobParameters where
  epoch : U64
  maxBlobsPerBlock : U64
  deriving DecidableEq, Repr

/-- `get_blob_parameters(epoch)`: the latest `BLOB_SCHEDULE` entry (sorted by `EPOCH`,
descending, stably, as Python's `sorted(..., reverse=True)`) whose `EPOCH` is at most `epoch`;
otherwise Electra's parameters. Building `BlobParameters` types both fields `uint64`. -/
def getBlobParameters (cfg : Config) (epoch : U64) : M BlobParameters := do
  let sorted := cfg.BLOB_SCHEDULE.mergeSort (fun a b => decide (b.EPOCH ≤ a.EPOCH))
  match sorted.find? (fun e => decide (e.EPOCH ≤ epoch.toNat)) with
  | some e =>
    pure ⟨← u64 e.EPOCH "BlobParameters.epoch", ← u64 e.MAX_BLOBS_PER_BLOCK "BlobParameters.max"⟩
  | none =>
    pure ⟨← u64 cfg.ELECTRA_FORK_EPOCH "ELECTRA_FORK_EPOCH",
          ← u64 cfg.MAX_BLOBS_PER_BLOCK_ELECTRA "MAX_BLOBS_PER_BLOCK_ELECTRA"⟩

/-! ## Tests -/

-- Test literals; every one used below is under `2^64`, so `ofNat?` accepts it.
private def n64 (n : Nat) : U64 :=
  match U64.ofNat? n with
  | .ok x => x
  | .error _ => U64.max
private def sqrt? (n : Nat) : Option Nat := ((integerSquareroot (n64 n)).toOption).map (·.toNat)

#guard (List.range 50).all fun n => sqrt? n == some n.sqrt
#guard sqrt? (2 ^ 64 - 1) == some 4294967295
#guard sqrt? (2 ^ 64 - 2) == some 4294967295
#guard sqrt? (2 ^ 32 * 2 ^ 32 - 2 ^ 33) == some (2 ^ 32 - 2)
#guard sqrt? 1000000007 == some 31622
#guard B256.beq (xor 0xff00 0x0ff0) 0xf0f0
#guard bytesToUint [1, 2] == 0x0201
#guard (bytesToUint64 (List.replicate 9 0xff)).toBool == false
#guard ((bytesToUint64 (List.replicate 8 0xff)).toOption.map (·.toNat)) == some (2 ^ 64 - 1)
#guard uintToBytes 4 0x01020304 == [4, 3, 2, 1]
#guard saturatingSub 3 5 == 0 && saturatingSub 5 3 == 2
#guard ((computeEpochAtSlot .mainnet (n64 65)).toOption.map (·.toNat)) == some 2
#guard ((computeStartSlotAtEpoch .minimal (n64 3)).toOption.map (·.toNat)) == some 24
#guard (computeStartSlotAtEpoch .mainnet (n64 (2 ^ 60))).toBool == false
#guard ((computeActivationExitEpoch .mainnet (n64 10)).toOption.map (·.toNat)) == some 15
#guard (computeActivationExitEpoch .mainnet FAR_FUTURE_EPOCH).toBool == false
#guard ((addFlag UIntN.zero 2).toOption.map (·.toNat)) == some 4
#guard (addFlag UIntN.zero 8).toBool == false
#guard (((addFlag UIntN.zero 1).toOption).bind (fun f => (hasFlag f 1).toOption)) == some true
#guard (((addFlag UIntN.zero 1).toOption).bind (fun f => (hasFlag f 0).toOption)) == some false
#guard isCompoundingWithdrawalCredential (B256.ofBytes (0x02 :: List.replicate 31 0))
#guard !isCompoundingWithdrawalCredential (B256.ofBytes (0x01 :: List.replicate 31 0))
-- a depth-1 branch: root = hash(leaf ++ sibling) at index 0, hash(sibling ++ leaf) at index 1
#guard (isValidMerkleBranch 1 [2] (n64 1) (n64 0) (hash ((1 : B256).toBytes ++ (2 : B256).toBytes))).toOption == some true
#guard (isValidMerkleBranch 1 [2] (n64 1) (n64 1) (hash ((2 : B256).toBytes ++ (1 : B256).toBytes))).toOption == some true
#guard (isValidMerkleBranch 1 [2] (n64 1) (n64 1) (hash ((1 : B256).toBytes ++ (2 : B256).toBytes))).toOption == some false
#guard (isValidMerkleBranch 1 [] (n64 1) (n64 0) 0).toBool == false
-- `get_blob_parameters` over the mainnet schedule (Fulu at 411392, BPO1 at 412672, BPO2 at 419072)
#guard ((getBlobParameters .mainnet (n64 411392)).toOption.map (fun p => (p.epoch.toNat, p.maxBlobsPerBlock.toNat))) == some (364032, 9)
#guard ((getBlobParameters .mainnet (n64 412672)).toOption.map (fun p => (p.epoch.toNat, p.maxBlobsPerBlock.toNat))) == some (412672, 15)
#guard ((getBlobParameters .mainnet (n64 500000)).toOption.map (fun p => (p.epoch.toNat, p.maxBlobsPerBlock.toNat))) == some (419072, 21)
#guard (kzgCommitmentToVersionedHash (List.replicate 48 0)).toBytes.head? == some 0x01

end JauneConsensus
