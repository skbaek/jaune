import JauneConsensus.Error
import Jaune.Basic

/-!
# Checked unsigned integers

`ssz/simple-serialize.md`, "Basic types": `uintN` for `N in [8, 16, 32, 64, 128, 256]`.
pyspec computes typed `uintN` arithmetic through remerkleable, which raises when a result
leaves `[0, 2^N)`. The model therefore gives these types **no** `HAdd`, `HSub`, `HMul`,
`HDiv`, `HMod` or `OfNat` instances: wrapping arithmetic cannot be written. Arithmetic is
`add?`, `sub?`, `mul?`, `div?`, `mod?` in `M`, failing exactly where remerkleable raises
(`Reject.overflow`, `Reject.underflow`, `Reject.divByZero`).

* `U64` is the spec layer's workhorse (`Slot`, `Epoch`, `Gwei`, `ValidatorIndex`, ...). It is a
  structure over `UInt64` so that values stay unboxed scalars in compiled code.
* `UIntN n` is the `8 * n`-bit unsigned integer as a bounded `Nat`, used for `uint16`,
  `uint32`, `uint128` and `uint256` (for example Fulu's `NodeID`).

Each operation is defined on `toNat`, so its specification is its definition: the result, when
there is one, is the mathematical result.
-/

namespace JauneConsensus

/-! ## `uint64` -/

/-- `uint64`, with checked arithmetic only. -/
structure U64 where
  u64 : UInt64
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace U64

/-- The value as a natural number. -/
@[inline] def toNat (x : U64) : Nat := x.u64.toNat

/-- The value as the execution layer's 64-bit word, for fields Jaune types as `UInt64` (the engine's
withdrawal conversion, `JauneConsensus/Engine.lean`). A projection: no arithmetic, no truncation. -/
@[inline] def toWord (x : U64) : UInt64 := x.u64

theorem toNat_lt (x : U64) : x.toNat < 2 ^ 64 := x.u64.toNat_lt

/-- `uint64(n)`: rejects with `Reject.overflow` when `n ≥ 2^64`. -/
@[inline] def ofNat? (n : Nat) (site : String := "uint64") : M U64 :=
  if n < 2 ^ 64 then pure ⟨n.toUInt64⟩ else throw (.overflow site)

/-- A value known to fit. -/
@[inline] def ofNatLt (n : Nat) (_h : n < 2 ^ 64) : U64 := ⟨n.toUInt64⟩

/-- A literal known to fit; the bound is checked by the kernel at the use site. -/
@[inline] def lit (n : Nat) (_h : n < 2 ^ 64 := by decide) : U64 := ⟨n.toUInt64⟩

def zero : U64 := ⟨0⟩
def one : U64 := ⟨1⟩
def max : U64 := ⟨0xFFFFFFFFFFFFFFFF⟩

/-- `a + b` on `uint64`; rejects when the sum is at least `2^64`. -/
@[inline] def add? (a b : U64) (site : String := "uint64 add") : M U64 :=
  ofNat? (a.toNat + b.toNat) site

/-- `a - b` on `uint64`; rejects when `b > a`. -/
@[inline] def sub? (a b : U64) (site : String := "uint64 sub") : M U64 :=
  if b.toNat ≤ a.toNat then pure ⟨(a.toNat - b.toNat).toUInt64⟩ else throw (.underflow site)

/-- `a * b` on `uint64`; rejects when the product is at least `2^64`. -/
@[inline] def mul? (a b : U64) (site : String := "uint64 mul") : M U64 :=
  ofNat? (a.toNat * b.toNat) site

/-- `a // b` on `uint64`; rejects when `b = 0`. -/
@[inline] def div? (a b : U64) (site : String := "uint64 div") : M U64 :=
  if b.toNat = 0 then throw (.divByZero site) else pure ⟨(a.toNat / b.toNat).toUInt64⟩

/-- `a % b` on `uint64`; rejects when `b = 0`. -/
@[inline] def mod? (a b : U64) (site : String := "uint64 mod") : M U64 :=
  if b.toNat = 0 then throw (.divByZero site) else pure ⟨(a.toNat % b.toNat).toUInt64⟩

/-- `a >> k` on `uint64` (never fails). -/
@[inline] def shiftRight (a : U64) (k : Nat) : U64 := ⟨(a.toNat >>> k).toUInt64⟩

/-- `a << k` on `uint64`; remerkleable raises when bits leave the type. -/
@[inline] def shiftLeft? (a : U64) (k : Nat) (site : String := "uint64 shl") : M U64 :=
  ofNat? (a.toNat <<< k) site

/-- Bitwise `&`, `|`, `^` on `uint64` (never fail). -/
@[inline] def and (a b : U64) : U64 := ⟨a.u64 &&& b.u64⟩
@[inline] def or (a b : U64) : U64 := ⟨a.u64 ||| b.u64⟩
@[inline] def xor (a b : U64) : U64 := ⟨a.u64 ^^^ b.u64⟩

instance : LT U64 := ⟨fun a b => a.toNat < b.toNat⟩
instance : LE U64 := ⟨fun a b => a.toNat ≤ b.toNat⟩
instance (a b : U64) : Decidable (a < b) := inferInstanceAs (Decidable (a.toNat < b.toNat))
instance (a b : U64) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toNat ≤ b.toNat))
instance : ToString U64 := ⟨fun x => toString x.toNat⟩

theorem toNat_ofNat? {n : Nat} {site : String} {x : U64} (h : ofNat? n site = .ok x) :
    x.toNat = n := by
  unfold ofNat? at h
  split at h
  · cases h
    simp only [toNat, Nat.toUInt64]
    exact Nat.mod_eq_of_lt ‹_›
  · cases h

theorem toNat_add? {a b x : U64} {site : String} (h : add? a b site = .ok x) :
    x.toNat = a.toNat + b.toNat := toNat_ofNat? h

theorem toNat_mul? {a b x : U64} {site : String} (h : mul? a b site = .ok x) :
    x.toNat = a.toNat * b.toNat := toNat_ofNat? h

theorem add?_ok_iff {a b : U64} {site : String} :
    (∃ x, add? a b site = .ok x) ↔ a.toNat + b.toNat < 2 ^ 64 := by
  unfold add? ofNat?
  constructor
  · rintro ⟨x, hx⟩
    split at hx
    · assumption
    · cases hx
  · intro h
    exact ⟨⟨(a.toNat + b.toNat).toUInt64⟩, by simp only [add?, ofNat?, if_pos h]; rfl⟩

end U64

/-! ## `uintN` as a bounded natural number -/

/-- The unsigned integer of `n` bytes (`8 * n` bits). -/
structure UIntN (n : Nat) where
  toNat : Nat
  isLt : toNat < 2 ^ (8 * n)

namespace UIntN

variable {n : Nat}

theorem ext : ∀ {a b : UIntN n}, a.toNat = b.toNat → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance : DecidableEq (UIntN n) := fun a b =>
  if h : a.toNat = b.toNat then isTrue (ext h) else isFalse (fun e => h (e ▸ rfl))

instance : Repr (UIntN n) := ⟨fun x _ => repr x.toNat⟩
instance : ToString (UIntN n) := ⟨fun x => toString x.toNat⟩

/-- `uintN(v)`: rejects with `Reject.overflow` when `v ≥ 2^(8n)`. -/
@[inline] def ofNat? (v : Nat) (site : String := "uintN") : M (UIntN n) :=
  if h : v < 2 ^ (8 * n) then pure ⟨v, h⟩ else throw (.overflow site)

def zero : UIntN n := ⟨0, Nat.two_pow_pos _⟩

instance : Inhabited (UIntN n) := ⟨zero⟩

/-- The largest value, `2^(8n) - 1` (for example pyspec `UINT256_MAX`). -/
def max : UIntN n := ⟨2 ^ (8 * n) - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩

@[inline] def add? (a b : UIntN n) (site : String := "uintN add") : M (UIntN n) :=
  ofNat? (a.toNat + b.toNat) site

@[inline] def sub? (a b : UIntN n) (site : String := "uintN sub") : M (UIntN n) :=
  if b.toNat ≤ a.toNat then pure ⟨a.toNat - b.toNat, Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt⟩
  else throw (.underflow site)

@[inline] def mul? (a b : UIntN n) (site : String := "uintN mul") : M (UIntN n) :=
  ofNat? (a.toNat * b.toNat) site

@[inline] def div? (a b : UIntN n) (site : String := "uintN div") : M (UIntN n) :=
  if b.toNat = 0 then throw (.divByZero site)
  else pure ⟨a.toNat / b.toNat, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt⟩

@[inline] def mod? (a b : UIntN n) (site : String := "uintN mod") : M (UIntN n) :=
  if b.toNat = 0 then throw (.divByZero site)
  else pure ⟨a.toNat % b.toNat, Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.isLt⟩

instance : LT (UIntN n) := ⟨fun a b => a.toNat < b.toNat⟩
instance : LE (UIntN n) := ⟨fun a b => a.toNat ≤ b.toNat⟩
instance (a b : UIntN n) : Decidable (a < b) := inferInstanceAs (Decidable (a.toNat < b.toNat))
instance (a b : UIntN n) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

end UIntN

/-- `uint8` as a number (`byte` is `UInt8`, opaque data). -/
abbrev U8 := UIntN 1
/-- `uint16`. -/
abbrev U16 := UIntN 2
/-- `uint32`. -/
abbrev U32 := UIntN 4
/-- `uint128`. -/
abbrev U128 := UIntN 16
/-- `uint256`. -/
abbrev U256 := UIntN 32

/-! ## Reading a word from a byte array

The SSZ fast path for `Bytes32` (`SSZ/Basic.lean`) reads its 32 bytes by index. The pass is
Jaune's word codec `Bytes.toB256.go` (`Jaune/Basic.lean`), which works on raw `UInt64` limbs,
so it lives here, beside the other raw-word code. -/

open Jaune

/-- `Bytes.toB256.go` over the bytes `[i, i + n)` of a scope, read by index (no list). -/
def b256GoAt (bs : Array UInt8) : Nat → Nat → UInt64 → UInt64 → UInt64 → UInt64 → B256
  | 0, _, l3, l2, l1, l0 => ⟨⟨l3, l2⟩, ⟨l1, l0⟩⟩
  | n + 1, i, l3, l2, l1, l0 =>
    match bs[i]? with
    | some b => b256GoAt bs n (i + 1) ((l3 <<< 8) ||| (l2 >>> 56)) ((l2 <<< 8) ||| (l1 >>> 56))
        ((l1 <<< 8) ||| (l0 >>> 56)) ((l0 <<< 8) ||| b.toUInt64)
    | none => ⟨⟨l3, l2⟩, ⟨l1, l0⟩⟩

theorem b256GoAt_eq (bs : Array UInt8) : ∀ (n i : Nat) (l3 l2 l1 l0 : UInt64),
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

end JauneConsensus
