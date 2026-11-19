-- Types.lean : types used by both executable and abstract semantics of EVM and Blanc.

import Jaune.Basic
import Std.Data.TreeMap.Lemmas

namespace Jaune

open Jaune _root_.Nat

def Address : Type := UInt32 × U128

def Address.toNat (x : Address) : Nat :=
  (x.1.toNat <<< 128) ||| x.2.toNat

def Nat.toAddress (n : Nat) : Address :=
  ⟨(n >>> 128).toUInt32, n.toU128⟩

instance {n} : OfNat Address n := ⟨n.toAddress⟩

/-- The greatest address. -/
def Address.max : Address := ⟨-1, -1, -1⟩

lemma toNat_toUInt16 {n : ℕ} : UInt16.toNat n.toUInt16 = n ↾ 16 := UInt16.toNat_ofNat
lemma toNat_toUInt32 {n : ℕ} : UInt32.toNat n.toUInt32 = n ↾ 32 := UInt32.toNat_ofNat
lemma toNat_toUInt64 {n : ℕ} : UInt64.toNat (n.toUInt64) = n ↾ 64 := UInt64.toNat_ofNat

lemma Nat.lo_lo_of_le {k m n : Nat} (le : m ≤ n) :
    (k ↾ m) ↾ n = k ↾ m := mod_mod_of_dvd' <| Nat.pow_dvd_pow _ le

lemma Nat.lo_lo_of_ge {k m n : Nat} (ge : m ≥ n) :
    (k ↾ m) ↾ n = k ↾ n := mod_mod_of_dvd _ <| Nat.pow_dvd_pow _ ge

lemma Nat.hi_or_lo (a b : Nat) : a ↿ b ||| a ↾ b = a := by
  simp only [Nat.hi, Nat.lo]
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [← @Nat.add_eq_or b, Nat.div_add_mod']
  · apply Nat.dvd_mul_left
  · apply Nat.mod_lt _ (Nat.pow_pos _); omega

lemma Nat.or_eq_lo_add {k m n : Nat} :
    (k >>> n ↾ m) <<< n ||| k ↾ n = k ↾ (m + n) := by
  rw [← @Nat.lo_add_shr k m n]
  rw [← @Nat.lo_lo_of_ge k (m + n) n (by omega)]
  apply Nat.hi_or_lo

lemma toNat_toU128 (n : Nat) : n.toU128.toNat = n ↾ 128 := by
  simp only [Nat.toU128, U128.toNat]; rw [toNat_toUInt64, toNat_toUInt64]
  apply Nat.or_eq_lo_add

lemma Nat.toNat_toAddress (n : Nat) : n.toAddress.toNat = n ↾ 160 := by
  simp only [Nat.toAddress, Address.toNat]; rw [toNat_toUInt32, toNat_toU128]
  apply Nat.or_eq_lo_add

lemma toUInt32_toNat {x : UInt32} : x.toNat.toUInt32 = x := UInt32.ofNat_toNat

lemma toUInt64_or (a b : Nat) : (a ||| b).toUInt64 = a.toUInt64 ||| b.toUInt64 :=
  UInt64.ofNat_or a b

lemma U128.or_eq (x y : U128) :
  x ||| y = ⟨x.1 ||| y.1, x.2 ||| y.2⟩ := rfl

lemma toU128_or (a b : Nat) : (a ||| b).toU128 = a.toU128 ||| b.toU128 := by
  change (((a ||| b) >>> 64).toUInt64, (a ||| b).toUInt64) =
    (((a >>> 64).toUInt64 ||| (b >>> 64).toUInt64), a.toUInt64 ||| b.toUInt64)
  rw [Nat.shiftRight_or_distrib, toUInt64_or, toUInt64_or]

lemma Nat.shiftLeft_lt_of_lt {a b n : Nat} (h : a < 2 ^ n) :
    (a <<< b) < (2 ^ (n + b)) := by
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  apply Nat.mul_lt_mul_of_pos_right h (Nat.pow_pos (by omega))

lemma U128.toNat_lt {x : U128} : x.toNat < 2 ^ 128 := by
  simp only [U128.toNat]; apply Nat.or_lt_two_pow
  · apply Nat.shiftLeft_lt_of_lt (UInt64.toNat_lt _)
  · apply lt_trans (UInt64.toNat_lt _); omega

lemma U256.toNat_lt (x : U256) : x.toNat < 2 ^ 256 := BitVec.isLt x

lemma U128.zero_or {x : U128} : (0 ||| x) = x := by
  rw [U128.or_eq]; apply Prod.ext <;> exact UInt64.zero_or

lemma Nat.div_eq_zero_of_lt {k x : Nat} (h : x < k) : x / k = 0 := by
  rw [Nat.div_eq_zero_iff_lt (by omega)]; apply h

lemma UInt8.toNat_add_lo (a b : UInt8) : (a + b).toNat = (a.toNat + b.toNat) ↾ 8 :=
  UInt8.toNat_add a b

lemma UInt64.toNat_add_lo (a b : UInt64) : (a + b).toNat = (a.toNat + b.toNat) ↾ 64 :=
  UInt64.toNat_add a b

lemma Nat.lo_eq_of_lt {a b : ℕ} (h : a < (2 ^ b)) : a ↾ b = a :=
  Nat.mod_eq_of_lt h

lemma Nat.add_mod_eq_add_sub {k m n : Nat} (m_lt : m < k)
    (n_lt : n < k) (k_le : k ≤ m + n) : (m + n) % k = m + n - k := by
  rcases Nat.exists_eq_add_of_le k_le with ⟨d, eq⟩
  rw [eq, Nat.add_mod_left]
  have d_lt : d < k := by
    rw [← @Nat.add_lt_add_iff_left k, ← eq]
    apply Nat.add_lt_add m_lt n_lt
  simp [Nat.mod_eq_of_lt d_lt]

lemma UInt64.toNat_overflow {x y : UInt64} :
    x + y < x ↔ 2 ^ 64 ≤ x.toNat + y.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add_lo]
  by_cases h : x.toNat + y.toNat < 2 ^ 64
  · rw [Nat.lo_eq_of_lt h]
    apply iff_of_false <;> omega
  · rw [not_lt] at h; apply iff_of_true _ h
    have x_lt := @UInt64.toNat_lt x
    have y_lt := @UInt64.toNat_lt y
    rw [Nat.lo, Nat.add_mod_eq_add_sub x_lt y_lt h]
    omega

lemma ite_distrib {α β} {f : α → β} {p : Prop} [Decidable p] {a b : α} :
    f (if p then a else b) = if p then f a else f b := by
  by_cases h : p <;> simp [h]

lemma ite_eq_ite_of_iff {α} {p q : Prop} [Decidable p] [Decidable q]
    {a b c d : α} (pq : p ↔ q) (ac : a = c) (bd : b = d) :
    (if p then a else b) = (if q then c else d) := by
  rw [ac, bd]; by_cases h : p
  · rw [ite_eq_left h, ite_eq_left (pq.mp h)]
  · rw [ite_eq_right h, ite_eq_right (mt pq.mpr h)]

lemma toUInt64_toNat (x : UInt64) : x.toNat.toUInt64 = x :=
  UInt64.ofNat_toNat

lemma UInt64.ofNat_eq_iff_lo_eq_toNat (a : Nat) (b : UInt64) :
    a.toUInt64 = b ↔ a ↾ 64 = b.toNat :=
  UInt64.ofNat_eq_iff_mod_eq_toNat a b

lemma Nat.lo_lo {m n : Nat} : (m ↾ n) ↾ n = m ↾ n :=
  Nat.mod_mod _ _

lemma lo_toUInt64 (n : Nat) : (n ↾ 64).toUInt64 = n.toUInt64 := by
  rw [← UInt64.toNat_inj, toNat_toUInt64, toNat_toUInt64, Nat.lo_lo]

lemma Nat.or_lo {k m n : Nat} : (m ||| n) ↾ k = (m ↾ k) ||| (n ↾ k) :=
  Nat.or_mod_two_pow

/-
Byte-pair decoding for the `Bytes.toUIntN` family and `UIntN.concat`, whose
definitions are in `Basic.lean`. The lemmas live here rather than beside them
because their proofs need the `Nat.lo`/`Nat.hi` algebra declared above.
-/

lemma pair_aux (n m : Nat) :
    ((n >>> m ↾ m) ↾ (m + m)) <<< m ↾ (m + m) ||| (n ↾ m) ↾ (m + m) =
      n ↾ (m + m) := by
  rw [Nat.lo_lo_of_le (by omega)]
  rw [Nat.lo_lo_of_le (by omega)]
  apply Eq.trans _ <| high_or_low_eq_self (n ↾ (m + m)) m Nat.lo_lt
  apply congr_arg₂  _ _ (Nat.lo_lo_of_ge (by omega)).symm
  rw [@Nat.lo_add_shr n m m, ← Nat.lo_eq _ m, Nat.lo_lo]; rfl

lemma Nat.toUInt16_toUInt8 (n : Nat) : n.toUInt8.toUInt16 = (n ↾ 8).toUInt16 := by
  have h0 : n.toUInt8.toUInt16 = n.toUInt16 % (2 ^ 8) :=
      (UInt8.toUInt16_eq_mod_256_iff n.toUInt8 n.toUInt16).mpr
        (UInt16.toUInt8_ofNat' _).symm
  have h1: (n.toUInt16 % 2 ^ 8).toNat = n ↾ 8 := by
    have rw : UInt16.toNat (2 ^ 8) = 2 ^ 8 := rfl
    rw [UInt16.toNat_mod, rw]; clear rw
    rw [toNat_toUInt16, ← Nat.lo_eq]
    apply Nat.lo_lo_of_ge (by omega)
  have h2 : (n ↾ 8).toUInt16 = n.toUInt16 % (2 ^ 8) := by
    apply (UInt16.ofNat_eq_iff_mod_eq_toNat _ _).mpr
    apply Eq.trans (Nat.lo_lo_of_le (by omega)) h1.symm
  apply Eq.trans h0 h2.symm

lemma List.toUInt16_pair (n : Nat) :
    Bytes.toUInt16 [(n >>> 8).toUInt8, n.toUInt8] = n.toUInt16 := by
  have h : (n >>> 8 ↾ 8).toUInt16 <<< 8 ||| (n ↾ 8).toUInt16 = n.toUInt16 := by
    rw [← UInt16.toNat_inj, toNat_toUInt16, UInt16.toNat_or, toNat_toUInt16]
    rw [UInt16.toNat_shiftLeft, toNat_toUInt16]; apply pair_aux n 8
  simp [Bytes.toUInt16, Bytes.getElem_packV, Bytes.pack, takeRightD, List.takeD,
    List.reverse, List.reverseAux, List.tail, List.headD]
  rw [Nat.toUInt16_toUInt8, Nat.toUInt16_toUInt8, h]

lemma Nat.toUInt32_toUInt16 (n : Nat) : n.toUInt16.toUInt32 = (n ↾ 16).toUInt32 := by
  have h0 : n.toUInt16.toUInt32 = n.toUInt32 % (2 ^ 16) :=
      (UInt16.toUInt32_eq_mod_65536_iff n.toUInt16 n.toUInt32).mpr
        (UInt32.toUInt16_ofNat' _).symm
  have h1: (n.toUInt32 % 2 ^ 16).toNat = n ↾ 16 := by
    have rw : UInt32.toNat (2 ^ 16) = 2 ^ 16 := rfl
    rw [UInt32.toNat_mod, rw]; clear rw
    rw [toNat_toUInt32, ← Nat.lo_eq]
    apply Nat.lo_lo_of_ge (by omega)
  have h2 : (n ↾ 16).toUInt32 = n.toUInt32 % (2 ^ 16) := by
    apply (UInt32.ofNat_eq_iff_mod_eq_toNat _ _).mpr
    apply Eq.trans (Nat.lo_lo_of_le (by omega)) h1.symm
  apply Eq.trans h0 h2.symm

lemma toUInt32_eq_concat (n : Nat) :
    n.toUInt32 = UInt16.concat (n >>> 16).toUInt16 n.toUInt16 := by
  rw [← UInt32.toNat_inj, toNat_toUInt32]
  simp only [UInt16.concat, Nat.toUInt32_toUInt16]
  rw [UInt32.toNat_or, UInt32.toNat_shiftLeft_lo, toNat_toUInt32, toNat_toUInt32]
  rw [Nat.lo_lo_of_le (by omega), Nat.lo_lo_of_le (by omega)]
  have rw : (UInt32.toNat 16 % 32) = 16 := rfl
  rw [rw]; clear rw
  have rw : (n >>> 16 ↾ 16) <<< 16 ↾ 32 = (n ↾ 32) ↿ 16 := by
    rw [← Nat.lo_add_shr, ← Nat.hi_eq]
    apply Nat.lo_eq_of_lt
    apply lt_of_le_of_lt (Nat.hi_le _ _) Nat.lo_lt
  rw [rw, ← @Nat.lo_lo_of_ge n 32 16 (by omega)]
  apply (Nat.hi_or_lo _ _).symm

lemma List.toUInt32_pair (n : Nat) (n_lt : n < 2 ^ 16) :
    Bytes.toUInt32 [(n >>> 8).toUInt8, n.toUInt8] = n.toUInt32 := by
  simp only [ Bytes.toUInt32, Bytes.pack, takeRightD, List.takeD,
    List.reverse, List.reverseAux, List.tail, List.headD, List.take, List.drop ]
  apply Eq.trans _ (toUInt32_eq_concat _).symm
  apply congr_arg₂ _ _ (congr_arg _ _)
  · apply congr_arg (λ x : UInt32 => x <<< 16) <| congr_arg _ _
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_of_lt (by omega)]; rfl
  · apply List.toUInt16_pair

lemma Nat.toUInt64_toUInt32 (n : Nat) : n.toUInt32.toUInt64 = (n ↾ 32).toUInt64 := by
  have h0 : n.toUInt32.toUInt64 = n.toUInt64 % (2 ^ 32) :=
      (UInt32.toUInt64_eq_mod_4294967296_iff n.toUInt32 n.toUInt64).mpr
        (UInt64.toUInt32_ofNat' _).symm
  have h1: (n.toUInt64 % 2 ^ 32).toNat = n ↾ 32 := by
    have rw : UInt64.toNat (2 ^ 32) = 2 ^ 32 := rfl
    rw [UInt64.toNat_mod, rw]; clear rw
    rw [toNat_toUInt64, ← Nat.lo_eq]
    apply Nat.lo_lo_of_ge (by omega)
  have h2 : (n ↾ 32).toUInt64 = n.toUInt64 % (2 ^ 32) := by
    apply (UInt64.ofNat_eq_iff_mod_eq_toNat _ _).mpr
    apply Eq.trans (Nat.lo_lo_of_le (by omega)) h1.symm
  apply Eq.trans h0 h2.symm

lemma toUInt64_eq_concat (n : Nat) :
    n.toUInt64 = UInt32.concat (n >>> 32).toUInt32 n.toUInt32 := by
  rw [← UInt64.toNat_inj, toNat_toUInt64]
  simp only [UInt32.concat, Nat.toUInt64_toUInt32]
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft_lo, toNat_toUInt64, toNat_toUInt64]
  rw [Nat.lo_lo_of_le (by omega), Nat.lo_lo_of_le (by omega)]
  have rw : (UInt64.toNat 32 % 64) = 32 := rfl
  rw [rw]; clear rw
  have rw : (n >>> 32 ↾ 32) <<< 32 ↾ 64 = (n ↾ 64) ↿ 32 := by
    rw [← Nat.lo_add_shr, ← Nat.hi_eq]
    apply Nat.lo_eq_of_lt
    apply lt_of_le_of_lt (Nat.hi_le _ _) Nat.lo_lt
  rw [rw, ← @Nat.lo_lo_of_ge n 64 32 (by omega)]
  apply (Nat.hi_or_lo _ _).symm

lemma List.toUInt64_pair (n : Nat) (n_lt : n < 2 ^ 16) :
    Bytes.toUInt64 [(n >>> 8).toUInt8, n.toUInt8] = n.toUInt64 := by
  simp only [ Bytes.toUInt64, Bytes.pack, takeRightD, List.takeD,
    List.reverse, List.reverseAux, List.tail, List.headD, List.take, List.drop ]
  apply Eq.trans _ (toUInt64_eq_concat _).symm
  apply congr_arg₂ _ _ (congr_arg _ _)
  · apply congr_arg (λ x : UInt64 => x <<< 32) <| congr_arg _ _
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_of_lt (by omega)]; rfl
  · apply List.toUInt32_pair _ n_lt

lemma List.toU256_pair (n : Nat) (n_lt : n < 2 ^ 16):
    Bytes.toU256 [(n >>> 8).toUInt8, n.toUInt8] = n.toU256 := by
  simp only [Bytes.toU256, List.length_cons, List.length_nil, Nat.reduceLeDiff, ↓reduceIte,
    List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add,
    UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  congr 1
  omega

lemma toU128_toNat (x : U128) : x.toNat.toU128 = x := by
  simp only [U128.toNat, Nat.toU128]
  apply congr_arg₂
  · rw [Nat.shiftRight_or_distrib, Nat.shiftLeft_shiftRight]
    rw [Nat.shiftRight_eq_zero _ _ (UInt64.toNat_lt _), Nat.or_zero, toUInt64_toNat]
  · rw [← lo_toUInt64, Nat.or_lo, Nat.shl_lo_eq_zero_of_le (by omega)]
    rw [Nat.zero_or, lo_toUInt64, toUInt64_toNat]

lemma U128.toNat_inj (xs ys : U128) : xs.toNat = ys.toNat ↔ xs = ys := by
  constructor <;> intro h
  · rw [← toU128_toNat xs, ← toU128_toNat ys, h]
  · simp [h]

lemma lo_toU128 (n : Nat) : (n ↾ 128).toU128 = n.toU128 := by
  rw [← U128.toNat_inj, toNat_toU128, toNat_toU128, Nat.lo_lo]

lemma toU128_eq_iff_lo_eq_toNat (a : Nat) (b : U128) :
    a.toU128 = b ↔ a ↾ 128 = b.toNat := by
  constructor <;> intro h
  · rw [← h, toNat_toU128]
  · rw [← U128.toNat_inj, ← h, toNat_toU128]

lemma U128.sub_eq (x y : U128) :
  x - y = ⟨(x.1 - y.1) - (if x.2 < y.2 then 1 else 0), x.2 - y.2⟩ := rfl

lemma U128.zero_eq : (0 : U128) = ⟨0, 0⟩ := rfl

lemma U128.add_eq (x y : U128) :
  x + y = ⟨x.1 + y.1 + if x.2 + y.2 < x.2 then 1 else 0, x.2 + y.2⟩ := rfl

lemma U128.zero_add (n : U128) : 0 + n = n := by
  rw [U128.add_eq];
  simp only [
    show ((0 : U128).1) = 0 from rfl, _root_.zero_add,
    show ((0 : U128).2) = 0 from rfl,
    UInt64.not_lt_zero, ↓reduceIte, add_zero
  ]
  rfl

lemma toU256_toNat (x : U256) : x.toNat.toU256 = x :=
  BitVec.eq_of_toNat_eq ((BitVec.toNat_ofNat _ _).trans (Nat.mod_eq_of_lt (BitVec.isLt x)))

theorem U256.toNat_inj (xs ys : U256) (eq : xs.toNat = ys.toNat) : xs = ys :=
  BitVec.eq_of_toNat_eq eq

/-
The `toNat` characterization of the `Nat`-routed word operations: the
interface downstream developments consume instead of unfolding definitions.
-/

theorem U256.toNat_toU256 (n : Nat) : (Nat.toU256 n).toNat = n ↾ 256 :=
  BitVec.toNat_ofNat _ _

theorem U256.toNat_toU256_of_lt {n : Nat} (h : n < 2 ^ 256) :
    (Nat.toU256 n).toNat = n := by rw [U256.toNat_toU256, Nat.lo_eq_of_lt h]

theorem U256.toNat_mul (x y : U256) :
    (x * y).toNat = (x.toNat * y.toNat) ↾ 256 := BitVec.toNat_mul _ _

theorem U256.toNat_mod {x y : U256} (h : y ≠ 0) :
    (x % y).toNat = x.toNat % y.toNat := by
  have hm : U256.mod x y = BitVec.umod x y := if_neg h
  exact (congrArg U256.toNat hm).trans (@BitVec.toNat_umod 256 x y)

lemma U128.lt_or_eq_of_le {n m : U128} (h : n ≤ m) : n < m ∨ n = m := by
  rcases h with h | h
  · left; left; apply h
  · rcases UInt64.lt_or_eq_of_le h.2 with h' | h'
    · left; right; refine ⟨h.1, h'⟩
    · right; apply Prod.ext h.1 h'

lemma U256.lt_or_eq_of_le {n m : U256} (h : n ≤ m) : n < m ∨ n = m := by
  rcases Nat.lt_or_eq_of_le (BitVec.le_def.mp h) with h' | h'
  · exact Or.inl (BitVec.lt_def.mpr h')
  · exact Or.inr (U256.toNat_inj _ _ h')

lemma U128.le_refl (x : U128) : x ≤ x := by
  right; refine ⟨rfl, UInt64.le_refl _⟩

lemma U256.le_refl (x : U256) : x ≤ x := BitVec.le_def.mpr (Nat.le_refl _)

lemma U128.le_of_lt_or_eq {n m : U128} (h : n < m ∨ n = m) : n ≤ m := by
  rcases h with (h | ⟨h, h'⟩) | h
  · left; apply h
  · right; refine' ⟨h, UInt64.le_of_lt h'⟩
  · rw [h]; apply le_refl

lemma U128.lt_iff (x y : U128) :
  x < y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)) := Iff.refl _

lemma U128.le_iff (x y : U128) :
    x ≤ y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)) := Iff.refl _

lemma U128.le_iff_lt_or_eq {n m : U128} : n ≤ m ↔ (n < m ∨ n = m) :=
  ⟨U128.lt_or_eq_of_le, U128.le_of_lt_or_eq⟩

lemma U128.le_or_gt (a b : U128) : a ≤ b ∨ a > b := by
  simp [GT.gt]; rw [U128.le_iff, U128.lt_iff];
  rcases UInt64.le_or_lt a.1 b.1 with h | h
  · rcases UInt64.lt_or_eq_of_le h with h' | h'
    · left; left; apply h'
    · rcases UInt64.le_or_lt a.2 b.2 with h'' | h''
      · left; right; refine ⟨h', h''⟩
      · right; right; refine ⟨h'.symm, h''⟩
  · right; left; apply h

lemma U128.lt_or_ge (a b : U128) : a < b ∨ a ≥ b :=
  Or.symm <| U128.le_or_gt _ _

lemma U256.le_or_gt (a b : U256) : a ≤ b ∨ a > b := by
  rcases Nat.lt_or_ge b.toNat a.toNat with h | h
  · exact Or.inr (BitVec.lt_def.mpr h)
  · exact Or.inl (BitVec.le_def.mpr h)

lemma Nat.lt_of_lt_high {sz high low high' low' : Nat}
    (h_high : high < high') (h_low : low < sz) :
    high * sz + low < high' * sz + low' := by
  rcases high' with _ | high'
  · cases Nat.not_lt_zero _ h_high
  · have h_le := Nat.le_of_lt_succ h_high
    rw [Nat.succ_mul, Nat.add_assoc]
    apply @Nat.add_lt_add_of_le_of_lt
    · apply Nat.mul_le_mul_right _ h_le
    · apply Nat.lt_add_right _ h_low

lemma Nat.shl_or_lt_shl_or_of_left {k m n m' n' : Nat}
    (m_lt_m' : m < m') (n_lt : n < 2 ^ k) (n'_lt : n' < 2 ^ k) :
    m <<< k ||| n < m' <<< k ||| n' := by
  rw [← Nat.add_eq_or two_pow_dvd_shl n_lt]
  rw [← Nat.add_eq_or two_pow_dvd_shl n'_lt]
  simp only [Nat.shiftLeft_eq]
  apply lt_of_lt_high m_lt_m' n_lt

lemma Nat.shl_or_lt_shl_or_of_right {k m n n' : Nat}
    (n_lt : n < n') (n'_lt : n' < 2 ^ k) :
    m <<< k ||| n < m <<< k ||| n' := by
  rw [← Nat.add_eq_or two_pow_dvd_shl (lt_trans n_lt n'_lt)]
  rw [← Nat.add_eq_or two_pow_dvd_shl n'_lt]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.add_lt_add_iff_left]; apply n_lt

lemma U128.toNat_lt_toNat {a b : U128} (h : a < b) :
    a.toNat < b.toNat := by
  rcases a with ⟨_, _⟩; rcases b with ⟨_, _⟩
  rcases h with h | h <;> simp at h
  · rw [UInt64.lt_iff_toNat_lt] at h
    apply Nat.shl_or_lt_shl_or_of_left h (UInt64.toNat_lt _) (UInt64.toNat_lt _)
  · rw [h.1]; apply Nat.shl_or_lt_shl_or_of_right _ (UInt64.toNat_lt _)
    rw [← UInt64.lt_iff_toNat_lt]; apply h.2

lemma U128.toNat_le_toNat {a b : U128} (h : a ≤ b) : a.toNat ≤ b.toNat := by
  rcases U128.lt_or_eq_of_le h with h | h
  · apply Nat.le_of_lt <| U128.toNat_lt_toNat h
  · rw [h]

lemma U128.lt_of_toNat_lt_toNat {a b : U128} (lt : a.toNat < b.toNat) : a < b := by
  rcases U128.le_or_gt b a with h | h
  · cases not_le_of_gt lt <| U128.toNat_le_toNat h
  · apply h

lemma U128.lt_iff_toNat_lt_toNat {a b : U128} : a < b ↔ a.toNat < b.toNat := by
  constructor
  · apply U128.toNat_lt_toNat
  · apply U128.lt_of_toNat_lt_toNat

lemma U256.toNat_lt_toNat {a b : U256} (h : a < b) :
    a.toNat < b.toNat := BitVec.lt_def.mp h

lemma U128.le_of_lt {a b : U128} (h : a < b) : a ≤ b := by
  rcases h with h | h
  · left; apply h
  · right; refine' ⟨h.1, UInt64.le_of_lt h.2⟩

lemma U256.le_of_lt {a b : U256} (h : a < b) : a ≤ b :=
  BitVec.le_def.mpr (Nat.le_of_lt (BitVec.lt_def.mp h))

lemma U256.le_of_lt_or_eq {n m : U256} (h : n < m ∨ n = m) : n ≤ m := by
  rcases h with h | h
  · exact U256.le_of_lt h
  · subst h; exact U256.le_refl _

lemma U256.le_iff_lt_or_eq {n m : U256} : n ≤ m ↔ (n < m ∨ n = m) :=
  ⟨U256.lt_or_eq_of_le, U256.le_of_lt_or_eq⟩

lemma U256.toNat_le_toNat {a b : U256} (h : a ≤ b) : a.toNat ≤ b.toNat :=
  BitVec.le_def.mp h

lemma U256.lt_of_toNat_lt_toNat {a b : U256} (lt : a.toNat < b.toNat) : a < b :=
  BitVec.lt_def.mpr lt

lemma U256.lt_iff_toNat_lt_toNat {a b : U256} : a < b ↔ a.toNat < b.toNat :=
  BitVec.lt_def

lemma U128.not_lt {a b : U128} : ¬ a < b ↔ b ≤ a := by
  simp [U128.lt_iff, U128.le_iff]
  rw [@Eq.comm _ a.1 b.1, @UInt64.le_iff_lt_or_eq b.1 a.1]
  aesop

lemma U128.lt_irrefl (x : U128) : ¬ x < x := by
  intro h; rcases h with h | h <;> simp at h

lemma U256.lt_irrefl (x : U256) : ¬ x < x := by
  rw [U256.lt_iff_toNat_lt_toNat]; exact Nat.lt_irrefl _

lemma U256.not_lt {a b : U256} : ¬ a < b ↔ b ≤ a := by
  rw [U256.lt_iff_toNat_lt_toNat, Nat.not_lt]
  exact BitVec.le_def.symm

lemma U128.not_le {a b : U128} : ¬ a ≤ b ↔ b < a := by
  rw [not_iff_comm, U128.not_lt]

lemma U256.not_le {a b : U256} : ¬ a ≤ b ↔ b < a := by
  rw [not_iff_comm, U256.not_lt]

lemma U128.le_iff_toNat_le_toNat {a b : U128} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [← not_iff_not, not_le, Nat.not_le, lt_iff_toNat_lt_toNat]

lemma U256.le_iff_toNat_le_toNat {a b : U256} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [← not_iff_not, not_le, Nat.not_le, lt_iff_toNat_lt_toNat]

lemma U128.le_of_toNat_le_toNat {a b : U128} : a.toNat ≤ b.toNat → a ≤ b :=
  U128.le_iff_toNat_le_toNat.mpr

lemma U256.le_of_toNat_le_toNat {a b : U256} : a.toNat ≤ b.toNat → a ≤ b :=
  U256.le_iff_toNat_le_toNat.mpr

lemma Nat.lo_add_lo (m n k : ℕ) : (m ↾ k + n) ↾ k = (m + n) ↾ k :=
  Nat.mod_add_mod _ _ _

lemma U128.toNat_add (x y : U128) :
    (x + y).toNat = (x.toNat + y.toNat) ↾ 128 := by
  rw [U128.add_eq]; simp only [U128.toNat]
  rw [Nat.shl_or_add_shl_or_lo_add (UInt64.toNat_lt _) (UInt64.toNat_lt _)]
  apply congr_arg₂ _ (congr_arg₂ _ _ rfl) (UInt64.toNat_add_lo _ _)
  rw [UInt64.toNat_add_lo, UInt64.toNat_add_lo, Nat.lo_add_lo]
  apply congr_arg₂ _ (congr_arg₂ _ rfl _) rfl
  rw [← ite_not, @ite_distrib _ _ UInt64.toNat]
  apply ite_eq_ite_of_iff _ rfl rfl
  simp [UInt64.toNat_overflow]

lemma U128.toNat_overflow {x y : U128} :
    x + y < x ↔ 2 ^ 128 ≤ x.toNat + y.toNat := by
  rw [U128.lt_iff_toNat_lt_toNat, U128.toNat_add]
  by_cases h : x.toNat + y.toNat < 2 ^ 128
  · rw [Nat.lo_eq_of_lt h]
    apply iff_of_false <;> omega
  · rw [_root_.not_lt] at h; apply iff_of_true _ h
    have x_lt := @U128.toNat_lt x
    have y_lt := @U128.toNat_lt y
    rw [Nat.lo, Nat.add_mod_eq_add_sub x_lt y_lt h]
    omega

lemma U256.toNat_add (x y : U256) :
    (x + y).toNat = (x.toNat + y.toNat) ↾ 256 := BitVec.toNat_add _ _

/-- No-overflow predicate for `B256` addition. -/
def U256.AddNoOverflow (xs ys : U256) : Prop := xs.toNat + ys.toNat < 2 ^ 256

lemma U256.toNat_add_eq_of_add_no_overflow (x y : U256) (h : U256.AddNoOverflow x y) :
    (x + y).toNat = (x.toNat + y.toNat) := by
  rw [U256.toNat_add, Nat.lo_eq_of_lt h]

theorem U256.add_comm {xs ys : U256} : xs + ys = ys + xs := by
  apply U256.toNat_inj
  rw [U256.toNat_add, U256.toNat_add, Nat.add_comm]

lemma toUInt32_toUInt64 (n : UInt32) : n.toUInt64.toUInt32 = n :=
  UInt32.toUInt32_toUInt64 n

lemma Address.toNat_lt (a : Address) : a.toNat < 2 ^ 160 := by
  simp only [Address.toNat]
  apply Nat.or_lt_two_pow
  · apply Nat.shiftLeft_lt_of_lt (UInt32.toNat_lt _)
  · exact lt_trans U128.toNat_lt (by omega)

def U256.toAddress (x : U256) : Address := x.toNat.toAddress

def Address.toU256 (a : Address) : U256 := Nat.toU256 a.toNat

lemma toAddress_toU256 (a : Address) : a.toU256.toAddress = a := by
  rw [U256.toAddress, Address.toU256,
    U256.toNat_toU256_of_lt (Nat.lt_trans a.toNat_lt (by omega))]
  -- proved by `toAddress_toNat` below; direct proof:
  simp only [Nat.toAddress, Address.toNat]
  apply Prod.ext <;> simp
  · rw [Nat.shiftRight_or_distrib, Nat.shiftLeft_shiftRight]
    rw [Nat.shiftRight_eq_zero _ _ U128.toNat_lt, Nat.or_zero]
    apply toUInt32_toNat
  · rw [toU128_or]
    have eq : (a.1.toNat <<< 128).toU128 = 0 := by
      rw [toU128_eq_iff_lo_eq_toNat, Nat.shl_lo_eq_zero_of_le (by omega)]
      rfl
    rw [eq, U128.zero_or, toU128_toNat]

theorem Address.toU256_inj {x y : Address} (eq : x.toU256 = y.toU256) : x = y := by
  rw [← toAddress_toU256 x, ← toAddress_toU256 y, eq]

lemma UInt64.toNat_sub_lo {a b : UInt64} :
    (a - b).toNat = (2 ^ 64 + a.toNat - b.toNat) ↾ 64 := by
  apply Eq.trans (UInt64.toNat_sub _ _)
  apply congr_arg₂ _ _ rfl
  rw [Nat.sub_add_comm <| Nat.le_of_lt (UInt64.toNat_lt _)]

lemma Nat.add_mul_self_mod (x y z : ℕ) : (x + y * z) % z = x % z := by
  induction y with
  | zero => simp
  | succ y ih => rw [succ_mul, ← Nat.add_assoc, add_mod_right, ih]

lemma Nat.sub_mod_eq_sub_mod_right {a d c b : Nat}
    (eq : a % d = b % d) (le_a : c ≤ a) (le_b : c ≤ b) :
    (a - c) % d = (b - c) % d := by
  rcases d with _ | d
  · simp at *; rw [eq]
  · rw [← add_mul_self_mod _ c, ← add_mul_self_mod (b - c) c]
    rw [← Nat.sub_add_comm le_a, ← Nat.sub_add_comm le_b]
    rw [Nat.add_sub_assoc (Nat.le_mul_of_pos_right _ (by omega))]
    rw [Nat.add_sub_assoc (Nat.le_mul_of_pos_right _ (by omega))]
    apply Nat.add_mod_eq_add_mod_right _ eq

lemma Nat.two_pow_add_lo (x y : Nat) : (2 ^ x + y) ↾ x = y ↾ x :=
  Nat.add_mod_left _ _

lemma U128.toNat_sub {a b : U128} :
    (a - b).toNat = (2 ^ 128 + a.toNat - b.toNat) ↾ 128 := by
  rw [U128.sub_eq]; simp only [U128.toNat]
  rw [Nat.add_shl_or_sub_shl_or_lo_add (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)]
  apply congr_arg₂ _ (congr_arg₂ _ _ rfl) UInt64.toNat_sub_lo
  simp only [UInt64.toNat_sub_lo]
  rw [@ite_distrib _ _ UInt64.toNat, UInt64.toNat_one, UInt64.toNat_zero]
  rw [← ite_eq_ite_of_iff UInt64.lt_iff_toNat_lt rfl rfl]
  apply Nat.sub_mod_eq_sub_mod_right
  · rw [Nat.add_mod_left]; apply Nat.lo_lo
  · split <;> omega
  · have _ := @UInt64.toNat_lt b.1; split <;> omega

lemma U128.toNat_zero : U128.toNat 0 = 0 := rfl
lemma U128.toNat_one : U128.toNat 1 = 1 := rfl

lemma U256.toNat_zero : (0 : U256).toNat = 0 := rfl

lemma U256.zero_ne_one : (0 : U256) ≠ 1 := by decide

lemma U256.toNat_sub (a b : U256) :
    (a - b).toNat = (2 ^ 256 + a.toNat - b.toNat) ↾ 256 := by
  rw [show (a - b).toNat = ((2 ^ 256 - b.toNat + a.toNat) % 2 ^ 256) from BitVec.toNat_sub _ _]
  have hb := U256.toNat_lt b
  rw [Nat.lo_eq, show 2 ^ 256 + a.toNat - b.toNat = 2 ^ 256 - b.toNat + a.toNat by omega]

theorem U256.toNat_sub_eq_of_le (xs ys : U256) (h : ys ≤ xs) :
    (xs - ys).toNat = xs.toNat - ys.toNat := by
  rw [toNat_sub, Nat.lo, Nat.add_sub_mod_eq_sub]
  · apply U256.toNat_lt
  · apply U256.toNat_le_toNat h

lemma U128.lt_asymm {a b : U128} (h : a < b) : ¬ b < a := by
  intro h'; rcases h with h | h <;> rcases h' with h' | h'
  · cases UInt64.lt_asymm h h'
  · rw [h'.1] at h; cases UInt64.lt_irrefl _ h
  · rw [h.1] at h'; cases UInt64.lt_irrefl _ h'
  · cases UInt64.lt_asymm h.2 h'.2

lemma U256.lt_asymm {a b : U256} (h : a < b) : ¬ b < a := by
  rw [U256.lt_iff_toNat_lt_toNat] at h ⊢
  omega

lemma U128.lt_iff_le_not_ge {a b : U128} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [not_le, ← not_lt]; simp; apply lt_asymm

lemma U256.lt_iff_le_not_ge {a b : U256} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [not_le, ← not_lt]; simp; apply lt_asymm

lemma U128.lt_trans {a b c : U128} (ab : a < b) (bc : b < c) : a < c := by
  rcases ab with ab | ab <;> rcases bc with bc | bc
  · left; apply UInt64.lt_trans ab bc
  · left; rw [← bc.1]; exact ab
  · left; rw [ab.1]; exact bc
  · right; refine ⟨Eq.trans ab.1 bc.1, UInt64.lt_trans ab.2 bc.2⟩

lemma U128.le_trans {a b c : U128} (ab : a ≤ b) (bc : b ≤ c) : a ≤ c := by
  rcases ab with ab | ab <;> rcases bc with bc | bc
  · left; apply UInt64.lt_trans ab bc
  · left; rw [← bc.1]; exact ab
  · left; rw [ab.1]; exact bc
  · right; refine ⟨Eq.trans ab.1 bc.1, UInt64.le_trans ab.2 bc.2⟩

lemma U256.le_trans {a b c : U256} (ab : a ≤ b) (bc : b ≤ c) : a ≤ c := by
  rw [U256.le_iff_toNat_le_toNat] at ab bc ⊢
  exact Nat.le_trans ab bc

instance : Preorder U128 where
  le_refl := U128.le_refl
  le_trans _ _ _ := U128.le_trans
  lt := U128.LT
  lt_iff_le_not_ge _ _ := U128.lt_iff_le_not_ge

instance : Preorder U256 where
  le_refl := U256.le_refl
  le_trans _ _ _ := U256.le_trans
  lt := (· < ·)
  lt_iff_le_not_ge _ _ := U256.lt_iff_le_not_ge

lemma U128.le_antisymm {a b : U128} : a ≤ b → b ≤ a → a = b := by
  intro h₁ h₂; rw [le_iff_lt_or_eq] at h₁ h₂
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · cases U128.lt_asymm h₁ h₂
    · exact h₂.symm
  · exact h₁

lemma U256.le_antisymm {a b : U256} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  rw [U256.le_iff_toNat_le_toNat] at h₁ h₂
  exact U256.toNat_inj _ _ (Nat.le_antisymm h₁ h₂)

instance : PartialOrder U128 where
  le_antisymm _ _ := U128.le_antisymm

instance : PartialOrder U256 where
  le_antisymm _ _ := U256.le_antisymm

lemma U128.le_total (m n : U128) : m ≤ n ∨ n ≤ m := by
  rcases U128.le_or_gt m n with h | h
  · left; apply h
  · right; simp [GT.gt] at h; apply U128.le_of_lt h

lemma U256.le_total (m n : U256) : m ≤ n ∨ n ≤ m := by
  rcases U256.le_or_gt m n with h | h
  · left; apply h
  · right; simp [GT.gt] at h; apply U256.le_of_lt h

instance : Ord U128 where
  compare a b := compareOfLessAndEq a b

instance : Ord U256 where
  compare a b := compareOfLessAndEq a b

instance : LinearOrder U128 where
  le_total := U128.le_total
  toDecidableLE := by infer_instance

instance : LinearOrder U256 where
  le_total := U256.le_total
  toDecidableLE := by infer_instance
  -- `Min B256` resolves to the pre-existing `B256.min` instance from
  -- `Basic.lean` (used by execution's fee/gas clamping), not this class's
  -- default `min` field. `B256.min a b` is literally `if a ≤ b then a else b`,
  -- and the structural `DecidableLE` now unfolds to the same decision procedure
  -- on both sides, so the field closes definitionally while preserving that
  -- instance resolution.
  min_def a b := rfl

lemma U128.sub_self (a : U128) : a - a = 0 := by
  rw [U128.sub_eq]; simp; rfl

lemma U128.sub_zero (x : U128) : x - 0 = x := by
  rw [U128.sub_eq, U128.zero_eq]
  simp
  rfl

lemma U256.sub_self (a : U256) : a - a = 0 := by
  apply U256.toNat_inj
  rw [U256.toNat_sub, U256.toNat_zero]
  have ha := U256.toNat_lt a
  rw [Nat.lo_eq, show 2 ^ 256 + a.toNat - a.toNat = 2 ^ 256 by omega, Nat.mod_self]

lemma U256.sub_zero (x : U256) : x - 0 = x := by
  apply U256.toNat_inj
  rw [U256.toNat_sub_eq_of_le _ _ (by rw [U256.le_iff_toNat_le_toNat, U256.toNat_zero]; omega),
    U256.toNat_zero, Nat.sub_zero]

lemma U256.add_zero (x : U256) : x + 0 = x := by
  apply U256.toNat_inj
  rw [U256.toNat_add, U256.toNat_zero, Nat.add_zero]
  exact Nat.lo_eq_of_lt (U256.toNat_lt x)

lemma U256.zero_le (x : U256) : (0 : U256) ≤ x := by
  rw [U256.le_iff_toNat_le_toNat, U256.toNat_zero]
  omega

def Address.LE (x y : Address) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
instance : @LE Address := ⟨Address.LE⟩
instance {x y : Address} : Decidable (x ≤ y) := instDecidableOr

lemma Address.le_iff (x y : Address) :
  x ≤ y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)) := Iff.refl _

lemma Address.le_refl (x : Address) : x ≤ x := by
  right; refine ⟨rfl, U128.le_refl _⟩

lemma Address.le_trans {a b c : Address} (ab : a ≤ b) (bc : b ≤ c) : a ≤ c := by
  rcases ab with ab | ab <;> rcases bc with bc | bc
  · left; apply UInt32.lt_trans ab bc
  · left; rw [← bc.1]; exact ab
  · left; rw [ab.1]; exact bc
  · right; refine ⟨Eq.trans ab.1 bc.1, U128.le_trans ab.2 bc.2⟩

def Address.LT (x y : Address) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)
instance : @LT Address := ⟨Address.LT⟩
instance {x y : Address} : Decidable (x < y) := instDecidableOr

lemma Address.lt_iff (x y : Address) :
  x < y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)) := Iff.refl _

lemma Address.lt_iff_le_not_ge {a b : Address} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  constructor <;> intro h
  · rcases h with h | h
    · refine' ⟨.inl h, not_or_intro (UInt32.lt_asymm h) _⟩
      apply not_and_of_not_left _ <| Ne.symm <| UInt32.ne_of_lt h
    · refine' ⟨.inr ⟨h.1, U128.le_of_lt h.2⟩, not_or_intro _ _⟩
      · rw [h.1]; apply UInt32.lt_irrefl
      · apply not_and_of_not_right; rw [U128.not_le]; apply h.2
  · rcases h with ⟨h | ⟨h1, h2⟩, h'⟩
    · apply Or.inl h
    · rcases not_or.mp h' with ⟨h1', h2'⟩
      right; refine' ⟨h1, U128.lt_iff_le_not_ge.mpr ⟨h2, not_and.mp h2' h1.symm⟩⟩

instance : Preorder Address where
  le_refl := Address.le_refl
  le_trans _ _ _ := Address.le_trans
  lt := Address.LT
  lt_iff_le_not_ge _ _ := Address.lt_iff_le_not_ge

lemma Address.le_antisymm {a b : Address} : a ≤ b → b ≤ a → a = b := by
  intro h₁ h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · cases lt_asymm h₁ h₂
  · cases UInt32.ne_of_lt h₁ h₂.1.symm
  · cases UInt32.ne_of_lt h₂ h₁.1.symm
  · exact Prod.ext h₁.1 <| U128.le_antisymm h₁.2 h₂.2

instance : PartialOrder Address where
  le_antisymm _ _ := Address.le_antisymm

lemma Address.le_total (m n : Address) : m ≤ n ∨ n ≤ m := by
  by_cases h : m.1 < n.1
  · left; left; exact h
  · rw [not_lt, UInt32.le_iff_lt_or_eq] at h
    rcases h with h | h
    · right; left; exact h
    · rcases U128.le_total m.2 n.2 with h' | h'
      · left; right; refine ⟨h.symm, h'⟩
      · right; right; refine ⟨h, h'⟩

instance : DecidableEq Address :=
  inferInstanceAs (DecidableEq (UInt32 × U128))

instance : Ord Address where
  compare a b := compareOfLessAndEq a b

instance : LinearOrder Address where
  le_total := Address.le_total
  toDecidableLE := by infer_instance

lemma Address.lt_asymm {a b : Address} (h : a < b) : ¬ b < a := by
  intro h'; rcases h with h | h <;> rcases h' with h' | h'
  · cases UInt32.lt_asymm h h'
  · rw [h'.1] at h; cases UInt32.lt_irrefl _ h
  · rw [h.1] at h'; cases UInt32.lt_irrefl _ h'
  · cases U128.lt_asymm h.2 h'.2

lemma Address.lt_irrefl (x : Address) : ¬ x < x := by
  intro h; rcases h with h | h <;> simp at h

-- Both map key orders are *lawful for equality*: `compareOfLessAndEq` answers
-- `.eq` only on the `DecidableEq` branch, so it never conflates two distinct
-- keys. `Std.TransCmp` is already inferred for both from their `LinearOrder`s;
-- these two instances supply the missing half, and together they are what lets
-- a `Std.TreeMap` lookup be read off the map's finite `toList` -- the finite
-- traversal that `Stor.Canonical` and `State.Canonical` are defined by. Without
-- them the only route to a decision procedure would quantify over every `B256`
-- or `Adr`, which is exactly what those predicates must avoid.
private theorem lawfulEqCmp_of_compareOfLessAndEq {α : Type u}
    [Ord α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.ReflCmp (compare : α → α → Ordering)]
    (h : ∀ a b : α, (compare a b : Ordering) = compareOfLessAndEq a b) :
    Std.LawfulEqCmp (compare : α → α → Ordering) := by
  constructor
  intro a b hab
  rw [h a b] at hab
  unfold compareOfLessAndEq at hab
  split at hab
  · exact absurd hab (by simp)
  · split at hab
    · assumption
    · exact absurd hab (by simp)

instance : Std.LawfulEqCmp (compare : U256 → U256 → Ordering) :=
  lawfulEqCmp_of_compareOfLessAndEq (fun _ _ => rfl)

instance : Std.LawfulEqCmp (compare : Address → Address → Ordering) :=
  lawfulEqCmp_of_compareOfLessAndEq (fun _ _ => rfl)

theorem U256.sub_add_cancel {x y : U256} : x - y + y = x := by
  apply U256.toNat_inj
  simp only [U256.toNat_add, U256.toNat_sub]
  have x_lt : x.toNat < 2 ^ 256 := U256.toNat_lt _
  have y_lt : y.toNat < 2 ^ 256 := U256.toNat_lt _
  revert x_lt; revert y_lt
  generalize x.toNat = x, y.toNat = y
  intros y_lt x_lt
  by_cases h : x < y
  · rw [@Nat.lo_eq_of_lt (2 ^ 256 + x - y) _ (by omega)]
    rw [Nat.sub_add_cancel (by omega)]
    rw [Nat.two_pow_add_lo, Nat.lo_eq_of_lt x_lt]
  · rw [Nat.not_lt] at h
    rw [Nat.add_sub_assoc h, Nat.two_pow_add_lo]
    rw [Nat.lo_eq_of_lt (by {rw [Nat.lo]; omega})]
    rw [Nat.lo_eq_of_lt (by omega)]
    apply Nat.sub_add_cancel h

lemma toAddress_toNat (a : Address) : a.toNat.toAddress = a := by
  simp only [Nat.toAddress, Address.toNat]
  apply Prod.ext <;> simp
  · rw [Nat.shiftRight_or_distrib, Nat.shiftLeft_shiftRight]
    rw [Nat.shiftRight_eq_zero _ _ U128.toNat_lt, Nat.or_zero]
    apply toUInt32_toNat
  · rw [toU128_or]
    have eq : (a.1.toNat <<< 128).toU128 = 0 := by
      rw [toU128_eq_iff_lo_eq_toNat]
      rw [Nat.shl_lo_eq_zero_of_le (by omega)]
      rfl
    rw [eq, U128.zero_or]
    apply toU128_toNat

def Address.toHex (a : Address) : String := a.1.toHex ++ a.2.toHex

instance : ToString Address := ⟨Address.toHex⟩

def String.dropZeroes (s : String) : String :=
  match String.ofList (s.toList.dropWhile (· == '0')) with
  | "" => "0"
  | s => s

def Storage := Std.TreeMap U256 U256 compare

def Storage.get (s : Storage) (k : U256) : U256 := s.getD k 0
def Storage.empty : Storage := Std.TreeMap.empty

lemma Std.TreeMap.eq_empty_of_isEmpty {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} (h : t.isEmpty = true) :
    t = Std.TreeMap.empty := by
  rcases t with ⟨⟨dt, wf⟩⟩
  simp [Std.TreeMap.isEmpty, Std.DTreeMap.isEmpty] at h
  cases dt
  · simp [Std.DTreeMap.Internal.Impl.isEmpty] at h
  · rfl

@[ext]
structure Account where
  (nonce : UInt64)
  (balance : U256)
  (storage : Storage)
  (code : ByteArray)

def Account.withBalance (a : Account) (bal : U256) : Account :=
  {a with balance := bal}

-- An address is exactly twenty bytes. The trailing `[]` is load-bearing: a
-- twenty-one-byte list is a malformed address, not an address with a tail to
-- ignore. Accepting the prefix let an overlong RLP field survive decoding and
-- be rejected later, if at all, for the wrong reason (finding 3.6). Every
-- caller already supplies exactly twenty bytes -- `ByteArray.sliceD _ 20`, the
-- low twenty bytes of a keccak hash, or a checked consensus field -- so the
-- rejection is new only for untrusted input.
def Bytes.toAddress? : Bytes → Option Address
  | x0 :: x1 :: x2 :: x3 ::
    y0 :: y1 :: y2 :: y3 ::
    y4 :: y5 :: y6 :: y7 ::
    z0 :: z1 :: z2 :: z3 ::
    z4 :: z5 :: z6 :: z7 :: [] =>
    some ⟨
      UInt32.ofBytes x0 x1 x2 x3,
      UInt64.ofBytes y0 y1 y2 y3 y4 y5 y6 y7,
      UInt64.ofBytes z0 z1 z2 z3 z4 z5 z6 z7,
    ⟩
  | _ => none

def Hex.toAddress? (hx : String) : Option Address := Hex.toBytes hx >>= Bytes.toAddress?

------------------- STRICT CONSENSUS-FIELD DECODING --------------------

-- RLP bytes are untrusted consensus input, so a field's *shape* must be
-- checked before its value is converted, never after. The conversions
-- themselves (`Bytes.toUInt64`, `Bytes.toB256`) pad or truncate to a fixed width
-- through `Bytes.pack`, which silently turns a nine-byte withdrawal index into a
-- plausible eight-byte one; the encode-and-compare round trip then reports the
-- corruption as a generic RLP mismatch, long after the value was lost.
--
-- The helpers below are the pure shape checks, one per shape the consensus
-- fields actually have. They are deliberately value-level and error-free:
-- `Jaune/Execution.lean` wraps each one with the tagged error naming the
-- precise reason, which is what a fixture exception identity is mapped from.

/-- A fixed-width field: the length must equal `n` exactly. -/
def Bytes.toFixed? (n : Nat) (xs : Bytes) : Option Bytes :=
  if xs.length = n then some xs else none

/-- Is this a canonical unsigned scalar of at most `n` bytes?

Two independent conditions, both required by RLP: the width must fit, and the
encoding must be canonical -- zero is the empty byte string, and a nonempty
scalar never begins with a zero byte. `Execution.lean` distinguishes the two
failures, since only one of them is a field-overflow. -/
def Bytes.isCanonicalScalar (n : Nat) (xs : Bytes) : Bool :=
  (xs.length ≤ n) && (xs.head? != some (0 : UInt8))

/-- A canonical unsigned scalar of at most `n` bytes, as a `Nat`. -/
def Bytes.toScalarNat? (n : Nat) (xs : Bytes) : Option Nat :=
  if xs.isCanonicalScalar n then some xs.toNat else none

/-- A canonical 64-bit scalar: at most eight bytes, hence converted without
truncation. Note this is *not* `Bytes.toUInt64?`, which demands exactly eight bytes
and so rejects every valid small integer. -/
def Bytes.toScalarUInt64? (xs : Bytes) : Option UInt64 :=
  if xs.isCanonicalScalar 8 then some xs.toUInt64 else none

/-- A canonical 256-bit scalar: at most thirty-two bytes, hence converted
without truncation. -/
def Bytes.toScalarU256? (xs : Bytes) : Option U256 :=
  if xs.isCanonicalScalar 32 then some xs.toU256 else none

/-- An optional contract-creation receiver: either empty, meaning creation, or
exactly twenty bytes. Anything else is malformed rather than a creation. -/
def Bytes.toReceiver? : Bytes → Option (Option Address)
  | [] => some none
  | xs => xs.toAddress?.map some

--------------- CHECKED JSON QUANTITY DECODING ----------------

-- Test-fixture JSON states quantities in its own syntax, which is *not* RLP's
-- minimal-scalar syntax: a fixture may write a balance with leading zero bytes,
-- or the empty string for zero, and both are well formed there. Only the width
-- conversion is shared with the strict consensus-field decoders above; the
-- canonicality half deliberately is not, because imposing a leading-zero rule
-- here would reject inputs the pinned source calls valid.
--
-- What was wrong was the other direction. The fixture parser converted these
-- fields with the raw `Bytes.toUInt64` / `Bytes.toB256`, which pad short values
-- and silently *truncate* long ones -- a thirty-three-byte balance became its
-- low 256 bits and a nine-byte nonce its rightmost eight bytes, with no error
-- and no trace. The two decoders below keep the short-value acceptance and
-- reject the over-long input outright, which is the whole change.

/-- A JSON quantity of at most eight bytes, converted without truncation.
Unlike `Bytes.toUInt64?` it accepts every shorter width, and unlike
`Bytes.toScalarB64?` it imposes no leading-zero rule. -/
def Bytes.toQuantityUInt64? (xs : Bytes) : Option UInt64 :=
  if xs.length ≤ 8 then some xs.toUInt64 else none

/-- A JSON quantity of at most thirty-two bytes, converted without
truncation. -/
def Bytes.toQuantityU256? (xs : Bytes) : Option U256 :=
  if xs.length ≤ 32 then some xs.toU256 else none

-- Parser soundness. Acceptance is exactly "the width fits", the accepted value
-- is exactly the old conversion -- so nothing a fixture previously parsed can
-- change value -- and rejection is exactly "the width does not fit".

theorem Bytes.toQuantityUInt64?_eq_some_iff {xs : Bytes} {v : UInt64} :
    Bytes.toQuantityUInt64? xs = some v ↔ xs.length ≤ 8 ∧ xs.toUInt64 = v := by
  rw [Bytes.toQuantityUInt64?]; split <;> simp_all

theorem Bytes.toQuantityUInt64?_eq_none_iff {xs : Bytes} :
    Bytes.toQuantityUInt64? xs = none ↔ 8 < xs.length := by
  rw [Bytes.toQuantityUInt64?]; split <;> simp_all

theorem Bytes.toQuantityU256?_eq_some_iff {xs : Bytes} {v : U256} :
    Bytes.toQuantityU256? xs = some v ↔ xs.length ≤ 32 ∧ xs.toU256 = v := by
  rw [Bytes.toQuantityU256?]; split <;> simp_all

theorem Bytes.toQuantityU256?_eq_none_iff {xs : Bytes} :
    Bytes.toQuantityU256? xs = none ↔ 32 < xs.length := by
  rw [Bytes.toQuantityU256?]; split <;> simp_all

/-- Round trip through the canonical fixed-width encoder. -/
theorem Bytes.toQuantityUInt64?_toBytes (x : UInt64) :
    Bytes.toQuantityUInt64? (UInt64.toBytes x) = some x := by
  rw [Bytes.toQuantityUInt64?, ite_eq_left (by rw [UInt64.length_toBytes])]
  rw [UInt64.toUInt64_toBytes]

theorem Bytes.toQuantityU256?_toBytes (x : U256) :
    Bytes.toQuantityU256? x.toBytes = some x := by
  rw [Bytes.toQuantityU256?, ite_eq_left (by rw [U256.length_toBytes])]
  rw [U256.toU256_toBytes]

/-- Strictly weaker than the exact-width decoder: whatever `Bytes.toUInt64?`
accepts, this accepts with the same value. -/
theorem Bytes.toQuantityUInt64?_of_toUInt64? {xs : Bytes} {v : UInt64}
    (h : Bytes.toUInt64? xs = some v) : Bytes.toQuantityUInt64? xs = some v := by
  rw [Bytes.toUInt64?] at h; split at h
  · rw [Bytes.toQuantityUInt64?, ite_eq_left (by omega)]; exact h
  · cases h

/-- And strictly weaker than the RLP scalar decoder, whose extra condition is
the leading-zero rule this one deliberately drops. -/
theorem Bytes.toQuantityUInt64?_of_toScalarUInt64? {xs : Bytes} {v : UInt64}
    (h : Bytes.toScalarUInt64? xs = some v) : Bytes.toQuantityUInt64? xs = some v := by
  rw [Bytes.toScalarUInt64?] at h; split at h
  · rename_i hc
    rw [Bytes.isCanonicalScalar] at hc
    rw [Bytes.toQuantityUInt64?, ite_eq_left (by simp_all)]; exact h
  · cases h

theorem Bytes.toQuantityU256?_of_toScalarU256? {xs : Bytes} {v : U256}
    (h : Bytes.toScalarU256? xs = some v) : Bytes.toQuantityU256? xs = some v := by
  rw [Bytes.toScalarU256?] at h; split at h
  · rename_i hc
    rw [Bytes.isCanonicalScalar] at hc
    rw [Bytes.toQuantityU256?, ite_eq_left (by simp_all)]; exact h
  · cases h

def Address.toBytes (a : Address) : Bytes := a.1.toBytes ++ a.2.toBytes

inductive PlainOp : Type
  | add -- 0x01 / 2 / 1 / addition operation.
  | mul -- 0x02 / 2 / 1 / multiplication operation.
  | sub -- 0x03 / 2 / 1 / subtraction operation.
  | div -- 0x04 / 2 / 1 / integer division operation.
  | sdiv -- 0x05 / 2 / 1 / signed integer division operation.
  | mod -- 0x06 / 2 / 1 / modulo operation.
  | smod -- 0x07 / 2 / 1 / signed modulo operation.
  | addmod -- 0x08 / 3 / 1 / modulo addition operation.
  | mulmod -- 0x09 / 3 / 1 / modulo multiplication operation.
  | exp -- 0x0A / 2 / 1 / exponentiation operation.
  | signextend -- 0x0B / 2 / 1 / sign extend operation.
  | lt -- 0x10 / 2 / 1 / less-than comparison.
  | gt -- 0x11 / 2 / 1 / greater-than comparison.
  | slt -- 0x12 / 2 / 1 / signed less-than comparison.
  | sgt -- 0x13 / 2 / 1 / signed greater-than comparison.
  | eq -- 0x14 / 2 / 1 / equality comparison.
  | iszero -- 0x15 / 1 / 1 / tests if the input is zero.
  | and -- 0x16 / 2 / 1 / bitwise and operation.
  | or -- 0x17 / 2 / 1 / bitwise or operation.
  | xor -- 0x18 / 2 / 1 / bitwise xor operation.
  | not -- 0x19 / 1 / 1 / bitwise not operation.
  | byte -- 0x1A / 2 / 1 / retrieve a single Byte from a Word.
  | shl -- 0x1B / 2 / 1 / logical shift left operation.
  | shr -- 0x1C / 2 / 1 / logical shift right operation.
  | sar -- 0x1D / 2 / 1 / arithmetic (signed) shift right operation.
  | clz -- 0x1E / 1 / 1 / count leading zero bits (Osaka and later only).
  | keccak256 -- 0x20 / 2 / 1 / compute Keccak-256 hash.
  | address -- 0x30 / 0 / 1 / Get the Addr of the currently executing account.
  | balance -- 0x31 / 1 / 1 / Get the balance of the specified account.
  | origin -- 0x32 / 0 / 1 / Get the Addr that initiated the current transaction.
  | caller -- 0x33 / 0 / 1 / Get the Addr that directly called the currently executing contract.
  | callvalue -- 0x34 / 0 / 1 / Get the value (in wei) sent with the current transaction.
  | calldataload -- 0x35 / 1 / 1 / Load input data from the current transaction.
  | calldatasize -- 0x36 / 0 / 1 / Get the size of the input data from the current transaction.
  | calldatacopy -- 0x37 / 3 / 0 / Copy input data from the current transaction to Memory.
  | codesize -- 0x38 / 0 / 1 / Get the size of the code of the currently executing contract.
  | codecopy -- 0x39 / 3 / 0 / Copy the code of the currently executing contract to memory.
  | gasprice -- 0x3a / 0 / 1 / Get the gas price of the current transaction.
  | extcodesize -- 0x3B / 1 / 1 / Get the size of the code of an external account.
  | extcodecopy -- 0x3C / 4 / 0 / Copy the code of an external account to memory.
  | returndatasize -- 0x3D / 0 / 1 / Get the size of the output data from the previous call.
  | returndatacopy -- 0x3E / 3 / 0 / Copy output data from the previous call to memory.
  | extcodehash -- 0x3F / 1 / 1 / Get the code hash of an external account.
  | blockhash -- 0x40 / 1 / 1 / get the hash of the specified block.
  | coinbase -- 0x41 / 0 / 1 / get the Addr of the current block's miner.
  | timestamp -- 0x42 / 0 / 1 / get the timestamp of the current block.
  | number -- 0x43 / 0 / 1 / get the current block number.
  | prevrandao -- 0x44 / 0 / 1 / get the latest RANDAO mix of the post beacon state of the previous block.
  | gaslimit -- 0x45 / 0 / 1 / get the gas limit of the current block.
  | chainid -- 0x46 / 0 / 1 / get the chain id of the current blockchain.
  | selfbalance -- 0x47 / 0 / 1 / get the balance of the currently executing account.
  | basefee -- 0x48 / 0 / 1 / get the current block's base fee.
  | blobhash -- 0x49 / 1 / 1 /
  | blobbasefee -- 0x4A / 0 / 1 / get the current block's blob base fee.
  | slotnum -- 0x4B / 0 / 1 / get the current block's consensus slot number (Amsterdam and later only).
  | pop -- 0x50 / 1 / 0 / Remove an item from the Stack.
  | mload -- 0x51 / 1 / 1 / Load a Word from memory.
  | mstore -- 0x52 / 2 / 0 / Store a Word in memory.
  | mstore8 -- 0x53 / 2 / 0 / store a Byte in memory.
  | sload -- 0x54 / 1 / 1 / load a word from storage.
  | sstore -- 0x55 / 2 / 0 / store a word in storage.
  | tload -- 0x5C / 1 / 1 / load a word from transient storage.
  | tstore -- 0x5D / 2 / 0 / store a word in transient storage.
  | mcopy -- 0x5E / 3 / 0 /
  | pc -- 0x58 / 0 / 1 / Get the current program counter value.
  | msize -- 0x59 / 0 / 1 / Get the size of the memory.
  | gas -- 0x5a / 0 / 1 / Get the amount of remaining gas.
  | dup : Fin 16 → PlainOp
  | swap : Fin 16 → PlainOp
  | log : Fin 5 → PlainOp
deriving DecidableEq

inductive JumpOp : Type
  | jump -- 0x56 / 1 / 0 / Unconditional jump.
  | jumpi -- 0x57 / 2 / 0 / Conditional jump.
  | jumpdest -- 0x5b / 0 / 0 / Mark a valid jump destination.
deriving DecidableEq

inductive MessageOp : Type
  | create -- 0xf0 / 3 / 1 / Create a new contract account.
  | call -- 0xf1 / 7 / 1 / Call an existing account, which can be either a contract or a non-contract account.
  | callcode -- 0xf2 / 7 / 1 / Call an existing contract's code using the current contract's Storage and Addr.
  | delegatecall -- 0xf4 / 6 / 1 / Call an existing contract's code using the current contract's Storage and the calling contract's Addr and value.
  | create2 -- 0xf5 / 4 / 1 / Create a new contract account at a deterministic Addr using a salt value.
  | staticcall -- 0xfa / 6 / 1 / Perform a read-only call to an existing contract.
deriving DecidableEq

inductive HaltOp : Type
  | stop -- 0x00 / 0 / 0 / halts execution.
  | return_ -- 0xf3 / 2 / 0 / Halt execution and return output data.
  | revert -- 0xfd / 2 / 0 / Halt execution and revert State changes, returning output data.
  | selfdestruct -- 0xff / 1 / 0 / Halt execution and destroy the current contract, transferring remaining Ether to a specified Addr.
deriving DecidableEq

def PlainOp.toString : PlainOp → String
  | add => "ADD"
  | mul => "MUL"
  | sub => "SUB"
  | div => "DIV"
  | sdiv => "SDIV"
  | mod => "MOD"
  | smod => "SMOD"
  | addmod => "ADDMOD"
  | mulmod => "MULMOD"
  | exp => "EXP"
  | signextend => "SIGNEXTEND"
  | lt => "LT"
  | gt => "GT"
  | slt => "SLT"
  | sgt => "SGT"
  | eq => "EQ"
  | iszero => "ISZERO"
  | and => "AND"
  | or => "OR"
  | xor => "XOR"
  | not => "NOT"
  | byte => "BYTE"
  | shr => "SHR"
  | shl => "SHL"
  | sar => "SAR"
  | clz => "CLZ"
  | keccak256 => "KECCAK256"
  | address => "ADDRESS"
  | balance => "BALANCE"
  | origin => "ORIGIN"
  | caller => "CALLER"
  | callvalue => "CALLVALUE"
  | calldataload => "CALLDATALOAD"
  | calldatasize => "CALLDATASIZE"
  | calldatacopy => "CALLDATACOPY"
  | codesize => "CODESIZE"
  | codecopy => "CODECOPY"
  | gasprice => "GASPRICE"
  | extcodesize => "EXTCODESIZE"
  | extcodecopy => "EXTCODECOPY"
  | returndatasize => "RETURNDATASIZE"
  | returndatacopy => "RETURNDATACOPY"
  | extcodehash => "EXTCODEHASH"
  | blockhash => "BLOCKHASH"
  | coinbase => "COINBASE"
  | timestamp => "TIMESTAMP"
  | number => "NUMBER"
  | prevrandao => "PREVRANDAO"
  | gaslimit => "GASLIMIT"
  | chainid => "CHAINID"
  | selfbalance => "SELFBALANCE"
  | basefee => "BASEFEE"
  | blobhash => "BLOBHASH"
  | blobbasefee => "BLOBBASEFEE"
  | slotnum => "SLOTNUM"
  | pop => "POP"
  | mload => "MLOAD"
  | mstore => "MSTORE"
  | mstore8 => "MSTORE8"
  | sload => "SLOAD"
  | sstore => "SSTORE"
  | tload => "TLOAD"
  | tstore => "TSTORE"
  | mcopy => "MCOPY"
  | pc => "PC"
  | msize => "MSIZE"
  | gas => "GAS"
  | dup n => "DUP" ++ (n.val + 1).repr
  | swap n => "SWAP" ++ (n.val + 1).repr
  | log n => "LOG" ++ n.val.repr

def MessageOp.toString : MessageOp → String
  | create => "CREATE"
  | call => "CALL"
  | callcode => "CALLCODE"
  | delegatecall => "DELEGATECALL"
  | create2 => "CREATE2"
  | staticcall => "STATICCALL"

def HaltOp.toString : HaltOp → String
  | .stop => "STOP"
  | .selfdestruct => "SELFDESTRUCT"
  | .revert => "REVERT"
  | .return_ => "RETURN"

def UInt8.toPlainOp : UInt8 → Option PlainOp
  | 0x01 => some .add -- 0x01 / 2 / 1 / addition operation.
  | 0x02 => some .mul -- 0x02 / 2 / 1 / multiplication operation.
  | 0x03 => some .sub -- 0x03 / 2 / 1 / subtraction operation.
  | 0x04 => some .div -- 0x04 / 2 / 1 / integer division operation.
  | 0x05 => some .sdiv -- 0x05 / 2 / 1 / signed integer division operation.
  | 0x06 => some .mod -- 0x06 / 2 / 1 / modulo operation.
  | 0x07 => some .smod -- 0x07 / 2 / 1 / signed modulo operation.
  | 0x08 => some .addmod -- 0x08 / 3 / 1 / modulo addition operation.
  | 0x09 => some .mulmod -- 0x09 / 3 / 1 / modulo multiplication operation.
  | 0x0a => some .exp -- 0x0a / 2 / 1 / exponentiation operation.
  | 0x0b => some .signextend -- 0x0b / 2 / 1 / sign extend operation.
  | 0x10 => some .lt -- 0x10 / 2 / 1 / less-than comparison.
  | 0x11 => some .gt -- 0x11 / 2 / 1 / greater-than comparison.
  | 0x12 => some .slt -- 0x12 / 2 / 1 / signed less-than comparison.
  | 0x13 => some .sgt -- 0x13 / 2 / 1 / signed greater-than comparison.
  | 0x14 => some .eq -- 0x14 / 2 / 1 / equality comparison.
  | 0x15 => some .iszero -- 0x15 / 1 / 1 / tests if the input is zero.
  | 0x16 => some .and -- 0x16 / 2 / 1 / bitwise and operation.
  | 0x17 => some .or -- 0x17 / 2 / 1 / bitwise or operation.
  | 0x18 => some .xor -- 0x18 / 2 / 1 / bitwise xor operation.
  | 0x19 => some .not -- 0x19 / 1 / 1 / bitwise not operation.
  | 0x1a => some .byte -- 0x1a / 2 / 1 / retrieve a single byte from a word.
  | 0x1b => some .shl -- 0x1b / 2 / 1 / logical shift left operation.
  | 0x1c => some .shr -- 0x1c / 2 / 1 / logical shift right operation.
  | 0x1d => some .sar -- 0x1d / 2 / 1 / arithmetic (signed) shift right operation.
  -- 0x1e decodes at every fork; whether it is a defined instruction is a rule,
  -- checked by `PlainOp.runCore` against `ForkRules.op`.  Decoding stays
  -- fork-independent so that instruction positions -- and every downstream
  -- statement about them -- do not depend on which rules are running.
  | 0x1e => some .clz -- 0x1e / 1 / 1 / count leading zero bits.
  | 0x20 => some .keccak256 -- 0x20 / 2 / 1 / compute Keccak-256 hash.
  | 0x30 => some .address -- 0x30 / 0 / 1 / Get the address of the currently executing account.
  | 0x31 => some .balance -- 0x31 / 1 / 1 / Get the balance of the specified account.
  | 0x32 => some .origin -- 0x32 / 0 / 1 / Get the address that initiated the current transaction.
  | 0x33 => some .caller -- 0x33 / 0 / 1 / Get the address that directly called the currently executing contract.
  | 0x34 => some .callvalue -- 0x34 / 0 / 1 / Get the value (in wei) sent with the current transaction.
  | 0x35 => some .calldataload -- 0x35 / 1 / 1 / Load input data from the current transaction.
  | 0x36 => some .calldatasize -- 0x36 / 0 / 1 / Get the size of the input data from the current transaction.
  | 0x37 => some .calldatacopy -- 0x37 / 3 / 0 / Copy input data from the current transaction to memory.
  | 0x38 => some .codesize -- 0x38 / 0 / 1 / Get the size of the code of the currently executing contract.
  | 0x39 => some .codecopy -- 0x39 / 3 / 0 / Copy the code of the currently executing contract to memory.
  | 0x3a => some .gasprice -- 0x3a / 0 / 1 / Get the gas price of the current transaction.
  | 0x3b => some .extcodesize -- 0x3b / 1 / 1 / Get the size of the code of an external account.
  | 0x3c => some .extcodecopy -- 0x3c / 4 / 0 / Copy the code of an external account to memory.
  | 0x3d => some .returndatasize -- 0x3d / 0 / 1 / Get the size of the output data from the previous call.
  | 0x3e => some .returndatacopy -- 0x3e / 3 / 0 / Copy output data from the previous call to memory.
  | 0x3f => some .extcodehash -- 0x3f / 1 / 1 / Get the code hash of an external account.
  | 0x40 => some .blockhash -- 0x40 / 1 / 1 / get the hash of the specified block.
  | 0x41 => some .coinbase -- 0x41 / 0 / 1 / get the address of the current block's miner.
  | 0x42 => some .timestamp -- 0x42 / 0 / 1 / get the timestamp of the current block.
  | 0x43 => some .number -- 0x43 / 0 / 1 / get the current block number.
  | 0x44 => some .prevrandao -- 0x44 / 0 / 1 / get the difficulty of the current block.
  | 0x45 => some .gaslimit -- 0x45 / 0 / 1 / get the gas limit of the current block.
  | 0x46 => some .chainid -- 0x46 / 0 / 1 / get the chain id of the current blockchain.
  | 0x47 => some .selfbalance
  | 0x48 => some .basefee -- 0x48 / 0 / 1 /
  | 0x49 => some .blobhash -- 0x49 / 1 / 1 /
  | 0x4A => some .blobbasefee -- 0x4A / 0 / 1 /
  -- 0x4B decodes at every fork, like 0x1E; whether it is a defined instruction
  -- is `ForkRules.op.slotnum`, checked by `PlainOp.runCore` (EIP-7843).
  | 0x4B => some .slotnum -- 0x4B / 0 / 1 / get the current block's slot number.
  | 0x50 => some .pop -- 0x50 / 1 / 0 / Remove an item from the stack.
  | 0x51 => some .mload -- 0x51 / 1 / 1 / Load a word from memory.
  | 0x52 => some .mstore -- 0x52 / 2 / 0 / Store a word in memory.
  | 0x53 => some .mstore8 -- 0x53 / 2 / 0 / Store a byte in memory.
  | 0x54 => some .sload -- 0x54 / 1 / 1 / Load a word from storage.
  | 0x55 => some .sstore -- 0x55 / 2 / 0 / Store a word in storage.
  | 0x58 => some .pc -- 0x58 / 0 / 1 / Get the current program counter value.
  | 0x59 => some .msize -- 0x59 / 0 / 1 / Get the size of the memory.
  | 0x5a => some .gas -- 0x5a / 0 / 1 / Get the amount of remaining gas.
  | 0x5C => some .tload
  | 0x5D => some .tstore
  | 0x5E => some .mcopy
  | 0x80 => some (.dup 0)
  | 0x81 => some (.dup 1)
  | 0x82 => some (.dup 2)
  | 0x83 => some (.dup 3)
  | 0x84 => some (.dup 4)
  | 0x85 => some (.dup 5)
  | 0x86 => some (.dup 6)
  | 0x87 => some (.dup 7)
  | 0x88 => some (.dup 8)
  | 0x89 => some (.dup 9)
  | 0x8A => some (.dup 10)
  | 0x8B => some (.dup 11)
  | 0x8C => some (.dup 12)
  | 0x8D => some (.dup 13)
  | 0x8E => some (.dup 14)
  | 0x8F => some (.dup 15)
  | 0x90 => some (.swap 0)
  | 0x91 => some (.swap 1)
  | 0x92 => some (.swap 2)
  | 0x93 => some (.swap 3)
  | 0x94 => some (.swap 4)
  | 0x95 => some (.swap 5)
  | 0x96 => some (.swap 6)
  | 0x97 => some (.swap 7)
  | 0x98 => some (.swap 8)
  | 0x99 => some (.swap 9)
  | 0x9A => some (.swap 10)
  | 0x9B => some (.swap 11)
  | 0x9C => some (.swap 12)
  | 0x9D => some (.swap 13)
  | 0x9E => some (.swap 14)
  | 0x9F => some (.swap 15)
  | 0xA0 => some (.log 0)
  | 0xA1 => some (.log 1)
  | 0xA2 => some (.log 2)
  | 0xA3 => some (.log 3)
  | 0xA4 => some (.log 4)
  | _ => none

def UInt8.toMessageOp : UInt8 → Option MessageOp
  | 0xF0 => some .create
  | 0xF1 => some .call
  | 0xF2 => some .callcode
  | 0xF4 => some .delegatecall
  | 0xF5 => some .create2
  | 0xFA => some .staticcall
  | _    => none

def UInt8.toJumpOp : UInt8 → Option JumpOp
  | 0x56 => some .jump
  | 0x57 => some .jumpi
  | 0x5B => some .jumpdest
  | _    => none

def UInt8.toHaltOp : UInt8 → Option HaltOp
  | 0x00 => some .stop
  | 0xF3 => some .return_
  | 0xFD => some .revert
  | 0xFF => some .selfdestruct
  | _ => none

def HaltOp.toUInt8 : HaltOp → UInt8
  | .stop => 0x00
  | .return_ => 0xF3
  | .revert => 0xFD
  | .selfdestruct => 0xFF

def JumpOp.toUInt8 : JumpOp → UInt8
  | jump => 0x56     -- 0x56 / 1 / 0 / Unconditional jump.
  | jumpi => 0x57    -- 0x57 / 2 / 0 / Conditional jump.
  | jumpdest => 0x5B -- 0x5b / 0 / 0 / Mark a valid jump destination.

lemma toJumpOp_toUInt8 {o : JumpOp} :
  UInt8.toJumpOp o.toUInt8 = some o := by cases o <;> rfl
lemma toHaltOp_toUInt8 {o : HaltOp} :
  UInt8.toHaltOp o.toUInt8 = some o := by cases o <;> rfl

instance : Repr PlainOp := ⟨λ o _ => o.toString⟩
instance : Repr MessageOp := ⟨λ o _ => o.toString⟩

def JumpOp.toString : JumpOp → String
  | .jump => "JUMP"
  | .jumpdest => "JUMPDEST"
  | .jumpi => "JUMPI"

end Jaune
