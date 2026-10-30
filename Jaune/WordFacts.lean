import Jaune.MulDiv

/-!
# Word facts: comparison flags and `Nat.toB256` arithmetic

The EVM comparison words `B256.eqCheck`, `B256.ltCheck` and `B256.gtCheck`
(`Jaune.Basic`) are `if _ then 1 else 0`. This module characterises them, as
`iff`s against the order and as sufficient conditions over the operands'
natural-number values, so that a downstream walk discharging a branch flag
cites one lemma instead of unfolding the `if`.

It also states `Nat.toB256` as a homomorphism for word addition,
multiplication and (bounded) subtraction, the forms downstream proofs about
pointer and counter arithmetic otherwise re-derive from `B256.toNat_add` and
`B256.toNat_toB256_of_lt`.

None of these is `@[simp]`.
-/

namespace Jaune

open Jaune _root_.Nat

/-- The word `1` is not the word `0`: every comparison flag's two values differ. -/
theorem B256.one_ne_zero : (1 : B256) ≠ 0 := by decide +kernel

/-! ### Comparison flags -/

theorem B256.eqCheck_ne_zero_iff {x y : B256} : B256.eqCheck x y ≠ 0 ↔ x = y := by
  unfold B256.eqCheck
  by_cases h : x = y <;> simp [h, B256.one_ne_zero]

theorem B256.eqCheck_eq_zero_iff {x y : B256} : B256.eqCheck x y = 0 ↔ x ≠ y := by
  unfold B256.eqCheck
  by_cases h : x = y <;> simp [h, B256.one_ne_zero]

theorem B256.ltCheck_ne_zero_iff {x y : B256} : B256.ltCheck x y ≠ 0 ↔ x < y := by
  unfold B256.ltCheck
  by_cases h : x < y <;> simp [h, B256.one_ne_zero]

theorem B256.ltCheck_eq_zero_iff {x y : B256} : B256.ltCheck x y = 0 ↔ ¬ x < y := by
  unfold B256.ltCheck
  by_cases h : x < y <;> simp [h, B256.one_ne_zero]

theorem B256.gtCheck_ne_zero_iff {x y : B256} : B256.gtCheck x y ≠ 0 ↔ y < x := by
  unfold B256.gtCheck
  by_cases h : y < x <;> simp [h, B256.one_ne_zero]

theorem B256.gtCheck_eq_zero_iff {x y : B256} : B256.gtCheck x y = 0 ↔ ¬ y < x := by
  unfold B256.gtCheck
  by_cases h : y < x <;> simp [h, B256.one_ne_zero]

/-- A nonzero `EQ` flag gives the equality. -/
theorem B256.eq_of_eqCheck_ne_zero {x y : B256} (h : B256.eqCheck x y ≠ 0) : x = y :=
  B256.eqCheck_ne_zero_iff.mp h

/-- A zero `LT` flag rules out the strict order. -/
theorem B256.not_lt_of_ltCheck_eq_zero {x y : B256} (h : B256.ltCheck x y = 0) : ¬ x < y :=
  B256.ltCheck_eq_zero_iff.mp h

/-- A nonzero `LT` flag gives the strict order. -/
theorem B256.lt_of_ltCheck_ne_zero {x y : B256} (h : B256.ltCheck x y ≠ 0) : x < y :=
  B256.ltCheck_ne_zero_iff.mp h

/-- A nonzero `GT` flag gives the strict order, operands swapped. -/
theorem B256.lt_of_gtCheck_ne_zero {x y : B256} (h : B256.gtCheck x y ≠ 0) : y < x :=
  B256.gtCheck_ne_zero_iff.mp h

/-- `LT` yields `0` when the left operand's value is at least the right's. -/
theorem B256.ltCheck_eq_zero_of_toNat_le {x y : B256} (h : y.toNat ≤ x.toNat) :
    B256.ltCheck x y = 0 :=
  B256.ltCheck_eq_zero_iff.mpr fun hlt => by
    have := B256.toNat_lt_toNat hlt
    omega

/-- `GT` yields `0` when the left operand's value is at most the right's. -/
theorem B256.gtCheck_eq_zero_of_toNat_le {x y : B256} (h : x.toNat ≤ y.toNat) :
    B256.gtCheck x y = 0 :=
  B256.gtCheck_eq_zero_iff.mpr fun hlt => by
    have := B256.toNat_lt_toNat hlt
    omega

/-- `LT` yields a nonzero flag when the left operand's value is below the right's. -/
theorem B256.ltCheck_ne_zero_of_toNat_lt {x y : B256} (h : x.toNat < y.toNat) :
    B256.ltCheck x y ≠ 0 :=
  B256.ltCheck_ne_zero_iff.mpr (B256.lt_of_toNat_lt_toNat h)

/-- `GT` yields a nonzero flag when the left operand's value is above the right's. -/
theorem B256.gtCheck_ne_zero_of_toNat_lt {x y : B256} (h : y.toNat < x.toNat) :
    B256.gtCheck x y ≠ 0 :=
  B256.gtCheck_ne_zero_iff.mpr (B256.lt_of_toNat_lt_toNat h)

/-! ### `Nat.toB256` arithmetic -/

/-- `Nat.toB256` turns natural addition into word addition (modulo `2 ^ 256`). -/
theorem Nat.toB256_add_toB256 (a b : Nat) :
    Nat.toB256 a + Nat.toB256 b = Nat.toB256 (a + b) := by
  apply B256.toNat_inj
  rw [B256.toNat_add, B256.toNat_toB256, B256.toNat_toB256, B256.toNat_toB256]
  exact (Nat.add_mod _ _ _).symm

/-- `Nat.toB256` turns natural multiplication into word multiplication
(modulo `2 ^ 256`). -/
theorem Nat.toB256_mul_toB256 (a b : Nat) :
    Nat.toB256 a * Nat.toB256 b = Nat.toB256 (a * b) := by
  apply B256.toNat_inj
  simp only [B256.toNat_mul, B256.toNat_toB256, Nat.lo_eq]
  exact (Nat.mul_mod a b (2 ^ 256)).symm

/-- Word subtraction of in-range naturals without underflow is natural
subtraction. -/
theorem Nat.toB256_sub_toB256 {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 256) :
    Nat.toB256 a - Nat.toB256 b = Nat.toB256 (a - b) := by
  apply B256.toNat_inj
  rw [B256.toNat_sub_eq_of_le _ _ (by
      rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt (by omega),
        B256.toNat_toB256_of_lt ha]; exact hb),
    B256.toNat_toB256_of_lt ha, B256.toNat_toB256_of_lt (show b < 2 ^ 256 by omega),
    B256.toNat_toB256_of_lt (show a - b < 2 ^ 256 by omega)]

/-- Adding a small literal to a word without overflow adds its value. -/
theorem B256.toNat_add_toB256_of_lt {x : B256} {n : Nat} (h : x.toNat + n < 2 ^ 256) :
    (x + Nat.toB256 n).toNat = x.toNat + n := by
  rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), Nat.lo_eq_of_lt h]

end Jaune
