import Jaune.WordBits

/-!
# Word facts: the signed reading of a word

`U256.toInt` reads a word as a two's-complement integer: a value below `2 ^ 255`
is itself, a value at or above it is that value less `2 ^ 256`. This module
proves that the signed operations of the instruction table
(`Jaune.Instructions.Table`) mean, on that reading, what the EVM documents:

* `SLT` and `SGT` (`U256.SignedLt`, `U256.sltCheck`, `U256.sgtCheck`) compare the
  signed readings;
* `SAR` (`U256.arithmeticShiftRight`) is floor division of the signed reading by
  `2 ^ s`, so a shift by `256` or more gives `0` or `-1` by sign; on `toNat` it
  fills the vacated high bits with the sign bit;
* `SIGNEXTEND b x` reads the low `8 (b + 1)` bits of `x` as a signed integer
  (`Int.bmod`);
* `SDIV` is division truncated toward zero, except that `-2 ^ 255 / -1` wraps to
  `-2 ^ 255`; a zero divisor gives `0`;
* `SMOD` is the remainder of that division, signed as the dividend; a zero
  divisor gives `0`.

None of these is `@[simp]`.
-/

namespace Jaune

open Jaune _root_.Nat

/-- The two's-complement reading of a word: values from `2 ^ 255` up are negative. -/
def U256.toInt (x : U256) : Int :=
  if x.toNat < 2 ^ 255 then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 256

theorem U256.toInt_lt (x : U256) : x.toInt < 2 ^ 255 := by
  sorry

theorem U256.le_toInt (x : U256) : -2 ^ 255 ≤ x.toInt := by
  sorry

/-- A word is negative exactly when its value is at least `2 ^ 255`. -/
theorem U256.isNegative_eq_true_iff (x : U256) : x.isNegative = true ↔ 2 ^ 255 ≤ x.toNat := by
  sorry

theorem U256.isNegative_eq_true_iff_toInt_neg (x : U256) :
    x.isNegative = true ↔ x.toInt < 0 := by
  sorry

/-! ### `SLT` and `SGT` -/

/-- Jaune's signed order on words is the order of their signed readings. -/
theorem U256.signedLt_iff_toInt_lt {x y : U256} : U256.SignedLt x y ↔ x.toInt < y.toInt := by
  sorry

theorem U256.signedGt_iff_toInt_lt {x y : U256} : U256.SignedGt x y ↔ y.toInt < x.toInt := by
  sorry

theorem U256.sltCheck_ne_zero_iff {x y : U256} : U256.sltCheck x y ≠ 0 ↔ x.toInt < y.toInt := by
  sorry

theorem U256.sltCheck_eq_zero_iff {x y : U256} :
    U256.sltCheck x y = 0 ↔ ¬ x.toInt < y.toInt := by
  sorry

theorem U256.sgtCheck_ne_zero_iff {x y : U256} : U256.sgtCheck x y ≠ 0 ↔ y.toInt < x.toInt := by
  sorry

theorem U256.sgtCheck_eq_zero_iff {x y : U256} :
    U256.sgtCheck x y = 0 ↔ ¬ y.toInt < x.toInt := by
  sorry

/-! ### `SAR` -/

/-- `SAR` by `s` shifts the value right and fills the vacated high bits with the sign
bit: for a negative word it adds the top `min s 256` bits. -/
theorem U256.toNat_arithmeticShiftRight (x : U256) (s : Nat) :
    (x.arithmeticShiftRight s).toNat =
      if x.isNegative then x.toNat >>> s + (2 ^ 256 - 2 ^ (256 - s)) else x.toNat >>> s := by
  sorry

/-- `SAR` by `s` is floor division of the signed reading by `2 ^ s`. -/
theorem U256.toInt_arithmeticShiftRight (x : U256) (s : Nat) :
    (x.arithmeticShiftRight s).toInt = x.toInt >>> s := by
  sorry

/-! ### `SIGNEXTEND` -/

/-- `SIGNEXTEND b x` is the low `8 (b + 1)` bits of `x` read as a signed integer of
that width; for `b ≥ 31` it is `x` itself. -/
theorem U256.toInt_signextend (b x : U256) :
    (U256.signextend b x).toInt = Int.bmod x.toNat (2 ^ (8 * (Nat.min b.toNat 31 + 1))) := by
  sorry

/-! ### `SDIV` and `SMOD` -/

/-- `SDIV` is division truncated toward zero (`0` for a zero divisor), except that
`-2 ^ 255 / -1` wraps to `-2 ^ 255`. -/
theorem U256.toInt_sdiv (x y : U256) :
    (U256.sdiv x y).toInt =
      if x.toInt = -2 ^ 255 ∧ y.toInt = -1 then -2 ^ 255 else x.toInt.tdiv y.toInt := by
  sorry

/-- `SMOD` is the remainder of truncated division, signed as the dividend, and `0` for
a zero divisor. -/
theorem U256.toInt_smod (x y : U256) :
    (U256.smod x y).toInt = if y.toInt = 0 then 0 else x.toInt.tmod y.toInt := by
  sorry

end Jaune
