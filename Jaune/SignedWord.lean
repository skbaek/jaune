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

private theorem UInt64.highBit_eq_testBit (w : UInt64) : w.highBit = w.toNat.testBit 63 := by
  unfold UInt64.highBit
  have h : (w &&& 0x8000000000000000 != 0) = decide ((w &&& 0x8000000000000000).toNat ≠ 0) := by
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, ne_eq, ← UInt64.toNat_inj]; rfl
  have h2 : w.toNat &&& 2 ^ 63 = if w.toNat.testBit 63 then 2 ^ 63 else 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hi : 63 = i
    · subst hi
      split <;> simp only [*, Nat.testBit_two_pow_self, decide_true, Bool.and_true, Nat.zero_testBit]
    · split <;> simp only [Nat.testBit_two_pow, hi, decide_false, Bool.and_false, Nat.zero_testBit]
  rw [h, UInt64.toNat_and, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl, h2]
  cases w.toNat.testBit 63 <;> simp

/-- Below `2 ^ (j + 1)`, bit `j` is set exactly from `2 ^ j` up. -/
private theorem Nat.testBit_eq_decide_le {r j : Nat} (h : r < 2 ^ (j + 1)) :
    r.testBit j = decide (2 ^ j ≤ r) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hp : 0 < 2 ^ j := Nat.two_pow_pos j
  have hq : r / 2 ^ j < 2 := by
    rw [Nat.div_lt_iff_lt_mul hp]; rw [Nat.pow_succ] at h; omega
  by_cases hr : 2 ^ j ≤ r
  · have : 1 ≤ r / 2 ^ j := (Nat.le_div_iff_mul_le hp).mpr (by omega)
    simp only [hr, decide_true, decide_eq_true_eq]; omega
  · have : r / 2 ^ j = 0 := Nat.div_eq_of_lt (by omega)
    simp only [hr, decide_false, this]; decide

theorem U256.toInt_lt (x : U256) : x.toInt < 2 ^ 255 := by
  have := U256.toNat_lt x
  unfold U256.toInt; split <;> omega

theorem U256.le_toInt (x : U256) : -2 ^ 255 ≤ x.toInt := by
  have := U256.toNat_lt x
  unfold U256.toInt; split <;> omega

/-- A word is negative exactly when its value is at least `2 ^ 255`. -/
theorem U256.isNegative_eq_true_iff (x : U256) : x.isNegative = true ↔ 2 ^ 255 ≤ x.toNat := by
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  change UInt64.highBit a = true ↔ _
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hc := UInt64.toNat_lt c
  have hd := UInt64.toNat_lt d
  have hx : U256.toNat ((a, b), (c, d)) =
      a.toNat * 2 ^ 192 + b.toNat * 2 ^ 128 + c.toNat * 2 ^ 64 + d.toNat := by
    change (((a.toNat <<< 64) ||| b.toNat) <<< 128) ||| ((c.toNat <<< 64) ||| d.toNat) = _
    rw [← Nat.shiftLeft_add_eq_or_of_lt hb, ← Nat.shiftLeft_add_eq_or_of_lt hd,
      ← Nat.shiftLeft_add_eq_or_of_lt (by rw [Nat.shiftLeft_eq]; omega)]
    simp only [Nat.shiftLeft_eq]; omega
  rw [UInt64.highBit_eq_testBit, Nat.testBit_eq_decide_le ha, decide_eq_true_iff, hx]
  omega

theorem U256.isNegative_eq_true_iff_toInt_neg (x : U256) :
    x.isNegative = true ↔ x.toInt < 0 := by
  rw [U256.isNegative_eq_true_iff]
  have := U256.toNat_lt x
  unfold U256.toInt; split <;> omega

/-! ### `SLT` and `SGT` -/

/-- Jaune's signed order on words is the order of their signed readings. -/
theorem U256.signedLt_iff_toInt_lt {x y : U256} : U256.SignedLt x y ↔ x.toInt < y.toInt := by
  unfold U256.SignedLt
  have hm : (U256.max >>> 1).toNat = 2 ^ 255 - 1 :=
    U256.toNat_max_shiftRight (k := 255) (by omega)
  have hx := U256.isNegative_eq_true_iff x
  have hy := U256.isNegative_eq_true_iff y
  have hx' := U256.toNat_lt x
  have hy' := U256.toNat_lt y
  simp only [U256.isNegative] at hx hy
  change _ ∨ (_ ∧ U256.and x (U256.max >>> 1) < U256.and y (U256.max >>> 1)) ↔ _
  rw [U256.lt_iff_toNat_lt_toNat, U256.toNat_and, U256.toNat_and, hm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  have hbx : x.highBit = !decide (x.toNat < 2 ^ 255) := by
    rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]; exact hx
  have hby : y.highBit = !decide (y.toNat < 2 ^ 255) := by
    rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]; exact hy
  rw [hbx, hby]
  by_cases h1 : x.toNat < 2 ^ 255 <;> by_cases h2 : y.toNat < 2 ^ 255 <;>
    simp only [U256.toInt, h1, h2, ite_true, ite_false, decide_true, decide_false, Bool.not_true,
      Bool.not_false] <;>
    simp [show ¬ (true < false) by decide, show (false < true) by decide] <;> omega

theorem U256.signedGt_iff_toInt_lt {x y : U256} : U256.SignedGt x y ↔ y.toInt < x.toInt := by
  exact U256.signedLt_iff_toInt_lt

theorem U256.sltCheck_ne_zero_iff {x y : U256} : U256.sltCheck x y ≠ 0 ↔ x.toInt < y.toInt := by
  rw [← U256.signedLt_iff_toInt_lt]
  unfold U256.sltCheck
  by_cases h : U256.SignedLt x y <;> simp [h, U256.one_ne_zero]

theorem U256.sltCheck_eq_zero_iff {x y : U256} :
    U256.sltCheck x y = 0 ↔ ¬ x.toInt < y.toInt := by
  rw [← U256.signedLt_iff_toInt_lt]
  unfold U256.sltCheck
  by_cases h : U256.SignedLt x y <;> simp [h, U256.one_ne_zero]

theorem U256.sgtCheck_ne_zero_iff {x y : U256} : U256.sgtCheck x y ≠ 0 ↔ y.toInt < x.toInt := by
  rw [← U256.signedGt_iff_toInt_lt]
  unfold U256.sgtCheck
  by_cases h : U256.SignedGt x y <;> simp [h, U256.one_ne_zero]

theorem U256.sgtCheck_eq_zero_iff {x y : U256} :
    U256.sgtCheck x y = 0 ↔ ¬ y.toInt < x.toInt := by
  rw [← U256.signedGt_iff_toInt_lt]
  unfold U256.sgtCheck
  by_cases h : U256.SignedGt x y <;> simp [h, U256.one_ne_zero]

/-! ### `SAR` -/

/-- `SAR` by `s` shifts the value right and fills the vacated high bits with the sign
bit: for a negative word it adds the top `min s 256` bits. -/
theorem U256.toNat_arithmeticShiftRight (x : U256) (s : Nat) :
    (x.arithmeticShiftRight s).toNat =
      if x.isNegative then x.toNat >>> s + (2 ^ 256 - 2 ^ (256 - s)) else x.toNat >>> s := by
  have hlt : x.toNat >>> s < 2 ^ (256 - s) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le (U256.toNat_lt x) (Nat.pow_le_pow_right (by omega) (by omega))
  unfold U256.arithmeticShiftRight
  split
  · change (U256.or _ _).toNat = _
    rw [U256.toNat_or, U256.toNat_shiftRight, U256.toNat_max_shiftLeft (by omega), Nat.or_comm,
      Nat.two_pow_sub_two_pow_or (by omega)
        (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.mod_eq_of_lt hlt, Nat.add_comm]
  · rw [U256.toNat_shiftRight]

/-- `SAR` by `s` is floor division of the signed reading by `2 ^ s`. -/
theorem U256.toInt_arithmeticShiftRight (x : U256) (s : Nat) :
    (x.arithmeticShiftRight s).toInt = x.toInt >>> s := by
  rw [Int.shiftRight_eq_div_pow]
  have hR := U256.toNat_arithmeticShiftRight x s
  have hx' := U256.toNat_lt x
  have hP : 0 < 2 ^ s := Nat.two_pow_pos s
  by_cases hn : x.isNegative = true
  · rw [ite_eq_left hn] at hR
    have hx := (U256.isNegative_eq_true_iff x).mp hn
    unfold U256.toInt
    rw [hR, ite_eq_right (show ¬ x.toNat < 2 ^ 255 by omega), Nat.shiftRight_eq_div_pow]
    by_cases hs0 : s = 0
    · subst hs0
      simp only [Nat.pow_zero, Nat.div_one, Nat.sub_zero, Nat.sub_self, Nat.add_zero,
        ite_eq_right (show ¬ x.toNat < 2 ^ 255 by omega), Nat.cast_one, Int.ediv_one]
    by_cases hs : s ≤ 256
    · have hQ : 2 ^ (256 - s) ≤ 2 ^ 255 := Nat.pow_le_pow_right (by omega) (by omega)
      have hPQ : (2 : Nat) ^ 256 = 2 ^ (256 - s) * 2 ^ s := by
        rw [← Nat.pow_add, Nat.sub_add_cancel hs]
      have hq := Nat.div_le_self x.toNat (2 ^ s)
      have hq0 : (0 : Int) ≤ ((x.toNat / 2 ^ s : Nat) : Int) := Int.natCast_nonneg _
      rw [ite_eq_right (show ¬ x.toNat / 2 ^ s + (2 ^ 256 - 2 ^ (256 - s)) < 2 ^ 255 by omega)]
      have hc : ((x.toNat : Int) - 2 ^ 256) =
          (x.toNat : Int) + (-((2 ^ (256 - s) : Nat) : Int)) * ((2 ^ s : Nat) : Int) := by
        rw [show ((2 : Int) ^ 256) = (((2 : Nat) ^ 256 : Nat) : Int) by norm_cast, hPQ,
          Nat.cast_mul, Int.neg_mul, Int.sub_eq_add_neg]
      rw [hc, Int.add_mul_ediv_right _ _ (by exact_mod_cast hP.ne'), ← Int.natCast_ediv,
        Nat.cast_add, Nat.cast_sub (show 2 ^ (256 - s) ≤ 2 ^ 256 by omega)]
      push_cast
      omega
    · have hz : x.toNat / 2 ^ s = 0 :=
        Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx' (Nat.pow_le_pow_right (by omega) (by omega)))
      have hP' : 2 ^ 256 < 2 ^ s := Nat.pow_lt_pow_right (by omega) (by omega)
      rw [hz, show 256 - s = 0 by omega]
      simp only [Nat.pow_zero, Nat.zero_add]
      rw [ite_eq_right (by omega), show (((2 ^ 256 - 1 : Nat) : Int) - 2 ^ 256) = -1 by norm_num]
      generalize hPdef : (2 ^ s : Nat) = P at *
      symm
      exact ((Int.ediv_emod_unique (q := -1) (r := (x.toNat : Int) - 2 ^ 256 + P)
        (by omega)).mpr ⟨by omega, by omega, by omega⟩).1
  · rw [ite_eq_right hn] at hR
    have hx : x.toNat < 2 ^ 255 := by
      by_contra h; exact hn ((U256.isNegative_eq_true_iff x).mpr (by omega))
    have hle : x.toNat >>> s ≤ x.toNat := Nat.shiftRight_le _ _
    unfold U256.toInt
    rw [hR, ite_eq_left (by omega), ite_eq_left hx, Nat.shiftRight_eq_div_pow, Int.natCast_ediv]

/-! ### `SIGNEXTEND` -/

/-- `SIGNEXTEND b x` is the low `8 (b + 1)` bits of `x` read as a signed integer of
that width; for `b ≥ 31` it is `x` itself. -/
theorem U256.toInt_signextend (b x : U256) :
    (U256.signextend b x).toInt = Int.bmod x.toNat (2 ^ (8 * (Min.min b.toNat 31 + 1))) := by
  have hx := U256.toNat_lt x
  have hR := U256.toNat_signextend b x
  unfold U256.toInt
  rw [hR, Int.bmod_def, ← Int.natCast_emod]
  by_cases hb : b.toNat < 31
  · have hmin : Min.min b.toNat 31 = b.toNat := Nat.min_eq_left (by omega)
    simp only [hb, ite_true, hmin]
    rw [show 8 * (b.toNat + 1) = 8 * b.toNat + 8 by omega]
    have hm : 2 ^ (8 * b.toNat + 8) = 2 * 2 ^ (8 * b.toNat + 7) := by
      rw [show 8 * b.toNat + 8 = (8 * b.toNat + 7) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hm' : 2 ^ (8 * b.toNat + 7) ≤ 2 ^ 247 := Nat.pow_le_pow_right (by omega) (by omega)
    have hr := Nat.mod_lt x.toNat (Nat.two_pow_pos (8 * b.toNat + 8))
    have hbit : x.toNat.testBit (8 * b.toNat + 7) =
        decide (2 ^ (8 * b.toNat + 7) ≤ x.toNat % 2 ^ (8 * b.toNat + 8)) := by
      rw [← Nat.testBit_eq_decide_le hr, Nat.testBit_mod_two_pow]
      simp
    rw [hbit, hm, Nat.cast_mul, Nat.cast_ofNat] at *
    rw [hm] at hr
    generalize x.toNat % (2 * 2 ^ (8 * b.toNat + 7)) = r at *
    generalize 2 ^ (8 * b.toNat + 7) = m at *
    by_cases hrm : m ≤ r
    · simp only [hrm, decide_true, ite_true]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      push_cast [Nat.cast_sub (show 2 * m ≤ 2 ^ 256 by omega)]
      omega
    · simp only [hrm, decide_false, ite_false, Bool.false_eq_true]
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  · have hmin : Min.min b.toNat 31 = 31 := Nat.min_eq_right (by omega)
    simp only [hb, ite_false, hmin]
    rw [Nat.mod_eq_of_lt hx]
    split_ifs <;> push_cast at * <;> omega

/-! ### `SDIV` and `SMOD` -/

private theorem U256.toInt_of_lt {w : U256} (h : w.toNat < 2 ^ 255) : w.toInt = w.toNat := by
  unfold U256.toInt; rw [ite_eq_left h]

private theorem U256.toInt_of_le {w : U256} (h : 2 ^ 255 ≤ w.toNat) :
    w.toInt = (w.toNat : Int) - 2 ^ 256 := by
  unfold U256.toInt; rw [ite_eq_right (by omega)]

private theorem U256.toNat_neg (w : U256) :
    (U256.neg w).toNat = (2 ^ 256 - w.toNat) % 2 ^ 256 := by
  have hw := U256.toNat_lt w
  unfold U256.neg
  rw [U256.toNat_add, U256.toNat_complement, show U256.one.toNat = 1 from rfl, Nat.lowBits_eq,
    show 2 ^ 256 - 1 - w.toNat + 1 = 2 ^ 256 - w.toNat by omega]

/-- The negation of a word of value at most `2 ^ 255` reads as its value negated. -/
private theorem U256.toInt_neg_of_le {w : U256} (h : w.toNat ≤ 2 ^ 255) :
    (U256.neg w).toInt = -(w.toNat : Int) := by
  have hn := U256.toNat_neg w
  by_cases h0 : w.toNat = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self] at hn
    rw [U256.toInt_of_lt (by omega), hn, h0]; rfl
  · rw [Nat.mod_eq_of_lt (by omega)] at hn
    rw [U256.toInt_of_le (by omega), hn, Nat.cast_sub (by omega)]
    push_cast; omega

/-- The value of a negative word's negation is `2 ^ 256` less its value. -/
private theorem U256.toNat_neg_of_isNegative {w : U256} (h : 2 ^ 255 ≤ w.toNat) :
    (U256.neg w).toNat = 2 ^ 256 - w.toNat := by
  rw [U256.toNat_neg, Nat.mod_eq_of_lt (by omega)]

private theorem U256.toInt_eq_neg_of_le {w : U256} (h : 2 ^ 255 ≤ w.toNat) :
    w.toInt = -((U256.neg w).toNat : Int) := by
  have hw := U256.toNat_lt w
  rw [U256.toInt_of_le h, U256.toNat_neg_of_isNegative h, Nat.cast_sub (by omega)]
  push_cast; omega

private theorem U256.ne_zero_of_toNat_ne_zero {w : U256} (h : w.toNat ≠ 0) : w ≠ 0 := by
  rintro rfl; exact h rfl

private theorem U256.isNegative_cases (w : U256) :
    (w.isNegative = true ∧ 2 ^ 255 ≤ w.toNat) ∨ (w.isNegative = false ∧ w.toNat < 2 ^ 255) := by
  have := U256.isNegative_eq_true_iff w
  cases h : w.isNegative
  · right; exact ⟨rfl, by rw [h] at this; simp at this; omega⟩
  · left; exact ⟨rfl, this.mp h⟩

/-- `SDIV` is division truncated toward zero (`0` for a zero divisor), except that
`-2 ^ 255 / -1` wraps to `-2 ^ 255`. -/
theorem U256.toInt_sdiv (x y : U256) :
    (U256.sdiv x y).toInt =
      if x.toInt = -2 ^ 255 ∧ y.toInt = -1 then -2 ^ 255 else x.toInt.tdiv y.toInt := by
  have hx' := U256.toNat_lt x
  have hy' := U256.toNat_lt y
  have hmin : U256.signedMin.toNat = 2 ^ 255 := by decide
  have hneg1 : U256.negOne.toNat = 2 ^ 256 - 1 := by decide
  -- The exceptional pair, read on values.
  have hexc : (x.toInt = -2 ^ 255 ∧ y.toInt = -1) ↔ (x = U256.signedMin ∧ y = U256.negOne) := by
    constructor
    · rintro ⟨h1, h2⟩
      unfold U256.toInt at h1 h2
      split at h1 <;> split at h2 <;> try omega
      exact ⟨U256.toNat_inj _ _ (by omega), U256.toNat_inj _ _ (by omega)⟩
    · rintro ⟨rfl, rfl⟩; constructor <;> decide
  unfold U256.sdiv
  by_cases h0 : y = 0
  · subst h0
    rw [ite_eq_left rfl, ite_eq_right (by rintro ⟨_, h⟩; exact absurd h (by decide)),
      show (0 : U256).toInt = 0 by decide, Int.tdiv_zero]
  rw [ite_eq_right h0]
  have hy0 : y.toNat ≠ 0 := U256.toNat_ne_zero h0
  by_cases he : x = U256.signedMin ∧ y = U256.negOne
  · rw [ite_eq_left he, ite_eq_left (hexc.mpr he)]; decide
  rw [ite_eq_right he, ite_eq_right (fun h => he (hexc.mp h))]
  rcases U256.isNegative_cases x with ⟨hx, hxv⟩ | ⟨hx, hxv⟩ <;>
    rcases U256.isNegative_cases y with ⟨hy, hyv⟩ | ⟨hy, hyv⟩ <;> simp only [hx, hy]
  · -- both negative: the quotient of the magnitudes
    have ha := U256.toNat_neg_of_isNegative hxv
    have hb := U256.toNat_neg_of_isNegative hyv
    have hb0 : (U256.neg y).toNat ≠ 0 := by omega
    rw [U256.toInt_eq_neg_of_le hxv, U256.toInt_eq_neg_of_le hyv, Int.neg_tdiv, Int.tdiv_neg,
      Int.neg_neg, ← Int.ofNat_tdiv]
    have hq : (U256.neg x).toNat / (U256.neg y).toNat < 2 ^ 255 := by
      by_cases hb1 : (U256.neg y).toNat = 1
      · rw [hb1, Nat.div_one]
        have : x ≠ U256.signedMin := by
          intro hxe; apply he; refine ⟨hxe, U256.toNat_inj _ _ (by omega)⟩
        have : x.toNat ≠ 2 ^ 255 := fun h => this (U256.toNat_inj _ _ (by omega))
        omega
      · exact Nat.lt_of_le_of_lt (Nat.div_le_div_left (show 2 ≤ (U256.neg y).toNat by omega)
          (by omega)) (by omega)
    rw [U256.toInt_of_lt (by rw [U256.toNat_div (U256.ne_zero_of_toNat_ne_zero hb0)]; exact hq),
      U256.toNat_div (U256.ne_zero_of_toNat_ne_zero hb0)]
  · -- negative dividend, nonnegative divisor
    have ha := U256.toNat_neg_of_isNegative hxv
    have hq : (U256.neg x).toNat / y.toNat ≤ 2 ^ 255 :=
      Nat.le_trans (Nat.div_le_self _ _) (by omega)
    rw [U256.toInt_neg_of_le (by rw [U256.toNat_div h0]; exact hq), U256.toNat_div h0,
      U256.toInt_eq_neg_of_le hxv, U256.toInt_of_lt hyv, Int.neg_tdiv, ← Int.ofNat_tdiv]
  · -- nonnegative dividend, negative divisor
    have hb := U256.toNat_neg_of_isNegative hyv
    have hb0 : (U256.neg y).toNat ≠ 0 := by omega
    have hq : x.toNat / (U256.neg y).toNat ≤ 2 ^ 255 :=
      Nat.le_trans (Nat.div_le_self _ _) (by omega)
    rw [U256.toInt_neg_of_le (by rw [U256.toNat_div (U256.ne_zero_of_toNat_ne_zero hb0)]; exact hq),
      U256.toNat_div (U256.ne_zero_of_toNat_ne_zero hb0),
      U256.toInt_of_lt hxv, U256.toInt_eq_neg_of_le hyv, Int.tdiv_neg, ← Int.ofNat_tdiv]
  · -- both nonnegative
    rw [U256.toInt_of_lt (by rw [U256.toNat_div h0]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxv),
      U256.toNat_div h0, U256.toInt_of_lt hxv, U256.toInt_of_lt hyv, ← Int.ofNat_tdiv]

/-- `SMOD` is the remainder of truncated division, signed as the dividend, and `0` for
a zero divisor. -/
theorem U256.toInt_smod (x y : U256) :
    (U256.smod x y).toInt = if y.toInt = 0 then 0 else x.toInt.tmod y.toInt := by
  have hx' := U256.toNat_lt x
  have hy' := U256.toNat_lt y
  unfold U256.smod
  by_cases h0 : y = 0
  · subst h0
    rw [ite_eq_left rfl, ite_eq_left (by decide)]; decide
  have hy0 : y.toNat ≠ 0 := U256.toNat_ne_zero h0
  rw [ite_eq_right h0]
  -- The divisor's magnitude, its sign absorbed by `Int.tmod_neg`.
  have hb : (U256.abs y).toNat ≠ 0 ∧ (U256.abs y).toNat ≤ 2 ^ 255 ∧
      ∀ a : Int, a.tmod y.toInt = a.tmod ((U256.abs y).toNat : Int) := by
    rcases U256.isNegative_cases y with ⟨hy, hyv⟩ | ⟨hy, hyv⟩
    · have := U256.toNat_neg_of_isNegative hyv
      simp only [U256.abs, hy, ite_true]
      refine ⟨by omega, by omega, fun a => ?_⟩
      rw [U256.toInt_eq_neg_of_le hyv, Int.tmod_neg]
    · simp only [U256.abs, hy, Bool.false_eq_true, ite_false]
      refine ⟨hy0, by omega, fun a => ?_⟩
      rw [U256.toInt_of_lt hyv]
  obtain ⟨hb0, hble, hmod⟩ := hb
  have hab : U256.abs y ≠ 0 := U256.ne_zero_of_toNat_ne_zero hb0
  have hy0' : y.toInt ≠ 0 := by
    unfold U256.toInt; split <;> omega
  rw [ite_eq_right hy0', hmod]
  have hlt := Nat.mod_lt (U256.abs x).toNat (Nat.pos_of_ne_zero hb0)
  rcases U256.isNegative_cases x with ⟨hx, hxv⟩ | ⟨hx, hxv⟩
  · have ha := U256.toNat_neg_of_isNegative hxv
    have habx : U256.abs x = U256.neg x := by simp only [U256.abs, hx, ite_true]
    rw [habx] at hlt ⊢
    simp only [hx, ite_true]
    rw [U256.toInt_neg_of_le (by rw [U256.toNat_mod hab]; omega), U256.toNat_mod hab,
      U256.toInt_eq_neg_of_le hxv, Int.neg_tmod, ← Int.ofNat_tmod]
  · have habx : U256.abs x = x := by simp only [U256.abs, hx, Bool.false_eq_true, ite_false]
    rw [habx] at hlt ⊢
    simp only [hx, Bool.false_eq_true, ite_false]
    have hle := Nat.mod_le x.toNat (U256.abs y).toNat
    rw [U256.toInt_of_lt (by rw [U256.toNat_mod hab]; omega), U256.toNat_mod hab,
      U256.toInt_of_lt hxv, ← Int.ofNat_tmod]

end Jaune
