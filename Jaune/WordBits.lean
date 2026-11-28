import Jaune.WordFacts

/-!
# Word facts: bit operations read as numbers

Jaune states the natural-number value of word `+`, `-`, `*`, `/` and `%`
(`U256.toNat_add`, `U256.toNat_sub`, `U256.toNat_mul`, `U256.toNat_div`,
`U256.toNat_mod`). This module states it for the unsigned bit operations the
instruction table applies to words (`Jaune.Instructions.Table`): `AND`, `OR`,
`XOR`, `NOT`, `SHL`, `SHR`, `BYTE` and `SIGNEXTEND`, each on `toNat`.

* `U256.and`, `U256.or`, `U256.xor` are the bitwise operations on the values,
  and `~~~` is `2 ^ 256 - 1 - x`.
* `x <<< s` is `x * 2 ^ s` modulo `2 ^ 256` and `x >>> s` is `x / 2 ^ s`; a
  shift by `256` or more gives `0`.
* `BYTE i x` is byte `i` of `x` counted from the most significant end, `0` for
  `i ≥ 32`.
* `SIGNEXTEND b x` for `b < 31` keeps the low `8 (b + 1)` bits and fills the
  rest with bit `8 b + 7`; for `b ≥ 31` it is `x`.

The signed operations, read through `U256.toInt`, are in `Jaune.SignedWord`.
None of these is `@[simp]`.
-/

namespace Jaune

open Jaune _root_.Nat

/-! ### Bitwise operations -/

/-- The bits of a joined pair of limbs. -/
private theorem testBit_join {a b k i : Nat} (hb : b < 2 ^ k) :
    ((a <<< k) ||| b).testBit i = if i < k then b.testBit i else a.testBit (i - k) := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < k
  · rw [ite_eq_left hi]
    have : ¬ (k ≤ i) := by omega
    simp only [ge_iff_le, this, decide_false, Bool.false_and, Bool.false_or]
  · rw [ite_eq_right hi]
    have hk : k ≤ i := by omega
    have hbf : b.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hk))
    simp only [ge_iff_le, hk, decide_true, Bool.true_and, hbf, Bool.or_false]

private theorem toNat_toUInt64_of_lt {n : Nat} (h : n < 64) : n.toUInt64.toNat = n :=
  Nat.mod_eq_of_lt (by omega)

private theorem U128.toNat_pair (a b : UInt64) :
    U128.toNat ((a, b) : UInt64 × UInt64) = a.toNat * 2 ^ 64 + b.toNat := by
  change (a.toNat <<< 64) ||| b.toNat = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt _), Nat.shiftLeft_eq]

private theorem U256.toNat_pair (a b : U128) :
    U256.toNat ((a, b) : U128 × U128) = a.toNat * 2 ^ 128 + b.toNat := by
  change (a.toNat <<< 128) ||| b.toNat = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt U128.toNat_lt, Nat.shiftLeft_eq]

theorem U128.toNat_and (x y : U128) : (x &&& y).toNat = x.toNat &&& y.toNat := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  change (((a &&& c).toNat <<< 64) ||| (b &&& d).toNat) =
    ((a.toNat <<< 64) ||| b.toNat) &&& ((c.toNat <<< 64) ||| d.toNat)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_join (UInt64.toNat_lt _), Nat.testBit_and, testBit_join (UInt64.toNat_lt _), testBit_join (UInt64.toNat_lt _), UInt64.toNat_and, UInt64.toNat_and]
  split <;> simp only [Nat.testBit_and]

theorem U128.toNat_or (x y : U128) : (x ||| y).toNat = x.toNat ||| y.toNat := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  change (((a ||| c).toNat <<< 64) ||| (b ||| d).toNat) =
    ((a.toNat <<< 64) ||| b.toNat) ||| ((c.toNat <<< 64) ||| d.toNat)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_join (UInt64.toNat_lt _), Nat.testBit_or, testBit_join (UInt64.toNat_lt _), testBit_join (UInt64.toNat_lt _), UInt64.toNat_or, UInt64.toNat_or]
  split <;> simp only [Nat.testBit_or]

theorem U128.toNat_xor (x y : U128) : (x ^^^ y).toNat = x.toNat ^^^ y.toNat := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  change (((a ^^^ c).toNat <<< 64) ||| (b ^^^ d).toNat) =
    ((a.toNat <<< 64) ||| b.toNat) ^^^ ((c.toNat <<< 64) ||| d.toNat)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_join (UInt64.toNat_lt _), Nat.testBit_xor, testBit_join (UInt64.toNat_lt _), testBit_join (UInt64.toNat_lt _), UInt64.toNat_xor, UInt64.toNat_xor]
  split <;> simp only [Nat.testBit_xor]

theorem U128.toNat_complement (x : U128) : (~~~ x).toNat = 2 ^ 128 - 1 - x.toNat := by
  rcases x with ⟨a, b⟩
  change U128.toNat ((~~~ a, ~~~ b) : UInt64 × UInt64) = _
  rw [U128.toNat_pair, U128.toNat_pair, UInt64.toNat_not, UInt64.toNat_not]
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  simp only [UInt64.size] at *
  omega

/-- `AND` is the bitwise conjunction of the operands' values. -/
theorem U256.toNat_and (x y : U256) : (U256.and x y).toNat = x.toNat &&& y.toNat := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  change (((a &&& c).toNat <<< 128) ||| (b &&& d).toNat) =
    ((a.toNat <<< 128) ||| b.toNat) &&& ((c.toNat <<< 128) ||| d.toNat)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_join (U128.toNat_lt), Nat.testBit_and, testBit_join (U128.toNat_lt), testBit_join (U128.toNat_lt), U128.toNat_and, U128.toNat_and]
  split <;> simp only [Nat.testBit_and]

/-- `OR` is the bitwise disjunction of the operands' values. -/
theorem U256.toNat_or (x y : U256) : (U256.or x y).toNat = x.toNat ||| y.toNat := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  change (((a ||| c).toNat <<< 128) ||| (b ||| d).toNat) =
    ((a.toNat <<< 128) ||| b.toNat) ||| ((c.toNat <<< 128) ||| d.toNat)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_join (U128.toNat_lt), Nat.testBit_or, testBit_join (U128.toNat_lt), testBit_join (U128.toNat_lt), U128.toNat_or, U128.toNat_or]
  split <;> simp only [Nat.testBit_or]

/-- `XOR` is the bitwise exclusive or of the operands' values. -/
theorem U256.toNat_xor (x y : U256) : (U256.xor x y).toNat = x.toNat ^^^ y.toNat := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  change (((a ^^^ c).toNat <<< 128) ||| (b ^^^ d).toNat) =
    ((a.toNat <<< 128) ||| b.toNat) ^^^ ((c.toNat <<< 128) ||| d.toNat)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_join (U128.toNat_lt), Nat.testBit_xor, testBit_join (U128.toNat_lt), testBit_join (U128.toNat_lt), U128.toNat_xor, U128.toNat_xor]
  split <;> simp only [Nat.testBit_xor]

/-- `NOT` subtracts the value from the all-ones word. -/
theorem U256.toNat_complement (x : U256) : (~~~ x).toNat = 2 ^ 256 - 1 - x.toNat := by
  rcases x with ⟨a, b⟩
  change U256.toNat ((~~~ a, ~~~ b) : U128 × U128) = _
  rw [U256.toNat_pair, U256.toNat_pair, U128.toNat_complement, U128.toNat_complement]
  have ha := @U128.toNat_lt a
  have hb := @U128.toNat_lt b
  omega

/-! ### Shifts -/

private theorem U128.toNat_shiftRight_pair (a b : UInt64) (os : Nat) :
    U128.toNat (U128.shiftRight (a, b) os) =
      if os = 0 then (a.toNat <<< 64) ||| b.toNat
      else if os < 64 then ((a >>> os.toUInt64).toNat <<< 64) |||
        ((a <<< (64 - os).toUInt64) ||| (b >>> os.toUInt64)).toNat
      else if os < 128 then ((0 : UInt64).toNat <<< 64) ||| (a >>> (os - 64).toUInt64).toNat
      else (0 : Nat) := by
  unfold U128.shiftRight
  by_cases h0 : os = 0 <;> by_cases h64 : os < 64 <;> by_cases h128 : os < 128 <;>
    simp only [h0, h64, h128, ↓reduceIte] <;> rfl

private theorem U128.toNat_shiftLeft_pair (a b : UInt64) (os : Nat) :
    U128.toNat (U128.shiftLeft (a, b) os) =
      if os = 0 then (a.toNat <<< 64) ||| b.toNat
      else if os < 64 then (((a <<< os.toUInt64) ||| (b >>> (64 - os).toUInt64)).toNat <<< 64) |||
        (b <<< os.toUInt64).toNat
      else if os < 128 then ((b <<< (os - 64).toUInt64).toNat <<< 64) ||| (0 : UInt64).toNat
      else (0 : Nat) := by
  unfold U128.shiftLeft
  by_cases h0 : os = 0 <;> by_cases h64 : os < 64 <;> by_cases h128 : os < 128 <;>
    simp only [h0, h64, h128, ↓reduceIte] <;> rfl

private theorem U256.toNat_shiftRight_pair (a b : U128) (os : Nat) :
    U256.toNat (U256.shiftRight (a, b) os) =
      if os = 0 then (a.toNat <<< 128) ||| b.toNat
      else if os < 128 then ((a >>> os).toNat <<< 128) |||
        ((a <<< (128 - os)) ||| (b >>> os)).toNat
      else if os < 256 then ((0 : U128).toNat <<< 128) ||| (a >>> (os - 128)).toNat
      else (0 : Nat) := by
  unfold U256.shiftRight
  by_cases h0 : os = 0 <;> by_cases h128 : os < 128 <;> by_cases h256 : os < 256 <;>
    simp only [h0, h128, h256, ↓reduceIte] <;> rfl

private theorem U256.toNat_shiftLeft_pair (a b : U128) (s : Nat) :
    U256.toNat (U256.shiftLeft (a, b) s) =
      if s = 0 then (a.toNat <<< 128) ||| b.toNat
      else if s < 128 then (((a <<< s) ||| (b >>> (128 - s))).toNat <<< 128) |||
        (b <<< s).toNat
      else if s < 256 then ((b <<< (s - 128)).toNat <<< 128) ||| (0 : U128).toNat
      else (0 : Nat) := by
  unfold U256.shiftLeft
  by_cases h0 : s = 0 <;> by_cases h128 : s < 128 <;> by_cases h256 : s < 256 <;>
    simp only [h0, h128, h256, ↓reduceIte] <;> rfl

theorem U128.toNat_shiftRight (x : U128) (s : Nat) : (x >>> s).toNat = x.toNat >>> s := by
  rcases x with ⟨a, b⟩
  change (U128.shiftRight (a, b) s).toNat = ((a.toNat <<< 64) ||| b.toNat) >>> s
  rw [U128.toNat_shiftRight_pair]
  split_ifs with h0 h64 h128
  · subst h0; rfl
  · rw [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
      toNat_toUInt64_of_lt h64, toNat_toUInt64_of_lt (by omega : 64 - s < 64),
      Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt (by omega : 64 - s < 64)]
    apply Nat.eq_of_testBit_eq
    intro i
    have hlo : ((a.toNat <<< (64 - s)) % 2 ^ 64 ||| b.toNat >>> s) < 2 ^ 64 :=
      Nat.or_lt_two_pow (Nat.mod_lt _ (by positivity))
        (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (UInt64.toNat_lt _))
    rw [testBit_join hlo, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      testBit_join (UInt64.toNat_lt _)]
    by_cases hi : i < 64
    · rw [ite_eq_left hi, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
        Nat.testBit_shiftRight]
      by_cases hio : s + i < 64
      · rw [ite_eq_left hio]
        have : ¬ (64 - s ≤ i) := by omega
        simp only [hi, decide_true, ge_iff_le, this, decide_false, Bool.false_and, Bool.and_false,
          Bool.false_or]
      · rw [ite_eq_right hio]
        have hbf : b.toNat.testBit (s + i) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt64.toNat_lt _)
            (Nat.pow_le_pow_right (by omega) (by omega)))
        have : 64 - s ≤ i := by omega
        rw [show i - (64 - s) = s + i - 64 by omega]
        simp only [hi, decide_true, ge_iff_le, this, Bool.true_and, hbf, Bool.or_false]
    · rw [ite_eq_right hi, ite_eq_right (by omega), show s + i - 64 = s + (i - 64) by omega]
  · rw [UInt64.toNat_shiftRight, toNat_toUInt64_of_lt (by omega : s - 64 < 64),
      Nat.mod_eq_of_lt (by omega : s - 64 < 64)]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_shiftRight, testBit_join (UInt64.toNat_lt _), ite_eq_right (by omega),
      show (0 : UInt64).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or, Nat.testBit_shiftRight,
      show s + i - 64 = s - 64 + i by omega]
  · have hlt : ((a.toNat <<< 64) ||| b.toNat) < 2 ^ s :=
      Nat.lt_of_lt_of_le (U128.toNat_lt (x := (a, b))) (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]

theorem U128.toNat_shiftLeft (x : U128) (s : Nat) :
    (x <<< s).toNat = (x.toNat <<< s) % 2 ^ 128 := by
  rcases x with ⟨a, b⟩
  change (U128.shiftLeft (a, b) s).toNat = (((a.toNat <<< 64) ||| b.toNat) <<< s) % 2 ^ 128
  rw [U128.toNat_shiftLeft_pair]
  have hx : ((a.toNat <<< 64) ||| b.toNat) < 2 ^ 128 := U128.toNat_lt (x := (a, b))
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  split_ifs with h0 h64 h128
  · subst h0
    rw [Nat.sub_zero]
    by_cases hi : i < 128
    · simp only [hi, decide_true, ge_iff_le, Nat.zero_le, Bool.true_and]
    · simp only [hi, decide_false, Bool.false_and]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
  · rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft,
      toNat_toUInt64_of_lt h64, toNat_toUInt64_of_lt (by omega : 64 - s < 64),
      Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt (by omega : 64 - s < 64),
      testBit_join (Nat.mod_lt _ (by positivity)), Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    by_cases hi : i < 64
    · rw [ite_eq_left hi]
      by_cases hio : s ≤ i
      · rw [testBit_join (UInt64.toNat_lt _), ite_eq_left (by omega)]
        simp only [hi, decide_true, ge_iff_le, hio, Bool.true_and, show i < 128 by omega]
      · simp only [hi, decide_true, ge_iff_le, hio, decide_false, Bool.and_false, Bool.false_and]
    · rw [ite_eq_right hi, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
        Nat.testBit_shiftRight, testBit_join (UInt64.toNat_lt _)]
      by_cases hi2 : i < 128
      · have hio : s ≤ i := by omega
        by_cases h3 : i - s < 64
        · rw [ite_eq_left h3]
          by_cases h4 : s ≤ i - 64
          · simp only [hi2, decide_true, ge_iff_le, hio, Bool.true_and, show i - 64 < 64 by omega, h4]
            have hbz : b.toNat.testBit (64 - s + (i - 64)) = false :=
              Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt64.toNat_lt _)
                (Nat.pow_le_pow_right (by omega) (by omega)))
            rw [hbz, Bool.or_false]
            omega
          · simp only [hi2, decide_true, ge_iff_le, hio, Bool.true_and, show i - 64 < 64 by omega, h4,
              decide_false, Bool.false_and, Bool.false_or, show 64 - s + (i - 64) = i - s by omega]
        · rw [ite_eq_right h3]
          simp only [hi2, decide_true, ge_iff_le, hio, Bool.true_and, show i - 64 < 64 by omega,
            show s ≤ i - 64 by omega, show i - 64 - s = i - s - 64 by omega]
          have hbz : b.toNat.testBit (64 - s + (i - 64)) = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt64.toNat_lt _)
              (Nat.pow_le_pow_right (by omega) (by omega)))
          rw [hbz, Bool.or_false]
      · simp only [hi2, decide_false, Bool.false_and, show ¬ (i - 64 < 64) by omega, Bool.false_or]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt64.toNat_lt _)
          (Nat.pow_le_pow_right (by omega) (by omega)))
  · rw [UInt64.toNat_shiftLeft, toNat_toUInt64_of_lt (by omega : s - 64 < 64),
      Nat.mod_eq_of_lt (by omega : s - 64 < 64), show (0 : UInt64).toNat = 0 from rfl,
      Nat.or_zero, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    by_cases hi : i < 128
    · by_cases hio : s ≤ i
      · rw [testBit_join (UInt64.toNat_lt _), ite_eq_left (by omega)]
        simp only [hi, decide_true, ge_iff_le, show 64 ≤ i by omega, hio, Bool.true_and,
          show i - 64 < 64 by omega, show s - 64 ≤ i - 64 by omega,
          show i - 64 - (s - 64) = i - s by omega]
      · simp only [hi, decide_true, ge_iff_le, hio, decide_false, Bool.and_false, Bool.false_and]
        by_cases h64' : 64 ≤ i
        · simp only [h64', decide_true, Bool.true_and, show i - 64 < 64 by omega,
            show ¬ (s - 64 ≤ i - 64) by omega, decide_false, Bool.false_and]
        · simp only [h64', decide_false, Bool.false_and]
    · simp only [hi, decide_false, Bool.false_and]
      by_cases h64' : 64 ≤ i
      · simp only [h64', decide_true, Bool.true_and, show ¬ (i - 64 < 64) by omega, decide_false,
          Bool.false_and]
      · simp only [h64', decide_false, Bool.false_and]
  · rw [Nat.zero_testBit]
    by_cases hi : i < 128
    · simp only [hi, decide_true, Bool.true_and]
      by_cases hio : s ≤ i
      · omega
      · simp only [ge_iff_le, hio, decide_false, Bool.false_and]
    · simp only [hi, decide_false, Bool.false_and]

/-- `SHR` by `s` is division of the value by `2 ^ s`. -/
theorem U256.toNat_shiftRight (x : U256) (s : Nat) : (x >>> s).toNat = x.toNat >>> s := by
  rcases x with ⟨a, b⟩
  change (U256.shiftRight (a, b) s).toNat = ((a.toNat <<< 128) ||| b.toNat) >>> s
  rw [U256.toNat_shiftRight_pair]
  split_ifs with h0 h128 h256
  · subst h0; rfl
  · rw [U128.toNat_or, U128.toNat_shiftRight, U128.toNat_shiftLeft, U128.toNat_shiftRight]
    apply Nat.eq_of_testBit_eq
    intro i
    have hlo : ((a.toNat <<< (128 - s)) % 2 ^ 128 ||| b.toNat >>> s) < 2 ^ 128 :=
      Nat.or_lt_two_pow (Nat.mod_lt _ (by positivity))
        (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) U128.toNat_lt)
    rw [testBit_join hlo, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      testBit_join U128.toNat_lt]
    by_cases hi : i < 128
    · rw [ite_eq_left hi, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
        Nat.testBit_shiftRight]
      by_cases hio : s + i < 128
      · rw [ite_eq_left hio]
        have : ¬ (128 - s ≤ i) := by omega
        simp only [hi, decide_true, ge_iff_le, this, decide_false, Bool.false_and, Bool.and_false,
          Bool.false_or]
      · rw [ite_eq_right hio]
        have hbf : b.toNat.testBit (s + i) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le U128.toNat_lt
            (Nat.pow_le_pow_right (by omega) (by omega)))
        have : 128 - s ≤ i := by omega
        rw [show i - (128 - s) = s + i - 128 by omega]
        simp only [hi, decide_true, ge_iff_le, this, Bool.true_and, hbf, Bool.or_false]
    · rw [ite_eq_right hi, ite_eq_right (by omega), show s + i - 128 = s + (i - 128) by omega]
  · rw [U128.toNat_shiftRight]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_shiftRight, testBit_join U128.toNat_lt, ite_eq_right (by omega),
      show (0 : U128).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or, Nat.testBit_shiftRight,
      show s + i - 128 = s - 128 + i by omega]
  · have hlt : ((a.toNat <<< 128) ||| b.toNat) < 2 ^ s :=
      Nat.lt_of_lt_of_le (U256.toNat_lt (a, b)) (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]

/-- `SHL` by `s` is multiplication of the value by `2 ^ s`, modulo `2 ^ 256`. -/
theorem U256.toNat_shiftLeft (x : U256) (s : Nat) :
    (x <<< s).toNat = (x.toNat <<< s) % 2 ^ 256 := by
  rcases x with ⟨a, b⟩
  change (U256.shiftLeft (a, b) s).toNat = (((a.toNat <<< 128) ||| b.toNat) <<< s) % 2 ^ 256
  rw [U256.toNat_shiftLeft_pair]
  have hx : ((a.toNat <<< 128) ||| b.toNat) < 2 ^ 256 := U256.toNat_lt (a, b)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  split_ifs with h0 h128 h256
  · subst h0
    rw [Nat.sub_zero]
    by_cases hi : i < 256
    · simp only [hi, decide_true, ge_iff_le, Nat.zero_le, Bool.true_and]
    · simp only [hi, decide_false, Bool.false_and]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
  · rw [U128.toNat_or, U128.toNat_shiftLeft, U128.toNat_shiftRight, U128.toNat_shiftLeft,
      testBit_join (Nat.mod_lt _ (by positivity)), Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    by_cases hi : i < 128
    · rw [ite_eq_left hi]
      by_cases hio : s ≤ i
      · rw [testBit_join (U128.toNat_lt), ite_eq_left (by omega)]
        simp only [hi, decide_true, ge_iff_le, hio, Bool.true_and, show i < 256 by omega]
      · simp only [hi, decide_true, ge_iff_le, hio, decide_false, Bool.and_false, Bool.false_and]
    · rw [ite_eq_right hi, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
        Nat.testBit_shiftRight, testBit_join (U128.toNat_lt)]
      by_cases hi2 : i < 256
      · have hio : s ≤ i := by omega
        by_cases h3 : i - s < 128
        · rw [ite_eq_left h3]
          by_cases h4 : s ≤ i - 128
          · simp only [hi2, decide_true, ge_iff_le, hio, Bool.true_and, show i - 128 < 128 by omega, h4]
            have hbz : b.toNat.testBit (128 - s + (i - 128)) = false :=
              Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (U128.toNat_lt)
                (Nat.pow_le_pow_right (by omega) (by omega)))
            rw [hbz, Bool.or_false]
            omega
          · simp only [hi2, decide_true, ge_iff_le, hio, Bool.true_and, show i - 128 < 128 by omega, h4,
              decide_false, Bool.false_and, Bool.false_or, show 128 - s + (i - 128) = i - s by omega]
        · rw [ite_eq_right h3]
          simp only [hi2, decide_true, ge_iff_le, hio, Bool.true_and, show i - 128 < 128 by omega,
            show s ≤ i - 128 by omega, show i - 128 - s = i - s - 128 by omega]
          have hbz : b.toNat.testBit (128 - s + (i - 128)) = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (U128.toNat_lt)
              (Nat.pow_le_pow_right (by omega) (by omega)))
          rw [hbz, Bool.or_false]
      · simp only [hi2, decide_false, Bool.false_and, show ¬ (i - 128 < 128) by omega, Bool.false_or]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (U128.toNat_lt)
          (Nat.pow_le_pow_right (by omega) (by omega)))
  · rw [U128.toNat_shiftLeft, show (0 : U128).toNat = 0 from rfl,
      Nat.or_zero, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    by_cases hi : i < 256
    · by_cases hio : s ≤ i
      · rw [testBit_join (U128.toNat_lt), ite_eq_left (by omega)]
        simp only [hi, decide_true, ge_iff_le, show 128 ≤ i by omega, hio, Bool.true_and,
          show i - 128 < 128 by omega, show s - 128 ≤ i - 128 by omega,
          show i - 128 - (s - 128) = i - s by omega]
      · simp only [hi, decide_true, ge_iff_le, hio, decide_false, Bool.and_false, Bool.false_and]
        by_cases h128' : 128 ≤ i
        · simp only [h128', decide_true, Bool.true_and, show i - 128 < 128 by omega,
            show ¬ (s - 128 ≤ i - 128) by omega, decide_false, Bool.false_and]
        · simp only [h128', decide_false, Bool.false_and]
    · simp only [hi, decide_false, Bool.false_and]
      by_cases h128' : 128 ≤ i
      · simp only [h128', decide_true, Bool.true_and, show ¬ (i - 128 < 128) by omega, decide_false,
          Bool.false_and]
      · simp only [h128', decide_false, Bool.false_and]
  · rw [Nat.zero_testBit]
    by_cases hi : i < 256
    · simp only [hi, decide_true, Bool.true_and]
      by_cases hio : s ≤ i
      · omega
      · simp only [ge_iff_le, hio, decide_false, Bool.false_and]
    · simp only [hi, decide_false, Bool.false_and]

/-- A right shift by `256` or more gives `0`. -/
theorem U256.shiftRight_eq_zero_of_le (x : U256) {s : Nat} (h : 256 ≤ s) : x >>> s = 0 := by
  apply U256.toNat_inj
  rw [U256.toNat_shiftRight, U256.toNat_zero, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (U256.toNat_lt x) (Nat.pow_le_pow_right (by omega) h))

/-- A left shift by `256` or more gives `0`. -/
theorem U256.shiftLeft_eq_zero_of_le (x : U256) {s : Nat} (h : 256 ≤ s) : x <<< s = 0 := by
  apply U256.toNat_inj
  rw [U256.toNat_shiftLeft, U256.toNat_zero, Nat.shiftLeft_eq]
  exact Nat.mod_eq_zero_of_dvd
    (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 h) _)

/-! ### `BYTE` -/

theorem UInt8.toNat_toU256 (b : UInt8) : b.toU256.toNat = b.toNat := by
  simp only [UInt8.toU256, U256.toNat, U128.toNat, show (0 : U128).1.toNat = 0 from rfl,
    show (0 : U128).2.toNat = 0 from rfl, show (0 : UInt64).toNat = 0 from rfl, Nat.zero_shiftLeft,
    Nat.zero_or, UInt8.toNat_toUInt64]

private theorem U256.toNat_limbs (a b c d : UInt64) :
    U256.toNat ((a, b), (c, d)) =
      a.toNat * 2 ^ 192 + b.toNat * 2 ^ 128 + c.toNat * 2 ^ 64 + d.toNat := by
  have hb := UInt64.toNat_lt b
  have hc := UInt64.toNat_lt c
  have hd := UInt64.toNat_lt d
  change (((a.toNat <<< 64) ||| b.toNat) <<< 128) ||| ((c.toNat <<< 64) ||| d.toNat) = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb, ← Nat.shiftLeft_add_eq_or_of_lt hd,
    ← Nat.shiftLeft_add_eq_or_of_lt (by rw [Nat.shiftLeft_eq]; omega)]
  simp only [Nat.shiftLeft_eq]; omega

/-- Byte `i` of a word's big-endian encoding is bits `248 - 8 i` to `255 - 8 i`
of its value; past the 32nd byte the default `0` is read. -/
theorem U256.toNat_getD_toBytes (x : U256) (i : Nat) :
    (x.toBytes.getD i 0).toNat = if i < 32 then (x.toNat >>> (248 - 8 * i)) % 256 else 0 := by
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have hc := UInt64.toNat_lt c
  have hd := UInt64.toNat_lt d
  rw [U256.toNat_limbs]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;>
    simp [U256.toBytes, U128.toBytes, UInt64.toBytes, UInt32.toBytes, UInt16.toBytes,
      Nat.shiftRight_eq_div_pow] <;> omega

/-- `BYTE i x`, as the instruction table computes it, is byte `i` of `x` counted from
the most significant end, and `0` for `i ≥ 32`. -/
theorem U256.toNat_toU256_getD_toBytes (x : U256) (i : Nat) :
    (x.toBytes.getD i 0).toU256.toNat =
      if i < 32 then (x.toNat >>> (248 - 8 * i)) % 256 else 0 := by
  rw [UInt8.toNat_toU256, U256.toNat_getD_toBytes]

/-! ### `SIGNEXTEND` -/

private theorem UInt8.highBit_eq_testBit (z : UInt8) : z.highBit = z.toNat.testBit 7 := by
  unfold UInt8.highBit
  have h : (z &&& 128 != 0) = decide ((z &&& 128).toNat ≠ 0) := by
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, ne_eq, ← UInt8.toNat_inj]; rfl
  have h2 : z.toNat &&& 2 ^ 7 = if z.toNat.testBit 7 then 2 ^ 7 else 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hi : 7 = i
    · subst hi
      split <;> simp only [*, Nat.testBit_two_pow_self, decide_true, Bool.and_true, Nat.zero_testBit]
    · split <;> simp only [Nat.testBit_two_pow, hi, decide_false, Bool.and_false, Nat.zero_testBit]
  rw [h, UInt8.toNat_and, show (128 : UInt8).toNat = 2 ^ 7 from rfl, h2]
  cases z.toNat.testBit 7 <;> simp

private theorem U256.pack_toBytes (y : U256) : Bytes.pack y.toBytes 32 = y.toBytes := by
  rcases y with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

theorem Nat.two_pow_sub_two_pow_eq_shiftLeft {n k : Nat} (hk : k ≤ n) :
    2 ^ n - 2 ^ k = (2 ^ (n - k) - 1) <<< k := by
  rw [Nat.shiftLeft_eq, Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hk]

/-- The all-ones word shifted left by `k ≤ 256` is the top `256 - k` bits. -/
theorem U256.toNat_max_shiftLeft {k : Nat} (hk : k ≤ 256) :
    (U256.max <<< k).toNat = 2 ^ 256 - 2 ^ k := by
  rw [U256.toNat_shiftLeft, show U256.max.toNat = 2 ^ 256 - 1 by decide,
    Nat.two_pow_sub_two_pow_eq_shiftLeft hk]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < 256 <;> by_cases h2 : k ≤ i <;> simp [h1, h2] <;> omega

/-- The all-ones word shifted right by `256 - k` is the low `k` bits. -/
theorem U256.toNat_max_shiftRight {k : Nat} (hk : k ≤ 256) :
    (U256.max >>> (256 - k)).toNat = 2 ^ k - 1 := by
  rw [U256.toNat_shiftRight, show U256.max.toNat = 2 ^ 256 - 1 by decide]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  simp; omega

/-- Setting the top `256 - k` bits of a 256-bit number adds them to its low `k` bits. -/
theorem Nat.two_pow_sub_two_pow_or {k y : Nat} (hk : k ≤ 256) (hy : y < 2 ^ 256) :
    (2 ^ 256 - 2 ^ k) ||| y = 2 ^ 256 - 2 ^ k + y % 2 ^ k := by
  rw [Nat.two_pow_sub_two_pow_eq_shiftLeft hk,
    Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by positivity))]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow]
  by_cases h1 : i < 256
  · by_cases h2 : k ≤ i
    · simp [h2, show i - k < 256 - k by omega]
    · simp only [h2, decide_false, Bool.false_and, Bool.false_or, show i < k by omega,
        decide_true, Bool.true_and]
  · have : y.testBit i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [this]

/-- `SIGNEXTEND b x` for `b < 31` keeps the low `8 (b + 1)` bits of `x` and sets every
higher bit to bit `8 b + 7`; for `b ≥ 31` it is `x`. -/
theorem U256.toNat_signextend (b x : U256) :
    (U256.signextend b x).toNat =
      if b.toNat < 31 then
        (if x.toNat.testBit (8 * b.toNat + 7)
         then 2 ^ 256 - 2 ^ (8 * b.toNat + 8) + x.toNat % 2 ^ (8 * b.toNat + 8)
         else x.toNat % 2 ^ (8 * b.toNat + 8))
      else x.toNat := by
  have hlt : b < 31 ↔ b.toNat < 31 := by rw [U256.lt_iff_toNat_lt_toNat]; rfl
  unfold U256.signextend
  by_cases hb : b.toNat < 31
  · have hb' : b < 31 := hlt.mpr hb
    rw [dite_eq_left hb', ite_eq_left hb]
    have key : ∀ (i : Nat) (hi : i < (Bytes.pack x.toBytes 32).length),
        (Bytes.pack x.toBytes 32)[i]'hi = x.toBytes.getD i 0 := by
      intro i hi
      simp only [U256.pack_toBytes] at hi ⊢
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    have hz : ∀ (i : Nat), i = 32 - (b.toNat + 1) →
        ((x.toBytes.getD i 0).highBit = x.toNat.testBit (8 * b.toNat + 7)) := by
      rintro i rfl
      rw [UInt8.highBit_eq_testBit, U256.toNat_getD_toBytes, ite_eq_left (by omega),
        show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      simp only [show 7 < 8 from by decide, decide_true, Bool.true_and]
      congr 1; omega
    have hlen : 32 - (b.toNat + 1) < (Bytes.pack x.toBytes 32).length := by
      rw [U256.pack_toBytes]
      simp only [U256.toBytes, U128.toBytes, UInt64.toBytes, UInt32.toBytes, UInt16.toBytes,
        List.length_append, List.length_cons, List.length_nil]
      omega
    have hz' : UInt8.highBit ((x.toBytes.pack 32)[32 - (b.toNat + 1)]'hlen) =
        x.toNat.testBit (8 * b.toNat + 7) := by
      rw [key]; exact hz _ rfl
    simp only [cond_eq_ite]
    have hk : 8 * (b.toNat + 1) ≤ 256 := by omega
    rw [show 8 * b.toNat + 8 = 8 * (b.toNat + 1) by omega]
    split
    · rename_i hc
      have ht : x.toNat.testBit (8 * b.toNat + 7) = true := hz'.symm.trans hc
      rw [ite_eq_left ht]
      change (U256.or _ _).toNat = _
      rw [U256.toNat_or, U256.toNat_max_shiftLeft hk, Nat.two_pow_sub_two_pow_or hk (U256.toNat_lt x)]
    · rename_i hc
      have ht : ¬ x.toNat.testBit (8 * b.toNat + 7) = true := fun h => hc (hz'.trans h)
      rw [ite_eq_right ht]
      change (U256.and _ _).toNat = _
      rw [U256.toNat_and, U256.toNat_max_shiftRight hk, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  · rw [dite_eq_right (fun h => hb (hlt.mp h)), ite_eq_right hb]

end Jaune
