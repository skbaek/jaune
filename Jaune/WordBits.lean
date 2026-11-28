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

theorem U128.toNat_and (x y : U128) : (x &&& y).toNat = x.toNat &&& y.toNat := by
  sorry

theorem U128.toNat_or (x y : U128) : (x ||| y).toNat = x.toNat ||| y.toNat := by
  sorry

theorem U128.toNat_xor (x y : U128) : (x ^^^ y).toNat = x.toNat ^^^ y.toNat := by
  sorry

theorem U128.toNat_complement (x : U128) : (~~~ x).toNat = 2 ^ 128 - 1 - x.toNat := by
  sorry

/-- `AND` is the bitwise conjunction of the operands' values. -/
theorem U256.toNat_and (x y : U256) : (U256.and x y).toNat = x.toNat &&& y.toNat := by
  sorry

/-- `OR` is the bitwise disjunction of the operands' values. -/
theorem U256.toNat_or (x y : U256) : (U256.or x y).toNat = x.toNat ||| y.toNat := by
  sorry

/-- `XOR` is the bitwise exclusive or of the operands' values. -/
theorem U256.toNat_xor (x y : U256) : (U256.xor x y).toNat = x.toNat ^^^ y.toNat := by
  sorry

/-- `NOT` subtracts the value from the all-ones word. -/
theorem U256.toNat_complement (x : U256) : (~~~ x).toNat = 2 ^ 256 - 1 - x.toNat := by
  sorry

/-! ### Shifts -/

theorem U128.toNat_shiftRight (x : U128) (s : Nat) : (x >>> s).toNat = x.toNat >>> s := by
  sorry

theorem U128.toNat_shiftLeft (x : U128) (s : Nat) :
    (x <<< s).toNat = (x.toNat <<< s) % 2 ^ 128 := by
  sorry

/-- `SHR` by `s` is division of the value by `2 ^ s`. -/
theorem U256.toNat_shiftRight (x : U256) (s : Nat) : (x >>> s).toNat = x.toNat >>> s := by
  sorry

/-- `SHL` by `s` is multiplication of the value by `2 ^ s`, modulo `2 ^ 256`. -/
theorem U256.toNat_shiftLeft (x : U256) (s : Nat) :
    (x <<< s).toNat = (x.toNat <<< s) % 2 ^ 256 := by
  sorry

/-- A right shift by `256` or more gives `0`. -/
theorem U256.shiftRight_eq_zero_of_le (x : U256) {s : Nat} (h : 256 ≤ s) : x >>> s = 0 := by
  sorry

/-- A left shift by `256` or more gives `0`. -/
theorem U256.shiftLeft_eq_zero_of_le (x : U256) {s : Nat} (h : 256 ≤ s) : x <<< s = 0 := by
  sorry

/-! ### `BYTE` -/

theorem UInt8.toNat_toU256 (b : UInt8) : b.toU256.toNat = b.toNat := by
  sorry

/-- Byte `i` of a word's big-endian encoding is bits `248 - 8 i` to `255 - 8 i`
of its value; past the 32nd byte the default `0` is read. -/
theorem U256.toNat_getD_toBytes (x : U256) (i : Nat) :
    (x.toBytes.getD i 0).toNat = if i < 32 then (x.toNat >>> (248 - 8 * i)) % 256 else 0 := by
  sorry

/-- `BYTE i x`, as the instruction table computes it, is byte `i` of `x` counted from
the most significant end, and `0` for `i ≥ 32`. -/
theorem U256.toNat_toU256_getD_toBytes (x : U256) (i : Nat) :
    (x.toBytes.getD i 0).toU256.toNat =
      if i < 32 then (x.toNat >>> (248 - 8 * i)) % 256 else 0 := by
  sorry

/-! ### `SIGNEXTEND` -/

/-- `SIGNEXTEND b x` for `b < 31` keeps the low `8 (b + 1)` bits of `x` and sets every
higher bit to bit `8 b + 7`; for `b ≥ 31` it is `x`. -/
theorem U256.toNat_signextend (b x : U256) :
    (U256.signextend b x).toNat =
      if b.toNat < 31 then
        (if x.toNat.testBit (8 * b.toNat + 7)
         then 2 ^ 256 - 2 ^ (8 * b.toNat + 8) + x.toNat % 2 ^ (8 * b.toNat + 8)
         else x.toNat % 2 ^ (8 * b.toNat + 8))
      else x.toNat := by
  sorry

end Jaune
