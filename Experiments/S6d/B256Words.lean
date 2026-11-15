import Jaune.WordFacts
import Experiments.S6d.Timing

/-!
# jsn-s6d: the S6d theorem set over the current word type `B256` (experiment; never lands)

Groups A-D and F: each `B256.s6d_<name>` is a verbatim copy of the current Jaune proof of
`B256.<name>` (or of the named lemma), declared in the same namespace so that every
unqualified name in the proof resolves exactly as in the original. The copy exists so that
its elaboration and kernel time can be profiled per declaration in one file; its helper
lemmas are the original's (counted by `Experiments/S6d/Count.lean`).

Group E has no Jaune lemma; both sides are written fresh, with comparable effort.
-/

set_option linter.unusedSimpArgs false
set_option Elab.async false

namespace Jaune

open Jaune _root_.Nat

/-! ## A. Nat bridge -/

-- Types.lean:80
s6d_time lemma B256.s6d_toNat_lt (x : B256) : x.toNat < 2 ^ 256 := by
  simp only [B256.toNat]; apply Nat.or_lt_two_pow
  · apply Nat.shiftLeft_lt_of_lt B128.toNat_lt
  · apply lt_trans B128.toNat_lt; omega

-- Types.lean:344
s6d_time theorem B256.s6d_toNat_inj (xs ys : B256) (eq : xs.toNat = ys.toNat) : xs = ys := by
  rw [← toB256_toNat xs, ← toB256_toNat ys, eq]

-- Types.lean:352
s6d_time theorem B256.s6d_toNat_toB256 (n : Nat) : (Nat.toB256 n).toNat = n ↾ 256 := by
  simp only [Nat.toB256, B256.toNat]; rw [toNat_toB128, toNat_toB128]
  apply Nat.or_eq_lo_add

-- Types.lean:356
s6d_time theorem B256.s6d_toNat_toB256_of_lt {n : Nat} (h : n < 2 ^ 256) :
    (Nat.toB256 n).toNat = n := by rw [B256.toNat_toB256, Nat.lo_eq_of_lt h]

-- Types.lean:359
s6d_time theorem B256.s6d_toNat_mul (x y : B256) :
    (x * y).toNat = (x.toNat * y.toNat) ↾ 256 := B256.toNat_toB256 _

-- Types.lean:362
s6d_time theorem B256.s6d_toNat_mod {x y : B256} (h : y ≠ 0) :
    (x % y).toNat = x.toNat % y.toNat := by
  show (B256.divMod x y).snd.toNat = _
  rw [B256.divMod, ite_eq_right h]
  exact B256.toNat_toB256_of_lt
    (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (B256.toNat_lt x))

-- Types.lean:589
s6d_time lemma B256.s6d_toNat_add (x y : B256) :
    (x + y).toNat = (x.toNat + y.toNat) ↾ 256 := by
  rw [B256.add_eq]; simp only [B256.toNat]
  rw [Nat.shl_or_add_shl_or_lo_add B128.toNat_lt B128.toNat_lt]
  apply congr_arg₂ _ (congr_arg₂ _ _ rfl) (B128.toNat_add _ _)
  rw [B128.toNat_add, B128.toNat_add, Nat.lo_add_lo]
  apply congr_arg₂ _ (congr_arg₂ _ rfl _) rfl
  rw [← ite_not, @ite_distrib _ _ B128.toNat]
  apply ite_eq_ite_of_iff _ rfl rfl
  simp [B128.toNat_overflow]

-- Types.lean:603
s6d_time lemma B256.s6d_toNat_add_eq_of_nof (x y : B256) (h : B256.Nof x y) :
    (x + y).toNat = (x.toNat + y.toNat) := by
  rw [B256.toNat_add, Nat.lo_eq_of_lt h]

-- Types.lean:684
s6d_time theorem B256.s6d_toNat_sub_eq_of_le (xs ys : B256) (h : ys ≤ xs) :
    (xs - ys).toNat = xs.toNat - ys.toNat := by
  rw [toNat_sub, Nat.lo, Nat.add_sub_mod_eq_sub]
  · apply B256.toNat_lt
  · apply B256.toNat_le_toNat h

-- MulDiv.lean:77
s6d_time theorem B256.s6d_toNat_div {x y : B256} (h : y ≠ 0) :
    (x / y).toNat = x.toNat / y.toNat := by
  show (B256.divMod x y).fst.toNat = _
  rw [B256.divMod, ite_eq_right h]
  exact B256.toNat_toB256_of_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (B256.toNat_lt x))

/-! ## B. Order -/

-- Types.lean:484
s6d_time lemma B256.s6d_toNat_lt_toNat {a b : B256} (h : a < b) :
    a.toNat < b.toNat := by
  rcases a with ⟨_, _⟩; rcases b with ⟨_, _⟩
  rcases h with h | h <;> simp at h
  · rw [B128.lt_iff_toNat_lt_toNat] at h
    apply Nat.shl_or_lt_shl_or_of_left h B128.toNat_lt B128.toNat_lt
  · rw [h.1]; apply Nat.shl_or_lt_shl_or_of_right _ B128.toNat_lt
    rw [← B128.lt_iff_toNat_lt_toNat]; apply h.2

-- Types.lean:522
s6d_time lemma B256.s6d_lt_iff_toNat_lt_toNat {a b : B256} : a < b ↔ a.toNat < b.toNat := by
  constructor
  · apply B256.toNat_lt_toNat
  · apply B256.lt_of_toNat_lt_toNat

-- Types.lean:554
s6d_time lemma B256.s6d_le_iff_toNat_le_toNat {a b : B256} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [← not_iff_not, not_le, Nat.not_le, lt_iff_toNat_lt_toNat]

/-! ## C. Comparison flags (WordFacts.lean) -/

-- WordFacts.lean:25
s6d_time theorem B256.s6d_one_ne_zero : (1 : B256) ≠ 0 := by decide +kernel

-- WordFacts.lean:29
s6d_time theorem B256.s6d_eqCheck_ne_zero_iff {x y : B256} : B256.eqCheck x y ≠ 0 ↔ x = y := by
  unfold B256.eqCheck
  by_cases h : x = y <;> simp [h, B256.one_ne_zero]

-- WordFacts.lean:37
s6d_time theorem B256.s6d_ltCheck_ne_zero_iff {x y : B256} : B256.ltCheck x y ≠ 0 ↔ x < y := by
  unfold B256.ltCheck
  by_cases h : x < y <;> simp [h, B256.one_ne_zero]

-- WordFacts.lean:49
s6d_time theorem B256.s6d_gtCheck_eq_zero_iff {x y : B256} : B256.gtCheck x y = 0 ↔ ¬ y < x := by
  unfold B256.gtCheck
  by_cases h : y < x <;> simp [h, B256.one_ne_zero]

-- WordFacts.lean:70
s6d_time theorem B256.s6d_ltCheck_eq_zero_of_toNat_le {x y : B256} (h : y.toNat ≤ x.toNat) :
    B256.ltCheck x y = 0 :=
  B256.ltCheck_eq_zero_iff.mpr fun hlt => by
    have := B256.toNat_lt_toNat hlt
    omega

-- WordFacts.lean:89
s6d_time theorem B256.s6d_gtCheck_ne_zero_of_toNat_lt {x y : B256} (h : y.toNat < x.toNat) :
    B256.gtCheck x y ≠ 0 :=
  B256.gtCheck_ne_zero_iff.mpr (B256.lt_of_toNat_lt_toNat h)

/-! ## D. Bytes -/

-- Basic.lean:893
s6d_time lemma B256.s6d_length_toBytes (w : B256) : w.toBytes.length = 32 := rfl

-- Basic.lean:1512
s6d_time lemma B256.s6d_toB256_toBytes (x : B256) : x.toBytes.toB256 = x := by
  show Bytes.toB256.go 0 0 0 0 (B256.toBytes x) = ((x.1.1, x.1.2), (x.2.1, x.2.2))
  simp only [B256.toBytes, B128.toBytes, List.append_assoc]
  rw [Bytes.toB256_go_append_toBytes, Bytes.toB256_go_append_toBytes,
      Bytes.toB256_go_append_toBytes]
  rw [show x.2.2.toBytes = x.2.2.toBytes ++ [] by simp]
  rw [Bytes.toB256_go_append_toBytes]
  rfl

-- Types.lean:264
s6d_time lemma List.s6d_toB256_pair (n : Nat) (n_lt : n < 2 ^ 16):
    Bytes.toB256 [(n >>> 8).toUInt8, n.toUInt8] = n.toB256 := by
  have hlow : ∀ a b : UInt8, UInt8.toUInt64 a <<< 8 ||| UInt8.toUInt64 b = Bytes.toUInt64 [a, b] := by
    intro a b
    simp only [ Bytes.toUInt64, Bytes.toUInt32, Bytes.toUInt16, Bytes.getElem_packV,
      Bytes.pack, List.takeRightD, List.takeD,
      List.reverse, List.reverseAux, List.tail, List.headD, List.take, List.drop,
      List.getD_cons_zero, List.getD_cons_succ ]
    simp
    apply congrArg (fun x : UInt64 => x ||| b.toUInt64)
    rw [← UInt64.toNat_inj]
    rw [UInt64.toNat_mod, UInt64.toNat_mod, UInt64.toNat_shiftLeft_lo]
    have hw : UInt64.toNat (UInt8.toUInt64 a) = UInt8.toNat a := by cases a; rfl
    have h8 : UInt64.toNat 8 % 64 = 8 := rfl
    have h32 : UInt64.toNat 4294967296 = 4294967296 := rfl
    have h16 : UInt64.toNat 65536 = 65536 := rfl
    rw [hw, h8, h32, h16]
    simp only [Nat.shiftLeft_eq, Nat.lo]
    have h := UInt8.toNat_lt a
    omega
  show Bytes.toB256 [(n >>> 8).toUInt8, n.toUInt8] = n.toB256
  rw [Bytes.toB256_pair, hlow, List.toUInt64_pair n n_lt]
  have h128 : n >>> 128 = 0 := Nat.shiftRight_eq_zero _ _ (by omega)
  have h64 : n >>> 64 = 0 := Nat.shiftRight_eq_zero _ _ (by omega)
  simp only [Nat.toB256, Nat.toB128, h128, h64]
  rfl

/-! ## E. Bit and sign (no Jaune lemma: written fresh) -/
s6d_time theorem s6d_UInt64_testBit_ge (a : UInt64) {i : Nat} (h : 64 ≤ i) : a.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (UInt64.toNat_lt a) (Nat.pow_le_pow_right (by omega) h))

s6d_time theorem s6d_toUInt64_mod {k : Nat} (h : k < 64) : k.toUInt64.toNat % 64 = k := by
  rw [toNat_toUInt64, Nat.lo, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt h]

s6d_time theorem B128.s6d_testBit_toNat (a b : UInt64) (i : Nat) :
    (B128.toNat ((a, b) : B128)).testBit i =
      if i < 64 then b.toNat.testBit i else a.toNat.testBit (i - 64) := by
  simp only [B128.toNat, Nat.testBit_or, Nat.testBit_shiftLeft]
  split <;> rename_i h
  · simp [show ¬ i ≥ 64 by omega]
  · simp [show i ≥ 64 by omega, s6d_UInt64_testBit_ge _ (show 64 ≤ i by omega)]

s6d_time theorem B128.s6d_toNat_shiftRight (x : B128) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rcases x with ⟨a, b⟩
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_div_two_pow]
  show (B128.toNat (if n = 0 then ((a, b) : B128) else if n < 64 then
      ((a >>> n.toUInt64, (a <<< (64 - n).toUInt64) ||| (b >>> n.toUInt64)) : B128)
      else if n < 128 then ((0, a >>> (n - 64).toUInt64) : B128) else ((0, 0) : B128))).testBit i =
    (B128.toNat ((a, b) : B128)).testBit (i + n)
  by_cases h0 : n = 0
  · simp only [h0, ↓reduceIte]; simp
  have key := fun (P Q : UInt64) => B128.s6d_testBit_toNat P Q
  by_cases h64 : n < 64
  · simp only [h0, h64, ↓reduceIte]
    rw [key, key]
    simp (disch := omega) only [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft,
      Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      s6d_toUInt64_mod, UInt64.toNat_zero, Nat.zero_testBit]
    have ge := fun k (h : 64 ≤ k) => s6d_UInt64_testBit_ge b h
    have gea := fun k (h : 64 ≤ k) => s6d_UInt64_testBit_ge a h
    by_cases hi : i < 64
    · by_cases hin : i + n < 64
      · simp [hi, hin, show ¬ i ≥ 64 - n by omega, Nat.add_comm n i]
      · simp [hi, hin, show i ≥ 64 - n by omega, ge (n + i) (by omega),
          show i - (64 - n) = i + n - 64 by omega]
    · simp [hi, show ¬ i + n < 64 by omega, show n + (i - 64) = i + n - 64 by omega]
  by_cases h128 : n < 128
  · simp only [h0, h64, h128, ↓reduceIte]
    rw [key, key]
    simp (disch := omega) only [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft,
      Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      s6d_toUInt64_mod, UInt64.toNat_zero, Nat.zero_testBit]
    have gea := fun k (h : 64 ≤ k) => s6d_UInt64_testBit_ge a h
    by_cases hi : i < 64
    · simp [hi, show ¬ i + n < 64 by omega, show n - 64 + i = i + n - 64 by omega]
    · simp [hi, show ¬ i + n < 64 by omega, gea (i + n - 64) (by omega)]
  · simp only [h0, h64, h128, ↓reduceIte]
    rw [key, key]
    simp (disch := omega) only [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft,
      Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      s6d_toUInt64_mod, UInt64.toNat_zero, Nat.zero_testBit]
    have gea := fun k (h : 64 ≤ k) => s6d_UInt64_testBit_ge a h
    simp [show ¬ i + n < 64 by omega, gea (i + n - 64) (by omega)]

s6d_time theorem B128.s6d_testBit_shiftLeft (x : B128) (n i : Nat) :
    (x <<< n).toNat.testBit i = (decide (i < 128) && (decide (n ≤ i) && x.toNat.testBit (i - n))) := by
  rcases x with ⟨a, b⟩
  show (B128.toNat (if n = 0 then ((a, b) : B128) else if n < 64 then
      (((a <<< n.toUInt64) ||| (b >>> (64 - n).toUInt64), b <<< n.toUInt64) : B128)
      else if n < 128 then ((b <<< (n - 64).toUInt64, 0) : B128) else ((0, 0) : B128))).testBit i =
    (decide (i < 128) && (decide (n ≤ i) && (B128.toNat ((a, b) : B128)).testBit (i - n)))
  have key := fun (P Q : UInt64) => B128.s6d_testBit_toNat P Q
  have ge := fun k (h : 64 ≤ k) => s6d_UInt64_testBit_ge b h
  have gea := fun k (h : 64 ≤ k) => s6d_UInt64_testBit_ge a h
  by_cases h0 : n = 0
  · subst h0; simp only [↓reduceIte, key]
    by_cases hi : i < 64
    · simp [hi, show i < 128 by omega]
    · by_cases hi' : i < 128
      · simp [hi, hi']
      · simp [hi, hi', gea (i - 64) (by omega)]
  by_cases h64 : n < 64
  · simp only [h0, h64, ↓reduceIte]
    rw [key, key]
    simp (disch := omega) only [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft,
      Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      s6d_toUInt64_mod, UInt64.toNat_zero, Nat.zero_testBit]
    by_cases hi : i < 64
    · by_cases hn : n ≤ i
      · simp [hi, hn, show i < 128 by omega, show i - n < 64 by omega]
      · simp [hi, hn, show i < 128 by omega]
    · by_cases hi' : i < 128
      · by_cases hn : i - n < 64
        · simp [hi, hi', hn, show n ≤ i by omega, show ¬ i - 64 ≥ n by omega,
            show 64 - n + (i - 64) = i - n by omega, show i - 64 < 64 by omega]
        · simp [hi, hi', hn, show n ≤ i by omega, show i - 64 ≥ n by omega,
            show i - 64 < 64 by omega, show i - 64 - n = i - n - 64 by omega,
            ge (64 - n + (i - 64)) (by omega)]
      · simp [hi, hi', show ¬ i - 64 < 64 by omega, ge (64 - n + (i - 64)) (by omega)]
  by_cases h128 : n < 128
  · simp only [h0, h64, h128, ↓reduceIte]
    rw [key, key]
    simp (disch := omega) only [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft,
      Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      s6d_toUInt64_mod, UInt64.toNat_zero, Nat.zero_testBit]
    by_cases hi : i < 64
    · simp [hi, show ¬ n ≤ i by omega, show i < 128 by omega]
    · by_cases hi' : i < 128
      · by_cases hn : n ≤ i
        · simp [hi, hi', hn, show i - 64 < 64 by omega, show i - 64 ≥ n - 64 by omega,
            show i - n < 64 by omega, show i - 64 - (n - 64) = i - n by omega]
        · simp [hi, hi', hn, show i - 64 < 64 by omega, show ¬ i - 64 ≥ n - 64 by omega]
      · simp [hi, hi', show ¬ i - 64 < 64 by omega]
  · simp only [h0, h64, h128, ↓reduceIte]
    rw [key]
    by_cases hi : i < 64
    · simp [hi, show ¬ n ≤ i by omega]
    · by_cases hi' : i < 128
      · simp [hi, hi', show ¬ n ≤ i by omega]
      · simp [hi, hi']

s6d_time theorem B128.s6d_testBit_shiftRight (x : B128) (n i : Nat) :
    (x >>> n).toNat.testBit i = x.toNat.testBit (i + n) := by
  rw [B128.s6d_toNat_shiftRight, Nat.testBit_div_two_pow]

s6d_time theorem B128.s6d_testBit_or (x y : B128) (i : Nat) :
    (x ||| y).toNat.testBit i = (x.toNat.testBit i || y.toNat.testBit i) := by
  rcases x with ⟨a, b⟩; rcases y with ⟨c, d⟩
  show (B128.toNat (((a ||| c), (b ||| d)) : B128)).testBit i = _
  rw [B128.s6d_testBit_toNat, B128.s6d_testBit_toNat, B128.s6d_testBit_toNat]
  split <;> simp [UInt64.toNat_or, Nat.testBit_or]

s6d_time theorem B128.s6d_testBit_ge (x : B128) {i : Nat} (h : 128 ≤ i) : x.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le B128.toNat_lt (Nat.pow_le_pow_right (by omega) h))

s6d_time theorem B256.s6d_testBit_toNat (a b : B128) (i : Nat) :
    (B256.toNat ((a, b) : B256)).testBit i =
      if i < 128 then b.toNat.testBit i else a.toNat.testBit (i - 128) := by
  simp only [B256.toNat, Nat.testBit_or, Nat.testBit_shiftLeft]
  split <;> rename_i h
  · simp [show ¬ i ≥ 128 by omega]
  · simp [show i ≥ 128 by omega, B128.s6d_testBit_ge b (show 128 ≤ i by omega)]

s6d_time theorem B256.s6d_toNat_shiftRight (x : B256) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rcases x with ⟨a, b⟩
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_div_two_pow]
  show (B256.toNat (if n = 0 then ((a, b) : B256) else if n < 128 then
      ((a >>> n, (a <<< (128 - n)) ||| (b >>> n)) : B256)
      else if n < 256 then ((0, a >>> (n - 128)) : B256) else ((0, 0) : B256))).testBit i =
    (B256.toNat ((a, b) : B256)).testBit (i + n)
  have key := fun (P Q : B128) => B256.s6d_testBit_toNat P Q
  have ge := fun k (h : 128 ≤ k) => B128.s6d_testBit_ge b h
  have gea := fun k (h : 128 ≤ k) => B128.s6d_testBit_ge a h
  have z : ∀ k, (0 : B128).toNat.testBit k = false := fun k => by
    rw [B128.toNat_zero, Nat.zero_testBit]
  by_cases h0 : n = 0
  · simp only [h0, ↓reduceIte]; simp
  by_cases h128 : n < 128
  · simp only [h0, h128, ↓reduceIte]
    rw [key, key]
    simp only [B128.s6d_testBit_or, B128.s6d_testBit_shiftLeft, B128.s6d_testBit_shiftRight]
    by_cases hi : i < 128
    · by_cases hin : i + n < 128
      · simp [hi, hin, show ¬ 128 - n ≤ i by omega, Nat.add_comm n i]
      · simp [hi, hin, show 128 - n ≤ i by omega, ge (i + n) (by omega),
          show i - (128 - n) = i + n - 128 by omega]
    · simp [hi, show ¬ i + n < 128 by omega, show i - 128 + n = i + n - 128 by omega]
  by_cases h256 : n < 256
  · simp only [h0, h128, h256, ↓reduceIte]
    rw [key, key]
    simp only [B128.s6d_testBit_shiftRight, z]
    by_cases hi : i < 128
    · simp [hi, show ¬ i + n < 128 by omega, show i + (n - 128) = i + n - 128 by omega]
    · simp [hi, show ¬ i + n < 128 by omega, gea (i + n - 128) (by omega)]
  · simp only [h0, h128, h256, ↓reduceIte]
    rw [key, key, z, z]
    simp [show ¬ i + n < 128 by omega, gea (i + n - 128) (by omega)]

s6d_time theorem B256.s6d_toNat_shiftLeft (x : B256) (n : Nat) :
    (x <<< n).toNat = x.toNat * 2 ^ n % 2 ^ 256 := by
  rcases x with ⟨a, b⟩
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow]
  show (B256.toNat (if n = 0 then ((a, b) : B256) else if n < 128 then
      (((a <<< n) ||| (b >>> (128 - n)), b <<< n) : B256)
      else if n < 256 then ((b <<< (n - 128), 0) : B256) else ((0, 0) : B256))).testBit i =
    (decide (i < 256) && (decide (n ≤ i) && (B256.toNat ((a, b) : B256)).testBit (i - n)))
  have key := fun (P Q : B128) => B256.s6d_testBit_toNat P Q
  have ge := fun k (h : 128 ≤ k) => B128.s6d_testBit_ge b h
  have gea := fun k (h : 128 ≤ k) => B128.s6d_testBit_ge a h
  have z : ∀ k, (0 : B128).toNat.testBit k = false := fun k => by
    rw [B128.toNat_zero, Nat.zero_testBit]
  by_cases h0 : n = 0
  · subst h0; simp only [↓reduceIte, key]
    by_cases hi : i < 128
    · simp [hi, show i < 256 by omega]
    · by_cases hi' : i < 256
      · simp [hi, hi']
      · simp [hi, hi', gea (i - 128) (by omega)]
  by_cases h128 : n < 128
  · simp only [h0, h128, ↓reduceIte]
    rw [key, key]
    simp only [B128.s6d_testBit_or, B128.s6d_testBit_shiftLeft, B128.s6d_testBit_shiftRight]
    by_cases hi : i < 128
    · by_cases hn : n ≤ i
      · simp [hi, hn, show i < 256 by omega, show i - n < 128 by omega]
      · simp [hi, hn, show i < 256 by omega]
    · by_cases hi' : i < 256
      · by_cases hn : i - n < 128
        · simp [hi, hi', hn, show n ≤ i by omega, show ¬ n ≤ i - 128 by omega,
            show i - 128 + (128 - n) = i - n by omega, show i - 128 < 128 by omega]
        · simp [hi, hi', hn, show n ≤ i by omega, show n ≤ i - 128 by omega,
            show i - 128 < 128 by omega, show i - 128 - n = i - n - 128 by omega,
            ge (i - 128 + (128 - n)) (by omega)]
      · simp [hi, hi', show ¬ i - 128 < 128 by omega, ge (i - 128 + (128 - n)) (by omega)]
  by_cases h256 : n < 256
  · simp only [h0, h128, h256, ↓reduceIte]
    rw [key, key]
    simp only [B128.s6d_testBit_shiftLeft, z]
    by_cases hi : i < 128
    · simp [hi, show ¬ n ≤ i by omega, show i < 256 by omega]
    · by_cases hi' : i < 256
      · by_cases hn : n ≤ i
        · simp [hi, hi', hn, show i - 128 < 128 by omega, show n - 128 ≤ i - 128 by omega,
            show i - n < 128 by omega, show i - 128 - (n - 128) = i - n by omega]
        · simp [hi, hi', hn, show i - 128 < 128 by omega, show ¬ n - 128 ≤ i - 128 by omega]
      · simp [hi, hi', show ¬ i - 128 < 128 by omega]
  · simp only [h0, h128, h256, ↓reduceIte]
    rw [key, z]
    by_cases hi : i < 128
    · simp [hi, show ¬ n ≤ i by omega, z]
    · by_cases hi' : i < 256
      · simp [hi, hi', show ¬ n ≤ i by omega, z]
      · simp [hi, hi', z]

s6d_time theorem B256.s6d_sdiv_smin_negOne : B256.sdiv B256.smin B256.negOne = B256.smin := by
  decide +kernel

s6d_time theorem B256.s6d_sdiv_of_nonneg {x y : B256} (hx : B256.isNeg x = false)
    (hy : B256.isNeg y = false) : B256.sdiv x y = x / y := by
  have hs : B256.isNeg B256.smin = true := by decide +kernel
  unfold B256.sdiv
  by_cases h0 : y = 0
  · subst h0; rfl
  · have hne : ¬ (x = B256.smin ∧ y = B256.negOne) := fun ⟨h, _⟩ => by
      rw [h, hs] at hx; cases hx
    simp only [h0, hne, ↓reduceIte, hx, hy]

s6d_time theorem B256.s6d_arithShiftRight_of_nonneg {x : B256} (hx : B256.isNeg x = false) (n : Nat) :
    B256.arithShiftRight x n = x >>> n := by
  simp [B256.arithShiftRight, hx]

/-! ## F. MulDiv word bridges (MulDiv.lean) -/

-- MulDiv.lean:44
s6d_time theorem B256.s6d_toNat_ne_zero {z : B256} (h : z ≠ 0) : z.toNat ≠ 0 := by
  intro hz
  exact h (B256.toNat_inj z 0 (by rw [hz, B256.toNat_zero]))

-- MulDiv.lean:55
s6d_time theorem B256.s6d_nofm_iff_le_div {y : B256} (hy : y ≠ 0) (x : B256) :
    B256.Nofm x y ↔ x.toNat ≤ (2 ^ 256 - 1) / y.toNat := by
  have hpos : 0 < 2 ^ 256 := Nat.two_pow_pos 256
  rw [B256.Nofm, Nat.le_div_iff_mul_le (B256.toNat_pos hy)]
  omega

-- MulDiv.lean:71
s6d_time theorem B256.s6d_toNat_mul_eq_of_nofm {x y : B256} (h : B256.Nofm x y) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [B256.toNat_mul, Nat.lo_eq_of_lt h]

-- MulDiv.lean:86
s6d_time theorem B256.s6d_toNat_mulmod {x y z : B256} (h : z ≠ 0) :
    (B256.mulmod x y z).toNat = x.toNat * y.toNat % z.toNat := by
  rw [B256.mulmod, ite_eq_right h]
  exact B256.toNat_toB256_of_lt
    (Nat.lt_trans (Nat.mod_lt _ (B256.toNat_pos h)) (B256.toNat_lt z))

-- MulDiv.lean:92
s6d_time theorem B256.s6d_toNat_addmod {x y z : B256} (h : z ≠ 0) :
    (B256.addmod x y z).toNat = (x.toNat + y.toNat) % z.toNat := by
  rw [B256.addmod, ite_eq_right h]
  exact B256.toNat_toB256_of_lt
    (Nat.lt_trans (Nat.mod_lt _ (B256.toNat_pos h)) (B256.toNat_lt z))

end Jaune
