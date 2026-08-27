-- MulDiv.lean : multiplicative arithmetic — floor/ceil `a * b / d` facts over
-- `Nat`, with the `B256` word-level bridges that connect them to compiled code.

import Jaune.Types

namespace Jaune

open Jaune _root_.Nat

/-!
# Multiplicative arithmetic

Ratio pricing computes `a * b / d`, and every such computation rounds. This
module collects the facts a proof about such a computation needs: the defining
bounds of floor and ceiling division, the direction each one rounds in,
monotonicity in each argument, the loss of a division/multiplication round
trip, and how a division reacts when its denominator or numerator is
perturbed.

Everything is stated over `Nat` and parametrically in the scale: no fixed-point
constant appears anywhere, and every division carries an explicit `d ≠ 0` side
condition rather than leaning on `n / 0 = 0`.

The word-level section bridges to `B256`. Those statements are either explicit
about the `% 2 ^ 256` truncation or carry a no-overflow hypothesis; none of
them states an unconditional word equality that hides wraparound.
-/

/-! ## Word-level bridges -/

/-- No-overflow predicate for `B256` multiplication, mirroring `B256.Nof`. -/
def B256.Nofm (xs ys : B256) : Prop := xs.toNat * ys.toNat < 2 ^ 256

theorem B256.toNat_ne_zero {z : B256} (h : z ≠ 0) : z.toNat ≠ 0 := by
  intro hz
  exact h (B256.toNat_inj z 0 (by rw [hz, B256.toNat_zero]))

theorem B256.toNat_pos {z : B256} (h : z ≠ 0) : 0 < z.toNat :=
  Nat.pos_of_ne_zero (B256.toNat_ne_zero h)

theorem B256.toNat_one : (1 : B256).toNat = 1 := rfl

/-- The full-width product, truncated: the multiplication a word actually does. -/
theorem B256.toNat_mul_mod (x y : B256) :
    (x * y).toNat = x.toNat * y.toNat % 2 ^ 256 :=
  B256.toNat_mul x y

/-- The untruncated product, available exactly when it does not overflow. -/
theorem B256.toNat_mul_eq_of_nofm {x y : B256} (h : B256.Nofm x y) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [B256.toNat_mul, Nat.lo_eq_of_lt h]

theorem B256.toNat_div {x y : B256} (h : y ≠ 0) :
    (x / y).toNat = x.toNat / y.toNat := by
  show (B256.divMod x y).fst.toNat = _
  rw [B256.divMod, if_neg h]
  exact B256.toNat_toB256_of_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (B256.toNat_lt x))

/-- `mulmod` computes the full-width product modulo `z`, with no intermediate
truncation: the identity that makes it usable as an exact-arithmetic primitive. -/
theorem B256.toNat_mulmod {x y z : B256} (h : z ≠ 0) :
    (B256.mulmod x y z).toNat = x.toNat * y.toNat % z.toNat := by
  rw [B256.mulmod, if_neg h]
  exact B256.toNat_toB256_of_lt
    (Nat.lt_trans (Nat.mod_lt _ (B256.toNat_pos h)) (B256.toNat_lt z))

theorem B256.toNat_addmod {x y z : B256} (h : z ≠ 0) :
    (B256.addmod x y z).toNat = (x.toNat + y.toNat) % z.toNat := by
  rw [B256.addmod, if_neg h]
  exact B256.toNat_toB256_of_lt
    (Nat.lt_trans (Nat.mod_lt _ (B256.toNat_pos h)) (B256.toNat_lt z))

/-! ## A1 — the defining bounds of floor and ceiling division -/

/-- The floor bound: the quotient, scaled back up, never exceeds the dividend. -/
theorem Nat.mul_div_mul_le (a b d : Nat) : d * (a * b / d) ≤ a * b :=
  Nat.mul_div_le (a * b) d

/-- The complementary strict bound: one more quantum overshoots. -/
theorem Nat.lt_mul_div_add_one {d : Nat} (hd : d ≠ 0) (a b : Nat) :
    a * b < d * (a * b / d + 1) := by
  have h := Nat.lt_div_mul_add (a := a * b) (b := d) (Nat.pos_of_ne_zero hd)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm d (a * b / d)]
  exact h

/-- Ceiling division agrees with the `(n + d - 1) / d` spelling. -/
theorem Nat.ceilDiv_eq_add_pred_div {d : Nat} (hd : d ≠ 0) (n : Nat) :
    ceilDiv n d = (n + d - 1) / d := by
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  have hlt : n % d < d := Nat.mod_lt _ hd'
  have hsub : n + d - 1 = n + (d - 1) := by omega
  have hmod : (d - 1) % d = d - 1 := Nat.mod_eq_of_lt (by omega)
  have hdiv : (d - 1) / d = 0 := Nat.div_eq_of_lt (by omega)
  rw [hsub, Nat.add_div hd', hmod, hdiv, ceilDiv, Nat.add_zero]
  rcases Nat.eq_zero_or_pos (n % d) with h | h
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg (by omega), if_pos (by omega)]

/-- Ceiling division agrees with "floor, plus one unless the division is exact". -/
theorem Nat.ceilDiv_eq_div_add_ite (n d : Nat) :
    ceilDiv n d = n / d + if d ∣ n then 0 else 1 := by
  rw [ceilDiv]
  congr 1
  simp only [Nat.dvd_iff_mod_eq_zero]

/-- The ceiling bound: the ceiling quotient, scaled back up, covers the dividend. -/
theorem Nat.le_mul_ceilDiv {d : Nat} (hd : d ≠ 0) (n : Nat) :
    n ≤ d * ceilDiv n d := by
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  have h := Nat.div_add_mod n d
  rw [ceilDiv, Nat.mul_add]
  rcases Nat.eq_zero_or_pos (n % d) with hm | hm
  · rw [if_pos hm, Nat.mul_zero, Nat.add_zero]; omega
  · rw [if_neg (by omega), Nat.mul_one]
    have := Nat.mod_lt n hd'
    omega

/-- The complementary ceiling bound: it overshoots by less than one quantum. -/
theorem Nat.mul_ceilDiv_lt {d : Nat} (hd : d ≠ 0) (n : Nat) :
    d * ceilDiv n d < n + d := by
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  have h := Nat.div_add_mod n d
  have := Nat.mod_lt n hd'
  rw [ceilDiv, Nat.mul_add]
  rcases Nat.eq_zero_or_pos (n % d) with hm | hm
  · rw [if_pos hm, Nat.mul_zero, Nat.add_zero]; omega
  · rw [if_neg (by omega), Nat.mul_one]; omega

/-- Exactness of the floor division is exactly divisibility. -/
theorem Nat.mul_div_mul_eq_iff_dvd (a b d : Nat) :
    a * b / d * d = a * b ↔ d ∣ a * b :=
  (Nat.dvd_iff_div_mul_eq (a * b) d).symm

/-- The ceiling division's Galois connection: the workhorse for the ceil side. -/
theorem Nat.ceilDiv_le_iff_le_mul {d : Nat} (hd : d ≠ 0) (n k : Nat) :
    ceilDiv n d ≤ k ↔ n ≤ k * d := by
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  rw [Nat.ceilDiv_eq_add_pred_div hd, Nat.div_le_iff_le_mul_add_pred hd',
    Nat.mul_comm k d]
  omega

/-! ## A2 — which way each division rounds, and the degenerate cases -/

/-- The floor never exceeds the ceiling. -/
theorem Nat.div_le_ceilDiv (n d : Nat) : n / d ≤ ceilDiv n d := by
  rw [ceilDiv]; exact Nat.le_add_right _ _

/-- Floor and ceiling agree exactly when the division is exact. -/
theorem Nat.div_eq_ceilDiv_iff_dvd (n d : Nat) :
    n / d = ceilDiv n d ↔ d ∣ n := by
  rw [ceilDiv, Nat.dvd_iff_mod_eq_zero]
  rcases Nat.eq_zero_or_pos (n % d) with h | h
  · rw [if_pos h]; omega
  · rw [if_neg (by omega)]; omega

/-- Dividing by the scale you multiplied by is exact. -/
theorem Nat.mul_div_self_eq {d : Nat} (hd : d ≠ 0) (a : Nat) : a * d / d = a :=
  Nat.mul_div_cancel a (Nat.pos_of_ne_zero hd)

theorem Nat.zero_mul_div (b d : Nat) : 0 * b / d = 0 := by
  rw [Nat.zero_mul, Nat.zero_div]

theorem Nat.ceilDiv_zero (d : Nat) : ceilDiv 0 d = 0 := by
  rw [ceilDiv, Nat.zero_div, Nat.zero_mod, if_pos rfl]

/-- Jaune's `ceilDiv` at a zero divisor: characterized here so that no proof
has to rely on it silently. It is `1` on every positive dividend, which is not
a junk-value convention and must never be read as one. -/
theorem Nat.ceilDiv_zero_right (n : Nat) :
    ceilDiv n 0 = if n = 0 then 0 else 1 := by
  rw [ceilDiv, Nat.div_zero, Nat.mod_zero, Nat.zero_add]

/-! ## A3 — monotonicity -/

theorem Nat.mul_div_le_mul_div_left {a a' : Nat} (h : a ≤ a') (b d : Nat) :
    a * b / d ≤ a' * b / d :=
  Nat.div_le_div_right (Nat.mul_le_mul_right b h)

theorem Nat.mul_div_le_mul_div_right {b b' : Nat} (h : b ≤ b') (a d : Nat) :
    a * b / d ≤ a * b' / d :=
  Nat.div_le_div_right (Nat.mul_le_mul_left a h)

/-- Antitone in the denominator: a larger scale divides to no more. -/
theorem Nat.mul_div_le_mul_div_of_le_denom {d d' : Nat} (h : d' ≤ d) (hd' : d' ≠ 0)
    (a b : Nat) : a * b / d ≤ a * b / d' :=
  Nat.div_le_div_left h (Nat.pos_of_ne_zero hd')

theorem Nat.ceilDiv_le_ceilDiv_left {n n' : Nat} (h : n ≤ n') {d : Nat} (hd : d ≠ 0) :
    ceilDiv n d ≤ ceilDiv n' d := by
  rw [Nat.ceilDiv_le_iff_le_mul hd]
  exact Nat.le_trans h (Nat.le_mul_ceilDiv hd n' |>.trans (Nat.le_of_eq (Nat.mul_comm _ _)))

theorem Nat.mul_ceilDiv_le_mul_ceilDiv_left {a a' : Nat} (h : a ≤ a') (b : Nat)
    {d : Nat} (hd : d ≠ 0) : ceilDiv (a * b) d ≤ ceilDiv (a' * b) d :=
  Nat.ceilDiv_le_ceilDiv_left (Nat.mul_le_mul_right b h) hd

/-- Antitone in the denominator on the ceiling side too. -/
theorem Nat.ceilDiv_le_ceilDiv_of_le_denom {d d' : Nat} (h : d' ≤ d) (hd' : d' ≠ 0)
    (n : Nat) : ceilDiv n d ≤ ceilDiv n d' := by
  have hd : d ≠ 0 := by omega
  rw [Nat.ceilDiv_le_iff_le_mul hd]
  exact Nat.le_trans (Nat.le_mul_ceilDiv hd' n)
    (Nat.le_of_eq (Nat.mul_comm _ _) |>.trans (Nat.mul_le_mul_left _ h))

/-! ## A4 — what a division/multiplication round trip loses -/

/-- A round trip through a ratio never gains: the residue always favours the
side holding the rounding. -/
theorem Nat.mul_div_mul_div_le {p : Nat} (hp : p ≠ 0) (x q : Nat) :
    x * p / q * q / p ≤ x :=
  calc x * p / q * q / p ≤ x * p / p := Nat.div_le_div_right (Nat.div_mul_le_self _ _)
    _ = x := Nat.mul_div_self_eq hp x

/-- The exact round-trip loss: it is the first division's residue, rounded up
through the second divisor. Nothing here is an estimate. -/
theorem Nat.le_mul_div_mul_div_add {p : Nat} (hp : p ≠ 0) (x q : Nat) :
    x ≤ x * p / q * q / p + ceilDiv (x * p % q) p := by
  have hp' : 0 < p := Nat.pos_of_ne_zero hp
  have hsplit : x * p / q * q = x * p - x * p % q := by
    have := Nat.div_add_mod' (x * p) q
    omega
  have hcover : x * p % q ≤ ceilDiv (x * p % q) p * p := by
    have h := Nat.le_mul_ceilDiv hp (x * p % q)
    rw [Nat.mul_comm p (ceilDiv (x * p % q) p)] at h
    exact h
  have key : (x - ceilDiv (x * p % q) p) * p ≤ x * p / q * q := by
    rw [Nat.sub_mul, hsplit]
    exact Nat.sub_le_sub_left hcover _
  have := (Nat.le_div_iff_mul_le hp').mpr key
  omega

/-- The round-trip loss bounded by one price quantum, uniformly in the amount. -/
theorem Nat.sub_mul_div_mul_div_le {p q : Nat} (hp : p ≠ 0) (hq : q ≠ 0) (x : Nat) :
    x - x * p / q * q / p ≤ ceilDiv (q - 1) p := by
  have h := Nat.le_mul_div_mul_div_add hp x q
  have hr : x * p % q ≤ q - 1 := by
    have := Nat.mod_lt (x * p) (Nat.pos_of_ne_zero hq)
    omega
  have := Nat.ceilDiv_le_ceilDiv_left hr hp
  omega

/-- The mixed form the withdraw path needs: rounding the first conversion up
makes the round trip cover the original amount rather than fall short of it. -/
theorem Nat.le_ceilDiv_mul_div {p q : Nat} (hp : p ≠ 0) (hq : q ≠ 0) (x : Nat) :
    x ≤ ceilDiv (x * p) q * q / p := by
  have hcover : x * p ≤ ceilDiv (x * p) q * q := by
    have h := Nat.le_mul_ceilDiv hq (x * p)
    rw [Nat.mul_comm q (ceilDiv (x * p) q)] at h
    exact h
  calc x = x * p / p := (Nat.mul_div_self_eq hp x).symm
    _ ≤ ceilDiv (x * p) q * q / p := Nat.div_le_div_right hcover

/-! ## A5 — how a division reacts to a perturbed denominator or numerator -/

/-- Adding to the denominator can only shrink the quotient: the donation lever. -/
theorem Nat.mul_div_add_denom_le {d : Nat} (hd : d ≠ 0) (a b e : Nat) :
    a * b / (d + e) ≤ a * b / d :=
  Nat.div_le_div_left (Nat.le_add_right d e) (Nat.pos_of_ne_zero hd)

/-- How much a denominator perturbation can cost, quantitatively: the exact
real-valued difference `n * e / (d * (d + e))`, plus the one unit that two
independent floors can hide. -/
theorem Nat.div_le_div_add_denom_add {d : Nat} (hd : d ≠ 0) (n e : Nat) :
    n / d ≤ n / (d + e) + n * e / (d * (d + e)) + 1 := by
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  have hde : 0 < d + e := by omega
  have hL : n / d = n * (d + e) / (d * (d + e)) := by
    rw [Nat.mul_comm d (d + e), Nat.mul_comm n (d + e),
      Nat.mul_div_mul_left _ _ hde]
  have hR : n / (d + e) = n * d / (d * (d + e)) := by
    rw [Nat.mul_comm n d, Nat.mul_div_mul_left _ _ hd']
  rw [hL, hR, Nat.mul_add n d e, Nat.add_div (Nat.mul_pos hd' hde)]
  split <;> omega

/-- Numerator shift, in the same shape. -/
theorem Nat.add_div_le_div_add_div {d : Nat} (hd : d ≠ 0) (n e : Nat) :
    (n + e) / d ≤ n / d + e / d + 1 := by
  rw [Nat.add_div (Nat.pos_of_ne_zero hd)]
  split <;> omega

/-- A conversion returns nothing exactly when the scaled amount is below the
scale: the arithmetic core of what an inflation attack has to achieve. -/
theorem Nat.mul_div_eq_zero_iff {d : Nat} (hd : d ≠ 0) (a b : Nat) :
    a * b / d = 0 ↔ a * b < d := by
  rw [Nat.div_eq_zero_iff]
  omega

/-- The virtual offset's guarantee: whatever the numerator's own term has been
driven to, a nonzero offset floors the conversion at the unoffset quotient. -/
theorem Nat.le_mul_add_div_add {o : Nat} (ho : o ≠ 0) (x s t : Nat) :
    x / (t + o) ≤ x * (s + o) / (t + o) := by
  apply Nat.div_le_div_right
  calc x = x * 1 := (Nat.mul_one x).symm
    _ ≤ x * (s + o) := Nat.mul_le_mul_left x (by omega)

/-- The donation lever in the offset-compensated shape the defense composes in. -/
theorem Nat.mul_add_div_add_le {o : Nat} (ho : o ≠ 0) (x s t e : Nat) :
    x * (s + o) / (t + e + o) ≤ x * (s + o) / (t + o) :=
  Nat.div_le_div_left (by omega) (by omega)

/-! ## The word-level connective -/

/-- The bridge the compiled code actually crosses: a `mulDiv` at word level is
the `Nat`-level one, provided the product does not wrap. -/
theorem B256.toNat_mul_div_of_nofm {x y z : B256} (h : B256.Nofm x y) (hz : z ≠ 0) :
    (x * y / z).toNat = x.toNat * y.toNat / z.toNat := by
  rw [B256.toNat_div hz, B256.toNat_mul_eq_of_nofm h]

end Jaune
