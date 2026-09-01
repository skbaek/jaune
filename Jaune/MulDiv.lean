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
constant appears anywhere. A division whose `d = 0` case would change the
meaning carries an explicit `d ≠ 0`; the rest are the ones true on both
branches, and Jaune's `ceilDiv` at a zero divisor — which is `1`, not
`0`, on a positive dividend — is characterized outright at
`ceilDiv_zero_divisor` so that no proof relies on it silently.

The word-level section bridges to `B256`. Those statements are either explicit
about the `% 2 ^ 256` truncation or carry a no-overflow hypothesis; none of
them states an unconditional word equality that hides wraparound.

Names follow the house convention, including Lean core's rule that a
monotonicity lemma is named after the argument held **fixed**: varying the left
factor of `a * b / d` gives `Nat.mul_div_le_mul_div_right`, matching
`Nat.div_le_div_right`. The `ceilDiv` lemmas sit in the plain `Jaune` namespace
rather than under `Nat`, because Jaune's `ceilDiv` is its own function and
Mathlib's `Nat.ceilDiv_eq_add_pred_div`, `ceilDiv_zero` and
`ceilDiv_le_iff_le_mul` name different statements about a different one.
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

/-- The discharge route for the multiplication guard: the check compiled code
actually performs, against the largest representable word. -/
theorem B256.nofm_iff_le_div {y : B256} (hy : y ≠ 0) (x : B256) :
    B256.Nofm x y ↔ x.toNat ≤ (2 ^ 256 - 1) / y.toNat := by
  have hpos : 0 < 2 ^ 256 := Nat.two_pow_pos 256
  rw [B256.Nofm, Nat.le_div_iff_mul_le (B256.toNat_pos hy)]
  omega

/-- The full-width product, truncated: the multiplication a word actually does.
This is the `%`-spelling of the existing `B256.toNat_mul`, whose `↾ 256` is the
same function; it is stated here because the `Nat` lemmas below are written
with `%`. -/
theorem B256.toNat_mul_mod (x y : B256) :
    (x * y).toNat = x.toNat * y.toNat % 2 ^ 256 :=
  B256.toNat_mul x y

/-- The untruncated product, available exactly when it does not overflow. -/
theorem B256.toNat_mul_eq_of_nofm {x y : B256} (h : B256.Nofm x y) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [B256.toNat_mul, Nat.lo_eq_of_lt h]

/-- The `div` half of the div/mod pair. The `mod` half is the pre-existing
`B256.toNat_mod`. Neither truncates: both results are bounded by an operand. -/
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
theorem ceilDiv_eq_add_sub_one_div {d : Nat} (hd : d ≠ 0) (n : Nat) :
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
theorem ceilDiv_eq_div_add_ite (n d : Nat) :
    ceilDiv n d = n / d + if d ∣ n then 0 else 1 := by
  rw [ceilDiv]
  congr 1
  simp only [Nat.dvd_iff_mod_eq_zero]

/-- The ceiling bound: the ceiling quotient, scaled back up, covers the dividend. -/
theorem le_ceilDiv_mul {d : Nat} (hd : d ≠ 0) (n : Nat) : n ≤ ceilDiv n d * d := by
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  have h := Nat.div_add_mod' n d
  have hlt := Nat.mod_lt n hd'
  rw [ceilDiv, Nat.add_mul]
  rcases Nat.eq_zero_or_pos (n % d) with hm | hm
  · rw [if_pos hm, Nat.zero_mul, Nat.add_zero]; omega
  · rw [if_neg (by omega), Nat.one_mul]; omega

/-- The complementary ceiling bound: it overshoots by less than one quantum. -/
theorem ceilDiv_mul_lt {d : Nat} (hd : d ≠ 0) (n : Nat) : ceilDiv n d * d < n + d := by
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  have h := Nat.div_add_mod' n d
  have hlt := Nat.mod_lt n hd'
  rw [ceilDiv, Nat.add_mul]
  rcases Nat.eq_zero_or_pos (n % d) with hm | hm
  · rw [if_pos hm, Nat.zero_mul, Nat.add_zero]; omega
  · rw [if_neg (by omega), Nat.one_mul]; omega

/-- Exactness of the floor division is exactly divisibility. -/
theorem Nat.mul_div_mul_eq_iff_dvd (a b d : Nat) :
    a * b / d * d = a * b ↔ d ∣ a * b :=
  (Nat.dvd_iff_div_mul_eq (a * b) d).symm

/-- The ceiling division's Galois connection: the workhorse for the ceil side. -/
theorem ceilDiv_le_iff {d : Nat} (hd : d ≠ 0) (n k : Nat) :
    ceilDiv n d ≤ k ↔ n ≤ k * d := by
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  rw [ceilDiv_eq_add_sub_one_div hd, Nat.div_le_iff_le_mul_add_pred hd',
    Nat.mul_comm k d]
  omega

/-- A ceiling division that is exact returns the multiplier unchanged. -/
theorem ceilDiv_mul_self {d : Nat} (hd : d ≠ 0) (x : Nat) : ceilDiv (x * d) d = x := by
  have hmod : x * d % d = 0 := Nat.dvd_iff_mod_eq_zero.mp ⟨x, Nat.mul_comm x d⟩
  rw [ceilDiv, hmod, if_pos rfl, Nat.add_zero,
    Nat.mul_div_cancel x (Nat.pos_of_ne_zero hd)]

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

theorem ceilDiv_zero_dividend (d : Nat) : ceilDiv 0 d = 0 := by
  rw [ceilDiv, Nat.zero_div, Nat.zero_mod, if_pos rfl]

/-- Jaune's `ceilDiv` at a zero divisor, characterized here so that no proof has
to rely on it silently. It is `1` on every positive dividend, which is not a
junk-value convention and must never be read as one. -/
theorem ceilDiv_zero_divisor (n : Nat) :
    ceilDiv n 0 = if n = 0 then 0 else 1 := by
  rw [ceilDiv, Nat.div_zero, Nat.mod_zero, Nat.zero_add]

/-! ## A3 — monotonicity

Named after the argument held fixed, as Lean core does. -/

theorem Nat.mul_div_le_mul_div_right {a a' : Nat} (h : a ≤ a') (b d : Nat) :
    a * b / d ≤ a' * b / d :=
  Nat.div_le_div_right (Nat.mul_le_mul_right b h)

theorem Nat.mul_div_le_mul_div_left {b b' : Nat} (h : b ≤ b') (a d : Nat) :
    a * b / d ≤ a * b' / d :=
  Nat.div_le_div_right (Nat.mul_le_mul_left a h)

/-- Antitone in the denominator: a larger scale divides to no more. -/
theorem Nat.mul_div_le_mul_div_of_le_denom {d d' : Nat} (h : d' ≤ d) (hd' : d' ≠ 0)
    (a b : Nat) : a * b / d ≤ a * b / d' :=
  Nat.div_le_div_left h (Nat.pos_of_ne_zero hd')

theorem ceilDiv_le_ceilDiv_right {n n' : Nat} (h : n ≤ n') {d : Nat} (hd : d ≠ 0) :
    ceilDiv n d ≤ ceilDiv n' d := by
  rw [ceilDiv_le_iff hd]
  exact Nat.le_trans h (le_ceilDiv_mul hd n')

theorem ceilDiv_mul_le_ceilDiv_mul_right {a a' : Nat} (h : a ≤ a') (b : Nat)
    {d : Nat} (hd : d ≠ 0) : ceilDiv (a * b) d ≤ ceilDiv (a' * b) d :=
  ceilDiv_le_ceilDiv_right (Nat.mul_le_mul_right b h) hd

theorem ceilDiv_mul_le_ceilDiv_mul_left {b b' : Nat} (h : b ≤ b') (a : Nat)
    {d : Nat} (hd : d ≠ 0) : ceilDiv (a * b) d ≤ ceilDiv (a * b') d :=
  ceilDiv_le_ceilDiv_right (Nat.mul_le_mul_left a h) hd

/-- Antitone in the denominator on the ceiling side too. -/
theorem ceilDiv_le_ceilDiv_of_le_denom {d d' : Nat} (h : d' ≤ d) (hd' : d' ≠ 0)
    (n : Nat) : ceilDiv n d ≤ ceilDiv n d' := by
  have hd : d ≠ 0 := by omega
  rw [ceilDiv_le_iff hd]
  exact Nat.le_trans (le_ceilDiv_mul hd' n) (Nat.mul_le_mul_left _ h)

/-! ## A4 — what a division/multiplication round trip loses -/

/-- The round-trip loss, **exactly**: it is the first division's residue,
rounded up through the second divisor. Nothing here is an estimate, and the
equality is what a cumulative dust invariant needs in order to induct. -/
theorem Nat.mul_div_mul_div_add_ceilDiv {p : Nat} (hp : p ≠ 0) (x q : Nat) :
    x * p / q * q / p + ceilDiv (x * p % q) p = x := by
  have hp' : 0 < p := Nat.pos_of_ne_zero hp
  have hsplit : x * p / q * q = x * p - x * p % q := by
    have := Nat.div_add_mod' (x * p) q
    omega
  have hrle : x * p % q ≤ x * p := Nat.mod_le _ _
  have hcx : ceilDiv (x * p % q) p ≤ x := by
    have h1 := ceilDiv_le_ceilDiv_right hrle hp
    rwa [ceilDiv_mul_self hp x] at h1
  have hcp : ceilDiv (x * p % q) p * p ≤ x * p := Nat.mul_le_mul_right p hcx
  have hcover : x * p % q ≤ ceilDiv (x * p % q) p * p := le_ceilDiv_mul hp _
  have hlt : ceilDiv (x * p % q) p * p < x * p % q + p := ceilDiv_mul_lt hp _
  have hlow : x - ceilDiv (x * p % q) p ≤ x * p / q * q / p := by
    rw [hsplit]
    refine (Nat.le_div_iff_mul_le hp').mpr ?_
    rw [Nat.sub_mul]
    exact Nat.sub_le_sub_left hcover _
  have hhigh : x * p / q * q / p ≤ x - ceilDiv (x * p % q) p := by
    rw [hsplit]
    refine (Nat.div_le_iff_le_mul_add_pred hp').mpr ?_
    have hexp : p * (x - ceilDiv (x * p % q) p) = x * p - ceilDiv (x * p % q) p * p := by
      rw [Nat.mul_comm p (x - ceilDiv (x * p % q) p), Nat.sub_mul]
    rw [hexp]
    omega
  omega

/-- A round trip through a ratio never gains: the residue always favours the
side holding the rounding. -/
theorem Nat.mul_div_mul_div_le {p : Nat} (hp : p ≠ 0) (x q : Nat) :
    x * p / q * q / p ≤ x := by
  have := Nat.mul_div_mul_div_add_ceilDiv hp x q
  omega

/-- The round-trip loss bounded by one price quantum, uniformly in the amount. -/
theorem Nat.sub_mul_div_mul_div_le {p q : Nat} (hp : p ≠ 0) (hq : q ≠ 0) (x : Nat) :
    x - x * p / q * q / p ≤ ceilDiv (q - 1) p := by
  have h := Nat.mul_div_mul_div_add_ceilDiv hp x q
  have hr : x * p % q ≤ q - 1 := by
    have := Nat.mod_lt (x * p) (Nat.pos_of_ne_zero hq)
    omega
  have := ceilDiv_le_ceilDiv_right hr hp
  omega

/-- The mixed form the withdraw path needs: rounding the first conversion up
makes the round trip cover the original amount rather than fall short of it. -/
theorem Nat.le_ceilDiv_mul_div {p q : Nat} (hp : p ≠ 0) (hq : q ≠ 0) (x : Nat) :
    x ≤ ceilDiv (x * p) q * q / p := by
  calc x = x * p / p := (Nat.mul_div_self_eq hp x).symm
    _ ≤ ceilDiv (x * p) q * q / p := Nat.div_le_div_right (le_ceilDiv_mul hq (x * p))

/-- The other mixed form: rounding the second conversion up still cannot gain,
because the first one already rounded down. -/
theorem ceilDiv_mul_div_mul_le {p : Nat} (hp : p ≠ 0) (x q : Nat) :
    ceilDiv (x * p / q * q) p ≤ x := by
  calc ceilDiv (x * p / q * q) p
      ≤ ceilDiv (x * p) p := ceilDiv_le_ceilDiv_right (Nat.div_mul_le_self _ _) hp
    _ = x := ceilDiv_mul_self hp x

/-! ## A5 — how a division reacts to a perturbed denominator or numerator -/

/-- Adding to the denominator can only shrink the quotient: the donation lever. -/
theorem Nat.mul_div_add_denom_le {d : Nat} (hd : d ≠ 0) (a b e : Nat) :
    a * b / (d + e) ≤ a * b / d :=
  Nat.div_le_div_left (Nat.le_add_right d e) (Nat.pos_of_ne_zero hd)

/-- How much a denominator perturbation can cost, from above: the exact
real-valued difference `n * e / (d * (d + e))`, plus the one unit that two
independent floors can hide. The `+ 1` is necessary. -/
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

/-- The same perturbation from below, making the pair two-sided. -/
theorem Nat.div_add_denom_add_le_div {d : Nat} (hd : d ≠ 0) (n e : Nat) :
    n / (d + e) + n * e / (d * (d + e)) ≤ n / d := by
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  have hde : 0 < d + e := by omega
  have hL : n / d = n * (d + e) / (d * (d + e)) := by
    rw [Nat.mul_comm d (d + e), Nat.mul_comm n (d + e),
      Nat.mul_div_mul_left _ _ hde]
  have hR : n / (d + e) = n * d / (d * (d + e)) := by
    rw [Nat.mul_comm n d, Nat.mul_div_mul_left _ _ hd']
  rw [hL, hR, Nat.mul_add n d e]
  exact Nat.div_add_div_le_add_div

/-- Numerator shift. The `+ 1` is necessary: the statement without it is false. -/
theorem Nat.add_div_le_div_add_div_add_one {d : Nat} (hd : d ≠ 0) (n e : Nat) :
    (n + e) / d ≤ n / d + e / d + 1 := by
  rw [Nat.add_div (Nat.pos_of_ne_zero hd)]
  split <;> omega

/-- A conversion returns nothing exactly when the scaled amount is below the
scale: the arithmetic core of what an inflation attack has to achieve. -/
theorem Nat.mul_div_eq_zero_iff {d : Nat} (hd : d ≠ 0) (a b : Nat) :
    a * b / d = 0 ↔ a * b < d := by
  rw [Nat.div_eq_zero_iff]
  omega

/-- The virtual offset's guarantee, stated as the price of defeating it: to
round a party of size `x` down to nothing, the denominator must first have been
driven to at least `x` times the offset. The offset is therefore a
multiplicative floor on the attacker's outlay, and it is parametric — no
particular offset size is assumed. -/
theorem Nat.mul_le_of_mul_add_div_add_eq_zero {o : Nat} (ho : o ≠ 0) {x s t : Nat}
    (h : x * (s + o) / (t + o) = 0) : x * o ≤ t + o := by
  have hto : t + o ≠ 0 := by omega
  have hlt : x * (s + o) < t + o := (Nat.mul_div_eq_zero_iff hto x (s + o)).mp h
  have : x * o ≤ x * (s + o) := Nat.mul_le_mul_left x (by omega)
  omega

/-- With a nonzero offset the numerator's own term can never drag a conversion
below the unoffset quotient: monotonicity in the numerator, in the shape the
offset defense composes in. -/
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
the `Nat`-level one, provided the product does not wrap. The quotient itself
cannot overflow, so `Nofm` is the only guard needed. -/
theorem B256.toNat_mul_div_of_nofm {x y z : B256} (h : B256.Nofm x y) (hz : z ≠ 0) :
    (x * y / z).toNat = x.toNat * y.toNat / z.toNat := by
  rw [B256.toNat_div hz, B256.toNat_mul_eq_of_nofm h]

/-! ## Cross-denominator comparison -/

/-- Cross-multiplication is a sufficient comparison principle for two floor
quotients with nonzero denominators. -/
theorem Nat.div_le_div_of_cross {n₁ n₂ d₁ d₂ : Nat}
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hcross : n₁ * d₂ ≤ n₂ * d₁) : n₁ / d₁ ≤ n₂ / d₂ := by
  apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd₂)).2
  apply Nat.le_of_mul_le_mul_right (c := d₁) _ (Nat.pos_of_ne_zero hd₁)
  calc
    (n₁ / d₁ * d₂) * d₁ = (n₁ / d₁ * d₁) * d₂ := by ac_rfl
    _ ≤ n₁ * d₂ := Nat.mul_le_mul_right d₂ (Nat.div_mul_le_self n₁ d₁)
    _ ≤ n₂ * d₁ := hcross

end Jaune
