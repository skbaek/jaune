-- A faster final exponentiation for the BLS12-381 pairing, consensus side.
--
-- Jaune's `blsMillerLoop` raises the Miller-loop value to `(p^12 - 1) / r` by
-- square-and-multiply over the whole 4,314-bit exponent: about 94% of a pairing
-- (measured 2026-11-09 on the WSL host, compiled: 856 ms pairing, 804 ms of it the
-- final exponentiation). This module computes the same power with the standard
-- split `(p^12 - 1) / r = (p^6 - 1) * (p^2 + 1) * h`, `h = (p^4 - p^2 + 1) / r`:
--
-- * the easy part `f^((p^6 - 1)(p^2 + 1))` costs Frobenius maps, one inversion
--   and two multiplications;
-- * the hard part writes `h` in base `p`, `h = l0 + l1 p + l2 p^2 + l3 p^3`, and
--   evaluates `prod_i (frob^i g)^(l_i)` as one simultaneous (Straus) exponentiation
--   over 4 bases with digits below `p` (381 bits), with a 16-entry table.
--
-- The Frobenius `x ↦ x^p` on `Fp12 = Fp[w] / (w^12 - 2 w^6 + 2)` is linear over
-- `Fp` and fixes `Fp`, so `(sum c_i w^i)^p = sum c_i (w^p)^i`: twelve `Fp`-scalar
-- multiples of the precomputed powers of `w^p`.
--
-- The exponent identities are kernel-checked theorems below. That `frob x = x^p`
-- and that the whole function agrees with `x ^ blsFinalExponent` is checked by
-- differential `#guard`s in FinalExpVectors.lean (Miller-loop values of several
-- point pairs), not proved: Jaune's `GaloisField` carries no field-theory lemmas.
-- `Jaune/BLS.lean` is not changed.

import Jaune.BLS

namespace JauneConsensus

open Jaune

/-- The reduced pairing's final exponent `(p^12 - 1) / r`, as Jaune's
`blsMillerLoop` and `verifyKzgProofImpl` apply it. -/
def blsFinalExponent : Nat := (blsPrime ^ 12 - 1) / blsCurveOrder

/-- `h = (p^4 - p^2 + 1) / r`, the hard part of the final exponent. -/
def blsHardExponent : Nat := (blsPrime ^ 4 - blsPrime ^ 2 + 1) / blsCurveOrder

theorem blsHardExponent_exact :
    blsHardExponent * blsCurveOrder = blsPrime ^ 4 - blsPrime ^ 2 + 1 := by decide

theorem blsFinalExponent_split :
    blsFinalExponent = (blsPrime ^ 6 - 1) * (blsPrime ^ 2 + 1) * blsHardExponent := by
  decide

/-- The base-`p` digits of `h`, low first. -/
def blsHardDigits : List Nat :=
  [blsHardExponent % blsPrime, blsHardExponent / blsPrime % blsPrime,
   blsHardExponent / blsPrime ^ 2 % blsPrime, blsHardExponent / blsPrime ^ 3]

theorem blsHardDigits_sum :
    (blsHardDigits.zipIdx.map fun (d, i) => d * blsPrime ^ i).sum = blsHardExponent := by
  decide

theorem blsHardDigits_lt : ∀ d ∈ blsHardDigits, d < blsPrime := by decide

/-- The coefficients `c_0, ..., c_11` of `sum c_i w^i`, low degree first. -/
def f12Coeffs (x : BLSF12) : List BLSF :=
  (List.takeRightV 12 x.val (0 : BLSF)).toList.reverse

/-- `c * x` for `c` in `Fp`. -/
def f12Scale (c : BLSF) (x : BLSF12) : BLSF12 :=
  if c = 0 then 0 else ⟨x.val.map (c * ·)⟩

/-- `w^p`, and its powers `(w^p)^i` for `i < 12`. -/
def blsFrobW : BLSF12 := (⟨[1, 0]⟩ : BLSF12) ^ blsPrime

def blsFrobWPowers : List BLSF12 :=
  (List.range 12).map fun i => blsFrobW ^ i

/-- The Frobenius `x ↦ x^p` on `Fp12`. -/
def f12Frob (x : BLSF12) : BLSF12 :=
  ((f12Coeffs x).zip blsFrobWPowers).foldl (fun acc (c, g) => acc + f12Scale c g) 0

/-- `frob^k`. -/
def f12FrobN : Nat → BLSF12 → BLSF12
  | 0, x => x
  | k + 1, x => f12FrobN k (f12Frob x)

/-- Simultaneous exponentiation `prod_i b_i ^ e_i` for four bases (Straus, 16-entry
table indexed by the bits of the four exponents at one position). -/
def f12MultiPow4 (b0 b1 b2 b3 : BLSF12) (e0 e1 e2 e3 : Nat) : BLSF12 :=
  -- table[j] = prod over set bits k of j of b_k
  let table : Array BLSF12 := (List.range 16).toArray.map fun j =>
    (if j.testBit 0 then b0 else 1) * (if j.testBit 1 then b1 else 1) *
    (if j.testBit 2 then b2 else 1) * (if j.testBit 3 then b3 else 1)
  let n := max (max e0.log2 e1.log2) (max e2.log2 e3.log2) + 1
  (List.range n).reverse.foldl (fun acc i =>
    let j := (if e0.testBit i then 1 else 0) + (if e1.testBit i then 2 else 0) +
             (if e2.testBit i then 4 else 0) + (if e3.testBit i then 8 else 0)
    let sq := acc * acc
    match table[j]? with
    | some t => if j = 0 then sq else sq * t
    | none => sq) 1   -- unreachable: j < 16

/-- `f ^ ((p^12 - 1) / r)` by the easy/hard split. -/
def blsFinalExpFast (f : BLSF12) : BLSF12 :=
  -- easy part: g = (f^(p^6) / f)^(p^2 + 1)
  let t := f12FrobN 6 f / f
  let g := f12FrobN 2 t * t
  -- hard part: g^h = prod_i (frob^i g)^(l_i)
  match blsHardDigits with
  | [l0, l1, l2, l3] =>
    f12MultiPow4 g (f12Frob g) (f12FrobN 2 g) (f12FrobN 3 g) l0 l1 l2 l3
  | _ => g ^ blsHardExponent   -- unreachable: `blsHardDigits` has four entries

/-- Pairing-product check with the plain final power, the shape of Jaune's
`verifyKzgProofImpl`: the reference `pairingCheck` is checked against. -/
def pairingCheckRef (pairs : List (BLSP × BLSP2)) : Bool :=
  let loops := pairs.mapM fun (p, q) => blsPairing q p (finalExp := false)
  match loops with
  | some fs => fs.foldl (· * ·) (1 : BLSF12) ^ blsFinalExponent = 1
  | none => false

end JauneConsensus
