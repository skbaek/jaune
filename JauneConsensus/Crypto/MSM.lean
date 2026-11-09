-- Multi-scalar multiplication in G1 (the `multi_exp` behind `g1_lincomb`,
-- specs/deneb/polynomial-commitments.md).
--
-- `g1MsmSum` (Jaune/BLS.lean) is the naive sum of scalar multiples and stays the
-- reference. `g1Msm` is the bucket (Pippenger) method over Jaune's Jacobian
-- arithmetic (`EllipticCurve.Jacobian` in Jaune/EC.lean: `double`, `add`,
-- `mixedAdd`, one normalisation at the end). The two agree on the differential
-- checks in MSMVectors.lean; no equality theorem is claimed.

import Jaune.BLS

namespace JauneConsensus

open Jaune

/-- Subtraction in `Fp` on reduced values without the `Int` round trip of Jaune's
`FinField.sub`: `(x + p - y) % p`. Equal to `FinField.sub` whenever `y ≤ p`
(`fpSubFast_eq`), which holds for every value the field operations produce. -/
def fpSubFast (x y : BLSF) : BLSF := ⟨(x.val + blsPrime - y.val) % blsPrime⟩

theorem fpSubFast_eq (x y : BLSF) (hy : y.val ≤ blsPrime) : fpSubFast x y = x - y := by
  show fpSubFast x y = FinField.sub x y
  unfold fpSubFast FinField.sub
  congr 1
  have h : ((x.val + blsPrime - y.val : Nat) : Int) = (x.val : Int) - y.val + blsPrime := by
    omega
  have h2 : ((x.val : Int) - y.val) % (blsPrime : Int)
      = (((x.val + blsPrime - y.val) % blsPrime : Nat) : Int) := by
    rw [Int.natCast_mod, h, Int.add_emod_right]
  show _ = Int.natAbs (((x.val : Int) - y.val) % (blsPrime : Int))
  rw [h2, Int.natAbs_natCast]

/-- The G1 arithmetic in this module (Jaune's generic Jacobian formulas) is
instantiated with `fpSubFast`; `fpSubFast_eq` says this changes no result on reduced
inputs, and the MSM guards compare against Jaune's `g1MsmSum`, which uses
`FinField.sub`. -/
local instance (priority := high) fpSubFastInst : HSub BLSF BLSF BLSF := ⟨fpSubFast⟩

/-- Jacobian G1 points, Jaune's representation. -/
abbrev G1J : Type := EllipticCurve.JacobianPoint BLSF

/-- Bit width of the scalars `g1Msm` reads: scalars are reduced mod `r` first, and
`r < 2^255`. -/
def msmScalarBits : Nat := 255

/-- Window width for `n` points: about `log2 n - 3`, at least 1. For 4,096 points it
is 9: 29 windows of 4,096 mixed additions plus about 1,000 bucket-sum additions. -/
def msmWindow (n : Nat) : Nat := max 1 (n.log2 - 3)

/-- One window: bucket every point by its `c`-bit digit at window `w`, then sum
`sum_d d * bucket_d` with the running-sum trick (two additions per bucket). -/
def msmWindowSum (pairs : Array (BLSP × Nat)) (c w : Nat) : G1J :=
  let mask := 2 ^ c - 1
  let buckets : Array G1J := pairs.foldl
    (fun bs (p, s) =>
      let d := (s >>> (w * c)) &&& mask
      if d = 0 then bs else bs.modify (d - 1) fun b => EllipticCurve.Jacobian.mixedAdd b p)
    (Array.replicate mask EllipticCurve.Jacobian.infinity)
  let (_, total) := buckets.foldr
    (fun b (running, total) =>
      let running := EllipticCurve.Jacobian.add running b
      (running, EllipticCurve.Jacobian.add total running))
    (EllipticCurve.Jacobian.infinity, EllipticCurve.Jacobian.infinity)
  total

/-- Bucket (Pippenger) MSM: `sum_i s_i * P_i` in G1. Lists of different lengths
are zipped (the callers check lengths first, as `g1_lincomb` asserts). -/
def g1Msm (points : Array BLSP) (scalars : Array Nat) : BLSP :=
  let pairs := (points.zip scalars).map fun (p, s) => (p, s % blsCurveOrder)
  let c := msmWindow pairs.size
  let nWin := (msmScalarBits + c - 1) / c
  let acc := (List.range nWin).reverse.foldl
    (fun (acc : G1J) w =>
      let shifted := (List.range c).foldl (fun a _ => EllipticCurve.Jacobian.double a) acc
      EllipticCurve.Jacobian.add shifted (msmWindowSum pairs c w))
    EllipticCurve.Jacobian.infinity
  EllipticCurve.Jacobian.toAffine acc

end JauneConsensus
