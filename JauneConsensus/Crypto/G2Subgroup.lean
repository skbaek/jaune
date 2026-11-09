-- A fast G2 membership test for BLS12-381.
--
-- `subgroup_check_E2` may be the naive `r * P = identity` (draft-irtf-cfrg-bls-signature-04,
-- section 1.3) or a faster equivalent (its Appendix A allows [Bowe19]). This module uses the
-- endomorphism test for BLS12 curves: `P` (on `E'`) lies in G2 if and only if
-- `psi(P) = [t] P`, where `t = -2^63 - 2^62 - 2^60 - 2^57 - 2^48 - 2^16` is the BLS12-381
-- parameter (draft-irtf-cfrg-pairing-friendly-curves-11, section 4.2.1) and `psi` is the
-- untwist-Frobenius-twist endomorphism (M. Scott, "A note on group membership tests for
-- G1, G2 and GT on BLS pairing-friendly curves", 2021). `|t|` is Jaune's
-- `blsAteLoopCount`, so the test costs a 64-bit scalar multiplication instead of a
-- 255-bit one.
--
-- The equivalence is the cited theorem, not proved here. Differential `#guard`s in
-- G2SubgroupVectors.lean compare it with the naive check on subgroup points, on points of
-- `E'` outside the subgroup (map-to-curve outputs before cofactor clearing, and their
-- small multiples), and on the identity.

import Jaune.BLS

namespace JauneConsensus

open Jaune

/-- `xi = 1 + u`, the twisting element (`E'`: `y^2 = x^3 + 4 xi`). -/
def blsXi : BLSF2 := BLSF2.mk 1 1

/-- The Frobenius `x ↦ x^p` on `Fp2`: `c0 + c1 u ↦ c0 - c1 u`. -/
def f2Frob (x : BLSF2) : BLSF2 :=
  let cs := List.takeRightV 2 x.val (0 : BLSF)
  BLSF2.mk cs[1].val (blsPrime - cs[0].val)

/-- `psi`'s coefficients `xi^(-(p-1)/3)` and `xi^(-(p-1)/2)`: Jaune's twist divides by
`w^2` and `w^3` with `w^6 = xi`, so untwisting, applying Frobenius and twisting back
multiplies `x^p` by `w^(2 - 2p)` and `y^p` by `w^(3 - 3p)`. -/
def psiCx : BLSF2 := (blsXi ^ ((blsPrime - 1) / 3))⁻¹
def psiCy : BLSF2 := (blsXi ^ ((blsPrime - 1) / 2))⁻¹

/-- The endomorphism `psi` on `E'`. -/
def g2Psi (p : BLSP2) : BLSP2 :=
  if p = ⟨0, 0⟩ then p else ⟨f2Frob p.x * psiCx, f2Frob p.y * psiCy⟩

/-- G2 membership for a point of `E'`: `psi(P) = [t] P` with `t = -blsAteLoopCount`. -/
def g2SubgroupCheckFast (p : BLSP2) : Bool :=
  g2Psi p = -(p.mulBy blsAteLoopCount)

end JauneConsensus
