-- Check/BLS.lean : executable checks of `Jaune/BLS.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/BLS.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.BLS

namespace Jaune

open Jaune

-- py_ecc.bls12_381.bls12_381_curve.double(G1) (== add(G1, G1) == multiply(G1,
-- 2), confirmed against the local venv), pinned here as an independent
-- cross-check on EllipticCurve.add's p = q branch for BLSF.
def BLSGenerators.G1Double.x : Nat :=
  838589206289216005799424730305866328161735431124665289961769162861615689790485775997575391185127590486775437397838
def BLSGenerators.G1Double.y : Nat :=
  3450209970729243429733164009999191867485184320918914219895632678707687208996709678363578245114137957452475385814312

def blsG1GenDouble : Bls12G1 := ⟨FieldElement.ofNat BLSGenerators.G1Double.x, FieldElement.ofNat BLSGenerators.G1Double.y⟩

#guard blsG1Generator.isOnCurve
#guard blsG1Generator.double = blsG1GenDouble
#guard (blsG1Generator + blsG1Generator) = blsG1GenDouble
#guard Bls12G1.toBytes (⟨0, 0⟩ : Bls12G1) = List.replicate 128 (0 : UInt8)
#guard (blsG1Generator.mulBy blsCurveOrder) = ⟨0, 0⟩

#guard blsG2Generator.isOnCurve
#guard Bls12G2.toBytes (⟨0, 0⟩ : Bls12G2) = List.replicate 256 (0 : UInt8)
#guard (blsG2Generator.mulBy blsCurveOrder) = ⟨0, 0⟩

-- py_ecc checks `is_on_curve(G12, b12)` for the twisted generator;
-- b12 = b = 4, so the G1 embedding must land on the same curve.
#guard (blsTwist blsG2Generator).isOnCurve
#guard (Bls12G1.toBls12Fp12Pair blsG1Generator).isOnCurve

-- Trimming leading zeros is representational: the padded coefficient reads
-- give the same answer for a trimmed element and its full-width spelling.
#guard Bls12Fp2.toBytes ⟨trimZero [0, 5]⟩ = Bls12Fp2.toBytes ⟨[0, 5]⟩
#guard Bls12Fp2.sgn0 ⟨trimZero [0, 5]⟩ = Bls12Fp2.sgn0 ⟨[0, 5]⟩
#guard Bls12Fp2.sgn0 ⟨[]⟩ = Bls12Fp2.sgn0 ⟨[0, 0]⟩

-- Correctness #guards: the first positive vector of each official EIP-2537
-- map file (bls_g1map_ / bls_g2map_).  Input field element maps to exactly
-- the expected output point, which is on curve and in the correct subgroup.
-- map_fp_to_G1_bls.json[0]:
#guard
  blsMapFpToG1 (blsToFp 0x156c8a6a2c184569d69a76be144b5cdc5141d2d2ca4fe341f011e25e3969c55ad9e9b9ce2eb833c81a908e5fa4ac5f03)
    = (⟨FieldElement.ofNat 0x184bb665c37ff561a89ec2122dd343f20e0f4cbcaec84e3c3052ea81d1834e192c426074b02ed3dca4e7676ce4ce48ba,
        FieldElement.ofNat 0x04407b8d35af4dacc809927071fc0405218f1401a6d15af775810e4e460064bcc9468beeba82fdc751be70476c888bf3⟩ : Bls12G1)
#guard
  let g1 := blsMapFpToG1 (blsToFp 0x156c8a6a2c184569d69a76be144b5cdc5141d2d2ca4fe341f011e25e3969c55ad9e9b9ce2eb833c81a908e5fa4ac5f03)
  g1.isOnCurve ∧ g1.mulBy blsCurveOrder = ⟨0, 0⟩
-- map_fp2_to_G2_bls.json[0]:
#guard
  blsMapFp2ToG2 (Bls12Fp2.mk
      0x07355d25caf6e7f2f0cb2812ca0e513bd026ed09dda65b177500fa31714e09ea0ded3a078b526bed3307f804d4b93b04
      0x02829ce3c021339ccb5caf3e187f6370e1e2a311dec9b75363117063ab2015603ff52c3d3b98f19c2f65575e99e8b78c)
    = (⟨Bls12Fp2.mk
        0x00e7f4568a82b4b7dc1f14c6aaa055edf51502319c723c4dc2688c7fe5944c213f510328082396515734b6612c4e7bb7
        0x126b855e9e69b1f691f816e48ac6977664d24d99f8724868a184186469ddfd4617367e94527d4b74fc86413483afb35b,
        Bls12Fp2.mk
        0x0caead0fd7b6176c01436833c79d305c78be307da5f6af6c133c47311def6ff1e0babf57a0fb5539fce7ee12407b0a42
        0x1498aadcf7ae2b345243e281ae076df6de84455d766ab6fcdaad71fab60abb2e8b980a440043cd305db09d283c895e3d⟩ : Bls12G2)
#guard
  let g2 := blsMapFp2ToG2 (Bls12Fp2.mk
      0x07355d25caf6e7f2f0cb2812ca0e513bd026ed09dda65b177500fa31714e09ea0ded3a078b526bed3307f804d4b93b04
      0x02829ce3c021339ccb5caf3e187f6370e1e2a311dec9b75363117063ab2015603ff52c3d3b98f19c2f65575e99e8b78c)
  g2.isOnCurve ∧ g2.mulBy blsCurveOrder = ⟨0, 0⟩

#guard kzgSetupG2Monomial1Point.isOnCurve
#guard kzgSetupG2Monomial1Point.mulBy blsCurveOrder = ⟨0, 0⟩

end Jaune

