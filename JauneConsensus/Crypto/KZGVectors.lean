-- Cheap checks on the generated trusted setup (TrustedSetup.lean). Only the first
-- entries are decoded here: decoding all 8,192 G1 points in the interpreter would cost
-- far more than the check is worth; the kzg vector runner decodes them all.

import JauneConsensus.Crypto.KZG

namespace JauneConsensus.KZGVectors

open Jaune JauneConsensus

-- Shapes: 4096 + 4096 points of 48 bytes, 65 of 96 bytes, as hex.
#guard kzgSetupG1MonomialHex.length = 4096 * 96
#guard kzgSetupG1LagrangeHex.length = 4096 * 96
#guard kzgSetupG2MonomialHex.length = 65 * 192
-- KZG_SETUP_G2_MONOMIAL[1] equals Jaune's independently pinned point (BLSConst), and
-- the first monomial entries are the generators.
#guard ((setupPoints kzgSetupG2MonomialHex 96).take 2).mapM signatureToPoint
  = .ok [blsG2Generator, kzgSetupG2Monomial1P]
#guard ((setupPoints kzgSetupG1MonomialHex 48).take 1).mapM pubkeyToPoint = .ok [blsG1Generator]
-- Bit reversal on 8 entries.
#guard bitReversalPermutation #[0, 1, 2, 3, 4, 5, 6, 7] = .ok #[0, 4, 2, 6, 1, 5, 3, 7]

end JauneConsensus.KZGVectors
