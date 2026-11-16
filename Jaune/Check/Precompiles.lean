-- Check/Precompiles.lean : executable checks of `Jaune/Precompiles.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/Precompiles.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.Precompiles

namespace Jaune

open Jaune

-- MODEXP boundary guards.  The schedules themselves are checked against
-- authoritative upstream vectors (`modexp_eip2565.json` for Prague and
-- `modexp_eip7883.json` for Osaka); these pin the points where EIP-7883 and
-- EIP-7823 change behaviour, which a vector corpus can silently stop covering.

-- The multiplication complexity agrees at the 32-byte boundary and diverges
-- immediately above it, where Osaka charges the doubled quadratic term.
#guard modexpComplexity .eip2565 pragueModexpRules 32 32 = 16
#guard modexpComplexity .eip2565 osakaModexpRules 32 32 = 16
#guard modexpComplexity .eip2565 pragueModexpRules 33 0 = 25
#guard modexpComplexity .eip2565 osakaModexpRules 33 0 = 50
#guard modexpComplexity .eip2565 osakaModexpRules 0 32 = 16
#guard modexpComplexity .eip2565 osakaModexpRules 0 33 = 50
-- Below the boundary the flat term is what Osaka charges, not the quadratic
-- one Prague would have used.
#guard modexpComplexity .eip2565 pragueModexpRules 8 8 = 1
#guard modexpComplexity .eip2565 osakaModexpRules 8 8 = 16

-- EIP-198's piecewise polynomial in the raw byte lengths: `x ^ 2` at or below
-- 64 bytes, `x ^ 2 / 4 + 96 * x - 3072` through 1024, and
-- `x ^ 2 / 16 + 480 * x - 199680` above. The knot rows agree from both sides.
#guard modexpComplexity .eip198 eip198ModexpRules 0 0 = 0
#guard modexpComplexity .eip198 eip198ModexpRules 32 32 = 1024
#guard modexpComplexity .eip198 eip198ModexpRules 64 0 = 4096
#guard modexpComplexity .eip198 eip198ModexpRules 65 0 = 4224
#guard modexpComplexity .eip198 eip198ModexpRules 1024 0 = 357376
#guard modexpComplexity .eip198 eip198ModexpRules 1025 0 = 357984

-- The exponent-length term doubles above 32 bytes; at or below it, both forks
-- read the same `bit_length - 1` of the exponent head.
#guard modexpIterations pragueModexpRules 32 0 = 1
#guard modexpIterations osakaModexpRules 32 0 = 1
#guard modexpIterations pragueModexpRules 33 0 = 8
#guard modexpIterations osakaModexpRules 33 0 = 16
#guard modexpIterations osakaModexpRules 64 0 = 512
#guard modexpIterations pragueModexpRules 8 255 = 7
#guard modexpIterations osakaModexpRules 8 255 = 7

-- The floor rises from 200 to 500.
#guard modexpGasCost .eip2565 pragueModexpRules 32 32 32 0 = 200
#guard modexpGasCost .eip2565 osakaModexpRules 32 32 32 0 = 500
-- Before Berlin the divisor is 20, there is no floor, and the complexity above
-- is EIP-198's: `1024 * 1 / 20`.
#guard modexpGasCost .eip198 eip198ModexpRules 32 32 32 0 = 51

-- EIP-7823 bounds every header at 1024 and only from Osaka.
#guard modexpLengthsInBounds pragueModexpRules 1025 1025 1025
#guard modexpLengthsInBounds osakaModexpRules 1024 1024 1024
#guard ¬ modexpLengthsInBounds osakaModexpRules 1025 0 0
#guard ¬ modexpLengthsInBounds osakaModexpRules 0 1025 0
#guard ¬ modexpLengthsInBounds osakaModexpRules 0 0 1025

-- The precompile's own length check is what makes the widths above hold; these
-- pin that the reader really does produce eight and sixteen words.
#guard (readLeUInt64Words (List.replicate 213 (0x00 : UInt8)) 4 8).length = 8
#guard (readLeUInt64Words (List.replicate 213 (0x00 : UInt8)) 68 16).length = 16

#guard (Bytes.toExceptBls12G1 (Bls12G1.toBytes blsG1Generator)).toOption = some blsG1Generator
#guard
  (Bytes.toExceptBls12G1 (List.replicate 128 (0 : UInt8))).toOption = some (⟨0, 0⟩ : Bls12G1)
#guard (Bytes.toExceptBls12G2 (Bls12G2.toBytes blsG2Generator)).toOption = some blsG2Generator

end Jaune

