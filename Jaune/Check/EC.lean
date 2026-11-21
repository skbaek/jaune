-- Check/EC.lean : executable checks of `Jaune/EC.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/EC.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.EC

namespace Jaune

open Jaune

-- Trimming is representational, not semantic: a coordinate written with its
-- leading zero and the same coordinate with that zero trimmed away twist to
-- the same point.
#guard twist ⟨⟨trimZero [0, 5]⟩, ⟨trimZero [0, 7]⟩⟩
        = twist ⟨⟨[0, 5]⟩, ⟨[0, 7]⟩⟩
#guard twist ⟨⟨[]⟩, ⟨[]⟩⟩ = twist ⟨⟨[0, 0]⟩, ⟨[0, 0]⟩⟩
#guard trimZero [(0 : AltBn128Fp), 5] = [(5 : AltBn128Fp)]

-- The base point is on the curve, and multiplying it by the stated group order
-- reaches infinity: a transcription error in any of the six curve literals
-- would have to survive both.
#guard secp256r1.generator.isOnCurve
#guard EllipticCurve.mulBy secp256r1.generator secp256r1.curveOrder
  = secp256r1.infinity
#guard EllipticCurve.mulBy secp256r1.generator (secp256r1.curveOrder + 1)
  = secp256r1.generator
#guard secp256r1.a.val + 3 = secp256r1.prime

end Jaune

