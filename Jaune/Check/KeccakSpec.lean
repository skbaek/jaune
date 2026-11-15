-- Check/KeccakSpec.lean : executable checks of `Jaune/KeccakSpec.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/KeccakSpec.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.KeccakSpec

namespace Jaune

open Jaune

namespace Keccak.FIPS

/- Known answer: Keccak-256 of the empty string is
`c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`, the code
hash of every account without code. Source: the official Ethereum test
fixtures, e.g. EEST `constantinople/eip1052_extcodehash/extcodehash/
extcodehash_of_empty` and ethereum/tests `GeneralStateTests/stExtCodeHash/
codeCopyZero` (the `EXTCODEHASH` of a codeless account, stored as the expected
post-state value). This evaluates the transcription alone; it does not touch
the kernel. -/
#guard keccak256Digest [] ==
    [0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c, 0x92, 0x7e, 0x7d, 0xb2,
     0xdc, 0xc7, 0x03, 0xc0, 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
     0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70]

end Keccak.FIPS

end Jaune

