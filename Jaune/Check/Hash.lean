-- Check/Hash.lean : executable checks of `Jaune/Hash.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/Hash.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.Hash

namespace Jaune

open Jaune

namespace RIPEMD160

-- On a full 64-byte chunk the length-indexed reader agrees, word for word,
-- with the list transcription it replaced.
#guard (Bytes.toChunk ((List.range 64).map Nat.toUInt8)).toList
        = Bytes.toUInt32Rev ((List.range 64).map Nat.toUInt8)

end RIPEMD160

end Jaune

