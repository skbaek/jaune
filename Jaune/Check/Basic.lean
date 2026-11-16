-- Check/Basic.lean : executable checks of `Jaune/Basic.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/Basic.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.Basic

namespace Jaune

open Jaune _root_.List _root_.Nat

-- The byte-list comparator Jaune's tries use resolves both.
example : Std.TransCmp (compare : Bytes → Bytes → Ordering) := inferInstance
example : Std.LawfulEqCmp (compare : Bytes → Bytes → Ordering) := inferInstance

end Jaune

