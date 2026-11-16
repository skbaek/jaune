-- Check/RlpEval.lean : executable checks of `Jaune/RlpEval.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/RlpEval.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.RlpEval

namespace Jaune

/-! ### Controls

The build fails here if a twin stops being kernel-evaluable or stops matching
the public codec on a long-form item (length of length, nested list). -/

example : Bytes.toRlpItem? [0xf8, 0x02, 0x81, 0xff] = some (.list [.bytes [0xff]]) := by
  rw [Bytes.toRlpItem?_eq_toRlpItemS]; decide +kernel

example : Bytes.toRlpItem? [0xc4, 0xc3, 0x82, 0x01, 0xaa] =
    some (.list [.list [.bytes [0x01, 0xaa]]]) := by
  rw [Bytes.toRlpItem?_eq_toRlpItemS]; decide +kernel

example : (Rlp.Item.bytes (List.replicate 56 0)).toBytes = 0xb8 :: 0x38 :: List.replicate 56 0 := by
  rw [Rlp.Item.toBytes_eq_toBytesS]; decide +kernel

end Jaune

