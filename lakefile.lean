import Lake
open Lake DSL

package «jaune» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

@[default_target]
lean_lib «Jaune» where

@[default_target]
lean_exe «jaune» where
  root := `Main

/--
Bounded native probe for call-depth/calldata-size memory scaling, driven by
`scripts/check-memory-probe.sh`. It is a default target so the ordinary
`lake build` elaborates it: an anti-regression instrument that no automated
path builds is an instrument that rots.
-/
@[default_target]
lean_exe «jaune-memory-probe» where
  root := `MemoryProbe
