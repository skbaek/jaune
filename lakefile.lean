import Lake
open Lake DSL

package «elevm» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

@[default_target]
lean_lib «Elevm» where

@[default_target]
lean_exe «elevm» where
  root := `Main
