import Lake
open Lake DSL

package «jaune» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib «Jaune» where

/-- Consumer examples compile in the ambient package, outside the library import closure. -/
@[default_target]
lean_lib «Examples» where

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

/-- Optional streaming message tracer, outside Jaune's production import closure. -/
@[default_target]
lean_exe «jaune-trace» where
  root := `TraceMain

/--
Exact axiom expectations for the canonical execution surface
(`scripts/ExecutionAxioms.lean`), checked by the from-scratch walker in
`scripts/AxiomAudit.lean`. A default target, so an ordinary build enforces them.
`AxiomAudit` imports only `Lean`, for downstream reuse.
-/
@[default_target]
lean_lib «Assurance» where
  srcDir := "scripts"
  roots := #[`AxiomAudit, `ExecutionAxioms, `JauneUnionAxioms, `UnionAxiomsControls, `UnionAxiomsFixture.Good, `UnionAxiomsFixture.Bad, `UnionAxiomsFixture.Dep, `UnionAxiomsFixture.ViaDep]

/-- Consensus layer (goal `jaune-consensus-electra-fulu-v1`), outside `Jaune/` so Blanc's
`Assurance` closure does not build it. Minimal target added by the BLS worker; the SSZ
worker's branch adds the same library and the master reconciles them. -/
@[default_target]
lean_lib «JauneConsensus» where

/-- Timing probe for the consensus BLS primitives (pairing, map-to-curve, hash-to-curve).
Not a default target. -/
lean_exe «jaune-consensus-bls-bench» where
  root := `ConsensusBLSBench

/-- Local runner for the general-preset `bls` vectors (`eth_aggregate_pubkeys`,
`eth_fast_aggregate_verify`), until the shared consensus harness lands. Not a default
target. -/
lean_exe «jaune-consensus-bls-vectors» where
  root := `ConsensusBLSVectors
