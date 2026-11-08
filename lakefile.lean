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

/--
Consensus layer (goal `jaune-consensus-electra-fulu-v1`): an executable Electra and Fulu
beacon-chain specification. It lives outside `Jaune/` so that Blanc, whose build needs only
`jaune/Assurance`, does not build it; `JauneUnionAxioms` covers `Jaune/` only.
-/
@[default_target]
lean_lib «JauneConsensus» where

/-- The consensus conformance runner (`ConsensusMain.lean`): strict, count-checked runs of the
pinned `v1.6.1` vectors, and the cross-layer fork pairing printer (`--forks`). -/
@[default_target]
lean_exe «jaune-consensus» where
  root := `ConsensusMain

/--
Whole-library axiom union for the consensus layer (`scripts/ConsensusUnionAxioms.lean`).
Separate from `Assurance`, which Blanc builds in full, so Blanc's build does not grow.
-/
@[default_target]
lean_lib «ConsensusAssurance» where
  srcDir := "scripts"
  roots := #[`ConsensusUnionAxioms]

/-- Timing probe for the consensus BLS primitives (pairing, map-to-curve, hash-to-curve).
Not a default target. -/
lean_exe «jaune-consensus-bls-bench» where
  root := `ConsensusBLSBench

/-- Local runner for the general-preset `kzg` vectors (EIP-4844 and EIP-7594), until it is
folded into `jaune-consensus`. Not a default target. -/
lean_exe «jaune-consensus-kzg-vectors» where
  root := `ConsensusKZGVectors
