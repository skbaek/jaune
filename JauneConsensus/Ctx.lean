import JauneConsensus.Config

/-!
# The processing context

The first argument of the block and epoch entry points (`processBlock`, `processEpoch`): the
runtime configuration and the two switches pyspec's test harness sets. `blsActive` is pyspec's
`bls.bls_active` (when off, only the verification predicates are switched, to `True`; the
predicates under the switch are `Signing.blsVerify` and its siblings). `executionValid` is the
mocked execution engine's verdict (`execution.yaml`); state transitions outside the
`operations` vectors run with `true`.
-/

namespace JauneConsensus

/-- The processing context: configuration and the harness switches. -/
structure Ctx where
  cfg : Config
  /-- pyspec `bls.bls_active`. -/
  blsActive : Bool := true
  /-- The mocked `execution_engine.verify_and_notify_new_payload` verdict. -/
  executionValid : Bool := true

end JauneConsensus
