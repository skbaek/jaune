import JauneConsensus.GloasForkChoice

/-!
# The Gloas state transition for the fork-choice runners

`on_block`, `on_attestation` and the fast confirmation rule reach the Gloas `process_slots` and
`state_transition` through `Gloas.Transition` (`JauneConsensus/GloasForkChoice.lean`). Until the
Gloas state transition (goal `eip8282-gloas-cross-layer-v1`, U5) is merged there is none, and every
Gloas fork-choice case fails closed as unimplemented.
-/

namespace JauneConsensus.Harness

/-- The Gloas state transition the fork-choice runners use, once it exists. -/
def gloasTransition? {P : Preset} : Option (Gloas.Transition P) := none

end JauneConsensus.Harness
