import JauneConsensus.GloasForkChoice
import JauneConsensus.GloasTransition

/-!
# The Gloas state transition for the fork-choice runners

`on_block`, `on_attestation` and the fast confirmation rule reach the Gloas `process_slots` and
`state_transition` through `Gloas.Transition` (`JauneConsensus/GloasForkChoice.lean`); the runners
pass the Gloas twins of `JauneConsensus/GloasTransition.lean` (goal
`eip8282-gloas-cross-layer-v1`, U5).
-/

namespace JauneConsensus.Harness

/-- The Gloas state transition the fork-choice runners use: `Gloas.processSlots` and
`Gloas.stateTransition`. -/
def gloasTransition {P : Preset} : Gloas.Transition P :=
  { processSlots := Gloas.processSlots
    stateTransition := fun ctx state block validate =>
      Gloas.stateTransition ctx state block validate }

end JauneConsensus.Harness
