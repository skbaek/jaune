import JauneConsensus.Transition
import JauneConsensus.Block
import JauneConsensus.Epoch

/-!
# The state transition with the spec's block and epoch processing

`process_slots` and `state_transition` (`specs/phase0/beacon-chain.md`) instantiated with the
fork's `process_epoch` (`JauneConsensus/Epoch.lean`) and `process_block`
(`JauneConsensus/Block.lean`). The compositions themselves are `processSlotsWith` and
`stateTransitionWith` in `JauneConsensus/Transition.lean`; this module only closes them over
the two entry points, so the conformance harness and later theorems name one function.
-/

namespace JauneConsensus

variable {P : Preset} {f : CFork}

/-- `process_slots(state, slot)`. -/
def processSlots (ctx : Ctx) (state : BeaconState P f) (slot : Slot) : M (BeaconState P f) :=
  processSlotsWith (processEpoch ctx) state slot

/-- `state_transition(state, signed_block, validate_result)`; the BLS switch is
`ctx.blsActive`. -/
def stateTransition (ctx : Ctx) (state : BeaconState P f) (signedBlock : SignedBeaconBlock P f)
    (validateResult : Bool := true) : M (BeaconState P f) :=
  stateTransitionWith (processEpoch ctx) (processBlock ctx) ctx.blsActive state signedBlock
    validateResult

end JauneConsensus
