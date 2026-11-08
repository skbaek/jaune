import JauneConsensus.Containers
import JauneConsensus.Helpers

/-!
# Epoch processing (Electra and Fulu)

`process_epoch` and each of its sub-steps, transcribed from `ethereum/consensus-specs` `v1.6.1`
in the operation order of `specs/electra/beacon-chain.md` (`process_epoch`) and
`specs/fulu/beacon-chain.md` (which appends `process_proposer_lookahead`). Each definition cites
the spec file of its latest definition at or before Fulu. Every step is a function
`BeaconState P f → M (BeaconState P f)`: pyspec mutates the state in place; a failure anywhere is
a typed rejection and no partial state is returned.
-/

namespace JauneConsensus

open Jaune

variable {P : Preset} {f : CFork}

/-- `get_current_epoch(state) = compute_epoch_at_slot(state.slot)`
(`specs/phase0/beacon-chain.md`). -/
def stateEpoch (s : BeaconState P f) : M Epoch := computeEpochAtSlot P s.slot

/-- `process_eth1_data_reset` (`specs/phase0/beacon-chain.md`). -/
def processEth1DataReset (s : BeaconState P f) : M (BeaconState P f) := do
  let nextEpoch ← (← stateEpoch s).add? U64.one "process_eth1_data_reset: epoch + 1"
  let period ← u64 P.EPOCHS_PER_ETH1_VOTING_PERIOD "EPOCHS_PER_ETH1_VOTING_PERIOD"
  if (← nextEpoch.mod? period "process_eth1_data_reset: %").toNat == 0 then
    pure { s with eth1_data_votes := ⟨#[], by simp⟩ }
  else pure s

/-- `process_participation_flag_updates` (`specs/altair/beacon-chain.md`). -/
def processParticipationFlagUpdates (s : BeaconState P f) : M (BeaconState P f) :=
  pure { s with
    previous_epoch_participation := s.current_epoch_participation
    current_epoch_participation :=
      ⟨Array.replicate s.validators.toArray.size UIntN.zero,
        by simpa using s.validators.size_le⟩ }

end JauneConsensus
