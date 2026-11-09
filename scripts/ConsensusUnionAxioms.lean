import AxiomAudit
import JauneConsensus
import JauneConsensus.Facts.Operations
import JauneConsensus.Facts.ExpectedWithdrawals
import JauneConsensus.Facts.Gloas.Step
import JauneConsensus.Facts.Gloas.Frame
import JauneConsensus.JointGloas
import JauneConsensus.Facts.JointGloas
import JauneConsensus.Facts.Gloas.BuilderAuth
import JauneConsensus.Facts.Gloas.BuilderTraces
import JauneConsensus.Facts.Gloas.WithdrawalsB5
import JauneConsensus.Facts.Gloas.B5Witnesses
import JauneConsensus.Facts.Gloas.BuilderWitnesses
import JauneConsensus.Facts.Gloas.BuilderFrames
import JauneConsensus.Facts.Gloas.Invariants
import JauneConsensus.Facts.Gloas.InvariantsFrames
import JauneConsensus.Facts.Gloas.InvariantsPhases
import JauneConsensus.Facts.Gloas.InvariantsRequests
import JauneConsensus.Facts.Gloas.InvariantsSweep
import JauneConsensus.Facts.Gloas.InvariantsSlots
import JauneConsensus.Facts.Gloas.InvariantsGen
import JauneConsensus.Facts.Gloas.InvariantsBid
import JauneConsensus.Facts.Gloas.InvariantsAttest
import JauneConsensus.Facts.Gloas.InvariantsQueues
import JauneConsensus.Facts.Gloas.InvariantsRefs

/-!
# Whole-library axiom union for `JauneConsensus`

The consensus layer (goal `jaune-consensus-electra-fulu-v1`) is a second library root outside
`Jaune/`, so `JauneUnionAxioms` (rooted at modules named `Jaune` or `Jaune.…`; `Name` prefixes
are compared by component, so `JauneConsensus` is not among them) does not reach it, and Blanc's
`jaune/Assurance` never builds it. This module audits it the same way: one walk over every
kernel constant recorded by every imported module named `JauneConsensus` or
`JauneConsensus.…`. Elaboration fails if the union contains an axiom outside the standard
`propext, Classical.choice, Quot.sound`, if the population is empty, or if the walk reaches an
absent constant. `scripts/check-assurance-manifest.py` checks that this module's imports cover
every source module under `JauneConsensus/`.
-/

#union_axioms_of_modules JauneConsensus
