import AxiomAudit
import Jaune
-- Runner-side modules that `Jaune.lean` does not import; `Main` does.
import Jaune.BLSGuards
import Jaune.ChainStore
import Jaune.FixtureTransition
import Jaune.FixtureException
import Jaune.T8n
-- Executable checks relocated out of the specification modules (`Jaune/Check/`).
import Jaune.Check.BLS
import Jaune.Check.Basic
import Jaune.Check.Blake2Spec
import Jaune.Check.EC
import Jaune.Check.Execution
import Jaune.Check.Fork
import Jaune.Check.CheckedExecution
import Jaune.Check.CheckedMessageCall
import Jaune.Check.CheckedSufficiency
import Jaune.Check.CheckedTransaction
import Jaune.Check.CheckedBody
import Jaune.Check.CheckedMachine
import Jaune.Check.CheckedPortAuditA
import Jaune.Check.CheckedPortAuditB
import Jaune.Check.CheckedFactPorts
import Jaune.Check.FrameRunAudit
import Jaune.Check.CheckedSpecAudit
import Jaune.Check.InstructionFamiliesAudit
import Jaune.Check.Hash
import Jaune.Check.InstructionsAudit
import Jaune.Check.KeccakSpec
import Jaune.Check.Machine
import Jaune.Check.Precompiles
import Jaune.Check.RIPEMD160Spec
import Jaune.Check.RlpEval
import Jaune.Check.Transaction
import Jaune.Check.Types
-- Standalone proof facts, outside the production umbrella.
-- Standalone tracer modules, outside the production umbrella.
import Jaune.Run.BodyFactsT8n
import Jaune.MessageCall.CheckedTrace
import Jaune.MessageCall.CheckedTraceJson

/-!
# Whole-library axiom union for `Jaune`

One walk, with one shared visited set, rooted at every kernel constant (all kinds,
private names and auxiliaries) recorded by every imported module named `Jaune` or
`Jaune.…` — all of `Jaune/`, including the runner-side and standalone tracer modules.
The assurance-manifest gate checks this import coverage against the source tree. Elaboration fails if that union contains an axiom outside the standard
`propext, Classical.choice, Quot.sound`, if the population is empty, or if the walk
reaches an absent constant. This complements, and never replaces, the exact
per-declaration rows of `ExecutionAxioms.lean`: a union can only say that no
declaration uses a non-standard axiom, not which standard axioms a pinned
declaration uses. Blanc's own union covers `Blanc.…` modules only, so the Jaune
constants Blanc does not reach are audited here.
-/

#union_axioms_of_modules Jaune
