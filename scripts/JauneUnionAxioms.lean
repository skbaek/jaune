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
import Jaune.Check.FrameBridgeAudit
import Jaune.Check.Hash
import Jaune.Check.InstructionsAudit
import Jaune.Check.KeccakSpec
import Jaune.Check.Machine
import Jaune.Check.Precompiles
import Jaune.Check.RIPEMD160Spec
import Jaune.Check.RlpEval
import Jaune.Check.Sufficiency
import Jaune.Check.Transaction
import Jaune.Check.Types
import Jaune.Check.MessageCall
-- Standalone proof facts, outside the production umbrella.
import Jaune.StaticcallEffects
-- Standalone tracer modules, outside the production umbrella.
import Jaune.TraceTransaction
import Jaune.MessageCall.TraceJson
import Jaune.Run.Trace
import Jaune.Run.BodyT8n
import Jaune.Run.BodyFactsT8n

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
