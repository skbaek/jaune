-- This module serves as the root of the `JauneChecks` library.
-- Executable checks (`#guard`, `example`) and their test helpers that used to sit
-- inside the specification modules live in `Jaune/Check/`. They are kept out of
-- the `Jaune` library root so that no proof client elaborates them, and are
-- reached by the default build through this root (goal
-- `jaune-shape-and-names-v1`, unit W0; classification in `scripts/layering.json`).
import Jaune.BLSGuards
import Jaune.Check.BLS
import Jaune.Check.Basic
import Jaune.Check.Blake2Spec
import Jaune.Check.EC
import Jaune.Check.Execution
import Jaune.Check.Fork
import Jaune.Check.FrameExecution
import Jaune.Check.MessageCall
import Jaune.Check.Sufficiency
import Jaune.Check.TopLevel
import Jaune.Check.Body
import Jaune.Check.PlainInstructions
import Jaune.Check.PortAuditA
import Jaune.Check.PortAuditB
import Jaune.Check.FactPorts
import Jaune.Check.FrameRunAudit
import Jaune.Check.SpecAudit
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
import Jaune.Run.BodyFactsT8n
