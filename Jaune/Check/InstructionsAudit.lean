-- Check/InstructionsAudit.lean : axiom rows for the Memory and Read instruction families.
--
-- Check module (see `scripts/layering.json`). Each family law and each bridge of
-- `Jaune/Instructions/{Memory,Read}Facts.lean` (goal `jaune-shape-and-names-v1`, W4/S4) is held
-- to its exact subset of the three standard axioms. The default build compiles this module
-- through `JauneChecks.lean`.
import AxiomAudit
import Jaune.Instructions.MemoryFacts
import Jaune.Instructions.ReadFacts

#expect_axioms Jaune.Checked.MemoryRow.step_ok [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MemoryRow.step_error [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MemoryEffect.apply_size [Quot.sound, propext]
#expect_axioms Jaune.Checked.MemoryRow.step_size [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.memoryRow?_run_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.memoryRow?_run_fork_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.memory_run_congr_fork [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.memory_run_world [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.memory_run_substate [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.memory_run_trail [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.memory_run_gasMeasure_lt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.ReadRow.step_ok [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.ReadRow.step_error [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.State.liftRead_keeps [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.readRow?_run_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.readRow?_run_fork_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.read_run_congr_fork [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.read_run_keeps [Classical.choice, Quot.sound, propext]

-- The family dispatch (G2b, W4 step H): the cut's bridge against the per-opcode arms.
