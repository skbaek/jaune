import AxiomAudit
import Jaune.FrameRun.CheckedUnique
import Jaune.FrameRun.CheckedFacts
import Jaune.FrameRun.CheckedMemory
import Jaune.CheckedSymbolicPush
import Jaune.CheckedSymbolicArith
import Examples.CheckedPrefix
import Examples.CheckedExecution
import Examples.CheckedArithmetic

/-!
Axiom audit for the frame-run facts that `scripts/ExecutionAxioms.lean` does not pin (goal
`jaune-shape-and-names-v1`, G2b delete commit). The surviving rows of the deleted
`Jaune/Check/CheckedRowsAudit.lean`: the union rows of the run-fact, symbolic and example modules,
and the five theorems with no destination row. The other surviving rows of that module are the
re-pointed rows of `scripts/ExecutionAxioms.lean`, so they are not repeated here.
-/

#union_axioms_of_modules Jaune.FrameRun.CheckedFacts
#union_axioms_of_modules Jaune.FrameRun.CheckedMemory
#union_axioms_of_modules Jaune.CheckedSymbolicPush
#union_axioms_of_modules Jaune.CheckedSymbolicArith
#union_axioms_of_modules Examples.CheckedPrefix
#union_axioms_of_modules Examples.CheckedExecution
#union_axioms_of_modules Examples.CheckedArithmetic
#expect_axioms Jaune.Checked.Frame.Run.Prefix.unique [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.settledGasLe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.memory_accounting_output [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.Node.Prefix.trans [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.Node.Prefix.lt [Classical.choice, Quot.sound, propext]
