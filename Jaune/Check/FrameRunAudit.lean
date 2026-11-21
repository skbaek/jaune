import AxiomAudit
import Jaune.FrameRun.Unique
import Jaune.FrameRun.Facts
import Jaune.FrameRun.Memory
import Jaune.SymbolicPush
import Jaune.SymbolicArithmetic
import Examples.Prefix
import Examples.Execution
import Examples.Arithmetic

/-!
Axiom audit for the frame-run facts that `scripts/ExecutionAxioms.lean` does not pin (goal
`jaune-shape-and-names-v1`, G2b delete commit). The surviving rows of the deleted
`Jaune/Check/CheckedRowsAudit.lean`: the union rows of the run-fact, symbolic and example modules,
and the five theorems with no destination row. The other surviving rows of that module are the
re-pointed rows of `scripts/ExecutionAxioms.lean`, so they are not repeated here.
-/

#union_axioms_of_modules Jaune.FrameRun.Facts
#union_axioms_of_modules Jaune.FrameRun.Memory
#union_axioms_of_modules Jaune.SymbolicPush
#union_axioms_of_modules Jaune.SymbolicArithmetic
#union_axioms_of_modules Examples.Prefix
#union_axioms_of_modules Examples.Execution
#union_axioms_of_modules Examples.Arithmetic
#expect_axioms Jaune.Frame.Run.Prefix.unique [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.settledGasLe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.memory_accounting_output [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.Node.Prefix.trans [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.Node.Prefix.lt [Classical.choice, Quot.sound, propext]
