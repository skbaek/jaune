import AxiomAudit
import Jaune.Instructions.ShuffleFacts
import Jaune.Instructions.PushFacts
import Jaune.Instructions.LogFacts

/-! Axiom rows for the Shuffle, push and Log families (S4): each family law and each bridge to
the checked interpreter uses only the standard axioms. -/

#expect_axioms Jaune.Shuffle.run_eq [Quot.sound, propext]
#expect_axioms Jaune.ShuffleRow.step_ok [Quot.sound, propext]
#expect_axioms Jaune.ShuffleRow.step_error [Quot.sound, propext]
#expect_axioms Jaune.ShuffleRow.step_frame [Quot.sound, propext]
#expect_axioms Jaune.PlainOp.shuffle_run_congr_fork [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.NextOp.shuffle_step_congr_fork [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.NextOp.push_step_congr_fork [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.LogRow.step_ok [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.LogRow.step_error [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.LogRow.step_frame [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.State.liftLog_keeps [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.PlainOp.log_run_congr_fork [Classical.choice, Quot.sound, propext]
