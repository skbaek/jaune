import AxiomAudit
import Jaune.Bridge.G2b.CheckedRowAgreement
import Jaune.Instructions.ShuffleFacts
import Jaune.Instructions.PushFacts
import Jaune.Instructions.LogFacts

/-! Axiom rows for the Shuffle, push and Log families (S4): each family law and each bridge to
the checked interpreter uses only the standard axioms. -/

#expect_axioms Jaune.Checked.Shuffle.run_eq [Quot.sound, propext]
#expect_axioms Jaune.Checked.ShuffleRow.step_ok [Quot.sound, propext]
#expect_axioms Jaune.Checked.ShuffleRow.step_error [Quot.sound, propext]
#expect_axioms Jaune.Checked.ShuffleRow.step_frame [Quot.sound, propext]
#expect_axioms Jaune.Checked.Arms.PlainOp.shuffleRow?_runCore_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Arms.NextOp.shuffleRow?_step_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.shuffle_run_congr_fork [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.NextOp.shuffle_step_congr_fork [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Arms.NextOp.pushRow_step_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Arms.NextOp.pushRow?_step_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.NextOp.push_step_congr_fork [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.LogRow.step_ok [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.LogRow.step_error [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.LogRow.step_frame [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.State.liftLog_keeps [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Arms.PlainOp.logRow?_runCore_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.log_run_congr_fork [Classical.choice, Quot.sound, propext]
