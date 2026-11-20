import AxiomAudit
import Jaune.Bridge.G2b.FinalAdequacy
import Jaune.Bridge.G2b.FinalPrefix
import Jaune.Bridge.G2b.FinalRetained
import Jaune.Bridge.G2b.BodyRoots
import Jaune.Bridge.G2b.BodyResults
import Jaune.Bridge.G2b.KeptHistory
import Jaune.Bridge.G2b.KeptHistoryFold

#union_axioms_of_modules Jaune.Bridge.G2b
#union_axioms_of_modules Jaune.Run.Root
#union_axioms_of_modules Jaune.MessageCall.FinalAdequacy
#expect_axioms Jaune.Staging.Exec.ofRun [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.Exec.ofEvm_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.observe_rawNodes [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.Deriv.observe_parentPrefix_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.observe_retainedNodes [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.observe_committedFrames [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.Message.run_root_settled [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.exists_messageRoots [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.exists_transactionRoots [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.exists_preRoots [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.exists_requestRoots [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.exists_bodyRoots [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.BlockRun.exists_bodyRoots [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.KeptHistory.of_fold [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.BodyRoots.ran [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.BodyRoots.applied [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.bodyRoots_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.BodyPhase.Ran.unique [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.BodyRoots.unique [Classical.choice, Quot.sound, propext]
