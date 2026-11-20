import AxiomAudit
import Jaune.CheckedSufficiencyWalk
import Jaune.MessageCall.CheckedMemoryCosts
import Jaune.MessageCall.CheckedPlainMemory
import Jaune.MessageCall.CheckedMessageMemory
import Jaune.MessageCall.CheckedMemoryAccounting
import Jaune.FrameRun.CheckedBasic
import Jaune.FrameRun.CheckedAdequacy
import Jaune.FrameRun.CheckedPrefix
import Jaune.FrameRun.CheckedUnique
import Jaune.FrameRun.CheckedViews
import Jaune.FrameRun.CheckedDecompose
import Jaune.FrameRun.CheckedSettlementViews
import Jaune.FrameRun.CheckedOrder

/-! Axiom audit for the u66 Checked ports (memory accounting, sufficiency walk, derivation, frame runs):
each module's constants reach only the three standard axioms. -/

#union_axioms_of_modules Jaune.CheckedSufficiencyWalk
#union_axioms_of_modules Jaune.MessageCall.CheckedMemoryCosts
#union_axioms_of_modules Jaune.MessageCall.CheckedPlainMemory
#union_axioms_of_modules Jaune.MessageCall.CheckedMessageMemory
#union_axioms_of_modules Jaune.MessageCall.CheckedMemoryAccounting
#union_axioms_of_modules Jaune.FrameRun.CheckedBasic
#union_axioms_of_modules Jaune.FrameRun.CheckedAdequacy
#union_axioms_of_modules Jaune.FrameRun.CheckedPrefix
#union_axioms_of_modules Jaune.FrameRun.CheckedUnique
#union_axioms_of_modules Jaune.FrameRun.CheckedViews
#union_axioms_of_modules Jaune.FrameRun.CheckedDecompose
#union_axioms_of_modules Jaune.FrameRun.CheckedSettlementViews
#union_axioms_of_modules Jaune.FrameRun.CheckedOrder
#expect_axioms Jaune.Checked.Frame.Run.exec_iff [Classical.choice, Quot.sound, propext]
