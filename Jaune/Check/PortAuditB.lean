import AxiomAudit
import Jaune.SufficiencyWalk
import Jaune.MessageCall.MemoryCosts
import Jaune.MessageCall.PlainMemory
import Jaune.MessageCall.MessageMemory
import Jaune.MessageCall.MemoryAccounting
import Jaune.FrameRun.Basic
import Jaune.FrameRun.Adequacy
import Jaune.FrameRun.Prefix
import Jaune.FrameRun.Unique
import Jaune.FrameRun.Views
import Jaune.FrameRun.Decompose
import Jaune.FrameRun.SettlementViews
import Jaune.FrameRun.Order

/-! Axiom audit for the u66 Checked ports (memory accounting, sufficiency walk, derivation, frame runs):
each module's constants reach only the three standard axioms. -/

#union_axioms_of_modules Jaune.SufficiencyWalk
#union_axioms_of_modules Jaune.MessageCall.MemoryCosts
#union_axioms_of_modules Jaune.MessageCall.PlainMemory
#union_axioms_of_modules Jaune.MessageCall.MessageMemory
#union_axioms_of_modules Jaune.MessageCall.MemoryAccounting
#union_axioms_of_modules Jaune.FrameRun.Basic
#union_axioms_of_modules Jaune.FrameRun.Adequacy
#union_axioms_of_modules Jaune.FrameRun.Prefix
#union_axioms_of_modules Jaune.FrameRun.Unique
#union_axioms_of_modules Jaune.FrameRun.Views
#union_axioms_of_modules Jaune.FrameRun.Decompose
#union_axioms_of_modules Jaune.FrameRun.SettlementViews
#union_axioms_of_modules Jaune.FrameRun.Order
#expect_axioms Jaune.Frame.Run.exec_iff [Classical.choice, Quot.sound, propext]
