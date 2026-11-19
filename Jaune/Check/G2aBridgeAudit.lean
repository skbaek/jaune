import AxiomAudit
import Jaune.Bridge.G2a.Block
import Jaune.Bridge.G2a.Canonical
import Jaune.Bridge.G2a.Decode
import Jaune.Bridge.G2a.Old.T8n
import Jaune.Bridge.AccountWrite
import Jaune.Bridge.Import
import Jaune.Run.BodyFacts

/-! Axiom checks for the message, transaction, body, block, decoder, settlement and import contracts at G2a. -/

#union_axioms_of_modules Jaune.Bridge.G2a
#union_axioms_of_modules Jaune.Bridge.AccountWrite
#union_axioms_of_modules Jaune.Bridge.Import

#expect_axioms Jaune.Bridge.G2a.processMessageCall_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.processTransaction_eq_b2 [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.processSystemTransaction_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.processUncheckedSystemTransaction_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.processCheckedSystemTransaction_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.runRequestContracts_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.processGeneralPurposeRequestsAt_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.processGeneralPurposeRequests_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.beaconRootsCall_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.historyStorageCall_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.applyBody_eq_of_not_split [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.applyBody_of_split [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.stateTransitionCoreE_eq_of_not_split [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.stateTransitionCoreE_of_split [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.E.stateTransitionCoreE_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.E.stateTransitionCoreE_eq_of_not_split [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.canonicalImport_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Staging.scheduledCanonicalImport_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.KeySet.clearIfEmpty_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.Old.T8n.foldTransactions_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.Old.T8n.runStateTest_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.Old.T8n.runBlockchain_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Transaction.settleRun_state [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.E.stateTransitionCoreE_difference [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.decodeTransaction_difference [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.mapM_decodeTransaction_difference [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.applyBody_difference [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2a.stateTransitionCoreE_difference [Classical.choice, Quot.sound, propext]
