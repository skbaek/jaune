import AxiomAudit
import Jaune.MessageCall.CheckedKeccakFacts
import Jaune.MessageCall.CheckedStaticcallEffects
import Jaune.MessageCall.CheckedNativePrecompile
import Jaune.MessageCall.CheckedMessageExecution
import Jaune.MessageCall.CheckedAccountWriteFacts
import Jaune.Run.CheckedPrepareFacts

/-! Axiom audit for the jsn-u97 fact ports (the KECCAK256 reference digest, the STATICCALL run
effects and native entry, and the message-execution entry and outcome forms over the checked
frame): each module's constants reach only the three standard axioms. -/

#union_axioms_of_modules Jaune.MessageCall.CheckedKeccakFacts
#union_axioms_of_modules Jaune.MessageCall.CheckedStaticcallEffects
#union_axioms_of_modules Jaune.MessageCall.CheckedNativePrecompile
#union_axioms_of_modules Jaune.MessageCall.CheckedMessageExecution
#expect_axioms Jaune.Checked.Memory.keccakReadRun_eq_keccak_read [Quot.sound, propext]
#expect_axioms Jaune.Checked.MemoryEffect.apply_digest [Quot.sound, propext]
#expect_axioms Jaune.Checked.PlainOp.runCore_keccak256_eq_reference [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.NextOp.staticcall_run_effects [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageOp.step_staticcall_not_run_of_precompile [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageExecution.runTop_eq_settle_exec_of_enter [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageExecution.enterWith_eq_run_of_notPrecompile [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageExecution.enterWith_eq_run_of_noCodeAddress [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageExecution.enterWith_eq_run_of_disablePrecompiles [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageExecution.settle_ok_call [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageExecution.settle_revert [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageExecution.settle_halt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageExecution.worldAfter_of_failed [Classical.choice, Quot.sound, propext]

-- G2b ports requested by the Blanc-ledger re-cite (jsn-u95): the beneficiary-credit protection
-- facts over the checked frame state and the kind coherence of the native top-level preparation.
#union_axioms_of_modules Jaune.MessageCall.CheckedAccountWriteFacts
#union_axioms_of_modules Jaune.Run.CheckedPrepareFacts
#expect_axioms Jaune.Checked.State.Protected.creditBeneficiary [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.State.creditBeneficiary_storage_of_protected [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.TopLevel.prepare_kindCoherent [Classical.choice, Quot.sound, propext]
