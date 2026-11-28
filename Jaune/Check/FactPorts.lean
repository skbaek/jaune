import AxiomAudit
import Jaune.MessageCall.KeccakFacts
import Jaune.MessageCall.StaticcallEffects
import Jaune.MessageCall.NativePrecompile
import Jaune.MessageCall.MessageExecution
import Jaune.MessageCall.AccountWriteFacts
import Jaune.Run.PrepareFacts
import Jaune.SignedWord

/-! Axiom audit for the jsn-u97 fact ports (the KECCAK256 reference digest, the STATICCALL run
effects and native entry, and the message-execution entry and outcome forms over the checked
frame): each module's constants reach only the three standard axioms. -/

#union_axioms_of_modules Jaune.MessageCall.KeccakFacts
#union_axioms_of_modules Jaune.MessageCall.StaticcallEffects
#union_axioms_of_modules Jaune.MessageCall.NativePrecompile
#union_axioms_of_modules Jaune.MessageCall.MessageExecution
#expect_axioms Jaune.Memory.keccakReadRun_eq_keccak_read [Quot.sound, propext]
#expect_axioms Jaune.MemoryEffect.apply_digest [Quot.sound, propext]
#expect_axioms Jaune.PlainOp.runCore_keccak256_eq_reference [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.NextOp.staticcall_run_effects [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.NextOp.call_run_effects [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.NextOp.call_run_stack [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.NextOp.callcode_run_stack [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.NextOp.delegatecall_run_stack [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.NextOp.create_run_stack [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.NextOp.create2_run_stack [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.MessageOp.step_staticcall_not_run_of_precompile [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.MessageExecution.runTop_eq_settle_exec_of_enter [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.MessageExecution.enterWith_eq_run_of_notPrecompile [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.MessageExecution.enterWith_eq_run_of_noCodeAddress [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.MessageExecution.enterWith_eq_run_of_disablePrecompiles [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.MessageExecution.settle_ok_call [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.MessageExecution.settle_revert [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.MessageExecution.settle_halt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.MessageExecution.worldAfter_of_failed [Classical.choice, Quot.sound, propext]

-- G2b ports requested by the Blanc-ledger re-cite (jsn-u95): the beneficiary-credit protection
-- facts over the checked frame state and the kind coherence of the native top-level preparation.
#union_axioms_of_modules Jaune.MessageCall.AccountWriteFacts
#union_axioms_of_modules Jaune.Run.PrepareFacts
#expect_axioms Jaune.State.Protected.creditBeneficiary [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.State.creditBeneficiary_storage_of_protected [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.TopLevel.prepare_kindCoherent [Classical.choice, Quot.sound, propext]

-- The number meaning of the bit and signed word operations (`jaune-word-bridge`): every public
-- fact of the two modules, each at the set its build reports.
#union_axioms_of_modules Jaune.WordBits
#union_axioms_of_modules Jaune.SignedWord
#expect_axioms Jaune.U128.toNat_and [Quot.sound, propext]
#expect_axioms Jaune.U128.toNat_or [Quot.sound, propext]
#expect_axioms Jaune.U128.toNat_xor [Quot.sound, propext]
#expect_axioms Jaune.U128.toNat_complement [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.toNat_and [Quot.sound, propext]
#expect_axioms Jaune.U256.toNat_or [Quot.sound, propext]
#expect_axioms Jaune.U256.toNat_xor [Quot.sound, propext]
#expect_axioms Jaune.U256.toNat_complement [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U128.toNat_shiftRight [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U128.toNat_shiftLeft [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.toNat_shiftRight [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.toNat_shiftLeft [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.shiftRight_eq_zero_of_le [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.shiftLeft_eq_zero_of_le [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.UInt8.toNat_toU256 [Quot.sound, propext]
#expect_axioms Jaune.U256.toNat_getD_toBytes [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.toNat_toU256_getD_toBytes [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Nat.two_pow_sub_two_pow_eq_shiftLeft [propext]
#expect_axioms Jaune.U256.toNat_max_shiftLeft [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.toNat_max_shiftRight [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Nat.two_pow_sub_two_pow_or [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.toNat_signextend [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.toInt_lt [Quot.sound, propext]
#expect_axioms Jaune.U256.le_toInt [Quot.sound, propext]
#expect_axioms Jaune.U256.isNegative_eq_true_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.isNegative_eq_true_iff_toInt_neg [Classical.choice,
 Quot.sound,
 propext]
#expect_axioms Jaune.U256.signedLt_iff_toInt_lt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.signedGt_iff_toInt_lt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.sltCheck_ne_zero_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.sltCheck_eq_zero_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.sgtCheck_ne_zero_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.sgtCheck_eq_zero_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.toNat_arithmeticShiftRight [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.toInt_arithmeticShiftRight [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.toInt_signextend [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.toInt_sdiv [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.U256.toInt_smod [Classical.choice, Quot.sound, propext]
