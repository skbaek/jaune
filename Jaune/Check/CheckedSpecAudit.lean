import AxiomAudit
import Jaune.Bridge.G2b.PrecompileInput
import Jaune.PrecompileInputFacts
import Jaune.Bridge.G2b.CheckedContext

/-! Axiom audit for the G2b Checked specification completion (u71): the precompile-input bridge
and its wrappers, and the output-length facts ported to the precompile input. -/

#union_axioms_of_modules Jaune.PrecompileInput
#union_axioms_of_modules Jaune.PrecompileInputFacts
#union_axioms_of_modules Jaune.Bridge.G2b.PrecompileInput
#expect_axioms Jaune.Precompile.run_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.chargeGas_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.ecrecover_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.sha256_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.ripemd160_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.identity_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.modexp_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.ecAdd_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.ecMul_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.ecPairing_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.blake2f_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.pointEvaluation_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.bls12G1Add_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.bls12G1Msm_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.bls12G2Add_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.bls12G2Msm_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.bls12PairingCheck_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.bls12MapFpToG1_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.bls12MapFp2ToG2_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.p256Verify_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.run_ok_output_length_lt_two_pow_160 [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.modexp_ok_output_length_lt_two_pow_160 [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.modexp_ok_output_length_le [Quot.sound, propext]
#expect_axioms Jaune.Precompile.modexp_ok_selected_cost [Quot.sound, propext]
#expect_axioms Jaune.Precompile.identity_ok_output_and_cost []
#union_axioms_of_modules Jaune.MessageCall.CheckedContext
#union_axioms_of_modules Jaune.Bridge.G2b.CheckedContext
#expect_axioms Jaune.CallContext.toChecked_eq_of_reads [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.CallContext.toChecked_originalState [Classical.choice, Quot.sound, propext]
