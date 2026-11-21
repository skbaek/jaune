import AxiomAudit
import Jaune.PrecompileInputFacts
import Jaune.MessageCall.Context

/-! Axiom audit for the G2b Checked specification completion (u71): the precompile-input bridge
and its wrappers, and the output-length facts ported to the precompile input. -/

#union_axioms_of_modules Jaune.PrecompileInput
#union_axioms_of_modules Jaune.PrecompileInputFacts
#expect_axioms Jaune.Precompile.run_ok_output_length_lt_two_pow_160 [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.modexp_ok_output_length_lt_two_pow_160 [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Precompile.modexp_ok_output_length_le [Quot.sound, propext]
#expect_axioms Jaune.Precompile.modexp_ok_selected_cost [Quot.sound, propext]
#expect_axioms Jaune.Precompile.identity_ok_output_and_cost []
#union_axioms_of_modules Jaune.MessageCall.Context
