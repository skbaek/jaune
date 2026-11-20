import AxiomAudit
import Jaune.MessageCall.CheckedGasFacts
import Jaune.MessageCall.CheckedPlainGasFacts
import Jaune.MessageCall.CheckedMessageGasFacts
import Jaune.MessageCall.CheckedStepGasBound
import Jaune.MessageCall.CheckedPartsGas
import Jaune.MessageCall.CheckedTotality
import Jaune.MessageCall.CheckedStateGasOps
import Jaune.MessageCall.CheckedStateGasZero
import Jaune.MessageCall.CheckedRunInvariants
import Jaune.MessageCall.CheckedDriverInvariants
import Jaune.MessageCall.CheckedSpawnFacts
import Jaune.MessageCall.CheckedResumeFacts
import Jaune.MessageCall.CheckedCanonical
import Examples.CheckedShapePilot

/-! Axiom audit for the u65 Checked ports (gas, totality, invariants, S3, spawn, canonicality,
pilot): each module's constants reach only the three standard axioms. -/

#union_axioms_of_modules Jaune.MessageCall.CheckedGasFacts
#union_axioms_of_modules Jaune.MessageCall.CheckedPlainGasFacts
#union_axioms_of_modules Jaune.MessageCall.CheckedMessageGasFacts
#union_axioms_of_modules Jaune.MessageCall.CheckedStepGasBound
#union_axioms_of_modules Jaune.MessageCall.CheckedPartsGas
#union_axioms_of_modules Jaune.MessageCall.CheckedTotality
#union_axioms_of_modules Jaune.MessageCall.CheckedStateGasOps
#union_axioms_of_modules Jaune.MessageCall.CheckedStateGasZero
#union_axioms_of_modules Jaune.MessageCall.CheckedRunInvariants
#union_axioms_of_modules Jaune.MessageCall.CheckedDriverInvariants
#union_axioms_of_modules Jaune.MessageCall.CheckedSpawnFacts
#union_axioms_of_modules Jaune.MessageCall.CheckedResumeFacts
#union_axioms_of_modules Jaune.MessageCall.CheckedCanonical
#union_axioms_of_modules Examples.CheckedShapePilot
#expect_axioms Jaune.Checked.step_gasBound [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageOp.step_gas [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.execFueled_run_sufficientFuel [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.exec_eq_of_run [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.exec_ok [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.exec_stateGasZero [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.RunInvariants.exec_inv [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Running.Reaches.resume_failed [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Running.Reaches.resume_success [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.resume_failed [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.resume_trail [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.returnedMachine_failed_call [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.returnedMachine_failed_create [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.step_spawn_kindCoherent [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.startState_accessedAddresses [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.enter_run_accessedAddresses [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageOp.step_spawn_accessedAddresses [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.step_spawn_accessedAddresses [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.step_spawn_start_warm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.step_spawn_child_warm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.step_spawn_create_enter_warm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.step_spawn_enter_context [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.runTop_canonical [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.ShapePilot.Checked.call_return_survival [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.ShapePilot.Checked.create_return_survival [Classical.choice, Quot.sound, propext]
