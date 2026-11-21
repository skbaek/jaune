import AxiomAudit
import Jaune.MessageCall.GasFacts
import Jaune.MessageCall.PlainGasFacts
import Jaune.MessageCall.MessageGasFacts
import Jaune.MessageCall.StepGasBound
import Jaune.MessageCall.PartsGas
import Jaune.MessageCall.Totality
import Jaune.MessageCall.StateGasOps
import Jaune.MessageCall.StateGasZero
import Jaune.MessageCall.RunInvariants
import Jaune.MessageCall.DriverInvariants
import Jaune.MessageCall.SpawnFacts
import Jaune.MessageCall.ResumeFacts
import Jaune.MessageCall.Canonical
import Examples.ShapePilot

/-! Axiom audit for the u65 Checked ports (gas, totality, invariants, S3, spawn, canonicality,
pilot): each module's constants reach only the three standard axioms. -/

#union_axioms_of_modules Jaune.MessageCall.GasFacts
#union_axioms_of_modules Jaune.MessageCall.PlainGasFacts
#union_axioms_of_modules Jaune.MessageCall.MessageGasFacts
#union_axioms_of_modules Jaune.MessageCall.StepGasBound
#union_axioms_of_modules Jaune.MessageCall.PartsGas
#union_axioms_of_modules Jaune.MessageCall.Totality
#union_axioms_of_modules Jaune.MessageCall.StateGasOps
#union_axioms_of_modules Jaune.MessageCall.StateGasZero
#union_axioms_of_modules Jaune.MessageCall.RunInvariants
#union_axioms_of_modules Jaune.MessageCall.DriverInvariants
#union_axioms_of_modules Jaune.MessageCall.SpawnFacts
#union_axioms_of_modules Jaune.MessageCall.ResumeFacts
#union_axioms_of_modules Jaune.MessageCall.Canonical
#union_axioms_of_modules Examples.ShapePilot
#expect_axioms Jaune.step_gasBound [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.MessageOp.step_gas [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.execFueled_run_sufficientFuel [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.exec_eq_of_run [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.exec_ok [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.exec_stateGasZero [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.RunInvariants.exec_invariant [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Running.Reaches.resume_failed [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Running.Reaches.resume_success [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.resume_failed [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.resume_trail [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.returnedMachine_failed_call [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.returnedMachine_failed_create [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.step_spawn_kindCoherent [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.startState_accessedAddresses [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.enter_run_accessedAddresses [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.MessageOp.step_spawn_accessedAddresses [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.step_spawn_accessedAddresses [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.step_spawn_start_warm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.step_spawn_child_warm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.step_spawn_create_enter_warm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.step_spawn_enter_context [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.runTop_canonical [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.ShapePilot.call_return_survival [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.ShapePilot.create_return_survival [Classical.choice, Quot.sound, propext]
