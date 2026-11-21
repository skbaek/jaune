import AxiomAudit
import Jaune.FrameRun.Calls
import Jaune.FrameRun.CallsHistory
import Jaune.FrameRun.Entered
import Jaune.FrameRun.EnteredRoots
import Examples.RunCalls

/-!
Axiom audit for the run views of G2b unit U102: the calls of a frame run with their lifts, and
entered frames with their propagation and top-level bounds.
-/

#union_axioms_of_modules Jaune.FrameRun.Calls
#union_axioms_of_modules Jaune.FrameRun.CallsHistory
#union_axioms_of_modules Jaune.FrameRun.Entered
#union_axioms_of_modules Jaune.FrameRun.EnteredRoots
#union_axioms_of_modules Examples.RunCalls
#expect_axioms Jaune.Frame.Run.callsFrom_valid [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.calls_valid [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.calls_step_spawn [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.calls_childResult [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.calls_ran_eq_none_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.calls_ran_eq_some [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.calls_complete [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.calls_length [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.calls_site_mem [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.calls_frameStarts [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.frames_eq_calls [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.calls_ran_mem_rawNodes [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.keptCalls_eq_nil_of_failed [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.keptCalls_of_finished [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.keptCalls_sublist [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.mem_keptCalls [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.keptCalls_site_mem_retainedNodes [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Root.keptCalls_of_failed [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Root.keptCalls_of_success [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Root.keptCalls_sublist [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.BlockRun.exists_bodyRoots_calls [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.KeptHistory.calls_append [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.KeptHistory.keptCalls_append [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.KeptHistory.mem_calls [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Running.Entered.gasLeft_lt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.enterWith_run [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.enter_run_entered [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.step_spawn_calldata [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.step_spawn_enter_entered [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.visits_entered [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.visits_gasMeasure_lt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.frames_entered [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.calls_ran_entered [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.calls_site_gasMeasure_lt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.State.Fresh.of_machine_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.State.Fresh.chargeGas [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.State.Fresh.chargeStateGas [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.State.Fresh.commitStateGas [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.State.Fresh.preparationCharge [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.TopLevel.prepare_fresh [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.TopLevel.run_root_entered [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.TopLevel.initialCheckpoint_fresh [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.TopLevel.systemInput_fresh [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.validateTransaction_data_le [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.checkTransactionGasLimits_le [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Transaction.admit_bounds [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Transaction.prepare_fresh [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Transaction.run_root_entered [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.processSystemRun_root_entered [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.BlockRun.roots_entered [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.checkGasLimit_lt [Quot.sound, propext]
#expect_axioms Jaune.validateHeader_gasLimit_lt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.BlockRun.run_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.KeptStep.gasLimit_lt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.KeptHistory.roots_entered [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.KeptHistory.frames_entered [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.KeptHistory.calls_ran_entered [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.RunCalls.calls_length [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.RunCalls.entry_call [Classical.choice, Quot.sound, propext]
