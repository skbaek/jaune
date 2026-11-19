import AxiomAudit
import Jaune.FrameRun.CheckedUnique
import Jaune.Bridge.G2b.CheckedViews
import Jaune.FrameRun.CheckedFacts
import Jaune.FrameRun.CheckedMemory
import Jaune.MessageCall.CheckedAuditedRows
import Jaune.CheckedSymbolicPush
import Jaune.CheckedSymbolicArith
import Examples.CheckedPrefix
import Examples.CheckedExecution
import Examples.CheckedArithmetic

/-!
Axiom audit for the checked view bridges and the checked counterparts of audited rows 29-80
(goal `jaune-shape-and-names-v1`, G2b, unit u72). Every new module's constants reach only the three
standard axioms; each row's checked counterpart, each proposed replacement and each view bridge is
pinned by name. `scripts/ExecutionAxioms.lean` and `scripts/assurance-manifest.json` are not
changed: these rows are the draft for the G2b decision packet.
-/

#union_axioms_of_modules Jaune.Bridge.G2b.CheckedViews
#union_axioms_of_modules Jaune.FrameRun.CheckedFacts
#union_axioms_of_modules Jaune.FrameRun.CheckedMemory
#union_axioms_of_modules Jaune.MessageCall.CheckedAuditedRows
#union_axioms_of_modules Jaune.CheckedSymbolicPush
#union_axioms_of_modules Jaune.CheckedSymbolicArith
#union_axioms_of_modules Examples.CheckedPrefix
#union_axioms_of_modules Examples.CheckedExecution
#union_axioms_of_modules Examples.CheckedArithmetic

#expect_axioms Jaune.Checked.Frame.raw_commits_of_settlementCommits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Exec.descendantFrames_runOk_of_settlementCommits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Exec.descendantFrames_runOk_of_not_settlementCommits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Exec.descendantFrames_runOk_create_codeDepositRollback [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Exec.committedFrames_eq_nil_of_not_commits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.settlementCommits_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.settlementCommits_ofCall_of_raw_commits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Exec.retainedNodes_runOk_of_settlementCommits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Exec.retainedNodes_runOk_of_not_settlementCommits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.enter_run_context [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.enter_run_benvStat [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.genericCall.step_spawn_benvStat [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.genericCreate.step_spawn_benvStat [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageOp.step_spawn_benvStat [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.genericCall.step_spawn_context [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.genericCreate.step_spawn_context [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.MessageOp.step_spawn_context [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.stop [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.halt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.next [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.callDoneEnd [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.callDone [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.callRanEnd [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.callRan [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.exec_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.strong_rec [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.Node.strongRec [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.Prefix.unique [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.rawNodes [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.retainedNodes [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.SymbolicPush.step_success [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.SymbolicPush.step_outOfGas [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.SymbolicPush.step_stackOverflow [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.SymbolicPush.prepend [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Execution.execution [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Execution.interpreter [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Execution.final_stack [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Execution.final_gas [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Execution.final_world [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Execution.final_substate_trail [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.SymbolicArith.step_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.SymbolicArith.step_success [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.SymbolicArith.step_outOfGas [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.SymbolicArith.step_stackUnderflow [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.SymbolicArith.prepend [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Arithmetic.execution [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Arithmetic.next [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Arithmetic.result [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Arithmetic.interpreter [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Arithmetic.final_stack [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Arithmetic.final_sum [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Arithmetic.final_gas [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Arithmetic.final_world [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Arithmetic.final_substate_trail [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Checked.Arithmetic.concrete [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.rawNodes_w1 [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.retainedNodes_w1 [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.committedFrames_w1 [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.prefix_w1_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.rawNodes_toLegacy [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.retainedNodes_toLegacy [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.committedFrames_toLegacy [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.prefix_toLegacy_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.rawNodes_bridge [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.retainedNodes_bridge [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.committedFrames_bridge [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.descendantFrames_bridge [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.parentPrefix_bridge [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.settledGasLe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.memory_accounting_output [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.Node.Prefix.trans [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.Node.Prefix.lt [Classical.choice, Quot.sound, propext]
