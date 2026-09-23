import AxiomAudit
import Jaune.ExecChronology
import Jaune.MessageExecution
import Jaune.SymbolicArith
import Examples.Execution
import Examples.Arithmetic

/-!
# Destination axiom audit for the canonical execution surface

Fifty-three rows, each with the exact expected set
`Classical.choice, Quot.sound, propext`. The first thirty-eight are the approved
rows of user decision `jaune-destination-axiom-pins-20260924`: fifteen restate
obligations Blanc already pinned under the declarations' former `Blanc.*` names;
the rest bind the canonical `Exec` type and its constructors, adequacy,
derivation operations, symbolic PUSH rules and the PUSH example. The last
fifteen, added with the declarations they audit (unit
`jaune-c6-surface-20260924`), bind the symbolic arithmetic rules and the
composed arithmetic example. `scripts/assurance-manifest.json` records each
row's provenance, and `scripts/check-assurance-manifest.py` keeps the two in
step. Expectations are reviewed data: nothing here learns a set from
the candidate. The walk is `Jaune.AxiomAudit.auditFullAxioms`, never
`Lean.collectAxioms`. The default `Assurance` target builds this file, so an
ordinary build fails on any mismatch.
-/

#expect_axioms Jaune.Frame.raw_commits_of_settlementCommits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.descendantFrames_runOk_of_settlementCommits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.descendantFrames_runOk_of_not_settlementCommits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.descendantFrames_runOk_create_codeDepositRollback [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.committedFrames_eq_nil_of_not_commits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.ProcessMessage.settlementCommits_of_some_ok_clean [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.settlementCommits_ofCall_of_raw_commits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.retainedNodes_runOk_of_settlementCommits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.retainedNodes_runOk_of_not_settlementCommits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.benvAfterTransfer_stat [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.enter_run_benvStat [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.RunFrame.benvStat_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.genericCall.step_spawn_benvStat [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.genericCreate.step_spawn_benvStat [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Xinst.step_spawn_benvStat [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.halt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.cont [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.doneErr [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.doneOk [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.runErr [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.runOk [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.exec_iff_exec_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.strong_rec [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.Deriv.strongRec [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.Deriv.ParentStep.unique [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.rawNodes [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Exec.retainedNodes [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicPush.step_success [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicPush.step_outOfGas [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicPush.step_stackOverflow [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicPush.prepend [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Execution.execution [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Execution.interpreter [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Execution.final_stack [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Execution.final_gas [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Execution.final_world [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Execution.final_meta [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicArith.step_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicArith.step_success [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicArith.step_outOfGas [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicArith.step_stackUnderflow [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicArith.prepend [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.execution [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.next [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.result [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.interpreter [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.final_stack [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.final_sum [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.final_gas [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.final_world [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.final_meta [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.concrete [Classical.choice, Quot.sound, propext]
