import AxiomAudit
import Jaune.FrameRun.SettlementViews
import Jaune.FrameRun.Adequacy
import Jaune.FrameRun.Order
import Jaune.MessageCall.SpawnFacts
import Jaune.MessageCall.MemoryAccounting
import Jaune.SymbolicArithmetic
import Examples.Execution
import Examples.Arithmetic

/-!
# Destination axiom audit for the canonical execution surface

Fifty-two rows, each with the exact expected set
`Classical.choice, Quot.sound, propext`. The first thirty-seven are the approved
rows of user decision `jaune-destination-axiom-pins-20260924`, as amended by user
decision `jsn-g1-packet` (one row removed, one re-pointed to
`Jaune.Frame.settlementCommits_iff`) and by user decision `jsn-g2b-u78-accept`,
which re-pointed 26 rows to the declarations that replaced theirs at G2b.
Thirteen restate obligations Blanc already pinned, two under the declarations'
former `Blanc.*` names; the fourteenth, `benvAfterTransfer_stat`, needs no row
(the value transfer now returns only a world, and `Frame.enter_run_context`
covers entry), and its place audits the run constructor `Frame.Run.stop`.
The rest bind the canonical `Frame.Run` type and its constructors, adequacy,
the run order and node views, symbolic PUSH rules and the PUSH example. The last
fifteen, added with the declarations they audit (unit
`jaune-c6-surface-20260924`), bind the symbolic arithmetic rules and the
composed arithmetic example. `scripts/assurance-manifest.json` records each
row's provenance, and `scripts/check-assurance-manifest.py` keeps the two in
step. Expectations are reviewed data: nothing here learns a set from
the candidate. The walk is `Jaune.AxiomAudit.walk`, never
`Lean.collectAxioms`. The default `Assurance` target builds this file, so an
ordinary build fails on any mismatch.
-/

#expect_axioms Jaune.Frame.raw_commits_of_settlementCommits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.descendantFrames_callRan_of_settles [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.descendantFrames_callRan_of_not_settles [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.descendantFrames_callRan_create_codeDepositRollback [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.committedFrames_eq_nil_of_not_commits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.settlementCommits_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.settlementCommits_ofCall_of_raw_commits [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.retainedNodes_callRan_of_settles [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.retainedNodes_callRan_of_not_settles [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.stop [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.enter_run_context [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.prepareCall.step_spawn_context [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.prepareCreate.step_spawn_context [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.MessageOp.step_spawn_context [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.halt [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.next [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.callDoneEnd [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.callDone [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.callRanEnd [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.callRan [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.exec_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.strongRec [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.Node.strongRec [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.Node.parentNext_unique [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.rawNodes [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Frame.Run.retainedNodes [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicPush.step_success [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicPush.step_outOfGas [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicPush.step_stackOverflow [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicPush.prepend [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Execution.execution [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Execution.interpreter [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Execution.final_stack [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Execution.final_gas [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Execution.final_world [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Execution.final_substate_trail [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicArithmetic.step_eq [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicArithmetic.step_success [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicArithmetic.step_outOfGas [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicArithmetic.step_stackUnderflow [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.SymbolicArithmetic.prepend [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.execution [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.next [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.result [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.interpreter [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.final_stack [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.final_sum [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.final_gas [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.final_world [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.final_substate_trail [Classical.choice, Quot.sound, propext]
#expect_axioms Examples.Arithmetic.concrete [Classical.choice, Quot.sound, propext]
