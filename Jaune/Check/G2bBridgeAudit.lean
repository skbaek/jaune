import AxiomAudit
import Jaune.Bridge.G2b.CheckedTop
import Jaune.Bridge.G2b.CheckedViews
import Jaune.Bridge.G2b.CheckedTraceJson
import Jaune.Bridge.G2b.PrecompileInput
import Jaune.Bridge.Memory
import Jaune.Transaction

/-! # The G2b bridge-ledger audit (goal `jaune-shape-and-names-v1`, X1)

One `#expect_axioms` row for every theorem the G2b entries of `scripts/bridge-ledger.json` cite,
and one `checkBridge` row (`run_cmd`) per entry.

``checkBridge `T #[`o₁, …] #[`n₁, …]`` reads the kernel type of the exact constant `T`, strips its
leading binders and `let`s, and requires an `Eq` or an `Iff` with one side naming every `nᵢ` and
none of the `oⱼ`, and the other side naming every `oⱼ` and none of the `nᵢ`. The names are
the ledger entry's `old.at_tag` and `new.names`, resolved exactly. The ledger checker's Mode A
only checks that those names are declared (review finding 7), so this row is what ties each
entry's theorem to the two definitions it is said to relate. Hypotheses are not inspected:
the entry's notes state them.

`Checked.TopLevel.runNative_observe_waiting` is the one composed statement here: the native
top-level run against the waiting `TopLevel.run`, through the two bridge steps
`runNative_observe` and `run_observe` (which meet at the bridge-side `Checked.TopLevel.run`). -/

namespace Jaune.Check.G2bBridgeAudit

open Lean Elab Command Meta

/-- The constants each side of the statement of `thm` names, after its binders and `let`s. -/
def statementSides (thm : Name) : MetaM (Array Name × Array Name) := do
  let info ← getConstInfo thm
  forallTelescope info.type fun _ body => do
    let body ← zetaReduce body
    let body := body.consumeMData
    if let some (_, l, r) := body.eq? then
      return (l.getUsedConstants, r.getUsedConstants)
    if let some (l, r) := body.iff? then
      return (l.getUsedConstants, r.getUsedConstants)
    throwError "checkBridge: the statement of {thm} is neither an equation nor an iff"

/-- One orientation of the bridge: `here` names every name of `want` and none of `avoid`. -/
def sideHolds (here : Array Name) (want avoid : Array Name) : Bool :=
  want.all here.contains && !avoid.any here.contains

/-- One bridge row: the statement of `name` relates exactly `olds` (the entry's `old.at_tag`) and
`news` (its `new.names`). Rows call it through `run_cmd`, a command form the N4 capture records;
the capture refuses unregistered `#` commands. -/
def checkBridge (name : Name) (olds news : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  for n in #[name] ++ olds ++ news do
    unless env.contains n do throwError "checkBridge: unknown declaration {n}"
  if olds.isEmpty || news.isEmpty then
    throwError "checkBridge: {name} needs at least one old and one new name"
  let (l, r) ← liftTermElabM (statementSides name)
  let ok := (sideHolds l news olds && sideHolds r olds news) ||
    (sideHolds r news olds && sideHolds l olds news)
  unless ok do
    throwError "BRIDGE mismatch for {name}: expected one side to name exactly the new side {news} \
      and the other the old side {olds}; the left names {l.filter (fun c => olds.contains c || news.contains c)}, \
      the right {r.filter (fun c => olds.contains c || news.contains c)}"
  logInfo m!"BRIDGE OK {name}: {olds} ↔ {news}"

end Jaune.Check.G2bBridgeAudit

namespace Jaune.Checked.TopLevel

/-- **The top-level message run.** For every message whose waiting preparation succeeds, the
native run on the message's native input, read back through the waiting observation of that
preparation, is the waiting `TopLevel.run`, whole result. -/
theorem runNative_observe_waiting (msg : Msg) (prepared : Jaune.TopLevel.Preparation)
    (hp : Jaune.TopLevel.prepare msg = .ok prepared) :
    (runNative (Input.ofLegacy msg)).map (observe msg prepared) = Jaune.TopLevel.run msg := by
  rw [runNative_observe, run_of_prepare_ok hp]
  exact run_observe msg prepared hp

/-- On a preparation fault both runs return that fault. -/
theorem runNative_of_prepare_error {msg : Msg} {fault : Fault}
    (hp : Jaune.TopLevel.prepare msg = .error fault) :
    runNative (Input.ofLegacy msg) = .error fault ∧ Jaune.TopLevel.run msg = .error fault := by
  refine ⟨by rw [runNative_observe, run_of_prepare_error hp], ?_⟩
  rw [Jaune.TopLevel.run, hp]
  rfl

end Jaune.Checked.TopLevel

/-! ## Axiom rows

The W6a memory squares use no choice, so their entries cite the union row of their module, which
allows a subset of the standard axioms; their exact sets are stated below as well. -/

#union_axioms_of_modules Jaune.Bridge.Memory


#expect_axioms Jaune.Checked.stateTransitionCoreE_observe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.applyBody_initBlockEnvironment [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.applyBody_observe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Transaction.run_observe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.TopLevel.runNative_observe_waiting [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.TopLevel.runNative_of_prepare_error [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.TopLevel.runNative_observe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.TopLevel.run_observe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.processSystemTransaction_observe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.processCheckedSystemTransaction_observe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Body.step_observe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Body.importer_observe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.runTop_square [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.exec_square [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.step_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.initBlockContext_observe [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Memory.write_toMem [Quot.sound, propext]
#expect_axioms Jaune.Memory.read_toMem [Quot.sound, propext]
#expect_axioms Jaune.Memory.extend_toMem [Quot.sound, propext]
#expect_axioms Jaune.Precompile.run_ofEvm [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.rawNodes_w1 [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.retainedNodes_w1 [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.committedFrames_w1 [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Checked.Frame.Run.prefix_w1_iff [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2b.CheckedTrace.runFrame_nativeJson [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2b.CheckedTrace.runDirectFrame_nativeJson [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.Bridge.G2b.CheckedTrace.runNativeTransaction_nativeJson [Classical.choice, Quot.sound, propext]
#expect_axioms Jaune.stateTransitionCanonical_eq [Classical.choice, Quot.sound, propext]

/-! ## Bridge rows: each entry's theorem relates exactly its old side at the tag and its new names -/

run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.stateTransitionCoreE_observe #[`Jaune.stateTransitionCoreE] #[`Jaune.Checked.stateTransitionCoreE]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.applyBody_initBlockEnvironment #[`Jaune.applyBody] #[`Jaune.Checked.applyBody]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.applyBody_observe #[`Jaune.applyBody] #[`Jaune.Checked.applyBody]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.Transaction.run_observe #[`Jaune.Transaction.run] #[`Jaune.Checked.Transaction.run]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.TopLevel.runNative_observe_waiting #[`Jaune.TopLevel.run] #[`Jaune.Checked.TopLevel.runNative]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.processSystemTransaction_observe #[`Jaune.processSystemTransaction] #[`Jaune.Checked.processSystemTransaction]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.processCheckedSystemTransaction_observe #[`Jaune.processCheckedSystemTransaction] #[`Jaune.Checked.processCheckedSystemTransaction]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.Body.step_observe #[`Jaune.Body.step] #[`Jaune.Checked.Body.step]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.Body.importer_observe #[`Jaune.Body.importer] #[`Jaune.Checked.Body.importer]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.Frame.runTop_square #[`Jaune.Frame.runTop] #[`Jaune.Checked.Frame.runTop]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.exec_square #[`Jaune.exec] #[`Jaune.Checked.exec]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.step_ofEvm #[`Jaune.Evm.step] #[`Jaune.Checked.step]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.initBlockContext_observe #[`Jaune.initBlockEnvironment] #[`Jaune.Checked.initBlockContext]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Memory.write_toMem #[`Jaune.Mem.write] #[`Jaune.Memory.write]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Memory.read_toMem #[`Jaune.Mem.read] #[`Jaune.Memory.read]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Memory.extend_toMem #[`Jaune.Mem.extend] #[`Jaune.Memory.extend]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Precompile.run_ofEvm #[`Jaune.precompileRun] #[`Jaune.Precompile.run]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.Frame.Run.rawNodes_w1 #[`Jaune.Exec.rawNodes] #[`Jaune.Checked.Frame.Run.rawNodes]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.Frame.Run.retainedNodes_w1 #[`Jaune.Exec.retainedNodes] #[`Jaune.Checked.Frame.Run.retainedNodes]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.Frame.Run.committedFrames_w1 #[`Jaune.Exec.committedFrames] #[`Jaune.Checked.Frame.Run.committedFrames]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Checked.Frame.Run.prefix_w1_iff #[`Jaune.Exec.Deriv.ParentPrefix] #[`Jaune.Checked.Frame.Run.Node.Prefix]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Bridge.G2b.CheckedTrace.runFrame_nativeJson #[`Jaune.Trace.runFrame, `Jaune.TraceJson.sink] #[`Jaune.Checked.Trace.runFrame]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Bridge.G2b.CheckedTrace.runDirectFrame_nativeJson #[`Jaune.Trace.runFrame, `Jaune.TraceJson.sink] #[`Jaune.Checked.Trace.runFrame]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.Bridge.G2b.CheckedTrace.runNativeTransaction_nativeJson #[`Jaune.TraceTransaction.runTransaction, `Jaune.TraceJson.sink] #[`Jaune.Checked.Trace.runTransaction]
run_cmd Jaune.Check.G2bBridgeAudit.checkBridge `Jaune.stateTransitionCanonical_eq #[`Jaune.stateTransitionCanonical] #[`Jaune.stateTransitionE]
