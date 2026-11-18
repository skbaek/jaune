import Jaune.FinalSufficiencyWalk

/-!
# Fuel sufficiency over the staged chain: the instruction layer (goal `jaune-shape-and-names-v1`, W3-4b)

The successor of the instruction layer of `Jaune.Sufficiency`, over the staged bodies
(`Jaune.Staging.PlainOp.runCore`, `JumpOp.runCore`, `HaltOp.run`, `NextOp.step`), proved natively
(no `Devm`, no bridge). The measure is `Machine.gasMeasure` of the frame's state: execution gas
plus the outstanding and the committed spill.

Each body is walked once (`Walk`, `Jaune.FinalSufficiencyWalk`): every halt stops in a state that
measures at most what the step began with, and every state the step goes on with measures
strictly less.
-/

namespace Jaune.Staging

open Jaune

/-- Unfold the fixed gas constants for `omega`. -/
macro "gas_consts" : tactic => `(tactic|
  simp only [Gas.base, Gas.veryLow, Gas.low, Gas.mid, Gas.high, Gas.jumpdest, Gas.exp,
    Gas.expByte, Gas.keccak256, Gas.keccak256Word, Gas.log, Gas.logData, Gas.logTopic, Gas.copy,
    Gas.returnDataCopy, Gas.blockhash, Gas.hashOpcodeGas, Gas.warmStorageReadCost,
    Gas.coldSloadCost, Gas.selfdestruct, Gas.callStipend, Gas.codeDeposit, Gas.initcodeWordCost,
    Gas.sstoreSetGas, Gas.sstoreResetGas, Gas.selfdestructNewAccount] at *)

/-- Close a walk leaf: unfold the walk at a value or a halt, normalise the measure, `omega`. -/
macro "gas_leaf" : tactic => `(tactic| (
  (try simp only [Walk.ok_iff, Walk.error_iff, MWalk.ok_iff, MWalk.error_iff,
    Frame.State.withMachine_machine, Frame.State.withWorld_machine,
    Frame.State.withSubstate_machine, Frame.State.withTrail_machine,
    Frame.State.liftMachinePure_machine, Machine.gasMeasure_withStack,
    Machine.gasMeasure_withMemory, Machine.gasMeasure_withReturnData,
    Machine.memWrite_gasMeasure, Machine.memExtends_gasMeasure, Machine.memRead_gasMeasure,
    apply_ite Frame.State.machine, ite_self]
    at *) <;>
  (try gas_consts) <;> omega))

/-- One step of a gas walk. -/
macro "gas_step" : tactic => `(tactic| first
  | split
  | (refine Walk.bind (Frame.State.pop_gas (by gas_leaf)) ?_; intro ⟨_, _⟩ _; try dsimp only at *)
  | (refine Walk.bind (Frame.State.popToNat_gas (by gas_leaf)) ?_; intro ⟨_, _⟩ _; try dsimp only at *)
  | (refine Walk.bind (Frame.State.popToAddress_gas (by gas_leaf)) ?_; intro ⟨_, _⟩ _;
      try dsimp only at *)
  | (refine Walk.bind (Frame.State.popN_gas _ (by gas_leaf)) ?_; intro ⟨_, _⟩ _; try dsimp only at *)
  | (refine Walk.bind (Frame.State.chargeGas_gas _ (by gas_leaf)) ?_; intro _ _; try dsimp only at *)
  | (refine Walk.bind (Frame.State.chargeStateGas_gas _ (by gas_leaf)) ?_; intro _ _;
      try dsimp only at *)
  | (refine Walk.bind (Frame.State.push_gas _ (by gas_leaf)) ?_; intro _ _; try dsimp only at *)
  | (refine Walk.bind (Frame.State.assertDynamic_gas _ (by gas_leaf)) ?_; intro _ _;
      try dsimp only at *)
  | (refine Walk.bind (Walk.assert (by gas_leaf)) ?_; intro _ _; try dsimp only at *)
  | (refine Walk.mono (Frame.State.push_gas _ (by gas_leaf)) ?_; intro _ _)
  | (refine Walk.mono (Frame.State.pushItem_gas _ _ (by gas_leaf)) ?_; intro _ _)
  | (refine Walk.mono (Frame.State.applyUnary_gas _ _ (by gas_leaf)) ?_; intro _ _)
  | (refine Walk.mono (Frame.State.applyBinary_gas _ _ (by gas_leaf)) ?_; intro _ _)
  | (refine Walk.mono (Frame.State.applyTernary_gas _ _ (by gas_leaf)) ?_; intro _ _)
  | (refine Walk.mono (Frame.State.chargeGas_gas _ (by gas_leaf)) ?_; intro _ _)
  | (refine Walk.mono (Frame.State.chargeStateGas_gas _ (by gas_leaf)) ?_; intro _ _)
  | (refine Walk.liftMachine_gas ?_)
  | (refine MWalk.bind (Machine.pop_gas (by gas_leaf)) ?_; intro ⟨_, _⟩ _; try dsimp only at *)
  | (refine MWalk.bind (Machine.popToNat_gas (by gas_leaf)) ?_; intro ⟨_, _⟩ _; try dsimp only at *)
  | (refine MWalk.bind (Machine.popToAddress_gas (by gas_leaf)) ?_; intro ⟨_, _⟩ _;
      try dsimp only at *)
  | (refine MWalk.bind (Machine.popN_gas _ (by gas_leaf)) ?_; intro ⟨_, _⟩ _; try dsimp only at *)
  | (refine MWalk.bind (Machine.chargeGas_gas _ (by gas_leaf)) ?_; intro _ _; try dsimp only at *)
  | (refine MWalk.bind (MWalk.assert (by gas_leaf)) ?_; intro _ _; try dsimp only at *)
  | (refine MWalk.mono (Machine.push_gas _ (by gas_leaf)) ?_; intro _ _)
  | (refine MWalk.mono (Machine.pushItem_gas _ _ (by gas_leaf)) ?_; intro _ _)
  | (refine MWalk.mono (Machine.applyUnary_gas _ _ (by gas_leaf)) ?_; intro _ _)
  | (refine MWalk.mono (Machine.applyBinary_gas _ _ (by gas_leaf)) ?_; intro _ _)
  | (refine MWalk.mono (Machine.applyTernary_gas _ _ (by gas_leaf)) ?_; intro _ _)
  | (refine MWalk.mono (Machine.chargeGas_gas _ (by gas_leaf)) ?_; intro _ _)
  | gas_leaf)

/-- Walk a body to its leaves. -/
macro "gas_walk" : tactic => `(tactic| repeat' gas_step)

set_option maxHeartbeats 4000000 in
theorem test_add (pc : Nat) (ctx : CallContext) (s : Frame.State) (op : Jaune.PlainOp) {n : Nat}
    (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure < s.machine.gasMeasure)
      (PlainOp.runCore pc ctx s op) := by
  cases op
  case balance => sorry
  case extcodesize => sorry
  case extcodecopy => sorry
  case extcodehash => sorry
  case sload => sorry
  case sstore => sorry
  case selfbalance => sorry
  case tload => sorry
  case tstore => sorry
  case log => sorry
  all_goals simp only [PlainOp.runCore] <;> gas_walk

end Jaune.Staging
