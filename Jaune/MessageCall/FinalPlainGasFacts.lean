import Jaune.FinalSufficiencyWalk
import Jaune.Sufficiency

/-! Gas bounds for the plain instructions over the lifetime-grouped state. A successful
step strictly decreases the machine's measure. An exceptional halt stays within the bound
supplied by the caller. -/

namespace Jaune.Staging

open Jaune

/-- Unfold the fixed gas constants for `omega`. -/
local macro "gas_consts" : tactic => `(tactic|
  simp only [Gas.base, Gas.veryLow, Gas.low, Gas.mid, Gas.high, Gas.jumpdest, Gas.exp,
    Gas.expByte, Gas.keccak256, Gas.keccak256Word, Gas.log, Gas.logData, Gas.logTopic, Gas.copy,
    Gas.returnDataCopy, Gas.blockhash, Gas.hashOpcodeGas, Gas.warmStorageReadCost,
    Gas.coldSloadCost, Gas.selfdestruct, Gas.callStipend, Gas.codeDeposit, Gas.initcodeWordCost,
    Gas.sstoreSetGas, Gas.sstoreResetGas, Gas.selfdestructNewAccount] at *)

/-- Close a walk leaf: unfold the walk at a value or a halt, normalise the measure, `omega`. -/
local macro "gas_leaf" : tactic => `(tactic| first
  | assumption
  | omega
  | (
  (try simp only [Walk.ok_iff, Walk.error_iff, MWalk.ok_iff, MWalk.error_iff,
    Frame.State.withMachine_machine, Frame.State.withWorld_machine,
    Frame.State.withSubstate_machine, Frame.State.withTrail_machine,
    Frame.State.liftMachinePure_machine, Machine.gasMeasure_withStack,
    Machine.gasMeasure_withMemory, Machine.gasMeasure_withReturnData,
    Machine.memWrite_gasMeasure, Machine.memExtends_gasMeasure, Machine.memRead_gasMeasure,
    Frame.State.recordAccountRead, Frame.State.recordStorageRead, Frame.State.addAccessedAddress,
    Frame.State.addAccessedStorageKey, Frame.State.setTransientValue,
    Frame.State.withRefund, Frame.State.setStorageValue, Frame.State.creditStateGasRefund,
    Machine.creditStateGasRefund_gasMeasure, Frame.State.memWrite, apply_ite Frame.State.machine, ite_self]
    at *) <;>
  (try gas_consts) <;> omega))

private theorem chargePositive {s : Frame.State} {n c : Nat}
    (h : s.machine.gasMeasure ≤ n) (hc : 0 < c) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure < s.machine.gasMeasure) (s.chargeGas c) := by
  apply Walk.mono (Frame.State.chargeGas_gas c h)
  intro t ht
  change t.machine.gasMeasure + c = s.machine.gasMeasure at ht
  omega

/-- One step of a gas walk. -/
local macro "gas_step" : tactic => `(tactic| with_reducible first
  | split
  | (refine Walk.bind (Frame.State.pop_gas (by gas_leaf)) ?_; intro ⟨_, _⟩ _; try dsimp only at *)
  | (refine Walk.bind (Frame.State.popToNat_gas (by gas_leaf)) ?_; intro ⟨_, _⟩ _; try dsimp only at *)
  | (refine Walk.bind (Frame.State.popToAddress_gas (by gas_leaf)) ?_; intro ⟨_, _⟩ _;
      try dsimp only at *)
  | (refine Walk.bind (Frame.State.popN_gas _ (by gas_leaf)) ?_; intro ⟨_, _⟩ _; try dsimp only at *)
  | (refine Walk.bind (chargePositive (by gas_leaf) (by
        first | apply sstoreAmsterdamGasCost_pos | apply sstoreRegimeGasCost_pos; assumption)) ?_;
     intro _ _)
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

open Lean Elab Tactic Meta in
/-- Select the walk rule using the head of the next operation. Matching against every
primitive by reduction would repeatedly unfold the calculation inside its operands. -/
elab "gas_head_step" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let onMachine := target.isAppOf ``MWalk
  unless onMachine || target.isAppOf ``Walk do throwError "not a walk"
  let x := target.appArg!.headBeta
  let bind := x.isAppOf ``Bind.bind
  let operation := if bind then (x.getArg! 4).headBeta else x
  let some head := operation.getAppFn.constName? | throwError "not a named operation"
  if head == ``Frame.State.liftMachine && !bind then
    evalTactic (← `(tactic| apply Walk.liftMachine_gas))
    return
  let (rule, arity, pair) ← match head with
    | ``Jaune.Frame.State.pop => pure (mkIdent ``Frame.State.pop_gas, 0, true)
    | ``Jaune.Frame.State.popToNat => pure (mkIdent ``Frame.State.popToNat_gas, 0, true)
    | ``Jaune.Frame.State.popToAddress => pure (mkIdent ``Frame.State.popToAddress_gas, 0, true)
    | ``Jaune.Frame.State.popN => pure (mkIdent ``Frame.State.popN_gas, 1, true)
    | ``Jaune.Frame.State.chargeGas => pure (mkIdent ``Frame.State.chargeGas_gas, 1, false)
    | ``Jaune.Frame.State.chargeStateGas => pure (mkIdent ``Frame.State.chargeStateGas_gas, 1, false)
    | ``Jaune.Frame.State.push => pure (mkIdent ``Frame.State.push_gas, 1, false)
    | ``Jaune.Frame.State.pushItem => pure (mkIdent ``Frame.State.pushItem_gas, 2, false)
    | ``Jaune.Frame.State.applyUnary => pure (mkIdent ``Frame.State.applyUnary_gas, 2, false)
    | ``Jaune.Frame.State.applyBinary => pure (mkIdent ``Frame.State.applyBinary_gas, 2, false)
    | ``Jaune.Frame.State.applyTernary => pure (mkIdent ``Frame.State.applyTernary_gas, 2, false)
    | ``Jaune.Frame.State.assertDynamic => pure (mkIdent ``Frame.State.assertDynamic_gas, 1, false)
    | ``Jaune.Machine.pop => pure (mkIdent ``Machine.pop_gas, 0, true)
    | ``Jaune.Machine.popToNat => pure (mkIdent ``Machine.popToNat_gas, 0, true)
    | ``Jaune.Machine.popToAddress => pure (mkIdent ``Machine.popToAddress_gas, 0, true)
    | ``Jaune.Machine.popN => pure (mkIdent ``Machine.popN_gas, 1, true)
    | ``Jaune.Machine.chargeGas => pure (mkIdent ``Machine.chargeGas_gas, 1, false)
    | ``Jaune.Machine.chargeStateGas => pure (mkIdent ``Machine.chargeStateGas_gas, 1, false)
    | ``Jaune.Machine.push => pure (mkIdent ``Machine.push_gas, 1, false)
    | ``Jaune.Machine.pushItem => pure (mkIdent ``Machine.pushItem_gas, 2, false)
    | ``Jaune.Machine.applyUnary => pure (mkIdent ``Machine.applyUnary_gas, 2, false)
    | ``Jaune.Machine.applyBinary => pure (mkIdent ``Machine.applyBinary_gas, 2, false)
    | ``Jaune.Machine.applyTernary => pure (mkIdent ``Machine.applyTernary_gas, 2, false)
    | ``Except.assert => pure (mkIdent (if onMachine then ``MWalk.assert else ``Walk.assert), 0, false)
    | _ => throwError "not a gas primitive"
  let fact ← match arity with
    | 0 => `($rule (by gas_leaf))
    | 1 => `($rule _ (by gas_leaf))
    | _ => `($rule _ _ (by gas_leaf))
  let combinator := mkIdent (if onMachine then (if bind then ``MWalk.bind else ``MWalk.mono)
    else (if bind then ``Walk.bind else ``Walk.mono))
  if pair then
    evalTactic (← `(tactic| (refine $combinator $fact ?_; intro ⟨_, _⟩ _; try dsimp only at *)))
  else
    evalTactic (← `(tactic| (refine $combinator $fact ?_; intro _ _; try dsimp only at *)))

local macro "gas_walk" : tactic => `(tactic| repeat' gas_step)

private abbrev PlainGas (s : Frame.State) (n : Nat) :=
  Walk (ε := ExceptionalHalt) (α := Frame.State) (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure < s.machine.gasMeasure)

private theorem logStep_gas (n : Fin 5) (ctx : CallContext) (m : Machine) {bound : Nat}
    (h : m.gasMeasure ≤ bound) :
    MWalk (·.gasMeasure ≤ bound) (fun p => p.1.gasMeasure < m.gasMeasure) (PlainOp.logStep n ctx m) := by
  unfold PlainOp.logStep
  gas_walk

private theorem log_gas (n : Fin 5) (ctx : CallContext) (s : Frame.State) {bound : Nat}
    (h : s.machine.gasMeasure ≤ bound) : PlainGas s bound (PlainOp.liftLog (PlainOp.logStep n ctx) s) := by
  have law := logStep_gas n ctx s.machine h
  unfold PlainOp.liftLog
  cases eqn : PlainOp.logStep n ctx s.machine with
  | error e => rcases e with ⟨reason, m⟩; rw [eqn] at law; exact law
  | ok result => rcases result with ⟨m, log⟩; rw [eqn] at law; exact law

private theorem balance_gas (pc : Nat) (ctx : CallContext) (s : Frame.State) {n : Nat}
    (h : s.machine.gasMeasure ≤ n) : PlainGas s n (PlainOp.runCore pc ctx s .balance) := by
  have valid := BenvStat.rules_valid ctx.block
  have cold := valid.gas.1
  cases access : ctx.block.rules.access with
  | flat g =>
    have pos := (valid.flatAccess access).1
    simp only [PlainGas, PlainOp.runCore, access]
    gas_walk
  | eip2929 =>
    simp only [PlainGas, PlainOp.runCore, access]
    gas_walk

private theorem extcodesize_gas (pc : Nat) (ctx : CallContext) (s : Frame.State) {n : Nat}
    (h : s.machine.gasMeasure ≤ n) : PlainGas s n (PlainOp.runCore pc ctx s .extcodesize) := by
  have valid := BenvStat.rules_valid ctx.block
  have cold := valid.gas.1
  cases access : ctx.block.rules.access with
  | flat g =>
    have pos := (valid.flatAccess access).2.1
    simp only [PlainGas, PlainOp.runCore, access]
    gas_walk
  | eip2929 =>
    simp only [PlainGas, PlainOp.runCore, access]
    gas_walk

private theorem extcodecopy_gas (pc : Nat) (ctx : CallContext) (s : Frame.State) {n : Nat}
    (h : s.machine.gasMeasure ≤ n) : PlainGas s n (PlainOp.runCore pc ctx s .extcodecopy) := by
  have valid := BenvStat.rules_valid ctx.block
  have cold := valid.gas.1
  cases access : ctx.block.rules.access with
  | flat g =>
    have pos := (valid.flatAccess access).2.1
    simp only [PlainGas, PlainOp.runCore, access]
    gas_walk
  | eip2929 =>
    simp only [PlainGas, PlainOp.runCore, access]
    gas_walk

private theorem extcodehash_gas (pc : Nat) (ctx : CallContext) (s : Frame.State) {n : Nat}
    (h : s.machine.gasMeasure ≤ n) : PlainGas s n (PlainOp.runCore pc ctx s .extcodehash) := by
  have valid := BenvStat.rules_valid ctx.block
  have cold := valid.gas.1
  cases access : ctx.block.rules.access with
  | flat g =>
    have pos := (valid.flatAccess access).2.2.1
    simp only [PlainGas, PlainOp.runCore, access]
    gas_walk
  | eip2929 =>
    simp only [PlainGas, PlainOp.runCore, access]
    gas_walk

private theorem sload_gas (pc : Nat) (ctx : CallContext) (s : Frame.State) {n : Nat}
    (h : s.machine.gasMeasure ≤ n) : PlainGas s n (PlainOp.runCore pc ctx s .sload) := by
  have valid := BenvStat.rules_valid ctx.block
  have cold := valid.gas.1
  cases access : ctx.block.rules.access with
  | flat g =>
    have pos := (valid.flatAccess access).2.2.2.1
    simp only [PlainGas, PlainOp.runCore, access]
    gas_walk
  | eip2929 =>
    simp only [PlainGas, PlainOp.runCore, access]
    gas_walk

private theorem selfbalance_gas (pc : Nat) (ctx : CallContext) (s : Frame.State) {n : Nat}
    (h : s.machine.gasMeasure ≤ n) : PlainGas s n (PlainOp.runCore pc ctx s .selfbalance) := by
  simp only [PlainGas, PlainOp.runCore]
  gas_walk

private theorem tload_gas (pc : Nat) (ctx : CallContext) (s : Frame.State) {n : Nat}
    (h : s.machine.gasMeasure ≤ n) : PlainGas s n (PlainOp.runCore pc ctx s .tload) := by
  simp only [PlainGas, PlainOp.runCore]
  gas_walk

private theorem tstore_gas (pc : Nat) (ctx : CallContext) (s : Frame.State) {n : Nat}
    (h : s.machine.gasMeasure ≤ n) : PlainGas s n (PlainOp.runCore pc ctx s .tstore) := by
  simp only [PlainGas, PlainOp.runCore]
  gas_walk

private theorem sstoreBerlin_gas (ctx : CallContext) (s : Frame.State) {n : Nat}
    (h : s.machine.gasMeasure ≤ n) : PlainGas s n (PlainOp.sstoreBerlin ctx s) := by
  unfold PlainGas PlainOp.sstoreBerlin
  gas_walk

private theorem sstoreLegacy_gas (ctx : CallContext) (s : Frame.State) {n : Nat}
    (h : s.machine.gasMeasure ≤ n) : PlainGas s n (PlainOp.sstoreLegacy ctx s) := by
  have hv := (BenvStat.rules_valid ctx.block).access
  unfold PlainGas PlainOp.sstoreLegacy
  gas_walk

private theorem storageWrite_gas (s : Frame.State) (rules : ForkRules) (ct : Address)
    (key val : U256) (cost stateCost : Nat) {start bound : Nat} (hs : s.machine.gasMeasure = start)
    (hb : start ≤ bound) (hp : 0 < cost) :
    Walk (·.machine.gasMeasure ≤ bound) (fun t : Frame.State => t.machine.gasMeasure < start) (do
      let t ← s.chargeGas cost
      let u ← t.chargeStateGas stateCost
      pure ((u.recordAccountRead rules ct).setStorageValue ct key val)) := by
  apply Walk.bind (chargePositive (hs.trans_le hb) hp)
  intro t ht
  change t.machine.gasMeasure < s.machine.gasMeasure at ht
  apply Walk.bind (Frame.State.chargeStateGas_gas _ (by omega))
  intro u hu
  change u.machine.gasMeasure = t.machine.gasMeasure at hu
  change u.machine.gasMeasure < start
  omega

private theorem sstoreAmsterdam_gas (state : StateGasRules) (ctx : CallContext) (s : Frame.State)
    {n : Nat} (h : s.machine.gasMeasure ≤ n) : PlainGas s n (PlainOp.sstoreAmsterdam state ctx s) := by
  unfold PlainGas PlainOp.sstoreAmsterdam
  apply Walk.bind (Frame.State.assertDynamic_gas ctx h)
  intro _ _
  apply Walk.bind (Frame.State.pop_gas h)
  rintro ⟨key, t⟩ ht
  change t.machine.gasMeasure = s.machine.gasMeasure at ht
  apply Walk.bind (Frame.State.pop_gas (ht.trans_le h))
  rintro ⟨val, u⟩ hu
  change u.machine.gasMeasure = t.machine.gasMeasure at hu
  apply Walk.bind (Walk.assert ((hu.trans ht).trans_le h))
  intro _ _
  apply storageWrite_gas _ _ _ _ _ _ _ _ h (sstoreAmsterdamGasCost_pos _ _ _ _ _)
  simp only [Frame.State.creditStateGasRefund, Frame.State.liftMachinePure_machine,
    Machine.creditStateGasRefund_gasMeasure, Frame.State.withRefund, Frame.State.withSubstate_machine,
    Frame.State.recordStorageRead, Frame.State.withTrail_machine, apply_ite Frame.State.machine,
    Frame.State.addAccessedStorageKey, ite_self]
  exact hu.trans ht

private theorem fixedCost_gas {s : Frame.State} {n c : Nat}
    {body : Except (ExceptionalHalt × Frame.State) Frame.State} (hc : 0 < c)
    (law : Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure + c = s.machine.gasMeasure) body) :
    PlainGas s n body := by
  apply Walk.mono law
  intro t ht
  change t.machine.gasMeasure + c = s.machine.gasMeasure at ht
  omega

private theorem gatedMachine_gas {s : Frame.State} {n cost : Nat}
    (enabled : Bool) (core : Machine → Except (ExceptionalHalt × Machine) Machine)
    (h : s.machine.gasMeasure ≤ n) (pos : 0 < cost)
    (law : MWalk (·.gasMeasure ≤ n) (·.gasMeasure + cost = s.machine.gasMeasure) (core s.machine)) :
    PlainGas s n (s.liftMachine (fun m => if enabled then core m else PlainOp.unavailable m)) := by
  apply Walk.liftMachine_gas
  cases enabled with
  | false => exact h
  | true =>
    apply MWalk.mono law
    intro t ht
    change t.gasMeasure + cost = s.machine.gasMeasure at ht
    change t.gasMeasure < s.machine.gasMeasure
    omega

/-- Elaborate the longer machine walks separately so each opcode checks independently. -/
local macro "plain_machine_walk " name:ident " for " op:term : command =>
  `(private theorem $name (pc : Nat) (ctx : CallContext) (s : Frame.State) {n : Nat}
      (h : s.machine.gasMeasure ≤ n) : PlainGas s n (PlainOp.runCore pc ctx s $op) := by
      simp only [PlainGas, PlainOp.runCore]
      repeat' (first | gas_head_step | gas_step))

plain_machine_walk calldataload_gas for .calldataload
plain_machine_walk blockhash_gas for .blockhash
plain_machine_walk pop_gas for .pop
plain_machine_walk gas_gas for .gas
plain_machine_walk mload_gas for .mload
plain_machine_walk mstore_gas for .mstore
plain_machine_walk mstore8_gas for .mstore8
plain_machine_walk calldatacopy_gas for .calldatacopy
plain_machine_walk codecopy_gas for .codecopy
plain_machine_walk returndatacopy_gas for .returndatacopy
plain_machine_walk mcopy_gas for .mcopy
plain_machine_walk keccak256_gas for .keccak256
plain_machine_walk exp_gas for .exp
plain_machine_walk blobhash_gas for .blobhash

/-- Each plain instruction either halts within the input gas bound or continues with a strictly
smaller measure. This includes the state-gas spill in both bounds. -/
theorem PlainOp.runCore_gas (pc : Nat) (ctx : CallContext) (s : Frame.State) (op : Jaune.PlainOp)
    {n : Nat} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure < s.machine.gasMeasure)
      (PlainOp.runCore pc ctx s op) := by
  cases op
  case calldataload => exact calldataload_gas pc ctx s h
  case blockhash => exact blockhash_gas pc ctx s h
  case pop => exact pop_gas pc ctx s h
  case gas => exact gas_gas pc ctx s h
  case mload => exact mload_gas pc ctx s h
  case mstore => exact mstore_gas pc ctx s h
  case mstore8 => exact mstore8_gas pc ctx s h
  case calldatacopy => exact calldatacopy_gas pc ctx s h
  case codecopy => exact codecopy_gas pc ctx s h
  case returndatacopy => exact returndatacopy_gas pc ctx s h
  case mcopy => exact mcopy_gas pc ctx s h
  case keccak256 => exact keccak256_gas pc ctx s h
  case exp => exact exp_gas pc ctx s h
  case blobhash => exact blobhash_gas pc ctx s h
  case log k => exact log_gas k ctx s h
  case balance => exact balance_gas pc ctx s h
  case extcodesize => exact extcodesize_gas pc ctx s h
  case extcodehash => exact extcodehash_gas pc ctx s h
  case extcodecopy => exact extcodecopy_gas pc ctx s h
  case selfbalance => exact selfbalance_gas pc ctx s h
  case sload => exact sload_gas pc ctx s h
  case tload => exact tload_gas pc ctx s h
  case tstore => exact tstore_gas pc ctx s h
  case sstore =>
    simp only [PlainOp.runCore]
    split
    · split <;> first | apply sstoreBerlin_gas ctx s h | apply sstoreLegacy_gas ctx s h
    · exact sstoreAmsterdam_gas _ ctx s h
  all_goals simp only [PlainOp.runCore]
  all_goals try first
    | exact fixedCost_gas (by decide) (Frame.State.pushItem_gas _ _ h)
    | exact fixedCost_gas (by decide) (Frame.State.applyUnary_gas _ _ h)
    | exact fixedCost_gas (by decide) (Frame.State.applyBinary_gas _ _ h)
    | exact fixedCost_gas (by decide) (Frame.State.applyTernary_gas _ _ h)
  all_goals try with_reducible first
    | exact gatedMachine_gas _ _ h (by decide) (Machine.applyBinary_gas _ _ h)
    | exact gatedMachine_gas _ _ h (by decide) (Machine.applyUnary_gas _ _ h)
    | exact gatedMachine_gas _ _ h (by decide) (Machine.pushItem_gas _ _ h)
  all_goals gas_walk

end Jaune.Staging
