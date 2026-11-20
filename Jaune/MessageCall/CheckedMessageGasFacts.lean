import Jaune.CheckedSufficiencyWalk
import Jaune.GasFacts

/-! Gas at a message operation, on the continuation, spawn and exceptional-halt paths. -/
namespace Jaune.Checked

open Jaune

/-! ### Gas obligations

`Staging`'s message-operation gas obligations, restated over the checked state. -/

/-- A state's spill: what an exceptional halt keeps of its state-gas meter. -/
def Frame.State.spill (s : Frame.State) : Nat :=
  s.stateGas.spilled + s.stateGas.committedSpill

/-- The call-family obligation against the measure `n` the step began with: a finished
operation leaves less, and a spawn's child grant plus its checkpoint's measure is less, with the
child under the spawning frame's rules. -/
def MessageOp.Outcome.GasDecreasing (ctx : CallContext) (n : Nat) : MessageOp.Outcome → Prop
  | .done r => ∀ s, r = .ok s → s.machine.gasMeasure < n
  | .spawn child _ =>
      child.message.gas + child.checkpoint.machine.gasMeasure < n ∧
        child.message.context.block.rules = ctx.block.rules

/-- What a message operation owes on its halt branch: a spill `n` still covers. -/
def MessageOp.Outcome.Halt (n : Nat) : MessageOp.Outcome → Prop
  | .done r => ∀ p, r = .error p → p.2.spill ≤ n
  | .spawn _ _ => True

private abbrev OutcomeBound (ctx : CallContext) (n : Nat) (outcome : MessageOp.Outcome) :=
  outcome.GasDecreasing ctx n ∧ outcome.Halt n

private theorem ofExcept_bound {ctx : CallContext} {n : Nat}
    {x : Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (h : Walk (·.machine.gasMeasure ≤ n) (OutcomeBound ctx n) x) :
    OutcomeBound ctx n (MessageOp.Outcome.ofExcept x) := by
  cases x with
  | ok result => exact h
  | error p =>
    obtain ⟨reason, s⟩ := p
    constructor
    · intro t he; contradiction
    · intro p he; cases he
      change s.machine.gasMeasure ≤ n at h
      change s.machine.stateGas.spilled + s.machine.stateGas.committedSpill ≤ n
      unfold Machine.gasMeasure at h
      omega

private theorem done_bound {ctx : CallContext} {n : Nat} {s : Frame.State}
    (h : s.machine.gasMeasure < n) : OutcomeBound ctx n (.done (.ok s)) := by
  constructor
  · intro t ht; cases ht; exact h
  · intro p hp; contradiction

private theorem pushZero_bound (ctx : CallContext) (s : Frame.State) {n : Nat}
    (h : s.machine.gasMeasure < n) :
    Walk (·.machine.gasMeasure ≤ n) (OutcomeBound ctx n) (do
      let u ← s.push 0
      return .done (.ok u)) := by
  apply Walk.bind (Frame.State.push_gas 0 h.le)
  intro u hu
  apply done_bound
  exact hu.trans_lt h

private theorem restoreChildGas_measure (s : Frame.State) (gas reservoir : Nat) :
    (s.restoreChildGas gas reservoir).machine.gasMeasure = s.machine.gasMeasure + gas := by
  simp only [Frame.State.restoreChildGas, Frame.State.liftMachinePure_machine,
    Machine.restoreChildGas, Machine.gasMeasure]
  omega

private theorem genericCall_bound (ctx : CallContext) (s : Frame.State) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (transfersValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat) (code : ByteArray) (disablePrecompiles : Bool)
    {n : Nat} (h : s.machine.gasMeasure + gas < n) :
    OutcomeBound ctx n (genericCall.step ctx s gas value caller target codeAddress transfersValue
      isStaticcall inputIndex inputSize outputIndex outputSize code disablePrecompiles) := by
  unfold genericCall.step
  split
  · apply ofExcept_bound
    apply pushZero_bound
    change s.machine.gasLeft + gas + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill < n
    unfold Machine.gasMeasure at h
    omega
  · exact ⟨⟨by change gas + s.machine.gasMeasure < n; omega, rfl⟩, True.intro⟩

private theorem genericCallAmsterdam_bound (ctx : CallContext) (state : StateGasRules)
    (s : Frame.State) (gas reservoir : Nat) (value : U256) (caller target codeAddress : Address)
    (transfersValue isStaticcall : Bool) (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles newAccountCharged insufficientBalance : Bool) {n : Nat}
    (h : s.machine.gasMeasure + gas < n) : OutcomeBound ctx n (genericCallAmsterdam.step ctx state
      s gas reservoir value caller target codeAddress transfersValue isStaticcall inputIndex
      inputSize outputIndex outputSize code disablePrecompiles newAccountCharged insufficientBalance) := by
  unfold genericCallAmsterdam.step
  split
  · apply ofExcept_bound
    apply pushZero_bound
    have budget : ((s.withReturnData []).restoreChildGas gas reservoir).machine.gasMeasure < n := by
      rw [restoreChildGas_measure]
      exact h
    cases newAccountCharged <;> simp only [Bool.false_eq_true, ↓reduceIte,
      Frame.State.creditStateGasRefund, Frame.State.liftMachinePure_machine,
      Machine.creditStateGasRefund_gasMeasure] <;> exact budget
  · exact ⟨⟨by change gas + s.machine.gasMeasure < n; omega, rfl⟩, True.intro⟩

private theorem withGasLeft_measure (s : Frame.State) (g : Nat) :
    (s.withGasLeft g).machine.gasMeasure = g + s.spill := by
  unfold Frame.State.spill Machine.gasMeasure
  change g + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill =
    g + (s.machine.stateGas.spilled + s.machine.stateGas.committedSpill)
  omega

private theorem createBudget (s : Frame.State) :
    (s.withGasLeft (s.gasLeft - except64th s.gasLeft)).machine.gasMeasure +
      except64th s.gasLeft = s.machine.gasMeasure := by
  have := except64th_le s.gasLeft
  rw [withGasLeft_measure]
  change _ = s.gasLeft + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill
  change s.gasLeft - except64th s.gasLeft + (s.machine.stateGas.spilled + s.machine.stateGas.committedSpill) + except64th s.gasLeft = _
  omega

private theorem genericCreate_bound (ctx : CallContext) (s : Frame.State) (endowment : U256)
    (address : Address) (offset size : Nat) {n : Nat} (h : s.machine.gasMeasure < n) :
    OutcomeBound ctx n (genericCreate.step ctx s endowment address offset size) := by
  unfold genericCreate.step
  apply ofExcept_bound
  apply Walk.bind (Walk.assert h.le)
  intro _ _
  have budget := createBudget s
  apply Walk.bind (Frame.State.assertDynamic_gas ctx (by omega))
  intro _ _
  dsimp only
  split
  · apply pushZero_bound
    have := except64th_le s.gasLeft
    change s.gasLeft - except64th s.gasLeft + except64th s.gasLeft +
      s.machine.stateGas.spilled + s.machine.stateGas.committedSpill < n
    change s.gasLeft + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill < n at h
    omega
  · split
    · apply pushZero_bound
      change (s.withGasLeft (s.gasLeft - except64th s.gasLeft)).machine.gasMeasure < n
      omega
    · constructor
      · constructor
        · change except64th s.gasLeft + (s.withGasLeft (s.gasLeft - except64th s.gasLeft)).machine.gasMeasure < n
          omega
        · rfl
      · trivial

private theorem genericCreateAmsterdam_bound (ctx : CallContext) (rules : StateGasRules)
    (s : Frame.State) (endowment : U256) (address : Address) (offset size : Nat) {n : Nat}
    (h : s.machine.gasMeasure < n) :
    OutcomeBound ctx n (genericCreateAmsterdam.step ctx rules s endowment address offset size) := by
  unfold genericCreateAmsterdam.step
  apply ofExcept_bound
  dsimp only
  split
  · exact pushZero_bound ctx _ h
  · split
    · apply Walk.bind (Frame.State.chargeStateGas_gas _ (by change s.machine.gasMeasure ≤ n; exact h.le))
      intro t ht
      change t.machine.gasMeasure = s.machine.gasMeasure at ht
      have hb := Machine.withholdCreateGas_gasMeasure t.machine
      split
      · apply pushZero_bound
        change t.machine.withholdCreateGas.2.gasMeasure < n
        omega
      · constructor
        · constructor
          · change t.machine.withholdCreateGas.1 + t.machine.withholdCreateGas.2.drainStateGasReservoir.2.gasMeasure < n
            rw [Machine.drainStateGasReservoir_gasMeasure]
            omega
          · rfl
        · trivial
    · have hb := Machine.withholdCreateGas_gasMeasure (s.withReturnData []).machine
      simp only [bind, Except.bind]
      split
      · apply pushZero_bound
        change (s.withReturnData []).machine.withholdCreateGas.2.gasMeasure < n
        change (s.withReturnData []).machine.gasMeasure < n at h
        omega
      · constructor
        · constructor
          · change (s.withReturnData []).machine.withholdCreateGas.1 +
              (s.withReturnData []).machine.withholdCreateGas.2.drainStateGasReservoir.2.gasMeasure < n
            rw [Machine.drainStateGasReservoir_gasMeasure]
            change (s.withReturnData []).machine.gasMeasure < n at h
            omega
          · rfl
        · trivial

private theorem accessDelegation_measure (rules : ForkRules) (s : Frame.State) (a : Address) :
    (ForkRules.accessDelegation rules s a).2.2.2.2.machine.gasMeasure = s.machine.gasMeasure := by
  unfold ForkRules.accessDelegation GasSchedule.accessDelegation
  split
  · dsimp only
    split <;> rfl
  · rfl

private theorem completeDelegation_measure (s : Frame.State) (delegated : Bool) (a : Address) :
    (completeDelegationAccess s delegated a).2.machine.gasMeasure = s.machine.gasMeasure := by
  cases delegated <;> rfl

private theorem stipend_covered (rules : ForkRules) (value : U256) (hv : rules.Valid) :
    (if value.toNat = 0 then 0 else Gas.callStipend) ≤ (if value = 0 then 0 else rules.gas.callValue) := by
  have hz : value.toNat = 0 ↔ value = 0 :=
    ⟨fun h => U256.toNat_inj value 0 (by simpa only [U256.toNat_zero] using h), fun h => h ▸ rfl⟩
  by_cases he : value = 0
  · simp only [he, U256.toNat_zero, ite_true, Nat.le_refl]
  · simp only [ite_eq_right he, ite_eq_right (mt hz.mp he)]
    exact hv.gas.stipend_le_callValue

private theorem chargeForCall {s : Frame.State} {n value gas gasLeft memory extra : Nat}
    (h : s.machine.gasMeasure ≤ n)
    (hpaid : (if value = 0 then 0 else Gas.callStipend) < extra + memory) :
    Walk (·.machine.gasMeasure ≤ n) (fun t : Frame.State =>
      t.machine.gasMeasure + (calculateMsgCallGas value gas gasLeft memory extra).2 < n)
      (s.chargeGas ((calculateMsgCallGas value gas gasLeft memory extra).1 + memory)) := by
  apply Walk.mono (Frame.State.chargeGas_gas _ h)
  intro t ht
  have hgrant := calculateMessageCallGas_stipend_lt (gas := gas) (gasLeft := gasLeft) hpaid
  change t.machine.gasMeasure + _ = s.machine.gasMeasure at ht
  omega

private theorem chargeGrant {s : Frame.State} {n value gas : Nat}
    (h : s.machine.gasMeasure + (if value = 0 then 0 else Gas.callStipend) < n) :
    Walk (·.machine.gasMeasure ≤ n) (fun t : Frame.State =>
      t.machine.gasMeasure + (calculateMsgCallGas value gas s.gasLeft 0 0).2 < n)
      (s.chargeGas (calculateMsgCallGas value gas s.gasLeft 0 0).1) := by
  apply Walk.mono (Frame.State.chargeGas_gas _ (by omega))
  intro t ht
  rw [calculateMessageCallGas_zero_cost]
  change t.machine.gasMeasure + _ = s.machine.gasMeasure at ht
  omega

private theorem accessPositive {ctx : CallContext} (a : Address) (warm : AdrSet) :
    0 < (match ctx.block.rules.access with
      | .eip2929 => ctx.block.rules.gas.accessCost a warm
      | .flat g => g.call) := by
  have valid := BlockContext.rules_valid ctx.block
  cases ha : ctx.block.rules.access with
  | flat g => exact (valid.flatAccess ha).2.2.2.2
  | eip2929 => exact valid.gas.accessCost_pos _ _

local macro "message_arith" : tactic => `(tactic| first
  | assumption
  | omega
  | (simp only [Frame.State.memExtends, Frame.State.liftMachinePure_machine, Machine.memExtends_gasMeasure,
      Frame.State.addAccessedAddress, Frame.State.withSubstate_machine, Frame.State.recordAccountRead,
      Frame.State.withTrail_machine, Frame.State.drainStateGasReservoir, Frame.State.withMachine_machine,
      Machine.drainStateGasReservoir_gasMeasure, accessDelegation_measure, completeDelegation_measure]
      at *
     omega))

local macro "message_pops" : tactic => `(tactic| repeat' (with_reducible first
  | (apply Walk.bind (Frame.State.pop_gas (by message_arith)); rintro ⟨_, _⟩ _; try dsimp only at *)
  | (apply Walk.bind (Frame.State.popToAddress_gas (by message_arith)); rintro ⟨_, _⟩ _; try dsimp only at *)
  | (apply Walk.bind (Frame.State.popToNat_gas (by message_arith)); rintro ⟨_, _⟩ _; try dsimp only at *)
  | (apply Walk.bind (Frame.State.assertDynamic_gas _ (by message_arith)); intro _ _; try dsimp only at *)
  | (apply Walk.bind (Walk.assert (by message_arith)); intro _ _; try dsimp only at *)))

local macro "creation_walk" : tactic => `(tactic| (
  apply ofExcept_bound
  message_pops
  apply Walk.bind (Frame.State.chargeGas_gas _ (by message_arith))
  intro t hcharge
  try dsimp only at *
  message_pops
  first | (apply genericCreate_bound; message_arith) | (apply genericCreateAmsterdam_bound; message_arith)))

private theorem create_bound (ctx : CallContext) (s : Frame.State) :
    OutcomeBound ctx s.machine.gasMeasure (MessageOp.step ctx s .create) := by
  have cost := (BlockContext.rules_valid ctx.block).gas.2.1
  cases hs : ctx.block.rules.stateGas <;> simp only [MessageOp.step, hs] <;> creation_walk

private theorem create2_bound (ctx : CallContext) (s : Frame.State) :
    OutcomeBound ctx s.machine.gasMeasure (MessageOp.step ctx s .create2) := by
  have cost := (BlockContext.rules_valid ctx.block).gas.2.1
  simp only [MessageOp.step]
  split
  · split <;> creation_walk
  · apply ofExcept_bound (x := .error (.invalidOpcode .none, s))
    exact Nat.le_refl _

private theorem accessState_measure (rules : ForkRules) (s : Frame.State) (a : Address) :
    (match rules.access with | .eip2929 => s.addAccessedAddress a | .flat _ => s).machine.gasMeasure =
      s.machine.gasMeasure := by
  cases rules.access <;> rfl

private theorem addGas_measure (s : Frame.State) (gas : Nat) :
    (s.withGasLeft (s.gasLeft + gas)).machine.gasMeasure = s.machine.gasMeasure + gas := by
  unfold Machine.gasMeasure
  change s.gasLeft + gas + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill =
    s.gasLeft + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill + gas
  omega

private theorem refundResult_bound (s : Frame.State) (gas : Nat) {ctx : CallContext} {n : Nat}
    (h : s.machine.gasMeasure + gas < n) :
    Walk (·.machine.gasMeasure ≤ n) (OutcomeBound ctx n) (do
      let t ← s.push 0
      return .done (.ok ((t.withReturnData []).withGasLeft (t.gasLeft + gas)))) := by
  apply Walk.bind (Frame.State.push_gas 0 (by omega))
  intro t ht
  apply done_bound
  change t.machine.gasMeasure = s.machine.gasMeasure at ht
  change (t.withGasLeft (t.gasLeft + gas)).machine.gasMeasure < n
  rw [addGas_measure, ht]
  exact h

private theorem refundResult'_bound (s : Frame.State) (gas : Nat) {ctx : CallContext} {n : Nat}
    (h : s.machine.gasMeasure + gas < n) :
    Walk (·.machine.gasMeasure ≤ n) (OutcomeBound ctx n) (do
      let t ← s.push 0
      return .done (.ok ((t.withGasLeft (t.gasLeft + gas)).withReturnData []))) := by
  apply Walk.bind (Frame.State.push_gas 0 (by omega))
  intro t ht
  apply done_bound
  change t.machine.gasMeasure = s.machine.gasMeasure at ht
  change (t.withGasLeft (t.gasLeft + gas)).machine.gasMeasure < n
  rw [addGas_measure, ht]
  exact h

local macro "call_walk " ctx:term : tactic => `(tactic| (
  apply ofExcept_bound
  apply Walk.bind (Frame.State.pop_gas (Nat.le_refl _))
  rintro ⟨gas, a⟩ ha
  apply Walk.bind (Frame.State.popToAddress_gas (by message_arith))
  rintro ⟨callee, b⟩ hb
  try (apply Walk.bind (Frame.State.pop_gas (by message_arith)); rintro ⟨value, v⟩ hv;
       have paid := stipend_covered ($ctx).block.rules value (BlockContext.rules_valid ($ctx).block))
  iterate 3 (apply Walk.bind (Frame.State.popToNat_gas (by message_arith)); rintro ⟨_, _⟩ _)
  apply Walk.bind (Frame.State.popToNat_gas (by message_arith))
  rintro ⟨_, t⟩ ht
  try dsimp only at *
  have flat := accessPositive (ctx := $ctx) callee t.accessedAddresses
  have warm := (BlockContext.rules_valid ($ctx).block).gas.accessCost_pos callee t.accessedAddresses
  message_pops
  refine Walk.bind (chargeForCall ?_ ?_) ?_
  · try simp only [accessDelegation_measure, completeDelegation_measure, accessState_measure,
      Frame.State.recordAccountRead, Frame.State.withTrail_machine, Frame.State.addAccessedAddress,
      Frame.State.withSubstate_machine]
    cases hacc : ($ctx).block.rules.access <;> simp only [hacc, Frame.State.addAccessedAddress, Frame.State.withSubstate_machine] at * <;> message_arith
  · cases hacc : ($ctx).block.rules.access <;> simp only [hacc, ite_true] at * <;> omega
  intro charged hcharged
  try dsimp only at *
  message_pops
  first
  | (apply genericCall_bound; message_arith)
  | (apply genericCallAmsterdam_bound; message_arith)
  | (split
     · first | apply refundResult_bound | apply refundResult'_bound
       message_arith
     · apply genericCall_bound
       message_arith)))

private theorem staticcall_bound (ctx : CallContext) (s : Frame.State) :
    OutcomeBound ctx s.machine.gasMeasure (MessageOp.step ctx s .staticcall) := by
  cases hs : ctx.block.rules.stateGas <;> simp only [MessageOp.step, hs] <;> call_walk ctx


private theorem delegatecall_bound (ctx : CallContext) (s : Frame.State) :
    OutcomeBound ctx s.machine.gasMeasure (MessageOp.step ctx s .delegatecall) := by
  cases hs : ctx.block.rules.stateGas <;> simp only [MessageOp.step, hs] <;> call_walk ctx

private theorem callcode_bound (ctx : CallContext) (s : Frame.State) :
    OutcomeBound ctx s.machine.gasMeasure (MessageOp.step ctx s .callcode) := by
  cases hs : ctx.block.rules.stateGas <;> simp only [MessageOp.step, hs] <;> call_walk ctx

private theorem call_legacy_bound (ctx : CallContext) (s : Frame.State)
    (hs : ctx.block.rules.stateGas = none) :
    OutcomeBound ctx s.machine.gasMeasure (MessageOp.step ctx s .call) := by
  simp only [MessageOp.step, hs]
  call_walk ctx

private theorem call_state_bound (ctx : CallContext) (s : Frame.State) (state : StateGasRules)
    (hs : ctx.block.rules.stateGas = some state) :
    OutcomeBound ctx s.machine.gasMeasure (MessageOp.step ctx s .call) := by
  simp only [MessageOp.step, hs]
  apply ofExcept_bound
  apply Walk.bind (Frame.State.pop_gas (Nat.le_refl _))
  rintro ⟨gas, a⟩ ha
  apply Walk.bind (Frame.State.popToAddress_gas (by message_arith))
  rintro ⟨callee, b⟩ hb
  apply Walk.bind (Frame.State.pop_gas (by message_arith))
  rintro ⟨value, v⟩ hv
  have paid := stipend_covered ctx.block.rules value (BlockContext.rules_valid ctx.block)
  iterate 3 (apply Walk.bind (Frame.State.popToNat_gas (by message_arith)); rintro ⟨_, _⟩ _)
  apply Walk.bind (Frame.State.popToNat_gas (by message_arith))
  rintro ⟨_, t⟩ ht
  try dsimp only at *
  have warm := (BlockContext.rules_valid ctx.block).gas.accessCost_pos callee t.accessedAddresses
  message_pops
  refine Walk.bind (Frame.State.chargeGas_gas _ ?_) ?_
  · message_arith
  intro charged hc
  have budget : charged.machine.gasMeasure + (if value.toNat = 0 then 0 else Gas.callStipend) <
      s.machine.gasMeasure := by message_arith
  split
  · apply Walk.bind (Frame.State.chargeStateGas_gas _ (by omega))
    intro u hu
    change u.machine.gasMeasure = charged.machine.gasMeasure at hu
    apply Walk.bind (chargeGrant (by rw [hu]; exact budget))
    intro z hz
    apply genericCallAmsterdam_bound
    message_arith
  · simp only [bind, Except.bind]
    apply Walk.bind (chargeGrant budget)
    intro z hz
    apply genericCallAmsterdam_bound
    message_arith

/-- A message instruction funds its continuation or its child and suspended frame, and an
exceptional halt retains at most the input gas measure. -/
theorem MessageOp.step_gas (ctx : CallContext) (s : Frame.State) (op : Jaune.MessageOp) :
    (MessageOp.step ctx s op).GasDecreasing ctx s.machine.gasMeasure ∧
    (MessageOp.step ctx s op).Halt s.machine.gasMeasure := by
  cases op with
  | create => exact create_bound ctx s
  | create2 => exact create2_bound ctx s
  | call =>
    cases hs : ctx.block.rules.stateGas with
    | none => exact call_legacy_bound ctx s hs
    | some state => exact call_state_bound ctx s state hs
  | callcode => exact callcode_bound ctx s
  | delegatecall => exact delegatecall_bound ctx s
  | staticcall => exact staticcall_bound ctx s

end Jaune.Checked
