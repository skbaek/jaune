import Jaune.CheckedSufficiencyWalk
import Jaune.Instructions.WordFacts
import Jaune.Instructions.ShuffleFacts
import Jaune.Instructions.LogFacts
import Jaune.Instructions.MemoryFacts
import Jaune.Instructions.ReadFacts
import Jaune.Instructions.StoreFacts

/-! # Stack and execution-gas operations preserve the state-gas meter -/

namespace Jaune.Checked
open Jaune

namespace Machine


theorem pop_meter (m : Machine) :
    MWalk (·.stateGas = m.stateGas) (fun p => p.2.stateGas = m.stateGas) m.pop := by
  unfold Machine.pop
  split <;> rfl

theorem push_meter (m : Machine) (x : U256) :
    MWalk (·.stateGas = m.stateGas) (·.stateGas = m.stateGas) (m.push x) := by
  unfold Machine.push
  split <;> rfl

theorem chargeGas_meter (m : Machine) (c : Nat) :
    MWalk (·.stateGas = m.stateGas) (·.stateGas = m.stateGas) (m.chargeGas c) := by
  unfold Machine.chargeGas
  split <;> rfl

theorem popToNat_meter (m : Machine) :
    MWalk (·.stateGas = m.stateGas) (fun p => p.2.stateGas = m.stateGas) m.popToNat := by
  unfold Machine.popToNat
  have h := pop_meter m
  split <;> rename_i he <;> rw [he] at h <;> exact h

theorem popToAddress_meter (m : Machine) :
    MWalk (·.stateGas = m.stateGas) (fun p => p.2.stateGas = m.stateGas) m.popToAddress := by
  unfold Machine.popToAddress
  have h := pop_meter m
  split <;> rename_i he <;> rw [he] at h <;> exact h

theorem popN_meter (m : Machine) (k : Nat) :
    MWalk (·.stateGas = m.stateGas) (fun p => p.2.stateGas = m.stateGas) (m.popN k) := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    unfold Machine.popN
    have h := pop_meter m
    split
    · rename_i he; rw [he] at h; exact h
    · rename_i x m' he
      rw [he] at h
      have hm : m'.stateGas = m.stateGas := h
      rw [← hm]
      have h' := ih m'
      split <;> rename_i he' <;> rw [he'] at h' <;> exact h'

/-- Discharge a prefix of machine operations by its meter equality at either exit. -/
local macro "next_meter" fact:term : tactic => `(tactic| (
  have h := $fact
  split <;> rename_i he <;> rw [he] at h
  all_goals first | exact h | (simp only [MWalk.ok_iff] at h; rw [← h])))

theorem pushItem_meter (m : Machine) (x : U256) (c : Nat) :
    MWalk (·.stateGas = m.stateGas) (·.stateGas = m.stateGas) (m.pushItem x c) := by
  unfold Machine.pushItem
  next_meter (chargeGas_meter m c)
  apply push_meter

theorem applyUnary_meter (m : Machine) (f : U256 → U256) (c : Nat) :
    MWalk (·.stateGas = m.stateGas) (·.stateGas = m.stateGas) (m.applyUnary f c) := by
  unfold Machine.applyUnary
  next_meter (pop_meter m)
  apply pushItem_meter

theorem applyBinary_meter (m : Machine) (f : U256 → U256 → U256) (c : Nat) :
    MWalk (·.stateGas = m.stateGas) (·.stateGas = m.stateGas) (m.applyBinary f c) := by
  unfold Machine.applyBinary
  next_meter (pop_meter m)
  rename_i mNext _ _
  next_meter (pop_meter mNext)
  apply pushItem_meter

theorem applyTernary_meter (m : Machine) (f : U256 → U256 → U256 → U256) (c : Nat) :
    MWalk (·.stateGas = m.stateGas) (·.stateGas = m.stateGas) (m.applyTernary f c) := by
  unfold Machine.applyTernary
  next_meter (pop_meter m)
  rename_i mNext _ _
  next_meter (pop_meter mNext)
  rename_i mNext _ _
  next_meter (pop_meter mNext)
  apply pushItem_meter

end Machine

private theorem MWalk.meter {α : Type} {m : Machine} {g : StateGasMeter}
    {read : α → StateGasMeter} {x : Except (ExceptionalHalt × Machine) α}
    (hx : MWalk (·.stateGas = m.stateGas) (fun a => read a = m.stateGas) x)
    (hm : m.stateGas = g) :
    MWalk (·.stateGas = g) (fun a => read a = g) x := by
  subst g
  exact hx

private theorem Walk.meter {α : Type} {s : Frame.State} {g : StateGasMeter}
    {read : α → StateGasMeter} {x : Except (ExceptionalHalt × Frame.State) α}
    (hx : Walk (·.machine.stateGas = s.machine.stateGas) (fun a => read a = s.machine.stateGas) x)
    (hs : s.machine.stateGas = g) :
    Walk (·.machine.stateGas = g) (fun a => read a = g) x := by
  subst g
  exact hx

theorem Frame.State.push_meter (s : Frame.State) (x : U256) :
    Walk (·.machine.stateGas = s.machine.stateGas) (·.machine.stateGas = s.machine.stateGas)
      (s.push x) :=
  Walk.liftMachine (Machine.push_meter s.machine x)

theorem Frame.State.chargeGas_meter (s : Frame.State) (c : Nat) :
    Walk (·.machine.stateGas = s.machine.stateGas) (·.machine.stateGas = s.machine.stateGas)
      (s.chargeGas c) :=
  Walk.liftMachine (Machine.chargeGas_meter s.machine c)

theorem Frame.State.pushItem_meter (s : Frame.State) (x : U256) (c : Nat) :
    Walk (·.machine.stateGas = s.machine.stateGas) (·.machine.stateGas = s.machine.stateGas)
      (s.pushItem x c) :=
  Walk.liftMachine (Machine.pushItem_meter s.machine x c)

theorem Frame.State.applyUnary_meter (s : Frame.State) (f : U256 → U256) (c : Nat) :
    Walk (·.machine.stateGas = s.machine.stateGas) (·.machine.stateGas = s.machine.stateGas)
      (s.applyUnary f c) :=
  Walk.liftMachine (Machine.applyUnary_meter s.machine f c)

theorem Frame.State.applyBinary_meter (s : Frame.State) (f : U256 → U256 → U256) (c : Nat) :
    Walk (·.machine.stateGas = s.machine.stateGas) (·.machine.stateGas = s.machine.stateGas)
      (s.applyBinary f c) :=
  Walk.liftMachine (Machine.applyBinary_meter s.machine f c)

theorem Frame.State.applyTernary_meter (s : Frame.State) (f : U256 → U256 → U256 → U256) (c : Nat) :
    Walk (·.machine.stateGas = s.machine.stateGas) (·.machine.stateGas = s.machine.stateGas)
      (s.applyTernary f c) :=
  Walk.liftMachine (Machine.applyTernary_meter s.machine f c)

theorem Frame.State.pop_meter (s : Frame.State) :
    Walk (·.machine.stateGas = s.machine.stateGas) (fun p => p.2.machine.stateGas = s.machine.stateGas)
      (s.pop) :=
  Walk.liftMachineValue (Machine.pop_meter s.machine)

theorem Frame.State.popToNat_meter (s : Frame.State) :
    Walk (·.machine.stateGas = s.machine.stateGas) (fun p => p.2.machine.stateGas = s.machine.stateGas)
      (s.popToNat) :=
  Walk.liftMachineValue (Machine.popToNat_meter s.machine)

theorem Frame.State.popToAddress_meter (s : Frame.State) :
    Walk (·.machine.stateGas = s.machine.stateGas) (fun p => p.2.machine.stateGas = s.machine.stateGas)
      (s.popToAddress) :=
  Walk.liftMachineValue (Machine.popToAddress_meter s.machine)

theorem Frame.State.popN_meter (s : Frame.State) (n : Nat) :
    Walk (·.machine.stateGas = s.machine.stateGas) (fun p => p.2.machine.stateGas = s.machine.stateGas)
      (s.popN n) :=
  Walk.liftMachineValue (core := (Machine.popN · n)) (Machine.popN_meter s.machine n)


/-- Walk the binds of an instruction, keeping the incoming meter on both outcomes.
The leaves touch the stack, the memory, the execution gas or the world. -/
local macro "meter_leaf" : tactic => `(tactic| first
  | assumption
  | rfl
  | (solve | simp only [Walk.ok_iff, Walk.error_iff, MWalk.ok_iff, MWalk.error_iff] at * <;> assumption))

local macro "meter_known" : tactic => `(tactic| first
  | (apply Walk.meter (Frame.State.popToAddress_meter _); meter_leaf)
  | (apply Walk.meter (Frame.State.popToNat_meter _); meter_leaf)
  | (apply Walk.meter (Frame.State.popN_meter _ _); meter_leaf)
  | (apply Walk.meter (Frame.State.pop_meter _); meter_leaf)
  | (apply Walk.meter (Frame.State.chargeGas_meter _ _); meter_leaf)
  | (apply Walk.meter (Frame.State.pushItem_meter _ _ _); meter_leaf)
  | (apply Walk.meter (Frame.State.push_meter _ _); meter_leaf)
  | (apply Walk.meter (Frame.State.applyUnary_meter _ _ _); meter_leaf)
  | (apply Walk.meter (Frame.State.applyBinary_meter _ _ _); meter_leaf)
  | (apply Walk.meter (Frame.State.applyTernary_meter _ _ _); meter_leaf)
  | (apply MWalk.meter (Machine.popToAddress_meter _); meter_leaf)
  | (apply MWalk.meter (Machine.popToNat_meter _); meter_leaf)
  | (apply MWalk.meter (Machine.popN_meter _ _); meter_leaf)
  | (apply MWalk.meter (Machine.pop_meter _); meter_leaf)
  | (apply MWalk.meter (Machine.chargeGas_meter _ _); meter_leaf)
  | (apply MWalk.meter (Machine.pushItem_meter _ _ _); meter_leaf)
  | (apply MWalk.meter (Machine.push_meter _ _); meter_leaf)
  | (apply MWalk.meter (Machine.applyUnary_meter _ _ _); meter_leaf)
  | (apply MWalk.meter (Machine.applyBinary_meter _ _ _); meter_leaf)
  | (apply MWalk.meter (Machine.applyTernary_meter _ _ _); meter_leaf)
  | (apply Walk.assert (H := (·.machine.stateGas = _)); meter_leaf)
  | (apply MWalk.assert (H := (·.stateGas = _)); meter_leaf))

local macro "meter_walk" : tactic => `(tactic| repeat' first
  | meter_leaf
  | meter_known
  | (apply Walk.bind (by meter_known); first | intro ⟨_, _⟩ _ | intro _ _; try dsimp only at *)
  | (apply MWalk.bind (by meter_known); first | intro ⟨_, _⟩ _ | intro _ _; try dsimp only at *)
  | (apply Walk.liftMachine (Hm := (·.stateGas = _)) (Pm := (·.stateGas = _)))
  | split)

/-- Jump instructions preserve the state-gas meter on both successful and exceptional exits. -/
theorem JumpOp.runCore_meter (pc : Nat) (ctx : CallContext) (s : Frame.State) (op : Jaune.JumpOp) :
    Walk (·.machine.stateGas = s.machine.stateGas) (fun p => p.2.machine.stateGas = s.machine.stateGas)
      (JumpOp.runCore pc ctx s op) := by
  cases op <;> simp only [JumpOp.runCore]
  case jumpdest =>
    refine Walk.bind (Frame.State.chargeGas_meter s _) ?_
    intro _ h
    exact h
  case jump =>
    refine Walk.bind (Frame.State.pop_meter _) ?_
    intro ⟨dest, s'⟩ hs'
    refine Walk.bind (Walk.meter (Frame.State.chargeGas_meter s' _) hs') ?_
    intro s'' hs''
    refine Walk.bind (Walk.assert (H := (·.machine.stateGas = s.machine.stateGas)) hs'') ?_
    intro _ _
    exact hs''
  case jumpi =>
    meter_walk


private theorem mcases {α : Type} {H : Machine → Prop} {P : α → Prop}
    {x : Except (ExceptionalHalt × Machine) α}
    (h : MWalk H P x) : (∀ e m, x = .error (e, m) → H m) ∧ (∀ a, x = .ok a → P a) := by
  constructor
  · intro e m he; subst he; exact h
  · intro a ha; subst ha; exact h

/-- A lifted machine step keeps the meter when the step does, on both channels. -/
private theorem liftMachine_meter {s : Frame.State}
    {core : Machine → Except (ExceptionalHalt × Machine) Machine}
    (h : (match core s.machine with | .ok out | .error (_, out) => out.stateGas) = s.machine.stateGas) :
    Walk (·.machine.stateGas = s.machine.stateGas) (·.machine.stateGas = s.machine.stateGas)
      (s.liftMachine core) := by
  unfold Frame.State.liftMachine
  split <;> rename_i he <;> rw [he] at h <;> exact h

private theorem ShuffleRow.step_stateGas (row : ShuffleRow) (o : OpcodeRules) (m : Machine) :
    (match row.step o m with | .ok out | .error (_, out) => out.stateGas) = m.stateGas := by
  have hf := ShuffleRow.step_frame row o m
  cases he : row.step o m with
  | ok out => rw [he] at hf; obtain ⟨_, _, _, rfl⟩ := hf; rfl
  | error p => obtain ⟨e, out⟩ := p; rw [he] at hf; obtain ⟨_, _, _, rfl⟩ := hf; rfl

private theorem MemoryRow.step_stateGas (row : MemoryRow) (o : OpcodeRules) (ctx : CallContext)
    (m : Machine) :
    (match row.step o ctx m with | .ok out | .error (_, out) => out.stateGas) = m.stateGas := by
  cases he : row.step o ctx m with
  | ok out => exact (MemoryRow.step_ok he).2.choose_spec.choose_spec.choose_spec.2.2.2.2.1
  | error p =>
    obtain ⟨e, out⟩ := p
    rcases MemoryRow.step_error he with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ |
      ⟨_, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ <;> rfl

/-- The meter of a step of the Read or Store families, read on the machine of either channel. -/
private def TouchMeter {τ : Type} (g : StateGasMeter) :
    Except (ExceptionalHalt × Machine × τ) (Machine × τ) → Prop
  | .error (_, m, _) => m.stateGas = g
  | .ok (m, _) => m.stateGas = g

/-- An `SSTORE` row with no state-gas charge or credit keeps the meter. -/
private theorem SstoreRow.step_meter (row : SstoreRow) (isStatic : Bool) (slot : U256 → SlotView)
    (m : Machine) (hc : ∀ a b d, row.stateGasCost a b d = 0)
    (hr : ∀ a b d, row.stateGasRefund a b d = 0) :
    TouchMeter m.stateGas (row.step isStatic slot m) := by
  unfold SstoreRow.step
  split
  · rfl
  · have p1 := mcases (Machine.pop_meter m)
    split
    · rename_i e m' he; exact p1.1 _ _ he
    · rename_i key m₁ he
      have e1 : m₁.stateGas = m.stateGas := p1.2 _ he
      have p2 := mcases (Machine.pop_meter m₁)
      split
      · rename_i e m' he'; exact (p2.1 _ _ he').trans e1
      · rename_i v m₂ he'
        have e2 : m₂.stateGas = m.stateGas := (p2.2 _ he').trans e1
        dsimp only
        split
        · exact e2
        · simp only [hr, hc, Machine.creditStateGasRefund_zero, Machine.chargeStateGas_zero]
          have p3 := mcases (Machine.chargeGas_meter m₂
            (row.gasCost (row.tracksWarmth && (slot key).cold) v (slot key).original (slot key).current))
          split
          · rename_i e m' h5; exact (p3.1 _ _ h5).trans e2
          · rename_i m₄ h5
            have e4 := (p3.2 _ h5).trans e2
            split
            · exact e4
            · exact e4

/-- `TSTORE` keeps the meter. -/
private theorem TstoreRow.step_meter (row : TstoreRow) (o : OpcodeRules) (isStatic : Bool)
    (m : Machine) : TouchMeter m.stateGas (row.step o isStatic m) := by
  unfold TstoreRow.step
  split
  · rfl
  · split
    · rfl
    · have p1 := mcases (Machine.pop_meter m)
      split
      · rename_i e m' he; exact p1.1 _ _ he
      · rename_i key m₁ he
        have e1 : m₁.stateGas = m.stateGas := p1.2 _ he
        have p2 := mcases (Machine.pop_meter m₁)
        split
        · rename_i e m' he'; exact (p2.1 _ _ he').trans e1
        · rename_i v m₂ he'
          have e2 : m₂.stateGas = m.stateGas := (p2.2 _ he').trans e1
          have p3 := mcases (Machine.chargeGas_meter m₂ row.gasCost)
          split
          · rename_i e m' h5; exact (p3.1 _ _ h5).trans e2
          · rename_i m₃ h5
            have e3 := (p3.2 _ h5).trans e2
            split
            · exact e3
            · exact e3

/-- A family step keeps the incoming meter when state gas is disabled: only `SSTORE`'s state-gas
charge and credit could move it, and its row has none without state-gas rules. -/
theorem Family.run_meter (f : Family) (x : Frame.Running)
    (hn : x.context.block.rules.stateGas = none) :
    Walk (·.machine.stateGas = x.state.machine.stateGas) (·.machine.stateGas = x.state.machine.stateGas)
      (f.run x) := by
  cases f with
  | word row => exact liftMachine_meter (WordRow.step_stateGas row _ _ _)
  | shuffle row => exact liftMachine_meter (ShuffleRow.step_stateGas row _ _)
  | memory row => exact liftMachine_meter (MemoryRow.step_stateGas row _ _ _)
  | log row =>
    have hf := LogRow.step_frame row x.context x.state.machine
    show Walk _ _ (x.state.liftLog (row.step x.context x.state.machine))
    unfold Frame.State.liftLog
    split <;> rename_i he <;> rw [he] at hf
    · exact hf.2.1
    · exact hf.2.1
  | read row =>
    show Walk _ _ (x.state.liftRead _ _)
    unfold Frame.State.liftRead
    split <;> rename_i he
    · show (Frame.State.machine _).stateGas = _
      rw [(Frame.State.applyReadTouch_keeps _ _ _).1]
      exact (ReadRow.step_error he).1
    · show (Frame.State.machine _).stateGas = _
      rw [(Frame.State.applyReadTouch_keeps _ _ _).1]
      exact (ReadRow.step_ok he).2.choose_spec.choose_spec.2.2.1
  | store kind =>
    cases kind with
    | persistent =>
      have hs := SstoreRow.step_meter (SstoreRow.ofRules x.context.block.rules) x.context.isStatic
        (fun k => x.state.slotView x.context k) x.state.machine
        (by intro a b d; simp [SstoreRow.ofRules, hn]) (by intro a b d; simp [SstoreRow.ofRules, hn])
      show Walk _ _ (x.state.liftStore _ _ _)
      unfold Frame.State.liftStore
      split <;> rename_i he <;> rw [he] at hs
      all_goals
        show (Frame.State.machine _).stateGas = _
        rw [Frame.State.applyStoreTouch_machine]
        exact hs
    | transient =>
      have hs := TstoreRow.step_meter (TstoreRow.ofRules x.context.block.rules)
        x.context.block.rules.opcodes x.context.isStatic x.state.machine
      show Walk _ _ (x.state.liftStore _ _ _)
      unfold Frame.State.liftStore
      split <;> rename_i he <;> rw [he] at hs
      all_goals
        show (Frame.State.machine _).stateGas = _
        rw [Frame.State.applyStoreTouch_machine]
        exact hs

/-- A plain instruction preserves the incoming meter when state gas is disabled. The state-gas-enabled storage
branches take a separate charge and are excluded by the rules premise. -/
theorem PlainOp.runCore_meter (pc : Nat) (ctx : CallContext) (s : Frame.State)
    (hn : ctx.block.rules.stateGas = none) (op : Jaune.PlainOp) :
    Walk (·.machine.stateGas = s.machine.stateGas) (·.machine.stateGas = s.machine.stateGas)
      (PlainOp.runCore pc ctx s op) :=
  Family.run_meter (PlainOp.family op) ⟨pc, ctx, s⟩ hn

private def exitMeter (g : StateGasMeter) : Except Fault Frame.Exit → Prop
  | .ok exit => exit.state.machine.stateGas = g
  | .error _ => True

private theorem catchHalt_meter {g : StateGasMeter} {x} (hx : Walk (·.machine.stateGas = g)
    (exitMeter g) x) : exitMeter g (Frame.Exit.catchHalt x) := by
  cases x with
  | error e => cases e; exact hx
  | ok result => exact hx

private theorem creditBeneficiary_meter (rules : ForkRules) (a : Address) (v : U256) (s : Frame.State) :
    (s.creditBeneficiary rules a v).machine.stateGas = s.machine.stateGas := by
  unfold Frame.State.creditBeneficiary
  split <;> rfl

private theorem selfdestruct_meter (ctx : CallContext) (s : Frame.State)
    (hn : ctx.block.rules.stateGas = none) :
    exitMeter s.machine.stateGas (HaltOp.run ctx s .selfdestruct) := by
  simp only [HaltOp.run, hn]
  apply catchHalt_meter
  refine Walk.bind (Frame.State.popToAddress_meter s) ?_
  intro ⟨donee, s₁⟩ h₁
  dsimp only at *
  refine Walk.bind (Walk.meter (Frame.State.chargeGas_meter _ _) ?_) ?_
  · split <;> first | exact h₁ | (split <;> exact h₁)
  · intro s₂ h₂
    refine Walk.bind (Walk.assert (H := (·.machine.stateGas = s.machine.stateGas)) h₂) ?_
    intro _ _
    unfold Frame.State.subtractBalance
    cases hs : s₂.world.subtractBalance ctx.recipient _ with
    | none => trivial
    | some world =>
      dsimp only [Option.map]
      split
      · unfold Frame.State.creditSelfdestructRefund
        split <;> exact (creditBeneficiary_meter _ _ _ _).trans h₂
      · exact (creditBeneficiary_meter _ _ _ _).trans h₂

/-- Before state gas, a halt instruction leaves the meter intact, including exceptional exits. -/
theorem HaltOp.run_meter (ctx : CallContext) (s : Frame.State) (op : Jaune.HaltOp)
    (hn : ctx.block.rules.stateGas = none) {exit} (h : HaltOp.run ctx s op = .ok exit) :
    exit.state.machine.stateGas = s.machine.stateGas := by
  suffices hp : exitMeter s.machine.stateGas (HaltOp.run ctx s op) by
    rw [h] at hp
    exact hp
  cases op with
  | stop => rfl
  | selfdestruct => exact selfdestruct_meter ctx s hn
  | revert | return_ =>
    apply catchHalt_meter
    refine Walk.bind (Frame.State.popToNat_meter s) ?_
    intro ⟨start, s₁⟩ h₁
    refine Walk.bind (Walk.meter (Frame.State.popToNat_meter s₁) h₁) ?_
    intro ⟨size, s₂⟩ h₂
    refine Walk.bind (Walk.meter (Frame.State.chargeGas_meter s₂ _) h₂) ?_
    intro s₃ h₃
    exact h₃

/-- Under rules without state gas a spawn gives its child zero state gas and saves
a caller with the disabled meter. -/
def Frame.SpawnStateGasZero (child : Frame) : Prop :=
  child.message.context.block.rules.stateGas = none ∧ child.message.stateGasGrant = 0 ∧
    child.checkpoint.machine.stateGas = .zero

def MessageOp.Outcome.StateGasZero : MessageOp.Outcome → Prop
  | .done result => Walk (·.machine.stateGas = .zero) (·.machine.stateGas = .zero) result
  | .spawn child _ => Frame.SpawnStateGasZero child

private theorem outcome_stateGasZero {x} (h : Walk (·.machine.stateGas = .zero)
    MessageOp.Outcome.StateGasZero x) : (MessageOp.Outcome.ofExcept x).StateGasZero := by
  cases x <;> exact h

theorem genericCall.step_stateGasZero {ctx : CallContext} {s : Frame.State}
    (hn : ctx.block.rules.stateGas = none) (hs : s.machine.stateGas = .zero)
    (gas : Nat) (value : U256) (caller target codeAddress : Address)
    (transfers isStaticcall : Bool) (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disabled : Bool) :
    (genericCall.step ctx s gas value caller target codeAddress transfers isStaticcall
      inputIndex inputSize outputIndex outputSize code disabled).StateGasZero := by
  unfold genericCall.step
  split
  · apply outcome_stateGasZero
    refine Walk.bind (Walk.meter (Frame.State.push_meter _ _) hs) ?_
    intro _ h; exact h
  · exact ⟨hn, rfl, hs⟩

theorem genericCreate.step_stateGasZero {ctx : CallContext} {s : Frame.State}
    (hn : ctx.block.rules.stateGas = none) (hs : s.machine.stateGas = .zero)
    (endowment : U256) (address : Address) (start size : Nat) :
    (genericCreate.step ctx s endowment address start size).StateGasZero := by
  unfold genericCreate.step
  apply outcome_stateGasZero
  refine Walk.bind (Walk.assert (H := (·.machine.stateGas = .zero)) hs) ?_
  intro _ _
  refine Walk.bind (Walk.assert (H := (·.machine.stateGas = .zero)) hs) ?_
  intro _ _
  dsimp only
  split
  · refine Walk.bind (Walk.meter (Frame.State.push_meter _ _) hs) ?_
    intro _ h; exact h
  · split
    · refine Walk.bind (Walk.meter (Frame.State.push_meter _ _) hs) ?_
      intro _ h; exact h
    · exact ⟨hn, rfl, hs⟩

private theorem delegation_meter (rules : ForkRules) (s : Frame.State) (address : Address) :
    (ForkRules.accessDelegation rules s address).2.2.2.2.machine.stateGas = s.machine.stateGas := by
  unfold ForkRules.accessDelegation
  split
  · unfold GasSchedule.accessDelegation
    try dsimp only
    split <;> rfl
  · rfl

/-- Follow the stack pops, the execution-gas charge and the optional static check.
The remaining computation either pushes a failed call status or spawns a child. -/
local macro "message_meter" : tactic => `(tactic| (
  apply outcome_stateGasZero
  repeat' first
    | (refine Walk.bind (Walk.meter (Frame.State.pop_meter _) (by assumption)) ?_; intro ⟨_, _⟩ _)
    | (refine Walk.bind (Walk.meter (Frame.State.popToAddress_meter _) (by assumption)) ?_; intro ⟨_, _⟩ _)
    | (refine Walk.bind (Walk.meter (Frame.State.popToNat_meter _) (by assumption)) ?_; intro ⟨_, _⟩ _)
  dsimp only at *
  refine Walk.bind (Walk.meter (Frame.State.chargeGas_meter _ _) ?_) ?_
  · first | assumption | (rw [delegation_meter]; split <;> assumption)
  · intro s' h'
    try (refine Walk.bind (Walk.assert (H := (·.machine.stateGas = .zero)) h') ?_; intro _ _)
    first
    | (apply genericCreate.step_stateGasZero <;> assumption)
    | (apply genericCall.step_stateGasZero <;> assumption)
    | (split
       · refine Walk.bind (Walk.meter (Frame.State.push_meter _ _) h') ?_
         intro _ h; exact h
       · apply genericCall.step_stateGasZero <;> assumption)))

private theorem call_meter {ctx : CallContext} {s : Frame.State}
    (hn : ctx.block.rules.stateGas = none) (hs : s.machine.stateGas = .zero) :
    (MessageOp.step ctx s .call).StateGasZero := by
  simp only [MessageOp.step, hn]
  message_meter

private theorem callcode_meter {ctx : CallContext} {s : Frame.State}
    (hn : ctx.block.rules.stateGas = none) (hs : s.machine.stateGas = .zero) :
    (MessageOp.step ctx s .callcode).StateGasZero := by
  simp only [MessageOp.step, hn]
  message_meter

private theorem delegatecall_meter {ctx : CallContext} {s : Frame.State}
    (hn : ctx.block.rules.stateGas = none) (hs : s.machine.stateGas = .zero) :
    (MessageOp.step ctx s .delegatecall).StateGasZero := by
  simp only [MessageOp.step, hn]
  message_meter

private theorem staticcall_meter {ctx : CallContext} {s : Frame.State}
    (hn : ctx.block.rules.stateGas = none) (hs : s.machine.stateGas = .zero) :
    (MessageOp.step ctx s .staticcall).StateGasZero := by
  simp only [MessageOp.step, hn]
  message_meter

private theorem create_meter {ctx : CallContext} {s : Frame.State}
    (hn : ctx.block.rules.stateGas = none) (hs : s.machine.stateGas = .zero) :
    (MessageOp.step ctx s .create).StateGasZero := by
  simp only [MessageOp.step, hn]
  message_meter

private theorem create2_meter {ctx : CallContext} {s : Frame.State}
    (hn : ctx.block.rules.stateGas = none) (hs : s.machine.stateGas = .zero) :
    (MessageOp.step ctx s .create2).StateGasZero := by
  simp only [MessageOp.step, hn]
  split
  · message_meter
  · exact hs

/-- Every message instruction keeps the zero meter at each return and at each spawn. -/
theorem MessageOp.step_stateGasZero {ctx : CallContext} {s : Frame.State}
    (hn : ctx.block.rules.stateGas = none) (hs : s.machine.stateGas = .zero)
    (op : Jaune.MessageOp) : (MessageOp.step ctx s op).StateGasZero := by
  cases op with
  | call => exact call_meter hn hs
  | callcode => exact callcode_meter hn hs
  | delegatecall => exact delegatecall_meter hn hs
  | staticcall => exact staticcall_meter hn hs
  | create => exact create_meter hn hs
  | create2 => exact create2_meter hn hs

def Step.StateGasZero : Step → Prop
  | .exit e => e.state.machine.stateGas = .zero
  | .next _ s => s.machine.stateGas = .zero
  | .spawn child _ _ => Frame.SpawnStateGasZero child

theorem Step.ofHalt_stateGasZero (pc : Nat) {x}
    (h : Walk (·.machine.stateGas = .zero) (·.machine.stateGas = .zero) x) :
    (Step.ofHalt pc x).StateGasZero := by
  cases x with
  | error e => cases e; exact h
  | ok _ => exact h

theorem Step.ofJump_stateGasZero (running : Frame.Running) (op : Jaune.JumpOp)
    (h : running.state.machine.stateGas = .zero) : (Step.ofJump (JumpOp.run running op)).StateGasZero := by
  have hj := JumpOp.runCore_meter running.pc running.context running.state op
  unfold JumpOp.run
  split
  · rename_i e he
    rw [he] at hj
    cases e
    exact hj.trans h
  · rename_i pc s he
    rw [he] at hj
    exact hj.trans h

theorem MessageOp.Outcome.toStep_stateGasZero (pc : Nat) {x : MessageOp.Outcome}
    (h : x.StateGasZero) : (x.toStep pc).StateGasZero := by
  cases x with
  | done _ => exact Step.ofHalt_stateGasZero pc h
  | spawn _ _ => exact h

theorem NextOp.step_stateGasZero (running : Frame.Running)
    (hn : running.context.block.rules.stateGas = none) (hs : running.state.machine.stateGas = .zero)
    (op : Jaune.NextOp) : (NextOp.step running op).StateGasZero := by
  cases op with
  | plain p =>
    apply Step.ofHalt_stateGasZero
    exact Walk.meter (PlainOp.runCore_meter _ _ _ hn p) hs
  | message m =>
    exact MessageOp.Outcome.toStep_stateGasZero _ (MessageOp.step_stateGasZero hn hs m)
  | push xs h =>
    exact Step.ofHalt_stateGasZero _ (Walk.meter (Family.run_meter _ running hn) hs)
  | dupn imm | swapn imm | exchange imm =>
    exact Step.ofHalt_stateGasZero _ (Walk.meter (Family.run_meter _ running hn) hs)

theorem step_stateGasZero {running : Frame.Running} {next : Step}
    (hn : running.context.block.rules.stateGas = none) (hs : running.state.machine.stateGas = .zero)
    (h : step running = .ok next) : next.StateGasZero := by
  unfold step at h
  split at h
  · cases h; exact hs
  · cases h; exact NextOp.step_stateGasZero _ hn hs _
  · cases h; exact Step.ofJump_stateGasZero _ _ hs
  · rename_i op _
    cases he : HaltOp.run running.context running.state op with
    | error e => rw [he] at h; cases h
    | ok exit =>
      rw [he] at h
      cases h
      exact (HaltOp.run_meter _ _ op hn he).trans hs

end Jaune.Checked
