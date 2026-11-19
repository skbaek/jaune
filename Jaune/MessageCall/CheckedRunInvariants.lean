import Jaune.CheckedSufficiencyWalk
import Jaune.MessageCall.RunInvariants
import Jaune.Instructions.ReadFacts
import Jaune.Instructions.StoreFacts
import Jaune.Instructions.Log

/-! A running machine preserves its committed spill and has room for the caller's return push
after a spawning opcode pops its arguments. -/
namespace Jaune.Checked

open Jaune

namespace RunInvariants

/-- The machine has the given committed spill and room for the specified number of words. -/
def MInv (c n : Nat) (m : Machine) : Prop :=
  m.stateGas.committedSpill = c ∧ m.stack.length + n ≤ 1024

abbrev Inv (c n : Nat) (s : Frame.State) : Prop := MInv c n s.machine

theorem MInv.weaken {c n k : Nat} {m : Machine} (h : MInv c n m) (hk : k ≤ n) : MInv c k m :=
  ⟨h.1, by have := h.2; omega⟩

namespace Machine

variable {c n : Nat} {m : Machine}

theorem push_inv (x : U256) (h : MInv c n m) :
    MWalk (MInv c 0) (MInv c (n - 1)) (m.push x) := by
  unfold Machine.push
  split
  · refine ⟨h.1, ?_⟩
    have hl := h.2
    change (x :: m.stack).length + (n - 1) ≤ 1024
    rw [List.length_cons]
    omega
  · exact h.weaken (Nat.zero_le _)

theorem pop_inv (h : MInv c n m) :
    MWalk (MInv c 0) (fun p => MInv c (n + 1) p.2) m.pop := by
  unfold Machine.pop
  split
  · exact h.weaken (Nat.zero_le _)
  · rename_i x xs hx
    refine ⟨h.1, ?_⟩
    have hl := h.2
    rw [hx, List.length_cons] at hl
    change xs.length + (n + 1) ≤ 1024
    omega

theorem chargeGas_inv (cost : Nat) (h : MInv c n m) :
    MWalk (MInv c 0) (MInv c n) (m.chargeGas cost) := by
  unfold Machine.chargeGas
  split
  · exact h.weaken (Nat.zero_le _)
  · exact h

theorem chargeStateGas_inv (amount : Nat) (h : MInv c n m) :
    MWalk (MInv c 0) (MInv c n) (m.chargeStateGas amount) := by
  unfold Machine.chargeStateGas
  split
  · exact h
  · split
    · exact h
    · exact h.weaken (Nat.zero_le _)

theorem popToNat_inv (h : MInv c n m) :
    MWalk (MInv c 0) (fun p => MInv c (n + 1) p.2) m.popToNat := by
  unfold Machine.popToNat
  have hw := pop_inv h
  split <;> rename_i he <;> rw [he] at hw <;> exact hw

theorem popToAddress_inv (h : MInv c n m) :
    MWalk (MInv c 0) (fun p => MInv c (n + 1) p.2) m.popToAddress := by
  unfold Machine.popToAddress
  have hw := pop_inv h
  split <;> rename_i he <;> rw [he] at hw <;> exact hw

theorem popN_inv (k : Nat) (h : MInv c n m) :
    MWalk (MInv c 0) (fun p => MInv c (n + k) p.2) (m.popN k) := by
  induction k generalizing m n with
  | zero => exact h
  | succ k ih =>
    unfold Machine.popN
    have first := pop_inv h
    split
    · rename_i he; rw [he] at first; exact first
    · rename_i x m' he
      rw [he] at first
      have next := ih (n := n+1) (m := m') first
      split
      · rename_i he; rw [he] at next; exact next
      · rename_i xs m'' he
        rw [he] at next
        have hn : MInv c ((n+1)+k) m'' := next
        exact hn.weaken (by omega)

local macro "machine_prefix " law:term : tactic => `(tactic| (
  have hw := $law
  split <;> rename_i he <;> rw [he] at hw
  all_goals first | exact hw | simp only [MWalk.ok_iff] at hw))

theorem pushItem_inv (x : U256) (cost : Nat) (h : MInv c n m) :
    MWalk (MInv c 0) (MInv c (n - 1)) (m.pushItem x cost) := by
  unfold Machine.pushItem
  machine_prefix (chargeGas_inv cost h)
  exact push_inv (n := n) _ (by assumption)

theorem applyUnary_inv (f : U256 → U256) (cost : Nat) (h : MInv c n m) :
    MWalk (MInv c 0) (MInv c n) (m.applyUnary f cost) := by
  unfold Machine.applyUnary
  machine_prefix (pop_inv h)
  exact pushItem_inv (n := n+1) _ _ (by assumption)

theorem applyBinary_inv (f : U256 → U256 → U256) (cost : Nat) (h : MInv c n m) :
    MWalk (MInv c 0) (MInv c (n + 1)) (m.applyBinary f cost) := by
  unfold Machine.applyBinary
  machine_prefix (pop_inv h)
  machine_prefix (pop_inv (by assumption))
  exact pushItem_inv (n := n+2) _ _ (by assumption)

theorem applyTernary_inv (f : U256 → U256 → U256 → U256) (cost : Nat) (h : MInv c n m) :
    MWalk (MInv c 0) (MInv c (n + 2)) (m.applyTernary f cost) := by
  unfold Machine.applyTernary
  machine_prefix (pop_inv h)
  machine_prefix (pop_inv (by assumption))
  machine_prefix (pop_inv (by assumption))
  exact pushItem_inv (n := n+3) _ _ (by assumption)

end Machine

namespace State

variable {c n : Nat} {s : Frame.State}

theorem push_inv (x : U256) (h : Inv c n s) :
    Walk (Inv c 0) (Inv c (n - 1)) (s.push x) :=
  Walk.liftMachine (Machine.push_inv x h)

theorem pop_inv (h : Inv c n s) :
    Walk (Inv c 0) (fun p => Inv c (n + 1) p.2) s.pop :=
  Walk.liftMachineValue (Machine.pop_inv h)

theorem chargeGas_inv (cost : Nat) (h : Inv c n s) :
    Walk (Inv c 0) (Inv c n) (s.chargeGas cost) :=
  Walk.liftMachine (Machine.chargeGas_inv cost h)

theorem chargeStateGas_inv (amount : Nat) (h : Inv c n s) :
    Walk (Inv c 0) (Inv c n) (s.chargeStateGas amount) :=
  Walk.liftMachine (Machine.chargeStateGas_inv amount h)

theorem popToNat_inv (h : Inv c n s) :
    Walk (Inv c 0) (fun p => Inv c (n + 1) p.2) s.popToNat :=
  Walk.liftMachineValue (Machine.popToNat_inv h)

theorem popToAddress_inv (h : Inv c n s) :
    Walk (Inv c 0) (fun p => Inv c (n + 1) p.2) s.popToAddress :=
  Walk.liftMachineValue (Machine.popToAddress_inv h)

theorem popN_inv (k : Nat) (h : Inv c n s) :
    Walk (Inv c 0) (fun p => Inv c (n + k) p.2) (s.popN k) :=
  Walk.liftMachineValue (core := (Machine.popN · k)) (Machine.popN_inv k h)

theorem pushItem_inv (x : U256) (cost : Nat) (h : Inv c n s) :
    Walk (Inv c 0) (Inv c (n - 1)) (s.pushItem x cost) :=
  Walk.liftMachine (Machine.pushItem_inv x cost h)

theorem applyUnary_inv (f : U256 → U256) (cost : Nat) (h : Inv c n s) :
    Walk (Inv c 0) (Inv c n) (s.applyUnary f cost) :=
  Walk.liftMachine (Machine.applyUnary_inv f cost h)

theorem applyBinary_inv (f : U256 → U256 → U256) (cost : Nat) (h : Inv c n s) :
    Walk (Inv c 0) (Inv c (n + 1)) (s.applyBinary f cost) :=
  Walk.liftMachine (Machine.applyBinary_inv f cost h)

theorem applyTernary_inv (f : U256 → U256 → U256 → U256) (cost : Nat) (h : Inv c n s) :
    Walk (Inv c 0) (Inv c (n + 2)) (s.applyTernary f cost) :=
  Walk.liftMachine (Machine.applyTernary_inv f cost h)

end State

theorem State.assertDynamic_inv (ctx : CallContext) {s : Frame.State} {c n : Nat} (h : Inv c n s) :
    Walk (Inv c 0) (fun _ => True) (s.assertDynamic ctx) :=
  Walk.assert (h.weaken (Nat.zero_le _))

private theorem liftMachine_inv {c : Nat} {s : Frame.State} {P : Frame.State → Prop}
    {core : Machine → Except (ExceptionalHalt × Machine) Machine}
    (h : MWalk (MInv c 0) (fun m => P (s.withMachine m)) (core s.machine)) :
    Walk (Inv c 0) P (s.liftMachine core) := by
  unfold Frame.State.liftMachine
  rcases hc : core s.machine with ⟨e, m⟩ | m <;> rw [hc] at h <;> exact h

private theorem accessDelegation_machine (rules : ForkRules) (s : Frame.State) (a : Address) :
    (ForkRules.accessDelegation rules s a).2.2.2.2.machine = s.machine := by
  unfold ForkRules.accessDelegation GasSchedule.accessDelegation
  split
  · dsimp only
    split <;> rfl
  · rfl

private theorem completeDelegation_machine (s : Frame.State) (b : Bool) (a : Address) :
    (completeDelegationAccess s b a).2.machine = s.machine := by
  cases b <;> rfl

local macro "inv_leaf" : tactic => `(tactic| first
  | assumption
  | trivial
  | (apply MInv.weaken (by assumption); omega)
  | (solve | simp only [Inv, accessDelegation_machine, completeDelegation_machine, Frame.State.addAccessedAddress,
        Frame.State.withSubstate_machine, Frame.State.recordAccountRead, Frame.State.withTrail_machine,
        Frame.State.memExtends, Frame.State.liftMachinePure_machine, Frame.State.withMachine_machine] at * <;>
      (first | assumption | (apply MInv.weaken (by assumption); omega)))
  | (solve | simp only [Inv, MInv, Walk.ok_iff, Walk.error_iff, MWalk.ok_iff, MWalk.error_iff,
        Machine.memWrite, Machine.memRead, Machine.memExtends, List.length_set,
        Frame.State.withMachine_machine, Frame.State.withWorld_machine, Frame.State.withTrail_machine,
        Frame.State.withSubstate_machine, Frame.State.liftMachinePure_machine] at * <;>
      (first | trivial | (constructor <;> omega))))

open Lean Elab Tactic Meta in
/-- Thread the stack bound through the primitive at the head of a bind or its final value. -/
elab "inv_primitive" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let machine := target.isAppOf ``MWalk
  unless machine || target.isAppOf ``Walk do throwError "expected a walk"
  let x := target.appArg!.headBeta
  let bound := x.isAppOf ``Bind.bind
  let op := if bound then (x.getArg! 4).headBeta else x
  let some head := op.getAppFn.constName? | throwError "expected a primitive"
  if head == ``Frame.State.liftMachine && !bound then
    evalTactic (← `(tactic| apply liftMachine_inv))
    return
  let (rule, arity, pair) ← match head with
    | ``Frame.State.pop | ``Machine.pop =>
      pure ("pop_inv", 0, true)
    | ``Frame.State.popToNat | ``Machine.popToNat =>
      pure ("popToNat_inv", 0, true)
    | ``Frame.State.popToAddress | ``Machine.popToAddress =>
      pure ("popToAddress_inv", 0, true)
    | ``Frame.State.popN | ``Machine.popN => pure ("popN_inv", 1, true)
    | ``Frame.State.chargeGas | ``Machine.chargeGas => pure ("chargeGas_inv", 1, false)
    | ``Frame.State.chargeStateGas | ``Machine.chargeStateGas => pure ("chargeStateGas_inv", 1, false)
    | ``Frame.State.push | ``Machine.push => pure ("push_inv", 1, false)
    | ``Frame.State.pushItem | ``Machine.pushItem => pure ("pushItem_inv", 2, false)
    | ``Frame.State.applyUnary | ``Machine.applyUnary => pure ("applyUnary_inv", 2, false)
    | ``Frame.State.applyBinary | ``Machine.applyBinary => pure ("applyBinary_inv", 2, false)
    | ``Frame.State.applyTernary | ``Machine.applyTernary => pure ("applyTernary_inv", 2, false)
    | ``Frame.State.assertDynamic => pure ("assertDynamic_inv", 1, false)
    | ``Except.assert => pure ("assert", 0, false)
    | _ => throwError "unknown primitive"
  let group := if rule == "assert" then (if machine then ``MWalk else ``Walk)
    else (if machine then `Jaune.Checked.RunInvariants.Machine else `Jaune.Checked.RunInvariants.State)
  let rule := mkIdent <| group.str rule
  let fact ← match arity with
    | 0 => `($rule (by inv_leaf))
    | 1 => `($rule _ (by inv_leaf))
    | _ => `($rule _ _ (by inv_leaf))
  let combinator := mkIdent (if machine then (if bound then ``MWalk.bind else ``MWalk.mono)
    else (if bound then ``Walk.bind else ``Walk.mono))
  if pair then
    evalTactic (← `(tactic| (refine $combinator $fact ?_; intro ⟨_, _⟩ _; try dsimp only at *)))
  else
    evalTactic (← `(tactic| (refine $combinator $fact ?_; intro _ _; try dsimp only at *)))

local macro "inv_walk" : tactic => `(tactic| repeat' (first | inv_primitive | inv_leaf | split))

theorem Machine.popWords_inv {c : Nat} {m : Machine} (a : Fin 4) (h : MInv c 0 m) :
    MWalk (MInv c 0) (fun p => MInv c 0 p.2) (m.popWords a) := by
  match a with
  | 0 => exact h
  | 1 => exact MWalk.mono (Machine.pop_inv h) fun _ hp => hp.weaken (Nat.zero_le _)
  | 2 =>
    refine MWalk.bind (Machine.pop_inv h) ?_
    rintro ⟨x, m₁⟩ h₁
    refine MWalk.bind (Machine.pop_inv (h₁.weaken (Nat.zero_le _))) ?_
    rintro ⟨y, m₂⟩ h₂
    exact h₂.weaken (Nat.zero_le _)
  | 3 =>
    refine MWalk.bind (Machine.pop_inv h) ?_
    rintro ⟨x, m₁⟩ h₁
    refine MWalk.bind (Machine.pop_inv (h₁.weaken (Nat.zero_le _))) ?_
    rintro ⟨y, m₂⟩ h₂
    refine MWalk.bind (Machine.pop_inv (h₂.weaken (Nat.zero_le _))) ?_
    rintro ⟨z, m₃⟩ h₃
    exact h₃.weaken (Nat.zero_le _)

/-- The Word family's step keeps the bound (S4: one walk for every Word row). -/
theorem WordRow.step_inv (row : WordRow) (o : OpcodeRules) (e : Word.Env) {c : Nat} {m : Machine}
    (h : MInv c 0 m) : MWalk (MInv c 0) (MInv c 0) (row.step o e m) := by
  unfold WordRow.step
  cases ha : row.available o
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h
  · simp only [↓reduceIte]
    refine MWalk.bind (Machine.popWords_inv row.arity h) ?_
    rintro ⟨args, m₁⟩ h₁
    refine MWalk.bind (Machine.chargeGas_inv _ h₁) ?_
    intro m₂ h₂
    split
    · exact h₂
    · exact Machine.push_inv _ h₂

/-- The Shuffle family's step keeps the bound. -/
theorem ShuffleRow.step_inv (row : ShuffleRow) (o : OpcodeRules) {c : Nat} {m : Machine}
    (h : MInv c 0 m) : MWalk (MInv c 0) (MInv c 0) (row.step o m) := by
  unfold ShuffleRow.step
  cases ha : row.available o
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h
  · simp only [↓reduceIte]
    refine MWalk.bind (Machine.chargeGas_inv _ h) ?_
    intro m₁ h₁
    split
    · exact h₁
    · rename_i sh
      unfold Shuffle.run
      split
      · split
        · exact h₁
        · exact Machine.push_inv _ h₁
      · split
        · exact h₁
        · rename_i st he
          exact ⟨h₁.1, by
            have hl := Jaune.RunInvariants.List.swap_length he
            have := h₁.2
            change st.length + 0 ≤ 1024
            simp only [hl] at *; omega⟩
      · split
        · exact h₁
        · rename_i st he
          exact ⟨h₁.1, by
            have hl := Jaune.RunInvariants.List.exchange_length he
            have := h₁.2
            change st.length + 0 ≤ 1024
            simp only [hl] at *; omega⟩

/-- The Memory family's step keeps the bound. -/
theorem MemoryRow.step_inv (row : MemoryRow) (o : OpcodeRules) (ctx : CallContext) {c : Nat}
    {m : Machine} (h : MInv c 0 m) : MWalk (MInv c 0) (MInv c 0) (row.step o ctx m) := by
  unfold MemoryRow.step
  cases ha : row.available o
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h
  · simp only [↓reduceIte]
    refine MWalk.bind (Machine.popWords_inv row.arity h) ?_
    rintro ⟨args, m₁⟩ h₁
    refine MWalk.bind (Machine.chargeGas_inv _ h₁) ?_
    intro m₂ h₂
    split
    · exact h₂
    · exact h₂
    · rename_i memory x _
      exact MWalk.mono (Machine.push_inv (n := 0) x
        (⟨h₂.1, h₂.2⟩ : MInv c 0 { m₂ with memory := memory })) (fun _ hp => hp)

/-- The Log family's step keeps the bound. -/
theorem LogRow.step_inv (row : LogRow) (ctx : CallContext) {c : Nat} {m : Machine}
    (h : MInv c 0 m) : MWalk (MInv c 0) (fun p => MInv c 0 p.1) (row.step ctx m) := by
  unfold LogRow.step
  inv_walk

/-- A step of the Read or Store families: the machine on both channels, with a touch beside it. -/
private def TouchInv {τ : Type} (c : Nat) :
    Except (ExceptionalHalt × Machine × τ) (Machine × τ) → Prop
  | .error (_, m, _) => MInv c 0 m
  | .ok (m, _) => MInv c 0 m

theorem ReadTarget.pop_inv (t : ReadTarget) {c : Nat} {m : Machine} (h : MInv c 0 m) :
    MWalk (MInv c 0) (fun p => MInv c 0 p.2) (t.pop m) := by
  cases t with
  | account => exact MWalk.mono (Machine.popToAddress_inv h) fun _ hp => hp.weaken (Nat.zero_le _)
  | slot => exact MWalk.mono (Machine.pop_inv h) fun _ hp => hp.weaken (Nat.zero_le _)
  | transient => exact MWalk.mono (Machine.pop_inv h) fun _ hp => hp.weaken (Nat.zero_le _)
  | recipient => exact h

/-- The Read family's step keeps the bound. -/
theorem ReadRow.step_inv (row : ReadRow) (rules : ForkRules) (ctx : CallContext) (v : ReadView)
    {c : Nat} {m : Machine} (h : MInv c 0 m) : TouchInv c (row.step rules ctx v m) := by
  rcases row with ⟨avail, target, price, result⟩
  unfold ReadRow.step
  dsimp only
  split
  · exact h
  · have hpop := ReadTarget.pop_inv target h
    split
    · rename_i e m' hp; exact (MWalk.cases hpop).1 _ _ hp
    · rename_i key m₁ hp
      have h₁ : MInv c 0 m₁ := (MWalk.cases hpop).2 _ hp
      cases result with
      | push f =>
        simp only [ReadResult.finish]
        have hc := MWalk.cases (Machine.chargeGas_inv (price.quote rules ctx v key).1 h₁)
        split
        · rename_i e m' he; exact hc.1 _ _ he
        · rename_i m₂ he
          have hp := MWalk.cases (Machine.push_inv (f ctx v.world key) (hc.2 _ he))
          split
          · rename_i e m' he'; exact hp.1 _ _ he'
          · rename_i m₃ he'; exact hp.2 _ he'
      | copyCode perWord =>
        simp only [ReadResult.finish]
        have p1 := MWalk.cases (Machine.popToNat_inv h₁)
        split
        · rename_i e m' he; exact p1.1 _ _ he
        · rename_i d m₂ he
          have p2 := MWalk.cases (Machine.popToNat_inv ((p1.2 _ he).weaken (Nat.zero_le _)))
          split
          · rename_i e m' he'; exact p2.1 _ _ he'
          · rename_i o m₃ he'
            have p3 := MWalk.cases (Machine.popToNat_inv ((p2.2 _ he').weaken (Nat.zero_le _)))
            split
            · rename_i e m' he''; exact p3.1 _ _ he''
            · rename_i n m₄ he''
              have h₄ : MInv c 0 m₄ := (p3.2 _ he'').weaken (Nat.zero_le _)
              split
              · rename_i e m' h5; exact (MWalk.cases (Machine.chargeGas_inv _ h₄)).1 _ _ h5
              · rename_i m₅ h5
                have h₅ := (MWalk.cases (Machine.chargeGas_inv _ h₄)).2 m₅ h5
                exact h₅

/-- The `SSTORE` row's step keeps the bound: a state-gas credit moves gas between the meters
but keeps the committed spill. -/
theorem SstoreRow.step_inv (row : SstoreRow) (isStatic : Bool) (slot : U256 → SlotView) {c : Nat}
    {m : Machine} (h : MInv c 0 m) : TouchInv c (row.step isStatic slot m) := by
  unfold SstoreRow.step
  split
  · exact h
  · have p1 := MWalk.cases (Machine.pop_inv h)
    split
    · rename_i e m' he; exact p1.1 _ _ he
    · rename_i key m₁ he
      have p2 := MWalk.cases (Machine.pop_inv ((p1.2 _ he).weaken (Nat.zero_le _)))
      split
      · rename_i e m' he'; exact p2.1 _ _ he'
      · rename_i v m₂ he'
        have h₂ : MInv c 0 m₂ := (p2.2 _ he').weaken (Nat.zero_le _)
        dsimp only
        split
        · exact h₂
        · have h₃ : MInv c 0 (m₂.creditStateGasRefund
              (row.stateGasRefund v (slot key).original (slot key).current)) := h₂
          have p3 := MWalk.cases (Machine.chargeGas_inv
            (row.gasCost (row.tracksWarmth && (slot key).cold) v (slot key).original (slot key).current) h₃)
          split
          · rename_i e m' h5; exact p3.1 _ _ h5
          · rename_i m₄ h5
            have p4 := MWalk.cases (Machine.chargeStateGas_inv
              (row.stateGasCost v (slot key).original (slot key).current) (p3.2 _ h5))
            split
            · rename_i e m' h6; exact p4.1 _ _ h6
            · rename_i m₅ h6
              split
              · exact p4.2 _ h6
              · exact p4.2 _ h6

/-- The `TSTORE` row's step keeps the bound. -/
theorem TstoreRow.step_inv (row : TstoreRow) (o : OpcodeRules) (isStatic : Bool) {c : Nat}
    {m : Machine} (h : MInv c 0 m) : TouchInv c (row.step o isStatic m) := by
  unfold TstoreRow.step
  split
  · exact h
  · split
    · exact h
    · have p1 := MWalk.cases (Machine.pop_inv h)
      split
      · rename_i e m' he; exact p1.1 _ _ he
      · rename_i key m₁ he
        have p2 := MWalk.cases (Machine.pop_inv ((p1.2 _ he).weaken (Nat.zero_le _)))
        split
        · rename_i e m' he'; exact p2.1 _ _ he'
        · rename_i v m₂ he'
          have p3 := MWalk.cases (Machine.chargeGas_inv row.gasCost ((p2.2 _ he').weaken (Nat.zero_le _)))
          split
          · rename_i e m' h5; exact p3.1 _ _ h5
          · rename_i m₃ h5
            split
            · exact p3.2 _ h5
            · exact p3.2 _ h5

/-- Every family step preserves the stack bound and the committed spill, on either exit: one
walk per family (S4), read off for every instruction by its row. -/
theorem Family.run_inv (f : Family) (x : Frame.Running) {c : Nat} (h : Inv c 0 x.state) :
    Walk (Inv c 0) (Inv c 0) (f.run x) := by
  cases f with
  | word row => exact liftMachine_inv (P := Inv c 0) (WordRow.step_inv row _ _ h)
  | shuffle row => exact liftMachine_inv (P := Inv c 0) (ShuffleRow.step_inv row _ h)
  | memory row => exact liftMachine_inv (P := Inv c 0) (MemoryRow.step_inv row _ _ h)
  | log row =>
    have hl := LogRow.step_inv row x.context h
    show Walk (Inv c 0) (Inv c 0) (x.state.liftLog (row.step x.context x.state.machine))
    unfold Frame.State.liftLog
    split <;> rename_i he <;> rw [he] at hl <;> exact hl
  | read row =>
    have hr := ReadRow.step_inv row x.context.block.rules x.context x.state.readView h
    show Walk (Inv c 0) (Inv c 0) (x.state.liftRead _ _)
    unfold Frame.State.liftRead
    split <;> rename_i he <;> rw [he] at hr
    all_goals
      show MInv c 0 (Frame.State.machine _)
      rw [(Frame.State.applyReadTouch_keeps _ _ _).1]
      exact hr
  | store kind =>
    cases kind with
    | persistent =>
      have hs := SstoreRow.step_inv (SstoreRow.ofRules x.context.block.rules) x.context.isStatic
        (x.state.slotView x.context.recipient x.context.tx.originalState) h
      show Walk (Inv c 0) (Inv c 0) (x.state.liftStore _ _ _)
      unfold Frame.State.liftStore
      split <;> rename_i he <;> rw [he] at hs
      all_goals
        show MInv c 0 (Frame.State.machine _)
        rw [Frame.State.applyStoreTouch_machine]
        exact hs
    | transient =>
      have hs := TstoreRow.step_inv (TstoreRow.ofRules x.context.block.rules)
        x.context.block.rules.opcodes x.context.isStatic h
      show Walk (Inv c 0) (Inv c 0) (x.state.liftStore _ _ _)
      unfold Frame.State.liftStore
      split <;> rename_i he <;> rw [he] at hs
      all_goals
        show MInv c 0 (Frame.State.machine _)
        rw [Frame.State.applyStoreTouch_machine]
        exact hs

/-- Ordinary instructions preserve the stack bound and the frame's committed spill on either exit. -/
theorem PlainOp.runCore_inv (pc : Nat) (ctx : CallContext) (s : Frame.State) {c : Nat}
    (h : Inv c 0 s) (op : Jaune.PlainOp) :
    Walk (Inv c 0) (Inv c 0) (PlainOp.runCore pc ctx s op) :=
  Family.run_inv (PlainOp.family op) ⟨pc, ctx, s⟩ h

/-- A successful jump leaves the same bound on its target state as an exceptional jump. -/
theorem JumpOp.runCore_inv (pc : Nat) (ctx : CallContext) (s : Frame.State) {c : Nat} (h : Inv c 0 s)
    (op : Jaune.JumpOp) : Walk (Inv c 0) (fun p => Inv c 0 p.2) (JumpOp.runCore pc ctx s op) := by
  cases op <;> simp only [JumpOp.runCore] <;> inv_walk

/-- A semantic fault has no frame. Every ordinary exit carries a bounded state. -/
def ExitInv (c : Nat) : Except Fault Frame.Exit → Prop
  | .error _ => True
  | .ok exit => Inv c 0 exit.state

private theorem catchHalt_inv {c : Nat}
    {body : Except (ExceptionalHalt × Frame.State) (Except Fault Frame.Exit)}
    (h : Walk (Inv c 0) (ExitInv c) body) : ExitInv c (Frame.Exit.catchHalt body) := by
  cases body with
  | error e => cases e; exact h
  | ok x => exact h

private theorem selfdestruct_inv (ctx : CallContext) (s : Frame.State) {c : Nat} (h : Inv c 0 s) :
    ExitInv c (HaltOp.run ctx s .selfdestruct) := by
  cases hs : ctx.block.rules.stateGas with
  | none =>
    simp only [HaltOp.run, hs]
    apply catchHalt_inv
    refine Walk.bind (State.popToAddress_inv h) ?_
    rintro ⟨donee, t⟩ ht
    cases ctx.block.rules.access <;> simp only
    all_goals repeat' split
    all_goals
      refine Walk.bind (State.chargeGas_inv _ (n := 0) (MInv.weaken ht (Nat.zero_le _))) ?_
      intro u hu
      refine Walk.bind (State.assertDynamic_inv ctx hu) ?_
      intro _ _
      unfold Frame.State.subtractBalance
      cases hb : u.world.subtractBalance ctx.recipient _ with
      | none => trivial
      | some world =>
        simp only [Option.map]
        unfold Frame.State.creditBeneficiary
        repeat' split
        all_goals first | exact hu | (unfold Frame.State.creditSelfdestructRefund; split <;> exact hu)
  | some state =>
    simp only [HaltOp.run, hs]
    apply catchHalt_inv
    refine Walk.bind (State.assertDynamic_inv ctx h) ?_
    intro _ _
    refine Walk.bind (State.popToAddress_inv h) ?_
    rintro ⟨donee, t⟩ ht
    refine Walk.bind (Walk.assert (H := Inv c 0) (MInv.weaken ht (Nat.zero_le _))) ?_
    intro _ _
    split <;>
      refine Walk.bind (State.chargeGas_inv _ (n := 0) (MInv.weaken ht (Nat.zero_le _))) ?_ <;>
      intro u hu <;>
      refine Walk.bind (State.chargeStateGas_inv _ hu) ?_ <;>
      intro v hv
    all_goals
      unfold Frame.State.subtractBalance
      cases hb : v.world.subtractBalance ctx.recipient _ with
      | none => trivial
      | some world =>
        simp only [Option.map]
        unfold Frame.State.emitTransferLog
        repeat' split
        all_goals exact hv

theorem HaltOp.run_inv (ctx : CallContext) (s : Frame.State) {c : Nat} (h : Inv c 0 s)
    (op : Jaune.HaltOp) : ExitInv c (HaltOp.run ctx s op) := by
  cases op with
  | stop => exact h
  | selfdestruct => exact selfdestruct_inv _ _ h
  | revert | return_ => apply catchHalt_inv; inv_walk

/-- A spawning opcode has already popped its operands and has room for the return push. -/
def OutcomeInv (c : Nat) : MessageOp.Outcome → Prop
  | .done x => Walk (Inv c 0) (Inv c 0) x
  | .spawn child _ => Inv c 1 child.checkpoint

private theorem ofExcept_inv {c : Nat} {x : Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (h : Walk (Inv c 0) (OutcomeInv c) x) : OutcomeInv c (MessageOp.Outcome.ofExcept x) := by
  cases x <;> exact h

private theorem pushZero_inv {c : Nat} {s : Frame.State} (h : Inv c 1 s) :
    Walk (Inv c 0) (OutcomeInv c) (do
      let u ← s.push 0
      return .done (.ok u)) := by
  refine Walk.bind (State.push_inv 0 h) ?_
  intro u hu
  exact hu

theorem genericCall.step_inv (ctx : CallContext) (s : Frame.State) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (transfersValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat) (code : ByteArray) (disablePrecompiles : Bool)
    {c : Nat} (h : Inv c 1 s) :
    OutcomeInv c (genericCall.step ctx s gas value caller target codeAddress transfersValue
      isStaticcall inputIndex inputSize outputIndex outputSize code disablePrecompiles) := by
  unfold genericCall.step
  split
  · apply ofExcept_inv
    exact pushZero_inv h
  · exact h

theorem genericCallAmsterdam.step_inv (ctx : CallContext) (state : StateGasRules)
    (s : Frame.State) (gas reservoir : Nat) (value : U256) (caller target codeAddress : Address)
    (transfersValue isStaticcall : Bool) (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles newAccountCharged insufficientBalance : Bool) {c : Nat} (h : Inv c 1 s) :
    OutcomeInv c (genericCallAmsterdam.step ctx state
      s gas reservoir value caller target codeAddress transfersValue isStaticcall inputIndex
      inputSize outputIndex outputSize code disablePrecompiles newAccountCharged insufficientBalance) := by
  unfold genericCallAmsterdam.step
  split
  · apply ofExcept_inv
    cases newAccountCharged <;> exact pushZero_inv h
  · exact h

theorem genericCreate.step_inv (ctx : CallContext) (s : Frame.State) (endowment : U256)
    (address : Address) (offset size : Nat) {c : Nat} (h : Inv c 1 s) :
    OutcomeInv c (genericCreate.step ctx s endowment address offset size) := by
  unfold genericCreate.step
  apply ofExcept_inv
  refine Walk.bind (Walk.assert (H := Inv c 0) (h.weaken (Nat.zero_le _))) ?_
  intro _ _
  refine Walk.bind (State.assertDynamic_inv ctx h) ?_
  intro _ _
  dsimp only
  split
  · exact pushZero_inv h
  · split
    · exact pushZero_inv h
    · exact h

theorem genericCreateAmsterdam.step_inv (ctx : CallContext) (rules : StateGasRules)
    (s : Frame.State) (endowment : U256) (address : Address) (offset size : Nat) {c : Nat} (h : Inv c 1 s) :
    OutcomeInv c (genericCreateAmsterdam.step ctx rules s endowment address offset size) := by
  unfold genericCreateAmsterdam.step
  apply ofExcept_inv
  dsimp only
  split
  · exact pushZero_inv h
  · split
    · refine Walk.bind (State.chargeStateGas_inv _ (n := 1) h) ?_
      intro t ht
      split
      · exact pushZero_inv ht
      · exact ht
    · simp only [bind, Except.bind]
      split
      · exact pushZero_inv h
      · exact h

local macro "spawn_inv" : tactic => `(tactic| first
  | (apply genericCreate.step_inv; inv_leaf)
  | (apply genericCall.step_inv; inv_leaf)
  | (apply genericCreateAmsterdam.step_inv; inv_leaf)
  | (apply genericCallAmsterdam.step_inv; inv_leaf))

private theorem bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl

local macro "message_inv_walk" : tactic => `(tactic| repeat' first
  | inv_primitive
  | (solve | spawn_inv)
  | (solve | apply pushZero_inv; inv_leaf)
  | (with_reducible apply ofExcept_inv)
  | (solve | inv_leaf)
  | simp only [bind_ok]
  | dsimp only
  | split)

private theorem step_call_inv (ctx : CallContext) (s : Frame.State) {c : Nat} (h : Inv c 0 s) :
    OutcomeInv c (MessageOp.step ctx s .call) := by
  simp only [MessageOp.step]
  message_inv_walk

private theorem step_callcode_inv (ctx : CallContext) (s : Frame.State) {c : Nat} (h : Inv c 0 s) :
    OutcomeInv c (MessageOp.step ctx s .callcode) := by
  simp only [MessageOp.step]
  message_inv_walk

private theorem step_delegatecall_inv (ctx : CallContext) (s : Frame.State) {c : Nat} (h : Inv c 0 s) :
    OutcomeInv c (MessageOp.step ctx s .delegatecall) := by
  simp only [MessageOp.step]
  message_inv_walk

private theorem step_staticcall_inv (ctx : CallContext) (s : Frame.State) {c : Nat} (h : Inv c 0 s) :
    OutcomeInv c (MessageOp.step ctx s .staticcall) := by
  simp only [MessageOp.step]
  message_inv_walk

private theorem step_create_inv (ctx : CallContext) (s : Frame.State) {c : Nat} (h : Inv c 0 s) :
    OutcomeInv c (MessageOp.step ctx s .create) := by
  simp only [MessageOp.step]
  message_inv_walk

private theorem step_create2_inv (ctx : CallContext) (s : Frame.State) {c : Nat} (h : Inv c 0 s) :
    OutcomeInv c (MessageOp.step ctx s .create2) := by
  simp only [MessageOp.step]
  message_inv_walk

theorem MessageOp.step_inv (ctx : CallContext) (s : Frame.State) {c : Nat} (h : Inv c 0 s)
    (op : Jaune.MessageOp) : OutcomeInv c (MessageOp.step ctx s op) := by
  cases op with
  | call => exact step_call_inv _ _ h
  | callcode => exact step_callcode_inv _ _ h
  | delegatecall => exact step_delegatecall_inv _ _ h
  | staticcall => exact step_staticcall_inv _ _ h
  | create => exact step_create_inv _ _ h
  | create2 => exact step_create2_inv _ _ h

/-- A continuation or exit fits the stack. A spawn already made room for the return push. -/
def StepInv (c : Nat) : Step → Prop
  | .next _ s => Inv c 0 s
  | .exit e => Inv c 0 e.state
  | .spawn child _ _ => Inv c 1 child.checkpoint

private theorem ofHalt_inv {c pc : Nat} {x}
    (h : Walk (Inv c 0) (Inv c 0) x) : StepInv c (Step.ofHalt pc x) := by
  cases x with
  | error e => cases e; exact h
  | ok _ => exact h

private theorem toStep_inv {c pc : Nat} {o : MessageOp.Outcome}
    (h : OutcomeInv c o) : StepInv c (o.toStep pc) := by
  cases o with
  | done _ => exact ofHalt_inv h
  | spawn _ _ => exact h

theorem NextOp.step_inv (r : Frame.Running) {c : Nat} (h : Inv c 0 r.state) (op : Jaune.NextOp) :
    StepInv c (NextOp.step r op) := by
  cases op with
  | plain p => exact ofHalt_inv (PlainOp.runCore_inv _ _ _ h p)
  | message m => exact toStep_inv (MessageOp.step_inv _ _ h m)
  | push xs _ => exact ofHalt_inv (Family.run_inv _ r h)
  | dupn imm | swapn imm | exchange imm => exact ofHalt_inv (Family.run_inv _ r h)

/-- The single-step invariant for every decoder outcome and fork. -/
theorem step_inv {r : Frame.Running} {c : Nat} (h : Inv c 0 r.state) {out : Step}
    (hs : step r = .ok out) : StepInv c out := by
  unfold step at hs
  split at hs
  · cases hs; exact h
  · cases hs; exact NextOp.step_inv _ h _
  · rename_i j _
    have hj := JumpOp.runCore_inv r.pc r.context r.state h j
    unfold JumpOp.run at hs
    split at hs
    · rename_i p he
      rw [he] at hj
      cases hs; cases p; exact hj
    · rename_i pc s he
      rw [he] at hj
      cases hs; exact hj
  · rename_i op _
    have hh := HaltOp.run_inv r.context r.state h op
    cases he : HaltOp.run r.context r.state op with
    | error e => rw [he] at hs; cases hs
    | ok exit => rw [he] at hs hh; cases hs; exact hh
end RunInvariants
end Jaune.Checked
