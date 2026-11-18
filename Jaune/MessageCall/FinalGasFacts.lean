import Jaune.MessageCall.FinalStep
import Jaune.Sufficiency

/-!
# Native gas facts of the staged step: the walk and the plain, jump and halt corpus
(goal `jaune-shape-and-names-v1`, G2b unit W3-4a)

The facts `Jaune.MessageCall.StepGas` and `Jaune.Sufficiency` state of the `Devm` interpreter,
proved here of the staged instruction bodies over `Frame.State` directly: no `Jaune.Bridge.*`
module is imported and no statement goes through the old interpreter.

The proofs are one mechanical walk (`gas_walk`): a postcondition `GasFacts.W E P` on both
channels of an `Except (ExceptionalHalt × σ) α` computation, pushed through the binds with one
lemma per machine primitive that records what the primitive does to the three gas atoms
(`gasLeft`, `stateGas.spilled`, `stateGas.committedSpill`), and closed at each leaf by linear
arithmetic over those atoms (`gas_close`). The gas measure is `Machine.gasMeasure`; the spill an
exceptional halt keeps is `Frame.State.spill`.

What a body owes:

* on success, a measure strictly below the frame's at the start of the step;
* on an exceptional halt, a spill at most that measure (a halt forfeits its execution gas).

The non-`Devm` arithmetic (`calculateMsgCallGas_stipend_lt`, `sstoreAmsterdamGasCost_pos`,
`GasSchedule.access_cost_pos`, `ForkRules.Valid.flatAccess`, `except64th_le`) is reused from
`Jaune.Sufficiency`.
-/

open private keccakReadRun from Jaune.Machine

namespace Jaune.Staging

open Jaune

namespace GasFacts

/-! ### The walk -/

/-- A postcondition on both channels: `E` of the state an error carries, `P` of a success. -/
def W {σ α : Type} (E : σ → Prop) (P : α → Prop) : Except (ExceptionalHalt × σ) α → Prop
  | .error p => E p.2
  | .ok a => P a

theorem W.bind {σ α β : Type} {E : σ → Prop} {P : α → Prop} {Q : β → Prop}
    {x : Except (ExceptionalHalt × σ) α} {f : α → Except (ExceptionalHalt × σ) β}
    (hx : W E P x) (hf : ∀ a, P a → W E Q (f a)) : W E Q (x >>= f) := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem W.mono {σ α : Type} {E : σ → Prop} {P Q : α → Prop}
    {x : Except (ExceptionalHalt × σ) α} (hx : W E P x) (hf : ∀ a, P a → Q a) : W E Q x := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem W.ok {σ α : Type} {E : σ → Prop} {P : α → Prop} {a : α} (h : P a) :
    W E P (Except.ok a : Except (ExceptionalHalt × σ) α) := h

theorem W.error {σ α : Type} {E : σ → Prop} {P : α → Prop} {r : ExceptionalHalt} {s : σ}
    (h : E s) : W E P (Except.error (r, s) : Except (ExceptionalHalt × σ) α) := h

theorem W.ok_bind {σ α β : Type} (a : α) (f : α → Except (ExceptionalHalt × σ) β) :
    (Except.ok a >>= f) = f a := rfl

theorem W.assert {σ : Type} {E : σ → Prop} {p : Prop} [Decidable p] {r : ExceptionalHalt}
    {s : σ} (h : E s) : W E (fun _ : Unit => p) (Except.assert p (r, s)) := by
  unfold Except.assert
  split
  · assumption
  · exact h

/-! ### Machine primitives -/

/-- What a primitive does to the gas atoms: `c` of execution gas charged, the spill kept. -/
def Charged (c : Nat) (m' m : Machine) : Prop :=
  m'.gasLeft + c = m.gasLeft ∧ m'.stateGas.spilled = m.stateGas.spilled ∧
    m'.stateGas.committedSpill = m.stateGas.committedSpill

namespace Machine

/-- The error-channel side condition every primitive asks: `E` of any machine whose spill the
measure of `m` covers. A primitive halts on a machine of `m`'s spill (the one it was given, or
one that only popped or charged), and every spill is part of its measure. -/
abbrev Keeps (E : Machine → Prop) (m : Machine) : Prop :=
  ∀ m' : Machine, m'.stateGas.spilled + m'.stateGas.committedSpill ≤
    m.gasLeft + m.stateGas.spilled + m.stateGas.committedSpill → E m'

theorem Keeps.self {E : Machine → Prop} {m : Machine} (h : Keeps E m) : E m :=
  h m (by omega)

theorem Keeps.charged {E : Machine → Prop} {c : Nat} {m' m : Machine} (h : Keeps E m)
    (hc : Charged c m' m) : Keeps E m' := by
  intro m'' h''; apply h; obtain ⟨a, b, d⟩ := hc; omega

theorem push_W {E : Machine → Prop} {x : U256} {m : Machine} (h : Keeps E m) :
    W E (Charged 0 · m) (m.push x) := by
  unfold Jaune.Machine.push; split
  · exact ⟨rfl, rfl, rfl⟩
  · exact h.self

theorem pop_W {E : Machine → Prop} {m : Machine} (h : Keeps E m) :
    W E (fun p : U256 × Machine => Charged 0 p.2 m) m.pop := by
  unfold Jaune.Machine.pop; split
  · exact h.self
  · exact ⟨rfl, rfl, rfl⟩

theorem popToNat_W {E : Machine → Prop} {m : Machine} (h : Keeps E m) :
    W E (fun p : Nat × Machine => Charged 0 p.2 m) m.popToNat := by
  have hp := pop_W (E := E) h
  unfold Jaune.Machine.popToNat
  revert hp; cases m.pop <;> exact id

theorem popToAddress_W {E : Machine → Prop} {m : Machine} (h : Keeps E m) :
    W E (fun p : Address × Machine => Charged 0 p.2 m) m.popToAddress := by
  have hp := pop_W (E := E) h
  unfold Jaune.Machine.popToAddress
  revert hp; cases m.pop <;> exact id

theorem Charged.trans {c d : Nat} {m'' m' m : Machine} (h2 : Charged d m'' m')
    (h1 : Charged c m' m) : Charged (d + c) m'' m := by
  obtain ⟨a1, b1, c1⟩ := h1; obtain ⟨a2, b2, c2⟩ := h2
  exact ⟨by omega, b2.trans b1, c2.trans c1⟩

theorem popN_W {E : Machine → Prop} (n : Nat) : ∀ {m : Machine}, Keeps E m →
    W E (fun p : List U256 × Machine => Charged 0 p.2 m) (m.popN n) := by
  induction n with
  | zero => intro m _; exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    intro m h
    have hp := pop_W (E := E) h
    unfold Jaune.Machine.popN
    revert hp
    cases m.pop with
    | error e => exact id
    | ok p =>
      intro hp
      obtain ⟨x, m'⟩ := p
      dsimp only
      have hq := ih (m := m') (h.charged hp)
      revert hq
      cases m'.popN n with
      | error e => exact id
      | ok q => exact fun hq => (by simpa using Charged.trans hq hp : Charged 0 q.2 m)

theorem chargeGas_W {E : Machine → Prop} {c : Nat} {m : Machine} (h : Keeps E m) :
    W E (Charged c · m) (m.chargeGas c) := by
  unfold Jaune.Machine.chargeGas safeSub
  split
  · rename_i heq; split at heq
    · simp at heq
    · exact h.self
  · rename_i g heq; split at heq
    · simp only [Option.some.injEq] at heq; subst heq
      refine ⟨?_, rfl, rfl⟩; dsimp only; omega
    · simp at heq

/-- `chargeStateGas`: the measure is kept (the reservoir's shortfall moves from execution gas to
the spill), the committed spill too. -/
def StateCharged (m' m : Machine) : Prop :=
  m'.gasLeft + m'.stateGas.spilled = m.gasLeft + m.stateGas.spilled ∧
    m'.stateGas.committedSpill = m.stateGas.committedSpill

theorem chargeStateGas_W {E : Machine → Prop} {a : Nat} {m : Machine} (h : Keeps E m) :
    W E (StateCharged · m) (m.chargeStateGas a) := by
  unfold Jaune.Machine.chargeStateGas
  split
  · exact ⟨rfl, rfl⟩
  · split
    · refine ⟨?_, rfl⟩; dsimp only; omega
    · exact h.self

theorem pushItem_W {E : Machine → Prop} {x : U256} {c : Nat} {m : Machine} (h : Keeps E m) :
    W E (Charged c · m) (m.pushItem x c) := by
  have hc := chargeGas_W (E := E) (c := c) h
  unfold Jaune.Machine.pushItem
  revert hc
  cases m.chargeGas c with
  | error e => exact id
  | ok m1 =>
    intro hc
    exact W.mono (push_W (x := x) (h.charged hc)) (fun a ha => by
      simpa using Charged.trans ha hc)

theorem applyUnary_W {E : Machine → Prop} {f : U256 → U256} {c : Nat} {m : Machine}
    (h : Keeps E m) : W E (Charged c · m) (m.applyUnary f c) := by
  have hp := pop_W (E := E) h
  unfold Jaune.Machine.applyUnary
  revert hp
  cases m.pop with
  | error e => exact id
  | ok p =>
    intro hp
    exact W.mono (pushItem_W (x := f p.1) (c := c) (h.charged hp)) (fun a ha => by
      simpa using Charged.trans ha hp)

theorem applyBinary_W {E : Machine → Prop} {f : U256 → U256 → U256} {c : Nat} {m : Machine}
    (h : Keeps E m) : W E (Charged c · m) (m.applyBinary f c) := by
  have hp := pop_W (E := E) h
  unfold Jaune.Machine.applyBinary
  revert hp
  cases m.pop with
  | error e => exact id
  | ok p =>
    obtain ⟨x1, m1⟩ := p
    intro hp
    dsimp only
    have hq := pop_W (E := E) (h.charged hp)
    revert hq
    cases m1.pop with
    | error e => exact id
    | ok q =>
      obtain ⟨x2, m2⟩ := q
      intro hq
      dsimp only
      exact W.mono (pushItem_W (x := f x1 x2) (c := c) ((h.charged hp).charged hq))
        (fun a ha => by simpa using Charged.trans (Charged.trans ha hq) hp)

theorem applyTernary_W {E : Machine → Prop} {f : U256 → U256 → U256 → U256} {c : Nat}
    {m : Machine} (h : Keeps E m) : W E (Charged c · m) (m.applyTernary f c) := by
  have hp := pop_W (E := E) h
  unfold Jaune.Machine.applyTernary
  revert hp
  cases m.pop with
  | error e => exact id
  | ok p =>
    obtain ⟨x1, m1⟩ := p
    intro hp
    dsimp only
    have hq := pop_W (E := E) (h.charged hp)
    revert hq
    cases m1.pop with
    | error e => exact id
    | ok q =>
      obtain ⟨x2, m2⟩ := q
      intro hq
      dsimp only
      have hr := pop_W (E := E) ((h.charged hp).charged hq)
      revert hr
      cases m2.pop with
      | error e => exact id
      | ok r =>
        obtain ⟨x3, m3⟩ := r
        intro hr
        dsimp only
        exact W.mono (pushItem_W (x := f x1 x2 x3) (c := c)
          (((h.charged hp).charged hq).charged hr))
          (fun a ha => by simpa using Charged.trans (Charged.trans (Charged.trans ha hr) hq) hp)

end Machine

/-! ### State primitives -/

namespace State

open Machine (Keeps)

theorem liftMachine_W {E : Frame.State → Prop} {P : Frame.State → Prop}
    {core : Machine → Except (ExceptionalHalt × Machine) Machine} {s : Frame.State}
    (h : W (fun m => E (s.withMachine m)) (fun m => P (s.withMachine m)) (core s.machine)) :
    W E P (s.liftMachine core) := by
  unfold Frame.State.liftMachine
  revert h
  cases core s.machine with
  | error e => obtain ⟨r, m⟩ := e; exact id
  | ok m => exact id

theorem liftMachineValue_W {α : Type} {E : Frame.State → Prop} {P : α × Frame.State → Prop}
    {core : Machine → Except (ExceptionalHalt × Machine) (α × Machine)} {s : Frame.State}
    (h : W (fun m => E (s.withMachine m)) (fun p => P (p.1, s.withMachine p.2))
      (core s.machine)) :
    W E P (s.liftMachineValue core) := by
  unfold Frame.State.liftMachineValue
  revert h
  cases core s.machine with
  | error e => obtain ⟨r, m⟩ := e; exact id
  | ok p => obtain ⟨a, m⟩ := p; exact id

variable {E : Frame.State → Prop} {s : Frame.State}

theorem push_W {x : U256} (h : Keeps (fun m => E (s.withMachine m)) s.machine) :
    W E (fun s' => Charged 0 s'.machine s.machine) (s.push x) :=
  liftMachine_W (Machine.push_W h)

theorem pop_W (h : Keeps (fun m => E (s.withMachine m)) s.machine) :
    W E (fun p : U256 × Frame.State => Charged 0 p.2.machine s.machine) s.pop :=
  liftMachineValue_W (Machine.pop_W h)

theorem popToNat_W (h : Keeps (fun m => E (s.withMachine m)) s.machine) :
    W E (fun p : Nat × Frame.State => Charged 0 p.2.machine s.machine) s.popToNat :=
  liftMachineValue_W (Machine.popToNat_W h)

theorem popToAddress_W (h : Keeps (fun m => E (s.withMachine m)) s.machine) :
    W E (fun p : Address × Frame.State => Charged 0 p.2.machine s.machine) s.popToAddress :=
  liftMachineValue_W (Machine.popToAddress_W h)

theorem popN_W {n : Nat} (h : Keeps (fun m => E (s.withMachine m)) s.machine) :
    W E (fun p : List U256 × Frame.State => Charged 0 p.2.machine s.machine) (s.popN n) :=
  liftMachineValue_W (Machine.popN_W n h)

theorem chargeGas_W {c : Nat} (h : Keeps (fun m => E (s.withMachine m)) s.machine) :
    W E (fun s' => Charged c s'.machine s.machine) (s.chargeGas c) :=
  liftMachine_W (Machine.chargeGas_W h)

theorem chargeStateGas_W {a : Nat} (h : Keeps (fun m => E (s.withMachine m)) s.machine) :
    W E (fun s' => Machine.StateCharged s'.machine s.machine) (s.chargeStateGas a) :=
  liftMachine_W (Machine.chargeStateGas_W h)

theorem pushItem_W {x : U256} {c : Nat} (h : Keeps (fun m => E (s.withMachine m)) s.machine) :
    W E (fun s' => Charged c s'.machine s.machine) (s.pushItem x c) :=
  liftMachine_W (Machine.pushItem_W h)

theorem applyUnary_W {f : U256 → U256} {c : Nat}
    (h : Keeps (fun m => E (s.withMachine m)) s.machine) :
    W E (fun s' => Charged c s'.machine s.machine) (s.applyUnary f c) :=
  liftMachine_W (Machine.applyUnary_W h)

theorem applyBinary_W {f : U256 → U256 → U256} {c : Nat}
    (h : Keeps (fun m => E (s.withMachine m)) s.machine) :
    W E (fun s' => Charged c s'.machine s.machine) (s.applyBinary f c) :=
  liftMachine_W (Machine.applyBinary_W h)

theorem applyTernary_W {f : U256 → U256 → U256 → U256} {c : Nat}
    (h : Keeps (fun m => E (s.withMachine m)) s.machine) :
    W E (fun s' => Charged c s'.machine s.machine) (s.applyTernary f c) :=
  liftMachine_W (Machine.applyTernary_W h)

theorem assertDynamic_W {ctx : CallContext} (h : E s) :
    W E (fun _ : Unit => True) (s.assertDynamic ctx) := by
  unfold Frame.State.assertDynamic Except.assert
  split
  · trivial
  · exact h

end State

/-! ### The tactics -/

/-- The gas atoms' simp set: the measure and the spill unfolded, the group setters and the pure
machine updates pushed through, the constant prices unfolded. -/
macro "gas_simp" : tactic => `(tactic| simp only [Jaune.Machine.gasMeasure,
  Jaune.Frame.State.spill, Charged, Machine.StateCharged,
  Jaune.Frame.State.withMachine_machine, Jaune.Frame.State.withWorld_machine,
  Jaune.Frame.State.withSubstate_machine, Jaune.Frame.State.withTrail_machine,
  Jaune.Machine.memWrite, Jaune.Machine.memExtends, Jaune.Machine.restoreChildGas,
  Jaune.Machine.creditStateGasRefund, Jaune.Machine.forfeitRemainingGas,
  Jaune.Machine.restoreStateGas, Jaune.Machine.repayStateGasSpill,
  Gas.base, Gas.veryLow, Gas.low, Gas.mid, Gas.high, Gas.jumpdest, Gas.exp, Gas.expByte,
  Gas.copy, Gas.returnDataCopy, Gas.keccak256, Gas.keccak256Word, Gas.blockhash,
  Gas.hashOpcodeGas, Gas.log, Gas.logData, Gas.logTopic, Gas.warmStorageReadCost,
  Gas.coldSloadCost, Gas.sstoreSetGas, Gas.sstoreResetGas, Gas.callStipend, Gas.selfdestruct,
  Gas.selfdestructNewAccount, Gas.newAccount, Gas.initcodeWordCost] at *)

open Lean Elab Tactic Meta in
/-- Close an arithmetic leaf (not a walk goal) over the gas atoms. -/
elab "gas_close" : tactic => withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  if tgt.isAppOf ``W then throwError "gas_close: a walk goal"
  evalTactic (← `(tactic| (intros; (try simp only [Machine.Keeps]); intros; (try gas_simp);
    first | omega | (split_ifs at * <;> omega))))

theorem W.error' {σ α : Type} {E : σ → Prop} {P : α → Prop} {e : ExceptionalHalt × σ}
    (h : E e.2) : W E P (Except.error e : Except (ExceptionalHalt × σ) α) := h

open Lean Elab Tactic Meta in
/-- One step of the walk, chosen by the head of the computation (never by unification against
an unfolded body, which would evaluate it). -/
elab "gas_step" : tactic => withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  unless tgt.isAppOf ``W do throwError "gas_step: not a walk goal"
  let x := tgt.appArg!.headBeta
  let run (t : TSyntax `tactic) : TacticM Unit := evalTactic t
  let env ← getEnv
  let splittable (e : Expr) : Bool := (e.find? fun t =>
    (t.isAppOf ``ite || t.isAppOf ``dite || isMatcherAppCore env t) && !t.hasLooseBVars).isSome
  let some hd := x.getAppFn.constName? | do
    run (← `(tactic| dsimp only)); return
  -- primitive: (bind-lemma, mono-lemma, binds a pair?)
  let prim (n : Name) : Option (Ident × Bool) :=
    if n == ``Frame.State.pop then some (mkIdent ``State.pop_W, true)
    else if n == ``Frame.State.popToNat then some (mkIdent ``State.popToNat_W, true)
    else if n == ``Frame.State.popToAddress then some (mkIdent ``State.popToAddress_W, true)
    else if n == ``Frame.State.popN then some (mkIdent ``State.popN_W, true)
    else if n == ``Frame.State.chargeGas then some (mkIdent ``State.chargeGas_W, false)
    else if n == ``Frame.State.chargeStateGas then some (mkIdent ``State.chargeStateGas_W, false)
    else if n == ``Frame.State.push then some (mkIdent ``State.push_W, false)
    else if n == ``Frame.State.pushItem then some (mkIdent ``State.pushItem_W, false)
    else if n == ``Frame.State.applyUnary then some (mkIdent ``State.applyUnary_W, false)
    else if n == ``Frame.State.applyBinary then some (mkIdent ``State.applyBinary_W, false)
    else if n == ``Frame.State.applyTernary then some (mkIdent ``State.applyTernary_W, false)
    else if n == ``Frame.State.assertDynamic then some (mkIdent ``State.assertDynamic_W, false)
    else if n == ``Except.assert then some (mkIdent ``W.assert, false)
    else if n == ``Jaune.Machine.pop then some (mkIdent ``Machine.pop_W, true)
    else if n == ``Jaune.Machine.popToNat then some (mkIdent ``Machine.popToNat_W, true)
    else if n == ``Jaune.Machine.popToAddress then some (mkIdent ``Machine.popToAddress_W, true)
    else if n == ``Jaune.Machine.chargeGas then some (mkIdent ``Machine.chargeGas_W, false)
    else if n == ``Jaune.Machine.chargeStateGas then some (mkIdent ``Machine.chargeStateGas_W, false)
    else if n == ``Jaune.Machine.push then some (mkIdent ``Machine.push_W, false)
    else if n == ``Jaune.Machine.pushItem then some (mkIdent ``Machine.pushItem_W, false)
    else if n == ``Jaune.Machine.applyUnary then some (mkIdent ``Machine.applyUnary_W, false)
    else if n == ``Jaune.Machine.applyBinary then some (mkIdent ``Machine.applyBinary_W, false)
    else if n == ``Jaune.Machine.applyTernary then some (mkIdent ``Machine.applyTernary_W, false)
    else none
  if hd == ``Except.ok then run (← `(tactic| refine W.ok ?_))
  else if hd == ``Except.error then run (← `(tactic| refine W.error' ?_))
  else if hd == ``Pure.pure then run (← `(tactic| simp only [pure, Except.pure]))
  else if hd == ``Frame.State.liftMachine then run (← `(tactic| refine State.liftMachine_W ?_))
  else if hd == ``Jaune.Machine.popN then
    run (← `(tactic| refine W.mono (Machine.popN_W _ ?_) ?_))
  else if hd == ``Bind.bind then
    let x0 := (x.getArg! 4).headBeta
    let some h0 := x0.getAppFn.constName? | throwError "gas_step: opaque bind head"
    if (prim h0).isSome && splittable x0 then run (← `(tactic| split)) else
    if h0 == ``Except.ok then run (← `(tactic| rw [W.ok_bind]))
    else if h0 == ``Jaune.Machine.popN then
      run (← `(tactic| (refine W.bind (Machine.popN_W _ ?_) ?_; rotate_left; intro ⟨_, _⟩ _)))
    else match prim h0 with
      | some (l, true) => run (← `(tactic| (refine W.bind ($l ?_) ?_; rotate_left; intro ⟨_, _⟩ _)))
      | some (l, false) => run (← `(tactic| (refine W.bind ($l ?_) ?_; rotate_left; intro _ _)))
      | none => run (← `(tactic| first | (dsimp only) | split))
  else match prim hd with
    | some (l, _) =>
      if splittable x then run (← `(tactic| split))
      else run (← `(tactic| (refine W.mono ($l ?_) ?_; rotate_left; intro _ _)))
    | none =>
      if hd == ``ite || hd == ``dite then run (← `(tactic| split))
      else run (← `(tactic| first | (dsimp only) | split))

/-- Walk a computation to its leaves. -/
macro "gas_walk" : tactic => `(tactic| repeat' (first | gas_close | gas_step))

/-! ### Plain instructions -/

/-- What a plain instruction owes: a success strictly below `n`, a halt's spill at most `n`. -/
abbrev PlainPost (n : Nat) : Except (ExceptionalHalt × Frame.State) Frame.State → Prop :=
  W (fun e => e.spill ≤ n) (fun s' => s'.machine.gasMeasure < n)

set_option maxHeartbeats 4000000 in
theorem PlainOp.runCore_gas (pc : Nat) (ctx : CallContext) (s : Frame.State) (op : Jaune.PlainOp) :
    PlainPost s.machine.gasMeasure (PlainOp.runCore pc ctx s op) := by
  cases op <;> simp only [PlainOp.runCore, Frame.State.pushItem]
  case add => gas_walk
  case mstore => gas_walk
  case balance => gas_walk
  all_goals sorry

end GasFacts

end Jaune.Staging
