import Jaune.MessageCall.Control
import Jaune.MessageCall.Step
import Jaune.Bridge.G2b.State

/-!
# Bridge: jumps, halts and precompile results against the `Devm` interpreter (G2b, W3-2b+d)

The squares of `Jaune.MessageCall.Control` against today's definitions:

* `ofOutcome_jumpRunCore`: `Staging.JumpOp.runCore` against `JumpOp.runCore`, every jump, every
  state, every fork; and `ofJumpOutcome_run` for the running frame against `JumpOp.run`.
* `ofExecution_haltRun`: `Staging.HaltOp.run` against `HaltOp.run` under
  `Frame.Exit.ofExecution`, for a state with no output (every running frame's: only a halt writes
  one, and a frame stops at its halt).
* `ofExecution_applyPrecompileResult` and `ofExecution_executePrecompile`: `runPrecompile`
  against today's precompile result path, under the same premise.
* `Evm.step_jump`, `Evm.step_halt` and `Frame.Running.getOp_ofEvm`: `Evm.step`'s jump and halt
  arms are the old runs the squares relate, decoded at the same operation.

The squares compose W3-1's primitive squares through `Except.Agree`, which relates an old
outcome to a new halt-only one step by step.

Everything here is a bridge artifact: it goes with `Devm` after G2b's tag.
-/

namespace Jaune

open Frame.State

/-! ### Agreement of an old outcome with a halt-only one -/

/-- An old outcome and a halt-only new one agree: both halt for the same reason, the new state
being the old one grouped, or both go on with related values. -/
def Except.Agree {α β : Type} (R : α → β → Prop) :
    Except (EvmError × Devm) α → Except (ExceptionalHalt × Frame.State) β → Prop
  | .error (e, d), .error (h, s) => e = .halt h ∧ s = ofDevm d
  | .ok a, .ok b => R a b
  | _, _ => False

namespace Except.Agree

theorem bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {x : Except (EvmError × Devm) α} {y : Except (ExceptionalHalt × Frame.State) β}
    {f : α → Except (EvmError × Devm) γ} {g : β → Except (ExceptionalHalt × Frame.State) δ}
    (hx : Except.Agree R x y) (hf : ∀ a b, R a b → Except.Agree S (f a) (g b)) :
    Except.Agree S (x >>= f) (y >>= g) := by
  rcases x with ⟨e, d⟩ | a <;> rcases y with ⟨h, s⟩ | b <;> simp only [Except.Agree] at hx
  · exact hx
  · exact hf a b hx

theorem ok {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Except.Agree R (.ok a) (.ok b) := h

theorem assert {p : Prop} [Decidable p] (h : ExceptionalHalt) (d : Devm) :
    Except.Agree (fun _ _ => True) (Except.assert p (EvmError.halt h, d))
      (Except.assert p (h, ofDevm d)) := by
  unfold Except.assert; split <;> simp [Except.Agree]

/-- A halt-only step without a value, from its W3-1 square. -/
theorem ofExecution {x : Execution} {y : Except (ExceptionalHalt × Frame.State) Frame.State}
    (h : Frame.State.ofExecution x = Except.ofHalt y) :
    Except.Agree (fun d s => s = ofDevm d) x y := by
  rcases x with ⟨e, d⟩ | d <;> rcases y with ⟨r, s⟩ | s <;>
    simp_all [Except.Agree, Except.mapResultState, Except.ofHalt]

/-- A halt-only step with a value, from its W3-1 square. -/
theorem ofOutcome {α : Type} {x : Except (EvmError × Devm) (α × Devm)}
    {y : Except (ExceptionalHalt × Frame.State) (α × Frame.State)}
    (h : Frame.State.ofOutcome x = Except.ofHalt y) :
    Except.Agree (fun p q => q = (p.1, ofDevm p.2)) x y := by
  rcases x with ⟨e, d⟩ | ⟨a, d⟩ <;> rcases y with ⟨r, s⟩ | ⟨b, s⟩ <;>
    simp_all [Except.Agree, Except.mapState, Except.ofHalt]

theorem weaken {α β : Type} {R S : α → β → Prop} {x : Except (EvmError × Devm) α}
    {y : Except (ExceptionalHalt × Frame.State) β} (hx : Except.Agree R x y)
    (hRS : ∀ a b, R a b → S a b) : Except.Agree S x y := by
  rcases x with ⟨e, d⟩ | a <;> rcases y with ⟨h, s⟩ | b <;> simp only [Except.Agree] at hx ⊢
  · exact hx
  · exact hRS a b hx

/-- Add a fact every old value satisfies. -/
theorem and_ok {α β : Type} {R : α → β → Prop} {P : α → Prop} {x : Except (EvmError × Devm) α}
    {y : Except (ExceptionalHalt × Frame.State) β} (hx : Except.Agree R x y)
    (hP : ∀ a, x = .ok a → P a) : Except.Agree (fun a b => R a b ∧ P a) x y := by
  rcases x with ⟨e, d⟩ | a <;> rcases y with ⟨h, s⟩ | b <;> simp only [Except.Agree] at hx ⊢
  · exact hx
  · exact ⟨hx, hP a rfl⟩

/-- Agreement with grouped values is the square under `ofOutcome`. -/
theorem toOfOutcome {α : Type} {x : Except (EvmError × Devm) (α × Devm)}
    {y : Except (ExceptionalHalt × Frame.State) (α × Frame.State)}
    (h : Except.Agree (fun p q => q = (p.1, ofDevm p.2)) x y) :
    Frame.State.ofOutcome x = Except.ofHalt y := by
  rcases x with ⟨e, d⟩ | ⟨a, d⟩ <;> rcases y with ⟨r, s⟩ | ⟨b, s⟩ <;>
    simp only [Except.Agree] at h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl

/-- A frame-ending computation: if the steps agree and every pair of related continuations ends
the frame the same way, the whole computations do. -/
theorem toExit {α β : Type} {R : α → β → Prop} {x : Except (EvmError × Devm) α}
    {y : Except (ExceptionalHalt × Frame.State) β} {f : α → Execution}
    {g : β → Except (ExceptionalHalt × Frame.State) (Except Fault Frame.Exit)}
    (hx : Except.Agree R x y)
    (hf : ∀ a b, R a b → Frame.Exit.ofExecution (f a) = Frame.Exit.catchHalt (g b)) :
    Frame.Exit.ofExecution (x >>= f) = Frame.Exit.catchHalt (y >>= g) := by
  rcases x with ⟨e, d⟩ | a <;> rcases y with ⟨h, s⟩ | b <;> simp only [Except.Agree] at hx
  · obtain ⟨rfl, rfl⟩ := hx; rfl
  · exact hf a b hx

end Except.Agree

/-! ### The machine lifts keep the output -/

theorem liftMach_ok_output {α : Type} {core : Mach → Footprint.Outcome Mach α} {d d' : Devm}
    {a : α} (h : liftMach core d = .ok (a, d')) : d'.output = d.output := by
  unfold liftMach Footprint.liftOutcome at h
  split at h <;> cases h; rfl

theorem liftMachExecution_ok_output {core : Mach → Footprint.Outcome Mach Unit} {d d' : Devm}
    (h : liftMachExecution core d = .ok d') : d'.output = d.output := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · cases h
  · rename_i heq; cases h; exact liftMach_ok_output heq

/-! ### Jumps -/

/-- The square for jumps: every jump, every state, every fork. -/
theorem ofOutcome_jumpRunCore (pc : Nat) (d : Devm) (sevm : Sevm) (j : JumpOp) :
    ofOutcome (JumpOp.runCore pc d sevm j) =
      Except.ofHalt (Staging.JumpOp.runCore pc (CallContext.ofSevm sevm) (ofDevm d) j) := by
  apply Except.Agree.toOfOutcome
  cases j <;> simp only [JumpOp.runCore, Staging.JumpOp.runCore]
  case jumpdest =>
    refine (Except.Agree.ofExecution (ofExecution_chargeGas _ d)).bind ?_
    rintro d' s rfl; rfl
  case jump =>
    refine (Except.Agree.ofOutcome (ofOutcome_pop d)).bind ?_
    rintro ⟨x, d₁⟩ _ rfl
    refine (Except.Agree.ofExecution (ofExecution_chargeGas _ d₁)).bind ?_
    rintro d₂ _ rfl
    refine (Except.Agree.assert _ d₂).bind ?_
    intro _ _ _; rfl
  case jumpi =>
    refine (Except.Agree.ofOutcome (ofOutcome_pop d)).bind ?_
    rintro ⟨x, d₁⟩ _ rfl
    refine (Except.Agree.ofOutcome (ofOutcome_pop d₁)).bind ?_
    rintro ⟨c, d₂⟩ _ rfl
    refine (Except.Agree.ofExecution (ofExecution_chargeGas _ d₂)).bind ?_
    rintro d₃ _ rfl
    dsimp only
    by_cases hc : c = 0 <;> simp only [hc, ↓reduceIte]
    · rfl
    · exact (Except.Agree.assert _ d₃).bind (fun _ _ _ => rfl)

/-- An old jump result as a running frame's. -/
def Frame.Running.ofJumpOutcome (sevm : Sevm) :
    Except (EvmError × Devm) (Nat × Devm) → Except (EvmError × Frame.State) Frame.Running
  | .error (e, d) => .error (e, ofDevm d)
  | .ok (pc, d) => .ok (Frame.Running.ofEvm ⟨pc, sevm, d⟩)

/-- The square for a jump on a running frame. -/
theorem Frame.Running.ofJumpOutcome_run (evm : Evm) (j : JumpOp) :
    Frame.Running.ofJumpOutcome evm.sta (j.run evm) =
      Except.ofHalt (Staging.JumpOp.run (Frame.Running.ofEvm evm) j) := by
  have h := ofOutcome_jumpRunCore evm.pc evm.dyna evm.sta j
  unfold JumpOp.run Staging.JumpOp.run
  revert h
  generalize JumpOp.runCore evm.pc evm.dyna evm.sta j = o
  generalize hn : Staging.JumpOp.runCore _ _ _ j = n
  intro h
  rcases o with ⟨e, d⟩ | ⟨pc, d⟩ <;> rcases n with ⟨r, s⟩ | ⟨pc', s⟩ <;>
    simp_all [Except.mapState, Except.ofHalt, ofJumpOutcome, Frame.Running.ofEvm]

/-! ### Halts -/

private theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

theorem Devm.balReadAccount_output (rules : ForkRules) (a : Address) (d : Devm) :
    (d.balReadAccount rules a).output = d.output := by
  unfold Devm.balReadAccount; split <;> rfl

theorem Devm.subBal_some_output {d d' : Devm} {a : Address} {v : U256}
    (h : d.subBal a v = some d') : d'.output = d.output := by
  unfold Devm.subBal at h
  cases hs : Jaune.State.subBal d.state a v <;> simp [hs] at h
  subst h; rfl

theorem ofDevm_creditSelfdestructRefund (rules : ForkRules) (p : Prop) [Decidable p] (d : Devm) :
    ofDevm (creditSelfdestructRefund rules p d) =
      (ofDevm d).creditSelfdestructRefund rules p := by
  unfold creditSelfdestructRefund Frame.State.creditSelfdestructRefund; split <;> rfl

theorem ofDevm_addAccountToDelete (d : Devm) (a : Address) :
    ofDevm (addAccountToDelete d a) = (ofDevm d).addSelfDestruct a := rfl

theorem Agree.assertDynamic (sevm : Sevm) (d : Devm) :
    Except.Agree (fun _ _ => True) (Jaune.assertDynamic sevm d)
      ((ofDevm d).assertDynamic (CallContext.ofSevm sevm)) :=
  Except.Agree.assert _ d

/-- The common tail of `SELFDESTRUCT` before Amsterdam, from the charged state on. -/
private theorem selfdestructNone_tail (sevm : Sevm) (donee : Address) (bal : U256) (d₃ : Devm)
    (ho : d₃.output = []) :
    Frame.Exit.ofExecution (do
      Jaune.assertDynamic sevm d₃
      let devm ← Jaune.Option.toExcept
          (EvmError.internal (.invariant (.text "InsufficientBalanceError")), d₃)
          (d₃.subBal sevm.currentTarget bal)
      let devm ← Except.ok (Devm.creditBeneficiary sevm.benvStat.rules donee bal devm)
      if sevm.currentTarget ∈ devm.createdAccounts ∨
          sevm.benvStat.rules.settlement.selfdestructOnlyCreated = false then
        Except.ok (creditSelfdestructRefund sevm.benvStat.rules
          (sevm.currentTarget ∈ devm.accountsToDelete)
          (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget))
      else Except.ok devm) =
    Frame.Exit.catchHalt (do
      (ofDevm d₃).assertDynamic (CallContext.ofSevm sevm)
      match (ofDevm d₃).subtractBalance sevm.currentTarget bal with
      | none => return .error insufficientBalanceFault
      | some s =>
        let s := s.creditBeneficiary sevm.benvStat.rules donee bal
        if sevm.currentTarget ∈ s.createdAccounts ∨
            sevm.benvStat.rules.settlement.selfdestructOnlyCreated = false then
          return .ok (.finished []
            (((s.setBalance sevm.currentTarget 0).addSelfDestruct sevm.currentTarget
              ).creditSelfdestructRefund sevm.benvStat.rules
              (sevm.currentTarget ∈ s.selfDestructs)))
        else return .ok (.finished [] s)) := by
  refine (Agree.assertDynamic sevm d₃).toExit ?_
  intro _ _ _
  rw [← ofDevm_subBal]
  rcases hsb : d₃.subBal sevm.currentTarget bal with _ | d₄
  · rfl
  · have ho₄ : d₄.output = [] := by rw [Devm.subBal_some_output hsb, ho]
    simp only [Jaune.Option.toExcept, Option.map, ok_bind, ← ofDevm_creditBeneficiary]
    generalize hX : Devm.creditBeneficiary _ donee bal d₄ = X
    have hoX : X.output = [] := by rw [← hX, Devm.creditBeneficiary_output, ho₄]
    by_cases hc : sevm.currentTarget ∈ X.createdAccounts ∨
        sevm.benvStat.rules.settlement.selfdestructOnlyCreated = false
    · simp only [ofDevm_createdAccounts, hc, ↓reduceIte]
      show Except.ok (Frame.Exit.finished _ _) = Except.ok _
      rw [creditSelfdestructRefund_output, ofDevm_creditSelfdestructRefund]
      exact congrArg _ (congrArg₂ _ hoX rfl)
    · simp only [ofDevm_createdAccounts, hc, ↓reduceIte]
      show Except.ok (Frame.Exit.finished _ _) = Except.ok _
      rw [hoX]

/-- The tail of `SELFDESTRUCT` under Amsterdam, from the warmed and read state on. -/
private theorem selfdestructSome_tail (sevm : Sevm) (donee : Address) (bal : U256)
    (c₁ c₂ : Nat) (d₂ : Devm) (ho : d₂.output = []) :
    Frame.Exit.ofExecution (do
      let devm ← Jaune.chargeGas c₁ d₂
      let devm ← Jaune.chargeStateGas c₂ devm
      let devm ← Jaune.Option.toExcept
          (EvmError.internal (.invariant (.text "InsufficientBalanceError")), devm)
          (devm.subBal sevm.currentTarget bal)
      let devm := devm.addBal donee bal
      let devm := devm.emitTransferLog sevm.currentTarget donee bal
      if sevm.currentTarget ∈ devm.createdAccounts then
        Except.ok (addAccountToDelete devm sevm.currentTarget)
      else Except.ok devm) =
    Frame.Exit.catchHalt (do
      let s ← (ofDevm d₂).chargeGas c₁
      let s ← s.chargeStateGas c₂
      match s.subtractBalance sevm.currentTarget bal with
      | none => return .error insufficientBalanceFault
      | some s =>
        let s := (s.addBalance donee bal).emitTransferLog sevm.currentTarget donee bal
        if sevm.currentTarget ∈ s.createdAccounts then
          return .ok (.finished [] (s.addSelfDestruct sevm.currentTarget))
        else return .ok (.finished [] s)) := by
  refine ((Except.Agree.ofExecution (ofExecution_chargeGas c₁ d₂)).and_ok
    (P := fun d => d.output = []) ?_).toExit ?_
  · intro d₃ h; rw [Jaune.chargeGas] at h; rw [liftMachExecution_ok_output h, ho]
  rintro d₃ _ ⟨rfl, ho₃⟩
  refine ((Except.Agree.ofExecution (ofExecution_chargeStateGas c₂ d₃)).and_ok
    (P := fun d => d.output = []) ?_).toExit ?_
  · intro d₄ h; rw [Jaune.chargeStateGas] at h; rw [liftMachExecution_ok_output h, ho₃]
  rintro d₄ _ ⟨rfl, ho₄⟩
  rw [← ofDevm_subBal]
  rcases hsb : d₄.subBal sevm.currentTarget bal with _ | d₅
  · rfl
  · have ho₅ : d₅.output = [] := by rw [Devm.subBal_some_output hsb, ho₄]
    simp only [Jaune.Option.toExcept, Option.map, ok_bind, ← ofDevm_addBal,
      ← ofDevm_emitTransferLog]
    generalize hX : (d₅.addBal donee bal).emitTransferLog sevm.currentTarget donee bal = X
    have hoX : X.output = [] := by
      rw [← hX]; unfold Devm.emitTransferLog; split <;> exact ho₅
    by_cases hc : sevm.currentTarget ∈ X.createdAccounts
    · simp only [ofDevm_createdAccounts, hc, ↓reduceIte]
      show Except.ok (Frame.Exit.finished _ _) = Except.ok _
      exact congrArg _ (congrArg₂ _ hoX rfl)
    · simp only [ofDevm_createdAccounts, hc, ↓reduceIte]
      show Except.ok (Frame.Exit.finished _ _) = Except.ok _
      rw [hoX]

/-- The square for halts: every halt, every fork, from a state with no output. -/
theorem ofExecution_haltRun (sevm : Sevm) {d : Devm} (ho : d.output = []) (l : HaltOp) :
    Frame.Exit.ofExecution (HaltOp.run sevm d l) =
      Staging.HaltOp.run (CallContext.ofSevm sevm) (ofDevm d) l := by
  cases l
  case stop => simp only [HaltOp.run, Staging.HaltOp.run, Frame.Exit.ofExecution, ho]
  case revert =>
    simp only [HaltOp.run, Staging.HaltOp.run]
    refine (Except.Agree.ofOutcome (ofOutcome_popToNat d)).toExit ?_
    rintro ⟨i, d₁⟩ _ rfl
    refine (Except.Agree.ofOutcome (ofOutcome_popToNat d₁)).toExit ?_
    rintro ⟨n, d₂⟩ _ rfl
    refine (Except.Agree.ofExecution (ofExecution_chargeGas _ d₂)).toExit ?_
    rintro d₃ _ rfl
    have hm : (ofDevm d₃).machine.memory = d₃.memory := rfl
    simp only [Devm.memRead, Machine.memRead, hm]
    rcases d₃.memory.read i n with ⟨out, mem⟩
    rfl
  case return_ =>
    simp only [HaltOp.run, Staging.HaltOp.run]
    refine (Except.Agree.ofOutcome (ofOutcome_popToNat d)).toExit ?_
    rintro ⟨i, d₁⟩ _ rfl
    refine (Except.Agree.ofOutcome (ofOutcome_popToNat d₁)).toExit ?_
    rintro ⟨n, d₂⟩ _ rfl
    refine (Except.Agree.ofExecution (ofExecution_chargeGas _ d₂)).toExit ?_
    rintro d₃ _ rfl
    have hm : (ofDevm d₃).machine.memory = d₃.memory := rfl
    simp only [Devm.memRead, Machine.memRead, hm]
    rcases d₃.memory.read i n with ⟨out, mem⟩
    rfl
  case selfdestruct =>
    simp only [HaltOp.run, Staging.HaltOp.run, CallContext.ofSevm]
    rcases hsg : sevm.benvStat.rules.stateGas with _ | state
    · refine ((Except.Agree.ofOutcome (ofOutcome_popToAdr d)).and_ok
        (P := fun p => p.2.output = []) ?_).toExit ?_
      · rintro ⟨a, d₁⟩ h; rw [Devm.popToAdr] at h; rw [liftMach_ok_output h, ho]
      rintro ⟨donee, d₁⟩ _ ⟨rfl, ho₁⟩
      simp only [ok_bind, ← ofDevm_balReadAccount]
      generalize hd₂ : Devm.balReadAccount _ _ (Devm.balReadAccount _ donee d₁) = d₂
      have ho₂ : d₂.output = [] := by
        rw [← hd₂, Devm.balReadAccount_output, Devm.balReadAccount_output]; exact ho₁
      have charge : ∀ (d₃ : Devm) (c : Nat), d₃.output = [] →
          Frame.Exit.ofExecution (Jaune.chargeGas c d₃ >>= fun devm => (do
            Jaune.assertDynamic sevm devm
            let devm ← Jaune.Option.toExcept
                (EvmError.internal (.invariant (.text "InsufficientBalanceError")), devm)
                (devm.subBal sevm.currentTarget (d₂.getAcct sevm.currentTarget).balance)
            let devm ← Except.ok (Devm.creditBeneficiary sevm.benvStat.rules donee
              (d₂.getAcct sevm.currentTarget).balance devm)
            if sevm.currentTarget ∈ devm.createdAccounts ∨
                sevm.benvStat.rules.settlement.selfdestructOnlyCreated = false then
              Except.ok (creditSelfdestructRefund sevm.benvStat.rules
                (sevm.currentTarget ∈ devm.accountsToDelete)
                (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget))
            else Except.ok devm)) =
          Frame.Exit.catchHalt ((ofDevm d₃).chargeGas c >>= fun s => (do
            s.assertDynamic (CallContext.ofSevm sevm)
            match s.subtractBalance sevm.currentTarget
                ((ofDevm d₂).balance sevm.currentTarget) with
            | none => return .error insufficientBalanceFault
            | some s =>
              let s := s.creditBeneficiary sevm.benvStat.rules donee
                ((ofDevm d₂).balance sevm.currentTarget)
              if sevm.currentTarget ∈ s.createdAccounts ∨
                  sevm.benvStat.rules.settlement.selfdestructOnlyCreated = false then
                return .ok (.finished []
                  (((s.setBalance sevm.currentTarget 0).addSelfDestruct sevm.currentTarget
                    ).creditSelfdestructRefund sevm.benvStat.rules
                    (sevm.currentTarget ∈ s.selfDestructs)))
              else return .ok (.finished [] s))) := by
        intro d₃ c ho₃
        refine ((Except.Agree.ofExecution (ofExecution_chargeGas c d₃)).and_ok
          (P := fun d => d.output = []) ?_).toExit ?_
        · intro d₄ h; rw [Jaune.chargeGas] at h; rw [liftMachExecution_ok_output h, ho₃]
        rintro d₄ _ ⟨rfl, ho₄⟩
        exact selfdestructNone_tail sevm donee _ d₄ ho₄
      cases hacc : sevm.benvStat.rules.access
      case eip2929 =>
        simp only
        by_cases hcold : donee ∈ d₂.accessedAddresses
        · simp only [ofDevm_accessedAddresses, hcold, not_true_eq_false, ↓reduceIte]
          exact charge d₂ _ ho₂
        · simp only [ofDevm_accessedAddresses, hcold, not_false_eq_true, ↓reduceIte,
            ← ofDevm_addAccessedAddress]
          exact charge _ _ ho₂
      case flat g =>
        simp only
        exact charge d₂ _ ho₂
    · refine (Agree.assertDynamic sevm d).toExit ?_
      intro _ _ _
      refine ((Except.Agree.ofOutcome (ofOutcome_popToAdr d)).and_ok
        (P := fun p => p.2.output = []) ?_).toExit ?_
      · rintro ⟨a, d₁⟩ h; rw [Devm.popToAdr] at h; rw [liftMach_ok_output h, ho]
      rintro ⟨donee, d₁⟩ _ ⟨rfl, ho₁⟩
      refine (Except.Agree.assert _ d₁).toExit ?_
      intro _ _ _
      by_cases hcold : donee ∈ d₁.accessedAddresses
      · simp only [ofDevm_accessedAddresses, hcold, not_true_eq_false, ↓reduceIte,
          ← ofDevm_balReadAccount]
        exact selfdestructSome_tail sevm donee _ _ _ _ (by
          rw [Devm.balReadAccount_output, Devm.balReadAccount_output]; exact ho₁)
      · simp only [ofDevm_accessedAddresses, hcold, not_false_eq_true, ↓reduceIte,
          ← ofDevm_addAccessedAddress, ← ofDevm_balReadAccount]
        exact selfdestructSome_tail sevm donee _ _ _ _ (by
          rw [Devm.balReadAccount_output, Devm.balReadAccount_output]; exact ho₁)

/-- The square for a halt on a running frame. -/
theorem Frame.Running.ofExecution_haltRun (evm : Evm) (ho : evm.dyna.output = []) (l : HaltOp) :
    Frame.Exit.ofExecution (l.run evm.sta evm.dyna) =
      Staging.HaltOp.run (Frame.Running.ofEvm evm).context (Frame.Running.ofEvm evm).state l :=
  _root_.Jaune.ofExecution_haltRun evm.sta ho l

/-! ### `Evm.step`'s jump and halt arms -/

/-- The operation decoded on a running frame is the one `Evm.step` decodes. -/
theorem Frame.Running.getOp_ofEvm (evm : Evm) :
    (Frame.Running.ofEvm evm).getOp = evm.getInst := rfl

/-- `Evm.step`'s jump arm runs the old jump the jump squares relate. -/
theorem Evm.step_jump {evm : Evm} {j : JumpOp}
    (h : (Frame.Running.ofEvm evm).getOp = some (.jump j)) :
    evm.step = Step.ofJump (j.run evm) := by
  rw [Frame.Running.getOp_ofEvm] at h
  unfold Evm.step; rw [h]

/-- `Evm.step`'s halt arm runs the old halt the halt squares relate. -/
theorem Evm.step_halt {evm : Evm} {l : HaltOp}
    (h : (Frame.Running.ofEvm evm).getOp = some (.halt l)) :
    evm.step = .halt (l.run evm.sta evm.dyna) := by
  rw [Frame.Running.getOp_ofEvm] at h
  unfold Evm.step; rw [h]

/-! ### Precompiles -/

/-- Today's precompile bodies give the same result on the machine rebuilt from the running
frame: they read only the input, the rules and the gas left. -/
theorem precompileRun_precompileEvm (evm : Evm) (address : Address) :
    precompileRun (Frame.Running.ofEvm evm).precompileEvm address = precompileRun evm address := by
  unfold precompileRun
  split <;> rfl

/-- The square for a precompile's result, from a state with no output. -/
theorem ofExecution_applyPrecompileResult (evm : Evm) (ho : evm.dyna.output = [])
    (res : PrecompileResult) :
    Frame.Exit.ofExecution (applyPrecompileResult evm res) =
      Frame.Exit.ofPrecompileResult (ofDevm evm.dyna) res := by
  rcases res with ⟨_ | _ | _ | _, cost⟩ | ⟨cost, output⟩
  case error.revert =>
    show Except.ok (Frame.Exit.reverted _ _) = Except.ok _
    exact congrArg _ (congrArg₂ _ ho rfl)
  all_goals rfl

/-- The square for running a precompile, from a state with no output. -/
theorem ofExecution_executePrecompile (evm : Evm) (ho : evm.dyna.output = [])
    (address : Address) :
    Frame.Exit.ofExecution (executePrecompile evm address) =
      runPrecompile (Frame.Running.ofEvm evm) address := by
  rw [executePrecompile, ofExecution_applyPrecompileResult evm ho, runPrecompile,
    precompileRun_precompileEvm]
  rfl

end Jaune
