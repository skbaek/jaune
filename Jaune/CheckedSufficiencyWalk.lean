import Jaune.MessageCall.CheckedDriver

/-!
# Walks over the staged instruction bodies (goal `jaune-shape-and-names-v1`, G2b port of the W3-4b walks)

The checked instruction bodies (`Jaune.Checked.PlainOp.runCore`, `JumpOp.runCore`, `HaltOp.run`,
`MessageOp.step`) run in the halt-only monad over `Frame.State`, and most of them lift a
computation over `Machine`. A fact about every state such a computation can stop in, or return,
is proved by one walk through its binds: `Walk H P x` says every halt's state satisfies `H` and
every value satisfies `P`, and `MWalk` is its `Machine` twin.

Two families of primitive facts are proved here, one per invariant the proof modules carry:

* the gas family (`*_gas`): no primitive raises the measure `Machine.gasMeasure`, a charge lowers
  it by exactly its cost, and a halt's state measures at most the bound `n` the walk carries;
* the meter family (`*_meter`): no primitive other than a state-gas charge changes the
  state-gas meter.

The fuel sufficiency argument (`Jaune.Checked` totality) uses the first, the zero-meter invariant
(`Jaune.MessageCall.CheckedStateGasZero`) the second.
-/

namespace Jaune.Checked

open Jaune

/-! ### The walk predicates -/

/-- Every halt of a machine computation stops in a machine satisfying `H`; every value
satisfies `P`. -/
def MWalk {ε α : Type} (H : Machine → Prop) (P : α → Prop) : Except (ε × Machine) α → Prop
  | .error e => H e.2
  | .ok a => P a

/-- Every halt of a state computation stops in a state satisfying `H`; every value satisfies
`P`. -/
def Walk {ε α : Type} (H : Frame.State → Prop) (P : α → Prop) :
    Except (ε × Frame.State) α → Prop
  | .error e => H e.2
  | .ok a => P a

namespace MWalk

variable {ε α β : Type} {H : Machine → Prop} {P : α → Prop} {Q : β → Prop}

@[simp] theorem ok_iff (a : α) : MWalk (ε := ε) H P (.ok a) ↔ P a := Iff.rfl
@[simp] theorem error_iff (e : ε × Machine) : MWalk H P (.error e : Except _ α) ↔ H e.2 := Iff.rfl

theorem bind {x : Except (ε × Machine) α} {f : α → Except (ε × Machine) β}
    (hx : MWalk H P x) (hf : ∀ a, P a → MWalk H Q (f a)) : MWalk H Q (x >>= f) := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem mono {P' : α → Prop} {x : Except (ε × Machine) α} (hx : MWalk H P x)
    (h : ∀ a, P a → P' a) : MWalk H P' x := by
  cases x with
  | error e => exact hx
  | ok a => exact h a hx

end MWalk

namespace Walk

variable {ε α β : Type} {H : Frame.State → Prop} {P : α → Prop} {Q : β → Prop}

@[simp] theorem ok_iff (a : α) : Walk (ε := ε) H P (.ok a) ↔ P a := Iff.rfl
@[simp] theorem error_iff (e : ε × Frame.State) :
    Walk H P (.error e : Except _ α) ↔ H e.2 := Iff.rfl

theorem bind {x : Except (ε × Frame.State) α} {f : α → Except (ε × Frame.State) β}
    (hx : Walk H P x) (hf : ∀ a, P a → Walk H Q (f a)) : Walk H Q (x >>= f) := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem mono {P' : α → Prop} {x : Except (ε × Frame.State) α} (hx : Walk H P x)
    (h : ∀ a, P a → P' a) : Walk H P' x := by
  cases x with
  | error e => exact hx
  | ok a => exact h a hx

theorem mono' {H' : Frame.State → Prop} {P' : α → Prop} {x : Except (ε × Frame.State) α}
    (hx : Walk H P x) (hH : ∀ s, H s → H' s) (h : ∀ a, P a → P' a) : Walk H' P' x := by
  cases x with
  | error e => exact hH _ hx
  | ok a => exact h a hx

/-- A lifted machine computation walks as the computation does, read on the machine. -/
theorem liftMachine {Hm : Machine → Prop} {Pm : Machine → Prop}
    {core : Machine → Except (ε × Machine) Machine} {s : Frame.State}
    (h : MWalk Hm Pm (core s.machine)) :
    Walk (fun s' => Hm s'.machine) (fun s' => Pm s'.machine) (s.liftMachine core) := by
  unfold Frame.State.liftMachine
  rcases hc : core s.machine with ⟨e, m⟩ | m <;> rw [hc] at h <;> exact h

/-- `liftMachine` for a computation that returns a value. -/
theorem liftMachineValue {γ : Type} {Hm : Machine → Prop} {Pm : γ × Machine → Prop}
    {core : Machine → Except (ε × Machine) (γ × Machine)} {s : Frame.State}
    (h : MWalk Hm Pm (core s.machine)) :
    Walk (fun s' => Hm s'.machine) (fun p : γ × Frame.State => Pm (p.1, p.2.machine))
      (s.liftMachineValue core) := by
  unfold Frame.State.liftMachineValue
  rcases hc : core s.machine with ⟨e, m⟩ | ⟨a, m⟩ <;> rw [hc] at h <;> exact h

theorem assert {p : Prop} [Decidable p] {e : ε} {s : Frame.State} (hs : H s) :
    Walk H (fun _ : Unit => True) (Except.assert p (e, s)) := by
  unfold Except.assert
  split
  · trivial
  · exact hs

end Walk

theorem MWalk.assert {ε : Type} {H : Machine → Prop} {p : Prop} [Decidable p] {e : ε}
    {m : Machine} (hm : H m) : MWalk H (fun _ : Unit => True) (Except.assert p (e, m)) := by
  unfold Except.assert
  split
  · trivial
  · exact hm

/-- `liftMachine` read for the gas family: the halt bound on the state is the bound on its
machine. -/
theorem Walk.liftMachine_gas {ε : Type} {n : Nat} {P : Frame.State → Prop}
    {core : Machine → Except (ε × Machine) Machine} {s : Frame.State}
    (h : MWalk (·.gasMeasure ≤ n) (fun m => P (s.withMachine m)) (core s.machine)) :
    Walk (·.machine.gasMeasure ≤ n) P (s.liftMachine core) := by
  unfold Frame.State.liftMachine
  rcases hc : core s.machine with ⟨e, m⟩ | m <;> rw [hc] at h <;> exact h

/-! ### The gas family: machine primitives -/

namespace Machine

variable {n : Nat}

@[simp] theorem gasMeasure_withStack (m : Machine) (st : List U256) :
    ({ m with stack := st } : Machine).gasMeasure = m.gasMeasure := rfl
@[simp] theorem gasMeasure_withMemory (m : Machine) (mem : Memory) :
    ({ m with memory := mem } : Machine).gasMeasure = m.gasMeasure := rfl
@[simp] theorem gasMeasure_withReturnData (m : Machine) (r : Bytes) :
    ({ m with returnData := r } : Machine).gasMeasure = m.gasMeasure := rfl
@[simp] theorem memWrite_gasMeasure (m : Machine) (i : Nat) (v : Bytes) :
    (m.memWrite i v).gasMeasure = m.gasMeasure := rfl
@[simp] theorem memExtends_gasMeasure (m : Machine) (ps : List (Nat × Nat)) :
    (m.memExtends ps).gasMeasure = m.gasMeasure := rfl
@[simp] theorem memRead_gasMeasure (m : Machine) (i k : Nat) :
    (m.memRead i k).2.gasMeasure = m.gasMeasure := rfl

theorem gasMeasure_eq (m : Machine) :
    m.gasMeasure = m.gasLeft + m.stateGas.spilled + m.stateGas.committedSpill := rfl

theorem push_gas (x : U256) {m : Machine} (h : m.gasMeasure ≤ n) :
    MWalk (ε := ExceptionalHalt) (·.gasMeasure ≤ n) (·.gasMeasure = m.gasMeasure) (m.push x) := by
  unfold Machine.push; split <;> simp [h]

theorem pop_gas {m : Machine} (h : m.gasMeasure ≤ n) :
    MWalk (ε := ExceptionalHalt) (·.gasMeasure ≤ n) (fun p => p.2.gasMeasure = m.gasMeasure)
      m.pop := by
  unfold Machine.pop; split <;> simp [h]

theorem popToNat_gas {m : Machine} (h : m.gasMeasure ≤ n) :
    MWalk (ε := ExceptionalHalt) (·.gasMeasure ≤ n) (fun p => p.2.gasMeasure = m.gasMeasure)
      m.popToNat := by
  unfold Machine.popToNat
  have := pop_gas h
  split <;> rename_i heq <;> rw [heq] at this <;> simpa using this

theorem popToAddress_gas {m : Machine} (h : m.gasMeasure ≤ n) :
    MWalk (ε := ExceptionalHalt) (·.gasMeasure ≤ n) (fun p => p.2.gasMeasure = m.gasMeasure)
      m.popToAddress := by
  unfold Machine.popToAddress
  have := pop_gas h
  split <;> rename_i heq <;> rw [heq] at this <;> simpa using this

theorem popN_gas : ∀ (k : Nat) {m : Machine}, m.gasMeasure ≤ n →
    MWalk (ε := ExceptionalHalt) (·.gasMeasure ≤ n) (fun p => p.2.gasMeasure = m.gasMeasure)
      (m.popN k)
  | 0, m, _ => by simp [Machine.popN]
  | k + 1, m, h => by
    unfold Machine.popN
    have h1 := pop_gas h
    split
    · rename_i heq; rw [heq] at h1; exact h1
    · rename_i x m' heq
      rw [heq] at h1
      simp only [MWalk.ok_iff] at h1
      have h2 := popN_gas k (m := m') (by omega)
      split
      · rename_i heq2; rw [heq2] at h2; exact h2
      · rename_i heq2; rw [heq2] at h2; simp only [MWalk.ok_iff] at h2 ⊢; omega

theorem chargeGas_gas (c : Nat) {m : Machine} (h : m.gasMeasure ≤ n) :
    MWalk (ε := ExceptionalHalt) (·.gasMeasure ≤ n) (·.gasMeasure + c = m.gasMeasure)
      (m.chargeGas c) := by
  unfold Machine.chargeGas safeSub
  split
  · simp [h]
  · rename_i g hg
    split at hg
    · cases hg; simp only [MWalk.ok_iff, Machine.gasMeasure]; omega
    · cases hg

theorem pushItem_gas (x : U256) (c : Nat) {m : Machine} (h : m.gasMeasure ≤ n) :
    MWalk (ε := ExceptionalHalt) (·.gasMeasure ≤ n) (·.gasMeasure + c = m.gasMeasure)
      (m.pushItem x c) := by
  unfold Machine.pushItem
  have h1 := chargeGas_gas c h
  split
  · rename_i heq; rw [heq] at h1; exact h1
  · rename_i m' heq
    rw [heq] at h1
    simp only [MWalk.ok_iff] at h1
    exact MWalk.mono (push_gas (n := n) x (by omega)) (fun a ha => by omega)

theorem applyUnary_gas (f : U256 → U256) (c : Nat) {m : Machine} (h : m.gasMeasure ≤ n) :
    MWalk (ε := ExceptionalHalt) (·.gasMeasure ≤ n) (·.gasMeasure + c = m.gasMeasure)
      (m.applyUnary f c) := by
  unfold Machine.applyUnary
  have h1 := pop_gas h
  split
  · rename_i heq; rw [heq] at h1; exact h1
  · rename_i x m' heq
    rw [heq] at h1
    simp only [MWalk.ok_iff] at h1
    exact MWalk.mono (pushItem_gas (n := n) _ c (by omega)) (fun a ha => by omega)

theorem applyBinary_gas (f : U256 → U256 → U256) (c : Nat) {m : Machine}
    (h : m.gasMeasure ≤ n) :
    MWalk (ε := ExceptionalHalt) (·.gasMeasure ≤ n) (·.gasMeasure + c = m.gasMeasure)
      (m.applyBinary f c) := by
  unfold Machine.applyBinary
  have h1 := pop_gas h
  split
  · rename_i heq; rw [heq] at h1; exact h1
  · rename_i x m' heq
    rw [heq] at h1
    simp only [MWalk.ok_iff] at h1
    have h2 := pop_gas (n := n) (m := m') (by omega)
    split
    · rename_i heq2; rw [heq2] at h2; exact h2
    · rename_i y m'' heq2
      rw [heq2] at h2
      simp only [MWalk.ok_iff] at h2
      exact MWalk.mono (pushItem_gas (n := n) _ c (by omega)) (fun a ha => by omega)

theorem applyTernary_gas (f : U256 → U256 → U256 → U256) (c : Nat) {m : Machine}
    (h : m.gasMeasure ≤ n) :
    MWalk (ε := ExceptionalHalt) (·.gasMeasure ≤ n) (·.gasMeasure + c = m.gasMeasure)
      (m.applyTernary f c) := by
  unfold Machine.applyTernary
  have h1 := pop_gas h
  split
  · rename_i heq; rw [heq] at h1; exact h1
  · rename_i x m' heq
    rw [heq] at h1
    simp only [MWalk.ok_iff] at h1
    have h2 := pop_gas (n := n) (m := m') (by omega)
    split
    · rename_i heq2; rw [heq2] at h2; exact h2
    · rename_i y m'' heq2
      rw [heq2] at h2
      simp only [MWalk.ok_iff] at h2
      have h3 := pop_gas (n := n) (m := m'') (by omega)
      split
      · rename_i heq3; rw [heq3] at h3; exact h3
      · rename_i z m''' heq3
        rw [heq3] at h3
        simp only [MWalk.ok_iff] at h3
        exact MWalk.mono (pushItem_gas (n := n) _ c (by omega)) (fun a ha => by omega)

theorem chargeStateGas_gas (a : Nat) {m : Machine} (h : m.gasMeasure ≤ n) :
    MWalk (ε := ExceptionalHalt) (·.gasMeasure ≤ n) (·.gasMeasure = m.gasMeasure)
      (m.chargeStateGas a) := by
  unfold Machine.chargeStateGas
  split
  · simp only [MWalk.ok_iff, Machine.gasMeasure]
  · split
    · simp only [MWalk.ok_iff, Machine.gasMeasure]; omega
    · simp [h]

@[simp] theorem creditStateGasRefund_gasMeasure (a : Nat) (m : Machine) :
    (m.creditStateGasRefund a).gasMeasure = m.gasMeasure := by
  simp only [Machine.creditStateGasRefund, Machine.gasMeasure]; omega

@[simp] theorem repayStateGasSpill_gasMeasure (m : Machine) :
    m.repayStateGasSpill.gasMeasure = m.gasMeasure := by
  simp only [Machine.repayStateGasSpill, Machine.gasMeasure]; omega

@[simp] theorem restoreStateGas_gasMeasure (m : Machine) :
    m.restoreStateGas.gasMeasure = m.gasMeasure := by
  simp only [Machine.restoreStateGas, Machine.gasMeasure]; omega

@[simp] theorem drainStateGasReservoir_gasMeasure (m : Machine) :
    m.drainStateGasReservoir.2.gasMeasure = m.gasMeasure := rfl

theorem withholdCreateGas_gasMeasure (m : Machine) :
    m.withholdCreateGas.2.gasMeasure + m.withholdCreateGas.1 = m.gasMeasure := by
  simp only [Machine.withholdCreateGas, Machine.gasMeasure]
  have : except64th m.gasLeft ≤ m.gasLeft := by unfold except64th; omega
  omega

end Machine

/-! ### The gas family: state primitives -/

namespace Frame.State

variable {n : Nat}

@[simp] theorem liftMachinePure_machine (core : Machine → Machine) (s : Frame.State) :
    (s.liftMachinePure core).machine = core s.machine := rfl

theorem push_gas (x : U256) {s : Frame.State} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure = s.machine.gasMeasure) (s.push x) :=
  Walk.liftMachine (Machine.push_gas x h)

theorem pop_gas {s : Frame.State} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (fun p => p.2.machine.gasMeasure = s.machine.gasMeasure)
      s.pop :=
  Walk.liftMachineValue (Machine.pop_gas h)

theorem popToNat_gas {s : Frame.State} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (fun p => p.2.machine.gasMeasure = s.machine.gasMeasure)
      s.popToNat :=
  Walk.liftMachineValue (Machine.popToNat_gas h)

theorem popToAddress_gas {s : Frame.State} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (fun p => p.2.machine.gasMeasure = s.machine.gasMeasure)
      s.popToAddress :=
  Walk.liftMachineValue (Machine.popToAddress_gas h)

theorem popN_gas (k : Nat) {s : Frame.State} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (fun p => p.2.machine.gasMeasure = s.machine.gasMeasure)
      (s.popN k) :=
  Walk.liftMachineValue (core := (Machine.popN · k)) (Machine.popN_gas k h)

theorem chargeGas_gas (c : Nat) {s : Frame.State} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure + c = s.machine.gasMeasure)
      (s.chargeGas c) :=
  Walk.liftMachine (Machine.chargeGas_gas c h)

theorem pushItem_gas (x : U256) (c : Nat) {s : Frame.State} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure + c = s.machine.gasMeasure)
      (s.pushItem x c) :=
  Walk.liftMachine (Machine.pushItem_gas x c h)

theorem applyUnary_gas (f : U256 → U256) (c : Nat) {s : Frame.State}
    (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure + c = s.machine.gasMeasure)
      (s.applyUnary f c) :=
  Walk.liftMachine (Machine.applyUnary_gas f c h)

theorem applyBinary_gas (f : U256 → U256 → U256) (c : Nat) {s : Frame.State}
    (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure + c = s.machine.gasMeasure)
      (s.applyBinary f c) :=
  Walk.liftMachine (Machine.applyBinary_gas f c h)

theorem applyTernary_gas (f : U256 → U256 → U256 → U256) (c : Nat) {s : Frame.State}
    (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure + c = s.machine.gasMeasure)
      (s.applyTernary f c) :=
  Walk.liftMachine (Machine.applyTernary_gas f c h)

theorem chargeStateGas_gas (a : Nat) {s : Frame.State} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure = s.machine.gasMeasure)
      (s.chargeStateGas a) :=
  Walk.liftMachine (Machine.chargeStateGas_gas a h)

theorem assertDynamic_gas (ctx : CallContext) {s : Frame.State} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (fun _ : Unit => True) (s.assertDynamic ctx) :=
  Walk.assert (H := (·.machine.gasMeasure ≤ n)) h

end Frame.State

end Jaune.Checked
