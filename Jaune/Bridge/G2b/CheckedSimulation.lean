import Jaune.Bridge.G2b.CheckedFrame
import Jaune.MessageCall.CheckedState

/-! Erasing the bounded memory commutes with machine operations on either result channel. -/

namespace Jaune.MemorySimulation

class Erases (α : Type) (β : outParam Type) where
  erase : α → β

export Erases (erase)

instance (priority := low) eraseId : Erases α α := ⟨id⟩
instance eraseMachine : Erases Checked.Machine Machine := ⟨Checked.Machine.toLegacy⟩
instance eraseState : Erases Checked.Frame.State Frame.State := ⟨Checked.Frame.State.toLegacy⟩
instance eraseFrame : Erases Checked.Frame Frame := ⟨Checked.Frame.toLegacy⟩
instance eraseRunning : Erases Checked.Frame.Running Frame.Running := ⟨Checked.Frame.Running.toLegacy⟩
instance eraseExit : Erases Checked.Frame.Exit Frame.Exit := ⟨Checked.Frame.Exit.toLegacy⟩
instance eraseProd [Erases α γ] [Erases β δ] : Erases (α × β) (γ × δ) :=
  ⟨fun p => (erase p.1, erase p.2)⟩
instance eraseExcept [Erases ε ζ] [Erases α β] : Erases (Except ε α) (Except ζ β) where
  erase
    | .error e => .error (erase e)
    | .ok a => .ok (erase a)

def Square [Erases α β] (x : α) (y : β) : Prop := erase x = y

theorem Square.legacy_eq [Erases α β] {x : α} {y : β} (h : Square x y) : y = erase x := h.symm

theorem erase_ok [Erases ε ζ] [Erases α β] (a : α) : erase (Except.ok (ε := ε) a) = (Except.ok (ε := ζ) (erase a) : Except ζ β) := rfl
theorem erase_same (a : α) : @erase _ _ eraseId a = a := rfl

theorem Square.bind [Erases ε ζ] [Erases α β] [Erases γ δ]
    {x : Except ε α} {y : Except ζ β} {f : α → Except ε γ} {g : β → Except ζ δ}
    (h : Square x y) (k : ∀ a, Square (f a) (g (erase a))) : Square (x >>= f) (y >>= g) := by
  change erase x = y at h
  subst y
  cases x with
  | error e => rfl
  | ok a => exact k a

theorem Square.casesExcept [Erases ε ζ] [Erases α β] [Erases γ δ]
    {x : Except ε α} {y : Except ζ β}
    {ce : ε → γ} {co : α → γ} {le : ζ → δ} {lo : β → δ}
    (h : Square x y) (he : ∀ e, Square (ce e) (le (erase e)))
    (ho : ∀ a, Square (co a) (lo (erase a))) :
    Square (match x with | .error e => ce e | .ok a => co a)
      (match y with | .error e => le e | .ok a => lo a) := by
  change erase x = y at h
  subst y
  cases x with
  | error e => exact he e
  | ok a => exact ho a

theorem Square.ok [Erases ε ζ] [Erases α β] {a : α} {b : β} (h : Square a b) :
    Square (Except.ok a : Except ε α) (Except.ok b : Except ζ β) :=
  congrArg Except.ok h

theorem Square.error [Erases ε ζ] [Erases α β] {a : ε} {b : ζ} (h : Square a b) :
    Square (Except.error a : Except ε α) (Except.error b : Except ζ β) :=
  congrArg Except.error h

theorem Square.pair [Erases α γ] [Erases β δ] {a : α} {b : β} {c : γ} {d : δ}
    (h : Square a c) (k : Square b d) : Square (a, b) (c, d) := congrArg₂ Prod.mk h k

theorem Square.ite [Erases α β] {c d : Prop} [Decidable c] [Decidable d]
    {x y : α} {u v : β} (cd : c = d) (h : c → Square x u) (k : ¬ c → Square y v) :
    Square (if c then x else y) (if d then u else v) := by
  subst d
  by_cases hc : c
  · simpa only [hc, ↓reduceIte] using h hc
  · simpa only [hc, ↓reduceIte] using k hc

@[simp] theorem erase_machine (m : Checked.Machine) : erase m = m.toLegacy := rfl
@[simp] theorem erase_state (s : Checked.Frame.State) : erase s = s.toLegacy := rfl
@[simp] theorem erase_pair [Erases α γ] [Erases β δ] (a : α) (b : β) :
    erase (a,b) = (erase a, erase b) := rfl

theorem Machine.memWrite (m : Checked.Machine) (i : Nat) (b : Bytes) :
    Square (m.memWrite i b) (m.toLegacy.memWrite i b) := by
  change Checked.Machine.toLegacy {m with memory := m.memory.write i b} = _
  simp only [Checked.Machine.toLegacy, Memory.write_toMem]
  rfl

theorem Machine.memExtends (m : Checked.Machine) (pairs : List (Nat × Nat)) :
    Square (m.memExtends pairs) (m.toLegacy.memExtends pairs) := rfl

theorem Machine.memRead (m : Checked.Machine) (i n : Nat) :
    Square (m.memRead i n) (m.toLegacy.memRead i n) := rfl

theorem Machine.push (x : U256) (m : Checked.Machine) :
    Square (m.push x) (m.toLegacy.push x) := by
  by_cases h : m.stack.length < 1024 <;>
    simp only [Checked.Machine.push, Jaune.Machine.push, Checked.Machine.toLegacy, h, ite_true, ite_false] <;> rfl

theorem Machine.pop (m : Checked.Machine) : Square m.pop m.toLegacy.pop := by
  cases m with
  | mk stack mem gas sg rd => cases stack <;> rfl

theorem Machine.chargeGas (m : Checked.Machine) (n : Nat) :
    Square (m.chargeGas n) (m.toLegacy.chargeGas n) := by
  cases hg : safeSub m.gasLeft n <;>
    simp only [Checked.Machine.chargeGas, Jaune.Machine.chargeGas, Checked.Machine.toLegacy, hg] <;> rfl

theorem Machine.chargeStateGas (m : Checked.Machine) (n : Nat) :
    Square (m.chargeStateGas n) (m.toLegacy.chargeStateGas n) := by
  unfold Checked.Machine.chargeStateGas Jaune.Machine.chargeStateGas
  by_cases ha : n ≤ m.stateGas.left
  · simp only [Checked.Machine.toLegacy, ha, ite_true]; rfl
  · by_cases hb : n - m.stateGas.left ≤ m.gasLeft <;>
      simp only [Checked.Machine.toLegacy, ha, hb, ite_true, ite_false] <;> rfl

theorem Machine.popToNat (m : Checked.Machine) : Square m.popToNat m.toLegacy.popToNat := by
  unfold Checked.Machine.popToNat Jaune.Machine.popToNat
  rw [(Machine.pop m).legacy_eq]
  rcases m.pop with e | ⟨x, t⟩ <;> rfl

theorem Machine.popToAddress (m : Checked.Machine) : Square m.popToAddress m.toLegacy.popToAddress := by
  unfold Checked.Machine.popToAddress Jaune.Machine.popToAddress
  rw [(Machine.pop m).legacy_eq]
  rcases m.pop with e | ⟨x, t⟩ <;> rfl

theorem Machine.popN (n : Nat) (m : Checked.Machine) :
    Square (m.popN n) (m.toLegacy.popN n) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Checked.Machine.popN, Jaune.Machine.popN]
    rw [(Machine.pop m).legacy_eq]
    rcases m.pop with e | ⟨x, m'⟩
    · rfl
    · simp only [erase_ok, erase_pair, erase_machine, erase_same]
      rw [(ih m').legacy_eq]
      rcases m'.popN n with e | ⟨xs, t⟩ <;> rfl

theorem Machine.pushItem (v : U256) (n : Nat) (m : Checked.Machine) :
    Square (m.pushItem v n) (m.toLegacy.pushItem v n) := by
  unfold Checked.Machine.pushItem Jaune.Machine.pushItem
  rw [(Machine.chargeGas m n).legacy_eq]
  rcases m.chargeGas n with e | t
  · rfl
  · exact Machine.push v t

theorem Machine.applyUnary (f : U256 → U256) (n : Nat) (m : Checked.Machine) :
    Square (m.applyUnary f n) (m.toLegacy.applyUnary f n) := by
  unfold Checked.Machine.applyUnary Jaune.Machine.applyUnary
  rw [(Machine.pop m).legacy_eq]
  rcases m.pop with e | ⟨x, m'⟩
  · rfl
  · exact Machine.pushItem (f x) n m'

theorem Machine.applyBinary (f : U256 → U256 → U256) (n : Nat) (m : Checked.Machine) :
    Square (m.applyBinary f n) (m.toLegacy.applyBinary f n) := by
  unfold Checked.Machine.applyBinary Jaune.Machine.applyBinary
  rw [(Machine.pop m).legacy_eq]
  rcases m.pop with e | ⟨x, m'⟩
  · rfl
  · simp only [erase_ok, erase_pair, erase_machine, erase_same]
    rw [(Machine.pop m').legacy_eq]
    rcases m'.pop with e | ⟨y, m''⟩
    · rfl
    · exact Machine.pushItem (f x y) n m''

theorem Machine.applyTernary (f : U256 → U256 → U256 → U256) (n : Nat) (m : Checked.Machine) :
    Square (m.applyTernary f n) (m.toLegacy.applyTernary f n) := by
  unfold Checked.Machine.applyTernary Jaune.Machine.applyTernary
  rw [(Machine.pop m).legacy_eq]
  rcases m.pop with e | ⟨x, m'⟩
  · rfl
  · simp only [erase_ok, erase_pair, erase_machine, erase_same]
    rw [(Machine.pop m').legacy_eq]
    rcases m'.pop with e | ⟨y, m''⟩
    · rfl
    · simp only [erase_ok, erase_pair, erase_machine, erase_same]
      rw [(Machine.pop m'').legacy_eq]
      rcases m''.pop with e | ⟨z, m'''⟩
      · rfl
      · exact Machine.pushItem (f x y z) n m'''

theorem Frame.State.liftMachine {f : Checked.Machine → Except (ExceptionalHalt × Checked.Machine) Checked.Machine}
    {g : Jaune.Machine → Except (ExceptionalHalt × Jaune.Machine) Jaune.Machine}
    (s : Checked.Frame.State) (h : ∀ m, Square (f m) (g m.toLegacy)) :
    Square (s.liftMachine f) (s.toLegacy.liftMachine g) := by
  unfold Checked.Frame.State.liftMachine Jaune.Frame.State.liftMachine
  rw [show s.toLegacy.machine = s.machine.toLegacy from rfl, (h s.machine).legacy_eq]
  rcases f s.machine with ⟨e, m⟩ | m <;> rfl

theorem Frame.State.liftMachineValue
    {f : Checked.Machine → Except (ExceptionalHalt × Checked.Machine) (α × Checked.Machine)}
    {g : Jaune.Machine → Except (ExceptionalHalt × Jaune.Machine) (α × Jaune.Machine)}
    (s : Checked.Frame.State) (h : ∀ m, Square (f m) (g m.toLegacy)) :
    Square (s.liftMachineValue f) (s.toLegacy.liftMachineValue g) := by
  unfold Checked.Frame.State.liftMachineValue Jaune.Frame.State.liftMachineValue
  rw [show s.toLegacy.machine = s.machine.toLegacy from rfl, (h s.machine).legacy_eq]
  rcases f s.machine with ⟨e, m⟩ | ⟨a, m⟩ <;> rfl

theorem Frame.State.push (s : Checked.Frame.State) (w : U256) :
    Square (s.push w) (s.toLegacy.push w) := Frame.State.liftMachine s (Machine.push w)
theorem Frame.State.pop (s : Checked.Frame.State) : Square s.pop s.toLegacy.pop :=
  Frame.State.liftMachineValue s Machine.pop
theorem Frame.State.popToNat (s : Checked.Frame.State) : Square s.popToNat s.toLegacy.popToNat :=
  Frame.State.liftMachineValue s Machine.popToNat
theorem Frame.State.popToAddress (s : Checked.Frame.State) : Square s.popToAddress s.toLegacy.popToAddress :=
  Frame.State.liftMachineValue s Machine.popToAddress
theorem Frame.State.popN (s : Checked.Frame.State) (n : Nat) :
    Square (s.popN n) (s.toLegacy.popN n) := Frame.State.liftMachineValue s (Machine.popN n)
theorem Frame.State.chargeGas (s : Checked.Frame.State) (n : Nat) :
    Square (s.chargeGas n) (s.toLegacy.chargeGas n) := Frame.State.liftMachine s (fun m => Machine.chargeGas m n)
theorem Frame.State.chargeStateGas (s : Checked.Frame.State) (n : Nat) :
    Square (s.chargeStateGas n) (s.toLegacy.chargeStateGas n) :=
  Frame.State.liftMachine s (fun m => Machine.chargeStateGas m n)
theorem Frame.State.pushItem (s : Checked.Frame.State) (w : U256) (n : Nat) :
    Square (s.pushItem w n) (s.toLegacy.pushItem w n) := Frame.State.liftMachine s (Machine.pushItem w n)
theorem Frame.State.applyUnary (s : Checked.Frame.State) (f : U256 → U256) (n : Nat) :
    Square (s.applyUnary f n) (s.toLegacy.applyUnary f n) := Frame.State.liftMachine s (Machine.applyUnary f n)
theorem Frame.State.applyBinary (s : Checked.Frame.State) (f : U256 → U256 → U256) (n : Nat) :
    Square (s.applyBinary f n) (s.toLegacy.applyBinary f n) := Frame.State.liftMachine s (Machine.applyBinary f n)
theorem Frame.State.applyTernary (s : Checked.Frame.State) (f : U256 → U256 → U256 → U256) (n : Nat) :
    Square (s.applyTernary f n) (s.toLegacy.applyTernary f n) := Frame.State.liftMachine s (Machine.applyTernary f n)

theorem Square.assert {ε ζ : Type} [Erases ε ζ] (p : Prop) [Decidable p] (e : ε) :
    Square (Except.assert p e) (Except.assert p (erase e : ζ)) := by
  by_cases hp : p <;> simp only [Except.assert, hp, ite_true, ite_false] <;> rfl

theorem Frame.State.assertDynamic (s : Checked.Frame.State) (ctx : CallContext) :
    Square (s.assertDynamic ctx) (s.toLegacy.assertDynamic ctx) := by
  unfold Checked.Frame.State.assertDynamic Jaune.Frame.State.assertDynamic
  apply Square.assert

theorem Frame.State.memWrite (s : Checked.Frame.State) (i : Nat) (b : Bytes) :
    Square (s.memWrite i b) (s.toLegacy.memWrite i b) := by
  change ⟨(s.machine.memWrite i b).toLegacy, _, _, _⟩ = s.toLegacy.memWrite i b
  rw [show (s.machine.memWrite i b).toLegacy = s.machine.toLegacy.memWrite i b from Machine.memWrite ..]
  rfl

theorem Frame.State.memRead (s : Checked.Frame.State) (i n : Nat) :
    Square (s.memRead i n) (s.toLegacy.memRead i n) := rfl

theorem Frame.State.memExtends (s : Checked.Frame.State) (p : List (Nat × Nat)) :
    Square (s.memExtends p) (s.toLegacy.memExtends p) := rfl

end Jaune.MemorySimulation
