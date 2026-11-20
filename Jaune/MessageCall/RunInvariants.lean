import Jaune.MessageCall.Exec
import Jaune.MessageCall.ResumeFacts
import Jaune.MessageCall.Measures

/-!
# Two run invariants of the four-part message call (goal `jaune-shape-and-names-v1`, S3)

`resume_failed` and `resume_success` (`Jaune.MessageCall.ResumeFacts`) take two premises that
`resume` alone cannot supply: `room`, that the saved caller's stack has room for the calling
opcode's push, and `settled`, that a failed child's meter is settled. Each follows from a run
invariant, proved here once, by induction, so that a client discharges them without unfolding
the interpreter:

* **The stack bound.** Before every step a frame's stack holds at most 1024 words: a frame
  starts empty and every push is guarded. A spawning opcode pops at least one word, so its
  saved caller has fewer than 1024 (`Evm.Reaches.room`).
* **An uncommitted child.** Nothing in a frame's run commits state gas (only the top frame
  does, at transaction preparation), so a spawned child, which starts with no committed spill,
  ends with none; settlement then leaves a failed child's meter settled
  (`settled_of_enter_run`).

Both invariants are carried by one walk over every instruction (`Inv c n`: committed spill `c`,
and room for `n` more words), on both result channels.

This module is the instruction-level walk (register, jump and halting instructions, and the four
message-opcode tails with their spawn obligation); `Jaune.MessageCall.DriverInvariants` carries
it through the message-opcode dispatch, `Evm.step`, `resume` and the driver, and states the
client theorems named above.
-/

namespace Jaune

namespace RunInvariants

/-! ## The walked invariant -/

/-- A machine with committed spill `c` and room for `n` more stack words. -/
def MInv (c n : Nat) (m : Mach) : Prop :=
  m.stateGas.committedSpill = c ∧ m.stack.length + n ≤ 1024

/-- `MInv` of a machine's `Mach`. -/
def Inv (c n : Nat) (d : Devm) : Prop := MInv c n d.mach

/-- Any machine with the same meter and stack, and no more room demanded. -/
theorem Inv.keep {c n k : Nat} {d d' : Devm} (h : Inv c n d)
    (hcs : d'.mach.stateGas.committedSpill = d.mach.stateGas.committedSpill)
    (hst : d'.mach.stack = d.mach.stack) (hk : k ≤ n) : Inv c k d' := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨hcs.trans h1, by rw [hst]; omega⟩

/-- `P` on success and `Inv c 0` on the machine an error carries. -/
def Both {α : Type} (c : Nat) (P : α → Prop) : Except (EvmError × Devm) α → Prop
  | .ok a => P a
  | .error e => Inv c 0 e.2

theorem Both.bind {α β : Type} {c : Nat} {P : α → Prop} {Q : β → Prop}
    {x : Except (EvmError × Devm) α} {f : α → Except (EvmError × Devm) β}
    (hx : Both c P x) (hf : ∀ a, P a → Both c Q (f a)) : Both c Q (x >>= f) := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem Both.ok {α : Type} {c : Nat} {P : α → Prop} {a : α} (h : P a) :
    Both c P (Except.ok a : Except (EvmError × Devm) α) := h

theorem Both.pure {α : Type} {c : Nat} {P : α → Prop} {a : α} (h : P a) :
    Both c P (pure a : Except (EvmError × Devm) α) := h

theorem Both.error {α : Type} {c : Nat} {P : α → Prop} {e : EvmError} {d : Devm}
    (h : Inv c 0 d) : Both c P (Except.error (e, d) : Except (EvmError × Devm) α) := h

theorem Both.map {α β : Type} {c : Nat} {P : α → Prop} {Q : β → Prop}
    {x : Except (EvmError × Devm) α} {f : α → β}
    (hx : Both c P x) (hf : ∀ a, P a → Q (f a)) : Both c Q (f <$> x) := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem Both.mapRev {α β : Type} {c : Nat} {P : α → Prop} {Q : β → Prop}
    {x : Except (EvmError × Devm) α} {f : α → β}
    (hx : Both c P x) (hf : ∀ a, P a → Q (f a)) : Both c Q (x <&> f) :=
  Both.map hx hf

theorem Both.assert {c n : Nat} {p : Prop} [Decidable p] {e : EvmError} {d : Devm}
    (h : Inv c n d) : Both c (fun _ => True) (Except.assert p (e, d)) := by
  unfold Except.assert
  split
  · trivial
  · exact Inv.keep h rfl rfl (Nat.zero_le _)

theorem Both.ite {α : Type} {c : Nat} {P : α → Prop} {p : Prop} [Decidable p]
    {a b : Except (EvmError × Devm) α} (ha : p → Both c P a) (hb : ¬p → Both c P b) :
    Both c P (if p then a else b) := by
  by_cases h : p
  · simpa only [h, ite_true] using ha h
  · simpa only [h, ite_false] using hb h

theorem Both.dite {α : Type} {c : Nat} {P : α → Prop} {p : Prop} [Decidable p]
    {a : p → Except (EvmError × Devm) α} {b : ¬p → Except (EvmError × Devm) α}
    (ha : ∀ h, Both c P (a h)) (hb : ∀ h, Both c P (b h)) :
    Both c P (if h : p then a h else b h) := by
  by_cases h : p
  · simpa only [h, dite_true] using ha h
  · simpa only [h, dite_false] using hb h

/-! ## Machine cores -/

/-- The invariant on a core's outcome: `MInv c 0` on the machine an error carries, `MInv c k`
on a result's. -/
def OInv {α : Type} (c k : Nat) : Footprint.Outcome Mach α → Prop
  | .error (_, m') => MInv c 0 m'
  | .ok (_, m') => MInv c k m'

/-- A core keeps the invariant, turning room for `n` words into room for `f n`. -/
def CoreOk {α : Type} (core : Mach → Footprint.Outcome Mach α) (f : Nat → Nat) : Prop :=
  ∀ c n m, MInv c n m → OInv c (f n) (core m)

theorem liftMach_both {α : Type} {core : Mach → Footprint.Outcome Mach α} {f : Nat → Nat}
    (hc : CoreOk core f) {c n : Nat} {d : Devm} (h : Inv c n d) :
    Both c (fun a => Inv c (f n) a.2) (liftMach core d) := by
  have := hc c n d.mach h
  unfold liftMach Footprint.liftOutcome
  revert this
  cases core d.mach with
  | error e => exact id
  | ok a => exact id

theorem liftMachExecution_both {core : Mach → Footprint.Outcome Mach Unit} {f : Nat → Nat}
    (hc : CoreOk core f) {c n : Nat} {d : Devm} (h : Inv c n d) :
    Both c (Inv c (f n)) (liftMachExecution core d) := by
  have := liftMach_both hc h
  unfold liftMachExecution Footprint.toExecution
  revert this
  cases liftMach core d with
  | error _ => exact id
  | ok a => exact id

theorem MInv.weaken {c n k : Nat} {m : Mach} (h : MInv c n m) (hk : k ≤ n) : MInv c k m :=
  ⟨h.1, by have := h.2; omega⟩

theorem Mach.chargeGas_ok (cost : Nat) : CoreOk (Mach.chargeGas cost) id := by
  intro c n m h
  unfold Mach.chargeGas
  cases safeSub m.gasLeft cost with
  | none => exact h.weaken (Nat.zero_le _)
  | some g => exact h

theorem Mach.chargeStateGas_ok (amount : Nat) : CoreOk (Mach.chargeStateGas amount) id := by
  intro c n m h
  unfold Mach.chargeStateGas
  by_cases h1 : amount ≤ m.stateGas.left
  · simp only [h1, ↓reduceIte]; exact h
  · by_cases h2 : amount - m.stateGas.left ≤ m.gasLeft
    · simp only [h1, h2, ↓reduceIte]; exact h
    · simp only [h1, h2, ↓reduceIte]; exact h.weaken (Nat.zero_le _)

theorem Mach.push_ok (x : U256) : CoreOk (Mach.push x) (· - 1) := by
  intro c n m h
  unfold Mach.push
  by_cases hl : m.stack.length < 1024
  · simp only [hl, ↓reduceIte]
    exact ⟨h.1, by have := h.2; simp only [List.length_cons]; omega⟩
  · simp only [hl, ↓reduceIte]; exact h.weaken (Nat.zero_le _)

theorem Mach.pop_ok : CoreOk Mach.pop (· + 1) := by
  intro c n m h
  unfold Mach.pop
  rcases m with ⟨stack, memory, gasLeft, sg⟩
  cases stack with
  | nil => exact h.weaken (Nat.zero_le _)
  | cons x xs => exact ⟨h.1, by have := h.2; simp only [List.length_cons] at this ⊢; omega⟩

/-- Sequence a core after another: the first's error is kept, its result feeds the second. -/
theorem OInv.seq {α β : Type} {c k k' : Nat} {x : Footprint.Outcome Mach α}
    {g : α → Mach → Footprint.Outcome Mach β} (hx : OInv c k x)
    (hg : ∀ a m', MInv c k m' → OInv c k' (g a m')) :
    OInv c k' (match x with
      | .error err => .error err
      | .ok (a, m') => g a m') := by
  rcases x with ⟨e, m'⟩ | ⟨a, m'⟩
  · exact hx
  · exact hg a m' hx

theorem OInv.mapVal {α β : Type} {c k : Nat} {x : Footprint.Outcome Mach α} (f : α → β)
    (hx : OInv c k x) :
    OInv c k (match x with
      | .error err => .error err
      | .ok (a, m') => .ok (f a, m')) := by
  rcases x with ⟨e, m'⟩ | ⟨a, m'⟩
  · exact hx
  · exact hx

theorem Mach.popToNat_ok : CoreOk Mach.popToNat (· + 1) := by
  intro c n m h
  have h1 := Mach.pop_ok c n m h
  unfold Mach.popToNat
  rcases hp : m.pop with ⟨e, m'⟩ | ⟨a, m'⟩ <;> rw [hp] at h1 <;> exact h1

theorem Mach.popToAdr_ok : CoreOk Mach.popToAdr (· + 1) := by
  intro c n m h
  have h1 := Mach.pop_ok c n m h
  unfold Mach.popToAdr
  rcases hp : m.pop with ⟨e, m'⟩ | ⟨a, m'⟩ <;> rw [hp] at h1 <;> exact h1

theorem Mach.pushItem_ok (x : U256) (cost : Nat) : CoreOk (Mach.pushItem x cost) (· - 1) := by
  intro c n m h
  have h1 := Mach.chargeGas_ok cost c n m h
  unfold Mach.pushItem
  rcases hp : Mach.chargeGas cost m with ⟨e, m'⟩ | ⟨a, m'⟩ <;> rw [hp] at h1
  · exact h1
  · exact Mach.push_ok x c n m' h1

theorem Mach.applyUnary_ok (g : U256 → U256) (cost : Nat) :
    CoreOk (Mach.applyUnary g cost) id := by
  intro c n m h
  rcases m with ⟨stack, memory, gasLeft, sg⟩
  rcases stack with _ | ⟨x, rest⟩
  · exact h.weaken (Nat.zero_le _)
  · simp only [Mach.applyUnary, Mach.pop]
    have := Mach.pushItem_ok (g x) cost c (n + 1) ⟨rest, memory, gasLeft, sg⟩
      ⟨h.1, by have := h.2; simp only [List.length_cons] at this ⊢; omega⟩
    simpa using this

theorem Mach.applyBinary_ok (g : U256 → U256 → U256) (cost : Nat) :
    CoreOk (Mach.applyBinary g cost) id := by
  intro c n m h
  rcases m with ⟨stack, memory, gasLeft, sg⟩
  rcases stack with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · exact h.weaken (Nat.zero_le _)
  · exact ⟨h.1, by simp⟩
  · simp only [Mach.applyBinary, Mach.pop]
    have := Mach.pushItem_ok (g x y) cost c (n + 2) ⟨rest, memory, gasLeft, sg⟩
      ⟨h.1, by have := h.2; simp only [List.length_cons] at this ⊢; omega⟩
    revert this
    rcases Mach.pushItem (g x y) cost ⟨rest, memory, gasLeft, sg⟩ with ⟨e, m3⟩ | ⟨u, m3⟩
    · exact id
    · intro h3; exact h3.weaken (show n ≤ n + 2 - 1 by omega)

theorem Mach.applyTernary_ok (g : U256 → U256 → U256 → U256) (cost : Nat) :
    CoreOk (Mach.applyTernary g cost) id := by
  intro c n m h
  rcases m with ⟨stack, memory, gasLeft, sg⟩
  rcases stack with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · exact h.weaken (Nat.zero_le _)
  · exact ⟨h.1, by simp⟩
  · exact ⟨h.1, by simp⟩
  · simp only [Mach.applyTernary, Mach.pop]
    have := Mach.pushItem_ok (g x y z) cost c (n + 3) ⟨rest, memory, gasLeft, sg⟩
      ⟨h.1, by have := h.2; simp only [List.length_cons] at this ⊢; omega⟩
    revert this
    rcases Mach.pushItem (g x y z) cost ⟨rest, memory, gasLeft, sg⟩ with ⟨e, m3⟩ | ⟨u, m3⟩
    · exact id
    · intro h3; exact h3.weaken (show n ≤ n + 3 - 1 by omega)

theorem Mach.popN_ok (k : Nat) : CoreOk (Mach.popN · k) (· + k) := by
  induction k with
  | zero => intro c n m h; exact h
  | succ k ih =>
    intro c n m h
    have h1 := Mach.pop_ok c n m h
    simp only [Mach.popN]
    rcases hp : m.pop with ⟨e, m'⟩ | ⟨x, m'⟩ <;> rw [hp] at h1
    · exact h1
    · have h2 := ih c (n + 1) m' h1
      dsimp only at h2
      rcases hq : Mach.popN m' k with ⟨e, m''⟩ | ⟨xs, m''⟩ <;> rw [hq] at h2 <;>
        simp only [hq, OInv] at h2 ⊢
      · exact h2
      · exact ⟨h2.1, by have := h2.2; omega⟩

/-! ## Machine operations -/

theorem Inv.weaken {c n k : Nat} {d : Devm} (h : Inv c n d) (hk : k ≤ n) : Inv c k d :=
  Inv.keep h rfl rfl hk


/-- A result with room for `n` words has room for any `k ≤ n`. -/
theorem Both.weaken {c n k : Nat} {x : Execution} (hx : Both c (Inv c n) x) (hk : k ≤ n) :
    Both c (Inv c k) x := by
  cases x with
  | error e => exact hx
  | ok d => exact Inv.weaken hx hk


theorem chargeGas_both (cost : Nat) {c n k : Nat} {d : Devm} (h : Inv c n d)
    (hk : k ≤ n) : Both c (Inv c k) (chargeGas cost d) :=
  Both.weaken (liftMachExecution_both (Mach.chargeGas_ok cost) h) hk

theorem chargeStateGas_both (amount : Nat) {c n k : Nat} {d : Devm} (h : Inv c n d)
    (hk : k ≤ n) : Both c (Inv c k) (chargeStateGas amount d) :=
  Both.weaken (liftMachExecution_both (Mach.chargeStateGas_ok amount) h) hk

theorem Devm.push_both (x : U256) {c n k : Nat} {d : Devm} (h : Inv c n d)
    (hk : k ≤ n - 1) : Both c (Inv c k) (d.push x) :=
  Both.weaken (liftMachExecution_both (Mach.push_ok x) h) hk

theorem Devm.pop_both {c n : Nat} {d : Devm} (h : Inv c n d) :
    Both c (fun a => Inv c (n + 1) a.2) d.pop := liftMach_both Mach.pop_ok h

theorem Devm.popToNat_both {c n : Nat} {d : Devm} (h : Inv c n d) :
    Both c (fun a => Inv c (n + 1) a.2) d.popToNat := liftMach_both Mach.popToNat_ok h

theorem Devm.popToAdr_both {c n : Nat} {d : Devm} (h : Inv c n d) :
    Both c (fun a => Inv c (n + 1) a.2) d.popToAdr := liftMach_both Mach.popToAdr_ok h

theorem Devm.popN_both (k : Nat) {c n : Nat} {d : Devm} (h : Inv c n d) :
    Both c (fun a => Inv c (n + k) a.2) (d.popN k) := liftMach_both (Mach.popN_ok k) h

theorem pushItem_both (x : U256) (cost : Nat) {c n k : Nat} {d : Devm} (h : Inv c n d)
    (hk : k ≤ n - 1) : Both c (Inv c k) (pushItem x cost d) :=
  Both.weaken (liftMachExecution_both (Mach.pushItem_ok x cost) h) hk

theorem applyUnary_both (g : U256 → U256) (cost : Nat) {c n k : Nat} {d : Devm} (h : Inv c n d)
    (hk : k ≤ n) : Both c (Inv c k) (applyUnary g cost d) :=
  Both.weaken (liftMachExecution_both (Mach.applyUnary_ok g cost) h) hk

theorem applyBinary_both (g : U256 → U256 → U256) (cost : Nat) {c n k : Nat} {d : Devm} (h : Inv c n d)
    (hk : k ≤ n) : Both c (Inv c k) (applyBinary g cost d) :=
  Both.weaken (liftMachExecution_both (Mach.applyBinary_ok g cost) h) hk

theorem applyTernary_both (g : U256 → U256 → U256 → U256) (cost : Nat) {c n k : Nat} {d : Devm} (h : Inv c n d)
    (hk : k ≤ n) : Both c (Inv c k) (applyTernary g cost d) :=
  Both.weaken (liftMachExecution_both (Mach.applyTernary_ok g cost) h) hk

theorem assertDynamic_both (sevm : Sevm) {c n : Nat} {d : Devm} (h : Inv c n d) :
    Both c (fun _ => True) (assertDynamic sevm d) := Both.assert h

theorem Devm.subBal_both (x : EvmError × Devm) {c n : Nat} {d : Devm}
    (hx : Inv c 0 x.2) (h : Inv c n d) (a : Address) (v : U256) :
    Both c (Inv c n) (Option.toExcept x (d.subBal a v) : Except (EvmError × Devm) Devm) := by
  unfold Devm.subBal
  cases d.state.subBal a v with
  | none => exact hx
  | some st => exact Inv.keep h rfl rfl (Nat.le_refl _)

theorem Inv.memRead {c n : Nat} {d : Devm} (h : Inv c n d) (i size : Nat) :
    Inv c n (d.memRead i size).2 := by
  unfold Devm.memRead
  exact Inv.keep h rfl rfl (Nat.le_refl _)



theorem Inv.withStack {c n : Nat} {d : Devm} {l : List U256} (h : Inv c n d)
    (hl : l.length = d.stack.length) : Inv c n (d.withStack l) :=
  ⟨h.1, by have := h.2; show l.length + n ≤ 1024; simp only [Devm.stack] at hl; omega⟩

theorem OInv.of_eq {α : Type} {c k : Nat} {x y : Footprint.Outcome Mach α} (hx : OInv c k x)
    (h : x = y) : OInv c k y := h ▸ hx

/-- The invariant on a machine-and-substate core's outcome. -/
def OInv2 {α : Type} (c k : Nat) : Footprint.Outcome (Mach × Meta) α → Prop
  | .error (_, v) => MInv c 0 v.1
  | .ok (_, v) => MInv c k v.1

theorem liftMachMetaExecution_both {core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit}
    {c n : Nat} {d : Devm} (hc : OInv2 c n (core d.mach d.meta)) :
    Both c (Inv c n) (liftMachMetaExecution core d) := by
  unfold liftMachMetaExecution Footprint.toExecution liftMachMeta Footprint.liftOutcome
  dsimp only
  revert hc
  cases core d.mach d.meta with
  | error e => exact id
  | ok a => exact id

theorem PlainOp.balance_both (rules : ForkRules) {c n : Nat} {d : Devm} (h : Inv c n d) :
    Both c (Inv c n) (liftMachMetaWorldExecution (PlainOp.balanceCore rules) d) := by
  apply liftMachMetaExecution_both
  obtain ⟨h1, h2⟩ := h
  generalize d.mach = m at h1 h2 ⊢
  rcases m with ⟨stack, memory, gasLeft, sg⟩
  simp only at h1 h2
  cases stack with
  | nil => simp [PlainOp.balanceCore, Mach.pop, OInv2, MInv, h1]
  | cons x xs =>
    have hm : MInv c (n + 1) ⟨xs, memory, gasLeft, sg⟩ :=
      ⟨h1, by simp only [List.length_cons] at h2 ⊢; omega⟩
    simp only [PlainOp.balanceCore, Mach.pop]
    split
    · rename_i e m' heq
      exact OInv.of_eq (Mach.chargeGas_ok _ c (n + 1) _ hm) heq
    · rename_i u m' heq
      have h3 : MInv c (n + 1) m' := OInv.of_eq (Mach.chargeGas_ok _ c (n + 1) _ hm) heq
      split
      · rename_i e m'' heq2
        exact OInv.of_eq (Mach.push_ok _ c (n + 1) _ h3) heq2
      · rename_i u m'' heq2
        exact (OInv.of_eq (Mach.push_ok _ c (n + 1) _ h3) heq2 : MInv c n m'')

theorem Both.bind_ok {α β : Type} {c : Nat} {Q : β → Prop} {v : α}
    {f : α → Except (EvmError × Devm) β} (h : Both c Q (f v)) :
    Both c Q (Except.ok v >>= f) := h

theorem Both.bind_pure {α β : Type} {c : Nat} {Q : β → Prop} {v : α}
    {f : α → Except (EvmError × Devm) β} (h : Both c Q (f v)) :
    Both c Q (Pure.pure v >>= f) := h

/-- Setters of the substate and the world leave the machine alone. -/
theorem creditSelfdestructRefund_mach (rules : ForkRules) (p : Prop) [Decidable p] (d : Devm) :
    (creditSelfdestructRefund rules p d).mach = d.mach := by
  unfold creditSelfdestructRefund; split <;> rfl

theorem addAccountToDelete_mach (d : Devm) (a : Address) : (addAccountToDelete d a).mach = d.mach := by
  unfold addAccountToDelete; first | rfl | (split <;> rfl)

theorem Devm.creditBeneficiary_mach (rules : ForkRules) (a : Address) (v : U256) (d : Devm) :
    (Devm.creditBeneficiary rules a v d).mach = d.mach := by
  unfold Devm.creditBeneficiary; first | rfl | (split <;> rfl) | (repeat' split) <;> rfl

theorem Devm.emitTransferLog_mach (d : Devm) (a b : Address) (v : U256) :
    (d.emitTransferLog a b v).mach = d.mach := by
  unfold Devm.emitTransferLog; first | rfl | (split <;> rfl) | (repeat' split) <;> rfl

theorem Devm.setBal_mach (d : Devm) (a : Address) (v : U256) : (d.setBal a v).mach = d.mach := by
  unfold Devm.setBal; first | rfl | (split <;> rfl)

theorem addAccessedAddress_mach (d : Devm) (a : Address) :
    (addAccessedAddress d a).mach = d.mach := by
  unfold addAccessedAddress; first | rfl | (split <;> rfl)

theorem Devm.incrNonce_mach (d : Devm) (a : Address) : (d.incrNonce a).mach = d.mach := by
  unfold Devm.incrNonce; first | rfl | (split <;> rfl)

/-- `Inv` through the setters above. -/
theorem Inv.of_mach {c n k : Nat} {d d' : Devm} (h : Inv c n d) (hm : d'.mach = d.mach)
    (hk : k ≤ n) : Inv c k d' := by
  unfold Inv at *; rw [hm]; exact ⟨h.1, by have := h.2; omega⟩

/-! ## The walk -/

open Lean Elab Tactic Meta in
/-- Close `Inv c k d'` from a hypothesis `Inv c n d` where `d'` keeps `d`'s meter and stack
definitionally and `k ≤ n`. -/
elab "inv_close_core" : tactic => withMainContext do
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    unless ty.isAppOf ``Inv do continue
    let h ← Term.exprToSyntax (mkFVar decl.fvarId)
    let s ← saveState
    let ok ← (do
        evalTactic (← `(tactic| exact Inv.keep $h rfl rfl (by first | exact Nat.le_refl _ | omega)))
        pure true) <|> (do s.restore; pure false)
    if ok then return
    let ok2 ← (focusAndDone do
        evalTactic (← `(tactic| refine Inv.of_mach $h ?_ ?_))
        evalTactic (← `(tactic| simp only [creditSelfdestructRefund_mach, addAccountToDelete_mach,
          Devm.creditBeneficiary_mach, Devm.emitTransferLog_mach, Devm.setBal_mach,
          addAccessedAddress_mach, Devm.incrNonce_mach]))
        evalTactic (← `(tactic| all_goals first | rfl | exact Nat.le_refl _ | omega))
        pure true) <|>
      (do s.restore; pure false)
    if ok2 then return
  throwError "inv_close: no hypothesis closes the goal"

/-- `inv_close_core`, also through a memory read. -/
syntax "inv_close" : tactic

macro_rules
  | `(tactic| inv_close) => `(tactic| first
  | (split <;> inv_close)
  | inv_close_core
  | (apply Inv.memRead; inv_close_core))

/-- A machine operation, its machine argument closed from a hypothesis. -/
syntax "inv_prim" : tactic

macro_rules
  | `(tactic| inv_prim) => `(tactic| first
  | (with_reducible apply chargeGas_both <;> first | inv_close | exact Nat.le_refl _ | omega)
  | (with_reducible apply chargeStateGas_both <;> first | inv_close | exact Nat.le_refl _ | omega)
  | (with_reducible apply Devm.push_both <;> first | inv_close | exact Nat.le_refl _ | omega)
  | (with_reducible apply Devm.pop_both; inv_close)
  | (with_reducible apply Devm.popToNat_both; inv_close)
  | (with_reducible apply Devm.popToAdr_both; inv_close)
  | (with_reducible apply Devm.popN_both; inv_close)
  | (with_reducible apply pushItem_both <;> first | inv_close | exact Nat.le_refl _ | omega)
  | (with_reducible apply applyUnary_both <;> first | inv_close | exact Nat.le_refl _ | omega)
  | (with_reducible apply applyBinary_both <;> first | inv_close | exact Nat.le_refl _ | omega)
  | (with_reducible apply applyTernary_both <;> first | inv_close | exact Nat.le_refl _ | omega)
  | (with_reducible apply assertDynamic_both; inv_close)
  | (with_reducible apply Both.assert; inv_close)
  | (with_reducible apply Devm.subBal_both <;> inv_close)
  | (with_reducible apply PlainOp.balance_both; inv_close)
  | (with_reducible apply Inv.withStack <;> first | inv_close | (apply List.swap_length; assumption) | (apply List.exchange_length; assumption)))

/-- One step of the walk. -/
syntax "inv_step" : tactic

macro_rules
  | `(tactic| inv_step) => `(tactic| first
  | with_reducible intro _
  | exact True.intro
  | (with_reducible refine Both.ok ?_)
  | (with_reducible refine Both.pure ?_)
  | (with_reducible refine Both.error ?_; inv_close)
  | (with_reducible refine Both.bind_ok ?_; beta_reduce)
  | (with_reducible refine Both.bind_pure ?_; beta_reduce)
  | with_reducible apply Both.bind
  | with_reducible apply Both.mapRev
  | with_reducible apply Both.map
  | with_reducible refine Both.ite ?_ ?_
  | with_reducible refine Both.dite ?_ ?_
  | inv_prim
  | inv_close
  | (simp only []; done)
  | split
  | (dsimp only; fail_if_success done))

/-- Repeat `inv_step` on every goal. -/
macro "inv_walk" : tactic => `(tactic| repeat' inv_step)

/-! ## Every instruction -/

theorem PlainOp.runCore_inv_add (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .add) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_mul (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .mul) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_sub (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .sub) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_div (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .div) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_sdiv (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .sdiv) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_mod (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .mod) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_smod (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .smod) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_addmod (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .addmod) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_mulmod (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .mulmod) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_exp (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .exp) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_signextend (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .signextend) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_lt (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .lt) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_gt (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .gt) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_slt (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .slt) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_sgt (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .sgt) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_eq (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .eq) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_iszero (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .iszero) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_and (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .and) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_or (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .or) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_xor (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .xor) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_not (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .not) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_byte (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .byte) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_shl (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .shl) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_shr (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .shr) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_sar (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .sar) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_clz (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .clz) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_keccak256 (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .keccak256) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_address (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .address) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_balance (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .balance) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_origin (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .origin) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_caller (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .caller) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_callvalue (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .callvalue) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_calldataload (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .calldataload) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_calldatasize (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .calldatasize) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_calldatacopy (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .calldatacopy) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_codesize (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .codesize) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_codecopy (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .codecopy) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_gasprice (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .gasprice) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_extcodesize (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .extcodesize) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_extcodecopy (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .extcodecopy) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_returndatasize (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .returndatasize) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_returndatacopy (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .returndatacopy) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_extcodehash (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .extcodehash) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_blockhash (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .blockhash) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_coinbase (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .coinbase) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_timestamp (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .timestamp) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_number (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .number) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_prevrandao (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .prevrandao) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_gaslimit (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .gaslimit) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_chainid (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .chainid) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_selfbalance (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .selfbalance) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_basefee (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .basefee) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_blobhash (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .blobhash) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_blobbasefee (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .blobbasefee) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_slotnum (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .slotnum) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_pop (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .pop) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_mload (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .mload) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_mstore (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .mstore) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_mstore8 (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .mstore8) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_sload (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .sload) := by
  simp only [PlainOp.runCore]; inv_walk

set_option maxHeartbeats 8000000 in
theorem PlainOp.runCore_inv_sstore (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .sstore) := by
  simp only [PlainOp.runCore]
  split
  · split
    · inv_walk
    · inv_walk
  · inv_walk

theorem PlainOp.runCore_inv_tload (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .tload) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_tstore (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .tstore) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_mcopy (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .mcopy) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_pc (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .pc) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_msize (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .msize) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_gas (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm .gas) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_dup (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) (k) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm (.dup k)) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_swap (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) (k) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm (.swap k)) := by
  simp only [PlainOp.runCore]; inv_walk

theorem PlainOp.runCore_inv_log (pc : Nat) (devm : Devm) (sevm : Sevm) {c : Nat}
    (h : Inv c 0 devm) (k) : Both c (Inv c 0) (PlainOp.runCore pc devm sevm (.log k)) := by
  simp only [PlainOp.runCore]; inv_walk

/-- Every register instruction keeps the invariant. -/
theorem PlainOp.run_inv (evm : Evm) {c : Nat} (h : Inv c 0 evm.dyna) (r : PlainOp) :
    Both c (Inv c 0) (r.run evm) := by
  unfold PlainOp.run
  cases r with
  | add => exact PlainOp.runCore_inv_add _ _ _ h
  | mul => exact PlainOp.runCore_inv_mul _ _ _ h
  | sub => exact PlainOp.runCore_inv_sub _ _ _ h
  | div => exact PlainOp.runCore_inv_div _ _ _ h
  | sdiv => exact PlainOp.runCore_inv_sdiv _ _ _ h
  | mod => exact PlainOp.runCore_inv_mod _ _ _ h
  | smod => exact PlainOp.runCore_inv_smod _ _ _ h
  | addmod => exact PlainOp.runCore_inv_addmod _ _ _ h
  | mulmod => exact PlainOp.runCore_inv_mulmod _ _ _ h
  | exp => exact PlainOp.runCore_inv_exp _ _ _ h
  | signextend => exact PlainOp.runCore_inv_signextend _ _ _ h
  | lt => exact PlainOp.runCore_inv_lt _ _ _ h
  | gt => exact PlainOp.runCore_inv_gt _ _ _ h
  | slt => exact PlainOp.runCore_inv_slt _ _ _ h
  | sgt => exact PlainOp.runCore_inv_sgt _ _ _ h
  | eq => exact PlainOp.runCore_inv_eq _ _ _ h
  | iszero => exact PlainOp.runCore_inv_iszero _ _ _ h
  | and => exact PlainOp.runCore_inv_and _ _ _ h
  | or => exact PlainOp.runCore_inv_or _ _ _ h
  | xor => exact PlainOp.runCore_inv_xor _ _ _ h
  | not => exact PlainOp.runCore_inv_not _ _ _ h
  | byte => exact PlainOp.runCore_inv_byte _ _ _ h
  | shl => exact PlainOp.runCore_inv_shl _ _ _ h
  | shr => exact PlainOp.runCore_inv_shr _ _ _ h
  | sar => exact PlainOp.runCore_inv_sar _ _ _ h
  | clz => exact PlainOp.runCore_inv_clz _ _ _ h
  | keccak256 => exact PlainOp.runCore_inv_keccak256 _ _ _ h
  | address => exact PlainOp.runCore_inv_address _ _ _ h
  | balance => exact PlainOp.runCore_inv_balance _ _ _ h
  | origin => exact PlainOp.runCore_inv_origin _ _ _ h
  | caller => exact PlainOp.runCore_inv_caller _ _ _ h
  | callvalue => exact PlainOp.runCore_inv_callvalue _ _ _ h
  | calldataload => exact PlainOp.runCore_inv_calldataload _ _ _ h
  | calldatasize => exact PlainOp.runCore_inv_calldatasize _ _ _ h
  | calldatacopy => exact PlainOp.runCore_inv_calldatacopy _ _ _ h
  | codesize => exact PlainOp.runCore_inv_codesize _ _ _ h
  | codecopy => exact PlainOp.runCore_inv_codecopy _ _ _ h
  | gasprice => exact PlainOp.runCore_inv_gasprice _ _ _ h
  | extcodesize => exact PlainOp.runCore_inv_extcodesize _ _ _ h
  | extcodecopy => exact PlainOp.runCore_inv_extcodecopy _ _ _ h
  | returndatasize => exact PlainOp.runCore_inv_returndatasize _ _ _ h
  | returndatacopy => exact PlainOp.runCore_inv_returndatacopy _ _ _ h
  | extcodehash => exact PlainOp.runCore_inv_extcodehash _ _ _ h
  | blockhash => exact PlainOp.runCore_inv_blockhash _ _ _ h
  | coinbase => exact PlainOp.runCore_inv_coinbase _ _ _ h
  | timestamp => exact PlainOp.runCore_inv_timestamp _ _ _ h
  | number => exact PlainOp.runCore_inv_number _ _ _ h
  | prevrandao => exact PlainOp.runCore_inv_prevrandao _ _ _ h
  | gaslimit => exact PlainOp.runCore_inv_gaslimit _ _ _ h
  | chainid => exact PlainOp.runCore_inv_chainid _ _ _ h
  | selfbalance => exact PlainOp.runCore_inv_selfbalance _ _ _ h
  | basefee => exact PlainOp.runCore_inv_basefee _ _ _ h
  | blobhash => exact PlainOp.runCore_inv_blobhash _ _ _ h
  | blobbasefee => exact PlainOp.runCore_inv_blobbasefee _ _ _ h
  | slotnum => exact PlainOp.runCore_inv_slotnum _ _ _ h
  | pop => exact PlainOp.runCore_inv_pop _ _ _ h
  | mload => exact PlainOp.runCore_inv_mload _ _ _ h
  | mstore => exact PlainOp.runCore_inv_mstore _ _ _ h
  | mstore8 => exact PlainOp.runCore_inv_mstore8 _ _ _ h
  | sload => exact PlainOp.runCore_inv_sload _ _ _ h
  | sstore => exact PlainOp.runCore_inv_sstore _ _ _ h
  | tload => exact PlainOp.runCore_inv_tload _ _ _ h
  | tstore => exact PlainOp.runCore_inv_tstore _ _ _ h
  | mcopy => exact PlainOp.runCore_inv_mcopy _ _ _ h
  | pc => exact PlainOp.runCore_inv_pc _ _ _ h
  | msize => exact PlainOp.runCore_inv_msize _ _ _ h
  | gas => exact PlainOp.runCore_inv_gas _ _ _ h
  | dup k => exact PlainOp.runCore_inv_dup _ _ _ h k
  | swap k => exact PlainOp.runCore_inv_swap _ _ _ h k
  | log k => exact PlainOp.runCore_inv_log _ _ _ h k


theorem JumpOp.run_inv (evm : Evm) {c : Nat} (h : Inv c 0 evm.dyna) (j : JumpOp) :
    Both c (fun a => Inv c 0 a.2) (j.run evm) := by
  unfold JumpOp.run
  cases j <;> simp only [JumpOp.runCore] <;> inv_walk

set_option maxHeartbeats 4000000 in
theorem HaltOp.run_inv_selfdestruct (sevm : Sevm) (devm : Devm) {c : Nat} (h : Inv c 0 devm) :
    Both c (Inv c 0) (HaltOp.run sevm devm .selfdestruct) := by
  simp only [HaltOp.run]; inv_walk

theorem HaltOp.run_inv (sevm : Sevm) (devm : Devm) {c : Nat} (h : Inv c 0 devm) (l : HaltOp) :
    Both c (Inv c 0) (l.run sevm devm) := by
  cases l
  case selfdestruct => exact HaltOp.run_inv_selfdestruct sevm devm h
  all_goals simp only [HaltOp.run]; inv_walk

/-! ## Message opcodes -/

/-- A message opcode's outcome keeps the invariant: a result in place on both channels; a spawn's
saved caller with room for one more word, its child running under the spawning rules. -/
def OutcomeInv (rules : ForkRules) (c : Nat) : MessageOp.Outcome → Prop
  | .done ex => Both c (Inv c 0) ex
  | .spawn child _ =>
    Inv c 1 child.checkpoint.toDevm ∧ child.message.context.block.rules = rules

theorem OutcomeInv.ofExcept {rules : ForkRules} {c : Nat}
    {x : Except (EvmError × Devm) MessageOp.Outcome} (h : Both c (OutcomeInv rules c) x) :
    OutcomeInv rules c (MessageOp.Outcome.ofExcept x) := by
  cases x with
  | error e => exact h
  | ok o => exact h

theorem OutcomeInv.done {rules : ForkRules} {c : Nat} {ex : Execution} (h : Both c (Inv c 0) ex) :
    OutcomeInv rules c (.done ex) := h

theorem OutcomeInv.spawn {rules : ForkRules} {c : Nat} {m : Message} {d : Devm} {p : Pending}
    (h : Inv c 1 d) (hr : m.context.block.rules = rules) :
    OutcomeInv rules c (.spawn ⟨m, Frame.State.ofDevm d⟩ p) :=
  ⟨Inv.keep h rfl rfl (Nat.le_refl _), hr⟩

macro_rules
  | `(tactic| inv_step) => `(tactic| first
  | with_reducible apply OutcomeInv.ofExcept
  | with_reducible apply OutcomeInv.done
  | (with_reducible apply OutcomeInv.spawn <;> first | inv_close | rfl))

theorem genericCreate.step_inv (sevm : Sevm) (devm : Devm) {c : Nat} (h : Inv c 1 devm)
    (endowment : U256) (newAddress : Address) (memoryIndex memorySize : Nat) :
    OutcomeInv sevm.benvStat.rules c
      (genericCreate.step sevm devm endowment newAddress memoryIndex memorySize) := by
  unfold genericCreate.step; inv_walk
  all_goals (apply OutcomeInv.spawn <;> first | inv_close | rfl)

theorem genericCall.step_inv (sevm : Sevm) (devm : Devm) {c : Nat} (h : Inv c 1 devm)
    (gas : Nat) (value : U256) (caller target codeAddress : Address)
    (shouldTransferValue isStaticcall : Bool) (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) :
    OutcomeInv sevm.benvStat.rules c
      (genericCall.step sevm devm gas value caller target codeAddress shouldTransferValue
        isStaticcall inputIndex inputSize outputIndex outputSize code disablePrecompiles) := by
  unfold genericCall.step; inv_walk
  all_goals (apply OutcomeInv.spawn <;> first | inv_close | rfl)

theorem genericCallAmsterdam.step_inv (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    {c : Nat} (h : Inv c 1 devm) (gas reservoir : Nat) (value : U256)
    (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat) (code : ByteArray)
    (disablePrecompiles newAccountCharged insufficientBalance : Bool) :
    OutcomeInv sevm.benvStat.rules c
      (genericCallAmsterdam.step sevm state devm gas reservoir value caller target codeAddress
        shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize code
        disablePrecompiles newAccountCharged insufficientBalance) := by
  unfold genericCallAmsterdam.step; inv_walk
  all_goals (apply OutcomeInv.spawn <;> first | inv_close | rfl)

theorem genericCreateAmsterdam.step_inv (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    {c : Nat} (h : Inv c 1 devm) (endowment : U256) (newAddress : Address)
    (memoryIndex memorySize : Nat) :
    OutcomeInv sevm.benvStat.rules c
      (genericCreateAmsterdam.step sevm state devm endowment newAddress memoryIndex
        memorySize) := by
  unfold genericCreateAmsterdam.step; inv_walk
  all_goals (apply OutcomeInv.spawn <;> first | inv_close | rfl)

end RunInvariants

end Jaune
