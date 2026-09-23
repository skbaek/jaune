import Jaune.Exec

/-!
Induction and subderivation order for the canonical complete execution tree.
Both child and resumed-parent recursive premises remain explicit. The strict
order points from a proper subderivation to its enclosing derivation.
-/

namespace Blanc

open Jaune

abbrev Exec.Pred : Type :=
  ∀ pc sevm devm exc, Exec pc sevm devm exc → Prop

def Exec.Fa (π : Exec.Pred) : Prop :=
  ∀ e s pc r (ex : Exec e s pc r), π _ _ _ _ ex

def Fortify (π : Exec.Pred) : Exec.Pred :=
  λ _ sevm _ _ exn =>
    (Exec.Fa <| λ _ sevm' _ _ exn' => sevm'.depth < sevm.depth → π _ _ _ _ exn') → π _ _ _ _ exn

lemma Exec.strong_rec (π : Exec.Pred)
  (h_fa : Exec.Fa (Fortify π)) : Exec.Fa π := by
  intros pc sevm devm exn exc
  apply
    @Nat.strongRecOn
      (λ n => ∀ pc_ sevm_ devm_ exn_ (exc_ : Exec pc_ sevm_ devm_ exn_), n = sevm_.depth → π _ _ _ _ exc_)
      sevm.depth
  · intros n h pc_ sevm_ devm_ exn_ exc_ h_eq; apply h_fa
    intros pc' sevm' devm' exn' exc' h_lt; rw [← h_eq] at h_lt
    apply h sevm'.depth h_lt _ _ _ _ exc' rfl
  · rfl

-- alternative version of Exec which rolls all arguments into a structure.

structure Exec.Deriv : Type where
  (pc : Nat)
  (sevm : Sevm)
  (devm : Devm)
  (exn : Execution)
  (exc : Exec pc sevm devm exn)

/-- The immediate sub-derivation relation.  One constructor per recursive
premise of `Exec`: the same-frame continuation (`cont`, `doneOk`), the child
derivation of a spawn (`runErrChild`, `runOkChild`), and the parent's
continuation after a spawn returns (`runOkCont`). -/
inductive Exec.Deriv.Prec : Exec.Deriv → Exec.Deriv → Prop
  | cont {pc : Nat} {sevm : Sevm} {devm : Devm} {pc' : Nat}
    {devm' : Devm} {exn : Execution}
    (hstep : Evm.step ⟨pc, sevm, devm⟩ = .cont pc' devm')
    (exc : Exec pc' sevm devm' exn) :
    Exec.Deriv.Prec
      ⟨pc', sevm, devm', exn, exc⟩
      ⟨pc, sevm, devm, exn, .cont hstep exc⟩
  | doneOk {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {r} {devm' : Devm} {exn : Execution}
    (hstep : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (henter : f.enter = .done r)
    (hr : rsm.run r = .ok devm')
    (exc : Exec pc' sevm devm' exn) :
    Exec.Deriv.Prec
      ⟨pc', sevm, devm', exn, exc⟩
      ⟨pc, sevm, devm, exn, .doneOk hstep henter hr exc⟩
  | runErrChild {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm} {raw : Execution} {e}
    (hstep : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (excChild : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .error e) :
    Exec.Deriv.Prec
      ⟨cevm.pc, cevm.sta, cevm.dyna, raw, excChild⟩
      ⟨pc, sevm, devm, .error e, .runErr hstep henter excChild hr⟩
  | runOkChild {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm} {raw : Execution}
    {devm' : Devm} {exn : Execution}
    (hstep : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (excChild : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (exc : Exec pc' sevm devm' exn) :
    Exec.Deriv.Prec
      ⟨cevm.pc, cevm.sta, cevm.dyna, raw, excChild⟩
      ⟨pc, sevm, devm, exn, .runOk hstep henter excChild hr exc⟩
  | runOkCont {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm} {raw : Execution}
    {devm' : Devm} {exn : Execution}
    (hstep : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (excChild : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (exc : Exec pc' sevm devm' exn) :
    Exec.Deriv.Prec
      ⟨pc', sevm, devm', exn, exc⟩
      ⟨pc, sevm, devm, exn, .runOk hstep henter excChild hr exc⟩

infix:70 " ≺ " => Exec.Deriv.Prec

inductive Exec.Deriv.le : Exec.Deriv → Exec.Deriv → Prop
  | refl : ∀ p, Exec.Deriv.le p p
  | step : ∀ {p p' p''}, Exec.Deriv.le p p' → p' ≺ p'' → Exec.Deriv.le p p''

def Exec.Deriv.lt (pk pk'' : Exec.Deriv) : Prop :=
  ∃ pk' : Exec.Deriv, Exec.Deriv.le pk pk' ∧ Exec.Deriv.Prec pk' pk''

lemma Exec.Deriv.lt_of_prec {pk pk' : Exec.Deriv} (h : pk ≺ pk') : lt pk pk' :=
  ⟨pk, .refl _, h⟩

abbrev Exec.Deriv.gt (pk pk' : Exec.Deriv) : Prop := Exec.Deriv.lt pk' pk

lemma Exec.Deriv.eq_or_lt_of_le :
  ∀ {p p'}, Exec.Deriv.le p p' → p = p' ∨ Exec.Deriv.lt p p' := by
  intros p p'' h0; rcases h0 with _ | ⟨le, prec⟩
  · left; rfl
  · right; refine ⟨_, le, prec⟩

lemma Exec.Deriv.acc_of_le {pk pk' : Exec.Deriv}
    (h_le : Exec.Deriv.le pk pk') (h_acc : Acc Exec.Deriv.lt pk') : Acc Exec.Deriv.lt pk := by
  cases Exec.Deriv.eq_or_lt_of_le h_le with
  | inl h => rw [h]; exact h_acc
  | inr h => exact Acc.inv h_acc h

theorem Exec.Deriv.lt.well_founded : WellFounded Exec.Deriv.lt := by
  constructor;
  intro pk; rcases pk with ⟨_, _, _, _, _⟩
  apply
    @Exec.rec
      (λ pc sevm devm exn exc => Acc Exec.Deriv.lt ⟨pc, sevm, devm, exn, exc⟩) <;>
    clear *-
  -- halt : no sub-derivation
  · intro _ _ _ _ _; constructor
    intro _ lt; rcases lt with ⟨_, _, ⟨_⟩⟩
  -- cont : the same-frame continuation
  · intro _ _ _ _ _ _ _ _ ih
    constructor; intro _ lt
    rcases lt with ⟨_, le, prec⟩
    cases prec; exact acc_of_le le ih
  -- doneErr : no sub-derivation
  · intro _ _ _ _ _ _ _ _ _ _ _; constructor
    intro _ lt; rcases lt with ⟨_, _, ⟨_⟩⟩
  -- doneOk : the same-frame continuation
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih
    constructor; intro _ lt
    rcases lt with ⟨_, le, prec⟩
    cases prec; exact acc_of_le le ih
  -- runErr : the child derivation only
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ihc
    constructor; intro _ lt
    rcases lt with ⟨_, le, prec⟩
    cases prec; exact acc_of_le le ihc
  -- runOk : the child derivation and the parent's continuation
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihc ih
    constructor; intro _ lt
    rcases lt with ⟨_, le, prec⟩
    cases prec
    · exact acc_of_le le ihc
    · exact acc_of_le le ih

abbrev Exec.Deriv.Pred : Type := Exec.Deriv → Prop

def Exec.Deriv.imp (π π' : Exec.Deriv.Pred) : Exec.Deriv.Pred := λ pk => π pk → π' pk

infix:70 " →p " => Exec.Deriv.imp

def Exec.Deriv.Fa (π : Exec.Deriv.Pred) : Prop := ∀ pk, π pk

notation "□p" => Exec.Deriv.Fa

def carryover (π : Exec.Deriv.Pred) : Exec.Deriv.Pred :=
(λ pk => □p (Exec.Deriv.gt pk →p π)) →p π

theorem Exec.Deriv.strongRec (π : Exec.Deriv.Pred) : □p (carryover π) → □p π := by
  intro ih pk
  apply @WellFounded.induction _ Exec.Deriv.lt Exec.Deriv.lt.well_founded π pk
  clear pk; intro pk ih'
  apply ih
  intro pk' h_gt
  apply ih' _ h_gt


end Blanc
