-- Fuel.lean : the carrier of the fuel-bounded driver and its helpers.
--
-- `execFueled` (`Jaune/Execution.lean`) is structurally recursive on a fuel
-- parameter and so reports exhaustion as an outcome; `Jaune/Sufficiency.lean`
-- proves that fuel seeded by `sufficientFuel` always suffices and wraps the
-- driver as the total `exec`. Nothing a reader of `API.md` is pointed to states
-- fuel: the carrier, its helpers and the residue lemmas the adequacy bridge
-- needs live here, and nowhere else.
--
-- Relocated unchanged from `Jaune/Machine.lean` (the carrier and helpers),
-- `Jaune/Exec.lean` (the residue lemmas) and `Jaune/Sufficiency.lean`
-- (`sufficientFuel`), goal `jaune-shape-and-names-v1`, unit W0.
import Mathlib.Tactic.Lemma

namespace Jaune

section FuelCarrier

open Jaune _root_.Nat

/-- A fuel-bounded computation.  The outer `Option` records whether the
computation exhausted its recursion fuel; the inner `Except` is the ordinary
semantic result. -/
abbrev Fueled (ε α : Type) : Type := ExceptT ε Option α

namespace Fueled

/-- The distinguished result for recursion-fuel exhaustion. -/
def exhausted : Fueled ε α := ExceptT.mk none

/-- Lift an ordinary semantic result into a completed fueled computation. -/
def ofExcept (x : Except ε α) : Fueled ε α := liftM x

/-- A completed successful computation. -/
def ok (x : α) : Fueled ε α := pure x

/-- A completed computation that produced an ordinary semantic error. -/
def error (e : ε) : Fueled ε α := throw e

/-- The fueled analogue of `Except.assert`; failure is a semantic error, not
fuel exhaustion. -/
def assert (p : Prop) [Decidable p] (e : ε) : Fueled ε Unit :=
  if p then pure () else throw e

/-- Apply a transformation to a completed semantic result while propagating
fuel exhaustion unchanged.  This is used where the old interpreter converted
between its two semantic error-state types. -/
def mapResult (f : Except ε α → Except ζ β) (x : Fueled ε α) : Fueled ζ β :=
  ExceptT.mk <| x.run.map f

/-- Reconstitute the legacy `Except` API at a public boundary. -/
def toExcept (onExhausted : ε) (x : Fueled ε α) : Except ε α :=
  match x.run with
  | none => .error onExhausted
  | some result => result

@[simp] lemma exhausted_run : (exhausted : Fueled ε α).run = none := rfl

@[simp] lemma ofExcept_run (x : Except ε α) : (ofExcept x).run = some x := rfl

@[simp] lemma ok_run (x : α) : (ok x : Fueled ε α).run = some (.ok x) := rfl

@[simp] lemma error_run (e : ε) :
    (error e : Fueled ε α).run = some (.error e) := rfl

@[simp] lemma mapResult_run (f : Except ε α → Except ζ β) (x : Fueled ε α) :
    (mapResult f x).run = x.run.map f := rfl

@[simp] lemma toExcept_exhausted (e : ε) :
    toExcept e (exhausted : Fueled ε α) = .error e := rfl

@[simp] lemma toExcept_ofExcept (e : ε) (x : Except ε α) :
    toExcept e (ofExcept x) = x := rfl

end Fueled

end FuelCarrier

section FuelResidue

open Jaune

/- The residue of the fuel-bounded (`Fueled`) reasoning layer.  With
   sufficiency proved in Jaune, fuel never reaches a Blanc statement: these
   three lemmas exist only so that the adequacy bridge between `Exec` and the
   total `exec` can be proved by induction over `execFueled`. -/

namespace Fueled

variable {ε : Type} {α : Type}

lemma ext {x y : Fueled ε α} (h : x.run = y.run) : x = y := h

lemma exhausted_ne_ofExcept {x : Except ε α} :
    (Fueled.exhausted : Fueled ε α) ≠ Fueled.ofExcept x :=
  fun h => nomatch congrArg ExceptT.run h

@[simp] lemma ofExcept_inj {x y : Except ε α} :
    (Fueled.ofExcept x : Fueled ε α) = Fueled.ofExcept y ↔ x = y :=
  ⟨fun h => Option.some.inj (congrArg ExceptT.run h), fun h => by rw [h]⟩

end Fueled

end FuelResidue

/-- The fuel budget seeded from a frame's gas measure. The additive constant is
the one `execFueled_succ_ne_exhausted` proves sufficient: **1**. Under
`rules.stateGas = none` the measure is `gasLeft`, so the seed is the seed it
always was; under `some _` it also counts the spill a refund can hand back. -/
def sufficientFuel (gas : Nat) : Nat := gas + 1

end Jaune
