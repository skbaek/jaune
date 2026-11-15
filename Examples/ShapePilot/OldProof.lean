import Examples.ShapePilot.Lifetime

namespace Examples.ShapePilot
open Jaune Prototype

/-- Today's failed-child incorporation still takes the child's world. Its
world survival proof therefore requires an already-established rollback fact. -/
theorem old_call_survival (parent child out : Devm) (index size : Nat)
    (failed : child.error.isSome = true)
    (rolledBack : child.world = parent.world)
    (room : parent.stack.length < 1024)
    (ran : Jaune.Resume.run (.call parent index size) (.ok child) = .ok out) :
    out.world = parent.world ∧
    (Dynamic.ofLegacy out).substate =
      (Dynamic.ofLegacy parent).substate.keepTouch (Dynamic.ofLegacy child).trail := by
  simp only [Jaune.Resume.run, liftToExecution, bind, Except.bind,
    failed, ↓reduceIte, Devm.push_def, Except.assert] at ran
  simp only [incorporateChildOnError, Devm.setMach, Devm.setMeta, Devm.setWorld,
    Devm.stack] at ran
  simp only [Devm.stack] at room
  simp only [room, ↓reduceIte, Except.ok.injEq] at ran
  subst out
  constructor
  · change child.world = parent.world
    exact rolledBack
  · rfl

/-- Amsterdam additionally needs the child-settlement invariant: in
particular, the old incorporation adds its refund counter to the parent's. -/
theorem old_create_survival (parent child out : Devm) (address : Adr)
    (state : StateGasRules) (charged : Bool)
    (failed : child.error.isSome = true)
    (rolledBack : child.world = parent.world)
    (settled : child.AmsterdamFailedChildSettled)
    (room : parent.stack.length < 1024)
    (ran : Jaune.Resume.run (.createAmsterdam state parent address charged)
      (.ok child) = .ok out) :
    out.world = parent.world ∧
    (Dynamic.ofLegacy out).substate = (Dynamic.ofLegacy parent).substate := by
  simp only [Jaune.Resume.run, liftToExecution, bind, Except.bind,
    failed, ↓reduceIte, Except.assert, settled] at ran
  have zeroRefund : child.refundCounter = 0 := settled.2.2.1
  cases charged <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Devm.push_def, Except.assert,
      incorporateChildAmsterdamOnError, Devm.creditStateGasRefund,
      Mach.creditStateGasRefund, Devm.setMach, Devm.setMeta, Devm.setWorld,
      Devm.stack] at ran <;>
    simp only [Devm.stack] at room <;>
    simp only [room, ↓reduceIte, bind, Except.bind, Except.ok.injEq] at ran <;>
    subst out
  all_goals
    constructor
    · change child.world = parent.world
      exact rolledBack
    · change { (Dynamic.ofLegacy parent).substate with
          refund := parent.refundCounter + child.refundCounter } = _
      rw [zeroRefund, Int.add_zero]
      rfl

end Examples.ShapePilot
