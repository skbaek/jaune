import Jaune.MessageCall.Driver

/-!
# The four-part message call: the total interpreter (goal `jaune-shape-and-names-v1`, W1 unit F)

`exec` runs the staged driver with fuel seeded from the frame's own gas measure, as today's
`exec` does; the exhaustion branch is a typed internal invariant error. Staged under
`Jaune.Staging` beside today's `exec`.

It sits in its own module so that the cached twin of the driver, with its `@[csimp]` theorem, can
be imported here before `exec` is compiled (`@[csimp]` rewrites only code compiled after it).
-/

namespace Jaune

namespace Staging

/-- The total interpreter over the staged driver. -/
def exec (evm : Evm) : Except (EvmError × Devm) Devm :=
  match (execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run with
  | some r => r
  | none => .error ⟨.internal (.invariant .none), evm.dyna⟩

end Staging

end Jaune
