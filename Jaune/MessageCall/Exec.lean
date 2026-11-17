import Jaune.MessageCall.Driver
import Jaune.Implementation.CachedDriver

/-!
# The four-part message call: the total interpreter (goal `jaune-shape-and-names-v1`, W1 unit F)

`exec` runs the driver with fuel seeded from the frame's own gas measure; the exhaustion branch
is a typed internal invariant error.

It sits in its own module so that the cached twin of the driver, with its compiler-substitution
theorem, can be imported here before `exec` is compiled: that substitution rewrites only code
compiled after it. The import of `Jaune.Implementation.CachedDriver` above is that one; dropping it
compiles `exec` against the uncached driver.
-/

namespace Jaune

/-- The total interpreter over the driver `execFueled`. -/
def exec (evm : Evm) : Except (EvmError × Devm) Devm :=
  match (execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run with
  | some r => r
  | none => .error ⟨.internal (.invariant .none), evm.dyna⟩

end Jaune

