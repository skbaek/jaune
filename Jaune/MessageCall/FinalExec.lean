import Jaune.MessageCall.FinalDriver

/-!
# The total interpreter over `Frame.Running`, and the top-level frame (goal `jaune-shape-and-names-v1`, W3-3)

`Staging.exec` runs the driver with fuel seeded from the frame's own gas measure; the exhaustion
branch is a typed internal invariant fault. `Staging.Frame.runTop` enters a top-level frame from
its checkpoint, runs `exec` and settles.

This module is where the compiled-code substitution must be in scope when the staged chain
becomes the interpreter: it then imports `Jaune.Implementation.FinalCachedDriver`, whose twin
theorem rewrites only code compiled after it (the switch adds that import, its layering row and
the attribute; until then the twin is a plain theorem and this module compiles `exec` against the
uncached driver, which is what the `Devm` interpreter still runs).
-/

namespace Jaune.Staging

open Jaune

/-- The total interpreter over the driver `Staging.execFueled`. -/
def exec (r : Frame.Running) : Except Fault Frame.Exit :=
  match (execFueled r (sufficientFuel r.state.machine.gasMeasure)).run with
  | some x => x
  | none => .error (.internal (.invariant .none))

/-- Run a top-level frame: enter it from its checkpoint, run the code, settle. -/
def Frame.runTop (f : Frame) : Except Fault Frame.Result :=
  match enterWith f f.checkpoint with
  | .done result => result
  | .run r => exec r >>= settle f

end Jaune.Staging
