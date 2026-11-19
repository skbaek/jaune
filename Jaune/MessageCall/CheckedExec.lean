import Jaune.MessageCall.CheckedDriver

/-!
# The total checked interpreter, and the top-level frame (goal `jaune-shape-and-names-v1`, G2b, F1d)

`Checked.exec` runs the driver with fuel seeded from the frame's own gas measure; the exhaustion
branch is a typed internal invariant fault. `Checked.Frame.runTop` enters a top-level frame from
its checkpoint, runs `exec` and settles.

It sits in its own module, as `Jaune.MessageCall.Exec` does for the `Devm` interpreter, so that
the cached twin of the driver, with its compiled-code substitution theorem, can be imported here
before `exec` is compiled: that substitution rewrites only code compiled after it. The import of
`Jaune.Implementation.CheckedCachedDriver`, its `implementation_imports` row in
`scripts/layering.json` and the compiled-code substitution attribute (with its hygiene row) land together as one
reserved packet item; until then the twin is a plain theorem and this module compiles `exec`
against the uncached driver.
-/

namespace Jaune.Checked

open Jaune

/-- The total interpreter over the driver `Checked.execFueled`. -/
def exec (r : Frame.Running) : Except Fault Frame.Exit :=
  match (execFueled r (sufficientFuel r.state.machine.gasMeasure)).run with
  | some x => x
  | none => .error (.internal (.invariant .none))

/-- Run a top-level frame: enter it from its checkpoint, run the code, settle. -/
def Frame.runTop (f : Frame) : Except Fault Frame.Result :=
  match enterWith f f.checkpoint with
  | .done result => result
  | .run r => exec r >>= settle f

end Jaune.Checked
