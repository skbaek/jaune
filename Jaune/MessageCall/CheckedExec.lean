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

/-- A settled top-level frame and the running machine it entered with, if it ran code. -/
structure Frame.TopRun where
  root : Option Frame.Running
  result : Frame.Result

/-- Run a top-level frame from its checkpoint and retain the entered root. A frame that
finishes on entry, such as a precompile, has a settled result and no running root. -/
def Frame.runTopWithRoot (f : Frame) : Except Fault Frame.TopRun :=
  match enterWith f f.checkpoint with
  | .done result => result.map (fun value => ⟨none, value⟩)
  | .run r => (exec r >>= settle f).map (fun value => ⟨some r, value⟩)

/-- The settled result of a top-level frame. -/
def Frame.runTop (f : Frame) : Except Fault Frame.Result :=
  (f.runTopWithRoot).map Frame.TopRun.result

/-- The root of a run is exactly the running state produced by entry. -/
theorem Frame.runTopWithRoot_root {f : Frame} {run : Frame.TopRun}
    (h : f.runTopWithRoot = .ok run) : run.root =
    match enterWith f f.checkpoint with
    | .done _ => none
    | .run root => some root := by
  unfold Frame.runTopWithRoot at h
  cases entry : enterWith f f.checkpoint with
  | done result =>
    rw [entry] at h
    cases result <;> cases h <;> rfl
  | run root =>
    rw [entry] at h
    change Except.map (fun value => (⟨some root, value⟩ : Frame.TopRun))
      (exec root >>= settle f) = .ok run at h
    cases evaluated : (exec root >>= settle f) <;> rw [evaluated] at h <;> cases h <;> rfl

theorem Frame.runTop_eq (f : Frame) : f.runTop =
    match enterWith f f.checkpoint with
    | .done result => result
    | .run r => exec r >>= settle f := by
  unfold Frame.runTop Frame.runTopWithRoot
  cases enterWith f f.checkpoint with
  | done result => cases result <;> rfl
  | run r =>
    change Except.map Frame.TopRun.result (Except.map _ (exec r >>= settle f)) = (exec r >>= settle f)
    cases (exec r >>= settle f) <;> rfl

end Jaune.Checked
