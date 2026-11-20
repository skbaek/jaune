import Jaune.MessageCall.CheckedDriver
import Jaune.Implementation.CheckedCachedDriver

/-!
# The total checked interpreter, and the top-level frame (goal `jaune-shape-and-names-v1`, G2b, F1d)

`Checked.exec` runs the driver with fuel seeded from the frame's own gas measure; the exhaustion
branch is a typed internal invariant fault. `Checked.Frame.runTop` enters a top-level frame from
its checkpoint, runs `exec` and settles.

It sits in its own module, as `Jaune.MessageCall.Exec` does for the `Devm` interpreter, so that
the cached twin of the driver, with its compiled-code substitution theorem, is imported here
before `exec` is compiled: that substitution rewrites only code compiled after it. The import of
`Jaune.Implementation.CheckedCachedDriver` carries an `implementation_imports` row in
`scripts/layering.json`, and the substitution attribute a row in `scripts/hygiene-allow.txt`;
`scripts/check-memory-probe.sh` fails without either.
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

namespace TopLevel

/-- A refusal before any frame was entered. State-gas forks keep the reads from
preparation and restore the reservoir to its message grant. -/
inductive Refusal where
  | collision (reason : ExceptionalHalt)
  | stateGas (reason : ExceptionalHalt) (stateGasLeft : Nat)
      (accountReads : AdrSet) (storageReads : KeySet)

inductive Preparation where
  | refused (reason : Refusal)
  | frame (frame : Frame) (authorizationRefund : Nat)

/-- A refusal has no frame. An executed frame always has a settled result, and
has a running root exactly when it entered the interpreter. -/
inductive Run where
  | refused (reason : Refusal)
  | frame (frame : Frame) (authorizationRefund : Nat) (run : Frame.TopRun)

/-- The settled frame's refund, plus the authorization refund on forks without state gas.
A successful frame with a negative refund counter faults. -/
def Run.refundCounter : Run → Except Fault Nat
  | .refused _ => .ok 0
  | .frame f authorizationRefund run =>
    let refund : Except Fault Nat := match run.result with
      | .success _ _ _ _ substate _ =>
        (Int.toNat? substate.refund).toExcept
          (Fault.internal (.invariant (.text "refund counter is negative")))
      | _ => .ok 0
    match f.message.context.block.rules.stateGas with
    | none => (authorizationRefund + ·) <$> refund
    | some _ => refund

def Preparation.run : Preparation → Except Fault Run
  | .refused reason => .ok (.refused reason)
  | .frame f refund => f.runTopWithRoot.map (.frame f refund)

end TopLevel

end Jaune.Checked
