import Jaune.MessageCall.Resume

/-!
# What `resume` does with a child's result (goal `jaune-shape-and-names-v1`, S3)

Facts about `resume` alone, relative to the saved caller, with no induction over the
interpreter:

* `resume_failed`: a failed child leaves the caller's world and substate as saved, except the
  one touch of RIPEMD-160's address a rule keeps; the caller takes the child's trail.
* `returnedMachine_failed_call`, `returnedMachine_failed_create`: the calling opcode's effect on
  the caller's machine after a failed child, given exactly: a zero on the stack, for a call the
  returned bytes in its output window, the gas and state gas the child hands back, and under
  state gas the refund of a new-account charge the caller paid before the child ran.
* `resume_success`: a successful child's world replaces the caller's and its substate is
  absorbed.

`resume` can fail in three ways: the push's capacity check and, under state gas, the two
assertions on the child's meter. The premises `room` and `settled` rule them out. Both follow
from run invariants (`Jaune.MessageCall.RunInvariants`), so a client discharges them without
unfolding the interpreter.
-/

namespace Jaune

/-- A failed child's meter as settlement leaves it: no committed or outstanding spill, and the
reservoir at its baseline. -/
def StateGasMeter.Settled (m : StateGasMeter) : Prop :=
  m.committedSpill = 0 ∧ m.spilled = 0 ∧ m.left = m.baseline

instance (m : StateGasMeter) : Decidable m.Settled := by
  unfold StateGasMeter.Settled; infer_instance

/-- The caller's machine after its child returns and the calling opcode's push and output write:
`resume`'s machine when the push fits. -/
def returnedMachine (rules : ForkRules) (p : Pending) (saved : Machine) (r : Frame.Result) :
    Machine :=
  p.target.finish r (absorbMeters rules p saved r)

/-- The caller's lifetime groups after its child returns, before the W1 rebuild into `Devm`. -/
def resumedState (rules : ForkRules) (p : Pending) (saved : Frame.State) (r : Frame.Result) :
    Frame.State :=
  { machine := returnedMachine rules p saved.machine r
    world := match r with
      | .success _ _ _ world _ _ => world
      | _ => saved.world
    substate := match r with
      | .success _ _ _ _ sub _ => saved.substate.absorb rules sub
      | _ => match rules.stateGas with
        | none => saved.substate.keepTouch r.trail
        | some _ => saved.substate
    trail := saved.trail.absorb r.trail }

@[simp] theorem absorbMeters_stack (rules : ForkRules) (p : Pending) (saved : Machine)
    (r : Frame.Result) : (absorbMeters rules p saved r).stack = saved.stack := by
  unfold absorbMeters
  cases rules.stateGas with
  | none => rfl
  | some state =>
    dsimp only
    split
    · split <;> rfl
    · rfl

/-- The general form: whenever the push fits and the meter assertions pass, `resume` returns
the resumed state. -/
theorem resume_of_room (rules : ForkRules) (p : Pending) (saved : Frame.State)
    (r : Frame.Result) (room : saved.machine.stack.length < 1024)
    (settled : rules.stateGas.isSome → r.failed → r.stateGas.Settled)
    (committed : rules.stateGas.isSome → r.failed = false → r.stateGas.committedSpill = 0) :
    resume rules p saved r = .ok (.ok (p.restore (resumedState rules p saved r))) := by
  have hroom : (absorbMeters rules p saved.machine r).stack.length < 1024 := by
    rw [absorbMeters_stack]; exact room
  unfold resume
  cases hs : rules.stateGas with
  | none =>
    cases r <;>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hroom, resumedState,
        returnedMachine, hs, pure, Except.pure]
  | some state =>
    have hset : rules.stateGas.isSome = true := by rw [hs]; rfl
    cases hf : r.failed with
    | true =>
      obtain ⟨h1, h2, h3⟩ := settled hset hf
      cases r <;> simp_all [Frame.Result.failed, resumedState, returnedMachine, pure,
        Except.pure]
    | false =>
      have h1 := committed hset hf
      cases r <;> simp_all [Frame.Result.failed, resumedState, returnedMachine, pure,
        Except.pure]

/-- (a) and (c): a failed child. The caller's world is the saved one; its substate is the saved
one, except that under rules without state gas it keeps the child's touch of RIPEMD-160's
address; its trail absorbs the child's. -/
theorem resume_failed (rules : ForkRules) (p : Pending) (saved : Frame.State) (r : Frame.Result)
    (failed : r.failed = true) (room : saved.machine.stack.length < 1024)
    (settled : rules.stateGas.isSome → r.stateGas.Settled) :
    resume rules p saved r = .ok (.ok (p.restore
      { machine := returnedMachine rules p saved.machine r
        world := saved.world
        substate := match rules.stateGas with
          | none => saved.substate.keepTouch r.trail
          | some _ => saved.substate
        trail := saved.trail.absorb r.trail })) := by
  rw [resume_of_room rules p saved r room (fun h _ => settled h)
    (fun _ h => by rw [failed] at h; cases h)]
  cases r with
  | success => simp [Frame.Result.failed] at failed
  | revert => rfl
  | halt => rfl

/-- A successful child: its world replaces the caller's, its substate is absorbed into the
caller's, and its trail is absorbed. -/
theorem resume_success (rules : ForkRules) (p : Pending) (saved : Frame.State)
    (output : Bytes) (gasLeft : Nat) (stateGas : StateGasMeter) (world : World)
    (substate : Substate) (trail : Trail) (room : saved.machine.stack.length < 1024)
    (committed : rules.stateGas.isSome → stateGas.committedSpill = 0) :
    resume rules p saved (.success output gasLeft stateGas world substate trail) =
      .ok (.ok (p.restore
        { machine := returnedMachine rules p saved.machine
            (.success output gasLeft stateGas world substate trail)
          world := world
          substate := saved.substate.absorb rules substate
          trail := saved.trail.absorb trail })) :=
  resume_of_room rules p saved _ room (fun _ h => by cases h) (fun h _ => committed h)

/-- (b) for a call: after a failed child the caller's stack gets a zero, the returned bytes go
into the output window, the return data is the child's output, and the meters take back what
the child hands back; under state gas a charged new account is refunded. -/
theorem returnedMachine_failed_call (rules : ForkRules) (p : Pending) (saved : Machine)
    (r : Frame.Result) {outputIndex outputSize : Nat}
    (target : p.target = .call outputIndex outputSize) (failed : r.failed = true) :
    returnedMachine rules p saved r =
      let m : Machine :=
        { stack := 0 :: saved.stack
          memory := saved.memory.write outputIndex (r.output.take outputSize)
          gasLeft := saved.gasLeft + r.gasLeft
          stateGas := match rules.stateGas with
            | none => saved.stateGas
            | some _ =>
              { saved.stateGas with
                left := saved.stateGas.left + r.stateGas.left
                spilled := saved.stateGas.spilled + r.stateGas.spilled }
          returnData := r.output }
      match rules.stateGas with
      | some state => if p.newAccountCharged then m.creditStateGasRefund state.newAccount else m
      | none => m := by
  unfold returnedMachine ReturnTarget.finish ReturnTarget.status absorbMeters
  rw [target]
  cases r with
  | success => simp [Frame.Result.failed] at failed
  | revert =>
    cases rules.stateGas with
    | none => rfl
    | some state =>
      cases p.newAccountCharged <;> simp [Frame.Result.failed, Machine.creditStateGasRefund]
  | halt =>
    cases rules.stateGas with
    | none => rfl
    | some state =>
      cases p.newAccountCharged <;> simp [Frame.Result.failed, Machine.creditStateGasRefund]

/-- (b) for a creation: after a failed child the caller's stack gets a zero, its memory is
unchanged, the return data is the child's output, and the meters are as for a call. -/
theorem returnedMachine_failed_create (rules : ForkRules) (p : Pending) (saved : Machine)
    (r : Frame.Result) {address : Address}
    (target : p.target = .create address) (failed : r.failed = true) :
    returnedMachine rules p saved r =
      let m : Machine :=
        { stack := 0 :: saved.stack
          memory := saved.memory
          gasLeft := saved.gasLeft + r.gasLeft
          stateGas := match rules.stateGas with
            | none => saved.stateGas
            | some _ =>
              { saved.stateGas with
                left := saved.stateGas.left + r.stateGas.left
                spilled := saved.stateGas.spilled + r.stateGas.spilled }
          returnData := r.output }
      match rules.stateGas with
      | some state => if p.newAccountCharged then m.creditStateGasRefund state.newAccount else m
      | none => m := by
  unfold returnedMachine ReturnTarget.finish ReturnTarget.status absorbMeters
  rw [target]
  cases r with
  | success => simp [Frame.Result.failed] at failed
  | revert =>
    cases rules.stateGas with
    | none => rfl
    | some state =>
      cases p.newAccountCharged <;> simp [Frame.Result.failed, Machine.creditStateGasRefund]
  | halt =>
    cases rules.stateGas with
    | none => rfl
    | some state =>
      cases p.newAccountCharged <;> simp [Frame.Result.failed, Machine.creditStateGasRefund]

end Jaune
