import Jaune.MessageCall

/-!
# The four-part message call: `resume` (goal `jaune-shape-and-names-v1`, W1 unit E)

`resume` hands a finished child's result back to the caller that spawned it: under Amsterdam's
rules it first checks that the result is settled, then merges the result into the saved caller
by lifetime and runs the calling opcode's push and output write.

* The machine is the saved caller's, with the child's meters absorbed and its return data set
  (`absorbMeters`).
* The world and the substate are the child's merged in on success, the caller's otherwise; a
  failed child leaves only its touch of RIPEMD-160's address, under rules without state gas.
* The trail is always merged.
* The push has its capacity check: on a full stack the caller halts with the merged state.

The caller comes back as a `Devm`, rebuilt from the merged groups and
the caller's `output` and `error`, which `Pending` passes through unchanged.
-/

namespace Jaune

/-- `credit_state_gas_refund` on a lifetime-grouped machine: `Mach.creditStateGasRefund`'s
counterpart. -/
def Machine.creditStateGasRefund (amount : Nat) (m : Machine) : Machine :=
  let g := m.stateGas
  let fromGasLeft := min amount g.spilled
  { m with
    gasLeft := m.gasLeft + fromGasLeft
    stateGas :=
      { g with left := g.left + (amount - fromGasLeft), spilled := g.spilled - fromGasLeft } }

/-- `repay_state_gas_spill` on a lifetime-grouped machine: `Mach.repayStateGasSpill`'s
counterpart. -/
def Machine.repayStateGasSpill (m : Machine) : Machine :=
  let g := m.stateGas
  let repayment := min g.left g.spilled
  { m with
    gasLeft := m.gasLeft + repayment
    stateGas := { g with left := g.left - repayment, spilled := g.spilled - repayment } }

/-- The caller's machine after its child returns. Execution gas comes back whatever the child's
fate; under state gas so do the reservoir and the spill, after which a failed child refunds a
charged new account and a successful one repays spill. The return data is the child's output,
except after a successful creation, which returns none. -/
def absorbMeters (rules : ForkRules) (p : Pending) (saved : Machine) (r : Frame.Result) :
    Machine :=
  let returnData := match p.target, r.failed with
    | .create _, false => []
    | _, _ => r.output
  match rules.stateGas with
  | none => { saved with gasLeft := saved.gasLeft + r.gasLeft, returnData := returnData }
  | some state =>
    let m : Machine :=
      { saved with
        gasLeft := saved.gasLeft + r.gasLeft
        stateGas := { saved.stateGas with
          left := saved.stateGas.left + r.stateGas.left
          spilled := saved.stateGas.spilled + r.stateGas.spilled }
        returnData := returnData }
    if r.failed then
      if p.newAccountCharged then m.creditStateGasRefund state.newAccount else m
    else m.repayStateGasSpill

/-- The word the calling opcode pushes: the new address after a successful creation, 1 after a
successful call, 0 after a failure. -/
def ReturnTarget.status : ReturnTarget → Frame.Result → U256
  | .create address, .success .. => address.toU256
  | .call .., .success .. => 1
  | _, _ => 0

/-- The calling opcode's effect on the caller's machine: push the status, and for a call write
the output into the caller's output window. -/
def ReturnTarget.finish (target : ReturnTarget) (r : Frame.Result) (m : Machine) : Machine :=
  let m := { m with stack := target.status r :: m.stack }
  match target with
  | .call outputIndex outputSize =>
    { m with memory := m.memory.write outputIndex (r.output.take outputSize) }
  | .create _ => m

/-- A lifetime-grouped caller as a `Devm`, with the output and stored error it had when
it spawned. Goes when `Devm` is replaced by `Frame.State`. -/
def Pending.restore (p : Pending) (s : Frame.State) : Devm :=
  let d := s.toDevm
  { d with «meta» := { d.meta with output := p.legacyOutput, error := p.legacyError } }

/-- Resume the caller `saved` with its child's result `r`.

Under state gas a failed result must be settled (no committed or outstanding spill, the
reservoir at its baseline) and a successful one must have no committed spill; otherwise the run
faults. The merged caller is then pushed the status; a full stack halts it
with the merged state. -/
def resume (rules : ForkRules) (p : Pending) (saved : Frame.State) (r : Frame.Result) :
    Except Fault (Except (ExceptionalHalt × Devm) Devm) := do
  if rules.stateGas.isSome then
    if r.failed then
      unless r.stateGas.committedSpill = 0 ∧ r.stateGas.spilled = 0 ∧
          r.stateGas.left = r.stateGas.baseline do
        throw (.internal (.invariant (.text "failed Amsterdam child is not settled")))
    else unless r.stateGas.committedSpill = 0 do
      throw (.internal (.invariant (.text "Amsterdam child has committed state-gas spill")))
  let (world, substate) := match r with
    | .success _ _ _ world sub _ => (world, saved.substate.absorb rules sub)
    | _ => (saved.world, match rules.stateGas with
                         | none => saved.substate.keepTouch r.trail
                         | some _ => saved.substate)
  let merged : Frame.State :=
    ⟨absorbMeters rules p saved.machine r, world, substate, saved.trail.absorb r.trail⟩
  if merged.machine.stack.length < 1024 then
    pure (.ok (p.restore { merged with machine := p.target.finish r merged.machine }))
  else pure (.error (.stackOverflow .none, p.restore merged))

end Jaune

