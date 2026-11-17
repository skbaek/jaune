import Jaune.MessageCall

/-!
# The four-part message call: `settle` (goal `jaune-shape-and-names-v1`, W1 unit C)

`settle` turns a frame's raw result into what the frame hands back to its caller, a
`Frame.Result`, or a fault. It was staged until the switch commit gave it its final name, and
nothing in today's interpreter reads it until the switch commit.

This is the W1 form: the raw result is still today's `Execution`, over `Devm`. The final form,
over `Frame.State` and `Frame.Exit`, is the same text without the two fault arms and the
conversions through `Frame.State.ofDevm`.

`settle` never reads `Meta.error` of a raw `.ok`: the constructor of the raw result says how the
frame ended. Today's interpreter never stores an error before settlement, so the two agree on
every raw result it produces (the bridge's premise `Execution.Clean`).
-/

namespace Jaune

/-- Charge execution gas, failing only by running out: today's `chargeGas` with a halt-only error
type. -/
def Devm.chargeGas (cost : Nat) (d : Devm) : Except (ExceptionalHalt × Devm) Devm :=
  match safeSub d.gasLeft cost with
  | none => .error (.outOfGas .none, d)
  | some gas => .ok (d.withGasLeft gas)

/-- Charge state gas, reservoir first and then spilling into execution gas, failing only by
running out: today's `chargeStateGas` with a halt-only error type. -/
def Devm.chargeStateGas (amount : Nat) (d : Devm) : Except (ExceptionalHalt × Devm) Devm :=
  if amount ≤ d.mach.stateGas.left then
    .ok (d.setMach { d.mach with
      stateGas := { d.mach.stateGas with left := d.mach.stateGas.left - amount } })
  else if amount - d.mach.stateGas.left ≤ d.mach.gasLeft then
    .ok (d.setMach { d.mach with
      gasLeft := d.mach.gasLeft - (amount - d.mach.stateGas.left)
      stateGas := { d.mach.stateGas with
        left := 0
        spilled := d.mach.stateGas.spilled + (amount - d.mach.stateGas.left) } })
  else
    .error (.outOfGas .none, d)

/-- The charge for a creation's code deposit: today's `processCreateMessage.chargeCodeGas` with a
halt-only error type. Without state gas the code is charged per byte before its size is checked,
so a size failure carries the charged state; with state gas the prefix and the size are checked
before either charge. -/
def chargeDeposit (rules : ForkRules) (code : Bytes) (d : Devm) :
    Except (ExceptionalHalt × Devm) Devm :=
  match rules.stateGas with
  | none =>
    let chargeThenSize : Except (ExceptionalHalt × Devm) Devm := do
      let d ← Devm.chargeGas (code.length * Gas.codeDeposit) d
      if rules.code.maxCodeSize < code.length then .error (.outOfGas .none, d) else .ok d
    match code with
    | 0xEF :: _ =>
      if rules.creation.rejectEf then .error (.invalidContractPrefix .none, d)
      else chargeThenSize
    | _ => chargeThenSize
  | some state =>
    match code with
    | 0xEF :: _ => .error (.invalidContractPrefix .none, d)
    | _ =>
      if rules.code.maxCodeSize < code.length then .error (.outOfGas .none, d)
      else do
        let d ← Devm.chargeGas (Gas.keccak256Word * ceilDiv code.length 32) d
        Devm.chargeStateGas (code.length * state.costPerStateByte) d

/-- A creation's code deposit: the charge, then the code set at the new address
(`Devm.setCode`, which also forgets an empty account's storage writes). -/
def depositCode (rules : ForkRules) (recipient : Address) (code : Bytes) (d : Devm) :
    Except (ExceptionalHalt × Devm) Devm :=
  (chargeDeposit rules code d).map fun d => d.setCode recipient ⟨⟨code⟩⟩

/-- A successful frame's result, from its final state and output. -/
def Frame.Result.ofSuccess (output : Bytes) (d : Devm) : Frame.Result :=
  let s := Frame.State.ofDevm d
  .success output s.machine.gasLeft s.machine.stateGas s.world s.substate s.trail

/-- Settle a frame's raw result.

* A fault stays a fault; its state is dropped.
* A revert keeps its output and gas; under state gas its meter is refilled to the baseline.
* A halt forfeits its gas; under state gas its meter is refilled first.
* A failed frame's trail records whether RIPEMD-160's address was touched: by a child, or by the
  frame itself when it targets that address and it exists and is empty in the world the frame
  was entered on.
* A finished frame records its own touch, then a creation deposits its code; a failed deposit
  is a halt whose trail records only the touches already made. -/
def settle (f : Frame) (raw : Execution) : Except Fault Frame.Result :=
  let m := f.message
  let rules := m.context.block.rules
  let failedTrail (d : Devm) : Trail :=
    let selfTouch := rules.settlement.touchedSweep && (m.context.recipient == ripemd160Address) &&
      decide (accountExistsAndIsEmpty f.enteredWorld.state m.context.recipient)
    { (Frame.State.ofDevm d).trail with
      touchedRIPEMD160 := selfTouch || d.meta.touchedAccounts.contains ripemd160Address }
  let depositTrail (d : Devm) : Trail :=
    { (Frame.State.ofDevm d).trail with
      touchedRIPEMD160 := d.meta.touchedAccounts.contains ripemd160Address }
  let reverted (d : Devm) : Devm :=
    match rules.stateGas with
    | none => d
    | some _ => d.restoreStateGas
  let halted (d : Devm) : Devm :=
    match rules.stateGas with
    | none => d.withGasLeft 0
    | some _ => d.restoreStateGas.forfeitRemainingGas
  match raw with
  | .error (.crypto reason, _) => .error (.crypto reason)
  | .error (.internal reason, _) => .error (.internal reason)
  | .error (.revert, d) =>
    .ok (.revert d.output (reverted d).gasLeft (reverted d).stateGas (failedTrail d))
  | .error (.halt reason, d) => .ok (.halt reason (halted d).stateGas (failedTrail d))
  | .ok d =>
    let d := d.recordTouch rules true m.context.recipient
    match m.kind with
    | .call => .ok (Frame.Result.ofSuccess d.output d)
    | .create =>
      match depositCode rules m.context.recipient d.output d with
      | .ok s => .ok (Frame.Result.ofSuccess d.output s)
      | .error (reason, s) => .ok (.halt reason (halted s).stateGas (depositTrail s))

end Jaune

