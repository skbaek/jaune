-- Check/Sufficiency.lean : executable checks of `Jaune/Sufficiency.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated from `Jaune/Sufficiency.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0), and restated over the four-part message call at the
-- W1 delete commit. The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.Sufficiency
import Jaune.MessageCall.Top
import Jaune.MessageCall.Totality

namespace Jaune

open Jaune

/-! ## Focused executable checks for the total entry points

These mirror the flatten arc's representative states — arithmetic loop, nested
CALL, CREATE collision, precompile under both dispatch paths, depth-zero
short-circuit, out-of-gas halt, REVERT with output — but drive them through the
fuel-free four-part message call: `exec`, and a top-level frame entered, run and settled by
`Frame.runTop`. `Jaune.Check.Execution` keeps the checks that pin `execFueled` itself,
including the one that shows fuel really can run out when it is not seeded from
the frame's gas.

`private` declarations do not cross module boundaries, so the two helpers this
block shares with `Jaune.Check.Execution` are restated here. Keep them in step with
their counterparts `flattenGuardCode` and `flattenGuardMsg` in
`Jaune/Check/Execution.lean`. -/

private def totalGuardCode (bytes : Bytes) : ByteArray := .mk <| .mk bytes

private def totalGuardMsg (bytes : Bytes) (gas depth : Nat) : Msg :=
  {
    (default : Msg) with
    gas := gas
    code := totalGuardCode bytes
    depth := depth
  }

/-- A top-level call frame for `msg`. -/
private def totalGuardFrame (msg : Msg) : Frame := Frame.ofTop msg false

/-- The frame's raw result before settlement, when its code runs: `Frame.runTop`'s
`exec evm`. -/
private def totalGuardRaw (msg : Msg) : Option Execution :=
  match enterWith (totalGuardFrame msg) (totalGuardFrame msg).checkpoint.toDevm with
  | .run evm => some (exec evm)
  | .done _ => none

/-- The settled result's halt reason, output and measure, and the top of the stack the frame's
code left (none when it did not run or faulted). -/
private def totalGuardSummary (msg : Msg) :
    Option (Option SettledHalt × Option U256 × Bytes × Nat) :=
  match Frame.runTop (totalGuardFrame msg) with
  | .ok r =>
    let top := match totalGuardRaw msg with
      | some (.ok d) => d.stack.head?
      | _ => none
    some ⟨r.error?, top, r.output, r.gasMeasure⟩
  | .error _ => none

-- Arithmetic loop: the state that exhausted `execFueled` at fuel 20 now runs to a
-- definite out-of-gas result, because the seeded budget is provably sufficient.
private def totalGuardArithmeticLoop : Bool :=
  let msg := totalGuardMsg [0x5B, 0x60, 0x00, 0x56] 1000 8
  match exec (initEvm msg), Frame.runTop (totalGuardFrame msg) with
  | .error ⟨err, _⟩, .ok r =>
    err == .halt (.outOfGas .none) &&
      r.error? == some (.halt (.outOfGas .none)) &&
      r.gasMeasure == 0
  | _, _ => false

#guard totalGuardArithmeticLoop

-- Nested CALL: run a parent that calls address 0x20, whose code is STOP.
private def totalGuardNestedCallMsg : Msg :=
  let child : Address := 0x20
  let state := State.setCode .empty child (totalGuardCode [0x00])
  let benv := {(default : Benv) with state := state}
  {
    (totalGuardMsg
      [ 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00,
        0x60, 0x00, 0x60, 0x20, 0x61, 0x03, 0xE8, 0xF1, 0x00 ]
      100000 8) with
    benv := benv
  }

#guard (totalGuardSummary totalGuardNestedCallMsg).map
    (fun x => ((x.2.1, x.2.2.2) : Option U256 × Nat)) =
  some (some 1, 97379)

-- CREATE collision, reached the way a transaction reaches it: a frame executes
-- CREATE at an address that already carries code, so the child is never
-- spawned, the reserved `createGas` is not returned, and 0 is pushed.
private def totalGuardCreateCollisionCreator : Address := 0x30

private def totalGuardCreateCollisionMsg : Msg :=
  let created := computeContractAddress totalGuardCreateCollisionCreator 0
  let state := State.setCode .empty created (totalGuardCode [0x00])
  {
    (totalGuardMsg [0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0xF0, 0x00] 100000 8) with
    benv := {(default : Benv) with state := state}
    currentTarget := totalGuardCreateCollisionCreator
  }

private def totalGuardCreateCollision : Bool :=
  match totalGuardSummary totalGuardCreateCollisionMsg with
  | some ⟨error, top, _, measure⟩ => error == none && top == some 0 && measure == 1062
  | none => false

#guard totalGuardCreateCollision

-- Precompile dispatch is taken normally and bypassed when explicitly disabled:
-- the enabled path pays ecrecover's 3,000 gas without ever entering the driver.
private def totalGuardPrecompileMsg (disabled : Bool) : Msg :=
  {
    (totalGuardMsg [] 10000 8) with
    target := some 1
    currentTarget := 1
    codeAddress := some 1
    disablePrecompiles := disabled
  }

private def totalGuardPrecompileDispatch : Bool :=
  match
      Frame.runTop (totalGuardFrame (totalGuardPrecompileMsg false)),
      Frame.runTop (totalGuardFrame (totalGuardPrecompileMsg true)) with
  | .ok viaPrecomp, .ok viaCode => viaPrecomp.gasMeasure == 7000 && viaCode.gasMeasure == 10000
  | _, _ => false

#guard totalGuardPrecompileDispatch

-- Depth zero prevents spawning: the same parent that gets failure word 1 at
-- depth 8 gets 0 at depth 0, with the call never reaching the driver.
private def totalGuardDepthZero : Bool :=
  match totalGuardSummary {totalGuardNestedCallMsg with depth := 0} with
  | some ⟨_, top, _, measure⟩ => top == some 0 && measure == 97379
  | none => false

#guard totalGuardDepthZero

-- A PUSH with zero gas halts through the frozen OutOfGasError channel.
private def totalGuardOog : Bool :=
  let msg := totalGuardMsg [0x60, 0x01, 0x00] 0 8
  match exec (initEvm msg) with
  | .error ⟨err, _⟩ => err == .halt (.outOfGas .none)
  | .ok _ => false

#guard totalGuardOog

-- REVERT retains the 32-byte memory slice and becomes a settled frame result.
private def totalGuardRevert : Bool :=
  let msg :=
    totalGuardMsg
      [ 0x60, 0x2A, 0x60, 0x00, 0x52,
        0x60, 0x20, 0x60, 0x00, 0xFD ]
      1000 8
  match Frame.runTop (totalGuardFrame msg) with
  | .ok r =>
    r.error? == some .revert &&
      r.output.length == 32 &&
      r.output.getLast? == some 0x2A &&
      r.gasMeasure == 982
  | .error _ => false

#guard totalGuardRevert

end Jaune
