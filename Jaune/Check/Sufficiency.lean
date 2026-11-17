-- Check/Sufficiency.lean : executable checks of `Jaune/Sufficiency.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/Sufficiency.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.Sufficiency

namespace Jaune

open Jaune

/-! ## Focused executable checks for the total entry points

These mirror the flatten arc's representative states — arithmetic loop, nested
CALL, CREATE collision, precompile under both dispatch paths, depth-zero
short-circuit, out-of-gas halt, REVERT with output — but drive them through the
fuel-free API. `Jaune.Check.Execution` keeps the checks that pin `execFueled` itself,
including the one that shows fuel really can run out when it is not seeded from
the frame's gas.

`private` declarations do not cross module boundaries, so the two helpers this
block shares with `Jaune.Check.Execution` are restated here. Keep them in step with
their counterparts `flattenGuardCode` and `flattenGuardMsg` at
`Jaune/Check/Execution.lean:263`. -/

private def totalGuardCode (bytes : Bytes) : ByteArray := .mk <| .mk bytes

private def totalGuardMsg (bytes : Bytes) (gas depth : Nat) : Msg :=
  {
    (default : Msg) with
    gas := gas
    code := totalGuardCode bytes
    depth := depth
  }

private def totalGuardSummary
    (r : Except (EvmError × State × AdrSet × TransientStorage) Devm) :
    Option (Option SettledHalt × List U256 × Bytes × Nat) :=
  match r with
  | .ok devm => some ⟨devm.error, devm.stack, devm.output, devm.gasMeasure⟩
  | .error _ => none

-- Arithmetic loop: the state that exhausted `execFueled` at fuel 20 now runs to a
-- definite out-of-gas result, because the seeded budget is provably sufficient.
private def totalGuardArithmeticLoop : Bool :=
  let msg := totalGuardMsg [0x5B, 0x60, 0x00, 0x56] 1000 8
  match Legacy.exec (initEvm msg), processMessage msg with
  | .error ⟨err, _⟩, .ok devm =>
    err == .halt (.outOfGas .none) &&
      devm.error == some (.halt (.outOfGas .none)) &&
      devm.gasMeasure == 0
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

private def totalGuardNestedCallDirect :=
  totalGuardSummary (runFrame (Legacy.Frame.ofCall totalGuardNestedCallMsg))

private def totalGuardNestedCallPublic :=
  totalGuardSummary (processMessage totalGuardNestedCallMsg)

#guard totalGuardNestedCallDirect = totalGuardNestedCallPublic
#guard totalGuardNestedCallDirect.map
    (fun x => ((x.2.1.head?, x.2.2.2) : Option U256 × Nat)) =
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
  match processMessage totalGuardCreateCollisionMsg with
  | .ok devm =>
    devm.error == none && devm.stack.head? == some 0 && devm.gasMeasure == 1062
  | .error _ => false

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
      processMessage (totalGuardPrecompileMsg false),
      processMessage (totalGuardPrecompileMsg true) with
  | .ok viaPrecomp, .ok viaCode => viaPrecomp.gasMeasure == 7000 && viaCode.gasMeasure == 10000
  | _, _ => false

#guard totalGuardPrecompileDispatch

-- Depth zero prevents spawning: the same parent that gets failure word 1 at
-- depth 8 gets 0 at depth 0, with the call never reaching the driver.
private def totalGuardDepthZero : Bool :=
  match processMessage {totalGuardNestedCallMsg with depth := 0} with
  | .ok devm => devm.stack.head? == some 0 && devm.gasMeasure == 97379
  | .error _ => false

#guard totalGuardDepthZero

-- A PUSH with zero gas halts through the frozen OutOfGasError channel.
private def totalGuardOog : Bool :=
  let msg := totalGuardMsg [0x60, 0x01, 0x00] 0 8
  match Legacy.exec (initEvm msg) with
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
  match runFrame (Legacy.Frame.ofCall msg) with
  | .ok devm =>
    devm.error == some .revert &&
      devm.output.length == 32 &&
      devm.output.getLast? == some 0x2A &&
      devm.gasMeasure == 982
  | .error _ => false

#guard totalGuardRevert

end Jaune

