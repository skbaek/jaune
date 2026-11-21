-- Check/CheckedSufficiency.lean : the guards of `Jaune/Check/Sufficiency.lean`, restated over the
-- Checked message call.
--
-- Check module (see `scripts/layering.json`). Goal `jaune-shape-and-names-v1`, G2b (unit jsn-u85,
-- S0): each guard of `Jaune/Check/Sufficiency.lean` (`exec`, `enterWith`, `Frame.runTop` over a
-- `Msg`-built frame) is restated over `Checked.exec`, `Checked.enterWith` and
-- `Checked.Frame.runTop` with the same observation and the same expected value. The frame a W1
-- guard built with `Frame.ofTop` from a `Msg` is built here from the corresponding
-- `Checked.Message` on `Checked.Message.initialCheckpoint` (the map of
-- `Checked.TopLevel.Input.ofLegacy`). The default build compiles this module through
-- `JauneChecks.lean`.
import Jaune.MessageCall.Exec
import Jaune.MessageCall.PartsGas

namespace Jaune

open Jaune

/-! ## Focused executable checks for the total entry points

The flatten arc's representative states -- arithmetic loop, nested CALL, CREATE collision,
precompile under both dispatch paths, depth-zero short-circuit, out-of-gas halt, REVERT with
output -- driven through the fuel-free Checked message call: `Checked.exec`, and a top-level frame
entered, run and settled by `Checked.Frame.runTop`. -/

private def totalGuardCode (bytes : Bytes) : ByteArray := .mk <| .mk bytes

/-- The message of a guard: `Msg`'s defaults (caller and recipient 0, no value, no calldata,
nothing static, an empty original state, Prague's block record) with the given code, gas and
depth left. -/
private def totalGuardMessage (bytes : Bytes) (gas depthLeft : Nat) : Message :=
  { context := {
      caller := 0, recipient := 0, value := 0, calldata := [], code := totalGuardCode bytes
      depthLeft := depthLeft, isStatic := false
      tx := { origin := 0, gasPrice := 0, blobVersionedHashes := [], originalState := .empty }
      block := default }
    kind := .call, codeAddress := none, target := none, gas := gas, stateGasGrant := 0
    transfersValue := false, disablePrecompiles := false }

/-- A top-level call frame for `m` over `state`, with nothing warm. -/
private def totalGuardFrame (m : Message) (state : State := .empty) : Frame :=
  ⟨m, m.initialCheckpoint ⟨state, .empty, .emptyWithCapacity⟩ .emptyWithCapacity
    .emptyWithCapacity .emptyWithCapacity .emptyWithCapacity⟩

/-- The running frame a message starts as, before entry (`initEvm`). -/
private def totalGuardRunning (m : Message) : Frame.Running :=
  ⟨0, m.context, (totalGuardFrame m).checkpoint⟩

/-- The frame's raw exit before settlement, when its code runs: `Frame.runTop`'s `exec`. -/
private def totalGuardRaw (f : Frame) : Option (Except Fault Frame.Exit) :=
  match enterWith f f.checkpoint with
  | .run r => some (exec r)
  | .done _ => none

/-- The settled result's halt reason, output and measure, and the top of the stack the frame's
code left (none when it did not run, halted or faulted). -/
private def totalGuardSummary (f : Frame) :
    Option (Option SettledHalt × Option U256 × Bytes × Nat) :=
  match Frame.runTop f with
  | .ok r =>
    let top := match totalGuardRaw f with
      | some (.ok (.finished _ s)) => s.stack.head?
      | _ => none
    some ⟨r.error?, top, r.output, r.gasMeasure⟩
  | .error _ => none

-- Arithmetic loop: the state that exhausted `execFueled` at fuel 20 runs to a definite
-- out-of-gas result, because the seeded budget is provably sufficient.
private def totalGuardArithmeticLoop : Bool :=
  let m := totalGuardMessage [0x5B, 0x60, 0x00, 0x56] 1000 8
  match exec (totalGuardRunning m), Frame.runTop (totalGuardFrame m) with
  | .ok (.halted reason _), .ok r =>
    reason == .outOfGas .none &&
      r.error? == some (.halt (.outOfGas .none)) &&
      r.gasMeasure == 0
  | _, _ => false

#guard totalGuardArithmeticLoop

-- Nested CALL: run a parent that calls address 0x20, whose code is STOP.
private def totalGuardNestedCallMessage (depthLeft : Nat) : Message :=
  totalGuardMessage
    [ 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00,
      0x60, 0x00, 0x60, 0x20, 0x61, 0x03, 0xE8, 0xF1, 0x00 ]
    100000 depthLeft

private def totalGuardNestedCallState : State :=
  State.setCode .empty 0x20 (totalGuardCode [0x00])

#guard (totalGuardSummary (totalGuardFrame (totalGuardNestedCallMessage 8)
      totalGuardNestedCallState)).map
    (fun x => ((x.2.1, x.2.2.2) : Option U256 × Nat)) =
  some (some 1, 97379)

-- CREATE collision, reached the way a transaction reaches it: a frame executes
-- CREATE at an address that already carries code, so the child is never
-- spawned, the reserved `createGas` is not returned, and 0 is pushed.
private def totalGuardCreateCollisionCreator : Address := 0x30

private def totalGuardCreateCollision : Bool :=
  let created := computeContractAddress totalGuardCreateCollisionCreator 0
  let state := State.setCode .empty created (totalGuardCode [0x00])
  let m := totalGuardMessage [0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0xF0, 0x00] 100000 8
  let m := { m with context := { m.context with recipient := totalGuardCreateCollisionCreator } }
  match totalGuardSummary (totalGuardFrame m state) with
  | some ⟨error, top, _, measure⟩ => error == none && top == some 0 && measure == 1062
  | none => false

#guard totalGuardCreateCollision

-- Precompile dispatch is taken normally and bypassed when explicitly disabled:
-- the enabled path pays ecrecover's 3,000 gas without ever entering the driver.
private def totalGuardPrecompileMessage (disabled : Bool) : Message :=
  let m := totalGuardMessage [] 10000 8
  { m with
    context := { m.context with recipient := 1 }
    target := some 1
    codeAddress := some 1
    disablePrecompiles := disabled }

private def totalGuardPrecompileDispatch : Bool :=
  match
      Frame.runTop (totalGuardFrame (totalGuardPrecompileMessage false)),
      Frame.runTop (totalGuardFrame (totalGuardPrecompileMessage true)) with
  | .ok viaPrecomp, .ok viaCode => viaPrecomp.gasMeasure == 7000 && viaCode.gasMeasure == 10000
  | _, _ => false

#guard totalGuardPrecompileDispatch

-- Depth zero prevents spawning: the same parent that gets failure word 1 at
-- depth 8 gets 0 at depth 0, with the call never reaching the driver.
private def totalGuardDepthZero : Bool :=
  match totalGuardSummary (totalGuardFrame (totalGuardNestedCallMessage 0)
      totalGuardNestedCallState) with
  | some ⟨_, top, _, measure⟩ => top == some 0 && measure == 97379
  | none => false

#guard totalGuardDepthZero

-- A PUSH with zero gas halts through the frozen OutOfGasError channel.
private def totalGuardOutOfGas : Bool :=
  let m := totalGuardMessage [0x60, 0x01, 0x00] 0 8
  match exec (totalGuardRunning m) with
  | .ok (.halted reason _) => reason == .outOfGas .none
  | _ => false

#guard totalGuardOutOfGas

-- REVERT retains the 32-byte memory slice and becomes a settled frame result.
private def totalGuardRevert : Bool :=
  let m :=
    totalGuardMessage
      [ 0x60, 0x2A, 0x60, 0x00, 0x52,
        0x60, 0x20, 0x60, 0x00, 0xFD ]
      1000 8
  match Frame.runTop (totalGuardFrame m) with
  | .ok r =>
    r.error? == some .revert &&
      r.output.length == 32 &&
      r.output.getLast? == some 0x2A &&
      r.gasMeasure == 982
  | .error _ => false

#guard totalGuardRevert

end Jaune
