-- Check/CheckedExecution.lean : the W1 guards of `Jaune/Check/Execution.lean`, restated over the
-- Checked message call.
--
-- Check module (see `scripts/layering.json`). Goal `jaune-shape-and-names-v1`, G2b (unit jsn-u85,
-- S0): every guard of `Jaune/Check/Execution.lean` that drives a W1 definition (`Evm.step`,
-- `MessageOp.step`, `genericCreate*.step`, `genericCall.step`, `enter`, `HaltOp.run`,
-- `chargeDeposit`, `execFueled`, the delegation pricing over `Devm`) is restated here over its
-- Checked counterpart with the same observation and the same expected value. The machine a W1
-- guard built with `initDevm`/`initEvm` from a `Msg` is built here with
-- `Checked.Message.initialCheckpoint` from the corresponding `Checked.Message` (the map of
-- `Checked.TopLevel.Input.ofLegacy`). The guards of `Jaune/Check/Execution.lean` that read no W1
-- definition (decoding, gas-schedule constants) stay where they are. The default build compiles
-- this module through `JauneChecks.lean`.
import Jaune.MessageCall.CheckedDriver
import Jaune.MessageCall.CheckedParts

namespace Jaune.Checked

open Jaune

/-- The message of a guard: `Msg`'s defaults (caller and recipient 0, no value, no calldata, depth
left 1024, nothing static, an empty original state, Prague's block record) with the given code,
gas and fork. -/
private def guardMessage (code : ByteArray := .empty) (gas : Nat := 0) (depthLeft : Nat := 1024)
    (fork : Fork := .prague) : Checked.Message :=
  { context := {
      caller := 0, recipient := 0, value := 0, calldata := [], code, depthLeft, isStatic := false
      tx := { origin := 0, gasPrice := 0, blobVersionedHashes := [], originalState := .empty }
      block := { (default : BlockContext) with fork } }
    kind := .call, codeAddress := none, target := none, gas, stateGasGrant := 0
    transfersValue := false, disablePrecompiles := false }

/-- The machine a message starts on, over `state` with nothing warm (`initDevm`). -/
private def guardStart (m : Checked.Message) (state : State := .empty) : Frame.State :=
  m.initialCheckpoint ⟨state, .empty, .emptyWithCapacity⟩ .emptyWithCapacity .emptyWithCapacity
    .emptyWithCapacity .emptyWithCapacity

/-- The running frame a message starts as (`initEvm`). -/
private def guardRunning (m : Checked.Message) (state : State := .empty) : Frame.Running :=
  ⟨0, m.context, guardStart m state⟩

-- EIP-8024 `DUPN`/`SWAPN`/`EXCHANGE` (goal C, G4), stepped from real code
-- through the Checked step, so that the immediate's sizing, the zero fill past the
-- end of code, the activation check, the `VERY_LOW` charge, the decode, and
-- the stack effect are all observed together. The summary is
-- `(status, gasLeft, stack as Nats, pc)`; `"ok"` is a continued frame.
private def stackAccessGuardRunning (fork : Fork) (code : ByteArray)
    (gasLeft : Nat) (stack : List U256) : Frame.Running :=
  let m := guardMessage code 0 1024 fork
  ⟨0, m.context, ((guardStart m).withGasLeft gasLeft).withStack stack⟩

private def stackAccessGuard (fork : Fork) (code : List UInt8)
    (gasLeft : Nat) (stack : List Nat) : String × Nat × List Nat × Nat :=
  match Checked.step (stackAccessGuardRunning fork ⟨code.toArray⟩ gasLeft
      (stack.map Nat.toU256)) with
  | .ok (.next pc s) => ("ok", s.gasLeft, s.stack.map U256.toNat, pc)
  | .ok (.exit (.halted e s)) => (e.render, s.gasLeft, s.stack.map U256.toNat, 0)
  | .ok (.exit e) => ("halt-ok", e.state.gasLeft, e.state.stack.map U256.toNat, 0)
  | .ok (.spawn _ _ _) => ("spawn", 0, [], 0)
  | .error _ => ("fault", 0, [], 0)

private def guardStackOf (n : Nat) : List Nat := List.range n

-- Sizing: an accepted immediate advances the counter by two (`pc += 2`).
-- `DUPN 0x80` decodes to 17 and duplicates position 17 (index 16).
#guard stackAccessGuard .amsterdam [0xE6, 0x80] 100 (guardStackOf 17)
  = ("ok", 100 - Gas.veryLow, 16 :: guardStackOf 17, 2)
-- One item short is a stack underflow -- after the charge, as in the pinned
-- `dupn`, whose `charge_gas` precedes the length test.
#guard stackAccessGuard .amsterdam [0xE6, 0x80] 100 (guardStackOf 16)
  = ("StackUnderflowError", 100 - Gas.veryLow, guardStackOf 16, 0)
-- `DUPN 0x00` decodes to 145: 145 items suffice, 144 do not.
#guard (stackAccessGuard .amsterdam [0xE6, 0x00] 100 (guardStackOf 145)).1 = "ok"
#guard (stackAccessGuard .amsterdam [0xE6, 0x00] 100 (guardStackOf 144)).1
  = "StackUnderflowError"
-- `DUPN` as the final byte of code: the immediate is zero-filled to 0x00,
-- decoding to 145 -- a stack underflow unless 145 items are present.
#guard (stackAccessGuard .amsterdam [0xE6] 100 (guardStackOf 144)).1
  = "StackUnderflowError"
#guard (stackAccessGuard .amsterdam [0xE6] 100 (guardStackOf 145)).1 = "ok"
#guard (stackAccessGuard .amsterdam [0xE6] 100 (guardStackOf 145)).2.2.2 = 2
-- A forbidden immediate is an invalid instruction -- after the charge, since
-- the pinned `charge_gas` precedes the decode -- whatever the stack holds.
#guard stackAccessGuard .amsterdam [0xE6, 0x5B] 100 (guardStackOf 200)
  = ("InvalidOpcode", 100 - Gas.veryLow, guardStackOf 200, 0)
#guard (stackAccessGuard .amsterdam [0xE6, 0x7F] 100 (guardStackOf 200)).1 = "InvalidOpcode"
#guard (stackAccessGuard .amsterdam [0xE7, 0x5B] 100 (guardStackOf 200)).1 = "InvalidOpcode"
#guard (stackAccessGuard .amsterdam [0xE8, 0x52] 100 (guardStackOf 200)).1 = "InvalidOpcode"
#guard (stackAccessGuard .amsterdam [0xE8, 0x7F] 100 (guardStackOf 200)).1 = "InvalidOpcode"
-- Out of gas precedes the decode: with 2 gas even a forbidden immediate
-- reports the gas failure, not the immediate.
#guard (stackAccessGuard .amsterdam [0xE6, 0x5B] 2 (guardStackOf 200)).1 = "OutOfGasError"
-- `SWAPN 0x80` decodes to 17: swaps the top with position 18 (index 17); 18
-- items suffice, 17 do not.
#guard stackAccessGuard .amsterdam [0xE7, 0x80] 100 (guardStackOf 18)
  = ("ok", 100 - Gas.veryLow, ((guardStackOf 18).set 0 17).set 17 0, 2)
#guard (stackAccessGuard .amsterdam [0xE7, 0x80] 100 (guardStackOf 17)).1
  = "StackUnderflowError"
-- `EXCHANGE 0x00` decodes to `(9, 16)`: swaps positions 10 and 17 (indices 9
-- and 16); 17 items suffice, 16 do not.
#guard stackAccessGuard .amsterdam [0xE8, 0x00] 100 (guardStackOf 17)
  = ("ok", 100 - Gas.veryLow, ((guardStackOf 17).set 9 16).set 16 9, 2)
#guard (stackAccessGuard .amsterdam [0xE8, 0x00] 100 (guardStackOf 16)).1
  = "StackUnderflowError"
-- `EXCHANGE 0xFF` decodes to `(1, 22)`: indices 1 and 22, 23 items needed.
#guard stackAccessGuard .amsterdam [0xE8, 0xFF] 100 (guardStackOf 23)
  = ("ok", 100 - Gas.veryLow, ((guardStackOf 23).set 1 22).set 22 1, 2)
-- Under BPO2 the three bytes are unassigned: an invalid instruction whatever
-- the stack and gas hold, and no gas is charged.
#guard stackAccessGuard .bpo2 [0xE6, 0x80] 100 (guardStackOf 17)
  = ("InvalidOpcode", 100, guardStackOf 17, 0)
#guard (stackAccessGuard .bpo2 [0xE7, 0x80] 100 (guardStackOf 18)).1 = "InvalidOpcode"
#guard (stackAccessGuard .bpo2 [0xE8, 0x00] 0 []).1 = "InvalidOpcode"
#guard (stackAccessGuard .prague [0xE6, 0x80] 100 (guardStackOf 17)).1 = "InvalidOpcode"
-- And `SLOTNUM` from code, for the same fixture: `BASE`, the push, `pc += 1`.
#guard stackAccessGuard .amsterdam [0x4B] 100 [] = ("ok", 100 - Gas.base, [0], 1)
#guard (stackAccessGuard .bpo2 [0x4B] 100 []).1 = "InvalidOpcode"

-- S8 (EIP-1014) `CREATE2` availability (unit U5): without the fork the byte is
-- an undefined instruction whatever the stack holds; with it an empty stack
-- reaches the first pop instead (the gate passed, the stack failed).
private def guardCreate2 (fork : Fork) : MessageOp.Outcome :=
  let m := guardMessage .empty 0 1024 fork
  MessageOp.step m.context (guardStart m) .create2

#guard match guardCreate2 .byzantium with
  | .done (.error ⟨.invalidOpcode _, _⟩) => true
  | _ => false
#guard match guardCreate2 .prague with
  | .done (.error ⟨.stackUnderflow _, _⟩) => true
  | _ => false

-- S8 (EIP-3855) `PUSH0` availability (unit U5): where defined it pushes zero
-- for `BASE`; without the fork the byte is undefined and charges nothing.
#guard stackAccessGuard .shanghai [0x5F] 100 [] = ("ok", 100 - Gas.base, [0], 1)
#guard stackAccessGuard .istanbul [0x5F] 100 [] = ("InvalidOpcode", 100, [], 0)
#guard (stackAccessGuard .istanbul [0x5F] 0 []).1 = "InvalidOpcode"

/-! Focused executable checks for the Checked core. The frame-level checks (entry, run,
settlement) are in `Jaune.Check.CheckedSufficiency`. -/

private def flattenGuardCode (bytes : Bytes) : ByteArray := .mk <| .mk bytes

private def flattenGuardMessage (bytes : Bytes) (gas depthLeft : Nat) : Checked.Message :=
  guardMessage (flattenGuardCode bytes) gas depthLeft

-- Arithmetic loop: the driver spends one unit per instruction and exhausts.
private def flattenGuardArithmeticLoop : Bool :=
  let m := flattenGuardMessage [0x5B, 0x60, 0x00, 0x56] 1000 8
  (Checked.execFueled (guardRunning m) 20).run.isNone

#guard flattenGuardArithmeticLoop

-- CREATE collision: code and nonce each short-circuit with stack word 0.
private def flattenGuardCreateCollision (code : Bool) : Bool :=
  let target : Address := 0x40
  let state :=
    if code then State.setCode .empty target (flattenGuardCode [0x00])
    else State.set .empty target {nonce := 1, balance := 0, storage := .empty, code := .empty}
  let m := flattenGuardMessage [] 100000 8
  match genericCreate.step m.context (guardStart m state) 0 target 0 0 with
  | .done (.ok s) => s.stack.head? == some 0
  | _ => false

#guard flattenGuardCreateCollision true
#guard flattenGuardCreateCollision false

private def flattenGuardCreateAmsterdamCollision (code : Bool) : Bool :=
  let target : Address := 0x43
  let state :=
    if code then State.setCode .empty target (flattenGuardCode [0x00])
    else State.set .empty target {nonce := 1, balance := 0, storage := .empty, code := .empty}
  let m := { guardMessage (flattenGuardCode []) 100000 8 .amsterdam with stateGasGrant := 200000 }
  match genericCreateAmsterdam.step m.context amsterdamStateGasRules (guardStart m state)
      0 target 0 0 with
  | .done (.ok s) => s.stack.head? == some 0
  | _ => false

#guard flattenGuardCreateAmsterdamCollision true
#guard flattenGuardCreateAmsterdamCollision false

-- Storage alone admits a child in both shared CREATE helpers. CREATE2
-- reaches these same helpers through `MessageOp.step`; child entry wipes storage.
private def flattenGuardCreateStorageOnly : Bool :=
  let target : Address := 0x41
  let state := State.setStorVal .empty target 1 1
  let m := flattenGuardMessage [] 100000 8
  match genericCreate.step m.context (guardStart m state) 0 target 0 0 with
  | .spawn _ _ => true
  | _ => false

private def flattenGuardCreateAmsterdamStorageOnly : Bool :=
  let target : Address := 0x42
  let state := State.setStorVal .empty target 1 1
  let m := { guardMessage (flattenGuardCode []) 100000 8 .amsterdam with stateGasGrant := 200000 }
  match genericCreateAmsterdam.step m.context amsterdamStateGasRules (guardStart m state)
      0 target 0 0 with
  | .spawn _ _ => true
  | _ => false

#guard flattenGuardCreateStorageOnly
#guard flattenGuardCreateAmsterdamStorageOnly

-- Precompile dispatch is taken normally and bypassed when explicitly disabled.
private def flattenGuardPrecompileDispatch : Bool :=
  let m := flattenGuardMessage [] 10000 8
  let m := { m with
    context := { m.context with recipient := 1 }
    target := some 1
    codeAddress := some 1 }
  let disabled := { m with disablePrecompiles := true }
  match Checked.enter ⟨m, guardStart m⟩, Checked.enter ⟨disabled, guardStart disabled⟩ with
  | .done _, .run _ => true
  | _, _ => false

#guard flattenGuardPrecompileDispatch

-- Depth zero prevents spawning and returns failure word 0 to the caller.
private def flattenGuardDepthZero : Bool :=
  let m := flattenGuardMessage [] 100 0
  match
      genericCall.step m.context (guardStart m) 17 0
        0 0 0 false false 0 0 0 0 .empty false with
  | .done (.ok s) =>
    s.stack.head? == some 0 && s.gasLeft == 117
  | _ => false

#guard flattenGuardDepthZero

private def flattenGuardCallData
    (codeBytes : Bytes) (codeAddress : Address) (disablePrecompiles : Bool) : Option Bytes :=
  let m := flattenGuardMessage [] 100 8
  let s := (guardStart m).withMemory ⟨#[0xAA], 1, by decide⟩
  match
      genericCall.step m.context s 17 0
        0 codeAddress codeAddress false false 0 1 0 0
        (flattenGuardCode codeBytes) disablePrecompiles with
  | .spawn child _ => some child.message.context.calldata
  | _ => none

-- `genericCall.step` keeps its exact original spawned-message construction;
-- the native driver only reuses an equal calldata allocation.
#guard flattenGuardCallData [0x00] 0 false = some [0xAA]
#guard flattenGuardCallData [0x35] 0 false = some [0xAA]
#guard flattenGuardCallData [0x60, 0x35, 0x00] 0 false = some [0xAA]
#guard flattenGuardCallData [0x60, 0x35, 0x35] 0 false = some [0xAA]
#guard flattenGuardCallData [
  0x73, 0x58, 0x3a, 0xa5, 0x87, 0xd7, 0xd8, 0x52, 0xa5, 0xb8, 0x44,
  0x8c, 0xc4, 0x16, 0x05, 0x37, 0xd9, 0xbd, 0x12, 0xc8, 0x89, 0x00
] 0 false = some [0xAA]
#guard flattenGuardCallData [] 1 false = some [0xAA]
#guard flattenGuardCallData [] 1 true = some [0xAA]

/-! ### Amsterdam metering site table: CALL, CREATE and SELFDESTRUCT

The site guards of `Jaune/Check/Execution.lean` over the Checked instruction sites. The
schedule-only guards (`meteringGuardLegacySchedule` and its comparisons with Prague) read no
machine and stay there; this section's delegated-charge rows hand that schedule's numbers to the
Checked pricing functions directly. -/

private def meteringGuardGas : Nat := 1_000_000
private def meteringGuardStateGas : Nat := 1_000_000
private def meteringGuardCaller : Address := 0x1000
private def meteringGuardCallee : Address := 0x2000
private def meteringGuardDelegate : Address := 0x3000

/-- The legacy-shaped schedule of `Jaune/Check/Execution.lean` (`meteringGuardLegacySchedule`),
whose three instruction-site numbers differ from Prague's; its comparisons with Prague are
guarded there. -/
private def meteringGuardLegacySchedule : GasSchedule :=
  {pragueGasSchedule with
    coldAccountAccess := 2700
    callValue := 9100
    createAccess := 31000}

private def meteringGuardState : State := State.setBal .empty meteringGuardCaller 100

private def meteringGuardMessage (fork : Fork) (stateGasGrant : Nat) : Checked.Message :=
  let m := guardMessage .empty meteringGuardGas 8 fork
  { m with
    context := { m.context with
      caller := meteringGuardCaller
      recipient := meteringGuardCaller
      tx := { m.context.tx with originalState := meteringGuardState } }
    target := some meteringGuardCaller
    stateGasGrant }

private def meteringGuardStart
    (fork : Fork) (stateGasGrant : Nat) (stack : List U256) : Frame.State :=
  (guardStart (meteringGuardMessage fork stateGasGrant) meteringGuardState).withStack stack

private def meteringGuardCreateCharges
    (fork : Fork) (stateGasGrant : Nat) (x : MessageOp)
    (stack : List U256) : Option (Nat × Nat) :=
  let m := meteringGuardMessage fork stateGasGrant
  match MessageOp.step m.context (meteringGuardStart fork stateGasGrant stack) x with
  | .spawn child _ =>
    let parent := child.checkpoint
    some
      (meteringGuardGas - (parent.gasLeft + child.message.gas),
       stateGasGrant - (parent.stateGas.left + child.message.stateGasGrant))
  | _ => none

-- EIP-7954 (goal C, G5): the deposited-code check and both `CREATE`-family
-- memory-size checks read Amsterdam's raised limits through `rules.code`.
-- The deposit check is inclusive at 0x10000 bytes and halts with `OutOfGas`
-- one byte above; under BPO2 the same boundary sits at 0x6000.
private def codeLimitGuardDeposit (fork : Fork) (stateGasGrant : Nat)
    (size : Nat) : Option Bool :=
  match chargeDeposit (Fork.ruleSet fork) (List.replicate size (0x00 : UInt8))
      ((meteringGuardStart fork stateGasGrant []).withGasLeft 20_000_000) with
  | .ok _ => some true
  | .error ⟨.outOfGas _, _⟩ => some false
  | .error _ => none

#guard codeLimitGuardDeposit .amsterdam 200_000_000 0x10000 = some true
#guard codeLimitGuardDeposit .amsterdam 200_000_000 (0x10000 + 1) = some false
#guard codeLimitGuardDeposit .bpo2 0 0x6000 = some true
#guard codeLimitGuardDeposit .bpo2 0 (0x6000 + 1) = some false
#guard codeLimitGuardDeposit .prague 0 (0x6000 + 1) = some false
-- `CREATE` and `CREATE2` refuse an initcode above `maxInitCodeSize` before
-- spawning a child: 0x20000 bytes spawn under Amsterdam, 0x20000 + 1 halt;
-- 0xC000 + 1 already halts under BPO2. The stack is `[value, offset, size]`
-- (`[value, offset, size, salt]` for `CREATE2`), top first.
#guard (meteringGuardCreateCharges .amsterdam meteringGuardStateGas .create
  [0, 0, 0x20000]).isSome
#guard (meteringGuardCreateCharges .amsterdam meteringGuardStateGas .create
  [0, 0, 0x20000 + 1]).isNone
#guard (meteringGuardCreateCharges .amsterdam meteringGuardStateGas .create2
  [0, 0, 0x20000, 0]).isSome
#guard (meteringGuardCreateCharges .amsterdam meteringGuardStateGas .create2
  [0, 0, 0x20000 + 1, 0]).isNone
#guard (meteringGuardCreateCharges .bpo2 0 .create [0, 0, 0xC000]).isSome
#guard (meteringGuardCreateCharges .bpo2 0 .create [0, 0, 0xC000 + 1]).isNone
#guard (meteringGuardCreateCharges .bpo2 0 .create2 [0, 0, 0xC000 + 1, 0]).isNone

private def meteringGuardCallCharges
    (fork : Fork) (stateGasGrant : Nat) (x : MessageOp)
    (stack : List U256) : Option (Nat × Nat) :=
  let m := meteringGuardMessage fork stateGasGrant
  match MessageOp.step m.context (meteringGuardStart fork stateGasGrant stack) x with
  | .spawn child _ =>
    let parent := child.checkpoint
    some
      (meteringGuardGas - parent.gasLeft,
       stateGasGrant - (parent.stateGas.left + child.message.stateGasGrant))
  | _ => none

private def meteringGuardSelfdestructCharges
    (fork : Fork) (stateGasGrant : Nat) : Option (Nat × Nat × Nat) :=
  let m := meteringGuardMessage fork stateGasGrant
  let s := meteringGuardStart fork stateGasGrant [meteringGuardCallee.toU256]
  match HaltOp.run m.context s .selfdestruct with
  | .ok (.finished _ d) =>
    some
      (meteringGuardGas - d.gasLeft,
       stateGasGrant - d.stateGas.left,
       d.logs.length)
  | _ => none

-- CREATE and CREATE2 share the same zero-initcode base at both shapes.
#guard meteringGuardCreateCharges .prague 0 .create [0, 0, 0]
  = some (32000, 0)
#guard meteringGuardCreateCharges .amsterdam meteringGuardStateGas
    .create [0, 0, 0]
  = some (12000, 183600)
#guard meteringGuardCreateCharges .prague 0 .create2 [0, 0, 0, 0]
  = some (32000, 0)
#guard meteringGuardCreateCharges .amsterdam meteringGuardStateGas
    .create2 [0, 0, 0, 0]
  = some (12000, 183600)

-- A cold value-bearing CALL creates its empty recipient at both shapes. Prague
-- pays the legacy 25,000 execution surcharge; Amsterdam pays NEW_ACCOUNT in
-- the state dimension instead. CALLCODE never creates an account.
#guard meteringGuardCallCharges .prague 0 .call
    [0, meteringGuardCallee.toU256, 1, 0, 0, 0, 0]
  = some (36600, 0)
#guard meteringGuardCallCharges .amsterdam meteringGuardStateGas .call
    [0, meteringGuardCallee.toU256, 1, 0, 0, 0, 0]
  = some (14300, 183600)
#guard meteringGuardCallCharges .prague 0 .callcode
    [0, meteringGuardCallee.toU256, 1, 0, 0, 0, 0]
  = some (11600, 0)
#guard meteringGuardCallCharges .amsterdam meteringGuardStateGas
    .callcode [0, meteringGuardCallee.toU256, 1, 0, 0, 0, 0]
  = some (14300, 0)

-- A delegation designator makes both the opcode target and delegated code
-- address cold. The rows below price the delegated value-bearing (14,500) and
-- no-value (5,400) calls through the Checked schedule-carrying functions, each
-- paired with the Prague value it differs from, so a function that stopped
-- reading its schedule argument turns both halves of the pair equal and fails.
private def meteringGuardDelegationStart : Frame.State :=
  let code := (eoaDelegationMarker ++ meteringGuardDelegate.toBytes).toByteArray
  guardStart (meteringGuardMessage .prague 0)
    (meteringGuardState.setCode meteringGuardCallee code)

/-- The access-and-value charge a legacy CALL-family site computes for a
delegated target, priced by an explicit schedule: the target's own cold access,
then the delegated address's, then the value surcharge -- in the order and with
the warming the arms perform. -/
private def meteringGuardDelegatedCharge (gas : GasSchedule) (value : U256) : Nat :=
  let s := meteringGuardDelegationStart
  let pre := gas.accessCost meteringGuardCallee s.accessedAddresses
  let s := s.addAccessedAddress meteringGuardCallee
  let delegated := (Checked.GasSchedule.accessDelegation gas s meteringGuardCallee).2.2.2.1
  pre + delegated + (if value = 0 then 0 else gas.callValue)

#guard meteringGuardDelegatedCharge meteringGuardLegacySchedule 1 = 14500
#guard meteringGuardDelegatedCharge pragueGasSchedule 1 = 14200
#guard meteringGuardDelegatedCharge meteringGuardLegacySchedule 0 = 5400
#guard meteringGuardDelegatedCharge pragueGasSchedule 0 = 5200
-- The cached CALL path resolves the same delegation through `delegationCost`,
-- which prices the delegated address without warming it.
#guard (Checked.GasSchedule.delegationCost meteringGuardLegacySchedule
    meteringGuardDelegationStart meteringGuardCallee).2.2 = 2700
#guard (Checked.GasSchedule.delegationCost pragueGasSchedule
    meteringGuardDelegationStart meteringGuardCallee).2.2 = 2600

-- The no-value call variants pay only the cold account access at this input.
#guard meteringGuardCallCharges .prague 0 .delegatecall
    [0, meteringGuardCallee.toU256, 0, 0, 0, 0]
  = some (2600, 0)
#guard meteringGuardCallCharges .amsterdam meteringGuardStateGas
    .delegatecall [0, meteringGuardCallee.toU256, 0, 0, 0, 0]
  = some (3000, 0)
#guard meteringGuardCallCharges .prague 0 .staticcall
    [0, meteringGuardCallee.toU256, 0, 0, 0, 0]
  = some (2600, 0)
#guard meteringGuardCallCharges .amsterdam meteringGuardStateGas
    .staticcall [0, meteringGuardCallee.toU256, 0, 0, 0, 0]
  = some (3000, 0)

-- Design S1: under the flat (pre-EIP-2929) schedule the four legacy arms charge
-- the fixed `call` base (700, EIP-150) and no warm/cold price: the same inputs
-- as the Prague rows above, whose 2,600 cold access becomes 700. A value-bearing
-- CALL to an empty account still pays the 25,000 surcharge and the 9,000 value
-- charge.
#guard meteringGuardCallCharges .byzantium 0 .call
    [0, meteringGuardCallee.toU256, 1, 0, 0, 0, 0]
  = some (34700, 0)
#guard meteringGuardCallCharges .byzantium 0 .callcode
    [0, meteringGuardCallee.toU256, 1, 0, 0, 0, 0]
  = some (9700, 0)
#guard meteringGuardCallCharges .byzantium 0 .delegatecall
    [0, meteringGuardCallee.toU256, 0, 0, 0, 0]
  = some (700, 0)
#guard meteringGuardCallCharges .byzantium 0 .staticcall
    [0, meteringGuardCallee.toU256, 0, 0, 0, 0]
  = some (700, 0)

-- A cold sweep to a new beneficiary: Amsterdam replaces the legacy 25,000
-- execution surcharge with ACCOUNT_WRITE plus NEW_ACCOUNT state gas, and emits
-- the EIP-7708 transfer log.
#guard meteringGuardSelfdestructCharges .prague 0 = some (32600, 0, 0)
-- Design S1: the flat schedule has no cold surcharge, so the same sweep into an
-- empty beneficiary pays the 5,000 base and the 25,000 creation alone.
#guard meteringGuardSelfdestructCharges .byzantium 0 = some (30000, 0, 0)
#guard meteringGuardSelfdestructCharges .amsterdam
    meteringGuardStateGas
  = some (17000, 183600, 1)

-- A PUSH with zero gas halts through the frozen OutOfGasError channel.
private def flattenGuardOog : Bool :=
  let m := flattenGuardMessage [0x60, 0x01, 0x00] 0 8
  match (Checked.execFueled (guardRunning m) 10).run with
  | .some (.ok (.halted reason _)) => reason == .outOfGas .none
  | _ => false

#guard flattenGuardOog

-- P0.6 item 2 regressions: JUMP and JUMPI to a destination beyond the end of
-- code halt with InvalidJumpDestError through the ordinary halt channel. The
-- destination read is total; out of range is semantically `false`.
private def flattenGuardJumpOob : Bool :=
  -- PUSH1 0xFF; JUMP — destination 255 is out of range for 3 bytes of code.
  let m := flattenGuardMessage [0x60, 0xFF, 0x56] 100 8
  match (Checked.execFueled (guardRunning m) 10).run with
  | .some (.ok (.halted reason _)) => reason == .invalidJumpDest .none
  | _ => false

#guard flattenGuardJumpOob

private def flattenGuardJumpiOob : Bool :=
  -- PUSH1 0x01 (condition); PUSH1 0xFF (destination); JUMPI — taken branch,
  -- destination 255 is out of range for 5 bytes of code.
  let m := flattenGuardMessage [0x60, 0x01, 0x60, 0xFF, 0x57] 100 8
  match (Checked.execFueled (guardRunning m) 10).run with
  | .some (.ok (.halted reason _)) => reason == .invalidJumpDest .none
  | _ => false

#guard flattenGuardJumpiOob

end Jaune.Checked
