-- Check/Execution.lean : executable checks of `Jaune/Execution.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/Execution.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.Execution

namespace Jaune

open Jaune

private def rlpTags : List String :=
  [ rlpStructureTag, rlpFixedWidthTag, rlpFieldOverflow64Tag,
    rlpFieldOverflow256Tag, rlpLeadingZerosTag,
    rlpWithdrawalsNotReadTag, rlpRoundTripTag, rlpHeaderWidthTag ]

-- The tags are distinct, and none is a prefix of another, so no rendered
-- decode reason can be read as another by a `" : "`-delimited reader.
#guard rlpTags.eraseDups.length = 8
#guard rlpTags.all fun t => (rlpTags.filter fun u => t.isPrefixOf u).length = 1

/-- The reason of a failing strict decode, for the boundary guards below:
constructor identity is the discriminant now, so the guards match reasons
rather than reading rendered text back. -/
private def failsAs {α : Type} (p : DecodeError → Bool) :
    Except DecodeError α → Bool
  | .error e => p e
  | .ok _ => false

private def isFixedWidth : DecodeError → Bool
  | .fixedWidth _ => true | _ => false
private def isOverflow64 : DecodeError → Bool
  | .fieldOverflow64 _ => true | _ => false
private def isOverflow256 : DecodeError → Bool
  | .fieldOverflow256 _ => true | _ => false
private def isLeadingZeros : DecodeError → Bool
  | .leadingZeros _ => true | _ => false

-- Fixed-width fields: both the short and the long side are width errors.
#guard (Bytes.toRlpFixed "root" 32 (List.replicate 32 (0x11 : UInt8))).toOption.isSome
#guard failsAs isFixedWidth (Bytes.toRlpFixed "root" 32 (List.replicate 31 (0x11 : UInt8)))
#guard failsAs isFixedWidth (Bytes.toRlpFixed "root" 32 (List.replicate 33 (0x11 : UInt8)))
-- The renderer template for the fixed-width family, pinned end to end once.
#guard (Bytes.toRlpFixed "root" 32 (List.replicate 31 (0x11 : UInt8)))
  = .error (.fixedWidth (.text "root must be exactly 32 bytes, but is 31"))

-- 64-bit scalars: accepted widths convert exactly, nine bytes is an overflow
-- rather than a truncation, and a leading zero is a distinct reason from an
-- overflow. This is the withdrawal-index case.
#guard (Bytes.toRlpUInt64 "index" []).toOption.map UInt64.toNat = some 0
#guard (Bytes.toRlpUInt64 "index" (List.replicate 8 (0xFF : UInt8))).toOption.map UInt64.toNat
  = some (2 ^ 64 - 1)
#guard failsAs isOverflow64
  (Bytes.toRlpUInt64 "index" (0x01 :: List.replicate 8 (0x00 : UInt8)))
#guard failsAs isLeadingZeros (Bytes.toRlpUInt64 "index" [0x00, 0x01])
#guard ¬ failsAs isOverflow64 (Bytes.toRlpUInt64 "index" [0x00, 0x01])
#guard ¬ failsAs isLeadingZeros
  (Bytes.toRlpUInt64 "index" (0x01 :: List.replicate 8 (0x00 : UInt8)))

-- 256-bit scalars: same reasons, one width up, under the 256-bit overflow
-- constructor.
#guard (Bytes.toRlpU256 "amount" (List.replicate 32 (0xFF : UInt8))).toOption.map U256.toNat
  = some (2 ^ 256 - 1)
#guard failsAs isOverflow256
  (Bytes.toRlpU256 "amount" (List.replicate 33 (0x01 : UInt8)))
#guard failsAs isLeadingZeros (Bytes.toRlpU256 "amount" [0x00, 0x01])
#guard (Bytes.toRlpNat "value" 32 (List.replicate 32 (0xFF : UInt8))).toOption
  = some (2 ^ 256 - 1)
#guard failsAs isOverflow256 (Bytes.toRlpNat "value" 32 (List.replicate 33 (0x01 : UInt8)))
-- The renderer templates for both scalar families and the canonicality rule.
#guard (Bytes.toRlpUInt64 "index" (0x01 :: List.replicate 8 (0x00 : UInt8)))
  = .error (.fieldOverflow64
      (.text "index scalar is 9 bytes, exceeding its 8-byte width"))
#guard (Bytes.toRlpUInt64 "index" [0x00, 0x01])
  = .error (.leadingZeros
      (.text "index scalar 0x0001 is not canonically encoded (leading zero byte)"))

-- Addresses and optional receivers: a width error, never a silent creation.
#guard (Bytes.toRlpAddress "recipient" (List.replicate 20 (0x11 : UInt8))).toOption.isSome
#guard failsAs isFixedWidth (Bytes.toRlpAddress "recipient" (List.replicate 19 (0x11 : UInt8)))
#guard failsAs isFixedWidth (Bytes.toRlpAddress "recipient" (List.replicate 21 (0x11 : UInt8)))
#guard failsAs isFixedWidth (Bytes.toRlpAddress "recipient" [])
#guard (Bytes.toRlpReceiver "receiver" []).toOption = some none
#guard (Bytes.toRlpReceiver "receiver" (List.replicate 20 (0x11 : UInt8))).toOption.isSome
#guard failsAs isFixedWidth (Bytes.toRlpReceiver "receiver" (List.replicate 21 (0x11 : UInt8)))

-- A structure failure is its own reason, not a width or overflow one, and its
-- render is byte-for-byte the retired string helper's.
#guard DecodeError.structure "block" "expected a 4-item list"
  = .rlpStructure (.text "block : expected a 4-item list")
#guard (DecodeError.structure "block" "expected a 4-item list").render
  = "RlpStructureError : block : expected a 4-item list"

private def resumeGuardCommittedChild : Devm :=
  (default : Devm).setMach
    { (default : Devm).mach with
      stateGas := {StateGasMeter.zero with committedSpill := 1} }

private def resumeGuardUnsettledFailure : Devm :=
  ((default : Devm).setMach
    { (default : Devm).mach with
      stateGas := {StateGasMeter.zero with spilled := 1} }).withError (some .revert)

private def resumeGuardFailedCommittedSpill : Devm :=
  ((default : Devm).setMach
    { (default : Devm).mach with
      stateGas := {StateGasMeter.zero with committedSpill := 1} }).withError (some .revert)

private def resumeGuardFailedRefund : Devm :=
  ((default : Devm).withRefundCounter 1).withError (some .revert)

private def resumeGuardFailedReservoir : Devm :=
  ((default : Devm).setMach
    { (default : Devm).mach with
      stateGas := {StateGasMeter.zero with baseline := 1} }).withError (some .revert)

private def resumeGuardSettledFailure : Devm :=
  (default : Devm).withError (some .revert)

private def resumeGuardIsInvariantError : Execution → Bool
  | .error ⟨.internal (.invariant _), _⟩ => true
  | _ => false

private def resumeGuardStack : Execution → Option (List U256)
  | .ok devm => some devm.stack
  | .error _ => none

-- Both actual Amsterdam resume constructors reject a child whose committed
-- spill would otherwise disappear, and a failed child whose rollback facts do
-- not hold. Clean success and settled failure still reach incorporation.
#guard resumeGuardIsInvariantError <|
  Resume.run (.createAmsterdam amsterdamStateGasRules default 0 false)
    (.ok resumeGuardCommittedChild)
#guard resumeGuardIsInvariantError <|
  Resume.run (.callAmsterdam amsterdamStateGasRules default 0 0 false)
    (.ok resumeGuardUnsettledFailure)
#guard resumeGuardIsInvariantError <|
  Resume.run (.createAmsterdam amsterdamStateGasRules default 0 false)
    (.ok resumeGuardFailedCommittedSpill)
#guard resumeGuardIsInvariantError <|
  Resume.run (.callAmsterdam amsterdamStateGasRules default 0 0 false)
    (.ok resumeGuardFailedRefund)
#guard resumeGuardIsInvariantError <|
  Resume.run (.createAmsterdam amsterdamStateGasRules default 0 false)
    (.ok resumeGuardFailedReservoir)
#guard resumeGuardStack
    (Resume.run (.createAmsterdam amsterdamStateGasRules default 0 false) (.ok default))
      = some [0]
#guard resumeGuardStack
    (Resume.run (.callAmsterdam amsterdamStateGasRules default 0 0 false)
      (.ok resumeGuardSettledFailure)) = some [0]

-- EIP-8024 `DUPN`/`SWAPN`/`EXCHANGE` (goal C, G4), stepped from real code
-- through `getInst`, so that the immediate's sizing, the zero fill past the
-- end of code, the activation check, the `VERY_LOW` charge, the decode, and
-- the stack effect are all observed together. The summary is
-- `(status, gasLeft, stack as Nats, pc)`; `"ok"` is a continued frame.
private def stackAccessGuardEvm (fork : Fork) (code : ByteArray)
    (gasLeft : Nat) (stack : List U256) : Evm :=
  { pc := 0,
    sta := { (default : Sevm) with
      code := code,
      benvStat := { (default : BenvStat) with fork := fork } },
    dyna := ((default : Devm).withGasLeft gasLeft).withStack stack }

private def stackAccessGuard (fork : Fork) (code : List UInt8)
    (gasLeft : Nat) (stack : List Nat) : String × Nat × List Nat × Nat :=
  match Evm.step (stackAccessGuardEvm fork ⟨code.toArray⟩ gasLeft
      (stack.map Nat.toU256)) with
  | .cont pc d => ("ok", d.gasLeft, d.stack.map U256.toNat, pc)
  | .halt (.error ⟨e, d⟩) => (e.render, d.gasLeft, d.stack.map U256.toNat, 0)
  | .halt (.ok d) => ("halt-ok", d.gasLeft, d.stack.map U256.toNat, 0)
  | .spawn _ _ _ => ("spawn", 0, [], 0)

private def guardStackOf (n : Nat) : List Nat := List.range n

-- Sizing: an accepted immediate advances the counter by two (`pc += 2`).
-- `DUPN 0x80` decodes to 17 and duplicates position 17 (index 16).
#guard stackAccessGuard .amsterdam [0xE6, 0x80] 100 (guardStackOf 17)
  = ("ok", 100 - Gas.veryLow, 16 :: guardStackOf 17, 2)
#guard Gas.veryLow = 3
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
private def guardCreate2 (fork : Fork) : XStep :=
  MessageOp.step
    { (default : Sevm) with
      benvStat := { (default : BenvStat) with fork := fork } }
    default .create2

#guard match guardCreate2 .byzantium with
  | .done (.error ⟨.halt (.invalidOpcode _), _⟩) => true
  | _ => false
#guard match guardCreate2 .prague with
  | .done (.error ⟨.halt (.stackUnderflow _), _⟩) => true
  | _ => false

-- S8 (EIP-3855) `PUSH0` availability (unit U5): where defined it pushes zero
-- for `BASE`; without the fork the byte is undefined and charges nothing.
#guard stackAccessGuard .shanghai [0x5F] 100 [] = ("ok", 100 - Gas.base, [0], 1)
#guard stackAccessGuard .istanbul [0x5F] 100 [] = ("InvalidOpcode", 100, [], 0)
#guard (stackAccessGuard .istanbul [0x5F] 0 []).1 = "InvalidOpcode"

/-! Focused executable checks for the flattened core.

The frame wrappers these once also covered (`runFrame`, `executeCode`,
`processMessage`, `processCreateMessage`) are total and therefore live in
`Jaune.Sufficiency`; their checks moved with them. -/

private def flattenGuardCode (bytes : Bytes) : ByteArray := .mk <| .mk bytes

private def flattenGuardMsg (bytes : Bytes) (gas depth : Nat) : Msg :=
  {
    (default : Msg) with
    gas := gas
    code := flattenGuardCode bytes
    depth := depth
  }

-- Arithmetic loop: the driver spends one unit per instruction and exhausts.
private def flattenGuardArithmeticLoop : Bool :=
  let msg := flattenGuardMsg [0x5B, 0x60, 0x00, 0x56] 1000 8
  (execFueled (initEvm msg) 20).run.isNone

#guard flattenGuardArithmeticLoop

-- CREATE collision: code and nonce each short-circuit with stack word 0.
private def flattenGuardCreateCollision (code : Bool) : Bool :=
  let target : Address := 0x40
  let state :=
    if code then State.setCode .empty target (flattenGuardCode [0x00])
    else State.set .empty target {nonce := 1, balance := 0, storage := .empty, code := .empty}
  let msg : Msg :=
    {
      (flattenGuardMsg [] 100000 8) with
      benv := {(default : Benv) with state := state}
    }
  match
      genericCreate.step (initSevm msg) (initDevm msg)
        0 target 0 0 with
  | .done (.ok devm) => devm.stack.head? == some 0
  | _ => false

#guard flattenGuardCreateCollision true
#guard flattenGuardCreateCollision false

private def flattenGuardCreateAmsterdamCollision (code : Bool) : Bool :=
  let target : Address := 0x43
  let state :=
    if code then State.setCode .empty target (flattenGuardCode [0x00])
    else State.set .empty target {nonce := 1, balance := 0, storage := .empty, code := .empty}
  let base : Benv := default
  let msg : Msg :=
    {(flattenGuardMsg [] 100000 8) with
      benv := {base with state := state, stat := {base.stat with fork := .amsterdam}}
      stateGasGrant := 200000}
  match genericCreateAmsterdam.step (initSevm msg) amsterdamStateGasRules (initDevm msg)
      0 target 0 0 with
  | .done (.ok devm) => devm.stack.head? == some 0
  | _ => false

#guard flattenGuardCreateAmsterdamCollision true
#guard flattenGuardCreateAmsterdamCollision false

-- Storage alone admits a child in both shared CREATE helpers. CREATE2
-- reaches these same helpers through `Xinst.step`; child entry wipes storage.
private def flattenGuardCreateStorageOnly : Bool :=
  let target : Address := 0x41
  let state := State.setStorVal .empty target 1 1
  let msg : Msg :=
    {(flattenGuardMsg [] 100000 8) with benv := {(default : Benv) with state := state}}
  match genericCreate.step (initSevm msg) (initDevm msg) 0 target 0 0 with
  | .spawn _ _ => true
  | _ => false

private def flattenGuardCreateAmsterdamStorageOnly : Bool :=
  let target : Address := 0x42
  let state := State.setStorVal .empty target 1 1
  let base : Benv := default
  let msg : Msg :=
    {(flattenGuardMsg [] 100000 8) with
      benv := {base with state := state, stat := {base.stat with fork := .amsterdam}}
      stateGasGrant := 200000}
  match genericCreateAmsterdam.step (initSevm msg) amsterdamStateGasRules (initDevm msg)
      0 target 0 0 with
  | .spawn _ _ => true
  | _ => false

#guard flattenGuardCreateStorageOnly
#guard flattenGuardCreateAmsterdamStorageOnly

-- Precompile dispatch is taken normally and bypassed when explicitly disabled.
private def flattenGuardPrecompileDispatch : Bool :=
  let msg : Msg :=
    {
      (flattenGuardMsg [] 10000 8) with
      target := some 1
      currentTarget := 1
      codeAddress := some 1
    }
  let disabled := {msg with disablePrecompiles := true}
  match (Frame.ofCall msg).enter, (Frame.ofCall disabled).enter with
  | .done _, .run _ => true
  | _, _ => false

#guard flattenGuardPrecompileDispatch

-- Depth zero prevents spawning and returns failure word 0 to the caller.
private def flattenGuardDepthZero : Bool :=
  let msg := flattenGuardMsg [] 100 0
  match
      genericCall.step (initSevm msg) (initDevm msg) 17 0
        0 0 0 false false 0 0 0 0 .empty false with
  | .done (.ok devm) =>
    devm.stack.head? == some 0 && devm.gasLeft == 117
  | _ => false

#guard flattenGuardDepthZero

private def flattenGuardCallData
    (codeBytes : Bytes) (codeAddress : Address) (disablePrecompiles : Bool) : Option Bytes :=
  let msg := flattenGuardMsg [] 100 8
  let devm := (initDevm msg).withMemory ⟨#[0xAA], 1⟩
  match
      genericCall.step (initSevm msg) devm 17 0
        0 codeAddress codeAddress false false 0 1 0 0
        (flattenGuardCode codeBytes) disablePrecompiles with
  | .spawn frame _ => some frame.inner.data
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

These guards execute the instruction sites themselves against the Prague rule
shape and the Amsterdam metering vehicle. CREATE recovers its opcode charge by
adding the retained parent gas to the child grant; CALL uses a zero requested
grant, so the parent's debit is exactly the access/value site charge. The
state component similarly adds the parent and child reservoirs. -/

private def meteringGuardGas : Nat := 1_000_000
private def meteringGuardStateGas : Nat := 1_000_000
private def meteringGuardCaller : Address := 0x1000
private def meteringGuardCallee : Address := 0x2000
private def meteringGuardDelegate : Address := 0x3000

/-- A valid legacy-shaped schedule whose three inherited instruction-site
numbers deliberately differ from Prague's. These values make the charge guards
below sensitive to the schedule they are handed, even in the `stateGas = none`
lane where every fork carries `pragueGasSchedule`.

**Why this is a `GasSchedule` and no longer a `ForkRules`.** It used to be a
whole rule record, and the guards below drove `Xinst.step`/`Linst.run` on a
machine carrying it, which is how a *third* legacy-shaped record proved that
the instruction sites read the *selected* `rules.gas` rather than the globals
or a hard-wired Prague/Amsterdam pair. A machine now carries a `Fork`, so no
such record can reach a machine, and no machine-driven evaluation can make the
distinction any more: of the nine fork records the eight with `stateGas = none`
all carry `pragueGasSchedule`, and `pragueGasSchedule`'s three numbers equal
the globals by `rfl`, so on every reachable machine "reads the record" and
"reads the global" compute the same number. The three schedules the legacy lane
can distinguish are therefore exactly the ones no fork carries.

What survives here is the half that needs no machine, each row paired with
the Prague value it differs from. The 14,500 and 5,400 rows run
`GasSchedule.accessCost`, `GasSchedule.accessDelegation` and
`GasSchedule.delegationCost`, so a helper that stopped reading its schedule
argument fails there. The independent review (F-2) found that the former
31,000 row only restated this record's own `createAccess` literal and the
former 32,700 row was arithmetic over two globals and a literal field; neither
could fail for anything an instruction site does, so both were removed
(evidence-economy trim, 2026-09-23) and the CREATE and SELFDESTRUCT quantities
have **no function-level control** here.
`.createAccess` and `.callValue` are field projections, not functions, and
listing them beside three real `GasSchedule` functions is what made the earlier
wording read as stronger than it was.

The other half -- that the sites name those functions rather than the globals
beside them -- is a source condition after this change rather than an evaluation
one, and `scripts/check-rule-data-reads.sh` is **the whole of the replacement's
site coverage**. It is shown to bite twice, each in a disposable tree: on
`Xinst.step`'s legacy CALL arm reading the global that shadows `callValue`, and
on `Linst.run`'s legacy SELFDESTRUCT arm (`Jaune/Machine.lean`) reading the one
that shadows `coldAccountAccess` -- each leaves the tree green with every
`#guard` below still passing, and turns only that gate red. Its three names
cover exactly the CREATE and SELFDESTRUCT reads no row here controls.

The two globals are named here by the field they shadow rather than spelled,
because that gate's inventory is a plain identifier grep with **no comment
exemption**: prose that spells one is an occurrence like any other and has to be
classified in `scripts/rule-data-allow.txt`. That is deliberate -- a gate that
skipped comments would let a reader be told the wrong thing about which name the
interpreter uses -- and this paragraph is the first thing to have tripped it.
Goal `jaune-forks-by-construction-v1`, D-F6 (iii). -/
private def meteringGuardLegacySchedule : GasSchedule :=
  {pragueGasSchedule with
    coldAccountAccess := 2700
    callValue := 9100
    createAccess := 31000}

#guard decide meteringGuardLegacySchedule.Valid
-- The schedule differs from Prague's in exactly the three numbers the guards
-- below price, so each of those rows is a live comparison rather than a
-- restatement of Prague.
#guard meteringGuardLegacySchedule.coldAccountAccess
  ≠ pragueGasSchedule.coldAccountAccess
#guard meteringGuardLegacySchedule.callValue ≠ pragueGasSchedule.callValue
#guard meteringGuardLegacySchedule.createAccess ≠ pragueGasSchedule.createAccess

private def meteringGuardMsg (fork : Fork) (stateGasGrant : Nat) : Msg :=
  let state := State.setBal .empty meteringGuardCaller 100
  {
    (default : Msg) with
    benv := {
      (default : Benv) with
      state := state
      stat := {(default : BenvStat) with fork := fork, origState := state}
    }
    caller := meteringGuardCaller
    target := some meteringGuardCaller
    currentTarget := meteringGuardCaller
    gas := meteringGuardGas
    depth := 8
    stateGasGrant := stateGasGrant
  }

private def meteringGuardDevm
    (fork : Fork) (stateGasGrant : Nat) (stack : List U256) : Devm :=
  (initDevm (meteringGuardMsg fork stateGasGrant)).withStack stack

private def meteringGuardDelegatedMsg (fork : Fork) : Msg :=
  let code := (eoaDelegationMarker ++ meteringGuardDelegate.toBytes).toByteArray
  (meteringGuardMsg fork 0).setCode meteringGuardCallee code

private def meteringGuardDelegatedDevm
    (fork : Fork) (stack : List U256) : Devm :=
  (initDevm (meteringGuardDelegatedMsg fork)).withStack stack

private def meteringGuardResumeParent : Resume → Devm
  | .create parent _ => parent
  | .call parent _ _ => parent
  | .createAmsterdam _ parent _ _ => parent
  | .callAmsterdam _ parent _ _ _ => parent

private def meteringGuardCreateCharges
    (fork : Fork) (stateGasGrant : Nat) (x : MessageOp)
    (stack : List U256) : Option (Nat × Nat) :=
  let msg := meteringGuardMsg fork stateGasGrant
  match MessageOp.step (initSevm msg) (meteringGuardDevm fork stateGasGrant stack) x with
  | .spawn frame resume =>
    let parent := meteringGuardResumeParent resume
    some
      (meteringGuardGas - (parent.gasLeft + frame.inner.gas),
       stateGasGrant - (parent.stateGasLeft + frame.inner.stateGasGrant))
  | _ => none

-- EIP-7954 (goal C, G5): the deposited-code check and both `CREATE`-family
-- memory-size checks read Amsterdam's raised limits through `rules.code`.
-- The deposit check is inclusive at 0x10000 bytes and halts with `OutOfGas`
-- one byte above; under BPO2 the same boundary sits at 0x6000.
private def codeLimitGuardDeposit (fork : Fork) (stateGasGrant : Nat)
    (size : Nat) : Option Bool :=
  match processCreateMessage.chargeCodeGas (Fork.ruleSet fork)
      (((meteringGuardDevm fork stateGasGrant []).withGasLeft 20_000_000).withOutput
        (List.replicate size (0x00 : UInt8))) with
  | .ok _ => some true
  | .error ⟨.halt (.outOfGas _), _⟩ => some false
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
  let msg := meteringGuardMsg fork stateGasGrant
  match MessageOp.step (initSevm msg) (meteringGuardDevm fork stateGasGrant stack) x with
  | .spawn frame resume =>
    let parent := meteringGuardResumeParent resume
    some
      (meteringGuardGas - parent.gasLeft,
       stateGasGrant - (parent.stateGasLeft + frame.inner.stateGasGrant))
  | _ => none

private def meteringGuardSelfdestructCharges
    (fork : Fork) (stateGasGrant : Nat) : Option (Nat × Nat × Nat) :=
  let msg := meteringGuardMsg fork stateGasGrant
  let devm := meteringGuardDevm fork stateGasGrant [meteringGuardCallee.toU256]
  match HaltOp.run (initSevm msg) devm .selfdestruct with
  | .ok d =>
    some
      (meteringGuardGas - d.gasLeft,
       stateGasGrant - d.stateGasLeft,
       d.logs.length)
  | .error _ => none

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
-- address cold.  Every CALL-family legacy arm must charge both through the
-- selected schedule; the value-bearing arms also read its `callValue`.
--
-- The rows below price two of the quantities the retired legacy-record rows
-- priced -- 14,500 for a delegated value-bearing call and 5,400 for a
-- delegated no-value call -- but through the schedule-carrying functions
-- themselves rather than through a machine, because a machine now carries a
-- `Fork` and cannot carry these numbers. (The CREATE-base and cold-sweep rows,
-- 31,000 and 32,700, restated a definition's literal and arithmetic over
-- definitions, so they were removed; `meteringGuardLegacySchedule` says why.)
-- Each row is paired with the Prague value it differs from, so a function that
-- stopped reading its schedule argument turns both halves of the pair equal and
-- fails here.
private def meteringGuardDelegationDevm : Devm :=
  meteringGuardDelegatedDevm .prague []

/-- The access-and-value charge a legacy CALL-family site computes for a
delegated target, priced by an explicit schedule: the target's own cold access,
then the delegated address's, then the value surcharge -- in the order and with
the warming the arms perform. -/
private def meteringGuardDelegatedCharge (gas : GasSchedule) (value : U256) : Nat :=
  let devm := meteringGuardDelegationDevm
  let pre := gas.accessCost meteringGuardCallee devm.accessedAddresses
  let devm := addAccessedAddress devm meteringGuardCallee
  let delegated := (gas.accessDelegation devm meteringGuardCallee).2.2.2.1
  pre + delegated + (if value = 0 then 0 else gas.callValue)

#guard meteringGuardDelegatedCharge meteringGuardLegacySchedule 1 = 14500
#guard meteringGuardDelegatedCharge pragueGasSchedule 1 = 14200
#guard meteringGuardDelegatedCharge meteringGuardLegacySchedule 0 = 5400
#guard meteringGuardDelegatedCharge pragueGasSchedule 0 = 5200
-- The cached CALL path resolves the same delegation through `delegationCost`,
-- which prices the delegated address without warming it.
#guard (meteringGuardLegacySchedule.delegationCost
    meteringGuardDelegationDevm meteringGuardCallee).2.2 = 2700
#guard (pragueGasSchedule.delegationCost
    meteringGuardDelegationDevm meteringGuardCallee).2.2 = 2600

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
  let msg := flattenGuardMsg [0x60, 0x01, 0x00] 0 8
  match (execFueled (initEvm msg) 10).run with
  | .some (.error ⟨err, _⟩) => err == .halt (.outOfGas .none)
  | _ => false

#guard flattenGuardOog

-- P0.6 item 2 regressions: JUMP and JUMPI to a destination beyond the end of
-- code render the legacy InvalidJumpDestError through the ordinary error
-- channel, with nothing written by a host-level partial read (typed
-- construction is Step 9). The destination read is total; out of range is
-- semantically `false`.
private def flattenGuardJumpOob : Bool :=
  -- PUSH1 0xFF; JUMP — destination 255 is out of range for 3 bytes of code.
  let msg := flattenGuardMsg [0x60, 0xFF, 0x56] 100 8
  match (execFueled (initEvm msg) 10).run with
  | .some (.error ⟨err, _⟩) => err == .halt (.invalidJumpDest .none)
  | _ => false

#guard flattenGuardJumpOob

private def flattenGuardJumpiOob : Bool :=
  -- PUSH1 0x01 (condition); PUSH1 0xFF (destination); JUMPI — taken branch,
  -- destination 255 is out of range for 5 bytes of code.
  let msg := flattenGuardMsg [0x60, 0x01, 0x60, 0xFF, 0x57] 100 8
  match (execFueled (initEvm msg) 10).run with
  | .some (.error ⟨err, _⟩) => err == .halt (.invalidJumpDest .none)
  | _ => false

#guard flattenGuardJumpiOob

inductive ExpectedWorldState : Type
  | wor : State → ExpectedWorldState
  | root : U256 → ExpectedWorldState

structure Test where
  (name : String)
  (info : Lean.Json)
  (blocks : Lean.Json)
  (gbh : Lean.Json)
  (grlp : Lean.Json)
  (lbh : Lean.Json)
  (network : Lean.Json)
  (pre : Lean.Json)
  (post : ExpectedWorldState)
  (sealEngine : Lean.Json)

end Jaune

