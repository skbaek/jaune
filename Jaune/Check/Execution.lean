-- Check/Execution.lean : executable checks of `Jaune/Execution.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated from `Jaune/Execution.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0); those that drove the old chain were
-- restated over the four-part message call when it was deleted (W1). The default
-- build compiles this module through `JauneChecks.lean`.
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

-- The guards of the deleted `Resume.run` that stood here are restated over `resume` and
-- `Frame.Result` in `Jaune/Check/MessageCall.lean` (goal `jaune-shape-and-names-v1`, W1).

-- EIP-8024 `DUPN`/`SWAPN`/`EXCHANGE` (goal C, G4), stepped from real code
-- through `getInst`, so that the immediate's sizing, the zero fill past the
-- end of code, the activation check, the `VERY_LOW` charge, the decode, and
-- the stack effect are all observed together. The summary is
-- `(status, gasLeft, stack as Nats, pc)`; `"ok"` is a continued frame.

private def guardStackOf (n : Nat) : List Nat := List.range n

-- Sizing: an accepted immediate advances the counter by two (`pc += 2`).
-- `DUPN 0x80` decodes to 17 and duplicates position 17 (index 16).
#guard Gas.veryLow = 3
-- One item short is a stack underflow -- after the charge, as in the pinned
-- `dupn`, whose `charge_gas` precedes the length test.
-- `DUPN 0x00` decodes to 145: 145 items suffice, 144 do not.
-- `DUPN` as the final byte of code: the immediate is zero-filled to 0x00,
-- decoding to 145 -- a stack underflow unless 145 items are present.
-- A forbidden immediate is an invalid instruction -- after the charge, since
-- the pinned `charge_gas` precedes the decode -- whatever the stack holds.
-- Out of gas precedes the decode: with 2 gas even a forbidden immediate
-- reports the gas failure, not the immediate.
-- `SWAPN 0x80` decodes to 17: swaps the top with position 18 (index 17); 18
-- items suffice, 17 do not.
-- `EXCHANGE 0x00` decodes to `(9, 16)`: swaps positions 10 and 17 (indices 9
-- and 16); 17 items suffice, 16 do not.
-- `EXCHANGE 0xFF` decodes to `(1, 22)`: indices 1 and 22, 23 items needed.
-- Under BPO2 the three bytes are unassigned: an invalid instruction whatever
-- the stack and gas hold, and no gas is charged.
-- And `SLOTNUM` from code, for the same fixture: `BASE`, the push, `pc += 1`.

-- S8 (EIP-1014) `CREATE2` availability (unit U5): without the fork the byte is
-- an undefined instruction whatever the stack holds; with it an empty stack
-- reaches the first pop instead (the gate passed, the stack failed).

-- S8 (EIP-3855) `PUSH0` availability (unit U5): where defined it pushes zero
-- for `BASE`; without the fork the byte is undefined and charges nothing.

/-! Focused executable checks for the flattened core.

The frame-level checks (entry, run, settlement) are in `Jaune.Check.Sufficiency`, over the
four-part message call. -/

private def flattenGuardCode (bytes : Bytes) : ByteArray := .mk <| .mk bytes

-- Arithmetic loop: the driver spends one unit per instruction and exhausts.

-- CREATE collision: code and nonce each short-circuit with stack word 0.

-- Storage alone admits a child in both shared CREATE helpers. CREATE2
-- reaches these same helpers through `MessageOp.step`; child entry wipes storage.

-- Precompile dispatch is taken normally and bypassed when explicitly disabled.

-- Depth zero prevents spawning and returns failure word 0 to the caller.

-- `genericCall.step` keeps its exact original spawned-message construction;
-- the native driver only reuses an equal calldata allocation.

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
whole rule record, and the guards below drove `MessageOp.step`/`HaltOp.run` on a
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
`MessageOp.step`'s legacy CALL arm reading the global that shadows `callValue`, and
on `HaltOp.run`'s legacy SELFDESTRUCT arm (`Jaune/Machine.lean`) reading the one
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

-- EIP-7954 (goal C, G5): the deposited-code check and both `CREATE`-family
-- memory-size checks read Amsterdam's raised limits through `rules.code`.
-- The deposit check is inclusive at 0x10000 bytes and halts with `OutOfGas`
-- one byte above; under BPO2 the same boundary sits at 0x6000.

-- `CREATE` and `CREATE2` refuse an initcode above `maxInitCodeSize` before
-- spawning a child: 0x20000 bytes spawn under Amsterdam, 0x20000 + 1 halt;
-- 0xC000 + 1 already halts under BPO2. The stack is `[value, offset, size]`
-- (`[value, offset, size, salt]` for `CREATE2`), top first.

-- CREATE and CREATE2 share the same zero-initcode base at both shapes.

-- A cold value-bearing CALL creates its empty recipient at both shapes. Prague
-- pays the legacy 25,000 execution surcharge; Amsterdam pays NEW_ACCOUNT in
-- the state dimension instead. CALLCODE never creates an account.

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

-- The cached CALL path resolves the same delegation through `delegationCost`,
-- which prices the delegated address without warming it.

-- The no-value call variants pay only the cold account access at this input.

-- Design S1: under the flat (pre-EIP-2929) schedule the four legacy arms charge
-- the fixed `call` base (700, EIP-150) and no warm/cold price: the same inputs
-- as the Prague rows above, whose 2,600 cold access becomes 700. A value-bearing
-- CALL to an empty account still pays the 25,000 surcharge and the 9,000 value
-- charge.

-- A cold sweep to a new beneficiary: Amsterdam replaces the legacy 25,000
-- execution surcharge with ACCOUNT_WRITE plus NEW_ACCOUNT state gas, and emits
-- the EIP-7708 transfer log.
-- Design S1: the flat schedule has no cold surcharge, so the same sweep into an
-- empty beneficiary pays the 5,000 base and the 25,000 creation alone.

-- A PUSH with zero gas halts through the frozen OutOfGasError channel.

-- P0.6 item 2 regressions: JUMP and JUMPI to a destination beyond the end of
-- code render the legacy InvalidJumpDestError through the ordinary error
-- channel, with nothing written by a host-level partial read (typed
-- construction is Step 9). The destination read is total; out of range is
-- semantically `false`.

inductive ExpectedWorldState : Type
  | worldState : State → ExpectedWorldState
  | root : U256 → ExpectedWorldState

structure Test where
  (name : String)
  (info : Lean.Json)
  (blocks : Lean.Json)
  (genesisBlockHeader : Lean.Json)
  (genesisRlp : Lean.Json)
  (lastBlockHash : Lean.Json)
  (network : Lean.Json)
  (pre : Lean.Json)
  (post : ExpectedWorldState)
  (sealEngine : Lean.Json)

end Jaune

