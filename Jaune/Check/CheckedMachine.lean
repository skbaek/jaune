-- Check/CheckedMachine.lean : the W1 instruction guards of `Jaune/Check/Machine.lean`, restated
-- over the Checked plain instructions.
--
-- Check module (see `scripts/layering.json`). Goal `jaune-shape-and-names-v1`, G2b (unit jsn-u87,
-- S0): the guards of `Jaune/Check/Machine.lean` that run the W1 `PlainOp.runCore` over a `Devm`
-- and a `Sevm` (`CLZ`, `SLOTNUM`, the S1 access shape, the S8 opcode availability rows) are
-- restated here over `Checked.PlainOp.runCore` with the same observations and expected values.
-- The W1 machine `(default : Devm)` with the given gas and stack is the empty Checked frame state
-- with that gas and stack; the W1 `Sevm` of `guardSevmAt fork` is the call context of `Sevm`'s
-- defaults (caller and recipient 0, no value, no calldata, no code, depth left 1024, nothing
-- static, an empty original state) over `BenvStat`'s default block record with the given fork.
-- The guards of `Jaune/Check/Machine.lean` that read no W1 definition stay where they are; its
-- transaction-boundary regression (`origStateRegressionOrigVals`) is restated over
-- `Checked.Transaction.prepare` in `Jaune.Check.CheckedBody`. The default build compiles this
-- module through `JauneChecks.lean`.
import Jaune.MessageCall.CheckedPlain

namespace Jaune.Checked

open Jaune

/-- `BenvStat`'s default block record under `fork`, with the given slot number. -/
private def machineGuardBlock (fork : Fork) (slot : UInt64 := 0) : BlockContext :=
  { fork, chainId := 0, gasLimit := 0, blockHashes := [], coinbase := 0, number := 0
    baseFeePerGas := 0, timestamp := 0, prevRandao := 0, excessBlobGas := 0
    parentBeaconBlockRoot := 0, slotNumber := slot }

/-- `guardSevmAt fork`: `Sevm`'s defaults over the block record of `fork`. -/
private def machineGuardContext (fork : Fork) (slot : UInt64 := 0) : CallContext :=
  { caller := 0, recipient := 0, value := 0, calldata := [], code := .empty, depthLeft := 1024
    isStatic := false
    tx := { origin := 0, gasPrice := 0, blobVersionedHashes := [], originalState := .empty }
    block := machineGuardBlock fork slot }

/-- `((default : Devm).withGasLeft gasLeft).withStack stack`. -/
private def machineGuardState (gasLeft : Nat) (stack : List U256) : Frame.State :=
  { machine := { stack, memory := .empty, gasLeft, returnData := [] }
    world := ⟨.empty, .empty, .emptyWithCapacity⟩
    substate := { logs := [], refund := 0, selfDestructs := .emptyWithCapacity
                  accessedAddresses := .emptyWithCapacity
                  accessedStorageKeys := .emptyWithCapacity }
    trail := { createdAccounts := .emptyWithCapacity } }

private abbrev MachineGuardRun := Except (ExceptionalHalt × Frame.State) Frame.State

private def guardClz (fork : Fork) (gasLeft : Nat) (stack : List U256) : MachineGuardRun :=
  PlainOp.runCore 0 (machineGuardContext fork) (machineGuardState gasLeft stack) .clz

private def guardClzErr (e : MachineGuardRun) : String :=
  match e with
  | .error ⟨err, _⟩ => err.render
  | .ok _ => "unexpected success"

private def guardStack (e : MachineGuardRun) : Option (List U256) :=
  e.toOption.map Frame.State.stack

private def guardGasLeft (e : MachineGuardRun) : Option Nat :=
  e.toOption.map Frame.State.gasLeft

-- EIP-7939 `CLZ`. Under Osaka the opcode pops one word, charges `LOW`, and pushes the count.
#guard guardStack (guardClz .osaka 100 [0]) = some [Nat.toU256 256]
#guard guardStack (guardClz .osaka 100 [1]) = some [Nat.toU256 255]
#guard guardStack (guardClz .osaka 100 [U256.max]) = some [Nat.toU256 0]
#guard guardGasLeft (guardClz .osaka 100 [0]) = some (100 - Gas.low)
-- The rest of the stack is untouched and only the top word is consumed.
#guard guardStack (guardClz .osaka 100 [0, 7]) = some [Nat.toU256 256, Nat.toU256 7]
-- Under Prague 0x1E is an unassigned byte: an invalid instruction whatever the stack and gas
-- hold.
#guard guardClzErr (guardClz .prague 100 [0]) = "InvalidOpcode"
#guard guardClzErr (guardClz .prague 100 []) = "InvalidOpcode"
#guard guardClzErr (guardClz .prague 0 [0]) = "InvalidOpcode"

-- EIP-7843 `SLOTNUM` (goal C, G3): under Amsterdam it charges `BASE` (2) and pushes the block's
-- slot number zero-extended to 256 bits; under BPO2 the byte 0x4B is unassigned.
private def guardSlotnum (fork : Fork) (slot : UInt64) (gasLeft : Nat) (stack : List U256) :
    MachineGuardRun :=
  PlainOp.runCore 0 (machineGuardContext fork slot) (machineGuardState gasLeft stack) .slotnum

#guard guardStack (guardSlotnum .amsterdam 12345 100 []) = some [Nat.toU256 12345]
#guard guardGasLeft (guardSlotnum .amsterdam 12345 100 []) = some (100 - Gas.base)
#guard guardStack (guardSlotnum .amsterdam (2 ^ 64 - 1) 100 [7])
  = some [Nat.toU256 (2 ^ 64 - 1), Nat.toU256 7]
#guard guardGasLeft (guardSlotnum .amsterdam 0 2 []) = some 0
#guard guardClzErr (guardSlotnum .amsterdam 12345 1 []) = "OutOfGasError"
#guard guardClzErr (guardSlotnum .bpo2 12345 100 []) = "InvalidOpcode"
#guard guardClzErr (guardSlotnum .bpo2 12345 0 []) = "InvalidOpcode"
#guard guardClzErr (guardSlotnum .prague 0 100 [1]) = "InvalidOpcode"

-- Under Osaka the same two degenerate inputs reach the real failures instead.
#guard guardClzErr (guardClz .osaka 100 []) = "StackUnderflowError"
#guard guardClzErr (guardClz .osaka (Gas.low - 1) [0]) = "OutOfGasError"
#guard guardGasLeft (guardClz .osaka Gas.low [0]) = some 0

/-! Design S1: the access shape at the account- and slot-access arms. Under the flat
(pre-EIP-2929) schedule each family charges its own fixed price and leaves the accessed sets
untouched; under EIP-2929 the same arm charges the cold price and records the access. -/
private def guardAccess (fork : Fork) (r : Jaune.PlainOp) (stack : List U256) :
    MachineGuardRun :=
  PlainOp.runCore 0 (machineGuardContext fork) (machineGuardState 10000 stack) r

private def guardAccessCharge (fork : Fork) (r : Jaune.PlainOp) (stack : List U256) :
    Option Nat :=
  (guardAccess fork r stack).toOption.map (10000 - ·.gasLeft)

private def guardAccessWarmed (fork : Fork) (r : Jaune.PlainOp) (x : U256) : Option Bool :=
  (guardAccess fork r [x]).toOption.map fun s =>
    decide (x.toAddress ∈ s.substate.accessedAddresses) ||
      decide (((machineGuardContext fork).recipient, x) ∈ s.substate.accessedStorageKeys)

#guard guardAccessCharge .byzantium .balance [0x1000] = some 400
#guard guardAccessCharge .istanbul .balance [0x1000] = some 700
#guard guardAccessCharge .prague .balance [0x1000] = some 2600
#guard guardAccessCharge .byzantium .extcodesize [0x1000] = some 700
#guard guardAccessCharge .prague .extcodesize [0x1000] = some 2600
#guard guardAccessCharge .petersburg .extcodehash [0x1000] = some 400
#guard guardAccessCharge .istanbul .extcodehash [0x1000] = some 700
#guard guardAccessCharge .prague .extcodehash [0x1000] = some 2600
#guard guardAccessCharge .byzantium .sload [7] = some 200
#guard guardAccessCharge .istanbul .sload [7] = some 800
#guard guardAccessCharge .prague .sload [7] = some 2100
-- `EXTCODECOPY` of zero bytes: the access price alone.
#guard guardAccessCharge .byzantium .extcodecopy [0x1000, 0, 0, 0] = some 700
#guard guardAccessCharge .prague .extcodecopy [0x1000, 0, 0, 0] = some 2600
-- The flat shape records nothing; EIP-2929 records the cold access.
#guard guardAccessWarmed .byzantium .balance 0x1000 = some false
#guard guardAccessWarmed .prague .balance 0x1000 = some true
#guard guardAccessWarmed .byzantium .extcodesize 0x1000 = some false
#guard guardAccessWarmed .prague .extcodesize 0x1000 = some true
#guard guardAccessWarmed .istanbul .extcodehash 0x1000 = some false
#guard guardAccessWarmed .prague .extcodehash 0x1000 = some true
#guard guardAccessWarmed .byzantium .sload 7 = some false
#guard guardAccessWarmed .prague .sload 7 = some true

-- S8 opcode availability (unit U5): each of the eleven `OpcodeRules` flags gates its opcodes.
-- Under rules without the fork the byte is an invalid instruction whatever the stack and gas
-- hold; under Prague each runs its Prague body.
private def guardRinst (fork : Fork) (gasLeft : Nat) (stack : List U256) (r : Jaune.PlainOp) :
    MachineGuardRun :=
  PlainOp.runCore 0 (machineGuardContext fork) (machineGuardState gasLeft stack) r

-- EIP-145 shifts: Byzantium has none of them.
#guard guardClzErr (guardRinst .byzantium 100 [1, 7] .shl) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 100 [1, 7] .shr) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 100 [1, 7] .sar) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 100 [] .shl) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 0 [1, 7] .shl) = "InvalidOpcode"
-- Under Prague each shifts: the top word is the shift amount.
#guard guardStack (guardRinst .prague 100 [1, 7] .shl) = some [Nat.toU256 14]
#guard guardStack (guardRinst .prague 100 [1, 7] .shr) = some [Nat.toU256 3]
#guard guardStack (guardRinst .prague 100 [1, 7] .sar) = some [Nat.toU256 3]
#guard guardGasLeft (guardRinst .prague 100 [1, 7] .shl) = some (100 - Gas.veryLow)
-- EIP-1052 `EXTCODEHASH`, EIP-1344 `CHAINID`, EIP-1884 `SELFBALANCE`, EIP-3198 `BASEFEE`.
#guard guardClzErr (guardRinst .byzantium 100000 [27] .extcodehash) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 100 [] .chainid) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 100 [] .selfbalance) = "InvalidOpcode"
#guard guardClzErr (guardRinst .byzantium 100 [] .basefee) = "InvalidOpcode"
#guard guardStack (guardRinst .prague 100000 [27] .extcodehash) = some [Nat.toU256 0]
#guard guardStack (guardRinst .prague 100 [] .chainid) = some [Nat.toU256 0]
#guard guardStack (guardRinst .prague 100 [] .selfbalance) = some [Nat.toU256 0]
#guard guardStack (guardRinst .prague 100 [] .basefee) = some [Nat.toU256 0]
-- EIP-4844 `BLOBHASH`/`BLOBBASEFEE`: Cancun only.
#guard guardClzErr (guardRinst .shanghai 100 [5] .blobhash) = "InvalidOpcode"
#guard guardClzErr (guardRinst .shanghai 100 [] .blobbasefee) = "InvalidOpcode"
#guard guardStack (guardRinst .prague 100 [5] .blobhash) = some [Nat.toU256 0]
#guard guardGasLeft (guardRinst .prague 100 [5] .blobhash) = some (100 - Gas.hashOpcodeGas)
#guard (guardRinst .prague 100 [] .blobbasefee).toOption.isSome = true
-- EIP-1153 transient storage and EIP-5656 `MCOPY`: Cancun only.
#guard guardClzErr (guardRinst .shanghai 100 [7] .tload) = "InvalidOpcode"
#guard guardClzErr (guardRinst .shanghai 100 [7, 8] .tstore) = "InvalidOpcode"
#guard guardClzErr (guardRinst .shanghai 100 [0, 0, 0] .mcopy) = "InvalidOpcode"
#guard guardStack (guardRinst .prague 100 [7] .tload) = some [Nat.toU256 0]
#guard guardStack (guardRinst .prague 100 [7, 8] .tstore) = some []
#guard (guardRinst .prague 100000 [0, 0, 32] .mcopy).toOption.isSome = true

end Jaune.Checked
