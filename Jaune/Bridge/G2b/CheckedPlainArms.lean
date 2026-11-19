import Batteries.Tactic.OpenPrivate
import Jaune.MessageCall.CheckedStep
import Jaune.Bridge.G2b.CheckedFrame

/-!
# Bridge: the per-opcode checked arms, the old side of the family dispatch (G2b, W4 step H)

Old side: `Jaune.Checked.PlainOp.runCore`, `Jaune.Checked.PlainOp.run` and their helpers
(`unavailable`, `logStep`, `liftLog`, `sstoreBerlin`, `sstoreLegacy`, `sstoreAmsterdam`) from
`Jaune/MessageCall/CheckedPlain.lean`, and `Jaune.Checked.NextOp.step` from
`Jaune/MessageCall/CheckedStep.lean`, both at `9ce48608`. They are moved here unchanged into the
namespace `Jaune.Checked.Arms`; inside it the unchanged text resolves `PlainOp.run`,
`PlainOp.runCore` and the helpers to the old side. Both sides use `PlainOp.blockHashAt` from `Jaune.Instructions.Table`,
with the arm projecting the context the helper reads.

New side: the family dispatch (`Jaune.Checked.Family.run`, `Jaune.Checked.PlainOp.runCore`,
`Jaune.Checked.NextOp.step`). The rows' agreement lemmas against these arms are in
`Jaune.Bridge.G2b.CheckedRowAgreement` and `Jaune.Bridge.G2b.CheckedStoreAgreement`, and the cut's
bridge in `Jaune.Bridge.G2b.CheckedDispatch`. All of them go after G2b's tag.
-/

open private keccakReadRun from Jaune.Machine

namespace Jaune.Checked.Arms

open Jaune
open Jaune.Checked.PlainOp (blockHashAt)

namespace PlainOp

/-- An instruction the rules do not define halts with `invalidOpcode`, whatever the stack holds. -/
abbrev unavailable (m : Machine) : Except (ExceptionalHalt × Machine) Machine :=
  .error (.invalidOpcode .none, m)

/-- `LOG n` on the machine: pops, the charge, the static check after the charge, the read of the
data. Returns the log to append. -/
def logStep (n : Fin 5) (ctx : Jaune.CallContext) (m : Machine) :
    Except (ExceptionalHalt × Machine) (Machine × Log) := do
  let ⟨memory_start_index, m⟩ ← m.popToNat
  let ⟨size, m⟩ ← m.popToNat
  let ⟨topics, m⟩ ← m.popN n
  let extend_memory_cost := m.extCost [⟨memory_start_index, size⟩]
  let m ←
    m.chargeGas
      (Gas.log + (Gas.logData * size) + (Gas.logTopic * n) + extend_memory_cost)
  Except.assert (!ctx.isStatic) (.writeInStaticContext .none, m)
  let ⟨data, m⟩ := m.memRead memory_start_index size
  .ok (m, ⟨ctx.recipient, topics, data⟩)

/-- Lift a machine step that emits a log: the machine on both channels, the log appended on
success. -/
def liftLog (step : Machine → Except (ExceptionalHalt × Machine) (Machine × Log))
    (s : Frame.State) : Except (ExceptionalHalt × Frame.State) Frame.State :=
  match step s.machine with
  | .error (e, m) => .error (e, s.withMachine m)
  | .ok (m, log) => .ok ((s.withMachine m).addLog log)

/-- `SSTORE` under the legacy shapes (`stateGas = none`) with net metering and EIP-2929 access
(Berlin onward). -/
def sstoreBerlin (ctx : Jaune.CallContext) (s : Frame.State) :
    Except (ExceptionalHalt × Frame.State) Frame.State := do
  let rules := ctx.block.rules
  let ⟨key, s⟩ ← s.pop
  let ⟨new_value, s⟩ ← s.pop
  Except.assert (Gas.callStipend < s.gasLeft) (.outOfGas .none, s)
  let ct := ctx.recipient
  let original_value := s.originalStorageValue ctx.block.origState ct key
  -- `get_storage_original` records nothing; `get_storage` records the slot (EIP-7928).
  let s := s.recordStorageRead rules ct key
  let current_value := s.storageValue ct key
  let ⟨s, gasCost2⟩ : Frame.State × Nat :=
    if (ct, key) ∉ s.accessedStorageKeys then (s.addAccessedStorageKey ct key, Gas.coldSloadCost)
    else (s, 0)
  let gasCost3 :=
    if original_value = current_value ∧ current_value ≠ new_value then
      if original_value = 0 then gasCost2 + Gas.sstoreSetGas
      else gasCost2 + (Gas.sstoreResetGas - Gas.coldSloadCost)
    else gasCost2 + Gas.warmStorageReadCost
  let s := s.withRefund <|
    sstoreNewRefundCounter rules.gas new_value original_value current_value s.refund
  let s ← s.chargeGas gasCost3
  s.assertDynamic ctx.toChecked
  -- `set_storage` asserts `get_account_optional(address)`: an account read.
  .ok ((s.recordAccountRead rules ct).setStorageValue ct key new_value)

/-- `SSTORE` under the other legacy shapes (`stateGas = none`): Frontier to Muir Glacier. -/
def sstoreLegacy (ctx : Jaune.CallContext) (s : Frame.State) :
    Except (ExceptionalHalt × Frame.State) Frame.State := do
  let rules := ctx.block.rules
  let ⟨key, s⟩ ← s.pop
  let ⟨new_value, s⟩ ← s.pop
  -- EIP-2200's stipend sentry (Istanbul onward); vacuous before.
  Except.assert (rules.sstore.stipendSentry → Gas.callStipend < s.gasLeft) (.outOfGas .none, s)
  let ct := ctx.recipient
  let original_value := s.originalStorageValue ctx.block.origState ct key
  let s := s.recordStorageRead rules ct key
  let current_value := s.storageValue ct key
  -- Cold surcharge and warming only under EIP-2929 access.
  let ⟨s, gasCost2⟩ : Frame.State × Nat :=
    match rules.access with
    | .flat _ => (s, 0)
    | .eip2929 =>
      if ((ct, key) : Address × U256) ∉ s.accessedStorageKeys then
        (s.addAccessedStorageKey ct key, Gas.coldSloadCost)
      else (s, 0)
  let gasCost3 :=
    sstoreRegimeGasCost rules.sstore rules.access gasCost2 new_value original_value current_value
  let s := s.withRefund <|
    match rules.sstore.netMetering, rules.access with
    | false, _ =>
      sstoreLegacyRefundCounter rules.gas new_value original_value current_value s.refund
    | true, .flat g =>
      sstoreFlatRefundCounter rules.gas g.sload new_value original_value current_value s.refund
    | true, .eip2929 =>
      sstoreNewRefundCounter rules.gas new_value original_value current_value s.refund
  let s ← s.chargeGas gasCost3
  s.assertDynamic ctx.toChecked
  .ok ((s.recordAccountRead rules ct).setStorageValue ct key new_value)

/-- `SSTORE` under the Amsterdam shape (`stateGas = some state`): the static check first, an
explicit gas check, warming before the reads, and the state creation in the second dimension. -/
def sstoreAmsterdam (state : StateGasRules) (ctx : Jaune.CallContext) (s : Frame.State) :
    Except (ExceptionalHalt × Frame.State) Frame.State := do
  let rules := ctx.block.rules
  s.assertDynamic ctx.toChecked
  let ⟨key, s⟩ ← s.pop
  let ⟨new_value, s⟩ ← s.pop
  let ct := ctx.recipient
  let cold := (ct, key) ∉ s.accessedStorageKeys
  let accessGas := if cold then Gas.coldSloadCost else Gas.warmStorageReadCost
  Except.assert (max accessGas (Gas.callStipend + 1) ≤ s.gasLeft) (.outOfGas .none, s)
  let s := if cold then s.addAccessedStorageKey ct key else s
  let original_value := s.originalStorageValue ctx.block.origState ct key
  let s := s.recordStorageRead rules ct key
  let current_value := s.storageValue ct key
  let s := s.withRefund <|
    sstoreAmsterdamRefundCounter rules.gas state new_value original_value current_value s.refund
  let s := s.creditStateGasRefund
    (sstoreAmsterdamStateRefund state new_value original_value current_value)
  let s ← s.chargeGas (sstoreAmsterdamGasCost state new_value original_value current_value cold)
  let s ← s.chargeStateGas (sstoreAmsterdamStateGas state new_value original_value current_value)
  .ok ((s.recordAccountRead rules ct).setStorageValue ct key new_value)

/-- The plain instructions over the lifetime-grouped state: the successor of
`Jaune.PlainOp.runCore`. `pc` is the program counter (`PC` reads it), `ctx` what the frame reads
of its message, `s` its state. -/
def runCore (pc : Nat) (ctx : Jaune.CallContext) (s : Frame.State) :
    Jaune.PlainOp → Except (ExceptionalHalt × Frame.State) Frame.State
  /- Word family: environment pushes. -/
  | .address => s.pushItem ctx.recipient.toU256 Gas.base
  | .origin => s.pushItem ctx.tx.origin.toU256 Gas.base
  | .caller => s.pushItem ctx.caller.toU256 Gas.base
  | .callvalue => s.pushItem ctx.value Gas.base
  | .calldatasize => s.pushItem ctx.calldata.length.toU256 Gas.base
  | .codesize => s.pushItem ctx.code.size.toU256 Gas.base
  | .gasprice => s.pushItem ctx.tx.gasPrice.toU256 Gas.base
  | .returndatasize => s.pushItem s.returnData.length.toU256 Gas.base
  | .number => s.pushItem ctx.block.number.toU256 Gas.base
  | .timestamp => s.pushItem ctx.block.time Gas.base
  | .gaslimit => s.pushItem ctx.block.blockGasLimit.toU256 Gas.base
  | .prevrandao => s.pushItem ctx.block.prevRandao Gas.base
  | .coinbase => s.pushItem ctx.block.coinbase.toU256 Gas.base
  | .msize => s.pushItem s.memory.size.toU256 Gas.base
  | .pc => s.pushItem pc.toU256 Gas.base
  | .basefee => s.liftMachine fun m =>
    if ctx.block.rules.opcodes.baseFee then m.pushItem ctx.block.baseFeePerGas.toU256 Gas.base
    else unavailable m
  | .blobbasefee => s.liftMachine fun m =>
    if ctx.block.rules.opcodes.blobBaseFee then
      m.pushItem
        (getBaseFeePerBlobGas ctx.block.rules.blob ctx.block.excessBlobGas).toU256 Gas.base
    else unavailable m
  | .chainid => s.liftMachine fun m =>
    if ctx.block.rules.opcodes.chainId then m.pushItem ctx.block.chainId.toU256 Gas.base
    else unavailable m
  | .slotnum => s.liftMachine fun m =>
    if ctx.block.rules.opcodes.slotnum then
      m.pushItem ctx.block.slotNumber.toNat.toU256 Gas.base
    else unavailable m
  | .gas => s.liftMachine fun m => do
    let m ← m.chargeGas Gas.base
    m.push m.gasLeft.toU256
  /- Word family: reads of a popped operand. -/
  | .blobhash => s.liftMachine fun m =>
    if ctx.block.rules.opcodes.blobHash then do
      let ⟨x, m⟩ ← m.pop
      let y : U256 := ctx.tx.blobVersionedHashes.getD x.toNat 0
      m.chargeGas Gas.hashOpcodeGas >>= Machine.push y
    else unavailable m
  | .calldataload => s.liftMachine fun m => do
    let ⟨start_index, m⟩ ← m.pop
    let m ← m.chargeGas Gas.veryLow
    m.push (Bytes.toU256 <| ctx.calldata.sliceD start_index.toNat 32 0)
  | .blockhash => s.liftMachine fun m => do
    let ⟨blockNumberWord, m⟩ ← m.pop
    let m ← m.chargeGas Gas.blockhash
    m.push (blockHashAt ctx.toChecked blockNumberWord.toNat)
  /- Word family: arithmetic, comparison, bitwise. -/
  | .eq => s.applyBinary .eqCheck Gas.veryLow
  | .lt => s.applyBinary .ltCheck Gas.veryLow
  | .gt => s.applyBinary .gtCheck Gas.veryLow
  | .slt => s.applyBinary .sltCheck Gas.veryLow
  | .sgt => s.applyBinary .sgtCheck Gas.veryLow
  | .iszero => s.applyUnary (.eqCheck · 0) Gas.veryLow
  | .not => s.applyUnary (~~~ ·) Gas.veryLow
  | .and => s.applyBinary U256.and Gas.veryLow
  | .or => s.applyBinary U256.or Gas.veryLow
  | .xor => s.applyBinary U256.xor Gas.veryLow
  | .signextend => s.applyBinary U256.signext Gas.low
  | .byte => s.applyBinary (fun x y => (List.getD y.toBytes x.toNat 0).toU256) Gas.veryLow
  | .shl => s.liftMachine fun m =>
    if ctx.block.rules.opcodes.shifts then m.applyBinary (fun x y => y <<< x.toNat) Gas.veryLow
    else unavailable m
  | .shr => s.liftMachine fun m =>
    if ctx.block.rules.opcodes.shifts then m.applyBinary (fun x y => y >>> x.toNat) Gas.veryLow
    else unavailable m
  | .sar => s.liftMachine fun m =>
    if ctx.block.rules.opcodes.shifts then
      m.applyBinary (fun x y => U256.arithShiftRight y x.toNat) Gas.veryLow
    else unavailable m
  | .clz => s.liftMachine fun m =>
    if ctx.block.rules.opcodes.clz then
      m.applyUnary (fun x => (U256.leadingZeros x).toU256) Gas.low
    else unavailable m
  | .add => s.applyBinary (· + ·) Gas.veryLow
  | .sub => s.applyBinary (· - ·) Gas.veryLow
  | .mul => s.applyBinary (· * ·) Gas.low
  | .div => s.applyBinary (· / ·) Gas.low
  | .sdiv => s.applyBinary U256.sdiv Gas.low
  | .mod => s.applyBinary (· % ·) Gas.low
  | .smod => s.applyBinary U256.smod Gas.low
  | .addmod => s.applyTernary U256.addmod Gas.mid
  | .mulmod => s.applyTernary U256.mulmod Gas.mid
  | .exp => s.liftMachine fun m => do
    let ⟨base, m⟩ ← m.pop
    let ⟨exponent, m⟩ ← m.pop
    let m ← m.chargeGas (Gas.exp + (Gas.expByte * exponent.bytecount))
    m.push (U256.exp base exponent)
  | .pop => s.liftMachine fun m => do
    let ⟨_, m⟩ ← m.pop
    m.chargeGas Gas.base
  /- Shuffle family. -/
  | .swap n => s.liftMachine fun m => do
    let m ← m.chargeGas Gas.veryLow
    match List.swap m.stack n with
    | none => .error (.stackUnderflow .none, m)
    | some stack => .ok { m with stack }
  | .dup n => s.liftMachine fun m => do
    let m ← m.chargeGas Gas.veryLow
    match m.stack[n]? with
    | none => .error (.stackUnderflow .none, m)
    | some word => m.push word
  /- Memory family. -/
  | .mload => s.liftMachine fun m => do
    let ⟨start_index, m⟩ ← m.popToNat
    let extend_memory_cost := m.extCost [⟨start_index, 32⟩]
    let m ← m.chargeGas (Gas.veryLow + extend_memory_cost)
    let ⟨value, m⟩ := m.memRead start_index 32
    m.push (Bytes.toU256 value)
  | .mstore => s.liftMachine fun m => do
    let ⟨start_index, m⟩ ← m.popToNat
    let ⟨value, m⟩ ← m.pop
    let extend_memory_cost := m.extCost [⟨start_index, 32⟩]
    let m ← m.chargeGas (Gas.veryLow + extend_memory_cost)
    .ok (m.memWrite start_index value.toBytes)
  | .mstore8 => s.liftMachine fun m => do
    let ⟨start_index, m⟩ ← m.popToNat
    let ⟨value, m⟩ ← m.pop
    let extend_memory_cost := m.extCost [⟨start_index, 1⟩]
    let m ← m.chargeGas (Gas.veryLow + extend_memory_cost)
    .ok (m.memWrite start_index [value.2.2.toUInt8])
  | .calldatacopy => s.liftMachine fun m => do
    let ⟨memory_start_index, m⟩ ← m.popToNat
    let ⟨data_start_index, m⟩ ← m.popToNat
    let ⟨size, m⟩ ← m.popToNat
    let copy_gas_cost := Gas.copy * ceilDiv size 32
    let extend_memory_cost := m.extCost [⟨memory_start_index, size⟩]
    let m ← m.chargeGas (Gas.veryLow + copy_gas_cost + extend_memory_cost)
    .ok (m.memWrite memory_start_index (ctx.calldata.sliceD data_start_index size 0))
  | .codecopy => s.liftMachine fun m => do
    let ⟨memory_start_index, m⟩ ← m.popToNat
    let ⟨code_start_index, m⟩ ← m.popToNat
    let ⟨size, m⟩ ← m.popToNat
    let copy_gas_cost := Gas.copy * ceilDiv size 32
    let extend_memory_cost := m.extCost [⟨memory_start_index, size⟩]
    let m ← m.chargeGas (Gas.veryLow + copy_gas_cost + extend_memory_cost)
    .ok (m.memWrite memory_start_index
      (ctx.code.sliceD code_start_index size (HaltOp.toUInt8 .stop)))
  | .returndatacopy => s.liftMachine fun m => do
    let ⟨memory_start_index, m⟩ ← m.popToNat
    let ⟨return_data_start_index, m⟩ ← m.popToNat
    let ⟨size, m⟩ ← m.popToNat
    let copy_gas_cost := Gas.returnDataCopy * ceilDiv size 32
    let extend_memory_cost := m.extCost [⟨memory_start_index, size⟩]
    let m ← m.chargeGas (Gas.veryLow + copy_gas_cost + extend_memory_cost)
    if m.returnData.length < return_data_start_index + size then
      .error (.outOfBoundsRead .none, m)
    else
      .ok (m.memWrite memory_start_index (m.returnData.sliceD return_data_start_index size 0))
  | .mcopy => s.liftMachine fun m =>
    if ctx.block.rules.opcodes.mcopy then do
      let ⟨destination, m⟩ ← m.popToNat
      let ⟨source, m⟩ ← m.popToNat
      let ⟨length, m⟩ ← m.popToNat
      let copy_gas_cost := Gas.copy * ceilDiv length 32
      let extend_memory_cost := m.extCost [⟨source, length⟩, ⟨destination, length⟩]
      let m ← m.chargeGas (Gas.veryLow + copy_gas_cost + extend_memory_cost)
      let ⟨value, m⟩ := m.memRead source length
      .ok (m.memWrite destination value)
    else unavailable m
  | .keccak256 => s.liftMachine fun m => do
    let ⟨memory_start_index, m⟩ ← m.popToNat
    let ⟨size, m⟩ ← m.popToNat
    let word_gas_cost := Gas.keccak256Word * ceilDiv size 32
    let extend_memory_cost := m.extCost [⟨memory_start_index, size⟩]
    let m ← m.chargeGas (Gas.keccak256 + word_gas_cost + extend_memory_cost)
    Machine.push
      (keccakReadRun (fun j => m.memory.data.getD j 0) memory_start_index size 0
        (.replicate 25 0))
      { m with memory := m.memory.extend memory_start_index size }
  /- Log family. -/
  | .log n => liftLog (logStep n ctx) s
  /- Read family. -/
  | .balance => do
    let rules := ctx.block.rules
    let ⟨a, s⟩ ← s.popToAddress
    let warm := a ∈ s.accessedAddresses
    -- Before EIP-2929 the price is flat and the accessed set is untouched.
    let s := match rules.access with
      | .eip2929 => if warm then s else s.addAccessedAddress a
      | .flat _ => s
    let cost := match rules.access with
      | .eip2929 => if warm then Gas.warmStorageReadCost else rules.gas.coldAccountAccess
      | .flat g => g.balance
    let s ← s.chargeGas cost
    -- `get_account(address)` after the charge and before the push (EIP-7928).
    let s := s.recordAccountRead rules a
    s.push (s.balance a)
  | .extcodesize => do
    let rules := ctx.block.rules
    let ⟨adr, s⟩ ← s.popToAddress
    let gas := rules.gas
    let s ←
      match rules.access with
      | .eip2929 =>
        if adr ∈ s.accessedAddresses then
          s.chargeGas (Gas.warmStorageReadCost + gas.codeReadSurcharge)
        else (s.addAccessedAddress adr).chargeGas (gas.coldAccountAccess + gas.codeReadSurcharge)
      | .flat g => s.chargeGas (g.extCode + gas.codeReadSurcharge)
    let s := s.recordAccountRead rules adr
    s.push (s.code adr).size.toU256
  | .extcodecopy => do
    let rules := ctx.block.rules
    let ⟨adr, s⟩ ← s.popToAddress
    let ⟨memory_start_index, s⟩ ← s.popToNat
    let ⟨code_start_index, s⟩ ← s.popToNat
    let ⟨size, s⟩ ← s.popToNat
    let copy_gas_cost := Gas.copy * ceilDiv size 32
    let extend_memory_cost := s.extCost [⟨memory_start_index, size⟩]
    let gas := rules.gas
    let s ←
      match rules.access with
      | .eip2929 =>
        if adr ∈ s.accessedAddresses then
          s.chargeGas
            (Gas.warmStorageReadCost + gas.codeReadSurcharge + copy_gas_cost + extend_memory_cost)
        else
          (s.addAccessedAddress adr).chargeGas
            (gas.coldAccountAccess + gas.codeReadSurcharge + copy_gas_cost + extend_memory_cost)
      | .flat g =>
        s.chargeGas (g.extCode + gas.codeReadSurcharge + copy_gas_cost + extend_memory_cost)
    let s := s.recordAccountRead rules adr
    .ok (s.memWrite memory_start_index
      ((s.code adr).sliceD code_start_index size (HaltOp.toUInt8 .stop)))
  | .extcodehash =>
    if ctx.block.rules.opcodes.extCodeHash then do
      let rules := ctx.block.rules
      let ⟨adr, s⟩ ← s.popToAddress
      let s ←
        match rules.access with
        | .eip2929 =>
          if adr ∈ s.accessedAddresses then s.chargeGas Gas.warmStorageReadCost
          else (s.addAccessedAddress adr).chargeGas rules.gas.coldAccountAccess
        | .flat g => s.chargeGas g.extCodeHash
      let s := s.recordAccountRead rules adr
      let account := s.account adr
      s.push (if account.isEmpty then 0 else ByteArray.keccak 0 account.code.size account.code)
    else .error (.invalidOpcode .none, s)
  | .selfbalance =>
    if ctx.block.rules.opcodes.selfBalance then do
      let s ← s.chargeGas Gas.low
      (s.recordAccountRead ctx.block.rules ctx.recipient).push (s.balance ctx.recipient)
    else .error (.invalidOpcode .none, s)
  | .sload => do
    let rules := ctx.block.rules
    let ⟨key, s⟩ ← s.pop
    let ct := ctx.recipient
    let s ←
      match rules.access with
      | .eip2929 =>
        if (ct, key) ∈ s.accessedStorageKeys then s.chargeGas Gas.warmStorageReadCost
        else (s.addAccessedStorageKey ct key).chargeGas Gas.coldSloadCost
      | .flat g => s.chargeGas g.sload
    let s := s.recordStorageRead rules ct key
    s.push (s.storageValue ct key)
  | .tload =>
    if ctx.block.rules.opcodes.transient then do
      let ⟨key, s⟩ ← s.pop
      s.pushItem (s.transientValue ctx.recipient key) Gas.warmStorageReadCost
    else .error (.invalidOpcode .none, s)
  /- Store family. -/
  | .sstore =>
    match ctx.block.rules.stateGas with
    | none =>
      match ctx.block.rules.sstore, ctx.block.rules.access with
      | ⟨true, true⟩, .eip2929 => sstoreBerlin ctx s
      | _, _ => sstoreLegacy ctx s
    | some state => sstoreAmsterdam state ctx s
  | .tstore =>
    if ctx.block.rules.opcodes.transient then
      match ctx.block.rules.stateGas with
      | none => do
        let ⟨key, s⟩ ← s.pop
        let ⟨new_value, s⟩ ← s.pop
        let s ← s.chargeGas Gas.warmStorageReadCost
        s.assertDynamic ctx.toChecked
        .ok (s.setTransientValue ctx.recipient key new_value)
      | some _ => do
        -- Static execution is rejected before stack access or charging.
        s.assertDynamic ctx.toChecked
        let ⟨key, s⟩ ← s.pop
        let ⟨new_value, s⟩ ← s.pop
        let s ← s.chargeGas Gas.warmStorageReadCost
        .ok (s.setTransientValue ctx.recipient key new_value)
    else .error (.invalidOpcode .none, s)

/-- A running frame's plain instruction (the form W4 states its table over). -/
def run [LegacyTransaction] (x : Frame.Running) (op : Jaune.PlainOp) :
    Except (ExceptionalHalt × Frame.State) Frame.State :=
  runCore x.pc x.context.inLegacy x.state op

end PlainOp
/-- The operations that go on to the next instruction. -/
def NextOp.step [LegacyTransaction] (r : Frame.Running) (n : NextOp) : Step :=
  let pc := r.pc + n.size
  let rules := r.context.block.rules
  match n with
  -- S8 (EIP-3855): `PUSH0` is the empty push; without the fork the byte is an undefined
  -- instruction whatever the stack and gas hold.
  | .push xs _ =>
    if xs = [] && !rules.opcodes.push0 then
      Step.ofHalt pc (.error (.invalidOpcode .none, r.state))
    else
      let cost := if xs = [] then Gas.base else Gas.veryLow
      Step.ofHalt pc do
        let s ← r.state.chargeGas cost
        s.push xs.toU256
  | .plain op => Step.ofHalt pc (PlainOp.run r op)
  | .message x => (MessageOp.step r.context r.state x).toStep pc
  -- EIP-8024: the availability check first, then the charge before the immediate is decoded,
  -- then the decode (a forbidden immediate is an invalid instruction), then the stack.
  | .dupn imm =>
    Step.ofHalt pc <| do
      if rules.opcodes.stackAccess then
        let s ← r.state.chargeGas Gas.veryLow
        match decodeSingle imm with
        | none => .error (.invalidOpcode .none, s)
        | some n =>
          match s.stack[n - 1]? with
          | none => .error (.stackUnderflow .none, s)
          | some word => s.push word
      else
        .error (.invalidOpcode .none, r.state)
  | .swapn imm =>
    Step.ofHalt pc <| do
      if rules.opcodes.stackAccess then
        let s ← r.state.chargeGas Gas.veryLow
        match decodeSingle imm with
        | none => .error (.invalidOpcode .none, s)
        | some n =>
          match List.swap s.stack (n - 1) with
          | none => .error (.stackUnderflow .none, s)
          | some stack => .ok (s.withStack stack)
      else
        .error (.invalidOpcode .none, r.state)
  | .exchange imm =>
    Step.ofHalt pc <| do
      if rules.opcodes.stackAccess then
        let s ← r.state.chargeGas Gas.veryLow
        match decodePair imm with
        | none => .error (.invalidOpcode .none, s)
        | some (n, m) =>
          match List.exchange s.stack n m with
          | none => .error (.stackUnderflow .none, s)
          | some stack => .ok (s.withStack stack)
      else
        .error (.invalidOpcode .none, r.state)

end Jaune.Checked.Arms
