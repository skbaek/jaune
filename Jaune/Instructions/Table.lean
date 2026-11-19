import Jaune.Instructions.Word
import Jaune.Instructions.Shuffle
import Jaune.Instructions.Push
import Jaune.Instructions.Memory
import Jaune.Instructions.Log
import Jaune.Instructions.Read
import Jaune.Instructions.Store

/-! The instruction table (goal `jaune-shape-and-names-v1`, S4; W4 design note §3.7).

Every plain instruction belongs to one family, and its row is data: the table `PlainOp.family`
gives each constructor its family and row, one line per constructor. `Family.run`
(`Jaune.MessageCall.CheckedPlain`) is the one step each family's rows are read by. The
per-family tables (`PlainOp.wordRow?` and the others) are projections of this one table, so a
row is written once.

The classes S4 leaves out are not plain instructions: jumps (`JumpOp`), halts (`HaltOp`) and the
frame-opening message operations (`MessageOp`) keep explicit equations
(`Jaune.MessageCall.CheckedControl`, `Jaune.MessageCall.CheckedMessageOps`). Among the
non-message operations, `NextOp.family?` gives `PUSH0`–`PUSH32` their Word row and `DUPN`,
`SWAPN` and `EXCHANGE` their Shuffle rows. -/

namespace Jaune.Checked

open Jaune

namespace PlainOp

/-- `BLOCKHASH`'s word: zero outside the last 256 blocks. -/
def blockHashAt (ctx : CallContext) (blockNumber : Nat) : U256 :=
  if ctx.block.number ≤ blockNumber ∨ blockNumber + 256 < ctx.block.number then 0
  else ctx.block.blockHashes.getD (ctx.block.blockHashes.length - (ctx.block.number - blockNumber)) 0

end PlainOp

/-- The two Store rows: `SSTORE` (persistent storage) and `TSTORE` (transient storage). Their rows
are functions of the rule set (`SstoreRow.ofRules`, `TstoreRow.ofRules`), so the table names the
kind and the step instantiates the row. -/
inductive StoreKind where
  | persistent
  | transient
deriving DecidableEq, Repr

/-- The families of S4, each with its row type. -/
inductive Family where
  | word (row : WordRow)
  | shuffle (row : ShuffleRow)
  | memory (row : MemoryRow)
  | log (row : LogRow)
  | read (row : ReadRow)
  | store (kind : StoreKind)

/-- The instruction table: each plain instruction's family and row. -/
def PlainOp.family : Jaune.PlainOp → Family
  /- Word family. -/
  | .address => .word (.context Gas.base fun v => v.context.recipient.toU256)
  | .origin => .word (.context Gas.base fun v => v.context.tx.origin.toU256)
  | .caller => .word (.context Gas.base fun v => v.context.caller.toU256)
  | .callvalue => .word (.context Gas.base fun v => v.context.value)
  | .calldatasize => .word (.context Gas.base fun v => v.context.calldata.length.toU256)
  | .codesize => .word (.context Gas.base fun v => v.context.code.size.toU256)
  | .gasprice => .word (.context Gas.base fun v => v.context.tx.gasPrice.toU256)
  | .returndatasize => .word (.context Gas.base fun v => v.returnData.length.toU256)
  | .number => .word (.context Gas.base fun v => v.context.block.number.toU256)
  | .timestamp => .word (.context Gas.base fun v => v.context.block.timestamp)
  | .gaslimit => .word (.context Gas.base fun v => v.context.block.gasLimit.toU256)
  | .prevrandao => .word (.context Gas.base fun v => v.context.block.prevRandao)
  | .coinbase => .word (.context Gas.base fun v => v.context.block.coinbase.toU256)
  | .msize => .word (.context Gas.base fun v => v.memorySize.toU256)
  | .pc => .word (.context Gas.base fun v => v.pc.toU256)
  | .basefee => .word { WordRow.context Gas.base (fun v => v.context.block.baseFeePerGas.toU256) with
      available := OpcodeRules.baseFee }
  | .blobbasefee => .word { WordRow.context Gas.base (fun v =>
      (getBaseFeePerBlobGas v.context.block.rules.blob v.context.block.excessBlobGas).toU256) with
      available := OpcodeRules.blobBaseFee }
  | .chainid => .word { WordRow.context Gas.base (fun v => v.context.block.chainId.toU256) with
      available := OpcodeRules.chainId }
  | .slotnum => .word { WordRow.context Gas.base (fun v => v.context.block.slotNumber.toNat.toU256) with
      available := OpcodeRules.slotnum }
  | .gas => .word (.context Gas.base fun v => v.gasLeft.toU256)
  | .blobhash => .word {
      available := OpcodeRules.blobHash, arity := 1, cost := fun _ => Gas.hashOpcodeGas,
      result := some fun x v => v.context.tx.blobVersionedHashes.getD x.toNat 0 }
  | .calldataload => .word {
      arity := 1, cost := fun _ => Gas.veryLow,
      result := some fun x v => Bytes.toU256 (v.context.calldata.sliceD x.toNat 32 0) }
  | .blockhash => .word {
      arity := 1, cost := fun _ => Gas.blockhash,
      result := some fun x v => PlainOp.blockHashAt v.context x.toNat }
  | .eq => .word (.binary .eqCheck Gas.veryLow)
  | .lt => .word (.binary .ltCheck Gas.veryLow)
  | .gt => .word (.binary .gtCheck Gas.veryLow)
  | .slt => .word (.binary .sltCheck Gas.veryLow)
  | .sgt => .word (.binary .sgtCheck Gas.veryLow)
  | .iszero => .word (.unary (.eqCheck · 0) Gas.veryLow)
  | .not => .word (.unary (~~~ ·) Gas.veryLow)
  | .and => .word (.binary U256.and Gas.veryLow)
  | .or => .word (.binary U256.or Gas.veryLow)
  | .xor => .word (.binary U256.xor Gas.veryLow)
  | .signextend => .word (.binary U256.signext Gas.low)
  | .byte => .word (.binary (fun x y => (List.getD y.toBytes x.toNat 0).toU256) Gas.veryLow)
  | .add => .word (.binary (· + ·) Gas.veryLow)
  | .sub => .word (.binary (· - ·) Gas.veryLow)
  | .mul => .word (.binary (· * ·) Gas.low)
  | .div => .word (.binary (· / ·) Gas.low)
  | .sdiv => .word (.binary U256.sdiv Gas.low)
  | .mod => .word (.binary (· % ·) Gas.low)
  | .smod => .word (.binary U256.smod Gas.low)
  | .addmod => .word (.ternary U256.addmod Gas.mid)
  | .mulmod => .word (.ternary U256.mulmod Gas.mid)
  | .shl => .word { WordRow.binary (fun x y => y <<< x.toNat) Gas.veryLow with available := OpcodeRules.shifts }
  | .shr => .word { WordRow.binary (fun x y => y >>> x.toNat) Gas.veryLow with available := OpcodeRules.shifts }
  | .sar => .word { WordRow.binary (fun x y => U256.arithShiftRight y x.toNat) Gas.veryLow with
      available := OpcodeRules.shifts }
  | .clz => .word { WordRow.unary (fun x => (U256.leadingZeros x).toU256) Gas.low with
      available := OpcodeRules.clz }
  | .exp => .word {
      arity := 2, cost := fun (_, exponent) => Gas.exp + Gas.expByte * exponent.bytecount,
      result := some fun (base, exponent) _ => U256.exp base exponent }
  | .pop => .word { arity := 1, cost := fun _ => Gas.base, result := none }
  /- Shuffle family. -/
  | .dup n => .shuffle { shuffle := some (.dup n.val) }
  | .swap n => .shuffle { shuffle := some (.swap n.val) }
  /- Memory family. -/
  | .mload => .memory { arity := 1, effect := .load, base := fun _ => Gas.veryLow }
  | .mstore => .memory { arity := 2, effect := .storeWord, base := fun _ => Gas.veryLow }
  | .mstore8 => .memory { arity := 2, effect := .storeByte, base := fun _ => Gas.veryLow }
  | .calldatacopy => .memory {
      arity := 3, effect := .copy .calldata,
      base := fun (_, _, n) => Gas.veryLow + Gas.copy * ceilDiv n.toNat 32 }
  | .codecopy => .memory {
      arity := 3, effect := .copy .code,
      base := fun (_, _, n) => Gas.veryLow + Gas.copy * ceilDiv n.toNat 32 }
  | .returndatacopy => .memory {
      arity := 3, effect := .copy .returnData,
      base := fun (_, _, n) => Gas.veryLow + Gas.returnDataCopy * ceilDiv n.toNat 32 }
  | .mcopy => .memory {
      available := OpcodeRules.mcopy, arity := 3, effect := .move,
      base := fun (_, _, n) => Gas.veryLow + Gas.copy * ceilDiv n.toNat 32 }
  | .keccak256 => .memory {
      arity := 2, effect := .digest,
      base := fun (_, n) => Gas.keccak256 + Gas.keccak256Word * ceilDiv n.toNat 32 }
  /- Log family. -/
  | .log n => .log { topics := n }
  /- Read family. -/
  | .balance => .read {
      target := .account,
      price := .account (fun _ => Gas.warmStorageReadCost) (fun r => r.gas.coldAccountAccess)
        (fun _ g => g.balance),
      result := .push fun _ w a => (Jaune.State.get w.state a).balance }
  | .extcodesize => .read {
      target := .account,
      price := .account (fun r => Gas.warmStorageReadCost + r.gas.codeReadSurcharge)
        (fun r => r.gas.coldAccountAccess + r.gas.codeReadSurcharge)
        (fun r g => g.extCode + r.gas.codeReadSurcharge),
      result := .push fun _ w a => (Jaune.State.get w.state a).code.size.toU256 }
  | .extcodecopy => .read {
      target := .account,
      price := .account (fun r => Gas.warmStorageReadCost + r.gas.codeReadSurcharge)
        (fun r => r.gas.coldAccountAccess + r.gas.codeReadSurcharge)
        (fun r g => g.extCode + r.gas.codeReadSurcharge),
      result := .copyCode Gas.copy }
  | .extcodehash => .read {
      available := OpcodeRules.extCodeHash, target := .account,
      price := .account (fun _ => Gas.warmStorageReadCost) (fun r => r.gas.coldAccountAccess)
        (fun _ g => g.extCodeHash),
      result := .push fun _ w a =>
        let account := Jaune.State.get w.state a
        if account.isEmpty then 0 else ByteArray.keccak 0 account.code.size account.code }
  | .selfbalance => .read {
      available := OpcodeRules.selfBalance, target := .recipient, price := .fixed Gas.low,
      result := .push fun ctx w _ => (Jaune.State.get w.state ctx.recipient).balance }
  | .sload => .read {
      target := .slot,
      price := .slot (fun _ => Gas.warmStorageReadCost) (fun _ => Gas.coldSloadCost)
        (fun _ g => g.sload),
      result := .push fun ctx w k => (Jaune.State.get w.state ctx.recipient).storage.get k }
  | .tload => .read {
      available := OpcodeRules.transient, target := .transient,
      price := .fixed Gas.warmStorageReadCost,
      result := .push fun ctx w k => (w.transientStorage.getD ctx.recipient .empty).get k }
  /- Store family. -/
  | .sstore => .store .persistent
  | .tstore => .store .transient

/-- Word instructions read their operands and a view of the running frame. -/
def PlainOp.wordRow? (op : Jaune.PlainOp) : Option WordRow :=
  match PlainOp.family op with
  | .word row => some row
  | _ => none

/-- `DUP1`–`DUP16` and `SWAP1`–`SWAP16`. -/
def PlainOp.shuffleRow? (op : Jaune.PlainOp) : Option ShuffleRow :=
  match PlainOp.family op with
  | .shuffle row => some row
  | _ => none

/-- The Memory table. -/
def PlainOp.memoryRow? (op : Jaune.PlainOp) : Option MemoryRow :=
  match PlainOp.family op with
  | .memory row => some row
  | _ => none

/-- `LOG0`–`LOG4`. -/
def PlainOp.logRow? (op : Jaune.PlainOp) : Option LogRow :=
  match PlainOp.family op with
  | .log row => some row
  | _ => none

/-- The Read table. -/
def PlainOp.readRow? (op : Jaune.PlainOp) : Option ReadRow :=
  match PlainOp.family op with
  | .read row => some row
  | _ => none

/-- The families of the non-message operations; `none` for a message operation, which opens a
frame and is outside S4 (it keeps its explicit equations, `MessageOp.step`). -/
def NextOp.family? : Jaune.NextOp → Option Family
  | .plain op => some (PlainOp.family op)
  | .push xs _ => some (.word (NextOp.pushRow xs))
  | .dupn imm => some (.shuffle (NextOp.dupnRow imm))
  | .swapn imm => some (.shuffle (NextOp.swapnRow imm))
  | .exchange imm => some (.shuffle (NextOp.exchangeRow imm))
  | .message _ => none

end Jaune.Checked
