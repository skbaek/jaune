import Jaune.Instructions.Word
import Jaune.MessageCall.CheckedPlain

namespace Jaune.Checked

open Jaune

/-- Word instructions read their operands and a view of the running frame. -/
def PlainOp.wordRow? : Jaune.PlainOp → Option WordRow
  | .address => some (.context Gas.base fun v => v.context.recipient.toU256)
  | .origin => some (.context Gas.base fun v => v.context.tx.origin.toU256)
  | .caller => some (.context Gas.base fun v => v.context.caller.toU256)
  | .callvalue => some (.context Gas.base fun v => v.context.value)
  | .calldatasize => some (.context Gas.base fun v => v.context.calldata.length.toU256)
  | .codesize => some (.context Gas.base fun v => v.context.code.size.toU256)
  | .gasprice => some (.context Gas.base fun v => v.context.tx.gasPrice.toU256)
  | .returndatasize => some (.context Gas.base fun v => v.returnData.length.toU256)
  | .number => some (.context Gas.base fun v => v.context.block.number.toU256)
  | .timestamp => some (.context Gas.base fun v => v.context.block.time)
  | .gaslimit => some (.context Gas.base fun v => v.context.block.blockGasLimit.toU256)
  | .prevrandao => some (.context Gas.base fun v => v.context.block.prevRandao)
  | .coinbase => some (.context Gas.base fun v => v.context.block.coinbase.toU256)
  | .msize => some (.context Gas.base fun v => v.memorySize.toU256)
  | .pc => some (.context Gas.base fun v => v.pc.toU256)
  | .basefee => some { WordRow.context Gas.base (fun v => v.context.block.baseFeePerGas.toU256) with
      available := OpcodeRules.baseFee }
  | .blobbasefee => some { WordRow.context Gas.base (fun v =>
      (getBaseFeePerBlobGas v.context.block.rules.blob v.context.block.excessBlobGas).toU256) with
      available := OpcodeRules.blobBaseFee }
  | .chainid => some { WordRow.context Gas.base (fun v => v.context.block.chainId.toU256) with
      available := OpcodeRules.chainId }
  | .slotnum => some { WordRow.context Gas.base (fun v => v.context.block.slotNumber.toNat.toU256) with
      available := OpcodeRules.slotnum }
  | .gas => some (.context Gas.base fun v => v.gasLeft.toU256)
  | .blobhash => some {
      available := OpcodeRules.blobHash, arity := 1, cost := fun _ => Gas.hashOpcodeGas,
      result := some fun x v => v.context.tx.blobVersionedHashes.getD x.toNat 0 }
  | .calldataload => some {
      arity := 1, cost := fun _ => Gas.veryLow,
      result := some fun x v => Bytes.toU256 (v.context.calldata.sliceD x.toNat 32 0) }
  | .blockhash => some {
      arity := 1, cost := fun _ => Gas.blockhash,
      result := some fun x v => PlainOp.blockHashAt v.context x.toNat }
  | .eq => some (.binary .eqCheck Gas.veryLow)
  | .lt => some (.binary .ltCheck Gas.veryLow)
  | .gt => some (.binary .gtCheck Gas.veryLow)
  | .slt => some (.binary .sltCheck Gas.veryLow)
  | .sgt => some (.binary .sgtCheck Gas.veryLow)
  | .iszero => some (.unary (.eqCheck · 0) Gas.veryLow)
  | .not => some (.unary (~~~ ·) Gas.veryLow)
  | .and => some (.binary U256.and Gas.veryLow)
  | .or => some (.binary U256.or Gas.veryLow)
  | .xor => some (.binary U256.xor Gas.veryLow)
  | .signextend => some (.binary U256.signext Gas.low)
  | .byte => some (.binary (fun x y => (List.getD y.toBytes x.toNat 0).toU256) Gas.veryLow)
  | .add => some (.binary (· + ·) Gas.veryLow)
  | .sub => some (.binary (· - ·) Gas.veryLow)
  | .mul => some (.binary (· * ·) Gas.low)
  | .div => some (.binary (· / ·) Gas.low)
  | .sdiv => some (.binary U256.sdiv Gas.low)
  | .mod => some (.binary (· % ·) Gas.low)
  | .smod => some (.binary U256.smod Gas.low)
  | .addmod => some (.ternary U256.addmod Gas.mid)
  | .mulmod => some (.ternary U256.mulmod Gas.mid)
  | .shl => some { WordRow.binary (fun x y => y <<< x.toNat) Gas.veryLow with available := OpcodeRules.shifts }
  | .shr => some { WordRow.binary (fun x y => y >>> x.toNat) Gas.veryLow with available := OpcodeRules.shifts }
  | .sar => some { WordRow.binary (fun x y => U256.arithShiftRight y x.toNat) Gas.veryLow with
      available := OpcodeRules.shifts }
  | .clz => some { WordRow.unary (fun x => (U256.leadingZeros x).toU256) Gas.low with
      available := OpcodeRules.clz }
  | .exp => some {
      arity := 2, cost := fun (_, exponent) => Gas.exp + Gas.expByte * exponent.bytecount,
      result := some fun (base, exponent) _ => U256.exp base exponent }
  | .pop => some { arity := 1, cost := fun _ => Gas.base, result := none }
  | _ => none

end Jaune.Checked
