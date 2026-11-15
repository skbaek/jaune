-- Check/Types.lean : executable checks of `Jaune/Types.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/Types.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.Types

namespace Jaune

open Jaune _root_.Nat

--------------- STRICT-SHAPE BOUNDARY CHECKS ----------------

-- Boundaries at 0, 1, n, and n+1 bytes for each shape, plus canonicality, plus
-- the 19/20/21-byte address cases.

-- Fixed width: only the exact length is accepted, on both sides.
#guard (Bytes.toFixed? 0 []).isSome
#guard (Bytes.toFixed? 0 [0x00]).isNone
#guard (Bytes.toFixed? 4 [0x01, 0x02, 0x03]).isNone                    -- n-1
#guard (Bytes.toFixed? 4 [0x01, 0x02, 0x03, 0x04]).isSome              -- n
#guard (Bytes.toFixed? 4 [0x01, 0x02, 0x03, 0x04, 0x05]).isNone        -- n+1
-- A fixed-width field is bytes, not a number: leading zeroes are content.
#guard (Bytes.toFixed? 4 [0x00, 0x00, 0x00, 0x00]).isSome

-- Canonical scalars: the empty string is zero, a leading zero byte is not.
#guard Bytes.toScalarNat? 8 [] = some 0                                -- 0 bytes
#guard Bytes.toScalarNat? 8 [0x01] = some 1                            -- 1 byte
#guard Bytes.toScalarNat? 8 (List.replicate 8 (0xFF : UInt8)) = some (2 ^ 64 - 1)
#guard (Bytes.toScalarNat? 8 (List.replicate 9 (0xFF : UInt8))).isNone    -- n+1
#guard (Bytes.toScalarNat? 8 [0x00]).isNone                            -- zero, not empty
#guard (Bytes.toScalarNat? 8 [0x00, 0x01]).isNone                      -- leading zero
#guard Bytes.toScalarNat? 8 [0x01, 0x00] = some 256                    -- trailing zero is fine

-- 64-bit scalars convert every accepted width without truncating.
#guard (Bytes.toScalarB64? []).map UInt64.toNat = some 0
#guard (Bytes.toScalarB64? [0x01]).map UInt64.toNat = some 1
#guard (Bytes.toScalarB64? [0x01, 0x00]).map UInt64.toNat = some 256
#guard (Bytes.toScalarB64? (List.replicate 8 (0xFF : UInt8))).map UInt64.toNat
  = some (2 ^ 64 - 1)                                                -- n
#guard (Bytes.toScalarB64? (0x01 :: List.replicate 8 (0x00 : UInt8))).isNone  -- n+1
-- The nine-byte withdrawal-index case: rejected outright, and emphatically not
-- accepted as the eight-byte value `Bytes.toUInt64` would have truncated it to.
#guard (Bytes.toUInt64 (0x01 :: List.replicate 8 (0x00 : UInt8))).toNat = 0
#guard (Bytes.toScalarB64? [0x00]).isNone

-- 256-bit scalars, same shape one width up.
#guard (Bytes.toScalarB256? []).map B256.toNat = some 0
#guard (Bytes.toScalarB256? [0x01]).map B256.toNat = some 1
#guard (Bytes.toScalarB256? (List.replicate 32 (0xFF : UInt8))).map B256.toNat
  = some (2 ^ 256 - 1)                                               -- n
#guard (Bytes.toScalarB256? (List.replicate 33 (0xFF : UInt8))).isNone     -- n+1
#guard (Bytes.toScalarB256? [0x00, 0x01]).isNone

-- Addresses: exactly twenty bytes, with 19 and 21 both rejected.
#guard (Bytes.toAdr? (List.replicate 19 (0x11 : UInt8))).isNone
#guard (Bytes.toAdr? (List.replicate 20 (0x11 : UInt8))).isSome
#guard (Bytes.toAdr? (List.replicate 21 (0x11 : UInt8))).isNone
#guard (Bytes.toAdr? []).isNone
-- The twenty accepted bytes are the address, in order.
#guard (Bytes.toAdr? (List.replicate 20 (0x11 : UInt8))).map Adr.toHex
  = some (String.join <| List.replicate 20 "11")
-- The overlong case used to decode to the address of its twenty-byte prefix.
#guard (Bytes.toAdr? (List.replicate 20 (0x11 : UInt8) ++ [0x22])).isNone

-- Optional creation receivers: empty is creation, twenty bytes is a call, and
-- every other width is malformed rather than silently one of the two.
#guard (Bytes.toReceiver? []) = some none
#guard ((Bytes.toReceiver? (List.replicate 20 (0x11 : UInt8))).map (Option.map Adr.toHex))
  = some (some (String.join <| List.replicate 20 "11"))
#guard (Bytes.toReceiver? (List.replicate 19 (0x11 : UInt8))).isNone
#guard (Bytes.toReceiver? (List.replicate 21 (0x11 : UInt8))).isNone
#guard (Bytes.toReceiver? [0x00]).isNone

-- Boundaries at 0, 1, n, and n+1 bytes, plus the leading-zero cases that must
-- stay accepted here even though the RLP scalar decoders reject them.
#guard (Bytes.toQuantityB64? []).map UInt64.toNat = some 0
#guard (Bytes.toQuantityB64? [0x00]).map UInt64.toNat = some 0
#guard (Bytes.toQuantityB64? [0x00, 0x01]).map UInt64.toNat = some 1
#guard (Bytes.toScalarB64? [0x00, 0x01]).isNone
#guard (Bytes.toQuantityB64? (List.replicate 8 (0xFF : UInt8))).map UInt64.toNat
  = some (2 ^ 64 - 1)                                                  -- n
#guard (Bytes.toQuantityB64? (0x01 :: List.replicate 8 (0x00 : UInt8))).isNone -- n+1
-- The nine-byte nonce, which the old converter turned into a plausible zero.
#guard (Bytes.toUInt64 (0x01 :: List.replicate 8 (0x00 : UInt8))).toNat = 0

#guard (Bytes.toQuantityB256? []).map B256.toNat = some 0
#guard (Bytes.toQuantityB256? [0x00]).map B256.toNat = some 0
#guard (Bytes.toQuantityB256? [0x00, 0x01]).map B256.toNat = some 1
#guard (Bytes.toScalarB256? [0x00, 0x01]).isNone
#guard (Bytes.toQuantityB256? (List.replicate 32 (0xFF : UInt8))).map B256.toNat
  = some (2 ^ 256 - 1)                                                 -- n
#guard (Bytes.toQuantityB256? (List.replicate 33 (0xFF : UInt8))).isNone -- n+1
-- The thirty-three-byte balance, likewise silently truncated before.
#guard (Bytes.toB256 (0x01 :: List.replicate 32 (0x00 : UInt8))).toNat = 0
#guard (Bytes.toQuantityB256? (0x01 :: List.replicate 32 (0x00 : UInt8))).isNone

#guard match (0x20 : UInt8).toRinst with
  | some .keccak256 => Rinst.keccak256.toString == "KECCAK256"
  | _ => false
#guard match (0x3D : UInt8).toRinst with
  | some .returndatasize => Rinst.returndatasize.toString == "RETURNDATASIZE"
  | _ => false
#guard match (0x3E : UInt8).toRinst with
  | some .returndatacopy => Rinst.returndatacopy.toString == "RETURNDATACOPY"
  | _ => false
#guard match (0xF4 : UInt8).toXinst with
  | some .delegatecall => Xinst.delegatecall.toString == "DELEGATECALL"
  | _ => false
#guard match (0xFA : UInt8).toXinst with
  | some .staticcall => Xinst.staticcall.toString == "STATICCALL"
  | _ => false
#guard match (0xF3 : UInt8).toLinst with
  | some .return_ => Linst.return_.toUInt8 == 0xF3 && Linst.return_.toString == "RETURN"
  | _ => false
#guard match (0xFD : UInt8).toLinst with
  | some .revert => Linst.revert.toUInt8 == 0xFD && Linst.revert.toString == "REVERT"
  | _ => false
#guard match (0xFF : UInt8).toLinst with
  | some .selfdestruct =>
      Linst.selfdestruct.toUInt8 == 0xFF && Linst.selfdestruct.toString == "SELFDESTRUCT"
  | _ => false

end Jaune

