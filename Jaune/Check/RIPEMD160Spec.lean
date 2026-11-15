-- Check/RIPEMD160Spec.lean : executable checks of `Jaune/RIPEMD160Spec.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/RIPEMD160Spec.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.RIPEMD160Spec

namespace Jaune.RIPEMD160.Spec

open Jaune

/-! ## Test vectors -/

/-- Parse hex from the vector table. -/
private def hex (s : String) : Bytes := (Hex.toBytes s).getD []

/-- The eight published test messages (`""`, `"a"`, `"abc"`, `"message digest"`,
`"a...z"`, `"abcdbcde...nopq"`, `"A...Za...z0...9"`, eight `"1234567890"`). -/
private def mEmpty : Bytes := []
private def mA : Bytes := [0x61]
private def mAbc : Bytes := [0x61, 0x62, 0x63]
private def mMsg : Bytes :=
  "message digest".toList.map (fun c => c.val.toUInt8)
private def mAlpha : Bytes :=
  "abcdefghijklmnopqrstuvwxyz".toList.map (fun c => c.val.toUInt8)
private def m448 : Bytes :=
  "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toList.map (fun c => c.val.toUInt8)
private def mAlnum : Bytes :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789".toList.map
    (fun c => c.val.toUInt8)
private def m8x : Bytes :=
  "12345678901234567890123456789012345678901234567890123456789012345678901234567890".toList.map
    (fun c => c.val.toUInt8)

/-- The eight published digests. Values are the RIPEMD-160 test suite's, as
committed in the `"ripemd160"` table of `scripts/gen-hash-precompile-vectors.py`. -/
private def dEmpty : Bytes := hex "9c1185a5c5e9fc54612808977ee8f548b2258d31"
private def dA : Bytes := hex "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"
private def dAbc : Bytes := hex "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
private def dMsg : Bytes := hex "5d0689ef49d2fae572b881b123a85ffa21595f36"
private def dAlpha : Bytes := hex "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"
private def d448 : Bytes := hex "12a053384a9c0c88e405a06c27dcf49ada62eb2b"
private def dAlnum : Bytes := hex "b0e20b6e3116640286ed3a87a5713079b21f5189"
private def d8x : Bytes := hex "9b752e45573d4b39f4dbd3323cab82bf63326bfb"

-- The eight published KATs: the spec returns the published digests.
#guard hash mEmpty == dEmpty
#guard hash mA == dA
#guard hash mAbc == dAbc
#guard hash mMsg == dMsg
#guard hash mAlpha == dAlpha
#guard hash m448 == d448
#guard hash mAlnum == dAlnum
#guard hash m8x == d8x

-- The one-million-"a" vector is deliberately not guarded: a million bytes
-- cannot be kernel-evaluated.

/-- Padding and block seams: `n` bytes `0, 1, 2, …` mod 256. -/
private def pat (n : Nat) : Bytes := (List.range n).map (fun i => (i % 256).toUInt8)

-- The kernel agrees with the spec on the eight published messages.
#guard hash mEmpty == Bytes.ripemd160 mEmpty
#guard hash mA == Bytes.ripemd160 mA
#guard hash mAbc == Bytes.ripemd160 mAbc
#guard hash mMsg == Bytes.ripemd160 mMsg
#guard hash mAlpha == Bytes.ripemd160 mAlpha
#guard hash m448 == Bytes.ripemd160 m448
#guard hash mAlnum == Bytes.ripemd160 mAlnum
#guard hash m8x == Bytes.ripemd160 m8x

-- The kernel agrees with the spec at every padding and block seam.
#guard hash (pat 0) == Bytes.ripemd160 (pat 0)
#guard hash (pat 1) == Bytes.ripemd160 (pat 1)
#guard hash (pat 55) == Bytes.ripemd160 (pat 55)
#guard hash (pat 56) == Bytes.ripemd160 (pat 56)
#guard hash (pat 57) == Bytes.ripemd160 (pat 57)
#guard hash (pat 63) == Bytes.ripemd160 (pat 63)
#guard hash (pat 64) == Bytes.ripemd160 (pat 64)
#guard hash (pat 65) == Bytes.ripemd160 (pat 65)
#guard hash (pat 119) == Bytes.ripemd160 (pat 119)
#guard hash (pat 120) == Bytes.ripemd160 (pat 120)
#guard hash (pat 121) == Bytes.ripemd160 (pat 121)
#guard hash (pat 127) == Bytes.ripemd160 (pat 127)
#guard hash (pat 128) == Bytes.ripemd160 (pat 128)

end Jaune.RIPEMD160.Spec

