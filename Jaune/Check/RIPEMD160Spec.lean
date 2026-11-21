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
private def messageEmpty : Bytes := []
private def messageSingleLetter : Bytes := [0x61]
private def messageAbc : Bytes := [0x61, 0x62, 0x63]
private def messageMessageDigest : Bytes :=
  "message digest".toList.map (fun c => c.val.toUInt8)
private def messageLowercaseLetters : Bytes :=
  "abcdefghijklmnopqrstuvwxyz".toList.map (fun c => c.val.toUInt8)
private def message448 : Bytes :=
  "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toList.map (fun c => c.val.toUInt8)
private def messageLettersAndDigits : Bytes :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789".toList.map
    (fun c => c.val.toUInt8)
private def messageDigitsTimes8 : Bytes :=
  "12345678901234567890123456789012345678901234567890123456789012345678901234567890".toList.map
    (fun c => c.val.toUInt8)

/-- The eight published digests. Values are the RIPEMD-160 test suite's, as
committed in the `"ripemd160"` table of `scripts/gen-hash-precompile-vectors.py`. -/
private def digestEmpty : Bytes := hex "9c1185a5c5e9fc54612808977ee8f548b2258d31"
private def digestSingleLetter : Bytes := hex "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"
private def digestAbc : Bytes := hex "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
private def digestMessageDigest : Bytes := hex "5d0689ef49d2fae572b881b123a85ffa21595f36"
private def digestLowercaseLetters : Bytes := hex "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"
private def digest448 : Bytes := hex "12a053384a9c0c88e405a06c27dcf49ada62eb2b"
private def digestLettersAndDigits : Bytes := hex "b0e20b6e3116640286ed3a87a5713079b21f5189"
private def digestDigitsTimes8 : Bytes := hex "9b752e45573d4b39f4dbd3323cab82bf63326bfb"

-- The eight published KATs: the spec returns the published digests.
#guard hash messageEmpty == digestEmpty
#guard hash messageSingleLetter == digestSingleLetter
#guard hash messageAbc == digestAbc
#guard hash messageMessageDigest == digestMessageDigest
#guard hash messageLowercaseLetters == digestLowercaseLetters
#guard hash message448 == digest448
#guard hash messageLettersAndDigits == digestLettersAndDigits
#guard hash messageDigitsTimes8 == digestDigitsTimes8

-- The one-million-"a" vector is deliberately not guarded: a million bytes
-- cannot be kernel-evaluated.

/-- Padding and block seams: `n` bytes `0, 1, 2, …` mod 256. -/
private def pattern (n : Nat) : Bytes := (List.range n).map (fun i => (i % 256).toUInt8)

-- The kernel agrees with the spec on the eight published messages.
#guard hash messageEmpty == Bytes.ripemd160 messageEmpty
#guard hash messageSingleLetter == Bytes.ripemd160 messageSingleLetter
#guard hash messageAbc == Bytes.ripemd160 messageAbc
#guard hash messageMessageDigest == Bytes.ripemd160 messageMessageDigest
#guard hash messageLowercaseLetters == Bytes.ripemd160 messageLowercaseLetters
#guard hash message448 == Bytes.ripemd160 message448
#guard hash messageLettersAndDigits == Bytes.ripemd160 messageLettersAndDigits
#guard hash messageDigitsTimes8 == Bytes.ripemd160 messageDigitsTimes8

-- The kernel agrees with the spec at every padding and block seam.
#guard hash (pattern 0) == Bytes.ripemd160 (pattern 0)
#guard hash (pattern 1) == Bytes.ripemd160 (pattern 1)
#guard hash (pattern 55) == Bytes.ripemd160 (pattern 55)
#guard hash (pattern 56) == Bytes.ripemd160 (pattern 56)
#guard hash (pattern 57) == Bytes.ripemd160 (pattern 57)
#guard hash (pattern 63) == Bytes.ripemd160 (pattern 63)
#guard hash (pattern 64) == Bytes.ripemd160 (pattern 64)
#guard hash (pattern 65) == Bytes.ripemd160 (pattern 65)
#guard hash (pattern 119) == Bytes.ripemd160 (pattern 119)
#guard hash (pattern 120) == Bytes.ripemd160 (pattern 120)
#guard hash (pattern 121) == Bytes.ripemd160 (pattern 121)
#guard hash (pattern 127) == Bytes.ripemd160 (pattern 127)
#guard hash (pattern 128) == Bytes.ripemd160 (pattern 128)

end Jaune.RIPEMD160.Spec

