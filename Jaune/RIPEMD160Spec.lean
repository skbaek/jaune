import Jaune.Basic
import Jaune.Hash

/-!
# RIPEMD-160 as published, and the kernel's agreement with it

`Jaune/Hash.lean`'s `RIPEMD160` namespace is an optimized hash: the two lines
are carried as scalar working variables, the message words are indexed through
tables held as vectors, and the padding is built by a chunk walk so the padded
message is never materialized twice. None of that is visible in the paper, and
none of it should be: the standard defines RIPEMD-160 with two parallel lines
of five 32-bit working variables, eighty steps over sixteen message words
selected by the published order tables, and MD4-style padding.

This module is that definition, transcribed from **H. Dobbertin, A. Bosselaers
and B. Preneel, "RIPEMD-160: A Strengthened Version of RIPEMD", FSE 1996** —
section numbers are cited at each declaration; the same algorithm is ISO/IEC
10118-3:2004 §8 "Dedicated Hash-Function 2" — and the `#guard`s at the end pin
the published test values and the kernel's `Bytes.ripemd160` against it.

The transcription is written from the paper, never read back out of the kernel:
the five boolean functions are the paper's `f(j, ·)`, the constants are the
paper's `K(j)`/`K'(j)`, the eighty steps read the paper's four order and
rotation tables, and the padding is the paper's append-`0x80`, pad-to-`56 mod
64`, append-bit-length. Where the kernel and this module disagree in shape they
are meant to — that gap is what the guards are about. Where they would disagree
in *value*, this module is right by definition and the kernel is wrong.

Nothing here is on any execution path. The hash Jaune computes is
`Bytes.ripemd160`; these declarations exist to be read against the paper and to
give that function something to agree with.
-/

namespace Jaune.RIPEMD160.Spec

open Jaune

/-! ## The five boolean functions -/

/-- The paper §2, left line: `f(j, x, y, z)` is `x ⊕ y ⊕ z` for `0 ≤ j ≤ 15`,
`(x ∧ y) ∨ (¬x ∧ z)` for `16 ≤ j ≤ 31`, `(x ∨ ¬y) ⊕ z` for `32 ≤ j ≤ 47`,
`(x ∧ z) ∨ (y ∧ ¬z)` for `48 ≤ j ≤ 63`, and `x ⊕ (y ∨ ¬z)` for `64 ≤ j ≤ 79`. -/
def f (j : Nat) (x y z : UInt32) : UInt32 :=
  if j < 16 then x ^^^ y ^^^ z
  else if j < 32 then (x &&& y) ||| ((~~~ x) &&& z)
  else if j < 48 then (x ||| ~~~ y) ^^^ z
  else if j < 64 then (x &&& z) ||| (y &&& ~~~ z)
  else x ^^^ (y ||| ~~~ z)

/-- The paper §2, right line: the same five functions in reverse order,
`f(79 − j, x, y, z)`. -/
def fp (j : Nat) (x y z : UInt32) : UInt32 := f (79 - j) x y z

/-! ## The added constants K(j) and K'(j) -/

/-- The paper §2: the left-line added constants — `0x00000000`, `0x5A827999`,
`0x6ED9EBA1`, `0x8F1BBCDC`, `0xA953FD4E` by sixteen-step block. -/
def K (j : Nat) : UInt32 :=
  if j < 16 then 0x00000000
  else if j < 32 then 0x5A827999
  else if j < 48 then 0x6ED9EBA1
  else if j < 64 then 0x8F1BBCDC
  else 0xA953FD4E

/-- The paper §2: the right-line added constants — `0x50A28BE6`, `0x5C4DD124`,
`0x6D703EF3`, `0x7A6D76E9`, `0x00000000` by sixteen-step block. -/
def Kp (j : Nat) : UInt32 :=
  if j < 16 then 0x50A28BE6
  else if j < 32 then 0x5C4DD124
  else if j < 48 then 0x6D703EF3
  else if j < 64 then 0x7A6D76E9
  else 0x00000000

/-! ## The message-word orders r(j), r'(j) and the rotations s(j), s'(j) -/

/-- The paper §2: the left-line message-word selection `r(j)`, eighty entries. -/
def rL : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
    3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
    1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
    4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]

/-- The paper §2: the right-line message-word selection `r'(j)`, eighty entries. -/
def rR : Array Nat :=
  #[5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
    6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
    15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
    8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
    12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]

/-- The paper §2: the left-line rotation amounts `s(j)`, eighty entries. -/
def sL : Array Nat :=
  #[11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
    7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
    11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
    11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
    9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]

/-- The paper §2: the right-line rotation amounts `s'(j)`, eighty entries. -/
def sR : Array Nat :=
  #[8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
    9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
    9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
    15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
    8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

/-! ## The initial value -/

/-- The paper §2: the initial chaining value `h0..h4` is `67452301`,
`EFCDAB89`, `98BADCFE`, `10325476`, `C3D2E1F0`. -/
def h0 : Array UInt32 :=
  #[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]

/-! ## Appendix A — the step, the block, the padding -/

/-- The five working variables of one line (Appendix A: `A, B, C, D, E`). -/
structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32

/-- Appendix A `ROTx`: left rotation of a 32-bit word by `c`. -/
def rol (x : UInt32) (c : Nat) : UInt32 :=
  (x <<< c.toUInt32) ||| (x >>> (32 - c.toUInt32))

/-- Appendix A: one step `j` of both lines. The left step is
`T := rol_s(j)(A + f(j, B, C, D) + X[r(j)] + K(j)) + E` with
`A := E; E := D; D := rol_10(C); C := B; B := T`; the right step is the same
with `f(79 − j)`, `r'`, `s'`, `K'`. -/
def step (X : Array UInt32) (j : Nat) (l r : State) : State × State :=
  let tl := rol (l.a + f j l.b l.c l.d + X.getD (rL.getD j 0) 0 + K j) (sL.getD j 0) + l.e
  let tr := rol (r.a + fp j r.b r.c r.d + X.getD (rR.getD j 0) 0 + Kp j) (sR.getD j 0) + r.e
  ({ a := l.e, b := tl, c := l.b, d := rol l.c 10, e := l.d },
    { a := r.e, b := tr, c := r.b, d := rol r.c 10, e := r.d })

/-- Appendix A: the compression of one 16-word block — both lines run all
eighty steps from the current chaining value, then
`T := h1 + C + D'; h1 := h2 + D + E'; h2 := h3 + E + A'; h3 := h4 + A + B';
h4 := h0 + B + C'; h0 := T`. -/
def compress (h : State) (X : Array UInt32) : State :=
  let (l, r) :=
    (List.range 80).foldl (fun (lr : State × State) j => step X j lr.1 lr.2) (h, h)
  { a := h.b + l.c + r.d, b := h.c + l.d + r.e, c := h.d + l.e + r.a,
    d := h.e + l.a + r.b, e := h.a + l.b + r.c }

/-- Appendix A: one little-endian 32-bit word from four bytes. -/
def wordLE (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

/-- Appendix A: a 64-byte block parsed as sixteen little-endian 32-bit words. -/
def toWords (b : Bytes) : Array UInt32 :=
  ((List.range 16).map (fun i =>
    wordLE (b.getD (4 * i) 0) (b.getD (4 * i + 1) 0)
      (b.getD (4 * i + 2) 0) (b.getD (4 * i + 3) 0))).toArray

/-- Appendix A: the message bit length as a 64-bit little-endian integer. -/
def bitLenLE (len : Nat) : Bytes :=
  let n := 8 * len
  (List.range 8).map (fun i => ((n >>> (8 * i)) % 256).toUInt8)

/-- Appendix A, MD4-style padding: append `0x80`, then zero bytes out to
`56 mod 64`, then the bit length. -/
def padZeros (len : Nat) : Nat := (119 - len % 64) % 64

/-- Appendix A, MD4-style padding of the whole message. -/
def pad (m : Bytes) : Bytes :=
  m ++ [(0x80 : UInt8)] ++ List.replicate (padZeros m.length) (0x00 : UInt8) ++ bitLenLE m.length

/-- The initial `State` from `h0`. -/
def initState : State :=
  { a := h0.getD 0 0, b := h0.getD 1 0, c := h0.getD 2 0,
    d := h0.getD 3 0, e := h0.getD 4 0 }

/-- Appendix A: run the compression over the padded blocks in order from `h0`. -/
def hashState (m : Bytes) : State :=
  let p := pad m
  (List.range (p.length / 64)).foldl
    (fun h i => compress h (toWords ((p.drop (64 * i)).take 64))) initState

/-- One 32-bit word as four little-endian bytes. -/
def wordLEBytes (w : UInt32) : Bytes :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

/-- Appendix A: the 20-byte digest is `h0..h4` little-endian. -/
def hash (m : Bytes) : Bytes :=
  let h := hashState m
  wordLEBytes h.a ++ wordLEBytes h.b ++ wordLEBytes h.c ++ wordLEBytes h.d ++ wordLEBytes h.e

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
