import Jaune.Basic
import Jaune.Precompiles

/-!
# BLAKE2b F as published, and the precompile's framing of it

`Jaune/Precompiles.lean`'s `bCompress` is an optimized BLAKE2b compression: the
working vector is carried as sixteen unboxed scalars, the sigma rows are read
out of arrays, and the EIP-152 framing is parsed by `getBlake2Parameters` far
from the rounds it feeds. None of that is visible in RFC 7693, and none of it
should be: the standard defines BLAKE2 with a sixteen-word working vector `v`,
ten sigma permutations, a mixing function `G`, and a compression function `F`
over an explicit round count.

This module is that definition, transcribed from **RFC 7693** (*The BLAKE2
Cryptographic Hash and MAC*, Saarinen and Aumasson, 2015) — section numbers are
cited at each declaration — and EIP-152's framing of it, with `#guard`s at the
end pinning it against the EIP-152 test cases and the production `bCompress`.

The transcription is written from the standard, never read back out of the
production code: the rotation amounts are the standard's `R1..R4`, the sigma
table is the standard's ten permutations, the round is the standard's column
and diagonal `G` calls, and the framing is EIP-152's 213-byte layout. Where the
production code and this module disagree in shape they are meant to — that gap
is what the guards are about. Where they would disagree in *value*, this module
is right by definition and the production code is wrong.

Nothing here is on any execution path. The compression Jaune runs is
`bCompress`; these declarations exist to be read against the standard and to
give that function something to agree with.
-/

namespace Jaune.Blake2.Spec

open Jaune

/-! ## §2.1 and §2.6 — the word size and the rotation constants -/

/-- RFC 7693 §2.1/§2.6: BLAKE2b works on 64-bit words (`w = 64`); the rotation
constants are `R1 = 32`, `R2 = 24`, `R3 = 16`, `R4 = 63`. -/
def R1 : UInt64 := 32
/-- RFC 7693 §2.1/§2.6: second rotation constant. -/
def R2 : UInt64 := 24
/-- RFC 7693 §2.1/§2.6: third rotation constant. -/
def R3 : UInt64 := 16
/-- RFC 7693 §2.1/§2.6: fourth rotation constant. -/
def R4 : UInt64 := 63

/-- RFC 7693 §2.1: `ROTR^w(x; c)`, right rotation of a `w`-bit word by `c`,
spelled out as the two shifts. Addition below is mod 2^64 throughout, which is
what `UInt64` addition is. -/
def rotR (x c : UInt64) : UInt64 := (x >>> c) ^^^ (x <<< (64 - c))

/-! ## §2.6 — the initialization vector -/

/-- RFC 7693 §2.6: the eight 64-bit initialization words `IV[0..7]`. -/
def iv : Array UInt64 :=
  #[0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
    0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]

/-! ## §2.7 — the sigma permutations -/

/-- RFC 7693 §2.7: the ten permutations of `{0, …, 15}`. -/
def sigma : Array (Array Nat) :=
  #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- RFC 7693 §2.7: round `i` uses row `i mod 10` (there are ten rows). -/
def sigmaRow (i : Nat) : Array Nat := sigma.getD (i % 10) #[]

/-! ## §3.1 — the mixing function G -/

/-- RFC 7693 §3.1: the mixing function, with `ROTR^64` and addition mod 2^64:

    a := a + b + x;  d := ROTR(d ^ a, R1);  c := c + d;  b := ROTR(b ^ c, R2)
    a := a + b + y;  d := ROTR(d ^ a, R3);  c := c + d;  b := ROTR(b ^ c, R4)
-/
def G (v : Array UInt64) (a b c d : Nat) (x y : UInt64) : Array UInt64 :=
  let va : UInt64 := v.getD a 0 + v.getD b 0 + x
  let vd : UInt64 := rotR (v.getD d 0 ^^^ va) R1
  let vc : UInt64 := v.getD c 0 + vd
  let vb : UInt64 := rotR (v.getD b 0 ^^^ vc) R2
  let va : UInt64 := va + vb + y
  let vd : UInt64 := rotR (vd ^^^ va) R3
  let vc : UInt64 := vc + vd
  let vb : UInt64 := rotR (vb ^^^ vc) R4
  ((((v.setIfInBounds a va).setIfInBounds b vb).setIfInBounds c vc).setIfInBounds d vd)

/-! ## §3.2 — the compression function F -/

/-- RFC 7693 §3.2: one compression round — the column step, then the diagonal
step — with the sixteen message words selected by the round's sigma row `s`. -/
def round (m : Array UInt64) (s : Array Nat) (v : Array UInt64) : Array UInt64 :=
  let v := G v 0 4 8 12 (m.getD (s.getD 0 0) 0) (m.getD (s.getD 1 0) 0)
  let v := G v 1 5 9 13 (m.getD (s.getD 2 0) 0) (m.getD (s.getD 3 0) 0)
  let v := G v 2 6 10 14 (m.getD (s.getD 4 0) 0) (m.getD (s.getD 5 0) 0)
  let v := G v 3 7 11 15 (m.getD (s.getD 6 0) 0) (m.getD (s.getD 7 0) 0)
  let v := G v 0 5 10 15 (m.getD (s.getD 8 0) 0) (m.getD (s.getD 9 0) 0)
  let v := G v 1 6 11 12 (m.getD (s.getD 10 0) 0) (m.getD (s.getD 11 0) 0)
  let v := G v 2 7 8 13 (m.getD (s.getD 12 0) 0) (m.getD (s.getD 13 0) 0)
  G v 3 4 9 14 (m.getD (s.getD 14 0) 0) (m.getD (s.getD 15 0) 0)

/-- RFC 7693 §3.2: `n` applications of the round function, round `i` using
`sigmaRow i`. The standard fixes twelve rounds; EIP-152 passes the count in, so
it is a parameter here. -/
def rounds (m : Array UInt64) (n : Nat) (v : Array UInt64) : Array UInt64 :=
  (List.range n).foldl (fun v i => round m (sigmaRow i) v) v

/-- RFC 7693 §3.2: the compression function `F(h, m, t, f)`. The working vector
is `v[0..7] = h`, `v[8..15] = IV`; `v[12]` takes the low word of the byte count
`t`, `v[13]` the high word; `v[14]` is inverted when `f` (the final-block flag)
is set. After the rounds, `h[i] ^= v[i] ^ v[i + 8]`. -/
def F (h m : Array UInt64) (t0 t1 : UInt64) (f : Bool) (n : Nat) : Array UInt64 :=
  let v0 : Array UInt64 :=
    #[h.getD 0 0, h.getD 1 0, h.getD 2 0, h.getD 3 0,
      h.getD 4 0, h.getD 5 0, h.getD 6 0, h.getD 7 0,
      iv.getD 0 0, iv.getD 1 0, iv.getD 2 0, iv.getD 3 0,
      t0 ^^^ iv.getD 4 0, t1 ^^^ iv.getD 5 0,
      if f then ~~~ iv.getD 6 0 else iv.getD 6 0, iv.getD 7 0]
  let v := rounds m n v0
  #[h.getD 0 0 ^^^ v.getD 0 0 ^^^ v.getD 8 0,
    h.getD 1 0 ^^^ v.getD 1 0 ^^^ v.getD 9 0,
    h.getD 2 0 ^^^ v.getD 2 0 ^^^ v.getD 10 0,
    h.getD 3 0 ^^^ v.getD 3 0 ^^^ v.getD 11 0,
    h.getD 4 0 ^^^ v.getD 4 0 ^^^ v.getD 12 0,
    h.getD 5 0 ^^^ v.getD 5 0 ^^^ v.getD 13 0,
    h.getD 6 0 ^^^ v.getD 6 0 ^^^ v.getD 14 0,
    h.getD 7 0 ^^^ v.getD 7 0 ^^^ v.getD 15 0]

/-! ## EIP-152 framing -/

/-- EIP-152, Specification: one little-endian 64-bit word at byte offset `off`. -/
def getLE (data : Bytes) (off : Nat) : UInt64 :=
  Bytes.toUInt64 ((data.sliceD off 8 (0x00 : UInt8)).reverse)

/-- EIP-152, Specification: `n` consecutive little-endian 64-bit words from byte
offset `off`. -/
def readLE (data : Bytes) (off n : Nat) : Array UInt64 :=
  ((List.range n).map (fun i => getLE data (off + 8 * i))).toArray

/-- EIP-152, Specification: eight words as 64 little-endian bytes. -/
def outBytes (h : Array UInt64) : Bytes :=
  List.flatten ((List.range 8).map (fun i => (h.getD i 0).toBytes.reverse))

/-! ## RFC 7693 §3.3 — the minimal unkeyed BLAKE2b-512 wrapper -/

/-- RFC 7693 §3.3: minimal unkeyed BLAKE2b-512 over `F` above. The parameter
block is `h[0] ^= 0x01010000 ^ (kk << 8) ^ nn` with `kk = 0`, `nn = 64`; the
message must fit in one 128-byte block, which is padded with zeros, compressed
once with `t` set to the message length, `f` set (single final block), and the
standard twelve rounds. Longer messages are out of scope (`none`). -/
def blake2b512 (msg : Bytes) : Option Bytes :=
  if 128 < msg.length then none
  else
    let h : Array UInt64 :=
      #[iv.getD 0 0 ^^^ (0x01010000 : UInt64) ^^^ ((0 : UInt64) <<< 8) ^^^ (64 : UInt64),
        iv.getD 1 0, iv.getD 2 0, iv.getD 3 0,
        iv.getD 4 0, iv.getD 5 0, iv.getD 6 0, iv.getD 7 0]
    let blk := readLE (msg ++ List.replicate (128 - msg.length) (0x00 : UInt8)) 0 16
    some (outBytes (F h blk msg.length.toUInt64 0 true 12))

end Jaune.Blake2.Spec
