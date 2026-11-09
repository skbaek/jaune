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

/-- EIP-152, Specification: the precompile input is exactly 213 bytes — rounds
(4 bytes, big-endian) ‖ h (64 bytes, eight little-endian u64) ‖ m (128 bytes,
sixteen little-endian u64) ‖ t (16 bytes, two little-endian u64) ‖ f (1 byte,
must be 0 or 1) — and the output is the 64-byte little-endian `h'`. Returns
`none` on a wrong length or `f ∉ {0, 1}`. -/
def blake2F (data : Bytes) : Option Bytes :=
  if data.length ≠ 213 then none
  else
    let n := Bytes.toNat (data.sliceD 0 4 (0x00 : UInt8))
    let h := readLE data 4 8
    let m := readLE data 68 16
    let t0 := getLE data 196
    let t1 := getLE data 204
    let f := data.getD 212 (0x00 : UInt8)
    if f == 0 then some (outBytes (F h m t0 t1 false n))
    else if f == 1 then some (outBytes (F h m t0 t1 true n))
    else none

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

/-! ## Agreement with the production precompile -/

/-- The production entry path for one 213-byte EIP-152 input: `executeBlake2F`
(`Jaune/Precompiles.lean`, reached by the EIP-152 dispatch) parses the input
with `getBlake2Parameters` and compresses with `bCompress`, charging gas around
it. This is that path without the gas, so `#guard`s below can compare values:
`executeBlake2F` itself returns a `PrecompResult` (cost plus output or error),
not bare bytes. -/
def prodBlake2F (data : Bytes) : Option Bytes :=
  if data.length ≠ 213 then none
  else
    let ⟨n, h, m, t0, t1, fn⟩ := Jaune.getBlake2Parameters data
    match fn with
    | 0 => Jaune.bCompress n h m t0 t1 false
    | 1 => Jaune.bCompress n h m t0 t1 true
    | _ => none

/-! ## Test vectors -/

/-- Parse hex from the vector corpus. -/
private def hex (s : String) : Bytes := (Hex.toBytes s).getD []

/-- EIP-152 "Test Cases": all five committed vectors share one chaining value.
Bytes are EIP-152's, as committed in `scripts/vectors/blake2F.json`. -/
private def eipH : Bytes :=
  hex ("48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
    "d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b")

/-- EIP-152 "Test Cases": all five committed vectors share the message `"abc"`
(zero-padded to one block). Bytes are EIP-152's, as committed in
`scripts/vectors/blake2F.json`. -/
private def eipM : Bytes := [0x61, 0x62, 0x63] ++ List.replicate 125 (0x00 : UInt8)

/-- EIP-152 "Test Cases": all five committed vectors share the counter `t = 3`.
Bytes are EIP-152's, as committed in `scripts/vectors/blake2F.json`. -/
private def eipT : Bytes := [0x03] ++ List.replicate 15 (0x00 : UInt8)

/-- EIP-152, Specification: the 213-byte layout from a rounds header, the shared
corpus parts above, and a final flag byte. -/
private def mkIn (r0 r1 r2 r3 f : UInt8) : Bytes :=
  [r0, r1, r2, r3] ++ eipH ++ eipM ++ eipT ++ [f]

/-- EIP-152 "Test Cases", vector 4: rounds 0, `f = 1`. -/
private def v4in : Bytes := mkIn 0x00 0x00 0x00 0x00 0x01
/-- EIP-152 "Test Cases", vector 5: rounds 12, `f = 1`. -/
private def v5in : Bytes := mkIn 0x00 0x00 0x00 0x0c 0x01
/-- EIP-152 "Test Cases", vector 6: rounds 12, `f = 0`. -/
private def v6in : Bytes := mkIn 0x00 0x00 0x00 0x0c 0x00
/-- EIP-152 "Test Cases", vector 7: rounds 1, `f = 1`. -/
private def v7in : Bytes := mkIn 0x00 0x00 0x00 0x01 0x01

/-- EIP-152 "Test Cases", vector 4 output. Value is EIP-152's, as committed in
`scripts/vectors/blake2F.json`. -/
private def v4out : Bytes :=
  hex ("08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
    "d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b")

/-- EIP-152 "Test Cases", vector 5 output. Value is EIP-152's, as committed in
`scripts/vectors/blake2F.json`. -/
private def v5out : Bytes :=
  hex ("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
    "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")

/-- EIP-152 "Test Cases", vector 6 output. Value is EIP-152's, as committed in
`scripts/vectors/blake2F.json`. -/
private def v6out : Bytes :=
  hex ("75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d287529" ++
    "8743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735")

/-- EIP-152 "Test Cases", vector 7 output. Value is EIP-152's, as committed in
`scripts/vectors/blake2F.json`. -/
private def v7out : Bytes :=
  hex ("b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fb" ++
    "a551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421")

-- The constructed inputs really are 213 bytes and the outputs 64.
#guard v4in.length == 213
#guard v5in.length == 213
#guard v6in.length == 213
#guard v7in.length == 213
#guard v4out.length == 64
#guard v5out.length == 64
#guard v6out.length == 64
#guard v7out.length == 64

-- EIP-152 "Test Cases": vectors 0-3 are framing failures (wrong length or flag).
-- They are not present in `scripts/vectors/blake2F.json`, which starts at
-- vector 4, so the three inputs below are representative malformed inputs of
-- the same classes: empty, short, long, and a valid-length input with `f = 2`.
#guard blake2F [] == none
#guard blake2F (List.replicate 212 (0x00 : UInt8)) == none
#guard blake2F (v5in ++ [(0x00 : UInt8)]) == none
#guard blake2F (v5in.take 212 ++ [(0x02 : UInt8)]) == none
-- The production path fails them the same way.
#guard prodBlake2F [] == none
#guard prodBlake2F (v5in ++ [(0x00 : UInt8)]) == none
#guard prodBlake2F (v5in.take 212 ++ [(0x02 : UInt8)]) == none

-- EIP-152 "Test Cases", vectors 4-7: the spec returns the published outputs.
#guard blake2F v4in == some v4out
#guard blake2F v5in == some v5out
#guard blake2F v6in == some v6out
#guard blake2F v7in == some v7out

-- EIP-152 "Test Cases", vectors 4-7: the production `bCompress` path (via
-- `getBlake2Parameters`, as `executeBlake2F` calls them) returns the same
-- published outputs.
#guard prodBlake2F v4in == some v4out
#guard prodBlake2F v5in == some v5out
#guard prodBlake2F v6in == some v6out
#guard prodBlake2F v7in == some v7out

-- Vectors 4-7: production and spec agree with each other directly.
#guard prodBlake2F v4in == blake2F v4in
#guard prodBlake2F v5in == blake2F v5in
#guard prodBlake2F v6in == blake2F v6in
#guard prodBlake2F v7in == blake2F v7in

-- Vector 8 (rounds `0x007A1200` = 8000000) is deliberately not guarded: eight
-- million rounds cannot be kernel-evaluated. Its input and output are EIP-152's,
-- as committed in `scripts/vectors/blake2F.json`, and are not repeated here.
-- No committed vector beyond the EIP's has a round count ≤ 20, so there is no
-- further cheap agreement case to add.

-- RFC 7693 Appendix A: BLAKE2b-512("abc"). The bytes below are EIP-152 vector 5's
-- published output from `scripts/vectors/blake2F.json`, which is the same
-- single-block computation (parameter block for `nn = 64`, message `"abc"`,
-- `t = 3`, `f` set, twelve rounds) the appendix publishes for `"abc"`.
#guard blake2b512 [0x61, 0x62, 0x63] == some v5out

/-! ## Equivalence with `bCompress` -/

/-- The same rounds as `rounds`, but counting down like the production loop:
round index `k - (n + 1)` first, then the remaining `n` rounds. -/
def roundsR (m : Array UInt64) (k : Nat) : Nat → Array UInt64 → Array UInt64
  | 0, v => v
  | n + 1, v => roundsR m k n (round m (sigmaRow (k - (n + 1))) v)

/-- `roundsR` applies the rounds with indices `k - n` through `k - 1` in order. -/
private theorem roundsR_eq_foldl (m : Array UInt64) (k n : Nat) (v : Array UInt64)
    (h : n ≤ k) :
    roundsR m k n v =
      (List.range' (k - n) n).foldl (fun v i => round m (sigmaRow i) v) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    have hnk : n ≤ k := by omega
    have e1 : roundsR m k (n + 1) v
        = roundsR m k n (round m (sigmaRow (k - (n + 1))) v) := rfl
    have e2 : List.range' (k - (n + 1)) (n + 1)
        = (k - (n + 1)) :: List.range' (k - n) n := by
      have rfl2 : List.range' (k - (n + 1)) (n + 1)
          = (k - (n + 1)) :: List.range' (k - (n + 1) + 1) n := rfl
      rw [rfl2, show k - (n + 1) + 1 = k - n by omega]
    rw [e1, ih _ hnk, e2, List.foldl_cons]

/-- The full `roundsR` run is `rounds`. -/
private theorem roundsR_eq_rounds (m : Array UInt64) (k : Nat) (v : Array UInt64) :
    roundsR m k k v = rounds m k v := by
  rw [roundsR_eq_foldl _ _ _ _ (by omega), Nat.sub_self]
  unfold rounds
  congr 1
  exact List.range_eq_range'.symm

/-- The production table is this module's table. -/
private theorem blake2IV_eq : ∀ i, i < 8 →
    Jaune.blake2IV.getD i 0 = iv.getD i 0 := by
  decide

/-- `Vec.toArray` of an explicit working vector. -/
private theorem vecToArray16 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64) :
    Jaune.Blake2.Vec.toArray ⟨a0, a1, a2, a3, a4, a5, a6, a7,
      a8, a9, a10, a11, a12, a13, a14, a15⟩
      = #[a0, a1, a2, a3, a4, a5, a6, a7,
        a8, a9, a10, a11, a12, a13, a14, a15] := rfl

/-- Array `get` is `getD` with any default (both reduce to the internal get). -/
private theorem arrGetGetD (a : Array α) (i : Nat) (d : α) (h : i < a.size) :
    a[i] = a.getD i d := by
  unfold Array.getD
  rw [dif_pos h]
  rfl

/-- `takeD 8` is the identity on eight-byte lists. -/
private theorem takeD8 (l : List UInt8) (h : l.length = 8) : l.takeD 8 0 = l :=
  List.takeD_eq_self 0 h.symm

/-- The masked sixth initialization word. -/
private theorem ivXor6 : (Jaune.blake2IV.getD 6 0).xor Jaune.b2MaskBits
    = ~~~iv.getD 6 0 := rfl

/-
-- WIP, not checked: turn-4 stretch main theorem. Proof in progress at the end
-- of turn 4; kept here so the file builds green. To resume, delete this block
-- comment wrapper and continue from the `generalize` step (the remaining gaps
-- were: `blake2IV` vs `iv` in `get?`-normal form, `.xor` vs `^^^`, and the
-- `takeD`-unfolded vs `reverse` output bytes).
theorem bCompress_eq (n : Nat) (h m : List UInt64) (t0 t1 : UInt64) (f : Bool)
    (hh : h.length = 8) (hm : m.length = 16) :
    Jaune.bCompress n h m t0 t1 f
      = some (outBytes (F h.toArray m.toArray t0 t1 f n)) := by
  unfold Jaune.bCompress
  rw [dif_pos hh, dif_pos hm]
  simp only [Jaune.Blake2.roundsVec_toArray]
  simp only [Blake2.Vec.toArray]
  simp only [F, outBytes]
  simp [vecToArray16, blake2IV_eq, ivXor6, arrGetGetD, takeD8,
    List.length_reverse, UInt64.length_toBytes, hh, hm]
  generalize hA : #[h.toArray.getD 0 0, h.toArray.getD 1 0, h.toArray.getD 2 0,
      h.toArray.getD 3 0, h.toArray.getD 4 0, h.toArray.getD 5 0,
      h.toArray.getD 6 0, h.toArray.getD 7 0, iv.getD 0 0, iv.getD 1 0,
      iv.getD 2 0, iv.getD 3 0, t0 ^^^ iv.getD 4 0, t1 ^^^ iv.getD 5 0,
      (if f then ~~~iv.getD 6 0 else iv.getD 6 0), iv.getD 7 0] = A
-/

/-- The RFC 7693 §2.7 table is the production table, literally. -/
private theorem sigma_eq : sigma = Jaune.blake2Sigma := rfl

/-- Production first-half rotation is `rotR s R1`: `blake2R1 = 64 - b2R1`
(`Jaune/Precompiles.lean`) and `rotR` (`§3.1` above) spell it the same way. -/
private theorem rotR_eq1 (s : UInt64) :
    (s >>> Jaune.b2R1) ^^^ (s <<< Jaune.blake2R1) = rotR s R1 := rfl

/-- Production second-half rotation is `rotR s R2`. -/
private theorem rotR_eq2 (s : UInt64) :
    (s >>> Jaune.b2R2) ^^^ (s <<< Jaune.blake2R2) = rotR s R2 := rfl

/-- Production third-half rotation is `rotR s R3`. -/
private theorem rotR_eq3 (s : UInt64) :
    (s >>> Jaune.b2R3) ^^^ (s <<< Jaune.blake2R3) = rotR s R3 := rfl

/-- Production fourth-half rotation is `rotR s R4`. -/
private theorem rotR_eq4 (s : UInt64) :
    (s >>> Jaune.b2R4) ^^^ (s <<< Jaune.blake2R4) = rotR s R4 := rfl

/-- In-bounds `get!` is `getD` with default `0` on word arrays: the production
`Blake2.g` reads (`v[a]!`) against this spec's reads (`v.getD a 0`). -/
private theorem getBang_eq_getD (v : Array UInt64) (i : Nat) (h : i < v.size) :
    v[i]! = v.getD i 0 :=
  (getElem!_pos v i h).trans (arrGetGetD _ _ _ h)

/-- In-bounds `get!` is `getD` with default `#[]` on sigma-row arrays. -/
private theorem getBang_eq_getD_row (a : Array (Array Nat)) (i : Nat)
    (h : i < a.size) :
    a[i]! = a.getD i #[] :=
  (getElem!_pos a i h).trans (arrGetGetD _ _ _ h)

/-- Round `r` uses the production row `r % 10`, in `get!` rather than `getD`
form: `blake2Sigma.size` is `10` (`Jaune.blake2Sigma_size`). -/
private theorem sigmaRow_eq (r : Nat) :
    sigmaRow r = Jaune.blake2Sigma[r % Jaune.blake2Sigma.size]! := by
  unfold sigmaRow
  rw [sigma_eq]
  have h10 : r % 10 < Jaune.blake2Sigma.size := by
    rw [Jaune.blake2Sigma_size]
    exact Nat.mod_lt _ (by omega)
  rw [show r % Jaune.blake2Sigma.size = r % 10 by rw [Jaune.blake2Sigma_size]]
  exact (getBang_eq_getD_row _ _ h10).symm

end Jaune.Blake2.Spec
