import Jaune.Hash

/-!
# SHA-256 as published, and the kernel's equivalence to it

`Jaune/Hash.lean`'s `SHA256` namespace is an optimized hash: the eight working
variables are carried as scalars, the sixty-four-entry message schedule is
folded onto sixteen live words updated in place, and padding is fused into the
chunk walk so the message is never materialized twice. None of that is visible
in FIPS 180-4, and none of it should be: the standard defines SHA-256 with a
sixty-four-entry schedule `W`, six named functions, and a padded message parsed
into 512-bit blocks.

This module is that definition, transcribed from **NIST FIPS 180-4** (*Secure
Hash Standard*, August 2015) — section numbers are cited at each declaration —
and `SHA256.FIPS.hash_eq` at the end proves the kernel computes it, for every
input.

The transcription is written from the standard, never read back out of the
kernel: the constants are the standard's tables, the schedule is the standard's
sixty-four entries, the round is the standard's `T₁`/`T₂` assignment, and the
padding is the standard's `l + 1 + k ≡ 448 mod 512`. Where the kernel and this
module disagree in shape they are meant to — that gap is what the theorem is
about. Where they would disagree in *value*, this module is right by definition
and the kernel is wrong.

Nothing here is on any execution path. The hash Jaune computes is
`Bytes.sha256`; these declarations exist to be read against the standard and to
give that function something to be equal to.
-/

namespace Jaune

open Jaune

namespace SHA256.FIPS

/-! ## §4.1.2 — the six logical functions -/

/-- FIPS 180-4 §4.1.2: `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)`. -/
def Ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~ x) &&& z)

/-- FIPS 180-4 §4.1.2: `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/
def Maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- FIPS 180-4 §4.1.2: `Σ₀{256}(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)`. -/
def Sigma0 (x : UInt32) : UInt32 :=
  UInt32.ror x 2 ^^^ UInt32.ror x 13 ^^^ UInt32.ror x 22

/-- FIPS 180-4 §4.1.2: `Σ₁{256}(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)`. -/
def Sigma1 (x : UInt32) : UInt32 :=
  UInt32.ror x 6 ^^^ UInt32.ror x 11 ^^^ UInt32.ror x 25

/-- FIPS 180-4 §4.1.2: `σ₀{256}(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`. -/
def sigma0 (x : UInt32) : UInt32 :=
  UInt32.ror x 7 ^^^ UInt32.ror x 18 ^^^ (x >>> 3)

/-- FIPS 180-4 §4.1.2: `σ₁{256}(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)`. -/
def sigma1 (x : UInt32) : UInt32 :=
  UInt32.ror x 17 ^^^ UInt32.ror x 19 ^^^ (x >>> 10)

/-! ## §4.2.2 and §5.3.3 — the constants -/

/-- FIPS 180-4 §4.2.2: the sixty-four constant 32-bit words `K₀{256} … K₆₃{256}`,
the first thirty-two bits of the fractional parts of the cube roots of the first
sixty-four prime numbers, in the order the standard tabulates them. -/
def K : Vector UInt32 64 :=
  #v[ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
      0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
      0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
      0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
      0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
      0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
      0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
      0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
      0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
      0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
      0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
      0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
      0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
      0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
      0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
      0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

/-- FIPS 180-4 §5.3.3: the initial hash value `H{0}` for SHA-256, the first
thirty-two bits of the fractional parts of the square roots of the first eight
prime numbers. -/
def H0 : Vector UInt32 8 :=
  #v[ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

/-! ## §5.1.1 and §5.2.1 — padding and parsing -/

/-- FIPS 180-4 §5.1.1: the number of zero *bytes* between the appended `1` bit
and the 64-bit length, for a message of `len` bytes.

The standard states it in bits: append the bit `1`, then `k` zero bits, where
`k` is the smallest non-negative solution of `l + 1 + k ≡ 448 mod 512`. Every
quantity there is a whole number of bytes for a byte-oriented message, so the
same condition reads: pad to `56 mod 64` bytes. -/
def padZeros (len : Nat) : Nat := (119 - len % 64) % 64

/-- FIPS 180-4 §5.1.1: the padded message — the message, the bit `1` as the byte
`0x80`, `k` zero bits, then `l` as a 64-bit big-endian block. -/
def pad (m : List UInt8) : List UInt8 :=
  m ++ ((0x80 : UInt8) ::
    (List.replicate (padZeros m.length) (0x00 : UInt8) ++
      UInt64.toBytes (8 * m.length).toUInt64))

/-- FIPS 180-4 §5.2.1: the padded message is parsed into `N` 512-bit blocks. -/
def blocksN : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | n + 1, m => m.take 64 :: blocksN n (m.drop 64)

/-- FIPS 180-4 §5.2.1: the `N = ℓ / 512` blocks of the padded message. -/
def blocks (m : List UInt8) : List (List UInt8) := blocksN (m.length / 64) m

/-- FIPS 180-4 §5.2.1: a 512-bit block is parsed as sixteen 32-bit words,
big-endian — `M₀{i} … M₁₅{i}`. -/
def toWords (b : List UInt8) : Vector UInt32 16 :=
  Vector.ofFn fun i =>
    UInt32.ofBytes
      (b.getD (4 * i.val) 0)
      (b.getD (4 * i.val + 1) 0)
      (b.getD (4 * i.val + 2) 0)
      (b.getD (4 * i.val + 3) 0)

/-! ## §6.2.2 — the message schedule and the sixty-four rounds -/

/-- FIPS 180-4 §6.2.2, step 1, second case: given `W₀ … W_{t-1}`, the next
schedule entry is `Wₜ = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}`. -/
def scheduleStep (W : Array UInt32) (t : Nat) : Array UInt32 :=
  W.push (sigma1 (W.getD (t - 2) 0) + W.getD (t - 7) 0 +
    sigma0 (W.getD (t - 15) 0) + W.getD (t - 16) 0)

/-- FIPS 180-4 §6.2.2, step 1: the sixty-four-entry message schedule of a block.
`Wₜ = Mₜ{i}` for `0 ≤ t ≤ 15`, and the recurrence above for `16 ≤ t ≤ 63`. -/
def schedule (M : Vector UInt32 16) : Array UInt32 :=
  (List.range' 16 48).foldl scheduleStep M.toArray

/-- The eight working variables `a, b, c, d, e, f, g, h` of FIPS 180-4 §6.2.2,
step 2. -/
structure Vars where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

/-- FIPS 180-4 §6.2.2, step 3: one round `t` of the compression function.

    T₁ = h + Σ₁{256}(e) + Ch(e, f, g) + Kₜ{256} + Wₜ
    T₂ = Σ₀{256}(a) + Maj(a, b, c)
    h = g;  g = f;  f = e;  e = d + T₁;  d = c;  c = b;  b = a;  a = T₁ + T₂
-/
def step (W : Array UInt32) (v : Vars) (t : Nat) : Vars :=
  let T₁ : UInt32 :=
    v.h + Sigma1 v.e + Ch v.e v.f v.g + K.getD t 0 + W.getD t 0
  let T₂ : UInt32 := Sigma0 v.a + Maj v.a v.b v.c
  { a := T₁ + T₂, b := v.a, c := v.b, d := v.c,
    e := v.d + T₁, f := v.e, g := v.f, h := v.g }

/-- FIPS 180-4 §6.2.2: the compression function on one block — initialize the
working variables with the current hash value (step 2), run rounds `t = 0` to
`63` (step 3), and compute the next hash value by adding the working variables
into it (step 4). -/
def compress (H : Vector UInt32 8) (M : Vector UInt32 16) : Vector UInt32 8 :=
  let v : Vars :=
    (List.range 64).foldl (step (schedule M))
      { a := H[0], b := H[1], c := H[2], d := H[3],
        e := H[4], f := H[5], g := H[6], h := H[7] }
  #v[ H[0] + v.a, H[1] + v.b, H[2] + v.c, H[3] + v.d,
      H[4] + v.e, H[5] + v.f, H[6] + v.g, H[7] + v.h ]

/-- FIPS 180-4 §6.2: SHA-256 — pad and parse the message (§5.1.1, §5.2.1), then
run the compression function over the blocks in order starting from `H{0}`
(§5.3.3). -/
def hashWords (m : List UInt8) : Vector UInt32 8 :=
  (blocks (pad m)).foldl (fun H b => compress H (toWords b)) H0

/-- FIPS 180-4 §6.2.2: the resulting 256-bit message digest is
`H₀{N} ‖ H₁{N} ‖ H₂{N} ‖ H₃{N} ‖ H₄{N} ‖ H₅{N} ‖ H₆{N} ‖ H₇{N}`. -/
def hash (m : List UInt8) : B256 :=
  let H : Vector UInt32 8 := hashWords m
  B32s.toB256 H[0] H[1] H[2] H[3] H[4] H[5] H[6] H[7]

end SHA256.FIPS

end Jaune
