import Jaune.Basic



namespace ripemd160

------------------------------ RIPEMD-160 ------------------------------

-- RIPEMD-160 hash function. Ported from David Turner's
-- C implementation (https://github.com/DaveCTurner/tiny-ripemd160)

-- ripemf160_shifts
def shiftLists : List B32L :=
  [
    [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8],
    [12, 13, 11, 15, 6, 9, 9, 7, 12, 15, 11, 13, 7, 8, 7, 7],
    [13, 15, 14, 11, 7, 7, 6, 8, 13, 14, 13, 12, 5, 5, 6, 9],
    [14, 11, 12, 14, 8, 6, 5, 5, 15, 12, 15, 14, 9, 9, 8, 6],
    [15, 12, 13, 13, 9, 5, 8, 6, 14, 11, 12, 11, 8, 6, 5, 5]
  ]

-- ripemd160_constants_left
def constantsLeft : B32L :=
  [0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]

-- ripemd160_constants_right
def constantsRight : B32L :=
  [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000]

-- ripemd160_fns_left
def fnsLeft : List Nat := [1, 2, 3, 4, 5]

-- ripemd160_fns_right
def fnsRight : List Nat := [5, 4, 3, 2, 1]

def rho : List Nat :=
  [ 0x7, 0x4, 0xd, 0x1, 0xa, 0x6, 0xf, 0x3,
    0xc, 0x0, 0x9, 0x5, 0x2, 0xe, 0xb, 0x8 ]

def computeLine (digest : B32L) (chunk : B32L) (index : List Nat)
  (shiftss : List B32L) (ks : B32L) (fns : List Nat) : Id B32L := do
  let mut index := index
  let mut w0 : B32 := digest[0]!
  let mut w1 : B32 := digest[1]!
  let mut w2 : B32 := digest[2]!
  let mut w3 : B32 := digest[3]!
  let mut w4 : B32 := digest[4]!
  for round in [0, 1, 2, 3, 4] do
    let shifts : B32L := shiftss[round]!
    let k : B32 := ks[round]!
    let fn : Nat := fns[round]!
    for i in List.range 16 do
      let mut tmp : B32 :=
        match fn with
        | 1 => w1 ^^^ w2 ^^^ w3
        | 2 => (w1 &&& w2) ||| (~~~ w1 &&& w3)
        | 3 => (w1 ||| ~~~ w2) ^^^ w3
        | 4 => (w1 &&& w3) ||| (w2 &&& ~~~ w3)
        | _ => w1 ^^^ (w2 ||| ~~~ w3)
      tmp := tmp + w0 + (chunk[(index[i]!)]!) + k
      tmp := B32.rol tmp (shifts[index[i]!]!) + w4
      w0 := w4
      w4 := w3
      w3 := B32.rol w2 10
      w2 := w1
      w1 := tmp
    index := index.map (fun i => rho[i]!)
  return [w0, w1, w2, w3, w4]

def updateDigest (digest : B32L) (chunk : B32L) : Id B32L := do
  let indexLeft : List Nat := List.range 16
  let wordsLeft : B32L ←
    computeLine digest chunk indexLeft shiftLists constantsLeft fnsLeft
  let indexRight : List Nat :=
    [ 0x05, 0x0e, 0x07, 0x00, 0x09, 0x02, 0x0b, 0x04,
      0x0d, 0x06, 0x0f, 0x08, 0x01, 0x0a, 0x03, 0x0c ]
  let wordsRight : B32L ←
    computeLine digest chunk indexRight
      shiftLists constantsRight fnsRight
  return [
    digest[1]! + wordsLeft[2]! + wordsRight[3]!,
    digest[2]! + wordsLeft[3]! + wordsRight[4]!,
    digest[3]! + wordsLeft[4]! + wordsRight[0]!,
    digest[4]! + wordsLeft[0]! + wordsRight[1]!,
    digest[0]! + wordsLeft[1]! + wordsRight[2]!
  ]

def B8L.toB32Rev : B8L → B32L
  | (b0 :: b1 :: b2 :: b3 :: bs) =>
    B8s.toB32 b3 b2 b1 b0 :: B8L.toB32Rev bs
  | _ => []

def processChunks (digest : B32L) (data : B8L) (lenSfx : B32L) : Nat → B32L
  | 0 =>
    if data.length > 55 then
      let penultChunk : B32L :=
        B8L.toB32Rev (List.takeD 64 (data ++ [0x80]) 0)
      let digest' := updateDigest digest penultChunk
      let lastChunk : B32L := List.replicate 14 (0 : B32) ++ lenSfx
      updateDigest digest' lastChunk
    else
      let lastChunk : B32L :=
        B8L.toB32Rev (List.takeD 56 (data ++ [0x80]) 0) ++ lenSfx
      updateDigest digest lastChunk
  | n + 1 =>
    let ⟨pfx, data'⟩ := data.splitAt 64
    let chunk : B32L := B8L.toB32Rev pfx
    let digest' := updateDigest digest chunk
    processChunks digest' data' lenSfx n

def run (data : B8L) : B8L := do
  let initDigest : B32L :=
    [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]
  let len : B32 := data.length.toUInt32
  let digest : B32L :=
    processChunks initDigest data [len <<< 3, len >>> 29] (data.length / 64)
  List.foldr (fun x acc => x.toB8L.reverse ++ acc) [] digest

end ripemd160

def B8L.ripemd160 : B8L → B8L := ripemd160.run



------------------------------SHA256------------------------------

-- 256-bit SHA-2 hash function. Ported from Alain Mosnier's
-- C implementation (https://github.com/amosnier/sha-2)

namespace SHA256

-- The eight-word initial state, length-indexed so the whole SHA-256 state is
-- statically an eight-word `Vector`. That makes the finaliser's projection
-- total (see `run`): there is no "wrong number of words" case to fall back on.
def initChunk : Vector B32 8 :=
  ⟨#[ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ], rfl⟩

def B8L.toChunks (lenB8L : B8L) : Nat → B8L → Nat → List B8A
  | 0, _, _ => []
  | _ + 1, _, 0 =>
    [((Array.replicate 64 0x00).set! 0 0x80).writeD 56 lenB8L]
  | k + 1, xs, len' + 64 =>
      let ⟨pfx, xs'⟩ := List.splitToArray 64 xs 0
      let xss := B8L.toChunks lenB8L k xs' len'
      pfx :: xss
  | _ + 1, xs, _ + 56 =>
    [ ⟨xs ++ (0x80 :: List.replicate (64 - (xs.length + 1)) 0x00)⟩,
      ⟨(List.replicate (56 : Nat) 0x00) ++ lenB8L⟩ ]
  | _ + 1, xs, _ =>
    [⟨xs ++ (0x80 :: List.replicate (64 - (xs.length + 9)) 0x00) ++ lenB8L⟩]

def roundConstants : B32A :=
 #[ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
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

-- The 64 compression rounds, specialized: the eight working variables are
-- carried as scalars rather than rebuilt as an `Array` literal each round,
-- and the message schedule `w` is updated in place. `n` counts rounds
-- remaining, so the round index is `t = 64 - n`; rounds `t < 16` read the
-- chunk, later rounds extend the schedule.
def rounds (p : B8A) :
  Nat → B32A → B32 → B32 → B32 → B32 → B32 → B32 → B32 → B32 → B32A
  | 0, _, a, b, c, d, e, f, g, h => ⟨[a, b, c, d, e, f, g, h]⟩
  | n + 1, w, a, b, c, d, e, f, g, h =>
    let t : Nat := 64 - (n + 1)
    let j : Nat := t % 16
    let wj : B32 :=
      if t < 16 then
        B8s.toB32
          (p.getD (4 * j) 0)
          (p.getD ((4 * j) + 1) 0)
          (p.getD ((4 * j) + 2) 0)
          (p.getD ((4 * j) + 3) 0)
      else
        let x1 : B32 := w.getD ((j + 1) % 16) 0
        let x14 : B32 := w.getD ((j + 14) % 16) 0
        let s0 : B32 :=
          (B32.ror x1 7) ^^^ (B32.ror x1 18) ^^^ (x1 >>> 3)
        let s1 : B32 :=
          (B32.ror x14 17) ^^^ (B32.ror x14 19) ^^^ (x14 >>> 10)
        (w.getD j 0) + s0 + (w.getD ((j + 9) % 16) 0) + s1
    let w' := Array.set! w j wj
    let s1 : B32 :=
      (B32.ror e 6) ^^^ (B32.ror e 11) ^^^ (B32.ror e 25)
    let ch : B32 := (e &&& f) ^^^ ((~~~ e) &&& g)
    let temp1 : B32 := h + s1 + ch + (roundConstants[t]!) + wj
    let s0 : B32 :=
      (B32.ror a 2) ^^^ (B32.ror a 13) ^^^ (B32.ror a 22)
    let maj : B32 := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 : B32 := s0 + maj
    rounds p n w' (temp1 + temp2) a b c (d + temp1) e f g

def consumeChunk (h : Vector B32 8) (p : B8A) : Vector B32 8 :=
  let h' : B32A :=
    rounds p 64 (Array.replicate 16 0)
      h[0] h[1] h[2] h[3] h[4] h[5] h[6] h[7]
  ⟨
    #[
      h[0] + h'[0]!,
      h[1] + h'[1]!,
      h[2] + h'[2]!,
      h[3] + h'[3]!,
      h[4] + h'[4]!,
      h[5] + h'[5]!,
      h[6] + h'[6]!,
      h[7] + h'[7]!
    ], rfl
  ⟩

def run (data : B8L) : B256 :=
  -- `data` is a list, so its length is an O(n) walk: take it once.
  let len : Nat := data.length
  let xss : List B8A :=
    B8L.toChunks
      (B64.toB8L (len * 8).toUInt64)
      (len / 64).succ
      data
      len
  -- `hash` is length-indexed at 8, so the eight projections below are total:
  -- the earlier "wrong number of 32-bit words" fallback is now unreachable by
  -- construction and has been removed rather than masked by a trace.
  let hash : Vector B32 8 := List.foldl consumeChunk initChunk xss
  B32s.toB256 hash[0] hash[1] hash[2] hash[3] hash[4] hash[5] hash[6] hash[7]

end SHA256

def B8L.sha256 : B8L → B256 := SHA256.run



------------------------------KECCAK------------------------------

-- 256-bit keccak hash function. Ported from Andrey Jivsov's
-- C implementation (https://github.com/brainhub/SHA3IUF)

namespace KECCAK

def Array.app {ξ : Type u} (k : Nat) (f : ξ → ξ) (ws : Array ξ) : Array ξ :=
  match ws[k]? with
  | none => panic "Array.app out of bounds"
  | some x => ws.set! k (f x)

-- def Bits.rol {n} (xs : Bits n) (y : Nat) : Bits n :=
--   Bits.or (xs.shl y) (xs.shr (n - y))

@[inline] def B64.rol (xs : B64) (y : Nat) : B64 :=
  (xs <<< y.toUInt64) ||| (xs >>> (64 - y).toUInt64)

-- The polymorphic permutation below (`θ`/`ρπ`/`χ`/`ι`/`f`, with the
-- `keccakf_rotc`/`keccakf_piln` tables and `B64.rol`) is the retained
-- reference transcription of the C original. Production hashing goes
-- through the specialized `fB64` further down; keep this block as the
-- readable spec the unrolled indices were generated from (the same
-- retention convention as `blake2MixTable`).
def θ {ξ : Type u} [XorOp ξ] [Inhabited ξ]
  (rol : ξ → Nat → ξ) (ws : Array ξ) : Array ξ :=
  let prep (x : Nat) : ξ :=
    ws[x]! ^^^
    ws[(x + 5)]! ^^^
    ws[(x + 10)]! ^^^
    ws[(x + 15)]! ^^^
    ws[(x + 20)]!
  let initVec : Vector ξ 5 :=
    ⟨#[prep 0, prep 1, prep 2, prep 3, prep 4], rfl⟩
  let rec inner (t : ξ) (i : Nat) : Nat → Array ξ → Array ξ
    | 0, ws => ws
    | j + 1, ws => inner t i j <| Array.app ((j * 5) + i) (· ^^^ t) ws
  let rec outer (bc : Vector ξ 5) : Nat → Array ξ → Array ξ
    | 0, ws => ws
    | i + 1, ws =>
      let t : ξ := bc.get (.ofNat _ (i + 4)) ^^^ rol (bc.get (.ofNat _ (i + 1))) 1
      outer bc i <| inner t i 5 ws
  outer initVec 5 ws

def B64.rdnc : Array B64 :=
  #[ 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
     0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
     0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
     0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
     0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
     0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ]

def keccakf_rotc : Array Nat :=
  #[ 1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14,
     27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44 ]

def keccakf_piln : Array Nat :=
  #[ 10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
     15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1 ]

def ρπ {ξ : Type u} [Inhabited ξ]  (rol : ξ → Nat → ξ) (ws : Array ξ) : Array ξ :=
  let rec aux : Nat → ξ → Array ξ → Array ξ
    | 0, _, ws => ws
    | k + 1, t, ws =>
      let i := 23 - k
      let j := keccakf_piln[i]!
      let ws' := ws.set! j (rol t <| keccakf_rotc[i]!)
      aux k (ws[j]!) ws'
  aux 24 (ws[1]!) ws

def χ {ξ : Type u} [XorOp ξ] [Complement ξ] [HAnd ξ ξ ξ] [Inhabited ξ]
  (ws : Array ξ) : Array ξ :=
  let rec inner (ws : Array ξ) (bc : Array ξ) (j : Nat) : Nat → Array ξ
    | 0 => ws
    | i + 1 =>
      let ws' :=
        Array.app (j + i)
          (· ^^^ ((~~~ bc[(i + 1) % 5]!) &&& (bc[(i + 2) % 5]!))) ws
      inner ws' bc j i
  let rec outer (ws : Array ξ) : Nat → Array ξ
    | 0 => ws
    | k + 1 =>
      let j := k * 5
      let f : Nat → ξ := λ x => ws[j + x]!
      let bc : Array ξ := #[f 0, f 1, f 2, f 3, f 4]
      let ws' : Array ξ := inner ws bc j 5
      outer ws' k
  outer ws 5

def ι {ξ : Type u} [XorOp ξ] [Inhabited ξ]
  (round : Nat) (rdnc : Array ξ) (ws : Array ξ) : Array ξ :=
  Array.app 0 (· ^^^ rdnc[round]!) ws

def f {ξ : Type u} [XorOp ξ] [Complement ξ] [HAnd ξ ξ ξ] [Inhabited ξ]
  (rdnc : Array ξ) (ws : Array ξ) (rol : ξ → Nat → ξ) : Array ξ :=
  let rec aux : Nat → Array ξ → Array ξ
    | 0, ws => ws
    | n + 1, ws =>
      aux n <| ι (23 - n) rdnc <| χ <| ρπ rol <| θ rol ws
  aux 24 ws

@[inline] private def rolc (x : B64) (n : UInt64) : B64 :=
  (x <<< n) ||| (x >>> (64 - n))

/-- The 5x5 keccak lane state as 25 unboxed scalars (lane (x, y) is
field `a(x + 5*y)`), so a round never touches the heap. -/
structure StateB64 where
  (a0 a1 a2 a3 a4 : B64)
  (a5 a6 a7 a8 a9 : B64)
  (a10 a11 a12 a13 a14 : B64)
  (a15 a16 a17 a18 a19 : B64)
  (a20 a21 a22 a23 a24 : B64)

private def roundB64 (rc : B64) (s : StateB64) : StateB64 :=
  let c0 := s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let d0 := c4 ^^^ rolc c1 1
  let d1 := c0 ^^^ rolc c2 1
  let d2 := c1 ^^^ rolc c3 1
  let d3 := c2 ^^^ rolc c4 1
  let d4 := c3 ^^^ rolc c0 1
  let a0 := s.a0 ^^^ d0
  let a1 := s.a1 ^^^ d1
  let a2 := s.a2 ^^^ d2
  let a3 := s.a3 ^^^ d3
  let a4 := s.a4 ^^^ d4
  let a5 := s.a5 ^^^ d0
  let a6 := s.a6 ^^^ d1
  let a7 := s.a7 ^^^ d2
  let a8 := s.a8 ^^^ d3
  let a9 := s.a9 ^^^ d4
  let a10 := s.a10 ^^^ d0
  let a11 := s.a11 ^^^ d1
  let a12 := s.a12 ^^^ d2
  let a13 := s.a13 ^^^ d3
  let a14 := s.a14 ^^^ d4
  let a15 := s.a15 ^^^ d0
  let a16 := s.a16 ^^^ d1
  let a17 := s.a17 ^^^ d2
  let a18 := s.a18 ^^^ d3
  let a19 := s.a19 ^^^ d4
  let a20 := s.a20 ^^^ d0
  let a21 := s.a21 ^^^ d1
  let a22 := s.a22 ^^^ d2
  let a23 := s.a23 ^^^ d3
  let a24 := s.a24 ^^^ d4
  let b0 := a0
  let b10 := rolc a1 1
  let b7 := rolc a10 3
  let b11 := rolc a7 6
  let b17 := rolc a11 10
  let b18 := rolc a17 15
  let b3 := rolc a18 21
  let b5 := rolc a3 28
  let b16 := rolc a5 36
  let b8 := rolc a16 45
  let b21 := rolc a8 55
  let b24 := rolc a21 2
  let b4 := rolc a24 14
  let b15 := rolc a4 27
  let b23 := rolc a15 41
  let b19 := rolc a23 56
  let b13 := rolc a19 8
  let b12 := rolc a13 25
  let b2 := rolc a12 43
  let b20 := rolc a2 62
  let b14 := rolc a20 18
  let b22 := rolc a14 39
  let b9 := rolc a22 61
  let b6 := rolc a9 20
  let b1 := rolc a6 44
  let e0 := b0 ^^^ ((~~~ b1) &&& b2)
  let e1 := b1 ^^^ ((~~~ b2) &&& b3)
  let e2 := b2 ^^^ ((~~~ b3) &&& b4)
  let e3 := b3 ^^^ ((~~~ b4) &&& b0)
  let e4 := b4 ^^^ ((~~~ b0) &&& b1)
  let e5 := b5 ^^^ ((~~~ b6) &&& b7)
  let e6 := b6 ^^^ ((~~~ b7) &&& b8)
  let e7 := b7 ^^^ ((~~~ b8) &&& b9)
  let e8 := b8 ^^^ ((~~~ b9) &&& b5)
  let e9 := b9 ^^^ ((~~~ b5) &&& b6)
  let e10 := b10 ^^^ ((~~~ b11) &&& b12)
  let e11 := b11 ^^^ ((~~~ b12) &&& b13)
  let e12 := b12 ^^^ ((~~~ b13) &&& b14)
  let e13 := b13 ^^^ ((~~~ b14) &&& b10)
  let e14 := b14 ^^^ ((~~~ b10) &&& b11)
  let e15 := b15 ^^^ ((~~~ b16) &&& b17)
  let e16 := b16 ^^^ ((~~~ b17) &&& b18)
  let e17 := b17 ^^^ ((~~~ b18) &&& b19)
  let e18 := b18 ^^^ ((~~~ b19) &&& b15)
  let e19 := b19 ^^^ ((~~~ b15) &&& b16)
  let e20 := b20 ^^^ ((~~~ b21) &&& b22)
  let e21 := b21 ^^^ ((~~~ b22) &&& b23)
  let e22 := b22 ^^^ ((~~~ b23) &&& b24)
  let e23 := b23 ^^^ ((~~~ b24) &&& b20)
  let e24 := b24 ^^^ ((~~~ b20) &&& b21)
  ⟨e0 ^^^ rc, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24⟩

/-- keccak-f[1600] monomorphized to `B64`: 24 unrolled rounds over 25
scalar locals. Semantically identical to `f B64.rdnc · B64.rol` over the
reference transcription above; round constants are read from `B64.rdnc`
rather than written as literals.

That read began as a workaround for a Lean-4.23 codegen bug (the duplicated
constant 0x8000000080008081 was CSE'd into a shared boxed value and the C
emitter then issued `lean_inc` on an unboxed uint64, which did not compile).
The bug is fixed as of the v4.32.1 toolchain: `scripts/repro-lean423-uint64-cse.lean`
now passes both of its documented compile steps and runs. The `B64.rdnc` read is
retained deliberately — it costs nothing measurable (the permutation is a few
percent of busy time with it) and is immune to regressions of the emitter path.
Do not rewrite the rounds back to literal constants. -/
def fB64 (ws : Array B64) : Array B64 :=
  let s : StateB64 :=
    ⟨ws[0]!, ws[1]!, ws[2]!, ws[3]!, ws[4]!,
     ws[5]!, ws[6]!, ws[7]!, ws[8]!, ws[9]!,
     ws[10]!, ws[11]!, ws[12]!, ws[13]!, ws[14]!,
     ws[15]!, ws[16]!, ws[17]!, ws[18]!, ws[19]!,
     ws[20]!, ws[21]!, ws[22]!, ws[23]!, ws[24]!⟩
  let s := roundB64 (B64.rdnc[0]!) s
  let s := roundB64 (B64.rdnc[1]!) s
  let s := roundB64 (B64.rdnc[2]!) s
  let s := roundB64 (B64.rdnc[3]!) s
  let s := roundB64 (B64.rdnc[4]!) s
  let s := roundB64 (B64.rdnc[5]!) s
  let s := roundB64 (B64.rdnc[6]!) s
  let s := roundB64 (B64.rdnc[7]!) s
  let s := roundB64 (B64.rdnc[8]!) s
  let s := roundB64 (B64.rdnc[9]!) s
  let s := roundB64 (B64.rdnc[10]!) s
  let s := roundB64 (B64.rdnc[11]!) s
  let s := roundB64 (B64.rdnc[12]!) s
  let s := roundB64 (B64.rdnc[13]!) s
  let s := roundB64 (B64.rdnc[14]!) s
  let s := roundB64 (B64.rdnc[15]!) s
  let s := roundB64 (B64.rdnc[16]!) s
  let s := roundB64 (B64.rdnc[17]!) s
  let s := roundB64 (B64.rdnc[18]!) s
  let s := roundB64 (B64.rdnc[19]!) s
  let s := roundB64 (B64.rdnc[20]!) s
  let s := roundB64 (B64.rdnc[21]!) s
  let s := roundB64 (B64.rdnc[22]!) s
  let s := roundB64 (B64.rdnc[23]!) s
  #[s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8, s.a9, s.a10, s.a11, s.a12, s.a13, s.a14, s.a15, s.a16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24]

def B8L.run : Fin 17 → B8L → Array B64 → B256
  | wc, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs, ws =>
    let t : B64 := B8s.toB64 b7 b6 b5 b4 b3 b2 b1 b0
    let ws' := Array.app wc (· ^^^ t) ws
    B8L.run (wc + 1) bs <| if wc = 16 then fB64 ws' else ws'
  | wc, bs, ws =>
    let us := (bs ++ [(1 : B8)]).takeD 8 (0 : B8)
    let t : B64 :=
      B8s.toB64
        (us[7]!) (us[6]!) (us[5]!) (us[4]!)
        (us[3]!) (us[2]!) (us[1]!) (us[0]!)
    let s : B64 := (8 : B64) <<< 60
    let temp0 := Array.app wc (· ^^^ t) ws
    let temp1 := Array.app 16 (· ^^^ s) temp0
    let ws' := fB64 temp1
    ⟨ ⟨B64.reverse (ws'[0]!), B64.reverse (ws'[1]!)⟩,
      ⟨B64.reverse (ws'[2]!), B64.reverse (ws'[3]!)⟩ ⟩

def ByteArray.run (bnd n : Nat) (wc : Fin 17) (bs : ByteArray) (ws : Array B64) : B256 :=
  if 7 < n then
    let b0 : B8 := bs[(bnd - n)]!
    let b1 : B8 := bs[(bnd - (n - 1))]!
    let b2 : B8 := bs[(bnd - (n - 2))]!
    let b3 : B8 := bs[(bnd - (n - 3))]!
    let b4 : B8 := bs[(bnd - (n - 4))]!
    let b5 : B8 := bs[(bnd - (n - 5))]!
    let b6 : B8 := bs[(bnd - (n - 6))]!
    let b7 : B8 := bs[(bnd - (n - 7))]!
    let t : B64 := B8s.toB64 b7 b6 b5 b4 b3 b2 b1 b0
    let ws' := Array.app wc (UInt64.xor · t) ws
    ByteArray.run bnd (n - 8) (wc + 1) bs <|
      if wc = 16 then fB64 ws' else ws'
  else
    let rec aux (bnd : Nat) (bs : ByteArray) : Nat → Nat → List B8
      | _, 0 => [] -- unreachable code
      | 0, n + 1 => 1 :: List.replicate n 0
      | m + 1, n + 1 =>
        (bs.get! (bnd - (m + 1))) :: aux bnd bs m n
    let us := aux bnd bs n 8
    let t : B64 :=
      B8s.toB64
        (us.getD 7 0)
        (us.getD 6 0)
        (us.getD 5 0)
        (us.getD 4 0)
        (us.getD 3 0)
        (us.getD 2 0)
        (us.getD 1 0)
        (us.getD 0 0)
    let s : B64 := (8 : B64) <<< 60
    let temp0 := Array.app wc (· ^^^ t) ws
    let temp1 := Array.app 16 (· ^^^ s) temp0
    let ws' := fB64 temp1
    ⟨ ⟨B64.reverse (ws'[0]!), B64.reverse (ws'[1]!)⟩,
      ⟨B64.reverse (ws'[2]!), B64.reverse (ws'[3]!)⟩ ⟩

end KECCAK

def B8L.keccak (bs : B8L) : B256 :=
  KECCAK.B8L.run (0 : Fin 17) bs <| .replicate 25 0

def ByteArray.keccak (loc sz : Nat) (bs : ByteArray) : B256 :=
  KECCAK.ByteArray.run (loc + sz) sz (0 : Fin 17) bs <| .replicate 25 0

def B256.keccak (x : B256) : B256 := B8L.keccak <| x.toB8L
