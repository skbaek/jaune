import Jaune.Machine

namespace Jaune

open Jaune

inductive PrecompileResult
| error (reason : EvmError) (cost : Nat)
| ok (cost : Nat) (output : Bytes)

def Bytes.sliceToNat (data : Bytes) (start : Nat) (length : Nat) : Nat :=
  match data.drop start with
  | [] => 0
  | tail@(_ :: _)=>
    if tail.length < length
    then
      if tail.all (· = 0)
      then 0
      else Bytes.toNat <| tail.takeD length (0 : UInt8)
    else Bytes.toNat <| tail.take length

-- def eip198Complexity
/-- EIP-198's multiplication complexity (Byzantium .. Muir Glacier): the
piecewise polynomial in the raw byte lengths, against EIP-2565's `words ^ 2`
below. -/
def eip198Complexity (baseLength modulusLength : Nat) : Nat :=
  let maxLength := max baseLength modulusLength
  if maxLength ≤ 64 then maxLength ^ 2
  else if maxLength ≤ 1024 then maxLength ^ 2 / 4 + 96 * maxLength - 3072
  else maxLength ^ 2 / 16 + 480 * maxLength - 199680

-- def complexity
def modexpComplexity
  (c : ModexpComplexity) (m : ModexpRules)
  (baseLength modulusLength : Nat) : Nat :=
  match c with
  | .eip198 => eip198Complexity baseLength modulusLength
  | .eip2565 =>
    let maxLength := max baseLength modulusLength
    let words := ceilDiv maxLength 8
    match m.flatComplexity with
    | some flat => if maxLength ≤ 32 then flat else m.complexityCoefficient * words ^ 2
    | none => m.complexityCoefficient * words ^ 2

-- def iterations
def modexpIterations (m : ModexpRules) (expLength : Nat) (expHead : Nat) : Nat :=
  let bitsPart : Nat := (Nat.log2 expHead)
  let count :=
    if expLength ≤ 32
    then
      if expHead = 0
      then 0
      else
        bitsPart
    else
      let lengthPart := m.iterationCoefficient * (expLength - 32)
      lengthPart + bitsPart

  max count 1

-- def gas_cost
def modexpGasCost
  (c : ModexpComplexity) (m : ModexpRules)
  (baseLength modulusLength expLength expHead : Nat) : Nat :=
  let mulComplexity := modexpComplexity c m baseLength modulusLength
  let iterationCount := modexpIterations m expLength expHead
  let cost := (mulComplexity * iterationCount) / m.gasDivisor
  max m.minGas cost

/-- EIP-7823's bound on the three `MODEXP` length headers.

The check is part of the gas phase and precedes charging, so an oversized
header is an exceptional halt that consumes the frame's gas rather than a
priced computation. `none` reproduces the pre-Osaka behaviour of accepting any
header. -/
def modexpLengthsInBounds
    (m : ModexpRules) (baseLength expLength modulusLength : Nat) : Bool :=
  match m.maxLength with
  | none => true
  | some bound =>
    baseLength ≤ bound && expLength ≤ bound && modulusLength ≤ bound

def Blake2.R1 : UInt64 := 32
def Blake2.R2 : UInt64 := 24
def Blake2.R3 : UInt64 := 16
def Blake2.R4 : UInt64 := 63
def Blake2.maskBits : UInt64 := 0xFFFFFFFFFFFFFFFF

def blake2IV : List UInt64 :=
  [
    0x6A09E667F3BCC908,
    0xBB67AE8584CAA73B,
    0x3C6EF372FE94F82B,
    0xA54FF53A5F1D36F1,
    0x510E527FADE682D1,
    0x9B05688C2B3E6C1F,
    0x1F83D9ABFB41BD6B,
    0x5BE0CD19137E2179
  ]

-- Reference for the word indices unrolled into `Blake2.round`: row `i` is the
-- `(a, b, c, d)` quadruple mixed by the `i`th `Blake2.g` call of a round.
def blake2MixTable : Array (Array Nat) :=
  #[
    #[0, 4, 8, 12],
    #[1, 5, 9, 13],
    #[2, 6, 10, 14],
    #[3, 7, 11, 15],
    #[0, 5, 10, 15],
    #[1, 6, 11, 12],
    #[2, 7, 8, 13],
    #[3, 4, 9, 14]
  ]

def blake2Sigma : Array (Array Nat) :=
  #[
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]
  ]

-- The three size facts the BLAKE2b wrapper is built on. The compression kernel
-- indexes the message by a sigma entry, so what it needs is that the table has
-- ten rows, that every row has sixteen entries, and that every entry names a
-- message word; all three are decided from the table rather than assumed of it.
theorem blake2Sigma_size : blake2Sigma.size = 10 := rfl

theorem size_blake2Sigma_row :
    ∀ i, (h : i < blake2Sigma.size) → blake2Sigma[i].size = 16 := by decide

theorem blake2Sigma_lt :
    ∀ i, (h : i < blake2Sigma.size) →
      ∀ j, (hj : j < blake2Sigma[i].size) → blake2Sigma[i][j] < 16 := by decide

/-- The sigma row the rounds loop actually selects has sixteen entries. -/
theorem size_blake2Sigma_get (r : Nat) :
    (blake2Sigma[r % blake2Sigma.size]!).size = 16 := by
  have h : r % blake2Sigma.size < blake2Sigma.size :=
    Nat.mod_lt _ (by rw [blake2Sigma_size]; omega)
  rw [getElem!_pos blake2Sigma (r % blake2Sigma.size) h]
  exact size_blake2Sigma_row _ h

-- def spit_le_to_uint
def readLittleEndianUInt64Words (data : Bytes) : Nat → Nat → List UInt64
  | _, 0 => []
  | start, num_words + 1 =>
    let wordBytes := data.sliceD start 8 (0x00 : UInt8)
    let word := Bytes.toUInt64 wordBytes.reverse
    word :: readLittleEndianUInt64Words data (start + 8) num_words

/-- The reader produces exactly the number of words asked for, whatever the
input length: it is the fact that lets `executeBlake2F`'s 213-byte check stand
in for the chaining value and message widths `bCompress` requires. -/
theorem length_readLittleEndianUInt64Words (data : Bytes) (start n : Nat) :
    (readLittleEndianUInt64Words data start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [readLittleEndianUInt64Words, ih]

def getBlake2Parameters (data : Bytes) :
  Nat × List UInt64 × List UInt64 × UInt64 × UInt64 × Nat :=
  let rounds := Bytes.sliceToNat data 0 4
  let h := readLittleEndianUInt64Words data 4 8
  let m := readLittleEndianUInt64Words data 68 16
  let t := readLittleEndianUInt64Words data 196 2
  let f := Bytes.toNat <| data.drop 212
  ⟨rounds, h, m, t.getD 0 0, t.getD 1 0, f⟩

-- The left rotation amounts are `64 - b2R*`: one source of truth for the pair.
def Blake2.wR1 : UInt64 := 64 - Blake2.R1
def Blake2.wR2 : UInt64 := 64 - Blake2.R2
def Blake2.wR3 : UInt64 := 64 - Blake2.R3
def Blake2.wR4 : UInt64 := 64 - Blake2.R4

-- `Blake2.g`, `Blake2.round`, and `Blake2.rounds` below are the readable
-- reference specification of the compression round. They are no longer on the
-- execution path — `Blake2.roundVec` and `Blake2.roundsVec` are — and they are
-- not dead code either: `Blake2.roundVec_toArray` and
-- `Blake2.roundsVec_toArray` prove that the unboxed implementation agrees with
-- them. Those theorems are the reason this block stays.

-- def G
-- The four touched words are read once, mixed entirely in local scalars, and
-- written back once: the intermediate `set!`/`get!` round trips of the
-- transcribed reference version are redundant, since every word re-read is
-- the value just computed.
private def Blake2.g (v : Array UInt64) (a b c d : Nat) (x y : UInt64) : Array UInt64 :=
  let va : UInt64 := v[a]!
  let vb : UInt64 := v[b]!
  let vc : UInt64 := v[c]!
  let vd : UInt64 := v[d]!
  let va : UInt64 := va + vb + x
  let s : UInt64 := vd ^^^ va
  let vd : UInt64 := (s >>> Blake2.R1) ^^^ (s <<< Blake2.wR1)
  let vc : UInt64 := vc + vd
  let s : UInt64 := vb ^^^ vc
  let vb : UInt64 := (s >>> Blake2.R2) ^^^ (s <<< Blake2.wR2)
  let va : UInt64 := va + vb + y
  let s : UInt64 := vd ^^^ va
  let vd : UInt64 := (s >>> Blake2.R3) ^^^ (s <<< Blake2.wR3)
  let vc : UInt64 := vc + vd
  let s : UInt64 := vb ^^^ vc
  let vb : UInt64 := (s >>> Blake2.R4) ^^^ (s <<< Blake2.wR4)
  (((v.set! a va).set! b vb).set! c vc).set! d vd

-- One full mixing round, with `blake2MixTable` unrolled into literal word
-- indices; `m` is an `Array` so the message words are indexed rather than
-- walked as a list.
private def Blake2.round (m : Array UInt64) (s : Array Nat) (v : Array UInt64) : Array UInt64 :=
  let v := Blake2.g v 0 4 8 12 (m[s[0]!]!) (m[s[1]!]!)
  let v := Blake2.g v 1 5 9 13 (m[s[2]!]!) (m[s[3]!]!)
  let v := Blake2.g v 2 6 10 14 (m[s[4]!]!) (m[s[5]!]!)
  let v := Blake2.g v 3 7 11 15 (m[s[6]!]!) (m[s[7]!]!)
  let v := Blake2.g v 0 5 10 15 (m[s[8]!]!) (m[s[9]!]!)
  let v := Blake2.g v 1 6 11 12 (m[s[10]!]!) (m[s[11]!]!)
  let v := Blake2.g v 2 7 8 13 (m[s[12]!]!) (m[s[13]!]!)
  Blake2.g v 3 4 9 14 (m[s[14]!]!) (m[s[15]!]!)

-- `n` counts rounds remaining out of `k`, so the round index is `k - n`.
private def Blake2.rounds (m : Array UInt64) (k : Nat) : Nat → Array UInt64 → Array UInt64
  | 0, v => v
  | n + 1, v =>
    let r := k - (n + 1)
    Blake2.rounds m k n (Blake2.round m (blake2Sigma[r % blake2Sigma.size]!) v)

/-- The sixteen BLAKE2b working words held as separate unboxed `UInt64`
scalars, so a compression round never touches the heap. `Array UInt64` stores
*boxed* elements, so every `Array.set!` in `Blake2.g` is a heap allocation and
a later free; a round is eight `Blake2.g` calls and therefore costs 32 of each.
This mirrors `Jaune/Hash.lean`'s `State1600`, which holds keccak's 25 lanes the
same way for the same reason. -/
structure Blake2.WorkingVector where
  (word0 word1 word2 word3 : UInt64)
  (word4 word5 word6 word7 : UInt64)
  (word8 word9 word10 word11 : UInt64)
  (word12 word13 word14 word15 : UInt64)

/-- Bridge from the unboxed working vector to the `Array UInt64` the reference
definitions operate on. It is used by the equivalence theorems and once per
compression, never inside a round. -/
def Blake2.WorkingVector.toArray (w : Blake2.WorkingVector) : Array UInt64 :=
  #[w.word0, w.word1, w.word2, w.word3, w.word4, w.word5, w.word6, w.word7,
    w.word8, w.word9, w.word10, w.word11, w.word12, w.word13, w.word14, w.word15]

/-- `Blake2.round` transliterated onto `Blake2.Vec`: the same eight mixes, in
the same order, over the same literal word indices, with each `Blake2.g` body
inlined as scalar `let` bindings. The message and sigma words are still read
out of arrays — a read does not allocate, only `set!` does. The mix temporary
is named `q` rather than `Blake2.g`'s `s`, which here names the sigma row.
`Blake2.roundVec_toArray` proves this agrees with `Blake2.round`. -/
private def Blake2.roundWorkingVector (m : Array UInt64) (s : Array Nat) (w : Blake2.WorkingVector) :
    Blake2.WorkingVector :=
  let v0 := w.word0
  let v1 := w.word1
  let v2 := w.word2
  let v3 := w.word3
  let v4 := w.word4
  let v5 := w.word5
  let v6 := w.word6
  let v7 := w.word7
  let v8 := w.word8
  let v9 := w.word9
  let v10 := w.word10
  let v11 := w.word11
  let v12 := w.word12
  let v13 := w.word13
  let v14 := w.word14
  let v15 := w.word15
  -- Blake2.g v 0 4 8 12 (m[s[0]!]!) (m[s[1]!]!)
  let x := m[s[0]!]!
  let y := m[s[1]!]!
  let v0 := v0 + v4 + x
  let q := v12 ^^^ v0
  let v12 := (q >>> Blake2.R1) ^^^ (q <<< Blake2.wR1)
  let v8 := v8 + v12
  let q := v4 ^^^ v8
  let v4 := (q >>> Blake2.R2) ^^^ (q <<< Blake2.wR2)
  let v0 := v0 + v4 + y
  let q := v12 ^^^ v0
  let v12 := (q >>> Blake2.R3) ^^^ (q <<< Blake2.wR3)
  let v8 := v8 + v12
  let q := v4 ^^^ v8
  let v4 := (q >>> Blake2.R4) ^^^ (q <<< Blake2.wR4)
  -- Blake2.g v 1 5 9 13 (m[s[2]!]!) (m[s[3]!]!)
  let x := m[s[2]!]!
  let y := m[s[3]!]!
  let v1 := v1 + v5 + x
  let q := v13 ^^^ v1
  let v13 := (q >>> Blake2.R1) ^^^ (q <<< Blake2.wR1)
  let v9 := v9 + v13
  let q := v5 ^^^ v9
  let v5 := (q >>> Blake2.R2) ^^^ (q <<< Blake2.wR2)
  let v1 := v1 + v5 + y
  let q := v13 ^^^ v1
  let v13 := (q >>> Blake2.R3) ^^^ (q <<< Blake2.wR3)
  let v9 := v9 + v13
  let q := v5 ^^^ v9
  let v5 := (q >>> Blake2.R4) ^^^ (q <<< Blake2.wR4)
  -- Blake2.g v 2 6 10 14 (m[s[4]!]!) (m[s[5]!]!)
  let x := m[s[4]!]!
  let y := m[s[5]!]!
  let v2 := v2 + v6 + x
  let q := v14 ^^^ v2
  let v14 := (q >>> Blake2.R1) ^^^ (q <<< Blake2.wR1)
  let v10 := v10 + v14
  let q := v6 ^^^ v10
  let v6 := (q >>> Blake2.R2) ^^^ (q <<< Blake2.wR2)
  let v2 := v2 + v6 + y
  let q := v14 ^^^ v2
  let v14 := (q >>> Blake2.R3) ^^^ (q <<< Blake2.wR3)
  let v10 := v10 + v14
  let q := v6 ^^^ v10
  let v6 := (q >>> Blake2.R4) ^^^ (q <<< Blake2.wR4)
  -- Blake2.g v 3 7 11 15 (m[s[6]!]!) (m[s[7]!]!)
  let x := m[s[6]!]!
  let y := m[s[7]!]!
  let v3 := v3 + v7 + x
  let q := v15 ^^^ v3
  let v15 := (q >>> Blake2.R1) ^^^ (q <<< Blake2.wR1)
  let v11 := v11 + v15
  let q := v7 ^^^ v11
  let v7 := (q >>> Blake2.R2) ^^^ (q <<< Blake2.wR2)
  let v3 := v3 + v7 + y
  let q := v15 ^^^ v3
  let v15 := (q >>> Blake2.R3) ^^^ (q <<< Blake2.wR3)
  let v11 := v11 + v15
  let q := v7 ^^^ v11
  let v7 := (q >>> Blake2.R4) ^^^ (q <<< Blake2.wR4)
  -- Blake2.g v 0 5 10 15 (m[s[8]!]!) (m[s[9]!]!)
  let x := m[s[8]!]!
  let y := m[s[9]!]!
  let v0 := v0 + v5 + x
  let q := v15 ^^^ v0
  let v15 := (q >>> Blake2.R1) ^^^ (q <<< Blake2.wR1)
  let v10 := v10 + v15
  let q := v5 ^^^ v10
  let v5 := (q >>> Blake2.R2) ^^^ (q <<< Blake2.wR2)
  let v0 := v0 + v5 + y
  let q := v15 ^^^ v0
  let v15 := (q >>> Blake2.R3) ^^^ (q <<< Blake2.wR3)
  let v10 := v10 + v15
  let q := v5 ^^^ v10
  let v5 := (q >>> Blake2.R4) ^^^ (q <<< Blake2.wR4)
  -- Blake2.g v 1 6 11 12 (m[s[10]!]!) (m[s[11]!]!)
  let x := m[s[10]!]!
  let y := m[s[11]!]!
  let v1 := v1 + v6 + x
  let q := v12 ^^^ v1
  let v12 := (q >>> Blake2.R1) ^^^ (q <<< Blake2.wR1)
  let v11 := v11 + v12
  let q := v6 ^^^ v11
  let v6 := (q >>> Blake2.R2) ^^^ (q <<< Blake2.wR2)
  let v1 := v1 + v6 + y
  let q := v12 ^^^ v1
  let v12 := (q >>> Blake2.R3) ^^^ (q <<< Blake2.wR3)
  let v11 := v11 + v12
  let q := v6 ^^^ v11
  let v6 := (q >>> Blake2.R4) ^^^ (q <<< Blake2.wR4)
  -- Blake2.g v 2 7 8 13 (m[s[12]!]!) (m[s[13]!]!)
  let x := m[s[12]!]!
  let y := m[s[13]!]!
  let v2 := v2 + v7 + x
  let q := v13 ^^^ v2
  let v13 := (q >>> Blake2.R1) ^^^ (q <<< Blake2.wR1)
  let v8 := v8 + v13
  let q := v7 ^^^ v8
  let v7 := (q >>> Blake2.R2) ^^^ (q <<< Blake2.wR2)
  let v2 := v2 + v7 + y
  let q := v13 ^^^ v2
  let v13 := (q >>> Blake2.R3) ^^^ (q <<< Blake2.wR3)
  let v8 := v8 + v13
  let q := v7 ^^^ v8
  let v7 := (q >>> Blake2.R4) ^^^ (q <<< Blake2.wR4)
  -- Blake2.g v 3 4 9 14 (m[s[14]!]!) (m[s[15]!]!)
  let x := m[s[14]!]!
  let y := m[s[15]!]!
  let v3 := v3 + v4 + x
  let q := v14 ^^^ v3
  let v14 := (q >>> Blake2.R1) ^^^ (q <<< Blake2.wR1)
  let v9 := v9 + v14
  let q := v4 ^^^ v9
  let v4 := (q >>> Blake2.R2) ^^^ (q <<< Blake2.wR2)
  let v3 := v3 + v4 + y
  let q := v14 ^^^ v3
  let v14 := (q >>> Blake2.R3) ^^^ (q <<< Blake2.wR3)
  let v9 := v9 + v14
  let q := v4 ^^^ v9
  let v4 := (q >>> Blake2.R4) ^^^ (q <<< Blake2.wR4)
  ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩

/-- `Blake2.rounds` over the unboxed working vector, with the same `k - (n + 1)`
round index and the same sigma-row lookup. -/
private def Blake2.roundsWorkingVector (m : Array UInt64) (k : Nat) :
    Nat → Blake2.WorkingVector → Blake2.WorkingVector
  | 0, w => w
  | n + 1, w =>
    let r := k - (n + 1)
    Blake2.roundsWorkingVector m k n
      (Blake2.roundWorkingVector m (blake2Sigma[r % blake2Sigma.size]!) w)

-- The two theorems below use an explicit `simp only` set rather than a bare
-- `simp`. A bare `simp` closes them too, but discharges the `0 < 16` / `1 < 16`
-- side conditions of `getElem!_pos` with `Nat.ofNat_pos` and `Nat.one_lt_ofNat`,
-- which are proved classically; the `Nat.reduceLT` simproc decides the same
-- literal comparisons without them. That keeps both axiom sets at exactly
-- `[propext, Quot.sound]`.

/-- The unboxed round agrees with the reference `Blake2.round`: bridging the
working vector to an array commutes with a single round. -/
theorem Blake2.roundWorkingVector_toArray (m : Array UInt64) (s : Array Nat)
    (w : Blake2.WorkingVector) :
    (Blake2.roundWorkingVector m s w).toArray = Blake2.round m s w.toArray := by
  cases w
  simp only [Blake2.WorkingVector.toArray, Blake2.roundWorkingVector, Blake2.round, Blake2.g,
    List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceAdd, getElem!_pos, List.getElem_toArray,
    List.getElem_cons_zero, Nat.reduceLT, List.getElem_cons_succ,
    Array.set!_eq_setIfInBounds, List.setIfInBounds_toArray,
    List.set_cons_zero, List.set_cons_succ, Nat.lt_add_one]

/-- The unboxed rounds loop agrees with the reference `Blake2.rounds`, for
every round budget `k` and every count `n` of rounds remaining. -/
theorem Blake2.roundsWorkingVector_toArray (m : Array UInt64) (k n : Nat)
    (w : Blake2.WorkingVector) :
    (Blake2.roundsWorkingVector m k n w).toArray = Blake2.rounds m k n w.toArray := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    simp only [Blake2.roundsWorkingVector, Blake2.rounds, ih, Blake2.roundWorkingVector_toArray]

/-- The working vector bridged to an array always has sixteen entries: it is a
sixteen-field structure, so this holds of the fields rather than of a length
that has to be maintained. -/
theorem Blake2.size_toArray (w : Blake2.WorkingVector) : w.toArray.size = 16 := rfl

-- compress
--
-- This is the checked wrapper the compression kernel sits behind. The kernel
-- (`Blake2.roundsVec`, and the reference `Blake2.rounds` its equivalence is
-- stated against) reads sixteen message words per round through a sigma row,
-- and those reads are in range exactly when the message is sixteen words and
-- the chaining value eight. Rather than assume that of the caller, this
-- rejects anything else outright — the widths are then types, and every read
-- below is total. `length_readLeUInt64Words` is why `executeBlake2F`'s
-- 213-byte check always satisfies it, and `size_blake2Sigma_get` /
-- `blake2Sigma_lt` are the corresponding facts for the table the kernel
-- indexes with.
def Blake2.compress (numRounds : Nat)
  (h m : List UInt64) (t0 t1 : UInt64) (f : Bool) : Option Bytes :=
  if hh : h.length = 8 then
    if hm : m.length = 16 then
      let hv : Vector UInt64 8 := ⟨h.toArray, by simp [hh]⟩
      let mv : Vector UInt64 16 := ⟨m.toArray, by simp [hm]⟩
      let v14 : UInt64 := blake2IV.getD 6 0
      -- The initial words are loaded into unboxed scalars once, so the rounds
      -- themselves never allocate. The seventeenth word this list used to
      -- carry was written and never read — `Blake2.round` touches indices 0–15
      -- and the tail below reads 0–15 — so it is no longer built.
      let v : Vector UInt64 16 :=
        #v[ hv[0], hv[1], hv[2], hv[3], hv[4], hv[5], hv[6], hv[7],
            blake2IV.getD 0 0, blake2IV.getD 1 0,
            blake2IV.getD 2 0, blake2IV.getD 3 0,
            .xor t0 (blake2IV.getD 4 0),
            .xor t1 (blake2IV.getD 5 0),
            if f then .xor v14 Blake2.maskBits else v14,
            (blake2IV.getD 7 0) ]
      let w : Blake2.WorkingVector :=
        ⟨v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7],
         v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15]⟩
      let out : Vector UInt64 16 :=
        ⟨(Blake2.roundsWorkingVector mv.toArray numRounds numRounds w).toArray,
         Blake2.size_toArray _⟩
      let resultMsgWords : Vector UInt64 8 :=
        Vector.ofFn fun i => hv[i.val] ^^^ out[i.val] ^^^ out[i.val + 8]
      some <| List.flatten <| resultMsgWords.toList.map
        (fun n => n.toBytes.reverse.takeD 8 (0x00 : UInt8))
    else none
  else none

-- blake2f

-- Precompile-facing BLS12-381 byte decoders, relocated here from
-- `Jaune/BLS.lean` by the typed-error migration: their rejection reasons are
-- constructors of the machine-level halt vocabulary declared in
-- `Jaune/Machine.lean` (design report section 6), which `Jaune/BLS.lean`
-- sits upstream of, and every consumer is a precompile in this module. The
-- pure curve, compression and pairing machinery stays in `Jaune/BLS.lean`.

/-- The one reason a precompile converts specially: a decoder rejection that
the gas schedule treats as an out-of-gas halt. -/
def ExceptionalHalt.isInvalidParameter : ExceptionalHalt → Bool
  | .invalidParameter _ => true
  | _ => false

-- def bytes_to_fq(data : Bytes) -> FQ:
def Bytes.toExceptBls12Fp (data : Bytes) : Except ExceptionalHalt Bls12Fp := do
  if data.length ≠ 64 then
    .error (.invalidParameter (.text "input should be 64 bytes long"))
  let x := Bytes.toNat data
  if x ≥ blsPrime then
    .error (.invalidParameter (.text "invalid field element"))
  pure (FieldElement.ofNat x)

-- def bytes_to_g1(data : Bytes) -> Point3D[FQ]:
def Bytes.toExceptBls12G1 (data : Bytes) (subgroupCheck : Bool := false) :
    Except ExceptionalHalt Bls12G1 := do
  if data.length ≠ 128 then
    .error (.invalidParameter (.text "input should be 128 bytes long"))
  let x ← Bytes.toExceptBls12Fp (data.take 64)
  let y ← Bytes.toExceptBls12Fp (data.drop 64)
  let p ← (EllipticCurve.mk? x y).toExcept
    (.invalidParameter (.text "point is not on curve"))
  if subgroupCheck then
    if (p.mulBy blsCurveOrder) ≠ ⟨0, 0⟩ then
      .error (.invalidParameter (.text "subgroup check failed"))
  pure p

def Bytes.toExceptBls12Fp2 (data : Bytes) : Except ExceptionalHalt Bls12Fp2 := do
  if data.length ≠ 128 then
    .error (.invalidParameter (.text "input should be 128 bytes long"))
  let c0 ← Bytes.toExceptBls12Fp (data.take 64)
  let c1 ← Bytes.toExceptBls12Fp (data.drop 64)
  pure ⟨trimZero [c1, c0]⟩

-- def bytes_to_g2(data : Bytes) -> Point3D[FQ2]:
def Bytes.toExceptBls12G2 (data : Bytes) (subgroupCheck : Bool := false) :
    Except ExceptionalHalt Bls12G2 := do
  if data.length ≠ 256 then
    .error (.invalidParameter (.text "input should be 256 bytes long"))
  let x ← Bytes.toExceptBls12Fp2 (data.take 128)
  let y ← Bytes.toExceptBls12Fp2 (data.drop 128)
  let p ← (EllipticCurve.mk? x y).toExcept
    (.invalidParameter (.text "point is not on curve"))
  if subgroupCheck then
    if (p.mulBy blsCurveOrder) ≠ ⟨0, 0⟩ then
      .error (.invalidParameter (.text "subgroup check failed"))
  pure p

def decodeG1MsmPairs (data : Bytes) : Except ExceptionalHalt (List (Bls12G1 × Nat)) :=
  let rec go (fuel : Nat) (acc : List (Bls12G1 × Nat)) (bs : Bytes) :
      Except ExceptionalHalt (List (Bls12G1 × Nat)) :=
    match fuel with
    | 0 => .ok acc.reverse
    | fuel' + 1 =>
      if bs.isEmpty then .ok acc.reverse
      else if bs.length < 160 then
        .error (.invalidParameter (.text "remaining bytes less than 160"))
      else do
        let p ← Bytes.toExceptBls12G1 (bs.take 128) true
        let s := Bytes.toNat ((bs.drop 128).take 32)
        go fuel' ((p, s) :: acc) (bs.drop 160)
  go data.length [] data

def decodeG2MsmPairs (data : Bytes) : Except ExceptionalHalt (List (Bls12G2 × Nat)) :=
  let rec go (fuel : Nat) (acc : List (Bls12G2 × Nat)) (bs : Bytes) :
      Except ExceptionalHalt (List (Bls12G2 × Nat)) :=
    match fuel with
    | 0 => .ok acc.reverse
    | fuel' + 1 =>
      if bs.isEmpty then .ok acc.reverse
      else if bs.length < 288 then
        .error (.invalidParameter (.text "remaining bytes less than 288"))
      else do
        let p ← Bytes.toExceptBls12G2 (bs.take 256) true
        let s := Bytes.toNat ((bs.drop 256).take 32)
        go fuel' ((p, s) :: acc) (bs.drop 288)
  go data.length [] data

-- def decompress_G1(z: G1Compressed) -> G1Uncompressed:
-- 48-byte compressed G1 point with the (c_flag, b_flag, a_flag, x) bit layout.
def decompressG1 (data : Bytes) : Except ExceptionalHalt Bls12G1 := do
  if data.length ≠ 48 then
    .error (.invalidParameter (.text "compressed G1 should be 48 bytes"))
  let z := Bytes.toNat data
  let cFlag := z.testBit 383  -- most significant bit
  let bFlag := z.testBit 382
  let aFlag := z.testBit 381
  -- c_flag == 1 indicates the compressed form.
  if !cFlag then .error (.invalidParameter (.text "c_flag should be 1"))
  -- is_point_at_infinity(z): z % 2^381 == 0.
  let isInf := z % blsTwoPow381 = 0
  if bFlag ≠ isInf then .error (.invalidParameter (.text "b_flag mismatch"))
  if isInf then
    if aFlag then .error (.invalidParameter (.text "infinity a_flag should be 0"))
    pure ⟨0, 0⟩
  else
    let x := z % blsTwoPow381
    if x ≥ blsPrime then
      .error (.invalidParameter (.text "x should be less than field modulus"))
    let xf : Bls12Fp := FieldElement.ofNat x
    -- Y^2 = X^3 + b, b = 4; y = (x^3 + b)^((p+1)/4).
    let rhs := xf ^ 3 + 4
    let y := rhs ^ blsPrimePlus1Div4
    if y ^ 2 ≠ rhs then
      .error (.invalidParameter (.text "the given point is not on G1"))
    -- Choose the y whose leftmost bit equals a_flag: (y * 2) // p.
    let yLead := (y.val * 2) / blsPrime
    let aBit := if aFlag then 1 else 0
    pure ⟨xf, if yLead ≠ aBit then -y else y⟩

-- def validate_kzg_g1(b) followed by pubkey_to_G1: decode + KeyValidate
-- (non-infinity, subgroup check), returning the decompressed point.
def decodeKzgG1 (data : Bytes) : Except ExceptionalHalt Bls12G1 :=
  if data = blsG1PointAtInfinity then
    pure ⟨0, 0⟩
  else do
    let p ← decompressG1 data
    if p = ⟨0, 0⟩ then
      .error (.invalidParameter (.text "point is at infinity"))
    if p.mulBy blsCurveOrder ≠ ⟨0, 0⟩ then
      .error (.invalidParameter (.text "subgroup check failed"))
    pure p

-- def bytes_to_bls_field(b): 32-byte big-endian scalar, must be < BLS_MODULUS.
def bytesToBlsField (data : Bytes) : Except ExceptionalHalt Nat := do
  if data.length ≠ 32 then
    .error (.invalidParameter (.text "field element should be 32 bytes"))
  let v := Bytes.toNat data
  if v ≥ blsModulus then
    .error (.invalidParameter (.text "field element >= BLS modulus"))
  pure v

-- def verify_kzg_proof(commitment_bytes, z_bytes, y_bytes, proof_bytes).
def verifyKzgProof (commitment z y proof : Bytes) :
    Except ExceptionalHalt Bool := do
  let comm ← decodeKzgG1 commitment
  let zf ← bytesToBlsField z
  let yf ← bytesToBlsField y
  let prf ← decodeKzgG1 proof
  pure (verifyKzgProofImpl comm zf yf prf)

/-- EIP-4844 point-evaluation precompile charge, 50,000 gas; execution-specs name
`GAS_POINT_EVALUATION`. -/
def pointEvaluationPrecompileGas : Nat := 50000

-- def point_evaluation(evm : Evm) -> None:

def gasBlsG1Add : Nat := 375
def gasBlsG1Mul : Nat := 12000
def gasBlsG1Map : Nat := 5500
def gasBlsG2Add : Nat := 600
def gasBlsG2Mul : Nat := 22500
def gasBlsG2Map : Nat := 23800

-- bls12_g1_add

-- bls12_g1_msm

-- bls12_g2_add

-- def bls12_g2_msm

-- def bls12_map_fp_to_g1(evm : Evm) -> None :

-- def bytes_to_g1(data : Bytes) -> Point3D[FQ]:
def Bytes.toExceptAltBn128G1 (data : Bytes) : Except ExceptionalHalt AltBn128G1 := do
  if data.length ≠ 64 then
    .error (.invalidParameter (.text "input should be 64 bytes long"))
  let x := data.sliceToNat 0 32
  let y := data.sliceToNat 32 32
  if x >= altBn128Prime then
    .error (.invalidParameter (.text "invalid field element"))
  if y >= altBn128Prime then
    .error (.invalidParameter (.text "invalid field element"))
  (EllipticCurve.mk? (FieldElement.ofNat x) (FieldElement.ofNat y)).toExcept
    (.invalidParameter (.text "point is not on curve"))

-- def bytes_to_g2(data : Bytes) -> Point3D[FQ2]:
def Bytes.toExceptAltBn128G2 (data : Bytes) : Except ExceptionalHalt AltBn128G2 := do
  if data.length ≠ 128 then
    .error (.invalidParameter (.text "input should be 128 bytes long"))
  let x0 := data.sliceToNat 0 32
  let x1 := data.sliceToNat 32 32
  let y0 := data.sliceToNat 64 32
  let y1 := data.sliceToNat 96 32
  if (
    x0 ≥ altBn128Prime ∨
    x1 ≥ altBn128Prime ∨
    y0 ≥ altBn128Prime ∨
    y1 ≥ altBn128Prime
  ) then
    .error (.invalidParameter (.text "invalid field element"))
  (EllipticCurve.mk? (AltBn128Fp2.mk x0 x1) (AltBn128Fp2.mk y0 y1)).toExcept
    (.invalidParameter (.text "point is not on curve"))

def catchWithOutOfGasPrecompile {ξ} (cost : Nat) (cond : ExceptionalHalt → Bool) :
  Except ExceptionalHalt ξ → Except (EvmError × Nat) ξ
  | .ok v => .ok v
  | .error e =>
    if cond e then .error ⟨.halt (.outOfGas .none), cost⟩
    else .error ⟨.halt e, cost⟩

-- def bls12_map_fp2_to_g2(evm : Evm) -> None :

def executeBls12PairingInner (data : Bytes) (cost : Nat) :
    Except (EvmError × Nat) (Nat × Bytes) := do
  let mut result : Bls12Fp12 := 1
  for i in List.range (data.length / 384) do
    let p : Bls12G1 ←
      catchWithOutOfGasPrecompile cost ExceptionalHalt.isInvalidParameter <|
        Bytes.toExceptBls12G1 (data.slice! (i * 384) 128) true
    let q : Bls12G2 ←
      catchWithOutOfGasPrecompile cost ExceptionalHalt.isInvalidParameter <|
        Bytes.toExceptBls12G2 (data.slice! (i * 384 + 128) 256) true
    let pairResult ← match blsPairing q p with
                     | some v => pure v
                     | none => throw ⟨.crypto (.value .none), cost⟩
    result := result * pairResult
  let output : Bytes :=
    if result = 1 then (1 : Nat).toU256.toBytes else (0 : Nat).toU256.toBytes
  pure (cost, output)

-- def bls12_pairing(evm : Evm) -> None :

def executePairingCheckInner (data : Bytes) (cost : Nat) :
    Except (EvmError × Nat) (Nat × Bytes) := do
  if data.length % 192 ≠ 0 then throw ⟨.halt (.outOfGas .none), cost⟩
  let mut result : AltBn128Fp12 := 1
  for i in List.range (data.length / 192) do
    let p : AltBn128G1 ←
      catchWithOutOfGasPrecompile cost ExceptionalHalt.isInvalidParameter <|
        Bytes.toExceptAltBn128G1 (data.slice! (i * 192) 64)
    let q : AltBn128G2 ←
      catchWithOutOfGasPrecompile cost ExceptionalHalt.isInvalidParameter <|
        Bytes.toExceptAltBn128G2 (data.slice! (i * 192 + 64) 128)
    if p * altBn128CurveOrder ≠ ⟨0, 0⟩ then throw ⟨.halt (.outOfGas .none), cost⟩
    if q * altBn128CurveOrder ≠ ⟨0, 0⟩ then throw ⟨.halt (.outOfGas .none), cost⟩
    let pairResult ← match pairing q p with
                     | some v => pure v
                     | none => throw ⟨.crypto (.value .none), cost⟩
    result := result * pairResult
  let output : Bytes := if result = 1 then (1 : Nat).toU256.toBytes else (0 : Nat).toU256.toBytes
  pure (cost, output)

end Jaune
