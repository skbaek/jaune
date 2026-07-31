import Jaune.Machine

namespace Jaune

open Jaune

inductive PrecompResult
| error (msg : String) (cost : Nat)
| ok (cost : Nat) (output : Bytes)

def PrecompResult.chargeGas (cost : Nat) (evm : Evm)
    (pr : Unit → PrecompResult) : PrecompResult :=
  if cost ≤ evm.dyna.gasLeft then pr () else .error "OutOfGasError" 0

def executeEcrecover (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  PrecompResult.chargeGas gasEcrecover evm fun () =>
    let h := Bytes.toB256 <| data.sliceD 0 32 (0x00 : UInt8)
    let v_opt := match (Bytes.toB256 <| data.sliceD 32 32 (0x00 : UInt8)) with
                 | 0x1B => some false
                 | 0x1C => some true
                 | _ => none
    match v_opt with
    | none => .ok gasEcrecover []
    | some v =>
      let r := Bytes.toB256 <| data.sliceD 64 32 (0x00 : UInt8)
      let s := Bytes.toB256 <| data.sliceD 96 32 (0x00 : UInt8)
      if r = 0 ∨ s = 0 ∨
         r ≥ secp256k1.curveOrder.toB256 ∨
         s ≥ secp256k1.curveOrder.toB256 then
        .ok gasEcrecover []
      else
        match secp256k1.recover h v r s with
        | .none => .ok gasEcrecover []
        | some adr => .ok gasEcrecover adr.toB256.toBytes

/-- EIP-7951 `P256VERIFY`.

Two properties of the specification are easy to lose and are deliberate here.
The flat fee is charged before the input is looked at, so a malformed call costs
the same as a well-formed one.  And every rejection -- wrong input length,
out-of-range component, off-curve key, bad signature -- returns empty output
successfully rather than halting, so a caller distinguishes them only by the
returned data size. -/
def executeP256Verify (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  PrecompResult.chargeGas gasP256Verify evm fun () =>
    if data.length ≠ 160 then .ok gasP256Verify []
    else
      let msgHash : Nat := Bytes.toNat <| data.sliceD 0 32 (0 : UInt8)
      let r : Nat := Bytes.toNat <| data.sliceD 32 32 (0 : UInt8)
      let s : Nat := Bytes.toNat <| data.sliceD 64 32 (0 : UInt8)
      let qx : Nat := Bytes.toNat <| data.sliceD 96 32 (0 : UInt8)
      let qy : Nat := Bytes.toNat <| data.sliceD 128 32 (0 : UInt8)
      if secp256r1.verify msgHash r s qx qy then
        .ok gasP256Verify (1 : Nat).toB256.toBytes
      else
        .ok gasP256Verify []

def executeSha256 (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  let cost : Nat := 60 + (12 * (ceilDiv data.length 32))
  PrecompResult.chargeGas cost evm fun () => .ok cost (Bytes.sha256 data).toBytes

def executeRipemd160 (evm : Evm) : PrecompResult :=
  let data : Bytes := evm.sta.data
  let cost : Nat := 600 + (120 * (ceilDiv data.length 32))
  PrecompResult.chargeGas cost evm fun () =>
    let hash : Bytes := data.ripemd160
    let output : Bytes := B256.toBytes <| (Bytes.toB256 <| hash)
    .ok cost output

def executeId (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  let cost := 15 + (3 * (ceilDiv data.length 32))
  PrecompResult.chargeGas cost evm fun () => .ok cost data

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

-- def complexity
def modexpComplexity
  (m : ModexpRules) (baseLength modulusLength : Nat) : Nat :=
  let maxLength := max baseLength modulusLength
  let words := ceilDiv maxLength 8
  match m.flatComplexity with
  | some flat => if maxLength ≤ 32 then flat else m.complexityCoeff * words ^ 2
  | none => m.complexityCoeff * words ^ 2

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
      let lengthPart := m.iterationCoeff * (expLength - 32)
      lengthPart + bitsPart

  max count 1

-- def gas_cost
def modexpGasCost
  (m : ModexpRules) (baseLength modulusLength expLength expHead : Nat) : Nat :=
  let mulComplexity := modexpComplexity m baseLength modulusLength
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

def executeModexp (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  let m : ModexpRules := evm.sta.benvStat.rules.modexp
  let baseLength : Nat := Bytes.sliceToNat data 0 32
  let expLength : Nat := Bytes.sliceToNat data 32 32
  let modulusLength : Nat := Bytes.sliceToNat data 64 32
  if ¬ modexpLengthsInBounds m baseLength expLength modulusLength then
    .error modexpInputLimitTag 0
  else
  let expHead : Nat := Bytes.sliceToNat data (96 + baseLength) (min 32 expLength)
  let cost : Nat := modexpGasCost m baseLength modulusLength expLength expHead
  PrecompResult.chargeGas cost evm fun () =>
    if baseLength = 0 ∧ modulusLength = 0 then .ok cost []
    else
      let base : Nat := Bytes.sliceToNat data 96 baseLength
      let exp : Nat := Bytes.sliceToNat data (96 + baseLength) expLength
      let modulus : Nat := Bytes.sliceToNat data (96 + baseLength + expLength) modulusLength
      let output :=
        if modulus = 0 then List.replicate modulusLength (0x00 : UInt8)
        else (Nat.powMod base exp modulus).toBytes.pack modulusLength
      .ok cost output

-- MODEXP boundary guards.  The schedules themselves are checked against
-- authoritative upstream vectors (`modexp_eip2565.json` for Prague and
-- `modexp_eip7883.json` for Osaka); these pin the points where EIP-7883 and
-- EIP-7823 change behaviour, which a vector corpus can silently stop covering.

-- The multiplication complexity agrees at the 32-byte boundary and diverges
-- immediately above it, where Osaka charges the doubled quadratic term.
#guard modexpComplexity pragueModexpRules 32 32 = 16
#guard modexpComplexity osakaModexpRules 32 32 = 16
#guard modexpComplexity pragueModexpRules 33 0 = 25
#guard modexpComplexity osakaModexpRules 33 0 = 50
#guard modexpComplexity osakaModexpRules 0 32 = 16
#guard modexpComplexity osakaModexpRules 0 33 = 50
-- Below the boundary the flat term is what Osaka charges, not the quadratic
-- one Prague would have used.
#guard modexpComplexity pragueModexpRules 8 8 = 1
#guard modexpComplexity osakaModexpRules 8 8 = 16

-- The exponent-length term doubles above 32 bytes; at or below it, both forks
-- read the same `bit_length - 1` of the exponent head.
#guard modexpIterations pragueModexpRules 32 0 = 1
#guard modexpIterations osakaModexpRules 32 0 = 1
#guard modexpIterations pragueModexpRules 33 0 = 8
#guard modexpIterations osakaModexpRules 33 0 = 16
#guard modexpIterations osakaModexpRules 64 0 = 512
#guard modexpIterations pragueModexpRules 8 255 = 7
#guard modexpIterations osakaModexpRules 8 255 = 7

-- The floor rises from 200 to 500.
#guard modexpGasCost pragueModexpRules 32 32 32 0 = 200
#guard modexpGasCost osakaModexpRules 32 32 32 0 = 500

-- EIP-7823 bounds every header at 1024 and only from Osaka.
#guard modexpLengthsInBounds pragueModexpRules 1025 1025 1025
#guard modexpLengthsInBounds osakaModexpRules 1024 1024 1024
#guard ¬ modexpLengthsInBounds osakaModexpRules 1025 0 0
#guard ¬ modexpLengthsInBounds osakaModexpRules 0 1025 0
#guard ¬ modexpLengthsInBounds osakaModexpRules 0 0 1025

def executeEcadd (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  PrecompResult.chargeGas 150 evm fun () =>
    let x0 : Nat := Bytes.toNat <| data.sliceD 0 32 (0 : UInt8)
    let y0 : Nat := Bytes.toNat <| data.sliceD 32 32 (0 : UInt8)
    let x1 : Nat := Bytes.toNat <| data.sliceD 64 32 (0 : UInt8)
    let y1 : Nat := Bytes.toNat <| data.sliceD 96 32 (0 : UInt8)
    if ¬ (x0 < altBn128Prime ∧ y0 < altBn128Prime ∧ x1 < altBn128Prime ∧ y1 < altBn128Prime) then
      .error "OutOfGasError" 150
    else
      match BNP.mk? x0 y0 with
      | none => .error "OutOfGasError" 150
      | some p0 =>
        match BNP.mk? x1 y1 with
        | none => .error "OutOfGasError" 150
        | some p1 => .ok 150 (BNP.toBytes (p0 + p1))

def executeEcmul (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  PrecompResult.chargeGas 6000 evm fun () =>
    let x : Nat := Bytes.toNat <| data.sliceD 0 32 (0 : UInt8)
    let y : Nat := Bytes.toNat <| data.sliceD 32 32 (0 : UInt8)
    let n : Nat := Bytes.toNat <| data.sliceD 64 32 (0 : UInt8)
    if ¬ (x < altBn128Prime ∧ y < altBn128Prime) then
      .error "OutOfGasError" 6000
    else
      match BNP.mk? x y with
      | none => .error "OutOfGasError" 6000
      | some p => .ok 6000 (BNP.toBytes (p * n))

def b2R1 : UInt64 := 32
def b2R2 : UInt64 := 24
def b2R3 : UInt64 := 16
def b2R4 : UInt64 := 63
def b2MaskBits : UInt64 := 0xFFFFFFFFFFFFFFFF

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
def readLeUInt64Words (data : Bytes) : Nat → Nat → List UInt64
  | _, 0 => []
  | start, num_words + 1 =>
    let wordBytes := data.sliceD start 8 (0x00 : UInt8)
    let word := Bytes.toUInt64 wordBytes.reverse
    word :: readLeUInt64Words data (start + 8) num_words

/-- The reader produces exactly the number of words asked for, whatever the
input length: it is the fact that lets `executeBlake2F`'s 213-byte check stand
in for the chaining value and message widths `bCompress` requires. -/
theorem length_readLeUInt64Words (data : Bytes) (start n : Nat) :
    (readLeUInt64Words data start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [readLeUInt64Words, ih]

def getBlake2Parameters (data : Bytes) :
  Nat × List UInt64 × List UInt64 × UInt64 × UInt64 × Nat :=
  let rounds := Bytes.sliceToNat data 0 4
  let h := readLeUInt64Words data 4 8
  let m := readLeUInt64Words data 68 16
  let t := readLeUInt64Words data 196 2
  let f := Bytes.toNat <| data.drop 212
  ⟨rounds, h, m, t.getD 0 0, t.getD 1 0, f⟩

def blake2R1 : UInt64 := 32
def blake2R2 : UInt64 := 40
def blake2R3 : UInt64 := 48
def blake2R4 : UInt64 := 1

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
def Blake2.g (v : Array UInt64) (a b c d : Nat) (x y : UInt64) : Array UInt64 :=
  let va : UInt64 := v[a]!
  let vb : UInt64 := v[b]!
  let vc : UInt64 := v[c]!
  let vd : UInt64 := v[d]!
  let va : UInt64 := va + vb + x
  let s : UInt64 := vd ^^^ va
  let vd : UInt64 := (s >>> b2R1) ^^^ (s <<< blake2R1)
  let vc : UInt64 := vc + vd
  let s : UInt64 := vb ^^^ vc
  let vb : UInt64 := (s >>> b2R2) ^^^ (s <<< blake2R2)
  let va : UInt64 := va + vb + y
  let s : UInt64 := vd ^^^ va
  let vd : UInt64 := (s >>> b2R3) ^^^ (s <<< blake2R3)
  let vc : UInt64 := vc + vd
  let s : UInt64 := vb ^^^ vc
  let vb : UInt64 := (s >>> b2R4) ^^^ (s <<< blake2R4)
  (((v.set! a va).set! b vb).set! c vc).set! d vd

-- One full mixing round, with `blake2MixTable` unrolled into literal word
-- indices; `m` is an `Array` so the message words are indexed rather than
-- walked as a list.
def Blake2.round (m : Array UInt64) (s : Array Nat) (v : Array UInt64) : Array UInt64 :=
  let v := Blake2.g v 0 4 8 12 (m[s[0]!]!) (m[s[1]!]!)
  let v := Blake2.g v 1 5 9 13 (m[s[2]!]!) (m[s[3]!]!)
  let v := Blake2.g v 2 6 10 14 (m[s[4]!]!) (m[s[5]!]!)
  let v := Blake2.g v 3 7 11 15 (m[s[6]!]!) (m[s[7]!]!)
  let v := Blake2.g v 0 5 10 15 (m[s[8]!]!) (m[s[9]!]!)
  let v := Blake2.g v 1 6 11 12 (m[s[10]!]!) (m[s[11]!]!)
  let v := Blake2.g v 2 7 8 13 (m[s[12]!]!) (m[s[13]!]!)
  Blake2.g v 3 4 9 14 (m[s[14]!]!) (m[s[15]!]!)

-- `n` counts rounds remaining out of `k`, so the round index is `k - n`.
def Blake2.rounds (m : Array UInt64) (k : Nat) : Nat → Array UInt64 → Array UInt64
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
structure Blake2.Vec where
  (v0 v1 v2 v3 : UInt64)
  (v4 v5 v6 v7 : UInt64)
  (v8 v9 v10 v11 : UInt64)
  (v12 v13 v14 v15 : UInt64)

/-- Bridge from the unboxed working vector to the `Array UInt64` the reference
definitions operate on. It is used by the equivalence theorems and once per
compression, never inside a round. -/
def Blake2.Vec.toArray (w : Blake2.Vec) : Array UInt64 :=
  #[w.v0, w.v1, w.v2, w.v3, w.v4, w.v5, w.v6, w.v7,
    w.v8, w.v9, w.v10, w.v11, w.v12, w.v13, w.v14, w.v15]

/-- `Blake2.round` transliterated onto `Blake2.Vec`: the same eight mixes, in
the same order, over the same literal word indices, with each `Blake2.g` body
inlined as scalar `let` bindings. The message and sigma words are still read
out of arrays — a read does not allocate, only `set!` does. The mix temporary
is named `q` rather than `Blake2.g`'s `s`, which here names the sigma row.
`Blake2.roundVec_toArray` proves this agrees with `Blake2.round`. -/
def Blake2.roundVec (m : Array UInt64) (s : Array Nat) (w : Blake2.Vec) :
    Blake2.Vec :=
  let v0 := w.v0
  let v1 := w.v1
  let v2 := w.v2
  let v3 := w.v3
  let v4 := w.v4
  let v5 := w.v5
  let v6 := w.v6
  let v7 := w.v7
  let v8 := w.v8
  let v9 := w.v9
  let v10 := w.v10
  let v11 := w.v11
  let v12 := w.v12
  let v13 := w.v13
  let v14 := w.v14
  let v15 := w.v15
  -- Blake2.g v 0 4 8 12 (m[s[0]!]!) (m[s[1]!]!)
  let x := m[s[0]!]!
  let y := m[s[1]!]!
  let v0 := v0 + v4 + x
  let q := v12 ^^^ v0
  let v12 := (q >>> b2R1) ^^^ (q <<< blake2R1)
  let v8 := v8 + v12
  let q := v4 ^^^ v8
  let v4 := (q >>> b2R2) ^^^ (q <<< blake2R2)
  let v0 := v0 + v4 + y
  let q := v12 ^^^ v0
  let v12 := (q >>> b2R3) ^^^ (q <<< blake2R3)
  let v8 := v8 + v12
  let q := v4 ^^^ v8
  let v4 := (q >>> b2R4) ^^^ (q <<< blake2R4)
  -- Blake2.g v 1 5 9 13 (m[s[2]!]!) (m[s[3]!]!)
  let x := m[s[2]!]!
  let y := m[s[3]!]!
  let v1 := v1 + v5 + x
  let q := v13 ^^^ v1
  let v13 := (q >>> b2R1) ^^^ (q <<< blake2R1)
  let v9 := v9 + v13
  let q := v5 ^^^ v9
  let v5 := (q >>> b2R2) ^^^ (q <<< blake2R2)
  let v1 := v1 + v5 + y
  let q := v13 ^^^ v1
  let v13 := (q >>> b2R3) ^^^ (q <<< blake2R3)
  let v9 := v9 + v13
  let q := v5 ^^^ v9
  let v5 := (q >>> b2R4) ^^^ (q <<< blake2R4)
  -- Blake2.g v 2 6 10 14 (m[s[4]!]!) (m[s[5]!]!)
  let x := m[s[4]!]!
  let y := m[s[5]!]!
  let v2 := v2 + v6 + x
  let q := v14 ^^^ v2
  let v14 := (q >>> b2R1) ^^^ (q <<< blake2R1)
  let v10 := v10 + v14
  let q := v6 ^^^ v10
  let v6 := (q >>> b2R2) ^^^ (q <<< blake2R2)
  let v2 := v2 + v6 + y
  let q := v14 ^^^ v2
  let v14 := (q >>> b2R3) ^^^ (q <<< blake2R3)
  let v10 := v10 + v14
  let q := v6 ^^^ v10
  let v6 := (q >>> b2R4) ^^^ (q <<< blake2R4)
  -- Blake2.g v 3 7 11 15 (m[s[6]!]!) (m[s[7]!]!)
  let x := m[s[6]!]!
  let y := m[s[7]!]!
  let v3 := v3 + v7 + x
  let q := v15 ^^^ v3
  let v15 := (q >>> b2R1) ^^^ (q <<< blake2R1)
  let v11 := v11 + v15
  let q := v7 ^^^ v11
  let v7 := (q >>> b2R2) ^^^ (q <<< blake2R2)
  let v3 := v3 + v7 + y
  let q := v15 ^^^ v3
  let v15 := (q >>> b2R3) ^^^ (q <<< blake2R3)
  let v11 := v11 + v15
  let q := v7 ^^^ v11
  let v7 := (q >>> b2R4) ^^^ (q <<< blake2R4)
  -- Blake2.g v 0 5 10 15 (m[s[8]!]!) (m[s[9]!]!)
  let x := m[s[8]!]!
  let y := m[s[9]!]!
  let v0 := v0 + v5 + x
  let q := v15 ^^^ v0
  let v15 := (q >>> b2R1) ^^^ (q <<< blake2R1)
  let v10 := v10 + v15
  let q := v5 ^^^ v10
  let v5 := (q >>> b2R2) ^^^ (q <<< blake2R2)
  let v0 := v0 + v5 + y
  let q := v15 ^^^ v0
  let v15 := (q >>> b2R3) ^^^ (q <<< blake2R3)
  let v10 := v10 + v15
  let q := v5 ^^^ v10
  let v5 := (q >>> b2R4) ^^^ (q <<< blake2R4)
  -- Blake2.g v 1 6 11 12 (m[s[10]!]!) (m[s[11]!]!)
  let x := m[s[10]!]!
  let y := m[s[11]!]!
  let v1 := v1 + v6 + x
  let q := v12 ^^^ v1
  let v12 := (q >>> b2R1) ^^^ (q <<< blake2R1)
  let v11 := v11 + v12
  let q := v6 ^^^ v11
  let v6 := (q >>> b2R2) ^^^ (q <<< blake2R2)
  let v1 := v1 + v6 + y
  let q := v12 ^^^ v1
  let v12 := (q >>> b2R3) ^^^ (q <<< blake2R3)
  let v11 := v11 + v12
  let q := v6 ^^^ v11
  let v6 := (q >>> b2R4) ^^^ (q <<< blake2R4)
  -- Blake2.g v 2 7 8 13 (m[s[12]!]!) (m[s[13]!]!)
  let x := m[s[12]!]!
  let y := m[s[13]!]!
  let v2 := v2 + v7 + x
  let q := v13 ^^^ v2
  let v13 := (q >>> b2R1) ^^^ (q <<< blake2R1)
  let v8 := v8 + v13
  let q := v7 ^^^ v8
  let v7 := (q >>> b2R2) ^^^ (q <<< blake2R2)
  let v2 := v2 + v7 + y
  let q := v13 ^^^ v2
  let v13 := (q >>> b2R3) ^^^ (q <<< blake2R3)
  let v8 := v8 + v13
  let q := v7 ^^^ v8
  let v7 := (q >>> b2R4) ^^^ (q <<< blake2R4)
  -- Blake2.g v 3 4 9 14 (m[s[14]!]!) (m[s[15]!]!)
  let x := m[s[14]!]!
  let y := m[s[15]!]!
  let v3 := v3 + v4 + x
  let q := v14 ^^^ v3
  let v14 := (q >>> b2R1) ^^^ (q <<< blake2R1)
  let v9 := v9 + v14
  let q := v4 ^^^ v9
  let v4 := (q >>> b2R2) ^^^ (q <<< blake2R2)
  let v3 := v3 + v4 + y
  let q := v14 ^^^ v3
  let v14 := (q >>> b2R3) ^^^ (q <<< blake2R3)
  let v9 := v9 + v14
  let q := v4 ^^^ v9
  let v4 := (q >>> b2R4) ^^^ (q <<< blake2R4)
  ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩

/-- `Blake2.rounds` over the unboxed working vector, with the same `k - (n + 1)`
round index and the same sigma-row lookup. -/
def Blake2.roundsVec (m : Array UInt64) (k : Nat) :
    Nat → Blake2.Vec → Blake2.Vec
  | 0, w => w
  | n + 1, w =>
    let r := k - (n + 1)
    Blake2.roundsVec m k n
      (Blake2.roundVec m (blake2Sigma[r % blake2Sigma.size]!) w)

-- The two theorems below use an explicit `simp only` set rather than a bare
-- `simp`. A bare `simp` closes them too, but discharges the `0 < 16` / `1 < 16`
-- side conditions of `getElem!_pos` with `Nat.ofNat_pos` and `Nat.one_lt_ofNat`,
-- which are proved classically; the `Nat.reduceLT` simproc decides the same
-- literal comparisons without them. That keeps both axiom sets at exactly
-- `[propext, Quot.sound]`.

/-- The unboxed round agrees with the reference `Blake2.round`: bridging the
working vector to an array commutes with a single round. -/
theorem Blake2.roundVec_toArray (m : Array UInt64) (s : Array Nat)
    (w : Blake2.Vec) :
    (Blake2.roundVec m s w).toArray = Blake2.round m s w.toArray := by
  cases w
  simp only [Blake2.Vec.toArray, Blake2.roundVec, Blake2.round, Blake2.g,
    List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceAdd, getElem!_pos, List.getElem_toArray,
    List.getElem_cons_zero, Nat.reduceLT, List.getElem_cons_succ,
    Array.set!_eq_setIfInBounds, List.setIfInBounds_toArray,
    List.set_cons_zero, List.set_cons_succ, Nat.lt_add_one]

/-- The unboxed rounds loop agrees with the reference `Blake2.rounds`, for
every round budget `k` and every count `n` of rounds remaining. -/
theorem Blake2.roundsVec_toArray (m : Array UInt64) (k n : Nat)
    (w : Blake2.Vec) :
    (Blake2.roundsVec m k n w).toArray = Blake2.rounds m k n w.toArray := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    simp only [Blake2.roundsVec, Blake2.rounds, ih, Blake2.roundVec_toArray]

/-- The working vector bridged to an array always has sixteen entries: it is a
sixteen-field structure, so this holds of the fields rather than of a length
that has to be maintained. -/
theorem Blake2.size_toArray (w : Blake2.Vec) : w.toArray.size = 16 := rfl

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
def bCompress (numRounds : Nat)
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
            if f then .xor v14 b2MaskBits else v14,
            (blake2IV.getD 7 0) ]
      let w : Blake2.Vec :=
        ⟨v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7],
         v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15]⟩
      let out : Vector UInt64 16 :=
        ⟨(Blake2.roundsVec mv.toArray numRounds numRounds w).toArray,
         Blake2.size_toArray _⟩
      let resultMsgWords : Vector UInt64 8 :=
        Vector.ofFn fun i => hv[i.val] ^^^ out[i.val] ^^^ out[i.val + 8]
      some <| List.flatten <| resultMsgWords.toList.map
        (fun n => n.toBytes.reverse.takeD 8 (0x00 : UInt8))
    else none
  else none

-- The precompile's own length check is what makes the widths above hold; these
-- pin that the reader really does produce eight and sixteen words.
#guard (readLeUInt64Words (List.replicate 213 (0x00 : UInt8)) 4 8).length = 8
#guard (readLeUInt64Words (List.replicate 213 (0x00 : UInt8)) 68 16).length = 16

-- blake2f
def executeBlake2F (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 213 then .error "InvalidParameter" 0
  else
    let ⟨rounds, h, m, t0, t1, fn⟩ := getBlake2Parameters data
    let cost := gasBlake2PerRound * rounds
    PrecompResult.chargeGas cost evm fun () =>
      match fn with
      | 0 =>
        match bCompress rounds h m t0 t1 false with
        | some output => .ok cost output
        | none => .error "bCompress failed" cost
      | 1 =>
        match bCompress rounds h m t0 t1 true with
        | some output => .ok cost output
        | none => .error "bCompress failed" cost
      | _ => .error "InvalidParameter" cost

def gasPointEval : Nat := 50000

-- def point_evaluation(evm : Evm) -> None:
def executePointEval (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 192 then .error "KZGProofError" 0
  else
    PrecompResult.chargeGas gasPointEval evm fun () =>
      let versionedHash := data.take 32
      let z := (data.drop 32).take 32
      let y := (data.drop 64).take 32
      let commitment := (data.drop 96).take 48
      let proof := (data.drop 144).take 48
      if kzgCommitmentToVersionedHash commitment ≠ versionedHash then
        .error "KZGProofError" gasPointEval
      else
        match verifyKzgProof commitment z y proof with
        | .ok true =>
          .ok gasPointEval ((4096 : Nat).toB256.toBytes ++ blsModulus.toB256.toBytes)
        | _ => .error "KZGProofError" gasPointEval

def gasBlsG1Add : Nat := 375
def gasBlsG1Mul : Nat := 12000
def gasBlsG1Map : Nat := 5500
def gasBlsG2Add : Nat := 600
def gasBlsG2Mul : Nat := 22500
def gasBlsG2Map : Nat := 23800

-- bls12_g1_add
def executeBls12G1Add (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 256 then .error "InvalidParameter" 0
  else
    PrecompResult.chargeGas gasBlsG1Add evm fun () =>
      match Bytes.toExStrBLSP (data.take 128), Bytes.toExStrBLSP (data.drop 128) with
      | .ok p1, .ok p2 => .ok gasBlsG1Add (BLSP.toBytes (p1 + p2))
      | _, _ => .error "OutOfGasError" gasBlsG1Add

-- bls12_g1_msm
def executeBls12G1Msm (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length = 0 ∨ data.length % g1MsmLengthPerPair ≠ 0 then
    .error s!"InvalidParameter : {data.length} is not a valid input length" 0
  else
    let k := data.length / g1MsmLengthPerPair
    let discount := List.getD g1KDiscount (k - 1) g1MaxDiscount
    let gasCost := (k * gasBlsG1Mul * discount) / 1000
    PrecompResult.chargeGas gasCost evm fun () =>
      match decodeG1MsmPairs data with
      | .ok pairs => .ok gasCost (g1MsmSum pairs).toBytes
      | .error _ => .error "OutOfGasError" gasCost

-- bls12_g2_add
def executeBls12G2Add (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 512 then .error "InvalidParameter" 0
  else
    PrecompResult.chargeGas gasBlsG2Add evm fun () =>
      match Bytes.toExStrBLSP2 (data.take 256), Bytes.toExStrBLSP2 (data.drop 256) with
      | .ok p1, .ok p2 => .ok gasBlsG2Add (BLSP2.toBytes (p1 + p2))
      | _, _ => .error "OutOfGasError" gasBlsG2Add

-- def bls12_g2_msm
def executeBls12G2Msm (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length = 0 ∨ data.length % g2MsmLengthPerPair ≠ 0 then
    .error s!"InvalidParameter : {data.length} is not a valid input length" 0
  else
    let k := data.length / g2MsmLengthPerPair
    let discount := List.getD g2KDiscount (k - 1) g2MaxDiscount
    let gasCost := (k * gasBlsG2Mul * discount) / 1000
    PrecompResult.chargeGas gasCost evm fun () =>
      match decodeG2MsmPairs data with
      | .ok pairs => .ok gasCost (g2MsmSum pairs).toBytes
      | .error _ => .error "OutOfGasError" gasCost

-- def bls12_map_fp_to_g1(evm : Evm) -> None :
def executeBls12MapFpToG1 (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 64 then .error "InvalidParameter" 0
  else
    PrecompResult.chargeGas gasBlsG1Map evm fun () =>
      match Bytes.toExStrBLSF data with
      | .ok fp => .ok gasBlsG1Map (BLSP.toBytes (blsMapFpToG1 fp))
      | .error _ => .error "OutOfGasError" gasBlsG1Map

-- def bytes_to_g1(data : Bytes) -> Point3D[FQ]:
def Bytes.toExStrBNP (data : Bytes) : Except String BNP := do
  if data.length ≠ 64 then
    .error "InvalidParameter : input should be 64 bytes long"
  let x := data.sliceToNat 0 32
  let y := data.sliceToNat 32 32
  if x >= altBn128Prime then
    .error "InvalidParameter : invalid field element"
  if y >= altBn128Prime then
    .error "InvalidParameter : invalid field element"
  (EllipticCurve.mk? (FinField.ofNat x) (FinField.ofNat y)).toExcept
    "InvalidParameter : point is not on curve"

-- def bytes_to_g2(data : Bytes) -> Point3D[FQ2]:
def Bytes.toExStrBNP2 (data : Bytes) : Except String BNP2 := do
  if data.length ≠ 128 then
    .error "InvalidParameter : input should be 128 bytes long"
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
    .error "InvalidParameter : invalid field element"
  (EllipticCurve.mk? (BNF2.mk x0 x1) (BNF2.mk y0 y1)).toExcept
    "InvalidParameter : point is not on curve"

def catchWithOOGPrecomp {ξ} (cost : Nat) (cond : String → Bool) :
  Except String ξ → Except (String × Nat) ξ
  | .ok v => .ok v
  | .error e => if cond e then .error ⟨"OutOfGasError", cost⟩ else .error ⟨e, cost⟩

-- def bls12_map_fp2_to_g2(evm : Evm) -> None :
def executeBls12MapFp2ToG2 (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 128 then .error "InvalidParameter" 0
  else
    PrecompResult.chargeGas gasBlsG2Map evm fun () =>
      match Bytes.toExStrBLSF2 data with
      | .ok fp2 => .ok gasBlsG2Map (BLSP2.toBytes (blsMapFp2ToG2 fp2))
      | .error _ => .error "OutOfGasError" gasBlsG2Map

def executeBls12PairingInner (data : Bytes) (cost : Nat) :
    Except (String × Nat) (Nat × Bytes) := do
  let mut result : BLSF12 := 1
  for i in List.range (data.length / 384) do
    let p : BLSP ←
      catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
        Bytes.toExStrBLSP (data.slice! (i * 384) 128) true
    let q : BLSP2 ←
      catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
        Bytes.toExStrBLSP2 (data.slice! (i * 384 + 128) 256) true
    let pairResult ← match blsPairing q p with
                     | some v => pure v
                     | none => throw ⟨"ValueError", cost⟩
    result := result * pairResult
  let output : Bytes :=
    if result = 1 then (1 : Nat).toB256.toBytes else (0 : Nat).toB256.toBytes
  pure (cost, output)

-- def bls12_pairing(evm : Evm) -> None :
def executeBls12Pairing (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length = 0 ∨ data.length % 384 ≠ 0 then
    .error s!"InvalidParameter : {data.length} is not a valid input length" 0
  else
    let k := data.length / 384
    let gasCost := (32600 * k + 37700)
    PrecompResult.chargeGas gasCost evm fun () =>
      match executeBls12PairingInner data gasCost with
      | .ok ⟨cost, output⟩ => .ok cost output
      | .error ⟨msg, cost⟩ => .error msg cost

def executePairingCheckInner (data : Bytes) (cost : Nat) :
    Except (String × Nat) (Nat × Bytes) := do
  if data.length % 192 ≠ 0 then throw ⟨"OutOfGasError", cost⟩
  let mut result : BNF12 := 1
  for i in List.range (data.length / 192) do
    let p : BNP ←
      catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
        Bytes.toExStrBNP (data.slice! (i * 192) 64)
    let q : BNP2 ←
      catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
        Bytes.toExStrBNP2 (data.slice! (i * 192 + 64) 128)
    if p * altBn128CurveOrder ≠ ⟨0, 0⟩ then throw ⟨"OutOfGasError", cost⟩
    if q * altBn128CurveOrder ≠ ⟨0, 0⟩ then throw ⟨"OutOfGasError", cost⟩
    let pairResult ← match pairing q p with
                     | some v => pure v
                     | none => throw ⟨"ValueError", cost⟩
    result := result * pairResult
  let output : Bytes := if result = 1 then (1 : Nat).toB256.toBytes else (0 : Nat).toB256.toBytes
  pure (cost, output)

def executePairingCheck (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  let cost := (34000 * (data.length / 192)) + 45000
  PrecompResult.chargeGas cost evm fun () =>
    let inner := executePairingCheckInner data cost
    match inner with
    | .ok ⟨cost, output⟩ => .ok cost output
    | .error ⟨msg, cost⟩ => .error msg cost

def precompileRun (evm : Evm) : Adr → PrecompResult
  | 1 => executeEcrecover evm -- 0x1
  | 2 => executeSha256 evm -- 0x2
  | 3 => executeRipemd160 evm -- 0x3
  | 4 => executeId evm -- 0x4
  | 5 => executeModexp evm -- 0x5
  | 6 => executeEcadd evm -- 0x6
  | 7 => executeEcmul evm -- 0x7
  | 8 => executePairingCheck evm --  0x8
  | 9 => executeBlake2F evm -- 0x9
  | 10 => executePointEval evm -- 0xA
  | 11 => executeBls12G1Add evm --  0xB
  | 12 => executeBls12G1Msm evm --  0xC
  | 13 => executeBls12G2Add evm --  0xD
  | 14 => executeBls12G2Msm evm --  0xE
  | 15 => executeBls12Pairing evm -- 0xF
  | 16 => executeBls12MapFpToG1 evm -- 0x10
  | 17 => executeBls12MapFp2ToG2 evm -- 0x11
  | 256 => executeP256Verify evm -- 0x100
  | n => .error s!"ERROR : precompiled contract {n} does not exist" 0

def applyPrecompResult (evm : Evm) (res : PrecompResult) : Execution :=
  match res with
  | .error msg cost => .error ⟨msg, evm.dyna.withGasLeft (evm.dyna.gasLeft - cost)⟩
  | .ok cost output =>
    .ok <| (evm.dyna.withGasLeft (evm.dyna.gasLeft - cost)).withOutput output

def executePrecomp (evm : Evm) (adr : Adr) : Execution :=
  applyPrecompResult evm (precompileRun evm adr)

/-- Precompiles never touch the world: a `PrecompResult` carries only a cost
and an output, and `applyPrecompResult` applies them with `withGasLeft` and
`withOutput` on both channels. -/
theorem applyPrecompResult_canonical {evm : Evm} (h : evm.dyna.Canonical)
    (res : PrecompResult) : (applyPrecompResult evm res).Canonical := by
  unfold applyPrecompResult
  split <;> exact Devm.Canonical.of_world_eq h rfl

theorem executePrecomp_canonical {evm : Evm} (h : evm.dyna.Canonical)
    (adr : Adr) : (executePrecomp evm adr).Canonical :=
  applyPrecompResult_canonical h (precompileRun evm adr)

end Jaune
