import Jaune.Precompiles

/-!
# The precompile interface over its own input (goal `jaune-shape-and-names-v1`, G2b, F1b)

A precompile reads three things of the frame that calls it: the input bytes, the gas it may spend,
and the rules that price it (MODEXP's and BN254's schedules). `PrecompileInput` holds exactly
those, and `Precompile.run` dispatches the eighteen precompiles over it. The bodies are the
`execute*` wrappers of `Jaune.Precompiles` with `evm.sta.data`, `evm.dyna.gasLeft` and
`evm.sta.benvStat.rules` read from the input instead; the cryptography they call is shared and
unchanged. `Jaune.Bridge.G2b.PrecompileInput` proves the two agree for every `Evm`.

The rules are derived from the fork, as `BenvStat.rules` derives them, so the only rule sets an
input can carry are the fork records.
-/

namespace Jaune

open Jaune

/-- What a precompile reads of the frame that runs it. -/
structure PrecompileInput : Type where
  /-- The input bytes (`CALLDATA`). -/
  calldata : Bytes
  /-- The gas the precompile may spend: the frame's gas left. -/
  gasLeft : Nat
  /-- The fork whose rules price the precompile. -/
  fork : Fork

/-- The rules the input runs under. -/
def PrecompileInput.rules (input : PrecompileInput) : ForkRules := Fork.ruleSet input.fork

namespace Precompile

/-- Charge `cost` if the input's gas covers it, else halt out of gas having spent nothing. -/
def chargeGas (cost : Nat) (input : PrecompileInput)
    (pr : Unit → PrecompileResult) : PrecompileResult :=
  if cost ≤ input.gasLeft then pr () else .error (.halt (.outOfGas .none)) 0

/-- `ECRECOVER` (0x01). -/
def ecrecover (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  chargeGas Gas.ecrecover input fun () =>
    let h := Bytes.toU256 <| data.sliceD 0 32 (0x00 : UInt8)
    let v_opt := match (Bytes.toU256 <| data.sliceD 32 32 (0x00 : UInt8)) with
                 | 0x1B => some false
                 | 0x1C => some true
                 | _ => none
    match v_opt with
    | none => .ok Gas.ecrecover []
    | some v =>
      let r := Bytes.toU256 <| data.sliceD 64 32 (0x00 : UInt8)
      let s := Bytes.toU256 <| data.sliceD 96 32 (0x00 : UInt8)
      if r = 0 ∨ s = 0 ∨
         r ≥ secp256k1.curveOrder.toU256 ∨
         s ≥ secp256k1.curveOrder.toU256 then
        .ok Gas.ecrecover []
      else
        match secp256k1.recover h v r s with
        | .none => .ok Gas.ecrecover []
        | some adr => .ok Gas.ecrecover adr.toU256.toBytes

/-- EIP-7951 `P256VERIFY` (0x100). The flat fee is charged before the input is read, and every
rejection returns empty output successfully. -/
def p256verify (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  chargeGas Gas.p256verify input fun () =>
    if data.length ≠ 160 then .ok Gas.p256verify []
    else
      let msgHash : Nat := Bytes.toNat <| data.sliceD 0 32 (0 : UInt8)
      let r : Nat := Bytes.toNat <| data.sliceD 32 32 (0 : UInt8)
      let s : Nat := Bytes.toNat <| data.sliceD 64 32 (0 : UInt8)
      let qx : Nat := Bytes.toNat <| data.sliceD 96 32 (0 : UInt8)
      let qy : Nat := Bytes.toNat <| data.sliceD 128 32 (0 : UInt8)
      if secp256r1.verify msgHash r s qx qy then
        .ok Gas.p256verify (1 : Nat).toU256.toBytes
      else
        .ok Gas.p256verify []

/-- `SHA256` (0x02). -/
def sha256 (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  let cost : Nat := 60 + (12 * (ceilDiv data.length 32))
  chargeGas cost input fun () => .ok cost (Bytes.sha256 data).toBytes

/-- `RIPEMD160` (0x03). -/
def ripemd160 (input : PrecompileInput) : PrecompileResult :=
  let data : Bytes := input.calldata
  let cost : Nat := 600 + (120 * (ceilDiv data.length 32))
  chargeGas cost input fun () =>
    let hash : Bytes := data.ripemd160
    let output : Bytes := U256.toBytes <| (Bytes.toU256 <| hash)
    .ok cost output

/-- The identity precompile (0x04). -/
def identity (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  let cost := 15 + (3 * (ceilDiv data.length 32))
  chargeGas cost input fun () => .ok cost data

/-- EIP-198 `MODEXP` (0x05), priced by the fork's schedule. -/
def modexp (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  let m : ModexpRules := input.rules.modexp
  let c : ModexpComplexity := input.rules.modexpComplexity
  let baseLength : Nat := Bytes.sliceToNat data 0 32
  let expLength : Nat := Bytes.sliceToNat data 32 32
  let modulusLength : Nat := Bytes.sliceToNat data 64 32
  if ¬ modexpLengthsInBounds m baseLength expLength modulusLength then
    .error (.halt (.modexpInputLimit .none)) 0
  else
  let expHead : Nat := Bytes.sliceToNat data (96 + baseLength) (min 32 expLength)
  let cost : Nat := modexpGasCost c m baseLength modulusLength expLength expHead
  chargeGas cost input fun () =>
    if baseLength = 0 ∧ modulusLength = 0 then .ok cost []
    else
      let base : Nat := Bytes.sliceToNat data 96 baseLength
      let exp : Nat := Bytes.sliceToNat data (96 + baseLength) expLength
      let modulus : Nat := Bytes.sliceToNat data (96 + baseLength + expLength) modulusLength
      let output :=
        if modulus = 0 then List.replicate modulusLength (0x00 : UInt8)
        else (Nat.powMod base exp modulus).toBytes.pack modulusLength
      .ok cost output

/-- EIP-196 `ECADD` on BN254 (0x06). -/
def ecAdd (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  let g : Nat := input.rules.altBn128.add
  chargeGas g input fun () =>
    let x0 : Nat := Bytes.toNat <| data.sliceD 0 32 (0 : UInt8)
    let y0 : Nat := Bytes.toNat <| data.sliceD 32 32 (0 : UInt8)
    let x1 : Nat := Bytes.toNat <| data.sliceD 64 32 (0 : UInt8)
    let y1 : Nat := Bytes.toNat <| data.sliceD 96 32 (0 : UInt8)
    if ¬ (x0 < altBn128Prime ∧ y0 < altBn128Prime ∧ x1 < altBn128Prime ∧ y1 < altBn128Prime) then
      .error (.halt (.outOfGas .none)) g
    else
      match AltBn128G1.mk? x0 y0 with
      | none => .error (.halt (.outOfGas .none)) g
      | some p0 =>
        match AltBn128G1.mk? x1 y1 with
        | none => .error (.halt (.outOfGas .none)) g
        | some p1 => .ok g (AltBn128G1.toBytes (p0 + p1))

/-- EIP-196 `ECMUL` on BN254 (0x07). -/
def ecMul (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  let g : Nat := input.rules.altBn128.mul
  chargeGas g input fun () =>
    let x : Nat := Bytes.toNat <| data.sliceD 0 32 (0 : UInt8)
    let y : Nat := Bytes.toNat <| data.sliceD 32 32 (0 : UInt8)
    let n : Nat := Bytes.toNat <| data.sliceD 64 32 (0 : UInt8)
    if ¬ (x < altBn128Prime ∧ y < altBn128Prime) then
      .error (.halt (.outOfGas .none)) g
    else
      match AltBn128G1.mk? x y with
      | none => .error (.halt (.outOfGas .none)) g
      | some p => .ok g (AltBn128G1.toBytes (p * n))

/-- EIP-152 `BLAKE2F` (0x09). -/
def blake2f (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  if data.length ≠ 213 then .error (.halt (.invalidParameter .none)) 0
  else
    let ⟨rounds, h, m, t0, t1, fn⟩ := getBlake2Parameters data
    let cost := Gas.gfround * rounds
    chargeGas cost input fun () =>
      match fn with
      | 0 =>
        match Blake2.compress rounds h m t0 t1 false with
        | some output => .ok cost output
        | none => .error (.crypto (.pointCompression .none)) cost
      | 1 =>
        match Blake2.compress rounds h m t0 t1 true with
        | some output => .ok cost output
        | none => .error (.crypto (.pointCompression .none)) cost
      | _ => .error (.halt (.invalidParameter .none)) cost

/-- EIP-4844 point evaluation (0x0A). -/
def pointEvaluation (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  if data.length ≠ 192 then .error (.halt (.kzgProof .none)) 0
  else
    chargeGas pointEvaluationPrecompileGas input fun () =>
      let versionedHash := data.take 32
      let z := (data.drop 32).take 32
      let y := (data.drop 64).take 32
      let commitment := (data.drop 96).take 48
      let proof := (data.drop 144).take 48
      if kzgCommitmentToVersionedHash commitment ≠ versionedHash then
        .error (.halt (.kzgProof .none)) pointEvaluationPrecompileGas
      else
        match verifyKzgProof commitment z y proof with
        | .ok true =>
          .ok pointEvaluationPrecompileGas ((4096 : Nat).toU256.toBytes ++ blsModulus.toU256.toBytes)
        | _ => .error (.halt (.kzgProof .none)) pointEvaluationPrecompileGas

/-- EIP-2537 `BLS12_G1ADD` (0x0B). -/
def bls12G1Add (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  if data.length ≠ 256 then .error (.halt (.invalidParameter .none)) 0
  else
    chargeGas gasBlsG1Add input fun () =>
      match Bytes.toExceptBls12G1 (data.take 128), Bytes.toExceptBls12G1 (data.drop 128) with
      | .ok p1, .ok p2 => .ok gasBlsG1Add (Bls12G1.toBytes (p1 + p2))
      | _, _ => .error (.halt (.outOfGas .none)) gasBlsG1Add

/-- EIP-2537 `BLS12_G1MSM` (0x0C). -/
def bls12G1Msm (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  if data.length = 0 ∨ data.length % g1MsmLengthPerPair ≠ 0 then
    .error (.halt (.invalidParameter
      (.text s!"{data.length} is not a valid input length"))) 0
  else
    let k := data.length / g1MsmLengthPerPair
    let discount := List.getD g1KDiscount (k - 1) g1MaxDiscount
    let gasCost := (k * gasBlsG1Mul * discount) / 1000
    chargeGas gasCost input fun () =>
      match decodeG1MsmPairs data with
      | .ok pairs => .ok gasCost (bls12G1MsmSum pairs).toBytes
      | .error _ => .error (.halt (.outOfGas .none)) gasCost

/-- EIP-2537 `BLS12_G2ADD` (0x0D). -/
def bls12G2Add (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  if data.length ≠ 512 then .error (.halt (.invalidParameter .none)) 0
  else
    chargeGas gasBlsG2Add input fun () =>
      match Bytes.toExceptBls12G2 (data.take 256), Bytes.toExceptBls12G2 (data.drop 256) with
      | .ok p1, .ok p2 => .ok gasBlsG2Add (Bls12G2.toBytes (p1 + p2))
      | _, _ => .error (.halt (.outOfGas .none)) gasBlsG2Add

/-- EIP-2537 `BLS12_G2MSM` (0x0E). -/
def bls12G2Msm (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  if data.length = 0 ∨ data.length % g2MsmLengthPerPair ≠ 0 then
    .error (.halt (.invalidParameter
      (.text s!"{data.length} is not a valid input length"))) 0
  else
    let k := data.length / g2MsmLengthPerPair
    let discount := List.getD g2KDiscount (k - 1) g2MaxDiscount
    let gasCost := (k * gasBlsG2Mul * discount) / 1000
    chargeGas gasCost input fun () =>
      match decodeG2MsmPairs data with
      | .ok pairs => .ok gasCost (bls12G2MsmSum pairs).toBytes
      | .error _ => .error (.halt (.outOfGas .none)) gasCost

/-- EIP-2537 `BLS12_MAP_FP_TO_G1` (0x10). -/
def bls12MapFpToG1 (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  if data.length ≠ 64 then .error (.halt (.invalidParameter .none)) 0
  else
    chargeGas gasBlsG1Map input fun () =>
      match Bytes.toExceptBls12Fp data with
      | .ok fp => .ok gasBlsG1Map (Bls12G1.toBytes (blsMapFpToG1 fp))
      | .error _ => .error (.halt (.outOfGas .none)) gasBlsG1Map

/-- EIP-2537 `BLS12_MAP_FP2_TO_G2` (0x11). -/
def bls12MapFp2ToG2 (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  if data.length ≠ 128 then .error (.halt (.invalidParameter .none)) 0
  else
    chargeGas gasBlsG2Map input fun () =>
      match Bytes.toExceptBls12Fp2 data with
      | .ok fp2 => .ok gasBlsG2Map (Bls12G2.toBytes (blsMapFp2ToG2 fp2))
      | .error _ => .error (.halt (.outOfGas .none)) gasBlsG2Map

/-- EIP-2537 `BLS12_PAIRING_CHECK` (0x0F). -/
def bls12PairingCheck (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  if data.length = 0 ∨ data.length % 384 ≠ 0 then
    .error (.halt (.invalidParameter
      (.text s!"{data.length} is not a valid input length"))) 0
  else
    let k := data.length / 384
    let gasCost := (32600 * k + 37700)
    chargeGas gasCost input fun () =>
      match executeBls12PairingInner data gasCost with
      | .ok ⟨cost, output⟩ => .ok cost output
      | .error ⟨msg, cost⟩ => .error msg cost

/-- EIP-197 `ECPAIRING` on BN254 (0x08). -/
def ecPairingCheck (input : PrecompileInput) : PrecompileResult :=
  let data := input.calldata
  let g := input.rules.altBn128
  let cost := (g.pairingPerPair * (data.length / 192)) + g.pairingBase
  chargeGas cost input fun () =>
    let inner := executePairingCheckInner data cost
    match inner with
    | .ok ⟨cost, output⟩ => .ok cost output
    | .error ⟨msg, cost⟩ => .error msg cost

/-- Run the precompile at `address` on `input`. An address with no precompile is an internal
invariant fault: dispatch reaches here only for addresses the rules list. -/
def run (input : PrecompileInput) : Address → PrecompileResult
  | 1 => ecrecover input -- 0x1
  | 2 => sha256 input -- 0x2
  | 3 => ripemd160 input -- 0x3
  | 4 => identity input -- 0x4
  | 5 => modexp input -- 0x5
  | 6 => ecAdd input -- 0x6
  | 7 => ecMul input -- 0x7
  | 8 => ecPairingCheck input --  0x8
  | 9 => blake2f input -- 0x9
  | 10 => pointEvaluation input -- 0xA
  | 11 => bls12G1Add input --  0xB
  | 12 => bls12G1Msm input --  0xC
  | 13 => bls12G2Add input --  0xD
  | 14 => bls12G2Msm input --  0xE
  | 15 => bls12PairingCheck input -- 0xF
  | 16 => bls12MapFpToG1 input -- 0x10
  | 17 => bls12MapFp2ToG2 input -- 0x11
  | 256 => p256verify input -- 0x100
  | n => .error (.internal (.invariant
      (.text s!"precompiled contract {n} does not exist"))) 0

end Precompile

end Jaune
