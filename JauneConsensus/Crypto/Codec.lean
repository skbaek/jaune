-- BLS12-381 point codecs, subgroup checks and the pairing-product check for the
-- consensus BLS ciphersuite BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_.
--
-- draft-irtf-cfrg-bls-signature-04, Appendix A: point_to_octets and
-- octets_to_point are the compressed ZCash formats, transcribed here from
-- draft-irtf-cfrg-pairing-friendly-curves-11, Appendix C (C.1 serialization,
-- C.2 deserialization). Public keys are compressed G1 points (48 bytes),
-- signatures compressed G2 points (96 bytes): the minimal-pubkey-size variant.
--
-- G1 decompression wraps Jaune's `decompressG1` (Jaune/Precompiles.lean, the
-- EIP-4844 KZG decoder) instead of re-implementing it; see `pubkeyToPoint`.
-- G2 decompression is new; its square root is Jaune's `sqrtDivisionFQ2`.
--
-- Failure model at this layer: `Except String`, as in HashToCurve.lean.

import Jaune.Precompiles
import JauneConsensus.Crypto.HashToCurve
import JauneConsensus.Crypto.FinalExp

namespace JauneConsensus

open Jaune

/-- The identity of `E` and `E'` in Jaune's affine representation. `(0, 0)` is on
neither curve (`0 ≠ 4`, `0 ≠ 4(1 + I)`), so the sentinel is unambiguous. -/
def g1Identity : BLSP := ⟨0, 0⟩
def g2Identity : BLSP2 := ⟨0, 0⟩

/-- Coefficients `(c0, c1)` of `c0 + c1 * I` (the pairing-friendly-curves draft's
`(x_0, x_1)`). -/
def f2Coeffs (x : BLSF2) : Nat × Nat :=
  let cs := List.takeRightV 2 x.val (0 : BLSF)
  (cs[1].val, cs[0].val)

/-- `sign_GF_p(y)`: 1 if `y > (p - 1) / 2`, else 0 (draft C, notation). -/
def signFp (y : Nat) : Bool := y > (blsPrime - 1) / 2

/-- `sign_GF_p^2(y')`: `sign_GF_p(y'_0)` if `y'_1 = 0`, else `sign_GF_p(y'_1)`. -/
def signFp2 (y : BLSF2) : Bool :=
  let (y0, y1) := f2Coeffs y
  if y1 = 0 then signFp y0 else signFp y1

/-- C.1 with compression for a point on `E`: `point_to_octets_E1`, the consensus
`point_to_pubkey` (48 bytes). -/
def g1Compress (p : BLSP) : Bytes :=
  if p = g1Identity then
    -- C_bit = 1, I_bit = 1, S_bit = 0; x_string = I2OSP(0, 48)
    (0xc0 : UInt8) :: List.replicate 47 0
  else
    let mByte : Nat := 0x80 + (if signFp p.y.val then 0x20 else 0)
    let xString := i2osp p.x.val 48
    match xString with
    | b :: rest => (b ||| mByte.toUInt8) :: rest
    | [] => []

/-- C.1 with compression for a point on `E'`: `point_to_octets_E2`, the consensus
`point_to_signature` (96 bytes). `x_string = I2OSP(x_1, 48) || I2OSP(x_0, 48)`. -/
def g2Compress (p : BLSP2) : Bytes :=
  if p = g2Identity then
    (0xc0 : UInt8) :: List.replicate 95 0
  else
    let mByte : Nat := 0x80 + (if signFp2 p.y then 0x20 else 0)
    let (x0, x1) := f2Coeffs p.x
    let xString := i2osp x1 48 ++ i2osp x0 48
    match xString with
    | b :: rest => (b ||| mByte.toUInt8) :: rest
    | [] => []

/-- `octets_to_point_E1` for compressed input (48 bytes): Jaune's `decompressG1`,
with its execution-layer error collapsed to a string.

It differs from draft C.2 on one input class only: a compressed string with
`I_bit = 0` and `x = 0`, which C.2 decodes to `(0, ±2)` and `decompressG1` rejects.
Those are 3-torsion points of `E`, so no consumer can tell the difference: every
consensus use of a decoded public key passes through `KeyValidate`, whose subgroup
check rejects them (`r` is prime and not 3). -/
def pubkeyToPoint (pk : Bytes) : Except String BLSP :=
  (decompressG1 pk).mapError fun _ => "invalid compressed G1 point"

/-- `octets_to_point_E2` for compressed input (96 bytes): draft C.2 on `E'`. -/
def signatureToPoint (sig : Bytes) : Except String BLSP2 := do
  -- 2. C_bit = 1 requires 96 bytes on E'.
  if sig.length ≠ 96 then throw "compressed G2 point must be 96 bytes"
  let b0 := (sig.headD 0).toNat
  -- 1. m_byte = s_string[0] AND 0xE0; 0x20, 0x60, 0xE0 are INVALID.
  let mByte := b0 &&& 0xe0
  if mByte = 0x20 ∨ mByte = 0x60 ∨ mByte = 0xe0 then throw "invalid G2 metadata bits"
  let cBit := decide (mByte &&& 0x80 ≠ 0)
  let iBit := decide (mByte &&& 0x40 ≠ 0)
  let sBit := decide (mByte &&& 0x20 ≠ 0)
  -- Only the compressed form is a signature encoding.
  if !cBit then throw "G2 signature must be compressed"
  -- 3. clear the metadata bits.
  let s := (b0 &&& 0x1f).toUInt8 :: sig.tail
  -- 4. the point at infinity must be all zeros apart from the metadata.
  if iBit then
    if s.all (· = 0) then return g2Identity else throw "non-canonical G2 infinity"
  -- 6. x = OS2IP(s_string), as (x_1, x_0); each coefficient must lie in GF(p).
  let x1 := os2ip (s.take 48)
  let x0 := os2ip (s.drop 48)
  if x0 ≥ blsPrime ∨ x1 ≥ blsPrime then throw "G2 x coordinate not in field"
  let x := BLSF2.mk x0 x1
  -- 7. y2 = x^3 + 4(u + 1); INVALID if not square, else y = sqrt(y2).
  let y2 := x ^ 3 + blsB2
  let (isRoot, y) := sqrtDivisionFQ2 y2 1
  if !isRoot then throw "G2 x coordinate not on curve"
  -- 8. choose the root whose sign is S_bit.
  return ⟨x, if signFp2 y = sBit then y else -y⟩

/-- `subgroup_check_E1`: the naive check `r * P = identity` (draft section 1.3). -/
def g1SubgroupCheck (p : BLSP) : Bool := p.mulBy blsCurveOrder = g1Identity

/-- `subgroup_check_E2`: the naive check `r * P = identity`. -/
def g2SubgroupCheck (p : BLSP2) : Bool := p.mulBy blsCurveOrder = g2Identity

/-- Pairing-product check: `prod_i e(P_i, Q_i) = 1` in `GT`, computed as Jaune's
`verifyKzgProofImpl` does (the shape of EIP-4844's `pairing_check`): the product
of the Miller loops, then one final exponentiation, here `blsFinalExpFast`
(FinalExp.lean; `pairingCheckRef` is the same check with the plain power). A pair
with a point off its curve fails the check. -/
def pairingCheck (pairs : List (BLSP × BLSP2)) : Bool :=
  let loops := pairs.mapM fun (p, q) => blsPairing q p (finalExp := false)
  match loops with
  | some fs => blsFinalExpFast (fs.foldl (· * ·) (1 : BLSF12)) = 1
  | none => false

end JauneConsensus
