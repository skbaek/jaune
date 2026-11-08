-- EIP-4844 KZG commitments, transcribed from consensus-specs v1.6.1
-- specs/deneb/polynomial-commitments.md, in the spec's order and operation order.
--
-- Reuse: the scalar field is Jaune's `FinField` at `blsModulus`; `bytesToBlsField` and
-- `decodeKzgG1` (validate_kzg_g1 + decode) are Jaune's EIP-4844 decoders
-- (Jaune/Precompiles.lean), wrapped; G1/G2 codecs and the fast pairing check are
-- Codec.lean's; `g1_lincomb` is the bucket MSM of MSM.lean.
--
-- Failure model at this layer: a pyspec `assert` (or a raising conversion) is
-- `Except.error`; verification predicates return `Except String Bool`, so an
-- assertion failure (`null` in the vectors) is distinguished from `False`.
--
-- Points are carried as decoded points between functions where pyspec
-- round-trips them through `Bytes48` (`g1_lincomb` returns bytes that the caller
-- decodes again); for a point produced by group operations that round trip is the
-- identity, so only boundary inputs are decoded and validated.

import JauneConsensus.Crypto.Codec
import JauneConsensus.Crypto.MSM
import JauneConsensus.Crypto.TrustedSetup

namespace JauneConsensus

open Jaune

/-- `BLSFieldElement`: the scalar field of BLS12-381. -/
abbrev Fr : Type := FinField blsModulus

/-! ### Constants and preset -/

def bytesPerCommitment : Nat := 48
def bytesPerProof : Nat := 48
def bytesPerFieldElement : Nat := 32
def fieldElementsPerBlob : Nat := 4096
def bytesPerBlob : Nat := bytesPerFieldElement * fieldElementsPerBlob
def primitiveRootOfUnity : Nat := 7
def kzgSetupG2Length : Nat := 65
def fiatShamirProtocolDomain : Bytes := "FSBLOBVERIFY_V1_".toUTF8.toList
def randomChallengeKzgBatchDomain : Bytes := "RCKZGBATCH___V1_".toUTF8.toList

/-- `assert cond` with a site label. -/
def kzgAssert (cond : Bool) (site : String) : Except String Unit :=
  if cond then pure () else throw s!"assert: {site}"

/-- Indexing that raises (pyspec `IndexError`) instead of defaulting. -/
def idx {α} (xs : Array α) (i : Nat) (site : String) : Except String α :=
  match xs[i]? with
  | some x => pure x
  | none => throw s!"index: {site}"

/-! ### Trusted setup, decoded from the generated hex (TrustedSetup.lean) -/

def hexNibble (c : Char) : Nat :=
  if c.toNat ≥ 'a'.toNat then c.toNat - 'a'.toNat + 10 else c.toNat - '0'.toNat

/-- The generated strings are lowercase hex of whole bytes (the generator checks). -/
def hexToBytes : List Char → Bytes
  | a :: b :: rest => (hexNibble a * 16 + hexNibble b).toUInt8 :: hexToBytes rest
  | _ => []

/-- Split a list into chunks of `n` (the last may be shorter). -/
def chunks {α} (n : Nat) (xs : List α) : List (List α) :=
  if h : n = 0 then [xs] else
  let rec go (fuel : Nat) (ys : List α) (acc : List (List α)) : List (List α) :=
    match fuel, ys with
    | _, [] => acc.reverse
    | 0, _ => (ys :: acc).reverse
    | fuel + 1, ys => go fuel (ys.drop n) (ys.take n :: acc)
  go xs.length xs []

def setupPoints (hex : String) (width : Nat) : List Bytes :=
  (chunks (2 * width) hex.toList).map hexToBytes

/-- `KZG_SETUP_G1_MONOMIAL`, decoded. Setup points are pinned by digest, so they are
decompressed without a subgroup check (the decoder still rejects points off the
curve). -/
def kzgSetupG1Monomial : Except String (Array BLSP) :=
  ((setupPoints kzgSetupG1MonomialHex 48).mapM pubkeyToPoint).map List.toArray

/-- `KZG_SETUP_G1_LAGRANGE`, decoded. -/
def kzgSetupG1Lagrange : Except String (Array BLSP) :=
  ((setupPoints kzgSetupG1LagrangeHex 48).mapM pubkeyToPoint).map List.toArray

/-- `KZG_SETUP_G2_MONOMIAL`, decoded. -/
def kzgSetupG2Monomial : Except String (Array BLSP2) :=
  ((setupPoints kzgSetupG2MonomialHex 96).mapM signatureToPoint).map List.toArray

/-! ### Bit-reversal permutation -/

/-- `is_power_of_two`. -/
def isPowerOfTwo (value : Nat) : Bool := value > 0 && (value &&& (value - 1)) = 0

/-- `reverse_bits(n, order)`: the low `log2 order` bits of `n`, reversed. -/
def reverseBits (n order : Nat) : Except String Nat := do
  kzgAssert (isPowerOfTwo order) "reverse_bits: order is a power of two"
  let k := order.log2
  return (List.range k).foldl (fun acc i => if n.testBit i then acc ||| (1 <<< (k - 1 - i)) else acc) 0

/-- `bit_reversal_permutation(sequence)`: `[sequence[reverse_bits(i, n)] for i in range(n)]`. -/
def bitReversalPermutation {α} (xs : Array α) : Except String (Array α) :=
  (List.range xs.size).toArray.mapM fun i => do
    let j ← reverseBits i xs.size
    idx xs j "bit_reversal_permutation"

/-! ### BLS12-381 helpers -/

/-- `hash_to_bls_field(data)`. -/
def hashToBlsField (data : Bytes) : Fr := FinField.ofNat (os2ip (Bytes.sha256 data).toBytes)

/-- `bytes_to_bls_field(b)`: Jaune's decoder (length 32, value below `BLS_MODULUS`). -/
def bytesToBlsFieldK (b : Bytes) : Except String Fr :=
  ((bytesToBlsField b).mapError fun _ => "assert: bytes_to_bls_field").map FinField.ofNat

/-- `bls_field_to_bytes(x)`. -/
def blsFieldToBytes (x : Fr) : Bytes := i2osp x.val 32

/-- `validate_kzg_g1` followed by the decode the callers perform: Jaune's
`decodeKzgG1` (identity allowed, otherwise KeyValidate). -/
def bytesToKzgG1 (b : Bytes) : Except String BLSP :=
  (decodeKzgG1 b).mapError fun _ => "assert: validate_kzg_g1"

/-- `blob_to_polynomial(blob)`. -/
def blobToPolynomial (blob : Bytes) : Except String (Array Fr) :=
  ((chunks bytesPerFieldElement blob).take fieldElementsPerBlob).toArray.mapM bytesToBlsFieldK

/-- `compute_challenge(blob, commitment)`. -/
def computeChallenge (blob commitment : Bytes) : Fr :=
  let degreePoly := i2osp fieldElementsPerBlob 16
  let data := fiatShamirProtocolDomain ++ degreePoly
  let data := data ++ blob
  let data := data ++ commitment
  hashToBlsField data

/-- `g1_lincomb(points, scalars)`, returning the point. -/
def g1Lincomb (points : Array BLSP) (scalars : Array Fr) : Except String BLSP := do
  kzgAssert (points.size = scalars.size) "g1_lincomb: lengths"
  if points.size = 0 then return g1Identity
  return g1Msm points (scalars.map (·.val))

/-- `compute_powers(x, n)`. -/
def computePowers (x : Fr) (n : Nat) : Array Fr :=
  ((List.range n).foldl (fun (acc : Array Fr × Fr) _ => (acc.1.push acc.2, acc.2 * x))
    (#[], 1)).1

/-- `compute_roots_of_unity(order)`. -/
def computeRootsOfUnity (order : Nat) : Except String (Array Fr) := do
  kzgAssert (order ≠ 0 && (blsModulus - 1) % order = 0) "compute_roots_of_unity: order divides r - 1"
  let rootOfUnity : Fr := FinField.ofNat (Nat.powMod primitiveRootOfUnity ((blsModulus - 1) / order) blsModulus)
  return computePowers rootOfUnity order

/-- `bit_reversal_permutation(compute_roots_of_unity(FIELD_ELEMENTS_PER_BLOB))`,
computed once. -/
def rootsOfUnityBrp : Except String (Array Fr) := do
  bitReversalPermutation (← computeRootsOfUnity fieldElementsPerBlob)

/-- `bit_reversal_permutation(KZG_SETUP_G1_LAGRANGE)`, computed once. -/
def kzgSetupG1LagrangeBrp : Except String (Array BLSP) := do
  bitReversalPermutation (← kzgSetupG1Lagrange)

/-! ### Polynomials -/

/-- `evaluate_polynomial_in_evaluation_form(polynomial, z)`. -/
def evaluatePolynomialInEvaluationForm (polynomial : Array Fr) (z : Fr) : Except String Fr := do
  let width := polynomial.size
  kzgAssert (width = fieldElementsPerBlob) "evaluate_polynomial_in_evaluation_form: width"
  let inverseWidth : Fr := (FinField.ofNat width : Fr)⁻¹
  let roots ← rootsOfUnityBrp
  -- If we are asked to evaluate within the domain, we already know the answer
  match roots.findIdx? (· = z) with
  | some evalIndex => idx polynomial evalIndex "evaluate_polynomial_in_evaluation_form"
  | none =>
    let mut result : Fr := 0
    for i in [0:width] do
      let a := (← idx polynomial i "polynomial") * (← idx roots i "roots")
      let b := z - (← idx roots i "roots")
      result := result + a / b
    let r := z ^ width - 1
    return result * r * inverseWidth

/-! ### KZG -/

/-- `blob_to_kzg_commitment(blob)`. -/
def blobToKzgCommitment (blob : Bytes) : Except String Bytes := do
  kzgAssert (blob.length = bytesPerBlob) "blob_to_kzg_commitment: blob length"
  return g1Compress (← g1Lincomb (← kzgSetupG1LagrangeBrp) (← blobToPolynomial blob))

/-- `verify_kzg_proof_impl(commitment, z, y, proof)`: `P - y = Q * (X - z)`. -/
def verifyKzgProofImplK (commitment : BLSP) (z y : Fr) (proof : BLSP) : Except String Bool := do
  let g2Setup1 ← idx (← kzgSetupG2Monomial) 1 "KZG_SETUP_G2_MONOMIAL[1]"
  let xMinusZ := g2Setup1 + blsG2Generator.mulBy (-z).val
  let pMinusY := commitment + blsG1Generator.mulBy (-y).val
  return pairingCheck [(pMinusY, -blsG2Generator), (proof, xMinusZ)]

/-- `verify_kzg_proof(commitment_bytes, z_bytes, y_bytes, proof_bytes)`. -/
def verifyKzgProof (commitmentBytes zBytes yBytes proofBytes : Bytes) : Except String Bool := do
  kzgAssert (commitmentBytes.length = bytesPerCommitment) "verify_kzg_proof: commitment length"
  kzgAssert (zBytes.length = bytesPerFieldElement) "verify_kzg_proof: z length"
  kzgAssert (yBytes.length = bytesPerFieldElement) "verify_kzg_proof: y length"
  kzgAssert (proofBytes.length = bytesPerProof) "verify_kzg_proof: proof length"
  verifyKzgProofImplK (← bytesToKzgG1 commitmentBytes) (← bytesToBlsFieldK zBytes)
    (← bytesToBlsFieldK yBytes) (← bytesToKzgG1 proofBytes)

/-- `verify_kzg_proof_batch(commitments, zs, ys, proofs)`; commitments and proofs are
the validated byte strings together with their decoded points. -/
def verifyKzgProofBatch (commitments : Array (Bytes × BLSP)) (zs ys : Array Fr)
    (proofs : Array (Bytes × BLSP)) : Except String Bool := do
  kzgAssert (commitments.size = zs.size && zs.size = ys.size && ys.size = proofs.size)
    "verify_kzg_proof_batch: lengths"
  -- Compute a random challenge.
  let degreePoly := i2osp fieldElementsPerBlob 8
  let numCommitments := i2osp commitments.size 8
  let mut data := randomChallengeKzgBatchDomain ++ degreePoly ++ numCommitments
  for i in [0:commitments.size] do
    data := data ++ (← idx commitments i "c").1 ++ blsFieldToBytes (← idx zs i "z")
      ++ blsFieldToBytes (← idx ys i "y") ++ (← idx proofs i "p").1
  let r := hashToBlsField data
  let rPowers := computePowers r commitments.size
  let proofPts := proofs.map (·.2)
  let proofLincomb ← g1Lincomb proofPts rPowers
  let proofZLincomb ← g1Lincomb proofPts ((zs.zip rPowers).map fun (z, rp) => z * rp)
  let cMinusYs := (commitments.zip ys).map fun ((_, c), y) => c + blsG1Generator.mulBy (-y).val
  let cMinusYLincomb ← g1Lincomb cMinusYs rPowers
  let g2Setup1 ← idx (← kzgSetupG2Monomial) 1 "KZG_SETUP_G2_MONOMIAL[1]"
  return pairingCheck [(proofLincomb, -g2Setup1), (cMinusYLincomb + proofZLincomb, blsG2Generator)]

/-- `compute_quotient_eval_within_domain(z, polynomial, y)`. -/
def computeQuotientEvalWithinDomain (z : Fr) (polynomial : Array Fr) (y : Fr) : Except String Fr := do
  let roots ← rootsOfUnityBrp
  let mut result : Fr := 0
  for i in [0:roots.size] do
    let omegaI ← idx roots i "roots"
    if omegaI = z then continue
    let fI := (← idx polynomial i "polynomial") - y
    let numerator := fI * omegaI
    let denominator := z * (z - omegaI)
    result := result + numerator / denominator
  return result

/-- `compute_kzg_proof_impl(polynomial, z)`. -/
def computeKzgProofImpl (polynomial : Array Fr) (z : Fr) : Except String (BLSP × Fr) := do
  let roots ← rootsOfUnityBrp
  -- For all x_i, compute p(x_i) - p(z)
  let y ← evaluatePolynomialInEvaluationForm polynomial z
  let polynomialShifted := polynomial.map (· - y)
  -- For all x_i, compute (x_i - z)
  let denominatorPoly := roots.map (· - z)
  -- Compute the quotient polynomial directly in evaluation form
  let mut quotientPolynomial : Array Fr := Array.replicate fieldElementsPerBlob 0
  for i in [0:fieldElementsPerBlob] do
    let a ← idx polynomialShifted i "shifted"
    let b ← idx denominatorPoly i "denominator"
    if b = 0 then
      quotientPolynomial := quotientPolynomial.setIfInBounds i
        (← computeQuotientEvalWithinDomain (← idx roots i "roots") polynomial y)
    else
      quotientPolynomial := quotientPolynomial.setIfInBounds i (a / b)
  return (← g1Lincomb (← kzgSetupG1LagrangeBrp) quotientPolynomial, y)

/-- `compute_kzg_proof(blob, z_bytes)`: the proof and `y` as bytes. -/
def computeKzgProof (blob zBytes : Bytes) : Except String (Bytes × Bytes) := do
  kzgAssert (blob.length = bytesPerBlob) "compute_kzg_proof: blob length"
  kzgAssert (zBytes.length = bytesPerFieldElement) "compute_kzg_proof: z length"
  let polynomial ← blobToPolynomial blob
  let (proof, y) ← computeKzgProofImpl polynomial (← bytesToBlsFieldK zBytes)
  return (g1Compress proof, i2osp y.val bytesPerFieldElement)

/-- `compute_blob_kzg_proof(blob, commitment_bytes)`. -/
def computeBlobKzgProof (blob commitmentBytes : Bytes) : Except String Bytes := do
  kzgAssert (blob.length = bytesPerBlob) "compute_blob_kzg_proof: blob length"
  kzgAssert (commitmentBytes.length = bytesPerCommitment) "compute_blob_kzg_proof: commitment length"
  let _ ← bytesToKzgG1 commitmentBytes
  let polynomial ← blobToPolynomial blob
  let evaluationChallenge := computeChallenge blob commitmentBytes
  let (proof, _) ← computeKzgProofImpl polynomial evaluationChallenge
  return g1Compress proof

/-- `verify_blob_kzg_proof(blob, commitment_bytes, proof_bytes)`. -/
def verifyBlobKzgProof (blob commitmentBytes proofBytes : Bytes) : Except String Bool := do
  kzgAssert (blob.length = bytesPerBlob) "verify_blob_kzg_proof: blob length"
  kzgAssert (commitmentBytes.length = bytesPerCommitment) "verify_blob_kzg_proof: commitment length"
  kzgAssert (proofBytes.length = bytesPerProof) "verify_blob_kzg_proof: proof length"
  let commitment ← bytesToKzgG1 commitmentBytes
  let polynomial ← blobToPolynomial blob
  let evaluationChallenge := computeChallenge blob commitmentBytes
  -- Evaluate polynomial at `evaluation_challenge`
  let y ← evaluatePolynomialInEvaluationForm polynomial evaluationChallenge
  -- Verify proof
  let proof ← bytesToKzgG1 proofBytes
  verifyKzgProofImplK commitment evaluationChallenge y proof

/-- `verify_blob_kzg_proof_batch(blobs, commitments_bytes, proofs_bytes)`. -/
def verifyBlobKzgProofBatch (blobs commitmentsBytes proofsBytes : List Bytes) : Except String Bool := do
  kzgAssert (blobs.length = commitmentsBytes.length && commitmentsBytes.length = proofsBytes.length)
    "verify_blob_kzg_proof_batch: lengths"
  let mut commitments : Array (Bytes × BLSP) := #[]
  let mut evaluationChallenges : Array Fr := #[]
  let mut ys : Array Fr := #[]
  let mut proofs : Array (Bytes × BLSP) := #[]
  for ((blob, commitmentBytes), proofBytes) in (blobs.zip commitmentsBytes).zip proofsBytes do
    kzgAssert (blob.length = bytesPerBlob) "verify_blob_kzg_proof_batch: blob length"
    kzgAssert (commitmentBytes.length = bytesPerCommitment) "verify_blob_kzg_proof_batch: commitment length"
    kzgAssert (proofBytes.length = bytesPerProof) "verify_blob_kzg_proof_batch: proof length"
    let commitment ← bytesToKzgG1 commitmentBytes
    commitments := commitments.push (commitmentBytes, commitment)
    let polynomial ← blobToPolynomial blob
    let evaluationChallenge := computeChallenge blob commitmentBytes
    evaluationChallenges := evaluationChallenges.push evaluationChallenge
    ys := ys.push (← evaluatePolynomialInEvaluationForm polynomial evaluationChallenge)
    proofs := proofs.push (proofBytes, ← bytesToKzgG1 proofBytes)
  verifyKzgProofBatch commitments evaluationChallenges ys proofs

end JauneConsensus
