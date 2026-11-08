-- EIP-7594 cell KZG (PeerDAS), transcribed from consensus-specs v1.6.1
-- specs/fulu/polynomial-commitments-sampling.md, in the spec's order and operation
-- order, on top of the EIP-4844 layer in KZG.lean.
--
-- Failure model as in KZG.lean: `assert`, raising conversions and out-of-range
-- indexing are `Except.error`; predicates return `Except String Bool`.

import JauneConsensus.Crypto.KZG

namespace JauneConsensus

open Jaune

/-! ### Preset -/

def fieldElementsPerExtBlob : Nat := 2 * fieldElementsPerBlob
def fieldElementsPerCell : Nat := 64
def bytesPerCell : Nat := fieldElementsPerCell * bytesPerFieldElement
def cellsPerExtBlob : Nat := fieldElementsPerExtBlob / fieldElementsPerCell
def randomChallengeKzgCellBatchDomain : Bytes := "RCKZGCBATCH__V1_".toUTF8.toList

/-! ### BLS12-381 helpers -/

/-- `cell_to_coset_evals(cell)`. -/
def cellToCosetEvals (cell : Bytes) : Except String (Array Fr) :=
  ((chunks bytesPerFieldElement cell).take fieldElementsPerCell).toArray.mapM bytesToBlsFieldK

/-- `coset_evals_to_cell(coset_evals)`. -/
def cosetEvalsToCell (cosetEvals : Array Fr) : Bytes :=
  cosetEvals.toList.flatMap blsFieldToBytes

/-! ### FFTs -/

/-- Every other entry starting at `start` (`xs[start::2]`). -/
def everyOther {α} (xs : Array α) (start : Nat) : Array α :=
  ((List.range xs.size).filter (· % 2 = start)).toArray.filterMap (xs[·]?)

/-- `_fft_field(vals, roots_of_unity)`; `fuel` bounds the recursion depth (the
callers pass the length, and each level halves it). -/
def fftFieldAux : Nat → Array Fr → Array Fr → Array Fr
  | 0, vals, _ => vals
  | fuel + 1, vals, roots =>
    if vals.size ≤ 1 then vals else
    let rootsHalf := everyOther roots 0
    let l := fftFieldAux fuel (everyOther vals 0) rootsHalf
    let r := fftFieldAux fuel (everyOther vals 1) rootsHalf
    let yTimesRoot := (r.zip roots).map fun (y, root) => y * root
    let lo := (l.zip yTimesRoot).map fun (x, yr) => x + yr
    let hi := (l.zip yTimesRoot).map fun (x, yr) => x - yr
    lo ++ hi

/-- `fft_field(vals, roots_of_unity, inv)`. -/
def fftField (vals roots : Array Fr) (inv : Bool := false) : Array Fr :=
  if inv then
    -- Inverse FFT
    let invlen : Fr := (FinField.ofNat vals.size : Fr) ^ (blsModulus - 2)
    let rootsInv := (roots.extract 0 1) ++ (roots.extract 1 roots.size).reverse
    (fftFieldAux vals.size vals rootsInv).map (· * invlen)
  else
    -- Regular FFT
    fftFieldAux vals.size vals roots

/-- `shift_vals(vals, factor)`: `[vals[i] * factor^i]`. -/
def shiftVals (vals : Array Fr) (factor : Fr) : Array Fr :=
  ((vals.foldl (fun (acc : Array Fr × Fr) v => (acc.1.push (v * acc.2), acc.2 * factor))
    (#[], 1))).1

/-- `coset_fft_field(vals, roots_of_unity, inv)`. -/
def cosetFftField (vals roots : Array Fr) (inv : Bool := false) : Array Fr :=
  -- This is the coset generator.
  let shiftFactor : Fr := FinField.ofNat primitiveRootOfUnity
  if inv then
    shiftVals (fftField vals roots inv) shiftFactor⁻¹
  else
    fftField (shiftVals vals shiftFactor) roots inv

/-- `compute_verify_cell_kzg_proof_batch_challenge(...)`. -/
def computeVerifyCellKzgProofBatchChallenge (commitments : Array Bytes)
    (commitmentIndices cellIndices : Array Nat) (cosetsEvals : Array (Array Fr))
    (proofs : Array Bytes) : Except String Fr := do
  let mut hashinput := randomChallengeKzgCellBatchDomain
  hashinput := hashinput ++ i2osp fieldElementsPerBlob 8
  hashinput := hashinput ++ i2osp fieldElementsPerCell 8
  hashinput := hashinput ++ i2osp commitments.size 8
  hashinput := hashinput ++ i2osp cellIndices.size 8
  for commitment in commitments do
    hashinput := hashinput ++ commitment
  for k in [0:cosetsEvals.size] do
    hashinput := hashinput ++ i2osp (← idx commitmentIndices k "commitment_indices") 8
    hashinput := hashinput ++ i2osp (← idx cellIndices k "cell_indices") 8
    for cosetEval in ← idx cosetsEvals k "cosets_evals" do
      hashinput := hashinput ++ blsFieldToBytes cosetEval
    hashinput := hashinput ++ (← idx proofs k "proofs")
  return hashToBlsField hashinput

/-! ### Polynomials in coefficient form -/

/-- `compute_roots_of_unity(FIELD_ELEMENTS_PER_BLOB)`, computed once. -/
def rootsOfUnityBlob : Except String (Array Fr) := computeRootsOfUnity fieldElementsPerBlob

/-- `compute_roots_of_unity(FIELD_ELEMENTS_PER_EXT_BLOB)`, computed once. -/
def rootsOfUnityExtended : Except String (Array Fr) := computeRootsOfUnity fieldElementsPerExtBlob

/-- Its bit-reversal permutation, computed once. -/
def rootsOfUnityExtendedBrp : Except String (Array Fr) := do
  bitReversalPermutation (← rootsOfUnityExtended)

/-- `polynomial_eval_to_coeff(polynomial)`. -/
def polynomialEvalToCoeff (polynomial : Array Fr) : Except String (Array Fr) := do
  return fftField (← bitReversalPermutation polynomial) (← rootsOfUnityBlob) (inv := true)

/-- `add_polynomialcoeff(a, b)`. -/
def addPolynomialcoeff (a b : Array Fr) : Array Fr :=
  let (a, b) := if a.size ≥ b.size then (a, b) else (b, a)
  (List.range a.size).toArray.filterMap fun i =>
    a[i]?.map fun ai => match b[i]? with
      | some bi => ai + bi
      | none => ai

/-- `multiply_polynomialcoeff(a, b)`. -/
def multiplyPolynomialcoeff (a b : Array Fr) : Except String (Array Fr) := do
  kzgAssert (a.size + b.size ≤ fieldElementsPerExtBlob) "multiply_polynomialcoeff: degree"
  let mut r : Array Fr := #[0]
  for power in [0:a.size] do
    let coef ← idx a power "a"
    let summand := Array.replicate power 0 ++ b.map (coef * ·)
    r := addPolynomialcoeff r summand
  return r

/-- `divide_polynomialcoeff(a, b)`: long division. -/
def dividePolynomialcoeff (a b : Array Fr) : Except String (Array Fr) := do
  let mut a := a
  let mut o : Array Fr := #[]   -- quotient coefficients, highest first
  let bpos := b.size - 1
  let bLead ← idx b bpos "b[bpos]"
  -- diff runs from len(a) - 1 - bpos down to 0 (none if len(a) <= bpos)
  if b.size ≤ a.size then
    for step in [0:a.size - bpos] do
      let apos := a.size - 1 - step
      let diff := apos - bpos
      let quot := (← idx a apos "a[apos]") / bLead
      o := o.push quot
      for j in [0:bpos + 1] do
        let i := bpos - j
        let bi ← idx b i "b[i]"
        a := a.modify (diff + i) fun x => x - bi * quot
  return o.reverse

/-- `interpolate_polynomialcoeff(xs, ys)`. -/
def interpolatePolynomialcoeff (xs ys : Array Fr) : Except String (Array Fr) := do
  kzgAssert (xs.size = ys.size) "interpolate_polynomialcoeff: lengths"
  let mut r : Array Fr := #[0]
  for i in [0:xs.size] do
    let mut summand : Array Fr := #[← idx ys i "ys"]
    for j in [0:ys.size] do
      if j ≠ i then
        let weightAdjustment := ((← idx xs i "xs") - (← idx xs j "xs"))⁻¹
        summand ← multiplyPolynomialcoeff summand
          #[-weightAdjustment * (← idx xs j "xs"), weightAdjustment]
    r := addPolynomialcoeff r summand
  return r

/-- `vanishing_polynomialcoeff(xs)`. -/
def vanishingPolynomialcoeff (xs : Array Fr) : Except String (Array Fr) := do
  let mut p : Array Fr := #[1]
  for x in xs do
    p ← multiplyPolynomialcoeff p #[-x, 1]
  return p

/-- `evaluate_polynomialcoeff(polynomial_coeff, z)`: Horner. -/
def evaluatePolynomialcoeff (polynomialCoeff : Array Fr) (z : Fr) : Fr :=
  polynomialCoeff.foldr (fun coef y => y * z + coef) 0

/-! ### KZG multiproofs -/

/-- `compute_kzg_proof_multi_impl(polynomial_coeff, zs)`. -/
def computeKzgProofMultiImpl (polynomialCoeff zs : Array Fr) : Except String (BLSP × Array Fr) := do
  -- For all points, compute the evaluation of those points
  let ys := zs.map (evaluatePolynomialcoeff polynomialCoeff)
  -- Compute Z(X)
  let denominatorPoly ← vanishingPolynomialcoeff zs
  -- Compute the quotient polynomial directly in monomial form
  let quotientPolynomial ← dividePolynomialcoeff polynomialCoeff denominatorPoly
  let monomial ← kzgSetupG1Monomial
  return (← g1Lincomb (monomial.extract 0 quotientPolynomial.size) quotientPolynomial, ys)

/-! ### Cell cosets -/

/-- `coset_shift_for_cell(cell_index)`. -/
def cosetShiftForCell (cellIndex : Nat) : Except String Fr := do
  kzgAssert (cellIndex < cellsPerExtBlob) "coset_shift_for_cell: index"
  idx (← rootsOfUnityExtendedBrp) (fieldElementsPerCell * cellIndex) "coset_shift_for_cell"

/-- `coset_for_cell(cell_index)`. -/
def cosetForCell (cellIndex : Nat) : Except String (Array Fr) := do
  kzgAssert (cellIndex < cellsPerExtBlob) "coset_for_cell: index"
  return (← rootsOfUnityExtendedBrp).extract (fieldElementsPerCell * cellIndex)
    (fieldElementsPerCell * (cellIndex + 1))

/-- `verify_cell_kzg_proof_batch_impl(...)`; commitments and proofs as validated
bytes with their points. -/
def verifyCellKzgProofBatchImpl (commitments : Array (Bytes × BLSP)) (commitmentIndices cellIndices : Array Nat)
    (cosetsEvals : Array (Array Fr)) (proofs : Array (Bytes × BLSP)) : Except String Bool := do
  kzgAssert (commitmentIndices.size = cellIndices.size && cellIndices.size = cosetsEvals.size
    && cosetsEvals.size = proofs.size) "verify_cell_kzg_proof_batch_impl: lengths"
  kzgAssert ((commitments.map (·.1)).toList.eraseDups.length = commitments.size)
    "verify_cell_kzg_proof_batch_impl: distinct commitments"
  for commitmentIndex in commitmentIndices do
    kzgAssert (commitmentIndex < commitments.size) "verify_cell_kzg_proof_batch_impl: commitment index"
  -- Preparation
  let numCells := cellIndices.size
  let n := fieldElementsPerCell
  let numCommitments := commitments.size
  -- Step 1: Compute a challenge r and its powers r^0, ..., r^{num_cells-1}
  let r ← computeVerifyCellKzgProofBatchChallenge (commitments.map (·.1)) commitmentIndices
    cellIndices cosetsEvals (proofs.map (·.1))
  let rPowers := computePowers r numCells
  -- Step 2: Compute LL = sum_k r^k proofs[k]
  let ll ← g1Lincomb (proofs.map (·.2)) rPowers
  -- Step 3: Compute LR = [s^n]
  let g2Setup ← kzgSetupG2Monomial
  let lr ← idx g2Setup n "KZG_SETUP_G2_MONOMIAL[n]"
  -- Step 4.1a: weights[i] = sum of r^k over cells k of commitment i
  let mut weights : Array Fr := Array.replicate numCommitments 0
  for k in [0:numCells] do
    let i ← idx commitmentIndices k "commitment_indices"
    let rk ← idx rPowers k "r_powers"
    weights := weights.modify i (· + rk)
  -- Step 4.1b: RLC = sum_i weights[i] commitments[i]
  let rlc ← g1Lincomb (commitments.map (·.2)) weights
  -- Step 4.2: RLI = [sum_k r^k interpolation_poly_k(s)]
  let mut sumInterpPolysCoeff : Array Fr := Array.replicate n 0
  for k in [0:numCells] do
    let interpPolyCoeff ← interpolatePolynomialcoeff (← cosetForCell (← idx cellIndices k "cell_indices"))
      (← idx cosetsEvals k "cosets_evals")
    let interpPolyScaledCoeff ← multiplyPolynomialcoeff #[← idx rPowers k "r_powers"] interpPolyCoeff
    sumInterpPolysCoeff := addPolynomialcoeff sumInterpPolysCoeff interpPolyScaledCoeff
  let monomial ← kzgSetupG1Monomial
  let rli ← g1Lincomb (monomial.extract 0 n) sumInterpPolysCoeff
  -- Step 4.3: RLP = sum_k (r^k * h_k^n) proofs[k]
  let mut weightedRPowers : Array Fr := #[]
  for k in [0:numCells] do
    let hK ← cosetShiftForCell (← idx cellIndices k "cell_indices")
    let hKPow := hK ^ n
    let wrp := (← idx rPowers k "r_powers") * hKPow
    weightedRPowers := weightedRPowers.push wrp
  let rlp ← g1Lincomb (proofs.map (·.2)) weightedRPowers
  -- Step 4.4: RL = RLC - RLI + RLP
  let rl := rlc + -rli
  let rl := rl + rlp
  -- Step 5: Check pairing (LL, LR) = pairing (RL, [1])
  let g2Setup0 ← idx g2Setup 0 "KZG_SETUP_G2_MONOMIAL[0]"
  return pairingCheck [(ll, lr), (rl, -g2Setup0)]

/-! ### Cells -/

/-- `compute_cells(blob)`. -/
def computeCells (blob : Bytes) : Except String (Array Bytes) := do
  kzgAssert (blob.length = bytesPerBlob) "compute_cells: blob length"
  let polynomial ← blobToPolynomial blob
  let polynomialCoeff ← polynomialEvalToCoeff polynomial
  (List.range cellsPerExtBlob).toArray.mapM fun i => do
    let coset ← cosetForCell i
    let ys := coset.map (evaluatePolynomialcoeff polynomialCoeff)
    return cosetEvalsToCell ys

/-- `compute_cells_and_kzg_proofs_polynomialcoeff(polynomial_coeff)`. -/
def computeCellsAndKzgProofsPolynomialcoeff (polynomialCoeff : Array Fr) :
    Except String (Array Bytes × Array Bytes) := do
  let mut cells : Array Bytes := #[]
  let mut proofs : Array Bytes := #[]
  for i in [0:cellsPerExtBlob] do
    let coset ← cosetForCell i
    let (proof, ys) ← computeKzgProofMultiImpl polynomialCoeff coset
    cells := cells.push (cosetEvalsToCell ys)
    proofs := proofs.push (g1Compress proof)
  return (cells, proofs)

/-- `compute_cells_and_kzg_proofs(blob)`. -/
def computeCellsAndKzgProofs (blob : Bytes) : Except String (Array Bytes × Array Bytes) := do
  kzgAssert (blob.length = bytesPerBlob) "compute_cells_and_kzg_proofs: blob length"
  let polynomial ← blobToPolynomial blob
  let polynomialCoeff ← polynomialEvalToCoeff polynomial
  computeCellsAndKzgProofsPolynomialcoeff polynomialCoeff

/-- `verify_cell_kzg_proof_batch(commitments_bytes, cell_indices, cells, proofs_bytes)`. -/
def verifyCellKzgProofBatch (commitmentsBytes : List Bytes) (cellIndices : List Nat)
    (cells proofsBytes : List Bytes) : Except String Bool := do
  kzgAssert (commitmentsBytes.length = cells.length && cells.length = proofsBytes.length
    && proofsBytes.length = cellIndices.length) "verify_cell_kzg_proof_batch: lengths"
  for commitmentBytes in commitmentsBytes do
    kzgAssert (commitmentBytes.length = bytesPerCommitment) "verify_cell_kzg_proof_batch: commitment length"
  for cellIndex in cellIndices do
    kzgAssert (cellIndex < cellsPerExtBlob) "verify_cell_kzg_proof_batch: cell index"
  for cell in cells do
    kzgAssert (cell.length = bytesPerCell) "verify_cell_kzg_proof_batch: cell length"
  for proofBytes in proofsBytes do
    kzgAssert (proofBytes.length = bytesPerProof) "verify_cell_kzg_proof_batch: proof length"
  -- Create the list of deduplicated commitments we are dealing with
  let dedupBytes := commitmentsBytes.eraseDups
  let deduplicatedCommitments ← dedupBytes.toArray.mapM fun b => do return (b, ← bytesToKzgG1 b)
  -- Create indices list mapping initial commitments to the deduplicated commitments
  let commitmentIndices ← commitmentsBytes.toArray.mapM fun b =>
    match dedupBytes.idxOf? b with
    | some i => pure i
    | none => throw "index: deduplicated_commitments.index"
  let cosetsEvals ← cells.toArray.mapM cellToCosetEvals
  let proofs ← proofsBytes.toArray.mapM fun b => do return (b, ← bytesToKzgG1 b)
  -- Do the actual verification
  verifyCellKzgProofBatchImpl deduplicatedCommitments commitmentIndices cellIndices.toArray
    cosetsEvals proofs

/-! ### Reconstruction -/

/-- `construct_vanishing_polynomial(missing_cell_indices)`. -/
def constructVanishingPolynomial (missingCellIndices : Array Nat) : Except String (Array Fr) := do
  -- Get the small domain
  let rootsOfUnityReduced ← computeRootsOfUnity cellsPerExtBlob
  -- Compute polynomial that vanishes at all the missing cells (over the small domain)
  let shortZeroPoly ← vanishingPolynomialcoeff (← missingCellIndices.mapM fun m => do
    idx rootsOfUnityReduced (← reverseBits m cellsPerExtBlob) "roots_of_unity_reduced")
  -- Extend vanishing polynomial to full domain
  let mut zeroPolyCoeff : Array Fr := Array.replicate fieldElementsPerExtBlob 0
  for (coeff, i) in shortZeroPoly.toList.zipIdx do
    zeroPolyCoeff := zeroPolyCoeff.modify (i * fieldElementsPerCell) fun _ => coeff
  return zeroPolyCoeff

/-- `recover_polynomialcoeff(cell_indices, cosets_evals)`. -/
def recoverPolynomialcoeff (cellIndices : Array Nat) (cosetsEvals : Array (Array Fr)) :
    Except String (Array Fr) := do
  -- Get the extended domain.
  let rootsOfUnityExtended ← rootsOfUnityExtended
  -- Flatten the cosets evaluations; missing cells are zero.
  let mut extendedEvaluationRbo : Array Fr := Array.replicate fieldElementsPerExtBlob 0
  for (cellIndex, cell) in cellIndices.zip cosetsEvals do
    let start := cellIndex * fieldElementsPerCell
    for (v, j) in cell.toList.zipIdx do
      extendedEvaluationRbo := extendedEvaluationRbo.modify (start + j) fun _ => v
  let extendedEvaluation ← bitReversalPermutation extendedEvaluationRbo
  -- Compute the vanishing polynomial Z(x) in coefficient form.
  let missingCellIndices := (List.range cellsPerExtBlob).toArray.filter (!cellIndices.contains ·)
  let zeroPolyCoeff ← constructVanishingPolynomial missingCellIndices
  -- Convert Z(x) to evaluation form over the FFT domain
  let zeroPolyEval := fftField zeroPolyCoeff rootsOfUnityExtended
  -- Compute (E*Z)(x) = E(x) * Z(x) in evaluation form over the FFT domain
  let extendedEvaluationTimesZero := (zeroPolyEval.zip extendedEvaluation).map fun (a, b) => a * b
  -- An inverse FFT yields the coefficient form of (P*Z)(x).
  let extendedEvaluationTimesZeroCoeffs := fftField extendedEvaluationTimesZero rootsOfUnityExtended (inv := true)
  -- Convert (P*Z)(x) to evaluation form over a coset of the FFT domain
  let extendedEvaluationsOverCoset := cosetFftField extendedEvaluationTimesZeroCoeffs rootsOfUnityExtended
  -- Convert Z(x) to evaluation form over a coset of the FFT domain
  let zeroPolyOverCoset := cosetFftField zeroPolyCoeff rootsOfUnityExtended
  -- Compute P(x) = (P*Z)(x) / Z(x) in evaluation form over a coset of the FFT domain
  let reconstructedPolyOverCoset := (extendedEvaluationsOverCoset.zip zeroPolyOverCoset).map
    fun (a, b) => a / b
  -- Convert P(x) to coefficient form
  let reconstructedPolyCoeff := cosetFftField reconstructedPolyOverCoset rootsOfUnityExtended (inv := true)
  return reconstructedPolyCoeff.extract 0 fieldElementsPerBlob

/-- `recover_cells_and_kzg_proofs(cell_indices, cells)`. -/
def recoverCellsAndKzgProofs (cellIndices : List Nat) (cells : List Bytes) :
    Except String (Array Bytes × Array Bytes) := do
  -- Check we have the same number of cells and indices
  kzgAssert (cellIndices.length = cells.length) "recover_cells_and_kzg_proofs: lengths"
  -- Check we have enough cells to be able to perform the reconstruction
  kzgAssert (cellsPerExtBlob / 2 ≤ cellIndices.length && cellIndices.length ≤ cellsPerExtBlob)
    "recover_cells_and_kzg_proofs: count"
  -- Check for duplicates
  kzgAssert (cellIndices.eraseDups.length = cellIndices.length) "recover_cells_and_kzg_proofs: duplicates"
  -- Check that indices are in ascending order
  kzgAssert (cellIndices.mergeSort (· ≤ ·) = cellIndices) "recover_cells_and_kzg_proofs: sorted"
  -- Check that the cell indices are within bounds
  for cellIndex in cellIndices do
    kzgAssert (cellIndex < cellsPerExtBlob) "recover_cells_and_kzg_proofs: cell index"
  -- Check that each cell is the correct length
  for cell in cells do
    kzgAssert (cell.length = bytesPerCell) "recover_cells_and_kzg_proofs: cell length"
  -- Convert cells to coset evaluations
  let cosetsEvals ← cells.toArray.mapM cellToCosetEvals
  -- Given the coset evaluations, recover the polynomial in coefficient form
  let polynomialCoeff ← recoverPolynomialcoeff cellIndices.toArray cosetsEvals
  -- Recompute all cells/proofs
  computeCellsAndKzgProofsPolynomialcoeff polynomialCoeff

end JauneConsensus
