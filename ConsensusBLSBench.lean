-- Timing probe for the consensus BLS primitives. Inputs depend on the command line so
-- that no measured value is a closed term the compiler could hoist to initialisation.
import JauneConsensus.Crypto.KZGCells
import JauneConsensus.Crypto.BLSSig

open Jaune JauneConsensus

/-- Run `f x` once and report wall milliseconds; `IO.lazyPure` keeps the pure work
between the two clock reads. -/
def timeIt {α β} (label : String) (f : α → β) (x : α) (show? : β → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure (fun _ => f x)
  let s := show? r
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {t1 - t0} ms ({s.length} chars)"

def main (args : List String) : IO Unit := do
  let k := args.length + 1
  let p : BLSP := blsG1Generator.mulBy k
  let q : BLSP2 := blsG2Generator.mulBy k
  -- KZG pieces (one repetition; setup decode is forced first).
  let t0 ← IO.monoMsNow
  let some lag := kzgSetupG1Lagrange.toOption | IO.println "setup failed"
  let some mono := kzgSetupG1Monomial.toOption | IO.println "setup failed"
  let t1 ← IO.monoMsNow
  IO.println s!"setup decode (8192 G1 points): {t1 - t0} ms"
  let scal : Array Fr := (List.range 4096).toArray.map fun i => FinField.ofNat (i * 0x9e3779b97f4a7c15f39cc0605cedc834 + k)
  timeIt "g1Msm 4096 (Pippenger)" (fun (x : Array Fr) => g1Msm lag (x.map (·.val))) scal (fun r => toString r.x.val)
  timeIt "naive MSM 64 (g1MsmSum)" (fun (x : Array Fr) => g1MsmSum ((lag.toList.take 64).zip (x.toList.map (·.val)))) scal (fun r => toString r.x.val)
  timeIt "g1Msm 64 (Pippenger)" (fun (x : Array Fr) => g1Msm (lag.extract 0 64) ((x.extract 0 64).map (·.val))) scal (fun r => toString r.x.val)
  match cosetForCell 5 with
  | .ok coset =>
    timeIt "evaluate 4096-coeff poly at 64 coset points (Horner)" (fun (c : Array Fr) => coset.map (evaluatePolynomialcoeff c)) scal (fun r => toString r.size)
    match vanishingPolynomialcoeff coset with
    | .ok zp =>
      timeIt "divide 4096-coeff poly by 64-point vanishing poly" (fun (c : Array Fr) => dividePolynomialcoeff c zp) scal (fun r => toString (r.toOption.map (·.size)))
    | .error e => IO.println e
    timeIt "compute_kzg_proof_multi_impl (one cell)" (fun (c : Array Fr) => computeKzgProofMultiImpl c coset) scal (fun r => toString (r.toOption.map (·.2.size)))
    timeIt "interpolate 64 points (quadratic)" (fun (c : Array Fr) => interpolatePolynomialcoeff coset (c.extract 0 64)) scal (fun r => toString (r.toOption.map (·.size)))
    timeIt "interpolate 64 points (spec, cubic)" (fun (c : Array Fr) => interpolatePolynomialcoeffSpec coset (c.extract 0 64)) scal (fun r => toString (r.toOption.map (·.size)))
  | .error e => IO.println e
  timeIt "FK20 table (64 G1 FFTs of 128, once per process)" (fun (_ : Nat) => fk20Table.get) k
    (fun r => toString (r.toOption.map (·.size)))
  timeIt "fk20H (direct MSMs, reference)" fk20H scal (fun r => toString (r.toOption.map (·.size)))
  timeIt "fk20HFft (Toeplitz in frequency domain)" fk20HFft scal (fun r => toString (r.toOption.map (·.size)))
  IO.println s!"fk20HFft = fk20H on this polynomial: {decide ((fk20HFft scal).toOption = (fk20H scal).toOption)}"
  timeIt "computeCellsAndKzgProofsPolynomialcoeff (FFT cells + FK20), one blob"
    computeCellsAndKzgProofsPolynomialcoeff scal (fun r => toString (r.toOption.map (·.2.size)))
  timeIt "cellsFromCoeff (FFT), one blob" cellsFromCoeff scal (fun r => toString (r.toOption.map (·.size)))
  let _ := mono
  let reps := 1
  for _ in List.range reps do
    timeIt "pairing (full)" (fun (qp : BLSP2 × BLSP) => blsPairing qp.1 qp.2) (q, p)
      (fun r => toString (r.map (·.val.length)))
    timeIt "miller loop only" (fun (qp : BLSP2 × BLSP) => blsPairing qp.1 qp.2 false) (q, p)
      (fun r => toString (r.map (·.val.length)))
    match blsPairing q p false with
    | some f =>
      timeIt "final exponentiation only"
        (fun (g : BLSF12) => g ^ ((blsPrime ^ 12 - 1) / blsCurveOrder)) f
        (fun r => toString r.val.length)
      timeIt "final exponentiation, easy/hard split (consensus)" blsFinalExpFast f
        (fun r => toString r.val.length)
    | none => IO.println "pairing none"
    timeIt "pairingCheck, 2 pairs (consensus, split final exp)" pairingCheck
      [(p, q), (-p, q)] (fun r => toString r)
    timeIt "hash_to_curve G2 (RFC 9380, 32-byte msg)"
      (fun (m : Bytes) => hashToPoint m) (List.replicate 32 k.toUInt8)
      (fun r => toString (r.toOption.map (·.x.val.length)))
    timeIt "G2 decompress" signatureToPoint (g2Compress q) (fun r => toString r.toOption.isSome)
    let u : BLSF2 := BLSF2.mk (k + 12345) (k + 678)
    timeIt "map_to_curve G2 (swu + iso, no cofactor)"
      (fun t => isoMapG2 (optimizedSwuG2 t)) u (fun r => toString r.x.val)
    timeIt "clear_cofactor G2 (mulBy hEffG2)"
      (fun (t : BLSP2) => t.mulBy BLSConst.hEffG2) (isoMapG2 (optimizedSwuG2 u))
      (fun r => toString r.x.val)
    timeIt "blsMapFp2ToG2 (EIP-2537 map incl. cofactor)" blsMapFp2ToG2 u
      (fun r => toString r.x.val)
    timeIt "G2 subgroup check (mulBy r)" (fun (t : BLSP2) => t.mulBy blsCurveOrder) q
      (fun r => toString r.x.val)
    timeIt "G2 subgroup check, psi endomorphism (consensus)" g2SubgroupCheckFast q
      (fun r => toString r)
    timeIt "G1 subgroup check (mulBy r)" (fun (t : BLSP) => t.mulBy blsCurveOrder) p
      (fun r => toString r.x.val)
