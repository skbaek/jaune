-- Timing probe for the consensus BLS primitives. Inputs depend on the command line so
-- that no measured value is a closed term the compiler could hoist to initialisation.
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
  let reps := 3
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
      (fun t => isoMapG2 (optimizedSwuG2 t)) u (fun r => toString r.x.val.length)
    timeIt "clear_cofactor G2 (mulBy hEffG2)"
      (fun (t : BLSP2) => t.mulBy BLSConst.hEffG2) (isoMapG2 (optimizedSwuG2 u))
      (fun r => toString r.x.val.length)
    timeIt "blsMapFp2ToG2 (EIP-2537 map incl. cofactor)" blsMapFp2ToG2 u
      (fun r => toString r.x.val.length)
    timeIt "G2 subgroup check (mulBy r)" (fun (t : BLSP2) => t.mulBy blsCurveOrder) q
      (fun r => toString r.x.val.length)
    timeIt "G1 subgroup check (mulBy r)" (fun (t : BLSP) => t.mulBy blsCurveOrder) p
      (fun r => toString r.x.val)
