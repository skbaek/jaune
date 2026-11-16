import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Yaml
import JauneConsensus.Crypto.KZGCells

/-!
# `kzg` case checks (general preset)

`tests/formats/kzg_4844/*.md` and `tests/formats/kzg_7594/*.md` (`consensus-specs` `v1.6.1`):
each case is one `data.yaml` with an `input` mapping and an `output`, which is `null` when the
spec raises. The model's EIP-4844 and EIP-7594 functions (`Crypto/KZG.lean`,
`Crypto/KZGCells.lean`) report a raised exception as `Except.error`, so `null` must meet an
error and any other output must equal the model's value, compared after normalising hex to
lowercase. This replaces the standalone `jaune-consensus-kzg-vectors` runner.
-/

namespace JauneConsensus.Harness

open Jaune Yaml

/-- A normalised output value. -/
inductive KzgV where
  | null
  | bool (b : Bool)
  | hex (s : String)
  | list (xs : List KzgV)
  deriving BEq

private def toHexString (bs : Bytes) : String :=
  let d (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  "0x" ++ String.ofList (bs.flatMap fun b => [d (b.toNat / 16), d (b.toNat % 16)])

private def kzgVOfYVal : YVal → Except String KzgV
  | .scalar "null" false => .ok .null
  | .scalar "true" false => .ok (.bool true)
  | .scalar "false" false => .ok (.bool false)
  | .scalar s _ => .ok (.hex s.toLower)
  | .seq xs => do .ok (.list (← xs.mapM kzgVOfYVal))
  | .map _ => .error "unexpected mapping in output"

private def vBytes (b : Bytes) : KzgV := .hex (toHexString b)
private def vOf {α} (r : Except String α) (f : α → KzgV) : KzgV :=
  match r with | .ok a => f a | .error _ => .null

private def res {α} (r : Res α) : Except String α := r.mapError toString
private def hexF (i : YVal) (k : String) : Except String Bytes := res do (← i.field k).asHex
private def hexListF (i : YVal) (k : String) : Except String (List Bytes) :=
  res do (← (← i.field k).asSeq).mapM YVal.asHex
private def natListF (i : YVal) (k : String) : Except String (List Nat) :=
  res do (← (← i.field k).asSeq).mapM YVal.asNat

/-- The model's output for one `kzg` handler and input. -/
def kzgOutput (handler : String) (i : YVal) : Except String KzgV := do
  match handler with
  | "blob_to_kzg_commitment" =>
    return vOf (blobToKzgCommitment (← hexF i "blob")) vBytes
  | "compute_challenge" =>
    return vBytes (blsFieldToBytes (computeChallenge (← hexF i "blob") (← hexF i "commitment")))
  | "compute_kzg_proof" =>
    return vOf (computeKzgProof (← hexF i "blob") (← hexF i "z")) fun (p, y) => .list [vBytes p, vBytes y]
  | "compute_blob_kzg_proof" =>
    return vOf (computeBlobKzgProof (← hexF i "blob") (← hexF i "commitment")) vBytes
  | "verify_kzg_proof" =>
    return vOf (verifyKzgProof (← hexF i "commitment") (← hexF i "z") (← hexF i "y")
      (← hexF i "proof")) .bool
  | "verify_blob_kzg_proof" =>
    return vOf (verifyBlobKzgProof (← hexF i "blob") (← hexF i "commitment") (← hexF i "proof")) .bool
  | "verify_blob_kzg_proof_batch" =>
    return vOf (verifyBlobKzgProofBatch (← hexListF i "blobs") (← hexListF i "commitments")
      (← hexListF i "proofs")) .bool
  | "compute_cells" =>
    return vOf (computeCells (← hexF i "blob")) fun cells => .list (cells.toList.map vBytes)
  | "compute_cells_and_kzg_proofs" =>
    return vOf (computeCellsAndKzgProofs (← hexF i "blob")) fun (cells, proofs) =>
      .list [.list (cells.toList.map vBytes), .list (proofs.toList.map vBytes)]
  | "compute_verify_cell_kzg_proof_batch_challenge" =>
    let evals ← res do (← (← i.field "cosets_evals").asSeq).mapM fun e => do
      (← e.asSeq).toArray.mapM fun b => do pure (FinField.ofNat (os2ip (← b.asHex)) : Fr)
    return vOf (computeVerifyCellKzgProofBatchChallenge (← hexListF i "commitments").toArray
      (← natListF i "commitment_indices").toArray (← natListF i "cell_indices").toArray
      evals.toArray (← hexListF i "proofs").toArray) fun r => vBytes (blsFieldToBytes r)
  | "verify_cell_kzg_proof_batch" =>
    return vOf (verifyCellKzgProofBatch (← hexListF i "commitments") (← natListF i "cell_indices")
      (← hexListF i "cells") (← hexListF i "proofs")) .bool
  | "recover_cells_and_kzg_proofs" =>
    return vOf (recoverCellsAndKzgProofs (← natListF i "cell_indices") (← hexListF i "cells"))
      fun (cells, proofs) => .list [.list (cells.toList.map vBytes), .list (proofs.toList.map vBytes)]
  | h => throw s!"no kzg handler {h}"

/-- `kzg/<handler>`: `data.yaml`'s `output` must equal the model's output (`null` for a
raised exception). -/
def kzgCase (c : Case) : IO (Except String Unit) := do
  if c.files != ["data.yaml"] then return .error s!"unexpected files {c.files}"
  let doc := parse (← IO.FS.readBinFile (c.dir / "data.yaml"))
  pure do
    let v ← res doc
    res (v.expectKeys ["input", "output"])
    let want ← kzgVOfYVal (← res (v.field "output"))
    let got ← kzgOutput c.key.handler (← res (v.field "input"))
    if got == want then pure () else throw "output differs"

end JauneConsensus.Harness
