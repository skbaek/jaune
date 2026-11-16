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
inductive KzgValue where
  | null
  | bool (b : Bool)
  | hex (s : String)
  | list (xs : List KzgValue)
  deriving BEq

private def toHexString (bs : Bytes) : String :=
  let d (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  "0x" ++ String.ofList (bs.flatMap fun b => [d (b.toNat / 16), d (b.toNat % 16)])

private def kzgValueOfYamlValue : YamlValue → Except String KzgValue
  | .scalar "null" false => .ok .null
  | .scalar "true" false => .ok (.bool true)
  | .scalar "false" false => .ok (.bool false)
  | .scalar s _ => .ok (.hex s.toLower)
  | .sequence xs => do .ok (.list (← xs.mapM kzgValueOfYamlValue))
  | .map _ => .error "unexpected mapping in output"

private def kzgValueOfBytes (b : Bytes) : KzgValue := .hex (toHexString b)
private def kzgValueOfExcept {α} (r : Except String α) (f : α → KzgValue) : KzgValue :=
  match r with | .ok a => f a | .error _ => .null

private def resultToExcept {α} (r : Yaml.Result α) : Except String α := r.mapError toString
private def hexField (i : YamlValue) (k : String) : Except String Bytes := resultToExcept do (← i.field k).asHex
private def hexListField (i : YamlValue) (k : String) : Except String (List Bytes) :=
  resultToExcept do (← (← i.field k).asSequence).mapM YamlValue.asHex
private def natListField (i : YamlValue) (k : String) : Except String (List Nat) :=
  resultToExcept do (← (← i.field k).asSequence).mapM YamlValue.asNat

/-- The model's output for one `kzg` handler and input. -/
def kzgOutput (handler : String) (i : YamlValue) : Except String KzgValue := do
  match handler with
  | "blob_to_kzg_commitment" =>
    return kzgValueOfExcept (blobToKzgCommitment (← hexField i "blob")) kzgValueOfBytes
  | "compute_challenge" =>
    return kzgValueOfBytes (blsFieldToBytes (computeChallenge (← hexField i "blob") (← hexField i "commitment")))
  | "compute_kzg_proof" =>
    return kzgValueOfExcept (computeKzgProof (← hexField i "blob") (← hexField i "z")) fun (p, y) => .list [kzgValueOfBytes p, kzgValueOfBytes y]
  | "compute_blob_kzg_proof" =>
    return kzgValueOfExcept (computeBlobKzgProof (← hexField i "blob") (← hexField i "commitment")) kzgValueOfBytes
  | "verify_kzg_proof" =>
    return kzgValueOfExcept (verifyKzgProof (← hexField i "commitment") (← hexField i "z") (← hexField i "y")
      (← hexField i "proof")) .bool
  | "verify_blob_kzg_proof" =>
    return kzgValueOfExcept (verifyBlobKzgProof (← hexField i "blob") (← hexField i "commitment") (← hexField i "proof")) .bool
  | "verify_blob_kzg_proof_batch" =>
    return kzgValueOfExcept (verifyBlobKzgProofBatch (← hexListField i "blobs") (← hexListField i "commitments")
      (← hexListField i "proofs")) .bool
  | "compute_cells" =>
    return kzgValueOfExcept (computeCells (← hexField i "blob")) fun cells => .list (cells.toList.map kzgValueOfBytes)
  | "compute_cells_and_kzg_proofs" =>
    return kzgValueOfExcept (computeCellsAndKzgProofs (← hexField i "blob")) fun (cells, proofs) =>
      .list [.list (cells.toList.map kzgValueOfBytes), .list (proofs.toList.map kzgValueOfBytes)]
  | "compute_verify_cell_kzg_proof_batch_challenge" =>
    let evals ← resultToExcept do (← (← i.field "cosets_evals").asSequence).mapM fun e => do
      (← e.asSequence).toArray.mapM fun b => do pure (FinField.ofNat (os2ip (← b.asHex)) : Fr)
    return kzgValueOfExcept (computeVerifyCellKzgProofBatchChallenge (← hexListField i "commitments").toArray
      (← natListField i "commitment_indices").toArray (← natListField i "cell_indices").toArray
      evals.toArray (← hexListField i "proofs").toArray) fun r => kzgValueOfBytes (blsFieldToBytes r)
  | "verify_cell_kzg_proof_batch" =>
    return kzgValueOfExcept (verifyCellKzgProofBatch (← hexListField i "commitments") (← natListField i "cell_indices")
      (← hexListField i "cells") (← hexListField i "proofs")) .bool
  | "recover_cells_and_kzg_proofs" =>
    return kzgValueOfExcept (recoverCellsAndKzgProofs (← natListField i "cell_indices") (← hexListField i "cells"))
      fun (cells, proofs) => .list [.list (cells.toList.map kzgValueOfBytes), .list (proofs.toList.map kzgValueOfBytes)]
  | h => throw s!"no kzg handler {h}"

/-- `kzg/<handler>`: `data.yaml`'s `output` must equal the model's output (`null` for a
raised exception). -/
def kzgCase (c : Case) : IO (Except String Unit) := do
  if c.files != ["data.yaml"] then return .error s!"unexpected files {c.files}"
  let doc := parse (← IO.FS.readBinFile (c.directory / "data.yaml"))
  pure do
    let v ← resultToExcept doc
    resultToExcept (v.expectKeys ["input", "output"])
    let want ← kzgValueOfYamlValue (← resultToExcept (v.field "output"))
    let got ← kzgOutput c.key.handler (← resultToExcept (v.field "input"))
    if got == want then pure () else throw "output differs"

end JauneConsensus.Harness
