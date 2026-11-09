import JauneConsensus.Error
import JauneConsensus.Crypto.BLSSig
import JauneConsensus.Crypto.KZG
import JauneConsensus.Crypto.KZGCells

/-!
# The crypto boundary of the spec layer

The primitives under `JauneConsensus/Crypto/` report pyspec's raised exceptions as
`Except.error` with a diagnostic message. The spec layer computes in `M := Except Reject`, so
every producer it calls is lifted here: an exception becomes `Reject.crypto site`, with the
message dropped (it is diagnostic only; no semantic branch inspects it). The Boolean predicates
(`verify`, `fastAggregateVerify`, `aggregateVerify`, `ethFastAggregateVerify`) are pyspec
predicates that return `False` on every decoding failure, so they stay `Bool`.

The spec layer calls the functions below, never the `Except`-valued primitives directly.
-/

namespace JauneConsensus
open Jaune

/-- Lift a primitive's exception into `Reject.crypto site`. -/
def liftCrypto {ε α : Type} (site : String) (x : Except ε α) : M α :=
  match x with
  | .ok a => pure a
  | .error _ => throw (.crypto site)

/-- `eth_aggregate_pubkeys(pubkeys)` (`specs/altair/bls.md`) in `M`. -/
def ethAggregatePubkeysM (pubkeys : List Bytes) : M Bytes :=
  liftCrypto "eth_aggregate_pubkeys" (ethAggregatePubkeys pubkeys)

/-- `bls.Aggregate(signatures)` in `M`. -/
def aggregateM (signatures : List Bytes) : M Bytes :=
  liftCrypto "bls.Aggregate" (aggregate signatures)

/-- `blob_to_kzg_commitment(blob)` (`specs/deneb/polynomial-commitments.md`) in `M`. -/
def blobToKzgCommitmentM (blob : Bytes) : M Bytes :=
  liftCrypto "blob_to_kzg_commitment" (blobToKzgCommitment blob)

/-- `verify_kzg_proof(...)` in `M` (it raises on malformed inputs). -/
def verifyKzgProofM (commitment z y proof : Bytes) : M Bool :=
  liftCrypto "verify_kzg_proof" (verifyKzgProof commitment z y proof)

/-- `verify_blob_kzg_proof_batch(...)` in `M`. -/
def verifyBlobKzgProofBatchM (blobs commitments proofs : List Bytes) : M Bool :=
  liftCrypto "verify_blob_kzg_proof_batch" (verifyBlobKzgProofBatch blobs commitments proofs)

/-- `compute_cells_and_kzg_proofs(blob)` (`specs/fulu/polynomial-commitments-sampling.md`)
in `M`. -/
def computeCellsAndKzgProofsM (blob : Bytes) : M (Array Bytes × Array Bytes) :=
  liftCrypto "compute_cells_and_kzg_proofs" (computeCellsAndKzgProofs blob)

/-- `verify_cell_kzg_proof_batch(...)` in `M` (used by Fulu's data-column sidecar checks). -/
def verifyCellKzgProofBatchM (commitments : List Bytes) (cellIndices : List Nat)
    (cells proofs : List Bytes) : M Bool :=
  liftCrypto "verify_cell_kzg_proof_batch"
    (verifyCellKzgProofBatch commitments cellIndices cells proofs)

end JauneConsensus
