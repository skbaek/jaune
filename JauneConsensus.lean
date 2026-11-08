-- Root of the consensus-layer library (goal `jaune-consensus-electra-fulu-v1`).
-- It lives outside `Jaune/` so that Blanc, which needs only `jaune/Assurance`, never builds it.
import JauneConsensus.Error
import JauneConsensus.UInt
import JauneConsensus.SSZ.Merkle
import JauneConsensus.SSZ.Basic
-- Harness modules (vector readers and case checks), outside the semantics but built with it.
import JauneConsensus.Harness.Snappy
import JauneConsensus.Harness.Yaml
import JauneConsensus.Harness.SszGeneric
