-- Differential checks: the endomorphism G2 membership test against the naive `r * P` test.

import JauneConsensus.Crypto.HashToCurve
import JauneConsensus.Crypto.G2Subgroup

namespace JauneConsensus.G2SubgroupVectors

open Jaune JauneConsensus

def naive (p : BLSP2) : Bool := p.mulBy blsCurveOrder = ⟨0, 0⟩

/-- Points of `E'` outside G2: map-to-curve outputs (RFC 9380 J.10.1 inputs) before
cofactor clearing, and small multiples. -/
def q0 : BLSP2 := mapToCurveG2 (BLSF2.mk 0x03dbc2cce174e91ba93cbb08f26b917f98194a2ea08d1cce75b2b9cc9f21689d80bd79b594a613d0a68eb807dfdc1cf8 0x05a2acec64114845711a54199ea339abd125ba38253b70a92c876df10598bd1986b739cad67961eb94f7076511b3b39a)
def q1 : BLSP2 := mapToCurveG2 (BLSF2.mk 0x15f7c0aa8f6b296ab5ff9c2c7581ade64f4ee6f1bf18f55179ff44a2cf355fa53dd2a2158c5ecb17d7c52f63e7195771 0x01c8067bf4c0ba709aa8b9abc3d1cef589a4758e09ef53732d670fd8739a7274e111ba2fcaa71b3d33df2a3a0c8529dd)
def outside : List BLSP2 := [q0, q1, q0 + q1, q0.mulBy 3, -q1, q0 + blsG2Generator]

def inside : List BLSP2 :=
  [⟨0, 0⟩, blsG2Generator, -blsG2Generator, blsG2Generator.mulBy 7,
   blsG2Generator.mulBy (blsCurveOrder - 2), clearCofactorG2 q0]

#guard outside.all fun p => p.isOnCurve
#guard inside.all fun p => naive p
#guard outside.all fun p => !naive p
#guard inside.all g2SubgroupCheckFast
#guard outside.all fun p => !g2SubgroupCheckFast p

end JauneConsensus.G2SubgroupVectors
