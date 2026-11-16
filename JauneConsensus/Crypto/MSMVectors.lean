-- Differential checks: the bucket MSM `g1Msm` against Jaune's naive `g1MsmSum`.
-- Inputs cover the empty sum, zero and `r - 1` scalars, scalars at least `r`,
-- repeated points (the doubling branch), a point with its negation (cancellation)
-- and the identity, at sizes that select window widths 1 through 3.

import JauneConsensus.Crypto.MSM

namespace JauneConsensus.MSMVectors

open Jaune JauneConsensus

def points (n : Nat) : Array Bls12G1 :=
  (List.range n).toArray.map fun i => blsG1Generator.mulBy (3 * i + 1)

def scalars (n : Nat) : Array Nat :=
  (List.range n).toArray.map fun i => (i * 0x9e3779b97f4a7c15f39cc0605cedc834 + i ^ 7) % (2 ^ 256)

def naive (ps : Array Bls12G1) (ss : Array Nat) : Bls12G1 := g1MsmSum (ps.toList.zip ss.toList)

#guard g1Msm #[] #[] = naive #[] #[]
#guard g1Msm #[blsG1Generator] #[0] = ⟨0, 0⟩
#guard g1Msm #[blsG1Generator] #[blsCurveOrder - 1] = -blsG1Generator
#guard g1Msm #[blsG1Generator] #[blsCurveOrder + 5] = blsG1Generator.mulBy 5
#guard g1Msm #[blsG1Generator, blsG1Generator, blsG1Generator] #[7, 7, 9] = blsG1Generator.mulBy 23
#guard g1Msm #[blsG1Generator, -blsG1Generator, ⟨0, 0⟩] #[11, 11, 3] = ⟨0, 0⟩
#guard g1Msm (points 5) (scalars 5) = naive (points 5) (scalars 5)
#guard g1Msm (points 17) (scalars 17) = naive (points 17) (scalars 17)
#guard g1Msm (points 40) (scalars 40) = naive (points 40) (scalars 40)

end JauneConsensus.MSMVectors
