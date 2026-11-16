-- Differential checks: the bucket MSM `g1Msm` against Jaune's naive `g1MsmSum`.
-- Inputs cover the empty sum, zero and `r - 1` scalars, scalars at least `r`,
-- repeated points (the doubling branch), a point with its negation (cancellation)
-- and the identity, at sizes that select window widths 1 through 3.

import JauneConsensus.Crypto.MSM

namespace JauneConsensus.MSMVectors

open Jaune JauneConsensus

def pts (n : Nat) : Array BLSP :=
  (List.range n).toArray.map fun i => blsG1Generator.mulBy (3 * i + 1)

def scs (n : Nat) : Array Nat :=
  (List.range n).toArray.map fun i => (i * 0x9e3779b97f4a7c15f39cc0605cedc834 + i ^ 7) % (2 ^ 256)

def naive (ps : Array BLSP) (ss : Array Nat) : BLSP := g1MsmSum (ps.toList.zip ss.toList)

#guard g1Msm #[] #[] = naive #[] #[]
#guard g1Msm #[blsG1Generator] #[0] = ⟨0, 0⟩
#guard g1Msm #[blsG1Generator] #[blsCurveOrder - 1] = -blsG1Generator
#guard g1Msm #[blsG1Generator] #[blsCurveOrder + 5] = blsG1Generator.mulBy 5
#guard g1Msm #[blsG1Generator, blsG1Generator, blsG1Generator] #[7, 7, 9] = blsG1Generator.mulBy 23
#guard g1Msm #[blsG1Generator, -blsG1Generator, ⟨0, 0⟩] #[11, 11, 3] = ⟨0, 0⟩
#guard g1Msm (pts 5) (scs 5) = naive (pts 5) (scs 5)
#guard g1Msm (pts 17) (scs 17) = naive (pts 17) (scs 17)
#guard g1Msm (pts 40) (scs 40) = naive (pts 40) (scs 40)

end JauneConsensus.MSMVectors
