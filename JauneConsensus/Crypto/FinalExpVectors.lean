-- Differential checks for JauneConsensus/Crypto/FinalExp.lean against the plain
-- power Jaune's pairing uses. Test values are Miller-loop outputs (before the final
-- exponentiation) of point pairs in G1 x G2, plus one value off the cyclotomic
-- subgroup, so the Frobenius check is not confined to the image of the easy part.

import JauneConsensus.Crypto.Codec

namespace JauneConsensus.FinalExpVectors

open Jaune JauneConsensus

def miller (p : BLSP) (q : BLSP2) : BLSF12 :=
  match blsPairing q p (finalExp := false) with
  | some f => f
  | none => 0

def f1 : BLSF12 := miller blsG1Generator blsG2Generator
def f2 : BLSF12 := miller (blsG1Generator.mulBy 5) kzgSetupG2Monomial1P
def f3 : BLSF12 := ⟨[3, 0, 7, 0, 0, 1, 0, 0, 0, 0, 2, 9]⟩

-- The Frobenius is the p-th power.
#guard f12Frob f1 = f1 ^ blsPrime
#guard f12Frob f3 = f3 ^ blsPrime
#guard f12FrobN 2 f2 = (f2 ^ blsPrime) ^ blsPrime

-- The split final exponentiation equals the plain power.
#guard blsFinalExpFast f1 = f1 ^ blsFinalExponent
#guard blsFinalExpFast f2 = f2 ^ blsFinalExponent
#guard blsFinalExpFast f3 = f3 ^ blsFinalExponent
#guard blsFinalExpFast f1 ≠ 1

-- The pairing check agrees with the reference on a true and a false instance.
#guard pairingCheck [(blsG1Generator, blsG2Generator), (-blsG1Generator, blsG2Generator)]
#guard pairingCheckRef [(blsG1Generator, blsG2Generator), (-blsG1Generator, blsG2Generator)]
#guard !pairingCheck [(blsG1Generator, blsG2Generator), (blsG1Generator, blsG2Generator)]
#guard pairingCheck [(blsG1Generator.mulBy 6, blsG2Generator), (-(blsG1Generator.mulBy 2), blsG2Generator.mulBy 3)]

end JauneConsensus.FinalExpVectors
