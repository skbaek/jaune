-- Differential checks for KZGCells.lean: the regrouped polynomial product against the
-- spec-shaped one, including empty and length-one operands, and the FFT against its
-- inverse.

import JauneConsensus.Crypto.KZGCells

namespace JauneConsensus.KZGCellsVectors

open Jaune JauneConsensus

def fr (xs : List Nat) : Array Fr := xs.toArray.map FinField.ofNat

#guard multiplyPolynomialcoeff #[] #[] = multiplyPolynomialcoeffSpec #[] #[]
#guard multiplyPolynomialcoeff (fr [5]) #[] = multiplyPolynomialcoeffSpec (fr [5]) #[]
#guard multiplyPolynomialcoeff (fr [5, 6, 7]) #[] = multiplyPolynomialcoeffSpec (fr [5, 6, 7]) #[]
#guard multiplyPolynomialcoeff #[] (fr [1, 2]) = multiplyPolynomialcoeffSpec #[] (fr [1, 2])
#guard multiplyPolynomialcoeff (fr [3]) (fr [1, 2]) = multiplyPolynomialcoeffSpec (fr [3]) (fr [1, 2])
#guard multiplyPolynomialcoeff (fr [1, 2, 3, 0]) (fr [blsModulus - 4, 1])
  = multiplyPolynomialcoeffSpec (fr [1, 2, 3, 0]) (fr [blsModulus - 4, 1])
#guard multiplyPolynomialcoeff (fr [9, 8, 7, 6, 5]) (fr [1, 0, 2])
  = multiplyPolynomialcoeffSpec (fr [9, 8, 7, 6, 5]) (fr [1, 0, 2])

-- Inverse FFT undoes the FFT on 8 points.
#guard (do
  let roots ← computeRootsOfUnity 8
  let v := fr [1, 2, 3, 4, 5, 6, 7, 8]
  return fftField (fftField v roots) roots (inv := true) == v : Except String Bool) = .ok true

end JauneConsensus.KZGCellsVectors

namespace JauneConsensus.KZGCellsVectors
open Jaune JauneConsensus

-- Quadratic interpolation equals the spec's cubic one.
#guard interpolatePolynomialcoeff #[] #[] = interpolatePolynomialcoeffSpec #[] #[]
#guard interpolatePolynomialcoeff (fr [7]) (fr [3]) = interpolatePolynomialcoeffSpec (fr [7]) (fr [3])
#guard interpolatePolynomialcoeff (fr [1, 2, 5]) (fr [10, 0, blsModulus - 1])
  = interpolatePolynomialcoeffSpec (fr [1, 2, 5]) (fr [10, 0, blsModulus - 1])
#guard (do
  let coset ← cosetForCell 3
  let xs := coset.extract 0 6
  let ys := fr [11, 22, 33, 44, 55, 66]
  return (← interpolatePolynomialcoeff xs ys) == (← interpolatePolynomialcoeffSpec xs ys)
  : Except String Bool) = .ok true

end JauneConsensus.KZGCellsVectors
