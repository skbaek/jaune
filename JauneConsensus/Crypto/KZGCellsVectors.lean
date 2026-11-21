-- Differential checks for KZGCells.lean: the regrouped polynomial product against the
-- spec-shaped one, including empty and length-one operands, and the FFT against its
-- inverse.

import JauneConsensus.Crypto.KZGCells

namespace JauneConsensus.KZGCellsVectors

open Jaune JauneConsensus

def fieldElements (xs : List Nat) : Array BLSFieldElement := xs.toArray.map FieldElement.ofNat

#guard multiplyPolynomialcoeff #[] #[] = multiplyPolynomialcoeffSpec #[] #[]
#guard multiplyPolynomialcoeff (fieldElements [5]) #[] = multiplyPolynomialcoeffSpec (fieldElements [5]) #[]
#guard multiplyPolynomialcoeff (fieldElements [5, 6, 7]) #[] = multiplyPolynomialcoeffSpec (fieldElements [5, 6, 7]) #[]
#guard multiplyPolynomialcoeff #[] (fieldElements [1, 2]) = multiplyPolynomialcoeffSpec #[] (fieldElements [1, 2])
#guard multiplyPolynomialcoeff (fieldElements [3]) (fieldElements [1, 2]) = multiplyPolynomialcoeffSpec (fieldElements [3]) (fieldElements [1, 2])
#guard multiplyPolynomialcoeff (fieldElements [1, 2, 3, 0]) (fieldElements [blsModulus - 4, 1])
  = multiplyPolynomialcoeffSpec (fieldElements [1, 2, 3, 0]) (fieldElements [blsModulus - 4, 1])
#guard multiplyPolynomialcoeff (fieldElements [9, 8, 7, 6, 5]) (fieldElements [1, 0, 2])
  = multiplyPolynomialcoeffSpec (fieldElements [9, 8, 7, 6, 5]) (fieldElements [1, 0, 2])

-- Inverse FFT undoes the FFT on 8 points.
#guard (do
  let roots ← computeRootsOfUnity 8
  let v := fieldElements [1, 2, 3, 4, 5, 6, 7, 8]
  return fftField (fftField v roots) roots (inv := true) == v : Except String Bool) = .ok true

end JauneConsensus.KZGCellsVectors

namespace JauneConsensus.KZGCellsVectors
open Jaune JauneConsensus

-- Quadratic interpolation equals the spec's cubic one.
#guard interpolatePolynomialcoeff #[] #[] = interpolatePolynomialcoeffSpec #[] #[]
#guard interpolatePolynomialcoeff (fieldElements [7]) (fieldElements [3]) = interpolatePolynomialcoeffSpec (fieldElements [7]) (fieldElements [3])
#guard interpolatePolynomialcoeff (fieldElements [1, 2, 5]) (fieldElements [10, 0, blsModulus - 1])
  = interpolatePolynomialcoeffSpec (fieldElements [1, 2, 5]) (fieldElements [10, 0, blsModulus - 1])
#guard (do
  let coset ← cosetForCell 3
  let xs := coset.extract 0 6
  let ys := fieldElements [11, 22, 33, 44, 55, 66]
  return (← interpolatePolynomialcoeff xs ys) == (← interpolatePolynomialcoeffSpec xs ys)
  : Except String Bool) = .ok true

end JauneConsensus.KZGCellsVectors
