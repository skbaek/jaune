-- BLS12-381 field, curve, and EIP-2537 byte codecs.
--
-- Ported from py_ecc's non-optimized `bls12_381_curve` module (affine
-- coordinates; the generic curve law is already provided by EC.lean) and
-- EELS's `bls12_381/__init__.py` (byte-level codecs; gas semantics live in
-- Execution.lean). Mirrors the BN254 conventions already in EC.lean /
-- Execution.lean (BNF/BNP/Bytes.toExBNP) rather than generalizing them.

import Jaune.EC
import Jaune.BLSConst

namespace Jaune

open Jaune

-- py_ecc.fields.field_properties.field_properties["bls12_381"]["field_modulus"];
-- equal to the pre-existing (unused) `bls12Prime` constant in EC.lean.
abbrev blsPrime : Nat := bls12Prime

-- py_ecc.bls12_381.bls12_381_curve.curve_order
abbrev blsCurveOrder : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

abbrev Bls12Fp : Type := FinField blsPrime

-- Curve is y^2 = x^3 + 4 (py_ecc.bls12_381.bls12_381_curve.b)
abbrev Bls12G1 : Type := EllipticCurve Bls12Fp (0 : Bls12Fp) (4 : Bls12Fp)

-- GaloisField stores polynomial coefficients from highest degree to the
-- constant coefficient.  Thus [c1, c0] represents c0 + c1*u, while the
-- EIP-2537 codec exposes the py_ecc order c0 || c1.  The modulus is
-- u^2 + 1, matching py_ecc's FQ2_MODULUS_COEFFS = (1, 0).
abbrev Bls12Fp2 : Type := GaloisField blsPrime [1, 0, 1]

def Bls12Fp2.mk (c0 c1 : Nat) : Bls12Fp2 :=
  ⟨trimZero [FinField.ofNat c1, FinField.ofNat c0]⟩

def blsB2 : Bls12Fp2 := Bls12Fp2.mk 4 4

abbrev Bls12G2 : Type := EllipticCurve Bls12Fp2 (0 : Bls12Fp2) blsB2

-- def g1_to_bytes(g1_point : Point3D[FQ]) -> Bytes:
def Bls12G1.toBytes (p : Bls12G1) : Bytes :=
  p.x.val.toBytes.pack 64 ++ p.y.val.toBytes.pack 64

-- `takeRightV` is `takeRightD` with its width in the type: the same
-- left-padding, which restores exactly the leading zeros `trimZero` removed,
-- but now the pair of coefficient reads is total rather than conventionally
-- safe.
def Bls12Fp2.toBytes (x : Bls12Fp2) : Bytes :=
  let cs := List.takeRightV 2 x.val (0 : Bls12Fp)
  let c1 := cs[0]
  let c0 := cs[1]
  c0.val.toBytes.pack 64 ++ c1.val.toBytes.pack 64

def Bls12G2.toBytes (p : Bls12G2) : Bytes :=
  p.x.toBytes ++ p.y.toBytes

def g1MsmSum (pairs : List (Bls12G1 × Nat)) : Bls12G1 :=
  let rec aux (acc : Bls12G1) : List (Bls12G1 × Nat) → Bls12G1
    | [] => acc
    | (p, s) :: ps => aux (acc + p.mulBy s) ps
  aux ⟨0, 0⟩ pairs

def g2MsmSum (pairs : List (Bls12G2 × Nat)) : Bls12G2 :=
  let rec aux (acc : Bls12G2) : List (Bls12G2 × Nat) → Bls12G2
    | [] => acc
    | (p, s) :: ps => aux (acc + p.mulBy s) ps
  aux ⟨0, 0⟩ pairs

-- py_ecc.bls12_381.bls12_381_curve.G1
def blsG1GenX : Nat :=
  3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507
def blsG1GenY : Nat :=
  1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569

def blsG1Generator : Bls12G1 := ⟨FinField.ofNat blsG1GenX, FinField.ofNat blsG1GenY⟩

-- py_ecc.bls12_381.bls12_381_curve.G2.  Its FQ2 coefficients are in the
-- c0, c1 order used by the EIP codec.
def blsG2GenX0 : Nat :=
  352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160
def blsG2GenX1 : Nat :=
  3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758
def blsG2GenY0 : Nat :=
  1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905
def blsG2GenY1 : Nat :=
  927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582

def blsG2Generator : Bls12G2 :=
  ⟨Bls12Fp2.mk blsG2GenX0 blsG2GenX1, Bls12Fp2.mk blsG2GenY0 blsG2GenY1⟩

-- Pairing machinery, ported from py_ecc's non-optimized
-- `bls12_381_pairing` module.  The Fp12 tower type BLSF12 (modulus
-- w^12 - 2*w^6 + 2, py_ecc FQ12_MODULUS_COEFFS = (2, 0, 0, 0, 0, 0,
-- -2, 0, 0, 0, 0, 0)) and the curve BLSP12 over it already live in
-- EC.lean next to their BN254 counterparts.

-- py_ecc.bls12_381.bls12_381_pairing.ate_loop_count
def blsAteLoopCount : Nat := 15132376222941642752

-- py_ecc.bls12_381.bls12_381_pairing.log_ate_loop_count
def blsLogAteLoopCount : Nat := 62

-- def cast_point_to_fq12(pt: Point2D[FQ]) -> Point2D[FQ12]:
def Bls12G1.toBls12Fp12Pair : Bls12G1 → Bls12Fp12Pair
  | ⟨x, y⟩ => ⟨⟨trimZero [x]⟩, ⟨trimZero [y]⟩⟩

-- def twist(pt: Point2D[FQP]) -> Point2D[FQ12]:
-- Unlike the BN254 twist in EC.lean (which multiplies by w^2 / w^3),
-- py_ecc's BLS12-381 twist divides the coordinates by w^2 / w^3.
def blsTwist (p : Bls12G2) : Bls12Fp12Pair :=
  let xs := List.takeRightV 2 p.x.val (0 : Bls12Fp)
  let ys := List.takeRightV 2 p.y.val (0 : Bls12Fp)
  let x1 := xs[0]
  let x0 := xs[1]
  let y1 := ys[0]
  let y0 := ys[1]
  -- Field isomorphism from Z[p] / u^2 + 1 to Z[p] / u^2 - 2*u + 2:
  -- xcoeffs = [_x.coeffs[0] - _x.coeffs[1], _x.coeffs[1]], embedded
  -- into FQ12 at degrees 0 and 6 (w^6 = u).
  let nx : Bls12Fp12 := ⟨trimZero [x1, 0, 0, 0, 0, 0, x0 - x1]⟩
  let ny : Bls12Fp12 := ⟨trimZero [y1, 0, 0, 0, 0, 0, y0 - y1]⟩
  let w : Bls12Fp12 := ⟨[1, 0]⟩
  ⟨nx / (w ^ 2), ny / (w ^ 3)⟩

-- def linefunc(P1, P2, T) -> Field:
-- Duplicated from EC.lean's BN254 `linefunc` (numerator/denominator
-- form, avoiding per-line division) rather than generalizing it.
def blsLinefunc : Bls12Fp12Pair → Bls12Fp12Pair → Bls12Fp12Pair → Bls12Fp12Pair
  | ⟨x1, y1⟩, ⟨x2, y2⟩, ⟨xt, yt⟩ =>
    let mNumerator : Bls12Fp12 := y2 - y1
    let mDenominator : Bls12Fp12 := x2 - x1
    if mDenominator ≠ 0
    then
      ⟨
        mNumerator * (xt - x1) - mDenominator * (yt - y1),
        mDenominator
      ⟩
    else
      if mNumerator = 0
      then
        let mNumerator := 3 * x1 * x1
        let mDenominator := 2 * y1
        ⟨
          mNumerator * (xt - x1) - mDenominator * (yt - y1),
          mDenominator
        ⟩
      else ⟨xt - x1, 1⟩

-- def miller_loop(Q: Point2D[FQ12], P: Point2D[FQ12]) -> FQ12:
-- Iterates the bits of ate_loop_count from bit log_ate_loop_count down
-- to bit 0; unlike the BN254 loop there are no negative pseudo-binary
-- digits and no Frobenius tail lines.
def blsMillerLoop (q p : Bls12Fp12Pair) (finalExp : Bool := true) : Option Bls12Fp12 := do
  let mut r : Bls12Fp12Pair := q
  let mut fNum : Bls12Fp12 := 1
  let mut fDen : Bls12Fp12 := 1
  -- for i in range(log_ate_loop_count, -1, -1):
  for i in (List.range (blsLogAteLoopCount + 1)).reverse do
    let ⟨_n, _d⟩ := blsLinefunc r r p
    fNum := fNum * fNum * _n
    fDen := fDen * fDen * _d
    r := r.double
    -- if ate_loop_count & (2**i):
    if blsAteLoopCount.testBit i then
      let ⟨_n, _d⟩ := blsLinefunc r q p
      fNum := fNum * _n
      fDen := fDen * _d
      r := r + q
  let f := fNum / fDen
  return (
    if finalExp
    then f ^ ((blsPrime ^ 12 - 1) / blsCurveOrder)
    else f
  )

-- def pairing(Q: Point2D[FQ2], P: Point2D[FQ]) -> FQ12:
-- The reference pairing: py_ecc's non-optimized loop above, with the plain final power.
-- `blsPairing` below is the fast form; `Jaune/BLSGuards.lean` checks they agree.
def blsPairingRef (q : Bls12G2) (p : Bls12G1) (finalExp : Bool := true) : Option Bls12Fp12 := do
  guard q.isOnCurve
  guard p.isOnCurve
  if p = ⟨0, 0⟩ ∨ q = ⟨0, 0⟩ then
    return 1
  blsMillerLoop (blsTwist q) (p.toBls12Fp12Pair) finalExp

-- ---------------------------------------------------------------------------
-- Fast final exponentiation.
--
-- `blsMillerLoop` raises the Miller-loop value to `(p^12 - 1) / r` by square-and-multiply
-- over the whole 4,314-bit exponent (measured 2026-11-09 on the WSL host, compiled: 804 ms of
-- an 856 ms pairing). `blsFinalExpFast` computes the same power with the standard split
-- `(p^12 - 1) / r = (p^6 - 1) * (p^2 + 1) * h`, `h = (p^4 - p^2 + 1) / r`: the easy part by
-- Frobenius maps and one inversion, the hard part from the base-`p` digits of `h` as one
-- simultaneous (Straus) exponentiation over four bases. The Frobenius `x ↦ x^p` on
-- `Fp12 = Fp[w] / (w^12 - 2 w^6 + 2)` is `Fp`-linear and fixes `Fp`, so
-- `(sum c_i w^i)^p = sum c_i (w^p)^i`. The exponent identities are kernel-checked below;
-- that the Frobenius is the `p`-th power and that `blsFinalExpFast` equals the plain power
-- are differential `#guard`s in `Jaune/BLSGuards.lean`.
-- ---------------------------------------------------------------------------

/-- The reduced pairing's final exponent `(p^12 - 1) / r`. -/
def blsFinalExponent : Nat := (blsPrime ^ 12 - 1) / blsCurveOrder

/-- `h = (p^4 - p^2 + 1) / r`, the hard part of the final exponent. -/
def blsHardExponent : Nat := (blsPrime ^ 4 - blsPrime ^ 2 + 1) / blsCurveOrder

theorem blsHardExponent_exact :
    blsHardExponent * blsCurveOrder = blsPrime ^ 4 - blsPrime ^ 2 + 1 := by decide

theorem blsFinalExponent_split :
    blsFinalExponent = (blsPrime ^ 6 - 1) * (blsPrime ^ 2 + 1) * blsHardExponent := by
  decide

/-- The base-`p` digits of `h`, low first. -/
def blsHardDigits : List Nat :=
  [blsHardExponent % blsPrime, blsHardExponent / blsPrime % blsPrime,
   blsHardExponent / blsPrime ^ 2 % blsPrime, blsHardExponent / blsPrime ^ 3]

theorem blsHardDigits_sum :
    (blsHardDigits.zipIdx.map fun (d, i) => d * blsPrime ^ i).sum = blsHardExponent := by
  decide

theorem blsHardDigits_lt : ∀ d ∈ blsHardDigits, d < blsPrime := by decide

/-- The coefficients `c_0, ..., c_11` of `sum c_i w^i`, low degree first. -/
def f12Coeffs (x : Bls12Fp12) : List Bls12Fp :=
  (List.takeRightV 12 x.val (0 : Bls12Fp)).toList.reverse

/-- `c * x` for `c` in `Fp`. -/
def f12Scale (c : Bls12Fp) (x : Bls12Fp12) : Bls12Fp12 :=
  if c = 0 then 0 else ⟨x.val.map (c * ·)⟩

/-- `w^p`, and its powers `(w^p)^i` for `i < 12`. -/
def blsFrobW : Bls12Fp12 := (⟨[1, 0]⟩ : Bls12Fp12) ^ blsPrime

def blsFrobWPowers : List Bls12Fp12 :=
  (List.range 12).map fun i => blsFrobW ^ i

/-- The Frobenius `x ↦ x^p` on `Fp12`. -/
def f12Frob (x : Bls12Fp12) : Bls12Fp12 :=
  ((f12Coeffs x).zip blsFrobWPowers).foldl (fun acc (c, g) => acc + f12Scale c g) 0

/-- `frob^k`. -/
def f12FrobN : Nat → Bls12Fp12 → Bls12Fp12
  | 0, x => x
  | k + 1, x => f12FrobN k (f12Frob x)

/-- Simultaneous exponentiation `prod_i b_i ^ e_i` for four bases (Straus, 16-entry
table indexed by the bits of the four exponents at one position). -/
def f12MultiPow4 (b0 b1 b2 b3 : Bls12Fp12) (e0 e1 e2 e3 : Nat) : Bls12Fp12 :=
  -- table[j] = prod over set bits k of j of b_k
  let table : Array Bls12Fp12 := (List.range 16).toArray.map fun j =>
    (if j.testBit 0 then b0 else 1) * (if j.testBit 1 then b1 else 1) *
    (if j.testBit 2 then b2 else 1) * (if j.testBit 3 then b3 else 1)
  let n := max (max e0.log2 e1.log2) (max e2.log2 e3.log2) + 1
  (List.range n).reverse.foldl (fun acc i =>
    let j := (if e0.testBit i then 1 else 0) + (if e1.testBit i then 2 else 0) +
             (if e2.testBit i then 4 else 0) + (if e3.testBit i then 8 else 0)
    let sq := acc * acc
    match table[j]? with
    | some t => if j = 0 then sq else sq * t
    | none => sq) 1   -- unreachable: j < 16

/-- `f ^ ((p^12 - 1) / r)` by the easy/hard split. -/
def blsFinalExpFast (f : Bls12Fp12) : Bls12Fp12 :=
  -- easy part: g = (f^(p^6) / f)^(p^2 + 1)
  let t := f12FrobN 6 f / f
  let g := f12FrobN 2 t * t
  -- hard part: g^h = prod_i (frob^i g)^(l_i)
  match blsHardDigits with
  | [l0, l1, l2, l3] =>
    f12MultiPow4 g (f12Frob g) (f12FrobN 2 g) (f12FrobN 3 g) l0 l1 l2 l3
  | _ => g ^ blsHardExponent   -- unreachable: `blsHardDigits` has four entries

-- ---------------------------------------------------------------------------
-- Fast Miller loop.
--
-- The reference loop keeps the running point in `E(Fp12)` affine coordinates, so every
-- step divides in `Fp12`. `blsMillerLoopFast` runs the same loop (same bits, same order)
-- with the running point `T` in Jacobian coordinates on the twist `E'(Fp2)`, so no step
-- divides, and evaluates each line at `P` directly as a sparse `Fp12` element. With
-- `T' = (x_T w^-2, y_T w^-3)` (the twist of `blsTwist`) and the slope `λ` of the line in
-- `Fp2`, the slope upstairs is `λ w^-1` and the line value is
-- `y_P - λ x_P w^-1 + (λ x_T - y_T) w^-3`; the loop uses it times `w^3`, and a vertical
-- line `x_P - x_T w^-2` times `w^2`; the Jacobian forms scale these further by
-- elements of `Fp2`. `w^2` lies in `Fp6` (its cube is `w^6 = 1 + i`, in
-- `Fp2`) and `w^3` in `Fp4` (its square is in `Fp2`); `p^6 - 1` and `p^4 - 1` both divide
-- `(p^12 - 1) / r` (`r` divides `p^4 - p^2 + 1`, a factor of both `p^6 + 1` and
-- `p^8 + p^4 + 1`), so the final exponentiation sends these factors, and the reference's
-- `-1` sign, to `1`.
-- So the final-exponentiated pairing is the same value, which `Jaune/BLSGuards.lean`
-- checks; the raw Miller values (`finalExp := false`) differ, and every consumer of those
-- multiplies them and then applies the final exponentiation.
-- ---------------------------------------------------------------------------

/-- An `Fp12` element from `(degree, coefficient)` pairs (absent degrees are zero). -/
def blsF12OfCoeffs (cs : List (Nat × Bls12Fp)) : Bls12Fp12 :=
  ⟨trimZero ((List.range 12).reverse.map fun d =>
    cs.foldl (fun acc (e, c) => if e = d then acc + c else acc) 0)⟩

/-- The `(c0, c1)` coefficients of `c0 + c1 i` in `Fp2`. -/
def blsF2Coeffs (a : Bls12Fp2) : Bls12Fp × Bls12Fp :=
  let cs := List.takeRightV 2 a.val (0 : Bls12Fp)
  (cs[1], cs[0])

/-- `e(a) - x_P e(b) w^2 + y_P e(c) w^3`, where `e` embeds `Fp2` in `Fp12` as `blsTwist`
does (`c0 + c1 i ↦ (c0 - c1) + c1 w^6`). -/
def blsLineOf (a b c : Bls12Fp2) (p : Bls12G1) : Bls12Fp12 :=
  let (a0, a1) := blsF2Coeffs a
  let (b0, b1) := blsF2Coeffs b
  let (c0, c1) := blsF2Coeffs c
  blsF12OfCoeffs [(0, a0 - a1), (6, a1), (2, -(p.x * (b0 - b1))), (8, -(p.x * b1)),
    (3, p.y * (c0 - c1)), (9, p.y * c1)]

/-- Jacobian points of the twist `E'(Fp2)` (Jaune's `EllipticCurve.Jacobian`). -/
abbrev Bls12G2Jacobian : Type := EllipticCurve.JacobianPoint Bls12Fp2

/-- The tangent at `T = (X, Y, Z)` (affine `(X/Z^2, Y/Z^3)`) evaluated at `p` and scaled:
with `λ = 3X^2 / (2YZ)`, the scaled line `(λ x_T - y_T) - λ x_P w^2 + y_P w^3` times
`2 Y Z^3` (in `Fp2`) is `(3X^3 - 2Y^2) - 3X^2 Z^2 x_P w^2 + 2Y Z^3 y_P w^3`. -/
def blsLineDblJ (t : Bls12G2Jacobian) (p : Bls12G1) : Bls12Fp12 :=
  let x2 := t.x * t.x
  let z2 := t.z * t.z
  blsLineOf (3 * x2 * t.x - 2 * (t.y * t.y)) (3 * x2 * z2) (2 * t.y * z2 * t.z) p

/-- The chord through `T` (Jacobian) and `q` (affine) at `p`, scaled: with
`N = y_Q Z^3 - Y`, `D = Z (x_Q Z^2 - X)`, `λ = N / D`, the scaled line times `D Z^3` is
`(N X Z - Y D) - N Z^3 x_P w^2 + D Z^3 y_P w^3`. When `x_Q Z^2 = X` it is the tangent
(`N = 0`) or the vertical line `x_P w^2 - x_T` times `Z^2`: `x_P Z^2 w^2 - X`. -/
def blsLineAddJ (t : Bls12G2Jacobian) (q : Bls12G2) (p : Bls12G1) : Bls12Fp12 :=
  let z2 := t.z * t.z
  let z3 := z2 * t.z
  let n := q.y * z3 - t.y
  let u := q.x * z2 - t.x
  if u = 0 then
    if n = 0 then blsLineDblJ t p
    else
      let (x0, x1) := blsF2Coeffs t.x
      let (z0, z1) := blsF2Coeffs z2
      blsF12OfCoeffs [(2, p.x * (z0 - z1)), (8, p.x * z1), (0, -(x0 - x1)), (6, -x1)]
  else
    let d := t.z * u
    blsLineOf (n * t.x * t.z - t.y * d) (n * z3) (d * z3) p

/-- The Miller loop of the reference (same bits, same order), with `T` in Jacobian
coordinates on the twist and lines evaluated directly at `P` (no final exponentiation and
no division anywhere). -/
def blsMillerLoopFast (q : Bls12G2) (p : Bls12G1) : Bls12Fp12 := Id.run do
  let mut t : Bls12G2Jacobian := EllipticCurve.Jacobian.ofAffine q
  let mut f : Bls12Fp12 := 1
  for i in (List.range (blsLogAteLoopCount + 1)).reverse do
    f := f * f * blsLineDblJ t p
    t := EllipticCurve.Jacobian.double t
    if blsAteLoopCount.testBit i then
      f := f * blsLineAddJ t q p
      t := EllipticCurve.Jacobian.mixedAdd t q
  return f

-- The pairing: `blsMillerLoopFast` and `blsFinalExpFast`; equal to `blsPairingRef` when
-- `finalExp` holds (differential guards in `Jaune/BLSGuards.lean`). With `finalExp :=
-- false` it returns the Miller value, which differs from the reference's by a factor the
-- final exponentiation removes.
def blsPairing (q : Bls12G2) (p : Bls12G1) (finalExp : Bool := true) : Option Bls12Fp12 := do
  guard q.isOnCurve
  guard p.isOnCurve
  if p = ⟨0, 0⟩ ∨ q = ⟨0, 0⟩ then
    return 1
  let f := blsMillerLoopFast q p
  return (if finalExp then blsFinalExpFast f else f)

-- The bilinearity sanity check on `blsPairing` lives in `Jaune/BLSGuards.lean`,
-- outside the `Jaune` library root. It evaluates four full pairings during
-- elaboration and was 9.6s of this file's 11.8s; off the critical path it still
-- runs on every build, via `Main.lean`. See that file for the measurements.

-- ---------------------------------------------------------------------------
-- EIP-2537 map-to-curve precompiles (0x10 map_fp_to_G1, 0x11 map_fp2_to_G2).
--
-- Ported from py_ecc.bls.hash_to_curve.map_to_curve_G1/G2 and
-- clear_cofactor_G1/G2, down through optimized_swu.py.  py_ecc works in
-- homogeneous projective coordinates; because SSWU + the isogeny map are
-- rational (projectively homogeneous) maps, evaluating them at the affine
-- representative (z = 1) yields the same projective point, so this port is
-- purely affine.  Bulk constants come from the generated BLSConst.
-- ---------------------------------------------------------------------------

-- Fp/Fp2 conversions from the generated Nat / (c0, c1) constants.
def blsToF (n : Nat) : Bls12Fp := FinField.ofNat n
def blsToF2 : Nat × Nat → Bls12Fp2 := fun (c0, c1) => Bls12Fp2.mk c0 c1

-- RFC 9380 sgn0 (py_ecc convention).  Fp: parity of the value.
def blsSgn0F (x : Bls12Fp) : Nat := x.val % 2

-- Fp2: sign_0 or (zero_0 and sign_1), coeffs in (c0, c1) order.
def blsSgn0F2 (x : Bls12Fp2) : Nat :=
  let cs := List.takeRightV 2 x.val (0 : Bls12Fp)
  let c1 := cs[0]
  let c0 := cs[1]
  if c0.val % 2 = 1 then 1
  else if c0.val = 0 then c1.val % 2 else 0

-- Horner evaluation of a polynomial given its coefficients low degree first.
def blsHornerF (coeffs : List Bls12Fp) (x : Bls12Fp) : Bls12Fp :=
  coeffs.foldr (fun c acc => acc * x + c) 0
def blsHornerF2 (coeffs : List Bls12Fp2) (x : Bls12Fp2) : Bls12Fp2 :=
  coeffs.foldr (fun c acc => acc * x + c) 0

-- Isogeny-map coefficient tables, converted once from BLSConst.
def iso11XNumF : List Bls12Fp := BLSConst.iso11XNum.map blsToF
def iso11XDenF : List Bls12Fp := BLSConst.iso11XDen.map blsToF
def iso11YNumF : List Bls12Fp := BLSConst.iso11YNum.map blsToF
def iso11YDenF : List Bls12Fp := BLSConst.iso11YDen.map blsToF
def iso3XNumF2 : List Bls12Fp2 := BLSConst.iso3XNum.map blsToF2
def iso3XDenF2 : List Bls12Fp2 := BLSConst.iso3XDen.map blsToF2
def iso3YNumF2 : List Bls12Fp2 := BLSConst.iso3YNum.map blsToF2
def iso3YDenF2 : List Bls12Fp2 := BLSConst.iso3YDen.map blsToF2

-- def optimized_swu_G1(t: FQ) -> (numerator, y, denominator)
-- Returned here as the affine point (x = numerator / denominator, y) on the
-- 11-isogenous curve.
def optimizedSwuG1 (t : Bls12Fp) : Bls12Fp × Bls12Fp :=
  let a := blsToF BLSConst.iso11A
  let b := blsToF BLSConst.iso11B
  let z := blsToF BLSConst.iso11Z
  let t2 := t ^ 2
  let zt2 := z * t2
  let temp := zt2 + zt2 ^ 2
  let denominator0 := -(a * temp)
  let numerator0 := b * (temp + 1)
  let denominator := if denominator0 = 0 then z * a else denominator0
  let v := denominator ^ 3
  let u := numerator0 ^ 3 + a * numerator0 * denominator ^ 2 + b * v
  -- sqrt_division_FQ(u, v)
  let tmp := u * v
  let y0 := tmp * ((tmp * v ^ 2) ^ BLSConst.pMinus3Div4)
  let isRoot := (y0 ^ 2 * v - u) = 0
  let numerator := if isRoot then numerator0 else numerator0 * zt2
  let y1 := if isRoot then y0
            else y0 * t ^ 3 * blsToF BLSConst.sqrtMinus11Cubed
  let y2 := if blsSgn0F t ≠ blsSgn0F y1 then -y1 else y1
  (numerator / denominator, y2)

-- def iso_map_G1(x, y, z) evaluated affinely (z = 1).
def isoMapG1 : Bls12Fp × Bls12Fp → Bls12G1
  | (x, y) =>
    let xNum := blsHornerF iso11XNumF x
    let xDen := blsHornerF iso11XDenF x
    let yNum := blsHornerF iso11YNumF x
    let yDen := blsHornerF iso11YDenF x
    ⟨xNum / xDen, y * yNum / yDen⟩

-- def map_to_curve_G1(u); then clear_cofactor_G1 (multiply by H_EFF_G1).
def blsMapFpToG1 (fp : Bls12Fp) : Bls12G1 :=
  (isoMapG1 (optimizedSwuG1 fp)).mulBy BLSConst.hEffG1

-- def sqrt_division_FQ2(u, v) -> (is_valid_root, result)
def sqrtDivisionFQ2 (u v : Bls12Fp2) : Bool × Bls12Fp2 :=
  let temp1 := u * v ^ 7
  let temp2 := temp1 * v ^ 8
  let gamma := temp2 ^ BLSConst.pMinus9Div16 * temp1
  let rec go : List Bls12Fp2 → Bool × Bls12Fp2
    | [] => (false, gamma)
    | root :: rest =>
      let cand := root * gamma
      if cand ^ 2 * v - u = 0 then (true, cand) else go rest
  go (BLSConst.eighthRoots.map blsToF2)

-- def optimized_swu_G2(t: FQ2) -> (numerator, y, denominator)
-- Returned as the affine point (numerator / denominator, y) on the
-- 3-isogenous curve.
def optimizedSwuG2 (t : Bls12Fp2) : Bls12Fp2 × Bls12Fp2 :=
  let a := blsToF2 BLSConst.iso3A
  let b := blsToF2 BLSConst.iso3B
  let z := blsToF2 BLSConst.iso3Z
  let t2 := t ^ 2
  let zt2 := z * t2
  let temp := zt2 + zt2 ^ 2
  let denominator0 := -(a * temp)
  let numerator0 := b * (temp + 1)
  let denominator := if denominator0 = 0 then z * a else denominator0
  let v := denominator ^ 3
  let u0 := numerator0 ^ 3 + a * numerator0 * denominator ^ 2 + b * v
  let (success, sqrtCand0) := sqrtDivisionFQ2 u0 v
  let sqrtCand := sqrtCand0 * t ^ 3
  let u := zt2 ^ 3 * u0
  -- First eta making (eta * sqrtCand)^2 * v - u = 0.
  let etaMatch : Option Bls12Fp2 :=
    (BLSConst.etas.map blsToF2).foldl
      (fun acc eta =>
        match acc with
        | some _ => acc
        | none =>
          let esc := eta * sqrtCand
          if esc ^ 2 * v - u = 0 then some esc else none)
      none
  let numerator := if success then numerator0 else numerator0 * zt2
  let y1 : Bls12Fp2 :=
    if success then sqrtCand0
    else match etaMatch with
         | some esc => esc
         | none => sqrtCand0  -- unreachable per py_ecc
  let y2 := if blsSgn0F2 t ≠ blsSgn0F2 y1 then -y1 else y1
  (numerator / denominator, y2)

-- def iso_map_G2(x, y, z) evaluated affinely (z = 1).
def isoMapG2 : Bls12Fp2 × Bls12Fp2 → Bls12G2
  | (x, y) =>
    let xNum := blsHornerF2 iso3XNumF2 x
    let xDen := blsHornerF2 iso3XDenF2 x
    let yNum := blsHornerF2 iso3YNumF2 x
    let yDen := blsHornerF2 iso3YDenF2 x
    ⟨xNum / xDen, y * yNum / yDen⟩

-- def map_to_curve_G2(u); then clear_cofactor_G2 (multiply by H_EFF_G2).
def blsMapFp2ToG2 (fp2 : Bls12Fp2) : Bls12G2 :=
  (isoMapG2 (optimizedSwuG2 fp2)).mulBy BLSConst.hEffG2

-- ---------------------------------------------------------------------------
-- EIP-4844 point evaluation (0x0a): compressed-G1 codec and KZG verification.
--
-- Ported from py_ecc.bls.point_compression.decompress_G1 (ZCash flag bits),
-- py_ecc.bls.ciphersuites KeyValidate / g2_primitives.subgroup_check, and
-- EELS ethereum.crypto.kzg (bytes_to_bls_field, verify_kzg_proof_impl,
-- pairing_check).  The scalar-field modulus BLS_MODULUS equals blsCurveOrder.
-- ---------------------------------------------------------------------------

-- EIP-4844 BLS_MODULUS (kzg.py); equal to the curve order r.
abbrev blsModulus : Nat := blsCurveOrder

-- Fp square-root exponent (p ≡ 3 mod 4, so (p+1)/4 is an integer).
def blsPPlus1Div4 : Nat := (blsPrime + 1) / 4

-- kzg.py G1_POINT_AT_INFINITY = b"\xc0" + b"\x00" * 47.
def blsG1PointAtInfinity : Bytes := (0xc0 : UInt8) :: List.replicate 47 (0 : UInt8)

-- point_compression.POW_2_381; the top three ZCash flag bits sit above it.
def blsTwoPow381 : Nat := 2 ^ 381

-- Decompressed KZG_SETUP_G2_MONOMIAL_1 (kzg.py:71) as an affine G2 point.
def kzgSetupG2Monomial1P : Bls12G2 :=
  let ((x0, x1), (y0, y1)) := BLSConst.kzgSetupG2Monomial1
  ⟨Bls12Fp2.mk x0 x1, Bls12Fp2.mk y0 y1⟩

-- def verify_kzg_proof_impl(commitment, z, y, proof) -> bool.
-- Verify P - y = Q * (X - z) via a two-pairing pairing_check.
def verifyKzgProofImpl (commitment : Bls12G1) (z y : Nat) (proof : Bls12G1) : Bool :=
  -- X_minus_z = KZG_SETUP_G2_MONOMIAL_1 + G2 * ((BLS_MODULUS - z) % BLS_MODULUS)
  let xMinusZ : Bls12G2 :=
    kzgSetupG2Monomial1P + blsG2Generator.mulBy ((blsModulus - z) % blsModulus)
  -- P_minus_y = commitment + G1 * ((BLS_MODULUS - y) % BLS_MODULUS)
  let pMinusY : Bls12G1 :=
    commitment + blsG1Generator.mulBy ((blsModulus - y) % blsModulus)
  -- pairing_check[((P_minus_y, -G2), (proof, X_minus_z))]: the product of the
  -- two Miller loops, final-exponentiated (`blsFinalExpFast`), must equal 1.
  match blsPairing (-blsG2Generator) pMinusY (finalExp := false),
        blsPairing xMinusZ proof (finalExp := false) with
  | some t1, some t2 =>
      blsFinalExpFast (t1 * t2) = 1
  | _, _ => false

-- def kzg_commitment_to_versioned_hash(commitment): 0x01 || sha256(c)[1:].
def kzgCommitmentToVersionedHash (commitment : Bytes) : Bytes :=
  (0x01 : UInt8) :: ((Bytes.sha256 commitment).toBytes.drop 1)

end Jaune
