import Jaune.EC
import Jaune.BLS

/-!
Elliptic-curve differential oracle.

Run with `scripts/check-ec.sh`.  Like `scripts/bench-ec.lean`, this file is not
a Lake target: the wrapper compiles it with `lean -c` plus `leanc -O2` and links
it against the native objects Lake already recorded for the `jaune` executable.

**This file is test-only.  Nothing under `Jaune/` may ever import it.**  It
carries a private copy of the affine curve algorithm as it stands before the
elliptic-curve optimization work (`refDouble`, `refAdd`, `refMulBy`,
`refRecover`), so that a later Jacobian/joint-projective rewrite of the public
`EllipticCurve.mulBy` and `secp256k1.recover` can be compared against the
algorithm it replaces rather than against itself.

Three independent kinds of case are checked; each one either passes or fails,
and there is no skip or unknown outcome:

1. *pinned* — the public implementation against constants produced by outside
   implementations (libsecp256k1 via coincurve, py_ecc, EELS);
2. *differential* — the public implementation against the local affine
   reference above, over scalars, points, and curves chosen to reach every
   branch of the affine law;
3. *identity* — algebraic laws that must hold whatever representation is used
   internally (`P + (-P) = O`, `2P = P + P`, `(j+k)P = jP + kP`, on-curve-ness).

Provenance of every embedded constant.  All commands run in the pinned
execution-specs environment `~/execution-specs/venv/bin/python` (coincurve
20.0.0 over libsecp256k1, py_ecc 8.0.0, EELS 1.17.0):

* secp256k1 multiples of the generator (`secpMultiples`):

  ```sh
  python -c '
  from coincurve import PrivateKey
  for k in [1,2,3,K1,K2,N-1]:
      pk = PrivateKey.from_int(k).public_key.format(compressed=False)
      print(hex(k), pk[1:33].hex(), pk[33:].hex())'
  ```

* the signature tuple and its address (`sigHash/sigR/sigS/sigV`, case
  `recover/real-signature`):

  ```sh
  python -c '
  from coincurve import PrivateKey
  from eth_utils import keccak
  d = 0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF
  h = keccak(b"elevm ec oracle step 1")
  sig = PrivateKey.from_int(d).sign_recoverable(h, hasher=None)
  pub = PrivateKey.from_int(d).public_key.format(compressed=False)
  print(h.hex(), sig[:32].hex(), sig[32:64].hex(), sig[64], keccak(pub[1:])[12:].hex())'
  ```

  The same address is returned by EELS
  `ethereum.crypto.elliptic_curve.secp256k1_recover(r, s, v, msg_hash)` followed
  by `keccak(pubkey)[12:]`.

* BLS12-381 and BN254 multiples (`blsG1Multiples`, `blsG2Multiples`,
  `bn254Multiples`):

  ```sh
  python -c '
  from py_ecc.bls12_381 import bls12_381_curve as bls
  from py_ecc.bn128 import bn128_curve as bn
  for k in [2,3,7,K1]: print(bls.multiply(bls.G1, k))
  for k in [2,7]:      print(bls.multiply(bls.G2, k))
  for k in [2,3,7]:    print(bn.multiply(bn.G1, k))'
  ```

  py_ecc `FQ2.coeffs` is `(c0, c1)`, which is the argument order of
  `BLSF2.mk`.

* the two toy curves and every expectation in the *frozen degenerate* group
  come from a byte-exact Python re-implementation of the current affine
  algorithm (sentinel `(0,0)`, `FinField.inv 0 = 0`), cross-checked here by the
  differential group.  They are recorded because they are *current behavior*,
  not because they are mathematically correct: see the group's comment.

The generator of the recovery hash is deliberately an ordinary 256-bit
signature rather than the synthetic `h=1, r=Gx, s=2` tuple, so that all three
scalar multiplications inside `recover` are full length; the synthetic tuple is
checked too, in both parities.
-/

namespace ECOracle

/-! ## Affine reference implementation (test-only) -/

/-- Verbatim copy of `EllipticCurve.double` as of commit 118b208. -/
def refDouble {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HSub F F F] [HMul F F F] [HDiv F F F]
  [HPow F Nat F] [OfNat F 3] [OfNat F 2]
  [ToString F]
  {a b} (p : EllipticCurve F a b) : EllipticCurve F a b :=
  if p.x = 0 ∧ p.y = 0
  then
    p
  else
    let lam : F := (3 * (p.x ^ 2) + a) / (2 * p.y)
    let x : F := lam ^ 2 - p.x - p.x
    let y : F := lam * (p.x - x) - p.y
    ⟨x, y⟩

/-- Verbatim copy of `EllipticCurve.add` as of commit 118b208. -/
def refAdd {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HSub F F F] [HMul F F F] [HDiv F F F]
  [HPow F Nat F] [OfNat F 3] [OfNat F 2]
  [ToString F]
  {a b} (p q : EllipticCurve F a b) : EllipticCurve F a b :=
  if p.x = 0 ∧ p.y = 0
  then q
  else
    if q.x = 0 ∧ q.y = 0
    then p
    else
      if p.x = q.x
      then
        if p.y = q.y
        then refDouble p
        else ⟨0, 0⟩ -- point at infinity
      else
        let yDiff := q.y - p.y
        let xDiff := q.x - p.x
        let lam : F := yDiff / xDiff
        let x : F := lam ^ 2 - p.x - q.x
        let y : F := lam * (p.x - x) - p.y
        ⟨x, y⟩

/-- Verbatim copy of `EllipticCurve.mulBy` as of commit 118b208. -/
def refMulBy {F} [Zero F] [DecidableEq F]
  [HAdd F F F] [HSub F F F] [HMul F F F] [HDiv F F F]
  [HPow F Nat F] [OfNat F 3] [OfNat F 2]
  [ToString F]
  {a b} (p : EllipticCurve F a b) : Nat → EllipticCurve F a b
  | 0 => ⟨0, 0⟩
  | n@(_ + 1) =>
    let half := refMulBy p (n / 2)
    let whole := refAdd half half
    if (n % 2) = 0
    then whole
    else refAdd whole p

def refNeg {F} [Neg F] {a b} : EllipticCurve F a b → EllipticCurve F a b
  | ⟨x, y⟩ => ⟨x, -y⟩

def refSub {F} [Neg F] [Zero F] [DecidableEq F]
  [HAdd F F F] [HSub F F F] [HMul F F F] [HDiv F F F]
  [HPow F Nat F] [OfNat F 3] [OfNat F 2]
  [ToString F]
  {a b} (p q : EllipticCurve F a b) : EllipticCurve F a b :=
  refAdd p (refNeg q)

/-- Verbatim copy of `secp256k1.sqrt` as of commit 118b208. -/
def refSqrt (x : secp256k1.Coord) : Option secp256k1.Coord :=
  let y := x ^ secp256k1.sqrtExp
  if y * y = x then some y else none

/-- Verbatim copy of `secp256k1.recover` as of commit 118b208, rewired to the
reference point operations above. -/
def refRecover (h : B256) (v : Bool) (r : B256) (s : B256) : Option Adr := do
  let x : secp256k1.Coord := .ofNat r.toNat
  let ySquared : secp256k1.Coord := x ^ 3 + 7
  let yFst ← refSqrt ySquared
  let ySnd := FinField.neg yFst
  let ⟨yOdd, yEven⟩ : secp256k1.Coord × secp256k1.Coord :=
    if yFst.val % 2 = 0 then ⟨ySnd, yFst⟩ else ⟨yFst, ySnd⟩
  let y := if v then yOdd else yEven
  let R : secp256k1.Point := ⟨x, y⟩
  let rInv : Nat :=
    @FinField.val secp256k1.curveOrder <| FinField.inv <| .ofNat r.toNat
  let sR : secp256k1.Point := refMulBy R <|
    @FinField.val secp256k1.curveOrder <| .ofNat s.toNat
  let zG : secp256k1.Point := refMulBy secp256k1.generator <|
    @FinField.val secp256k1.curveOrder <| .ofNat h.toNat
  let O : secp256k1.Point := refSub sR zG
  if O = ⟨0, 0⟩ then none
  let Q : secp256k1.Point := refMulBy O rInv
  let hash := B8L.keccak <| Q.x.val.toB256.toB8L ++ Q.y.val.toB256.toB8L
  B8L.toAdr? <| List.drop 12 <| hash.toB8L

/-! ## Harness -/

abbrev Tally : Type := IO.Ref (Nat × Nat)

def flat (s : String) : String := s.replace "\n" ""

def note (st : Tally) (name : String) (ok : Bool) (detail : String) : IO Unit := do
  if ok then
    st.modify fun (p, f) => (p + 1, f)
    IO.println s!"PASS  {name}"
  else
    st.modify fun (p, f) => (p, f + 1)
    IO.println s!"FAIL  {name} — {detail}"

def ppPoint {F} [ToString F] {a b} (p : EllipticCurve F a b) : String :=
  flat s!"({p.x}, {p.y})"

def checkPoint {F} [DecidableEq F] [ToString F] {a b}
    (st : Tally) (name : String) (got exp : EllipticCurve F a b) : IO Unit :=
  note st name (decide (got = exp))
    s!"got {ppPoint got}, expected {ppPoint exp}"

def ppJacobian {F} [ToString F] (p : EllipticCurve.Jacobian.Point F) : String :=
  flat s!"({p.x}, {p.y}, {p.z})"

def checkJacobian {F} [DecidableEq F] [ToString F]
    (st : Tally) (name : String)
    (got exp : EllipticCurve.Jacobian.Point F) : IO Unit :=
  note st name (decide (got = exp))
    s!"got {ppJacobian got}, expected {ppJacobian exp}"

def ppAdr : Option Adr → String
  | none => "none"
  | some a => "0x" ++ (a.toB256.toHex.drop 24)

def checkAdr (st : Tally) (name : String) (got exp : Option Adr) : IO Unit :=
  note st name (decide (got.map Adr.toNat = exp.map Adr.toNat))
    s!"got {ppAdr got}, expected {ppAdr exp}"

def checkBool (st : Tally) (name : String) (ok : Bool) : IO Unit :=
  note st name ok "expected true"

/-! ## Curves and constants -/

-- A private key / scalar pattern used as an operand only.  No secrecy or
-- randomness is claimed for either value.
def k1 : Nat :=
  0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF
def k2 : Nat :=
  0xFEDCBA9876543210FEDCBA9876543210FEDCBA9876543210FEDCBA9876543210

-- Scalars small enough that every case is a handful of point operations.
def smallScalars : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 15, 16, 31]

-- Full-length scalars, including the order boundaries.
def bigScalars (order : Nat) : List Nat :=
  [order - 1, order, order + 1, k1 % order, k2 % order, (k1 * 7 + 13) % order]

def mkSecp (x y : Nat) : secp256k1.Point := ⟨.ofNat x, .ofNat y⟩
def mkBls1 (x y : Nat) : BLSP := ⟨.ofNat x, .ofNat y⟩
def mkBls2 (x0 x1 y0 y1 : Nat) : BLSP2 := ⟨BLSF2.mk x0 x1, BLSF2.mk y0 y1⟩
def mkBn (x y : Nat) : BNP := ⟨.ofNat x, .ofNat y⟩

def bn254Generator : BNP := mkBn 1 2

-- Toy curve with a ≠ 0: y² = x³ + x + 999 over F_1009.  Discriminant
-- -16(4a³+27b²) = 123 ≠ 0; 959 affine points, group order 960; three points of
-- order two, of which (2,0) is used below.
abbrev ToyF : Type := FinField 1009
abbrev ToyP : Type := EllipticCurve ToyF (1 : ToyF) (999 : ToyF)

-- Toy curve with a = 0 and a point of order two: y² = x³ + 5 over F_1013.
-- 1013 ≡ 2 (mod 3), so every element is a cube and x³ = -5 has the solution
-- 555; group order 1014 = 2·3·13².  None of secp256k1, BN254 G1, BLS12-381 G1
-- or BLS12-381 G2 admits such a point (their group orders are odd), so this
-- curve is the only way to reach the `y = 0` branch of the affine law.
abbrev Toy0F : Type := FinField 1013
abbrev Toy0P : Type := EllipticCurve Toy0F (0 : Toy0F) (5 : Toy0F)

def mkToy (x y : Nat) : ToyP := ⟨.ofNat x, .ofNat y⟩
def mkToy0 (x y : Nat) : Toy0P := ⟨.ofNat x, .ofNat y⟩

/-! ## Direct Jacobian helper checks -/

/-- Exercise conversion, canonical infinity, doubling, full addition, and
mixed addition independently of the public scalar wrapper. -/
def jacobianEdges (st : Tally) : IO Unit := do
  let inf : secp256k1.Point := ⟨0, 0⟩
  let jInf : EllipticCurve.Jacobian.Point secp256k1.Coord :=
    EllipticCurve.Jacobian.infinity
  let noncanonicalInf : EllipticCurve.Jacobian.Point secp256k1.Coord :=
    ⟨.ofNat 17, .ofNat 23, 0⟩
  let g := secp256k1.generator
  let jg := EllipticCurve.Jacobian.ofAffine g
  let jNegG := EllipticCurve.Jacobian.ofAffine (-g)

  checkBool st "jacobian recognize canonical infinity"
    (EllipticCurve.Jacobian.isInfinity jInf)
  checkBool st "jacobian recognize every Z=0 infinity"
    (EllipticCurve.Jacobian.isInfinity noncanonicalInf)
  checkJacobian st "jacobian canonicalize Z=0"
    (EllipticCurve.Jacobian.canonicalize noncanonicalInf) jInf
  checkJacobian st "jacobian affine O -> canonical infinity"
    (EllipticCurve.Jacobian.ofAffine inf) jInf
  checkPoint st "jacobian Z=0 -> affine O"
    (EllipticCurve.Jacobian.toAffine noncanonicalInf) inf
  checkPoint st "jacobian affine round trip"
    (EllipticCurve.Jacobian.toAffine jg) g

  -- A nontrivial representative of G: (x*z², y*z³, z).
  let z : secp256k1.Coord := .ofNat 11
  let z2 := z * z
  let z3 := z2 * z
  let scaledG : EllipticCurve.Jacobian.Point secp256k1.Coord :=
    ⟨g.x * z2, g.y * z3, z⟩
  checkPoint st "jacobian scaled representative normalizes to G"
    (EllipticCurve.Jacobian.toAffine scaledG) g

  checkJacobian st "jacobian double infinity is canonical"
    (EllipticCurve.Jacobian.double noncanonicalInf) jInf
  checkPoint st "jacobian double G"
    (EllipticCurve.Jacobian.toAffine (EllipticCurve.Jacobian.double jg))
    (refDouble g)
  checkJacobian st "jacobian add O+G"
    (EllipticCurve.Jacobian.add noncanonicalInf jg) jg
  checkJacobian st "jacobian add G+O"
    (EllipticCurve.Jacobian.add jg noncanonicalInf) jg
  checkPoint st "jacobian full add G+2G"
    (EllipticCurve.Jacobian.toAffine <|
      EllipticCurve.Jacobian.add jg (EllipticCurve.Jacobian.double jg))
    (refMulBy g 3)
  checkJacobian st "jacobian full add equal points uses double"
    (EllipticCurve.Jacobian.add jg jg)
    (EllipticCurve.Jacobian.double jg)
  checkJacobian st "jacobian full add inverse is canonical infinity"
    (EllipticCurve.Jacobian.add jg jNegG) jInf

  checkJacobian st "jacobian mixed O+G"
    (EllipticCurve.Jacobian.mixedAdd noncanonicalInf g) jg
  checkJacobian st "jacobian mixed G+O"
    (EllipticCurve.Jacobian.mixedAdd jg inf) jg
  checkPoint st "jacobian mixed G+2G"
    (EllipticCurve.Jacobian.toAffine <|
      EllipticCurve.Jacobian.mixedAdd (EllipticCurve.Jacobian.double jg) g)
    (refMulBy g 3)
  checkJacobian st "jacobian mixed equal points uses double"
    (EllipticCurve.Jacobian.mixedAdd jg g)
    (EllipticCurve.Jacobian.double jg)
  checkJacobian st "jacobian mixed inverse is canonical infinity"
    (EllipticCurve.Jacobian.mixedAdd jg (-g)) jInf

  -- The internal formula is textbook-correct for two-torsion even though the
  -- public wrapper deliberately retains the historical affine result.
  let twoTorsion := mkToy0 555 0
  let jTwo := EllipticCurve.Jacobian.ofAffine twoTorsion
  let jToyInf : EllipticCurve.Jacobian.Point Toy0F :=
    EllipticCurve.Jacobian.infinity
  checkJacobian st "jacobian direct double Y=0 is canonical infinity"
    (EllipticCurve.Jacobian.double jTwo) jToyInf
  checkJacobian st "jacobian full add two-torsion is canonical infinity"
    (EllipticCurve.Jacobian.add jTwo jTwo) jToyInf
  checkJacobian st "jacobian mixed add two-torsion is canonical infinity"
    (EllipticCurve.Jacobian.mixedAdd jTwo twoTorsion) jToyInf

/-! ## Joint secp256k1 multiplication -/

def checkJoint (st : Tally) (name : String)
    (rPoint gPoint : secp256k1.Point) (rScalar gScalar : Nat) : IO Unit :=
  let got : secp256k1.Point :=
    EllipticCurve.Jacobian.toAffine <|
      secp256k1.jointMul rPoint gPoint rScalar gScalar
  let expected :=
    refAdd (refMulBy rPoint rScalar) (refMulBy gPoint gScalar)
  checkPoint st name got expected

/-- Directly cover all four table entries, deterministic full-width pairs,
coefficient/order boundaries, and the table degeneracies `R = G`, `R = -G`,
and infinity.  Expected points always come from the frozen affine oracle. -/
def jointGroup (st : Tally) : IO Unit := do
  let inf : secp256k1.Point := ⟨0, 0⟩
  let g := secp256k1.generator
  let r := refMulBy g 2
  let cases : List (String × Nat × Nat) :=
    [ ("table bits 00", 0, 0),
      ("table bits 10", 1, 0),
      ("table bits 01", 0, 1),
      ("table bits 11", 1, 1),
      ("alternating low bits", 0xAAAAAAAAAAAAAAAA, 0x5555555555555555),
      ("deterministic pair k1/k2", k1 % secp256k1.curveOrder,
        k2 % secp256k1.curveOrder),
      ("deterministic mixed pair", (k1 * 7 + 13) % secp256k1.curveOrder,
        (k2 * 11 + 29) % secp256k1.curveOrder),
      ("coefficient zeros", 0, 0),
      ("coefficient n-1/zero", secp256k1.curveOrder - 1, 0),
      ("coefficient zero/n-1", 0, secp256k1.curveOrder - 1),
      ("coefficient order/one", secp256k1.curveOrder, 1),
      ("coefficient n+1/n-1", secp256k1.curveOrder + 1,
        secp256k1.curveOrder - 1) ]
  for (name, rScalar, gScalar) in cases do
    checkJoint st s!"joint {name}" r g rScalar gScalar
  checkJoint st "joint degeneracy R=G" g g k1 k2
  checkJoint st "joint degeneracy R=-G" (-g) g k1 k2
  checkJoint st "joint degeneracy R=infinity" inf g k1 k2
  checkJoint st "joint degeneracy G=infinity" r inf k1 k2
  checkJoint st "joint degeneracy both infinity" inf inf k1 k2

/-! ## Groups -/

def sweepCurve {F} [Zero F] [DecidableEq F]
    [HAdd F F F] [HSub F F F] [HMul F F F] [HDiv F F F]
    [HPow F Nat F] [OfNat F 3] [OfNat F 2] [ToString F] {a b}
    (st : Tally) (curve : String)
    (points : List (String × EllipticCurve F a b))
    (scalars : List Nat) : IO Unit := do
  for (pname, p) in points do
    for k in scalars do
      checkPoint st s!"diff {curve} {pname}*{k}" (p.mulBy k) (refMulBy p k)

def identities {F} [Zero F] [DecidableEq F] [Neg F]
    [HAdd F F F] [HSub F F F] [HMul F F F] [HDiv F F F]
    [HPow F Nat F] [OfNat F 3] [OfNat F 2] [ToString F] {a b}
    (st : Tally) (curve : String) (g : EllipticCurve F a b)
    (order : Nat) : IO Unit := do
  let inf : EllipticCurve F a b := ⟨0, 0⟩
  checkPoint st s!"id {curve} P + (-P) = O" (g + (-g)) inf
  checkPoint st s!"id {curve} P + O = P" (g + inf) g
  checkPoint st s!"id {curve} O + P = P" (inf + g) g
  checkPoint st s!"id {curve} 2P = P + P" g.double (g + g)
  checkPoint st s!"id {curve} 1P = P" (g.mulBy 1) g
  checkPoint st s!"id {curve} 0P = O" (g.mulBy 0) inf
  checkPoint st s!"id {curve} order*P = O" (g.mulBy order) inf
  checkPoint st s!"id {curve} (order-1)*P = -P" (g.mulBy (order - 1)) (-g)
  checkPoint st s!"id {curve} (order+1)*P = P" (g.mulBy (order + 1)) g
  checkPoint st s!"id {curve} 5P + 9P = 14P"
    ((g.mulBy 5) + (g.mulBy 9)) (g.mulBy 14)
  checkPoint st s!"id {curve} 3*(7P) = 21P" ((g.mulBy 7).mulBy 3) (g.mulBy 21)
  checkBool st s!"id {curve} 7P on curve" (decide (g.mulBy 7).isOnCurve)

def secpPinned (st : Tally) : IO Unit := do
  let g := secp256k1.generator
  let cases : List (Nat × Nat × Nat) :=
    [ (1,
       0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
       0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8),
      (2,
       0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5,
       0x1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a),
      (3,
       0xf9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9,
       0x388f7b0f632de8140fe337e62a37f3566500a99934c2231b6cb9fd7584b8e672),
      (k1,
       0x4646ae5047316b4230d0086c8acec687f00b1cd9d1dc634f6cb358ac0a9a8fff,
       0xfe77b4dd0a4bfb95851f3b7355c781dd60f8418fc8a65d14907aff47c903a559),
      (k2,
       0x88e2ddeb04657dbd0edadf9c1f98da3b3895faa1f00527934dd35d17542ffe9b,
       0x1e7640d7737e24e36d208effb77e86affe670a9a497aa7fb52bf4e687a17fff4),
      (secp256k1.curveOrder - 1,
       0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
       0xb7c52588d95c3b9aa25b0403f1eef75702e84bb7597aabe663b82f6f04ef2777) ]
  for (k, x, y) in cases do
    checkPoint st s!"pin secp256k1 G*{k}" (g.mulBy k) (mkSecp x y)

def blsPinned (st : Tally) : IO Unit := do
  let g1 := blsG1Generator
  let g1cases : List (Nat × Nat × Nat) :=
    [ (2,
       838589206289216005799424730305866328161735431124665289961769162861615689790485775997575391185127590486775437397838,
       3450209970729243429733164009999191867485184320918914219895632678707687208996709678363578245114137957452475385814312),
      (3,
       1527649530533633684281386512094328299672026648504329745640827351945739272160755686119065091946435084697047221031460,
       487897572011753812113448064805964756454529228648704488481988876974355015977479905373670519228592356747638779818193),
      (7,
       3872473689207892378470335395114902631176541028916158626161662840934315241539439160301564344905260612642783644023991,
       2547806390474846378491145127515427451279430889101277169890334737406180277792171092197824251632631671609860505999900),
      (k1,
       1032310052213111954219872643110557886857426355660880187884944929197921151497879875809567553053909278931474809326548,
       864098652078652984775100613126389130872250925668471516116602988297282146682432492413990258728259241305725439599101) ]
  for (k, x, y) in g1cases do
    checkPoint st s!"pin bls-g1 G*{k}" (g1.mulBy k) (mkBls1 x y)
  let g2 := blsG2Generator
  checkPoint st "pin bls-g2 G*2" (g2.mulBy 2)
    (mkBls2
      3419974069068927546093595533691935972093267703063689549934039433172037728172434967174817854768758291501458544631891
      1586560233067062236092888871453626466803933380746149805590083683748120990227823365075019078675272292060187343402359
      678774053046495337979740195232911687527971909891867263302465188023833943429943242788645503130663197220262587963545
      2374407843478705782611042739236452317510200146460567463070514850492917978226342495167066333366894448569891658583283)
  checkPoint st "pin bls-g2 G*7" (g2.mulBy 7)
    (mkBls2
      709940604317203372084363045234008717826848775332345256708783709065481460296552174594695120412283630827121870605628
      2002357927014343339248864414634364694493007010346797894329949366020574238568791702800705687329188574611271276704968
      1341746576224694386674361975424855739534560887571639474887265245206456367479326365108850910936317989017305100831965
      912045267738927660774159947293138338745237549910946144646281482158519356186671009156889035570132788233623423316000)

def bnPinned (st : Tally) : IO Unit := do
  let g := bn254Generator
  let cases : List (Nat × Nat × Nat) :=
    [ (2,
       1368015179489954701390400359078579693043519447331113978918064868415326638035,
       9918110051302171585080402603319702774565515993150576347155970296011118125764),
      (3,
       3353031288059533942658390886683067124040920775575537747144343083137631628272,
       19321533766552368860946552437480515441416830039777911637913418824951667761761),
      (7,
       10415861484417082502655338383609494480414113902179649885744799961447382638712,
       10196215078179488638353184030336251401353352596818396260819493263908881608606) ]
  for (k, x, y) in cases do
    checkPoint st s!"pin bn254-g1 G*{k}" (g.mulBy k) (mkBn x y)

/-- The frozen degenerate group.  On a curve whose group order is even, the
affine law's doubling branch divides by `2y = 0`; `FinField.inv 0 = 0`, so it
returns a point that is *not* the point at infinity.  These expectations record
what the implementation does today, and they are only reachable on the toy
curves: secp256k1, BN254 G1, BLS12-381 G1 and BLS12-381 G2 all have odd group
order (equivalently `-b` is not a cube in the relevant field), so no point with
`y = 0` exists on any curve this repository actually uses. -/
def frozenDegenerate (st : Tally) : IO Unit := do
  let t2 : ToyP := mkToy 2 0
  checkPoint st "frozen toy-a1 double (2,0)" t2.double (mkToy 1005 0)
  checkPoint st "frozen toy-a1 (2,0)*2" (t2.mulBy 2) (mkToy 1005 0)
  checkPoint st "frozen toy-a1 (2,0)*3" (t2.mulBy 3) (mkToy 2 0)
  checkPoint st "frozen toy-a1 (2,0)*4" (t2.mulBy 4) (mkToy 8 0)
  -- (1,110) has order 480, but the ladder for 480 doubles the order-two point
  -- 240*(1,110), so the result is the degenerate value rather than O.
  checkPoint st "frozen toy-a1 (1,110)*480" ((mkToy 1 110).mulBy 480) (mkToy 144 0)
  let u2 : Toy0P := mkToy0 555 0
  checkPoint st "frozen toy-a0 double (555,0)" u2.double (mkToy0 916 0)
  checkPoint st "frozen toy-a0 (555,0)*2" (u2.mulBy 2) (mkToy0 916 0)
  checkPoint st "frozen toy-a0 (555,0)*3" (u2.mulBy 3) (mkToy0 555 0)
  checkPoint st "frozen toy-a0 (2,191)*1014" ((mkToy0 2 191).mulBy 1014) (mkToy0 916 0)

/-- Toy-curve behavior that *is* mathematically correct: odd-order points never
meet the `y = 0` branch. -/
def toyPinned (st : Tally) : IO Unit := do
  checkPoint st "pin toy-a1 (1,110)*7" ((mkToy 1 110).mulBy 7) (mkToy 819 165)
  checkPoint st "pin toy-a1 (1,110)*100" ((mkToy 1 110).mulBy 100) (mkToy 863 828)
  checkPoint st "pin toy-a1 (1,110)*479" ((mkToy 1 110).mulBy 479) (mkToy 1 899)
  -- x = 0 with y ≠ 0 is a real point, not the infinity sentinel.
  checkPoint st "pin toy-a1 (0,303)*15 = O" ((mkToy 0 303).mulBy 15) ⟨0, 0⟩
  checkPoint st "pin toy-a1 (0,303)*16" ((mkToy 0 303).mulBy 16) (mkToy 0 303)
  checkPoint st "pin toy-a0 (1,78)*7" ((mkToy0 1 78).mulBy 7) (mkToy0 194 252)
  checkPoint st "pin toy-a0 (1,78)*100" ((mkToy0 1 78).mulBy 100) (mkToy0 497 302)
  checkPoint st "pin toy-a0 (1,78)*507 = O" ((mkToy0 1 78).mulBy 507) ⟨0, 0⟩
  checkPoint st "pin toy-a0 (1,78)*1013" ((mkToy0 1 78).mulBy 1013) (mkToy0 1 935)

/-! ## Recovery matrix -/

def sigHash : Nat :=
  0xd5d014a4e0d4726c53875206057ee84dd3ca9492e940ed8dc5feb45e9a650a5d
def sigR : Nat :=
  0x532adeb14b96b65b64fc6481c3244cf1e2855ec91802bf441741dc912769b40d
def sigS : Nat :=
  0x785e45c2c421b3c98018897863ac53b03f278b2888e4d38ac35a5b2ff2293b32
def sigV : Bool := false

def gx : Nat := secp256k1.generator.x.val

structure RecoverCase where
  name : String
  h : Nat
  v : Bool
  r : Nat
  s : Nat
  expected : Option Nat

def recoverCases : List RecoverCase :=
  [ -- Valid signature; address cross-checked against EELS secp256k1_recover.
    ⟨"real-signature", sigHash, sigV, sigR, sigS,
      some 0xfcad0b19bb29d4674531d6f115237e16afce377c⟩,
    -- The other parity bit recovers a different, still well-defined, key.
    ⟨"real-signature/other-parity", sigHash, !sigV, sigR, sigS,
      some 0xc7217adbf9d908cbd5714ea78eca7993b98d80e1⟩,
    -- The synthetic tuple named in the optimization plan, both parities.  It
    -- succeeds, but two of its three multiplications are by 1 and 2.
    ⟨"synthetic h=1 r=Gx s=2 v=false", 1, false, gx, 2,
      some 0x0d9336b0c59b04354fb0082b3055caa29a112849⟩,
    ⟨"synthetic h=1 r=Gx s=2 v=true", 1, true, gx, 2,
      some 0x0fd781562e2fa26c78bed5c9dd542997afb113d9⟩,
    -- x³ + 7 = 7 is not a quadratic residue mod p, so the square root fails.
    ⟨"r=0", 0x1234, false, 0, 3, none⟩,
    -- Smallest r > 0 whose x³ + 7 is a non-residue.
    ⟨"r=5 (no square root)", 0x1234, false, 5, 3, none⟩,
    ⟨"r=1", 0x1234, false, 1, 3,
      some 0x7f35a4cf4131467996952b4ccdac2731e490f4a6⟩,
    -- r = n reduces to 0 in the scalar field, so rInv = FinField.inv 0 = 0 and
    -- Q = O·0 = (0,0): the recovered address is keccak(64 zero bytes)[12:].
    -- The EVM caller rejects this input before calling; the public definition
    -- must keep the behavior anyway.
    ⟨"r=n", 0x1234, false, secp256k1.curveOrder, 3,
      some 0x3f17f1962b36e491b30a40b2405849e597ba5fb5⟩,
    ⟨"s=0", sigHash, sigV, sigR, 0,
      some 0x9335fbcfb5dfaa3c467567af2d4ab7d545cd5492⟩,
    ⟨"s=n (reduces to 0)", sigHash, sigV, sigR, secp256k1.curveOrder,
      some 0x9335fbcfb5dfaa3c467567af2d4ab7d545cd5492⟩,
    ⟨"h=0", 0, sigV, sigR, sigS,
      some 0xc34c0677241ab6aecd7db950993e785f4df432c5⟩,
    ⟨"h=n (reduces to 0)", secp256k1.curveOrder, sigV, sigR, sigS,
      some 0xc34c0677241ab6aecd7db950993e785f4df432c5⟩,
    -- sR = zG = G, so the intermediate O is the point at infinity.
    ⟨"O = infinity", 1, false, gx, 1, none⟩,
    ⟨"O = infinity/other-parity", 1, true, gx, 1,
      some 0xbfe50111d3c73a6fd6cc132985b0227ea4508b32⟩,
    -- Every scalar reduces to zero.
    ⟨"h=n r=n s=n", secp256k1.curveOrder, true, secp256k1.curveOrder,
      secp256k1.curveOrder, none⟩ ]

def recoverGroup (st : Tally) : IO Unit := do
  for c in recoverCases do
    let got := secp256k1.recover c.h.toB256 c.v c.r.toB256 c.s.toB256
    let ref := refRecover c.h.toB256 c.v c.r.toB256 c.s.toB256
    let exp : Option Adr := c.expected.map Nat.toAdr
    checkAdr st s!"pin recover {c.name}" got exp
    checkAdr st s!"diff recover {c.name}" got ref
  let differentialCases : List (String × Nat × Bool × Nat × Nat) :=
    [ ("random-looking coefficients", k1, false, sigR, k2),
      ("random-looking coefficients/other parity", k1, true, sigR, k2),
      ("s=n-1", k1, false, sigR, secp256k1.curveOrder - 1),
      ("s=n+1", k2, true, sigR, secp256k1.curveOrder + 1),
      ("h=n-1", secp256k1.curveOrder - 1, false, sigR, k1),
      ("h=n+1", secp256k1.curveOrder + 1, true, sigR, k2),
      ("invalid r=n+1", k1, false, secp256k1.curveOrder + 1, k2),
      ("invalid r=B256 max", k2, true, (2 ^ 256) - 1, k1) ]
  for (name, h, v, r, s) in differentialCases do
    checkAdr st s!"diff recover {name}"
      (secp256k1.recover h.toB256 v r.toB256 s.toB256)
      (refRecover h.toB256 v r.toB256 s.toB256)

end ECOracle

open ECOracle in
def main : IO UInt32 := do
  let st ← IO.mkRef ((0, 0) : Nat × Nat)

  IO.println "--- pinned external multiples ---"
  secpPinned st
  blsPinned st
  bnPinned st
  toyPinned st

  IO.println "--- direct Jacobian helper edges ---"
  jacobianEdges st

  IO.println "--- joint secp256k1 multiplication ---"
  jointGroup st

  IO.println "--- algebraic identities ---"
  identities st "secp256k1" secp256k1.generator secp256k1.curveOrder
  identities st "bn254-g1" bn254Generator altBn128CurveOrder
  identities st "bls-g1" blsG1Generator blsCurveOrder
  identities st "bls-g2" blsG2Generator blsCurveOrder
  -- (1,78) has order 507 and (0,303) order 15; both are odd, so the ladder
  -- never doubles an order-two point.
  identities st "toy-a0" (mkToy0 1 78) 507
  identities st "toy-a1" (mkToy 0 303) 15

  IO.println "--- differential: public mulBy vs affine reference ---"
  let secpPoints : List (String × secp256k1.Point) :=
    [ ("G", secp256k1.generator), ("O", ⟨0, 0⟩),
      ("-G", -secp256k1.generator), ("2G", secp256k1.generator.double) ]
  sweepCurve st "secp256k1" secpPoints smallScalars
  sweepCurve st "secp256k1" [("G", secp256k1.generator)]
    (bigScalars secp256k1.curveOrder)
  let bnPoints : List (String × BNP) :=
    [ ("G", bn254Generator), ("O", ⟨0, 0⟩), ("-G", -bn254Generator),
      ("2G", bn254Generator.double) ]
  sweepCurve st "bn254-g1" bnPoints smallScalars
  sweepCurve st "bn254-g1" [("G", bn254Generator)]
    (bigScalars altBn128CurveOrder)
  let bls1Points : List (String × BLSP) :=
    [ ("G", blsG1Generator), ("O", ⟨0, 0⟩), ("-G", -blsG1Generator),
      ("2G", blsG1Generator.double) ]
  sweepCurve st "bls-g1" bls1Points smallScalars
  sweepCurve st "bls-g1" [("G", blsG1Generator)] (bigScalars blsCurveOrder)
  let bls2Points : List (String × BLSP2) :=
    [ ("G", blsG2Generator), ("O", ⟨0, 0⟩), ("-G", -blsG2Generator),
      ("2G", blsG2Generator.double) ]
  sweepCurve st "bls-g2" bls2Points smallScalars
  sweepCurve st "bls-g2" [("G", blsG2Generator)] (bigScalars blsCurveOrder)
  let toyPoints : List (String × ToyP) :=
    [ ("P", mkToy 1 110), ("O", ⟨0, 0⟩), ("-P", -(mkToy 1 110)),
      ("(0,303)", mkToy 0 303), ("2-torsion", mkToy 2 0) ]
  sweepCurve st "toy-a1" toyPoints (smallScalars ++ [239, 240, 479, 480, 481, 960])
  let toy0Points : List (String × Toy0P) :=
    [ ("P", mkToy0 1 78), ("O", ⟨0, 0⟩), ("-P", -(mkToy0 1 78)),
      ("full-order", mkToy0 2 191), ("2-torsion", mkToy0 555 0) ]
  sweepCurve st "toy-a0" toy0Points (smallScalars ++ [506, 507, 508, 1013, 1014])

  IO.println "--- frozen degenerate (current behavior of the y = 0 branch) ---"
  frozenDegenerate st

  IO.println "--- secp256k1.recover matrix ---"
  recoverGroup st

  let (passed, failed) ← st.get
  if failed = 0 then
    IO.println s!"OK — ec: {passed}/{passed} cases PASS"
    return 0
  else
    IO.println s!"RED — ec: {passed}/{passed + failed} cases PASS, {failed} FAIL"
    return 1
