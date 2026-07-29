import Jaune.EC
import Jaune.BLS

/-!
Elliptic-curve microbenchmark instrument.

Compile and run with `scripts/run-bench-ec.sh <label>`.  That wrapper uses
standalone `lean -c` followed by `leanc -O2` and links against the native
objects Lake already recorded for the `jaune` executable; this benchmark is not
a Lake target and never times interpreted reduction.

Discipline, following `scripts/bench-u256.lean`:

* Every row's result is forced through the `@[noinline] forceNat` IO boundary
  *before* the finish timestamp is read, so a lazily-suspended thunk cannot be
  mistaken for a fast row.
* Unlike the U256 instrument, **no clock nonce is used**.  Every input below is
  a fixed constant, because these rows are compared across optimization steps
  and a per-run input stream would make the medians incomparable.  Iteration
  `i` only shifts the scalar/hash by `i`, which keeps the operand bit-length
  (and therefore the double-and-add cost) constant while preventing the loop
  body from being hoisted out as a loop invariant.  Pairing rows instead use
  one fully forced generator pairing per process; their cost is already large
  enough for stable process-level repetitions.
* Each row prints a `sink` that is a deterministic function of every result it
  produced.  A semantics-preserving optimization must reproduce the sink value
  exactly; a changed sink means the row computed something different, not that
  it got faster.

Inputs and their provenance:

* `benchSig{Hash,R,S,V}` is a real secp256k1 signature over the ASCII message
  `elevm ec oracle step 1`, generated with libsecp256k1 via coincurve 20.0.0 in
  the pinned execution-specs venv:

  ```sh
  ~/execution-specs/venv/bin/python -c '
  from coincurve import PrivateKey
  from eth_utils import keccak
  d = 0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF
  h = keccak(b"elevm ec oracle step 1")
  sig = PrivateKey.from_int(d).sign_recoverable(h, hasher=None)
  print(h.hex(), sig[:32].hex(), sig[32:64].hex(), sig[64])'
  ```

  This tuple is used instead of the synthetic `h=1, r=generator.x, s=2` one
  because all three of `h`, `s`, and `rInv` are full 256-bit scalars, so the
  row measures three full double-and-add ladders — the cost an ordinary
  `ecrecover` actually pays.  The synthetic tuple would spend two of its three
  multiplications on the scalars 1 and 2.  Both tuples are checked for exact
  output by `scripts/check-ec.lean`.
* `benchScalar` is the fixed 256-bit pattern
  `0xFEDCBA98...` reduced into each curve's scalar field.  It is only an
  operand; no secrecy or randomness is claimed.
* `bn254G2Generator` is the affine generator from the pinned `py_ecc 8.0.0`
  `optimized_bn128` module.  `BNF2.mk` uses the coefficient order opposite
  to py_ecc's displayed `(c0, c1)`, so each pair is reversed here; the
  preflight checks the resulting point before any timed pairing row.
-/

-- Real signature over keccak("elevm ec oracle step 1") under the private key
-- 0x0123456789ABCDEF... (see the header for the exact reproduction command).
def benchSigHash : Nat :=
  0xd5d014a4e0d4726c53875206057ee84dd3ca9492e940ed8dc5feb45e9a650a5d

def benchSigR : Nat :=
  0x532adeb14b96b65b64fc6481c3244cf1e2855ec91802bf441741dc912769b40d

def benchSigS : Nat :=
  0x785e45c2c421b3c98018897863ac53b03f278b2888e4d38ac35a5b2ff2293b32

-- coincurve recovery id 0, i.e. even y, i.e. Jaune's `v = false`.
def benchSigV : Bool := false

-- Fixed scalar pattern, reduced per curve at use sites.
def benchScalar : Nat :=
  0xFEDCBA9876543210FEDCBA9876543210FEDCBA9876543210FEDCBA9876543210

def bn254G2Generator : BNP2 :=
  ⟨
    BNF2.mk
      11559732032986387107991004021392285783925812861821192530917403151452391805634
      10857046999023057135944570762232829481370756359578518086990519993285655852781,
    BNF2.mk
      4082367875863433681332203403145435568316851327593401208105741076214120093531
      8495653923123431417604973247489272438418190587263600148770280649306958101930
  ⟩

@[noinline] def forceNat (x : Nat) : IO Nat := pure x

-- Sink mixer: order-sensitive, cheap, and independent of the values' size.
def mix (acc : Nat) (x : Nat) : Nat := (acc * 1000003 + x) % 1000000007

def fieldSink {p} {m : FinFields p} (x : GaloisField p m) : Nat :=
  x.val.foldl (fun acc c => mix acc c.val) 0

def drive (n : Nat) (acc : Nat) (f : Nat → Nat → Nat) : Nat :=
  go n acc where
  go : Nat → Nat → Nat
    | 0, x => x
    | k + 1, x => go k (f k x)

def bench (label : String) (iterations : Nat) (f : Nat → Nat → Nat) : IO Unit := do
  let start ← IO.monoNanosNow
  let sink ← forceNat (drive iterations 1 f)
  let finish ← IO.monoNanosNow
  IO.println
    s!"{label}\t{(finish - start) / iterations} ns/op\titerations={iterations}\tsink={sink}"

-- Address expected from the benchmark tuple, cross-checked against
-- libsecp256k1 and EELS by `scripts/check-ec.lean`.
def benchSigAdr : Nat := 0xfcad0b19bb29d4674531d6f115237e16afce377c

-- Rendering only. `String.drop` yields a `String.Slice`, which has no
-- `DecidableEq`, so an address is never compared in this form; `Adr.toNat` is
-- the comparison, matching `checkAdr` in `scripts/check-ec.lean`.
def adrHex (a : Adr) : String := "0x" ++ (a.toB256.toHex.drop 24)

def main : IO UInt32 := do
  -- Preflight, outside every timed region: the recovery row is only meaningful
  -- if its tuple takes the successful path, in which case it performs three
  -- full-length scalar multiplications (`s`, `h`, and `rInv` are all 255–256
  -- bits) rather than failing early in the square root.
  match secp256k1.recover benchSigHash.toB256 benchSigV
          benchSigR.toB256 benchSigS.toB256 with
  | none =>
    IO.println "ERROR: the benchmark signature tuple does not recover"
    return 1
  | some adr =>
    if adr.toNat ≠ benchSigAdr then
      IO.println s!"ERROR: benchmark tuple recovered {adrHex adr}, expected {adrHex benchSigAdr.toAdr}"
      return 1
    IO.println s!"# recover tuple recovers {adrHex adr} (full successful path)"
  if !bn254G2Generator.isOnCurve then
    IO.println "ERROR: the pinned BN254 G2 benchmark generator is not on curve"
    return 1
  -- Full ecrecover: three 256-bit scalar multiplications, one scalar-field
  -- inversion, one affine subtraction, one keccak.  Iteration `i` perturbs the
  -- message hash only, so `r` (and therefore the square root) is fixed.
  bench "secp256k1-recover" 200 (fun i acc =>
    match secp256k1.recover (benchSigHash + i).toB256 benchSigV
            benchSigR.toB256 benchSigS.toB256 with
    | some adr => mix acc adr.toNat
    | none => mix acc 0)
  -- One 256-bit scalar multiplication on the same curve, for attribution
  -- between the ladder itself and recovery's surrounding algebra.
  bench "secp256k1-mul" 200 (fun i acc =>
    mix acc (secp256k1.generator.mulBy
      ((benchScalar + i) % secp256k1.curveOrder)).x.val)
  -- BN254 G1 uses the same generic ladder over a 254-bit base field.
  bench "bn254-g1-mul" 200 (fun i acc =>
    mix acc ((⟨1, 2⟩ : BNP).mulBy
      ((benchScalar + i) % altBn128CurveOrder)).x.val)
  bench "bls-g1-mul" 200 (fun i acc =>
    mix acc (blsG1Generator.mulBy
      ((benchScalar + i) % blsCurveOrder)).x.val)
  bench "bls-g2-mul" 100 (fun i acc =>
    mix acc ((blsG2Generator.mulBy
      ((benchScalar + i) % blsCurveOrder)).x.val.foldl
        (fun a c => mix a c.val) 0))
  -- Full pairings include the Miller loop and final exponentiation.  The
  -- corresponding `-miller` rows disable only the final exponentiation, so
  -- Step 7 can distinguish affine loop cost from the exponentiation tail.
  bench "bn254-pairing" 1 (fun _ acc =>
    match pairing bn254G2Generator (⟨1, 2⟩ : BNP) with
    | some f => mix acc (fieldSink f)
    | none => mix acc 0)
  bench "bn254-miller" 1 (fun _ acc =>
    match pairing bn254G2Generator (⟨1, 2⟩ : BNP) false with
    | some f => mix acc (fieldSink f)
    | none => mix acc 0)
  bench "bls-pairing" 1 (fun _ acc =>
    match blsPairing blsG2Generator blsG1Generator with
    | some f => mix acc (fieldSink f)
    | none => mix acc 0)
  bench "bls-miller" 1 (fun _ acc =>
    match blsPairing blsG2Generator blsG1Generator false with
    | some f => mix acc (fieldSink f)
    | none => mix acc 0)
  return 0
