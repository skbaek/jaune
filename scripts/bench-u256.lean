import Jaune.Basic
import Jaune.Execution

/-!
Step-1 U256 microbenchmark instrument.

Compile and run with `scripts/run-bench-u256.sh <label>`.  That wrapper uses
standalone `lean -c` followed by `leanc -O2`; this benchmark is not a Lake
target.  Timing a pure value that is only demanded after the second clock read
can produce a bogus near-zero result, so every result is forced through the
`@[noinline]` IO boundary below before the finish time is sampled.

Inputs are salted with a per-run `nonce` taken from the clock, so exact
operand streams differ across runs.  This is benign for the long-iteration
rows, but the `exp` row (100 iterations, each output chained as the next
base) is NOT comparable across runs: `Nat.powMod` cost tracks operand
magnitude, and once the chain hits a base that truncates to 0 mod 2^256
(visible as `sink=0...0`) the remaining iterations run on tiny `Nat`s and
the row reads artificially fast — observed swings exceed 10x (e.g. 179 vs
2471 ns/op on identical binaries, step 3).  Compare exp performance across
revisions via fixture wall-clocks (`vmPerformance/loopExp.json`), not this
row.

The `codec` row (step 5) bundles encode and decode: it times
`B256.toB8L` followed by `B8L.toB256` on a 32-byte list, because the
decoder needs a fresh byte list per iteration and a hoistable constant
input would be optimized out of the loop.  `B256.toB8L` is unchanged by
step 5, so the row's delta across revisions is still attributable to the
decoder alone; the encode half is a fixed additive offset.
-/

def sample : B256 :=
  (0x123456789abcdef0 : B64).toB256 <<< 128 ||| 0xfedcba9876543211

def drive (n : Nat) (seed : B256) (f : Nat → B256 → B256) : B256 :=
  go n seed where
  go : Nat → B256 → B256
    | 0, x => x
    | n + 1, x => go n (f n x)

@[noinline] def forceB256 (x : B256) : IO B256 := pure x

def bench (label : String) (iterations : Nat) (nonce : Nat)
    (f : Nat → B256 → B256) : IO Unit := do
  let seed := sample + nonce.toB256
  let start ← IO.monoNanosNow
  let sink ← forceB256 (drive iterations seed f)
  let finish ← IO.monoNanosNow
  IO.println s!"{label}\t{(finish - start) / iterations} ns/op\titerations={iterations}\tsink={sink.toHex}"

@[noinline] def forceB8L (x : B8L) : IO B8L := pure x

-- BLAKE2b compression driver: the same forced-sequencing discipline as
-- `bench`, but the loop output is a byte list, and each iteration's digest is
-- folded back into the next iteration's message so the call cannot be hoisted.
def benchBlake2 (label : String) (iterations : Nat) (nonce : Nat)
    (numRounds : Nat) : IO Unit := do
  let h : List B64 := blake2IV
  let rec go : Nat → List B64 → List B64
    | 0, m => m
    | k + 1, m =>
      let out := (bCompress numRounds h m 0 0 false).getD []
      go k (m.set 0 ((B8L.toB64 (out.take 8)) ^^^ (k.toUInt64)))
  let m0 : List B64 := (List.range 16).map (fun i => (nonce + i).toUInt64)
  let start ← IO.monoNanosNow
  let sink ← forceB8L
    ((bCompress numRounds h (go iterations m0) 0 0 false).getD [])
  let finish ← IO.monoNanosNow
  IO.println s!"{label}\t{(finish - start) / iterations} ns/op\titerations={iterations}\tsink={sink.take 4}"

def main : IO Unit := do
  let nonce ← IO.monoNanosNow
  bench "add" 1000000 nonce (fun i x => x + sample + i.toB256)
  bench "and" 1000000 nonce (fun i x => (x &&& sample) ^^^ i.toB256)
  bench "lt" 1000000 nonce (fun i x => if x < sample then x + i.toB256 else x - i.toB256)
  bench "mul" 200000 nonce (fun i x => x * sample + i.toB256)
  bench "div-2^128" 20000 nonce (fun i x => x / ((1 : Nat).toB256 <<< 128) + sample + i.toB256)
  bench "div-3" 20000 nonce (fun i x => x / 3 + sample + i.toB256)
  bench "exp" 100 nonce (fun i x => B256.bexp x (i + 1).toB256)
  bench "codec" 200000 nonce (fun i x => (x + i.toB256).toB8L.toB256)
  -- Step-6 precompile inner-loop rows.  `sha256` hashes a fresh 32-byte list
  -- per iteration (one padded chunk, so one full 64-round compression);
  -- `blake2f-12` runs one 12-round BLAKE2b compression, the round count of
  -- the EIP-152 reference vectors.
  bench "sha256" 100000 nonce (fun i x => B8L.sha256 (x + i.toB256).toB8L)
  benchBlake2 "blake2f-12" 100000 nonce 12
  -- Keccak rows (keccak/bytelayer arc).  Each iteration hashes a fresh
  -- digest-dependent byte list, so the call cannot be hoisted.  The rows
  -- deliberately include B8L construction and traversal: that marshalling is
  -- part of the memory-fed keccak path under measurement.  `keccak64` is the
  -- storage-slot shape (one permutation); `keccak512` spans four permutations
  -- and three full-rate blocks.
  bench "keccak64" 100000 nonce
    (fun i x => B8L.keccak ((x + i.toB256).toB8L ++ (x - i.toB256).toB8L))
  bench "keccak512" 20000 nonce
    (fun i x => B8L.keccak ((List.range 16).flatMap
      (fun j => (x + (16 * i + j).toB256).toB8L)))
