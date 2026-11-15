import Jaune.T8n
import Jaune.Machine
import Experiments.S6d.BitVecWords

/-!
# jsn-s6d runtime comparison: `B256` (current) against `BitVec 256`

`s6d-bench <u256.json> <reps> <loopN>`

1. **u256 oracle vectors.** Parses `scripts/vectors/u256.json` once, keeps the 21,359 word-op
   vectors (all ops except `keccak*`, `ofB8L`, `codec`, `bytecount`, `exp_gas`, which do not
   depend on the word operations measured here), converts arguments and expected results to
   each representation outside the timed region, checks every result against the oracle's
   expected value (this is the EVM-exactness check of the `BitVec` operations), then times
   `reps` passes over all vectors per representation.
2. **loopMul kernels.** The four loop bodies of `VMTests/vmPerformance/loopMul` (its Solidity
   filler: `r += y`, `r /= y; r += k`, `r *= y`, `r = mulmod(r, y, k)`, each with the loop
   counter `i += 1; i < n`), run `loopN` iterations per representation on the filler's
   constants. Word arithmetic only: no interpreter, gas or memory.
-/

open Jaune S6d

def hexToNat (s : String) : Nat :=
  let s := if s.startsWith "0x" then s.drop 2 else s
  s.foldl (fun n c =>
    let d := if c.isDigit then c.toNat - '0'.toNat
      else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0
    n * 16 + d) 0

def b256Op (op : String) (xs : Array B256) : Option B256 :=
  match op, xs.toList with
  | "add", [x, y] => some (x + y)
  | "sub", [x, y] => some (x - y)
  | "mul", [x, y] => some (x * y)
  | "div", [x, y] => some (x / y)
  | "mod", [x, y] => some (x % y)
  | "sdiv", [x, y] => some (B256.sdiv x y)
  | "smod", [x, y] => some (B256.smod x y)
  | "addmod", [x, y, z] => some (B256.addmod x y z)
  | "mulmod", [x, y, z] => some (B256.mulmod x y z)
  | "exp", [x, y] => some (x ^ y)
  | "signextend", [x, y] => some (B256.signext x y)
  | "lt", [x, y] => some (B256.ltCheck x y)
  | "gt", [x, y] => some (B256.gtCheck x y)
  | "slt", [x, y] => some (B256.sltCheck x y)
  | "sgt", [x, y] => some (B256.sgtCheck x y)
  | "eq", [x, y] => some (B256.eqCheck x y)
  | "iszero", [x] => some (B256.eqCheck x 0)
  | "and", [x, y] => some (x &&& y)
  | "or", [x, y] => some (x ||| y)
  | "xor", [x, y] => some (x ^^^ y)
  | "not", [x] => some (~~~ x)
  | "byte", [x, y] => some (List.getD y.toBytes x.toNat 0).toB256
  | "shl", [x, y] => some (y <<< x.toNat)
  | "shr", [x, y] => some (y >>> x.toNat)
  | "sar", [x, y] => some (B256.arithShiftRight y x.toNat)
  | _, _ => none

/-- `BitVec` shifts take a `Nat` amount and compute through `Nat`: `x <<< n` is
`(x.toNat <<< n) % 2 ^ 256`, so an unguarded EVM shift by a huge word would build a huge
number. The EVM wrappers clamp the amount first. -/
def wShl (y : W) (n : Nat) : W := if n < 256 then y <<< n else 0
def wShr (y : W) (n : Nat) : W := if n < 256 then y >>> n else 0
def wSar (y : W) (n : Nat) : W := W.sar y (min n 256)

def wOp (op : String) (xs : Array W) : Option W :=
  match op, xs.toList with
  | "add", [x, y] => some (x + y)
  | "sub", [x, y] => some (x - y)
  | "mul", [x, y] => some (x * y)
  | "div", [x, y] => some (x / y)
  | "mod", [x, y] => some (W.mod x y)
  | "sdiv", [x, y] => some (W.sdiv x y)
  | "smod", [x, y] => some (W.smod x y)
  | "addmod", [x, y, z] => some (W.addmod x y z)
  | "mulmod", [x, y, z] => some (W.mulmod x y z)
  | "exp", [x, y] => some (W.exp x y)
  | "signextend", [x, y] => some (W.signext x y)
  | "lt", [x, y] => some (W.ltCheck x y)
  | "gt", [x, y] => some (W.gtCheck x y)
  | "slt", [x, y] => some (W.sltCheck x y)
  | "sgt", [x, y] => some (W.sgtCheck x y)
  | "eq", [x, y] => some (W.eqCheck x y)
  | "iszero", [x] => some (W.eqCheck x 0)
  | "and", [x, y] => some (x &&& y)
  | "or", [x, y] => some (x ||| y)
  | "xor", [x, y] => some (x ^^^ y)
  | "not", [x] => some (~~~ x)
  | "byte", [x, y] => some (W.ofNat (List.getD (W.toBytes y) x.toNat 0).toNat)
  | "shl", [x, y] => some (wShl y x.toNat)
  | "shr", [x, y] => some (wShr y x.toNat)
  | "sar", [x, y] => some (wSar y x.toNat)
  | _, _ => none

def skipOps : List String := ["keccak", "keccak_ba", "ofB8L", "codec", "bytecount", "exp_gas"]

structure Vec where
  op : String
  args : Array Nat
  expected : Nat

def loadVectors (path : String) : IO (Array Vec) := do
  let j ← readJsonFile path
  let vs ← match j.getObjVal? "vectors" with
    | .ok (.arr a) => pure a
    | _ => throw (IO.userError "no vectors array")
  let mut out := #[]
  for v in vs do
    let .ok (.str op) := v.getObjVal? "op" | throw (IO.userError "op")
    if skipOps.contains op then continue
    let .ok (.arr as) := v.getObjVal? "args" | throw (IO.userError "args")
    let args := as.map fun a => match a with | .str s => hexToNat s | _ => 0
    let expected ← match v.getObjVal? "expected" with
      | .ok (.str s) => pure (hexToNat s)
      | .ok (.num n) => pure n.mantissa.toNat
      | _ => throw (IO.userError "expected")
    out := out.push { op, args, expected }
  return out

/-- Run every vector `reps` times; return (elapsed ns, failures on the first pass). -/
def runAll {α : Type} [DecidableEq α] (f : String → Array α → Option α)
    (vs : Array (String × Array α × α)) (reps : Nat) : IO (Nat × Nat) := do
  let mut fails := 0
  for (op, args, e) in vs do
    if f op args ≠ some e then fails := fails + 1
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  for _ in [0:reps] do
    for (op, args, e) in vs do
      if f op args = some e then acc := acc + 1
  let t1 ← IO.monoNanosNow
  if acc = 12345678901 then IO.println "unreachable"
  return (t1 - t0, fails)

def loopB (n : Nat) (x y k : B256) : B256 × B256 × B256 × B256 := Id.run do
  let one : B256 := 1
  let nB : B256 := n.toB256
  let mut r1 := x; let mut r2 := x; let mut r3 := x; let mut r4 := x
  let mut i : B256 := 0
  while i < nB do
    r1 := r1 + y
    i := i + one
  i := 0
  while i < nB do
    r2 := r2 / y; r2 := r2 + k
    i := i + one
  i := 0
  while i < nB do
    r3 := r3 * y
    i := i + one
  i := 0
  while i < nB do
    r4 := B256.mulmod r4 y k
    i := i + one
  return (r1, r2, r3, r4)

def loopW (n : Nat) (x y k : W) : W × W × W × W := Id.run do
  let one : W := 1
  let nW : W := W.ofNat n
  let mut r1 := x; let mut r2 := x; let mut r3 := x; let mut r4 := x
  let mut i : W := 0
  while i < nW do
    r1 := r1 + y
    i := i + one
  i := 0
  while i < nW do
    r2 := r2 / y; r2 := r2 + k
    i := i + one
  i := 0
  while i < nW do
    r3 := r3 * y
    i := i + one
  i := 0
  while i < nW do
    r4 := W.mulmod r4 y k
    i := i + one
  return (r1, r2, r3, r4)

def main (argv : List String) : IO UInt32 := do
  let path := argv.getD 0 "scripts/vectors/u256.json"
  let reps := (argv.getD 1 "20").toNat!
  let loopN := (argv.getD 2 "1000000").toNat!
  let vs ← loadVectors path
  IO.println s!"vectors: {vs.size} (reps {reps})"
  let vb : Array (String × Array B256 × B256) :=
    vs.map fun v => (v.op, v.args.map Nat.toB256, v.expected.toB256)
  let vw : Array (String × Array W × W) :=
    vs.map fun v => (v.op, v.args.map W.ofNat, W.ofNat v.expected)
  let (tb, fb) ← runAll b256Op vb reps
  let (tw, fw) ← runAll wOp vw reps
  IO.println s!"u256 B256   ns={tb} per_vector_ns={tb / (reps * vs.size)} oracle_failures={fb}"
  IO.println s!"u256 BitVec ns={tw} per_vector_ns={tw / (reps * vs.size)} oracle_failures={fw}"
  -- per-op split (one pass each, reps passes)
  let ops := (vs.map (·.op)).toList.eraseDups
  for op in ops do
    let sb := vb.filter (·.1 == op)
    let sw := vw.filter (·.1 == op)
    let (tb, _) ← runAll b256Op sb reps
    let (tw, _) ← runAll wOp sw reps
    IO.println s!"op {op} n={sb.size} B256_ns={tb} BitVec_ns={tw}"
  let x := hexToNat "0x8edad8b55b1586805ea8c245d8c16b06a5102b791fc6eb60693731c0677bf501"
  let y := hexToNat "0x1c68db1c179cd35ab3fc60c63704aa7fcbea40f19782b1611aaba86726a7686c"
  let k := hexToNat "0xff00ffffffffffffffffffffffffffaaffffffffffffffffbbffffffffffffff0000"
  let t0 ← IO.monoNanosNow
  let rb := loopB loopN x.toB256 y.toB256 k.toB256
  IO.println s!"loopB result {rb.1.toHex} {rb.2.1.toHex} {rb.2.2.1.toHex} {rb.2.2.2.toHex}"
  let t1 ← IO.monoNanosNow
  let rw := loopW loopN (W.ofNat x) (W.ofNat y) (W.ofNat k)
  IO.println s!"loopW result {rw.1.toHex} {rw.2.1.toHex} {rw.2.2.1.toHex} {rw.2.2.2.toHex}"
  let t2 ← IO.monoNanosNow
  let agree := rb.1.toNat == rw.1.toNat && rb.2.1.toNat == rw.2.1.toNat &&
    rb.2.2.1.toNat == rw.2.2.1.toNat && rb.2.2.2.toNat == rw.2.2.2.toNat
  IO.println s!"loopMul-kernels n={loopN} B256_ns={t1 - t0} BitVec_ns={t2 - t1} agree={agree}"
  return if fb == 0 && fw == 0 && agree then 0 else 1
