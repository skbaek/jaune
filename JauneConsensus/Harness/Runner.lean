import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Snappy
import JauneConsensus.Shuffle

/-!
# Case handlers and strict verdicts (conformance harness)

Each `(runner, handler)` pair the goal has brought up maps to a handler that reads one case
directory and returns `PASS` or a failure reason. A pair with no handler is a failure
(`UNIMPLEMENTED`), never a skip: verdicts are strict all-PASS with no expected-failure allowance.
-/

namespace JauneConsensus.Harness

open Jaune Yaml

inductive Verdict
  | pass
  | fail (why : String)
  deriving BEq, Repr

/-- `SHUFFLE_ROUND_COUNT` (`presets/minimal/phase0.yaml`: 10; `presets/mainnet/phase0.yaml`: 90).
Until the preset record exists, the harness carries the two values. -/
def shuffleRoundCount : String → Option Nat
  | "minimal" => some 10
  | "mainnet" => some 90
  | _ => none

private def readYaml (c : Case) (f : String) : IO (Except String YVal) := do
  let bytes ← IO.FS.readBinFile (c.dir / f)
  pure ((parse bytes).mapError (s!"{f}: " ++ ·))

/-- Big-endian bytes to `B256` (a `Bytes32` read from a vector). -/
def b256OfBytes (bs : List UInt8) : Except String B256 :=
  if bs.length == 32 then .ok (bs.foldl (fun (n : Nat) (b : UInt8) => 256 * n + b.toNat) 0).toB256
  else .error s!"expected 32 bytes, got {bs.length}"

/-- `shuffling/core` (`tests/formats/shuffling/README.md`): for every `i < count`,
`compute_shuffled_index(i, count, seed) == mapping[i]`, and `mapping` has exactly `count`
entries. -/
def shufflingCore (c : Case) : IO Verdict := do
  let some rounds := shuffleRoundCount c.preset
    | return .fail s!"no SHUFFLE_ROUND_COUNT for preset {c.preset}"
  if c.files != ["mapping.yaml"] then return .fail s!"unexpected files {c.files}"
  let doc ← readYaml c "mapping.yaml"
  let r : Except String Verdict := do
    let v ← doc
    v.expectKeys ["seed", "count", "mapping"]
    let seed ← b256OfBytes (← (← v.field "seed").asHex)
    let count ← (← v.field "count").asNat
    let mapping ← (← (← v.field "mapping").asSeq).mapM YVal.asNat
    if mapping.length != count then
      return .fail s!"mapping has {mapping.length} entries, count is {count}"
    let mut i := 0
    for want in mapping do
      match computeShuffledIndex rounds i count seed with
      | .ok got =>
        if got != want then return .fail s!"index {i}: computed {got}, expected {want}"
      | .error e => return .fail s!"index {i}: rejected: {repr e}"
      i := i + 1
    pure .pass
  match r with
  | .ok v => pure v
  | .error e => pure (.fail e)

/-- The handler table. -/
def handlerFor (runner handler : String) : Option (Case → IO Verdict) :=
  match runner, handler with
  | "shuffling", "core" => some shufflingCore
  | _, _ => none

def runCase (c : Case) : IO Verdict := do
  match handlerFor c.key.runner c.key.handler with
  | none => pure (.fail s!"UNIMPLEMENTED: no handler for {c.key.runner}/{c.key.handler}")
  | some h =>
    try h c catch e => pure (.fail s!"error: {e}")

/-! ## Reader scans

Corpus-wide checks of the two readers over a selection: every `.ssz_snappy` decodes (its declared
length is met and every copy is in range) and every `.yaml` is inside the accepted subset. -/

def snappyScan (cs : List Case) : IO (Nat × List String) := do
  let mut n := 0
  let mut bad := []
  for c in cs do
    for f in c.files do
      if f.endsWith ".ssz_snappy" then
        n := n + 1
        match Snappy.decompress (← IO.FS.readBinFile (c.dir / f)) with
        | .ok _ => pure ()
        | .error e => bad := s!"{c.render}/{f}: {e}" :: bad
  pure (n, bad.reverse)

def yamlScan (cs : List Case) : IO (Nat × List String) := do
  let mut n := 0
  let mut bad := []
  for c in cs do
    for f in c.files do
      if f.endsWith ".yaml" then
        n := n + 1
        match parse (← IO.FS.readBinFile (c.dir / f)) with
        | .ok _ => pure ()
        | .error e => bad := s!"{c.render}/{f}: {e}" :: bad
  pure (n, bad.reverse)

/-- An independent check of the Snappy decoder on real compressed files: for every
`ssz_generic/uints/valid` case (`uint_<bits>_...`), the decoded `serialized` must be the
`bits / 8`-byte little-endian encoding of the integer in `value.yaml` (`ssz/simple-serialize.md`,
`uintN`). Returns the number checked and the failures. -/
def snappyUintOracle (cs : List Case) : IO (Nat × List String) := do
  let mut n := 0
  let mut bad := []
  for c in cs do
    if c.key.runner != "ssz_generic" || c.key.handler != "uints" || c.key.suite != "valid" then
      continue
    let bits? := match c.name.splitOn "_" with
      | "uint" :: b :: _ => b.toNat?
      | _ => none
    match bits? with
    | none => bad := s!"{c.render}: unparsed case name" :: bad
    | some bits =>
    n := n + 1
    let dec := Snappy.decompress (← IO.FS.readBinFile (c.dir / "serialized.ssz_snappy"))
    -- integers wider than 64 bits are quoted strings in the vectors
    let val := (parse (← IO.FS.readBinFile (c.dir / "value.yaml"))).bind
      (if bits > 64 then YVal.asQuotedNat else YVal.asNat)
    match dec, val with
    | .ok out, .ok v =>
      if out.toList != uintToBytes (bits / 8) v || v ≥ 2 ^ bits then
        bad := s!"{c.render}: decoded bytes differ from value.yaml" :: bad
    | .error e, _ => bad := s!"{c.render}: {e}" :: bad
    | _, .error e => bad := s!"{c.render}: {e}" :: bad
  pure (n, bad.reverse)

end JauneConsensus.Harness
