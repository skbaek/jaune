import Lean.Data.Json
import JauneConsensus.Harness.SszGeneric

/-!
# `jaune-consensus-ssz-generic`: the `ssz_generic` runner (minimal path)

Runs the selected `ssz_generic` handlers of the extracted `general` vector tree, strict
all-PASS, and refuses an empty selection or any per-suite case count that differs from the
O0 inventory (`scripts/consensus/inventory-v1.6.1.json`). Every case runs; none is skipped.

Usage:
  jaune-consensus-ssz-generic --tests DIR --inventory FILE HANDLER...
where `DIR` is `.../tests/general` of the extracted `general` tarball and each `HANDLER` is an
`ssz_generic` handler directory name (`uints`, `boolean`, `bitvector`, `bitlist`,
`basic_vector`). Exit 0 iff every case passes and every count matches.

Tree provenance (per-file digests against the pinned tarball) is the harness runner's job
(goal outcome O6); this minimal path checks counts only.
-/

open JauneConsensus JauneConsensus.Harness Jaune

/-- Read a file as text, or a typed failure. -/
def readText (p : System.FilePath) : IO (Except CaseFail String) := do
  try pure (.ok (← IO.FS.readFile p)) catch e => pure (.error (.io (toString e)))

def readBin (p : System.FilePath) : IO (Except CaseFail ByteArray) := do
  try pure (.ok (← IO.FS.readBinFile p)) catch e => pure (.error (.io (toString e)))

def liftYaml {α : Type} : Except YamlError α → Except CaseFail α
  | .ok a => .ok a
  | .error e => .error (.yaml e)

/-- The expected root from `meta.yaml`. -/
def readRoot (text : String) : Except CaseFail B256 := do
  let y ← liftYaml (Yaml.parse text)
  let r ← liftYaml (y.field? "root" >>= Yaml.text?)
  let bs ← liftYaml (parseHex r)
  if bs.length = 32 then pure (Bytes.toB256 bs) else throw (.yaml (.shape "32-byte root"))

/-- Run one case directory. -/
def runCase (handler suite : String) (dir : System.FilePath) (name : String) :
    IO (Except CaseFail Unit) := do
  match typeOfCase handler name with
  | none => pure (.error (.unknownType name))
  | some checks =>
    let raw ← readBin (dir / "serialized.ssz_snappy")
    match raw with
    | .error e => pure (.error e)
    | .ok raw =>
    match decompress raw with
    | .error e => pure (.error (.snappy e))
    | .ok ser =>
      let ser := ser.toList
      if suite = "invalid" then pure (checks.invalid ser)
      else
        let valueText ← readText (dir / "value.yaml")
        let metaText ← readText (dir / "meta.yaml")
        pure do
          let value ← liftYaml (Yaml.parse (← valueText))
          let root ← readRoot (← metaText)
          checks.valid ser value root

/-- Sorted subdirectory names. -/
def subdirs (p : System.FilePath) : IO (Array String) := do
  let es ← p.readDir
  let mut out := #[]
  for e in es do
    if (← e.path.isDir) then out := out.push e.fileName
  pure (out.qsort (· < ·))

/-- The inventory's recorded count for `general/phase0/ssz_generic/HANDLER/SUITE`. -/
def recordedCount (inv : Lean.Json) (handler suite : String) : Option Nat :=
  match inv.getObjValD "presets" |>.getObjValD "general" |>.getObjValD "forks"
      |>.getObjValD "phase0" |>.getObjValD "ssz_generic" |>.getObjValD handler
      |>.getObjValD suite |>.getNat? with
  | .ok n => some n
  | .error _ => none

def main (args : List String) : IO UInt32 := do
  let rec parseArgs : List String → Option System.FilePath → Option System.FilePath →
      List String → Option (System.FilePath × System.FilePath × List String)
    | "--tests" :: d :: rest, _, i, hs => parseArgs rest (some d) i hs
    | "--inventory" :: f :: rest, t, _, hs => parseArgs rest t (some f) hs
    | h :: rest, t, i, hs => parseArgs rest t i (hs ++ [h])
    | [], some t, some i, hs => some (t, i, hs)
    | [], _, _, _ => none
  let some (tests, invPath, handlers) := parseArgs args none none []
    | IO.eprintln "usage: jaune-consensus-ssz-generic --tests DIR --inventory FILE HANDLER..."
      return 2
  if handlers.isEmpty then
    IO.eprintln "REFUSED — empty selection: name at least one ssz_generic handler"
    return 2
  let invText ← IO.FS.readFile invPath
  let inv ← match Lean.Json.parse invText with
    | .ok j => pure j
    | .error e => IO.eprintln s!"REFUSED — inventory unreadable: {e}"; return 2
  let base : System.FilePath := tests / "phase0" / "ssz_generic"
  let mut total := 0
  let mut failed := 0
  let mut refused := false
  for handler in handlers do
    for suite in ["invalid", "valid"] do
      let dir := base / handler / suite
      let cases ← if (← dir.isDir) then subdirs dir else pure #[]
      let some expected := recordedCount inv handler suite
        | IO.eprintln s!"REFUSED — {handler}/{suite}: not in the inventory"
          refused := true
          continue
      if cases.size ≠ expected then
        IO.eprintln s!"REFUSED — count mismatch {handler}/{suite}: found {cases.size} recorded {expected}"
        refused := true
        continue
      let t0 ← IO.monoMsNow
      let mut pass := 0
      for c in cases do
        match ← runCase handler suite (dir / c) c with
        | .ok () => pass := pass + 1
        | .error e =>
          failed := failed + 1
          IO.println s!"FAIL {handler}/{suite}/{c}: {repr e}"
      let t1 ← IO.monoMsNow
      total := total + cases.size
      IO.println s!"{handler}/{suite}: {pass}/{cases.size} PASS ({t1 - t0} ms)"
  if refused then
    IO.println "REFUSED — ssz_generic: selection does not match the inventory"
    return 1
  if total = 0 then
    IO.println "REFUSED — ssz_generic: empty selection"
    return 1
  if failed = 0 then
    IO.println s!"OK — ssz_generic: {total}/{total} cases PASS"
    return 0
  else
    IO.println s!"FAIL — ssz_generic: {failed} of {total} cases failed"
    return 1
