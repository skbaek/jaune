import Lean.Data.Json
import Jaune.Hash

/-!
# Pinned vector provenance and the per-suite manifest (conformance harness)

The runner trusts an extracted vector tree only as far as it matches two committed, generated
files (both written by `scripts/consensus-vector-inventory.py` from the tarballs it has checked
against their pinned SHA-256s):

* `scripts/consensus-vectors.json`: release tag, tag commit, and per-tarball name, size and digest
  (the `general` tarball under the general-only entry `general`, an earlier release, because the
  pinned release's general tarball has no `ssz_generic` or `kzg` cases);
* `scripts/consensus/inventory-v1.7.0-beta.4.json`: per preset, fork, runner, handler and suite the case
  count, and for every in-scope suite (`suites`) the SHA-256 of its sorted case names, the
  SHA-256 of its sorted `<case>/<file>` paths, its `bls_setting` histogram and its cases carrying a
  per-case `config.yaml`.

This module loads both and states the scope rule. `Discovery` compares the tree against them.
-/

namespace JauneConsensus.Harness

open Lean (Json)
open Jaune

/-- Why the provenance pin or the inventory could not be loaded or did not cross-check. The
payloads are diagnostic text only. -/
inductive ManifestError where
  /-- A file is not valid JSON. -/
  | json (what : String)
  /-- A field is missing or has the wrong type. -/
  | field (what : String)
  /-- The pin and the inventory disagree, or the inventory is not pinned. -/
  | mismatch (what : String)
  deriving Repr

instance : ToString ManifestError where
  toString
    | .json w => s!"manifest: invalid JSON: {w}"
    | .field w => s!"manifest: {w}"
    | .mismatch w => s!"manifest: {w}"

/-- What the manifest pins for one suite. -/
structure SuiteRecord where
  cases : Nat
  namesSha256 : String
  filesSha256 : String
  /-- `bls_setting` histogram: keys `absent`, `0`, `1`, `2`, sorted, zero counts omitted. -/
  blsSetting : List (String × Nat)
  configOverrides : List String
  deriving Repr, BEq

/-- A suite key `fork/runner/handler/suite` within a preset. -/
structure SuiteKey where
  fork : String
  runner : String
  handler : String
  suite : String
  deriving Repr, BEq, Inhabited

def SuiteKey.render (k : SuiteKey) : String := s!"{k.fork}/{k.runner}/{k.handler}/{k.suite}"

def SuiteKey.parse? (s : String) : Option SuiteKey :=
  match s.splitOn "/" with
  | [f, r, h, x] => some ⟨f, r, h, x⟩
  | _ => none

/-- The loaded provenance: release identity, and per preset the in-scope suite records together
with the inventory's count for each. -/
structure Manifest where
  release : String
  tagCommit : String
  /-- `(preset, suite, record, inventory count)` -/
  suites : List (String × SuiteKey × SuiteRecord × Nat)

/-- The presets this runner reads. The inventory also records the `comptests` tarball
(`minimal`-preset `fork_choice_compliance` cases), which no runner here executes yet. -/
def presets : List String := ["general", "minimal", "mainnet"]

/-- The committed inventory file, under `<manifest-dir>/consensus/`. -/
def inventoryFile : String := "inventory-v1.7.0-beta.4.json"

/-- The default extraction of a preset's tarball under `$HOME`: the general tarball comes from the
general-only provenance entry (`v1.6.1`), the others from the pinned release. -/
def defaultVectorsDir (preset : String) : String :=
  if preset == "general" then "consensus-spec-tests-v1.6.1" else "consensus-spec-tests-v1.7.0-beta.4"

/-- The goal's scope (`scripts/consensus-vector-inventory.py`, `in_scope`): every `general` case;
every `minimal` and `mainnet` case of Electra, Fulu or Gloas; and `phase0/shuffling` on both
presets. -/
def inScope (preset fork runner : String) : Bool :=
  preset == "general" || fork == "electra" || fork == "fulu" || fork == "gloas" ||
    (fork == "phase0" && runner == "shuffling")

private def field (j : Json) (k : String) : Except ManifestError Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error (.field s!"missing field {k}")

private def str (j : Json) (k : String) : Except ManifestError String := do
  match (← field j k).getStr? with
  | .ok s => .ok s
  | .error _ => .error (.field s!"field {k} is not a string")

private def nat (j : Json) (k : String) : Except ManifestError Nat := do
  match (← field j k).getNat? with
  | .ok n => .ok n
  | .error _ => .error (.field s!"field {k} is not a natural number")

private def objEntries (j : Json) (what : String) : Except ManifestError (List (String × Json)) :=
  match j with
  | .obj o => .ok o.toArray.toList
  | _ => .error (.field s!"{what} is not an object")

private def suiteRecord (j : Json) : Except ManifestError SuiteRecord := do
  let bls ← (← objEntries (← field j "bls_setting") "bls_setting").mapM fun (k, v) =>
    match v.getNat? with
    | .ok n => .ok (k, n)
    | .error _ => .error (.field s!"bls_setting {k} is not a natural number")
  let overrides ← match (← field j "config_overrides") with
    | .arr xs => xs.toList.mapM fun x => match x.getStr? with
      | .ok s => .ok s
      | .error _ => .error (.field "config_overrides entry is not a string")
    | _ => .error (.field "config_overrides is not an array")
  pure {
    cases := ← nat j "cases"
    namesSha256 := ← str j "names_sha256"
    filesSha256 := ← str j "files_sha256"
    blsSetting := bls
    configOverrides := overrides }

/-- The inventory's count for one suite (`presets.<preset>.forks.<fork>.<runner>.<handler>.<suite>`). -/
private def inventoryCount (inv : Json) (preset : String) (k : SuiteKey) : Except ManifestError Nat := do
  let forks ← field (← field (← field inv "presets") preset) "forks"
  let path := [k.fork, k.runner, k.handler]
  let h ← path.foldlM (fun j p => field j p) forks
  match (← field h k.suite).getNat? with
  | .ok n => .ok n
  | .error _ => .error (.field s!"inventory count for {preset}/{k.render} is not a number")

/-- Load and cross-check the provenance pin and the inventory. Refuses an unpinned inventory, a
release or tag-commit disagreement, a suite record whose count differs from the inventory's
count, and an in-scope inventory suite with no record (or the reverse). -/
def Manifest.load (provenanceText inventoryText : String) : Except ManifestError Manifest := do
  let prov ← (Json.parse provenanceText).mapError ManifestError.json
  let inv ← (Json.parse inventoryText).mapError ManifestError.json
  let release ← str prov "release"
  let tagCommit ← str prov "tag_commit"
  if (← str inv "release") != release then throw (.mismatch "inventory release differs from the pin")
  if (← str inv "tag_commit") != tagCommit then
    throw (.mismatch "inventory tag commit differs from the pin")
  match (← field inv "pinned").getBool? with
  | .ok true => pure ()
  | _ => throw (.mismatch "inventory was not produced from digest-checked tarballs")
  let tarballs ← field prov "tarballs"
  let general ← field prov "general"
  let generalRelease ← str general "release"
  let generalTag ← str general "tag_commit"
  let invGeneral ← field inv "general_release"
  if (← str invGeneral "release") != generalRelease || (← str invGeneral "tag_commit") != generalTag then
    throw (.mismatch "inventory general release differs from the pin's general entry")
  let generalTarballs ← field general "tarballs"
  let mut suites := []
  for preset in presets do
    let _ ← field (if preset == "general" then generalTarballs else tarballs) preset
    let recs ← objEntries (← field (← field inv "suites") preset) s!"suites.{preset}"
    for (name, j) in recs do
      let some k := SuiteKey.parse? name | throw (.mismatch s!"bad suite key {preset}/{name}")
      if !inScope preset k.fork k.runner then
        throw (.mismatch s!"suite record outside the scope rule: {preset}/{name}")
      let r ← suiteRecord j
      let n ← inventoryCount inv preset k
      if n != r.cases then
        throw (.mismatch s!"{preset}/{name}: suite record says {r.cases} cases, inventory {n}")
      suites := (preset, k, r, n) :: suites
    -- every in-scope inventory suite has a record
    let forks ← objEntries (← field (← field (← field inv "presets") preset) "forks") "forks"
    for (fork, rs) in forks do
      for (runner, hs) in ← objEntries rs "runners" do
        if inScope preset fork runner then
          for (handler, ss) in ← objEntries hs "handlers" do
            for (suite, _) in ← objEntries ss "suites" do
              let k : SuiteKey := ⟨fork, runner, handler, suite⟩
              if !suites.any (fun (p, k', _) => p == preset && k' == k) then
                throw (.mismatch s!"in-scope inventory suite {preset}/{k.render} has no record")
  pure { release, tagCommit, suites := suites.reverse }

/-! ## The digests the manifest pins -/

/-- SHA-256 (Jaune's `Bytes.sha256`) as lowercase hex. -/
def sha256Hex (s : String) : String := (Bytes.sha256 s.toUTF8.toList).toHex

/-- The digest of a sorted name list, framed as the inventory script frames it: each name
followed by `\n`. -/
def listDigest (names : List String) : String :=
  sha256Hex (String.join (names.map (· ++ "\n")))

#guard sha256Hex "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

end JauneConsensus.Harness
