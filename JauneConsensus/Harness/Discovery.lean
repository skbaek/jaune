import JauneConsensus.Harness.Manifest
import JauneConsensus.Harness.Yaml
import JauneConsensus.Fork

/-!
# Case discovery and the tree-manifest check (conformance harness)

Layout (`tests/formats/README.md` at the pin):
`<root>/<preset>/tests/<preset>/<fork>/<runner>/<handler>/<suite>/<case>/<file>`, and for the
`comptests` tarball `<root>/comptests/tests/minimal/...` (`casePresetOf`).

A selection names a preset and optionally a fork, runner, handler and suite. Discovery

1. refuses Gloas (through the single resolver `CFork.rules?`) for every runner but
   `ssz_static`, and the `eip7805` feature fork, by name (`forkRefusal?`), and any selection
   naming no in-scope suite. Gloas `ssz_static` only decodes, re-encodes and hashes the Gloas
   containers; no Gloas rule runs, and `--fork-rules gloas` still refuses;
2. walks the in-scope part of the tree under the selection and compares it to the manifest: a
   selected suite missing on disk, or present on disk without a record, is refused;
3. for every selected suite checks the case count (manifest and inventory), the digest of the
   sorted case names, the digest of the sorted `<case>/<file>` paths, the `bls_setting`
   histogram read from each case's `meta.yaml`, and the set of cases with a per-case
   `config.yaml`; any difference is refused;
4. classifies every file name against the runner's known file kinds (for example Fulu
   fork-choice data columns `column_0x<root>.ssz_snappy`) and refuses an unknown name or a
   subdirectory inside a case;
5. checks every case's `manifest.yaml` (`tests/formats/README.md` at `v1.7.0-beta.4`, "included
   in every test case"): its `preset`, `fork`, `runner`, `handler`, `suite` and `case` must equal
   the case's location. Its presence is pinned by the file-path digest; once checked it is left
   out of the case's file list, so handlers see the files of their format;
6. refuses an empty selection.

The checks run on every selected suite in every tier: the smoke tier narrows which cases are
*executed*, never what is checked.
-/

namespace JauneConsensus.Harness

open Yaml

/-! ## File kinds -/

private def isHex64 (s : String) : Bool :=
  s.length == 66 && s.startsWith "0x" &&
    (s.toList.drop 2).all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f'))

private def isDecimal (s : String) : Bool :=
  !s.isEmpty && s.toList.all Char.isDigit && (s.length == 1 || !s.startsWith "0")

/-- Normalize a file name: each `_`-separated segment that is a decimal becomes `N` and each
`0x` + 64-hex-digit root becomes `0xH`. `block_0x9dcc...ssz_snappy` becomes
`block_0xH.ssz_snappy`. -/
def normalizeName (name : String) : String :=
  let (stem, ext) :=
    if name.endsWith ".ssz_snappy" then ((name.dropEnd 11).toString, ".ssz_snappy")
    else if name.endsWith ".yaml" then ((name.dropEnd 5).toString, ".yaml")
    else (name, "")
  let segs := (stem.splitOn "_").map fun s =>
    if isDecimal s then "N" else if isHex64 s then "0xH" else s
  "_".intercalate segs ++ ext

/-- The file kinds each runner's cases may contain, from `tests/formats/<runner>/` at the pin and
the pinned tarballs' in-scope file names. -/
def runnerFileKinds : String → List String
  | "bls" => ["data.yaml"]
  | "kzg" => ["data.yaml"]
  | "shuffling" => ["mapping.yaml"]
  | "ssz_generic" => ["meta.yaml", "serialized.ssz_snappy", "value.yaml"]
  | "ssz_static" => ["roots.yaml", "serialized.ssz_snappy", "value.yaml"]
  | "epoch_processing" =>
    ["meta.yaml", "pre.ssz_snappy", "post.ssz_snappy", "pre_epoch.ssz_snappy",
     "post_epoch.ssz_snappy",
     -- the Gloas `ptc_window` case (`spec_state_test_with_matching_config`)
     "config.yaml"]
  | "operations" =>
    ["meta.yaml", "pre.ssz_snappy", "post.ssz_snappy", "execution.yaml",
     "address_change.ssz_snappy", "attestation.ssz_snappy", "attester_slashing.ssz_snappy",
     "block.ssz_snappy", "body.ssz_snappy", "consolidation_request.ssz_snappy",
     "deposit.ssz_snappy", "deposit_request.ssz_snappy", "execution_payload.ssz_snappy",
     "proposer_slashing.ssz_snappy", "sync_aggregate.ssz_snappy", "voluntary_exit.ssz_snappy",
     "withdrawal_request.ssz_snappy",
     -- Gloas (`tests/formats/operations/README.md` at `v1.7.0-beta.4`); the
     -- `payload_attestation` cases ship a `config.yaml` (`GLOAS_FORK_EPOCH: 0`)
     "builder_deposit_request.ssz_snappy", "builder_exit_request.ssz_snappy",
     "execution_payload_bid.ssz_snappy", "payload_attestation.ssz_snappy", "config.yaml"]
  | "rewards" =>
    ["pre.ssz_snappy", "source_deltas.ssz_snappy", "target_deltas.ssz_snappy",
     "head_deltas.ssz_snappy", "inactivity_penalty_deltas.ssz_snappy"]
  | "sanity" => ["meta.yaml", "pre.ssz_snappy", "post.ssz_snappy", "slots.yaml",
     "blocks_N.ssz_snappy"]
  | "finality" | "random" | "transition" =>
    ["meta.yaml", "pre.ssz_snappy", "post.ssz_snappy", "blocks_N.ssz_snappy"]
  | "fork" => ["meta.yaml", "pre.ssz_snappy", "post.ssz_snappy"]
  | "fork_choice" =>
    ["meta.yaml", "steps.yaml", "anchor_state.ssz_snappy", "anchor_block.ssz_snappy",
     "block_0xH.ssz_snappy", "attestation_0xH.ssz_snappy", "attester_slashing_0xH.ssz_snappy",
     "blobs_0xH.ssz_snappy",
     -- Fulu data-column sidecars (`tests/formats/fork_choice/README.md`, `columns`)
     "column_0xH.ssz_snappy"]
  | "sync" => ["meta.yaml", "steps.yaml", "anchor_state.ssz_snappy", "anchor_block.ssz_snappy",
     "block_0xH.ssz_snappy"]
  | "fast_confirmation" | "fork_choice_compliance" =>
    ["meta.yaml", "steps.yaml", "anchor_state.ssz_snappy", "anchor_block.ssz_snappy",
     "block_0xH.ssz_snappy", "attestation_0xH.ssz_snappy", "attester_slashing_0xH.ssz_snappy"]
  | "light_client" =>
    ["meta.yaml", "config.yaml", "steps.yaml", "proof.yaml", "object.ssz_snappy",
     "bootstrap.ssz_snappy", "initial_state.ssz_snappy", "updates_N.ssz_snappy",
     "block_N_0xH.ssz_snappy", "bootstrap_N_0xH.ssz_snappy", "update_N_0xH.ssz_snappy",
     "finality_update_N_0xH.ssz_snappy", "optimistic_update_N_0xH.ssz_snappy",
     "update_0xH_sf.ssz_snappy", "update_0xH_sx.ssz_snappy", "update_0xH_xf.ssz_snappy",
     "update_0xH_xx.ssz_snappy"]
  | "merkle_proof" => ["object.ssz_snappy", "proof.yaml"]
  | "networking" =>
    ["meta.yaml",
     -- `gossip_*` (`tests/formats/networking/gossip_validation.md`; the message prefixes are
     -- read from the `v1.7.0-beta.4` vectors, `Harness/GossipTable.lean`)
     "state.ssz_snappy", "config.yaml", "block_0xH.ssz_snappy",
     "proposer_slashing_0xH.ssz_snappy", "attester_slashing_0xH.ssz_snappy",
     "voluntary_exit_0xH.ssz_snappy", "bls_to_execution_change_0xH.ssz_snappy",
     "sync_committee_message_0xH.ssz_snappy", "contribution_0xH.ssz_snappy",
     "single_attestation_0xH.ssz_snappy", "aggregate_0xH.ssz_snappy",
     "blob_sidecar_0xH.ssz_snappy", "data_column_sidecar_0xH.ssz_snappy",
     "partial_data_column_group_id_0xH.ssz_snappy", "partial_data_column_header_0xH.ssz_snappy",
     "partial_data_column_sidecar_0xH.ssz_snappy", "execution_payload_bid_0xH.ssz_snappy",
     "execution_payload_envelope_0xH.ssz_snappy", "payload_attestation_message_0xH.ssz_snappy",
     "proposer_preferences_0xH.ssz_snappy"]
  | _ => []

/-! ## Refused forks -/

/-- The runners whose cases need no fork rules: they only decode, re-encode and hash containers,
so a fork whose rules do not resolve (Gloas) is accepted for them. -/
def containerOnlyRunners : List String := ["ssz_static"]

/-- The runners admitted at Gloas: the container-only runners, and the runners whose Gloas
semantics exist (goal `eip8282-gloas-cross-layer-v1`, U3: `epoch_processing` over
`JauneConsensus/GloasEpoch.lean`, `rewards` over `GloasEpochAccessors.lean`; U4: `operations` over
`GloasWithdrawals.lean`, `GloasOperations.lean` and `GloasBlock.lean`; U7a: `networking`, whose
custody helpers are fork-independent and whose `gossip_*` handlers dispatch by fork in
`Harness/GossipTable.lean`). Every other runner still refuses Gloas. -/
def gloasRunners : List String :=
  containerOnlyRunners ++ ["epoch_processing", "rewards", "operations", "networking"]

/-- Why a fork directory is refused by name for a runner (`none`: any runner), if it is. Gloas is
a declared `CFork` whose rules do not resolve (`CFork.resolve` gives `notImplemented`); it is
accepted only for a runner of `gloasRunners`. `eip7805` is a feature-fork
directory of the `v1.6.1` vectors with no `CFork` value (`unknown`). Both fail closed otherwise;
neither is ever run as Fulu. Other directory names that are not `CFork`s (`phase0`, `altair`,
... where formats were introduced) are not refused here: the scope rule decides them. -/
def forkRefusal? (f : String) (runner : Option String := none) : Option ForkRefusal :=
  if f == "eip7805" then some (.unknown f)
  else match CFork.ofName? f with
    | some c => match CFork.resolve f with
      | .error e =>
        if c == .gloas && runner.any gloasRunners.contains then none else some e
      | .ok _ => none
    | none => none

#guard (forkRefusal? "gloas").isSome
#guard (forkRefusal? "gloas" (some "operations")).isNone
#guard (forkRefusal? "gloas" (some "ssz_static")).isNone
#guard (forkRefusal? "gloas" (some "epoch_processing")).isNone
#guard (forkRefusal? "gloas" (some "rewards")).isNone
#guard (forkRefusal? "gloas" (some "sanity")).isSome
#guard (forkRefusal? "gloas" (some "networking")).isNone
#guard (forkRefusal? "eip7805" (some "ssz_static")).isSome
#guard (forkRefusal? "fulu").isNone
#guard (forkRefusal? "electra").isNone
#guard (forkRefusal? "phase0").isNone

/-! ## Selection -/

inductive Tier | smoke | full
  deriving BEq, Repr

/-- A directory name used as a selection filter (a fork, runner, handler or suite name). -/
abbrev DirName := String

structure Selection where
  root : System.FilePath
  preset : String
  fork : Option DirName := none
  runner : Option DirName := none
  handler : Option DirName := none
  suite : Option DirName := none
  tier : Tier := .full

/-- One discovered case: its suite and directory, with its sorted file names. -/
structure Case where
  preset : String
  key : SuiteKey
  name : String
  dir : System.FilePath
  files : List String

def Case.render (c : Case) : String := s!"{c.preset}/{c.key.render}/{c.name}"

def Case.has (c : Case) (f : String) : Bool := c.files.contains f

private def matches? (filter : Option DirName) (v : String) : Bool :=
  match filter with
  | none => true
  | some f => f == v

private def sortStrings (xs : Array String) : List String := (xs.qsort (· < ·)).toList

/-- Sorted names of the subdirectories (`dirs = true`) or regular files of `p`; refuses the
other kind when `strict`. -/
def listDir (p : System.FilePath) (dirs : Bool) (strict : Bool) : IO (List String) := do
  let es ← p.readDir
  let mut out := #[]
  for e in es do
    let isDir ← e.path.isDir
    if isDir == dirs then out := out.push e.fileName
    else if strict then
      throw (IO.userError s!"discovery: unexpected {if isDir then "directory" else "file"} {e.path}")
  pure (sortStrings out)

/-- `manifest.yaml`: exactly the six identity keys, each a scalar equal to the case's location. -/
def checkCaseManifest (dir : System.FilePath) (label : String) (want : List (String × String)) :
    IO Unit := do
  match parse (← IO.FS.readBinFile (dir / "manifest.yaml")) with
  | .error e => throw (IO.userError s!"refused: {label}/manifest.yaml: {e}")
  | .ok v =>
    match v.expectKeys (want.map (·.1)) with
    | .error e => throw (IO.userError s!"refused: {label}/manifest.yaml: {e}")
    | .ok () => pure ()
    for (k, w) in want do
      match v.get? k with
      | some (.scalar s _) =>
        if s != w then
          throw (IO.userError s!"refused: {label}/manifest.yaml: {k} is {s}, the case is at {w}")
      | _ => throw (IO.userError s!"refused: {label}/manifest.yaml: {k} is not a scalar")

/-- The `bls_setting` of one case, as the manifest's histogram key. -/
def blsSettingOf (c : Case) : IO String := do
  if !c.has "meta.yaml" then return "absent"
  let bytes ← IO.FS.readBinFile (c.dir / "meta.yaml")
  match parse bytes with
  | .error e => throw (IO.userError s!"{c.render}/meta.yaml: {e}")
  | .ok v =>
    match v.get? "bls_setting" with
    | none => return "absent"
    | some x =>
      match x.asNat with
      | .ok n =>
        if n ≤ 2 then return toString n
        else throw (IO.userError s!"{c.render}: bls_setting {n} outside 0, 1, 2")
      | .error e => throw (IO.userError s!"{c.render}: bls_setting: {e}")

private def histogram (xs : List String) : List (String × Nat) :=
  let keys := sortStrings (xs.eraseDups.toArray)
  keys.map fun k => (k, xs.count k)

/-- Discover the selection, check it against the manifest, and return every selected case (all
tiers), sorted by suite and case name. Throws on any refusal. -/
def discover (m : Manifest) (sel : Selection) : IO (List Case) := do
  if !presets.contains sel.preset then
    throw (IO.userError s!"refused: unknown preset {sel.preset}")
  if let some f := sel.fork then
    if let some why := forkRefusal? f sel.runner then throw (IO.userError (toString why))
  -- in-scope suites of the manifest under the selection
  let wanted := m.suites.filter fun (p, k, _, _) =>
    p == sel.preset && matches? sel.fork k.fork && matches? sel.runner k.runner &&
      matches? sel.handler k.handler && matches? sel.suite k.suite
  if wanted.isEmpty then
    throw (IO.userError "refused: the selection names no in-scope suite of the pinned inventory")
  -- the in-scope part of the tree under the selection
  let base := sel.root / sel.preset / "tests" / casePresetOf sel.preset
  let mut onDisk : List SuiteKey := []
  for fork in ← listDir base true true do
    if !matches? sel.fork fork then continue
    for runner in ← listDir (base / fork) true true do
      if !matches? sel.runner runner || !inScope sel.preset fork runner then continue
      if let some why := forkRefusal? fork (some runner) then throw (IO.userError (toString why))
      for handler in ← listDir (base / fork / runner) true true do
        if !matches? sel.handler handler then continue
        for suite in ← listDir (base / fork / runner / handler) true true do
          if !matches? sel.suite suite then continue
          onDisk := ⟨fork, runner, handler, suite⟩ :: onDisk
  for (_, k, _, _) in wanted do
    if !onDisk.contains k then
      throw (IO.userError s!"refused: suite {sel.preset}/{k.render} is missing from the tree")
  for k in onDisk do
    if !wanted.any (fun (_, k', _, _) => k' == k) then
      throw (IO.userError s!"refused: suite {sel.preset}/{k.render} on disk has no manifest record")
  -- per-suite checks
  let mut cases : Array Case := #[]
  for (_, k, r, invCount) in wanted do
    let sdir := base / k.fork / k.runner / k.handler / k.suite
    let names ← listDir sdir true true
    let label := s!"{sel.preset}/{k.render}"
    if names.length != r.cases || names.length != invCount then
      throw (IO.userError s!"refused: {label}: {names.length} cases on disk, manifest {r.cases}, inventory {invCount}")
    if listDigest names != r.namesSha256 then
      throw (IO.userError s!"refused: {label}: case names differ from the manifest (missing, extra or renamed case)")
    let kinds := runnerFileKinds k.runner
    let mut paths : Array String := #[]
    let mut suiteCases : Array Case := #[]
    for n in names do
      let files ← listDir (sdir / n) false true
      for f in files do
        if f != "manifest.yaml" && !kinds.contains (normalizeName f) then
          throw (IO.userError s!"refused: {label}/{n}: unknown file {f} for runner {k.runner}")
        paths := paths.push s!"{n}/{f}"
      if files.contains "manifest.yaml" then
        checkCaseManifest (sdir / n) s!"{label}/{n}" [("preset", casePresetOf sel.preset),
          ("fork", k.fork), ("runner", k.runner), ("handler", k.handler), ("suite", k.suite),
          ("case", n)]
      let files := files.filter (· != "manifest.yaml")
      suiteCases := suiteCases.push
        { preset := casePresetOf sel.preset, key := k, name := n, dir := sdir / n, files }
    if listDigest (sortStrings paths) != r.filesSha256 then
      throw (IO.userError s!"refused: {label}: file paths differ from the manifest (missing, extra or renamed file)")
    let bls ← suiteCases.toList.mapM blsSettingOf
    if histogram bls != r.blsSetting then
      throw (IO.userError s!"refused: {label}: bls_setting histogram {histogram bls} differs from the manifest {r.blsSetting}")
    let overrides := (suiteCases.filter (·.has "config.yaml")).toList.map (·.name)
    if overrides != r.configOverrides then
      throw (IO.userError s!"refused: {label}: per-case config.yaml set {overrides} differs from the manifest {r.configOverrides}")
    cases := cases ++ suiteCases
  if cases.isEmpty then throw (IO.userError "refused: empty selection")
  pure cases.toList

/-- The cases a tier executes: every case (`full`), or the first case of each suite in sorted
order (`smoke`). -/
def tierCases (t : Tier) (cs : List Case) : List Case :=
  match t with
  | .full => cs
  | .smoke =>
    let rec go : List Case → Option SuiteKey → List Case
      | [], _ => []
      | c :: rest, last => if some c.key == last then go rest last else c :: go rest (some c.key)
    go cs none

#guard normalizeName "block_0x9dcca58cccdffa1d6b8fd711c7cd3a66e0e736ebbb0790eb05976b825ce9ca68.ssz_snappy"
  == "block_0xH.ssz_snappy"
#guard normalizeName "blocks_12.ssz_snappy" == "blocks_N.ssz_snappy"
#guard normalizeName "update_0x9dcca58cccdffa1d6b8fd711c7cd3a66e0e736ebbb0790eb05976b825ce9ca68_sf.ssz_snappy"
  == "update_0xH_sf.ssz_snappy"
#guard normalizeName "block_0x9d.ssz_snappy" == "block_0x9d.ssz_snappy"

end JauneConsensus.Harness
