import JauneConsensus.LightClient
import JauneConsensus.GloasLightClientFullNode
import JauneConsensus.Harness.LightClientDataCollection
import JauneConsensus.Harness.GloasLightClientDataCollection
import JauneConsensus.SSZ.Proof
import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Snappy
import JauneConsensus.Harness.Yaml

/-!
# `light_client` and `merkle_proof` case checks (harness only)

`tests/formats/light_client/` and `tests/formats/merkle_proof/` (`consensus-specs` `v1.7.0-beta.4`):

* `single_merkle_proof/<Type>`: `is_valid_merkle_branch(leaf, branch, floorlog2(leaf_index),
  get_subtree_index(leaf_index), hash_tree_root(object))` must hold, and the optional check:
  `compute_merkle_proof(object, leaf_index)` (`LightClientFullNode.lean`) equals `branch`.
* `sync`: initialize a `LightClientStore` from `bootstrap` and run the steps, checking the
  finalized and optimistic headers after each. Every fork digest must be one of the case fork's
  (`forkDigestsOf`: from Fulu the digest changes at each `BLOB_SCHEDULE` epoch while the types do
  not), or a Gloas digest (`Gloas.forkDigests`), which selects the Gloas types. From
  `v1.7.0-beta.4` the store is named by `store_fork_version`, the version of the fork whose
  light-client types it holds: Fulu adds none, so an Electra or Fulu store carries
  `ELECTRA_FORK_VERSION`; a Gloas store (`GloasLightClient.lean`) carries `GLOAS_FORK_VERSION`
  and takes Electra-format data through `upgrade_lc_*_to_gloas` (`GloasLightClientFullNode.lean`);
  any other version is refused.
* Gloas (`gloasLightClientCase`): `single_merkle_proof` over the Gloas progressive proof trees,
  `sync` with a Gloas store, `update_ranking` over the Gloas updates, `data_collection` over the
  Gloas state transition (`Harness/GloasLightClientDataCollection.lean`).
* `update_ranking`: the `updates_<i>` are in descending precedence: no later update ranks
  better (`is_better_update`) than an earlier one.
-/

namespace JauneConsensus.Harness
open Jaune (Bytes U256)
open Yaml

private def readSsz (c : Case) (file : String) : IO (Except String Bytes) := do
  match Snappy.decompress (← IO.FS.readBinFile (c.directory / file)) with
  | .ok b => pure (.ok b.toList)
  | .error e => pure (.error s!"{file}: snappy: {e}")

private def readYamlFile (c : Case) (file : String) : IO (Except String YamlValue) := do
  pure ((parse (← IO.FS.readBinFile (c.directory / file))).mapError (s!"{file}: " ++ toString ·))

private def decodeAs {α : Type} [Ssz α] (bytes : Bytes) (what : String) : Except String α :=
  match (deserialize bytes : Fallible α) with
  | .ok v => .ok v
  | .error r => .error s!"{what}: decode rejected: {repr r}"

private def liftFallible {α : Type} (x : Fallible α) (what : String) : Except String α :=
  match x with
  | .ok v => .ok v
  | .error r => .error s!"{what}: rejected: {repr r}"

private def yamlResult {α : Type} (x : Result α) : Except String α := x.mapError toString

private def root32 (v : YamlValue) : Except String Jaune.U256 := do
  let bs ← yamlResult v.asHex
  if bs.length = 32 then pure (Jaune.Bytes.toU256 bs) else throw "expected 32 bytes"

/-- `is_valid_merkle_branch(leaf, branch, floorlog2(gindex), get_subtree_index(gindex), root)`. -/
def verifyGindexBranch (leaf : Jaune.U256) (branch : List Jaune.U256) (gindex : Nat) (root : Jaune.U256) : Fallible Bool := do
  isValidMerkleBranch leaf branch (← u64Checked (floorlog2 gindex)) (← getSubtreeIndex gindex) root

/-- `single_merkle_proof/<Type>` for an object of type `α` with proof tree `tree`. -/
@[nospecialize] def singleMerkleProof {α : Type} [Ssz α] (tree : α → ProofTree) (c : Case) :
    IO (Except String Unit) := do
  if c.files != ["object.ssz_snappy", "proof.yaml"] then return .error s!"unexpected files {c.files}"
  let obj ← readSsz c "object.ssz_snappy"
  let doc ← readYamlFile c "proof.yaml"
  pure do
    let o : α ← decodeAs (← obj) "object"
    let v ← doc
    yamlResult (v.expectKeys ["leaf", "leaf_index", "branch"])
    let leaf ← root32 (← yamlResult (v.field "leaf"))
    let index ← yamlResult ((v.field "leaf_index").bind YamlValue.asNat)
    let branch ← (← yamlResult ((v.field "branch").bind YamlValue.asSequence)).mapM root32
    let depth := floorlog2 index
    require' (branch.length == depth) "branch length differs from floorlog2(leaf_index)"
    let ok ← liftFallible (verifyGindexBranch leaf branch index (hashTreeRoot o)) "is_valid_merkle_branch"
    require' ok "is_valid_merkle_branch failed against hash_tree_root(object)"
    let regenerated ← liftFallible (computeMerkleProof (tree o) index) "compute_merkle_proof"
    require' (regenerated == branch) "compute_merkle_proof(object, leaf_index) differs from branch"
where require' (b : Bool) (msg : String) : Except String Unit := if b then pure () else throw msg

/-- Check a header against `{slot, beacon_root, execution_root}`, the execution root computed by
`getRoot` (the store fork's `get_lc_execution_root`). -/
private def checkHeader {H : Type} (beacon : H → BeaconBlockHeader) (getRoot : H → Fallible Root) (h : H)
    (v : YamlValue) (what : String) : Except String Unit := do
  yamlResult (v.expectKeys ["slot", "beacon_root", "execution_root"])
  let slot ← yamlResult ((v.field "slot").bind YamlValue.asNat)
  let br ← root32 (← yamlResult (v.field "beacon_root"))
  let er ← root32 (← yamlResult (v.field "execution_root"))
  if (beacon h).slot.toNat != slot then throw s!"{what}.slot {(beacon h).slot.toNat} != {slot}"
  if !(hashTreeRoot (beacon h) == br) then throw s!"{what}.beacon_root differs"
  let got ← liftFallible (getRoot h) "get_lc_execution_root"
  if !(got == er) then throw s!"{what}.execution_root differs"

/-- A sync case's store: an Electra-format store (Electra and Fulu add no light-client types), or
a Gloas store (`specs/gloas/light-client/`). -/
inductive SyncStore (P : Preset) (f : ConsensusFork) where
  | legacy (s : LightClientStore P f)
  | gloas (s : Gloas.LightClientStore P)

private def runChecks {P : Preset} {f : ConsensusFork} (cfg : Config) (s : SyncStore P f)
    (checks : YamlValue) : Except String Unit := do
  yamlResult (checks.expectKeys ["finalized_header", "optimistic_header"])
  let fin ← yamlResult (checks.field "finalized_header")
  let opt ← yamlResult (checks.field "optimistic_header")
  match s with
  | .legacy s =>
    let chk := checkHeader (·.beacon) (getLcExecutionRoot cfg)
    chk s.finalized_header fin "finalized_header"
    chk s.optimistic_header opt "optimistic_header"
  | .gloas s =>
    let chk := checkHeader (·.beacon) (Gloas.getLcExecutionRoot cfg P)
    chk s.finalized_header fin "finalized_header"
    chk s.optimistic_header opt "optimistic_header"

/-- `light_client/sync`. The store is named by `store_fork_version`: `ELECTRA_FORK_VERSION` (an
Electra or Fulu case only) or `GLOAS_FORK_VERSION`. Each object's type is fixed by its fork
digest: a digest of the case fork (`forkDigestsOf`; none at Gloas) is an Electra-format object, a
Gloas digest (`Gloas.forkDigests`) a Gloas one; any other digest, or one in both sets, is refused.
A Gloas store takes Electra-format data through `upgrade_lc_*_to_gloas`
(`specs/gloas/light-client/fork.md`), as the generator's `upgrade_lc_*_to_new_spec` does; an
Electra-format store refuses Gloas data. `upgrade_store` to `GLOAS_FORK_VERSION` runs
`upgrade_lc_store_to_gloas`; to the store's own version it is the identity; anything else is
refused. -/
def lightClientSync (P : Preset) (f : ConsensusFork) (cfg : Config) (c : Case) : IO (Except String Unit) := do
  let metaDoc ← readYamlFile c "meta.yaml"
  let stepsDoc ← readYamlFile c "steps.yaml"
  let bootstrapBytes ← readSsz c "bootstrap.ssz_snappy"
  -- read every update file named by a step
  let steps ← match stepsDoc.bind fun v => yamlResult v.asSequence with
    | .ok s => pure s
    | .error e => return .error e
  let mut updates : List (String × Except String Bytes) := []
  for st in steps do
    match st.get? "process_update" with
    | some pu =>
      match (pu.field "update") with
      | .ok (.scalar name _) => updates := (name, ← readSsz c (name ++ ".ssz_snappy")) :: updates
      | _ => pure ()
    | none => pure ()
  let ctx : Ctx := { config := cfg }
  pure do
    let m ← metaDoc
    yamlResult (m.expectKeys ["genesis_validators_root", "trusted_block_root", "bootstrap_fork_digest",
      "store_fork_version"])
    let gvr ← root32 (← yamlResult (m.field "genesis_validators_root"))
    let trusted ← root32 (← yamlResult (m.field "trusted_block_root"))
    let legacyDigests ← if f == .gloas then pure [] else
      liftFallible (forkDigestsOf cfg f gvr) "compute_fork_digest"
    let gloasDigests ← liftFallible (Gloas.forkDigests cfg gvr) "compute_fork_digest (Gloas)"
    -- `true`: a Gloas object
    let classify (v : Result YamlValue) (what : String) : Except String Bool := do
      let d ← yamlResult (v.bind YamlValue.asHex)
      match legacyDigests.contains d, gloasDigests.contains d with
      | true, false => pure false
      | false, true => pure true
      | true, true => throw s!"refused: {what} {d} is both a {f} and a Gloas fork digest"
      | false, false => throw s!"refused: {what} {d} is neither a {f} nor a Gloas fork digest"
    -- `true`: a Gloas store
    let storeVersion (v : Result YamlValue) : Except String Bool := do
      let d ← yamlResult (v.bind YamlValue.asHex)
      if d == cfg.GLOAS_FORK_VERSION then pure true
      else if d == cfg.ELECTRA_FORK_VERSION && f != .gloas then pure false
      else throw s!"refused: store_fork_version {d} is neither ELECTRA_FORK_VERSION (an Electra or Fulu store) nor GLOAS_FORK_VERSION"
    let gloasStore ← storeVersion (m.field "store_fork_version")
    let gloasBootstrap ← classify (m.field "bootstrap_fork_digest") "bootstrap_fork_digest"
    let bootstrapBytes ← bootstrapBytes
    let mut store : SyncStore P f ← match gloasStore, gloasBootstrap with
      | false, false => do
        let b : LightClientBootstrap P f ← decodeAs bootstrapBytes "bootstrap"
        pure (.legacy (← liftFallible (initializeLightClientStore cfg trusted b) "initialize_light_client_store"))
      | true, false => do
        let b : LightClientBootstrap P f ← decodeAs bootstrapBytes "bootstrap"
        let b ← liftFallible (Gloas.upgradeLcBootstrapToGloas cfg b) "upgrade_lc_bootstrap_to_gloas"
        pure (.gloas (← liftFallible (Gloas.initializeLightClientStore cfg trusted b)
          "initialize_light_client_store"))
      | true, true => do
        let b : Gloas.LightClientBootstrap P ← decodeAs bootstrapBytes "bootstrap"
        pure (.gloas (← liftFallible (Gloas.initializeLightClientStore cfg trusted b)
          "initialize_light_client_store"))
      | false, true => throw "refused: a Gloas bootstrap for an Electra-format store"
    for st in steps do
      match st with
      | .map [("process_update", pu)] =>
        yamlResult (pu.expectKeys ["update_fork_digest", "update", "current_slot", "checks"])
        let gloasUpdate ← classify (pu.field "update_fork_digest") "update_fork_digest"
        let name ← match ← yamlResult (pu.field "update") with
          | .scalar n _ => pure n
          | _ => throw "update name"
        let some bytes := updates.lookup name | throw s!"update file {name} not read"
        let bytes ← bytes
        let slot ← yamlResult ((pu.field "current_slot").bind YamlValue.asNat)
        let slot ← liftFallible (U64.ofNat? slot) "current_slot"
        let what := "process_light_client_update"
        store ← match store, gloasUpdate with
          | .legacy s, false => do
            let u : LightClientUpdate P f ← decodeAs bytes name
            pure (.legacy (← liftFallible (processLightClientUpdate ctx s u slot gvr) what))
          | .gloas s, false => do
            let u : LightClientUpdate P f ← decodeAs bytes name
            let u ← liftFallible (Gloas.upgradeLcUpdateToGloas cfg u) "upgrade_lc_update_to_gloas"
            pure (.gloas (← liftFallible (Gloas.processLightClientUpdate ctx s u slot gvr) what))
          | .gloas s, true => do
            let u : Gloas.LightClientUpdate P ← decodeAs bytes name
            pure (.gloas (← liftFallible (Gloas.processLightClientUpdate ctx s u slot gvr) what))
          | .legacy _, true => throw s!"refused: Gloas update {name} for an Electra-format store"
        runChecks cfg store (← yamlResult (pu.field "checks"))
      | .map [("force_update", fu)] =>
        yamlResult (fu.expectKeys ["current_slot", "checks"])
        let slot ← liftFallible (U64.ofNat? (← yamlResult ((fu.field "current_slot").bind YamlValue.asNat))) "current_slot"
        store ← match store with
          | .legacy s => do pure (.legacy (← liftFallible (processLightClientStoreForceUpdate s slot) "force_update"))
          | .gloas s => do
            pure (.gloas (← liftFallible (Gloas.processLightClientStoreForceUpdate s slot) "force_update"))
        runChecks cfg store (← yamlResult (fu.field "checks"))
      | .map [("upgrade_store", us)] =>
        yamlResult (us.expectKeys ["store_fork_version", "checks"])
        let toGloas ← storeVersion (us.field "store_fork_version")
        store ← match store, toGloas with
          | .legacy s, true => do
            pure (.gloas (← liftFallible (Gloas.upgradeLcStoreToGloas cfg s) "upgrade_lc_store_to_gloas"))
          | .legacy s, false => pure (.legacy s)
          | .gloas s, true => pure (.gloas s)
          | .gloas _, false => throw "refused: upgrade_store from a Gloas store to an earlier fork"
        runChecks cfg store (← yamlResult (us.field "checks"))
      | _ => throw "unknown sync step"

/-- `light_client/update_ranking`. -/
def lightClientUpdateRanking (P : Preset) (f : ConsensusFork) (c : Case) : IO (Except String Unit) := do
  let metaDoc ← readYamlFile c "meta.yaml"
  let n ← match metaDoc.bind fun m => yamlResult ((m.field "updates_count").bind YamlValue.asNat) with
    | .ok n => pure n
    | .error e => return .error e
  let mut files := #[]
  for i in [0:n] do files := files.push (← readSsz c s!"updates_{i}.ssz_snappy")
  pure do
    let us : Array (LightClientUpdate P f) ← files.mapM fun b => do decodeAs (← b) "update"
    for i in [0:us.size] do
      for j in [i+1:us.size] do
        match us[i]?, us[j]? with
        | some a, some b =>
          if ← liftFallible (isBetterUpdate P b a) "is_better_update" then
            throw s!"updates_{j} ranks better than updates_{i}"
        | _, _ => throw "index"

/-- `light_client/update_ranking` at Gloas: as `lightClientUpdateRanking`, over
`Gloas.LightClientUpdate` and the Gloas `is_better_update`. -/
def gloasLightClientUpdateRanking (P : Preset) (c : Case) : IO (Except String Unit) := do
  let metaDoc ← readYamlFile c "meta.yaml"
  let n ← match metaDoc.bind fun m => yamlResult ((m.field "updates_count").bind YamlValue.asNat) with
    | .ok n => pure n
    | .error e => return .error e
  let mut files := #[]
  for i in [0:n] do files := files.push (← readSsz c s!"updates_{i}.ssz_snappy")
  pure do
    let us : Array (Gloas.LightClientUpdate P) ← files.mapM fun b => do decodeAs (← b) "update"
    for i in [0:us.size] do
      for j in [i+1:us.size] do
        match us[i]?, us[j]? with
        | some a, some b =>
          if ← liftFallible (Gloas.isBetterUpdate P b a) "is_better_update" then
            throw s!"updates_{j} ranks better than updates_{i}"
        | _, _ => throw "index"

/-- A Gloas `light_client` case: `single_merkle_proof` over the Gloas proof trees
(`GloasLightClientFullNode.lean`), `sync` over the Gloas store, `update_ranking` over the Gloas
updates, `data_collection` over the Gloas state transition (goal `eip8282-gloas-cross-layer-v1`,
unit U7c: `Harness/GloasLightClientDataCollection.lean`). -/
def gloasLightClientCase (P : Preset) (cfg : Config) (c : Case) : IO (Except String Unit) := do
  match c.key.handler, c.key.suite with
  | "single_merkle_proof", "BeaconState" =>
    singleMerkleProof (Gloas.BeaconState.proofTree (P := P)) c
  | "single_merkle_proof", "BeaconBlockBody" =>
    singleMerkleProof (Gloas.BeaconBlockBody.proofTree (P := P)) c
  | "sync", _ => lightClientSync P .gloas cfg c
  | "update_ranking", _ => gloasLightClientUpdateRanking P c
  | "data_collection", _ => gloasLightClientDataCollection P cfg c
  | h, s => pure (.error s!"UNIMPLEMENTED: no Gloas light_client handler {h}/{s}")

/-- Run a `light_client/<handler>` or `merkle_proof/<handler>` case. -/
def lightClientCase (cfg : Config) (c : Case) : IO (Except String Unit) := do
  let some P := Preset.ofName? c.preset | return .error s!"no preset {c.preset}"
  let some f := ConsensusFork.ofName? c.key.fork | return .error s!"no fork {c.key.fork}"
  if f == .gloas then
    if c.key.runner != "light_client" then
      return .error s!"UNIMPLEMENTED: no Gloas {c.key.runner} handler"
    return ← gloasLightClientCase P cfg c
  match c.key.handler, c.key.suite with
  | "single_merkle_proof", "BeaconState" => singleMerkleProof (BeaconState.proofTree (P := P) (f := f)) c
  | "single_merkle_proof", "BeaconBlockBody" =>
    singleMerkleProof (BeaconBlockBody.proofTree (P := P) (f := f)) c
  | "sync", _ => lightClientSync P f cfg c
  | "data_collection", _ => lightClientDataCollection P f cfg c
  | "update_ranking", _ => lightClientUpdateRanking P f c
  | h, s => pure (.error s!"UNIMPLEMENTED: no light_client handler {h}/{s}")

end JauneConsensus.Harness
