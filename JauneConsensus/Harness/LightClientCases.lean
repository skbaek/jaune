import JauneConsensus.LightClient
import JauneConsensus.SSZ.Proof
import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Snappy
import JauneConsensus.Harness.Yaml

/-!
# `light_client` and `merkle_proof` case checks (harness only)

`tests/formats/light_client/` and `tests/formats/merkle_proof/` (`consensus-specs` `v1.6.1`):

* `single_merkle_proof/<Type>`: `is_valid_merkle_branch(leaf, branch, floorlog2(leaf_index),
  get_subtree_index(leaf_index), hash_tree_root(object))` must hold. (The optional check that a
  self-generated proof equals `branch` needs object-level proof generation, not implemented.)
* `sync`: initialize a `LightClientStore` from `bootstrap` and run the steps, checking the
  finalized and optimistic headers after each. Every fork digest must be one of the case fork's
  (`forkDigestsOf`: from Fulu the digest changes at each `BLOB_SCHEDULE` epoch while the types do
  not); a digest of another fork, which would need an object upgrade, is refused.
* `update_ranking`: the `updates_<i>` are in descending precedence: no later update ranks
  better (`is_better_update`) than an earlier one.
-/

namespace JauneConsensus.Harness
open Jaune (Bytes B256)
open Yaml

private def readSsz (c : Case) (file : String) : IO (Except String Bytes) := do
  match Snappy.decompress (← IO.FS.readBinFile (c.dir / file)) with
  | .ok b => pure (.ok b.toList)
  | .error e => pure (.error s!"{file}: snappy: {e}")

private def readYamlFile (c : Case) (file : String) : IO (Except String YVal) := do
  pure ((parse (← IO.FS.readBinFile (c.dir / file))).mapError (s!"{file}: " ++ toString ·))

private def decodeAs {α : Type} [Ssz α] (bytes : Bytes) (what : String) : Except String α :=
  match (deserialize bytes : M α) with
  | .ok v => .ok v
  | .error r => .error s!"{what}: decode rejected: {repr r}"

private def liftM {α : Type} (x : M α) (what : String) : Except String α :=
  match x with
  | .ok v => .ok v
  | .error r => .error s!"{what}: rejected: {repr r}"

private def y {α : Type} (x : Res α) : Except String α := x.mapError toString

private def root32 (v : YVal) : Except String B256 := do
  let bs ← y v.asHex
  if bs.length = 32 then pure (Jaune.Bytes.toB256 bs) else throw "expected 32 bytes"

/-- `is_valid_merkle_branch(leaf, branch, floorlog2(gindex), get_subtree_index(gindex), root)`. -/
def verifyGindexBranch (leaf : B256) (branch : List B256) (gindex : Nat) (root : B256) : M Bool := do
  isValidMerkleBranch leaf branch (← c64 (floorlog2 gindex)) (← getSubtreeIndex gindex) root

/-- `single_merkle_proof/<Type>` for an object of type `α`. -/
@[nospecialize] def singleMerkleProof {α : Type} [Ssz α] (c : Case) : IO (Except String Unit) := do
  if c.files != ["object.ssz_snappy", "proof.yaml"] then return .error s!"unexpected files {c.files}"
  let obj ← readSsz c "object.ssz_snappy"
  let doc ← readYamlFile c "proof.yaml"
  pure do
    let o : α ← decodeAs (← obj) "object"
    let v ← doc
    y (v.expectKeys ["leaf", "leaf_index", "branch"])
    let leaf ← root32 (← y (v.field "leaf"))
    let index ← y ((v.field "leaf_index").bind YVal.asNat)
    let branch ← (← y ((v.field "branch").bind YVal.asSeq)).mapM root32
    let depth := floorlog2 index
    require' (branch.length == depth) "branch length differs from floorlog2(leaf_index)"
    let ok ← liftM (verifyGindexBranch leaf branch index (hashTreeRoot o)) "is_valid_merkle_branch"
    require' ok "is_valid_merkle_branch failed against hash_tree_root(object)"
where require' (b : Bool) (msg : String) : Except String Unit := if b then pure () else throw msg

/-- Check a header against `{slot, beacon_root, execution_root}`. -/
private def checkHeader {P : Preset} (cfg : Config) (h : LightClientHeader P) (v : YVal)
    (what : String) : Except String Unit := do
  y (v.expectKeys ["slot", "beacon_root", "execution_root"])
  let slot ← y ((v.field "slot").bind YVal.asNat)
  let br ← root32 (← y (v.field "beacon_root"))
  let er ← root32 (← y (v.field "execution_root"))
  if h.beacon.slot.toNat != slot then throw s!"{what}.slot {h.beacon.slot.toNat} != {slot}"
  if !(hashTreeRoot h.beacon == br) then throw s!"{what}.beacon_root differs"
  let got ← liftM (getLcExecutionRoot cfg h) "get_lc_execution_root"
  if !(got == er) then throw s!"{what}.execution_root differs"

private def runChecks {P : Preset} {f : CFork} (cfg : Config) (s : LightClientStore P f)
    (checks : YVal) : Except String Unit := do
  y (checks.expectKeys ["finalized_header", "optimistic_header"])
  checkHeader cfg s.finalized_header (← y (checks.field "finalized_header")) "finalized_header"
  checkHeader cfg s.optimistic_header (← y (checks.field "optimistic_header")) "optimistic_header"

/-- `light_client/sync`. -/
def lightClientSync (P : Preset) (f : CFork) (cfg : Config) (c : Case) : IO (Except String Unit) := do
  let metaDoc ← readYamlFile c "meta.yaml"
  let stepsDoc ← readYamlFile c "steps.yaml"
  let bootstrapBytes ← readSsz c "bootstrap.ssz_snappy"
  -- read every update file named by a step
  let steps ← match stepsDoc.bind fun v => y v.asSeq with
    | .ok s => pure s
    | .error e => return .error e
  let mut updates : List (String × Except String Bytes) := []
  for st in steps do
    match st.get? "process_update" with
    | some pu =>
      match (pu.field "update").bind YVal.asNat |>.toOption, (pu.field "update") with
      | _, .ok (.scalar name _) => updates := (name, ← readSsz c (name ++ ".ssz_snappy")) :: updates
      | _, _ => pure ()
    | none => pure ()
  let ctx : Ctx := { cfg }
  pure do
    let m ← metaDoc
    y (m.expectKeys ["genesis_validators_root", "trusted_block_root", "bootstrap_fork_digest",
      "store_fork_digest"])
    let gvr ← root32 (← y (m.field "genesis_validators_root"))
    let trusted ← root32 (← y (m.field "trusted_block_root"))
    let digests ← liftM (forkDigestsOf cfg f gvr) "compute_fork_digest"
    let checkDigest (v : Res YVal) (what : String) : Except String Unit := do
      let d ← y (v.bind YVal.asHex)
      if !digests.contains d then throw s!"refused: {what} {d} is not a {f} fork digest"
    checkDigest (m.field "store_fork_digest") "store_fork_digest"
    checkDigest (m.field "bootstrap_fork_digest") "bootstrap_fork_digest"
    let bootstrap : LightClientBootstrap P f ← decodeAs (← bootstrapBytes) "bootstrap"
    let mut store ← liftM (initializeLightClientStore cfg trusted bootstrap) "initialize_light_client_store"
    for st in steps do
      match st with
      | .map [("process_update", pu)] =>
        y (pu.expectKeys ["update_fork_digest", "update", "current_slot", "checks"])
        checkDigest (pu.field "update_fork_digest") "update_fork_digest"
        let name ← match ← y (pu.field "update") with
          | .scalar n _ => pure n
          | _ => throw "update name"
        let some bytes := updates.lookup name | throw s!"update file {name} not read"
        let update : LightClientUpdate P f ← decodeAs (← bytes) name
        let slot ← y ((pu.field "current_slot").bind YVal.asNat)
        let slot ← liftM (U64.ofNat? slot) "current_slot"
        store ← liftM (processLightClientUpdate ctx store update slot gvr) "process_light_client_update"
        runChecks cfg store (← y (pu.field "checks"))
      | .map [("force_update", fu)] =>
        y (fu.expectKeys ["current_slot", "checks"])
        let slot ← liftM (U64.ofNat? (← y ((fu.field "current_slot").bind YVal.asNat))) "current_slot"
        store ← liftM (processLightClientStoreForceUpdate store slot) "force_update"
        runChecks cfg store (← y (fu.field "checks"))
      | .map [("upgrade_store", us)] =>
        checkDigest (us.field "store_fork_digest") "store_fork_digest"
        runChecks cfg store (← y (us.field "checks"))
      | _ => throw "unknown sync step"

/-- `light_client/update_ranking`. -/
def lightClientUpdateRanking (P : Preset) (f : CFork) (c : Case) : IO (Except String Unit) := do
  let metaDoc ← readYamlFile c "meta.yaml"
  let n ← match metaDoc.bind fun m => y ((m.field "updates_count").bind YVal.asNat) with
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
          if ← liftM (isBetterUpdate P b a) "is_better_update" then
            throw s!"updates_{j} ranks better than updates_{i}"
        | _, _ => throw "index"

/-- Run a `light_client/<handler>` or `merkle_proof/<handler>` case. -/
def lightClientCase (cfg : Config) (c : Case) : IO (Except String Unit) := do
  let some P := Preset.ofName? c.preset | return .error s!"no preset {c.preset}"
  let some f := CFork.ofName? c.key.fork | return .error s!"no fork {c.key.fork}"
  match c.key.handler, c.key.suite with
  | "single_merkle_proof", "BeaconState" => singleMerkleProof (α := BeaconState P f) c
  | "single_merkle_proof", "BeaconBlockBody" => singleMerkleProof (α := BeaconBlockBody P f) c
  | "sync", _ => lightClientSync P f cfg c
  | "update_ranking", _ => lightClientUpdateRanking P f c
  | h, s => pure (.error s!"UNIMPLEMENTED: no light_client handler {h}/{s}")

end JauneConsensus.Harness
