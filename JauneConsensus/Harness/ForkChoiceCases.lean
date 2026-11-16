import JauneConsensus.Sync
import JauneConsensus.FastConfirmation
import JauneConsensus.GloasFastConfirmation
import JauneConsensus.Harness.GloasTransition
import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Snappy
import JauneConsensus.Harness.Yaml
import JauneConsensus.Harness.ConfigOverride

/-!
# The fork-choice family: `fork_choice`, `sync`, `fast_confirmation`, `fork_choice_compliance`
(harness only)

`tests/formats/fork_choice/README.md`, `tests/formats/sync/README.md` and
`tests/formats/fast_confirmation/README.md` at `v1.7.0-beta.4`, and for the comptests
`fork_choice_compliance` suites (which have no `tests/formats` entry) the reference runner
`tests/generators/compliance_runners/fork_choice/runner/test_run.py` at the tag. The store is
initialised with `get_forkchoice_store(anchor_state, anchor_block)` (and, for
`fast_confirmation`, `get_fast_confirmation_store(store)`), and the steps of `steps.yaml` run in
order:

* `tick`: `on_tick(store, seconds_to_milliseconds(tick))`;
* `block` (with `valid`, default `true`): `on_block(store, block)`, then, when it applied,
  `on_attestation(store, a, is_from_block=True)` for each attestation of the block and
  `on_attester_slashing(store, s)` for each of its attester slashings (the format's
  "Condition"; the pyspec helper `add_block` runs both). The comptests reference runner
  suppresses an `AssertionError` from those block-carried messages, so in `fork_choice_compliance`
  an assertion rejection there is skipped; elsewhere any rejection fails the case.
  `blobs`/`proofs` are the values `retrieve_blobs_and_proofs` returns (empty lists when absent);
  `columns` are the sidecars `retrieve_column_sidecars` returns (an empty list when absent, a
  rejection when the list is empty);
* `attestation`, `attester_slashing` (with `valid`): the handlers;
* `block_hash` + `payload_status` (`sync` only): the mocked engine's response for that payload,
  used by the next `on_block` whose payload has that hash (`JauneConsensus/Sync.lean`);
* `checks`: `head` (`get_head(store).root` and its slot, the optimistic head for `sync`), `time`
  and `genesis_time` (`milliseconds_to_seconds` of the store's), `justified_checkpoint`,
  `finalized_checkpoint`, `proposer_boost_root`, `get_proposer_head` (of `get_head(store)` at
  `get_current_slot(store)`), and `viable_for_head_roots_and_weights` (the leaves of the filtered
  node tree with their `get_weight`, compared as a set as the reference runner does).
  `fast_confirmation` has no explicit step for its handler: the generator runs
  `on_fast_confirmation` and then yields a checks step carrying the fast-confirmation keys
  (`previous_epoch_observed_justified_checkpoint`, `current_epoch_observed_justified_checkpoint`,
  `previous_epoch_greatest_unrealized_checkpoint`, `previous_slot_head`, `current_slot_head`,
  `confirmed_root`, `safe_execution_block_hash`), so a checks step carrying them runs
  `on_fast_confirmation` first and then compares all its keys; a checks step carrying only some
  of them fails the case.

A step marked `valid: false` must reject, and leaves the store unchanged; in
`fork_choice_compliance` the rejection must be an assertion or an index error
(`expect_assertion_error`). Any other key fails the case. `bls_setting` 0 (or absent) allows BLS
on or off; the handler verifies signatures unless `JAUNE_CONSENSUS_FC_BLS=0`; `bls_setting` 2
(every `fast_confirmation` and `fork_choice_compliance` case) runs with BLS off.
-/

namespace JauneConsensus.Harness

open Jaune (Bytes B256)
open Yaml

private abbrev H := ExceptT String IO

private def liftE {α : Type} (x : Except String α) : H α := ExceptT.mk (pure x)

private def yamlE {α : Type} (what : String) (x : Except YamlError α) : H α :=
  liftE (x.mapError (fun e => s!"{what}: {e}"))

private def readSszFile (c : Case) (file : String) : H Bytes := do
  match Snappy.decompress (← IO.FS.readBinFile (c.dir / file)) with
  | .ok b => pure b.toList
  | .error e => throw s!"{file}: snappy: {e}"

private def decodeFile {α : Type} [Ssz α] (c : Case) (file : String) : H α := do
  let bytes ← readSszFile c file
  match (Ssz.deserialize bytes : M α) with
  | .ok v => pure v
  | .error r => throw s!"{file}: decode rejected: {repr r}"

private def rootOf (what : String) (v : YVal) : H Root := do
  let bs ← yamlE what v.asHex
  if bs.length != 32 then throw s!"{what}: not 32 bytes"
  pure (B256.ofBytes bs)

private def u64Of (what : String) (v : YVal) : H U64 := do
  let n ← yamlE what v.asNat
  match U64.ofNat? n what with
  | .ok x => pure x
  | .error _ => throw s!"{what}: out of uint64 range"

private def stepValid (s : YVal) : H Bool :=
  match s.get? "valid" with
  | none => pure true
  | some v => yamlE "valid" v.asBool

private def checkpointOf (what : String) (v : YVal) : H Checkpoint := do
  yamlE what (v.expectKeys ["epoch", "root"])
  pure { epoch := ← u64Of what (← yamlE what (v.field "epoch")),
         root := ← rootOf what (← yamlE what (v.field "root")) }

private def rejectE {α : Type} (what : String) (x : M α) : H α :=
  match x with
  | .ok v => pure v
  | .error r => throw s!"{what}: rejected: {repr r}"

private def payloadStatusOf (v : YVal) : H PayloadStatusV1 := do
  let kind ← match (← yamlE "status" (v.field "status")) with
    | .scalar "VALID" _ => pure PayloadStatusKind.valid
    | .scalar "INVALID" _ => pure .invalid
    | .scalar "SYNCING" _ => pure .syncing
    | .scalar "ACCEPTED" _ => pure .accepted
    | .scalar "INVALID_BLOCK_HASH" _ => pure .invalidBlockHash
    | _ => throw "payload_status: unknown status"
  let lvh ← match v.get? "latest_valid_hash" with
    | none => pure none
    | some x => if x.isNull then pure none else some <$> rootOf "latest_valid_hash" x
  pure { status := kind, latestValidHash := lvh }

/-- Which runner of the family a case belongs to. -/
inductive FcMode
  | forkChoice | sync | fastConfirmation | compliance
  deriving BEq

/-- The harness's state across steps: the fork-choice store, the optimistic store and the mocked
engine's responses by payload hash (`sync` only), and the fast-confirmation store. -/
private structure Run (P : Preset) (f : CFork) where
  store : Store P f
  opt : OptimisticStore P f
  statuses : Std.TreeMap Hash32 PayloadStatusV1 compare
  fcr : FastConfirmationStore P f

/-- The fast-confirmation check keys. -/
private def fcrKeys : List String :=
  ["previous_epoch_observed_justified_checkpoint", "current_epoch_observed_justified_checkpoint",
   "previous_epoch_greatest_unrealized_checkpoint", "previous_slot_head", "current_slot_head",
   "confirmed_root", "safe_execution_block_hash"]

/-- `expect_assertion_error`'s accepted failures: `AssertionError` and `IndexError`. -/
private def isAssertionLike : Reject → Bool
  | .assert _ | .index .. => true
  | _ => false

/-- `get_viable_for_head_checks(spec, store)` (`tests/core/pyspec/.../helpers/fork_choice.py`):
the leaves of the filtered node tree reached from the justified root, each with its
`get_weight`. -/
private def viableForHead (cfg : Config) (store : Store P f) : M (List (Root × Gwei)) := do
  let nodes ← getFilteredNodeTree cfg store
  let mut pending : List ForkChoiceNode := [{ root := store.justified_checkpoint.root }]
  let mut leaves : Array ForkChoiceNode := #[]
  for _ in [0:store.blocks.size + 1] do
    match pending with
    | [] => break
    | node :: rest =>
      pending := rest
      let children := (getNodeChildren store node).filter nodes.contains
      if children.isEmpty then leaves := leaves.push node
      else pending := children ++ pending
  if !pending.isEmpty then throw (.assert "viable_for_head: walk longer than the block tree")
  leaves.toList.mapM fun n => do pure (n.root, ← getWeight cfg store n)

/-- Run the steps of one case at preset `P`, fork `f`. -/
private def runSteps (P : Preset) (f : CFork) (c : Case) (ctx : Ctx) (mode : FcMode) :
    H Unit := do
  let cfg := ctx.cfg
  let sync := mode == .sync
  let compliance := mode == .compliance
  let anchorState : BeaconState P f ← decodeFile c "anchor_state.ssz_snappy"
  let anchorBlock : BeaconBlock P f ← decodeFile c "anchor_block.ssz_snappy"
  let steps ← yamlE "steps.yaml" ((parse (← IO.FS.readBinFile (c.dir / "steps.yaml"))).bind YVal.asSeq)
  let store ← rejectE "get_forkchoice_store" (getForkchoiceStore cfg anchorState anchorBlock)
  let opt ← rejectE "get_optimistic_store" (getOptimisticStore anchorState anchorBlock)
  let mut run : Run P f := { store, opt, statuses := ∅, fcr := getFastConfirmationStore store }
  let mut i := 0
  for s in steps do
    let here := s!"step {i}"
    i := i + 1
    let keys := s.keys
    -- A `valid: false` step must reject; in the comptests with an assertion or index error.
    let expectReject (what : String) (r : Reject) : H Unit :=
      if compliance && !isAssertionLike r then
        throw s!"{here}: {what} rejected with {repr r}, expected an assertion error"
      else pure ()
    if keys.contains "tick" then
      if !(keys.all (· ∈ ["tick", "valid"])) then throw s!"{here}: keys {keys}"
      let t ← u64Of "tick" (← yamlE here (s.field "tick"))
      let valid ← stepValid s
      match (do onTick cfg run.store (← secondsToMilliseconds t)), valid with
      | .ok st, true => run := { run with store := st }
      | .error r, true => throw s!"{here}: on_tick rejected: {repr r}"
      | .ok _, false => throw s!"{here}: on_tick applied, expected invalid"
      | .error r, false => expectReject "on_tick" r
    else if keys.contains "block" then
      if !(keys.all (· ∈ ["block", "valid", "blobs", "proofs", "columns"])) then
        throw s!"{here}: keys {keys}"
      let name ← match s.get? "block" with
        | some (.scalar n _) => pure n
        | _ => throw s!"{here}: block name"
      let signed : SignedBeaconBlock P f ← decodeFile c s!"{name}.ssz_snappy"
      let valid ← stepValid s
      -- `retrieve_blobs_and_proofs`
      let blobs : List (Blob P) ← match s.get? "blobs" with
        | none => pure []
        | some (.scalar b _) =>
          let l : SszList (Blob P) P.MAX_BLOB_COMMITMENTS_PER_BLOCK ← decodeFile c s!"{b}.ssz_snappy"
          pure l.toArray.toList
        | some _ => throw s!"{here}: blobs"
      let proofs : List KZGProof ← match s.get? "proofs" with
        | none => pure []
        | some v => do
          let xs ← yamlE "proofs" v.asSeq
          xs.mapM fun x => do
            let bs ← yamlE "proof" x.asHex
            if h : bs.toArray.size = 48 then pure (⟨bs.toArray, h⟩ : KZGProof)
            else throw s!"{here}: proof not 48 bytes"
      -- `retrieve_column_sidecars`
      let columns : Option (List (DataColumnSidecar P)) ← match s.get? "columns" with
        | none => pure (some [])
        | some v => do
          let names ← yamlE "columns" v.asSeq
          if names.isEmpty then pure none
          else some <$> names.mapM fun n => match n with
            | .scalar nm _ => decodeFile c s!"{nm}.ssz_snappy"
            | _ => throw s!"{here}: column name"
      let oracle : DataOracle P := {
        retrieveBlobsAndProofs := fun _ => pure (blobs, proofs)
        retrieveColumnSidecars := fun _ => match columns with
          | some cs => pure cs
          | none => throw (.assert "retrieve_column_sidecars: not all required columns sampled") }
      let applied : M (Store P f × OptimisticStore P f × Bool) :=
        if sync then
          match run.statuses.get? signed.message.body.execution_payload.block_hash with
          | some st => onBlockOptimistic ctx oracle run.store run.opt st signed
          | none => throw (.assert "harness: no payload status for the block's payload")
        else
          match onBlock ctx oracle run.store signed with
          | .ok st => pure (st, run.opt, true)
          | .error r => throw r
      match applied with
      | .error r =>
        if valid then throw s!"{here}: on_block {name} rejected: {repr r}"
        else expectReject s!"on_block {name}" r
      | .ok (st, opt, imported) =>
        run := { run with opt }
        if imported != valid then
          throw s!"{here}: on_block {name} imported={imported}, expected valid={valid}"
        if imported then
          let mut st := st
          -- The comptests reference runner suppresses `AssertionError` here.
          for a in signed.message.body.attestations.toArray do
            match onAttestation ctx st a true with
            | .ok st' => st := st'
            | .error r =>
              if !(compliance && r matches .assert _) then
                throw s!"{here}: on_attestation (from block) rejected: {repr r}"
          for sl in signed.message.body.attester_slashings.toArray do
            match onAttesterSlashing ctx st sl with
            | .ok st' => st := st'
            | .error r =>
              if !(compliance && r matches .assert _) then
                throw s!"{here}: on_attester_slashing (from block) rejected: {repr r}"
          run := { run with store := st }
    else if keys.contains "attestation" then
      if !(keys.all (· ∈ ["attestation", "valid"])) then throw s!"{here}: keys {keys}"
      let name ← match s.get? "attestation" with
        | some (.scalar n _) => pure n
        | _ => throw s!"{here}: attestation name"
      let a : Attestation P f ← decodeFile c s!"{name}.ssz_snappy"
      match onAttestation ctx run.store a false, ← stepValid s with
      | .ok st, true => run := { run with store := st }
      | .error r, true => throw s!"{here}: on_attestation rejected: {repr r}"
      | .ok _, false => throw s!"{here}: on_attestation applied, expected invalid"
      | .error r, false => expectReject "on_attestation" r
    else if keys.contains "attester_slashing" then
      if !(keys.all (· ∈ ["attester_slashing", "valid"])) then throw s!"{here}: keys {keys}"
      let name ← match s.get? "attester_slashing" with
        | some (.scalar n _) => pure n
        | _ => throw s!"{here}: attester_slashing name"
      let sl : AttesterSlashing P f ← decodeFile c s!"{name}.ssz_snappy"
      let valid ← stepValid s
      -- the comptests reference runner asserts `valid` for this step
      if compliance && !valid then throw s!"{here}: invalid attester_slashing in a comptests case"
      match onAttesterSlashing ctx run.store sl, valid with
      | .ok st, true => run := { run with store := st }
      | .error r, true => throw s!"{here}: on_attester_slashing rejected: {repr r}"
      | .ok _, false => throw s!"{here}: on_attester_slashing applied, expected invalid"
      | .error r, false => expectReject "on_attester_slashing" r
    else if keys.contains "block_hash" then
      if !sync then throw s!"{here}: payload status outside a sync case"
      yamlE here (s.expectKeys ["block_hash", "payload_status"])
      let h ← rootOf "block_hash" (← yamlE here (s.field "block_hash"))
      let st ← payloadStatusOf (← yamlE here (s.field "payload_status"))
      run := { run with statuses := run.statuses.insert h st }
    else if keys == ["checks"] then
      let checks ← yamlE here (s.field "checks")
      -- `on_fast_confirmation` precedes the checks step that reports it
      let present := fcrKeys.filter (checks.keys.contains ·)
      if !present.isEmpty then
        if mode != .fastConfirmation then throw s!"{here}: fast-confirmation checks outside fast_confirmation"
        if present.length != fcrKeys.length then
          throw s!"{here}: fast-confirmation checks {present}, expected all of {fcrKeys}"
        let fcr ← rejectE s!"{here}: on_fast_confirmation"
          (onFastConfirmation ctx (fun _ => true) { run.fcr with store := run.store })
        run := { run with fcr }
      let store := run.store
      let fcr := run.fcr
      let checkCheckpoint (k : String) (v : YVal) (got : Checkpoint) : H Unit := do
        let want ← checkpointOf k v
        if got != want then
          throw s!"{here}: {k} epoch {got.epoch} root {got.root.toHex}, expected epoch {want.epoch} root {want.root.toHex}"
      let checkRoot (k : String) (v : YVal) (got : Root) : H Unit := do
        let want ← rootOf k v
        if got != want then throw s!"{here}: {k} {got.toHex}, expected {want.toHex}"
      for k in checks.keys do
        let v ← yamlE here (checks.field k)
        match k with
        | "head" =>
          yamlE here (v.expectKeys ["slot", "root"])
          let head ← rejectE s!"{here}: get_head"
            (if sync then getOptimisticHead cfg store run.opt else getHead cfg store)
          let block ← rejectE s!"{here}: head block" (lookup store.blocks head.root "head")
          let wantRoot ← rootOf "head.root" (← yamlE here (v.field "root"))
          let wantSlot ← u64Of "head.slot" (← yamlE here (v.field "slot"))
          if head.root != wantRoot || block.slot != wantSlot then
            throw s!"{here}: head is {head.root.toHex} at slot {block.slot}, expected {wantRoot.toHex} at {wantSlot}"
        | "time" =>
          let want ← u64Of "time" v
          let got ← rejectE here (millisecondsToSeconds store.time_ms)
          if got != want then throw s!"{here}: time {got}, expected {want}"
        | "genesis_time" =>
          let want ← u64Of "genesis_time" v
          let got ← rejectE here (millisecondsToSeconds store.genesis_time_ms)
          if got != want then throw s!"{here}: genesis_time {got}, expected {want}"
        | "justified_checkpoint" => checkCheckpoint k v store.justified_checkpoint
        | "finalized_checkpoint" => checkCheckpoint k v store.finalized_checkpoint
        | "proposer_boost_root" => checkRoot k v store.proposer_boost_root
        | "get_proposer_head" =>
          let got ← rejectE s!"{here}: get_proposer_head" (do
            getProposerHead cfg store (← getHead cfg store) (← getCurrentSlot cfg store))
          checkRoot k v got.root
        | "viable_for_head_roots_and_weights" =>
          let xs ← yamlE k v.asSeq
          let want ← xs.mapM fun x => do
            yamlE k (x.expectKeys ["root", "weight"])
            pure ((← rootOf "root" (← yamlE k (x.field "root"))).toHex,
              (← u64Of "weight" (← yamlE k (x.field "weight"))).toNat)
          let got ← rejectE s!"{here}: viable_for_head" (viableForHead cfg store)
          let got := got.map fun (r, w) => (r.toHex, w.toNat)
          let norm (l : List (String × Nat)) :=
            (l.mergeSort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2))).eraseDups
          if norm got != norm want then
            throw s!"{here}: viable_for_head_roots_and_weights {norm got}, expected {norm want}"
        | "previous_epoch_observed_justified_checkpoint" =>
          checkCheckpoint k v fcr.previous_epoch_observed_justified_checkpoint
        | "current_epoch_observed_justified_checkpoint" =>
          checkCheckpoint k v fcr.current_epoch_observed_justified_checkpoint
        | "previous_epoch_greatest_unrealized_checkpoint" =>
          checkCheckpoint k v fcr.previous_epoch_greatest_unrealized_checkpoint
        | "previous_slot_head" => checkRoot k v fcr.previous_slot_head
        | "current_slot_head" => checkRoot k v fcr.current_slot_head
        | "confirmed_root" => checkRoot k v fcr.confirmed_root
        | "safe_execution_block_hash" =>
          checkRoot k v (← rejectE s!"{here}: get_safe_execution_block_hash" (getSafeExecutionBlockHash fcr))
        | other => throw s!"{here}: unknown check {other}"
    else throw s!"{here}: unknown step keys {keys}"


/-! ## Gloas (`JauneConsensus/GloasForkChoice.lean`, `GloasFastConfirmation.lean`)

The Gloas store, nodes and messages are the separate types of `GloasForkChoice.lean`, so the Gloas
cases run in their own step loop, with the Gloas steps of `tests/formats/fork_choice/README.md`:

* `execution_payload` (with `valid`): `on_execution_payload_envelope(store, signed_envelope)`, with
  the default `retrieve_column_sidecars_and_kzg_commitments` of the pyspec build (no sidecars, so
  the data is available) and the no-op engine (`ctx.executionValid`);
* `payload_attestation_message` (with `valid`): `on_payload_attestation_message(store, message)`;
* after an applied `block`, its attestations and attester slashings as before, then each of its
  payload attestations expanded into one message per set bit of `get_ptc(post_state, slot)`, in
  PTC order, each through `on_payload_attestation_message(..., is_from_block=True)` (the format's
  "Condition"; the comptests runner suppresses an `AssertionError` there);
* checks `head` with the head's `payload_status`, `viable_for_head_roots_and_weights` with each
  leaf's `payload_status`, and `payload_timeliness_vote` / `payload_data_availability_vote`
  (`{block_root, votes}`, the store's list with `null` for a position that has not voted).

The Gloas comptests run under `GLOAS_FORK_EPOCH = 0`, as the reference runner overrides it. -/

private structure GRun (P : Preset) where
  store : Gloas.Store P
  fcr : Gloas.FastConfirmationStore P

/-- `get_viable_for_head_checks(spec, store)` (Gloas): the leaves of the filtered node tree, each
with its `get_weight` and `payload_status`. -/
private def viableForHeadGloas (cfg : Config) (store : Gloas.Store P) :
    M (List (Root × Gwei × Nat)) := do
  let nodes ← Gloas.getFilteredNodeTree cfg store
  let mut pending : List Gloas.ForkChoiceNode :=
    [{ root := store.justified_checkpoint.root, payload_status := .pending }]
  let mut leaves : Array Gloas.ForkChoiceNode := #[]
  for _ in [0:Gloas.nodeFuel store] do
    match pending with
    | [] => break
    | node :: rest =>
      pending := rest
      let children := (← Gloas.getNodeChildren store node).filter nodes.contains
      if children.isEmpty then leaves := leaves.push node
      else pending := children ++ pending
  if !pending.isEmpty then throw (.assert "viable_for_head: walk longer than the node tree")
  leaves.toList.mapM fun n => do pure (n.root, ← Gloas.getWeight cfg store n, n.payload_status.toNat)

/-- The pyspec build's `retrieve_column_sidecars_and_kzg_commitments`: no sidecars. -/
private def gloasOracle : Gloas.DataOracle P :=
  { retrieveColumnSidecarsAndKzgCommitments := fun _ => pure ([], []) }

/-- The messages of a block-carried payload attestation (the format's "Condition"): one per set
bit of `get_ptc(state, slot)`, in PTC order, with an empty signature. -/
private def payloadAttestationMessages (cfg : Config) (state : Gloas.BeaconState P)
    (pa : Gloas.PayloadAttestation P) : M (List Gloas.PayloadAttestationMessage) := do
  let ptc ← Gloas.getPtc cfg state pa.data.slot
  let bits := pa.aggregation_bits.bits
  let mut out : Array Gloas.PayloadAttestationMessage := #[]
  let mut i := 0
  for index in ptc.toArray do
    if ← getAt bits i "aggregation_bits" then
      out := out.push { validator_index := index, data := pa.data, signature := Gloas.emptySignature }
    i := i + 1
  pure out.toList

/-- A YAML vote (`true`, `false` or `null`). -/
private def voteOf (v : YVal) : H (Option Bool) :=
  if v.isNull then pure none else some <$> yamlE "vote" v.asBool

/-- Run the steps of one Gloas case at preset `P`. -/
private def runStepsGloas (P : Preset) (c : Case) (ctx : Ctx) (mode : FcMode) : H Unit := do
  let cfg := ctx.cfg
  let compliance := mode == .compliance
  let tr : Gloas.Transition P := gloasTransition
  let anchorState : Gloas.BeaconState P ← decodeFile c "anchor_state.ssz_snappy"
  let anchorBlock : Gloas.BeaconBlock P ← decodeFile c "anchor_block.ssz_snappy"
  let steps ← yamlE "steps.yaml" ((parse (← IO.FS.readBinFile (c.dir / "steps.yaml"))).bind YVal.asSeq)
  let store ← rejectE "get_forkchoice_store" (Gloas.getForkchoiceStore cfg anchorState anchorBlock)
  let mut run : GRun P := { store, fcr := Gloas.getFastConfirmationStore store }
  let mut i := 0
  for s in steps do
    let here := s!"step {i}"
    i := i + 1
    let keys := s.keys
    let expectReject (what : String) (r : Reject) : H Unit :=
      if compliance && !isAssertionLike r then
        throw s!"{here}: {what} rejected with {repr r}, expected an assertion error"
      else pure ()
    let nameOf (k : String) : H String := match s.get? k with
      | some (.scalar n _) => pure n
      | _ => throw s!"{here}: {k} name"
    -- one handler step: apply, or require a rejection when `valid: false`
    let handle (what : String) (x : M (Gloas.Store P)) : H (Gloas.Store P) := do
      match x, ← stepValid s with
      | .ok st, true => pure st
      | .error r, true => throw s!"{here}: {what} rejected: {repr r}"
      | .ok _, false => throw s!"{here}: {what} applied, expected invalid"
      | .error r, false => do expectReject what r; pure run.store
    if keys.contains "tick" then
      if !(keys.all (· ∈ ["tick", "valid"])) then throw s!"{here}: keys {keys}"
      let t ← u64Of "tick" (← yamlE here (s.field "tick"))
      let st ← handle "on_tick" (do Gloas.onTick cfg run.store (← secondsToMilliseconds t))
      run := { run with store := st }
    else if keys.contains "block" then
      if !(keys.all (· ∈ ["block", "valid"])) then throw s!"{here}: keys {keys}"
      let name ← nameOf "block"
      let signed : Gloas.SignedBeaconBlock P ← decodeFile c s!"{name}.ssz_snappy"
      let valid ← stepValid s
      match Gloas.onBlock tr ctx run.store signed with
      | .error r =>
        if valid then throw s!"{here}: on_block {name} rejected: {repr r}"
        else expectReject s!"on_block {name}" r
      | .ok st =>
        if !valid then throw s!"{here}: on_block {name} applied, expected invalid"
        let mut st := st
        -- The comptests reference runner suppresses `AssertionError` from these.
        let tolerated (r : Reject) : Bool := compliance && r matches .assert _
        for a in signed.message.body.attestations.toArray do
          match Gloas.onAttestation tr ctx st a true with
          | .ok st' => st := st'
          | .error r =>
            if !tolerated r then throw s!"{here}: on_attestation (from block) rejected: {repr r}"
        for sl in signed.message.body.attester_slashings.toArray do
          match Gloas.onAttesterSlashing ctx st sl with
          | .ok st' => st := st'
          | .error r =>
            if !tolerated r then
              throw s!"{here}: on_attester_slashing (from block) rejected: {repr r}"
        let blockRoot : Root := Ssz.hashTreeRoot signed.message
        let postState ← rejectE s!"{here}: store.block_states[block]"
          (lookup st.block_states blockRoot "block_states")
        for pa in signed.message.body.payload_attestations.toArray do
          let msgs ← rejectE s!"{here}: payload attestation messages"
            (payloadAttestationMessages cfg postState pa)
          for m in msgs do
            match Gloas.onPayloadAttestationMessage ctx st m true with
            | .ok st' => st := st'
            | .error r =>
              if !tolerated r then
                throw s!"{here}: on_payload_attestation_message (from block) rejected: {repr r}"
        run := { run with store := st }
    else if keys.contains "attestation" then
      if !(keys.all (· ∈ ["attestation", "valid"])) then throw s!"{here}: keys {keys}"
      let name ← nameOf "attestation"
      let a : Gloas.Attestation P ← decodeFile c s!"{name}.ssz_snappy"
      let st ← handle "on_attestation" (Gloas.onAttestation tr ctx run.store a false)
      run := { run with store := st }
    else if keys.contains "attester_slashing" then
      if !(keys.all (· ∈ ["attester_slashing", "valid"])) then throw s!"{here}: keys {keys}"
      let name ← nameOf "attester_slashing"
      let sl : Gloas.AttesterSlashing ← decodeFile c s!"{name}.ssz_snappy"
      -- the comptests reference runner asserts `valid` for this step
      if compliance && !(← stepValid s) then
        throw s!"{here}: invalid attester_slashing in a comptests case"
      let st ← handle "on_attester_slashing" (Gloas.onAttesterSlashing ctx run.store sl)
      run := { run with store := st }
    else if keys.contains "execution_payload" then
      if !(keys.all (· ∈ ["execution_payload", "valid"])) then throw s!"{here}: keys {keys}"
      let name ← nameOf "execution_payload"
      let e : Gloas.SignedExecutionPayloadEnvelope P ← decodeFile c s!"{name}.ssz_snappy"
      let st ← handle "on_execution_payload_envelope"
        (Gloas.onExecutionPayloadEnvelope ctx gloasOracle run.store e)
      run := { run with store := st }
    else if keys.contains "payload_attestation_message" then
      if !(keys.all (· ∈ ["payload_attestation_message", "valid"])) then
        throw s!"{here}: keys {keys}"
      let name ← nameOf "payload_attestation_message"
      let m : Gloas.PayloadAttestationMessage ← decodeFile c s!"{name}.ssz_snappy"
      let st ← handle "on_payload_attestation_message"
        (Gloas.onPayloadAttestationMessage ctx run.store m false)
      run := { run with store := st }
    else if keys == ["checks"] then
      let checks ← yamlE here (s.field "checks")
      -- `on_fast_confirmation` precedes the checks step that reports it
      let present := fcrKeys.filter (checks.keys.contains ·)
      if !present.isEmpty then
        if mode != .fastConfirmation then throw s!"{here}: fast-confirmation checks outside fast_confirmation"
        if present.length != fcrKeys.length then
          throw s!"{here}: fast-confirmation checks {present}, expected all of {fcrKeys}"
        let fcr ← rejectE s!"{here}: on_fast_confirmation"
          (Gloas.onFastConfirmation tr ctx (fun _ => true) { run.fcr with store := run.store })
        run := { run with fcr }
      let store := run.store
      let fcr := run.fcr
      let checkCheckpoint (k : String) (v : YVal) (got : Checkpoint) : H Unit := do
        let want ← checkpointOf k v
        if got != want then
          throw s!"{here}: {k} epoch {got.epoch} root {got.root.toHex}, expected epoch {want.epoch} root {want.root.toHex}"
      let checkRoot (k : String) (v : YVal) (got : Root) : H Unit := do
        let want ← rootOf k v
        if got != want then throw s!"{here}: {k} {got.toHex}, expected {want.toHex}"
      let checkVotes (k : String) (v : YVal) (m : RootMap (Array (Option Bool))) : H Unit := do
        yamlE here (v.expectKeys ["block_root", "votes"])
        let root ← rootOf s!"{k}.block_root" (← yamlE here (v.field "block_root"))
        let want ← (← yamlE k ((← yamlE here (v.field "votes")).asSeq)).mapM voteOf
        let got ← rejectE s!"{here}: store.{k}" (lookup m root k)
        if got.toList != want then throw s!"{here}: {k} {repr got.toList}, expected {repr want}"
      for k in checks.keys do
        let v ← yamlE here (checks.field k)
        match k with
        | "head" =>
          yamlE here (v.expectKeys ["slot", "root", "payload_status"])
          let head ← rejectE s!"{here}: get_head" (Gloas.getHead cfg store)
          let block ← rejectE s!"{here}: head block" (lookup store.blocks head.root "head")
          let wantRoot ← rootOf "head.root" (← yamlE here (v.field "root"))
          let wantSlot ← u64Of "head.slot" (← yamlE here (v.field "slot"))
          let wantStatus ← yamlE "head.payload_status" ((← yamlE here (v.field "payload_status")).asNat)
          if head.root != wantRoot || block.slot != wantSlot || head.payload_status.toNat != wantStatus then
            throw s!"{here}: head is {head.root.toHex} at slot {block.slot} status {head.payload_status.toNat}, expected {wantRoot.toHex} at {wantSlot} status {wantStatus}"
        | "time" =>
          let want ← u64Of "time" v
          let got ← rejectE here (millisecondsToSeconds store.time_ms)
          if got != want then throw s!"{here}: time {got}, expected {want}"
        | "genesis_time" =>
          let want ← u64Of "genesis_time" v
          let got ← rejectE here (millisecondsToSeconds store.genesis_time_ms)
          if got != want then throw s!"{here}: genesis_time {got}, expected {want}"
        | "justified_checkpoint" => checkCheckpoint k v store.justified_checkpoint
        | "finalized_checkpoint" => checkCheckpoint k v store.finalized_checkpoint
        | "proposer_boost_root" => checkRoot k v store.proposer_boost_root
        | "get_proposer_head" =>
          let got ← rejectE s!"{here}: get_proposer_head" (do
            Gloas.getProposerHead cfg store (← Gloas.getHead cfg store)
              (← Gloas.getCurrentSlot cfg store))
          checkRoot k v got.root
        | "viable_for_head_roots_and_weights" =>
          let xs ← yamlE k v.asSeq
          let want ← xs.mapM fun x => do
            yamlE k (x.expectKeys ["root", "weight", "payload_status"])
            pure ((← rootOf "root" (← yamlE k (x.field "root"))).toHex,
              (← u64Of "weight" (← yamlE k (x.field "weight"))).toNat,
              ← yamlE k ((← yamlE k (x.field "payload_status")).asNat))
          let got ← rejectE s!"{here}: viable_for_head" (viableForHeadGloas cfg store)
          let got := got.map fun (r, w, ps) => (r.toHex, w.toNat, ps)
          let lt (a b : String × Nat × Nat) : Bool :=
            a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 ≤ b.2.2)))
          let norm (l : List (String × Nat × Nat)) := (l.mergeSort lt).eraseDups
          if norm got != norm want then
            throw s!"{here}: viable_for_head_roots_and_weights {norm got}, expected {norm want}"
        | "payload_timeliness_vote" => checkVotes k v store.payload_timeliness_vote
        | "payload_data_availability_vote" => checkVotes k v store.payload_data_availability_vote
        | "previous_epoch_observed_justified_checkpoint" =>
          checkCheckpoint k v fcr.previous_epoch_observed_justified_checkpoint
        | "current_epoch_observed_justified_checkpoint" =>
          checkCheckpoint k v fcr.current_epoch_observed_justified_checkpoint
        | "previous_epoch_greatest_unrealized_checkpoint" =>
          checkCheckpoint k v fcr.previous_epoch_greatest_unrealized_checkpoint
        | "previous_slot_head" => checkRoot k v fcr.previous_slot_head
        | "current_slot_head" => checkRoot k v fcr.current_slot_head
        | "confirmed_root" => checkRoot k v fcr.confirmed_root
        | "safe_execution_block_hash" =>
          checkRoot k v (← rejectE s!"{here}: get_safe_execution_block_hash"
            (Gloas.getSafeExecutionBlockHash fcr))
        | other => throw s!"{here}: unknown check {other}"
    else throw s!"{here}: unknown step keys {keys}"

/-- `fork_choice/<handler>`, `sync/optimistic`, `fast_confirmation/<handler>` and
`fork_choice_compliance/<handler>`. `config` gives the case's configuration. -/
def forkChoiceCase (config : Case → IO (Except ConfigError Config)) (mode : FcMode) (c : Case) :
    IO (Except String Unit) := do
  let some P := Preset.ofName? c.preset | return .error s!"no preset {c.preset}"
  let gloas := c.key.fork == "gloas"
  let cfg ← match ← config c with
    | .ok cfg => pure cfg
    | .error e => return .error s!"config: {e}"
  -- the comptests reference runner overrides `GLOAS_FORK_EPOCH` to 0 for Gloas
  let cfg := if gloas && mode == .compliance then { cfg with GLOAS_FORK_EPOCH := 0 } else cfg
  -- `bls_setting` (`tests/formats/README.md`): 2 ignored, 1 required, 0 or absent either way
  let setting ← blsSettingOf c
  let envOff := (← IO.getEnv "JAUNE_CONSENSUS_FC_BLS") == some "0"
  let bls ← match setting with
    | "absent" | "0" => pure !envOff
    | "1" => pure true
    | "2" => pure false
    | s => return .error s!"bls_setting {s}"
  let ctx : Ctx := { cfg, blsActive := bls }
  if gloas then
    if mode == .sync then return .error "sync: no Gloas suite"
    return ← ExceptT.run (runStepsGloas P c ctx mode)
  let some f := CFork.ofName? c.key.fork | return .error s!"no fork {c.key.fork}"
  ExceptT.run (runSteps P f c ctx mode)

end JauneConsensus.Harness
