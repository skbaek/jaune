import JauneConsensus.Sync
import JauneConsensus.FastConfirmation
import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Snappy
import JauneConsensus.Harness.Yaml
import JauneConsensus.Harness.ConfigOverride

/-!
# The fork-choice family: `fork_choice`, `sync`, `fast_confirmation` (harness only)

`tests/formats/fork_choice/README.md`, `tests/formats/sync/README.md` and
`tests/formats/fast_confirmation/README.md` at `v1.7.0-beta.4`. The store is
initialised with `get_forkchoice_store(anchor_state, anchor_block)` (and, for
`fast_confirmation`, `get_fast_confirmation_store(store)`), and the steps of `steps.yaml` run in
order:

* `tick`: `on_tick(store, seconds_to_milliseconds(tick))`;
* `block` (with `valid`, default `true`): `on_block(store, block)`, then, when it applied,
  `on_attestation(store, a, is_from_block=True)` for each attestation of the block and
  `on_attester_slashing(store, s)` for each of its attester slashings (the format's
  "Condition"; the pyspec helper `add_block` runs both); any rejection fails the case.
  `blobs`/`proofs` are the values `retrieve_blobs_and_proofs` returns (empty lists when absent);
  `columns` are the sidecars `retrieve_column_sidecars` returns (an empty list when absent, a
  rejection when the list is empty);
* `attestation`, `attester_slashing` (with `valid`): the handlers;
* `block_hash` + `payload_status` (`sync` only): the mocked engine's response for that payload,
  used by the next `on_block` whose payload has that hash (`JauneConsensus/Sync.lean`);
* `checks`: `head` (`get_head(store).root` and its slot, the optimistic head for `sync`), `time`
  and `genesis_time` (`milliseconds_to_seconds` of the store's), `justified_checkpoint`,
  `finalized_checkpoint`, `proposer_boost_root`, `get_proposer_head` (of `get_head(store)` at
  `get_current_slot(store)`).
  `fast_confirmation` has no explicit step for its handler: the generator runs
  `on_fast_confirmation` and then yields a checks step carrying the fast-confirmation keys
  (`previous_epoch_observed_justified_checkpoint`, `current_epoch_observed_justified_checkpoint`,
  `previous_epoch_greatest_unrealized_checkpoint`, `previous_slot_head`, `current_slot_head`,
  `confirmed_root`, `safe_execution_block_hash`), so a checks step carrying them runs
  `on_fast_confirmation` first and then compares all its keys; a checks step carrying only some
  of them fails the case.

A step marked `valid: false` must reject, and leaves the store unchanged. Any other key fails the
case. `bls_setting` 0 (or absent) allows BLS
on or off; the handler verifies signatures unless `JAUNE_CONSENSUS_FC_BLS=0`; `bls_setting` 2
(every `fast_confirmation` case) runs with BLS off.
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
  | forkChoice | sync | fastConfirmation
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

/-- Run the steps of one case at preset `P`, fork `f`. -/
private def runSteps (P : Preset) (f : CFork) (c : Case) (ctx : Ctx) (mode : FcMode) :
    H Unit := do
  let cfg := ctx.cfg
  let sync := mode == .sync
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
    if keys.contains "tick" then
      if !(keys.all (· ∈ ["tick", "valid"])) then throw s!"{here}: keys {keys}"
      let t ← u64Of "tick" (← yamlE here (s.field "tick"))
      let valid ← stepValid s
      match (do onTick cfg run.store (← secondsToMilliseconds t)), valid with
      | .ok st, true => run := { run with store := st }
      | .error r, true => throw s!"{here}: on_tick rejected: {repr r}"
      | .ok _, false => throw s!"{here}: on_tick applied, expected invalid"
      | .error _, false => pure ()
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
      | .ok (st, opt, imported) =>
        run := { run with opt }
        if imported != valid then
          throw s!"{here}: on_block {name} imported={imported}, expected valid={valid}"
        if imported then
          let mut st := st
          for a in signed.message.body.attestations.toArray do
            st ← rejectE s!"{here}: on_attestation (from block)" (onAttestation ctx st a true)
          for sl in signed.message.body.attester_slashings.toArray do
            st ← rejectE s!"{here}: on_attester_slashing (from block)" (onAttesterSlashing ctx st sl)
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
      | .error _, false => pure ()
    else if keys.contains "attester_slashing" then
      if !(keys.all (· ∈ ["attester_slashing", "valid"])) then throw s!"{here}: keys {keys}"
      let name ← match s.get? "attester_slashing" with
        | some (.scalar n _) => pure n
        | _ => throw s!"{here}: attester_slashing name"
      let sl : AttesterSlashing P f ← decodeFile c s!"{name}.ssz_snappy"
      match onAttesterSlashing ctx run.store sl, ← stepValid s with
      | .ok st, true => run := { run with store := st }
      | .error r, true => throw s!"{here}: on_attester_slashing rejected: {repr r}"
      | .ok _, false => throw s!"{here}: on_attester_slashing applied, expected invalid"
      | .error _, false => pure ()
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

/-- `fork_choice/<handler>`, `sync/optimistic` and `fast_confirmation/<handler>`. `config` gives the case's configuration. -/
def forkChoiceCase (config : Case → IO (Except ConfigError Config)) (mode : FcMode) (c : Case) :
    IO (Except String Unit) := do
  let some P := Preset.ofName? c.preset | return .error s!"no preset {c.preset}"
  let some f := CFork.ofName? c.key.fork | return .error s!"no fork {c.key.fork}"
  let cfg ← match ← config c with
    | .ok cfg => pure cfg
    | .error e => return .error s!"config: {e}"
  -- `bls_setting` (`tests/formats/README.md`): 2 ignored, 1 required, 0 or absent either way
  let setting ← blsSettingOf c
  let envOff := (← IO.getEnv "JAUNE_CONSENSUS_FC_BLS") == some "0"
  let bls ← match setting with
    | "absent" | "0" => pure !envOff
    | "1" => pure true
    | "2" => pure false
    | s => return .error s!"bls_setting {s}"
  let ctx : Ctx := { cfg, blsActive := bls }
  ExceptT.run (runSteps P f c ctx mode)

end JauneConsensus.Harness
