import JauneConsensus.Epoch
import JauneConsensus.Harness.ConfigOverride
import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Snappy

/-!
# `epoch_processing` case checks (harness only)

`tests/formats/epoch_processing/README.md` (`consensus-specs` `v1.6.1`). For a handler naming a
sub-transition, `pre.ssz_snappy` is the `BeaconState` just before it; running
`process_<handler>` must give exactly `post.ssz_snappy` (compared byte for byte, which implies
equal roots), or must reject when the case has no `post`. Where the case also carries
`pre_epoch.ssz_snappy`, the whole `process_epoch` is run from it and must give
`post_epoch.ssz_snappy` (or reject when that is absent): the format's alternative condition.

The alternative condition is not part of the verdict. In `v1.6.1`, two generators write
`pre_epoch` before editing the state by hand: `effective_balance_hysteresis` and
`effective_balance_hysteresis_with_compounding_credentials` (`tests/core/pyspec/eth2spec/test/
phase0/epoch_processing/test_process_effective_balance_updates.py` and its Electra twin) yield
`pre_epoch`, then overwrite effective balances and balances, then yield `pre`. Their
`pre_epoch → post_epoch` is therefore not a state transition, and no correct `process_epoch` can
satisfy it. The verdict is the format's required condition (`pre → post`) for every case;
`alsoFullEpoch := true` (the runner sets it from `JAUNE_CONSENSUS_EPOCH_FULL=1`) runs the
alternative check as well, for diagnostics.
-/

namespace JauneConsensus.Harness

/-- A state transition at every preset and fork, under a processing context. -/
abbrev StateStep := ∀ {P : Preset} {f : CFork}, Ctx → BeaconState P f → M (BeaconState P f)

/-- A configuration-only step as a context step. -/
def ofCfg (step : ∀ {P : Preset} {f : CFork}, Config → BeaconState P f → M (BeaconState P f)) :
    StateStep := fun ctx s => step ctx.cfg s

/-- The sub-transition of an `epoch_processing` handler (`process_<handler>`). -/
def epochStep : String → Option StateStep
  | "justification_and_finalization" => some (ofCfg processJustificationAndFinalization)
  | "inactivity_updates" => some (ofCfg processInactivityUpdates)
  | "rewards_and_penalties" => some (ofCfg processRewardsAndPenalties)
  | "registry_updates" => some (ofCfg processRegistryUpdates)
  | "slashings" => some (ofCfg processSlashings)
  | "eth1_data_reset" => some (ofCfg processEth1DataReset)
  | "pending_deposits" => some processPendingDeposits
  | "pending_consolidations" => some (ofCfg processPendingConsolidations)
  | "effective_balance_updates" => some (ofCfg processEffectiveBalanceUpdates)
  | "slashings_reset" => some (ofCfg processSlashingsReset)
  | "randao_mixes_reset" => some (ofCfg processRandaoMixesReset)
  | "historical_summaries_update" => some (ofCfg processHistoricalSummariesUpdate)
  | "participation_flag_updates" => some (ofCfg processParticipationFlagUpdates)
  | "sync_committee_updates" => some (ofCfg processSyncCommitteeUpdates)
  | "proposer_lookahead" => some (ofCfg processProposerLookahead)
  | _ => none

/-- The whole `process_epoch`, once every sub-step exists. -/
def fullEpoch? : Option StateStep := some processEpoch

/-- Read and decode a `BeaconState` file of the case. -/
def readState (P : Preset) (f : CFork) (c : Case) (file : String) :
    IO (Except String (BeaconState P f)) := do
  match Snappy.decompress (← IO.FS.readBinFile (c.dir / file)) with
  | .error e => pure (.error s!"{file}: {e}")
  | .ok b =>
    match (deserialize b.toList : M (BeaconState P f)) with
    | .ok s => pure (.ok s)
    | .error r => pure (.error s!"{file}: does not decode: {repr r}")

/-- The first byte offset at which two encodings differ, for diagnostics. -/
def firstDiff (a b : List UInt8) : Nat :=
  ((a.zip b).findIdx? (fun (x, y) => x != y)).getD (min a.length b.length)

/-- The fields of two states that differ, for diagnostics. -/
def stateDiff {P : Preset} {f : CFork} (a b : BeaconState P f) : List String :=
  let chk (name : String) (x : Bool) : List String := if x then [] else [name]
  chk "slot" (a.slot == b.slot) ++ chk "fork" (a.fork == b.fork) ++
  chk "latest_block_header" (a.latest_block_header == b.latest_block_header) ++
  chk "block_roots" (a.block_roots == b.block_roots) ++ chk "state_roots" (a.state_roots == b.state_roots) ++
  chk "historical_roots" (a.historical_roots == b.historical_roots) ++
  chk "eth1_data" (a.eth1_data == b.eth1_data) ++ chk "eth1_data_votes" (a.eth1_data_votes == b.eth1_data_votes) ++
  chk "validators" (a.validators == b.validators) ++ chk "balances" (a.balances == b.balances) ++
  chk "randao_mixes" (a.randao_mixes == b.randao_mixes) ++ chk "slashings" (a.slashings == b.slashings) ++
  chk "previous_epoch_participation" (a.previous_epoch_participation == b.previous_epoch_participation) ++
  chk "current_epoch_participation" (a.current_epoch_participation == b.current_epoch_participation) ++
  chk "justification_bits" (a.justification_bits == b.justification_bits) ++
  chk "previous_justified_checkpoint" (a.previous_justified_checkpoint == b.previous_justified_checkpoint) ++
  chk "current_justified_checkpoint" (a.current_justified_checkpoint == b.current_justified_checkpoint) ++
  chk "finalized_checkpoint" (a.finalized_checkpoint == b.finalized_checkpoint) ++
  chk "inactivity_scores" (a.inactivity_scores == b.inactivity_scores) ++
  chk "current_sync_committee" (a.current_sync_committee == b.current_sync_committee) ++
  chk "next_sync_committee" (a.next_sync_committee == b.next_sync_committee) ++
  chk "historical_summaries" (a.historical_summaries == b.historical_summaries) ++
  chk "deposit_balance_to_consume" (a.deposit_balance_to_consume == b.deposit_balance_to_consume) ++
  chk "exit_balance_to_consume" (a.exit_balance_to_consume == b.exit_balance_to_consume) ++
  chk "earliest_exit_epoch" (a.earliest_exit_epoch == b.earliest_exit_epoch) ++
  chk "pending_deposits" (a.pending_deposits == b.pending_deposits) ++
  chk "pending_consolidations" (a.pending_consolidations == b.pending_consolidations) ++
  chk "proposer_lookahead" (a.proposer_lookahead == b.proposer_lookahead)

/-- Run `step` from `preFile` and compare with `postFile` (or expect a rejection). -/
def checkTransition (P : Preset) (f : CFork) (ctx : Ctx) (c : Case) (step : StateStep)
    (preFile postFile : String) : IO (Option String) := do
  let pre ← match ← readState P f c preFile with
    | .ok s => pure s
    | .error e => return some e
  let got := step ctx pre
  if c.has postFile then
    let want ← match Snappy.decompress (← IO.FS.readBinFile (c.dir / postFile)) with
      | .ok b => pure b.toList
      | .error e => return some s!"{postFile}: {e}"
    match got with
    | .error r => return some s!"{preFile} → rejected ({repr r}), expected {postFile}"
    | .ok s =>
      let out := serialize s
      if out == want then return none
      let fields := match (deserialize want : M (BeaconState P f)) with
        | .ok w => stateDiff s w
        | .error _ => ["(post does not decode)"]
      return some s!"{preFile} → state differs from {postFile} at byte {firstDiff out want} \
        (got {out.length} bytes, want {want.length}); fields {fields}"
  else
    match got with
    | .error _ => return none
    | .ok _ => return some s!"{preFile} → accepted, but the case has no {postFile} (must reject)"

/-- `epoch_processing/<handler>`: `none` when the case passes, otherwise why it fails. -/
def epochProcessingCase (c : Case) (alsoFullEpoch : Bool := false) : IO (Option String) := do
  let some P := Preset.ofName? c.preset | return some s!"no preset {c.preset}"
  let some f := CFork.ofName? c.key.fork | return some s!"no fork {c.key.fork}"
  if !(f.atLeast .electra) then return some s!"fork {c.key.fork} is outside this handler"
  let some cfg := Config.ofPreset? c.preset | return some s!"no configuration for {c.preset}"
  if c.has "config.yaml" then return some "unexpected config.yaml"
  -- `bls_setting` 2 turns BLS verification off; 0, 1 or absent leave it on
  let ctx : Ctx := { cfg, blsActive := (← blsSettingOf c) != "2" }
  let some step := epochStep c.key.handler
    | return some s!"UNIMPLEMENTED: process_{c.key.handler}"
  if let some why ← checkTransition P f ctx c step "pre.ssz_snappy" "post.ssz_snappy" then
    return some why
  if alsoFullEpoch && c.has "pre_epoch.ssz_snappy" then
    let some full := fullEpoch? | return some "UNIMPLEMENTED: process_epoch (pre_epoch present)"
    if let some why ← checkTransition P f ctx c full "pre_epoch.ssz_snappy" "post_epoch.ssz_snappy" then
      return some why
  pure none

/-! ## `rewards` -/

/-- `Deltas` (`tests/formats/rewards/README.md`): the rewards and penalties a deltas function
returns, one entry per validator. -/
ssz_container DeltasFile (P : Preset) where
  rewards : (SszList Gwei P.VALIDATOR_REGISTRY_LIMIT)
  penalties : (SszList Gwei P.VALIDATOR_REGISTRY_LIMIT)

/-- `rewards/<handler>` (`tests/formats/rewards/README.md`): from `pre`, each of
`get_flag_index_deltas` for the source, target and head flags and `get_inactivity_penalty_deltas`
must return exactly the recorded `Deltas`. -/
def rewardsCase (c : Case) : IO (Option String) := do
  let some P := Preset.ofName? c.preset | return some s!"no preset {c.preset}"
  let some f := CFork.ofName? c.key.fork | return some s!"no fork {c.key.fork}"
  if !(f.atLeast .electra) then return some s!"fork {c.key.fork} is outside this handler"
  let some cfg := Config.ofPreset? c.preset | return some s!"no configuration for {c.preset}"
  let want := ["head_deltas.ssz_snappy", "inactivity_penalty_deltas.ssz_snappy", "pre.ssz_snappy",
    "source_deltas.ssz_snappy", "target_deltas.ssz_snappy"]
  if c.files != want then return some s!"unexpected files {c.files}"
  let pre ← match ← readState P f c "pre.ssz_snappy" with
    | .ok s => pure s
    | .error e => return some e
  let computed : List (String × M Deltas) :=
    [("source_deltas.ssz_snappy", getFlagIndexDeltas pre TIMELY_SOURCE_FLAG_INDEX),
     ("target_deltas.ssz_snappy", getFlagIndexDeltas pre TIMELY_TARGET_FLAG_INDEX),
     ("head_deltas.ssz_snappy", getFlagIndexDeltas pre TIMELY_HEAD_FLAG_INDEX),
     ("inactivity_penalty_deltas.ssz_snappy", getInactivityPenaltyDeltas cfg pre)]
  for (file, got) in computed do
    let bytes ← match Snappy.decompress (← IO.FS.readBinFile (c.dir / file)) with
      | .ok b => pure b.toList
      | .error e => return some s!"{file}: {e}"
    let expected ← match (deserialize bytes : M (DeltasFile P)) with
      | .ok d => pure d
      | .error r => return some s!"{file}: does not decode: {repr r}"
    match got with
    | .error r => return some s!"{file}: rejected ({repr r})"
    | .ok (rewards, penalties) =>
      if rewards != expected.rewards.toArray then return some s!"{file}: rewards differ"
      if penalties != expected.penalties.toArray then return some s!"{file}: penalties differ"
  pure none

end JauneConsensus.Harness
