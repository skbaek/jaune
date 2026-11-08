import JauneConsensus.Epoch
import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Snappy

/-!
# `epoch_processing` case checks (harness only)

`tests/formats/epoch_processing/README.md` (`consensus-specs` `v1.6.1`). For a handler naming a
sub-transition, `pre.ssz_snappy` is the `BeaconState` just before it; running
`process_<handler>` must give exactly `post.ssz_snappy` (compared byte for byte, which implies
equal roots), or must reject when the case has no `post`. Where the case also carries
`pre_epoch.ssz_snappy`, the whole `process_epoch` is run from it and must give
`post_epoch.ssz_snappy` (or reject when that is absent): the format's alternative condition,
checked in addition rather than instead.
-/

namespace JauneConsensus.Harness

/-- A state transition at every preset and fork. -/
abbrev StateStep := ∀ {P : Preset} {f : CFork}, BeaconState P f → M (BeaconState P f)

/-- The sub-transition of an `epoch_processing` handler (`process_<handler>`). -/
def epochStep : String → Option StateStep
  | "eth1_data_reset" => some processEth1DataReset
  | "participation_flag_updates" => some processParticipationFlagUpdates
  | _ => none

/-- The whole `process_epoch`, once every sub-step exists. -/
def fullEpoch? : Option StateStep := none

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

/-- Run `step` from `preFile` and compare with `postFile` (or expect a rejection). -/
def checkTransition (P : Preset) (f : CFork) (c : Case) (step : StateStep)
    (preFile postFile : String) : IO (Option String) := do
  let pre ← match ← readState P f c preFile with
    | .ok s => pure s
    | .error e => return some e
  let got := step pre
  if c.has postFile then
    let want ← match Snappy.decompress (← IO.FS.readBinFile (c.dir / postFile)) with
      | .ok b => pure b.toList
      | .error e => return some s!"{postFile}: {e}"
    match got with
    | .error r => return some s!"{preFile} → rejected ({repr r}), expected {postFile}"
    | .ok s =>
      let out := serialize s
      if out == want then return none
      return some s!"{preFile} → state differs from {postFile} at byte {firstDiff out want} \
        (got {out.length} bytes, want {want.length})"
  else
    match got with
    | .error _ => return none
    | .ok _ => return some s!"{preFile} → accepted, but the case has no {postFile} (must reject)"

/-- `epoch_processing/<handler>`: `none` when the case passes, otherwise why it fails. -/
def epochProcessingCase (c : Case) : IO (Option String) := do
  let some P := Preset.ofName? c.preset | return some s!"no preset {c.preset}"
  let some f := CFork.ofName? c.key.fork | return some s!"no fork {c.key.fork}"
  if !(f.atLeast .electra) then return some s!"fork {c.key.fork} is outside this handler"
  let some step := epochStep c.key.handler
    | return some s!"UNIMPLEMENTED: process_{c.key.handler}"
  if let some why ← checkTransition P f c step "pre.ssz_snappy" "post.ssz_snappy" then
    return some why
  if c.has "pre_epoch.ssz_snappy" then
    let some full := fullEpoch? | return some "UNIMPLEMENTED: process_epoch (pre_epoch present)"
    if let some why ← checkTransition P f c full "pre_epoch.ssz_snappy" "post_epoch.ssz_snappy" then
      return some why
  pure none

end JauneConsensus.Harness
