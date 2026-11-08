-- Timing probe for the state transition.
-- Usage: jaune-consensus-transition-bench <preset> <fork> <case dir with pre.ssz_snappy, blocks_0.ssz_snappy>
import JauneConsensus.StateTransition
import JauneConsensus.Harness.Snappy

open Jaune JauneConsensus

def timeIt {α β} (label : String) (f : α → β) (x : α) (show? : β → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure (fun _ => f x)
  let s := show? r
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {t1 - t0} ms ({s})"

def readSsz (α : Type) [Ssz α] (file : System.FilePath) : IO (Option α) := do
  let raw ← IO.FS.readBinFile file
  match Harness.Snappy.decompress raw with
  | .error _ => pure none
  | .ok b => pure (Ssz.deserialize b.toList : M α).toOption

def bench (P : Preset) (f : CFork) (dir : System.FilePath) : IO Unit := do
  let some s ← readSsz (BeaconState P f) (dir / "pre.ssz_snappy") | IO.println "pre decode failed"
  let some b ← readSsz (SignedBeaconBlock P f) (dir / "blocks_0.ssz_snappy") | IO.println "block decode failed"
  let cfg := if P.SLOTS_PER_EPOCH == 8 then Config.minimal else Config.mainnet
  IO.println s!"validators: {s.validators.toArray.size}, attestations in block 0: {b.message.body.attestations.toArray.size}, slot {s.slot} -> {b.message.slot}"
  timeIt "hash_tree_root(state)" (fun (st : BeaconState P f) => (Ssz.hashTreeRoot st : Root)) s toString
  timeIt "process_slot" processSlot s (fun r => toString r.toBool)
  let ctxOn : Ctx := { cfg, blsActive := true }
  let ctxOff : Ctx := { cfg, blsActive := false }
  timeIt "process_epoch" (processEpoch ctxOn) s (fun r => toString r.toBool)
  timeIt "process_slots to block slot" (fun (st : BeaconState P f) => processSlots ctxOn st b.message.slot) s (fun r => toString r.toBool)
  timeIt "state_transition block 0, BLS on" (fun (st : BeaconState P f) => stateTransition ctxOn st b) s (fun r => toString r.toBool)
  timeIt "state_transition block 0, BLS off" (fun (st : BeaconState P f) => stateTransition ctxOff st b) s (fun r => toString r.toBool)

def main (args : List String) : IO UInt32 := do
  match args with
  | [p, f, dir] =>
    let some P := Preset.ofName? p | IO.eprintln "preset"; return 2
    match f with
    | "deneb" => bench P .deneb dir
    | "electra" => bench P .electra dir
    | "fulu" => bench P .fulu dir
    | _ => IO.eprintln "fork"; return 2
    return 0
  | _ => IO.eprintln "usage"; return 2
