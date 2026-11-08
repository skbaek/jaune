-- Timing probe for the state transition: hash_tree_root of a decoded state and process_slot.
-- Usage: jaune-consensus-transition-bench <preset> <fork> <state.ssz_snappy>
import JauneConsensus.Transition
import JauneConsensus.Harness.Snappy

open Jaune JauneConsensus

def timeIt {α β} (label : String) (f : α → β) (x : α) (show? : β → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure (fun _ => f x)
  let s := show? r
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {t1 - t0} ms ({s})"

def bench (P : Preset) (f : CFork) (bytes : List UInt8) : IO Unit := do
  match (Ssz.deserialize bytes : M (BeaconState P f)) with
  | .error e => IO.println s!"decode failed: {repr e}"
  | .ok s =>
    IO.println s!"validators: {s.validators.toArray.size}"
    timeIt "hash_tree_root(state)" (fun (st : BeaconState P f) => (Ssz.hashTreeRoot st : Root)) s toString
    timeIt "serialize(state)" (fun (st : BeaconState P f) => (Ssz.serialize st).length) s toString
    timeIt "process_slot" processSlot s (fun r => toString r.toBool)

def main (args : List String) : IO UInt32 := do
  match args with
  | [p, f, file] =>
    let some P := Preset.ofName? p | IO.eprintln "preset"; return 2
    let raw ← IO.FS.readBinFile file
    let some bytes := (Harness.Snappy.decompress raw).toOption | IO.eprintln "snappy"; return 2
    match f with
    | "deneb" => bench P .deneb bytes.toList
    | "electra" => bench P .electra bytes.toList
    | "fulu" => bench P .fulu bytes.toList
    | _ => IO.eprintln "fork"; return 2
    return 0
  | _ => IO.eprintln "usage"; return 2
