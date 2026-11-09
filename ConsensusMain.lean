import JauneConsensus.Harness.Runner
import JauneConsensus.Harness.RecordedPairs
import JauneConsensus.Harness.RecordedPairsGloas
import JauneConsensus.Crypto.Sha256Pair

/-!
# `jaune-consensus`: the consensus conformance runner

```
lake exe jaune-consensus run  --preset P [--fork F] [--runner R] [--handler H] [--suite S]
                              [--tier smoke|full] [--vectors DIR] [--manifest-dir DIR]
lake exe jaune-consensus scan --preset P [selection as above]     reader scans (Snappy, YAML)
lake exe jaune-consensus --forks                                  cross-layer fork pairing
lake exe jaune-consensus --fork-rules NAME                        resolve one fork (Gloas refused)
lake exe jaune-consensus recorded-pairs [--dir DIR] [--negative-control]
lake exe jaune-consensus recorded-pairs-gloas [--dir DIR]          Gloas devnet pairs, control built in
```

`--vectors` is the extracted release, holding `<preset>/tests/<preset>/...` (default
`$HOME/consensus-spec-tests-v1.7.0-beta.4/extracted`, and for `--preset general`
`$HOME/consensus-spec-tests-v1.6.1/extracted`, the general-only provenance entry).
`--manifest-dir` holds `consensus-vectors.json` and `consensus/inventory-v1.7.0-beta.4.json`
(default `scripts`, so run from the repository root).

Exit status: 0 only when the selection passes every check and every executed case is `PASS`;
1 on any refusal or failure; 2 on a usage error.
-/

open JauneConsensus.Harness

/-- Why the command line was not understood. -/
inductive UsageError where
  | unknownArgument (arg : String)

instance : ToString UsageError where
  toString | .unknownArgument a => s!"unknown or incomplete argument {a}"

structure Opts where
  cmd : String := ""
  preset : Option DirName := none
  fork : Option DirName := none
  runner : Option DirName := none
  handler : Option DirName := none
  suite : Option DirName := none
  tier : Tier := .full
  vectors : Option System.FilePath := none
  manifestDir : String := "scripts"
  dir : Option System.FilePath := none
  negativeControl : Bool := false

def usage : String :=
  "usage: jaune-consensus run|scan --preset P [--fork F] [--runner R] [--handler H] [--suite S] " ++
  "[--tier smoke|full] [--vectors DIR] [--manifest-dir DIR]\n       jaune-consensus --forks\n       jaune-consensus --fork-rules NAME\n       jaune-consensus recorded-pairs [--dir DIR] [--negative-control]\n       jaune-consensus recorded-pairs-gloas [--dir DIR]"

def parseOpts : List String → Opts → Except UsageError Opts
  | [], o => .ok o
  | "--preset" :: v :: r, o => parseOpts r { o with preset := some v }
  | "--fork" :: v :: r, o => parseOpts r { o with fork := some v }
  | "--runner" :: v :: r, o => parseOpts r { o with runner := some v }
  | "--handler" :: v :: r, o => parseOpts r { o with handler := some v }
  | "--suite" :: v :: r, o => parseOpts r { o with suite := some v }
  | "--vectors" :: v :: r, o => parseOpts r { o with vectors := some (System.FilePath.mk v) }
  | "--manifest-dir" :: v :: r, o => parseOpts r { o with manifestDir := v }
  | "--dir" :: v :: r, o => parseOpts r { o with dir := some (System.FilePath.mk v) }
  | "--negative-control" :: r, o => parseOpts r { o with negativeControl := true }
  | "--tier" :: "smoke" :: r, o => parseOpts r { o with tier := .smoke }
  | "--tier" :: "full" :: r, o => parseOpts r { o with tier := .full }
  | a :: _, _ => .error (.unknownArgument a)

def loadSelection (o : Opts) : IO (Manifest × Selection) := do
  let some preset := o.preset | throw (IO.userError "refused: --preset is required")
  let root ← match o.vectors with
    | some v => pure v
    | none =>
      match ← IO.getEnv "HOME" with
      | some h => pure (System.FilePath.mk h / defaultVectorsDir preset / "extracted")
      | none => throw (IO.userError "refused: no --vectors and no HOME")
  let md := System.FilePath.mk o.manifestDir
  let prov ← IO.FS.readFile (md / "consensus-vectors.json")
  let inv ← IO.FS.readFile (md / "consensus" / inventoryFile)
  let m ← IO.ofExcept ((Manifest.load prov inv).mapError (IO.userError ∘ toString))
  pure (m, { root, preset, fork := o.fork, runner := o.runner, handler := o.handler,
             suite := o.suite, tier := o.tier })

def cmdRun (o : Opts) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let (m, sel) ← loadSelection o
  let all ← discover m sel
  let todo := tierCases sel.tier all
  IO.println s!"jaune-consensus: release {m.release} ({m.tagCommit}), preset {sel.preset}, \
    {all.length} cases checked against the manifest, {todo.length} to run \
    ({if sel.tier == .smoke then "smoke" else "full"} tier)"
  let mut pass := 0
  let mut fail := 0
  for c in todo do
    match ← runCase c with
    | .pass => pass := pass + 1
    | .fail why =>
      fail := fail + 1
      IO.println s!"FAIL {c.render}: {why}"
  let t1 ← IO.monoMsNow
  IO.println s!"jaune-consensus: PASS {pass}, FAIL {fail}, of {todo.length} in {t1 - t0} ms"
  if fail == 0 && pass == todo.length && pass > 0 then
    IO.println "jaune-consensus: OK"
    pure 0
  else
    IO.println "jaune-consensus: FAILED"
    pure 1

def cmdScan (o : Opts) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let (m, sel) ← loadSelection o
  let all ← discover m sel
  let (ns, bs) ← snappyScan all
  let (ny, by_) ← yamlScan all
  let (nu, bu) ← snappyUintOracle all
  let (nc, bc) ← configScan all
  for b in bs ++ by_ ++ bu ++ bc do IO.println s!"FAIL {b}"
  let t1 ← IO.monoMsNow
  IO.println s!"jaune-consensus scan: {all.length} cases; snappy {ns - bs.length}/{ns} decoded; \
    yaml {ny - by_.length}/{ny} parsed; uint oracle {nu - bu.length}/{nu}; config overrides {nc - bc.length}/{nc}; {t1 - t0} ms"
  if bs.isEmpty && by_.isEmpty && bu.isEmpty && bc.isEmpty then
    IO.println "jaune-consensus scan: OK"
    pure 0
  else
    IO.println "jaune-consensus scan: FAILED"
    pure 1

/-- `--forks`: the cross-layer pairing (outcome O7). `--fork-rules NAME`: resolve one consensus
fork through `CFork.resolve`, failing closed for Gloas, `eip7805` and unknown names. -/
def cmdForks : IO UInt32 := do
  for l in JauneConsensus.pairingTable do IO.println l
  pure 0

def cmdForkRules (n : String) : IO UInt32 := do
  match JauneConsensus.CFork.resolve n with
  | .ok d =>
    IO.println s!"{d.fork}: execution {d.blobs.map (·.1)}, max blobs {d.blobs.map (·.2)}, \
      request types {d.requestTypes.map (·.toNat)}"
    pure 0
  | .error e =>
    IO.println s!"jaune-consensus: {e}"
    pure 1

/-- `--bench-hash-pair N`: time `N` pair hashes three ways (Jaune's `Bytes.sha256` on the
64-byte list, `hashPairKernel`, `hashPair`) over the same pseudo-random inputs, and check that
all three agree on every input (a differential run beside `hashPair_eq`). -/
def cmdBenchHashPair (n : Nat) : IO UInt32 := do
  let inputs : Array (Jaune.B256 × Jaune.B256) := (Array.range n).map fun k =>
    (Jaune.Nat.toB256 (k * 0x9e3779b97f4a7c15f39cc0605cedc834 + k ^ 5 + 17),
     Jaune.Nat.toB256 ((k + 7) * 0xc2b2ae3d27d4eb4f165667b19e3779f9 + k ^ 3))
  let time (name : String) (f : Jaune.B256 → Jaune.B256 → Jaune.B256) :
      IO (Array (List UInt8)) := do
    let t0 ← IO.monoNanosNow
    let mut acc : UInt8 := 0
    let mut outs := #[]
    for (a, b) in inputs do
      let h := (f a b).toBytes
      acc := acc ^^^ h.headD 0
      outs := outs.push h
    let t1 ← IO.monoNanosNow
    let per := (t1 - t0).toFloat / n.toFloat / 1000.0
    IO.println s!"{name}: {n} pairs in {(t1 - t0) / 1000000} ms, {per} us/pair (checksum {acc})"
    pure outs
  let _ ← time "baseline (output bytes only, no hash)" (fun a b => if a.toBytes.length == 0 then b else a)
  let _ ← time "input list a.toBytes ++ b.toBytes only" (fun a b => if (a.toBytes ++ b.toBytes).length == 0 then b else a)
  let r0 ← time "Bytes.sha256 (a ++ b)" (fun a b => Jaune.Bytes.sha256 (a.toBytes ++ b.toBytes))
  let r1 ← time "hashPairKernel" JauneConsensus.Crypto.hashPairKernel
  let r2 ← time "hashPair" JauneConsensus.Crypto.hashPair
  if r0 == r1 && r1 == r2 then
    IO.println s!"bench-hash-pair: all three agree on {n} inputs"
    pure 0
  else
    IO.println "bench-hash-pair: DISAGREEMENT"
    pure 1

/-- `--bench-state-root FILE`: time decoding, serializing and hashing a mainnet Electra
`BeaconState` (`FILE` is a `pre.ssz_snappy`), and the roots of its largest fields. -/
def cmdBenchStateRoot (file : String) : IO UInt32 := do
  let raw ← IO.FS.readBinFile file
  let .ok bytes := JauneConsensus.Harness.Snappy.decompress raw
    | IO.println "bench-state-root: snappy failed"; return 1
  let bs := bytes.toList
  let t0 ← IO.monoMsNow
  let .ok (s : JauneConsensus.BeaconState .mainnet .electra) := (JauneConsensus.deserialize bs : JauneConsensus.M _)
    | IO.println "bench-state-root: decode failed"; return 1
  let t1 ← IO.monoMsNow
  let ser := JauneConsensus.serialize s
  let t2 ← IO.monoMsNow
  let r := JauneConsensus.hashTreeRoot s
  let t3 ← IO.monoMsNow
  let r1 := JauneConsensus.hashTreeRoot s.randao_mixes
  let t4 ← IO.monoMsNow
  let r2 := JauneConsensus.hashTreeRoot s.block_roots
  let t5 ← IO.monoMsNow
  let r3 := JauneConsensus.hashTreeRoot s.validators
  let t6 ← IO.monoMsNow
  let r4 := JauneConsensus.hashTreeRoot s.slashings
  let t7 ← IO.monoMsNow
  let rm := JauneConsensus.serialize s.randao_mixes
  let vs := JauneConsensus.serialize s.validators
  let t8 ← IO.monoMsNow
  let .ok (_ : JauneConsensus.SszVector JauneConsensus.Bytes32 65536) := (JauneConsensus.deserialize rm : JauneConsensus.M _)
    | IO.println "randao decode failed"; return 1
  let t9 ← IO.monoMsNow
  let .ok (_ : JauneConsensus.SszList JauneConsensus.Validator 1099511627776) := (JauneConsensus.deserialize vs : JauneConsensus.M _)
    | IO.println "validators decode failed"; return 1
  let t10 ← IO.monoMsNow
  let _ := JauneConsensus.serialize s.randao_mixes
  let t11 ← IO.monoMsNow
  IO.println s!"decode randao_mixes {t9-t8} ms ({rm.length} bytes), validators {t10-t9} ms ({vs.length} bytes); serialize randao_mixes {t11-t10} ms"
  IO.println s!"bytes {bs.length} ser {ser.length} root {r} {r1} {r2} {r3} {r4}"
  IO.println s!"decode {t1-t0} ms, serialize {t2-t1} ms, hash_tree_root {t3-t2} ms; randao_mixes {t4-t3}, block_roots {t5-t4}, validators {t6-t5}, slashings {t7-t6}"
  pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--bench-hash-pair", k] =>
    match k.toNat? with
    | some n => return (← cmdBenchHashPair n)
    | none => IO.eprintln usage; return 2
  | ["--bench-state-root", f] => return (← cmdBenchStateRoot f)
  | ["--forks"] => return (← cmdForks)
  | ["--fork-rules", n] => return (← cmdForkRules n)
  | _ => pure ()
  let (cmd, rest) := match args with
    | c :: r => (c, r)
    | [] => ("", [])
  match parseOpts rest {} with
  | .error e =>
    IO.eprintln s!"{e}\n{usage}"
    pure 2
  | .ok o =>
    try
      match cmd with
      | "run" => cmdRun o
      | "scan" => cmdScan o
      | "recorded-pairs" =>
        let dir := match o.dir with
          | some d => d
          | none => System.FilePath.mk "scripts/consensus/recorded-pairs"
        cmdRecordedPairs dir o.negativeControl
      | "recorded-pairs-gloas" =>
        let dir := match o.dir with
          | some d => d
          | none => System.FilePath.mk "scripts/consensus/recorded-devnet8"
        RecordedGloas.cmdRecordedPairsGloas dir
      | _ =>
        IO.eprintln usage
        pure 2
    catch e =>
      IO.println s!"jaune-consensus: {e}"
      pure 1
