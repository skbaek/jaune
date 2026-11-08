import JauneConsensus.Harness.Runner

/-!
# `jaune-consensus`: the consensus conformance runner

```
lake exe jaune-consensus run  --preset P [--fork F] [--runner R] [--handler H] [--suite S]
                              [--tier smoke|full] [--vectors DIR] [--manifest-dir DIR]
lake exe jaune-consensus scan --preset P [selection as above]     reader scans (Snappy, YAML)
lake exe jaune-consensus --forks                                  cross-layer fork pairing
lake exe jaune-consensus --fork-rules NAME                        resolve one fork (Gloas refused)
```

`--vectors` is the extracted release (default `$HOME/consensus-spec-tests-v1.6.1/extracted`),
holding `<preset>/tests/<preset>/...`. `--manifest-dir` holds `consensus-vectors.json` and
`consensus/inventory-v1.6.1.json` (default `scripts`, so run from the repository root).

Exit status: 0 only when the selection passes every check and every executed case is `PASS`;
1 on any refusal or failure; 2 on a usage error.
-/

open JauneConsensus.Harness

structure Opts where
  cmd : String := ""
  preset : Option String := none
  fork : Option String := none
  runner : Option String := none
  handler : Option String := none
  suite : Option String := none
  tier : Tier := .full
  vectors : Option String := none
  manifestDir : String := "scripts"

def usage : String :=
  "usage: jaune-consensus run|scan --preset P [--fork F] [--runner R] [--handler H] [--suite S] " ++
  "[--tier smoke|full] [--vectors DIR] [--manifest-dir DIR]\n       jaune-consensus --forks\n       jaune-consensus --fork-rules NAME"

def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--preset" :: v :: r, o => parseOpts r { o with preset := some v }
  | "--fork" :: v :: r, o => parseOpts r { o with fork := some v }
  | "--runner" :: v :: r, o => parseOpts r { o with runner := some v }
  | "--handler" :: v :: r, o => parseOpts r { o with handler := some v }
  | "--suite" :: v :: r, o => parseOpts r { o with suite := some v }
  | "--vectors" :: v :: r, o => parseOpts r { o with vectors := some v }
  | "--manifest-dir" :: v :: r, o => parseOpts r { o with manifestDir := v }
  | "--tier" :: "smoke" :: r, o => parseOpts r { o with tier := .smoke }
  | "--tier" :: "full" :: r, o => parseOpts r { o with tier := .full }
  | a :: _, _ => .error s!"unknown or incomplete argument {a}"

def loadSelection (o : Opts) : IO (Manifest × Selection) := do
  let some preset := o.preset | throw (IO.userError "refused: --preset is required")
  let root ← match o.vectors with
    | some v => pure (System.FilePath.mk v)
    | none =>
      match ← IO.getEnv "HOME" with
      | some h => pure (System.FilePath.mk h / "consensus-spec-tests-v1.6.1" / "extracted")
      | none => throw (IO.userError "refused: no --vectors and no HOME")
  let md := System.FilePath.mk o.manifestDir
  let prov ← IO.FS.readFile (md / "consensus-vectors.json")
  let inv ← IO.FS.readFile (md / "consensus" / "inventory-v1.6.1.json")
  let m ← IO.ofExcept ((Manifest.load prov inv).mapError IO.userError)
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

def main (args : List String) : IO UInt32 := do
  match args with
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
      | _ =>
        IO.eprintln usage
        pure 2
    catch e =>
      IO.println s!"jaune-consensus: {e}"
      pure 1
