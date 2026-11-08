import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Snappy
import JauneConsensus.Harness.ConfigOverride
import JauneConsensus.Upgrade

/-!
# State-transition case handlers (harness only)

Handlers for the runners that drive the state transition and the fork upgrades
(`tests/formats/forks/README.md` first; `sanity`, `finality`, `random` and `transition` as the
block and epoch processing land). Handlers return `Except String Unit` (the runner maps it to a verdict). A post-state is compared by its full SSZ serialization, which
fixes its hash-tree-root too.
-/

namespace JauneConsensus.Harness

open Jaune Yaml

private def readYamlFile (c : Case) (f : String) : IO (Except YamlError YVal) := do
  pure (parse (← IO.FS.readBinFile (c.dir / f)))

private def readSnappy (c : Case) (f : String) : IO (Except String (List UInt8)) := do
  match Snappy.decompress (← IO.FS.readBinFile (c.dir / f)) with
  | .ok b => pure (.ok b.toList)
  | .error e => pure (.error s!"{f}: snappy: {e}")

/-- Decode, transform, and compare the result's serialization with `post`. -/
private def checkUpgrade {α β : Type} [Ssz α] [Ssz β] (pre post : List UInt8)
    (upgrade : α → M β) : String ⊕ Unit :=
  match (Ssz.deserialize pre : M α) with
  | .error e => .inl s!"pre does not decode: {repr e}"
  | .ok s =>
    match upgrade s with
    | .error e => .inl s!"upgrade rejected: {repr e}"
    | .ok s' =>
      if Ssz.serialize s' == post then .inr ()
      else
        match (Ssz.deserialize post : M β) with
        | .ok p => .inl s!"post-state differs (root {Ssz.hashTreeRoot s'} vs {Ssz.hashTreeRoot p})"
        | .error e => .inl s!"post-state differs and post does not decode: {repr e}"

/-- `fork/fork` (`tests/formats/forks/README.md`): `meta.yaml` names the fork transitioned to
(it must be the case's fork); `pre` is the previous fork's `BeaconState`, `post` the result of
that fork's upgrade function. `config` is the case's configuration (base preset plus any
`config.yaml`). -/
def forkCase (config : Case → IO (Except ConfigError Config)) (c : Case) : IO (Except String Unit) := do
  if c.files != ["meta.yaml", "post.ssz_snappy", "pre.ssz_snappy"] then
    return .error s!"unexpected files {c.files}"
  let some P := Preset.ofName? c.preset | return .error s!"no preset {c.preset}"
  let cfg ← match ← config c with
    | .ok cfg => pure cfg
    | .error e => return .error s!"config: {e}"
  let target ← match ← readYamlFile c "meta.yaml" with
    | .ok m => match m.field "fork" with
      | .ok (.scalar s _) => pure s
      | _ => return .error "meta.yaml: no fork"
    | .error e => return .error s!"meta.yaml: {e}"
  if target != c.key.fork then return .error s!"meta fork {target} is not the case fork {c.key.fork}"
  let pre ← match ← readSnappy c "pre.ssz_snappy" with
    | .ok b => pure b
    | .error e => return .error e
  let post ← match ← readSnappy c "post.ssz_snappy" with
    | .ok b => pure b
    | .error e => return .error e
  let r : String ⊕ Unit ← match target with
    | "electra" => pure (checkUpgrade (α := BeaconState P .deneb) pre post (upgradeToElectra cfg))
    | "fulu" => pure (checkUpgrade (α := BeaconState P .electra) pre post (upgradeToFulu cfg))
    | t => return .error s!"fork {t}: no upgrade in scope"
  match r with
  | .inr () => pure (.ok ())
  | .inl why => pure (.error why)

end JauneConsensus.Harness
