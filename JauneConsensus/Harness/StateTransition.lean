import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Snappy
import JauneConsensus.Harness.ConfigOverride
import JauneConsensus.Upgrade
import JauneConsensus.Transition

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

/-! ## Block and slot sequences

`sanity/slots`, `sanity/blocks`, `finality/finality`, `random/random` and `transition/core`
drive `process_slots` and `state_transition` with the fork's `process_epoch` and
`process_block`, given here as `Steps` so the handlers do not depend on how those are
assembled. -/

/-- The per-fork processing functions a run needs, with the configuration and the BLS switch. -/
structure Steps where
  processEpoch : (P : Preset) → (f : CFork) → Config → Bool → BeaconState P f → M (BeaconState P f)
  processBlock : (P : Preset) → (f : CFork) → Config → Bool → BeaconState P f → BeaconBlock P f →
    M (BeaconState P f)

/-- The `meta.yaml` mapping, or an empty mapping when the case has none. -/
private def readMeta (c : Case) : IO (Except String YVal) := do
  if !c.has "meta.yaml" then return .ok (.map [])
  match ← readYamlFile c "meta.yaml" with
  | .ok m => pure (.ok m)
  | .error e => pure (.error s!"meta.yaml: {e}")

private def metaNat? (m : YVal) (k : String) : Except String (Option Nat) :=
  match m.get? k with
  | none => .ok none
  | some v => match v.asNat with
    | .ok n => .ok (some n)
    | .error e => .error s!"meta.yaml {k}: {e}"

/-- `bls_setting` (`tests/formats/README.md`): 0 BLS may be on or off, 1 required, 2 ignored.
The model verifies under 0 and 1. -/
private def blsActive (m : YVal) : Except String Bool := do
  match ← metaNat? m "bls_setting" with
  | none | some 0 | some 1 => pure true
  | some 2 => pure false
  | some n => throw s!"bls_setting {n}"

private def decodeFile {α : Type} [Ssz α] (c : Case) (f : String) : IO (Except String α) := do
  match ← readSnappy c f with
  | .error e => pure (.error e)
  | .ok b => match (Ssz.deserialize b : M α) with
    | .ok x => pure (.ok x)
    | .error e => pure (.error s!"{f} does not decode: {repr e}")

/-- Compare a computed post-state with `post.ssz_snappy`. -/
private def comparePost {P : Preset} {f : CFork} (c : Case) (s : BeaconState P f) :
    IO (Except String Unit) := do
  match ← readSnappy c "post.ssz_snappy" with
  | .error e => pure (.error e)
  | .ok post =>
    if Ssz.serialize s == post then pure (.ok ())
    else match (Ssz.deserialize post : M (BeaconState P f)) with
      | .ok p => pure (.error s!"post-state differs (slot {s.slot} vs {p.slot}, root {Ssz.hashTreeRoot s} vs {Ssz.hashTreeRoot p})")
      | .error e => pure (.error s!"post-state differs and post does not decode: {repr e}")

/-- Expect `run` to reject when the case has no `post`, and to equal `post` otherwise. -/
private def verdictOf {P : Preset} {f : CFork} (c : Case) (r : M (BeaconState P f)) :
    IO (Except String Unit) := do
  match r, c.has "post.ssz_snappy" with
  | .ok s, true => comparePost c s
  | .ok _, false => pure (.error "expected a rejection (no post state), but the transition succeeded")
  | .error e, true => pure (.error s!"transition rejected: {repr e}")
  | .error _, false => pure (.ok ())

/-- `process_slots` with `steps`. -/
def runSlots (steps : Steps) (P : Preset) (f : CFork) (cfg : Config) (bls : Bool)
    (state : BeaconState P f) (slot : Slot) : M (BeaconState P f) :=
  processSlotsWith (steps.processEpoch P f cfg bls) state slot

/-- `state_transition` over a sequence of signed blocks, with `steps`. -/
def runBlocks (steps : Steps) (P : Preset) (f : CFork) (cfg : Config) (bls : Bool)
    (state : BeaconState P f) (blocks : List (SignedBeaconBlock P f)) : M (BeaconState P f) :=
  blocks.foldlM (fun s b =>
    stateTransitionWith (steps.processEpoch P f cfg bls) (steps.processBlock P f cfg bls) bls s b)
    state

private def withPF (c : Case) (k : Preset → CFork → IO (Except String Unit)) :
    IO (Except String Unit) := do
  let some P := Preset.ofName? c.preset | return .error s!"no preset {c.preset}"
  let some f := CFork.ofName? c.key.fork | return .error s!"no fork {c.key.fork}"
  k P f

/-- `sanity/slots` (`tests/formats/sanity/slots.md`): `process_slots(pre, pre.slot + slots)`. -/
def sanitySlotsCase (steps : Steps) (config : Case → IO (Except ConfigError Config)) (c : Case) :
    IO (Except String Unit) := withPF c fun P f => do
  let cfg ← match ← config c with | .ok x => pure x | .error e => return .error s!"config: {e}"
  let m ← match ← readMeta c with | .ok m => pure m | .error e => return .error e
  let bls ← match blsActive m with | .ok b => pure b | .error e => return .error e
  let n ← match ← readYamlFile c "slots.yaml" with
    | .ok v => match v.asNat with | .ok n => pure n | .error e => return .error s!"slots.yaml: {e}"
    | .error e => return .error s!"slots.yaml: {e}"
  let pre ← match ← decodeFile (α := BeaconState P f) c "pre.ssz_snappy" with
    | .ok s => pure s | .error e => return .error e
  verdictOf c (do
    let target ← U64.add? pre.slot (← U64.ofNat? n "slots") "pre.slot + slots"
    runSlots steps P f cfg bls pre target)

/-- The signed blocks `blocks_0 .. blocks_{n-1}` of a case, decoded at fork `f`. -/
private def readBlocks (P : Preset) (f : CFork) (c : Case) (lo hi : Nat) :
    IO (Except String (List (SignedBeaconBlock P f))) := do
  let mut out := #[]
  for i in [lo:hi] do
    match ← decodeFile (α := SignedBeaconBlock P f) c s!"blocks_{i}.ssz_snappy" with
    | .ok b => out := out.push b
    | .error e => return .error e
  pure (.ok out.toList)

/-- `sanity/blocks`, `finality/finality`, `random/random` (`tests/formats/sanity/blocks.md`):
`state_transition` for each block in order; no `post` means the sequence must be rejected. -/
def blocksCase (steps : Steps) (config : Case → IO (Except ConfigError Config)) (c : Case) :
    IO (Except String Unit) := withPF c fun P f => do
  let cfg ← match ← config c with | .ok x => pure x | .error e => return .error s!"config: {e}"
  let m ← match ← readMeta c with | .ok m => pure m | .error e => return .error e
  let bls ← match blsActive m with | .ok b => pure b | .error e => return .error e
  let n ← match metaNat? m "blocks_count" with
    | .ok (some n) => pure n | .ok none => return .error "meta.yaml: no blocks_count"
    | .error e => return .error e
  let pre ← match ← decodeFile (α := BeaconState P f) c "pre.ssz_snappy" with
    | .ok s => pure s | .error e => return .error e
  let blocks ← match ← readBlocks P f c 0 n with | .ok bs => pure bs | .error e => return .error e
  verdictOf c (runBlocks steps P f cfg bls pre blocks)

/-- Advance `state` to the first slot of `forkEpoch` with the pre-fork `process_slots` (when it
is not there already), as the generators' `transition_until_fork` and `do_fork` do. -/
private def toForkSlot (steps : Steps) (P : Preset) (f : CFork) (cfg : Config) (bls : Bool)
    (state : BeaconState P f) (forkEpoch : Nat) : M (BeaconState P f) := do
  let forkSlot ← U64.ofNat? (forkEpoch * P.SLOTS_PER_EPOCH) "fork slot"
  if state.slot < forkSlot then runSlots steps P f cfg bls state forkSlot else pure state

/-- `transition/core` (`tests/formats/transition/README.md`): blocks up to `fork_block` (all
of them when it is absent, none when the first block is post-fork) run on the initial fork;
the state then crosses to the first slot of `fork_epoch` on the initial fork, is upgraded,
and the remaining blocks run on the post fork. -/
def transitionCase (steps : Steps) (config : Case → IO (Except ConfigError Config)) (c : Case) :
    IO (Except String Unit) := do
  let some P := Preset.ofName? c.preset | return .error s!"no preset {c.preset}"
  let cfg ← match ← config c with | .ok x => pure x | .error e => return .error s!"config: {e}"
  let m ← match ← readMeta c with | .ok m => pure m | .error e => return .error e
  let bls ← match blsActive m with | .ok b => pure b | .error e => return .error e
  let postFork ← match m.get? "post_fork" with
    | some (.scalar s _) => pure s | _ => return .error "meta.yaml: no post_fork"
  if postFork != c.key.fork then return .error s!"post_fork {postFork} is not the case fork"
  let some forkEpoch := (metaNat? m "fork_epoch").toOption.join | return .error "meta.yaml: no fork_epoch"
  let some n := (metaNat? m "blocks_count").toOption.join | return .error "meta.yaml: no blocks_count"
  let forkBlock? ← match metaNat? m "fork_block" with
    | .ok x => pure x | .error e => return .error e
  -- blocks [0, split) are pre-fork, [split, n) post-fork
  let split := match forkBlock? with | some k => k + 1 | none => 0
  match postFork with
  | "electra" =>
    let pre ← match ← decodeFile (α := BeaconState P .deneb) c "pre.ssz_snappy" with
      | .ok s => pure s | .error e => return .error e
    let preBlocks ← match ← readBlocks P .deneb c 0 split with | .ok b => pure b | .error e => return .error e
    let postBlocks ← match ← readBlocks P .electra c split n with | .ok b => pure b | .error e => return .error e
    verdictOf c (do
      let s ← runBlocks steps P .deneb cfg bls pre preBlocks
      let s ← toForkSlot steps P .deneb cfg bls s forkEpoch
      let s ← upgradeToElectra cfg s
      runBlocks steps P .electra cfg bls s postBlocks)
  | "fulu" =>
    let pre ← match ← decodeFile (α := BeaconState P .electra) c "pre.ssz_snappy" with
      | .ok s => pure s | .error e => return .error e
    let preBlocks ← match ← readBlocks P .electra c 0 split with | .ok b => pure b | .error e => return .error e
    let postBlocks ← match ← readBlocks P .fulu c split n with | .ok b => pure b | .error e => return .error e
    verdictOf c (do
      let s ← runBlocks steps P .electra cfg bls pre preBlocks
      let s ← toForkSlot steps P .electra cfg bls s forkEpoch
      let s ← upgradeToFulu cfg s
      runBlocks steps P .fulu cfg bls s postBlocks)
  | t => pure (.error s!"post_fork {t}: no upgrade in scope")

end JauneConsensus.Harness
