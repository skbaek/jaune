import JauneConsensus.Harness.EpochCases
import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Snappy
import JauneConsensus.Shuffle
import JauneConsensus.Harness.ConfigOverride
import JauneConsensus.Harness.SszGenericTypes
import JauneConsensus.Harness.SszStatic
import JauneConsensus.Harness.Operations
import JauneConsensus.Harness.Networking
import JauneConsensus.Harness.LightClientCases
import JauneConsensus.Crypto.Boundary
import JauneConsensus.Harness.StateTransition
import JauneConsensus.Harness.KzgCases
import JauneConsensus.Block
import JauneConsensus.Harness.ForkChoiceCases

/-!
# Case handlers and strict verdicts (conformance harness)

Each `(runner, handler)` pair the goal has brought up maps to a handler that reads one case
directory and returns `PASS` or a failure reason. A pair with no handler is a failure
(`UNIMPLEMENTED`), never a skip: verdicts are strict all-PASS with no expected-failure allowance.
-/

namespace JauneConsensus.Harness

open Jaune Yaml

inductive Verdict
  | pass
  | fail (why : String)
  deriving BEq, Repr

private def readYaml (c : Case) (f : String) : IO (Except YamlError YVal) := do
  pure (parse (← IO.FS.readBinFile (c.dir / f)))

/-- A `Bytes32` read from a vector: exactly 32 bytes. -/
def b256OfBytes (bs : List UInt8) : Except YamlError B256 :=
  if bs.length == 32 then .ok (B256.ofBytes bs)
  else .error (.shape s!"expected 32 bytes, got {bs.length}")

/-- `shuffling/core` (`tests/formats/shuffling/README.md`): for every `i < count`,
`compute_shuffled_index(i, count, seed) == mapping[i]`, and `mapping` has exactly `count`
entries. -/
def shufflingCore (c : Case) : IO Verdict := do
  let some P := Preset.ofName? c.preset
    | return .fail s!"no preset {c.preset}"
  if c.files != ["mapping.yaml"] then return .fail s!"unexpected files {c.files}"
  let doc ← readYaml c "mapping.yaml"
  let r : Except YamlError Verdict := do
    let v ← doc
    v.expectKeys ["seed", "count", "mapping"]
    let seed ← b256OfBytes (← (← v.field "seed").asHex)
    let count ← (← v.field "count").asNat
    let mapping ← (← (← v.field "mapping").asSeq).mapM YVal.asNat
    if mapping.length != count then
      return .fail s!"mapping has {mapping.length} entries, count is {count}"
    let toU64 (n : Nat) : Except YamlError U64 :=
      (U64.ofNat? n "vector uint64").mapError (fun e => .shape s!"{repr e}")
    let countU ← toU64 count
    let mut i := 0
    for want in mapping do
      match computeShuffledIndex P (← toU64 i) countU seed with
      | .ok got =>
        if got.toNat != want then return .fail s!"index {i}: computed {got}, expected {want}"
      | .error e => return .fail s!"index {i}: rejected: {repr e}"
      i := i + 1
    pure .pass
  match r with
  | .ok v => pure v
  | .error e => pure (.fail (toString e))

/-- `ssz_generic/<handler>` (`tests/formats/ssz_generic/README.md`): the SSZ type comes from the
case name; a `valid` case must decode, equal `value.yaml`, re-encode to `serialized` and have the
`meta.yaml` root; an `invalid` case must fail to decode. The checks run the library's `Ssz`
instances (`Harness/SszGeneric.lean`). -/
def sszGenericCase (c : Case) : IO Verdict := do
  let want := if c.key.suite == "valid" then ["meta.yaml", "serialized.ssz_snappy", "value.yaml"]
    else ["serialized.ssz_snappy"]
  if c.files != want then return .fail s!"unexpected files {c.files}"
  let some checks := typeOfCaseAll c.key.handler c.name
    | return .fail (CaseFail.unknownType c.name).render
  let ser ← match Snappy.decompress (← IO.FS.readBinFile (c.dir / "serialized.ssz_snappy")) with
    | .ok b => pure b.toList
    | .error e => return .fail (CaseFail.snappy e).render
  let r : Except CaseFail Unit ←
    if c.key.suite == "valid" then do
      let value ← readYaml c "value.yaml"
      let metaY ← readYaml c "meta.yaml"
      pure do
        let value ← value.mapError CaseFail.yaml
        let metaV ← metaY.mapError CaseFail.yaml
        metaV.expectKeys ["root"] |>.mapError CaseFail.yaml
        let rootBytes ← ((metaV.field "root").bind YVal.asHex).mapError CaseFail.yaml
        if rootBytes.length != 32 then throw (CaseFail.yaml (.shape "root is not 32 bytes"))
        checks.valid ser value (Bytes.toB256 rootBytes)
    else pure (checks.invalid ser)
  match r with
  | .ok () => pure .pass
  | .error e => pure (.fail e.render)

/-- `ssz_static/<Container>` (`tests/formats/ssz_static/core.md`): `serialized` decodes,
re-encodes to itself, equals `value.yaml`, and has the `roots.yaml` root, for the container at
the case's preset and fork (`Harness/SszStatic.lean`). -/
def sszStaticCase (c : Case) : IO Verdict := do
  if c.files != ["roots.yaml", "serialized.ssz_snappy", "value.yaml"] then
    return .fail s!"unexpected files {c.files}"
  let some P := Preset.ofName? c.preset | return .fail s!"no preset {c.preset}"
  let some f := CFork.ofName? c.key.fork | return .fail s!"no fork {c.key.fork}"
  let some checks := sszStaticChecks P f c.key.handler
    | return .fail (CaseFail.unknownType c.key.handler).render
  let ser ← match Snappy.decompress (← IO.FS.readBinFile (c.dir / "serialized.ssz_snappy")) with
    | .ok b => pure b.toList
    | .error e => return .fail (CaseFail.snappy e).render
  let value ← readYaml c "value.yaml"
  let roots ← readYaml c "roots.yaml"
  let r : Except CaseFail Unit := do
    let value ← value.mapError CaseFail.yaml
    let roots ← roots.mapError CaseFail.yaml
    roots.expectKeys ["root"] |>.mapError CaseFail.yaml
    let rootBytes ← ((roots.field "root").bind YVal.asHex).mapError CaseFail.yaml
    if rootBytes.length != 32 then throw (CaseFail.yaml (.shape "root is not 32 bytes"))
    checks.valid ser value (Bytes.toB256 rootBytes)
  match r with
  | .ok () => pure .pass
  | .error e => pure (.fail e.render)

/-- `bls/eth_aggregate_pubkeys` (`tests/formats/bls/eth_aggregate_pubkeys.md`): `input` is the
list of pubkeys; `output` is the aggregate, or `null` when pyspec raises. -/
def blsAggregatePubkeys (c : Case) : IO Verdict := do
  if c.files != ["data.yaml"] then return .fail s!"unexpected files {c.files}"
  let doc ← readYaml c "data.yaml"
  let r : Except YamlError Verdict := do
    let v ← doc
    v.expectKeys ["input", "output"]
    let pks ← (← (← v.field "input").asSeq).mapM YVal.asHex
    let out ← v.field "output"
    let got := ethAggregatePubkeysM pks
    if out.isNull then
      match got with
      | .error _ => pure .pass
      | .ok b => pure (.fail s!"expected a rejection, got {b.length} bytes")
    else
      let want ← out.asHex
      match got with
      | .ok b => pure (if b == want then .pass else .fail "aggregate differs")
      | .error e => pure (.fail s!"rejected: {repr e}")
  match r with
  | .ok v => pure v
  | .error e => pure (.fail (toString e))

/-- `bls/eth_fast_aggregate_verify` (`tests/formats/bls/eth_fast_aggregate_verify.md`). -/
def blsFastAggregateVerify (c : Case) : IO Verdict := do
  if c.files != ["data.yaml"] then return .fail s!"unexpected files {c.files}"
  let doc ← readYaml c "data.yaml"
  let r : Except YamlError Verdict := do
    let v ← doc
    v.expectKeys ["input", "output"]
    let i ← v.field "input"
    i.expectKeys ["pubkeys", "message", "signature"]
    let pks ← (← (← i.field "pubkeys").asSeq).mapM YVal.asHex
    let msg ← (← i.field "message").asHex
    let sig ← (← i.field "signature").asHex
    let want ← (← v.field "output").asBool
    let got := ethFastAggregateVerify pks msg sig
    pure (if got == want then .pass else .fail s!"verify gave {got}, expected {want}")
  match r with
  | .ok v => pure v
  | .error e => pure (.fail (toString e))

/-- The configuration a case runs under: the base `Config` of its preset, with the case's
`config.yaml` applied when it has one (`Config.applyOverrides`). -/
def caseConfig (c : Case) : IO (Except ConfigError Config) := do
  let some base := Config.ofPreset? c.preset
    | return .error (.presetBase c.preset "minimal or mainnet")
  if !c.has "config.yaml" then return .ok base
  let doc ← readYaml c "config.yaml"
  pure ((doc.mapError ConfigError.yaml).bind (base.applyOverrides ·))

private def overridden (y : String) : Option Config :=
  (((parseString y).mapError ConfigError.yaml).bind (Config.minimal.applyOverrides ·)).toOption

#guard (overridden "PRESET_BASE: 'minimal'\nALTAIR_FORK_EPOCH: 7\nBLOB_SCHEDULE:\n  - EPOCH: 1\n    MAX_BLOBS_PER_BLOCK: 9\n").map
  (fun c => (c.ALTAIR_FORK_EPOCH, c.BLOB_SCHEDULE, c.SLOT_DURATION_MS)) ==
  some (7, [⟨1, 9⟩], Config.minimal.SLOT_DURATION_MS)
#guard (overridden "PRESET_BASE: 'mainnet'\n").isNone
#guard (overridden "CONFIG_NAME: 'minimal'\n").isNone
#guard (overridden "HEZE_FORK_EPOCH: 0\n").isNone
#guard (overridden "ALTAIR_FORK_VERSION: 0x0100\n").isNone

/-- `operations/<handler>` (`Harness/Operations.lean`), under the case's configuration. -/
def operationsVerdict (c : Case) : IO Verdict := do
  match ← caseConfig c with
  | .error e => pure (.fail s!"config: {e}")
  | .ok cfg =>
    match ← operationsCase cfg c with
    | .ok () => pure .pass
    | .error e => pure (.fail e)

/-- The processing functions for the block and slot runners: A's `process_block` and C's
`process_epoch`. -/
def steps : Steps where
  processEpoch _ _ ctx state := processEpoch ctx state
  processBlock _ _ ctx state block := processBlock ctx state block

/-- A handler that reports `Except String Unit` as a verdict. -/
def ofResult (h : Case → IO (Except String Unit)) (c : Case) : IO Verdict := do
  match ← h c with
  | .ok () => pure .pass
  | .error why => pure (.fail why)

/-- `networking/<handler>` (`Harness/Networking.lean`), under the case's configuration. -/
def networkingVerdict (c : Case) : IO Verdict := do
  match ← caseConfig c with
  | .error e => pure (.fail s!"config: {e}")
  | .ok cfg =>
    match ← networkingCase cfg c with
    | .ok () => pure .pass
    | .error e => pure (.fail e)

/-- `light_client/<handler>` and `merkle_proof/<handler>` (`Harness/LightClientCases.lean`). -/
def lightClientVerdict (c : Case) : IO Verdict := do
  match ← caseConfig c with
  | .error e => pure (.fail s!"config: {e}")
  | .ok cfg =>
    match ← lightClientCase cfg c with
    | .ok () => pure .pass
    | .error e => pure (.fail e)

/-- The handler table. -/
def handlerFor (runner handler : String) : Option (Case → IO Verdict) :=
  match runner, handler with
  | "shuffling", "core" => some shufflingCore
  | "ssz_generic", _ => some sszGenericCase
  | "ssz_static", _ => some sszStaticCase
  | "rewards", _ => some fun c => do
    match ← rewardsCase c with
    | none => pure .pass
    | some why => pure (.fail why)
  | "epoch_processing", _ => some fun c => do
    -- `JAUNE_CONSENSUS_EPOCH_FULL=1` adds the diagnostic `pre_epoch → post_epoch` check
    let full := (← IO.getEnv "JAUNE_CONSENSUS_EPOCH_FULL") == some "1"
    match ← epochProcessingCase c full with
    | none => pure .pass
    | some why => pure (.fail why)
  | "operations", _ => some operationsVerdict
  | "networking", _ => some networkingVerdict
  | "light_client", _ => some lightClientVerdict
  | "merkle_proof", _ => some lightClientVerdict
  | "bls", "eth_aggregate_pubkeys" => some blsAggregatePubkeys
  | "bls", "eth_fast_aggregate_verify" => some blsFastAggregateVerify
  | "fork", "fork" => some (ofResult (forkCase caseConfig))
  | "kzg", _ => some (ofResult kzgCase)
  | "sanity", "slots" => some (ofResult (sanitySlotsCase steps caseConfig))
  | "sanity", "blocks" => some (ofResult (blocksCase steps caseConfig))
  | "finality", "finality" => some (ofResult (blocksCase steps caseConfig))
  | "random", "random" => some (ofResult (blocksCase steps caseConfig))
  | "transition", "core" => some (ofResult (transitionCase steps caseConfig))
  | "fork_choice", _ => some (ofResult (forkChoiceCase caseConfig .forkChoice))
  | "sync", "optimistic" => some (ofResult (forkChoiceCase caseConfig .sync))
  | "fast_confirmation", _ => some (ofResult (forkChoiceCase caseConfig .fastConfirmation))
  | _, _ => none

def runCase (c : Case) : IO Verdict := do
  match handlerFor c.key.runner c.key.handler with
  | none => pure (.fail s!"UNIMPLEMENTED: no handler for {c.key.runner}/{c.key.handler}")
  | some h =>
    try h c catch e => pure (.fail s!"error: {e}")

/-! ## Reader scans

Corpus-wide checks of the two readers over a selection: every `.ssz_snappy` decodes (its declared
length is met and every copy is in range) and every `.yaml` is inside the accepted subset. -/

def snappyScan (cs : List Case) : IO (Nat × List String) := do
  let mut n := 0
  let mut bad := []
  for c in cs do
    for f in c.files do
      if f.endsWith ".ssz_snappy" then
        n := n + 1
        match Snappy.decompress (← IO.FS.readBinFile (c.dir / f)) with
        | .ok _ => pure ()
        | .error e => bad := s!"{c.render}/{f}: {e}" :: bad
  pure (n, bad.reverse)

def yamlScan (cs : List Case) : IO (Nat × List String) := do
  let mut n := 0
  let mut bad := []
  for c in cs do
    for f in c.files do
      if f.endsWith ".yaml" then
        n := n + 1
        match parse (← IO.FS.readBinFile (c.dir / f)) with
        | .ok _ => pure ()
        | .error e => bad := s!"{c.render}/{f}: {e}" :: bad
  pure (n, bad.reverse)

/-- Every case `config.yaml` in the selection parses into `Config` over its preset's base.
Returns the number applied and the failures. -/
def configScan (cs : List Case) : IO (Nat × List String) := do
  let mut n := 0
  let mut bad := []
  for c in cs do
    if c.has "config.yaml" then
      n := n + 1
      match ← caseConfig c with
      | .ok _ => pure ()
      | .error e => bad := s!"{c.render}/config.yaml: {e}" :: bad
  pure (n, bad.reverse)

/-- An independent check of the Snappy decoder on real compressed files: for every
`ssz_generic/uints/valid` case (`uint_<bits>_...`), the decoded `serialized` must be the
`bits / 8`-byte little-endian encoding of the integer in `value.yaml` (`ssz/simple-serialize.md`,
`uintN`). Returns the number checked and the failures. -/
def snappyUintOracle (cs : List Case) : IO (Nat × List String) := do
  let mut n := 0
  let mut bad := []
  for c in cs do
    if c.key.runner != "ssz_generic" || c.key.handler != "uints" || c.key.suite != "valid" then
      continue
    let bits? := match c.name.splitOn "_" with
      | "uint" :: b :: _ => b.toNat?
      | _ => none
    match bits? with
    | none => bad := s!"{c.render}: unparsed case name" :: bad
    | some bits =>
    n := n + 1
    let dec := Snappy.decompress (← IO.FS.readBinFile (c.dir / "serialized.ssz_snappy"))
    -- integers wider than 64 bits are quoted strings in the vectors
    let val := (parse (← IO.FS.readBinFile (c.dir / "value.yaml"))).bind
      (if bits > 64 then YVal.asQuotedNat else YVal.asNat)
    match dec, val with
    | .ok out, .ok v =>
      if out.toList != JauneConsensus.uintToBytes (bits / 8) v || v ≥ 2 ^ bits then
        bad := s!"{c.render}: decoded bytes differ from value.yaml" :: bad
    | .error e, _ => bad := s!"{c.render}: {e}" :: bad
    | _, .error e => bad := s!"{c.render}: {e}" :: bad
  pure (n, bad.reverse)

end JauneConsensus.Harness
