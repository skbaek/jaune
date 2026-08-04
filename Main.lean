import «Jaune».Execution
import «Jaune».Sufficiency
import «Jaune».Transaction
import «Jaune».FixtureException
import «Jaune».ChainStore
import «Jaune».BLSGuards

open Jaune



----------------- JSON DECODING HELPERS ------------------

/-- Strip a mandatory `0x` prefix, or fail. This lives in the harness rather
than `Jaune/Basic.lean` because it is fixture-JSON syntax handling, not
library semantics, and its optional result is a parse channel that has no
business inside the semantic import closure. -/
def Option.remove0x (s : String) : Option String :=
  match s.toList with
  | '0' :: 'x' :: cs => return String.ofList cs
  | _ => .none

def Lean.Json.toIoList : Lean.Json → IO (List Json)
  | .arr a => return a.toList
  | _ => IO.throw "not an array"

def Lean.Json.toIoRBNode :
  Lean.Json → IO (Std.TreeMap.Raw String Json compare)
  | .obj r => return r
  | _ => IO.throw "not an object"

def Lean.Json.toString? : Lean.Json → Option String
  | .str s => some s
  | _ => none

def Lean.Json.toIoString : Lean.Json → IO String
  | .str s => return s
  | _ => IO.throw "not a string"

def Lean.Json.toIoBytes (j : Json) : IO Bytes := do
  let x ← toIoString j >>= .remove0x
  (Hex.toBytes x).toIO ""

def Lean.Json.toIoAdr (j : Json) : IO Adr := do
  let x ← toIoString j >>= .remove0x
  (Hex.toAdr? x).toIO ""

def Lean.Json.toIoB64 (j : Json) : IO UInt64 := do
  let x ← toIoString j >>= .remove0x
  (Hex.toUInt64? x).toIO

def Lean.Json.toB256? (j : Json) : Option B256 := do
  let x ← toString? j >>= .remove0x
  Hex.toB256? x

def Lean.Json.toIoB256 (j : Json) : IO B256 := do
  let x ← toIoString j >>= .remove0x
  (Hex.toB256? x).toIO ""

-- Fixture JSON quantities: any width up to the field's own, and no
-- leading-zero rule, because JSON quantity syntax is not RLP minimal-scalar
-- syntax. These replace a pair that converted through the raw
-- `Bytes.toUInt64` / `Bytes.toB256`, which pad short values and silently
-- *truncate* long ones -- so an over-wide prestate field used to become a
-- plausible in-range one with no error at all. `Bytes.toQuantityB64?` and
-- `Bytes.toQuantityB256?` accept exactly the same short values and reject the
-- over-long input; see the soundness theorems in `Jaune/Types.lean`.

def Lean.Json.toIoQuantityB64 (field : String) (j : Json) : IO UInt64 := do
  let x ← toIoString j >>= .remove0x
  let xs ← (Hex.toBytes x).toIO s!"error : {field} is not a hex byte string"
  (Bytes.toQuantityB64? xs).toIO
    s!"error : {field} is {xs.length} bytes wide, exceeding the 8-byte maximum"

def Lean.Json.toIoQuantityB256 (field : String) (j : Json) : IO B256 := do
  let x ← toIoString j >>= .remove0x
  let xs ← (Hex.toBytes x).toIO s!"error : {field} is not a hex byte string"
  (Bytes.toQuantityB256? xs).toIO
    s!"error : {field} is {xs.length} bytes wide, exceeding the 32-byte maximum"

/-- The same decoder for a quantity that arrives as a JSON *key* rather than a
value. The `0x` prefix stays mandatory, exactly as before. -/
def Hex.toIoQuantityB256 (field : String) (h : String) : IO B256 := do
  let x ← IO.remove0x h
  let xs ← (Hex.toBytes x).toIO s!"error : {field} is not a hex byte string"
  (Bytes.toQuantityB256? xs).toIO
    s!"error : {field} is {xs.length} bytes wide, exceeding the 32-byte maximum"

/-- Read a hex *quantity*, which unlike a byte string may have an odd number of
digits. Used for the small schedule numbers a fixture states about itself. -/
def Lean.Json.toIoHexNat (j : Json) : IO Nat := do
  let x ← toIoString j >>= .remove0x
  if x.isEmpty then .throw "error : empty hex quantity"
  let nibbles ← (x.toList.mapM Hexit.toB4).toIO s!"error : invalid hex quantity {x}"
  return nibbles.foldl (fun acc nibble => (acc * 16) + nibble.toNat) 0

def Lean.Json.toAcct : Lean.Json → IO Acct
  | .obj r => do
    let aux (xy : String × Lean.Json) : IO (B256 × B256) := do
      let key ← Hex.toIoQuantityB256 "storage key" xy.fst
      let value ← Lean.Json.toIoQuantityB256 "storage value" xy.snd
      return ⟨key, value⟩
    let bal_json ← (r.get? "balance").toIO ""
    let nonce_json ← (r.get? "nonce").toIO ""
    let code_json ← (r.get? "code").toIO ""
    let stor_json ← (r.get? "storage").toIO "" >>= Lean.Json.toIoRBNode
    let bal ← Lean.Json.toIoQuantityB256 "balance" bal_json
    let nonce ← Lean.Json.toIoQuantityB64 "nonce" nonce_json
    let code ← Lean.Json.toIoBytes code_json
    let storPairs ← List.mapM aux stor_json.toArray.toList
    -- Ethereum's state trie has no entries for zero-valued storage slots.  The
    -- JSON fixtures may spell such a slot explicitly in `pre`, so normalize
    -- through the canonical smart constructor rather than retaining a
    -- non-canonical map entry; `Stor.canonical_ofList` is the witness.
    return ⟨nonce, bal, Stor.ofList storPairs, code.toByteArray⟩
  | _ => .throw "cannot parse account (not .obj)"

-- The prestate is built through `State.ofList`, i.e. through `State.set`, so
-- `State.canonical_ofList` applies: every account comes out of `toAcct`, whose
-- storage is a `Stor.ofList` and hence canonical. An explicit `Acct.nil` or an
-- explicitly zero-valued slot in `pre` is dropped rather than stored, which is
-- what keeps the parsed state's trie root the committed one.
def Lean.Json.toWorld (j : Lean.Json) : IO State := do
  let aux (xy : String × Lean.Json) : IO (Adr × Acct) := do
    let adr ← (Hex.toAdr? <| remove0x xy.fst).toIO ""
    let acct ← xy.snd.toAcct
    return ⟨adr, acct⟩
  let ob ← j.toIoRBNode
  let entries ← List.mapM aux ob.toArray.toList
  return State.ofList entries

def Lean.Json.find? : String → Lean.Json → Option Lean.Json
  | k, .obj r => r.get? k
  | _, _ => .none

def Lean.Json.find : String → Lean.Json → IO Lean.Json
  | k, .obj r => (r.get? k).toIO s!"ERROR : FAILED JSON RETRIEVAL WITH KEY : {k}"
  | k, _ => .throw s!"ERROR : INPUT JSON IS NOT OBJECT, FAILED RETRIEVAL WITH KEY : {k}"

def getTxExMap (j : Lean.Json) : IO (Option String × Bytes) := do
  let rlp ← j.find "rlp" >>= Lean.Json.toIoBytes
  match j.find? "expectException" with
  | .none => pure ⟨.none, rlp⟩
  | .some exj => do
    let exs ← exj.toIoString
    pure ⟨.some exs, rlp⟩

def Lean.Json.toHeader (json : Lean.Json) : IO Header := do
  let parentHash ← json.find "parentHash" >>= Lean.Json.toIoB256
  let ommersHash ← json.find "uncleHash" >>= Lean.Json.toIoB256
  let coinbase ← json.find "coinbase" >>= Lean.Json.toIoAdr
  let stateRoot ← json.find "stateRoot" >>= Lean.Json.toIoB256
  let txsRoot ← json.find "transactionsTrie" >>= Lean.Json.toIoB256
  let receiptRoot ← json.find "receiptTrie" >>= Lean.Json.toIoB256
  let bloom ← json.find "bloom" >>= Lean.Json.toIoBytes
  let difficulty ← (json.find "difficulty" >>= Lean.Json.toIoBytes) <&> Bytes.toNat
  let number ← (json.find "number" >>= Lean.Json.toIoBytes) <&> Bytes.toNat
  let gasLimit ← (json.find "gasLimit" >>= Lean.Json.toIoBytes) <&> Bytes.toNat
  let gasUsed ← (json.find "gasUsed" >>= Lean.Json.toIoBytes) <&> Bytes.toNat
  let timestamp ← (json.find "timestamp" >>= Lean.Json.toIoBytes) <&> Bytes.toNat
  let extraData ← json.find "extraData" >>= Lean.Json.toIoBytes
  let prevRandao ← json.find "mixHash" >>= Lean.Json.toIoB256
  let nonce ← json.find "nonce" >>= Lean.Json.toIoB64
  let baseFeePerGas ← (json.find "baseFeePerGas" >>= Lean.Json.toIoBytes) <&> Bytes.toNat
  let withdrawalsRoot ← json.find "withdrawalsRoot" >>= Lean.Json.toIoB256
  let blobGasUsed ← (json.find "blobGasUsed" >>= Lean.Json.toIoBytes) <&> Bytes.toNat
  let excessBlobGas ← (json.find "excessBlobGas" >>= Lean.Json.toIoBytes) <&> Bytes.toNat
  let parentBeaconBlockRoot ← json.find "parentBeaconBlockRoot" >>= Lean.Json.toIoB256
  let requestsHash := (json.find? "requestsHash" >>= Lean.Json.toB256?)
  .ok {
    parentHash := parentHash
    ommersHash := ommersHash
    coinbase := coinbase
    stateRoot := stateRoot
    txsRoot := txsRoot
    receiptRoot := receiptRoot
    bloom := bloom
    difficulty := difficulty
    number := number
    gasLimit := gasLimit
    gasUsed := gasUsed
    timestamp := timestamp
    extraData := extraData
    prevRandao := prevRandao
    nonce := nonce
    baseFeePerGas := baseFeePerGas
    withdrawalsRoot := withdrawalsRoot
    blobGasUsed := blobGasUsed
    excessBlobGas := excessBlobGas
    parentBeaconBlockRoot := parentBeaconBlockRoot
    requestsHash := requestsHash
  }

def getPostStateRoot (json : Lean.Json) : IO B256 :=
  ( do let stateJson ← json.find "postState"
       let state ← stateJson.toWorld
       .ok state.root ) <|>
  (json.find "postStateHash" >>= Lean.Json.toIoB256)

def Except.toIO {ξ : Type} : Except String ξ → IO ξ
  | .ok x => .ok x
  | .error err => .throw err


/-- Golden-message capture for `~/plans/integrity.md` P0.7.

When `JAUNE_MSG_LOG` names a file, every fixture-observed rendered rejection
message — the raw diagnostic text an expected-invalid block actually failed
with — is appended to it, one message per line. The typed-error migration
(Steps 9–10) uses two full-tier captures, one before and one after each
producer change, to prove the observed rendered diagnostics are byte-identical.
Off (the ordinary case), this is a single environment probe per rejection. -/
def logObservedMessage (err : String) : IO Unit := do
  match (← IO.getEnv "JAUNE_MSG_LOG") with
  | none => pure ()
  | some path =>
    IO.FS.withFile path .append fun h =>
      h.putStr ((err.replace "\n" "\\n") ++ "\n")

/-- The rules this fixture's `network` label applies to a candidate.

A static label names its fork outright. A transition label is a *schedule*, so
each block's own timestamp decides which rules it runs under -- which is the
whole content of a transition fixture -- and the schedule's usability and
chain identity are checked first, in the order `addBlockToChainUsing` checks
them. -/
def fixtureImportRules (spec : NetworkSpec) (chainId : UInt64)
    (parent : CheckedBlockChain) (header : Header) : Except ImportFailure ForkRules := do
  match spec with
  | .static f => Except.mapError ImportFailure.support f.rules
  | .transition t =>
    -- Exactly what `addBlockToChainUsingE` checks, in its order: the schedule
    -- is usable, it names this chain, and only then does the candidate's own
    -- timestamp select the rules.
    let cfg := t.chainConfig chainId
    Except.mapError ImportFailure.context cfg.validate
    Except.mapError ImportFailure.context (cfg.checkChainId parent.val)
    Except.mapError ImportFailure.ofLookup (cfg.rulesAt header.timestamp)

/-- Strictly decode a fixture block once, select its parent snapshot by the
decoded `parentHash`, and import it into that snapshot through the checked
core. The result is the canonical two-level shape: an operational
`ImportFailure` on the outer channel -- which the runner can only ever report
as a harness fault, never score -- and a typed candidate verdict on the inner
one. Nothing is rendered here; text appears only at the logging and reporting
boundary.

The parent is a `CheckedBlockChain`, so its integrity is evidence rather than
a recomputation, and the child snapshot this returns carries the same evidence
-- built from the checks the import already performed. -/
def evaluateFixtureBlock (spec : NetworkSpec) (chainId : UInt64) (store : ChainStore)
    (blockRlp : Bytes) : Except ImportFailure (ImportOutcome CheckedBlockChain) :=
  match hd : rlpToBlockE blockRlp with
  | .error reason => .ok (.inr (.decode reason))
  | .ok ⟨block, _⟩ =>
    -- One strict decode, kept as the canonical envelope the checked import
    -- core consumes; the parent is already a checked snapshot, so no state
    -- root is recomputed for it.
    match store.findParent block.header.parentHash with
    | .error reason => .ok (.inr (.block reason))
    | .ok parent =>
      match fixtureImportRules spec chainId parent block.header with
      | .error failure => .error failure
      | .ok rules =>
        match him : addBlockToChainChecked rules parent
            (CanonicalBlock.ofDecode (rlpToBlock_eq_ok_iff.mpr hd)) with
        | .error failure => .error failure
        | .ok (.inr rejection) => .ok (.inr rejection)
        | .ok (.inl _) => .ok (.inl (CheckedBlockChain.ofImport him))

/-- Score one failed block evaluation against the fixture's expected set.

`err` is the rendered diagnostic (logged for the golden corpus and echoed in
reports); `actual?` is the constructor classification -- `none` for an
operational `ImportFailure`, which has no classification by type, and for the
knowingly unmapped rejection reasons. Classification never reads `err`. -/
def requireExpectedFailure (idx : Nat) (chainname : String)
    (expected : List FixtureException) (err : String)
    (actual? : Option FixtureException) : IO Unit := do
  logObservedMessage err
  match actual? with
  | none =>
    .throw s!"BLOCK #{idx} ({chainname}) failed with an unknown actual error\n\
      raw actual: {repr err}\ncanonical actual: <unknown>\n\
      expected: {expected.map FixtureException.toString}"
  | some actual =>
    if expected.contains actual then
      .println s!"EXPECTED INVALID BLOCK #{idx} ({chainname}) : {actual.toString}"
    else
      .throw s!"BLOCK #{idx} ({chainname}) exception mismatch\n\
        raw actual: {repr err}\ncanonical actual: {actual.toString}\n\
        expected: {expected.map FixtureException.toString}"

/-- Process every fixture block in list order while deriving ancestry only
from each decoded header's `parentHash`. Expected-invalid blocks are checked
exactly, leave the snapshot store unchanged, and never stop later blocks. -/
def processBlockJsons (spec : NetworkSpec) (chainId : UInt64) (store : ChainStore) :
  List (Nat × Lean.Json) → IO ChainStore
  | ⟨idx, blockJson⟩ :: rest => do
    -- Hand-authored blockchain fixtures carry `chainname`; blockchain tests
    -- generated from GeneralStateTests do not.  The label is diagnostic only:
    -- ancestry is always selected from the decoded parent hash.
    let chainname :=
      (blockJson.find? "chainname" >>= Lean.Json.toString?).getD "default"
    .println s!"BLOCK INDEX : {idx}"
    .println s!"CHAIN NAME : {chainname}"
    let ⟨rawExpected?, blockRlp⟩ ← getTxExMap blockJson
    let expected? ←
      match rawExpected? with
      | none => pure none
      | some raw =>
        match FixtureException.parseExpectation raw with
        | .ok expected => pure (some expected)
        | .error err =>
          .throw s!"BLOCK #{idx} ({chainname}) has invalid expectException: {err}"
    match evaluateFixtureBlock spec chainId store blockRlp with
    | .error failure =>
      -- An operational failure: the question was not answered, so this can
      -- never satisfy an expected exception -- with or without an
      -- expectation, the fixture fails.
      match expected? with
      | none =>
        .throw s!"BLOCK #{idx} ({chainname}) was expected valid but failed\n\
          raw actual: {repr failure.render}\ncanonical actual: <unknown canonical identity>"
      | some expected =>
        requireExpectedFailure idx chainname expected failure.render none
        processBlockJsons spec chainId store rest
    | .ok (.inr rejection) =>
      match expected? with
      | none =>
        .throw s!"BLOCK #{idx} ({chainname}) was expected valid but failed\n\
          raw actual: {repr rejection.render}\ncanonical actual: \
          {((FixtureException.ofBlockRejection rejection).map
             FixtureException.toString).getD "<unknown canonical identity>"}"
      | some expected =>
        requireExpectedFailure idx chainname expected rejection.render
          (FixtureException.ofBlockRejection rejection)
        processBlockJsons spec chainId store rest
    | .ok (.inl child) =>
      match expected? with
      | some expected =>
        .throw s!"BLOCK #{idx} ({chainname}) was expected invalid but imported\n\
          expected: {expected.map FixtureException.toString}\n\
          computed tip: {child.tipHash}"
      | none =>
        processBlockJsons spec chainId (store.addResult (.inl child)) rest
  | [] => .ok store

/-- Check a fixture's own declared blob schedule against the rules this run
will apply.

Current-mainnet fixtures state the target, ceiling, and base-fee update
fraction of every fork they use, as blob counts. Reading them here turns each
such fixture into an oracle for this build's `BlobSchedule` data -- which is
all a BPO fork consists of -- instead of trusting that both were transcribed
from the specification the same way. Older fixture families carry no `config`
section; where the declaration exists it is checked exactly, and requiring it
to exist on the current lane is the manifest generator's job. -/
def checkFixtureBlobSchedule (spec : NetworkSpec) (json : Lean.Json) : IO Unit := do
  let some config := json.find? "config" | pure ()
  let some schedule := config.find? "blobSchedule" | pure ()
  for f in spec.forks do
    let declared ← (schedule.find? f.toString).toIO
      s!"error : fixture declares a blob schedule but no entry for {f}"
    let target ← declared.find "target" >>= Lean.Json.toIoHexNat
    let ceiling ← declared.find "max" >>= Lean.Json.toIoHexNat
    let fraction ← declared.find "baseFeeUpdateFraction" >>= Lean.Json.toIoHexNat
    let rules ← IO.ofExcept (f.rules.mapError SupportError.render)
    .guard (rules.blob.target = target * gasPerBlob)
      s!"error : {f} blob target = {rules.blob.target}, fixture declares \
         {target} blobs = {target * gasPerBlob}"
    .guard (rules.blob.max = ceiling * gasPerBlob)
      s!"error : {f} blob maximum = {rules.blob.max}, fixture declares \
         {ceiling} blobs = {ceiling * gasPerBlob}"
    .guard (rules.blob.baseFeeUpdateFraction = fraction)
      s!"error : {f} blob base-fee update fraction = \
         {rules.blob.baseFeeUpdateFraction}, fixture declares {fraction}"

def runBlockchainStTest (spec : NetworkSpec) : (Nat × String × Lean.Json) → IO Unit
  | ⟨idx, name, json⟩ => do
    .println s!"TEST NAME : {name}"
    .println s!"TEST INDEX : {idx}"
    checkFixtureBlobSchedule spec json

    let gbh_json ← json.find "genesisBlockHeader"
    let gbh ← gbh_json.toHeader
    let gb : Block := {header := gbh, txs := [], ommers := [], wds := []}
    let gbh_hash ← gbh_json.find "hash" >>= Lean.Json.toIoB256
    let gbh_hash' := (BLT.toBytes (Header.toBLT gbh)).keccak

    .guard
      (gbh_hash = gbh_hash')
      s!"error : genesis block header hash, expected = {gbh_hash}, computed = {gbh_hash'}"

    let genesisRLP ← json.find "genesisRLP" >>= Lean.Json.toIoBytes
    let genesisRLP' := gb.toBLT.toBytes
    .guard (genesisRLP = genesisRLP') "error : unexpected genesis block RLP."
    let (chainId : Nat) ←
      match gbh_json.find? "chainId" with
      | .none => .ok 1
      | .some chainIdJson => chainIdJson.toIoB64 <&> UInt64.toNat

    let preState ← json.find "pre" >>= Lean.Json.toWorld

    -- P0.2 item 6. The genesis block enters through the same strict decoder
    -- every candidate does, rather than being trusted because a hand-built
    -- record re-encodes to itself, and the declared hash and the parsed
    -- prestate are compared against *that* decoded genesis. The prestate root
    -- check is the one this runner never made: without it the whole chain
    -- executes from a world its own genesis header does not commit to.
    let genesisEnvelope ← (CanonicalBlock.ofRlp? genesisRLP).toIO
      "error : genesis RLP is not canonical block RLP"
    .guard (genesisEnvelope.headerHash = gbh_hash)
      s!"error : decoded genesis header hash does not match\n  \
         expected : {gbh_hash}\n  computed : {genesisEnvelope.headerHash}"
    let genesisStateRoot := genesisEnvelope.block.header.stateRoot
    -- The prestate's root is computed here, once, and the proof of the
    -- comparison is what builds the checked snapshot -- so nothing downstream
    -- recomputes it, and no unchecked genesis snapshot can be built at all.
    let preStateRoot := preState.root
    let genesisChecked ←
      if hnum : genesisEnvelope.block.header.number = 0 then
        if hcanon : preState.Canonical then
          if hroot : preStateRoot = genesisStateRoot then
            pure (CheckedBlockChain.ofGenesis genesisEnvelope preState
              chainId.toUInt64 hnum hcanon hroot)
          else
            .throw s!"error : genesis prestate root does not match the genesis \
              header\n  expected : {genesisStateRoot}\n  computed : {preStateRoot}"
        else
          .throw "error : genesis prestate is not a canonical world"
      else
        .throw s!"error : genesis block number = \
          {genesisEnvelope.block.header.number}, expected 0"

    let blockJsons ← json.find "blocks" >>= Lean.Json.toIoList
    let store ←
      processBlockJsons spec chainId.toUInt64 (.init genesisChecked)
        blockJsons.putIndex
    let lastBlockHash ← json.find "lastblockhash" >>= Lean.Json.toIoB256
    let chain ← ((store.findLast lastBlockHash).mapError ImportFailure.render).toIO
    let lastBlockHash' := chain.tipHash
    .guard
      (lastBlockHash = lastBlockHash')
      s!"error : last block hash does not match\n  expected : {lastBlockHash}\n  computed : {lastBlockHash'}"

    let postStateRoot ← getPostStateRoot json
    -- Read the committed root instead of rebuilding it, exactly as the tip-hash
    -- check above reads `tipHash`. `CheckedBlockChain.stateRoot_eq` is the proof
    -- that this is the same comparison as against `chain.val.state.root`, so no
    -- fixture can classify differently -- and the world-state trie, which this
    -- runner was reconstructing once per fixture on top of the one
    -- `stateTransitionE` already built and checked, is not rebuilt at all.
    let postStateRoot' := chain.stateRoot
    .guard
      (postStateRoot = postStateRoot')
      s!"error : end state root does not match\n  expected : {postStateRoot}\n  computed : {postStateRoot'}"

/-- The network specs this build can actually run.

Rule 2 of the selection model below. A label is supported when it parses to a
`NetworkSpec` and, for a transition, names a usable schedule: a transition that
activates at genesis or runs the fork chain backwards determines no unambiguous
fork at every block, so no chain can run it. That is the answer `--network` has
always given such a label; it is applied here to the labels fixtures carry as
well, so both come from one definition of "supported". -/
def supportedSpec? (label : String) : Option NetworkSpec := do
  let spec ← NetworkSpec.ofString? label
  match spec with
  | .static _ => return spec
  | .transition t =>
    match (ChainConfig.mk 0 t.activations).validate with
    | .ok _ => return spec
    | .error _ => none

/-- The `--network` label the user asked for, as a supported spec.

This differs from `supportedSpec?` only in what it does with a rejection: a
label the user typed is a command-line mistake and is reported as one, naming
the label and the supported alternatives, rather than quietly selecting
nothing. The two rejection reasons stay distinct -- an unknown label and a
schedule that parses but is unusable are different mistakes.

The `0` chain ID is a placeholder: `ChainConfig.validate` never reads
`chainId`, so it is not a second, independently-chosen chain identity. The
actual chain ID is read per fixture and threaded by `evaluateFixtureBlock`. -/
def requireSupportedSpec (label : String) : IO NetworkSpec := do
  let some spec := NetworkSpec.ofString? label
    | .throw
        s!"error : unknown --network label {repr label}; supported labels are \
           {Fork.all.map Fork.toString} and transitions of the form \
           <fork>To<fork>AtTime<seconds>"
  if let .transition t := spec then
    IO.ofExcept ((ChainConfig.mk 0 t.activations).validate.mapError
      ChainContextError.render)
  return spec

/-- Every filter a fixture run can carry, plus the positional arguments seen.

Each filter field is limitative: it can only remove cases from the selection,
never add one. `paths` is not a filter -- it collects the non-option arguments
so that options may appear before or after the fixture path, and `main` can
report "exactly one file" as its own error rather than as an unknown option. It
is accumulated in reverse, as the parser prepends. -/
structure FixtureOpts where
  net : Option NetworkSpec := none
  testIdx : Option Nat := none
  incls : List String := []
  excls : List String := []
  paths : List String := []

/-- The case's own network spec, if the case survives every filter.

The selection model is three rules, and this function is the first two of them:

1. every user-supplied filter is limitative -- `--network`, `--name`,
   `--notName` and `--index` can only carve the selection down;
2. the selection is *always* intersected with what this build supports,
   `--network` given or not, so a file whose cases predate Prague contributes
   its supported ones and nothing more;
3. `runTestFile` requires what remains to be nonempty.

There is deliberately no default fork. The spec returned is the one the case's
own `network` label names, so each selected case runs under its own rules and
nothing downstream falls back to a hardcoded one. -/
def fixtureCaseSpec? (o : FixtureOpts) :
    (Nat × String × Lean.Json) → IO (Option NetworkSpec)
  | ⟨idx, name, json⟩ => do
    if let some specIdx := o.testIdx then
      if specIdx ≠ idx then return none
    if ¬ (o.incls.isEmpty ∨ name ∈ o.incls) then
      return none
    if name ∈ o.excls then
      return none
    let label ← json.find "network" >>= Lean.Json.toIoString
    let some spec := supportedSpec? label | return none
    if let some requested := o.net then
      if spec ≠ requested then return none
    return some spec

/-- One fixture case's declared `network` label, for reporting. -/
def fixtureCaseNetwork : (Nat × String × Lean.Json) → IO String
  | ⟨_, _, json⟩ => json.find "network" >>= Lean.Json.toIoString

/-- The fixture format a case declares, when it declares one.

EEST fills one test into sibling trees -- `blockchain_tests`,
`blockchain_tests_engine`, `blockchain_tests_engine_x`, `state_tests` and
`transaction_tests` -- under a single file name, and every case records the
tree it came from in `_info.fixture-format`. This runner consumes
`blockchain_test`; the others describe a different consumer and share almost
none of the shape it reads.

A case declaring no format is passed through. The field is EEST's, so a
hand-written or third-party fixture may omit it and still be readable if its
shape is right. This narrows a bad diagnostic; it does not add a requirement.
Every case in both installed corpora carries the field. -/
def fixtureCaseFormat? : (Nat × String × Lean.Json) → Option String
  | ⟨_, _, json⟩ =>
    match json.find? "_info" >>= Lean.Json.find? "fixture-format" with
    | some (.str fmt) => some fmt
    | _ => none

/-- The `blockchain_tests` sibling of a path inside another EEST fixture tree.

Since the trees agree on every path component but their root, the runnable
copy of a wrong-tree path is that path with the root swapped, and naming it
beats describing it. A path carrying no such component -- a file copied out of
the tree, which is how this mistake is most often made -- has nothing to
rewrite, and the caller names the tree instead.

The candidates are ordered longest-first so that a `blockchain_tests_engine_x`
path is not mistaken for a `blockchain_tests_engine` one; the surrounding
slashes already prevent it, and the order keeps that from resting on them. -/
def blockchainTestSibling? (path : String) : Option String :=
  ["blockchain_tests_engine_x", "blockchain_tests_engine", "transaction_tests",
   "state_tests"].findSome? fun tree =>
    let rewritten := path.replace s!"/{tree}/" "/blockchain_tests/"
    if rewritten == path then none else some rewritten

def runTestFile (o : FixtureOpts) (path : String) : IO Unit := do
  .println "\n================================================================\n"
  .println s!"TEST FILE : {path}\n"
  let rb ← readJsonFile path >>= Lean.Json.toIoRBNode
  let js := rb.toArray.toList.putIndex
  -- Rule 0, and the first thing a new user hits. EEST ships the same test
  -- under one name in five sibling trees and only `blockchain_tests` is this
  -- runner's, so a wrong-tree file is the likeliest way to arrive here. It
  -- used to surface as a missing JSON key -- `network` for a state test,
  -- `genesisRLP` for an engine one, and the engine case only after a header
  -- that had already announced selected cases, which reads like a real run
  -- failing. Neither names the actual mistake, and no filter can repair it:
  -- `--network` selects among cases, and these cases are not this shape. So
  -- refuse the file before reading one field that assumes the shape.
  let declared := (js.filterMap fixtureCaseFormat?).eraseDups
  let foreign := declared.filter (· ≠ "blockchain_test")
  .guard foreign.isEmpty
    s!"ERROR : {path} holds {foreign} cases, and jaune runs blockchain_test \
       fixtures. EEST fills one test into sibling trees under a single file \
       name, so the file to run is its blockchain_tests copy{
         match blockchainTestSibling? path with
         | some sibling => s!" -- here, {sibling}"
         | none => ""}"
  let labels ← js.mapM fixtureCaseNetwork
  let supported := labels.filter (fun l => (supportedSpec? l).isSome)
  let tagged ← js.mapM fun c => do
    return (← fixtureCaseSpec? o c).map (fun spec => (spec, c))
  let selected := tagged.filterMap id
  .println s!"NETWORKS : {(selected.map (fun p => p.fst.toString)).eraseDups}"
  .println s!"SELECTED CASES : {selected.length}"
  .println s!"SKIPPED CASES : {js.length - selected.length}"
  -- Rule 3. The three ways to arrive at an empty selection are different
  -- mistakes and are reported as different ones: a file with no cases at all
  -- is malformed, a file with no supported case is out of scope for this
  -- build, and a file whose supported cases were all filtered away is a
  -- command-line error. Folding them together is what made the old message
  -- blame a `--network Prague` the user never passed.
  .guard (¬ js.isEmpty)
    s!"ERROR : {path} holds no cases; an empty fixture file is a corpus error, \
       never a vacuous pass"
  .guard (¬ supported.isEmpty)
    s!"ERROR : no case in {path} runs at a network this build supports; the \
       file's labels are {labels.eraseDups}, and the supported labels are \
       {Fork.all.map Fork.toString} and transitions between them"
  .guard (¬ selected.isEmpty)
    s!"ERROR : the filters select no case in {path}; {supported.length} of its \
       {js.length} cases run at a supported network, with labels \
       {supported.eraseDups}"
  let _ ← selected.mapM (fun p => runBlockchainStTest p.fst p.snd)
  .ok ()

/-- Parse the fixture-mode options.

Unknown options are refused rather than reinterpreted. Before this existed any
token the option scanners did not recognise fell through to be treated as a
path or silently dropped, so a misspelled `--netwrok Prague` ran the default
fork without a word and a second `--network` was discarded.

`--network` is not repeatable: it is a filter, and a case carries exactly one
network, so a second one could only ever select nothing. An arity error reports
that far better than an empty selection would. `--name` and `--notName` do
repeat -- they accumulate within their own dimension, which stays limitative
because the dimension as a whole still only removes cases. -/
def parseFixtureOpts : FixtureOpts → List String → IO FixtureOpts
  | o, [] => return o
  | o, "--network" :: label :: rest => do
    if o.net.isSome then
      .throw
        s!"error : --network given more than once; a case has exactly one \
           network, so a second one can only select nothing"
    parseFixtureOpts { o with net := some (← requireSupportedSpec label) } rest
  | o, "--name" :: name :: rest =>
    parseFixtureOpts { o with incls := name :: o.incls } rest
  | o, "--notName" :: name :: rest =>
    parseFixtureOpts { o with excls := name :: o.excls } rest
  | o, "--index" :: idx :: rest => do
    let some n := idx.toNat?
      | .throw s!"error : --index expects a natural number, got {repr idx}"
    parseFixtureOpts { o with testIdx := some n } rest
  | o, arg :: rest => do
    -- Anything left that looks like an option is either misspelled or missing
    -- its argument; anything else is a positional. Testing the shape here is
    -- what keeps a typo from being silently reinterpreted as a file path.
    if arg.startsWith "-" then
      .throw
        s!"error : unknown or incomplete option {repr arg}; run with --help \
           for usage"
    parseFixtureOpts { o with paths := arg :: o.paths } rest

def getNetwork : List String → Option String
  | "--network" :: network :: _ => some network
  | _ :: opts => getNetwork opts
  | [] => none

/-- Resolve `--network` to a supported protocol fork.

Strict by construction: the label must be one this build knows, and an
unrecognised one aborts rather than quietly running Prague. Omitting the option
still means Prague, which is what every committed gate passes explicitly.

This is the *static* resolution, used where only one rule set can apply -- a
precompile vector file runs at one fork, so a transition label is an error
here rather than an ambiguity. -/
def getFork (opts : List String) : IO Fork :=
  match getNetwork opts with
  | none => .ok .prague
  | some label =>
    match Fork.ofString? label with
    | some f => .ok f
    | none =>
      .throw
        s!"error : unknown --network label {repr label}; supported labels are \
           {Fork.all.map Fork.toString}"

def createMinimalEvm
    (rules : ForkRules) (adr : Adr) (input : Bytes) (gasLimit : Nat) : Evm := {
  pc := 0
  sta := {
    caller := default
    target := none
    currentTarget := adr
    gas := gasLimit
    value := default
    data := input
    codeAddress := none
    code := .empty
    depth := 1
    shouldTransferValue := false
    isStatic := false
    disablePrecompiles := false
    benvStat := { (default : BenvStat) with rules := rules }
    tenvStat := default
  }
  dyna := {
    mach := {
      stack := []
      memory := .empty
      gasLeft := gasLimit
    }
    «meta» := {
      logs := []
      refundCounter := 0
      output := []
      accountsToDelete := .emptyWithCapacity
      returnData := []
      error := none
      accessedAddresses := .emptyWithCapacity
      accessedStorageKeys := .emptyWithCapacity
      createdAccounts := .emptyWithCapacity
    }
    world := {
      state := .empty
      transientStorage := .empty
    }
  }
}

def processVector (rules : ForkRules) (adr : Adr) : (Nat × Lean.Json) → IO Bool
  | ⟨idx, json⟩ => do
    let name ← (json.find? "Name" >>= Lean.Json.toString?).toIO s!"missing Name at index {idx}"
    let inputStr ← (json.find? "Input" >>= Lean.Json.toString?).toIO s!"missing Input for {name}"
    let input ← (Hex.toBytes <| remove0x inputStr).toIO s!"invalid Input hex for {name}"
    let isPositive := (json.find? "Expected").isSome
    let expected? ← if isPositive then
        let expStr ← (json.find? "Expected" >>= Lean.Json.toString?).toIO s!"missing Expected for {name}"
        some <$> (Hex.toBytes <| remove0x expStr).toIO s!"invalid Expected hex for {name}"
      else pure none
    let gas ← if isPositive then
        let g ← (json.find? "Gas").toIO s!"missing Gas for {name}"
        let gs := toString g
        (String.toNat? gs).toIO s!"invalid Gas for {name}"
      else pure 0
    let evm := createMinimalEvm rules adr input 0xffffffffffff
    let res := precompileRun evm adr
    match expected? with
    | some expected =>
      match res with
      | .ok cost output =>
        if cost == gas && output == expected then
          .println s!"PASS\t{name}"
          return true
        else
          .println s!"FAIL\t{name}\t(expected out={expected.toHex} gas={gas}, got out={output.toHex} gas={cost})"
          return false
      | .error err _ =>
        .println s!"FAIL\t{name}\t(expected out={expected.toHex}, got error {err.render})"
        return false
    | none =>
      match res with
      | .error _ _ =>
        .println s!"PASS\t{name}"
        return true
      | .ok _ output =>
        .println s!"FAIL\t{name}\t(expected error, got ok out={output.toHex})"
        return false

/-- Run one precompile vector file at `addr` under `f`'s rules.

The activation check is part of the gate, not a convenience: a vector file
listed against a fork whose rules do not carry its address is a manifest
error, and reporting it as such is what stops a fork-gated precompile from
being silently exercised under a fork that does not have it. -/
def runVectorFile (f : Fork) (addr : Adr) (path : String) : IO Bool := do
  let rules ← IO.ofExcept (f.rules.mapError SupportError.render)
  if ¬ rules.isPrecomp addr then
    IO.println
      s!"RED — vectors: no precompile is active at {addr.toHex} under {f}"
    return false
  let rb ← readJsonFile path >>= Lean.Json.toIoList
  let js := rb.putIndex
  let results ← js.mapM (processVector rules addr)
  let mut passes := 0
  for pass in results do
    if pass then passes := passes + 1
  let total := results.length
  -- `passes == total` is vacuously true at zero cases, so a file that parses to
  -- an empty list would otherwise report a green verdict over nothing at all.
  -- That is the permissive oracle this gate exists to prevent: an empty vector
  -- file means the manifest and the corpus disagree, not that there is nothing
  -- to check.
  if total == 0 then
    IO.println
      s!"RED — vectors: 0/0 PASS, target not met: {path} holds no cases; an empty vector file is a manifest error, never a vacuous pass"
    return false
  if passes == total then
    .println s!"OK — vectors: {passes}/{total} PASS"
    return true
  else
    .println s!"RED — vectors: {passes}/{total} PASS, target not met"
    return false

def Lean.Json.toIoU256Vectors (j : Lean.Json) : IO (List Lean.Json) :=
  match j with
  | .obj o => (o.get? "vectors").toIO "u256 vector file has no vectors array" >>= Lean.Json.toIoList
  | .arr _ => Lean.Json.toIoList j -- accepted for simple external differential files
  | _ => IO.throw "u256 vector file must be an object or array"

def b256VectorResult (op : String) (xs : List B256) : Option B256 :=
  match op, xs with
  | "add", [x, y] => some (x + y)
  | "sub", [x, y] => some (x - y)
  | "mul", [x, y] => some (x * y)
  | "div", [x, y] => some (x / y)
  | "mod", [x, y] => some (x % y)
  | "sdiv", [x, y] => some (B256.sdiv x y)
  | "smod", [x, y] => some (B256.smod x y)
  | "addmod", [x, y, z] => some (B256.addmod x y z)
  | "mulmod", [x, y, z] => some (B256.mulmod x y z)
  | "exp", [x, y] => some (x ^ y)
  | "signextend", [x, y] => some (B256.signext x y)
  | "lt", [x, y] => some (B256.ltCheck x y)
  | "gt", [x, y] => some (B256.gtCheck x y)
  | "slt", [x, y] => some (B256.sltCheck x y)
  | "sgt", [x, y] => some (B256.sgtCheck x y)
  | "eq", [x, y] => some (B256.eqCheck x y)
  | "iszero", [x] => some (B256.eqCheck x 0)
  | "and", [x, y] => some (x &&& y)
  | "or", [x, y] => some (x ||| y)
  | "xor", [x, y] => some (x ^^^ y)
  | "not", [x] => some (~~~ x)
  | "byte", [x, y] => some (List.getD y.toBytes x.toNat 0).toB256
  | "shl", [x, y] => some (y <<< x.toNat)
  | "shr", [x, y] => some (y >>> x.toNat)
  | "sar", [x, y] => some (B256.arithShiftRight y x.toNat)
  | "codec", [x] => some x.toBytes.toB256
  | "bytecount", [x] => some x.bytecount.toB256
  | "exp_gas", [x] => some (gExp + gExpbyte * x.bytecount).toB256
  | _, _ => none

def processU256Vector : (Nat × Lean.Json) → IO Bool
  | ⟨idx, json⟩ => do
    let op ← (json.find? "op" >>= Lean.Json.toString?).toIO s!"u256 vector {idx}: missing op"
    let argsJ ← (json.find? "args").toIO s!"u256 vector {idx}: missing args" >>= Lean.Json.toIoList
    let expectedJ ← (json.find? "expected").toIO s!"u256 vector {idx}: missing expected"
    let expected ← match expectedJ with
      | .str _ => Lean.Json.toIoB256 expectedJ
      | _ => do
        let n ← (String.toNat? (toString expectedJ)).toIO s!"u256 vector {idx}: invalid numeric expected"
        pure n.toB256
    let actual? ← match op with
      | "keccak" => match argsJ with
        | [arg] => pure (some ((← Lean.Json.toIoBytes arg).keccak))
        | _ => pure none
      | "keccak_ba" => match argsJ with
        | [arg] => do
          let bs ← Lean.Json.toIoBytes arg
          pure (some (ByteArray.keccak 0 bs.length ⟨bs.toArray⟩))
        | _ => pure none
      | "ofB8L" => match argsJ with
        | [arg] => pure (some (Bytes.toB256 (← Lean.Json.toIoBytes arg)))
        | _ => pure none
      | _ => pure (b256VectorResult op (← argsJ.mapM Lean.Json.toIoB256))
    match actual? with
    | some actual =>
      if actual = expected then IO.println s!"PASS\t{idx}\t{op}"; return true
      else IO.println s!"FAIL\t{idx}\t{op}\texpected={expected.toHex}\tactual={actual.toHex}"; return false
    | none => IO.println s!"FAIL\t{idx}\t{op}\tunknown op or arity"; return false

def runU256VectorFile (path : String) : IO Bool := do
  let js ← readJsonFile path >>= Lean.Json.toIoU256Vectors
  let results ← js.putIndex.mapM processU256Vector
  let passes := results.count true
  -- Same vacuous-pass hole as runVectorFile, same answer.
  if results.length == 0 then
    IO.println
      s!"RED — u256: 0/0 PASS, target not met: {path} holds no cases; an empty vector file is a manifest error, never a vacuous pass"
    return false
  if passes == results.length then
    IO.println s!"OK — u256: {passes}/{results.length} PASS"; return true
  else
    IO.println s!"RED — u256: {passes}/{results.length} PASS, target not met"; return false

-- Step-7 fake-exponential differential mode: every case carries the expected
-- value the pinned EELS `taylor_exponential` computed (see
-- scripts/gen-fake-exp-vectors.py); the binary evaluates the total `fakeExp`.
-- All four fields are decimal strings, so the grid is not bounded by B256.
def processFakeExpVector : (Nat × Lean.Json) → IO Bool
  | ⟨idx, json⟩ => do
    let get : String → IO Nat := fun field => do
      let s ← (json.find? field >>= Lean.Json.toString?).toIO
        s!"fake-exp vector {idx}: missing or non-string {field}"
      (String.toNat? s).toIO s!"fake-exp vector {idx}: non-decimal {field}"
    let fac ← get "factor"
    let num ← get "numerator"
    let den ← get "denominator"
    let expected ← get "expected"
    let actual := fakeExp fac num den
    if actual = expected then
      IO.println s!"PASS\t{idx}\tfakeExp {fac} {num} {den}"
      return true
    else
      IO.println
        s!"FAIL\t{idx}\tfakeExp {fac} {num} {den}\texpected={expected}\tactual={actual}"
      return false

def runFakeExpVectorFile (path : String) : IO Bool := do
  -- Same {"vectors": [...]} envelope as the U256 oracle file.
  let js ← readJsonFile path >>= Lean.Json.toIoU256Vectors
  let results ← js.putIndex.mapM processFakeExpVector
  let passes := results.count true
  -- Same vacuous-pass hole as runVectorFile, same answer.
  if results.length == 0 then
    IO.println
      s!"RED — fake-exp: 0/0 PASS, target not met: {path} holds no cases; an empty vector file is a manifest error, never a vacuous pass"
    return false
  if passes == results.length then
    IO.println s!"OK — fake-exp: {passes}/{results.length} PASS"; return true
  else
    IO.println s!"RED — fake-exp: {passes}/{results.length} PASS, target not met"
    return false

/-- The usage text.

The supported labels are rendered from `Fork.all` and from a constructed
`ForkTransition`, not written out by hand, so this text cannot drift from what
the build actually supports -- which is exactly how the README's fork list came
to disagree with the binary. -/
def usage : String :=
  s!"usage:
  jaune <fixture.json> [--network <label>] [--name <case>] \
[--notName <case>] [--index <n>]
  jaune --vectors <address> <file.json> [--network <fork>]
  jaune --u256 <file.json>
  jaune --fake-exp <file.json>
  jaune --help

Runs one blockchain-test fixture file. EEST fills one test into sibling trees
-- blockchain_tests, blockchain_tests_engine, blockchain_tests_engine_x,
state_tests and transaction_tests -- under a single file name; only
blockchain_tests is this runner's. Install the corpus with
`python3 scripts/bootstrap_mainnet.py`.

Every option is a filter: each one only narrows the set of cases that run, and
the selection is always narrowed to the networks this build supports. The run
fails if no case survives. Given no --network, every supported case in the file
runs under the rules its own network label names.

  --network <label>  run only cases at this network; not repeatable
  --name <case>      run only these cases; repeatable
  --notName <case>   skip these cases; repeatable
  --index <n>        run only the case at this index

supported networks:
  {Fork.all.map Fork.toString}
  transitions of the form <fork>To<fork>AtTime<seconds>, for example \
{ForkTransition.toString ⟨.prague, .osaka, 15000⟩}
"

def main : List String → IO Unit
  | [] => .throw "error : no arguments; run with --help for usage"
  | "--help" :: _ => .println usage
  | "-h" :: _ => .println usage
  | "--u256" :: pathStr :: [] => do
    if !(← runU256VectorFile pathStr) then IO.Process.exit 1
  | "--fake-exp" :: pathStr :: [] => do
    if !(← runFakeExpVectorFile pathStr) then IO.Process.exit 1
  | "--vectors" :: addrStr :: pathStr :: opts => do
    let addrStr2 := remove0x addrStr
    let paddedAddrStr :=
      String.ofList (List.replicate (40 - addrStr2.length) '0') ++ addrStr2
    let addr ← (Hex.toAdr? paddedAddrStr).toIO "invalid address"
    let f ← getFork opts
    if !(← runVectorFile f addr pathStr) then
      IO.Process.exit 1
  -- Arity errors for the alternate modes, so that a mode flag given the wrong
  -- number of arguments is reported as itself rather than falling through to
  -- fixture mode and being called an unknown option.
  | "--u256" :: _ => .throw "error : --u256 takes exactly one file path"
  | "--fake-exp" :: _ => .throw "error : --fake-exp takes exactly one file path"
  | "--vectors" :: _ =>
    .throw "error : --vectors takes an address and a file path"
  -- One fixture file, never a directory. Walking a tree here was a second,
  -- unaccounted enumeration path: it produced no per-file classification, no
  -- baseline comparison, no wall-clock guard and no gate lock, so its output
  -- read like a gate result while being none. `check.sh --dir` is the
  -- enumerator that has all four. `--skip`, which dropped leading *files*,
  -- went with it -- it could not mean anything for a single file.
  | args => do
    let o ← parseFixtureOpts {} args
    match o.paths with
    | [path] => runTestFile o path
    | [] => .throw "error : no fixture file given; run with --help for usage"
    | ps =>
      .throw
        s!"error : expected exactly one fixture file, got {ps.reverse}; a run \
           takes one file, and `check.sh --dir` is the enumerator for a tree"
