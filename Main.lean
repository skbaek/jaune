import «Jaune».Execution
import «Jaune».Sufficiency
import «Jaune».Transaction
import «Jaune».FixtureException
import «Jaune».ChainStore

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

def actualExceptionDiagnostic (err : String) : String :=
  match FixtureException.classify err with
  | some actual => actual.toString
  | none => "<unknown canonical identity>"

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
core. Both failure channels are collapsed only after being handled explicitly.

The parent is a `CheckedBlockChain`, so its integrity is evidence rather than
a recomputation, and the child snapshot this returns carries the same evidence
-- built from the checks the import already performed. -/
def evaluateFixtureBlock (spec : NetworkSpec) (chainId : UInt64) (store : ChainStore)
    (blockRlp : Bytes) : Except String CheckedBlockChain :=
  match hd : rlpToBlock blockRlp with
  | .error err => .error err
  | .ok ⟨block, _⟩ =>
    -- One strict decode, kept as the canonical envelope the checked import
    -- core consumes; the parent is already a checked snapshot, so no state
    -- root is recomputed for it.
    match store.findParent block.header.parentHash with
    | .error err => .error err
    | .ok parent =>
      match fixtureImportRules spec chainId parent block.header with
      | .error failure => .error failure.render
      | .ok rules =>
        match him : addBlockToChainChecked rules parent (CanonicalBlock.ofDecode hd) with
        | .error failure => .error failure.render
        | .ok (.inr rejection) => .error rejection.render
        | .ok (.inl _) => .ok (CheckedBlockChain.ofImport him)

def requireExpectedFailure (idx : Nat) (chainname : String)
    (expected : List FixtureException) (err : String) : IO Unit := do
  logObservedMessage err
  match FixtureException.classify err with
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
    | .error err =>
      match expected? with
      | none =>
        .throw s!"BLOCK #{idx} ({chainname}) was expected valid but failed\n\
          raw actual: {repr err}\ncanonical actual: {actualExceptionDiagnostic err}"
      | some expected =>
        requireExpectedFailure idx chainname expected err
        processBlockJsons spec chainId store rest
    | .ok child =>
      match expected? with
      | some expected =>
        .throw s!"BLOCK #{idx} ({chainname}) was expected invalid but imported\n\
          expected: {expected.map FixtureException.toString}\n\
          computed tip: {child.tipHash}"
      | none =>
        processBlockJsons spec chainId (store.addResult (.ok child)) rest
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
    let chain ← (store.findLast lastBlockHash).toIO
    let lastBlockHash' := chain.tipHash
    .guard
      (lastBlockHash = lastBlockHash')
      s!"error : last block hash does not match\n  expected : {lastBlockHash}\n  computed : {lastBlockHash'}"

    let postStateRoot ← getPostStateRoot json
    .guard
      (postStateRoot = chain.val.state.root)
      s!"error : end state root does not match\n  expected : {postStateRoot}\n  computed : {chain.val.state.root}"

/-- Select the cases whose fixture `network` label is exactly the requested
one. Selection is by label equality, as before; the label is now a parsed
value rather than an arbitrary string, so an unknown one cannot reach this
point, and a transition label matches only its own canonical spelling. -/
def fixtureCaseSelected (spec : NetworkSpec) (testIdx : Option Nat)
    (incls excls : List String) : (Nat × String × Lean.Json) → IO Bool
  | ⟨idx, name, json⟩ => do
    if let some specIdx := testIdx then
      if specIdx ≠ idx then return false
    if ¬ (incls.isEmpty ∨ name ∈ incls) then
      return false
    if name ∈ excls then
      return false
    let caseNetwork ← json.find "network" >>= Lean.Json.toIoString
    return caseNetwork = spec.toString

def runTestFile (spec : NetworkSpec) (testIdx : Option Nat)
  (incls excls : List String) (idxPath : Nat × String) : IO Unit := do
  let fileIdx := idxPath.fst
  let path := idxPath.snd
  .println "\n================================================================\n"
  .println s!"TEST FILE #{fileIdx} : {path}\n"
  let rb ← readJsonFile path >>= Lean.Json.toIoRBNode
  let js := rb.toArray.toList.putIndex
  let selected ← js.filterM <| fixtureCaseSelected spec testIdx incls excls
  .println s!"NETWORK : {spec}"
  .println s!"SELECTED CASES : {selected.length}"
  .println s!"SKIPPED CASES : {js.length - selected.length}"
  .guard (¬ selected.isEmpty)
    s!"ERROR : zero cases match the combined network/name/index filters \
       (network = {spec}) in {path}"
  let _ ← selected.mapM (runBlockchainStTest spec)
  .ok ()

def getTestNames (incls excls : List String) :
  List String → (List String × List String)
  | option :: arg :: strs =>
    if option = "--name"
    then getTestNames (arg :: incls) excls strs
    else
      if option = "--notName"
      then getTestNames incls (arg :: excls) strs
      else getTestNames incls excls (arg :: strs)
  | [_] => ⟨incls, excls⟩
  | [] => ⟨incls, excls⟩

def getSkip : List String → Option Nat
  | s0 :: s1 :: ss =>
    if s0 = "--skip"
    then String.toNat? s1
    else getSkip <| s1 :: ss
  | _ => none

def getTestIndex : List String → Option Nat
  | s0 :: s1 :: ss =>
    if s0 = "--index"
    then String.toNat? s1
    else getTestIndex <| s1 :: ss
  | _ => none

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

/-- Resolve `--network` to the fixture network a suite names: a static fork or
a supported transition schedule.

A transition's schedule is validated here, before any fixture is read, so a
label that parses but does not determine an unambiguous fork at every block --
an activation at genesis, or one that runs the fork chain backwards -- is
refused up front rather than once per case. This checks schedule shape only,
through `ForkTransition.activations`, before any fixture is read -- so there is
no real chain ID to check against yet. `ChainConfig.validate` never reads
`chainId` at all, so the `0` below is not a second, independently-chosen chain
identity, only a placeholder the check cannot see; the actual chain ID, read
per fixture, is threaded separately by `evaluateFixtureBlock`. -/
def getNetworkSpec (opts : List String) : IO NetworkSpec := do
  let some label := getNetwork opts | return .static .prague
  let some spec := NetworkSpec.ofString? label
    | .throw
        s!"error : unknown --network label {repr label}; supported labels are \
           {Fork.all.map Fork.toString} and transitions of the form \
           <fork>To<fork>AtTime<seconds>"
  if let .transition t := spec then
    IO.ofExcept ((ChainConfig.mk 0 t.activations).validate.mapError
      ChainContextError.render)
  return spec

def getFiles (path : System.FilePath) : IO (List System.FilePath) := do
  if (← System.FilePath.isDir path) then
    let paths ← System.FilePath.walkDir path
    List.filterM (fun path => path.isDir <&> .not) paths.toList
  else
    return [path]

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

def main : List String → IO Unit
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
  | path :: opts => do
    let testIdx : Option Nat := getTestIndex opts
    let skip : Option Nat := getSkip opts
    let spec ← getNetworkSpec opts
    let ⟨incls, excls⟩ := getTestNames [] [] opts
    let files ← getFiles path
    let files :=
      match skip with
      | none => files
      | some n => files.drop n
    let _ ←
      List.mapM
        (runTestFile spec testIdx incls excls)
        (files.map System.FilePath.toString).putIndex
    pure ()
  | _ => IO.throw "error : invalid arguments"
