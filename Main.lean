import «Jaune».Execution
import «Jaune».Sufficiency
import «Jaune».Transaction
import «Jaune».FixtureException
import «Jaune».ChainStore
import «Jaune».BLSGuards
import «Jaune».T8n

open Jaune



----------------- JSON DECODING HELPERS ------------------

-- The bulk of this section -- every `Lean.Json.toIo*` reader, `toAcct`,
-- `toWorld`, and the two `find` accessors -- now lives in `Jaune/T8n.lean`,
-- which this module imports. It moved there rather than being copied when the
-- transition-tool frontend needed to decode the same `alloc` shape: a second
-- `toWorld` would be a second definition of what a pre-state is. Only the
-- three declarations below are still fixture-runner-only.

/-- Strip a mandatory `0x` prefix, or fail. This lives in the harness rather
than `Jaune/Basic.lean` because it is fixture-JSON syntax handling, not
library semantics, and its optional result is a parse channel that has no
business inside the semantic import closure. -/
def Option.remove0x (s : String) : Option String :=
  match s.toList with
  | '0' :: 'x' :: cs => return String.ofList cs
  | _ => .none

def Lean.Json.toString? : Lean.Json → Option String
  | .str s => some s
  | _ => none

def Lean.Json.toB256? (j : Json) : Option B256 := do
  let x ← toString? j >>= .remove0x
  Hex.toB256? x

/-- A JSON quantity field as a `UInt64`, when present and readable.

`Bytes.toQuantityB64?` rather than `Bytes.toUInt64?`: fixture quantities are
written minimally, so a small slot number is a one-byte string, and the
exact-width decoder would reject it. Over-long input is still refused rather
than truncated. -/
def Lean.Json.toB64? (j : Json) : Option UInt64 := do
  let x ← toString? j >>= .remove0x
  let bytes ← Hex.toBytes x
  Bytes.toQuantityB64? bytes

def getTxExMap (j : Lean.Json) : IO (Option String × Bytes) := do
  let rlp ← j.find "rlp" >>= Lean.Json.toIoBytes
  match j.find? "expectException" with
  | .none => pure ⟨.none, rlp⟩
  | .some exj => do
    let exs ← exj.toIoString
    pure ⟨.some exs, rlp⟩

/-- The block-level access list a Glamsterdam fixture publishes beside an
Amsterdam block (`rlp_decoded.blockAccessList`, or `blockAccessList` on a
hand-authored block), read in its published order with no sorting and no
deduplication: the refinement in `refineBlockAccessListRejection` needs the
list exactly as delivered. The JSON prints its keys in an order that is not
the RLP field order, so the structure is rebuilt field by field. -/
def Lean.Json.toIoBlockAccessList (j : Lean.Json) : IO BlockAccessList := do
  let accounts ← j.toIoList
  accounts.mapM fun acc => do
    let indexOf (c : Lean.Json) : IO Nat :=
      (c.find "blockAccessIndex" >>= Lean.Json.toIoQuantityB64 "blockAccessIndex")
        <&> UInt64.toNat
    let address ← acc.find "address" >>= Lean.Json.toIoAdr
    let storageChanges ← (acc.find "storageChanges" >>= Lean.Json.toIoList) >>=
      List.mapM fun sc => do
        let slot ← sc.find "slot" >>= Lean.Json.toIoQuantityB256 "slot"
        let changes ← (sc.find "slotChanges" >>= Lean.Json.toIoList) >>= List.mapM fun c => do
          let i ← indexOf c
          let v ← c.find "postValue" >>= Lean.Json.toIoQuantityB256 "postValue"
          pure (i, v)
        pure (slot, changes)
    let storageReads ← (acc.find "storageReads" >>= Lean.Json.toIoList) >>=
      List.mapM (Lean.Json.toIoQuantityB256 "storageReads")
    let balanceChanges ← (acc.find "balanceChanges" >>= Lean.Json.toIoList) >>=
      List.mapM fun c => do
        let i ← indexOf c
        let v ← c.find "postBalance" >>= Lean.Json.toIoQuantityB256 "postBalance"
        pure (i, v)
    let nonceChanges ← (acc.find "nonceChanges" >>= Lean.Json.toIoList) >>=
      List.mapM fun c => do
        let i ← indexOf c
        let n ← c.find "postNonce" >>= Lean.Json.toIoQuantityB64 "postNonce"
        pure (i, n)
    let codeChanges ← (acc.find "codeChanges" >>= Lean.Json.toIoList) >>=
      List.mapM fun c => do
        let i ← indexOf c
        let code ← c.find "newCode" >>= Lean.Json.toIoBytes
        pure (i, code.toByteArray)
    pure { address, storageChanges, storageReads, balanceChanges, nonceChanges, codeChanges }

/-- Refine a consensus `blockAccessListHash` rejection with the list the fixture
publishes (goal C, fixed decision 9).

Consensus sees one thing: the hash of the list it built differs from the
header's `blockAccessListHash`, because an Amsterdam block carries only the
hash. The corpus names three reasons, and the fixture's published list -- a
verification aid, not part of the block -- is what tells them apart, so the
runner, which alone has it, does the telling:

- the header's hash is **not** the published list's hash: the header commits to
  something else, and the consensus identity `INVALID_BAL_HASH` stands;
- it is, and the published list's canonical re-arrangement
  (`BlockAccessList.canonicalise`) hashes to the computed list: the content is
  right and only the form is wrong -- `INCORRECT_BLOCK_FORMAT`;
- it is, and the content differs -- `INVALID_BLOCK_ACCESS_LIST`.

A block without a published list keeps its consensus identity. Classification
reads the typed rejection and the decoded header, never a rendered message. -/
def refineBlockAccessListRejection (blockJson : Lean.Json) (blockRlp : Bytes) :
    BlockRejection → IO BlockRejection
  | .block (.blockAccessListHash computed detail) => do
    let published? := blockJson.find? "blockAccessList" <|>
      (blockJson.find? "rlp_decoded" >>= Lean.Json.find? "blockAccessList")
    match published? with
    | none => pure (.block (.blockAccessListHash computed detail))
    | some listJson =>
      let published ← listJson.toIoBlockAccessList
      let header ← match rlpToBlockE blockRlp with
        | .ok ⟨block, _⟩ => pure block.header
        | .error reason =>
          .throw s!"error : block RLP undecodable while refining a block access \
            list rejection: {reason.render}"
      let publishedHash := published.hash
      if header.blockAccessListHash ≠ some publishedHash then
        pure (.block (.blockAccessListHash computed detail))
      else if published.canonicalise.hash = computed then
        pure (.block (.blockAccessListFormat (.text
          s!"published block access list ({published.length} entries) has the computed \
             content {computed} in a non-canonical arrangement, hash {publishedHash}")))
      else
        pure (.block (.blockAccessListContent (.text
          s!"published block access list hash = {publishedHash} (header-consistent) ≠ \
             computed block access list hash = {computed}")))
  | rejection => pure rejection

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
  -- The two Amsterdam header fields, read exactly as `requestsHash` is: absent
  -- in a fixture whose fork does not define them, present otherwise. Reading
  -- them is not running them -- an Amsterdam case is refused before this point
  -- -- but a header this runner parses must be the header the fixture wrote,
  -- and silently dropping two fields would make every such header re-encode to
  -- a different hash.
  let blockAccessListHash :=
    (json.find? "blockAccessListHash" >>= Lean.Json.toB256?)
  let slotNumber := (json.find? "slotNumber" >>= Lean.Json.toB64?)
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
    blockAccessListHash := blockAccessListHash
    slotNumber := slotNumber
  }

/-! ## The rule-data printer

`jaune --rules <fork>` prints one `ForkRules` record as JSON, so that
`scripts/check-fork-constants.sh` can compare what this build carries against
what `scripts/gen-fork-constants.py` extracted from the pinned
`execution-specs` revision. Neither side reads the other: the extractor reads
upstream and this reads the record, and the gate is the only place they meet.

The layout is **flat, keyed by dotted field path** rather than nested. A
comparison over dotted keys is exact key-by-key, its diff names the field that
moved rather than "the records differ", and the key *set* is itself checkable
-- which is what lets the gate refuse a `ForkRules` field that no one has
classified. -/

/-- A 20-byte address as `0x` and forty lowercase hex digits.

Written here rather than reused from `Adr.toHex`, which pads and cases for
human display: this string is compared byte-for-byte against a generator's
output, so its shape is part of the gate and is pinned by a `#guard`. -/
def Adr.toGateHex (a : Adr) : String :=
  let digits := "0123456789abcdef".toList
  let rec go (fuel n : Nat) (acc : List Char) : List Char :=
    match fuel with
    | 0 => acc
    | fuel + 1 => go fuel (n / 16) (digits[n % 16]! :: acc)
  "0x" ++ String.ofList (go 40 a.toNat [])

#guard Adr.toGateHex (0x00000961Ef480Eb55e80D19ad83579A64c007002 : Adr)
  = "0x00000961ef480eb55e80d19ad83579a64c007002"
#guard Adr.toGateHex (0 : Adr)
  = "0x0000000000000000000000000000000000000000"
#guard Adr.toGateHex (0x01 : Adr)
  = "0x0000000000000000000000000000000000000001"

private def jNat (n : Nat) : Lean.Json := Lean.toJson n

private def jOptNat : Option Nat → Lean.Json
  | none => .null
  | some n => jNat n

/-- One rule record as the flat JSON the constants gate compares.

One row is not a field of the record: `mainnetActivation` is the timestamp at
which `mainnetChainConfig` activates this record's fork on mainnet, or `null`
when the schedule names no such activation. It is printed here because the
pinned specification carries the same fact per fork as `FORK_CRITERIA`, and
D13 of the Amsterdam programme says the constants gate compares the two: the
day the pin's criterion for a fork becomes `ByTimestamp`, this row disagrees
with `null` and the gate names the missing `mainnet<Fork>Timestamp`. Reading
the schedule rather than a constant keeps the printer honest about what the
build actually activates. -/
def ForkRules.toGateJson (r : ForkRules) : Lean.Json :=
  Lean.Json.mkObj [
    ("mainnetActivation",
      jOptNat ((mainnetChainConfig.activations.find? (·.fork == r.fork)).map
        (·.timestamp))),
    ("blob.target", jNat r.blob.target),
    ("blob.max", jNat r.blob.max),
    ("blob.baseFeeUpdateFraction", jNat r.blob.baseFeeUpdateFraction),
    ("blob.reserveBaseCost", jOptNat r.blob.reserveBaseCost),
    ("code.maxCodeSize", jNat r.code.maxCodeSize),
    ("code.maxInitCodeSize", jNat r.code.maxInitCodeSize),
    ("tx.maxGas", jOptNat r.tx.maxGas),
    ("tx.maxBlobCount", jOptNat r.tx.maxBlobCount),
    ("block.maxRlpSize", jOptNat r.block.maxRlpSize),
    ("modexp.maxLength", jOptNat r.modexp.maxLength),
    ("modexp.flatComplexity", jOptNat r.modexp.flatComplexity),
    ("modexp.complexityCoeff", jNat r.modexp.complexityCoeff),
    ("modexp.iterationCoeff", jNat r.modexp.iterationCoeff),
    ("modexp.gasDivisor", jNat r.modexp.gasDivisor),
    ("modexp.minGas", jNat r.modexp.minGas),
    ("op.clz", Lean.Json.bool r.op.clz),
    ("op.slotnum", Lean.Json.bool r.op.slotnum),
    ("op.stackAccess", Lean.Json.bool r.op.stackAccess),
    ("precompiles",
      Lean.Json.arr ((r.precompiles.map (fun a => jNat a.toNat)).toArray)),
    ("gas.coldAccountAccess", jNat r.gas.coldAccountAccess),
    ("gas.callValue", jNat r.gas.callValue),
    ("gas.createAccess", jNat r.gas.createAccess),
    ("gas.storageClearRefund", jNat r.gas.storageClearRefund),
    ("gas.txBase", jNat r.gas.txBase),
    ("gas.txAccessListAddress", jNat r.gas.txAccessListAddress),
    ("gas.txAccessListStorageKey", jNat r.gas.txAccessListStorageKey),
    ("gas.floorTokenCost", jNat r.gas.floorTokenCost),
    ("gas.perAuthIntrinsic", jNat r.gas.perAuthIntrinsic),
    ("gas.codeReadSurcharge", jNat r.gas.codeReadSurcharge),
    -- EIP-8037's state-gas dimension. One key per field, `null` on a fork
    -- that meters in one dimension, exactly as `blob.reserveBaseCost` is
    -- `null` before EIP-7918: a comparison over dotted keys stays key-by-key
    -- and its diff names the number that moved. `stateGas.present` is the
    -- switch itself, so a fork acquiring or losing the dimension is one
    -- unambiguous row rather than ten simultaneous nulls.
    ("stateGas.present", Lean.Json.bool r.stateGas.isSome),
    ("stateGas.costPerStateByte",
      jOptNat (r.stateGas.map StateGasRules.costPerStateByte)),
    ("stateGas.stateBytesPerNewAccount",
      jOptNat (r.stateGas.map StateGasRules.stateBytesPerNewAccount)),
    ("stateGas.stateBytesPerStorageSet",
      jOptNat (r.stateGas.map StateGasRules.stateBytesPerStorageSet)),
    ("stateGas.stateBytesPerAuthBase",
      jOptNat (r.stateGas.map StateGasRules.stateBytesPerAuthBase)),
    ("stateGas.storageWrite",
      jOptNat (r.stateGas.map StateGasRules.storageWrite)),
    ("stateGas.accountWrite",
      jOptNat (r.stateGas.map StateGasRules.accountWrite)),
    ("stateGas.txValueCost",
      jOptNat (r.stateGas.map StateGasRules.txValueCost)),
    ("stateGas.accessListAddressFloorTokens",
      jOptNat (r.stateGas.map StateGasRules.accessListAddressFloorTokens)),
    ("stateGas.accessListStorageKeyFloorTokens",
      jOptNat (r.stateGas.map StateGasRules.accessListStorageKeyFloorTokens)),
    ("stateGas.systemMaxSstoresPerCall",
      jOptNat (r.stateGas.map StateGasRules.systemMaxSstoresPerCall)),
    ("header.blockAccessListHash", Lean.Json.bool r.header.blockAccessListHash),
    ("header.slotNumber", Lean.Json.bool r.header.slotNumber),
    -- EIP-7928's block-level access-list rules, under the same `present` +
    -- per-field `null` convention as `stateGas`.
    ("bal.present", Lean.Json.bool r.bal.isSome),
    ("bal.itemCost", jOptNat (r.bal.map BalRules.itemCost)),
    ("requests",
      Lean.Json.arr ((r.requests.map (fun p =>
        Lean.Json.arr #[jNat p.fst.toNat,
          Lean.Json.str (Adr.toGateHex p.snd)])).toArray))
  ]

/-- `jaune --rules <fork>`.

A fork whose rules this build does not implement is refused here exactly as it
is everywhere else: there is nothing to print, and printing another fork's
record would be the silent fallback the whole architecture exists to prevent.
Every declared fork resolves since goal C composed `amsterdamRules`, so today
the refusal is unreachable through a declared label; it stays for the next
declared-but-unimplemented fork. The gate's fork list and `Fork.supported` are
the same list by construction. -/
def runRulesPrinter (label : String) : IO Unit := do
  let some f := Fork.ofString? label
    | .throw
        s!"error : unknown --rules label {repr label}; declared labels are \
           {Fork.all.map Fork.toString}"
  let rules ← IO.ofExcept (f.rules.mapError SupportError.render)
  -- Named rather than dot-notated: this file `open`s `Jaune` but is not in it,
  -- so the definition above lands at the root while `ForkRules` is `Jaune`'s.
  .println (ForkRules.toGateJson rules).pretty

-- Goal B's `--rules-partial` printer and `ForkRules.toMeteringGateJson`, the
-- metering vehicle's partial view, are retired with the vehicle: every
-- declared fork is printed whole by `--rules`.

/-- `jaune --jumpdest-control <seed> <blobs> <size>`: the programme's D8
random-blob control for the jump-destination analysis (goal C, G4).

For each of `blobs` pseudo-random byte arrays of `size` bytes (a 64-bit LCG
seeded from `seed + i`, so the run is reproducible), compares three
computations of the valid jump-destination set: the pinned Amsterdam forward
walk `pinnedJumpDestsFrom` (with EIP-8024's `DUPN`/`SWAPN`/`EXCHANGE` cases),
the pre-Amsterdam forward walk `legacyJumpDestsFrom`, and the interpreter's own
backward scan `jumpable`. The first two are proved equal on every input
(`pinnedJumpDestsFrom_eq_legacy`); this control is the falsifier for that
theorem's *statement* and for `jumpable` agreeing with it, run on blobs large
enough to exercise EIP-7954's 64 KiB code ceiling. It also reports the slowest
blob's `jumpable` scan time, which is programme R3's measurement. -/
def runJumpdestControl (seedStr blobsStr sizeStr : String) : IO Bool := do
  let some seed := seedStr.toNat?
    | .throw s!"error : --jumpdest-control seed is not a number: {repr seedStr}"
  let some blobs := blobsStr.toNat?
    | .throw s!"error : --jumpdest-control blob count is not a number: {repr blobsStr}"
  let some size := sizeStr.toNat?
    | .throw s!"error : --jumpdest-control size is not a number: {repr sizeStr}"
  if blobs = 0 ∨ size = 0 then
    IO.println
      s!"RED — jumpdest-control: 0 blobs or 0 bytes compares nothing; an empty \
         control is never a vacuous pass"
    return false
  let mut ok := true
  let mut slowestMs : Nat := 0
  let mut slowestBlob : Nat := 0
  let mut slowestWalkMs : Nat := 0
  let mut destinations : Nat := 0
  let mut stackAccessBytes : Nat := 0
  for i in List.range blobs do
    let tGen ← IO.monoMsNow
    -- Knuth's MMIX LCG on `UInt64`; the top byte of each state is the next
    -- code byte, so every opcode value is equally likely and the three
    -- EIP-8024 bytes appear about `3 * size / 256` times per blob.
    let mut x : UInt64 := (seed + i).toUInt64 * 6364136223846793005 + 1442695040888963407
    let mut arr : Array UInt8 := Array.mkEmpty size
    for _ in List.range size do
      x := x * 6364136223846793005 + 1442695040888963407
      arr := arr.push (x >>> 56).toUInt8
    let cd : ByteArray := ⟨arr⟩
    stackAccessBytes := stackAccessBytes +
      (arr.toList.filter (fun b => b = 0xE6 ∨ b = 0xE7 ∨ b = 0xE8)).length
    -- Each phase's result is printed before the next timestamp is taken, so
    -- the compiler cannot float the pure computation past the clock read.
    IO.println s!"blob {i}: {cd.size} bytes generated, {stackAccessBytes} stack-access byte(s) so far"
    (← IO.getStdout).flush
    let tWalk ← IO.monoMsNow
    let pinned := pinnedJumpDestsFrom cd 0
    IO.println s!"blob {i}: pinned walk: {pinned.length} destination(s)"
    (← IO.getStdout).flush
    let tPinned ← IO.monoMsNow
    let legacy := legacyJumpDestsFrom cd 0
    IO.println s!"blob {i}: legacy walk: {legacy.length} destination(s)"
    (← IO.getStdout).flush
    let t0 ← IO.monoMsNow
    let scanned := (List.range size).filter (jumpable cd)
    IO.println s!"blob {i}: jumpable scan: {scanned.length} destination(s)"
    (← IO.getStdout).flush
    let t1 ← IO.monoMsNow
    IO.println
      s!"blob {i}: generate {tWalk - tGen} ms, pinned walk {tPinned - tWalk} ms, \
         legacy walk {t0 - tPinned} ms, jumpable scan {t1 - t0} ms"
    if t0 - tWalk > slowestWalkMs then
      slowestWalkMs := t0 - tWalk
    if t1 - t0 > slowestMs then
      slowestMs := t1 - t0
      slowestBlob := i
    destinations := destinations + pinned.length
    if pinned ≠ legacy then
      IO.println s!"RED — jumpdest-control: blob {i}: pinned walk ≠ legacy walk"
      ok := false
    if pinned ≠ scanned then
      IO.println s!"RED — jumpdest-control: blob {i}: pinned walk ≠ jumpable scan"
      ok := false
  if ok then
    IO.println
      s!"OK — jumpdest-control: {blobs} blob(s) × {size} bytes (seed {seed}): \
         pinned walk = legacy walk = jumpable on every blob; {destinations} \
         destination(s), {stackAccessBytes} DUPN/SWAPN/EXCHANGE byte(s); slowest \
         jumpable scan {slowestMs} ms (blob {slowestBlob}); slowest forward walks \
         {slowestWalkMs} ms"
  else
    IO.println
      s!"RED — jumpdest-control: {blobs} blob(s) × {size} bytes (seed {seed}): \
         a walk disagreed; see the lines above"
  return ok

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
    | .ok (.inr consensusRejection) =>
      -- An Amsterdam access-list hash rejection is refined with the fixture's
      -- published list before scoring; every other rejection passes through.
      let rejection ← refineBlockAccessListRejection blockJson blockRlp consensusRejection
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
    -- Every fork this case's network label can select must be one this build
    -- runs, and that is settled here -- before a header, a prestate, or a
    -- block is read. A declared fork whose rules are unimplemented is outside
    -- this build's domain, not evidence about the candidate: routed through
    -- the import path it would surface as `BLOCK #0 was expected valid but
    -- failed`, which reads as a verdict on a block this build never examined.
    -- A transition label is checked at both endpoints for the same reason,
    -- since its pre-fork blocks would otherwise run and only the post-fork
    -- ones refuse, halfway through a case.
    let _ ← IO.ofExcept
      ((spec.forks.mapM Fork.rules).mapError SupportError.render)
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
        s!"error : unknown --network label {repr label}; declared labels are \
           {Fork.all.map Fork.toString} and transitions of the form \
           <fork>To<fork>AtTime<seconds>. Of those, this build runs \
           {Fork.supported.map Fork.toString}"
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
       {Fork.supported.map Fork.toString} and transitions between them"
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
        s!"error : unknown --network label {repr label}; declared labels are \
           {Fork.all.map Fork.toString}, of which this build runs \
           {Fork.supported.map Fork.toString}"

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

The label lists are rendered from `Fork.all`, `Fork.supported`, and a
constructed `ForkTransition`, not written out by hand, so this text cannot
drift from what the build actually does -- which is exactly how the README's
fork list came to disagree with the binary. The declared and runnable sets are
printed separately because they are no longer the same list: a declared fork
whose rules are unimplemented parses here and is refused later, and a usage
text that folded the two would claim support this build does not have. -/
def usage : String :=
  s!"usage:
  jaune <fixture.json> [--network <label>] [--name <case>] \
[--notName <case>] [--index <n>]
  jaune t8n [options] --state.fork <label>
  jaune --vectors <address> <file.json> [--network <fork>]
  jaune --rules <fork>
  jaune --u256 <file.json>
  jaune --fake-exp <file.json>
  jaune --jumpdest-control <seed> <blobs> <size>
  jaune --version
  jaune --help

{T8n.usage}

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

declared networks:
  {Fork.all.map Fork.toString}
  transitions of the form <fork>To<fork>AtTime<seconds>, for example \
{ForkTransition.toString ⟨.prague, .osaka, 15000⟩}

runs at:
  {Fork.supported.map Fork.toString}
  Declared networks this build does not run: {Fork.unimplemented.map Fork.toString}. \
Such a label parses, and every case at it is then refused with \
UnsupportedForkError rather than answered.
"

def main : List String → IO Unit
  | [] => .throw "error : no arguments; run with --help for usage"
  | "--help" :: _ => .println usage
  | "-h" :: _ => .println usage
  -- The banner. A transition-tool framework identifies a binary by running it
  -- with `-v` and matching the first line against the wrapper registered for
  -- it, so this line is a wire surface: keep it one line and keep its shape.
  -- `jaune t8n --info` is the full handshake.
  | "-v" :: _ => .println s!"jaune version {T8n.version}"
  | "--version" :: _ => .println s!"jaune version {T8n.version}"
  | "t8n" :: rest => T8n.run rest
  | "--rules" :: label :: [] => runRulesPrinter label
  | "--rules" :: _ =>
    .throw "error : --rules takes exactly one fork label"
  | "--u256" :: pathStr :: [] => do
    if !(← runU256VectorFile pathStr) then IO.Process.exit 1
  | "--jumpdest-control" :: seed :: blobs :: size :: [] => do
    if !(← runJumpdestControl seed blobs size) then IO.Process.exit 1
  | "--jumpdest-control" :: _ =>
    .throw "error : --jumpdest-control takes exactly <seed> <blobs> <size>"
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
  -- read like a gate result while being none. `check-legacy.sh --dir` is the
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
           takes one file, and `check-legacy.sh --dir` is the enumerator for a tree"
