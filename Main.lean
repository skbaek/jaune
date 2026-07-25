import «Elevm».Execution
import «Elevm».FixtureException
import «Elevm».ChainStore



----------------- TESTING DEFS ------------------

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

def Lean.Json.toIoB8L (j : Json) : IO B8L := do
  let x ← toIoString j >>= .remove0x
  (Hex.toB8L x).toIO ""

def Lean.Json.toIoAdr (j : Json) : IO Adr := do
  let x ← toIoString j >>= .remove0x
  (Hex.toAdr? x).toIO ""

def Lean.Json.toIoB64 (j : Json) : IO B64 := do
  let x ← toIoString j >>= .remove0x
  (Hex.toB64? x).toIO

def Lean.Json.toB256? (j : Json) : Option B256 := do
  let x ← toString? j >>= .remove0x
  Hex.toB256? x

def Lean.Json.toIoB256 (j : Json) : IO B256 := do
  let x ← toIoString j >>= .remove0x
  (Hex.toB256? x).toIO ""

def Lean.Json.toIoB64P (j : Json) : IO B64 := do
  let x ← toIoString j >>= .remove0x
  let xs ← (Hex.toB8L x).toIO ""
  return (B8L.toB64 xs)

def Lean.Json.toIoB256P (j : Json) : IO B256 := do
  let x ← toIoString j >>= .remove0x
  let xs ← (Hex.toB8L x).toIO ""
  return (B8L.toB256 xs)

def Lean.Json.toAcct : Lean.Json → IO Acct
  | .obj r => do
    let aux (xy : String × Lean.Json) : IO (B256 × B256) := do
      let x ← .remove0x xy.fst
      let bs ← (Hex.toB8L x).toIO ""
      let bs' ← xy.snd.toIoB8L
      return ⟨bs.toB256, bs'.toB256⟩
    let bal_json ← (r.get? "balance").toIO ""
    let nonce_json ← (r.get? "nonce").toIO ""
    let code_json ← (r.get? "code").toIO ""
    let stor_json ← (r.get? "storage").toIO "" >>= Lean.Json.toIoRBNode
    let bal ← Lean.Json.toIoB256P bal_json
    let nonce ← Lean.Json.toIoB64P nonce_json
    let code ← Lean.Json.toIoB8L code_json
    let stor ← List.mapM aux stor_json.toArray.toList
    return ⟨nonce, bal, Std.TreeMap.ofList stor _, code.toByteArray⟩
  | _ => .throw "cannot parse account (not .obj)"

def Lean.Json.toWorld (j : Lean.Json) : IO State := do
  let aux : State → (String × Lean.Json) → IO State :=
    fun | w, ⟨s, j⟩ => do
      let adr ← (Hex.toAdr? <| remove0x s).toIO ""
      let acct ← j.toAcct
      pure <| w.set adr acct
  let ob ← j.toIoRBNode
  List.foldlM aux .empty ob.toArray.toList

def Lean.Json.find? : String → Lean.Json → Option Lean.Json
  | k, .obj r => r.get? k
  | _, _ => .none

def Lean.Json.find : String → Lean.Json → IO Lean.Json
  | k, .obj r => (r.get? k).toIO s!"ERROR : FAILED JSON RETRIEVAL WITH KEY : {k}"
  | k, _ => .throw s!"ERROR : INPUT JSON IS NOT OBJECT, FAILED RETRIEVAL WITH KEY : {k}"

def getTxExMap (j : Lean.Json) : IO (Option String × B8L) := do
  let rlp ← j.find "rlp" >>= Lean.Json.toIoB8L
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
  let bloom ← json.find "bloom" >>= Lean.Json.toIoB8L
  let difficulty ← (json.find "difficulty" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let number ← (json.find "number" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let gasLimit ← (json.find "gasLimit" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let gasUsed ← (json.find "gasUsed" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let timestamp ← (json.find "timestamp" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let extraData ← json.find "extraData" >>= Lean.Json.toIoB8L
  let prevRandao ← json.find "mixHash" >>= Lean.Json.toIoB256
  let nonce ← json.find "nonce" >>= Lean.Json.toIoB64
  let baseFeePerGas ← (json.find "baseFeePerGas" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let withdrawalsRoot ← json.find "withdrawalsRoot" >>= Lean.Json.toIoB256
  let blobGasUsed ← (json.find "blobGasUsed" >>= Lean.Json.toIoB8L) <&> B8L.toNat
  let excessBlobGas ← (json.find "excessBlobGas" >>= Lean.Json.toIoB8L) <&> B8L.toNat
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

/-- Decode enough of a fixture block to select its parent snapshot, then run
the public block-import API. Both failure channels of `addBlockToChain` are
collapsed only after they have been handled explicitly. -/
def evaluateFixtureBlock (store : ChainStore) (blockRlp : B8L) :
    Except String (B256 × BlockChain) := do
  let ⟨block, blockHeaderHash⟩ ← rlpToBlock blockRlp
  let parent ← store.findParent block.header.parentHash
  match addBlockToChain parent blockRlp with
  | .error err => .error err
  | .ok (.inr err) => .error err
  | .ok (.inl child) => .ok ⟨blockHeaderHash, child⟩

def requireExpectedFailure (idx : Nat) (chainname : String)
    (expected : List FixtureException) (err : String) : IO Unit := do
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
def processBlockJsons (store : ChainStore) :
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
    match evaluateFixtureBlock store blockRlp with
    | .error err =>
      match expected? with
      | none =>
        .throw s!"BLOCK #{idx} ({chainname}) was expected valid but failed\n\
          raw actual: {repr err}\ncanonical actual: {actualExceptionDiagnostic err}"
      | some expected =>
        requireExpectedFailure idx chainname expected err
        processBlockJsons store rest
    | .ok ⟨tipHash, child⟩ =>
      match expected? with
      | some expected =>
        .throw s!"BLOCK #{idx} ({chainname}) was expected invalid but imported\n\
          expected: {expected.map FixtureException.toString}\ncomputed tip: {tipHash}"
      | none =>
        processBlockJsons (store.addResult (.ok ⟨tipHash, child⟩)) rest
  | [] => .ok store

def runBlockchainStTest : (Nat × String × Lean.Json) → IO Unit
  | ⟨idx, name, json⟩ => do
    .println s!"TEST NAME : {name}"
    .println s!"TEST INDEX : {idx}"

    let gbh_json ← json.find "genesisBlockHeader"
    let gbh ← gbh_json.toHeader
    let gb : Block := {header := gbh, txs := [], ommers := [], wds := []}
    let gbh_hash ← gbh_json.find "hash" >>= Lean.Json.toIoB256
    let gbh_hash' := (BLT.toB8L (Header.toBLT gbh)).keccak

    .guard
      (gbh_hash = gbh_hash')
      s!"error : genesis block header hash, expected = {gbh_hash}, computed = {gbh_hash'}"

    let genesisRLP ← json.find "genesisRLP" >>= Lean.Json.toIoB8L
    let genesisRLP' := gb.toBLT.toB8L
    .guard (genesisRLP = genesisRLP') "error : unexpected genesis block RLP."
    let (chainId : Nat) ←
      match gbh_json.find? "chainId" with
      | .none => .ok 1
      | .some chainIdJson => chainIdJson.toIoB64 <&> UInt64.toNat

    let preState ← json.find "pre" >>= Lean.Json.toWorld

    let chain : BlockChain :=
    {
      blocks := [gb]
      state := preState
      chainId := chainId.toUInt64
    }

    let blockJsons ← json.find "blocks" >>= Lean.Json.toIoList
    let store ← processBlockJsons (.init gbh_hash chain) blockJsons.putIndex
    let lastBlockHash ← json.find "lastblockhash" >>= Lean.Json.toIoB256
    let chain ← (store.findLast lastBlockHash).toIO
    let lastBlock ← chain.blocks.getLast?.toIO "error : no last block "
    let lastBlockHash' := (Header.toBLT lastBlock.header).toB8L.keccak
    .guard
      (lastBlockHash = lastBlockHash')
      s!"error : last block hash does not match\n  expected : {lastBlockHash}\n  computed : {lastBlockHash'}"

    let postStateRoot ← getPostStateRoot json
    .guard
      (postStateRoot = chain.state.root)
      s!"error : end state root does not match\n  expected : {postStateRoot}\n  computed : {chain.state.root}"

def fixtureCaseSelected (network : String) (testIdx : Option Nat)
    (incls excls : List String) : (Nat × String × Lean.Json) → IO Bool
  | ⟨idx, name, json⟩ => do
    if let some specIdx := testIdx then
      if specIdx ≠ idx then return false
    if ¬ (incls.isEmpty ∨ name ∈ incls) then
      return false
    if name ∈ excls then
      return false
    let caseNetwork ← json.find "network" >>= Lean.Json.toIoString
    return caseNetwork = network

def runTestFile (network : String) (testIdx : Option Nat)
  (incls excls : List String) (idxPath : Nat × String) : IO Unit := do
  let fileIdx := idxPath.fst
  let path := idxPath.snd
  .println "\n================================================================\n"
  .println s!"TEST FILE #{fileIdx} : {path}\n"
  let rb ← readJsonFile path >>= Lean.Json.toIoRBNode
  let js := rb.toArray.toList.putIndex
  let selected ← js.filterM <| fixtureCaseSelected network testIdx incls excls
  .println s!"NETWORK : {network}"
  .println s!"SELECTED CASES : {selected.length}"
  .println s!"SKIPPED CASES : {js.length - selected.length}"
  .guard (¬ selected.isEmpty)
    s!"ERROR : zero cases match the combined network/name/index filters \
       (network = {network}) in {path}"
  let _ ← selected.mapM runBlockchainStTest
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

def getFiles (path : System.FilePath) : IO (List System.FilePath) := do
  if (← System.FilePath.isDir path) then
    let paths ← System.FilePath.walkDir path
    List.filterM (fun path => path.isDir <&> .not) paths.toList
  else
    return [path]

def createMinimalEvm (adr : Adr) (input : B8L) (gasLimit : Nat) : Evm := {
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
    benvStat := default
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

def processVector (adr : Adr) : (Nat × Lean.Json) → IO Bool
  | ⟨idx, json⟩ => do
    let name ← (json.find? "Name" >>= Lean.Json.toString?).toIO s!"missing Name at index {idx}"
    let inputStr ← (json.find? "Input" >>= Lean.Json.toString?).toIO s!"missing Input for {name}"
    let input ← (Hex.toB8L <| remove0x inputStr).toIO s!"invalid Input hex for {name}"
    let isPositive := (json.find? "Expected").isSome
    let expected? ← if isPositive then
        let expStr ← (json.find? "Expected" >>= Lean.Json.toString?).toIO s!"missing Expected for {name}"
        some <$> (Hex.toB8L <| remove0x expStr).toIO s!"invalid Expected hex for {name}"
      else pure none
    let gas ← if isPositive then
        let g ← (json.find? "Gas").toIO s!"missing Gas for {name}"
        let gs := toString g
        (String.toNat? gs).toIO s!"invalid Gas for {name}"
      else pure 0
    let evm := createMinimalEvm adr input 0xffffffffffff
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
        .println s!"FAIL\t{name}\t(expected out={expected.toHex}, got error {err})"
        return false
    | none =>
      match res with
      | .error _ _ =>
        .println s!"PASS\t{name}"
        return true
      | .ok _ output =>
        .println s!"FAIL\t{name}\t(expected error, got ok out={output.toHex})"
        return false

def runVectorFile (addr : Adr) (path : String) : IO Bool := do
  let rb ← readJsonFile path >>= Lean.Json.toIoList
  let js := rb.putIndex
  let results ← js.mapM (processVector addr)
  let mut passes := 0
  for pass in results do
    if pass then passes := passes + 1
  let total := results.length
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
  | "lt", [x, y] => some (B256.lt_check x y)
  | "gt", [x, y] => some (B256.gt_check x y)
  | "slt", [x, y] => some (B256.slt_check x y)
  | "sgt", [x, y] => some (B256.sgt_check x y)
  | "eq", [x, y] => some (B256.eq_check x y)
  | "iszero", [x] => some (B256.eq_check x 0)
  | "and", [x, y] => some (x &&& y)
  | "or", [x, y] => some (x ||| y)
  | "xor", [x, y] => some (x ^^^ y)
  | "not", [x] => some (~~~ x)
  | "byte", [x, y] => some (List.getD y.toB8L x.toNat 0).toB256
  | "shl", [x, y] => some (y <<< x.toNat)
  | "shr", [x, y] => some (y >>> x.toNat)
  | "sar", [x, y] => some (B256.arithShiftRight y x.toNat)
  | "codec", [x] => some x.toB8L.toB256
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
        | [arg] => pure (some ((← Lean.Json.toIoB8L arg).keccak))
        | _ => pure none
      | "keccak_ba" => match argsJ with
        | [arg] => do
          let bs ← Lean.Json.toIoB8L arg
          pure (some (ByteArray.keccak 0 bs.length ⟨bs.toArray⟩))
        | _ => pure none
      | "ofB8L" => match argsJ with
        | [arg] => pure (some (B8L.toB256 (← Lean.Json.toIoB8L arg)))
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
  if passes == results.length then
    IO.println s!"OK — u256: {passes}/{results.length} PASS"; return true
  else
    IO.println s!"RED — u256: {passes}/{results.length} PASS, target not met"; return false

def main : List String → IO Unit
  | "--u256" :: pathStr :: [] => do
    if !(← runU256VectorFile pathStr) then IO.Process.exit 1
  | "--vectors" :: addrStr :: pathStr :: [] => do
    let addrStr2 := remove0x addrStr
    let paddedAddrStr :=
      String.ofList (List.replicate (40 - addrStr2.length) '0') ++ addrStr2
    let addr ← (Hex.toAdr? paddedAddrStr).toIO "invalid address"
    if !(← runVectorFile addr pathStr) then
      IO.Process.exit 1
  | path :: opts => do
    verbosityRef.set (List.contains opts "--verbose")
    let testIdx : Option Nat := getTestIndex opts
    let skip : Option Nat := getSkip opts
    let network := (getNetwork opts).getD "Prague"
    let ⟨incls, excls⟩ := getTestNames [] [] opts
    let files ← getFiles path
    let files :=
      match skip with
      | none => files
      | some n => files.drop n
    let _ ←
      List.mapM
        (runTestFile network testIdx incls excls)
        (files.map System.FilePath.toString).putIndex
    pure ()
  | _ => IO.throw "error : invalid arguments"
