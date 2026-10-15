import Jaune.TraceJson
import Jaune.TraceTransaction

/-! Standalone message or signed-transaction tracing. Inputs state their scope;
transaction mode uses the proof-carrying public-pipeline driver. -/
open Lean Jaune

namespace Jaune.TraceRunner

private def required (j : Json) (key : String) : IO Json :=
  (j.find? key).toIO ("trace input is missing " ++ key)

private def stringField (j : Json) (key : String) : IO String := do
  IO.ofExcept ((← required j key).getStr?)

private def boolOr (j : Json) (key : String) (fallback : Bool) : IO Bool :=
  match j.find? key with
  | none => pure fallback
  | some value => IO.ofExcept value.getBool?

private def byteString (j : Json) (key : String) : IO Bytes :=
  match j.find? key with
  | none => pure []
  | some (.str text) => (T8n.hexToBytes? text).toIO (key ++ " must be prefixed hex bytes")
  | some _ => throw (IO.userError (key ++ " must be a hex string"))

private def decodeBenv (input : Json) (fork : Fork) (rules : ForkRules) : IO Benv := do
  let preState ← (← required input "alloc").toWorld
  let env ← T8n.decodeEnv rules false (← required input "env")
  let chainId ← T8n.natOr input "chainId" 1
  if chainId ≥ 2^64 then throw (IO.userError "chainId exceeds uint64")
  let benv : Benv := { (default : Benv) with
    state := preState
    stat := { (default : BenvStat) with
      fork := fork
      chainId := chainId.toUInt64
      origState := preState
      blockGasLimit := env.gasLimit
      blockHashes := env.blockHashes
      coinbase := env.coinbase
      number := env.number
      baseFeePerGas := env.baseFeePerGas
      time := env.timestamp.toB256
      prevRandao := env.prevRandao
      excessBlobGas := env.excessBlobGas
      parentBeaconBlockRoot := env.parentBeaconBlockRoot
      slotNumber := env.slotNumber } }
  return benv

private def decodeMessage (input : Json) (benv : Benv) (rules : ForkRules) : IO Msg := do
  let j ← required input "message"
  T8n.requireKnownFields "trace message" j ["kind", "caller", "address", "gas", "value",
    "input", "origin", "gasPrice", "stateGas", "static", "transferValue", "disablePrecompiles",
    "accessedAddresses", "accessedStorageKeys", "blobVersionedHashes"]
  let kind ← stringField j "kind"
  if kind != "call" && kind != "create" then
    throw (IO.userError "message.kind must be call or create")
  let caller ← T8n.readAdr "caller" (← required j "caller")
  let address ← T8n.readAdr "address" (← required j "address")
  let origin ← match j.find? "origin" with
    | none => pure caller
    | some value => T8n.readAdr "origin" value
  let gas ← T8n.natReq j "gas"
  let value ← T8n.natOr j "value" 0
  if value ≥ 2^256 then throw (IO.userError "message.value exceeds uint256")
  let data ← byteString j "input"
  let mut accessed : AdrSet := .emptyWithCapacity
  if let some values := j.find? "accessedAddresses" then
    for value in (← IO.ofExcept values.getArr?) do
      accessed := accessed.insert (← T8n.readAdr "accessedAddresses" value)
  let mut keys : KeySet := .emptyWithCapacity
  if let some values := j.find? "accessedStorageKeys" then
    for value in (← IO.ofExcept values.getArr?) do
      T8n.requireKnownFields "accessedStorageKeys entry" value ["address", "key"]
      let address ← T8n.readAdr "address" (← required value "address")
      let key ← T8n.readB256 "key" (← required value "key")
      keys := keys.insert (address, key)
  let mut hashes := []
  if let some values := j.find? "blobVersionedHashes" then
    for value in (← IO.ofExcept values.getArr?) do
      hashes := hashes ++ [← T8n.readB256 "blobVersionedHashes" value]
  let stateGas ← T8n.natOr j "stateGas" 0
  if rules.stateGas.isNone && stateGas != 0 then
    throw (IO.userError "stateGas requires a fork with state gas")
  let msg : Msg := { (default : Msg) with
    benv := benv
    tenv := { (default : Tenv) with stat := { (default : TenvStat) with
      origin := origin, gasPrice := (← T8n.natOr j "gasPrice" 0), gas := gas,
      stateGasReservoir := stateGas } }
    caller := caller
    target := if kind == "call" then some address else none
    currentTarget := address
    gas := gas
    value := value.toB256
    data := if kind == "call" then data else []
    codeAddress := if kind == "call" then some address else none
    code := if kind == "call" then benv.state.getCode address else ⟨data.toArray⟩
    depth := 1024
    shouldTransferValue := (← boolOr j "transferValue" true)
    isStatic := (← boolOr j "static" false)
    disablePrecompiles := (← boolOr j "disablePrecompiles" false)
    accessedAddresses := accessed
    accessedStorageKeys := keys
    stateGasGrant := stateGas }
  return { msg with tenv := { msg.tenv with stat := {
    msg.tenv.stat with blobVersionedHashes := hashes } } }

private inductive Input where
  | message (msg : Msg)
  | transaction (benv : Benv) (tx : Tx)

private def writeRow (cfg : TraceJson.Config) (handle : IO.FS.Handle) (row : Json) : IO Unit := do
  let line := row.compress ++ "\n"
  if line.utf8ByteSize > cfg.maxRowBytes then throw (IO.userError "trace: row byte limit exceeded")
  handle.putStr line
  handle.flush

def run (inputPath outputPath : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk inputPath .read
  let data ← handle.read (8 * 1024 * 1024 + 1)
  if data.size > 8 * 1024 * 1024 then throw (IO.userError "input exceeds 8 MiB")
  let text ← (String.fromUTF8? data).toIO "input is not UTF-8"
  let input ← IO.ofExcept (Json.parse text)
  T8n.requireKnownFields "trace request" input ["runId", "fork", "chainId", "alloc", "env",
    "message", "transaction", "memory", "maxSteps", "maxDataBytes", "maxRowBytes"]
  let runId ← stringField input "runId"
  if runId.trimAscii.toString.isEmpty then throw (IO.userError "runId must be nonempty")
  let forkName ← stringField input "fork"
  let fork ← (Fork.ofString? forkName).toIO "unknown fork"
  let rules ← IO.ofExcept (fork.rules.mapError SupportError.render)
  let benv ← decodeBenv input fork rules
  let selected : Input ← match input.find? "message", input.find? "transaction" with
    | some _, none => Input.message <$> decodeMessage input benv rules
    | none, some value =>
      match T8n.decodeTx value with
      | .ok tx => pure (.transaction benv tx)
      | .error error => throw (IO.userError ("transaction: " ++ error.render))
    | _, _ => throw (IO.userError "supply exactly one of message or transaction")
  let maxSteps ← match input.find? "maxSteps" with
    | none => pure none
    | some value => some <$> T8n.readNat "maxSteps" value
  let cfg : TraceJson.Config := {
    runId := runId, memory := (← boolOr input "memory" false), maxSteps := maxSteps
    maxDataBytes := (← T8n.natOr input "maxDataBytes" 1048576)
    maxRowBytes := (← T8n.natOr input "maxRowBytes" 1048576) }
  -- Exclusive directory creation refuses an existing path before opening files.
  IO.FS.createDir outputPath
  let directory : System.FilePath := outputPath
  let trace ← IO.FS.Handle.mk (directory / "trace.jsonl") .write
  let frames ← IO.FS.Handle.mk (directory / "frames.jsonl") .write
  let state ← IO.mkRef ({} : TraceJson.State)
  let details ← match selected with
    | .message msg => do
      let frame := if msg.target.isSome then Frame.ofCall msg else Frame.ofCreate msg
      let _ ← Trace.runFrame (TraceJson.sink cfg state trace frames) frame runId
      if !(← state.get).closed then throw (IO.userError "trace did not complete")
      pure [("scope", Json.str "message"), ("outcome", Json.str "executed"),
        ("traceComplete", Json.bool true),
        ("gasUsedScope", Json.str "frame grant minus settled remaining gas; no transaction settlement")]
    | .transaction initial tx => do
      let transactionCfg := { cfg with deferSummary := true }
      let refund := fun amount => do
        let current ← state.get
        if current.started then throw (IO.userError "authorization refund arrived after frame entry")
        state.set { current with rootRefund := amount }
      let result ← TraceTransaction.runTransaction
        (TraceJson.sink transactionCfg state trace frames) refund initial .init tx 0 runId
      let current ← state.get
      if current.started && !current.closed then throw (IO.userError "transaction frame did not close")
      let identity := [("scope", Json.str "transaction"), ("transactionIndex", toJson (0 : Nat)),
        ("transactionHash", Json.str (T8n.hexB256 (T8n.txHash tx))),
        ("authorizationRefund", toJson current.rootRefund),
        ("gasUsedScope", Json.str "transaction gas after intrinsic charge and settlement")]
      match result.value with
      | .error error =>
        if T8n.operational error then throw (IO.userError ("transaction: " ++ error.render))
        pure (identity ++ [("outcome", Json.str "rejected"), ("traceComplete", Json.bool false),
          ("error", Json.str error.render)])
      | .ok ⟨postState, bout⟩ =>
        let output ← result.messageOutput.toIO "accepted transaction has no message output"
        if output.returnData.length > cfg.maxDataBytes then
          throw (IO.userError "trace: output exceeds maxDataBytes")
        writeRow cfg trace (Json.mkObj [
          ("stateRoot", Json.str (T8n.hexB256 postState.root)),
          ("output", Json.str (T8n.hexBytes output.returnData)),
          ("gasUsed", Json.str (T8n.hexQuantity bout.cumulativeGasUsed)),
          ("pass", Json.bool output.error.isNone)])
        pure (identity ++ [("outcome", Json.str "executed"), ("traceComplete", Json.bool true)])
  let final ← state.get
  let metadata := Json.mkObj ([("runId", .str runId), ("fork", .str forkName),
    ("steps", toJson final.steps), ("complete", .bool true)] ++ details)
  let metadataHandle ← IO.FS.Handle.mk (directory / "run.json") .write
  writeRow cfg metadataHandle metadata

end Jaune.TraceRunner

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [input, output] => Jaune.TraceRunner.run input output; pure 0
    | _ =>
      (← IO.getStderr).putStrLn "usage: jaune-trace REQUEST.json NEW_OUTPUT_DIRECTORY"
      pure 2
  catch error =>
    (← IO.getStderr).putStrLn ("jaune-trace: " ++ error.toString)
    pure 2
