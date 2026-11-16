import Lean.Data.Json
import JauneConsensus.Engine
import JauneConsensus.Preset
import Jaune.Hash

/-!
# Recorded mainnet pairs control (goal `eip7002-cross-layer-v1`, O4)

Checks the consensus payload -> execution block conversion against recorded mainnet data in
`scripts/consensus/recorded-pairs/`: for each pair, the beacon block's execution payload (plus
`execution_requests` and `parent_root`) must reproduce the execution block's hash and requests
hash through `payloadHeader`, `Header.hash` and `computeRequestsHash`.
-/

namespace JauneConsensus.Harness

open Lean (Json)
open Jaune

/-- Parse failures carry the pair and field; strings are allowed in Harness code. -/
abbrev RPError := String

private def jfield (j : Json) (k : String) : Except RPError Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{k}'"

private def jstr (j : Json) (k : String) : Except RPError String := do
  match (← jfield j k).getStr? with
  | .ok s => pure s
  | .error _ => throw s!"field '{k}' is not a string"

private def jarr (j : Json) (k : String) : Except RPError (List Json) := do
  match (← jfield j k) with
  | .arr xs => pure xs.toList
  | _ => throw s!"field '{k}' is not an array"

/-- A beacon-API decimal string field. -/
private def jdec (j : Json) (k : String) : Except RPError Nat := do
  match (← jstr j k).toNat? with
  | some n => pure n
  | none => throw s!"field '{k}' is not a decimal string"

/-- A beacon-API `0x`-hex field as bytes. -/
private def jhex (j : Json) (k : String) : Except RPError Bytes := do
  let s ← jstr j k
  match Hex.toBytes (remove0x s) with
  | some bs => pure bs
  | none => throw s!"field '{k}' is not 0x hex"

private def jb256 (j : Json) (k : String) : Except RPError B256 := do
  let bs ← jhex j k
  match bs.toB256? with
  | some b => pure b
  | none => throw s!"field '{k}' is not 32 bytes"

private def jadr (j : Json) (k : String) : Except RPError Adr := do
  let bs ← jhex j k
  match bs.toAdr? with
  | some a => pure a
  | none => throw s!"field '{k}' is not 20 bytes"

private def ju64 (j : Json) (k : String) : Except RPError U64 := do
  let n ← jdec j k
  (U64.ofNat? n k).mapError (fun _ => s!"field '{k}' overflows uint64")

private def ju256 (j : Json) (k : String) : Except RPError U256 := do
  let n ← jdec j k
  (UIntN.ofNat? n k : M U256).mapError (fun _ => s!"field '{k}' overflows uint256")

/-- An exact-size byte vector, checked against `n`. -/
private def mkVec (n : Nat) (bs : Bytes) (what : String) :
    Except RPError (SszVector UInt8 n) :=
  if h : bs.toArray.size = n then .ok ⟨bs.toArray, h⟩
  else .error s!"{what}: want {n} bytes, got {bs.length}"

/-- A size-limited list, checked against `limit`. -/
private def mkList (xs : List α) (limit : Nat) (what : String) :
    Except RPError (SszList α limit) :=
  let arr := xs.toArray
  if h : arr.size ≤ limit then .ok ⟨arr, h⟩
  else .error s!"{what}: {xs.length} entries exceed limit {limit}"

private def jpubkey (j : Json) (k : String) : Except RPError BLSPubkey := do
  mkVec 48 (← jhex j k) s!"field '{k}'"

private def jsig (j : Json) (k : String) : Except RPError BLSSignature := do
  mkVec 96 (← jhex j k) s!"field '{k}'"

private def parseDepositRequest (j : Json) : Except RPError DepositRequest := do
  let pubkey ← jpubkey j "pubkey"
  let withdrawal_credentials ← jb256 j "withdrawal_credentials"
  let amount ← ju64 j "amount"
  let signature ← jsig j "signature"
  let index ← ju64 j "index"
  pure { pubkey, withdrawal_credentials, amount, signature, index }

private def parseWithdrawalRequest (j : Json) : Except RPError WithdrawalRequest := do
  let source_address ← jadr j "source_address"
  let validator_pubkey ← jpubkey j "validator_pubkey"
  let amount ← ju64 j "amount"
  pure { source_address, validator_pubkey, amount }

private def parseConsolidationRequest (j : Json) : Except RPError ConsolidationRequest := do
  let source_address ← jadr j "source_address"
  let source_pubkey ← jpubkey j "source_pubkey"
  let target_pubkey ← jpubkey j "target_pubkey"
  pure { source_address, source_pubkey, target_pubkey }

private def parseWithdrawal (j : Json) : Except RPError Withdrawal := do
  let index ← ju64 j "index"
  let validator_index ← ju64 j "validator_index"
  let address ← jadr j "address"
  let amount ← ju64 j "amount"
  pure { index, validator_index, address, amount }

private def parseTx (t : Json) : Except RPError (Transaction Preset.mainnet) := do
  let s ← match t.getStr? with
    | .ok s => pure s
    | .error _ => throw "transaction is not a string"
  let bs ← match Hex.toBytes (remove0x s) with
    | some bs => pure bs
    | none => throw "transaction is not 0x hex"
  mkList bs _ "transaction bytes"

private def parseExecutionRequests (j : Json) :
    Except RPError (ExecutionRequests Preset.mainnet) := do
  let deposits : SszList DepositRequest Preset.mainnet.MAX_DEPOSIT_REQUESTS_PER_PAYLOAD ←
    mkList (← (← jarr j "deposits").mapM parseDepositRequest) _ "deposits"
  let withdrawals : SszList WithdrawalRequest Preset.mainnet.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD ←
    mkList (← (← jarr j "withdrawals").mapM parseWithdrawalRequest) _ "withdrawal requests"
  let consolidations :
      SszList ConsolidationRequest Preset.mainnet.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD ←
    mkList (← (← jarr j "consolidations").mapM parseConsolidationRequest) _ "consolidations"
  pure { deposits, withdrawals, consolidations }

private def parseExecutionPayload (j : Json) :
    Except RPError (ExecutionPayload Preset.mainnet) := do
  let transactions : SszList (Transaction Preset.mainnet)
      Preset.mainnet.MAX_TRANSACTIONS_PER_PAYLOAD ←
    mkList (← (← jarr j "transactions").mapM parseTx) _ "transactions"
  let withdrawals : SszList Withdrawal Preset.mainnet.MAX_WITHDRAWALS_PER_PAYLOAD ←
    mkList (← (← jarr j "withdrawals").mapM parseWithdrawal) _ "withdrawals"
  let logs_bloom : SszVector UInt8 Preset.mainnet.BYTES_PER_LOGS_BLOOM ←
    mkVec _ (← jhex j "logs_bloom") "logs_bloom"
  let extra_data : SszList UInt8 Preset.mainnet.MAX_EXTRA_DATA_BYTES ←
    mkList (← jhex j "extra_data") _ "extra_data"
  let parent_hash ← jb256 j "parent_hash"
  let fee_recipient ← jadr j "fee_recipient"
  let state_root ← jb256 j "state_root"
  let receipts_root ← jb256 j "receipts_root"
  let prev_randao ← jb256 j "prev_randao"
  let block_number ← ju64 j "block_number"
  let gas_limit ← ju64 j "gas_limit"
  let gas_used ← ju64 j "gas_used"
  let timestamp ← ju64 j "timestamp"
  let base_fee_per_gas ← ju256 j "base_fee_per_gas"
  let block_hash ← jb256 j "block_hash"
  let blob_gas_used ← ju64 j "blob_gas_used"
  let excess_blob_gas ← ju64 j "excess_blob_gas"
  pure
    { parent_hash := parent_hash, fee_recipient := fee_recipient,
      state_root := state_root, receipts_root := receipts_root, logs_bloom := logs_bloom,
      prev_randao := prev_randao, block_number := block_number, gas_limit := gas_limit,
      gas_used := gas_used, timestamp := timestamp, extra_data := extra_data,
      base_fee_per_gas := base_fee_per_gas, block_hash := block_hash,
      transactions := transactions, withdrawals := withdrawals,
      blob_gas_used := blob_gas_used, excess_blob_gas := excess_blob_gas }

/-- The beacon block's `parent_root`, execution payload and execution requests. -/
private def parseBeacon (j : Json) : Except RPError
    (B256 × ExecutionPayload Preset.mainnet × ExecutionRequests Preset.mainnet) := do
  let msg ← jfield (← jfield j "data") "message"
  let body ← jfield msg "body"
  let parentRoot ← jb256 msg "parent_root"
  let payload ← parseExecutionPayload (← jfield body "execution_payload")
  let reqs ← parseExecutionRequests (← jfield body "execution_requests")
  pure (parentRoot, payload, reqs)

/-- The execution block's `result.hash` and `result.requestsHash`. -/
private def parseExecHashes (j : Json) : Except RPError (B256 × B256) := do
  let r ← jfield j "result"
  let h ← jb256 r "hash"
  let rh ← jb256 r "requestsHash"
  pure (h, rh)

/-- One recorded pair: file names and SHA-256 pins from the manifest. -/
structure PairSpec where
  label : String
  beaconFile : String
  beaconSha : String
  execFile : String
  execSha : String

private def parsePairSpec (j : Json) : Except RPError PairSpec := do
  let beacon ← jfield j "beacon"
  let exec ← jfield j "exec"
  let label ← jstr j "label"
  let beaconFile ← jstr beacon "file"
  let beaconSha ← jstr beacon "sha256"
  let execFile ← jstr exec "file"
  let execSha ← jstr exec "sha256"
  pure { label, beaconFile, beaconSha, execFile, execSha }

/-- Flip one bit of the first withdrawal request's validator pubkey, in memory only. -/
private def flipFirstWithdrawal (r : ExecutionRequests Preset.mainnet) :
    Except RPError (ExecutionRequests Preset.mainnet) := do
  let arr := r.withdrawals.toArray
  let some w := arr[0]? | .error "negative control needs a withdrawal request"
  let some b := w.validator_pubkey.toArray[0]? | .error "negative control: empty pubkey"
  let pk' : SszVector UInt8 48 :=
    ⟨w.validator_pubkey.toArray.setIfInBounds 0 (b ^^^ 1),
      by rw [Array.size_setIfInBounds, w.validator_pubkey.size_eq]⟩
  let w' : WithdrawalRequest := { w with validator_pubkey := pk' }
  pure { r with
    withdrawals := ⟨arr.setIfInBounds 0 w', by rw [Array.size_setIfInBounds]; exact r.withdrawals.size_le⟩ }

private def fmtB (b : B256) : String := "0x" ++ b.toHex

/-- Run one pair; the `Bool` is pass (positive mode) or failed-as-expected (negative mode). -/
private def runPairInner (dir : System.FilePath) (spec : PairSpec) (negative : Bool) :
    IO (Bool × String) := do
  let btext ← IO.FS.readFile (dir / spec.beaconFile)
  let etext ← IO.FS.readFile (dir / spec.execFile)
  let bsha := (Bytes.sha256 btext.toUTF8.toList).toHex
  if bsha != spec.beaconSha then
    throw (IO.userError s!"{spec.beaconFile}: sha256 {bsha}, manifest wants {spec.beaconSha}")
  let esha := (Bytes.sha256 etext.toUTF8.toList).toHex
  if esha != spec.execSha then
    throw (IO.userError s!"{spec.execFile}: sha256 {esha}, manifest wants {spec.execSha}")
  let .ok bjson := Json.parse btext | throw (IO.userError s!"{spec.beaconFile}: invalid JSON")
  let .ok ejson := Json.parse etext | throw (IO.userError s!"{spec.execFile}: invalid JSON")
  let (parentRoot, payload, reqs0) ← IO.ofExcept ((parseBeacon bjson).mapError IO.userError)
  let (execHash, execReqHash) ← IO.ofExcept ((parseExecHashes ejson).mapError IO.userError)
  let reqs ← IO.ofExcept
    (((if negative then flipFirstWithdrawal reqs0 else .ok reqs0)).mapError IO.userError)
  let list := getExecutionRequestsList reqs
  let computed := Header.hash (payloadHeader payload parentRoot list)
  let a := computed == payload.block_hash
  let b := computed == execHash
  let c := computeRequestsHash list == execReqHash
  if negative then
    if !a && !c then
      pure (true, s!"PASS {spec.label} (negative control failed as expected)")
    else
      pure (false, s!"FAIL {spec.label} (negative control): expected (a) and (c) to fail, \
        got a={a} b={b} c={c}")
  else
    if a && b && c then pure (true, s!"PASS {spec.label}")
    else
      pure (false, s!"FAIL {spec.label}: a={a} b={b} c={c} computed={fmtB computed} \
        payload.block_hash={fmtB payload.block_hash} exec.hash={fmtB execHash} \
        requests={fmtB (computeRequestsHash list)} exec.requestsHash={fmtB execReqHash}")

private def runPair (dir : System.FilePath) (spec : PairSpec) (negative : Bool) :
    IO (Bool × String) := do
  try
    runPairInner dir spec negative
  catch e =>
    pure (false, s!"FAIL {spec.label}: {e}")

/-- `recorded-pairs`: check every manifest pair; exit 0 only when all pairs behave as expected. -/
def cmdRecordedPairs (dir : System.FilePath) (negativeControl : Bool) : IO UInt32 := do
  let mtext ← IO.FS.readFile (dir / "manifest.json")
  let .ok mjson := Json.parse mtext | do
    IO.println "recorded-pairs: manifest.json is not valid JSON"
    return 1
  let pairs ← match mjson.getObjVal? "pairs" with
    | .ok (.arr xs) => IO.ofExcept ((xs.toList.mapM parsePairSpec).mapError IO.userError)
    | _ =>
      IO.println "recorded-pairs: manifest has no pairs array"
      return 1
  IO.println s!"recorded-pairs: {pairs.length} pairs from {dir}\
    {if negativeControl then " (negative control)" else ""}"
  let mut pass := 0
  let mut fail := 0
  for spec in pairs do
    let (ok, line) ← runPair dir spec negativeControl
    IO.println line
    if ok then pass := pass + 1 else fail := fail + 1
  if fail == 0 then
    IO.println s!"recorded-pairs: PASS {pass}, FAIL 0: OK"
    pure 0
  else
    IO.println s!"recorded-pairs: PASS {pass}, FAIL {fail}: FAILED"
    pure 1

end JauneConsensus.Harness
