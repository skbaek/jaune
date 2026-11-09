import Lean.Data.Json
import JauneConsensus.JointGloas
import Jaune.Hash

/-!
# Recorded devnet pairs control for Gloas (goal `eip8282-gloas-cross-layer-v1`, G4)

Checks the engine's Gloas payload → execution block conversion (`payloadToBlockG`,
`JointGloas.lean`) against recorded glamsterdam-devnet-8 data in
`scripts/consensus/recorded-devnet8/` (provenance in its `provenance.json`).

Every file listed in the directory's `SHA256SUMS` is read as bytes and checked against its digest
before anything is decoded; only listed files are read. Each `ssz/blk_<S>.ssz` (a Gloas
`SignedBeaconBlock`, mainnet preset) is one pair, with `ssz/env_<S-1>.ssz` (the
`SignedExecutionPayloadEnvelope` whose requests block `S` applies) and
`json/el_<block_hash>.json` (`eth_getBlockByHash` of the envelope payload's `block_hash`). For
each pair:

* link: the envelope's `beacon_block_root` is block `S`'s `parent_root`, and block `S`'s bid
  builds on the envelope payload's `block_hash` (FULL);
* requests: `block.body.parent_execution_requests` equals `envelope.execution_requests` as the
  five lists (`ExecutionRequests.lists`), and at least one EIP-8282 request is present;
* header: `payloadToBlockG` of the `Gloas.NewPayloadRequest` built from the envelope hashes to
  the payload's `block_hash` and to the recorded EL `hash`; its `requestsHash` is the recorded
  `requestsHash` and its `blockAccessListHash` the recorded `blockAccessListHash`. On a mismatch
  every header field is compared with the recorded EL block and the differing ones are named;
* control, on every run: one byte of the first builder request's `pubkey` is flipped in the
  request's `execution_requests`, and both the `requests_hash` check and the block-hash check
  must then fail. A run passes only if every real pair passes and every mutant is rejected.

The request's `versioned_hashes` are those of the payload's blob transactions
(`blobVersionedHashesOf`); the bid that committed the envelope's payload is in block `S-1`, which
is not recorded. `payloadToBlockG` does not read `versioned_hashes`, so they do not feed any
check here.
-/

namespace JauneConsensus.Harness.RecordedGloas

open Lean (Json)
open Jaune
open JauneConsensus

/-- The mainnet preset, which the devnet runs. -/
abbrev MP : Preset := Preset.mainnet

/-! ## `SHA256SUMS` -/

/-- `SHA256SUMS` lines `<hex>  ./<path>`, as (path without `./`, hex). -/
def parseSums (text : String) : Except String (List (String × String)) :=
  (text.splitOn "\n").filter (fun l => !l.all Char.isWhitespace) |>.mapM fun l =>
    match l.splitOn "  " with
    | [h, p] =>
      let p := if p.startsWith "./" then (p.drop 2).toString else p
      if h.length == 64 then .ok (p, h) else .error s!"SHA256SUMS: bad digest in '{l}'"
    | _ => .error s!"SHA256SUMS: bad line '{l}'"

/-- Read every listed file as bytes and check its SHA-256. -/
def readVerified (dir : System.FilePath) (sums : List (String × String)) :
    IO (List (String × ByteArray)) :=
  sums.mapM fun (p, h) => do
    let bs ← IO.FS.readBinFile (dir / p)
    let got := (Bytes.sha256 bs.toList).toHex
    if got != h then
      throw (IO.userError s!"{p}: sha256 {got}, SHA256SUMS wants {h}")
    pure (p, bs)

/-! ## The recorded EL block -/

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- A JSON-RPC quantity (`0x`-hex) as a number. -/
def hexNat? (s : String) : Option Nat :=
  let t := remove0x s
  if t.isEmpty then none
  else t.foldl (fun acc c => acc.bind fun n => (hexDigit? c).map (n * 16 + ·)) (some 0)

/-- A string field of the recorded block, lower-cased. -/
def elField (r : Json) (k : String) : Except String String :=
  match r.getObjValAs? String k with
  | .ok s => .ok s.toLower
  | .error _ => .error s!"EL block: missing string field '{k}'"

/-! ## Header fields against the recorded block -/

/-- How a computed header field is compared with the recorded one. -/
inductive Want where
  /-- Byte data, as lower-case `0x` hex. -/
  | bytes (hex : String)
  /-- A quantity. -/
  | qty (n : Nat)
  /-- The computed header has no such field. -/
  | absent

private def hx (bs : Bytes) : String := "0x" ++ bs.toHex
private def hb (b : B256) : String := "0x" ++ b.toHex

/-- The computed header's fields, keyed by the `eth_getBlockByHash` names. -/
def headerFields (h : Header) : List (String × Want) :=
  let ob : Option B256 → Want := fun o => match o with | some b => .bytes (hb b) | none => .absent
  let on : Option Nat → Want := fun o => match o with | some n => .qty n | none => .absent
  [("parentHash", .bytes (hb h.parentHash)),
   ("sha3Uncles", .bytes (hb h.ommersHash)),
   ("miner", .bytes ("0x" ++ h.coinbase.toHex)),
   ("stateRoot", .bytes (hb h.stateRoot)),
   ("transactionsRoot", .bytes (hb h.txsRoot)),
   ("receiptsRoot", .bytes (hb h.receiptRoot)),
   ("logsBloom", .bytes (hx h.bloom)),
   ("difficulty", .qty h.difficulty),
   ("number", .qty h.number),
   ("gasLimit", .qty h.gasLimit),
   ("gasUsed", .qty h.gasUsed),
   ("timestamp", .qty h.timestamp),
   ("extraData", .bytes (hx h.extraData)),
   ("mixHash", .bytes (hb h.prevRandao)),
   ("nonce", .qty h.nonce.toNat),
   ("baseFeePerGas", on h.baseFeePerGas),
   ("withdrawalsRoot", ob h.withdrawalsRoot),
   ("blobGasUsed", on h.blobGasUsed),
   ("excessBlobGas", on h.excessBlobGas),
   ("parentBeaconBlockRoot", ob h.parentBeaconBlockRoot),
   ("requestsHash", ob h.requestsHash),
   ("blockAccessListHash", ob h.blockAccessListHash),
   ("slotNumber", on (h.slotNumber.map UInt64.toNat))]

/-- The header fields that differ from the recorded block, each with both values. -/
def headerDiff (h : Header) (r : Json) : List String :=
  (headerFields h).filterMap fun (k, w) =>
    match elField r k, w with
    | .error e, _ => some e
    | .ok rec, .bytes c => if c == rec then none else some s!"{k}: computed {c}, recorded {rec}"
    | .ok rec, .qty n =>
      if hexNat? rec == some n then none else some s!"{k}: computed {n}, recorded {rec}"
    | .ok rec, .absent => some s!"{k}: computed header has none, recorded {rec}"

/-! ## One pair -/

/-- The control mutant: one byte of the first builder request's `pubkey` flipped (a builder
deposit if there is one, else a builder exit). -/
def flipFirstBuilderRequest (r : Gloas.ExecutionRequests) :
    Except String (Gloas.ExecutionRequests × String) :=
  let flip (pk : BLSPubkey) : BLSPubkey :=
    ⟨pk.toArray.modify 0 (· ^^^ 1), by rw [Array.size_modify, pk.size_eq]⟩
  match r.builder_deposits.toArray[0]? with
  | some d =>
    .ok ({ r with builder_deposits :=
      ⟨r.builder_deposits.toArray.setIfInBounds 0 { d with pubkey := flip d.pubkey }⟩ },
      "builder_deposits[0].pubkey[0] ^= 1")
  | none =>
    match r.builder_exits.toArray[0]? with
    | some e =>
      .ok ({ r with builder_exits :=
        ⟨r.builder_exits.toArray.setIfInBounds 0 { e with pubkey := flip e.pubkey }⟩ },
        "builder_exits[0].pubkey[0] ^= 1")
    | none => .error "no builder request to mutate"

/-- Where the engine's own `blobVersionedHashesOf` refuses the payload's transactions, if it
does: it decodes every transaction as a typed envelope (`Bytes.toExTx`), so a legacy (RLP list)
transaction is refused. Reported, not gated: no header field reads it. -/
def engineTxDecodeNote (payload : Gloas.ExecutionPayload MP) : Option String :=
  match blobVersionedHashesOf payload.txBytes with
  | .ok _ => none
  | .error e =>
    let bad := payload.txBytes.zipIdx.filter fun (t, _) => !(Bytes.toExTx t).isOk
    let at_ := bad.map fun (t, i) => s!"{i} (first byte 0x{(t.headD 0).toHex}, {t.length} bytes)"
    some s!"blobVersionedHashesOf refuses transaction(s) {at_}: {repr e}"

/-- The `Gloas.NewPayloadRequest` an envelope stands for, with `execution_requests := reqs`. The
versioned hashes are those of the payload's blob transactions; a legacy transaction (first byte
`≥ 0xc0`, an RLP list) carries none. -/
def newPayloadRequest (env : Gloas.ExecutionPayloadEnvelope MP) (reqs : Gloas.ExecutionRequests) :
    Except String (Gloas.NewPayloadRequest MP) := do
  let perTx ← env.payload.txBytes.zipIdx.mapM fun (t, i) =>
    if t.headD 0 ≥ 0xc0 then pure []
    else (blobVersionedHashesOf [t]).mapError fun e => s!"transaction {i}: {repr e}"
  let hashes := perTx.flatten
  let arr := hashes.toArray
  if h : arr.size ≤ MP.MAX_BLOB_COMMITMENTS_PER_BLOCK then
    pure { execution_payload := env.payload
           versioned_hashes := ⟨arr, h⟩
           parent_beacon_block_root := env.parent_beacon_block_root
           execution_requests := reqs }
  else throw "too many versioned hashes"

private def lookup (files : List (String × ByteArray)) (p : String) : Except String ByteArray :=
  match files.lookup p with
  | some b => .ok b
  | none => .error s!"{p} is not listed in SHA256SUMS"

private def decode (α : Type) [Ssz α] (what : String) (b : ByteArray) : Except String α :=
  match (deserialize b.toList : M α) with
  | .ok v => .ok v
  | .error e => .error s!"{what}: SSZ decode failed ({repr e})"

/-- One pair: the verdict lines; `true` iff every real check passes and the mutant is
rejected by both hash checks. -/
def runPair (files : List (String × ByteArray)) (slot : Nat) : Except String (Bool × List String) := do
  let blkPath := s!"ssz/blk_{slot}.ssz"
  let envPath := s!"ssz/env_{slot - 1}.ssz"
  let blk ← decode (Gloas.SignedBeaconBlock MP) blkPath (← lookup files blkPath)
  let senv ← decode (Gloas.SignedExecutionPayloadEnvelope MP) envPath (← lookup files envPath)
  let env := senv.message
  let payload := env.payload
  let elPath := s!"json/el_0x{payload.block_hash.toHex}.json"
  let elText ← match String.fromUTF8? (← lookup files elPath) with
    | some t => pure t
    | none => throw s!"{elPath}: not UTF-8"
  let elJson ← (Json.parse elText).mapError (fun e => s!"{elPath}: {e}")
  let r ← (elJson.getObjVal? "result").mapError (fun _ => s!"{elPath}: no result")
  let recHash ← elField r "hash"
  let recReqs ← elField r "requestsHash"
  let recBal ← elField r "blockAccessListHash"
  -- link and requests
  let linkRoot := blk.message.parent_root == env.beacon_block_root
  let linkFull := blk.message.body.signed_execution_payload_bid.message.parent_block_hash ==
    payload.block_hash
  let reqsEq := decide (blk.message.body.parent_execution_requests.lists =
    env.execution_requests.lists)
  let nBD := env.execution_requests.builder_deposits.toArray.size
  let nBE := env.execution_requests.builder_exits.toArray.size
  let has8282 := nBD + nBE > 0
  let note := engineTxDecodeNote payload
  -- the real request
  let req ← newPayloadRequest env env.execution_requests
  let hdr := (payloadToBlockG req).header
  let hash := hdr.hash
  let okBlockHash := hash == payload.block_hash && hb hash == recHash
  let okReqs := (hdr.requestsHash.map hb) == some recReqs
  let okBal := (hdr.blockAccessListHash.map hb) == some recBal
  -- the control mutant
  let (mreqs, what) ← flipFirstBuilderRequest env.execution_requests
  let mreq ← newPayloadRequest env mreqs
  let mhdr := (payloadToBlockG mreq).header
  let mutRejHash := !(mhdr.hash == payload.block_hash) && hb mhdr.hash != recHash
  let mutRejReqs := (mhdr.requestsHash.map hb) != some recReqs
  let real := linkRoot && linkFull && reqsEq && has8282 && okBlockHash && okReqs && okBal
  let control := mutRejHash && mutRejReqs
  let label := s!"slot {slot} / envelope {slot - 1} / EL #{payload.block_number.toNat} \
    (builder deposits {nBD}, builder exits {nBE})"
  let mut lines := [s!"{if real && control then "PASS" else "FAIL"} {label}",
    s!"  real: link={linkRoot && linkFull} parent_execution_requests==envelope.requests={reqsEq} \
      block_hash={okBlockHash} requests_hash={okReqs} block_access_list_hash={okBal} \
      ({hb hash}, requests_hash {(hdr.requestsHash.map hb).getD "none"})",
    s!"  control ({what}): block_hash rejected={mutRejHash} requests_hash rejected={mutRejReqs}"]
  if let some n := note then lines := lines ++ [s!"  note (not gated): {n}"]
  if !(okBlockHash && okReqs && okBal) then
    let diff := headerDiff hdr r
    lines := lines ++ (if diff.isEmpty then ["  header fields: all agree with the recorded block"]
      else diff.map ("  header field differs: " ++ ·))
  pure (real && control, lines)

/-- `recorded-pairs-gloas`: check `SHA256SUMS`, then every pair; exit 0 only when every pair
passes and every control mutant is rejected. -/
def cmdRecordedPairsGloas (dir : System.FilePath) : IO UInt32 := do
  let sums ← IO.ofExcept ((parseSums (← IO.FS.readFile (dir / "SHA256SUMS"))).mapError IO.userError)
  let files ← readVerified dir sums
  IO.println s!"recorded-pairs-gloas: SHA256SUMS OK ({files.length} files) in {dir}"
  let slots := sums.filterMap fun (p, _) =>
    if p.startsWith "ssz/blk_" && p.endsWith ".ssz" then
      ((p.drop "ssz/blk_".length).dropEnd ".ssz".length).toString.toNat?
    else none
  if slots.isEmpty then
    IO.println "recorded-pairs-gloas: no pairs: FAILED"
    return 1
  let mut pass := 0
  let mut fail := 0
  for s in slots do
    match runPair files s with
    | .ok (ok, lines) =>
      for l in lines do IO.println l
      if ok then pass := pass + 1 else fail := fail + 1
    | .error e =>
      IO.println s!"FAIL slot {s}: {e}"
      fail := fail + 1
  if fail == 0 then
    IO.println s!"recorded-pairs-gloas: PASS {pass}, FAIL 0 (controls rejected {pass}/{pass}): OK"
    pure 0
  else
    IO.println s!"recorded-pairs-gloas: PASS {pass}, FAIL {fail}: FAILED"
    pure 1

end JauneConsensus.Harness.RecordedGloas
