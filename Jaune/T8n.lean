-- T8n.lean : the `t8n` transition-tool frontend.
--
-- This module is runner-side infrastructure, not EVM semantics: it is
-- imported by `Main.lean` only, and deliberately not from the `Jaune` library
-- root, so that no proof client depends on it.
--
-- `t8n` is the interface every transition tool in the ecosystem exposes: read
-- a pre-state (`alloc`), an environment (`env`) and a transaction list
-- (`txs`) under a named fork, execute one state transition *outside* any
-- block-validation context, and emit the resulting `result` and post-state
-- `alloc`. The conformance target is the `execution-specs` checkout pinned as
-- `conformance_target` in `scripts/sources.json`; that revision owns every
-- field spelling, presence condition and ordering reproduced here.
--
-- The seam this module sits on is the one `stateTransitionE` uses. That
-- function validates a *sealed header*, builds a `Benv` from a chain and a
-- header, runs the body, computes six values, and *compares* them against the
-- header. A transition tool has no sealed header to compare against, so this
-- module drops `validateHeader` and `stateTransitionChecks`, builds the
-- `Benv` from `env` directly, runs the same body functions, computes the same
-- six values with the same functions, and *emits* rather than compares. No
-- EVM semantics is reimplemented: `processTransaction`, `processWithdrawals`,
-- `processGeneralPurposeRequests` and `processUncheckedSystemTransaction` are
-- called unchanged.
--
-- The one genuinely new piece of control flow is the reject-and-continue
-- fold. `applyTransactions` stops at the first failing transaction because a
-- block containing one is invalid; a transition tool instead *records* the
-- rejection and carries on, having discarded the failed transaction's state.
-- Rollback is therefore not a new mechanism -- it is not threading the new
-- state.

import Jaune.Transaction
import Jaune.FixtureException

open Jaune

----------------- SHARED JSON DECODING HELPERS ------------------

-- These moved here from `Main.lean` when the `t8n` frontend needed them: the
-- fixture runner and the transition tool decode the same `alloc` shape, and a
-- second copy of `toWorld` would be a second definition of what a pre-state
-- is. `Main.lean` imports this module, so its own uses are unchanged.

def Lean.Json.toIoList : Lean.Json → IO (List Json)
  | .arr a => return a.toList
  | _ => IO.throw "not an array"

def Lean.Json.toIoRBNode :
  Lean.Json → IO (Std.TreeMap.Raw String Json compare)
  | .obj r => return r
  | _ => IO.throw "not an object"

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

namespace Jaune
namespace T8n

----------------- THE FORK LANE -----------------

/-- The forks `jaune t8n --forks` advertises to a transition-tool framework.

This is the block-validation handshake. Goal A fixed it at the four forks
whose static and transition corpora the build then ran end to end, spelled out
as a hand-kept list; goal C composed `amsterdamRules` and left the list alone
on purpose (its fixed decision 7: advertising a fork is a user-consulted step,
not a side effect of `rules?` resolving). Goal `jaune-amsterdam-currency-v1`
took that step and made the line the build's own: the advertised lane *is* the
runnable lane, `Fork.supported`, and a guard says so, rather than a guard that
enumerates the gap. A fork therefore cannot be advertised here and refused by
`--state.fork`, nor run by `--state.fork` and hidden here. The basis for
advertising each fork is the evidence a framework then relies on: the fixture
corpora of `scripts/check-mainnet.sh` (the mainnet lane for Prague–BPO2, the
Glamsterdam devnet lane's static and transition suites for Amsterdam) and the
39-case transition-tool differential of `scripts/check-t8n.sh`.
`scripts/sources.json`'s `conformance_target.fork_lane` is the same list, and
`scripts/check-cli.sh` pins that the two agree.

Goal B's transaction-metering resolver (`meteringRules?`, `meteringForks`,
`laneRules`) is retired: there is one resolver, `Fork.rules`, for every label. -/
def advertisedForkLane : List Fork := Fork.supported

-- The advertised lane is the runnable lane, stated both ways so that a fork
-- added to `Fork.all` without rules would be neither advertised nor silently
-- omitted from a hand-kept list. Since goal `jaune-forks-by-construction-v1`
-- no fork can be in that state -- `Fork.ruleSet` is total, and
-- `Fork.supported_eq_all` and `Fork.unimplemented_eq_nil` are theorems -- so
-- these guards record today's lists rather than establishing them, and the
-- advertised lane is `Fork.all`. (Goal C's guards here said the lane was a *prefix* of
-- the runnable one with `[.amsterdam]` the only runnable fork not advertised;
-- goal B's said `Fork.unimplemented = [.amsterdam]` and named the metering
-- vehicle; each is rewritten to the statement that replaced it.)
#guard advertisedForkLane = Fork.supported
#guard advertisedForkLane = [.prague, .osaka, .bpo1, .bpo2, .amsterdam]
#guard advertisedForkLane.all (fun f => f.rules?.isSome)
#guard Fork.supported.filter (fun f => !advertisedForkLane.contains f) = []
#guard Fork.all.filter (fun f => !advertisedForkLane.contains f) = Fork.unimplemented
#guard Fork.unimplemented = []
#guard Fork.amsterdam.rules = .ok amsterdamRules
#guard Fork.all.all (fun f => f.rules.toOption.isSome)
#guard Fork.prague.rules = .ok pragueRules
#guard Fork.bpo2.rules = .ok bpo2Rules

----------------- JSON EMISSION ------------------

-- The conformance target writes its outputs with Python's
-- `json.dump(..., indent=4)`, whose exact spelling -- four-space indentation,
-- `": "` between key and value, `,\n` between members, `{}` / `[]` for the
-- empty cases, and `\uXXXX` for everything outside printable ASCII -- is part
-- of the wire format this tool reproduces. `Lean.Json`'s own pretty printer
-- spells all of that differently, so this is a small dedicated emitter rather
-- than a reuse.
--
-- It is deliberately a *value* type: the whole document is built and then
-- rendered once, so key order is fixed by construction and two runs on the
-- same input cannot differ.

inductive JOut : Type
  | str (s : String)
  | obj (fields : List (String × JOut))
  | arr (items : List JOut)

/-- One JSON string character, escaped the way Python's `json` module escapes
it with the default `ensure_ascii=True`. -/
def escapeChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c = '\n' then "\\n"
  else if c = '\r' then "\\r"
  else if c = '\t' then "\\t"
  else
    let n := c.toNat
    if n < 0x20 || n > 0x7e then
      if n ≤ 0xffff then
        "\\u" ++ (UInt16.ofNat n).toHex
      else
        -- A surrogate pair, spelled the way `ensure_ascii` spells it. No
        -- message this tool emits reaches this branch today; leaving it
        -- correct is cheaper than leaving it right by assumption.
        let v := n - 0x10000
        "\\u" ++ (UInt16.ofNat (0xd800 + (v >>> 10))).toHex
          ++ "\\u" ++ (UInt16.ofNat (0xdc00 + (v % 0x400))).toHex
    else String.ofList [c]

def escapeString (s : String) : String :=
  s.toList.foldl (fun acc c => acc ++ escapeChar c) ""

def quoted (s : String) : String := "\"" ++ escapeString s ++ "\""

def indentOf (n : Nat) : String := String.ofList (List.replicate n ' ')

mutual

/-- Render at an indentation depth measured in spaces, exactly as
`json.dump(..., indent=4)` does. -/
def JOut.render (depth : Nat) : JOut → String
  | .str s => quoted s
  | .obj [] => "{}"
  | .obj (f :: fs) =>
    "{\n" ++ JOut.renderFields (depth + 4) (f :: fs) ++ "\n" ++ indentOf depth ++ "}"
  | .arr [] => "[]"
  | .arr (i :: is) =>
    "[\n" ++ JOut.renderItems (depth + 4) (i :: is) ++ "\n" ++ indentOf depth ++ "]"

def JOut.renderFields (depth : Nat) : List (String × JOut) → String
  | [] => ""
  | [⟨k, v⟩] => indentOf depth ++ quoted k ++ ": " ++ JOut.render depth v
  | ⟨k, v⟩ :: rest =>
    indentOf depth ++ quoted k ++ ": " ++ JOut.render depth v ++ ",\n"
      ++ JOut.renderFields depth rest

def JOut.renderItems (depth : Nat) : List JOut → String
  | [] => ""
  | [v] => indentOf depth ++ JOut.render depth v
  | v :: rest =>
    indentOf depth ++ JOut.render depth v ++ ",\n" ++ JOut.renderItems depth rest

end

def JOut.toString (j : JOut) : String := j.render 0

----------------- HEX SPELLINGS ------------------

-- Two spellings, and confusing them is the easiest way to produce output that
-- parses and still differs from the target byte for byte. The `result`
-- document's numbers are the target's `HexNumber`: minimal, so zero is `0x0`
-- and seven is `0x7`. The `alloc` document's numbers are its
-- `ZeroPaddedHexNumber`: an even number of digits, so zero is `0x00` and
-- 0x1f926 is `0x01f926`.

/-- A minimal hex quantity: `0x0`, `0x7`, `0xa862`. -/
def hexQuantity (n : Nat) : String :=
  "0x" ++ String.dropZeroes (Bytes.toHex n.toBytes)

/-- An even-width hex quantity: `0x00`, `0x01`, `0x01f926`. -/
def hexPadded (n : Nat) : String :=
  let digits := String.dropZeroes (Bytes.toHex n.toBytes)
  if digits.length % 2 = 1 then "0x0" ++ digits else "0x" ++ digits

/-- A byte string: `0x`, `0x600160015500`. -/
def hexBytes (bs : Bytes) : String := "0x" ++ Bytes.toHex bs

def hexB256 (x : B256) : String := "0x" ++ x.toHex

def hexAdr (a : Adr) : String := "0x" ++ a.toHex

----------------- HEX READING ------------------

-- The wire's quantities are minimal, so `0x7` and `0x` are both legal and
-- neither is an even-length byte string. `Hex.toBytes` is the byte-string
-- reader and rejects both; these are the quantity readers.

def hexDigits? (s : String) : Option (List Char) :=
  match s.toList with
  | '0' :: 'x' :: cs => some cs
  | _ => none

/-- A JSON quantity as a natural. `0x` reads as zero, matching the target's
own `json_to_value` treatment of the empty quantity. -/
def hexToNat? (s : String) : Option Nat := do
  let cs ← hexDigits? s
  let ns ← cs.mapM Hexit.toB4
  some (ns.foldl (fun acc d => acc * 16 + d.toNat) 0)

def hexToBytes? (s : String) : Option Bytes := do
  let cs ← hexDigits? s
  if cs.length % 2 = 1 then none else Hex.toBytes (String.ofList cs)

def hexToAdr? (s : String) : Option Adr := do
  let cs ← hexDigits? s
  if cs.length ≠ 40 then none else Hex.toAdr? (String.ofList cs)

def hexToB256Wide? (s : String) : Option B256 := do
  let cs ← hexDigits? s
  if cs.length ≠ 64 then none else Hex.toB256? (String.ofList cs)

----------------- READING A JSON DOCUMENT ------------------

/-- A field, with JSON `null` read as absence. The target's models use
`exclude_none` on the way out and `Optional[...] = None` on the way in, so a
present `null` and an absent key are the same input to it. -/
def field? (j : Lean.Json) (k : String) : Option Lean.Json :=
  match j.find? k with
  | some .null => none
  | x => x

/-- Refuse an object carrying a field this tool does not know.

The target's input models are `extra="forbid"`, so an unrecognised field is an
error there too. Silently ignoring one is how a misspelled input silently runs
a different test. -/
def requireKnownFields (what : String) (j : Lean.Json) (known : List String) :
    IO Unit := do
  let ob ← j.toIoRBNode
  for k in ob.toArray.toList.map Prod.fst do
    if ¬ known.contains k then
      IO.throw
        s!"error : t8n {what} carries the unrecognised field {repr k}; \
           the recognised fields are {known}"

def readNat (label : String) (v : Lean.Json) : IO Nat :=
  match v with
  | .str s => (hexToNat? s).toIO s!"error : t8n {label} is not a hex quantity"
  | _ => IO.throw s!"error : t8n {label} must be a hex quantity string"

def readB256 (label : String) (v : Lean.Json) : IO B256 :=
  match v with
  | .str s => (hexToB256Wide? s).toIO s!"error : t8n {label} is not a 32-byte hash"
  | _ => IO.throw s!"error : t8n {label} must be a 32-byte hash string"

def readAdr (label : String) (v : Lean.Json) : IO Adr :=
  match v with
  | .str s => (hexToAdr? s).toIO s!"error : t8n {label} is not a 20-byte address"
  | _ => IO.throw s!"error : t8n {label} must be a 20-byte address string"

def natOr (j : Lean.Json) (k : String) (dflt : Nat) : IO Nat :=
  match field? j k with
  | none => pure dflt
  | some v => readNat k v

def natReq (j : Lean.Json) (k : String) : IO Nat := do
  let v ← (field? j k).toIO s!"error : t8n input is missing the {k} field"
  readNat k v

----------------- INPUT: THE ENVIRONMENT ------------------

/-- Everything `env` contributes to a `BenvStat`, after the target's two
derivations have been applied. Fields no lane consumes -- `currentDifficulty`,
`extraData`, the block-access-list pair -- are accepted and dropped, exactly
as the target accepts and does not consume them. -/
structure T8nEnv : Type where
  coinbase : Adr
  gasLimit : Nat
  number : Nat
  timestamp : Nat
  prevRandao : B256
  baseFeePerGas : Nat
  excessBlobGas : Nat
  parentBeaconBlockRoot : B256
  blockHashes : List B256
  withdrawals : List Withdrawal
  /-- EIP-7843 (goal C): `env.slotNumber`, what `SLOTNUM` pushes. The target's
  default block environment sets `slot_number = U64(0)`, and its driver passes
  an absent field through as `None`, on which no consuming instruction can
  run at all; this lane reads an absent field as zero. -/
  slotNumber : UInt64

def envKnownFields : List String :=
  [ "currentCoinbase", "currentGasLimit", "currentNumber", "currentTimestamp",
    "currentRandom", "currentDifficulty", "currentBaseFee",
    "currentExcessBlobGas", "currentBlobGasUsed", "slotNumber",
    "parentDifficulty", "parentTimestamp", "parentBaseFee", "parentGasUsed",
    "parentGasLimit", "parentUncleHash", "parentBlobGasUsed",
    "parentExcessBlobGas", "parentBeaconBlockRoot", "parentHash",
    "blockHashes", "ommers", "withdrawals", "extraData",
    "blockAccessListHash", "blockAccessLists" ]

/-- The target's `Environment` defaults, which a missing field takes. -/
def defaultCoinbaseHex : String := "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba"
def defaultGasLimit : Nat := 120000000
def defaultNumber : Nat := 1
def defaultTimestamp : Nat := 1000

def readWithdrawal (v : Lean.Json) : IO Withdrawal := do
  requireKnownFields "withdrawal" v ["index", "validatorIndex", "address", "amount"]
  let index ← natReq v "index"
  let validatorIndex ← natReq v "validatorIndex"
  let addressJson ← (field? v "address").toIO "error : t8n withdrawal is missing address"
  let address ← readAdr "withdrawal address" addressJson
  let amount ← natReq v "amount"
  return {
    globalIndex := index.toUInt64,
    validatorIndex := validatorIndex.toUInt64,
    recipient := address,
    amount := amount.toB256
  }

/-- The `BLOCKHASH` window the target builds: the hashes of the `min(256, n)`
blocks preceding block `n`, oldest first.

Two shapes, both the target's. An **absent or empty** `blockHashes` yields the
empty window whatever the block number says -- its `_resolve_block_hashes`
returns early before it looks at the number, and that is the shape every state
test arrives in. A **non-empty** one is expanded over the window; the target
represents a gap in it as a `None` placeholder, and `BenvStat.blockHashes` has
no placeholder, so a gap is refused here rather than silently read as some
other block's hash. Every corpus case and every `fill` invocation that
supplies the map at all supplies it dense. -/
def readBlockHashes (j : Lean.Json) (number : Nat) : IO (List B256) := do
  let entries : List (Nat × B256) ←
    match field? j "blockHashes" with
    | none => pure []
    | some v => do
      let ob ← v.toIoRBNode
      ob.toArray.toList.mapM fun ⟨k, hv⟩ => do
        let n ← (hexToNat? k).toIO
          s!"error : t8n blockHashes key {repr k} is not a hex quantity"
        let h ← readB256 "blockHashes entry" hv
        pure ⟨n, h⟩
  if entries.isEmpty then return []
  let window := min 256 number
  let first := number - window
  (List.range window).mapM fun i => do
    let want := first + i
    match entries.find? (fun e => e.fst = want) with
    | some e => pure e.snd
    | none =>
      IO.throw
        s!"error : t8n env.blockHashes has no entry for block {want}; the \
           window this tool needs is blocks {first} through {number - 1}"

def decodeEnv (rules : ForkRules) (stateTest : Bool) (j : Lean.Json) : IO T8nEnv := do
  requireKnownFields "env" j envKnownFields
  match field? j "ommers" with
  | some (.arr a) =>
    IO.guard a.isEmpty
      "error : t8n env.ommers is non-empty; the Prague-BPO2 lane is \
       proof-of-stake and has no ommers"
  | _ => pure ()
  let coinbase ←
    match field? j "currentCoinbase" with
    | none => (hexToAdr? defaultCoinbaseHex).toIO "error : bad default coinbase"
    | some v => readAdr "env.currentCoinbase" v
  let gasLimit ← natOr j "currentGasLimit" defaultGasLimit
  let number ← natOr j "currentNumber" defaultNumber
  let timestamp ← natOr j "currentTimestamp" defaultTimestamp
  let prevRandao ← natOr j "currentRandom" 0
  -- `currentBaseFee` if given, else the target's parent derivation.
  let baseFeePerGas ←
    match field? j "currentBaseFee" with
    | some v => readNat "env.currentBaseFee" v
    | none => do
      let parentGasLimit ← natReq j "parentGasLimit"
      let parentGasUsed ← natReq j "parentGasUsed"
      let parentBaseFee ← natReq j "parentBaseFee"
      IO.ofExcept <|
        (calculateBaseFeePerGas gasLimit parentGasLimit parentGasUsed parentBaseFee).mapError
          BlockValidationError.render
  -- `currentExcessBlobGas` if given, else the target's parent derivation,
  -- which feeds `calculate_excess_blob_gas` a header carrying only the three
  -- parent fields it reads.
  let excessBlobGas ←
    match field? j "currentExcessBlobGas" with
    | some v => readNat "env.currentExcessBlobGas" v
    | none => do
      let parentBlobGasUsed ← natOr j "parentBlobGasUsed" 0
      let parentExcessBlobGas ← natOr j "parentExcessBlobGas" 0
      let parentBaseFee ← natOr j "parentBaseFee" 0
      let parentHeader : Header :=
        { parentHash := 0, ommersHash := 0, coinbase := coinbase, stateRoot := 0,
          txsRoot := 0, receiptRoot := 0, bloom := List.replicate 256 0,
          difficulty := 0, number := 0, gasLimit := 0, gasUsed := 0,
          timestamp := 0, extraData := [], prevRandao := 0, nonce := 0,
          baseFeePerGas := parentBaseFee, withdrawalsRoot := 0,
          blobGasUsed := parentBlobGasUsed, excessBlobGas := parentExcessBlobGas,
          parentBeaconBlockRoot := 0, requestsHash := none,
          blockAccessListHash := none, slotNumber := none }
      pure (calculateExcessBlobGas rules.blob parentHeader)
  -- A state test performs no system operations, so the parent beacon block
  -- root is never read; the target sets it to `None` in that mode.
  let parentBeaconBlockRoot ←
    if stateTest then pure 0
    else
      match field? j "parentBeaconBlockRoot" with
      | none => pure 0
      | some v => readB256 "env.parentBeaconBlockRoot" v
  let blockHashes ← if stateTest then pure [] else readBlockHashes j number
  let withdrawals ←
    match field? j "withdrawals" with
    | none => pure []
    | some v => do
      let items ← v.toIoList
      items.mapM readWithdrawal
  let slotNumber ← natOr j "slotNumber" 0
  return {
    coinbase := coinbase, gasLimit := gasLimit, number := number,
    timestamp := timestamp, prevRandao := prevRandao.toB256,
    baseFeePerGas := baseFeePerGas, excessBlobGas := excessBlobGas,
    parentBeaconBlockRoot := parentBeaconBlockRoot,
    blockHashes := blockHashes, withdrawals := withdrawals,
    slotNumber := slotNumber.toUInt64
  }

----------------- INPUT: TRANSACTIONS ------------------

/-- Why one `txs` entry could not become a `Tx`.

These are the *parse* rejections of definition-of-done row G3: the target's
`convert_transaction` raising before `process_transaction` ever runs, which is
recorded in `rejected` and leaves the transactions trie untouched. They are a
typed channel precisely so that the fold classifies by constructor and never
by reading back its own rendered text. -/
inductive TxParseError : Type
  | notObject
  | unknownField (name : String)
  | missingField (name : String)
  | badField (name : String)
  | unsupportedType (ty : Nat)
  -- A shape that is *representable* in the target's transaction classes and
  -- not in Jaune's, and which every fork on this lane rejects anyway. A
  -- type-3 or type-4 transaction with no receiver is the whole of this case:
  -- `TxType.three`/`.four` carry a mandatory `Adr`, so the tuple cannot be
  -- built, while the target builds it and rejects it one step later inside
  -- `check_transaction`. Both arrive at the same official identity, and this
  -- constructor is what keeps that true -- the reason it carries is the very
  -- one Jaune's own RLP decoder raises for the same shape
  -- (`Transaction.lean`, the type-3 receiver check).
  | validation (reason : TxValidationError)

def TxParseError.render : TxParseError → String
  | .notObject => "JauneT8n.TX_PARSE_NOT_AN_OBJECT"
  | .unknownField n => "JauneT8n.TX_PARSE_UNKNOWN_FIELD: " ++ n
  | .missingField n => "JauneT8n.TX_PARSE_MISSING_FIELD: " ++ n
  | .badField n => "JauneT8n.TX_PARSE_MALFORMED_FIELD: " ++ n
  | .unsupportedType ty => s!"JauneT8n.TX_PARSE_UNSUPPORTED_TYPE: {ty}"
  | .validation reason =>
    match FixtureException.ofTxValidationError reason with
    | some e => e.toString
    | none => "JauneT8n.TX_PARSE_UNMAPPED: " ++ reason.render

abbrev TxParse := Except TxParseError

def txKnownFields : List String :=
  [ "type", "chainId", "nonce", "gasPrice", "maxPriorityFeePerGas",
    "maxFeePerGas", "gas", "gasLimit", "to", "value", "data", "input",
    "accessList", "maxFeePerBlobGas", "blobVersionedHashes",
    "authorizationList", "v", "yParity", "r", "s",
    -- Accepted and not consumed. `fill` dumps the whole testing
    -- `Transaction`, which retains `secretKey` and `sender` alongside the
    -- populated signature it produced; the target's own CLI drops both.
    "secretKey", "sender", "hash" ]

def txNat (j : Lean.Json) (k : String) : TxParse Nat :=
  match field? j k with
  | none => .error (.missingField k)
  | some (.str s) => (hexToNat? s).toExcept (.badField k)
  | some _ => .error (.badField k)

def txNatOr (j : Lean.Json) (k : String) (dflt : Nat) : TxParse Nat :=
  match field? j k with
  | none => .ok dflt
  | some (.str s) => (hexToNat? s).toExcept (.badField k)
  | some _ => .error (.badField k)

def txBytes (j : Lean.Json) (k k' : String) : TxParse Bytes :=
  match field? j k, field? j k' with
  | some (.str s), _ => (hexToBytes? s).toExcept (.badField k)
  | _, some (.str s) => (hexToBytes? s).toExcept (.badField k')
  | none, none => .ok []
  | _, _ => .error (.badField k)

/-- The `to` field, with the target's two spellings of contract creation: an
absent/`null` value and the empty string. -/
def txReceiver (j : Lean.Json) : TxParse (Option Adr) :=
  match field? j "to" with
  | none => .ok none
  | some (.str "") => .ok none
  | some (.str s) => (hexToAdr? s).toExcept (.badField "to") |>.map some
  | some _ => .error (.badField "to")

def txAccessList (j : Lean.Json) : TxParse AccessList :=
  match field? j "accessList" with
  | none => .ok []
  | some (.arr items) =>
    items.toList.mapM fun it =>
      match field? it "address", field? it "storageKeys" with
      | some (.str a), some (.arr keys) => do
        let adr ← (hexToAdr? a).toExcept (.badField "accessList.address")
        let ks ← keys.toList.mapM fun kj =>
          match kj with
          | .str ks => (hexToB256Wide? ks).toExcept (.badField "accessList.storageKeys")
          | _ => .error (.badField "accessList.storageKeys")
        .ok ⟨adr, ks⟩
      | _, _ => .error (.badField "accessList")
  | some _ => .error (.badField "accessList")

def txBlobHashes (j : Lean.Json) : TxParse (List B256) :=
  match field? j "blobVersionedHashes" with
  | none => .error (.missingField "blobVersionedHashes")
  | some (.arr items) =>
    items.toList.mapM fun it =>
      match it with
      | .str s => (hexToB256Wide? s).toExcept (.badField "blobVersionedHashes")
      | _ => .error (.badField "blobVersionedHashes")
  | some _ => .error (.badField "blobVersionedHashes")

def txAuths (j : Lean.Json) : TxParse (List Auth) :=
  match field? j "authorizationList" with
  | none => .error (.missingField "authorizationList")
  | some (.arr items) =>
    items.toList.mapM fun it => do
      let chainId ← txNatOr it "chainId" 0
      let adrJson := field? it "address"
      let address ←
        match adrJson with
        | some (.str a) => (hexToAdr? a).toExcept (.badField "authorizationList.address")
        | _ => .error (.badField "authorizationList.address")
      let nonce ← txNatOr it "nonce" 0
      let yParity ←
        match field? it "v", field? it "yParity" with
        | some (.str s), _ => (hexToNat? s).toExcept (.badField "authorizationList.v")
        | _, some (.str s) => (hexToNat? s).toExcept (.badField "authorizationList.yParity")
        | _, _ => .error (.missingField "authorizationList.v")
      let r ← txNatOr it "r" 0
      let s ← txNatOr it "s" 0
      .ok {
        chainId := chainId.toB256, address := address, nonce := nonce.toUInt64,
        yParity := yParity, r := r.toB256, s := s.toB256
      }
  | some _ => .error (.badField "authorizationList")

/-- One `txs` entry as a `Tx`.

The target reaches its transaction object in two hops -- a pydantic
`Transaction` and then `TransactionLoad` -- and this reproduces the composite
contract of both: the field spellings and defaults of the first, the
type-dispatch and shape rules of the second. -/
def decodeTx (j : Lean.Json) : TxParse Tx := do
  match j with
  | .obj ob =>
    for k in ob.toArray.toList.map Prod.fst do
      if ¬ txKnownFields.contains k then
        .error (.unknownField k)
  | _ => .error .notObject
  let ty ← txNatOr j "type" 0
  let nonce ← txNatOr j "nonce" 0
  let gas ←
    match field? j "gas", field? j "gasLimit" with
    | some (.str s), _ => (hexToNat? s).toExcept (.badField "gas")
    | _, some (.str s) => (hexToNat? s).toExcept (.badField "gasLimit")
    | none, none => .ok 21000
    | _, _ => .error (.badField "gas")
  let value ← txNatOr j "value" 0
  let data ← txBytes j "input" "data"
  let v ← txNatOr j "v" 0
  let r ← txNatOr j "r" 0
  let s ← txNatOr j "s" 0
  let receiver ← txReceiver j
  let chainId ← txNatOr j "chainId" 1
  let txType : TxType ←
    match ty with
    | 0 => do
      let gasPrice ← txNat j "gasPrice"
      .ok (.zero gasPrice receiver)
    | 1 => do
      let gasPrice ← txNat j "gasPrice"
      let al ← txAccessList j
      .ok (.one chainId.toUInt64 gasPrice receiver al)
    | 2 => do
      let maxPriorityFee ← txNat j "maxPriorityFeePerGas"
      let maxFee ← txNat j "maxFeePerGas"
      let al ← txAccessList j
      .ok (.two chainId.toUInt64 maxPriorityFee maxFee receiver al)
    | 3 => do
      let maxPriorityFee ← txNat j "maxPriorityFeePerGas"
      let maxFee ← txNat j "maxFeePerGas"
      let al ← txAccessList j
      let maxBlobFee ← txNat j "maxFeePerBlobGas"
      let hashes ← txBlobHashes j
      match receiver with
      | none =>
        .error (.validation (.type3ContractCreation
          (.text "type-3 transactions cannot create contracts")))
      | some dest =>
        .ok (.three chainId.toUInt64 maxPriorityFee maxFee dest al maxBlobFee hashes)
    | 4 => do
      let maxPriorityFee ← txNat j "maxPriorityFeePerGas"
      let maxFee ← txNat j "maxFeePerGas"
      let al ← txAccessList j
      let auths ← txAuths j
      match receiver with
      | none =>
        .error (.validation (.type4ContractCreation
          (.text "type-4 transactions cannot create contracts")))
      | some dest => .ok (.four chainId.toUInt64 maxPriorityFee maxFee dest al auths)
    | n => .error (.unsupportedType n)
  .ok {
    nonce := nonce.toUInt64, gas := gas, value := value, data := data,
    v := v, r := r.toB256.toBytes, s := s.toB256.toBytes, type := txType
  }

/-- The whole `txs` document. The RLP-string form the target refuses is
refused here for the same reason and with the same effect: this entry point
handles a JSON array. -/
def decodeTxs (j : Lean.Json) : IO (List (TxParse Tx)) :=
  match j with
  | .arr items => pure (items.toList.map decodeTx)
  | .null => pure []
  | .str _ =>
    IO.throw
      "error : RLP-encoded `txs` input is not supported by this t8n entry \
       point; provide a JSON array instead"
  | _ => IO.throw "error : t8n `txs` input must be a JSON array"

----------------- THE TRANSITION ------------------

/-- Why one transaction did not contribute to the block: it never became a
`Tx`, or it became one and `processTransaction` refused it. Both are recorded
by constructor and rendered once, at the emission boundary. -/
inductive RejectReason : Type
  | parse (e : TxParseError)
  | execution (e : TransitionError)

structure Rejection : Type where
  index : Nat
  reason : RejectReason

/-- What the transition produced. `blockException` carries the *typed*
block-validation reason, not its rendering: the wire text is produced once, by
`blockExceptionText`, at the emission boundary. -/
structure Outcome : Type where
  state : State
  bout : BlockOutput
  rejected : List Rejection
  blockException : Option BlockValidationError

/-- An operational failure is not a rejection. The target catches
`EthereumException` around each transaction -- which covers its transaction,
block and signature errors alike -- and lets anything else escape and end the
run; `internal` is Jaune's counterpart of the escaping case. -/
def operational : TransitionError → Bool
  | .internal _ => true
  | _ => false

/-- The target's `process_transaction` writes the transaction into
`block_output.transactions_trie` *before* validating it, on a block output it
mutates in place, so a transaction rejected during execution stays in that
trie and contributes to `txRoot`. `processTransaction` is pure and discards
its whole result on failure, so the frontend reinstates exactly that one
insertion -- the same key, the same value, in the same place. A transaction
rejected during *parse* never reaches that line in the target either, and does
not get one here. -/
def insertIntoTxTrie (bout : BlockOutput) (index : Nat) (tx : Tx) : BlockOutput :=
  {bout with
    transactionsTrie :=
      bout.transactionsTrie.insert (BLT.bytes index.toBytes).toBytes tx}

/-- The reject-and-continue fold: the one piece of control flow a transition
tool needs that a block importer must not have. Every arm calls
`processTransaction` unchanged, and a rejected transaction is rolled back by
not threading its state. -/
def foldTxs :
    List (Nat × TxParse Tx) → Benv → BlockOutput → List Rejection →
    Except TransitionError (Benv × BlockOutput × List Rejection)
  | [], benv, bout, rej => .ok ⟨benv, bout, rej⟩
  | ⟨i, .error e⟩ :: rest, benv, bout, rej =>
    foldTxs rest benv bout (rej ++ [⟨i, .parse e⟩])
  | ⟨i, .ok tx⟩ :: rest, benv, bout, rej =>
    match processTransaction benv bout tx i with
    | .ok ⟨st, bout'⟩ => foldTxs rest (benv.withState st) bout' rej
    | .error err =>
      if operational err then .error err
      else
        foldTxs rest benv (insertIntoTxTrie bout i tx) (rej ++ [⟨i, .execution err⟩])

/-- State-test mode: exactly one transaction, no system operations, no
withdrawals, no requests. -/
def runStateTest (benv : Benv) (txs : List (TxParse Tx)) :
    Except TransitionError Outcome := do
  let selected := match txs with | [] => [] | t :: _ => [⟨0, t⟩]
  let ⟨benv, bout, rej⟩ ← foldTxs selected benv .init []
  .ok ⟨benv.state, bout, rej, none⟩

/-- Blockchain mode: the target's `_run_blockchain_test`, step for step.

Block rewards are absent because they are unreachable on this lane: the
target pays them only when the fork is not proof-of-stake, and every runnable
or metering fork here is proof-of-stake.

EIP-7928 (goal C): the two pre-execution system calls are incorporated into
the block-level access list at index 0, each transaction at its index plus one
inside `processTransaction`, and the post-execution operations -- withdrawals,
then each request call -- at `len(txs) + 1`, the tool's count of the
transactions it was handed, rejected ones included (the driver sets the index
once, before withdrawals; Appendix E item 2 of the goal). The list is built
after the requests and the item rule is applied to it; a violation is the
`blockException` of a result that still carries the list, as the target
assigns `block_output.block_access_list` before validating it. -/
def runBlockchain (benv : Benv) (txs : List (TxParse Tx)) (wds : List Withdrawal) :
    Except TransitionError Outcome := do
  let rules := benv.stat.rules
  -- The parent hash the history-storage system transaction records. The
  -- target reads `block_hashes[-1]` and raises `IndexError` out of the whole
  -- tool when the window is empty, which is the shape every state test
  -- arrives in once the framework has declined to pass `--state-test` to an
  -- external binary. There is no reference behaviour to match on that input,
  -- so this records the zero hash and continues; on every input the target
  -- can process at all, the window is non-empty and this is its last entry.
  let lastHash := benv.stat.blockHashes.getLast?.getD 0
  let ⟨stHistory, outHistory⟩ ←
    Except.mapError TransitionError.vm <|
      processUncheckedSystemTransaction benv historyStorageAddress lastHash.toBytes
  let bal := ({} : BalBuilder).incorporateSystem rules 0 benv.state stHistory
    (historyStorageAddress :: outHistory.accountReads.toList) outHistory.storageReads.toList
  let benv := benv.withState stHistory
  let ⟨stBeacon, outBeacon⟩ ←
    Except.mapError TransitionError.vm <|
      processUncheckedSystemTransaction benv beaconRootsAddress
        benv.stat.parentBeaconBlockRoot.toBytes
  let bal := bal.incorporateSystem rules 0 benv.state stBeacon
    (beaconRootsAddress :: outBeacon.accountReads.toList) outBeacon.storageReads.toList
  let benv := benv.withState stBeacon
  let ⟨benv, bout, rej⟩ ← foldTxs txs.putIndex benv {BlockOutput.init with bal := bal} []
  let postIndex := txs.length + 1
  let ⟨stWds, bout⟩ := processWithdrawals benv bout wds
  let balWds := bout.bal.incorporateSystem rules postIndex benv.state stWds
    (wds.map Withdrawal.recipient) []
  let bout := {bout with bal := balWds}
  let benv := benv.withState stWds
  match processGeneralPurposeRequestsAt postIndex benv bout with
  | .ok ⟨st, bout'⟩ =>
    let list := match rules.bal with
      | none => []
      | some _ => bout'.bal.build
    let bout' := {bout' with blockAccessList := list}
    match checkBlockAccessListGasLimit rules benv.stat.blockGasLimit list with
    | .ok () => .ok ⟨st, bout', rej, none⟩
    | .error (.block reason) => .ok ⟨st, bout', rej, some reason⟩
    | .error err => .error err
  | .error (.block reason) =>
    -- The target raises `InvalidBlock` out of the step and builds its result
    -- from whatever the block environment and block output already hold.
    .ok ⟨benv.state, bout, rej, some reason⟩
  | .error err => .error err

----------------- REJECTION AND BLOCK-EXCEPTION TEXT ------------------

-- `rejected[].error` and `blockException` carry free text with no normative
-- content: every transition tool writes its own, and the framework maps the
-- text to a canonical identity through the *registered wrapper's* exception
-- mapper rather than comparing it. So this tool writes Jaune's own canonical
-- vocabulary -- the official identity `Jaune/FixtureException.lean` already
-- assigns to each typed reason -- and never imitates another tool's wording.
--
-- A reason with no official identity renders as an explicitly unmapped token.
-- That is the fail-loud case on purpose: an unmapped reason must be visible as
-- unmapped, never quietly resemble something the mapper recognises.

def unmappedText (kind : String) (detail : String) : String :=
  "JauneT8n.UNMAPPED_" ++ kind ++ ": " ++ detail

def identityText (kind : String) (detail : String) :
    Option FixtureException → String
  | some e => e.toString
  | none => unmappedText kind detail

def rejectionText : RejectReason → String
  | .parse e => e.render
  | .execution (.transaction e) =>
    identityText "TRANSACTION" e.render (FixtureException.ofTxValidationError e)
  | .execution (.block e) =>
    identityText "BLOCK" e.render (FixtureException.ofBlockValidationError e)
  | .execution (.decode e) =>
    identityText "DECODE" e.render (FixtureException.ofDecodeError e)
  | .execution (.senderRecovery e) =>
    identityText "SENDER_RECOVERY" e.render (FixtureException.ofCryptoError e)
  | .execution (.vm e) => unmappedText "VM" e.render
  | .execution (.internal e) => unmappedText "INTERNAL" e.render

def blockExceptionText (e : BlockValidationError) : String :=
  identityText "BLOCK" e.render (FixtureException.ofBlockValidationError e)

----------------- EMISSION ------------------

/-- The type-prefixed wire encoding of a transaction: what the transactions
trie stores and what the transaction hash is taken over. A pure projection
over `Tx.toBLT`; `getTransactionsRoot` computes the same prefix inline. -/
def txEncoding (tx : Tx) : Bytes :=
  let typeByte : Bytes :=
    match tx.type with
    | .zero _ _ => []
    | .one _ _ _ _ => [0x01]
    | .two _ _ _ _ _ => [0x02]
    | .three _ _ _ _ _ _ _ => [0x03]
    | .four _ _ _ _ _ _ => [0x04]
  typeByte ++ tx.toBLT.toBytes

def txHash (tx : Tx) : B256 := (txEncoding tx).keccak

def logJson (l : Log) : JOut :=
  .obj [
    ⟨"address", .str (hexAdr l.address)⟩,
    ⟨"topics", .arr (l.topics.map fun t => .str (hexB256 t))⟩,
    ⟨"data", .str (hexBytes l.data)⟩
  ]

def receiptJson (bout : BlockOutput) (key : Bytes) : Option JOut := do
  let tx ← bout.transactionsTrie[key]?
  let entry ← bout.receiptsTrie[key]?
  let r := entry.snd
  some <| .obj [
    ⟨"transactionHash", .str (hexB256 (txHash tx))⟩,
    ⟨"status", .str (hexQuantity (if r.succeeded then 1 else 0))⟩,
    ⟨"cumulativeGasUsed", .str (hexQuantity r.gasUsed)⟩,
    ⟨"bloom", .str (hexBytes r.bloom)⟩,
    ⟨"logs", .arr (r.logs.map logJson)⟩
  ]

def rejectionJson (r : Rejection) : JOut :=
  .obj [
    ⟨"index", .str (hexQuantity r.index)⟩,
    ⟨"error", .str (rejectionText r.reason)⟩
  ]

private def resultGasUsed (bout : BlockOutput) : Nat :=
  max bout.blockGasUsed bout.blockStateGasUsed

-- Legacy block outputs keep `blockStateGasUsed = 0`; Amsterdam may make either
-- dimension the header/result maximum.
#guard resultGasUsed {BlockOutput.init with blockGasUsed := 100} = 100
#guard resultGasUsed
  {BlockOutput.init with blockGasUsed := 50, blockStateGasUsed := 100} = 100

/-- The `result` document.

Key order is the target's pydantic declaration order, which is what its
`model_dump` emits -- note that `requestsHash` precedes `requests`. Absent
keys are the ones its `exclude_none=True` drops: `currentDifficulty` is
`None` on a proof-of-stake lane, the block-access-list pair (EIP-7928, goal
C) is present exactly when the rules carry a block-level access list -- the
list's RLP and its keccak, the empty list's `0xc0` in state-test mode, where
the target never builds one -- and traces are not claimed by this tool at
all. The key spellings are the ones goal B's first golden recorded. -/
def resultJson (rules : ForkRules) (env : T8nEnv) (o : Outcome) : JOut :=
  let logsHash := (BLT.list (o.bout.blockLogs.map Log.toBLT)).toBytes.keccak
  let base : List (String × JOut) := [
    ⟨"stateRoot", .str (hexB256 o.state.root)⟩,
    ⟨"txRoot", .str (hexB256 (getTransactionsRoot o.bout))⟩,
    ⟨"receiptsRoot", .str (hexB256 (getReceiptRoot o.bout))⟩,
    ⟨"logsHash", .str (hexB256 logsHash)⟩,
    ⟨"logsBloom", .str (hexBytes (logsBloom o.bout.blockLogs))⟩,
    ⟨"receipts", .arr (o.bout.receiptKeys.filterMap (receiptJson o.bout))⟩,
    ⟨"rejected", .arr (o.rejected.map rejectionJson)⟩,
    ⟨"gasUsed", .str (hexQuantity (resultGasUsed o.bout))⟩,
    ⟨"currentBaseFee", .str (hexQuantity env.baseFeePerGas)⟩,
    ⟨"withdrawalsRoot", .str (hexB256 (getWithdrawalsRoot o.bout))⟩,
    ⟨"currentExcessBlobGas", .str (hexQuantity env.excessBlobGas)⟩,
    ⟨"blobGasUsed", .str (hexQuantity o.bout.blobGasUsed)⟩,
    ⟨"requestsHash", .str (hexB256 (computeRequestsHash o.bout.requests))⟩,
    ⟨"requests", .arr (o.bout.requests.map fun r => .str (hexBytes r))⟩
  ]
  let base := match rules.bal with
    | none => base
    | some _ => base ++ [
      ⟨"blockAccessList", .str (hexBytes o.bout.blockAccessList.encode)⟩,
      ⟨"blockAccessListHash", .str (hexB256 o.bout.blockAccessList.hash)⟩ ]
  match o.blockException with
  | none => .obj base
  | some e => .obj (base ++ [⟨"blockException", .str (blockExceptionText e)⟩])

def acctJson (a : Acct) : JOut :=
  .obj [
    ⟨"nonce", .str (hexPadded a.nonce.toNat)⟩,
    ⟨"balance", .str (hexPadded a.bal.toNat)⟩,
    ⟨"code", .str (hexBytes a.code.toList)⟩,
    ⟨"storage", .obj <|
      (Std.TreeMap.toList a.stor).map fun kv =>
        ⟨hexPadded kv.fst.toNat, .str (hexPadded kv.snd.toNat)⟩⟩
  ]

/-- The post-state `alloc` document.

Addresses and storage keys come out of `Std.TreeMap`s, so both are emitted in
ascending key order. The target emits them in Python dictionary insertion
order instead -- the input allocation's order, then whatever its block diff
touched. Neither order is normative and no consumer reads one, so this tool
takes the order that is deterministic by construction; `scripts/check-t8n.sh`
canonicalises both sides before comparing. -/
def allocJson (st : State) : JOut :=
  .obj <| st.toList.map fun kv => ⟨hexAdr kv.fst, acctJson kv.snd⟩

/-- The `body` document: an RLP list whose members are the transactions'
type-prefixed encodings, as byte strings. Written as a bare JSON string,
which is what the target's `json.dump(body_hex, f)` produces. -/
def bodyHex (txs : List (TxParse Tx)) : String :=
  let encoded := txs.filterMap fun t => t.toOption.map txEncoding
  hexBytes (BLT.list (encoded.map BLT.bytes)).toBytes

----------------- THE COMMAND LINE ------------------

/-- This build's own version, printed by `jaune --version` and by the
handshake. It names the frontend contract, not the library: the pins the
handshake reports all come from `scripts/sources.json`. -/
def version : String := "0.1.0"

structure Opts : Type where
  inputAlloc : String := "alloc.json"
  inputEnv : String := "env.json"
  inputTxs : String := "txs.json"
  outputAlloc : String := "alloc.json"
  outputResult : String := "result.json"
  outputBody : String := ""
  outputBasedir : String := "."
  forkLabel : String := ""
  chainId : Nat := 1
  stateTest : Bool := false
  info : Bool := false
  forks : Bool := false

/-- Accept `--flag=value` as well as `--flag value`. The framework passes the
separated form to an external binary and the documented form uses `=`; both
have to mean the same thing. -/
def normalizeArgs : List String → List String
  | [] => []
  | a :: rest =>
    match a.toList with
    | '-' :: '-' :: _ =>
      match a.splitOn "=" with
      | k :: v :: vs => k :: String.intercalate "=" (v :: vs) :: normalizeArgs rest
      | _ => a :: normalizeArgs rest
    | _ => a :: normalizeArgs rest

def unclaimed (flag : String) (what : String) : IO Opts :=
  IO.throw
    s!"error : {flag} is not supported; jaune t8n does not claim {what}, and \
       a silently ignored capability flag is worse than a refusal"

def parseOpts : Opts → List String → IO Opts
  | o, [] => pure o
  | o, "--input.alloc" :: v :: rest => parseOpts {o with inputAlloc := v} rest
  | o, "--input.env" :: v :: rest => parseOpts {o with inputEnv := v} rest
  | o, "--input.txs" :: v :: rest => parseOpts {o with inputTxs := v} rest
  | o, "--output.alloc" :: v :: rest => parseOpts {o with outputAlloc := v} rest
  | o, "--output.result" :: v :: rest => parseOpts {o with outputResult := v} rest
  | o, "--output.body" :: v :: rest => parseOpts {o with outputBody := v} rest
  | o, "--output.basedir" :: v :: rest => parseOpts {o with outputBasedir := v} rest
  | o, "--state.fork" :: v :: rest => parseOpts {o with forkLabel := v} rest
  | o, "--state.chainid" :: v :: rest => do
    let some n := v.toNat? | IO.throw s!"error : --state.chainid expects a number, got {repr v}"
    parseOpts {o with chainId := n} rest
  -- Accepted and not consumed. The target pays block rewards only when the
  -- fork is not proof-of-stake, and every fork on this lane is, so the value
  -- cannot change the transition. `fill` always passes it.
  | o, "--state.reward" :: _ :: rest => parseOpts o rest
  | o, "--state-test" :: rest => parseOpts {o with stateTest := true} rest
  | o, "--info" :: rest => parseOpts {o with info := true} rest
  | o, "--forks" :: rest => parseOpts {o with forks := true} rest
  | _, "--trace" :: _ => unclaimed "--trace" "EIP-3155 tracing"
  | _, "--trace.memory" :: _ => unclaimed "--trace.memory" "EIP-3155 tracing"
  | _, "--trace.nomemory" :: _ => unclaimed "--trace.nomemory" "EIP-3155 tracing"
  | _, "--trace.nostack" :: _ => unclaimed "--trace.nostack" "EIP-3155 tracing"
  | _, "--trace.returndata" :: _ => unclaimed "--trace.returndata" "EIP-3155 tracing"
  | _, "--trace.noreturndata" :: _ => unclaimed "--trace.noreturndata" "EIP-3155 tracing"
  | _, "--opcode.count" :: _ => unclaimed "--opcode.count" "opcode counting"
  | _, "--input.blobParams" :: _ =>
    IO.throw
      "error : --input.blobParams is not supported; jaune names its BPO forks \
       directly, so pass --state.fork BPO1 or --state.fork BPO2 rather than a \
       schedule override"
  | _, a :: _ =>
    IO.throw
      s!"error : unrecognised or incomplete t8n option {repr a}; run \
         `jaune t8n --info` for the supported surface"

/-- Read one `t8n` JSON input, from a file or from the single stdin document
whose members the `stdin` sentinel names. -/
def readInput (stdinDoc : Option Lean.Json) (spec key : String) : IO Lean.Json :=
  if spec = "stdin" then
    match stdinDoc with
    | some j => (j.find? key).toIO s!"error : the stdin document has no {key} member"
    | none => IO.throw "error : t8n input names stdin but no stdin document was read"
  else readJsonFile spec

/-- Where `scripts/sources.json` is. `JAUNE_SOURCES` overrides, because the
binary is normally invoked from somewhere other than the repository. -/
def sourcesPath : IO System.FilePath := do
  match ← IO.getEnv "JAUNE_SOURCES" with
  | some p => pure p
  | none => pure "scripts/sources.json"

def sourceField (j : Lean.Json) (group key : String) : IO String := do
  let s ← (j.find? group).toIO
    s!"error : sources.json has no {group} section"
  let v ← (s.find? key).toIO
    s!"error : sources.json {group} has no {key} field"
  match v with
  | .str x => pure x
  | _ => pure (Lean.Json.compress v)

/-- The version-and-pins handshake.

Every pin is read from `scripts/sources.json` rather than restated here: the
manifest's own comment forbids duplicating its literals, and a handshake that
carried its own copy would be able to disagree with the generators. -/
def printInfo : IO Unit := do
  let path ← sourcesPath
  let sources ←
    try readJsonFile path
    catch _ =>
      IO.throw
        s!"error : could not read {path}; the t8n handshake reports the pins \
           recorded there, so set JAUNE_SOURCES to that file's path"
  IO.println s!"jaune version {version}"
  IO.println s!"lean toolchain: {Lean.versionString}"
  IO.println
    s!"t8n fork lane: \
       {String.intercalate " " (advertisedForkLane.map Fork.toString)}"
  IO.println
    s!"t8n lane basis: the advertised lane is every fork this build runs \
       (Fork.supported), each carried by its fixture corpus under \
       scripts/check-mainnet.sh (the current-mainnet lane for Prague, Osaka, \
       BPO1 and BPO2; the Glamsterdam devnet lane, static and transition \
       suites, for Amsterdam) and by the transition-tool differential of \
       scripts/check-t8n.sh against the conformance target below"
  IO.println
    s!"t8n resolves: \
       {String.intercalate " " (Fork.supported.map Fork.toString)} \
       (every declared fork, through Fork.rules?; the same list as the lane, \
       by construction)"
  IO.println s!"t8n modes: blockchain (default), state-test (--state-test)"
  IO.println s!"t8n tracing: not claimed"
  IO.println s!"sources manifest: {path}"
  IO.println
    s!"conformance target: {← sourceField sources "conformance_target" "repo_url"} \
       {← sourceField sources "conformance_target" "branch"} \
       {← sourceField sources "conformance_target" "commit"}"
  IO.println
    s!"oracle pin (execution-specs): \
       {← sourceField sources "execution_specs" "commit"}"
  IO.println
    s!"legacy corpus (ethereum/tests): \
       {← sourceField sources "ethereum_tests" "commit"}"
  IO.println
    s!"eest fixtures: {← sourceField sources "eest" "release_tag"}"
  IO.println
    s!"current-mainnet fixtures: \
       {← sourceField sources "current_mainnet" "release_tag"}"

/-- `jaune t8n`.

Unsupported input fails closed at every point: an out-of-lane fork, an
unrecognised flag, an unrecognised input field, and the RLP `txs` string form
are all errors with a non-zero exit and no fallback. -/
def run (args : List String) : IO Unit := do
  let o ← parseOpts {} (normalizeArgs args)
  -- The fork lane on its own, on one line. This is what a framework wrapper
  -- asks the binary in order to decide whether to hand it a test, so unlike
  -- `--info` it must answer from any working directory and must not depend on
  -- the sources manifest being reachable.
  if o.forks then
    -- The advertised lane. This line is a wrapper's whole basis for deciding
    -- what to send, so it names exactly the forks the very next step would
    -- run: `advertisedForkLane` is `Fork.supported`.
    IO.println (String.intercalate " " (advertisedForkLane.map Fork.toString))
    return ()
  if o.info then
    printInfo
    return ()
  if o.forkLabel.isEmpty then
    IO.throw
      s!"error : t8n requires --state.fork; there is no default fork, and the \
         runnable labels are {Fork.supported.map Fork.toString}"
  let some f := Fork.ofString? o.forkLabel
    | IO.throw
        s!"error : t8n does not support the fork {repr o.forkLabel}; this \
           build's runnable lane is {Fork.supported.map Fork.toString}, and \
           there is no fallback"
  let rules ← IO.ofExcept (f.rules.mapError SupportError.render)
  let usesStdin :=
    o.inputAlloc = "stdin" ∨ o.inputEnv = "stdin" ∨ o.inputTxs = "stdin"
  let stdinDoc ←
    if usesStdin then
      let text ← (← IO.getStdin).readToEnd
      match Lean.Json.parse text with
      | .ok j => pure (some j)
      | .error e => IO.throw s!"error : t8n stdin document is not JSON: {e}"
    else pure none
  let allocJsonIn ← readInput stdinDoc o.inputAlloc "alloc"
  let envJsonIn ← readInput stdinDoc o.inputEnv "env"
  let txsJsonIn ← readInput stdinDoc o.inputTxs "txs"
  let preState ← allocJsonIn.toWorld
  let env ← decodeEnv rules o.stateTest envJsonIn
  let txs ← decodeTxs txsJsonIn
  let benv : Benv := {
    state := preState,
    createdAccounts := .emptyWithCapacity,
    stat := {
      fork := f,
      chainId := o.chainId.toUInt64,
      origState := preState,
      blockGasLimit := env.gasLimit,
      blockHashes := env.blockHashes,
      coinbase := env.coinbase,
      number := env.number,
      baseFeePerGas := env.baseFeePerGas,
      time := env.timestamp.toB256,
      prevRandao := env.prevRandao,
      excessBlobGas := env.excessBlobGas,
      parentBeaconBlockRoot := env.parentBeaconBlockRoot,
      slotNumber := env.slotNumber
    }
  }
  let outcome ←
    IO.ofExcept <|
      (if o.stateTest then runStateTest benv txs
        else runBlockchain benv txs env.withdrawals).mapError TransitionError.render
  let resultText := (resultJson rules env outcome).toString
  let allocText := (allocJson outcome.state).toString
  let bodyText := quoted (bodyHex txs)
  let basedir : System.FilePath := o.outputBasedir
  let mut stdoutFields : List (String × JOut) := []
  if o.outputBody = "stdout" then
    stdoutFields := stdoutFields ++ [⟨"body", .str (bodyHex txs)⟩]
  else if ¬ o.outputBody.isEmpty then
    IO.FS.writeFile (basedir.join o.outputBody) bodyText
  if o.outputAlloc = "stdout" then
    stdoutFields := stdoutFields ++ [⟨"alloc", allocJson outcome.state⟩]
  else
    IO.FS.writeFile (basedir.join o.outputAlloc) allocText
  if o.outputResult = "stdout" then
    stdoutFields := stdoutFields ++ [⟨"result", resultJson rules env outcome⟩]
  else
    IO.FS.writeFile (basedir.join o.outputResult) resultText
  if ¬ stdoutFields.isEmpty then
    IO.print (JOut.obj stdoutFields).toString

def usage : String :=
  s!"usage:
  jaune t8n [--input.alloc <path|stdin>] [--input.env <path|stdin>]
            [--input.txs <path|stdin>] [--output.alloc <path|stdout>]
            [--output.result <path|stdout>] [--output.body <path|stdout>]
            [--output.basedir <dir>] --state.fork <label>
            [--state.chainid <n>] [--state.reward <n>] [--state-test]
  jaune t8n --info
  jaune t8n --forks

Executes one state transition outside any block-validation context and emits
`result` and the post-state `alloc` in the shapes the conformance target
emits. Options may be spelled --flag=value or --flag value.

  --state.fork <label>   required; one of the runnable labels
                         {Fork.supported.map Fork.toString}. There is no
                         default and no fallback.
  --state-test           apply exactly one transaction with no system
                         operations, no withdrawals and no requests.
  --state.reward <n>     accepted and not consumed: every fork on this lane is
                         proof-of-stake, so block rewards are unreachable.
  --info                 print the version, the advertised fork lane and its
                         basis, every fork this build resolves, and the pins recorded in
                         scripts/sources.json. Needs that file: pass
                         JAUNE_SOURCES if it is not at scripts/ from the
                         working directory.
  --forks                print the advertised fork lane and nothing else, on
                         one line ({advertisedForkLane.map Fork.toString}).
                         Answers from anywhere.

Tracing is not claimed: --trace, its variants and --opcode.count are refused
rather than ignored.
"

end T8n
end Jaune
