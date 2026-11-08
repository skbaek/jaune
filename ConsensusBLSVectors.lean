-- Local runner for the general-preset `bls` vectors of consensus-specs v1.6.1:
-- `tests/general/altair/bls/{eth_aggregate_pubkeys,eth_fast_aggregate_verify}`.
-- Usage: jaune-consensus-bls-vectors <path to tests/general/altair/bls>
--
-- A stop-gap until the shared harness (YAML reader, case discovery, count checks)
-- lands; it reads only the line shapes these two handlers use, refuses an empty
-- selection, and exits non-zero on any failure or unreadable case.

import JauneConsensus.Crypto.BLSSig

open Jaune JauneConsensus

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Characters with surrounding blanks and single quotes removed. -/
def strip (cs : List Char) : List Char :=
  let junk (c : Char) := c = ' ' ∨ c = '\'' ∨ c = '\r' ∨ c = '\t'
  ((cs.dropWhile junk).reverse.dropWhile junk).reverse

/-- `'0x..'` (quotes optional) to bytes. -/
def parseHex? (s : String) : Option Bytes := do
  let cs := strip s.toList
  guard (cs.take 2 = ['0', 'x'])
  let cs := cs.drop 2
  guard (cs.length % 2 = 0)
  let rec go : List Char → Option Bytes
    | a :: b :: rest => do
      let hi ← hexDigit? a
      let lo ← hexDigit? b
      return (hi * 16 + lo).toUInt8 :: (← go rest)
    | _ => some []
  go cs

/-- The value after `key:` on the first line that starts (after indentation) with it. -/
def field? (lines : List String) (key : String) : Option String :=
  lines.findSome? fun l =>
    let t := l.toList.dropWhile (· = ' ')
    let k := (key ++ ":").toList
    if t.take k.length = k then some (String.ofList (strip (t.drop k.length)))
    else none

/-- Every `- item` line. -/
def items (lines : List String) : List String :=
  lines.filterMap fun l =>
    let t := l.toList.dropWhile (· = ' ')
    if t.take 2 = ['-', ' '] then some (String.ofList (t.drop 2)) else none

def runAggregatePubkeys (lines : List String) : Except String Bool := do
  let pks ← (items lines).mapM fun s => (parseHex? s).elim (.error "bad pubkey") .ok
  let out ← (field? lines "output").elim (.error "no output") .ok
  let got := (ethAggregatePubkeys pks).toOption
  if out = "null" then return got.isNone
  let expected ← (parseHex? out).elim (.error "bad output") .ok
  return got = some expected

def runFastAggregateVerify (lines : List String) : Except String Bool := do
  let pks ← (items lines).mapM fun s => (parseHex? s).elim (.error "bad pubkey") .ok
  let msg ← ((field? lines "message").bind parseHex?).elim (.error "bad message") .ok
  let sig ← ((field? lines "signature").bind parseHex?).elim (.error "bad signature") .ok
  let out ← (field? lines "output").elim (.error "no output") .ok
  let expected ← if out = "true" then pure true else if out = "false" then pure false
    else .error "bad output"
  return ethFastAggregateVerify pks msg sig = expected

def main (args : List String) : IO UInt32 := do
  let some root := args.head? | IO.eprintln "usage: jaune-consensus-bls-vectors <bls dir>"; return 2
  let mut pass := 0
  let mut fail := 0
  for (handler, run) in [("eth_aggregate_pubkeys", runAggregatePubkeys),
                         ("eth_fast_aggregate_verify", runFastAggregateVerify)] do
    let dir : System.FilePath := root / handler / "bls"
    let entries ← dir.readDir
    let names := (entries.map (·.fileName)).qsort (· < ·)
    for name in names do
      let text ← IO.FS.readFile (dir / name / "data.yaml")
      let lines := (text.splitOn "\n")
      let t0 ← IO.monoMsNow
      let r ← IO.lazyPure fun _ => run lines
      let t1 ← IO.monoMsNow
      match r with
      | .ok true => pass := pass + 1; IO.println s!"PASS {handler}/{name} ({t1 - t0} ms)"
      | .ok false => fail := fail + 1; IO.println s!"FAIL {handler}/{name}"
      | .error e => fail := fail + 1; IO.println s!"ERROR {handler}/{name}: {e}"
  IO.println s!"bls: {pass} passed, {fail} failed"
  if pass + fail = 0 then IO.eprintln "empty selection"; return 1
  return if fail = 0 then 0 else 1
