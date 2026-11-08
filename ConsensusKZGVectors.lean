-- Differential tool for the general-preset `kzg` vectors of consensus-specs v1.6.1 (the
-- catalogue gate is `jaune-consensus run --preset general --runner kzg`; this keeps the
-- `@spec` and `@jaune` pseudo-handlers, which compare alternative implementations):
-- `tests/general/deneb/kzg/*/kzg-mainnet/*` and `tests/general/fulu/kzg/*/kzg-mainnet/*`.
-- Usage: jaune-consensus-kzg-vectors <tests/general dir> [handler ...]
--
-- A stop-gap until the shared harness lands. It reads the YAML subset these files use
-- (block mappings and sequences, nested `- -` sequences, single-line or wrapped flow
-- sequences of scalars, quoted and plain scalars), refuses an empty selection, prints
-- per-handler counts and times, and exits non-zero on any failure or unreadable case.
-- An expected `null` output means the spec raised: the model must return an error.

import JauneConsensus.Crypto.KZGCells

open Jaune JauneConsensus

/-! ### YAML subset -/

inductive Y where
  | str (s : String)
  | seq (xs : List Y)
  | map (kvs : List (String × Y))

def isBlank (c : Char) : Bool := c = ' ' ∨ c = '\r' ∨ c = '\t'

def stripChars (cs : List Char) : List Char :=
  ((cs.dropWhile isBlank).reverse.dropWhile isBlank).reverse

def unquote (cs : List Char) : String :=
  let cs := stripChars cs
  match cs with
  | '\'' :: rest => String.ofList (rest.reverse.dropWhile (· = '\'')).reverse
  | '"' :: rest => String.ofList (rest.reverse.dropWhile (· = '"')).reverse
  | _ => String.ofList cs

/-- `key: rest` when the line starts with an identifier followed by a colon. -/
def keyLine? (cs : List Char) : Option (String × List Char) :=
  let key := cs.takeWhile fun c => c.isAlphanum ∨ c = '_'
  match cs.drop key.length with
  | ':' :: rest => if key.isEmpty then none else some (String.ofList key, stripChars rest)
  | _ => none

/-- A flow sequence of scalars, `[a, b, c]`. -/
def flowSeq (cs : List Char) : Y :=
  let inner := ((stripChars cs).drop 1).reverse.drop 1 |>.reverse
  let parts := (String.ofList inner).splitOn ","
  .seq ((parts.map fun p => stripChars p.toList).filter (!·.isEmpty) |>.map fun p => .str (unquote p))

def scalar (cs : List Char) : Y :=
  if cs.head? = some '[' then flowSeq cs else .str (unquote cs)

/-- Lines as (indent, content), blank lines dropped, wrapped flow sequences joined. -/
def prepLines (text : String) : List (Nat × List Char) :=
  let raw := (text.splitOn "\n").map fun l =>
    let cs := l.toList
    let ind := (cs.takeWhile (· = ' ')).length
    (ind, stripChars (cs.drop ind))
  let raw := raw.filter (!·.2.isEmpty)
  let rec join (fuel : Nat) : List (Nat × List Char) → List (Nat × List Char)
    | [] => []
    | (i, cs) :: rest =>
      match fuel with
      | 0 => (i, cs) :: rest
      | fuel + 1 =>
        if cs.contains '[' && !cs.contains ']' then
          match rest with
          | (_, cs2) :: rest2 => join fuel ((i, cs ++ [' '] ++ cs2) :: rest2)
          | [] => [(i, cs)]
        else (i, cs) :: join fuel rest
  join (2 * raw.length) raw

/-- Parse one node from lines whose first line sets the indentation. -/
def parseNode : Nat → List (Nat × List Char) → Y
  | 0, _ => .str ""
  | _, [] => .str ""
  | fuel + 1, lines@((ind, first) :: _) =>
    if first.take 2 = ['-', ' '] || first = ['-'] then
      -- block sequence at `ind`
      let rec items (f : Nat) : List (Nat × List Char) → List Y
        | [] => []
        | (i, cs) :: rest =>
          match f with
          | 0 => []
          | f + 1 =>
            if i = ind && (cs.take 2 = ['-', ' '] || cs = ['-']) then
              let child := rest.takeWhile (·.1 > ind)
              let after := rest.drop child.length
              let itemText := stripChars (cs.drop 1)
              let itemLines := if itemText.isEmpty then child else (ind + 2, itemText) :: child
              parseNode fuel itemLines :: items f after
            else []
      .seq (items lines.length lines)
    else match keyLine? first with
      | none => scalar first
      | some _ =>
        let rec entries (f : Nat) : List (Nat × List Char) → List (String × Y)
          | [] => []
          | (i, cs) :: rest =>
            match f with
            | 0 => []
            | f + 1 =>
              match keyLine? cs with
              | some (k, v) =>
                if i ≠ ind then [] else
                if v.isEmpty then
                  let child := rest.takeWhile fun (j, c) =>
                    j > ind || (j = ind && (c.take 2 = ['-', ' '] || c = ['-']))
                  (k, parseNode fuel child) :: entries f (rest.drop child.length)
                else (k, scalar v) :: entries f rest
              | none => []
        .map (entries lines.length lines)

def parseYaml (text : String) : Y :=
  let ls := prepLines text
  parseNode (ls.length + 1) ls

def Y.get? (y : Y) (k : String) : Option Y :=
  match y with
  | .map kvs => (kvs.find? (·.1 = k)).map (·.2)
  | _ => none

/-! ### Values -/

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHex? (s : String) : Option Bytes := do
  let cs := s.toList
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

def toHex (bs : Bytes) : String :=
  let d (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  "0x" ++ String.ofList (bs.flatMap fun b => [d (b.toNat / 16), d (b.toNat % 16)])

def asStr (y : Y) : Except String String :=
  match y with | .str s => .ok s | _ => .error "expected scalar"
def asBytes (y : Y) : Except String Bytes := do
  (parseHex? (← asStr y)).elim (.error "bad hex") .ok
def asSeq (y : Y) : Except String (List Y) :=
  match y with | .seq xs => .ok xs | _ => .error "expected sequence"
def asNat (y : Y) : Except String Nat := do
  (← asStr y).toNat?.elim (.error "bad integer") .ok
def field (y : Y) (k : String) : Except String Y := (y.get? k).elim (.error s!"missing {k}") .ok
def bytesList (y : Y) : Except String (List Bytes) := do (← asSeq y).mapM asBytes
def natList (y : Y) : Except String (List Nat) := do (← asSeq y).mapM asNat

/-- A normalised value to compare: model results are rendered to it. -/
inductive V where
  | null | bool (b : Bool) | hex (s : String) | list (xs : List V)
deriving BEq

def V.ofY : Y → Except String V
  | .str "null" => .ok .null
  | .str "true" => .ok (.bool true)
  | .str "false" => .ok (.bool false)
  | .str s => .ok (.hex s.toLower)
  | .seq xs => do .ok (.list (← xs.mapM V.ofY))
  | .map _ => .error "unexpected mapping in output"

def vBytes (b : Bytes) : V := .hex (toHex b)
def vOf {α} (r : Except String α) (f : α → V) : V :=
  match r with | .ok a => f a | .error _ => .null

/-! ### Handlers: input mapping to normalised output -/

def kzgHandler (name : String) (inp : Y) : Except String V := do
  match name with
  | "blob_to_kzg_commitment" =>
    let blob ← asBytes (← field inp "blob")
    return vOf (blobToKzgCommitment blob) vBytes
  | "compute_challenge" =>
    let blob ← asBytes (← field inp "blob")
    let c ← asBytes (← field inp "commitment")
    return vBytes (blsFieldToBytes (computeChallenge blob c))
  | "compute_kzg_proof" =>
    let blob ← asBytes (← field inp "blob")
    let z ← asBytes (← field inp "z")
    return vOf (computeKzgProof blob z) fun (p, y) => .list [vBytes p, vBytes y]
  | "compute_blob_kzg_proof" =>
    let blob ← asBytes (← field inp "blob")
    let c ← asBytes (← field inp "commitment")
    return vOf (computeBlobKzgProof blob c) vBytes
  | "verify_kzg_proof" =>
    let c ← asBytes (← field inp "commitment")
    let z ← asBytes (← field inp "z")
    let y ← asBytes (← field inp "y")
    let p ← asBytes (← field inp "proof")
    return vOf (verifyKzgProof c z y p) .bool
  | "verify_kzg_proof@jaune" =>
    -- Differential: Jaune's execution-layer EIP-4844 verifier (Jaune/Precompiles.lean).
    let c ← asBytes (← field inp "commitment")
    let z ← asBytes (← field inp "z")
    let y ← asBytes (← field inp "y")
    let p ← asBytes (← field inp "proof")
    return match Jaune.verifyKzgProof c z y p with
      | .ok b => .bool b
      | .error _ => .null
  | "verify_blob_kzg_proof" =>
    let blob ← asBytes (← field inp "blob")
    let c ← asBytes (← field inp "commitment")
    let p ← asBytes (← field inp "proof")
    return vOf (verifyBlobKzgProof blob c p) .bool
  | "verify_blob_kzg_proof_batch" =>
    let blobs ← bytesList (← field inp "blobs")
    let cs ← bytesList (← field inp "commitments")
    let ps ← bytesList (← field inp "proofs")
    return vOf (verifyBlobKzgProofBatch blobs cs ps) .bool
  | "compute_cells" =>
    let blob ← asBytes (← field inp "blob")
    return vOf (computeCells blob) fun cells => .list (cells.toList.map vBytes)
  | "compute_cells@spec" =>
    let blob ← asBytes (← field inp "blob")
    return vOf (computeCellsSpec blob) fun cells => .list (cells.toList.map vBytes)
  | "compute_cells_and_kzg_proofs@spec" =>
    let blob ← asBytes (← field inp "blob")
    let r : Except String (Array Bytes × Array Bytes) := do
      kzgAssert (blob.length = bytesPerBlob) "blob length"
      computeCellsAndKzgProofsPolynomialcoeffSpec (← polynomialEvalToCoeff (← blobToPolynomial blob))
    return vOf r fun (cells, proofs) =>
      .list [.list (cells.toList.map vBytes), .list (proofs.toList.map vBytes)]
  | "compute_cells_and_kzg_proofs" =>
    let blob ← asBytes (← field inp "blob")
    return vOf (computeCellsAndKzgProofs blob) fun (cells, proofs) =>
      .list [.list (cells.toList.map vBytes), .list (proofs.toList.map vBytes)]
  | "compute_verify_cell_kzg_proof_batch_challenge" =>
    let cs ← bytesList (← field inp "commitments")
    let cis ← natList (← field inp "commitment_indices")
    let cells ← natList (← field inp "cell_indices")
    let evals ← (← asSeq (← field inp "cosets_evals")).mapM fun e => do
      (← bytesList e).toArray.mapM fun b => pure (FinField.ofNat (os2ip b) : Fr)
    let ps ← bytesList (← field inp "proofs")
    return vOf (computeVerifyCellKzgProofBatchChallenge cs.toArray cis.toArray cells.toArray
      evals.toArray ps.toArray) fun r => vBytes (blsFieldToBytes r)
  | "verify_cell_kzg_proof_batch" =>
    let cs ← bytesList (← field inp "commitments")
    let cis ← natList (← field inp "cell_indices")
    let cells ← bytesList (← field inp "cells")
    let ps ← bytesList (← field inp "proofs")
    return vOf (verifyCellKzgProofBatch cs cis cells ps) .bool
  | "recover_cells_and_kzg_proofs" =>
    let cis ← natList (← field inp "cell_indices")
    let cells ← bytesList (← field inp "cells")
    return vOf (recoverCellsAndKzgProofs cis cells) fun (cells, proofs) =>
      .list [.list (cells.toList.map vBytes), .list (proofs.toList.map vBytes)]
  | _ => throw s!"unknown handler {name}"

/-- Handlers and their inventory counts (scripts/consensus/inventory-v1.6.1.json). -/
def handlers : List (String × String × Nat) :=
  [("deneb", "blob_to_kzg_commitment", 11), ("deneb", "compute_blob_kzg_proof", 15),
   ("deneb", "compute_challenge", 9), ("deneb", "compute_kzg_proof", 52),
   ("deneb", "verify_blob_kzg_proof", 29), ("deneb", "verify_blob_kzg_proof_batch", 24),
   ("deneb", "verify_kzg_proof", 122),
   ("fulu", "compute_cells", 11), ("fulu", "compute_cells_and_kzg_proofs", 11),
   ("fulu", "compute_verify_cell_kzg_proof_batch_challenge", 10),
   ("fulu", "recover_cells_and_kzg_proofs", 18), ("fulu", "verify_cell_kzg_proof_batch", 32)]

/-- Differential pseudo-handlers, run only when named: (fork, name, directory, count). -/
def differentials : List (String × String × String × Nat) :=
  [("deneb", "verify_kzg_proof@jaune", "verify_kzg_proof", 122),
   ("fulu", "compute_cells@spec", "compute_cells", 11),
   ("fulu", "compute_cells_and_kzg_proofs@spec", "compute_cells_and_kzg_proofs", 11)]

def main (args : List String) : IO UInt32 := do
  let some root := args.head? | IO.eprintln "usage: jaune-consensus-kzg-vectors <tests/general> [handler ...]"; return 2
  let only := args.drop 1
  let selected := (handlers.map fun (f, h, n) => (f, h, h, n)).filter (fun (_, h, _, _) =>
      only.isEmpty || only.contains h)
    ++ differentials.filter fun (_, h, _, _) => only.contains h
  if selected.isEmpty then IO.eprintln "empty selection"; return 1
  -- Force the decoded setup before timing.
  match kzgSetupG1Lagrange, kzgSetupG1Monomial, kzgSetupG2Monomial with
  | .ok a, .ok b, .ok c => IO.println s!"setup: {a.size} lagrange, {b.size} monomial, {c.size} g2"
  | _, _, _ => IO.eprintln "setup decode failed"; return 1
  let mut totalPass := 0
  let mut totalFail := 0
  for (fork, h, hdir, expectedCount) in selected do
    let dir : System.FilePath := root / fork / "kzg" / hdir / "kzg-mainnet"
    let names := ((← dir.readDir).map (·.fileName)).qsort (· < ·)
    let mut pass := 0
    let mut fail := 0
    let t0 ← IO.monoMsNow
    for name in names do
      let y := parseYaml (← IO.FS.readFile (dir / name / "data.yaml"))
      let tc0 ← IO.monoMsNow
      let r ← IO.lazyPure fun _ => do
        let expected ← V.ofY (← field y "output")
        let got ← kzgHandler h (← field y "input")
        return got == expected
      let tc1 ← IO.monoMsNow
      if tc1 - tc0 ≥ 2000 then IO.println s!"  {name}: {tc1 - tc0} ms"
      match r with
      | .ok true => pass := pass + 1
      | .ok false => fail := fail + 1; IO.println s!"FAIL {fork}/{h}/{name}"
      | .error e => fail := fail + 1; IO.println s!"ERROR {fork}/{h}/{name}: {e}"
    let t1 ← IO.monoMsNow
    let countNote := if names.size = expectedCount then "count ok" else s!"COUNT MISMATCH (inventory {expectedCount})"
    if names.size ≠ expectedCount then fail := fail + 1
    IO.println s!"{fork}/{h}: {pass}/{names.size} passed, {countNote}, {t1 - t0} ms"
    totalPass := totalPass + pass
    totalFail := totalFail + fail
  IO.println s!"kzg: {totalPass} passed, {totalFail} failed"
  if totalPass + totalFail = 0 then IO.eprintln "empty selection"; return 1
  return if totalFail = 0 then 0 else 1
