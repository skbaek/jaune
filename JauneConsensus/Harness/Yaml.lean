/-!
# A fail-closed YAML-subset reader (conformance harness)

The consensus test vectors carry their metadata and expectations as YAML (`meta.yaml`,
`data.yaml`, `mapping.yaml`, `value.yaml`, `roots.yaml`, `steps.yaml`, ...), written by PyYAML.
This module reads the subset those files use and rejects everything else. The subset was fixed by
surveying every `.yaml` file of the pinned `v1.6.1` tarballs (126,019 files): none uses an anchor,
alias, tag, comment, block scalar (`|`, `>`), directive, `---` document marker, tab, carriage
return, blank line inside a document, or non-ASCII byte.

Accepted:

* block mappings `key: value` and block sequences `- item`, nested by indentation, including a
  block sequence at the same indentation as its parent key (PyYAML's default);
* flow sequences `[a, b]` and flow mappings `{k: v}`, which may span lines;
* plain scalars (possibly folded over several lines inside flow context; a negative integer such
  as `-3`, which the `v1.7.0-beta.4` comptests `meta.yaml` mutation lists carry, is the one plain
  scalar that may start with an indicator), single-quoted scalars
  (`''` escape) and double-quoted scalars (escapes `\\`, `\"`, `\/`, `\n`, `\t` only); a line
  break inside a scalar folds to one space;
* one optional trailing `...` document-end line.

Rejected, among others: any construct above that is absent from the subset, an empty value
(`key:` with nothing under it), a duplicate key, a plain scalar starting with an indicator
character or containing ` #`, and trailing content after a node.

Scalars stay text (`YVal.scalar s quoted`); typed readers (`asNat`, `asHex`, `asBool`, `isNull`)
interpret them strictly, so `count: '10'` is not a number and `seed: 0x..` must still be hex.

Parsing is total by fuel. This is harness code, outside the semantics.
-/

namespace JauneConsensus.Harness.Yaml

/-- A YAML node of the accepted subset. -/
inductive YVal where
  /-- A scalar, with whether it was quoted. -/
  | scalar (s : String) (quoted : Bool)
  | seq (xs : List YVal)
  | map (kvs : List (String × YVal))
  deriving Repr, Inhabited, BEq

/-- Why the reader or a typed value conversion failed. The payloads are diagnostic text only;
no caller branches on them. -/
inductive YamlError where
  /-- The input is outside the accepted subset, or malformed. -/
  | syntax (what : String)
  /-- An iteration bound was exhausted (unreachable for the bounds this module passes). -/
  | fuel
  /-- A value has the wrong shape for the typed reader. -/
  | shape (what : String)
  /-- A required mapping key is absent. -/
  | missingKey (key : String)
  deriving Repr, BEq

instance : ToString YamlError where
  toString
    | .syntax w => s!"yaml: {w}"
    | .fuel => "yaml: iteration bound exhausted"
    | .shape w => s!"yaml: {w}"
    | .missingKey k => s!"yaml: missing key {k}"

abbrev Res (α : Type) := Except YamlError α

/-! ## Characters -/

@[inline] def isSpaceOrNl (c : UInt8) : Bool := c == 0x20 || c == 0x0a

/-- Characters that may not start a plain scalar (YAML indicators). -/
def isIndicator (c : UInt8) : Bool :=
  "-?:,[]{}#&*!|>'\"%@`".toList.any (fun d => d.toNat == c.toNat)

@[inline] def isFlowEnd (c : UInt8) : Bool :=
  c == ','.toNat.toUInt8 || c == ']'.toNat.toUInt8 || c == '}'.toNat.toUInt8 ||
  c == '['.toNat.toUInt8 || c == '{'.toNat.toUInt8

@[inline] def ch (c : Char) : UInt8 := c.toNat.toUInt8

def charOf (b : UInt8) : Char := Char.ofNat b.toNat

/-- Fold a scalar's raw text: each run of spaces around a line break becomes one space. Leading
and trailing spaces of the whole are kept as given (callers trim plain scalars). -/
def foldLines (raw : List Char) : String :=
  let lines := (String.ofList raw).splitOn "\n"
  match lines with
  | [] => ""
  | [l] => l
  | l :: rest =>
    let mid := rest.dropLast.map (fun s => s.trimAscii.toString)
    let last := match rest.getLast? with
      | some s => s.trimAsciiStart.toString
      | none => ""
    " ".intercalate ((l.trimAsciiEnd.toString :: mid) ++ [last])

/-! ## Flow context

All flow parsers work on the input `ByteArray` between `pos` and an exclusive limit `lim`. -/

section Flow
variable (buf : ByteArray) (lim : Nat)

@[inline] def at? (i : Nat) : Option UInt8 := if i < lim then buf[i]? else none

/-- Skip spaces and line breaks. -/
def skipWs : Nat → Nat → Nat
  | 0, pos => pos
  | fuel + 1, pos =>
    match at? buf lim pos with
    | some c => if isSpaceOrNl c then skipWs fuel (pos + 1) else pos
    | none => pos

/-- A single-quoted scalar whose opening quote is at `pos - 1`. Returns text and the position
after the closing quote. -/
def singleQ : Nat → Nat → List Char → Res (String × Nat)
  | 0, _, _ => .error .fuel
  | fuel + 1, pos, acc =>
    match at? buf lim pos with
    | none => .error (.syntax "unterminated single-quoted scalar")
    | some c =>
      if c == ch '\'' then
        if at? buf lim (pos + 1) == some (ch '\'') then singleQ fuel (pos + 2) ('\'' :: acc)
        else .ok (foldLines acc.reverse, pos + 1)
      else singleQ fuel (pos + 1) (charOf c :: acc)

/-- A double-quoted scalar whose opening quote is at `pos - 1`. -/
def doubleQ : Nat → Nat → List Char → Res (String × Nat)
  | 0, _, _ => .error .fuel
  | fuel + 1, pos, acc =>
    match at? buf lim pos with
    | none => .error (.syntax "unterminated double-quoted scalar")
    | some c =>
      if c == ch '"' then .ok (foldLines acc.reverse, pos + 1)
      else if c == ch '\\' then
        match at? buf lim (pos + 1) with
        | some e =>
          let r : Option Char :=
            if e == ch '\\' then some '\\' else if e == ch '"' then some '"'
            else if e == ch '/' then some '/' else if e == ch 'n' then some '\n'
            else if e == ch 't' then some '\t' else none
          match r with
          | some d => doubleQ fuel (pos + 2) (d :: acc)
          | none => .error (.syntax s!"unsupported escape \\{charOf e}")
        | none => .error (.syntax "unterminated double-quoted scalar")
      else doubleQ fuel (pos + 1) (charOf c :: acc)

/-- Scan a plain scalar in flow context starting at `pos`: up to a flow indicator, a `:`
followed by a space, line break or the limit, or the limit. Returns the end position. -/
def plainEnd : Nat → Nat → Res Nat
  | 0, _ => .error .fuel
  | fuel + 1, pos =>
    match at? buf lim pos with
    | none => .ok pos
    | some c =>
      if isFlowEnd c then .ok pos
      else if c == ch ':' then
        match at? buf lim (pos + 1) with
        | none => .ok pos
        | some d => if isSpaceOrNl d then .ok pos else plainEnd fuel (pos + 1)
      else if c == ch '#' then .error (.syntax "'#' in a plain scalar (comment) is outside the subset")
      else plainEnd fuel (pos + 1)

def plainText (start stop : Nat) : String :=
  let raw := ((List.range (stop - start)).filterMap (fun i => buf[start + i]?)).map charOf
  (foldLines raw).trimAscii.toString

mutual
/-- One flow node at `pos` (whitespace already skipped). -/
def node : Nat → Nat → Res (YVal × Nat)
  | 0, _ => .error .fuel
  | fuel + 1, pos =>
    match at? buf lim pos with
    | none => .error (.syntax "missing value")
    | some c =>
      if c == ch '[' then seqItems fuel (skipWs buf lim (lim + 1) (pos + 1)) [] true
      else if c == ch '{' then mapItems fuel (skipWs buf lim (lim + 1) (pos + 1)) [] true
      else if c == ch '\'' then do
        let (s, p) ← singleQ buf lim (lim + 1) (pos + 1) []
        pure (.scalar s true, p)
      else if c == ch '"' then do
        let (s, p) ← doubleQ buf lim (lim + 1) (pos + 1) []
        pure (.scalar s true, p)
      else if isIndicator c && !(c == ch '-' && (at? buf lim (pos + 1)).any (fun d => ch '0' ≤ d && d ≤ ch '9')) then
        .error (.syntax s!"plain scalar starts with indicator '{charOf c}'")
      else do
        let stop ← plainEnd buf lim (lim + 1) pos
        let s := plainText buf pos stop
        if s.isEmpty then .error (.syntax "empty plain scalar") else pure (.scalar s false, stop)

/-- Items of a flow sequence; `pos` is past `[` and whitespace. -/
def seqItems : Nat → Nat → List YVal → Bool → Res (YVal × Nat)
  | 0, _, _, _ => .error .fuel
  | fuel + 1, pos, acc, first =>
    if first && at? buf lim pos == some (ch ']') then .ok (.seq [], pos + 1) else do
    let (v, p) ← node fuel pos
    let p := skipWs buf lim (lim + 1) p
    match at? buf lim p with
    | some c =>
      if c == ch ',' then seqItems fuel (skipWs buf lim (lim + 1) (p + 1)) (v :: acc) false
      else if c == ch ']' then .ok (.seq (v :: acc).reverse, p + 1)
      else .error (.syntax s!"expected ',' or ']' in flow sequence, found '{charOf c}'")
    | none => .error (.syntax "unterminated flow sequence")

/-- Entries of a flow mapping; `pos` is past `{` and whitespace. -/
def mapItems : Nat → Nat → List (String × YVal) → Bool → Res (YVal × Nat)
  | 0, _, _, _ => .error .fuel
  | fuel + 1, pos, acc, first =>
    if first && at? buf lim pos == some (ch '}') then .ok (.map [], pos + 1) else do
    let (k, p) ← node fuel pos
    let key ← match k with
      | .scalar s _ => pure s
      | _ => .error (.syntax "non-scalar mapping key")
    let p := skipWs buf lim (lim + 1) p
    if at? buf lim p != some (ch ':') then .error (.syntax s!"expected ':' after key {key}")
    else if !(at? buf lim (p + 1)).any isSpaceOrNl then
      .error (.syntax s!"expected space after ':' (key {key})")
    else if acc.any (·.1 == key) then .error (.syntax s!"duplicate key {key}")
    else do
    let (v, q) ← node fuel (skipWs buf lim (lim + 1) (p + 1))
    let q := skipWs buf lim (lim + 1) q
    match at? buf lim q with
    | some c =>
      if c == ch ',' then mapItems fuel (skipWs buf lim (lim + 1) (q + 1)) ((key, v) :: acc) false
      else if c == ch '}' then .ok (.map ((key, v) :: acc).reverse, q + 1)
      else .error (.syntax s!"expected ',' or '}}' in flow mapping, found '{charOf c}'")
    | none => .error (.syntax "unterminated flow mapping")
end

/-- A complete inline node occupying `[pos, lim)` up to trailing whitespace. -/
def inline (pos : Nat) : Res YVal := do
  let (v, p) ← node buf lim (2 * lim + 2) (skipWs buf lim (lim + 1) pos)
  if skipWs buf lim (lim + 1) p == lim then pure v
  else .error (.syntax s!"trailing content at byte {p}")

end Flow

/-! ## Block context -/

/-- A source line: indentation (column of `start`), first non-space byte, and end (the line
break or end of input, exclusive). `start = stop` never occurs: blank lines are rejected. -/
structure Line where
  col : Nat
  start : Nat
  stop : Nat
  deriving Repr

section Block
variable (buf : ByteArray)

def lineText (l : Line) : String :=
  String.ofList (((List.range (l.stop - l.start)).filterMap (fun i => buf[l.start + i]?)).map charOf)

/-- Is the line a block-sequence entry (`-` then a space or the line end)? -/
def isDash (l : Line) : Bool :=
  buf[l.start]? == some (ch '-') && (l.start + 1 == l.stop || buf[l.start + 1]? == some (ch ' '))

/-- If the line is a block-mapping entry, its key and the position where the value text starts
(after `: ` and spaces; equal to `stop` when the value is on following lines). A plain key is the
text before the first `: ` (or a final `:`); quoted keys are outside the subset. -/
def mapEntry? (l : Line) : Option (String × Nat) :=
  match buf[l.start]? with
  | none => none
  | some c =>
    if isIndicator c then none else
    let rec find : Nat → Nat → Option Nat
      | 0, _ => none
      | fuel + 1, i =>
        if i ≥ l.stop then none
        else if buf[i]? == some (ch ':') && (i + 1 == l.stop || buf[i + 1]? == some (ch ' '))
          then some i
        else find fuel (i + 1)
    match find (l.stop - l.start) l.start with
    | none => none
    | some i =>
      let key := lineText buf { col := l.col, start := l.start, stop := i }
      if key.any (· == ' ') && key.trimAsciiEnd.toString != key then none else
      let rec skip : Nat → Nat → Nat
        | 0, j => j
        | fuel + 1, j => if j < l.stop && buf[j]? == some (ch ' ') then skip fuel (j + 1) else j
      some (key, skip (l.stop - i) (i + 1))

/-- The end of the inline text that starts on `first`: through every following line indented at
least `minCol`. Returns that end and the remaining lines. -/
def gather (first : Line) (minCol : Nat) : List Line → Nat × List Line
  | [] => (first.stop, [])
  | l :: ls =>
    if l.col ≥ minCol then gather l minCol ls else (first.stop, l :: ls)

mutual
/-- A node whose first line is `l` (with indentation `l.col ≥ minCol`). -/
def blockNode : Nat → Line → List Line → Nat → Res (YVal × List Line)
  | 0, _, _, _ => .error .fuel
  | fuel + 1, l, ls, minCol =>
    if isDash buf l then blockSeq fuel l.col (l :: ls) []
    else if (mapEntry? buf l).isSome then blockMap fuel l.col (l :: ls) []
    else
      let (stop, rest) := gather l minCol ls
      match inline buf stop l.start with
      | .ok v => .ok (v, rest)
      | .error e => .error e

/-- Entries of a block sequence at column `col`. -/
def blockSeq : Nat → Nat → List Line → List YVal → Res (YVal × List Line)
  | 0, _, _, _ => .error .fuel
  | _, _, [], acc => .ok (.seq acc.reverse, [])
  | fuel + 1, col, l :: ls, acc =>
    if l.col < col then .ok (.seq acc.reverse, l :: ls)
    else if l.col > col then .error (.syntax s!"unexpected indentation at byte {l.start}")
    else if !isDash buf l then .ok (.seq acc.reverse, l :: ls)
    else do
      let (v, rest) ←
        if l.start + 1 == l.stop then
          match ls with
          | m :: ms =>
            if m.col > col then blockNode fuel m ms (col + 1)
            else .error (.syntax s!"empty sequence entry at byte {l.start}")
          | [] => .error (.syntax s!"empty sequence entry at byte {l.start}")
        else
          let rec firstNonSpace : Nat → Nat → Nat
            | 0, j => j
            | f + 1, j => if buf[j]? == some (ch ' ') then firstNonSpace f (j + 1) else j
          let s := firstNonSpace (l.stop - l.start) (l.start + 1)
          let virt : Line := { col := l.col + (s - l.start), start := s, stop := l.stop }
          blockNode fuel virt ls (col + 1)
      blockSeq fuel col rest (v :: acc)

/-- Entries of a block mapping at column `col`. -/
def blockMap : Nat → Nat → List Line → List (String × YVal) → Res (YVal × List Line)
  | 0, _, _, _ => .error .fuel
  | _, _, [], acc => .ok (.map acc.reverse, [])
  | fuel + 1, col, l :: ls, acc =>
    if l.col < col then .ok (.map acc.reverse, l :: ls)
    else if l.col > col then .error (.syntax s!"unexpected indentation at byte {l.start}")
    else match mapEntry? buf l with
    | none =>
      if isDash buf l then .error (.syntax s!"sequence entry inside a mapping at byte {l.start}")
      else .error (.syntax s!"expected a mapping entry at byte {l.start}")
    | some (key, vpos) =>
      if acc.any (·.1 == key) then .error (.syntax s!"duplicate key {key}") else do
      let (v, rest) ←
        if vpos < l.stop then
          let (stop, rest) := gather { l with start := vpos } (col + 1) ls
          match inline buf stop vpos with
          | .ok v => pure (v, rest)
          | .error e => throw e
        else
          match ls with
          | m :: ms =>
            if m.col > col then blockNode fuel m ms (col + 1)
            else if m.col == col && isDash buf m then blockSeq fuel col (m :: ms) []
            else .error (.syntax s!"empty value for key {key}")
          | [] => .error (.syntax s!"empty value for key {key}")
      blockMap fuel col rest ((key, v) :: acc)
end

end Block

/-! ## Documents -/

/-- Split into lines, enforcing the character subset: printable ASCII and `\n` only; no blank
line inside the document; an optional final `...` line. -/
def lines (buf : ByteArray) : Res (List Line) := do
  for b in buf.data do
    if b != 0x0a && (b < 0x20 || b > 0x7e) then
      throw (.syntax s!"byte {b} outside the accepted subset (printable ASCII and line breaks)")
  -- line boundaries
  let mut out : Array Line := #[]
  let mut begin := 0
  for i in [0:buf.size + 1] do
    if i == buf.size || buf[i]? == some 0x0a then
      if i < buf.size || begin < buf.size then
        let mut s := begin
        for j in [begin:i] do
          if s == j && buf[j]? == some 0x20 then s := j + 1
        out := out.push { col := s - begin, start := s, stop := i }
      begin := i + 1
  -- drop trailing blank lines and one `...`
  let mut ls := out.toList.reverse
  ls := ls.dropWhile (fun l => l.start == l.stop)
  match ls with
  | l :: rest =>
    if lineText buf l == "..." && l.col == 0 then ls := rest.dropWhile (fun l => l.start == l.stop)
  | [] => pure ()
  let docLines := ls.reverse
  for l in docLines do
    if l.start == l.stop then throw (.syntax s!"blank line at byte {l.start} is outside the subset")
    let t := lineText buf l
    if l.col == 0 && (t == "---" || t.startsWith "--- " || t == "..." || t.startsWith "%") then
      throw (.syntax s!"document marker or directive '{t}' is outside the subset")
  pure docLines

/-- Parse one document of the accepted subset. -/
def parse (buf : ByteArray) : Res YVal := do
  let ls ← lines buf
  match ls with
  | [] => throw (.syntax "empty document")
  | l :: rest =>
    if l.col != 0 then throw (.syntax "document does not start at column 0")
    let (v, rest) ← blockNode buf (2 * ls.length + 2) l rest 0
    if !rest.isEmpty then throw (.syntax "trailing content after the document node")
    pure v

def parseString (s : String) : Res YVal := parse s.toUTF8

/-! ## Typed readers -/

namespace YVal

def get? (v : YVal) (key : String) : Option YVal :=
  match v with
  | .map kvs => (kvs.find? (·.1 == key)).map (·.2)
  | _ => none

/-- The keys of a mapping, in order. -/
def keys : YVal → List String
  | .map kvs => kvs.map (·.1)
  | _ => []

def field (v : YVal) (key : String) : Res YVal :=
  match v.get? key with
  | some x => .ok x
  | none => .error (.missingKey key)

/-- Require a mapping with exactly the given keys (in any order). -/
def expectKeys (v : YVal) (ks : List String) : Res Unit :=
  match v with
  | .map kvs =>
    if kvs.length == ks.length && ks.all (fun k => kvs.any (·.1 == k)) then .ok ()
    else .error (.shape s!"expected exactly keys {ks}, found {kvs.map (·.1)}")
  | _ => .error (.shape "expected a mapping")

def asSeq : YVal → Res (List YVal)
  | .seq xs => .ok xs
  | _ => .error (.shape "expected a sequence")

/-- A plain decimal natural number: digits only, no sign, no leading zero (except `0`). -/
def asNat : YVal → Res Nat
  | .scalar s false =>
    let cs := s.toList
    if cs.isEmpty || !cs.all Char.isDigit || (cs.length > 1 && cs.head? == some '0') then
      .error (.shape s!"not a decimal natural: {s}")
    else .ok (cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0)
  | _ => .error (.shape "expected a plain decimal scalar")

/-- A quoted decimal natural (the vectors quote integers wider than 64 bits). Same digit rules
as `asNat`. -/
def asQuotedNat : YVal → Res Nat
  | .scalar s true => asNat (.scalar s false)
  | _ => .error (.shape "expected a quoted decimal scalar")

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode an even-length hexadecimal digit string. -/
def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexVal a
    let y ← hexVal b
    let r ← hexBytes rest
    pure ((16 * x + y).toUInt8 :: r)
  | [_] => none

/-- A `0x`-prefixed even-length hex string, quoted or plain. -/
def asHex : YVal → Res (List UInt8)
  | .scalar s _ =>
    match s.toList with
    | '0' :: 'x' :: cs =>
      match hexBytes cs with
      | some bs => .ok bs
      | none => .error (.shape s!"bad hex string {s}")
    | _ => .error (.shape s!"hex string without 0x prefix: {s}")
  | _ => .error (.shape "expected a hex scalar")

def asBool : YVal → Res Bool
  | .scalar "true" false => .ok true
  | .scalar "false" false => .ok false
  | _ => .error (.shape "expected true or false")

def isNull : YVal → Bool
  | .scalar "null" false => true
  | .scalar "~" false => true
  | _ => false

end YVal

/-! ## Tests -/

private def p (s : String) : Option YVal := (parseString s).toOption
private def rejects (s : String) : Bool := (parseString s).toBool == false
private def sc (s : String) : YVal := .scalar s false
private def q (s : String) : YVal := .scalar s true

-- shuffling `mapping.yaml`
#guard p "seed: '0x23'\ncount: 3\nmapping: [2, 0, 1]\n" ==
  some (.map [("seed", q "0x23"), ("count", sc "3"), ("mapping", .seq [sc "2", sc "0", sc "1"])])
#guard p "seed: '0x23'\ncount: 0\nmapping: []\n" ==
  some (.map [("seed", q "0x23"), ("count", sc "0"), ("mapping", .seq [])])
-- a flow sequence folded over lines
#guard p "mapping: [1, 2,\n  3]\n" == some (.map [("mapping", .seq [sc "1", sc "2", sc "3"])])
-- a bare scalar document with a document-end marker (ssz_generic `value.yaml`)
#guard p "15469901483724453991\n...\n" == some (sc "15469901483724453991")
-- flow mappings, double quotes, booleans (`meta.yaml`, `steps.yaml`)
#guard p "{description: \"it's \\\"x\\\"\"}\n" == some (.map [("description", q "it's \"x\"")])
#guard p "- {tick: 7728}\n- {block: \n    block_0x9d, \n    valid: true}\n" ==
  some (.seq [.map [("tick", sc "7728")], .map [("block", sc "block_0x9d"), ("valid", sc "true")]])
-- nested block structures, a sequence at its key's indentation
#guard p "- checks:\n    head:\n      slot: 0\n- a: 1\n  b: 2\nk:\n- x\n- y\n" == none
#guard p "steps:\n- checks:\n    head:\n      slot: 0\n- a: 1\n  b: 2\n" ==
  some (.map [("steps", .seq [.map [("checks", .map [("head", .map [("slot", sc "0")])])],
    .map [("a", sc "1"), ("b", sc "2")]])])
#guard p "input:\n  blob: '0x00'\noutput: null\n" ==
  some (.map [("input", .map [("blob", q "0x00")]), ("output", sc "null")])
-- single-quote escape
#guard p "a: 'it''s'\n" == some (.map [("a", q "it's")])
-- rejections
#guard rejects "a: 1\na: 2\n"            -- duplicate key
#guard rejects "a: &x 1\n"              -- anchor
#guard rejects "a: !t 1\n"              -- tag
#guard rejects "a: |\n  x\n"            -- block scalar
#guard rejects "a: 1 # c\n"             -- comment
#guard rejects "---\na: 1\n"            -- document marker
#guard rejects "a: 1\n\nb: 2\n"         -- blank line
#guard rejects "a:\tb\n"                -- tab
#guard rejects "a:\n"                   -- empty value
#guard rejects "a: [1, 2\n"             -- unterminated flow
#guard rejects "a: [1, 2]]\n"           -- trailing content
#guard rejects "a: 'x\n"                -- unterminated quote
#guard rejects "a: \"\\q\"\n"           -- unsupported escape
#guard rejects "a: 1\n b: 2\n"          -- bad indentation
#guard rejects ""                       -- empty document
-- typed readers
#guard ((p "c: 10\n").bind (·.get? "c")).map (·.asNat.toOption) == some (some 10)
#guard ((p "c: '10'\n").bind (·.get? "c")).map (·.asNat.toOption) == some none
#guard ((p "c: 010\n").bind (·.get? "c")).map (·.asNat.toOption) == some none
#guard ((p "c: '10'\n").bind (·.get? "c")).map (·.asQuotedNat.toOption) == some (some 10)
#guard ((p "c: 10\n").bind (·.get? "c")).map (·.asQuotedNat.toOption) == some none
#guard ((p "c: '0x0aFf'\n").bind (·.get? "c")).map (·.asHex.toOption) == some (some [10, 255])
#guard ((p "c: '0xa'\n").bind (·.get? "c")).map (·.asHex.toOption) == some none

end JauneConsensus.Harness.Yaml
