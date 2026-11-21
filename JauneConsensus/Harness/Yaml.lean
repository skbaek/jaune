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
inductive YamlValue where
  /-- A scalar, with whether it was quoted. -/
  | scalar (s : String) (quoted : Bool)
  | sequence (xs : List YamlValue)
  | map (kvs : List (String × YamlValue))
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

abbrev Result (α : Type) := Except YamlError α

/-! ## Characters -/

@[inline] def isSpaceOrNewline (c : UInt8) : Bool := c == 0x20 || c == 0x0a

/-- Characters that may not start a plain scalar (YAML indicators). -/
def isIndicator (c : UInt8) : Bool :=
  "-?:,[]{}#&*!|>'\"%@`".toList.any (fun d => d.toNat == c.toNat)

@[inline] def isFlowEnd (c : UInt8) : Bool :=
  c == ','.toNat.toUInt8 || c == ']'.toNat.toUInt8 || c == '}'.toNat.toUInt8 ||
  c == '['.toNat.toUInt8 || c == '{'.toNat.toUInt8

@[inline] def characterByte (c : Char) : UInt8 := c.toNat.toUInt8

def byteToCharacter (b : UInt8) : Char := Char.ofNat b.toNat

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
def skipWhitespace : Nat → Nat → Nat
  | 0, pos => pos
  | fuel + 1, pos =>
    match at? buf lim pos with
    | some c => if isSpaceOrNewline c then skipWhitespace fuel (pos + 1) else pos
    | none => pos

/-- A single-quoted scalar whose opening quote is at `pos - 1`. Returns text and the position
after the closing quote. -/
def singleQuoted : Nat → Nat → List Char → Result (String × Nat)
  | 0, _, _ => .error .fuel
  | fuel + 1, pos, acc =>
    match at? buf lim pos with
    | none => .error (.syntax "unterminated single-quoted scalar")
    | some c =>
      if c == characterByte '\'' then
        if at? buf lim (pos + 1) == some (characterByte '\'') then singleQuoted fuel (pos + 2) ('\'' :: acc)
        else .ok (foldLines acc.reverse, pos + 1)
      else singleQuoted fuel (pos + 1) (byteToCharacter c :: acc)

/-- A double-quoted scalar whose opening quote is at `pos - 1`. -/
def doubleQuoted : Nat → Nat → List Char → Result (String × Nat)
  | 0, _, _ => .error .fuel
  | fuel + 1, pos, acc =>
    match at? buf lim pos with
    | none => .error (.syntax "unterminated double-quoted scalar")
    | some c =>
      if c == characterByte '"' then .ok (foldLines acc.reverse, pos + 1)
      else if c == characterByte '\\' then
        match at? buf lim (pos + 1) with
        | some e =>
          let r : Option Char :=
            if e == characterByte '\\' then some '\\' else if e == characterByte '"' then some '"'
            else if e == characterByte '/' then some '/' else if e == characterByte 'n' then some '\n'
            else if e == characterByte 't' then some '\t' else none
          match r with
          | some d => doubleQuoted fuel (pos + 2) (d :: acc)
          | none => .error (.syntax s!"unsupported escape \\{byteToCharacter e}")
        | none => .error (.syntax "unterminated double-quoted scalar")
      else doubleQuoted fuel (pos + 1) (byteToCharacter c :: acc)

/-- Scan a plain scalar in flow context starting at `pos`: up to a flow indicator, a `:`
followed by a space, line break or the limit, or the limit. Returns the end position. -/
def plainEnd : Nat → Nat → Result Nat
  | 0, _ => .error .fuel
  | fuel + 1, pos =>
    match at? buf lim pos with
    | none => .ok pos
    | some c =>
      if isFlowEnd c then .ok pos
      else if c == characterByte ':' then
        match at? buf lim (pos + 1) with
        | none => .ok pos
        | some d => if isSpaceOrNewline d then .ok pos else plainEnd fuel (pos + 1)
      else if c == characterByte '#' then .error (.syntax "'#' in a plain scalar (comment) is outside the subset")
      else plainEnd fuel (pos + 1)

def plainText (start stop : Nat) : String :=
  let raw := ((List.range (stop - start)).filterMap (fun i => buf[start + i]?)).map byteToCharacter
  (foldLines raw).trimAscii.toString

mutual
/-- One flow node at `pos` (whitespace already skipped). -/
def node : Nat → Nat → Result (YamlValue × Nat)
  | 0, _ => .error .fuel
  | fuel + 1, pos =>
    match at? buf lim pos with
    | none => .error (.syntax "missing value")
    | some c =>
      if c == characterByte '[' then sequenceItems fuel (skipWhitespace buf lim (lim + 1) (pos + 1)) [] true
      else if c == characterByte '{' then mapItems fuel (skipWhitespace buf lim (lim + 1) (pos + 1)) [] true
      else if c == characterByte '\'' then do
        let (s, p) ← singleQuoted buf lim (lim + 1) (pos + 1) []
        pure (.scalar s true, p)
      else if c == characterByte '"' then do
        let (s, p) ← doubleQuoted buf lim (lim + 1) (pos + 1) []
        pure (.scalar s true, p)
      else if isIndicator c && !(c == characterByte '-' && (at? buf lim (pos + 1)).any (fun d => characterByte '0' ≤ d && d ≤ characterByte '9')) then
        .error (.syntax s!"plain scalar starts with indicator '{byteToCharacter c}'")
      else do
        let stop ← plainEnd buf lim (lim + 1) pos
        let s := plainText buf pos stop
        if s.isEmpty then .error (.syntax "empty plain scalar") else pure (.scalar s false, stop)

/-- Items of a flow sequence; `pos` is past `[` and whitespace. -/
def sequenceItems : Nat → Nat → List YamlValue → Bool → Result (YamlValue × Nat)
  | 0, _, _, _ => .error .fuel
  | fuel + 1, pos, acc, first =>
    if first && at? buf lim pos == some (characterByte ']') then .ok (.sequence [], pos + 1) else do
    let (v, p) ← node fuel pos
    let p := skipWhitespace buf lim (lim + 1) p
    match at? buf lim p with
    | some c =>
      if c == characterByte ',' then sequenceItems fuel (skipWhitespace buf lim (lim + 1) (p + 1)) (v :: acc) false
      else if c == characterByte ']' then .ok (.sequence (v :: acc).reverse, p + 1)
      else .error (.syntax s!"expected ',' or ']' in flow sequence, found '{byteToCharacter c}'")
    | none => .error (.syntax "unterminated flow sequence")

/-- Entries of a flow mapping; `pos` is past `{` and whitespace. -/
def mapItems : Nat → Nat → List (String × YamlValue) → Bool → Result (YamlValue × Nat)
  | 0, _, _, _ => .error .fuel
  | fuel + 1, pos, acc, first =>
    if first && at? buf lim pos == some (characterByte '}') then .ok (.map [], pos + 1) else do
    let (k, p) ← node fuel pos
    let key ← match k with
      | .scalar s _ => pure s
      | _ => .error (.syntax "non-scalar mapping key")
    let p := skipWhitespace buf lim (lim + 1) p
    if at? buf lim p != some (characterByte ':') then .error (.syntax s!"expected ':' after key {key}")
    else if !(at? buf lim (p + 1)).any isSpaceOrNewline then
      .error (.syntax s!"expected space after ':' (key {key})")
    else if acc.any (·.1 == key) then .error (.syntax s!"duplicate key {key}")
    else do
    let (v, q) ← node fuel (skipWhitespace buf lim (lim + 1) (p + 1))
    let q := skipWhitespace buf lim (lim + 1) q
    match at? buf lim q with
    | some c =>
      if c == characterByte ',' then mapItems fuel (skipWhitespace buf lim (lim + 1) (q + 1)) ((key, v) :: acc) false
      else if c == characterByte '}' then .ok (.map ((key, v) :: acc).reverse, q + 1)
      else .error (.syntax s!"expected ',' or '}}' in flow mapping, found '{byteToCharacter c}'")
    | none => .error (.syntax "unterminated flow mapping")
end

/-- A complete inline node occupying `[pos, lim)` up to trailing whitespace. -/
def inline (pos : Nat) : Result YamlValue := do
  let (v, p) ← node buf lim (2 * lim + 2) (skipWhitespace buf lim (lim + 1) pos)
  if skipWhitespace buf lim (lim + 1) p == lim then pure v
  else .error (.syntax s!"trailing content at byte {p}")

end Flow

/-! ## Block context -/

/-- A source line: indentation (column of `start`), first non-space byte, and end (the line
break or end of input, exclusive). `start = stop` never occurs: blank lines are rejected. -/
structure Line where
  column : Nat
  start : Nat
  stop : Nat
  deriving Repr

section Block
variable (buf : ByteArray)

def lineText (l : Line) : String :=
  String.ofList (((List.range (l.stop - l.start)).filterMap (fun i => buf[l.start + i]?)).map byteToCharacter)

/-- Is the line a block-sequence entry (`-` then a space or the line end)? -/
def isDash (l : Line) : Bool :=
  buf[l.start]? == some (characterByte '-') && (l.start + 1 == l.stop || buf[l.start + 1]? == some (characterByte ' '))

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
        else if buf[i]? == some (characterByte ':') && (i + 1 == l.stop || buf[i + 1]? == some (characterByte ' '))
          then some i
        else find fuel (i + 1)
    match find (l.stop - l.start) l.start with
    | none => none
    | some i =>
      let key := lineText buf { column := l.column, start := l.start, stop := i }
      if key.any (· == ' ') && key.trimAsciiEnd.toString != key then none else
      let rec skip : Nat → Nat → Nat
        | 0, j => j
        | fuel + 1, j => if j < l.stop && buf[j]? == some (characterByte ' ') then skip fuel (j + 1) else j
      some (key, skip (l.stop - i) (i + 1))

/-- The end of the inline text that starts on `first`: through every following line indented at
least `minCol`. Returns that end and the remaining lines. -/
def gather (first : Line) (minCol : Nat) : List Line → Nat × List Line
  | [] => (first.stop, [])
  | l :: ls =>
    if l.column ≥ minCol then gather l minCol ls else (first.stop, l :: ls)

mutual
/-- A node whose first line is `l` (with indentation `l.col ≥ minCol`). -/
def blockNode : Nat → Line → List Line → Nat → Result (YamlValue × List Line)
  | 0, _, _, _ => .error .fuel
  | fuel + 1, l, ls, minCol =>
    if isDash buf l then blockSequence fuel l.column (l :: ls) []
    else if (mapEntry? buf l).isSome then blockMap fuel l.column (l :: ls) []
    else
      let (stop, rest) := gather l minCol ls
      match inline buf stop l.start with
      | .ok v => .ok (v, rest)
      | .error e => .error e

/-- Entries of a block sequence at column `col`. -/
def blockSequence : Nat → Nat → List Line → List YamlValue → Result (YamlValue × List Line)
  | 0, _, _, _ => .error .fuel
  | _, _, [], acc => .ok (.sequence acc.reverse, [])
  | fuel + 1, col, l :: ls, acc =>
    if l.column < col then .ok (.sequence acc.reverse, l :: ls)
    else if l.column > col then .error (.syntax s!"unexpected indentation at byte {l.start}")
    else if !isDash buf l then .ok (.sequence acc.reverse, l :: ls)
    else do
      let (v, rest) ←
        if l.start + 1 == l.stop then
          match ls with
          | m :: ms =>
            if m.column > col then blockNode fuel m ms (col + 1)
            else .error (.syntax s!"empty sequence entry at byte {l.start}")
          | [] => .error (.syntax s!"empty sequence entry at byte {l.start}")
        else
          let rec firstNonSpace : Nat → Nat → Nat
            | 0, j => j
            | f + 1, j => if buf[j]? == some (characterByte ' ') then firstNonSpace f (j + 1) else j
          let s := firstNonSpace (l.stop - l.start) (l.start + 1)
          let virt : Line := { column := l.column + (s - l.start), start := s, stop := l.stop }
          blockNode fuel virt ls (col + 1)
      blockSequence fuel col rest (v :: acc)

/-- Entries of a block mapping at column `col`. -/
def blockMap : Nat → Nat → List Line → List (String × YamlValue) → Result (YamlValue × List Line)
  | 0, _, _, _ => .error .fuel
  | _, _, [], acc => .ok (.map acc.reverse, [])
  | fuel + 1, col, l :: ls, acc =>
    if l.column < col then .ok (.map acc.reverse, l :: ls)
    else if l.column > col then .error (.syntax s!"unexpected indentation at byte {l.start}")
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
            if m.column > col then blockNode fuel m ms (col + 1)
            else if m.column == col && isDash buf m then blockSequence fuel col (m :: ms) []
            else .error (.syntax s!"empty value for key {key}")
          | [] => .error (.syntax s!"empty value for key {key}")
      blockMap fuel col rest ((key, v) :: acc)
end

end Block

/-! ## Documents -/

/-- Split into lines, enforcing the character subset: printable ASCII and `\n` only; no blank
line inside the document; an optional final `...` line. -/
def lines (buf : ByteArray) : Result (List Line) := do
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
        out := out.push { column := s - begin, start := s, stop := i }
      begin := i + 1
  -- drop trailing blank lines and one `...`
  let mut ls := out.toList.reverse
  ls := ls.dropWhile (fun l => l.start == l.stop)
  match ls with
  | l :: rest =>
    if lineText buf l == "..." && l.column == 0 then ls := rest.dropWhile (fun l => l.start == l.stop)
  | [] => pure ()
  let docLines := ls.reverse
  for l in docLines do
    if l.start == l.stop then throw (.syntax s!"blank line at byte {l.start} is outside the subset")
    let t := lineText buf l
    if l.column == 0 && (t == "---" || t.startsWith "--- " || t == "..." || t.startsWith "%") then
      throw (.syntax s!"document marker or directive '{t}' is outside the subset")
  pure docLines

/-- Parse one document of the accepted subset. -/
def parse (buf : ByteArray) : Result YamlValue := do
  let ls ← lines buf
  match ls with
  | [] => throw (.syntax "empty document")
  | l :: rest =>
    if l.column != 0 then throw (.syntax "document does not start at column 0")
    let (v, rest) ← blockNode buf (2 * ls.length + 2) l rest 0
    if !rest.isEmpty then throw (.syntax "trailing content after the document node")
    pure v

def parseString (s : String) : Result YamlValue := parse s.toUTF8

/-! ## Typed readers -/

namespace YamlValue

def get? (v : YamlValue) (key : String) : Option YamlValue :=
  match v with
  | .map kvs => (kvs.find? (·.1 == key)).map (·.2)
  | _ => none

/-- The keys of a mapping, in order. -/
def keys : YamlValue → List String
  | .map kvs => kvs.map (·.1)
  | _ => []

def field (v : YamlValue) (key : String) : Result YamlValue :=
  match v.get? key with
  | some x => .ok x
  | none => .error (.missingKey key)

/-- Require a mapping with exactly the given keys (in any order). -/
def expectKeys (v : YamlValue) (ks : List String) : Result Unit :=
  match v with
  | .map kvs =>
    if kvs.length == ks.length && ks.all (fun k => kvs.any (·.1 == k)) then .ok ()
    else .error (.shape s!"expected exactly keys {ks}, found {kvs.map (·.1)}")
  | _ => .error (.shape "expected a mapping")

def asSequence : YamlValue → Result (List YamlValue)
  | .sequence xs => .ok xs
  | _ => .error (.shape "expected a sequence")

/-- A plain decimal natural number: digits only, no sign, no leading zero (except `0`). -/
def asNat : YamlValue → Result Nat
  | .scalar s false =>
    let cs := s.toList
    if cs.isEmpty || !cs.all Char.isDigit || (cs.length > 1 && cs.head? == some '0') then
      .error (.shape s!"not a decimal natural: {s}")
    else .ok (cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0)
  | _ => .error (.shape "expected a plain decimal scalar")

/-- A quoted decimal natural (the vectors quote integers wider than 64 bits). Same digit rules
as `asNat`. -/
def asQuotedNat : YamlValue → Result Nat
  | .scalar s true => asNat (.scalar s false)
  | _ => .error (.shape "expected a quoted decimal scalar")

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode an even-length hexadecimal digit string. -/
def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexValue a
    let y ← hexValue b
    let r ← hexBytes rest
    pure ((16 * x + y).toUInt8 :: r)
  | [_] => none

/-- A `0x`-prefixed even-length hex string, quoted or plain. -/
def asHex : YamlValue → Result (List UInt8)
  | .scalar s _ =>
    match s.toList with
    | '0' :: 'x' :: cs =>
      match hexBytes cs with
      | some bs => .ok bs
      | none => .error (.shape s!"bad hex string {s}")
    | _ => .error (.shape s!"hex string without 0x prefix: {s}")
  | _ => .error (.shape "expected a hex scalar")

def asBool : YamlValue → Result Bool
  | .scalar "true" false => .ok true
  | .scalar "false" false => .ok false
  | _ => .error (.shape "expected true or false")

def isNull : YamlValue → Bool
  | .scalar "null" false => true
  | .scalar "~" false => true
  | _ => false

end YamlValue

/-! ## Tests -/

private def parseToOption (s : String) : Option YamlValue := (parseString s).toOption
private def rejects (s : String) : Bool := (parseString s).toBool == false
private def plainScalar (s : String) : YamlValue := .scalar s false
private def quotedScalar (s : String) : YamlValue := .scalar s true

-- shuffling `mapping.yaml`
#guard parseToOption "seed: '0x23'\ncount: 3\nmapping: [2, 0, 1]\n" ==
  some (.map [("seed", quotedScalar "0x23"), ("count", plainScalar "3"), ("mapping", .sequence [plainScalar "2", plainScalar "0", plainScalar "1"])])
#guard parseToOption "seed: '0x23'\ncount: 0\nmapping: []\n" ==
  some (.map [("seed", quotedScalar "0x23"), ("count", plainScalar "0"), ("mapping", .sequence [])])
-- a flow sequence folded over lines
#guard parseToOption "mapping: [1, 2,\n  3]\n" == some (.map [("mapping", .sequence [plainScalar "1", plainScalar "2", plainScalar "3"])])
-- a bare scalar document with a document-end marker (ssz_generic `value.yaml`)
#guard parseToOption "15469901483724453991\n...\n" == some (plainScalar "15469901483724453991")
-- flow mappings, double quotes, booleans (`meta.yaml`, `steps.yaml`)
#guard parseToOption "{description: \"it's \\\"x\\\"\"}\n" == some (.map [("description", quotedScalar "it's \"x\"")])
#guard parseToOption "- {tick: 7728}\n- {block: \n    block_0x9d, \n    valid: true}\n" ==
  some (.sequence [.map [("tick", plainScalar "7728")], .map [("block", plainScalar "block_0x9d"), ("valid", plainScalar "true")]])
-- nested block structures, a sequence at its key's indentation
#guard parseToOption "- checks:\n    head:\n      slot: 0\n- a: 1\n  b: 2\nk:\n- x\n- y\n" == none
#guard parseToOption "steps:\n- checks:\n    head:\n      slot: 0\n- a: 1\n  b: 2\n" ==
  some (.map [("steps", .sequence [.map [("checks", .map [("head", .map [("slot", plainScalar "0")])])],
    .map [("a", plainScalar "1"), ("b", plainScalar "2")]])])
#guard parseToOption "input:\n  blob: '0x00'\noutput: null\n" ==
  some (.map [("input", .map [("blob", quotedScalar "0x00")]), ("output", plainScalar "null")])
-- single-quote escape
#guard parseToOption "a: 'it''s'\n" == some (.map [("a", quotedScalar "it's")])
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
#guard ((parseToOption "c: 10\n").bind (·.get? "c")).map (·.asNat.toOption) == some (some 10)
#guard ((parseToOption "c: '10'\n").bind (·.get? "c")).map (·.asNat.toOption) == some none
#guard ((parseToOption "c: 010\n").bind (·.get? "c")).map (·.asNat.toOption) == some none
#guard ((parseToOption "c: '10'\n").bind (·.get? "c")).map (·.asQuotedNat.toOption) == some (some 10)
#guard ((parseToOption "c: 10\n").bind (·.get? "c")).map (·.asQuotedNat.toOption) == some none
#guard ((parseToOption "c: '0x0aFf'\n").bind (·.get? "c")).map (·.asHex.toOption) == some (some [10, 255])
#guard ((parseToOption "c: '0xa'\n").bind (·.get? "c")).map (·.asHex.toOption) == some none

end JauneConsensus.Harness.Yaml
