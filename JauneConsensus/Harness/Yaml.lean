/-!
# A YAML subset reader (harness only)

Reads the YAML the consensus vectors use: block mappings and block sequences (indentation
structured, including the compact `- key: value` form), flow sequences and flow mappings that may
span lines, plain scalars, single-quoted and double-quoted scalars, `---` and `...` document
markers and `#` comments. Anything else fails closed with a `YamlError`; nothing is guessed.

Harness code, outside the semantics. Pure and total: every recursive function carries fuel
bounded by the input length. Temporary home: the harness worker's branch
(`claude/consensus-harness`) owns the shared reader; this copy is to be merged into it.
-/

namespace JauneConsensus.Harness

/-- A YAML node. Scalars keep their text and whether they were quoted, so `'1'` and `1` both
read as numbers but a reader can still tell `true` from `'true'`. -/
inductive Yaml where
  | scalar (text : String) (quoted : Bool)
  | seq (items : Array Yaml)
  | map (entries : Array (String × Yaml))
  deriving Repr, Inhabited

/-- Why the YAML reader or a value conversion failed. -/
inductive YamlError where
  | syntax (pos : Nat) (what : String)
  | fuel
  | shape (expected : String)
  | missingKey (key : String)
  deriving Repr

namespace Yaml

/-- Parser state: the input as an array of characters and a position. -/
abbrev P := ReaderT (Array Char) (StateT Nat (Except YamlError))

def peekAt (k : Nat) : P (Option Char) := do
  let s ← read
  let i ← get
  pure s[i + k]?

def peek : P (Option Char) := peekAt 0

def advance (k : Nat := 1) : P Unit := modify (· + k)

def fail {α : Type} (what : String) : P α := do
  throw (.syntax (← get) what)

/-- Drop trailing spaces and tabs. -/
def rtrim (s : String) : String := String.ofList (s.toList.reverse.dropWhile (fun c => c = ' ' ∨ c = '\t')).reverse

def isSpace (c : Char) : Bool := c = ' ' ∨ c = '\t'

/-- Skip spaces and tabs on the current line. -/
def skipSpaces : Nat → P Unit
  | 0 => pure ()
  | fuel + 1 => do
    match ← peek with
    | some c => if isSpace c then advance; skipSpaces fuel else pure ()
    | none => pure ()

/-- Skip to the end of the current line (not past the newline). -/
def skipToEol : Nat → P Unit
  | 0 => pure ()
  | fuel + 1 => do
    match ← peek with
    | some '\n' => pure ()
    | some _ => advance; skipToEol fuel
    | none => pure ()

/-- After a value on a line: only spaces and an optional comment may follow. -/
def endOfLine (fuel : Nat) : P Unit := do
  skipSpaces fuel
  match ← peek with
  | none => pure ()
  | some '\n' => pure ()
  | some '#' => skipToEol fuel
  | some _ => fail "unexpected text after a value"

/-- Count leading spaces at a line start without consuming them. -/
def indentHere : Nat → Nat → P Nat
  | 0, n => pure n
  | fuel + 1, n => do
    match ← peekAt n with
    | some ' ' => indentHere fuel (n + 1)
    | _ => pure n

/-- From a position at or before a newline, move to the first non-space character of the next
content line, skipping blank lines, comment lines and `---`. Returns its column, or `none` at
the end of input or a `...` document end. -/
def nextContent : Nat → P (Option Nat)
  | 0 => throw .fuel
  | fuel + 1 => do
    skipToEol fuel
    match ← peek with
    | none => pure none
    | some _ =>
      advance
      let n ← indentHere fuel 0
      advance n
      match ← peek with
      | none => pure none
      | some '\n' => nextContent fuel
      | some '#' => nextContent fuel
      | some '.' =>
        if (← peekAt 1) = some '.' ∧ (← peekAt 2) = some '.' then pure none
        else pure (some n)
      | some '-' =>
        if (← peekAt 1) = some '-' ∧ (← peekAt 2) = some '-' then nextContent fuel
        else pure (some n)
      | some _ => pure (some n)

/-- A single-quoted scalar (`''` is a quote). The opening quote is at the position. -/
def singleQuoted : Nat → String → P String
  | 0, _ => throw .fuel
  | fuel + 1, acc => do
    match ← peek with
    | none => fail "unterminated single-quoted scalar"
    | some '\'' =>
      if (← peekAt 1) = some '\'' then advance 2; singleQuoted fuel (acc.push '\'')
      else advance; pure acc
    | some '\n' => advance; singleQuoted fuel (acc.push ' ')
    | some c => advance; singleQuoted fuel (acc.push c)

/-- A double-quoted scalar with the escapes `\\`, `\"`, `\n`, `\t`. -/
def doubleQuoted : Nat → String → P String
  | 0, _ => throw .fuel
  | fuel + 1, acc => do
    match ← peek with
    | none => fail "unterminated double-quoted scalar"
    | some '"' => advance; pure acc
    | some '\\' =>
      match ← peekAt 1 with
      | some '\\' => advance 2; doubleQuoted fuel (acc.push '\\')
      | some '"' => advance 2; doubleQuoted fuel (acc.push '"')
      | some 'n' => advance 2; doubleQuoted fuel (acc.push '\n')
      | some 't' => advance 2; doubleQuoted fuel (acc.push '\t')
      | _ => fail "unsupported escape"
    | some c => advance; doubleQuoted fuel (acc.push c)

/-- A plain scalar, ending at a newline, at ` #`, at `: ` (when `stopColon`), and in flow
context at `,`, `]`, `}`. Trailing spaces are trimmed. -/
def plain (flow stopColon : Bool) : Nat → String → P String
  | 0, _ => throw .fuel
  | fuel + 1, acc => do
    match ← peek with
    | none => pure (rtrim acc)
    | some c =>
      if c = '\n' then pure (rtrim acc)
      else if flow ∧ (c = ',' ∨ c = ']' ∨ c = '}') then pure (rtrim acc)
      else if c = '#' ∧ (acc.isEmpty ∨ acc.back = ' ') then pure (rtrim acc)
      else if stopColon ∧ c = ':' then
        match ← peekAt 1 with
        | some d => if isSpace d ∨ d = '\n' ∨ (flow ∧ (d = ',' ∨ d = '}' ∨ d = ']')) then pure (rtrim acc)
                    else advance; plain flow stopColon fuel (acc.push c)
        | none => pure (rtrim acc)
      else advance; plain flow stopColon fuel (acc.push c)

/-- Skip whitespace including newlines and comments (flow context). -/
def skipWs : Nat → P Unit
  | 0 => pure ()
  | fuel + 1 => do
    match ← peek with
    | some ' ' | some '\t' | some '\n' | some '\r' => advance; skipWs fuel
    | some '#' => skipToEol fuel; skipWs fuel
    | _ => pure ()

/-- A scalar key or value at the position (quoted or plain). -/
def scalarNode (flow stopColon : Bool) (fuel : Nat) : P Yaml := do
  match ← peek with
  | some '\'' => advance; pure (.scalar (← singleQuoted fuel "") true)
  | some '"' => advance; pure (.scalar (← doubleQuoted fuel "") true)
  | _ => pure (.scalar (← plain flow stopColon fuel "") false)

/-- A key: a scalar followed by `:`. -/
def keyText (flow : Bool) (fuel : Nat) : P String := do
  match ← scalarNode flow true fuel with
  | .scalar t _ => pure t
  | _ => fail "key"

mutual
/-- A flow node: `[...]`, `{...}` or a scalar. -/
def flowNode : Nat → P Yaml
  | 0 => throw .fuel
  | fuel + 1 => do
    skipWs fuel
    match ← peek with
    | some '[' => advance; flowSeq fuel #[]
    | some '{' => advance; flowMap fuel #[]
    | _ => scalarNode true false fuel

def flowSeq : Nat → Array Yaml → P Yaml
  | 0, _ => throw .fuel
  | fuel + 1, acc => do
    skipWs fuel
    match ← peek with
    | some ']' => advance; pure (.seq acc)
    | _ =>
      let item ← flowNode fuel
      skipWs fuel
      match ← peek with
      | some ',' => advance; flowSeq fuel (acc.push item)
      | some ']' => advance; pure (.seq (acc.push item))
      | _ => fail "expected ',' or ']'"

def flowMap : Nat → Array (String × Yaml) → P Yaml
  | 0, _ => throw .fuel
  | fuel + 1, acc => do
    skipWs fuel
    match ← peek with
    | some '}' => advance; pure (.map acc)
    | _ =>
      let k ← keyText true fuel
      skipWs fuel
      if (← peek) ≠ some ':' then fail "expected ':' in a flow mapping"
      advance
      let v ← flowNode fuel
      skipWs fuel
      match ← peek with
      | some ',' => advance; flowMap fuel (acc.push (k, v))
      | some '}' => advance; pure (.map (acc.push (k, v)))
      | _ => fail "expected ',' or '}'"
end

/-- An inline value on the rest of a line: a flow collection or a scalar. -/
def inlineValue (fuel : Nat) : P Yaml := do
  match ← peek with
  | some '[' | some '{' => flowNode fuel
  | _ => scalarNode false false fuel

/-- Does the text at the position look like `key:` (a mapping entry)? Checked on a copy of
the state, so it consumes nothing. -/
def looksLikeKey (fuel : Nat) : P Bool := do
  if (← peek) = some '[' ∨ (← peek) = some '{' then return false
  let saved ← get
  let r ← (tryCatch (do let _ ← keyText false fuel; pure ((← peek) == some ':')) (fun _ => pure false))
  set saved
  pure r

/-- Is the position at a block sequence entry `- ` (or `-` at end of line)? -/
def atDash : P Bool := do
  if (← peek) = some '-' then
    match ← peekAt 1 with
    | some c => pure (isSpace c ∨ c = '\n')
    | none => pure true
  else pure false

/-- Distance from `i` back to the previous newline. -/
def colBack (s : Array Char) (i : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => if i < n + 1 then n else if s[i - n - 1]? = some '\n' then n else colBack s i k (n + 1)

/-- The column of the current position. -/
def currentColumn : P Nat := do
  let i ← get
  pure (colBack (← read) i i 0)

mutual
/-- A block node at the current position, whose line has column `col`. Returns the node and
the column of the next content line (the position is at its first character). -/
def blockNode : Nat → Nat → P (Yaml × Option Nat)
  | 0, _ => throw .fuel
  | fuel + 1, col => do
    if ← atDash then blockSeq fuel col #[]
    else if ← looksLikeKey fuel then blockMap fuel col #[]
    else
      let v ← inlineValue fuel
      endOfLine fuel
      pure (v, ← nextContent fuel)

/-- Entries `- item` at column `col`. -/
def blockSeq : Nat → Nat → Array Yaml → P (Yaml × Option Nat)
  | 0, _, _ => throw .fuel
  | fuel + 1, col, acc => do
    advance  -- the dash
    skipSpaces fuel
    let (item, next) ← do
      match ← peek with
      | none | some '\n' | some '#' =>
        match ← nextContent fuel with
        | some c => if c > col then blockNode fuel c else pure (.scalar "" false, some c)
        | none => pure (.scalar "" false, none)
      | some _ =>
        blockNode fuel (← currentColumn)
    match next with
    | some c =>
      if c = col ∧ (← atDash) then blockSeq fuel col (acc.push item)
      else if c ≤ col then pure (.seq (acc.push item), next)
      else fail "bad indentation in a block sequence"
    | none => pure (.seq (acc.push item), none)

/-- Entries `key: value` at column `col`. -/
def blockMap : Nat → Nat → Array (String × Yaml) → P (Yaml × Option Nat)
  | 0, _, _ => throw .fuel
  | fuel + 1, col, acc => do
    let k ← keyText false fuel
    if (← peek) ≠ some ':' then fail "expected ':'"
    advance
    skipSpaces fuel
    let (v, next) ← do
      match ← peek with
      | none | some '\n' | some '#' =>
        match ← nextContent fuel with
        | some c =>
          if c > col then blockNode fuel c
          else if c = col ∧ (← atDash) then blockSeq fuel c #[]
          else pure (.scalar "" false, some c)
        | none => pure (.scalar "" false, none)
      | some _ =>
        let v ← inlineValue fuel
        endOfLine fuel
        pure (v, ← nextContent fuel)
    match next with
    | some c =>
      if c = col then blockMap fuel col (acc.push (k, v))
      else if c < col then pure (.map (acc.push (k, v)), next)
      else fail "bad indentation in a block mapping"
    | none => pure (.map (acc.push (k, v)), none)
end

/-- Parse a whole document. -/
def parse (text : String) : Except YamlError Yaml :=
  let chars := ('\n' :: text.toList).toArray
  let fuel := 4 * chars.size + 16
  let prog : P Yaml := do
    match ← nextContent fuel with
    | none => pure (.scalar "" false)
    | some c =>
      let (v, next) ← blockNode fuel c
      match next with
      | none => pure v
      | some _ => fail "content after the document's top-level node"
  (prog.run chars).run' 0

/-! ## Accessors -/

def text? : Yaml → Except YamlError String
  | .scalar t _ => pure t
  | _ => throw (.shape "scalar")

def items? : Yaml → Except YamlError (Array Yaml)
  | .seq xs => pure xs
  | _ => throw (.shape "sequence")

def field? (y : Yaml) (key : String) : Except YamlError Yaml :=
  match y with
  | .map es =>
    match es.find? (·.1 = key) with
    | some (_, v) => pure v
    | none => throw (.missingKey key)
  | _ => throw (.shape "mapping")

end Yaml

end JauneConsensus.Harness
