import JauneConsensus.SSZ.Basic
import JauneConsensus.Harness.Snappy
import JauneConsensus.Harness.Yaml

/-!
# `ssz_generic` case checks (harness only)

`tests/formats/ssz_generic/README.md` (`consensus-specs` `v1.6.1`): each case names its SSZ type
in its directory name. A `valid` case must decode from `serialized`, equal `value`, re-encode
to `serialized`, and have hash-tree-root `meta.yaml: root`. An `invalid` case must fail to
decode (an illegal type counts as failing).

The checks run the library's own `Ssz` instances; nothing here re-implements SSZ. Reading YAML
values into SSZ values follows the canonical JSON mapping (`ssz/simple-serialize.md`, "JSON
mapping"): integers as decimal strings, booleans as `true`/`false`, bitfields and byte
sequences as `0x`-prefixed SSZ bytes, vectors and lists as sequences.
-/

namespace JauneConsensus.Harness
open Jaune

/-- Reading a YAML node as an SSZ value. -/
class FromYaml (α : Type) where
  fromYaml : Yaml → Except YamlError α

export FromYaml (fromYaml)

/-- A decimal natural number. -/
def parseDecimal (s : String) : Except YamlError Nat :=
  if s.isEmpty ∨ !s.all Char.isDigit then throw (.shape "decimal integer")
  else pure (s.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0)

/-- `0x`-prefixed hex bytes. -/
def parseHex (s : String) : Except YamlError Bytes :=
  if s.startsWith "0x" then
    match Hex.toBytes (s.drop 2).toString with
    | some bs => pure bs
    | none => throw (.shape "hex bytes")
  else throw (.shape "0x-prefixed hex")

instance : FromYaml Bool where
  fromYaml
    | .scalar "true" false => pure true
    | .scalar "false" false => pure false
    | _ => throw (.shape "boolean")

instance : FromYaml U64 where
  fromYaml y := do
    let n ← parseDecimal (← y.text?)
    if h : n < 2 ^ 64 then pure (U64.ofNatLt n h) else throw (.shape "uint64 in range")

instance {n : Nat} : FromYaml (UIntN n) where
  fromYaml y := do
    let v ← parseDecimal (← y.text?)
    if h : v < 2 ^ (8 * n) then pure ⟨v, h⟩ else throw (.shape "uintN in range")

instance {α : Type} {n : Nat} [FromYaml α] : FromYaml (SszVector α n) where
  fromYaml y := do
    let xs ← (← y.items?).mapM fromYaml
    if h : xs.size = n then pure ⟨xs, h⟩ else throw (.shape "vector of the declared length")

instance {α : Type} {n : Nat} [FromYaml α] : FromYaml (SszList α n) where
  fromYaml y := do
    let xs ← (← y.items?).mapM fromYaml
    if h : xs.size ≤ n then pure ⟨xs, h⟩ else throw (.shape "list within its limit")

/-- Bitfields are given as their SSZ bytes. -/
def fromSszHex {α : Type} [Ssz α] (y : Yaml) : Except YamlError α := do
  let bs ← parseHex (← y.text?)
  match (deserialize bs : M α) with
  | .ok v => pure v
  | .error _ => throw (.shape "decodable SSZ bytes")

instance {n : Nat} : FromYaml (Bitvector n) := ⟨fromSszHex⟩
instance {n : Nat} : FromYaml (Bitlist n) := ⟨fromSszHex⟩

/-- Why a case failed. -/
inductive CaseFail where
  | snappy (e : SnappyError)
  | yaml (e : YamlError)
  | decode (r : Reject)
  | valueMismatch
  | reserialize
  | rootMismatch
  | acceptedInvalid
  | unknownType (name : String)
  | io (msg : String)
  deriving Repr

/-- The two checks of one SSZ type. -/
structure TypeChecks where
  valid : Bytes → Yaml → B256 → Except CaseFail Unit
  invalid : Bytes → Except CaseFail Unit

/-- The checks for a type with SSZ, YAML and equality instances. -/
def TypeChecks.of (α : Type) [Ssz α] [FromYaml α] [DecidableEq α] : TypeChecks where
  valid ser value root := do
    let v ← match (deserialize ser : M α) with
      | .ok v => pure v
      | .error r => throw (.decode r)
    let y ← match (fromYaml value : Except YamlError α) with
      | .ok y => pure y
      | .error e => throw (.yaml e)
    if v ≠ y then throw .valueMismatch
    if serialize y ≠ ser then throw .reserialize
    if hashTreeRoot v ≠ root then throw .rootMismatch
  invalid ser :=
    match (deserialize ser : M α) with
    | .ok _ => throw .acceptedInvalid
    | .error _ => pure ()

/-- A basic element type by its `ssz_generic` name, passed to a continuation. -/
def withBasic (name : String)
    (k : (α : Type) → [Ssz α] → [FromYaml α] → [DecidableEq α] → TypeChecks) :
    Option TypeChecks :=
  match name with
  | "bool" => some (k Bool)
  | "uint8" => some (k (UIntN 1))
  | "uint16" => some (k (UIntN 2))
  | "uint32" => some (k (UIntN 4))
  | "uint64" => some (k U64)
  | "uint128" => some (k (UIntN 16))
  | "uint256" => some (k (UIntN 32))
  | _ => none

/-- The `uintN` type for `uint_{N}`. -/
def uintChecks (bits : String) : Option TypeChecks :=
  match bits with
  | "8" => some (.of (UIntN 1))
  | "16" => some (.of (UIntN 2))
  | "32" => some (.of (UIntN 4))
  | "64" => some (.of U64)
  | "128" => some (.of (UIntN 16))
  | "256" => some (.of (UIntN 32))
  | _ => none

/-- The type of a case, from its handler and directory name
(`tests/formats/ssz_generic/README.md`, "Type declarations"). -/
def typeOfCase (handler caseName : String) : Option TypeChecks :=
  let parts := (caseName.splitOn "_")
  match handler, parts with
  | "boolean", _ => some (.of Bool)
  | "uints", "uint" :: bits :: _ => uintChecks bits
  | "bitvector", "bitvec" :: n :: _ => n.toNat?.map fun n => .of (Bitvector n)
  | "bitlist", "bitlist" :: n :: _ => n.toNat?.map fun n => .of (Bitlist n)
  | "basic_vector", "vec" :: elem :: n :: _ =>
    n.toNat?.bind fun n => withBasic elem fun α => .of (SszVector α n)
  | _, _ => none

end JauneConsensus.Harness
