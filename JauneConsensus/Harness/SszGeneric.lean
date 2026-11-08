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
open Jaune Yaml

/-- Reading a YAML node as an SSZ value. -/
class FromYaml (α : Type) where
  fromYaml : YVal → Res α

export FromYaml (fromYaml)

/-- A decimal natural, plain or quoted (the vectors quote integers wider than 64 bits). -/
def natOf (y : YVal) : Res Nat :=
  match y with
  | .scalar _ true => y.asQuotedNat
  | _ => y.asNat

instance : FromYaml Bool := ⟨YVal.asBool⟩

instance : FromYaml U64 where
  fromYaml y := do
    let n ← natOf y
    if h : n < 2 ^ 64 then pure (U64.ofNatLt n h) else throw (.shape "uint64 out of range")

instance {n : Nat} : FromYaml (UIntN n) where
  fromYaml y := do
    let v ← natOf y
    if h : v < 2 ^ (8 * n) then pure ⟨v, h⟩ else throw (.shape "uintN out of range")

instance {α : Type} {n : Nat} [FromYaml α] : FromYaml (SszVector α n) where
  fromYaml y := do
    let xs := (← (← y.asSeq).mapM fromYaml).toArray
    if h : xs.size = n then pure ⟨xs, h⟩ else throw (.shape "vector of the wrong length")

instance {α : Type} {n : Nat} [FromYaml α] : FromYaml (SszList α n) where
  fromYaml y := do
    let xs := (← (← y.asSeq).mapM fromYaml).toArray
    if h : xs.size ≤ n then pure ⟨xs, h⟩ else throw (.shape "list beyond its limit")

instance : FromYaml UInt8 where
  fromYaml y := do
    let v ← natOf y
    if v < 256 then pure v.toUInt8 else throw (.shape "byte out of range")

/-- `List[byte, N]` / `ByteList[N]` are given as `0x`-prefixed bytes ("JSON mapping"). -/
instance (priority := high) {n : Nat} : FromYaml (SszList UInt8 n) where
  fromYaml y := do
    let bs := (← y.asHex).toArray
    if h : bs.size ≤ n then pure ⟨bs, h⟩ else throw (.shape "byte list beyond its limit")

/-- `ByteVector[N]` / `BytesN`, likewise. -/
instance (priority := high) {n : Nat} : FromYaml (SszVector UInt8 n) where
  fromYaml y := do
    let bs := (← y.asHex).toArray
    if h : bs.size = n then pure ⟨bs, h⟩ else throw (.shape "byte vector of the wrong length")

instance : FromYaml B256 where
  fromYaml y := do
    let bs ← y.asHex
    if bs.length = 32 then pure (Bytes.toB256 bs) else throw (.shape "expected 32 bytes")

instance : FromYaml Adr where
  fromYaml y := do
    match Bytes.toAdr? (← y.asHex) with
    | some a => pure a
    | none => throw (.shape "expected 20 bytes")

/-- Bitfields are given as their SSZ bytes. -/
def fromSszHex {α : Type} [Ssz α] (y : YVal) : Res α := do
  match (deserialize (← y.asHex) : M α) with
  | .ok v => pure v
  | .error _ => throw (.shape "undecodable SSZ bytes")

instance {n : Nat} : FromYaml (Bitvector n) := ⟨fromSszHex⟩
instance {n : Nat} : FromYaml (Bitlist n) := ⟨fromSszHex⟩

/-- Why a case failed. -/
inductive CaseFail where
  | snappy (e : Snappy.Error)
  | yaml (e : YamlError)
  | decode (r : Reject)
  | valueMismatch
  | reserialize
  | rootMismatch
  | acceptedInvalid
  | unknownType (name : String)
  | io (msg : String)

/-- A one-line rendering of a failure. -/
def CaseFail.render : CaseFail → String
  | .snappy e => s!"snappy: {e}"
  | .yaml e => toString e
  | .decode r => s!"decode rejected: {repr r}"
  | .valueMismatch => "decoded value differs from value.yaml"
  | .reserialize => "re-serialization differs from serialized"
  | .rootMismatch => "hash_tree_root differs from meta.yaml root"
  | .acceptedInvalid => "invalid encoding was accepted"
  | .unknownType n => s!"no SSZ type for case name {n}"
  | .io m => s!"io: {m}"

/-- The two checks of one SSZ type. -/
structure TypeChecks where
  valid : Bytes → YVal → B256 → Except CaseFail Unit
  invalid : Bytes → Except CaseFail Unit

/-- The checks for a type with SSZ, YAML and equality instances. Equality is `BEq` (derived
field by field for containers), which is what the comparison runs. -/
def TypeChecks.of (α : Type) [Ssz α] [FromYaml α] [BEq α] : TypeChecks where
  valid ser value root := do
    let v ← match (deserialize ser : M α) with
      | .ok v => pure v
      | .error r => throw (.decode r)
    let y ← match (fromYaml value : Res α) with
      | .ok y => pure y
      | .error e => throw (.yaml e)
    if !(v == y) then throw .valueMismatch
    if serialize y ≠ ser then throw .reserialize
    if hashTreeRoot v ≠ root then throw .rootMismatch
  invalid ser :=
    match (deserialize ser : M α) with
    | .ok _ => throw .acceptedInvalid
    | .error _ => pure ()

/-- A basic element type by its `ssz_generic` name, passed to a continuation. -/
def withBasic (name : String)
    (k : (α : Type) → [Ssz α] → [FromYaml α] → [BEq α] → TypeChecks) :
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
