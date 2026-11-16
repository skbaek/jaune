import JauneConsensus.SSZ.Progressive
import JauneConsensus.Harness.SszGeneric

/-!
# The `ssz_generic` test containers (harness only)

The structures of `tests/formats/ssz_generic/README.md` ("containers"), declared with the
library's `ssz_container`, and their YAML readers. `byte` is `UInt8`; `ByteList[N]` is
`SszList UInt8 N`.
-/

namespace JauneConsensus.Harness
open Jaune Yaml

ssz_container SingleFieldTestStruct where
  A : UInt8

ssz_container SmallTestStruct where
  A : U16
  B : U16

ssz_container FixedTestStruct where
  A : U8
  B : U64
  C : U32

ssz_container VarTestStruct where
  A : U16
  B : (SszList U16 1024)
  C : U8

ssz_container ComplexTestStruct where
  A : U16
  B : (SszList U16 128)
  C : U8
  D : (SszList UInt8 256)
  E : VarTestStruct
  F : (SszVector FixedTestStruct 4)
  G : (SszVector VarTestStruct 2)

ssz_container BitsStruct where
  A : (Bitlist 5)
  B : (Bitvector 2)
  C : (Bitvector 1)
  D : (Bitlist 6)
  E : (Bitvector 8)

yaml_container SingleFieldTestStruct [A]
yaml_container SmallTestStruct [A, B]
yaml_container FixedTestStruct [A, B, C]
yaml_container VarTestStruct [A, B, C]
yaml_container ComplexTestStruct [A, B, C, D, E, F, G]
yaml_container BitsStruct [A, B, C, D, E]

ssz_container ProgressiveTestStruct where
  A : (ProgressiveList UInt8)
  B : (ProgressiveList U64)
  C : (ProgressiveList SmallTestStruct)
  D : (ProgressiveList (ProgressiveList VarTestStruct))

ssz_container ProgressiveBitsStruct where
  A : (Bitvector 256)
  B : (Bitlist 256)
  C : ProgressiveBitlist
  D : (Bitvector 257)
  E : (Bitlist 257)
  F : ProgressiveBitlist
  G : (Bitvector 1280)
  H : (Bitlist 1280)
  I : ProgressiveBitlist
  J : (Bitvector 1281)
  K : (Bitlist 1281)
  L : ProgressiveBitlist

ssz_progressive_container ProgressiveSingleFieldContainerTestStruct [1] where
  A : UInt8

ssz_progressive_container ProgressiveSingleListContainerTestStruct [0, 0, 0, 0, 1] where
  C : ProgressiveBitlist

ssz_progressive_container ProgressiveVarTestStruct [1, 0, 1, 0, 1] where
  A : UInt8
  B : (SszList U16 123)
  C : ProgressiveBitlist

ssz_progressive_container ProgressiveComplexTestStruct
    [1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1] where
  A : UInt8
  B : (SszList U16 123)
  C : ProgressiveBitlist
  D : (ProgressiveList U64)
  E : (ProgressiveList SmallTestStruct)
  F : (ProgressiveList (ProgressiveList VarTestStruct))
  G : (SszList ProgressiveSingleFieldContainerTestStruct 10)
  H : (ProgressiveList ProgressiveVarTestStruct)

yaml_container ProgressiveTestStruct [A, B, C, D]
yaml_container ProgressiveBitsStruct [A, B, C, D, E, F, G, H, I, J, K, L]
yaml_container ProgressiveSingleFieldContainerTestStruct [A]
yaml_container ProgressiveSingleListContainerTestStruct [C]
yaml_container ProgressiveVarTestStruct [A, B, C]
yaml_container ProgressiveComplexTestStruct [A, B, C, D, E, F, G, H]

/-- `CompatibleUnionA = CompatibleUnion({1: ProgressiveSingleFieldContainerTestStruct})`. -/
inductive CompatibleUnionA where
  | s1 (v : ProgressiveSingleFieldContainerTestStruct)
  deriving DecidableEq, BEq

/-- `CompatibleUnionBC = CompatibleUnion({2: ProgressiveSingleListContainerTestStruct,
3: ProgressiveVarTestStruct})`. -/
inductive CompatibleUnionBC where
  | s2 (v : ProgressiveSingleListContainerTestStruct)
  | s3 (v : ProgressiveVarTestStruct)
  deriving DecidableEq, BEq

/-- `CompatibleUnionABCA = CompatibleUnion({1: ProgressiveSingleFieldContainerTestStruct,
2: ProgressiveSingleListContainerTestStruct, 3: ProgressiveVarTestStruct,
4: ProgressiveSingleFieldContainerTestStruct})`. -/
inductive CompatibleUnionABCA where
  | s1 (v : ProgressiveSingleFieldContainerTestStruct)
  | s2 (v : ProgressiveSingleListContainerTestStruct)
  | s3 (v : ProgressiveVarTestStruct)
  | s4 (v : ProgressiveSingleFieldContainerTestStruct)
  deriving DecidableEq, BEq

/-- Decode the data of a union option. -/
def unionOption {α β : Type} [Ssz α] (wrap : α → β) (data : Bytes) : Option (M β) :=
  some (wrap <$> (deserialize data : M α))

instance : Ssz CompatibleUnionA where
  fixedSize? := none
  serialize | .s1 v => serializeUnion 1 (serialize v)
  deserialize bs := deserializeUnion bs fun sel data =>
    if sel = 1 then unionOption .s1 data else none
  hashTreeRoot | .s1 v => mixInSelector (hashTreeRoot v) 1

instance : Ssz CompatibleUnionBC where
  fixedSize? := none
  serialize
    | .s2 v => serializeUnion 2 (serialize v)
    | .s3 v => serializeUnion 3 (serialize v)
  deserialize bs := deserializeUnion bs fun sel data =>
    if sel = 2 then unionOption .s2 data
    else if sel = 3 then unionOption .s3 data else none
  hashTreeRoot
    | .s2 v => mixInSelector (hashTreeRoot v) 2
    | .s3 v => mixInSelector (hashTreeRoot v) 3

instance : Ssz CompatibleUnionABCA where
  fixedSize? := none
  serialize
    | .s1 v => serializeUnion 1 (serialize v)
    | .s2 v => serializeUnion 2 (serialize v)
    | .s3 v => serializeUnion 3 (serialize v)
    | .s4 v => serializeUnion 4 (serialize v)
  deserialize bs := deserializeUnion bs fun sel data =>
    if sel = 1 then unionOption .s1 data
    else if sel = 2 then unionOption .s2 data
    else if sel = 3 then unionOption .s3 data
    else if sel = 4 then unionOption .s4 data else none
  hashTreeRoot
    | .s1 v => mixInSelector (hashTreeRoot v) 1
    | .s2 v => mixInSelector (hashTreeRoot v) 2
    | .s3 v => mixInSelector (hashTreeRoot v) 3
    | .s4 v => mixInSelector (hashTreeRoot v) 4

/-- The selector and data of a union value (`{selector: n, data: ...}`). -/
def unionParts (y : Yaml.YVal) : Yaml.Res (Nat × Yaml.YVal) := do
  let sel ← (← y.field "selector").asNat
  pure (sel, ← y.field "data")

instance : FromYaml CompatibleUnionA where
  fromYaml y := do
    match ← unionParts y with
    | (1, d) => .s1 <$> fromYaml d
    | _ => throw (.shape "CompatibleUnionA selector")

instance : FromYaml CompatibleUnionBC where
  fromYaml y := do
    match ← unionParts y with
    | (2, d) => .s2 <$> fromYaml d
    | (3, d) => .s3 <$> fromYaml d
    | _ => throw (.shape "CompatibleUnionBC selector")

instance : FromYaml CompatibleUnionABCA where
  fromYaml y := do
    match ← unionParts y with
    | (1, d) => .s1 <$> fromYaml d
    | (2, d) => .s2 <$> fromYaml d
    | (3, d) => .s3 <$> fromYaml d
    | (4, d) => .s4 <$> fromYaml d
    | _ => throw (.shape "CompatibleUnionABCA selector")


/-- The container type of a `containers` case, by structure name. -/
def containerChecks (name : String) : Option TypeChecks :=
  match name with
  | "SingleFieldTestStruct" => some (.of SingleFieldTestStruct)
  | "SmallTestStruct" => some (.of SmallTestStruct)
  | "FixedTestStruct" => some (.of FixedTestStruct)
  | "VarTestStruct" => some (.of VarTestStruct)
  | "ComplexTestStruct" => some (.of ComplexTestStruct)
  | "BitsStruct" => some (.of BitsStruct)
  | "ProgressiveTestStruct" => some (.of ProgressiveTestStruct)
  | "ProgressiveBitsStruct" => some (.of ProgressiveBitsStruct)
  | "ProgressiveSingleFieldContainerTestStruct" => some (.of ProgressiveSingleFieldContainerTestStruct)
  | "ProgressiveSingleListContainerTestStruct" => some (.of ProgressiveSingleListContainerTestStruct)
  | "ProgressiveVarTestStruct" => some (.of ProgressiveVarTestStruct)
  | "ProgressiveComplexTestStruct" => some (.of ProgressiveComplexTestStruct)
  | "CompatibleUnionA" => some (.of CompatibleUnionA)
  | "CompatibleUnionBC" => some (.of CompatibleUnionBC)
  | "CompatibleUnionABCA" => some (.of CompatibleUnionABCA)
  | _ => none

/-- The type of a case, from its handler and directory name, including containers. -/
def typeOfCaseAll (handler caseName : String) : Option TypeChecks :=
  match handler with
  | "containers" | "progressive_containers" | "compatible_unions" =>
    match caseName.splitOn "_" with
    | name :: _ => containerChecks name
    | [] => none
  | "basic_progressive_list" =>
    match caseName.splitOn "_" with
    | "proglist" :: elem :: _ => withBasic elem fun α => .of (ProgressiveList α)
    | _ => none
  | "progressive_bitlist" => some (.of ProgressiveBitlist)
  | _ => typeOfCase handler caseName

end JauneConsensus.Harness
