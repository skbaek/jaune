import JauneConsensus.SSZ.Basic

/-!
# SSZ containers

`ssz/simple-serialize.md` (`consensus-specs` `v1.6.1`): a container is an ordered heterogeneous
collection of fields. It is serialized like a vector whose elements are its fields ("Vectors,
containers, ..."), deserialized by reading the fixed part (fixed-size fields in place, `uint32`
offsets for variable-size fields) and then cutting the variable parts ("Deserialization"), and
hashed as `merkleize([hash_tree_root(field) for field in value])` ("Merkleization").

`ssz_container Name where f₁ : T₁ ...` declares the structure, its field leaves
`Name.fieldRoots` and its `Ssz` instance from one field list, so every container is declared
once and mirrors its pyspec class field by field.
-/

namespace JauneConsensus
open Jaune

/-- The fixed size of a container: the sum of its fields' sizes, or `none` when a field is
variable-size. -/
def containerFixedSize (sizes : List (Option Nat)) : Option Nat :=
  sizes.foldr (fun s acc => do let a ← s; let b ← acc; pure (a + b)) (some 0)

/-- The fixed part's length: a field's size, or `BYTES_PER_LENGTH_OFFSET` for a variable one. -/
def fixedPartLength (sizes : List (Option Nat)) : Nat :=
  sizes.foldl (fun n s => n + match s with
    | some k => k
    | none => BYTES_PER_LENGTH_OFFSET) 0

/-- Read the fixed part of a container scope: for each field its fixed bytes or its offset. -/
def readFixedPart (bs : Scope) : List (Option Nat) → Nat → List (Sum Bytes Nat)
  | [], _ => []
  | some n :: rest, pos => .inl (slice bs pos (pos + n)) :: readFixedPart bs rest (pos + n)
  | none :: rest, pos =>
    .inr (readOffset bs pos) :: readFixedPart bs rest (pos + BYTES_PER_LENGTH_OFFSET)

/-- The offsets among the fixed-part items, in field order. -/
def offsetsOf : List (Sum Bytes Nat) → List Nat
  | [] => []
  | .inl _ :: rest => offsetsOf rest
  | .inr o :: rest => o :: offsetsOf rest

/-- Replace each offset by its cut variable part, in order. -/
def fillVariable : List (Sum Bytes Nat) → List Bytes → M (List Bytes)
  | [], [] => pure []
  | .inl b :: rest, vs => do pure (b :: (← fillVariable rest vs))
  | .inr _ :: rest, v :: vs => do pure (v :: (← fillVariable rest vs))
  | _, _ => throw (.decode (.offset "variable part count"))

/-- Split a container scope into its field scopes ("Deserialization"): the scope holds the
whole fixed part; the first offset equals the fixed part's length; offsets are non-decreasing
and within the scope; a container with no variable-size field has no extra bytes. -/
def splitContainer (bs : Bytes) (sizes : List (Option Nat)) : M (List Bytes) := do
  let scope := bs.length
  let fixedLen := fixedPartLength sizes
  if scope < fixedLen then throw (.decode (.length fixedLen scope))
  let arr : Scope := bs.toArray
  let items := readFixedPart arr sizes 0
  match offsetsOf items with
  | [] =>
    if scope ≠ fixedLen then throw (.decode (.length fixedLen scope))
    fillVariable items []
  | first :: rest =>
    if first ≠ fixedLen then throw (.decode (.offset "first offset does not match the fixed part"))
    let parts ← cutVariable arr scope (first :: rest)
    fillVariable items parts

/-- The decoder state over the remaining field scopes. -/
abbrev FieldDecoder := StateT (List Bytes) M

/-- Decode the next field from its scope. -/
def nextField {α : Type} [Ssz α] : FieldDecoder α := do
  match ← get with
  | [] => throw (.decode (.offset "missing field"))
  | b :: rest =>
    set rest
    StateT.lift (deserialize b : M α)

/-- The Merkle leaf of a field, or none for an absent fork-gated field. -/
@[inline] def fieldRoot? {α : Type} [Ssz α] (x : α) : Option B256 :=
  if Ssz.present α then some (hashTreeRoot x) else none

/-- `merkleize` of the present fields' roots (a container's `hash_tree_root`). -/
def containerRoot (roots : List (Option B256)) : B256 :=
  let rs := roots.filterMap id
  merkleizeDepth rs (depthOf rs.length)

/-- The serialization part of a field. -/
@[inline] def fieldPart {α : Type} [Ssz α] (x : α) : Part :=
  match Ssz.fixedSize? α with
  | some _ => .fixed (serialize x)
  | none => .var (serialize x)

/-- `ssz_container Name where f₁ : T₁ f₂ : T₂ ...` declares `structure Name` with those fields
and its `Ssz` instance. Containers with no fields are illegal ("Illegal types"), so the
syntax requires at least one. -/
syntax (name := sszContainer) (docComment)? "ssz_container " ident
  ("(" ident " : " term ")")* " where" (ppLine ident " : " term:max)+ : command

macro_rules
  | `($[$doc?:docComment]? ssz_container $n:ident $[($ps:ident : $pts:term)]* where
      $[$fs:ident : $ts:term]*) => do
    let projs := fs.map fun f => Lean.mkIdent (n.getId ++ f.getId)
    let mk := Lean.mkIdent (n.getId ++ `mk)
    let parts ← projs.mapM fun p => `(fieldPart ($p x))
    let roots ← projs.mapM fun p => `(fieldRoot? ($p x))
    let mut dec ← `($mk <$> nextField)
    for _ in [1:fs.size] do
      dec ← `($dec <*> nextField)
    let ps : Array Lean.Ident := ps.map fun p => ⟨p.raw⟩
    let psT : Array Lean.Term := ps.map fun p => ⟨p.raw⟩
    let ty ← `($n $psT*)
    let fieldRootsId := Lean.mkIdent (n.getId ++ `fieldRoots)
    `($[$doc?:docComment]? structure $n $[($ps : $pts)]* where
        $[$fs:ident : $ts]*
        deriving DecidableEq, BEq
      /-- The Merkle leaves of the fields, in order (`none` for an absent fork-gated field):
      the chunks `hash_tree_root` merkleizes and `compute_merkle_proof` builds proofs over. -/
      def $fieldRootsId $[{$ps : $pts}]* (x : $ty) : List (Option B256) := [$roots,*]
      instance $[($ps : $pts)]* : Ssz $ty where
        fixedSize? := containerFixedSize [$[Ssz.fixedSize? $ts],*]
        serialize := fun x => serializeParts [$parts,*]
        deserialize := fun bs => do
          let scopes ← splitContainer bs [$[Ssz.fixedSize? $ts],*]
          StateT.run' (do
            let v ← ($dec : FieldDecoder $ty)
            if (← get).isEmpty then pure v
            else throw (.decode (.offset "extra fields"))) scopes
        hashTreeRoot := fun x => containerRoot ($fieldRootsId x))

end JauneConsensus
