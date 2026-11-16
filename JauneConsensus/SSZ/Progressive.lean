import JauneConsensus.SSZ.Container

/-!
# SSZ progressive types and compatible unions

`ssz/simple-serialize.md` (`consensus-specs` `v1.6.1`): `ProgressiveList[T]` (EIP-7916),
`ProgressiveBitlist` (EIP-7916), `ProgressiveContainer(active_fields)` (EIP-7495) and
`CompatibleUnion({selector: type})` (EIP-8016). Electra and Fulu use none of them; the
`ssz_generic` suite exercises them, and they are implemented so that no case is excluded. Gloas
(`v1.7.0-beta.4`, EIP-7688) uses the first three for its containers
(`JauneConsensus/ContainersGloas.lean`), with `active_fields(width=N)` only, and adds
`ProgressiveList[Byte]` (`ProgressiveByteList`); its `ssz_static` roots are the check that these
are the same rules.

Serialization is that of the non-progressive counterpart (a list without limit, a bitlist
without limit, a container); only Merkleization differs, through `merkleize_progressive`,
`mix_in_active_fields` and `mix_in_selector`.

**Two revisions of `merkleize_progressive`.** At `v1.6.1` each node hashes the rest of the spine
on the left and this level's subtree on the right:
`hash(merkleize_progressive(chunks[num_leaves:], num_leaves * 4), merkleize(chunks[:num_leaves],
num_leaves))`. Gloas (`v1.7.0-beta.4`, EIP-7688) imports the progressive types from the
`eth-ssz-specs==0.1.0` package (`pysetup/spec_builders/gloas.py`), whose `ssz/trees.py` hashes
the other way round, `sha256(subtree_root + successor_root)`: a right-leaning spine where a chunk
keeps its generalized index as the list grows. The two disagree on every non-empty input. The
`v1.6.1` `ssz_generic` vectors (the general preset stays on `v1.6.1`) fix the first, the
`v1.7.0-beta.4` Gloas `ssz_static` roots the second, so both are kept, selected by `Spine`, and
every progressive type is indexed by it: `ProgressiveList`, `ProgressiveBitlist` and
`ssz_progressive_container` default to `v1.6.1`'s `.successorLeft`; the Gloas containers use
`.successorRight` (`ProgressiveListR`, `ProgressiveBitlistR`, `ProgressiveByteList`). Everything
else (the per-level `merkleize`, `mix_in_length`, the `active_fields` word) agrees.
-/

namespace JauneConsensus
open Jaune

/-- Which child of a spine node the rest of the spine is (see the module doc). -/
inductive Spine where
  /-- `ssz/simple-serialize.md` at `v1.6.1`: `hash(successor, subtree)`. -/
  | successorLeft
  /-- `eth-ssz-specs==0.1.0` `ssz/trees.py` (Gloas at `v1.7.0-beta.4`): `hash(subtree, successor)`. -/
  | successorRight
  deriving DecidableEq, Repr

/-- One spine node: the rest of the spine and this level's subtree, in the spine's order. -/
@[inline] def Spine.node : Spine → B256 → B256 → B256
  | .successorLeft, successor, subtree => hashPair successor subtree
  | .successorRight, successor, subtree => hashPair subtree successor

/-- `merkleize_progressive(chunks, num_leaves)` ("Merkleization"): the empty input is the zero
chunk; otherwise the spine node of `merkleize_progressive(chunks[num_leaves:], num_leaves * 4)`
and `merkleize(chunks[:num_leaves], num_leaves)`. Total by fuel (`chunks.length + 1` suffices,
since every non-empty step consumes at least one chunk). -/
def merkleizeProgressiveAux (s : Spine) : Nat → List B256 → Nat → B256
  | 0, _, _ => zeroChunk
  | _ + 1, [], _ => zeroChunk
  | fuel + 1, cs, numLeaves =>
    s.node (merkleizeProgressiveAux s fuel (cs.drop numLeaves) (numLeaves * 4))
      (merkleizeDepth (cs.take numLeaves) (depthOf numLeaves))

/-- `merkleize_progressive(chunks)` with the default `num_leaves=1`. -/
def merkleizeProgressive (chunks : List B256) (s : Spine := .successorLeft) : B256 :=
  merkleizeProgressiveAux s (chunks.length + 1) chunks 1

/-- `mix_in_active_fields(root, active_fields)`: `hash(root, pack_bits(active_fields))`, with
`active_fields` restricted to at most 256 bits ("Merkleization": `active_fields` is restricted
to ≤ 256 bits), so `pack_bits` is one chunk. The bound is a proof obligation, so an overlong
`active_fields` is rejected at elaboration. -/
def mixInActiveFields (root : B256) (activeFields : List Bool)
    (_ : activeFields.length ≤ 256) : B256 :=
  hashPair root (chunkOf (bitsToBytes activeFields))

/-! ## `ProgressiveList[T]` -/

/-- `ProgressiveList[T]`: an ordered homogeneous collection without limit, Merkleized along
spine `s`. -/
structure ProgressiveListS (s : Spine) (α : Type) where
  toArray : Array α
  deriving DecidableEq, BEq

/-- `ProgressiveList[T]` at `v1.6.1` (`ssz_generic`). -/
abbrev ProgressiveList (α : Type) := ProgressiveListS .successorLeft α
/-- `ProgressiveList[T]` of `eth-ssz-specs==0.1.0` (Gloas). -/
abbrev ProgressiveListR (α : Type) := ProgressiveListS .successorRight α

/-- `ProgressiveList[T]` ("Merkleization": `mix_in_length(merkleize_progressive(pack(value)),
len(value))` for basic `T`, with element roots otherwise). Decoding is that of a list with no
limit. -/
instance {s : Spine} {α : Type} [Ssz α] : Ssz (ProgressiveListS s α) where
  fixedSize? := none
  serialize v := serializeParts (seqParts v.toArray.toList)
  deserialize bs := do
    -- Every element occupies at least one byte or one offset, so the scope length bounds the
    -- count; no further limit applies.
    let xs ← deserializeSeq (α := α) bs none bs.length
    pure ⟨xs⟩
  hashTreeRoot v :=
    let xs := v.toArray.toList
    let chunks := if Ssz.isBasic α then pack (xs.flatMap serialize) else xs.map hashTreeRoot
    mixInLength (merkleizeProgressive chunks s) v.toArray.size

/-- `ProgressiveList[Byte]` (Gloas `Transaction` and `BlockAccessList`): the SSZ of
`ProgressiveList UInt8`, kept a distinct type because the vectors' JSON mapping gives a list of
`byte` as `0x`-prefixed bytes and a list of `uint8` as a sequence of integers. -/
structure ProgressiveByteList where
  bytes : ProgressiveListR UInt8
  deriving DecidableEq, BEq

instance : Ssz ProgressiveByteList where
  fixedSize? := none
  serialize v := serialize v.bytes
  deserialize bs := do pure ⟨← deserialize bs⟩
  hashTreeRoot v := hashTreeRoot v.bytes

/-! ## `ProgressiveBitlist` -/

/-- `ProgressiveBitlist`: an ordered collection of booleans without limit, Merkleized along
spine `s`. -/
structure ProgressiveBitlistS (s : Spine) where
  bits : Array Bool
  deriving DecidableEq, BEq

/-- `ProgressiveBitlist` at `v1.6.1` (`ssz_generic`). -/
abbrev ProgressiveBitlist := ProgressiveBitlistS .successorLeft
/-- `ProgressiveBitList` of `eth-ssz-specs==0.1.0` (Gloas `AggregationBits`, `CellsBitList`). -/
abbrev ProgressiveBitlistR := ProgressiveBitlistS .successorRight

/-- `ProgressiveBitlist` ("Serialization" as `Bitlist[N]`; "Merkleization":
`mix_in_length(merkleize_progressive(pack_bits(value)), len(value))`). -/
instance {s : Spine} : Ssz (ProgressiveBitlistS s) where
  fixedSize? := none
  serialize v := bitsToBytes (v.bits.toList ++ [true])
  deserialize bs :=
    match bs.getLast? with
    | none => throw (.decode .delimiter)
    | some last =>
      if last = 0 then throw (.decode .delimiter)
      else
        let len := 8 * (bs.length - 1) + (byteBitLength last - 1)
        pure ⟨((bytesToBits bs).take len).toArray⟩
  hashTreeRoot v :=
    mixInLength (merkleizeProgressive (pack (bitsToBytes v.bits.toList)) s) v.bits.size

/-! ## `ProgressiveContainer(active_fields)` -/

/-- The chunks of a progressive container: field roots at the positions of the `1` entries of
`active_fields`, zero chunks at the `0` entries. -/
def activeChunks : List Bool → List B256 → List B256
  | [], _ => []
  | true :: as, r :: rs => r :: activeChunks as rs
  | true :: as, [] => zeroChunk :: activeChunks as []
  | false :: as, rs => zeroChunk :: activeChunks as rs

/-- `hash_tree_root` of a progressive container ("Merkleization":
`mix_in_active_fields(merkleize_progressive(...), get_active_fields(value))`). The `≤ 256`-bit
bound travels as a proof obligation, so an overlong `active_fields` is rejected at elaboration. -/
def progressiveContainerRoot (activeFields : List Bool) (roots : List B256)
    (h : activeFields.length ≤ 256) (s : Spine := .successorLeft) : B256 :=
  mixInActiveFields (merkleizeProgressive (activeChunks activeFields roots) s) activeFields h

/-- `ssz_progressive_container Name (P : Preset) ... [a₀, a₁, ...] where f₁ : T₁ ...`: a
progressive container with the given `active_fields` (each `0` or `1`), optionally indexed by
parameters as `ssz_container` is. The illegal configurations ("Illegal types": no fields, more
than 256 entries, a trailing `0`, a count of `1`s different from the field count) are refused
when the declaration is expanded. `Name.fieldRoots` lists the field roots in order (the leaves
at the `1` positions of `active_fields`). An optional `spine S` after the list selects the
`merkleize_progressive` revision (default `.successorLeft`, `v1.6.1`). -/
syntax (name := sszProgressiveContainer) (docComment)? "ssz_progressive_container " ident
  ("(" ident " : " term ")")* " [" num,* "]" (" spine " term:max)? " where"
  (ppLine ident " : " term:max)+ : command

macro_rules
  | `($[$doc?:docComment]? ssz_progressive_container $n:ident $[($ps:ident : $pts:term)]*
      [$as:num,*] $[spine $sp?]? where $[$fs:ident : $ts:term]*) => do
    let spineT ← match sp? with
      | some sp => pure sp
      | none => `(Spine.successorLeft)
    let active := as.getElems.map (·.getNat)
    if active.size > 256 then Lean.Macro.throwError "active_fields has more than 256 entries"
    if active.any (fun a => a > 1) then Lean.Macro.throwError "active_fields entries are 0 or 1"
    if active.back? ≠ some 1 then Lean.Macro.throwError "active_fields must end in 1"
    if (active.filter (· = 1)).size ≠ fs.size then
      Lean.Macro.throwError "active_fields count of 1 differs from the field count"
    let activeBools ← active.mapM fun a => if a = 1 then `(true) else `(false)
    let projs := fs.map fun f => Lean.mkIdent (n.getId ++ f.getId)
    let mk := Lean.mkIdent (n.getId ++ `mk)
    let parts ← projs.mapM fun p => `(fieldPart ($p x))
    let roots ← projs.mapM fun p => `(hashTreeRoot ($p x))
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
      /-- The roots of the fields, in order: the leaves `merkleize_progressive` places at the
      `1` positions of `active_fields`. -/
      def $fieldRootsId $[{$ps : $pts}]* (x : $ty) : List B256 := [$roots,*]
      instance $[($ps : $pts)]* : Ssz $ty where
        fixedSize? := containerFixedSize [$[Ssz.fixedSize? $ts],*]
        serialize := fun x => serializeParts [$parts,*]
        deserialize := fun bs => do
          let scopes ← splitContainer bs [$[Ssz.fixedSize? $ts],*]
          StateT.run' (do
            let v ← ($dec : FieldDecoder $ty)
            if (← get).isEmpty then pure v
            else throw (.decode (.offset "extra fields"))) scopes
        hashTreeRoot := fun x =>
          progressiveContainerRoot [$activeBools,*] ($fieldRootsId x) (by decide) $spineT)

/-! ## `CompatibleUnion({selector: type})` -/

/-- Serialization of a compatible union ("Compatible unions"):
`value.selector.to_bytes(1, "little") + serialize(value.data)`. The selector is a declared
option in `1..127` by construction (the value's constructor fixes it), so rejection of an
out-of-range or undeclared selector lives in `deserializeUnion`, which sees untrusted bytes. -/
def serializeUnion (selector : Nat) (data : Bytes) : Bytes := leBytes 1 selector ++ data

/-- Deserialization of a compatible union: the first byte is the selector, which must lie in
`1..127` ("Illegal types": a selector outside `uint8(1)` through `uint8(127)` is illegal) and
name a declared option (`decodeOption` returns `none` otherwise); the rest of the scope is that
option's data. An empty scope has no selector. -/
def deserializeUnion {α : Type} (bs : Bytes) (decodeOption : UInt8 → Bytes → Option (M α)) :
    M α :=
  match bs with
  | [] => throw (.decode (.offset "compatible union without a selector"))
  | sel :: data =>
    if sel = 0 ∨ 127 < sel.toNat then throw (.decode (.selector sel))
    else
      match decodeOption sel data with
      | some r => r
      | none => throw (.decode (.selector sel))

-- A selector outside `1..127`, or one no option declares, is rejected; a declared one decodes.
private def unionProbe (sel : UInt8) (data : Bytes) : Option (M Nat) :=
  if sel = 1 then some (pure data.length) else none

#guard ((deserializeUnion (α := Nat) [0] unionProbe).toOption.isNone)
#guard ((deserializeUnion (α := Nat) [200] unionProbe).toOption.isNone)
#guard ((deserializeUnion (α := Nat) [5] unionProbe).toOption.isNone)
#guard ((deserializeUnion [1, 9, 9] unionProbe).toOption == some 2)

end JauneConsensus
