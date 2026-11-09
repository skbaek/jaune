import JauneConsensus.SSZ.Container

/-!
# SSZ progressive types and compatible unions

`ssz/simple-serialize.md` (`consensus-specs` `v1.6.1`): `ProgressiveList[T]` (EIP-7916),
`ProgressiveBitlist` (EIP-7916), `ProgressiveContainer(active_fields)` (EIP-7495) and
`CompatibleUnion({selector: type})` (EIP-8016). Electra and Fulu use none of them; the
`ssz_generic` suite exercises them, and they are implemented so that no case is excluded.

Serialization is that of the non-progressive counterpart (a list without limit, a bitlist
without limit, a container); only Merkleization differs, through `merkleize_progressive`,
`mix_in_active_fields` and `mix_in_selector`.
-/

namespace JauneConsensus
open Jaune

/-- `merkleize_progressive(chunks, num_leaves)` ("Merkleization"): the empty input is the zero
chunk; otherwise `hash(merkleize_progressive(chunks[num_leaves:], num_leaves * 4),
merkleize(chunks[:num_leaves], num_leaves))`. Total by fuel (`chunks.length + 1` suffices,
since every non-empty step consumes at least one chunk). -/
def merkleizeProgressiveAux : Nat → List B256 → Nat → B256
  | 0, _, _ => zeroChunk
  | _ + 1, [], _ => zeroChunk
  | fuel + 1, cs, numLeaves =>
    hashPair (merkleizeProgressiveAux fuel (cs.drop numLeaves) (numLeaves * 4))
      (merkleizeDepth (cs.take numLeaves) (depthOf numLeaves))

/-- `merkleize_progressive(chunks)` with the default `num_leaves=1`. -/
def merkleizeProgressive (chunks : List B256) : B256 :=
  merkleizeProgressiveAux (chunks.length + 1) chunks 1

/-- `mix_in_active_fields(root, active_fields)`: `hash(root, pack_bits(active_fields))`, with
`active_fields` restricted to at most 256 bits ("Merkleization": `active_fields` is restricted
to ≤ 256 bits), so `pack_bits` is one chunk. The bound is a proof obligation, so an overlong
`active_fields` is rejected at elaboration. -/
def mixInActiveFields (root : B256) (activeFields : List Bool)
    (_ : activeFields.length ≤ 256) : B256 :=
  hashPair root (chunkOf (bitsToBytes activeFields))

/-! ## `ProgressiveList[T]` -/

/-- `ProgressiveList[T]`: an ordered homogeneous collection without limit. -/
structure ProgressiveList (α : Type) where
  toArray : Array α
  deriving DecidableEq, BEq

/-- `ProgressiveList[T]` ("Merkleization": `mix_in_length(merkleize_progressive(pack(value)),
len(value))` for basic `T`, with element roots otherwise). Decoding is that of a list with no
limit. -/
instance {α : Type} [Ssz α] : Ssz (ProgressiveList α) where
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
    mixInLength (merkleizeProgressive chunks) v.toArray.size

/-! ## `ProgressiveBitlist` -/

/-- `ProgressiveBitlist`: an ordered collection of booleans without limit. -/
structure ProgressiveBitlist where
  bits : Array Bool
  deriving DecidableEq, BEq

/-- `ProgressiveBitlist` ("Serialization" as `Bitlist[N]`; "Merkleization":
`mix_in_length(merkleize_progressive(pack_bits(value)), len(value))`). -/
instance : Ssz ProgressiveBitlist where
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
    mixInLength (merkleizeProgressive (pack (bitsToBytes v.bits.toList))) v.bits.size

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
    (h : activeFields.length ≤ 256) : B256 :=
  mixInActiveFields (merkleizeProgressive (activeChunks activeFields roots)) activeFields h

/-- `ssz_progressive_container Name [a₀, a₁, ...] where f₁ : T₁ ...`: a progressive container
with the given `active_fields` (each `0` or `1`). The illegal configurations ("Illegal types":
no fields, more than 256 entries, a trailing `0`, a count of `1`s different from the field
count) are refused when the declaration is expanded. -/
syntax (name := sszProgressiveContainer) (docComment)? "ssz_progressive_container " ident
  " [" num,* "]" " where" (ppLine ident " : " term:max)+ : command

macro_rules
  | `($[$doc?:docComment]? ssz_progressive_container $n:ident [$as:num,*] where
      $[$fs:ident : $ts:term]*) => do
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
    `($[$doc?:docComment]? structure $n where
        $[$fs:ident : $ts]*
        deriving DecidableEq, BEq
      instance : Ssz $n where
        fixedSize? := containerFixedSize [$[Ssz.fixedSize? $ts],*]
        serialize := fun x => serializeParts [$parts,*]
        deserialize := fun bs => do
          let scopes ← splitContainer bs [$[Ssz.fixedSize? $ts],*]
          StateT.run' (do
            let v ← ($dec : FieldDecoder $n)
            if (← get).isEmpty then pure v
            else throw (.decode (.offset "extra fields"))) scopes
        hashTreeRoot := fun x => progressiveContainerRoot [$activeBools,*] [$roots,*] (by decide))

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
