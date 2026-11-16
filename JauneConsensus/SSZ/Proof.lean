import JauneConsensus.SSZ.Merkle
import JauneConsensus.Helpers

/-!
# Generalized indices and Merkle proofs

Transcribed from `ssz/merkle-proofs.md` (`consensus-specs` `v1.6.1`): the generalized-index
helpers, the tree layout `merkle_tree`, single-item and multi-item proof verification, and a
proof builder over a tree of chunks (the chunk-level core of `compute_merkle_proof`,
`specs/altair/light-client/full-node.md`, whose object-level form needs a container's chunks and
lives with the containers).

A `GeneralizedIndex` is a Python `int` in the specification, so it is a `Nat` here; there is no
`uint64` arithmetic in this module. `hash(a + b)` is the SSZ layer's `hashPair`
(`SSZ/Merkle.lean`). A Python failure (`assert`, `math.log2(0)`, a missing dictionary key, an
index out of range) is a typed rejection (outcome O5).

`isValidMerkleBranch` (`Helpers.lean`, phase0's `is_valid_merkle_branch`) is the same check with
a position and depth in place of a generalized index (`2^depth + position`); the guards below
check that they agree on a hand tree.

`concat_generalized_indices` appeared in earlier editions of this document but is not in it at
`v1.6.1`, so it is not transcribed.
-/

namespace JauneConsensus

open Jaune

/-- A generalized index (`ssz/merkle-proofs.md`, "Generalized Merkle tree index"). -/
abbrev GeneralizedIndex := Nat

/-- `get_power_of_two_ceil(x)`. -/
def getPowerOfTwoCeil (x : Nat) : Nat :=
  if x ≤ 1 then 1
  else if x = 2 then 2
  else 2 * getPowerOfTwoCeil ((x + 1) / 2)
termination_by x
decreasing_by omega

/-- `merkle_tree(leaves)`: the tree as an array indexed by generalized index (index 0 unused),
twice the padded bottom layer long, zero chunks (`Bytes32()`) padding the bottom layer. -/
def merkleTree (leaves : List B256) : M (Array B256) := do
  let bottomLength := getPowerOfTwoCeil leaves.length
  let mut o : Array B256 :=
    (List.replicate bottomLength zeroChunk ++ leaves ++
      List.replicate (bottomLength - leaves.length) zeroChunk).toArray
  for j in List.range (bottomLength - 1) do
    let i := bottomLength - 1 - j
    let l ← getAt o (i * 2) "merkle_tree: o[i * 2]"
    let r ← getAt o (i * 2 + 1) "merkle_tree: o[i * 2 + 1]"
    o := o.setIfInBounds i (hashPair l r)
  pure o

/-! ## Helpers for generalized indices -/

/-- `get_generalized_index_length(index) = int(log2(index))`; `math.log2(0)` raises. -/
def getGeneralizedIndexLength (index : GeneralizedIndex) : M Nat :=
  if index = 0 then throw (.assert "get_generalized_index_length: log2(0)")
  else pure index.log2

/-- `get_generalized_index_bit(index, position) = (index & (1 << position)) > 0`. -/
def getGeneralizedIndexBit (index : GeneralizedIndex) (position : Nat) : Bool :=
  (index &&& (1 <<< position)) > 0

/-- `generalized_index_sibling(index) = index ^ 1`. -/
def generalizedIndexSibling (index : GeneralizedIndex) : GeneralizedIndex := index ^^^ 1

/-- `generalized_index_child(index, right_side) = index * 2 + right_side`. -/
def generalizedIndexChild (index : GeneralizedIndex) (rightSide : Bool) : GeneralizedIndex :=
  index * 2 + (if rightSide then 1 else 0)

/-- `generalized_index_parent(index) = index // 2`. -/
def generalizedIndexParent (index : GeneralizedIndex) : GeneralizedIndex := index / 2

/-! ## Multiproof index sets -/

/-- The loop `while o[-1] > 1: o.append(step(o[-1]))` from a first element, returning all of
`o`. Each step at least halves a value above one, so `start + 1` iterations always suffice;
the bound is fuel, never reached. -/
def indexWalk (step : Nat → Nat) : Nat → Nat → List Nat
  | 0, cur => [cur]
  | fuel + 1, cur => if cur > 1 then cur :: indexWalk step fuel (step cur) else [cur]

/-- `get_branch_indices(tree_index)`: the sisters along the path to the root, `o[:-1]`. -/
def getBranchIndices (treeIndex : GeneralizedIndex) : List GeneralizedIndex :=
  (indexWalk (fun x => generalizedIndexSibling (generalizedIndexParent x)) (treeIndex + 1)
    (generalizedIndexSibling treeIndex)).dropLast

/-- `get_path_indices(tree_index)`: the nodes along the path to the root, `o[:-1]`. -/
def getPathIndices (treeIndex : GeneralizedIndex) : List GeneralizedIndex :=
  (indexWalk generalizedIndexParent (treeIndex + 1) treeIndex).dropLast

/-- `get_helper_indices(indices)`: the branch indices of all paths minus the path indices,
sorted in decreasing order. -/
def getHelperIndices (indices : List GeneralizedIndex) : List GeneralizedIndex :=
  let helpers := (indices.flatMap getBranchIndices).eraseDups
  let paths := indices.flatMap getPathIndices
  (helpers.filter (fun h => !paths.contains h)).mergeSort (fun a b => decide (b ≤ a))

/-! ## Verification -/

/-- `calculate_merkle_root(leaf, proof, index)`. -/
def calculateMerkleRoot (leaf : B256) (proof : List B256) (index : GeneralizedIndex) : M B256 := do
  require (proof.length == (← getGeneralizedIndexLength index))
    "calculate_merkle_root: len(proof) == get_generalized_index_length(index)"
  let mut leaf := leaf
  for (h, i) in proof.zip (List.range proof.length) do
    if getGeneralizedIndexBit index i then leaf := hashPair h leaf
    else leaf := hashPair leaf h
  pure leaf

/-- `verify_merkle_proof(leaf, proof, index, root)`. -/
def verifyMerkleProof (leaf : B256) (proof : List B256) (index : GeneralizedIndex) (root : B256) :
    M Bool := do
  pure (B256.beq (← calculateMerkleRoot leaf proof index) root)

/-- A finite map from generalized indices to nodes, as an association list (the spec's
`objects` dictionary). Later bindings shadow earlier ones, as `{**a, **b}` does. -/
abbrev NodeMap := List (GeneralizedIndex × B256)

def NodeMap.lookup (m : NodeMap) (k : GeneralizedIndex) : Option B256 :=
  (List.find? (fun (e : GeneralizedIndex × B256) => e.1 == k) m).map (·.2)

/-- `calculate_multi_merkle_root(leaves, proof, indices)`. The key list grows while it is
walked; a parent is added only when absent, so it grows by at most one entry per index below the
largest key, which bounds the walk (fuel). -/
def calculateMultiMerkleRoot (leaves proof : List B256) (indices : List GeneralizedIndex) :
    M B256 := do
  require (leaves.length == indices.length)
    "calculate_multi_merkle_root: len(leaves) == len(indices)"
  let helperIndices := getHelperIndices indices
  require (proof.length == helperIndices.length)
    "calculate_multi_merkle_root: len(proof) == len(helper_indices)"
  -- `{**leaves, **helpers}`: helpers bound last, so listed first in the association list
  let objects0 : NodeMap := (helperIndices.zip proof).reverse ++ (indices.zip leaves).reverse
  let keys0 := ((objects0.map (·.1)).eraseDups).mergeSort (fun a b => decide (b ≤ a))
  let maxKey := keys0.foldl max 0
  let rec walk (fuel pos : Nat) (keys : Array Nat) (objects : NodeMap) : M NodeMap :=
    match fuel with
    | 0 => throw (.assert "calculate_multi_merkle_root: walk bound")
    | fuel + 1 =>
      if h : pos < keys.size then
        let k := keys[pos]
        if (objects.lookup k).isSome && (objects.lookup (k ^^^ 1)).isSome &&
            (objects.lookup (k / 2)).isNone then
          match objects.lookup ((k ||| 1) ^^^ 1), objects.lookup (k ||| 1) with
          | some l, some r =>
            walk fuel (pos + 1) (keys.push (k / 2)) ((k / 2, hashPair l r) :: objects)
          | _, _ => throw (.index "calculate_multi_merkle_root: objects[k]" k objects.length)
        else walk fuel (pos + 1) keys objects
      else pure objects
  let objects ← walk (keys0.length + maxKey + 2) 0 keys0.toArray objects0
  match objects.lookup 1 with
  | some r => pure r
  | none => throw (.index "calculate_multi_merkle_root: objects[1]" 1 objects.length)

/-- `verify_merkle_multiproof(leaves, proof, indices, root)`. -/
def verifyMerkleMultiproof (leaves proof : List B256) (indices : List GeneralizedIndex)
    (root : B256) : M Bool := do
  pure (B256.beq (← calculateMultiMerkleRoot leaves proof indices) root)

/-! ## Building proofs over a tree of chunks -/

/-- The chunk-level core of `compute_merkle_proof(object, index)`: the nodes at
`get_branch_indices(index)` of `merkle_tree(leaves)`, in that order (leaf to root). An index
outside the tree rejects. -/
def computeMerkleProofOfLeaves (leaves : List B256) (index : GeneralizedIndex) :
    M (List B256) := do
  let tree ← merkleTree leaves
  (getBranchIndices index).mapM fun i => getAt tree i "compute_merkle_proof: tree[i]"

/-- The root of `merkle_tree(leaves)` (`o[1]`); it equals `merkleize(leaves)`. -/
def merkleTreeRoot (leaves : List B256) : M B256 := do
  getAt (← merkleTree leaves) 1 "merkle_tree: o[1]"

/-! ## Tests: small hand trees -/

private def L (k : Nat) : B256 := (k + 1).toB256
private def ok? {α} (x : M α) : Option α := x.toOption

#guard (List.range 10).map getPowerOfTwoCeil == [1, 1, 2, 4, 4, 8, 8, 8, 8, 16]
#guard ok? (getGeneralizedIndexLength 1) == some 0 && ok? (getGeneralizedIndexLength 9) == some 3
#guard (getGeneralizedIndexLength 0).toBool == false
#guard getGeneralizedIndexBit 0b1010 1 && !getGeneralizedIndexBit 0b1010 2
#guard generalizedIndexSibling 9 == 8 && generalizedIndexSibling 8 == 9
#guard generalizedIndexChild 4 true == 9 && generalizedIndexChild 4 false == 8
#guard generalizedIndexParent 9 == 4
-- the spec's example: positions 0, 1, 6 of an 8-leaf tree (indices 8, 9, 14) need the three
-- `*` nodes of its diagram, indices 15, 6, 5
#guard getHelperIndices [8, 9, 14] == [15, 6, 5]
#guard getBranchIndices 9 == [8, 5, 3] && getPathIndices 9 == [9, 4, 2]
#guard getBranchIndices 1 == [] && getPathIndices 1 == []

-- a 4-leaf tree by hand: root = H(H(l0, l1), H(l2, l3))
private def l4 : List B256 := [L 0, L 1, L 2, L 3]
private def n2 : B256 := hashPair (L 0) (L 1)
private def n3 : B256 := hashPair (L 2) (L 3)
private def r4 : B256 := hashPair n2 n3

#guard (ok? (merkleTreeRoot l4)).map (B256.beq r4) == some true
-- the root equals the SSZ layer's merkleization of the same chunks
#guard (ok? (merkleTreeRoot l4)).map (B256.beq (merkleizeDepth l4 2)) == some true
-- 3 leaves pad with a zero chunk
#guard (ok? (merkleTreeRoot [L 0, L 1, L 2])).map
  (B256.beq (hashPair n2 (hashPair (L 2) zeroChunk))) == some true
-- proof of leaf 2 (index 6): [l3, n2]
#guard (ok? (computeMerkleProofOfLeaves l4 6)).map (·.map B256.toBytes) ==
  some [(L 3).toBytes, n2.toBytes]
#guard ok? (verifyMerkleProof (L 2) [L 3, n2] 6 r4) == some true
#guard ok? (verifyMerkleProof (L 2) [n2, L 3] 6 r4) == some false
#guard (verifyMerkleProof (L 2) [L 3] 6 r4).toBool == false
-- agreement with phase0's `is_valid_merkle_branch` (depth 2, position 2 is index 4 + 2)
#guard (List.range 4).all fun p =>
  match ok? (computeMerkleProofOfLeaves l4 (4 + p)), l4[p]?, ok? (U64.ofNat? p) with
  | some pr, some leaf, some pos => ok? (verifyMerkleProof leaf pr (4 + p) r4) == some true &&
      ok? (isValidMerkleBranch leaf pr (U64.lit 2) pos r4) == some true
  | _, _, _ => false
-- multiproof: leaves 0 and 1 (indices 4, 5) need only n3 (index 3)
#guard getHelperIndices [4, 5] == [3]
#guard ok? (verifyMerkleMultiproof [L 0, L 1] [n3] [4, 5] r4) == some true
#guard ok? (verifyMerkleMultiproof [L 1, L 0] [n3] [4, 5] r4) == some false
-- a single-item proof is a multiproof with one index
#guard ok? (verifyMerkleMultiproof [L 2] [L 3, n2] [6] r4) == some true
-- the spec's 8-leaf example, built and verified
private def l8 : List B256 := (List.range 8).map L
#guard match ok? (merkleTree l8), ok? (merkleTreeRoot l8) with
  | some t, some r =>
    let pr := [15, 6, 5].filterMap (fun i => t[i]?)
    ok? (verifyMerkleMultiproof [L 0, L 1, L 6] pr [8, 9, 14] r) == some true
  | _, _ => false
#guard (verifyMerkleMultiproof [L 0] [] [8, 9] r4).toBool == false

/-- `compute_merkle_branch_root(leaf, branch, depth, index)` (`specs/phase0/beacon-chain.md`);
`branch[i]` out of range raises. -/
def computeMerkleBranchRoot (leaf : B256) (branch : List B256) (depth index : Nat) :
    M B256 := do
  let mut value := leaf
  for i in List.range depth do
    let b ← match branch[i]? with
      | some b => pure b
      | none => throw (.index "compute_merkle_branch_root: branch[i]" i branch.length)
    if index / 2 ^ i % 2 == 1 then value := hashPair b value
    else value := hashPair value b
  pure value

end JauneConsensus
