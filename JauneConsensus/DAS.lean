import JauneConsensus.Helpers
import JauneConsensus.Config

/-!
# Fulu data-availability custody helpers

`get_custody_groups` and `compute_columns_for_custody_group` (`specs/fulu/das-core.md`,
`consensus-specs` `v1.6.1`). `NodeID` is `uint256`; the custody-group loop runs on fuel and
rejects if it is exhausted (`2^20` iterations, far beyond any input: each iteration adds a new
group with probability at least `1/128`).
-/

namespace JauneConsensus
open Jaune (Bytes B256)

/-- `UINT256_MAX` (`specs/fulu/das-core.md`). -/
def UINT256_MAX : U256 := UIntN.max

/-- `get_custody_groups(node_id, custody_group_count)` (Fulu). -/
def getCustodyGroups (cfg : Config) (nodeId : U256) (custodyGroupCount : U64) : M (Array U64) := do
  let groups := cfg.NUMBER_OF_CUSTODY_GROUPS
  require (custodyGroupCount.toNat ≤ groups) "get_custody_groups: count <= NUMBER_OF_CUSTODY_GROUPS"
  if custodyGroupCount.toNat == groups then
    return ← (List.range groups).toArray.mapM fun i => U64.ofNat? i "CustodyIndex"
  let rec loop : Nat → U256 → Array U64 → M (Array U64)
    | 0, _, _ => throw (.assert "get_custody_groups: iteration fuel exhausted")
    | fuel + 1, currentId, acc => do
      if acc.size ≥ custodyGroupCount.toNat then return acc
      let h := (hash (uintToBytes 32 currentId.toNat)).toBytes
      let v ← bytesToUint64 (h.take 8)
      let g ← U64.mod? v (← u64 groups "NUMBER_OF_CUSTODY_GROUPS") "get_custody_groups"
      let acc := if acc.contains g then acc else acc.push g
      let next ← if currentId == UINT256_MAX then pure UIntN.zero
        else UIntN.add? currentId ⟨1, by decide⟩ "get_custody_groups: current_id += 1"
      loop fuel next acc
  let out ← loop (2 ^ 20) nodeId #[]
  require (out.toList.eraseDups.length == out.size) "get_custody_groups: unique"
  pure (out.qsort (· < ·))

/-- `compute_columns_for_custody_group(custody_group)` (Fulu). -/
def computeColumnsForCustodyGroup (cfg : Config) (P : Preset) (custodyGroup : U64) :
    M (Array U64) := do
  let groups := cfg.NUMBER_OF_CUSTODY_GROUPS
  require (custodyGroup.toNat < groups) "compute_columns_for_custody_group: group < NUMBER_OF_CUSTODY_GROUPS"
  let perGroup := P.NUMBER_OF_COLUMNS / groups
  (List.range perGroup).toArray.mapM fun i =>
    U64.ofNat? (groups * i + custodyGroup.toNat) "ColumnIndex"

end JauneConsensus
