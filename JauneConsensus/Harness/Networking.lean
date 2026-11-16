import JauneConsensus.DAS
import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Yaml
import JauneConsensus.Harness.GossipTable

/-!
# `networking` case checks (harness only)

`tests/formats/networking/` (`consensus-specs` `v1.6.1`): `meta.yaml` holds the arguments and
the expected `result`; the helper's output must equal it exactly (as a list). A missing
`result` would mean the call must reject; the `v1.6.1` vectors always carry one.

The `gossip_*` handlers (`v1.7.0-beta.4`, `tests/formats/networking/gossip_validation.md`) go to
the gossip driver (`Harness/GossipCases.lean`) through the handler table
(`Harness/GossipTable.lean`).
-/

namespace JauneConsensus.Harness
open Yaml

private def nats (v : YVal) : Except String (List Nat) :=
  ((v.asSeq).bind (·.mapM YVal.asNat)).mapError toString

private def nat (v : YVal) (k : String) : Except String Nat :=
  ((v.field k).bind YVal.asNat).mapError toString

/-- Run a `networking/<handler>` case under `cfg` at preset `P`. -/
def networkingCase (cfg : Config) (c : Case) : IO (Except String Unit) := do
  if c.key.handler.startsWith "gossip_" then return ← gossipCase gossipHandlers cfg c
  let some P := Preset.ofName? c.preset | return .error s!"no preset {c.preset}"
  if c.files != ["meta.yaml"] then return .error s!"unexpected files {c.files}"
  let doc := (parse (← IO.FS.readBinFile (c.dir / "meta.yaml"))).mapError toString
  pure do
    let v ← doc
    let want ← nats (← (v.field "result").mapError toString)
    let got ← match c.key.handler with
      | "get_custody_groups" =>
        v.expectKeys ["node_id", "custody_group_count", "result"] |>.mapError toString
        let nodeId ← nat v "node_id"
        let count ← nat v "custody_group_count"
        let some nid := (UIntN.ofNat? nodeId : M U256).toOption | throw "node_id out of range"
        let some cnt := (U64.ofNat? count).toOption | throw "count out of range"
        match getCustodyGroups cfg nid cnt with
        | .ok r => pure (r.toList.map (·.toNat))
        | .error e => throw s!"rejected: {repr e}"
      | "compute_columns_for_custody_group" =>
        v.expectKeys ["custody_group", "result"] |>.mapError toString
        let g ← nat v "custody_group"
        let some gg := (U64.ofNat? g).toOption | throw "custody_group out of range"
        match computeColumnsForCustodyGroup cfg P gg with
        | .ok r => pure (r.toList.map (·.toNat))
        | .error e => throw s!"rejected: {repr e}"
      | h => throw s!"UNIMPLEMENTED: no networking handler {h}"
    if got == want then pure () else throw s!"result {got} differs from {want}"

end JauneConsensus.Harness
