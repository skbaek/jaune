import Lean

/-!
Collision check for the rename map (goal `jaune-shape-and-names-v1`).

Imports the pre-rename environment (the same modules as `EnvWalk.lean`, plus all of
Mathlib through `Jaune`) and reads a rename map.  Prints one line per finding:

* `COLLISION new` -- a `new` name that already exists in the pre-rename environment and
  is not itself renamed away by the map;
* `NAMESPACE new` -- a `new` name whose root (`Jaune.<root>`) is a root that Jaune does not
  have yet and that already names a root-level declaration or namespace outside Jaune
  (an `open Jaune` would then make `<root>` ambiguous).

Usage: lake env lean --run scripts/naming-map-gen/CollisionCheck.lean MAP.json
-/
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [mapPath] := args | IO.eprintln "usage: CollisionCheck MAP.json"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `Jaune}, {module := `Examples}, {module := `Main},
    {module := `Jaune.Trace}, {module := `Jaune.TraceJson}, {module := `Jaune.TraceTransaction},
    {module := `Jaune.StaticcallEffects}, {module := `Jaune.BLSGuards}] {} (trustLevel := 0)
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile mapPath))
  let entries ← IO.ofExcept (json.getObjValAs? (Array Json) "entries")
  let mut olds : Std.HashSet Name := {}
  let mut news : Array (String × String) := #[]
  for e in entries do
    let o ← IO.ofExcept (e.getObjValAs? String "old")
    let n ← IO.ofExcept (e.getObjValAs? String "new")
    olds := olds.insert o.toName
    news := news.push (o, n)
  -- every top-level namespace segment and constant outside Jaune
  let mut roots : Std.HashSet String := {}
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      let r := m.getRoot
      unless r == `Jaune || r == `Examples || r == `Main do
        roots := roots.insert n.getRoot.toString
  -- second components of every existing Jaune name: roots that already exist are not new
  let mut jauneRoots : Std.HashSet String := {}
  for (n, _) in env.constants.map₁.toList do
    let cs := n.components
    if cs[0]? == some `Jaune then
      if let some r := cs[1]? then
        jauneRoots := jauneRoots.insert r.toString
  let mut newRoots : Std.HashSet String := {}
  let mut bad := 0
  for (o, n) in news do
    let nn := n.toName
    if env.contains nn && !olds.contains nn then
      IO.println s!"COLLISION {o} -> {n}"
      bad := bad + 1
    let comps := nn.components
    if comps[0]? == some `Jaune then
      if let some root := comps[1]? then
        let r := root.toString
        unless jauneRoots.contains r do
          newRoots := newRoots.insert r
          if roots.contains r then
            IO.println s!"NAMESPACE {o} -> {n} (new Jaune root `{r}` also exists outside Jaune)"
            bad := bad + 1
  IO.println s!"new Jaune roots introduced by the map: {newRoots.toList.toArray.qsort (· < ·)}"
  IO.println s!"checked {news.size} new names; findings {bad}"
  return (if bad == 0 then 0 else 1)
