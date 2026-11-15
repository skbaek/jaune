import Lean

/-!
Environment walk behind the rename map (goal `jaune-shape-and-names-v1`, WN-b).

Prints one TSV row for every constant whose home module is a Jaune, Examples or
`Main` module. A constant with a declaration range was written (or derived from
something written) in a source file; one without (flag `g`) is compiler-generated
(recursors, matchers, equation lemmas, `proof_n`, `injEq`, ...).

Columns: module, line, kind, flags, qualified name.
`kind`: def, thm, axiom, opaque, inductive, ctor, field (structure projection),
quot, rec. `flags`: `p` private, `i` instance, `s` structure type, `c` class,
`g` generated (no declaration range), `u` unsafe/partial.

Usage: lake env lean --run scripts/naming-map-gen/EnvWalk.lean > OUT.tsv
-/
open Lean

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `Jaune}, {module := `Examples}, {module := `Main},
    {module := `Jaune.Trace}, {module := `Jaune.TraceJson}, {module := `Jaune.TraceTransaction},
    {module := `Jaune.StaticcallEffects}, {module := `Jaune.BLSGuards}] {} (trustLevel := 0)
  let mods := env.header.moduleNames
  let isOurs (m : Name) : Bool :=
    let r := m.getRoot
    r == `Jaune || r == `Examples || r == `Main
  let ctx : Core.Context := { fileName := "<walk>", fileMap := default }
  let _ := ctx
  let mut rows : Array (String × Nat × String × String × String) := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless isOurs m do continue
    let ranges? := declRangeExt.find? (α := DeclarationRanges) env n
    let (line, ranged) := match ranges? with
      | some r => (r.range.pos.line, true)
      | none => (0, false)
    let isCtor := match ci with | .ctorInfo _ => true | _ => false
    let kind :=
      if isCtor then "ctor"
      else match ci with
        | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
        | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
        | .recInfo _ => "rec" | .ctorInfo _ => "ctor"
    let kind := if kind == "def" && (env.getProjectionFnInfo? n).isSome then "field" else kind
    let mut flags := ""
    if isPrivateName n then flags := flags ++ "p"
    if !ranged then flags := flags ++ "g"
    if Lean.Meta.isInstanceCore env n then flags := flags ++ "i"
    if isStructure env n then flags := flags ++ "s"
    if isClass env n then flags := flags ++ "c"
    if (match ci with | .defnInfo d => decide (d.safety != .safe) | _ => false : Bool) then flags := flags ++ "u"
    let shown := if isPrivateName n then (privateToUserName n) else n
    rows := rows.push (m.toString, line, kind, flags, shown.toString)
  let sorted := rows.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2.2.2 < b.2.2.2.2)))
  let stdout ← IO.getStdout
  for (m, l, k, f, n) in sorted do
    stdout.putStrLn s!"{m}\t{l}\t{k}\t{f}\t{n}"
  return 0
