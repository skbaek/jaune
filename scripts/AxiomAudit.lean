import Lean

/-! # The from-scratch axiom walker every Jaune axiom audit uses

This module is the single definition of how an axiom audit learns which axioms
a declaration depends on. It imports only `Lean` and is a root of the default
`Assurance` library, so a downstream package can import it and state its own
audits with the same walk. Jaune's own rows are in `ExecutionAxioms.lean`;
`Jaune.lean` imports neither file.

Why not Lean's own report. Since Lean v4.30.0 `#print axioms` on an imported
constant reads a per-module result that was precomputed when that module's
`.olean` was written. The precomputation shares one cache across the module
and breaks the inductive/constructor cycle with an empty sentinel entry that it
cannot tell apart from a finished result, so an inductive reached first through
its own constructor can be exported as axiom-free, and every declaration that
reaches the axiom only through that inductive inherits the under-report
(https://github.com/leanprover/lean4/issues/15226). Which names are hit depends
on hash iteration order, so an unrelated edit can turn such an audit green or
red. By the user's decision of 2026-09-24, no audit takes its verdict from that
report, or from `Lean.collectAxioms`, until the issue is fixed.

What this walk does instead. For each audited name (or, for the union
audit below, for the whole set of roots together) it starts with an empty
visited set and follows, through `Environment.find?` alone, every constant used
by a declaration's type, by the value of a definition, theorem or opaque, and
every constructor of an inductive. It keeps no per-constant result between
walks or within a walk (a constant is visited at most once per walk, and
visiting it only adds that constant's direct references), and it reads no
precomputed per-module table, so the inductive/constructor cycle cannot hide
anything: whichever end the walk enters first, it reaches the other and walks
it. The result is the set of `axiom` declarations reached, which includes
`sorryAx`, `Lean.ofReduceBool` and `native_decide`/`bv_decide` auxiliary axioms.

Three commands use it, through one traversal (`walkMany`; `walk` is its
single-root case). None applies namespace resolution: a name that does not
resolve exactly is an elaboration error, and so is a referenced constant that
the environment does not contain.

* `#full_axioms X` reports, in its own task so a file of rows runs on every
  core, one line per audited name, sorted by the axiom names' text:

      FULL-AXIOMS '<name>': [<axiom>, <axiom>, ...]

  An empty list means no axiom at all.

* `#expect_axioms X [ax₁, …, axₙ]` fails elaboration unless the walk's set is
  exactly the listed one, in both directions:

      AXIOM mismatch for <name>: expected [...], actual [...]

  and logs `AXIOM OK <name>: [...]` otherwise.

* `#union_axioms_of_modules P [ax₁, …, axₙ]` audits a whole library in one walk
  with one shared visited set. Its roots are every constant recorded in the
  `constNames` of every imported module named `P` or `P.…` (all kinds, private
  names and elaborator auxiliaries included; code-generator names are not kernel
  constants and are not roots). It logs one line

      UNION-AXIOMS 'P': [<axiom>, ...] roots=<n> modules=<m> visited=<v>

  and fails elaboration if no module matches (an empty population is never
  green), if the walk reaches a constant the environment does not contain, or
  if the union contains an axiom outside the allowed list (default
  `[propext, Classical.choice, Quot.sound]`; `[]` allows none). A failure by an
  axiom locates it: for each offending axiom, up to 20 roots that reach it,
  nearest first, each with the chain of constants from the root to the axiom.
  Controls: `scripts/UnionAxiomsControls.lean`.
-/

namespace Jaune.AxiomAudit

open Lean Elab Command

/-- The axioms reachable from any of `roots`, any referenced constants that the
environment does not contain, and the number of distinct constants visited
(roots included, absent ones too). One visited set is shared by all roots, so a
constant is visited once per call however many roots reach it; nothing else is
cached, and no per-module table is read. -/
def walkMany (env : Environment) (roots : Array Name) :
    NameSet × NameSet × Nat := Id.run do
  -- Outside the module system this is the identity. Under it, imported
  -- private bodies are only visible with exporting off.
  let env := env.setExporting false
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[]
  for r in roots do
    unless seen.contains r do
      seen := seen.insert r
      stack := stack.push r
  let mut axioms : NameSet := {}
  let mut missing : NameSet := {}
  while h : 0 < stack.size do
    let c := stack.back
    stack := stack.pop
    match env.find? c with
    | none => missing := missing.insert c
    | some info =>
      if info matches .axiomInfo _ then
        axioms := axioms.insert c
      let mut refs := info.type.getUsedConstants
      match info with
      | .defnInfo v => refs := refs ++ v.value.getUsedConstants
      | .thmInfo v => refs := refs ++ v.value.getUsedConstants
      | .opaqueInfo v => refs := refs ++ v.value.getUsedConstants
      | .inductInfo v => refs := refs ++ v.ctors.toArray
      | _ => pure ()
      for n in refs do
        unless seen.contains n do
          seen := seen.insert n
          stack := stack.push n
  return (axioms, missing, seen.size)

/-- The axioms reachable from `root`, and any referenced constants that the
environment does not contain. A fresh visited set per call; nothing cached. -/
def walk (env : Environment) (root : Name) : NameSet × NameSet :=
  let (axioms, missing, _) := walkMany env #[root]
  (axioms, missing)

/-- Every kernel constant declared by an imported module whose name is `pfx` or
extends it, private names and elaborator auxiliaries included, as recorded in
the modules' own `constNames`; and how many modules matched. (`extraConstNames`
holds code-generator names such as `_closed_1`, `_redArg` and `_boxed`, which
are not kernel constants.) -/
def moduleRoots (env : Environment) (pfx : Name) : Array Name × Nat := Id.run do
  let mut roots : Array Name := #[]
  let mut have_ : Std.HashSet Name := {}
  let mut mods := 0
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if pfx.isPrefixOf m then
      mods := mods + 1
      let d := env.header.moduleData[i]!
      for c in d.constNames do
        unless have_.contains c do
          have_ := have_.insert c
          roots := roots.push c
  return (roots, mods)

/-- Where a failing union audit gets its evidence: for each name in `targets`
(offending axioms, or absent constants), up to `limit` of the `roots` that reach
it, nearest first, each with the chain of constants that leads from the root to
the target. One forward traversal builds the reverse reference graph and a
breadth-first search runs backwards from each target, so the cost is linear in
the reachable graph whatever the number of roots. -/
def locate (env : Environment) (roots : Array Name) (targets : Array Name)
    (limit : Nat := 20) : Array String := Id.run do
  let env := env.setExporting false
  let rootSet : Std.HashSet Name := Std.HashSet.ofArray roots
  -- reverse graph: constant ↦ constants that directly reference it
  let mut users : Std.HashMap Name (Array Name) := {}
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[]
  for r in roots do
    unless seen.contains r do
      seen := seen.insert r
      stack := stack.push r
  while h : 0 < stack.size do
    let c := stack.back
    stack := stack.pop
    if let some info := env.find? c then
      let mut refs := info.type.getUsedConstants
      match info with
      | .defnInfo v => refs := refs ++ v.value.getUsedConstants
      | .thmInfo v => refs := refs ++ v.value.getUsedConstants
      | .opaqueInfo v => refs := refs ++ v.value.getUsedConstants
      | .inductInfo v => refs := refs ++ v.ctors.toArray
      | _ => pure ()
      for n in refs do
        users := users.insert n ((users.getD n #[]).push c)
        unless seen.contains n do
          seen := seen.insert n
          stack := stack.push n
  let mut out : Array String := #[]
  for t in targets do
    -- breadth-first backwards from `t`; `next[c]` is the constant `c` was
    -- reached from, i.e. the next step of the chain from `c` towards `t`
    let mut next : Std.HashMap Name Name := {}
    let mut visited : Std.HashSet Name := ({} : Std.HashSet Name).insert t
    let mut queue : Array Name := #[t]
    let mut i := 0
    let mut found := 0
    while i < queue.size && found < limit do
      let c := queue[i]!
      i := i + 1
      if rootSet.contains c then
        found := found + 1
        let mut chain : List Name := [c]
        let mut cur := c
        while cur != t do
          cur := next.getD cur t
          chain := chain ++ [cur]
        let shown := if chain.length > 10 then
          (chain.take 4).map toString ++ ["…"] ++ (chain.drop (chain.length - 4)).map toString
        else chain.map toString
        out := out.push
          (if c == t then s!"  {t} is itself a root"
           else s!"  {t} <- root {c}: {" -> ".intercalate shown}")
      for u in users.getD c #[] do
        unless visited.contains u do
          visited := visited.insert u
          next := next.insert u c
          queue := queue.push u
    if found == 0 then
      out := out.push s!"  {t}: no root reaches it"
  return out

/-- The result of a union audit: the union of axioms reachable from the roots,
the roots and modules counted, and the constants visited. -/
structure UnionReport where
  axioms : Array String
  roots : Nat
  modules : Nat
  visited : Nat

/-- The union audit proper, over an explicit root list (the command feeds it the
module roots). Throws on an empty root list, on any reached constant absent from
the environment, and on any reached axiom not in `allowed`; the last two name
where the problem is (see `locate`). -/
def unionCheck (env : Environment) (label : String) (roots : Array Name)
    (modules : Nat) (allowed : Array String) : Except String UnionReport := do
  if roots.isEmpty || modules == 0 then
    throw s!"#union_axioms_of_modules: no constants found for {label} \
      ({modules} matching modules, {roots.size} roots); an empty population \
      audits nothing"
  let (axioms, missing, visited) := walkMany env roots
  unless missing.isEmpty do
    let ms := (missing.toList.toArray.qsort (fun a b => toString a < toString b))
    let where_ := locate env roots (ms.extract 0 5) 3
    throw s!"#union_axioms_of_modules: {label} reaches {ms.size} constants absent \
      from the environment, e.g. {(ms.extract 0 20).map toString}\n\
      {"\n".intercalate where_.toList}"
  let sorted := axioms.toList.toArray.qsort (fun a b => toString a < toString b)
  let bad := sorted.filter (fun a => !allowed.contains (toString a))
  unless bad.isEmpty do
    let where_ := locate env roots bad
    throw s!"#union_axioms_of_modules: {label} reaches axioms outside \
      {allowed.qsort (· < ·)}: {bad.map toString}\n{"\n".intercalate where_.toList}"
  return { axioms := sorted.map toString, roots := roots.size, modules, visited }

/-- `#full_axioms X` reports the from-scratch axiom set of the exact constant
`X` as one `FULL-AXIOMS` line. -/
elab "#full_axioms " id:ident : command => do
  let env ← getEnv
  let c := id.getId
  unless env.contains c do
    throwError "#full_axioms: unknown constant {c}"
  let report ← wrapAsyncAsSnapshot (cancelTk? := none) fun (_ : Unit) => do
    let (axioms, missing) := walk env c
    unless missing.isEmpty do
      throwError "#full_axioms: {c} reaches constants absent from the environment: \
        {missing.toList}"
    let names := (axioms.toList.map toString).toArray.qsort (· < ·)
    logInfo (MessageData.ofFormat (.text
      s!"FULL-AXIOMS '{c}': [{", ".intercalate names.toList}]"))
  logSnapshotTask { stx? := none, task := (← BaseIO.asTask (report ())), cancelTk? := none }

/-- `#expect_axioms X [ax₁, …, axₙ]` fails unless the from-scratch axiom set of
the exact constant `X` is exactly the listed set. -/
elab "#expect_axioms " id:ident " [" axs:ident,* "]" : command => do
  let env ← getEnv
  let name := id.getId
  unless env.contains name do throwError "AXIOM unknown declaration: {name}"
  let (axioms, missing) := walk env name
  unless missing.isEmpty do
    throwError "AXIOM {name} reaches constants absent from the environment: \
      {missing.toList}"
  let actual := (axioms.toList.map toString).toArray.qsort (· < ·)
  let expected := (axs.getElems.map (toString ∘ TSyntax.getId)).qsort (· < ·)
  unless actual == expected do
    throwError "AXIOM mismatch for {name}: expected {expected}, actual {actual}"
  logInfo m!"AXIOM OK {name}: {actual}"

/-- `#union_axioms_of_modules P [ax₁, …, axₙ]` audits a whole library at once.
Its roots are every constant declared by every imported module named `P` or
`P.…`; one walk with one shared visited set covers them all. It logs

    UNION-AXIOMS 'P': [<axiom>, ...] roots=<n> modules=<m> visited=<v>

(the union of reachable axioms, sorted by text) and fails elaboration if no
module matches, if a reached constant is absent from the environment, or if the
union contains an axiom outside the allowed list (default
`[propext, Classical.choice, Quot.sound]`; `[]` allows none). A failure by an
axiom names, for each offending axiom, up to 20 roots that reach it with the
chain of constants from the root to the axiom. -/
syntax (name := unionAxiomsOfModules)
  "#union_axioms_of_modules " ident (" [" ident,* "]")? : command

elab_rules : command
| `(#union_axioms_of_modules $id:ident $[[ $axs:ident,* ]]?) => do
  let env ← getEnv
  let pfx := id.getId
  let allowed : Array String :=
    match axs with
    | some a => a.getElems.map (toString ·.getId)
    | none => #["Classical.choice", "Quot.sound", "propext"]
  let (roots, modules) := moduleRoots env pfx
  match unionCheck env (toString pfx) roots modules allowed with
  | .error e => throwError "{e}"
  | .ok r =>
    logInfo (MessageData.ofFormat (.text
      s!"UNION-AXIOMS '{pfx}': [{", ".intercalate r.axioms.toList}] \
        roots={r.roots} modules={r.modules} visited={r.visited}"))

end Jaune.AxiomAudit
