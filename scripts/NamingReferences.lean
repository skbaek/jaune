import Lean

/-! Export compiler-resolved references including locals, which `.ilean` omits.
This is migration tooling, outside the specification and its trusted closure.
It elaborates one file against already-built imports; it never builds imports.
-/

open Lean Lean.Elab

namespace NamingReferences

/-- A constructor case created by Lean's ordinary `cases` eliminator. -/
structure CaseOrigin where
  parent : Name
  goal : MVarId
  ctor : Name

/-- Follow only proof metavariable assignments, not names or source proximity. -/
partial def descends (ctx : MetavarContext) (origin target : MVarId)
    (seen : List MVarId := []) : Bool :=
  if origin == target then true
  else if seen.contains origin then false
  else match ctx.getExprAssignmentCore? origin with
    | none => (ctx.dAssignment.find? origin).any fun delayed =>
        descends ctx delayed.mvarIdPending target (origin :: seen)
    | some e => (e.collectMVars {}).result.any fun child =>
        descends ctx child target (origin :: seen)

partial def usesCasesOn (ctx : MetavarContext) (goal : MVarId) (name : Name)
    (seen : List MVarId := []) : Bool :=
  if seen.contains goal then false
  else match ctx.getExprAssignmentCore? goal with
    | none => (ctx.dAssignment.find? goal).any fun delayed =>
        usesCasesOn ctx delayed.mvarIdPending name (goal :: seen)
    | some e => e.getUsedConstants.contains (mkCasesOnName name) ||
        (e.collectMVars {}).result.any fun child => usesCasesOn ctx child name (goal :: seen)

def caseOrigins (ctx : ContextInfo) (t : TacticInfo) : Array CaseOrigin := Id.run do
  -- Explicit/custom eliminators and inline alternatives have different naming
  -- contracts. Leave them unresolved unless a separate resolver supports them.
  unless privateToUserName t.elaborator == `Lean.Elab.Tactic.evalCases &&
      t.stx.isOfKind ``Lean.Parser.Tactic.cases && t.stx[2].isNone && t.stx[3].isNone do
    return #[]
  let some parent := ctx.parentDecl? | return #[]
  let mut result := #[]
  for goal in t.goalsAfter do
    if t.goalsBefore.contains goal then continue
    let some decl := t.mctxAfter.findDecl? goal | continue
    let tag := decl.userName.eraseMacroScopes
    let ctors := decl.type.getUsedConstants.filter fun name =>
      match ctx.env.find? name with
      | some (.ctorInfo ctor) =>
        ctor.name.getString! == tag.getString! &&
        t.goalsBefore.any (usesCasesOn t.mctxAfter · ctor.induct)
      | _ => false
    if ctors.size == 1 then
      result := result.push ⟨parent, goal, ctors[0]!⟩
  return result

def caseLabels (stx : Syntax) : Array Syntax := Id.run do
  match stx with
  | `(tactic| case $[$tags $hs*]|* => $_body:tacticSeq1Indented) =>
    let mut result := #[]
    for tag in tags do
      if let `(binderIdent| $id:ident) := tag then
        -- Compound labels can combine multiple nested constructors. They need
        -- component-wise provenance rather than a single reference range.
        if id.getId.getPrefix.isAnonymous then result := result.push id.raw
    return result
  | _ => return #[]

def addCaseReferences (trees : Array InfoTree) (fileMap : FileMap)
    (refs : Server.ModuleRefs) : Server.ModuleRefs := Id.run do
  let mut origins : Array CaseOrigin := #[]
  for tree in trees do
    origins := tree.foldInfo (fun ctx info found =>
      if let .ofTacticInfo t := info then found ++ caseOrigins ctx t else found) origins
  let mut result := refs
  for tree in trees do
    result := tree.foldInfo (fun ctx info found => Id.run do
      let .ofTacticInfo t := info | return found
      unless t.elaborator == ``Lean.Elab.Tactic.evalCase do return found
      let some parent := ctx.parentDecl? | return found
      let mut found := found
      for label in caseLabels t.stx do
        let tag := label.getId.eraseMacroScopes
        let goals := t.goalsBefore.filter fun goal =>
          (t.mctxBefore.findDecl? goal).any fun decl =>
            tag.isSuffixOf decl.userName.eraseMacroScopes
        unless goals.length == 1 do continue
        let names := (origins.filter fun origin => origin.parent == parent &&
          origin.ctor.getString! == tag.getString! &&
          descends t.mctxBefore origin.goal goals[0]!).map (·.ctor)
        let names := names.toList.eraseDups
        unless names.length == 1 do continue
        let name := names[0]!
        let some start := label.getPos? | continue
        let some stop := label.getTailPos? | continue
        let ref : Server.Reference := {
          ident := .const ((Server.getModuleContainingDecl? ctx.env name).getD ctx.env.header.mainModule).toString name.toString
          range := ⟨fileMap.utf8PosToLspPos start, fileMap.utf8PosToLspPos stop⟩
          stx := label, ci := ctx, info := info, isBinder := false }
        found := found.addRef ref
      return found) result
  return result

end NamingReferences

unsafe def main (args : List String) : IO UInt32 := do
  let [source, moduleName, output] := args
    | IO.eprintln "usage: jaune-naming-references SOURCE MODULE OUTPUT"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile source
  let inputCtx := Parser.mkInputContext input source
  let options := ({} : Options).setBool `Elab.async false
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header options messages inputCtx
    (mainModule := moduleName.toName)
  if messages.hasErrors then
    for message in messages.toList do
      IO.eprintln (← message.toString)
    return 1
  let state := { Command.mkState env messages options with infoState.enabled := true }
  let result ← IO.processCommands inputCtx parserState state
  if result.commandState.messages.hasErrors then
    for message in result.commandState.messages.toList do
      IO.eprintln (← message.toString)
    return 1
  let refs := Lean.Server.findModuleRefs inputCtx.fileMap
    result.commandState.infoState.trees.toArray (localVars := true)
  let refs := NamingReferences.addCaseReferences
    result.commandState.infoState.trees.toArray inputCtx.fileMap refs
  let (references, decls) ← refs.toLspModuleRefs
  let index : Lean.Server.Ilean := {
    module := moduleName.toName
    directImports := Lean.Server.collectImports header
    references, decls
  }
  -- Include the exact source bytes as a binding, so a reference bundle cannot
  -- silently be paired with another revision or with edits made during export.
  let json := Json.mkObj [
    ("source", toJson input),
    ("index", toJson index)
  ]
  IO.FS.writeFile output json.compress
  IO.println s!"OK — naming references: {moduleName}, {references.size} resolved identifiers"
  return 0
