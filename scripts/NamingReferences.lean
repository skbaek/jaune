import NamingReferencesCore

open Lean Lean.Elab

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
    (mainModule := (moduleName.splitOn ".").foldl Name.str .anonymous)
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
  let trees := result.commandState.infoState.trees.toArray
  let (refs, caseRows) := NamingReferences.caseReferences trees inputCtx.fileMap refs
  let refs := NamingReferences.addAuditReferences
    result.commandState.infoState.trees.toArray inputCtx.fileMap refs
  let (references, decls) ← refs.toLspModuleRefs
  let index : Lean.Server.Ilean := {
    module := (moduleName.splitOn ".").foldl Name.str .anonymous
    directImports := Lean.Server.collectImports header
    references, decls
  }
  -- Include the exact source bytes as a binding, so a reference bundle cannot
  -- silently be paired with another revision or with edits made during export.
  let json := Json.mkObj [
    ("source", toJson input),
    ("index", NamingReferences.indexJson index result.commands
      (NamingReferences.syntaxExtras result.commandState.env header.raw trees result.commands caseRows))
  ]
  IO.FS.writeFile output json.compress
  IO.println s!"OK — naming references: {moduleName}, {references.size} resolved identifiers"
  return 0
