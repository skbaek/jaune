import Lean

/-!
Import-closure printer for `scripts/native-link-objects.sh`.

`lake env lean --run scripts/ImportClosure.lean FILE` parses FILE's header,
imports those modules without running environment extensions, and prints one
line per module in the transitive closure: its name, a tab, and the `.olean`
path the search path resolved it to.  The native link objects are derived from
these paths, so they no longer depend on a Lake executable trace, which is a
placeholder with no link inputs when Lake restores the executable from its
artifact cache.
-/

open Lean

def main (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.eprintln "usage: lean --run scripts/ImportClosure.lean FILE"; return 2
  initSearchPath (← findSysroot)
  let (imports, _, log) ← Elab.parseImports (← IO.FS.readFile file) file
  if log.hasErrors then
    IO.eprintln s!"{file}: could not parse the import header"
    return 1
  let env ← importModules imports {} (loadExts := false)
  for m in env.header.moduleNames do
    IO.println s!"{m}\t{← findOLean m}"
  return 0
