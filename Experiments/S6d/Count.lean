import Experiments.S6d.B256Words
import Experiments.S6d.BitVecWords

/-!
# jsn-s6d: axioms, helper-lemma closure and source ranges of the measured theorems

For every measured theorem on either side, `#s6d_count` prints one line:

`S6D_COUNT <name> axioms=[...] helpers=<k> helper_lines=<l> range=<file>:<start>-<end> helper_names=[...]`

* `axioms`: `Lean.collectAxioms`.
* `helpers`: the theorems from Jaune's own modules or from these experiment modules that the
  proof uses, transitively through such theorems (Lean core, Std, Batteries and Mathlib are the
  library on both sides and are not counted). The theorem itself is excluded, and so is its
  verbatim original (`B256.<name>` for a copy `B256.s6d_<name>`), which a copy never uses.
* `helper_lines`: total source lines of those helpers (declaration ranges).
-/

open Lean Elab Command Meta

namespace S6dCount

def isLocalModule (m : Name) : Bool :=
  (`Jaune).isPrefixOf m || (`Experiments).isPrefixOf m

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

partial def closure (env : Environment) (root : Name) : StateM NameSet Unit := do
  let some ci := env.find? root | return
  let some v := ci.value? (allowOpaque := true) | return
  for c in v.getUsedConstants do
    if (← get).contains c then continue
    let some ci' := env.find? c | continue
    let some m := moduleOf env c | continue
    unless isLocalModule m do continue
    -- descend only through theorems; a definition is the vocabulary, not a helper
    let .thmInfo _ := ci' | continue
    -- generated equation lemmas and auxiliary names are not authored helpers
    if c.isInternal then continue
    match c with
    | .str _ s => if s.startsWith "eq_" || s == "eq_def" then continue
    | _ => pure ()
    modify (·.insert c)
    closure env c

end S6dCount

open S6dCount in
elab "#s6d_count " ids:ident* : command => do
  let env ← getEnv
  for id in ids do
    let n := id.getId
    let some _ := env.find? n | logError m!"unknown {n}"; continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    let ((), set) := (closure env n).run {}
    let helpers := set.toList.filter (· != n)
    let mut lines := 0
    for h in helpers do
      if let some r ← liftCoreM <| findDeclarationRanges? h then
        lines := lines + (r.range.endPos.line - r.range.pos.line + 1)
    let rng ← liftCoreM <| findDeclarationRanges? n
    let rs := match rng, moduleOf env n with
      | some r, some m => s!"{m}:{r.range.pos.line}-{r.range.endPos.line}"
      | _, _ => "?"
    let axStr := ",".intercalate (axs.toList.map toString)
    let hStr := ",".intercalate (helpers.map toString)
    logInfo (s!"S6D_COUNT {n} axioms=[{axStr}] helpers={helpers.length} helper_lines={lines} " ++
      s!"range={rs} helper_names=[{hStr}]")
