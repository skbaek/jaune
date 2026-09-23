import Lean

/-!
# Exact axiom expectations, checked by a from-scratch closure walk

`#expect_axioms name [ax₁, …, axₙ]` fails elaboration unless the axioms that
`name` depends on are exactly the listed set. The set is computed by
`Jaune.AxiomAudit.auditFullAxioms`, which walks every constant reachable from
the declaration's type and value (inductive types through their constructors)
and never calls `Lean.collectAxioms` or `#print axioms` (lean4#15226).

This module imports only `Lean`, so a downstream library can import it to state
its own expectations. Jaune's own rows are in `ExecutionAxioms.lean`; neither
file is imported by `Jaune.lean`.
-/

open Lean Elab Command

namespace Jaune.AxiomAudit

/-- Visit `c` and everything reachable from it, recording visited constants and
the axioms among them. -/
partial def auditFullAxioms (env : Environment) (c : Name) :
    StateM (NameSet × NameSet) Unit := do
  let (seen, axs) ← get
  if seen.contains c then return
  set (seen.insert c, axs)
  let walk (e : Expr) : StateM (NameSet × NameSet) Unit :=
    e.getUsedConstants.forM (auditFullAxioms env)
  match env.find? c with
  | some (.axiomInfo v) =>
      modify fun (seen, axs) => (seen, axs.insert c)
      walk v.type
  | some (.defnInfo v) => walk v.type *> walk v.value
  | some (.thmInfo v) => walk v.type *> walk v.value
  | some (.opaqueInfo v) => walk v.type *> walk v.value
  | some (.ctorInfo v) => walk v.type
  | some (.recInfo v) => walk v.type
  | some (.inductInfo v) => walk v.type *> v.ctors.forM (auditFullAxioms env)
  | _ => pure ()

/-- The axioms `c` depends on, sorted by name. -/
def fullAxioms (env : Environment) (c : Name) : Array String :=
  let (_, (_, actual)) := (auditFullAxioms env c).run ({}, {})
  (actual.toList.map toString).toArray.qsort (· < ·)

end Jaune.AxiomAudit

elab "#expect_axioms " id:ident " [" axs:ident,* "]" : command => do
  let env ← getEnv
  let name := id.getId
  unless env.contains name do throwError "AXIOM unknown declaration: {name}"
  let actual := Jaune.AxiomAudit.fullAxioms env name
  let expected := (axs.getElems.map (toString ∘ TSyntax.getId)).qsort (· < ·)
  unless actual == expected do
    throwError "AXIOM mismatch for {name}: expected {expected}, actual {actual}"
  logInfo m!"AXIOM OK {name}: {actual}"
