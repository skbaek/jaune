import Lean

/-!
Synthetic fixture for the field-reader walk (`scripts/FieldReaders.lean`). Each
declaration below is one row of the expectation table in
`scripts/check-field-readers-tool.py`; the comment names the use the walk must report.
-/

namespace FRFix

structure P where
  a : Nat
  b : Nat
  c : Nat := 0

/-- (a) projection function: reads `a`. -/
def readProj (p : P) : Nat := p.a

/-- (c) matcher alternative uses the variable bound to `a`: reads `a`. -/
def readMatch (p : P) : Nat := match p with | ⟨x, _, _⟩ => x + 1

/-- (c) direct `casesOn` minor premise uses field `a`'s variable: reads `a`. -/
def readCases (p : P) : Nat := P.casesOn (motive := fun _ => Nat) p (fun x _ _ => x)

/-- A theorem whose proof body (not its statement) reads `b`. -/
theorem readThm (p : P) (h : p.b = 0) : True := by
  have : p.b + 0 = 0 := by simp [h]
  trivial

/-- A literal: writes `a`, `b` and the default `c`. -/
def mkP : P := { a := 1, b := 2 }

/-- A record update: copies `a` and `c`, writes `b`; reads nothing. -/
def setB (p : P) : P := { p with b := 3 }

/-- Two declarations sharing one matcher: `shareA` reads `a` only, `shareB` reads `b`
only. The shared matcher must not link `shareB` to `a`. -/
def shareA (p : P) : Nat := match p with | ⟨x, _y, _⟩ => x
def shareB (p : P) : Nat := match p with | ⟨_x, y, _⟩ => y

/-- A plain constant query: `useMkP` mentions `mkP`. -/
def useMkP : Nat := mkP.b

-- (b) a kernel projection `Expr.proj FRFix.P 0 _`, added directly since the elaborator
-- writes projection functions: `readKernel` reads `a`.
open Lean Elab Command in
run_cmd liftTermElabM do
  addDecl <| .defnDecl {
    name := `FRFix.readKernel, levelParams := [],
    type := .forallE `p (.const `FRFix.P []) (.const `Nat []) .default,
    value := .lam `p (.const `FRFix.P []) (.proj `FRFix.P 0 (.bvar 0)) .default,
    hints := .abbrev, safety := .safe }
  addDeclarationRangesFromSyntax `FRFix.readKernel (← getRef)

end FRFix
