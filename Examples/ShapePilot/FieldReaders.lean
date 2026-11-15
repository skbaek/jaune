import Lean
import Jaune
import Jaune.BLSGuards
import Jaune.ChainStore
import Jaune.FixtureException
import Jaune.FixtureTransition
import Jaune.StaticcallEffects
import Jaune.T8n
import Jaune.Trace
import Jaune.TraceJson
import Jaune.TraceTransaction
import ExecutionAxioms
import Examples.Execution
import Examples.Arithmetic
import Examples.ShapePilot.Runs
import Examples.ShapePilot.OldProof

/-! Decision 13's environment walk, for the fields the pilot's `CallContext`
drops and the two transaction fields proposed for deletion.

For structure `S` and field `f` at index `i`, every constant of every module
under `Jaune/` (the umbrella plus the nine modules it leaves to the executable
roots), Assurance's `ExecutionAxioms` and the Examples modules is walked, type and
value. A constant reads `f` if either contains (a) the projection `S.f`, (b) a
primitive projection `Expr.proj S i _`, or (c) an `S.casesOn`, `S.recOn` or
`S.rec` whose minor premise uses the bound variable for field `i`. A matcher
is a constant of its own and is reported under (c) like any other.

Two classes are discounted and listed separately: copies (an occurrence of (a)
or (b) that is directly the `i`-th field argument of `S.mk`, as
`{ s with g := v }` elaborates) and constants generated for `S` itself
(projections, recursors, `noConfusion`, `injEq`, `sizeOf`, `ext`).

Not walked: the declarations of the three executable roots `Main`,
`TraceMain` and `MemoryProbe`, which cannot share one environment (each defines
`main`). They are pure CLI drivers; the shape pilot report records their
textual check. The `#guard` at the end fixes the result, so a new reader
fails this module.
-/
namespace Examples.ShapePilot.FieldReaders
open Lean

structure Target where
  struct : Name
  field : Name

def targets : List Target := [
  ⟨`Jaune.Sevm, `target⟩, ⟨`Jaune.Sevm, `gas⟩, ⟨`Jaune.Sevm, `codeAddress⟩,
  ⟨`Jaune.Sevm, `disablePrecompiles⟩, ⟨`Jaune.Sevm, `shouldTransferValue⟩,
  ⟨`Jaune.TenvStat, `indexInBlock⟩, ⟨`Jaune.TenvStat, `txHash⟩]

/-- Module roots whose constants are walked. -/
def walkedRoots : List Name := [`Jaune, `Examples, `ExecutionAxioms]

structure Found where
  reads : Bool := false
  copies : Bool := false
  deriving Inhabited

structure Spec where
  struct : Name
  index : Nat
  numFields : Nat
  numParams : Nat
  proj : Name
  ctor : Name
  deriving Inhabited

/-- Strip up to `n` leading lambdas; return how many were stripped. -/
def stripLams : Nat → Expr → Nat × Expr
  | n + 1, .lam _ _ body _ => let (d, b) := stripLams n body; (d + 1, b)
  | _, e => (0, e)

def Spec.fieldRead (s : Spec) : Expr → Option Expr
  | .proj n i x => if n == s.struct && i == s.index then some x else none
  | .app (.const n _) x => if n == s.proj then some x else none
  | _ => none

structure ScanState where
  visited : Std.HashSet Expr := {}
  found : Array Found
  exhausted : Bool := false

abbrev ScanM := StateT ScanState Id

def mark (k : Nat) (read : Bool) : ScanM Unit :=
  modify fun st => { st with found := st.found.modify k fun f =>
    if read then { f with reads := true } else { f with copies := true } }

/-- One pass over an expression for every spec at once. `depth` bounds the
nesting walked; running out is recorded and fails the walk. -/
def scan (specs : Array Spec) : Nat → Expr → ScanM Unit
  | 0, _ => modify fun st => { st with exhausted := true }
  | depth + 1, e => do
    if (← get).visited.contains e then return
    modify fun st => { st with visited := st.visited.insert e }
    match e with
    | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      if let .const n _ := fn then
        scan specs depth fn
        for h : k in [0:specs.size] do
          let s := specs[k]
          if n == s.struct ++ `casesOn || n == s.struct ++ `recOn || n == s.struct ++ `rec then
            let minor := if n == s.struct ++ `rec then s.numParams + 1 else s.numParams + 2
            if h : minor < args.size then
              let (stripped, body) := stripLams s.numFields args[minor]
              if stripped < s.numFields || body.hasLooseBVar (s.numFields - 1 - s.index) then
                mark k true
        for h : j in [0:args.size] do
          let a := args[j]
          let mut copied : Option Expr := none
          for h : k in [0:specs.size] do
            let s := specs[k]
            if n == s.ctor && args.size == s.numParams + s.numFields &&
                j == s.numParams + s.index then
              if let some x := s.fieldRead a then
                mark k false
                copied := some x
          scan specs depth (copied.getD a)
      else
        scan specs depth fn
        for a in args do scan specs depth a
    | .const n _ =>
      for h : k in [0:specs.size] do
        if n == specs[k].proj then mark k true
    | .proj n i x =>
      for h : k in [0:specs.size] do
        if n == specs[k].struct && i == specs[k].index then mark k true
      scan specs depth x
    | .lam _ t b _ | .forallE _ t b _ => do scan specs depth t; scan specs depth b
    | .letE _ t v b _ => do scan specs depth t; scan specs depth v; scan specs depth b
    | .mdata _ x => scan specs depth x
    | _ => pure ()

def lastComponent : Name → String
  | .str _ s => s
  | _ => ""

def generatedFor (s : Spec) (n : Name) : Bool :=
  s.struct.isPrefixOf n &&
    (n == s.proj || n.isInternal || n.hasMacroScopes ||
      ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "injEq", "inj",
        "sizeOf_spec", "ext", "ext_iff", "mk"].contains (lastComponent n))

structure Row where
  target : String
  readers : List Name
  copiers : List Name
  generated : Nat
  deriving Repr

def Target.spec (t : Target) : CoreM Spec := do
  let env ← getEnv
  let some info := getStructureInfo? env t.struct
    | throwError "{t.struct} is not a structure"
  let some index := info.fieldNames.idxOf? t.field
    | throwError "{t.struct} has no field {t.field}"
  let some (.inductInfo ind) := env.find? t.struct | throwError "no inductive"
  return { struct := t.struct, index, numFields := info.fieldNames.size,
           numParams := ind.numParams, proj := t.struct ++ t.field,
           ctor := (getStructureCtor env t.struct).name }

/-- Positive controls: fields `step` does read, so the walk must find readers. -/
def controls : List Target := [⟨`Jaune.Sevm, `currentTarget⟩, ⟨`Jaune.Sevm, `caller⟩,
  ⟨`Jaune.TenvStat, `origin⟩]

def walk (ts : List Target) : CoreM (List Row) := do
  let env ← getEnv
  let specs := (← ts.mapM Target.spec).toArray
  let mut readers : Array (Array Name) := specs.map fun _ => #[]
  let mut copiers : Array (Array Name) := specs.map fun _ => #[]
  let mut generated : Array Nat := specs.map fun _ => 0
  for (n, c) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some modName := env.header.moduleNames[idx.toNat]? | continue
    unless walkedRoots.contains modName.getRoot do continue
    let action : ScanM Unit := do
      scan specs 100000 c.type
      if let some v := c.value? then scan specs 100000 v
    let ((), st) := Id.run (action.run { found := specs.map fun _ => {} })
    if st.exhausted then throwError "walk depth exhausted in {n}"
    for h : k in [0:specs.size] do
      let f : Found := st.found.getD k {}
      if f.reads then
        if generatedFor specs[k] n then generated := generated.modify k (· + 1)
        else readers := readers.modify k (·.push n)
      else if f.copies then
        copiers := copiers.modify k (·.push n)
  let sortNames (a : Array Name) := (a.qsort Name.lt).toList
  return ((specs.zip readers).zip (copiers.zip generated)).toList.map
    fun ((s, r), (c, g)) =>
      { target := s!"{s.struct}.{lastComponent s.proj}", readers := sortNames r,
        copiers := sortNames c, generated := g }

-- Print the walk and fix its verdict: no reader of any of the seven fields,
-- and readers of each control field.
#eval show CoreM Unit from do
  let rows ← walk (targets ++ controls)
  for row in rows do
    logInfo m!"{row.target}: {row.readers.length} readers {row.readers.take 5}; \
      copies {row.copiers}; generated readers {row.generated}"
  let (fields, ctrl) := rows.splitAt targets.length
  for row in fields do
    unless row.readers.isEmpty do throwError "{row.target} has readers {row.readers}"
  for row in ctrl do
    if row.readers.isEmpty then throwError "control {row.target} found no reader"

end Examples.ShapePilot.FieldReaders
