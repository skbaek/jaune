import NamingReferencesCore

/-! Export kernel expressions and effective attributes for rename fidelity.
This optional metaprogram is outside the specification import closure.
-/

open Lean Lean.Elab

namespace NamingFidelity

def node (tag : String) (args : Array Json := #[]) : Json :=
  Json.arr (#[toJson tag] ++ args)

def nameRef (n : Name) : Json := node "name" #[toJson n.toString]

inductive LevelKey where
  | zero
  | succ (u : Nat)
  | max (u v : Nat)
  | imax (u v : Nat)
  | param (i : Nat)
  deriving BEq, Hashable

inductive ExprKey where
  | bvar (i : Nat)
  | sort (u : Nat)
  | const (n : String) (us : List Nat)
  | app (f a : Nat)
  | lam (bi : String) (t b : Nat)
  | forallE (bi : String) (t b : Nat)
  | letE (nonDep : Bool) (t v b : Nat)
  | nat (n : Nat)
  | str (s : String)
  | proj (n : String) (i : Nat) (e : Nat)
  deriving BEq, Hashable

structure PoolState where
  levelPool : Array Json := #[]
  levelMap  : Std.HashMap LevelKey Nat := {}
  exprPool  : Array Json := #[]
  exprMap   : Std.HashMap ExprKey Nat := {}

abbrev PoolM := ExceptT String (StateM PoolState)

def pushLevel (k : LevelKey) (j : Json) : PoolM Nat := do
  let s ← get
  if let some idx := s.levelMap[k]? then
    return idx
  let idx := s.levelPool.size
  set { s with levelPool := s.levelPool.push j, levelMap := s.levelMap.insert k idx }
  return idx

def pushExpr (k : ExprKey) (j : Json) : PoolM Nat := do
  let s ← get
  if let some idx := s.exprMap[k]? then
    return idx
  let idx := s.exprPool.size
  set { s with exprPool := s.exprPool.push j, exprMap := s.exprMap.insert k idx }
  return idx

partial def internLevel (params : List Name) : Level → PoolM Nat
  | .zero => pushLevel .zero (node "zero")
  | .succ u => do
    let uId ← internLevel params u
    pushLevel (.succ uId) (node "succ" #[toJson uId])
  | .max u v => do
    let uId ← internLevel params u
    let vId ← internLevel params v
    pushLevel (.max uId vId) (node "max" #[toJson uId, toJson vId])
  | .imax u v => do
    let uId ← internLevel params u
    let vId ← internLevel params v
    pushLevel (.imax uId vId) (node "imax" #[toJson uId, toJson vId])
  | .param n =>
    match params.idxOf? n with
    | some i => pushLevel (.param i) (node "param" #[toJson i])
    | none => throw s!"unbound universe parameter {n}"
  | .mvar _ => throw "unassigned universe metavariable"

def stripMdata : Expr → Expr
  | .mdata _ e => stripMdata e
  | e => e

private inductive InternWork where
  | visit (e : Expr)
  | finishApp (root f a : Expr)
  | finishLam (root : Expr) (bi : BinderInfo) (t b : Expr)
  | finishForall (root : Expr) (bi : BinderInfo) (t b : Expr)
  | finishLet (root : Expr) (nonDep : Bool) (t v b : Expr)
  | finishProj (root : Expr) (n : Name) (i : Nat) (e : Expr)
  deriving Inhabited

unsafe def internExpr (params : List Name) (e0 : Expr) : StateT (PtrMap Expr Nat) PoolM Nat := do
  let root := stripMdata e0
  if let some id := (← get).find? root then
    return id
  let mut stack : Array InternWork := #[.visit root]
  while !stack.isEmpty do
    let item := stack.back!
    stack := stack.pop
    match item with
    | .visit raw =>
      let e := stripMdata raw
      if (← get).contains e then
        continue
      match e with
      | .bvar i =>
        let id ← liftM <| pushExpr (.bvar i) (node "bvar" #[toJson i])
        modify (·.insert e id)
      | .fvar _ => throw "free variable in exported expression"
      | .mvar _ => throw "unassigned metavariable in exported expression"
      | .lit (.natVal n) =>
        let id ← liftM <| pushExpr (.nat n) (node "nat" #[toJson n])
        modify (·.insert e id)
      | .lit (.strVal s) =>
        let id ← liftM <| pushExpr (.str s) (node "str" #[toJson s])
        modify (·.insert e id)
      | .sort u =>
        let uId ← liftM <| internLevel params u
        let id ← liftM <| pushExpr (.sort uId) (node "sort" #[toJson uId])
        modify (·.insert e id)
      | .const n us =>
        let uIds ← liftM <| us.mapM (internLevel params)
        let id ← liftM <| pushExpr (.const n.toString uIds) (node "const" #[nameRef n, toJson uIds])
        modify (·.insert e id)
      | .app f a =>
        let f' := stripMdata f
        let a' := stripMdata a
        stack := stack.push (.finishApp e f' a') |>.push (.visit a') |>.push (.visit f')
      | .lam _ t b bi =>
        let t' := stripMdata t
        let b' := stripMdata b
        stack := stack.push (.finishLam e bi t' b') |>.push (.visit b') |>.push (.visit t')
      | .forallE _ t b bi =>
        let t' := stripMdata t
        let b' := stripMdata b
        stack := stack.push (.finishForall e bi t' b') |>.push (.visit b') |>.push (.visit t')
      | .letE _ t v b nonDep =>
        let t' := stripMdata t
        let v' := stripMdata v
        let b' := stripMdata b
        stack := stack.push (.finishLet e nonDep t' v' b') |>.push (.visit b') |>.push (.visit v') |>.push (.visit t')
      | .proj n i s =>
        let s' := stripMdata s
        stack := stack.push (.finishProj e n i s') |>.push (.visit s')
      | .mdata _ _ => throw "unexpected mdata after stripMdata"
    | .finishApp nodeRoot f a =>
      if (← get).contains nodeRoot then continue
      let some fId := (← get).find? f | throw "internal internExpr error: missing app fn"
      let some aId := (← get).find? a | throw "internal internExpr error: missing app arg"
      let id ← liftM <| pushExpr (.app fId aId) (node "app" #[toJson fId, toJson aId])
      modify (·.insert nodeRoot id)
    | .finishLam nodeRoot bi t b =>
      if (← get).contains nodeRoot then continue
      let some tId := (← get).find? t | throw "internal internExpr error: missing lam type"
      let some bId := (← get).find? b | throw "internal internExpr error: missing lam body"
      let biStr := toString (reprStr bi)
      let id ← liftM <| pushExpr (.lam biStr tId bId) (node "lam" #[toJson biStr, toJson tId, toJson bId])
      modify (·.insert nodeRoot id)
    | .finishForall nodeRoot bi t b =>
      if (← get).contains nodeRoot then continue
      let some tId := (← get).find? t | throw "internal internExpr error: missing forall type"
      let some bId := (← get).find? b | throw "internal internExpr error: missing forall body"
      let biStr := toString (reprStr bi)
      let id ← liftM <| pushExpr (.forallE biStr tId bId) (node "forall" #[toJson biStr, toJson tId, toJson bId])
      modify (·.insert nodeRoot id)
    | .finishLet nodeRoot nonDep t v b =>
      if (← get).contains nodeRoot then continue
      let some tId := (← get).find? t | throw "internal internExpr error: missing let type"
      let some vId := (← get).find? v | throw "internal internExpr error: missing let val"
      let some bId := (← get).find? b | throw "internal internExpr error: missing let body"
      let id ← liftM <| pushExpr (.letE nonDep tId vId bId) (node "let" #[toJson nonDep, toJson tId, toJson vId, toJson bId])
      modify (·.insert nodeRoot id)
    | .finishProj nodeRoot n i s =>
      if (← get).contains nodeRoot then continue
      let some sId := (← get).find? s | throw "internal internExpr error: missing proj struct"
      let id ← liftM <| pushExpr (.proj n.toString i sId) (node "proj" #[nameRef n, toJson i, toJson sId])
      modify (·.insert nodeRoot id)
  let some res := (← get).find? root | throw "internal internExpr error: missing root"
  return res

unsafe def constantJson (c : ConstantInfo) : PoolM Json := do
  let p := c.levelParams
  let (res, _) ← StateT.run (m := PoolM) (s := mkPtrMap) do
    let typeId ← internExpr p c.type
    let payload ← match c with
      | .axiomInfo v => pure <| node "axiom" #[toJson v.isUnsafe]
      | .thmInfo _ => pure <| node "theorem"
      | .defnInfo v =>
        let valId ← internExpr p v.value
        pure <| node "definition" #[toJson (reprStr v.safety), toJson valId]
      | .opaqueInfo v =>
        let valId ← internExpr p v.value
        pure <| node "opaque" #[toJson v.isUnsafe, toJson valId]
      | .quotInfo _ => throw "unexpected local quotient primitive"
      | .inductInfo v => pure <| node "inductive" #[toJson v.numParams, toJson v.numIndices,
          toJson (v.all.map nameRef), toJson (v.ctors.map nameRef), toJson v.numNested,
          toJson v.isRec, toJson v.isUnsafe, toJson v.isReflexive]
      | .ctorInfo v => pure <| node "constructor" #[nameRef v.induct, toJson v.cidx,
          toJson v.numParams, toJson v.numFields, toJson v.isUnsafe]
      | .recInfo v =>
        let rules ← v.rules.mapM fun r => do
          let rhsId ← internExpr p r.rhs
          pure <| node "rule" #[nameRef r.ctor, toJson r.nfields, toJson rhsId]
        pure <| node "recursor" #[toJson (v.all.map nameRef), toJson v.numParams,
          toJson v.numIndices, toJson v.numMotives, toJson v.numMinors,
          toJson rules, toJson v.k, toJson v.isUnsafe]
    return Json.mkObj [("universes", toJson p.length), ("type", toJson typeId), ("payload", payload)]
  return res

def inlineJson (env : Environment) (n : Name) : Json :=
  toJson <| (Compiler.getInlineAttribute? env n).map fun
    | .inline => "inline" | .noinline => "noinline" | .macroInline => "macro_inline"
    | .inlineIfReduce => "inline_if_reduce" | .alwaysInline => "always_inline"

/-- Effective attributes outside the first tracked set that change elaboration
or compilation, gathered once per export from their extensions. Each entry is
keyed by the declaration it applies to. Orders that resolution uses are kept:
an instance's rank among this module's instances with the same discrimination
keys (Lean tries equal-priority instances latest first), and a default
instance's position in its class's list. -/
structure Extra where
  simps : NameMap (Array Json) := {}
  instanceRank : NameMap Nat := {}
  defaultInstances : NameMap (Array Json) := {}
  eliminators : NameMap (Array Json) := {}
  ext : NameMap (Array Json) := {}
  elaborators : NameMap (Array Json) := {}

def pushAt (m : NameMap (Array Json)) (n : Name) (j : Json) : NameMap (Array Json) :=
  m.insert n ((m.getD n #[]).push j)

def keyedEntries {γ : Type} (env : Environment) (label : String) (attr : KeyedDeclsAttribute γ)
    (acc : NameMap (Array Json)) : NameMap (Array Json) :=
  let st := attr.ext.getState env
  st.table.fold (fun acc key entries => entries.foldl (fun acc e =>
    if st.erased.contains e.declName then acc
    else pushAt acc e.declName (node label #[nameRef key])) acc) acc

unsafe def extraAttributes (env : Environment) (moduleIdx? : Option ModuleIdx := none) : Extra := Id.run do
  let simp := Meta.simpExtension.getState env
  let addSimp := fun (acc : NameMap (Array Json)) (t : Meta.SimpTheorem) =>
    match t.origin with
    | .decl name post inv =>
      if !simp.erased.contains t.origin then
        pushAt acc name (node "simp" #[toJson post, toJson inv, toJson t.priority,
          toJson t.perm, toJson t.rfl, toJson t.backwardRfl])
      else acc
    | _ => acc
  let simps := simp.post.foldValues addSimp (simp.pre.foldValues addSimp {})
  let mut ranks : NameMap Nat := {}
  let mut seen : Array (Array Meta.InstanceKey) := #[]
  let instEntries : List (ScopedEnvExtension.Entry Meta.InstanceEntry) := match moduleIdx? with
    | none => (Meta.instanceExtension.ext.getState env).newEntries.reverse
    | some idx => (Meta.instanceExtension.ext.getModuleEntries env idx).toList
  for entry in instEntries do
    let i := match entry with | .global i => i | .scoped _ i => i
    if let some n := i.globalName? then
      ranks := ranks.insert n (seen.filter (· == i.keys)).size
      seen := seen.push i.keys
  let mut defaults : NameMap (Array Json) := {}
  for (cls, insts) in (Meta.defaultInstanceExtension.getState env).defaultInstances.toList do
    for ((n, prio), i) in insts.reverse.zipIdx do
      defaults := pushAt defaults n (node "default_instance" #[nameRef cls, toJson prio, toJson i])
  let elims := (Meta.customEliminatorExt.getState env).map.fold (fun acc (induction, types) n =>
    pushAt acc n (node "eliminator" #[toJson induction, toJson (types.map nameRef)])) {}
  let extState := Meta.Ext.extExtension.getState env
  let exts := extState.tree.foldValues (fun acc (t : Meta.Ext.ExtTheorem) =>
    if extState.erased.contains t.declName then acc
    else pushAt acc t.declName (node "ext" #[toJson t.priority])) {}
  let elaborators := keyedEntries env "macro" Elab.macroAttribute <|
    keyedEntries env "term_elab" Elab.Term.termElabAttribute <|
    keyedEntries env "command_elab" Elab.Command.commandElabAttribute <|
    keyedEntries env "tactic" Elab.Tactic.tacticElabAttribute {}
  return { simps, instanceRank := ranks, defaultInstances := defaults, eliminators := elims, ext := exts,
           elaborators }

def sortedJson (xs : Array Json) : Json :=
  toJson (xs.qsort (fun a b => a.compress < b.compress))

def attributesJson (env : Environment) (extra : Extra) (n : Name) : Json := Id.run do
  let simp := Meta.simpExtension.getState env
  let inst := (Meta.instanceExtension.getState env).instanceNames.find? n
  let csimp := (Compiler.CSimp.ext.getState env).map.find? n
  return Json.mkObj [
    ("simp", toJson (extra.simps.getD n #[])),
    ("simp_unfold", toJson (simp.toUnfold.contains n)),
    ("simp_equations", toJson ((simp.toUnfoldThms.find? n).map (·.map nameRef))),
    ("csimp", toJson (Compiler.hasCSimpAttribute env n)),
    ("csimp_replacement", toJson (csimp.map fun e => #[nameRef e.toDeclName, nameRef e.thmName])),
    ("inline", inlineJson env n),
    ("reducibility", toJson (reprStr (getReducibilityStatusCore env n))),
    ("instance", toJson (inst.map fun i => node "instance" #[toJson i.priority,
      toJson i.synthOrder, toJson (match i.attrKind with | .global => "global" | .local => "local" | .scoped => "scoped"),
      toJson (extra.instanceRank.find? n)])),
    ("implemented_by", toJson ((Compiler.getImplementedBy? env n).map nameRef)),
    ("match_pattern", toJson (hasMatchPatternAttribute env n)),
    ("default_instance", sortedJson (extra.defaultInstances.getD n #[])),
    ("eliminator", sortedJson (extra.eliminators.getD n #[])),
    ("ext", sortedJson (extra.ext.getD n #[])),
    ("elaborator", sortedJson (extra.elaborators.getD n #[])),
    ("elab_as_elim", toJson (Elab.Term.elabAsElim.hasTag env n)),
    ("elab_without_expected_type", toJson (Elab.Term.hasElabWithoutExpectedType env n)),
    ("specialize", toJson (Compiler.getSpecializationArgs? env n)),
    ("nospecialize", toJson (Compiler.hasNospecializeAttribute env n)),
    ("never_extract", toJson (hasNeverExtractAttribute env n)),
    ("export", toJson ((getExportNameFor? env n).map (·.toString))),
    ("protected", toJson (isProtected env n)),
    ("noncomputable", toJson (isNoncomputable env n))]

/-- Deterministic equation-theorem provenance across both full elaboration and `--from-olean`
imports: `Meta.eqnsExt` is non-persistent across `.olean`, so computing it via Lean's own
`declFromEqLikeName` + `mkEqLikeNameFor` yields identical results in both modes. -/
def equationOriginOf (env : Environment) (n : Name) : Option Name :=
  match Meta.declFromEqLikeName env n with
  | some (declName, suffix) =>
    if Meta.isEqnReservedNameSuffix suffix && n == Meta.mkEqLikeNameFor env declName suffix then
      some declName
    else none
  | none => none

partial def syntaxJson : Syntax → Json
  | .missing => node "missing"
  | .atom _ val => node "atom" #[toJson val]
  | s@(.ident _ _ val _) => node "ident" #[toJson val.toString,
      toJson (s.getPos?.map (·.byteIdx)), toJson (s.getTailPos?.map (·.byteIdx))]
  | .node _ kind args => node "syntax" #[toJson kind.toString, toJson (args.map syntaxJson)]

partial def guardTerms (s : Syntax) : Array Syntax :=
  if s.isOfKind ``Parser.Command.guardCmd then #[s[1]]
  else s.getArgs.foldl (fun acc child => acc ++ guardTerms child) #[]

partial def attributeNodes (s : Syntax) : Array Syntax :=
  if s.isOfKind ``Parser.Term.attributes || s.isOfKind ``Parser.Command.attribute then #[s]
  else s.getArgs.foldl (fun acc child => acc ++ attributeNodes child) #[]

def samePlace (a b : Syntax) : Bool :=
  a.getPos? == b.getPos? && a.getTailPos? == b.getTailPos?

/-- The declaration an attribute list on `decl` (a `declaration`'s second
argument) attaches to: its `declId`, or, for a declaration Lean names itself
(an anonymous `instance`), the keyword range Lean records as its definition. -/
def declarationTarget (decl : Syntax) : Json :=
  let id := decl.getArgs.findSome? fun a =>
    if a.isOfKind ``Parser.Command.declId then some a
    else a.getArgs.find? (·.isOfKind ``Parser.Command.declId)
  match id with
  | some id => syntaxJson id[0]
  | none =>
    match decl.getArgs.find? (fun a => a.isAtom && a.getAtomVal == "instance") with
    | some kw => node "declTarget" #[toJson (kw.getPos?.map (·.byteIdx)), toJson (kw.getTailPos?.map (·.byteIdx))]
    | none => node "anonymousDeclaration" #[toJson decl.getKind.toString]

/-- Explicit attributes per declaration (a `mutual` block or two anonymous
instances can no longer trade them), then any other attribute syntax of the
command (`attribute [...]` commands, nested positions) with the command's
declaration names. Never the declaration body. -/
def commandAttributes (command : Syntax) : Array Json := Id.run do
  let mut out : Array Json := #[]
  let mut handled : Array Syntax := #[]
  for decl in NamingReferences.syntaxNodes ``Parser.Command.declaration command do
    let attrs := attributeNodes decl[0][1]
    unless attrs.isEmpty do
      handled := handled ++ attrs
      out := out.push (node "declarationAttributes" #[declarationTarget decl[1], toJson (attrs.map syntaxJson)])
  let rest := (attributeNodes command).filter fun a => !handled.any (samePlace a)
  unless rest.isEmpty do
    let ids := (NamingReferences.syntaxNodes ``Lean.Parser.Command.declId command).map (syntaxJson ·[0])
    out := out.push (node "attributeCommand" #[toJson ids, toJson (rest.map syntaxJson)])
  return out

partial def firstAtom (s : Syntax) : Option String :=
  match s with
  | .atom _ value => some value
  | _ => s.getArgs.foldl (fun found child => found.orElse (fun _ => firstAtom child)) none

/-- These commands have no closed result expression. Preserve their complete
syntax, including expected diagnostics and options, rather than ignoring them. -/
def auditCommand (s : Syntax) : Bool :=
  (firstAtom s).any (fun a => a.trimAscii.toString == "#expect_axioms" || a.trimAscii.toString == "#union_axioms_of_modules")

def checkedCommand (s : Syntax) : Bool :=
  s.isOfKind ``Lean.guardMsgsCmd || s.isOfKind ``Lean.runCmd || auditCommand s ||
    (firstAtom s).any (fun a => #["#eval", "#eval!", "#count_heartbeats"].contains a.trimAscii.toString)

def unsupportedCommand (s : Syntax) : Bool :=
  !s.isOfKind ``Parser.Command.guardCmd && !checkedCommand s &&
    (firstAtom s).any (·.startsWith "#")

def within (outer inner : Syntax) : Bool :=
  match outer.getPos?, outer.getTailPos?, inner.getPos?, inner.getTailPos? with
  | some a, some b, some c, some d => a <= c && d <= b
  | _, _, _, _ => false

partial def checkedCommands (s : Syntax) : Array Syntax :=
  if checkedCommand s then #[s]
  else s.getArgs.foldl (fun acc child => acc ++ checkedCommands child) #[]

unsafe def guardJson (trees : Array InfoTree) (term : Syntax) : StateT PoolState IO Json := do
  let mut candidates : Array Json := #[]
  let mut provenance : Array Json := #[]
  let mut pool ← get
  for tree in trees do
    let mut treeCands : Array (Json × Json) := #[]
    let found ← tree.collectTermInfoM fun ctx info => do
      -- Macro-generated branches can inherit the entire guard span. Only the
      -- original syntax node denotes the complete guarded expression.
      if info.stx != term then
        return none
      ctx.runMetaM info.lctx do
        let e ← instantiateMVars info.expr
        let type ← Meta.inferType e
        let tag ← if type == mkConst ``Bool then pure "guardBool"
          else if ← Meta.isProp e then pure "guardProp"
          else return none
        return some (tag, e, Json.mkObj [
            ("syntax_kind", toJson info.stx.getKind.toString),
            ("exact_syntax", toJson (info.stx == term)),
            ("elaborator", toJson info.elaborator.toString)])
    for (tag, e, prov) in found do
      let (res, nextPool) := (((internExpr [] e).run mkPtrMap).run.run pool)
      match res with
      | .ok (exprId, _) =>
        pool := nextPool
        treeCands := treeCands.push (node tag #[toJson exprId], prov)
      | .error message =>
        throw <| IO.userError s!"guard export: {message}"
    candidates := candidates ++ treeCands.map Prod.fst
    provenance := provenance ++ treeCands.map Prod.snd
  set pool
  let some first := candidates[0]?
    | throw <| IO.userError s!"guard has no closed Bool/Prop expression at byte range {reprStr (term.getPos?.map (·.byteIdx))}..{reprStr (term.getTailPos?.map (·.byteIdx))}"
  unless candidates.all (· == first) do
    throw <| IO.userError s!"ambiguous guard expression at byte range {reprStr (term.getPos?.map (·.byteIdx))}..{reprStr (term.getTailPos?.map (·.byteIdx))}; {candidates.size} candidates: {toJson candidates}; provenance: {toJson provenance}"
  return first

def oleanArtifactParts (cwd : System.FilePath) (name : Name) : IO Json := do
  let olean ← findOLean name
  let olean := if olean.isAbsolute then olean else cwd / olean
  let parts ← #["olean", "olean.server", "olean.private", "ir.sig", "ir"].mapM fun ext => do
    let path := olean.withExtension ext
    let present ← path.pathExists
    pure (ext, if present then toJson path.toString else Json.null)
  return Json.mkObj parts.toList

/-- All transitive imports actually loaded by this frontend. Record every
possible data/IR part, including absence, so capture can bind the resolved
artifacts before and after elaboration. Lean 4.35 imports these five parts. -/
def importArtifacts (env : Environment) (exclude? : Option Name := none) : IO Json := do
  let cwd ← IO.currentDir
  let names := env.header.moduleNames.filter (fun n => exclude? != some n)
  let modules ← names.mapM fun name => do
    pure (name.toString, ← oleanArtifactParts cwd name)
  return Json.mkObj modules.toList

def importModuleNamesJson (env : Environment) (exclude? : Option Name := none) : Json :=
  let names := (env.header.moduleNames.filter (fun n => exclude? != some n)).map (·.toString)
  toJson (names.qsort (· < ·))

def parseModuleName (moduleName : String) : Name :=
  (moduleName.splitOn ".").foldl Name.str .anonymous

private partial def computeTrans (deps : Std.HashMap Name (Array Name)) (tc : Std.HashMap Name (Array Name))
    (mod : Name) : Std.HashMap Name (Array Name) × Array Name :=
  if let some cached := tc[mod]? then
    (tc, cached)
  else Id.run do
    let mut tc := tc
    let mut acc : Array Name := #[mod]
    let mut seen : NameSet := NameSet.empty.insert mod
    for d in deps[mod]! do
      let (tc', sub) := computeTrans deps tc d
      tc := tc'
      for s in sub do
        if !seen.contains s then
          seen := seen.insert s
          acc := acc.push s
    return (tc.insert mod acc, acc)

/-- Resolve all transitive import artifacts once across a batch of candidate modules
using `.olean` / `.olean.private` headers without re-elaborating any module. -/
unsafe def importsBatch (input output : String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let entries ← IO.ofExcept (fromJson? json : Except String (Array (String × String)))
  let cwd ← IO.currentDir
  let mut artsCache : Std.HashMap Name Json := {}
  let mut depsCache : Std.HashMap Name (Array Name) := {}
  let mut transCache : Std.HashMap Name (Array Name) := {}
  let mut regions : Array CompactedRegion := #[]
  let ensureModuleDeps (arts : Std.HashMap Name Json) (deps : Std.HashMap Name (Array Name))
      (regs : Array CompactedRegion) (start : Name) :
      IO (Std.HashMap Name Json × Std.HashMap Name (Array Name) × Array CompactedRegion) := do
    let mut arts := arts
    let mut deps := deps
    let mut regs := regs
    let mut work : Array Name := #[start]
    while !work.isEmpty do
      let mod := work.back!
      work := work.pop
      if deps.contains mod then
        continue
      let olean ← findOLean mod
      let oleanAbs := if olean.isAbsolute then olean else cwd / olean
      let parts ← #["olean", "olean.server", "olean.private", "ir.sig", "ir"].mapM fun ext => do
        let path := oleanAbs.withExtension ext
        let present ← path.pathExists
        pure (ext, if present then toJson path.toString else Json.null)
      arts := arts.insert mod (Json.mkObj parts.toList)
      let main ← unsafe CompactedRegion.read (α := ModuleData) oleanAbs #[]
      regs := regs.push main.2
      let mut mdata := main.1
      if main.1.isModule then
        let sFile := OLeanLevel.server.adjustFileName oleanAbs
        let pFile := OLeanLevel.private.adjustFileName oleanAbs
        let mut depRegs := #[main.2]
        if (← sFile.pathExists) then
          let srv ← unsafe CompactedRegion.read (α := ModuleData) sFile depRegs
          regs := regs.push srv.2
          depRegs := depRegs.push srv.2
          mdata := srv.1
        if (← pFile.pathExists) then
          let prv ← unsafe CompactedRegion.read (α := ModuleData) pFile depRegs
          regs := regs.push prv.2
          mdata := prv.1
      let modDeps := mdata.imports.map (·.module)
      deps := deps.insert mod modDeps
      for d in modDeps do
        if !deps.contains d then
          work := work.push d
    return (arts, deps, regs)
  let mut modRows : Array (String × Json) := #[]
  for (moduleName, source) in entries do
    let text ← IO.FS.readFile source
    let ctx := Parser.mkInputContext text source
    let (header, _, messages) ← Parser.parseHeader ctx
    if messages.hasErrors then
      for message in messages.toList do IO.eprintln (← message.toString)
      throw <| IO.userError s!"invalid module header: {source}"
    let directInfo := Lean.Server.collectImports header
    let directNames := (Elab.HeaderSyntax.imports header).map (·.module)
    for d in directNames do
      let (a', d', r') ← ensureModuleDeps artsCache depsCache regions d
      artsCache := a'
      depsCache := d'
      regions := r'
    let mut visited : NameSet := {}
    let mut transNames : Array String := #[]
    for d in directNames do
      let (tc', sub) := computeTrans depsCache transCache d
      transCache := tc'
      for m in sub do
        if !visited.contains m then
          visited := visited.insert m
          transNames := transNames.push m.toString
    modRows := modRows.push (moduleName, Json.mkObj [
      ("direct_imports", toJson directInfo),
      ("import_modules", toJson (transNames.qsort (· < ·)))
    ])
  let _ := regions.size
  let artsList := artsCache.fold (init := []) fun acc n j => (n.toString, j) :: acc
  let outJson := Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("lean_version", toJson Lean.versionString),
    ("artifacts", Json.mkObj artsList),
    ("modules", Json.mkObj modRows.toList)
  ]
  IO.FS.writeFile output outJson.compress

/-- Parse every candidate header with Lean itself, including modules outside
an eventual export set. No imported module or source body is elaborated here. -/
def headerInventory (input output : String) : IO Unit := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let entries ← IO.ofExcept (fromJson? json : Except String (Array (String × String)))
  let modules ← entries.mapM fun (moduleName, source) => do
    let text ← IO.FS.readFile source
    let ctx := Parser.mkInputContext text source
    let (header, _, messages) ← Parser.parseHeader ctx
    if messages.hasErrors then
      for message in messages.toList do IO.eprintln (← message.toString)
      throw <| IO.userError s!"invalid module header: {source}"
    pure (moduleName, Json.mkObj [("path", toJson source), ("is_module", toJson (HeaderSyntax.isModule header)),
      ("direct_imports", toJson (Lean.Server.collectImports header))])
  IO.FS.writeFile output (Json.mkObj [("schema_version", toJson (1 : Nat)),
    ("lean_version", toJson Lean.versionString), ("modules", Json.mkObj modules.toList)]).compress

def writeResolvedOut (path : Option String) (moduleName : String) (header : HeaderSyntax)
    (env : Environment) (ownArtifacts : Json := Json.null) (ileanPath : Json := Json.null)
    (exclude? : Option Name := none) : IO Unit := do
  let some path := path | return ()
  let imports ← importArtifacts env exclude?
  let payload := Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("module", toJson moduleName),
    ("lean_version", toJson Lean.versionString),
    ("direct_imports", toJson (Lean.Server.collectImports header)),
    ("imports", imports),
    ("own_artifacts", ownArtifacts),
    ("ilean", ileanPath)
  ]
  IO.FS.writeFile path payload.compress

/-- Core Lean command kinds allowed by `--from-olean`. Anything else (macros, syntax
declarations, `#guard`, `#eval`, `#expect_axioms`, `run_cmd`, `openPrivate`, custom
command macros) returns exit 3 and runs full elaboration. -/
def coreCommandKinds : Array SyntaxNodeKind := #[
  ``Parser.Command.declaration,
  ``Parser.Command.namespace,
  ``Parser.Command.end,
  ``Parser.Command.section,
  ``Parser.Command.open,
  ``Parser.Command.variable,
  ``Parser.Command.set_option,
  ``Parser.Command.universe,
  ``Parser.Command.export,
  ``Parser.Command.attribute,
  ``Parser.Command.deriving,
  ``Parser.Command.include,
  ``Parser.Command.omit,
  ``Parser.Command.moduleDoc,
  ``Parser.Command.eoi,
  `lemma
]

partial def hasCommandForbiddenSyntax (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Command.openScoped ||
  stx.isOfKind ``Parser.Command.eraseAttr ||
  stx.isOfKind ``Parser.Term.«scoped» ||
  stx.getArgs.any hasCommandForbiddenSyntax

partial def hasForbiddenSyntax (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Command.openScoped ||
  stx.isOfKind ``Parser.Command.eraseAttr ||
  stx.isOfKind ``Parser.Term.«local» ||
  stx.isOfKind ``Parser.Term.«scoped» ||
  (stx.isOfKind ``Parser.Term.attrKind && !stx[0].isNone) ||
  stx.getArgs.any hasForbiddenSyntax

def isLocalAttrKindStx (attrKind : Syntax) : Bool :=
  match attrKind with
  | `(Parser.Term.attrKind| local) => true
  | _ => false

def isAllowedTacticAttrKind (attrKind : Syntax) : Bool :=
  attrKind.isOfKind ``Parser.Term.attrKind &&
    (attrKind[0].isNone || isLocalAttrKindStx attrKind)

def isTacticQuotation (pat : Syntax) : Bool :=
  pat.isQuot &&
    (pat.getKind == ``Parser.Tactic.quot || pat.getKind == ``Parser.Tactic.quotSeq ||
      (pat.getNumArgs > 0 && pat[0].isAtom && pat[0].getAtomVal == "`(tactic|"))

def isTacticOnlyMetaCommand (cmd : Syntax) : Bool :=
  if !(guardTerms cmd).isEmpty || !(checkedCommands cmd).isEmpty ||
      unsupportedCommand cmd || hasCommandForbiddenSyntax cmd then
    false
  else match cmd with
  | `($[$_doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind syntax$[:$_prec?]? $[(name := $_name?)]? $[(priority := $_prio?)]? $[$_ps:stx]* : $cat) =>
    attrs?.isNone && isAllowedTacticAttrKind attrKind && cat.getId.eraseMacroScopes == `tactic
  | `($[$_doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind macro$[:$_prec?]? $[(name := $_name?)]? $[(priority := $_prio?)]? $_args:macroArg* : $cat => $_) =>
    attrs?.isNone && isAllowedTacticAttrKind attrKind && cat.getId.eraseMacroScopes == `tactic
  | `($[$_doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind elab$[:$_prec?]? $[(name := $_name?)]? $[(priority := $_prio?)]? $_args:macroArg* : $cat $[<= $_expty?]? => $_) =>
    attrs?.isNone && isAllowedTacticAttrKind attrKind && cat.getId.eraseMacroScopes == `tactic
  | `($[$_doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind macro_rules $[(kind := $kind?)]? $alts:matchAlt*) =>
    attrs?.isNone && isAllowedTacticAttrKind attrKind && kind?.isNone &&
      !alts.isEmpty && alts.all fun alt => match alt with
        | `(Parser.Term.matchAltExpr| | $pats,* => $_) =>
          let elems := pats.getElems
          !elems.isEmpty && elems.all fun pat => isTacticQuotation pat.raw
        | _ => false
  | `($[$_doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind elab_rules $[(kind := $kind?)]? : $cat $[<= $_expty?]? $alts:matchAlt*) =>
    attrs?.isNone && isAllowedTacticAttrKind attrKind && kind?.isNone &&
      cat.getId.eraseMacroScopes == `tactic && !alts.isEmpty
  | _ => false

private def tacticSyntaxItemParser (first : Bool) (stx : Syntax) : Option (Parser.Parser × Option String) :=
  let kind := stx.getKind
  if kind == ``Parser.Syntax.atom then
    match stx[0].isStrLit? with
    | some tk =>
      if first then
        some (Parser.nonReservedSymbol tk false, none)
      else
        let trimmed := tk.trimAscii.copy
        some (Parser.symbol tk, if trimmed.isEmpty then none else some trimmed)
    | none => none
  else if kind == ``Parser.Syntax.nonReserved then
    match stx[1].isStrLit? with
    | some tk => some (Parser.nonReservedSymbol tk false, none)
    | none => none
  else if kind == ``Parser.Syntax.cat && !first then
    match stx[0].getId.eraseMacroScopes with
    | `ident => some (Parser.ident, none)
    | `term => some (Parser.termParser, none)
    | `tactic => some (Parser.categoryParser `tactic 0, none)
    | `num => some (Parser.numLit, none)
    | `str => some (Parser.strLit, none)
    | _ => none
  else
    none

partial def registerLocalTacticParser (env : Environment) (cmd : Syntax) (counter : Nat) : Environment :=
  if cmd.isOfKind ``Parser.Command.in then
    registerLocalTacticParser env cmd[2] counter
  else if !isTacticOnlyMetaCommand cmd then
    env
  else
    let (attrKind?, itemStxs?) : Option Syntax × Option (Array Syntax) := match cmd with
      | `($[$_doc?:docComment]? $attrKind:attrKind syntax$[:$_prec?]? $[(name := $_name?)]? $[(priority := $_prio?)]? $[$ps:stx]* : $_cat) =>
        (some attrKind, some (ps.map (·.raw)))
      | `($[$_doc?:docComment]? $attrKind:attrKind macro$[:$_prec?]? $[(name := $_name?)]? $[(priority := $_prio?)]? $args:macroArg* : $_cat => $_) =>
        (some attrKind, some (args.map (·.raw[1])))
      | `($[$_doc?:docComment]? $attrKind:attrKind elab$[:$_prec?]? $[(name := $_name?)]? $[(priority := $_prio?)]? $args:macroArg* : $_cat $[<= $_expty?]? => $_) =>
        (some attrKind, some (args.map (·.raw[1])))
      | _ => (none, none)
    match attrKind?, itemStxs? with
    | some attrKind, some items =>
      if !isLocalAttrKindStx attrKind || items.isEmpty then
        env
      else
        Id.run do
          let mut built : Array Parser.Parser := #[]
          let mut tokens : Array String := #[]
          for i in [0:items.size] do
            match tacticSyntaxItemParser (i == 0) items[i]! with
            | some (p, tk?) =>
              built := built.push p
              if let some tk := tk? then
                tokens := tokens.push tk
            | none => return env
          let mut combined := built[0]!
          for p in built.extract 1 built.size do
            combined := Parser.andthen combined p
          let declName := Name.mkSimple s!"_localTactic_{counter}"
          let p := Parser.leadingNode declName 1022 combined
          let mut nextEnv := env
          for tk in tokens do
            nextEnv := Parser.parserExtension.addEntry nextEnv (.token tk)
          return Parser.parserExtension.addEntry nextEnv (.parser `tactic declName true p 1022)
    | _, _ => env

partial def allowOleanCommand (cmd : Syntax) : Bool :=
  if !(guardTerms cmd).isEmpty || !(checkedCommands cmd).isEmpty || unsupportedCommand cmd then
    false
  else if cmd.isOfKind ``Parser.Command.in then
    allowOleanCommand cmd[0] && allowOleanCommand cmd[2]
  else if cmd.isOfKind ``Parser.Command.mutual then
    cmd[1].getArgs.all allowOleanCommand
  else if isTacticOnlyMetaCommand cmd then
    true
  else if hasForbiddenSyntax cmd then
    false
  else
    coreCommandKinds.contains cmd.getKind

def hasScopedCommandParser (scopedParsers : SMap Name (PArray Parser.ParserExtension.Entry)) (ns : Name) : Bool :=
  match scopedParsers.find? ns with
  | none => false
  | some entries => entries.any fun
      | .parser cat .. => cat == `command || cat == `attr
      | .category .. => true
      | _ => false

partial def hasScopedParserActivation (env : Environment)
    (scopedParsers : SMap Name (PArray Parser.ParserExtension.Entry))
    (stack : Array NamingReferences.Frame) (cmd : Syntax) : Bool := Id.run do
  let top := stack.back?.getD {}
  if cmd.isOfKind ``Parser.Command.in then
    if hasScopedParserActivation env scopedParsers stack cmd[0] then
      return true
    let (inner, _) := NamingReferences.scopeCommand env (stack.push top) cmd[0]
    return hasScopedParserActivation env scopedParsers (if inner.isEmpty then #[{}] else inner) cmd[2]
  if cmd.isOfKind ``Parser.Command.namespace then
    let mut ns := top.ns
    for comp in cmd[1].getId.components do
      ns := ns ++ comp
      if hasScopedCommandParser scopedParsers ns then
        return true
  for decl in NamingReferences.nestedOpenDecls cmd do
    if decl.isOfKind ``Parser.Command.openScoped then
      return true
    if decl.isOfKind ``Parser.Command.openSimple then
      for id in decl[0].getArgs do
        let cands := ResolveName.resolveNamespace env top.ns top.opens id.getId
        if cands.any (hasScopedCommandParser scopedParsers) then
          return true
    else if let some id := decl[0]? then
      let cands := ResolveName.resolveNamespace env top.ns top.opens id.getId
      if cands.any (hasScopedCommandParser scopedParsers) then
        return true
  return false

unsafe def emitOneConstant (env : Environment) (extra : Extra) (name : Name)
    : ExceptT String (StateT PoolState IO) (String × Json) := do
  let kernel := env.toKernelEnv
  let some info := kernel.find? name
    | throw s!"constant absent from checked kernel environment: {name}"
  let data ← match constantJson info |>.run (← get) with
    | (.ok d, nextPool) => set nextPool; pure d
    | (.error err, _) => throw err
  let equationOrigin := equationOriginOf env info.name
  return (info.name.toString, Json.mkObj [
    ("kernel", data), ("attributes", attributesJson env extra info.name),
    ("equation_origin", toJson (equationOrigin.map nameRef))])

unsafe def runFromOlean (source moduleName ileanPath output : String) (resolvedOut? : Option String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile source
  let inputCtx := Parser.mkInputContext input source
  let options := ({} : Options).setBool `Elab.async false
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors || HeaderSyntax.isModule header then
    return 3
  let modName := parseModuleName moduleName
  let env ← try
    importModules #[{ module := modName, importAll := true }] options (loadExts := true)
  catch _ =>
    return 3
  let some idx := env.getModuleIdx? modName | return 3
  let mdata := env.header.moduleData[idx]!
  if mdata.isModule then
    return 3
  let hdrImports := (Elab.HeaderSyntax.imports header).map fun i => (i.module, i.isMeta, i.isExported, i.importAll)
  let modImports := mdata.imports.map fun i => (i.module, i.isMeta, i.isExported, i.importAll)
  if hdrImports != modImports then
    return 3
  let tacticCatKinds : Parser.SyntaxNodeKindSet := match (Parser.parserExtension.getState env).categories.find? `tactic with
    | some (cat : Parser.ParserCategory) => cat.kinds
    | none => {}
  if (Parser.parserExtension.ext.getModuleEntries env idx).any (fun
        | .global (.parser cat _ _) => cat != `tactic
        | .global (.category _ _ _) => true
        | .global _ => false
        | .scoped _ _ => true) ||
      !(Elab.Command.commandElabAttribute.ext.ext.getModuleEntries env idx).isEmpty ||
      !(Elab.Term.termElabAttribute.ext.ext.getModuleEntries env idx).isEmpty ||
      !(Elab.macroAttribute.ext.ext.getModuleEntries env idx).all (fun
        | .global e => tacticCatKinds.contains e.key
        | .scoped _ _ => false) then
    return 3
  let scopedParsers := (Parser.parserExtension.ext.getState env).scopedEntries.map
  let mut parseEnv := env
  let mut pstate := parserState
  let mut msgs := messages
  let mut stack : Array NamingReferences.Frame := #[{}]
  let mut cmds : Array Syntax := #[]
  repeat
    let top := stack.back?.getD {}
    let pmctx : Parser.ParserModuleContext := {
      env := parseEnv
      options := {}
      currNamespace := top.ns
      openDecls := top.opens
    }
    let (cmd, nextPs, nextMsgs) := Parser.parseCommand inputCtx pmctx pstate msgs
    pstate := nextPs
    msgs := nextMsgs
    if msgs.hasErrors then
      return 3
    if Parser.isTerminalCommand cmd then
      unless cmd.isOfKind ``Parser.Command.eoi do
        return 3
      cmds := cmds.push cmd
      break
    if !allowOleanCommand cmd || hasScopedParserActivation env scopedParsers stack cmd then
      return 3
    parseEnv := registerLocalTacticParser parseEnv cmd cmds.size
    cmds := cmds.push cmd
    let (nextStack, _) := NamingReferences.scopeCommand env stack cmd
    stack := if nextStack.isEmpty then #[{}] else nextStack
  let ilean ← try
    Lean.Server.Ilean.load ileanPath
  catch _ =>
    return 3
  if ilean.module != modName ||
      (toJson ilean.directImports).compress != (toJson (Lean.Server.collectImports header)).compress then
    return 3
  let cwd ← IO.currentDir
  let ownArts ← oleanArtifactParts cwd modName
  let ileanAbs := if (System.FilePath.mk ileanPath).isAbsolute then ileanPath else (cwd / ileanPath).toString
  writeResolvedOut resolvedOut? moduleName header env ownArts (toJson ileanAbs) (some modName)
  let mut attrs : Array Json := #[]
  for command in cmds do
    attrs := attrs ++ commandAttributes command
  let extra := extraAttributes env (some idx)
  let mut pool : PoolState := {}
  let mut constants : List (String × Json) := []
  for c in mdata.constants do
    let (res, nextPool) ← (emitOneConstant env extra c.name).run.run pool
    pool := nextPool
    match res with
    | .ok pair => constants := pair :: constants
    | .error err => throw <| IO.userError err
  let json := Json.mkObj [
    ("schema_version", toJson (8 : Nat)),
    ("lean_version", toJson Lean.versionString),
    ("import_modules", importModuleNamesJson env (some modName)),
    ("source", toJson input),
    ("level_pool", toJson pool.levelPool),
    ("expr_pool", toJson pool.exprPool),
    ("index", NamingReferences.indexJson ilean cmds (NamingReferences.syntaxExtrasOlean env header.raw cmds)),
    ("constants", Json.mkObj constants),
    ("guards", toJson (#[] : Array Json)),
    ("attribute_syntax", toJson attrs),
    ("checked_commands", toJson (#[] : Array Json))
  ]
  IO.FS.writeFile output json.compress
  IO.println s!"OK — naming fidelity (from-olean): {constants.length} constants, 0 guards"
  return 0

end NamingFidelity

open NamingFidelity

def parseResolvedArg : List String → Except String (Option String × List String)
  | "--resolved-out" :: path :: rest => pure (some path, rest)
  | ["--resolved-out"] => throw "missing path after --resolved-out"
  | x :: rest => do
    let (r, rs) ← parseResolvedArg rest
    pure (r, x :: rs)
  | [] => pure (none, [])

unsafe def main (args : List String) : IO UInt32 := do
  if let ["--headers", input, output] := args then
    headerInventory input output
    return 0
  if let ["--imports-batch", input, output] := args then
    importsBatch input output
    return 0
  let (resolvedOut?, args) ← match parseResolvedArg args with
    | .ok v => pure v
    | .error err => IO.eprintln err; return 2
  if let ["--from-olean", source, moduleName, ileanPath, output] := args then
    return ← runFromOlean source moduleName ileanPath output resolvedOut?
  let (importsOnly, rest) := match args with
    | "--imports" :: rest => (true, rest)
    | rest => (false, rest)
  let [source, moduleName, output] := rest
    | IO.eprintln "usage: jaune-naming-fidelity [--imports|--from-olean|--headers|--imports-batch] ... [--resolved-out PATH]"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile source
  let inputCtx := Parser.mkInputContext input source
  let options := ({} : Options).setBool `Elab.async false
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header options messages inputCtx (mainModule := parseModuleName moduleName)
  if messages.hasErrors then
    for message in messages.toList do IO.eprintln (← message.toString)
    return 1
  if importsOnly then
    let imports ← importArtifacts env
    IO.FS.writeFile output (Json.mkObj [
      ("schema_version", toJson (1 : Nat)), ("module", toJson moduleName),
      ("lean_version", toJson Lean.versionString),
      ("direct_imports", toJson (Lean.Server.collectImports header)),
      ("imports", imports)]).compress
    return 0
  writeResolvedOut resolvedOut? moduleName header env
  let state := { Command.mkState env messages options with infoState.enabled := true }
  let result ← IO.processCommands inputCtx parserState state
  if result.commandState.messages.hasErrors then
    for message in result.commandState.messages.toList do IO.eprintln (← message.toString)
    return 1
  let env := result.commandState.env
  let trees := result.commandState.infoState.trees.toArray
  let refs := Lean.Server.findModuleRefs inputCtx.fileMap trees (localVars := true)
  let (refs, caseRows) := NamingReferences.caseReferences trees inputCtx.fileMap refs
  let refs := NamingReferences.addAuditReferences
    result.commandState.infoState.trees.toArray inputCtx.fileMap refs
  let (references, decls) ← refs.toLspModuleRefs
  let index : Lean.Server.Ilean := {
    module := parseModuleName moduleName
    directImports := Lean.Server.collectImports header
    references, decls }
  let mut checks : Array Syntax := #[]
  for command in result.commands do
    checks := checks ++ checkedCommands command
  -- A command introduced by a macro may not occur in the original parse tree.
  for tree in trees do
    let expanded := tree.foldInfo (fun _ info acc => match info with
      | .ofCommandInfo ci => if checkedCommand ci.stx then acc.push ci.stx else acc
      | _ => acc) (#[] : Array Syntax)
    for command in expanded do
      unless checks.any (fun outer => within outer command) do checks := checks.push command
  let guarded := checks.filter (·.isOfKind ``Lean.guardMsgsCmd)
  -- Preserve the invocation as well as expanded checks. Two equal checks may
  -- share a macro's source span; their invocation arguments must not disappear.
  -- This also retains set_option/namespace wrappers around checked commands.
  for command in result.commands do
    if checks.any (fun inner => within command inner) && !checks.contains command then
      checks := checks.push command
  let mut terms : Array Syntax := #[]
  let mut attrs : Array Json := #[]
  for command in result.commands do
    if unsupportedCommand command then
      throw <| IO.userError "unsupported hash command: command has no registered fidelity representation"
    -- The attributes and the declaration each attaches to, never the body:
    -- theorem proofs are not compared, and a proof edit inside an attributed
    -- theorem is not an attribute change.
    attrs := attrs ++ commandAttributes command
    terms := terms ++ guardTerms command
  for tree in trees do
    let unsupported := tree.foldInfo (fun _ info found => found || match info with
      | .ofCommandInfo ci => unsupportedCommand ci.stx
      | _ => false) false
    if unsupported then
      throw <| IO.userError "unsupported expanded hash command"
    let expanded := tree.foldInfo (fun _ info acc => match info with
      | .ofCommandInfo ci => acc ++ guardTerms ci.stx
      | _ => acc) (#[] : Array Syntax)
    for term in expanded do
      unless terms.contains term do terms := terms.push term
  -- Expected failures can leave open or erroneous terms in info trees. Their
  -- enclosing message check is compared in full syntax, not as a true guard.
  terms := terms.filter fun term => !guarded.any (fun outer => within outer term)
  let extra := extraAttributes env none
  let (guards, pool) ← (terms.mapM (guardJson trees)).run {}
  let mut pool := pool
  let mut constants : List (String × Json) := []
  for c in (← env.getLocalConstantInfos) do
    let (res, nextPool) ← (emitOneConstant env extra c.name).run.run pool
    pool := nextPool
    match res with
    | .ok pair => constants := pair :: constants
    | .error err => throw <| IO.userError err
  let checksJson := checks.map fun command => Json.mkObj [
    ("syntax", syntaxJson command),
    ("literal_names", toJson (auditCommand command)),
    ("start", toJson (command.getPos?.map (·.byteIdx))),
    ("end", toJson (command.getTailPos?.map (·.byteIdx))),
    ("expected_failure_scope", toJson (command.isOfKind ``Lean.guardMsgsCmd))]
  let json := Json.mkObj [
    ("schema_version", toJson (8 : Nat)),
    ("lean_version", toJson Lean.versionString),
    ("import_modules", importModuleNamesJson env none),
    ("source", toJson input),
    ("level_pool", toJson pool.levelPool),
    ("expr_pool", toJson pool.exprPool),
    ("index", NamingReferences.indexJson index result.commands
      (NamingReferences.syntaxExtras env header.raw trees result.commands caseRows)),
    ("constants", Json.mkObj constants),
    ("guards", toJson guards),
    ("attribute_syntax", toJson attrs),
    ("checked_commands", toJson checksJson)]
  IO.FS.writeFile output json.compress
  IO.println s!"OK — naming fidelity: {constants.length} constants, {guards.size} guards"
  return 0
