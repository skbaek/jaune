import Lean

/-! Shared compiler provenance for migration reference and fidelity exports.
This optional tool library is outside the production import closure. -/

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

/-- Constructors whose `casesOn` minor premise leads to `target`. The minor's
position in the eliminator application is the compiler's own constructor
identity; the goal's type need not mention the constructor. -/
partial def minorCtors (env : Environment) (ctx : MetavarContext) (target : MVarId)
    (e : Expr) : StateM (Array MVarId) (Array Name) := do
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let mut found : Array Name := #[]
    if let .const n _ := fn then
      if isCasesOnRecursor env n then
        if let some (.inductInfo ind) := env.find? n.getPrefix then
          let first := ind.numParams + 1 + ind.numIndices + 1
          for i in [0:ind.ctors.length] do
            if let some minor := args[first + i]? then
              if (minor.collectMVars {}).result.any (descends ctx · target) then
                found := found.push ind.ctors[i]!
    unless fn.isConst do found := found ++ (← minorCtors env ctx target fn)
    for arg in args do found := found ++ (← minorCtors env ctx target arg)
    return found
  | .lam _ t b _ | .forallE _ t b _ =>
    return (← minorCtors env ctx target t) ++ (← minorCtors env ctx target b)
  | .letE _ t v b _ =>
    return (← minorCtors env ctx target t) ++ (← minorCtors env ctx target v) ++
      (← minorCtors env ctx target b)
  | .mdata _ b | .proj _ _ b => minorCtors env ctx target b
  | .mvar m =>
    if (← get).contains m then return #[]
    modify (·.push m)
    match ctx.getExprAssignmentCore? m with
    | some v => minorCtors env ctx target v
    | none => match ctx.dAssignment.find? m with
      | some d => minorCtors env ctx target (.mvar d.mvarIdPending)
      | none => return #[]
  | _ => return #[]

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
    let mut ctors : Array Name := #[]
    for before in t.goalsBefore do
      let some e := t.mctxAfter.getExprAssignmentCore? before | continue
      ctors := ctors ++ (((minorCtors ctx.env t.mctxAfter goal e).run' #[]).run)
    -- Lean tags each new goal with its constructor's name; the minor position
    -- and the tag must agree, and exactly one constructor may remain.
    let matching := (ctors.filter fun c => c.getString! == tag.getString!).toList.eraseDups
    if let [ctor] := matching then
      result := result.push ⟨parent, goal, ctor⟩
  return result

def caseLabels (stx : Syntax) : Array (Syntax × Bool) := Id.run do
  match stx with
  | `(tactic| case $[$tags $hs*]|* => $_body:tacticSeq1Indented) =>
    let mut result := #[]
    for tag in tags do
      if let `(binderIdent| $id:ident) := tag then
        -- Compound labels can combine multiple nested constructors. They need
        -- component-wise provenance rather than a single reference range.
        result := result.push (id.raw, id.getId.getPrefix.isAnonymous)
    return result
  | _ => return #[]

def byteRange? (stx : Syntax) : Option (Nat × Nat) := do
  let a ← stx.getPos? (canonicalOnly := true)
  let b ← stx.getTailPos? (canonicalOnly := true)
  return (a.byteIdx, b.byteIdx)

def diagnostic (stx : Syntax) (reason : String) : Array Json :=
  match byteRange? stx with
  | some (a, b) => #[toJson (#[toJson a, toJson b, toJson reason])]
  | none => #[]

/-- Constructor-case label references, plus precise reasons for every simple or
compound label that has no unique compiler provenance. -/
def caseReferences (trees : Array InfoTree) (fileMap : FileMap)
    (refs : Server.ModuleRefs) : Server.ModuleRefs × Array Json := Id.run do
  let mut origins : Array CaseOrigin := #[]
  for tree in trees do
    origins := tree.foldInfo (fun ctx info found =>
      if let .ofTacticInfo t := info then found ++ caseOrigins ctx t else found) origins
  let mut result := (refs, #[])
  for tree in trees do
    result := tree.foldInfo (fun ctx info found => Id.run do
      let .ofTacticInfo t := info | return found
      unless t.elaborator == ``Lean.Elab.Tactic.evalCase do return found
      let mut (refs, rows) := found
      let some parent := ctx.parentDecl? | return (refs, rows ++ (caseLabels t.stx).foldl
        (fun acc (label, _) => acc ++ diagnostic label "case label outside a declaration") #[])
      for (label, simple) in caseLabels t.stx do
        unless simple do
          rows := rows ++ diagnostic label "compound case label: component-wise constructor provenance is unsupported"
          continue
        let tag := label.getId.eraseMacroScopes
        let goals := t.goalsBefore.filter fun goal =>
          (t.mctxBefore.findDecl? goal).any fun decl =>
            tag.isSuffixOf decl.userName.eraseMacroScopes
        unless goals.length == 1 do
          rows := rows ++ diagnostic label s!"case label selects {goals.length} goals"
          continue
        let names := (origins.filter fun origin => origin.parent == parent &&
          origin.ctor.getString! == tag.getString! &&
          descends t.mctxBefore origin.goal goals[0]!).map (·.ctor)
        let names := names.toList.eraseDups
        unless names.length == 1 do
          rows := rows ++ diagnostic label (if names.isEmpty then
            "case label goal has no ordinary `cases` constructor origin (explicit eliminator, inline alternative, induction or user-named goal)"
            else s!"case label goal has {names.length} constructor origins")
          continue
        let name := names[0]!
        let some start := label.getPos? | continue
        let some stop := label.getTailPos? | continue
        let ref : Server.Reference := {
          ident := .const ((Server.getModuleContainingDecl? ctx.env name).getD ctx.env.header.mainModule).toString name.toString
          range := ⟨fileMap.utf8PosToLspPos start, fileMap.utf8PosToLspPos stop⟩
          stx := label, ci := ctx, info := info, isBinder := false }
        refs := refs.addRef ref
      return (refs, rows)) result
  return result

/-- Kept for callers of the earlier API. -/
def addCaseReferences (trees : Array InfoTree) (fileMap : FileMap)
    (refs : Server.ModuleRefs) : Server.ModuleRefs :=
  (caseReferences trees fileMap refs).1

partial def forallBinderNames : Expr → List Name
  | .forallE n _ b _ => n.eraseMacroScopes :: forallBinderNames b
  | .mdata _ e => forallBinderNames e
  | _ => []

partial def syntaxNodes (kind : SyntaxNodeKind) (stx : Syntax) : Array Syntax :=
  let below := stx.getArgs.foldl (fun acc child => acc ++ syntaxNodes kind child) #[]
  if stx.isOfKind kind then #[stx] ++ below else below

/-- Named arguments `(x := e)`: the function's compiler identity (from the
elaborated head of its own syntax), the binder, and the structure field the
binder denotes when the function is a structure constructor. -/
def namedArgumentRows (env : Environment) (trees : Array InfoTree)
    (commands : Array Syntax) : Array Json := Id.run do
  let mut heads : Std.HashMap (Nat × Nat) (Array Name) := {}
  for tree in trees do
    heads := tree.foldInfo (fun _ info acc => Id.run do
      let .ofTermInfo ti := info | return acc
      let some r := byteRange? ti.stx | return acc
      let some n := ti.expr.getAppFn.constName? | return acc
      let old := acc.getD r #[]
      return if old.contains n then acc else acc.insert r (old.push n)) heads
  let mut rows := #[]
  for command in commands do
    for app in syntaxNodes ``Lean.Parser.Term.app command do
      for arg in app[1].getArgs do
        unless arg.isOfKind ``Lean.Parser.Term.namedArgument do continue
        let id := arg[1]
        let some (a, b) := byteRange? id | continue
        let param := id.getId.eraseMacroScopes
        let fns := (byteRange? app[0]).map (heads.getD · #[]) |>.getD #[]
        let row := match fns with
          | #[fn] =>
            let binders := (env.find? fn).map (fun (ci : ConstantInfo) => forallBinderNames ci.type) |>.getD []
            let field := match env.find? fn with
              | some (.ctorInfo c) =>
                if isStructure env c.induct && (getStructureFields env c.induct).contains param then
                  toJson (c.induct ++ param).toString else Json.null
              | _ => Json.null
            if binders.contains param then
              #[toJson a, toJson b, toJson fn.toString, toJson param.toString, field, Json.null]
            else
              #[toJson a, toJson b, toJson fn.toString, toJson param.toString, Json.null,
                toJson s!"named argument is not a binder of {fn}"]
          | #[] => #[toJson a, toJson b, Json.null, toJson param.toString, Json.null,
              toJson "named argument of a function without a constant head (local or elaborated term)"]
          | _ => #[toJson a, toJson b, Json.null, toJson param.toString, Json.null,
              toJson s!"named argument function has {fns.size} compiler heads"]
        rows := rows.push (toJson row)
  return rows

structure Frame where
  ns : Name := .anonymous
  opens : List OpenDecl := []
  isNamespace : Bool := false
  variables : Bool := false
  options : Bool := false
  universes : Bool := false

def openJson : OpenDecl → Json
  | .simple ns except => toJson #[toJson "simple", toJson ns.toString, toJson (except.map (·.toString))]
  | .explicit id decl => toJson #[toJson "explicit", toJson id.toString, toJson decl.toString]

def nsRow (stx : Syntax) (kind : String) (full : Option Name) (reason : String := "") : Array Json :=
  match byteRange? stx with
  | some (a, b) => #[toJson #[toJson a, toJson b, toJson kind,
      match full with | some n => toJson n.toString | none => Json.null, toJson reason]]
  | none => #[]

/-- Final-environment namespace resolution. Namespaces are only ever added, so a
unique answer here is the one Lean found when the command elaborated. -/
def resolveRow (env : Environment) (frame : Frame) (kind : String) (id : Syntax) : Array Json :=
  if id.getId.hasMacroScopes || (`_root_).isPrefixOf id.getId then
    nsRow id kind none "macro-scoped or _root_ namespace spelling"
  else match ResolveName.resolveNamespace env frame.ns frame.opens id.getId with
    | [n] => nsRow id kind (some n)
    | ns => nsRow id kind none s!"namespace resolves to {ns.length} candidates"

/-- Apply one `openDecl` to a frame, returning namespace reference rows. -/
def openDecl (env : Environment) (frame : Frame) (decl : Syntax) : Frame × Array Json := Id.run do
  let mut frame := frame
  let mut rows := #[]
  if decl.isOfKind ``Lean.Parser.Command.openSimple then
    for id in decl[0].getArgs do
      rows := rows ++ resolveRow env frame "open" id
      for n in ResolveName.resolveNamespace env frame.ns frame.opens id.getId do
        frame := { frame with opens := .simple n [] :: frame.opens }
  else if decl.isOfKind ``Lean.Parser.Command.openScoped then
    for id in decl[1].getArgs do rows := rows ++ resolveRow env frame "open" id
  else if decl.isOfKind ``Lean.Parser.Command.openHiding then
    rows := rows ++ resolveRow env frame "open" decl[0]
    if let [n] := ResolveName.resolveNamespace env frame.ns frame.opens decl[0].getId then
      frame := { frame with opens := .simple n (decl[2].getArgs.toList.map (·.getId)) :: frame.opens }
  else if decl.isOfKind ``Lean.Parser.Command.openOnly ||
      decl.isOfKind ``Lean.Parser.Command.openRenaming then
    -- Their declaration identifiers carry compiler constant references.
    rows := rows ++ resolveRow env frame "open" decl[0]
  return (frame, rows)

def openDeclKinds : Array SyntaxNodeKind := #[``Lean.Parser.Command.openSimple,
  ``Lean.Parser.Command.openScoped, ``Lean.Parser.Command.openHiding,
  ``Lean.Parser.Command.openOnly, ``Lean.Parser.Command.openRenaming]

partial def nestedOpenDecls (stx : Syntax) : Array Syntax :=
  if openDeclKinds.any stx.isOfKind then #[stx]
  else stx.getArgs.foldl (fun acc child => acc ++ nestedOpenDecls child) #[]

/-- Replay the syntactic scope stack (`namespace`, `section`, `end`, `open`,
`variable`, `set_option`, `universe`, `in`). Returns namespace reference rows
and one row per top-level command with the scope it elaborated in. -/
partial def scopeCommand (env : Environment) (stack : Array Frame) (cmd : Syntax) :
    Array Frame × Array Json := Id.run do
  let top := stack.back?.getD {}
  let mut stack := stack
  let mut rows := #[]
  if cmd.isOfKind ``Lean.Parser.Command.namespace then
    let id := cmd[1]
    rows := rows ++ nsRow id "namespace" (some (top.ns ++ id.getId))
    let mut ns := top.ns
    for comp in id.getId.components do
      ns := ns ++ comp
      stack := stack.push { top with ns, isNamespace := true }
  else if cmd.isOfKind ``Lean.Parser.Command.section then
    if !cmd[2].isNone then rows := rows ++ nsRow cmd[2][0] "section" none
    stack := stack.push { top with isNamespace := false }
  else if cmd.isOfKind ``Lean.Parser.Command.end then
    let count := if cmd[1].isNone then 1 else cmd[1][0].getId.components.length
    let popped := stack.extract (stack.size - count) stack.size
    stack := stack.shrink (stack.size - count)
    if !cmd[1].isNone then
      if popped.all (·.isNamespace) && popped.size == count then
        rows := rows ++ nsRow cmd[1][0] "namespace" (some top.ns)
      else if popped.all (!·.isNamespace) then
        rows := rows ++ nsRow cmd[1][0] "section" none
      else
        rows := rows ++ nsRow cmd[1][0] "namespace" none "end closes mixed namespace/section scopes"
  else if cmd.isOfKind ``Lean.Parser.Command.open then
    let (frame, found) := openDecl env top cmd[1]
    rows := rows ++ found
    stack := stack.pop.push frame
  else if cmd.isOfKind ``Lean.Parser.Command.export then
    rows := rows ++ resolveRow env top "export" cmd[1]
  else if cmd.isOfKind ``Lean.Parser.Command.in then
    let (inner, found) := scopeCommand env (stack.push top) cmd[0]
    let (_, found') := scopeCommand env inner cmd[2]
    rows := rows ++ found ++ found'
  else
    if cmd.isOfKind ``Lean.Parser.Command.variable then
      stack := stack.pop.push { top with variables := true }
    else if cmd.isOfKind ``Lean.Parser.Command.set_option then
      stack := stack.pop.push { top with options := true }
    else if cmd.isOfKind ``Lean.Parser.Command.universe then
      stack := stack.pop.push { top with universes := true }
    -- Term- and tactic-level `open ... in` resolve in the command's scope.
    for decl in nestedOpenDecls cmd do
      rows := rows ++ (openDecl env top decl).2
  return (stack, rows)

def scopeRows (env : Environment) (commands : Array Syntax) : Array Json × Array Json × Json := Id.run do
  let mut stack : Array Frame := #[{}]
  let mut namespaces := #[]
  let mut commandRows := #[]
  for cmd in commands do
    let top := stack.back?.getD {}
    if let some (a, b) := byteRange? cmd then
      commandRows := commandRows.push (toJson #[toJson a, toJson b, toJson cmd.getKind.toString,
        toJson top.ns.toString, toJson (top.opens.toArray.reverse.map openJson),
        toJson #[toJson top.variables, toJson top.options, toJson top.universes]])
    let (next, rows) := scopeCommand env stack cmd
    stack := if next.isEmpty then #[{}] else next
    namespaces := namespaces ++ rows
  -- Text appended at the end of the file elaborates in this scope.
  let top := stack.back?.getD {}
  return (namespaces, commandRows, toJson #[toJson (stack.size - 1), toJson top.ns.toString,
    toJson (top.opens.toArray.reverse.map openJson)])

def importRows (header : Syntax) : Array Json :=
  (syntaxNodes ``Lean.Parser.Module.import header).foldl (fun acc imp =>
    acc ++ ((syntaxNodes identKind imp).foldl (fun acc id => match byteRange? id with
      | some (a, b) => acc.push (toJson #[toJson a, toJson b, toJson id.getId.toString])
      | none => acc) #[])) #[]

/-- Literal chunks come from the original parsed syntax, not macro expansions.
The interpolation parser gives the embedded expressions separate children. -/
partial def literalRanges (stx : Syntax) : Array Json := Id.run do
  if stx.isOfKind strLitKind || stx.isOfKind interpolatedStrLitKind ||
      stx.isOfKind charLitKind then
    if let .atom (.original _ start _ stop) value := stx[0] then
      return #[toJson (#[toJson start.byteIdx, toJson stop.byteIdx,
        toJson stx.getKind.toString, toJson value])]
  return stx.getArgs.foldl (fun acc child => acc ++ literalRanges child) #[]

def indexJson (index : Server.Ilean) (commands : Array Syntax)
    (extra : List (String × Json) := []) : Json :=
  (toJson index).setObjVal! "naming_syntax" <| Json.mkObj <| [
    ("version", toJson (if extra.isEmpty then 1 else 2 : Nat)),
    ("literal_ranges", toJson (commands.foldl (fun acc stx => acc ++ literalRanges stx) #[]))] ++ extra

/-- Version-2 syntax provenance shared by both exporters. -/
def syntaxExtras (env : Environment) (header : Syntax) (trees : Array InfoTree)
    (commands : Array Syntax) (caseRows : Array Json) : List (String × Json) :=
  let (namespaces, commandRows, eof) := scopeRows env commands
  [("named_arguments", toJson (namedArgumentRows env trees commands)),
   ("namespaces", toJson namespaces), ("commands", toJson commandRows), ("eof_scope", eof),
   ("imports", toJson (importRows header)), ("unresolved_syntax", toJson caseRows)]

partial def identifiersIn (stx : Syntax) : Array Syntax :=
  if stx.isIdent then #[stx]
  else stx.getArgs.foldl (fun acc child => acc ++ identifiersIn child) #[]

/-- The registered audit commands use literal `getId` names, without namespace
resolution. Other elaborators with similar spelling confer no provenance. -/
def addAuditReferences (trees : Array InfoTree) (fileMap : FileMap)
    (refs : Server.ModuleRefs) : Server.ModuleRefs := Id.run do
  let mut result := refs
  for tree in trees do
    result := tree.foldInfo (fun ctx info found => Id.run do
      let .ofCommandInfo ci := info | return found
      unless Server.getModuleContainingDecl? ctx.env ci.elaborator == some `AxiomAudit do
        return found
      let ids := if ci.stx.isOfKind `Jaune.AxiomAudit.«command#expect_axioms_[_,,]» then
          identifiersIn ci.stx
        else if ci.stx.isOfKind `Jaune.AxiomAudit.unionAxiomsOfModules then
          -- The first identifier denotes a module prefix, not a constant.
          identifiersIn ci.stx[2]
        else #[]
      let mut found := found
      for id in ids do
        let name := id.getId
        unless ctx.env.contains name do continue
        let .original _ start _ stop := id.getHeadInfo | continue
        let ref : Server.Reference := {
          ident := .const ((Server.getModuleContainingDecl? ctx.env name).getD ctx.env.header.mainModule).toString name.toString
          range := ⟨fileMap.utf8PosToLspPos start, fileMap.utf8PosToLspPos stop⟩
          stx := id, ci := ctx, info := info, isBinder := false }
        found := found.addRef ref
      return found) result
  return result

end NamingReferences

