import NamingReferencesCore

/-! Export kernel expressions and effective attributes for rename fidelity.
This optional metaprogram is outside the specification import closure.
-/

open Lean Lean.Elab

namespace NamingFidelity

def node (tag : String) (args : Array Json := #[]) : Json :=
  Json.arr (#[toJson tag] ++ args)

def nameRef (n : Name) : Json := node "name" #[toJson n.toString]

partial def levelJson (params : List Name) : Level → Except String Json
  | .zero => pure <| node "zero"
  | .succ u => return node "succ" #[← levelJson params u]
  | .max u v => return node "max" #[← levelJson params u, ← levelJson params v]
  | .imax u v => return node "imax" #[← levelJson params u, ← levelJson params v]
  | .param n =>
    match params.idxOf? n with
    | some i => pure <| node "param" #[toJson i]
    | none => throw s!"unbound universe parameter {n}"
  | .mvar _ => throw "unassigned universe metavariable"

partial def exprJson (params : List Name) : Expr → Except String Json
  | .bvar i => pure <| node "bvar" #[toJson i]
  | .fvar _ => throw "free variable in exported expression"
  | .mvar _ => throw "unassigned metavariable in exported expression"
  | .sort u => return node "sort" #[← levelJson params u]
  | .const n us => return node "const" #[nameRef n, toJson (← us.mapM (levelJson params))]
  | .app f a => return node "app" #[← exprJson params f, ← exprJson params a]
  | .lam _ t b bi => return node "lam" #[toJson (reprStr bi), ← exprJson params t, ← exprJson params b]
  | .forallE _ t b bi => return node "forall" #[toJson (reprStr bi), ← exprJson params t, ← exprJson params b]
  | .letE _ t v b nonDep => return node "let" #[toJson nonDep, ← exprJson params t, ← exprJson params v, ← exprJson params b]
  | .lit (.natVal n) => pure <| node "nat" #[toJson n]
  | .lit (.strVal s) => pure <| node "str" #[toJson s]
  | .mdata _ e => exprJson params e
  | .proj n i e => return node "proj" #[nameRef n, toJson i, ← exprJson params e]

def constantJson (c : ConstantInfo) : Except String Json := do
  let p := c.levelParams
  let payload ← match c with
    | .axiomInfo v => pure <| node "axiom" #[toJson v.isUnsafe]
    | .thmInfo _ => pure <| node "theorem"
    | .defnInfo v => return node "definition" #[toJson (reprStr v.safety), ← exprJson p v.value]
    | .opaqueInfo v => return node "opaque" #[toJson v.isUnsafe, ← exprJson p v.value]
    | .quotInfo _ => throw "unexpected local quotient primitive"
    | .inductInfo v => pure <| node "inductive" #[toJson v.numParams, toJson v.numIndices,
        toJson (v.all.map nameRef), toJson (v.ctors.map nameRef), toJson v.numNested,
        toJson v.isRec, toJson v.isUnsafe, toJson v.isReflexive]
    | .ctorInfo v => pure <| node "constructor" #[nameRef v.induct, toJson v.cidx,
        toJson v.numParams, toJson v.numFields, toJson v.isUnsafe]
    | .recInfo v =>
      let rules ← v.rules.mapM fun r => do
        return node "rule" #[nameRef r.ctor, toJson r.nfields, ← exprJson p r.rhs]
      pure <| node "recursor" #[toJson (v.all.map nameRef), toJson v.numParams,
        toJson v.numIndices, toJson v.numMotives, toJson v.numMinors,
        toJson rules, toJson v.k, toJson v.isUnsafe]
  return Json.mkObj [("universes", toJson p.length), ("type", ← exprJson p c.type),
    ("payload", payload)]

def inlineJson (env : Environment) (n : Name) : Json :=
  toJson <| (Compiler.getInlineAttribute? env n).map fun
    | .inline => "inline" | .noinline => "noinline" | .macroInline => "macro_inline"
    | .inlineIfReduce => "inline_if_reduce" | .alwaysInline => "always_inline"

def attributesJson (env : Environment) (n : Name) : Json := Id.run do
  let simp := Meta.simpExtension.getState env
  let collect := fun (acc : Array Json) (t : Meta.SimpTheorem) =>
    match t.origin with
    | .decl name post inv =>
      if name == n && !simp.erased.contains t.origin then
        acc.push (node "simp" #[toJson post, toJson inv, toJson t.priority,
          toJson t.perm, toJson t.rfl, toJson t.backwardRfl])
      else acc
    | _ => acc
  let simps := simp.post.foldValues collect (simp.pre.foldValues collect #[])
  let inst := (Meta.instanceExtension.getState env).instanceNames.find? n
  let csimp := (Compiler.CSimp.ext.getState env).map.find? n
  return Json.mkObj [
    ("simp", toJson simps),
    ("simp_unfold", toJson (simp.toUnfold.contains n)),
    ("simp_equations", toJson ((simp.toUnfoldThms.find? n).map (·.map nameRef))),
    ("csimp", toJson (Compiler.hasCSimpAttribute env n)),
    ("csimp_replacement", toJson (csimp.map fun e => #[nameRef e.toDeclName, nameRef e.thmName])),
    ("inline", inlineJson env n),
    ("reducibility", toJson (reprStr (getReducibilityStatusCore env n))),
    ("instance", toJson (inst.map fun i => node "instance" #[toJson i.priority,
      toJson i.synthOrder, toJson (match i.attrKind with | .global => "global" | .local => "local" | .scoped => "scoped")])),
    ("implemented_by", toJson ((Compiler.getImplementedBy? env n).map nameRef))]

partial def syntaxJson : Syntax → Json
  | .missing => node "missing"
  | .atom _ val => node "atom" #[toJson val]
  | s@(.ident _ _ val _) => node "ident" #[toJson val.toString,
      toJson (s.getPos?.map (·.byteIdx)), toJson (s.getTailPos?.map (·.byteIdx))]
  | .node _ kind args => node "syntax" #[toJson kind.toString, toJson (args.map syntaxJson)]

partial def guardTerms (s : Syntax) : Array Syntax :=
  if s.isOfKind ``Parser.Command.guardCmd then #[s[1]]
  else s.getArgs.foldl (fun acc child => acc ++ guardTerms child) #[]

-- Keep all explicit attribute syntax too: final extension state alone loses
-- local attributes that have gone out of scope and unfamiliar custom attrs.
partial def attributeSyntax (s : Syntax) : Array Json :=
  if s.isOfKind ``Parser.Term.attributes || s.isOfKind ``Parser.Command.attribute then
    #[syntaxJson s]
  else s.getArgs.foldl (fun acc child => acc ++ attributeSyntax child) #[]

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

def guardJson (trees : Array InfoTree) (term : Syntax) : IO Json := do
  let mut candidates : Array Json := #[]
  let mut provenance : Array Json := #[]
  for tree in trees do
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
        match exprJson [] e with
        | .ok json => return some (node tag #[json], Json.mkObj [
            ("syntax_kind", toJson info.stx.getKind.toString),
            ("exact_syntax", toJson (info.stx == term)),
            ("elaborator", toJson info.elaborator.toString)])
        | .error message => throwError "guard export: {message}"
    candidates := candidates ++ (found.map Prod.fst).toArray
    provenance := provenance ++ (found.map Prod.snd).toArray
  let some first := candidates[0]?
    | throw <| IO.userError s!"guard has no closed Bool/Prop expression at byte range {reprStr (term.getPos?.map (·.byteIdx))}..{reprStr (term.getTailPos?.map (·.byteIdx))}"
  unless candidates.all (· == first) do
    throw <| IO.userError s!"ambiguous guard expression at byte range {reprStr (term.getPos?.map (·.byteIdx))}..{reprStr (term.getTailPos?.map (·.byteIdx))}; {candidates.size} candidates: {toJson candidates}; provenance: {toJson provenance}"
  return first

/-- All transitive imports actually loaded by this frontend. Record every
possible data/IR part, including absence, so capture can bind the resolved
artifacts before and after elaboration. Lean 4.35 imports these five parts. -/
def importArtifacts (env : Environment) : IO Json := do
  let cwd ← IO.currentDir
  let modules ← env.header.moduleNames.mapM fun name => do
    let olean ← findOLean name
    let olean := if olean.isAbsolute then olean else cwd / olean
    let parts ← #["olean", "olean.server", "olean.private", "ir.sig", "ir"].mapM fun ext => do
      let path := olean.withExtension ext
      let present ← path.pathExists
      pure (ext, if present then toJson path.toString else Json.null)
    pure (name.toString, Json.mkObj parts.toList)
  return Json.mkObj modules.toList

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

end NamingFidelity

open NamingFidelity

unsafe def main (args : List String) : IO UInt32 := do
  if let ["--headers", input, output] := args then
    headerInventory input output
    return 0
  let (importsOnly, rest) := match args with
    | "--imports" :: rest => (true, rest)
    | rest => (false, rest)
  let [source, moduleName, output] := rest
    | IO.eprintln "usage: jaune-naming-fidelity [--imports] SOURCE MODULE OUTPUT"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile source
  let inputCtx := Parser.mkInputContext input source
  let options := ({} : Options).setBool `Elab.async false
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header options messages inputCtx (mainModule := moduleName.toName)
  if messages.hasErrors then
    for message in messages.toList do IO.eprintln (← message.toString)
    return 1
  let imports ← importArtifacts env
  if importsOnly then
    IO.FS.writeFile output (Json.mkObj [
      ("schema_version", toJson (1 : Nat)), ("module", toJson moduleName),
      ("lean_version", toJson Lean.versionString),
      ("direct_imports", toJson (Lean.Server.collectImports header)),
      ("imports", imports)]).compress
    return 0
  let state := { Command.mkState env messages options with infoState.enabled := true }
  let result ← IO.processCommands inputCtx parserState state
  if result.commandState.messages.hasErrors then
    for message in result.commandState.messages.toList do IO.eprintln (← message.toString)
    return 1
  let env := result.commandState.env
  let trees := result.commandState.infoState.trees.toArray
  let refs := Lean.Server.findModuleRefs inputCtx.fileMap trees (localVars := true)
  let refs := NamingReferences.addCaseReferences trees inputCtx.fileMap refs
  let (references, decls) ← refs.toLspModuleRefs
  let index : Lean.Server.Ilean := {
    module := moduleName.toName
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
    unless (attributeSyntax command).isEmpty do
      attrs := attrs.push (syntaxJson command)
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
  let guards ← terms.mapM (guardJson trees)
  let checksJson := checks.map fun command => Json.mkObj [
    ("syntax", syntaxJson command),
    ("literal_names", toJson (auditCommand command)),
    ("start", toJson (command.getPos?.map (·.byteIdx))),
    ("end", toJson (command.getTailPos?.map (·.byteIdx))),
    ("expected_failure_scope", toJson (command.isOfKind ``Lean.guardMsgsCmd))]
  let kernel := env.toKernelEnv
  let mut constants : List (String × Json) := []
  for c in (← env.getLocalConstantInfos) do
    let some info := kernel.find? c.name
      | throw <| IO.userError s!"constant absent from checked kernel environment: {c.name}"
    let data ← IO.ofExcept (constantJson info)
    let equationOrigin := (Meta.eqnsExt.getState env).mapInv.find? info.name
    constants := (info.name.toString, Json.mkObj [
      ("kernel", data), ("attributes", attributesJson env info.name),
      ("equation_origin", toJson (equationOrigin.map nameRef))]) :: constants
  let json := Json.mkObj [("schema_version", toJson (6 : Nat)),
    ("lean_version", toJson Lean.versionString), ("imports", imports), ("source", toJson input),
    ("index", toJson index), ("constants", Json.mkObj constants),
    ("guards", toJson guards), ("attribute_syntax", toJson attrs), ("checked_commands", toJson checksJson)]
  IO.FS.writeFile output json.compress
  IO.println s!"OK — naming fidelity: {constants.length} constants, {guards.size} guards"
  return 0
