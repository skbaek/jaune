import Lean

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

def unsupportedCommand (s : Syntax) : Bool :=
  !s.isOfKind ``Parser.Command.guardCmd && (firstAtom s).any (·.startsWith "#")

def guardJson (trees : Array InfoTree) (term : Syntax) : IO Json := do
  let mut candidates : Array Json := #[]
  for tree in trees do
    let found ← tree.collectTermInfoM fun ctx info => do
      if info.stx.getPos? != term.getPos? || info.stx.getTailPos? != term.getTailPos? then
        return none
      ctx.runMetaM info.lctx do
        let e ← instantiateMVars info.expr
        let type ← Meta.inferType e
        if type != mkConst ``Bool then return none
        match exprJson [] e with
        | .ok json => return some json
        | .error message => throwError "guard export: {message}"
    candidates := candidates ++ found.toArray
  let some first := candidates[0]?
    | throw <| IO.userError "guard has no closed Bool expression in compiler information"
  unless candidates.all (· == first) do
    throw <| IO.userError "ambiguous guard expression in compiler information"
  return first

end NamingFidelity

open NamingFidelity

unsafe def main (args : List String) : IO UInt32 := do
  let [source, moduleName, output] := args
    | IO.eprintln "usage: jaune-naming-fidelity SOURCE MODULE OUTPUT"; return 2
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
  let state := { Command.mkState env messages options with infoState.enabled := true }
  let result ← IO.processCommands inputCtx parserState state
  if result.commandState.messages.hasErrors then
    for message in result.commandState.messages.toList do IO.eprintln (← message.toString)
    return 1
  let env := result.commandState.env
  let trees := result.commandState.infoState.trees.toArray
  let refs := Lean.Server.findModuleRefs inputCtx.fileMap trees (localVars := true)
  let (references, decls) ← refs.toLspModuleRefs
  let index : Lean.Server.Ilean := {
    module := moduleName.toName
    directImports := Lean.Server.collectImports header
    references, decls }
  let kernel := env.toKernelEnv
  let mut constants : List (String × Json) := []
  for c in (← env.getLocalConstantInfos) do
    let some info := kernel.find? c.name
      | throw <| IO.userError s!"constant absent from checked kernel environment: {c.name}"
    let data ← IO.ofExcept (constantJson info)
    constants := (info.name.toString, Json.mkObj [
      ("kernel", data), ("attributes", attributesJson env info.name)]) :: constants
  let mut terms : Array Syntax := #[]
  let mut attrs : Array Json := #[]
  for command in result.commands do
    if unsupportedCommand command then
      throw <| IO.userError "unsupported hash command: fidelity currently exports #guard only"
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
  let guards ← terms.mapM (guardJson trees)
  let json := Json.mkObj [("schema_version", toJson (2 : Nat)),
    ("lean_version", toJson Lean.versionString), ("source", toJson input),
    ("index", toJson index), ("constants", Json.mkObj constants),
    ("guards", toJson guards), ("attribute_syntax", toJson attrs)]
  IO.FS.writeFile output json.compress
  IO.println s!"OK — naming fidelity: {constants.length} constants, {guards.size} guards"
  return 0
