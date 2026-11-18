import Lean

/-!
# Field-reader walk (goal `jaune-shape-and-names-v1`, decision 13 condition 2)

Before a structure field is deleted, a walk of the built Lean environment confirms that
nothing reads it. This executable is that walk's Lean half; `scripts/field-readers.py`
drives it and renders the verdict.

For every query it records, per constant of the scoped modules (types and values, proof
bodies included):

* `projFn` -- the projection function `S.f` applied or mentioned;
* `proj`   -- a kernel projection `Expr.proj S i _`;
* `cases`  -- an `S.casesOn` / `S.recOn` / `S.rec` minor premise that uses the bound
  variable of field `i` (an eta-reduced minor counts as a use);
* `match`  -- a matcher application whose alternative uses the parameter the matcher
  feeds from field `i`, or a matcher that consumes field `i` outside its alternatives.
  The matcher's own definition is analysed once and never counted as a reader, so a
  matcher shared between declarations links only the declarations whose alternatives
  actually use the field;
* `ref`    -- for a query that is a plain constant rather than a field: any mention;
* `write`  -- an `S.mk` application whose field-`i` argument is not a copy;
* `copy`   -- an occurrence of `S.f x`, `Expr.proj S i x` or the field's own pattern
  variable that is directly the field-`i` argument of `S.mk` (how `{ s with g := v }`
  elaborates). Copies are discounted from the readers and listed.

Each record carries the constant, the declaration it belongs to (`owner`: auxiliary
`_proof_n`, `_sunfold`, ... constants are attributed to their declaration) and a class:
`reader` or `generated` (equation lemmas, matcher splitters/equations, derived
instances with macro scopes, the structure's own recursors/`noConfusion`/`ext`/`injEq`/
`sizeOf` lemmas and projections, and constants with no declaration range).

Incremental: results are cached per module under `--cache DIR`, keyed by the module's
Lake trace hash (`depHash` in the `.trace` file beside its `.olean`, which covers its
imports), the query list and `--salt` (the driver passes a digest of this tool's binary).
A module whose key is unchanged is not walked again.

Usage (from the package root, after an owned build of `jaune-field-readers` and the
modules to walk):

  lake env .lake/build/bin/jaune-field-readers --cache DIR --salt S \
    --scope-root Jaune ... --query Jaune.Meta.output ... --import Jaune ...
-/

open Lean

namespace FieldReaders

/-- What a pattern-bound variable stands for. -/
inductive Tag where
  | field (q : Nat)
  | alt (k : Nat)
  deriving Inhabited, BEq, Hashable

structure FieldQ where
  struct : Name
  ctor : Name
  nparams : Nat
  idx : Nat
  nfields : Nat

inductive Query where
  | field (name : Name) (f : FieldQ)
  | const (name : Name)

def Query.name : Query → Name
  | .field n _ => n
  | .const n => n

structure Tables where
  env : Environment
  projQ : Std.HashMap Name Nat := {}
  constQ : Std.HashMap Name Nat := {}
  projIdx : Std.HashMap (Name × Nat) Nat := {}
  /-- ctor ↦ (nparams, [(field index, query)]) -/
  ctorQ : Std.HashMap Name (Nat × Array (Nat × Nat)) := {}
  /-- eliminator ↦ (minor position, nfields, [(field index, query)]) -/
  elimQ : Std.HashMap Name (Nat × Nat × Array (Nat × Nat)) := {}
  /-- Matcher infos, read from every module's imported entries (the extension's state is
  not initialised without `loadExts`). -/
  matcherInfo : Std.HashMap Name Meta.MatcherInfo := {}

/-- A matcher's summary: queries it consumes outside its alternatives, and
`(alternative, parameter, query)` flows. -/
structure MatchSummary where
  uncond : Array Nat := #[]
  flows : Array (Nat × Nat × Nat) := #[]
  deriving Inhabited

structure St where
  uses : Std.HashSet (Nat × String) := {}
  flows : Std.HashSet (Nat × Nat × Nat) := {}
  visited : Std.HashSet (USize × UInt64) := {}
  matchers : Std.HashMap Name MatchSummary := {}

abbrev M := ReaderT Tables (StateM St)

/-- Pattern variables are kept as `(absolute binder position, tag)`; a de Bruijn index `i`
at depth `d` names position `d - 1 - i`. -/
abbrev Tags := List (Nat × Tag)

def lookupTag (tags : Tags) (pos : Nat) : Option Tag :=
  (tags.find? (·.1 == pos)).map (·.2)

def ctxKey (e : Expr) (d : Nat) (tags : Tags) : UInt64 := Id.run do
  let r := e.looseBVarRange
  let mut h : UInt64 := 7
  for (pos, t) in tags do
    if pos + r ≥ d && pos < d then
      h := mixHash h (mixHash (hash (d - 1 - pos)) (hash t))
  return h

def emit (q : Nat) (how : String) : M Unit :=
  modify fun s => { s with uses := s.uses.insert (q, how) }

/-- Queries of the kernel projections inside `e`. -/
partial def projQsIn (t : Tables) (e : Expr) (acc : Array Nat) : Array Nat :=
  match e with
  | .proj s i x =>
    let acc := match t.projIdx[(s, i)]? with | some q => acc.push q | none => acc
    projQsIn t x acc
  | .app f x => projQsIn t x (projQsIn t f acc)
  | .lam _ ty b _ | .forallE _ ty b _ => projQsIn t b (projQsIn t ty acc)
  | .letE _ ty v b _ => projQsIn t b (projQsIn t v (projQsIn t ty acc))
  | .mdata _ b => projQsIn t b acc
  | _ => acc

/-- Queries whose field value occurs in `a` (an argument a matcher passes to one of its
alternatives): tagged pattern variables, projection functions and kernel projections. -/
def fieldsIn (t : Tables) (a : Expr) (d : Nat) (tags : Tags) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for (pos, tag) in tags do
    if let .field q := tag then
      if pos < d && a.hasLooseBVar (d - 1 - pos) then out := out.push q
  out := a.foldConsts out fun c acc => match t.projQ[c]? with
    | some q => acc.push q
    | none => acc
  return projQsIn t a out

/-- `a` is a copy of query `q`'s field: returns the copied-from expression (if any). -/
def copyOf? (t : Tables) (a : Expr) (q : Nat) (d : Nat) (tags : Tags) : Option (Option Expr) :=
  let a := a.consumeMData
  match a with
  | .proj s i x => if t.projIdx[(s, i)]? == some q then some (some x) else none
  | .bvar i =>
    if i < d then
      match lookupTag tags (d - 1 - i) with
      | some (.field q') => if q' == q then some none else none
      | _ => none
    else none
  | _ =>
    match a.getAppFn with
    | .const c _ =>
      if t.projQ[c]? == some q then
        let args := a.getAppArgs
        if args.size ≥ 1 then some (some args.back!) else none
      else none
    | _ => none

def usesParam (alt : Expr) (n j : Nat) : Bool := Id.run do
  let mut cur := alt
  for _ in [0:n] do
    match cur.consumeMData with
    | .lam _ _ b _ => cur := b
    | _ => return true
  return cur.hasLooseBVar (n - 1 - j)

mutual

partial def walk (e : Expr) (d : Nat) (tags : Tags) : M Unit := do
  let key := (unsafe ptrAddrUnsafe e, ctxKey e d tags)
  if (← get).visited.contains key then return
  modify fun s => { s with visited := s.visited.insert key }
  match e with
  | .mdata _ b => walk b d tags
  | .lam _ ty b _ | .forallE _ ty b _ => walk ty d tags; walk b (d + 1) tags
  | .letE _ ty v b _ => walk ty d tags; walk v d tags; walk b (d + 1) tags
  | .bvar i =>
    if i < d then
      if let some (.field q) := lookupTag tags (d - 1 - i) then emit q "cases"
  | .proj s i x =>
    if let some q := (← read).projIdx[(s, i)]? then emit q "proj"
    walk x d tags
  | .const c _ => walkApp (.const c []) #[] d tags
  | .app .. => walkApp e.getAppFn e.getAppArgs d tags
  | _ => pure ()

partial def walkApp (fn : Expr) (args : Array Expr) (d : Nat) (tags : Tags) : M Unit := do
  let t ← read
  match fn with
  | .const c _ =>
    if let some (np, fqs) := t.ctorQ[c]? then
      for h : p in [0:args.size] do
        let a := args[p]
        match fqs.find? (fun (fi, _) => np + fi == p) with
        | some (_, q) =>
          match copyOf? t a q d tags with
          | some base => emit q "copy"; if let some x := base then walk x d tags
          | none => emit q "write"; walk a d tags
        | none => walk a d tags
      for (fi, q) in fqs do
        if np + fi ≥ args.size then emit q "write"
    else if let some (minorPos, nf, fqs) := t.elimQ[c]? then
      for h : p in [0:args.size] do
        if p == minorPos then walkMinor args[p] nf fqs d tags
        else walk args[p] d tags
      if args.size ≤ minorPos then
        for (_, q) in fqs do emit q "cases"
    else if let some info := t.matcherInfo[c]? then
      let summ ← matcherSummary c info
      for q in summ.uncond do emit q "match"
      for (k, j, q) in summ.flows do
        let pos := info.getFirstAltPos + k
        if h : pos < args.size then
          if usesParam args[pos] (info.altNumParams[k]!) j then emit q "match"
        else emit q "match"
      for a in args do walk a d tags
    else
      if let some q := t.projQ[c]? then emit q "projFn"
      if let some q := t.constQ[c]? then emit q "ref"
      for a in args do walk a d tags
  | .bvar i =>
    match (if i < d then lookupTag tags (d - 1 - i) else none) with
    | some (.alt k) =>
      for h : j in [0:args.size] do
        for q in fieldsIn t args[j] d tags do
          modify fun s => { s with flows := s.flows.insert (k, j, q) }
    | some (.field q) => emit q "cases"; for a in args do walk a d tags
    | none => for a in args do walk a d tags
  | _ => walk fn d tags; for a in args do walk a d tags

partial def walkMinor (a : Expr) (nf : Nat) (fqs : Array (Nat × Nat)) (d : Nat)
    (tags : Tags) : M Unit := do
  let mut cur := a
  let mut tags := tags
  let mut k := 0
  while k < nf do
    match cur.consumeMData with
    | .lam _ ty b _ =>
      walk ty (d + k) tags
      if let some (_, q) := fqs.find? (·.1 == k) then
        tags := (d + k, .field q) :: tags
      cur := b
      k := k + 1
    | _ => break
  if k < nf then
    for (fi, q) in fqs do
      if fi ≥ k then emit q "cases"
  walk cur (d + k) tags

partial def matcherSummary (c : Name) (info : Meta.MatcherInfo) : M MatchSummary := do
  if let some s := (← get).matchers[c]? then return s
  let t ← read
  let saved ← get
  set ({ matchers := saved.matchers } : St)
  let some ci := t.env.find? c | return {}
  let some v := ci.value? (allowOpaque := true) | return {}
  let firstAlt := info.getFirstAltPos
  let total := firstAlt + info.numAlts
  let mut cur := v
  let mut tags : Tags := []
  let mut k := 0
  while k < total do
    match cur.consumeMData with
    | .lam _ _ b _ =>
      if k ≥ firstAlt then tags := (k, .alt (k - firstAlt)) :: tags
      cur := b
      k := k + 1
    | _ => break
  walk cur k tags
  let inner ← get
  let summ : MatchSummary :=
    { uncond := (inner.uses.toArray.filter (fun (_, how) => how != "write" && how != "copy")).map (·.1)
      flows := inner.flows.toArray }
  set ({ saved with matchers := inner.matchers.insert c summ } : St)
  return summ

end

/-! ## Attribution and classification -/

def isEqnSuffix (s : String) : Bool :=
  s == "eq_def" || s == "eq_unfold" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)

def isAuxComp (s : String) : Bool :=
  s.startsWith "_" || (s.startsWith "match_" && (s.drop 6).all Char.isDigit) ||
  (s.startsWith "proof_" && (s.drop 6).all Char.isDigit)

/-- The declaration a constant belongs to, and whether the constant is a generated
equation/matcher lemma. -/
def ownerOf (n : Name) : Name × Bool := Id.run do
  let user := (privateToUserName? n).getD n
  let comps := user.components
  let mut owner : Name := .anonymous
  let mut aux := false
  let mut eqn := false
  for c in comps do
    let s := c.toString (escape := false)
    if aux then
      if isEqnSuffix s || s == "splitter" then eqn := true
      continue
    if isAuxComp s then
      aux := true
      if s.startsWith "match_" then eqn := true
      continue
    owner := owner ++ c
  if !aux then
    if let some last := comps.getLast? then
      if isEqnSuffix (last.toString (escape := false)) then
        return (user.getPrefix, true)
  return (owner, eqn)

/-- `owner` (a user name) with the private prefix of `n`, if `n` is private. -/
def rawName (n owner : Name) : Name :=
  match privateToUserName? n with
  | none => owner
  | some user =>
    let pre := n.components.take (n.components.length - user.components.length)
    owner.components.foldl (· ++ ·) (pre.foldl (· ++ ·) .anonymous)

def structGeneratedSuffixes : List String :=
  ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "ctorIdx", "toCtorIdx",
   "ext", "ext_iff", "injEq", "inj", "sizeOf_spec", "below", "brecOn", "binductionOn",
   "ibelow", "ctorElim", "ctorElimType", "mk"]

def isGeneratedOwner (env : Environment) (owner : Name) : Bool :=
  owner.hasMacroScopes ||
  env.isProjectionFn owner ||
  (match owner with
   | .str p s =>
     structGeneratedSuffixes.contains s &&
       (isStructure env p || (env.find? p).any (·.isCtor))
   | _ => false) ||
  (match owner with
   | .str p _ => (env.find? p).any (·.isCtor)
   | _ => false) ||
  (declRangeExt.find? env owner).isNone

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.thmInfo _) => "theorem"
  | some (.defnInfo _) => if Meta.isInstanceCore env n then "instance" else "def"
  | some (.opaqueInfo _) => "opaque"
  | some (.axiomInfo _) => "axiom"
  | some (.inductInfo _) => "inductive"
  | some (.ctorInfo _) => "ctor"
  | some (.recInfo _) => "recursor"
  | some (.quotInfo _) => "quot"
  | none => "missing"

/-! ## Query tables -/

def buildTables (env : Environment) (names : Array Name) : Except String (Array Query × Tables) := do
  let mut qs : Array Query := #[]
  let mut t : Tables := { env }
  let mut mi : Std.HashMap Name Meta.MatcherInfo := {}
  for i in [0:env.header.moduleNames.size] do
    for e in PersistentEnvExtension.getModuleEntries Meta.Match.Extension.extension env i
        (level := .private) do
      mi := mi.insert e.name e.info
  t := { t with matcherInfo := mi }
  for n in names do
    let q := qs.size
    match env.getProjectionFnInfo? n with
    | some info =>
      let some (.ctorInfo cv) := env.find? info.ctorName
        | throw s!"{n}: constructor {info.ctorName} not found"
      let f : FieldQ := { struct := cv.induct, ctor := cv.name, nparams := info.numParams,
                          idx := info.i, nfields := cv.numFields }
      qs := qs.push (.field n f)
      t := { t with
        projQ := t.projQ.insert n q
        projIdx := t.projIdx.insert (cv.induct, info.i) q
        ctorQ := t.ctorQ.alter cv.name fun
          | some (np, fs) => some (np, fs.push (info.i, q))
          | none => some (info.numParams, #[(info.i, q)]) }
      -- eliminators: casesOn/recOn (minor after params, motive, major), rec (after motive)
      for (elim, pos) in [(mkCasesOnName cv.induct, info.numParams + 2),
                          (mkRecOnName cv.induct, info.numParams + 2),
                          (mkRecName cv.induct, info.numParams + 1)] do
        if env.contains elim then
          t := { t with elimQ := t.elimQ.alter elim fun
            | some (mp, nf, fs) => some (mp, nf, fs.push (info.i, q))
            | none => some (pos, cv.numFields, #[(info.i, q)]) }
    | none =>
      -- a query absent from this environment is still listed (its index stays stable);
      -- the driver fails when a query is absent from every environment
      qs := qs.push (.const n)
      if env.contains n then t := { t with constQ := t.constQ.insert n q }
  return (qs, t)

/-! ## Driver -/

def depHash (m : Name) : IO String := do
  try
    let olean ← findOLean m
    let trace := olean.withExtension "trace"
    let j ← IO.ofExcept (Json.parse (← IO.FS.readFile trace))
    match j.getObjValAs? String "depHash" with
    | .ok h => return h
    | .error _ => return "none"
  catch _ => return "none"

structure Args where
  cache : System.FilePath := ".lake/field-readers-cache"
  salt : String := ""
  roots : Array Name := #[]
  queries : Array Name := #[]
  imports : Array Name := #[]

partial def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--cache" :: v :: r, a => parseArgs r { a with cache := v }
  | "--salt" :: v :: r, a => parseArgs r { a with salt := v }
  | "--scope-root" :: v :: r, a => parseArgs r { a with roots := a.roots.push v.toName }
  | "--query" :: v :: r, a => parseArgs r { a with queries := a.queries.push v.toName }
  | "--import" :: v :: r, a => parseArgs r { a with imports := a.imports.push v.toName }
  | x :: _, _ => .error s!"unknown argument {x}"

def walkConstant (n : Name) (ci : ConstantInfo) : M (Array (Nat × String)) := do
  modify fun s => { s with uses := {}, flows := {}, visited := {} }
  walk ci.type 0 []
  if let some v := ci.value? (allowOpaque := true) then walk v 0 []
  let _ := n
  return (← get).uses.toArray

end FieldReaders

open FieldReaders in
def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => IO.eprintln e; return 2
  if args.imports.isEmpty || args.queries.isEmpty || args.roots.isEmpty then
    IO.eprintln "need --import, --query and --scope-root"; return 2
  initSearchPath (← findSysroot)
  let t0 ← IO.monoMsNow
  let env ← importModules (args.imports.map ({ module := · })) {} (trustLevel := 1024)
  let t1 ← IO.monoMsNow
  let (qs, tables) ← match buildTables env args.queries with
    | .ok r => pure r
    | .error e => IO.eprintln e; return 2
  let queried : Std.HashSet Name := qs.foldl (init := {}) fun acc q => match q with
    | .field _ f => acc.insert f.struct
    | .const _ => acc
  let qkey := toString (hash (args.queries.map toString |>.toList, args.salt))
  let mods := env.header.moduleNames
  let inScope (m : Name) := args.roots.any (·.isPrefixOf m)
  IO.FS.createDirAll args.cache
  -- decide which modules need a walk
  let mut todo : Std.HashMap Nat (String × System.FilePath) := {}
  let mut reused := 0
  let mut nScoped := 0
  for h : i in [0:mods.size] do
    let m := mods[i]
    unless inScope m do continue
    nScoped := nScoped + 1
    let key := s!"{← depHash m}:{qkey}"
    let file := args.cache / s!"{m}.json"
    let hit ← (do
      if !(← file.pathExists) then return false
      match Json.parse (← IO.FS.readFile file) with
      | .ok j => return (j.getObjValAs? String "key" |>.toOption) == some key && key.take 5 != "none:"
      | .error _ => return false)
    if hit then reused := reused + 1 else todo := todo.insert i (key, file)
  -- bucket constants of the modules to walk
  let mut buckets : Std.HashMap Nat (Array (Name × ConstantInfo)) := {}
  if !todo.isEmpty then
    for (n, ci) in env.constants.map₁.toList do
      let some idx := env.getModuleIdxFor? n | continue
      if todo.contains idx.toNat then
        buckets := buckets.alter idx.toNat fun
          | some a => some (a.push (n, ci))
          | none => some #[(n, ci)]
  let mut st : St := {}
  let mut walked := 0
  for (i, (key, file)) in todo.toList do
    let m := mods[i]!
    let mut entries : Array Json := #[]
    for (n, ci) in buckets.getD i #[] do
      if tables.matcherInfo.contains n then continue
      walked := walked + 1
      let (uses, st') := (walkConstant n ci).run tables |>.run st
      st := st'
      if uses.isEmpty then continue
      let (owner, eqn) := ownerOf n
      -- a private declaration keeps its private prefix for every environment lookup
      let rawOwner := rawName n owner
      -- the constructor or a projection of another inductive restates the field in its
      -- type: attribute it to that inductive, which a user wrote
      let induct? : Option Name := match env.find? rawOwner with
        | some (.ctorInfo cv) => some cv.induct
        | _ => (env.getProjectionFnInfo? rawOwner).bind fun i =>
            match env.find? i.ctorName with
            | some (.ctorInfo cv) => some cv.induct
            | _ => none
      let (owner, rawOwner) := match induct? with
        | some x => if queried.contains x then (owner, rawOwner) else (x, x)
        | none => (owner, rawOwner)
      let viaInduct := induct?.any (!queried.contains ·)
      let isAux := owner != ((privateToUserName? n).getD n)
      let generated := !viaInduct && (eqn || isGeneratedOwner env rawOwner) ||
        (isAux && (env.find? rawOwner).any (·.isInductive))
      let line := match declRangeExt.find? env rawOwner with
        | some r => r.range.pos.line
        | none => 0
      for (q, how) in uses do
        entries := entries.push <| Json.mkObj [
          ("query", toJson ((qs[q]?.map Query.name).getD .anonymous).toString), ("how", toJson how),
          ("const", toJson ((privateToUserName? n).getD n).toString),
          ("owner", toJson owner.toString), ("private", toJson (isPrivateName n)),
          ("kind", toJson (kindOf env rawOwner)), ("line", toJson line),
          ("class", toJson (if generated then "generated" else "reader")),
          ("module", toJson m.toString)]
    let out := Json.mkObj [("key", toJson key), ("module", toJson m.toString),
                           ("entries", Json.arr entries)]
    IO.FS.writeFile file out.compress
  let t2 ← IO.monoMsNow
  IO.println (Json.compress <| Json.mkObj [
    ("modules_scoped", toJson nScoped), ("modules_reused", toJson reused),
    ("modules_walked", toJson todo.size), ("constants_walked", toJson walked),
    ("import_ms", toJson (t1 - t0)), ("walk_ms", toJson (t2 - t1)),
    ("modules", toJson ((mods.filter inScope).map toString)),
    ("unknown", toJson ((args.queries.filter (!env.contains ·)).map toString))])
  return 0
