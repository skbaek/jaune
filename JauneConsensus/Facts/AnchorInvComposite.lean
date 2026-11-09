import JauneConsensus.Facts.AnchorInv

/-!
# Anchor invariants: composite steps (goal `eip7002-cross-layer-v1`, unit W2d-3)

`Facts/AnchorInv.lean` proves `Pres` for each mutator with a small verification-condition
generator. Lean's `do` elaboration shares the continuation after an `if` through a join point
`have __do_jp := fun … => rest; …`; reducing that `have` copies `rest` into every branch, so a
block with `n` sequential `if`s produced `2 ^ n` paths. This file adds two meta steps that keep
the join point abstract:

* `jp_intro` proves the continuation once, for every argument tuple, with the post-condition
  re-based at the state argument (`Pres σ`), and continues with the join point as a variable;
* `jp_call` closes a call of such a variable by `Pres` from the current base to the passed state.

The generator `pstep` is `pres_step` with these two steps first and without `zeta` reduction.
-/

namespace JauneConsensus.Facts
open JauneConsensus

variable {P : Preset} {f : CFork}

/-! ## Join points -/

section Meta
open Lean Meta Elab Tactic

/-- The parts `(α, c, Q)` of `Ok c Q`. -/
private def okParts? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity ``Ok 3 then some (e.getArg! 0, e.getArg! 1, e.getArg! 2) else none

/-- For a post-condition `Q` on `α` of the form `fun r => Pres A (g r)`, return `(A, g)`. -/
private def presParts (α Q : Expr) : MetaM (Expr × Expr) :=
  withLocalDeclD `r α fun r => do
    let qr := (mkApp Q r).headBeta
    unless qr.isAppOfArity ``Pres 5 do throwError "post-condition is not `Pres _ _`"
    let A := qr.getArg! 3
    if A.containsFVar r.fvarId! then throwError "post-condition base depends on the result"
    pure (A, ← mkLambdaFVars #[r] (qr.getArg! 4))

/-- `fun r => Pres σ (g r)`, eta-reduced. -/
private def mkPost (α σ g : Expr) : MetaM Expr := do
  let post ← withLocalDeclD `r α fun r => do
    mkLambdaFVars #[r] (← mkAppM ``Pres #[σ, (mkApp g r).headBeta])
  pure post.eta

private def isJpName (n : Name) : Bool := n.eraseMacroScopes == `__do_jp

/-- Reduce head beta-redexes and non-join-point `have`/`let`s of the computation in `Ok c Q`. -/
elab "ok_head" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (α, c, Q) := okParts? t | throwError "ok_head: goal is not `Ok _ _`"
  let rec go (c : Expr) (fuel : Nat) : Expr :=
    match fuel with
    | 0 => c
    | fuel + 1 =>
      let c := c.headBeta
      match c with
      | .letE n _ v b _ => if isJpName n then c else go (b.instantiate1 v) fuel
      | .mdata _ e => go e fuel
      | _ => c
  let c' := go c 64
  if c' == c then throwError "ok_head: no progress"
  replaceMainGoal [← g.replaceTargetDefEq (mkAppN t.getAppFn #[α, c', Q])]

/-- Abstract a join point `have __do_jp := k; e` in `Ok (have __do_jp := k; e) (Pres A ∘ g)`:
prove `∀ ys, Ok (k ys) (Pres (σ ys) ∘ g)`, where `σ ys` is the last state argument (or `A`), and
`Ok e (Pres A ∘ g)` for an abstract join point with that property. -/
elab "jp_intro" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (α, c, Q) := okParts? t | throwError "jp_intro: goal is not `Ok _ _`"
  let .letE n ty v b _ := c.headBeta | throwError "jp_intro: no `have` at the head"
  unless isJpName n do throwError "jp_intro: not a join point"
  let (A, gf) ← presParts α Q
  let stTy ← inferType A
  let mkH (jp : Expr) : MetaM Expr := forallTelescope ty fun ys _ => do
    let mut σ := A
    for y in ys do
      if ← isDefEq (← inferType y) stTy then σ := y
    let post ← mkPost α σ gf
    mkForallFVars ys (mkAppN t.getAppFn #[α, (mkAppN jp ys).headBeta, post])
  let hkTy ← mkH v
  let hk ← mkFreshExprSyntheticOpaqueMVar hkTy `jp_body
  let heTy ← withLocalDeclD n ty fun jp => do
    let h ← mkH jp
    withLocalDeclD `hjp h fun hjp =>
      mkForallFVars #[jp, hjp] (mkAppN t.getAppFn #[α, b.instantiate1 jp, Q])
  let he ← mkFreshExprSyntheticOpaqueMVar heTy `jp_rest
  g.assign (mkApp2 he v hk)
  let (_, hkG) ← hk.mvarId!.intros
  let (_, heG) ← he.mvarId!.introN 2
  replaceMainGoal [hkG, heG]

/-- Close `Ok (jp ys) (Pres A ∘ g)` from a join-point hypothesis `∀ ys, Ok (jp ys) (Pres σ ∘ g)`,
leaving `Pres A σ`. -/
elab "jp_call" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (α, c, Q) := okParts? t | throwError "jp_call: goal is not `Ok _ _`"
  let c := c.headBeta
  let fn := c.getAppFn
  unless fn.isFVar do throwError "jp_call: not a call of a local"
  let (A, _) ← presParts α Q
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isForall do continue
    let r : Option MVarId ← try
        let (mvs, _, body) ← forallMetaTelescope ty
        let some (_, c', post) := okParts? body | throwError "not Ok"
        unless c'.getAppFn == fn do throwError "other head"
        unless ← isDefEq c' c do throwError "args differ"
        let post ← instantiateMVars post
        let (σ, _) ← presParts α post
        let hp ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Pres #[A, σ]) `jp_pres
        let pf ← mkAppM ``okT #[hp, mkAppN d.toExpr mvs]
        unless ← isDefEq (← inferType pf) t do throwError "type differs"
        g.assign (← instantiateMVars pf)
        pure (some hp.mvarId!)
      catch _ => pure none
    if let some hpG := r then
      replaceMainGoal [hpG]
      return
  throwError "jp_call: no join-point hypothesis applies"

/-- Debug: print the head of each `Ok` goal. -/
elab "trace_ok" : tactic => do
  for g in (← getGoals).take 1 do
    g.withContext do
      let t ← instantiateMVars (← g.getType)
      match okParts? t with
      | some (_, c, Q) =>
        let c := c.headBeta
        let hd := match c with
          | .letE n .. => s!"let {n.eraseMacroScopes}"
          | _ => s!"{c.getAppFn.constName?.getD `fvar} / {c.getAppNumArgs}"
        logInfo m!"OK {hd} :: size {c.approxDepth} :: Q {(← ppExpr Q).pretty.take 120}"
      | none => logInfo m!"OTHER {(← ppExpr t).pretty.take 200}"

end Meta

theorem pres_ite {f1 f2 : CFork} {s : BeaconState P f1} {a b : BeaconState P f2} {c : Prop}
    [Decidable c] (h1 : Pres s a) (h2 : Pres s b) : Pres s (if c then a else b) := by
  split
  · exact h1
  · exact h2

macro_rules | `(tactic| pres_close) => `(tactic| (refine pres_ite ?_ ?_ <;> pres_close))

/-- One generator step: `pres_step` with join points kept abstract and no `zeta` reduction. -/
syntax "pstep" : tactic
macro_rules | `(tactic| pstep) => `(tactic| first
  | jp_intro
  | (jp_call; pres_close)
  | ok_head
  | with_reducible exact ok_throw
  | with_reducible exact ok_throw_bind
  | with_reducible exact ok_pure (Pres.refl _)
  | exact ok_pure (pres_frame rfl rfl)
  | (refine ok_pure ?_; try dsimp -zeta only
     pres_close)
  | exact ok_of fun _ hh => by pres_of hh
  | (refine ok_of fun _ hh => ?_; have h2 := by pres_of hh
     exact Pres.trans (by pres_close) h2)
  | (with_reducible apply ok_bind; intro _ hx; forIn_guard hx array state
     refine okT (Pres.trans ?_ (array_forIn_pres (fun _ _ => by repeat pstep) hx)) ?_; pres_close)
  | (with_reducible apply ok_bind; intro _ hx; forIn_guard hx list state
     refine okT (Pres.trans ?_ (list_forIn_pres (fun _ _ => by repeat pstep) hx)) ?_; pres_close)
  | (with_reducible apply ok_bind; intro _ hx; forIn_guard hx array pair
     refine okT (Pres.trans ?_ (array_forIn_pres_fst (fun _ _ => by repeat pstep) hx)) ?_; pres_close)
  | (with_reducible apply ok_bind; intro _ hx; forIn_guard hx list pair
     refine okT (Pres.trans ?_ (list_forIn_pres_fst (fun _ _ => by repeat pstep) hx)) ?_; pres_close)
  | (with_reducible apply ok_bind; intro _ hx
     first | (refine okT (Pres.trans ?_ (by pres_of hx)) ?_; pres_close) | skip)
  | (with_reducible apply ok_ite <;> intro _)
  | (with_reducible apply ok_dite <;> intro _)
  | (set_option simprocs false in dsimp -zeta only)
  | (rename_i x _; is_small_inductive x; cases x; all_goals (set_option simprocs false in dsimp -zeta only))
  | split)

/-! ## Block steps -/

theorem processSyncAggregate_pres (ctx : Ctx) {sa : SyncAggregate P} {s s' : BeaconState P f}
    (h : processSyncAggregate ctx s sa = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processSyncAggregate ctx s sa) (Pres s)
  unfold processSyncAggregate
  repeat pstep

theorem processAttestation_pres (ctx : Ctx) {a : Attestation P f} {s s' : BeaconState P f}
    (h : processAttestation ctx s a = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processAttestation ctx s a) (Pres s)
  unfold processAttestation
  repeat pstep

end JauneConsensus.Facts
