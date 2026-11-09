import JauneConsensus.Facts.AnchorInv
import JauneConsensus.StateTransition
import JauneConsensus.Facts.Joint

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

/-! ## Loops with the state inside the accumulator -/

theorem list_forIn_pres_proj {α β : Type} {f' : CFork} (π : β → BeaconState P f') {xs : List α}
    {init out : β} {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, Ok (body a b) (fun r => Pres (π b) (π r.value)))
    (h : forIn xs init body = .ok out) : Pres (π init) (π out) :=
  list_forIn_rel (fun a b => Pres (π a) (π b)) (fun _ => Pres.refl _)
    (fun _ _ _ h1 h2 => h1.trans h2) body (fun a b r hr => hb a b r hr) xs init out h

theorem array_forIn_pres_proj {α β : Type} {f' : CFork} (π : β → BeaconState P f') {xs : Array α}
    {init out : β} {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, Ok (body a b) (fun r => Pres (π b) (π r.value)))
    (h : forIn xs init body = .ok out) : Pres (π init) (π out) := by
  rw [← Array.forIn_toList] at h
  exact list_forIn_pres_proj π hb h

/-- The `for _ in [a:b]` loop. -/
theorem range_forIn_pres_proj {β : Type} {f' : CFork} (π : β → BeaconState P f')
    {xs : Std.Legacy.Range} {init out : β} {body : Nat → β → M (ForInStep β)}
    (hb : ∀ a b, Ok (body a b) (fun r => Pres (π b) (π r.value)))
    (h : forIn xs init body = .ok out) : Pres (π init) (π out) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact list_forIn_pres_proj π hb h

theorem ok_bind_ite {α β : Type} {c : Prop} [Decidable c] {x y : M α} {k : α → M β}
    {Q : β → Prop} (h : Ok (if c then x >>= k else y >>= k) Q) :
    Ok ((if c then x else y) >>= k) Q := by
  by_cases hc : c
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h ⊢; exact h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h ⊢; exact h

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

/-- The state component of a value `x : T` (a state, or nested pairs containing one). -/
private def findState : Nat → Expr → Expr → MetaM (Option Expr)
  | 0, _, _ => pure none
  | fuel + 1, x, T => do
    let T ← whnfR T
    if T.getAppFn.isConstOf ``BeaconState then return some x
    if T.isAppOfArity ``Prod 2 then
      if let some e ← findState fuel (← mkAppM ``Prod.fst #[x]) (T.getArg! 0) then return some e
      return ← findState fuel (← mkAppM ``Prod.snd #[x]) (T.getArg! 1)
    return none

/-- For `h : forIn xs init body = .ok out` whose accumulator contains a state (projection `π`) and
goal `Ok c (Pres A ∘ g)`: leave `Pres A (π init)`, the body obligation and `Ok c (Pres (π out) ∘ g)`. -/
elab "loop_pres " h:ident : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (α, c, Q) := okParts? t | throwError "loop_pres: goal is not `Ok _ _`"
  let d ← getLocalDeclFromUserName h.getId
  let ht ← instantiateMVars d.type
  let some (_, lhs, rhs) := ht.eq? | throwError "loop_pres: not an equation"
  unless lhs.getAppFn.isConstOf ``ForIn.forIn && lhs.getAppNumArgs ≥ 3 do
    throwError "loop_pres: not a forIn"
  let n := lhs.getAppNumArgs
  let xs := lhs.getArg! (n - 3)
  let init := lhs.getArg! (n - 2)
  let body := lhs.getArg! (n - 1)
  let ρ ← whnfR (← inferType xs)
  let lem ← if ρ.isAppOf ``List then pure ``list_forIn_pres_proj
    else if ρ.isAppOf ``Array then pure ``array_forIn_pres_proj
    else if ρ.isConstOf ``Std.Legacy.Range then pure ``range_forIn_pres_proj
    else throwError "loop_pres: collection {ρ}"
  unless rhs.isAppOfArity ``Except.ok 3 do throwError "loop_pres: not `.ok`"
  let out := rhs.appArg!
  let β ← inferType init
  let π ← withLocalDeclD `x β fun x => do
    let some e ← findState 8 x β | throwError "loop_pres: no state in the accumulator"
    mkLambdaFVars #[x] e
  let (A, gf) ← presParts α Q
  let stepTy ← mkAppM ``ForInStep #[β]
  let hbTy ← forallTelescope (← inferType body) fun as _ => do
    unless as.size == 2 do throwError "loop_pres: body arity"
    let b := as[1]!
    let post ← withLocalDeclD `r stepTy fun r => do
      mkLambdaFVars #[r] (← mkAppM ``Pres #[π.beta #[b], π.beta #[← mkAppM ``ForInStep.value #[r]]])
    mkForallFVars as (mkAppN t.getAppFn #[stepTy, (mkAppN body as).headBeta, post])
  let hb ← mkFreshExprSyntheticOpaqueMVar hbTy `loop_body
  let pf ← mkAppM lem #[π, hb, d.toExpr]
  let hp ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Pres #[A, π.beta #[init]]) `loop_pre
  let rest ← mkFreshExprSyntheticOpaqueMVar
    (mkAppN t.getAppFn #[α, c, ← mkPost α (π.beta #[out]) gf]) `loop_rest
  let full ← mkAppM ``okT #[← mkAppM ``Pres.trans #[hp, pf], rest]
  unless ← isDefEq (← inferType full) t do throwError "loop_pres: type mismatch"
  g.assign full
  let (_, hbG) ← hb.mvarId!.introN 2
  replaceMainGoal [hp.mvarId!, hbG, rest.mvarId!]

end Meta

theorem pres_ite {f1 f2 : CFork} {s : BeaconState P f1} {a b : BeaconState P f2} {c : Prop}
    [Decidable c] (h1 : Pres s a) (h2 : Pres s b) : Pres s (if c then a else b) := by
  split
  · exact h1
  · exact h2

macro_rules | `(tactic| pres_close) => `(tactic| (refine pres_ite ?_ ?_ <;> pres_close))
macro_rules | `(tactic| pres_close) => `(tactic|
    exact pres_frame (by split <;> rfl) (by split <;> rfl))

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
  | with_reducible apply ok_bind_ite
  | (with_reducible apply ok_bind; intro _ hx; loop_pres hx; pres_close)
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

macro_rules | `(tactic| pres_of $h) => `(tactic| with_reducible exact processSyncAggregate_pres _ $h)
macro_rules | `(tactic| pres_of $h) => `(tactic| with_reducible exact processAttestation_pres _ $h)

theorem processOperations_pres (ctx : Ctx) {body : BeaconBlockBody P f} {s s' : BeaconState P f}
    (h : processOperations ctx s body = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processOperations ctx s body) (Pres s)
  unfold processOperations
  repeat pstep

macro_rules | `(tactic| pres_of $h) => `(tactic| with_reducible exact processOperations_pres _ $h)

theorem processBlockWith_pres (ctx : Ctx) {blk : BeaconBlock P f} {s s' : BeaconState P f}
    (h : processBlockWith ctx s blk = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processBlockWith ctx s blk) (Pres s)
  unfold processBlockWith
  repeat pstep

theorem processBlock_pres (ctx : Ctx) {blk : BeaconBlock P f} {s s' : BeaconState P f}
    (h : processBlock ctx s blk = .ok s') : Pres s s' :=
  processBlockWith_pres ctx h

macro_rules | `(tactic| pres_of $h) => `(tactic| with_reducible exact processBlock_pres _ $h)

/-! ## Epoch steps -/

theorem weighJustificationAndFinalization_pres {s s' : BeaconState P f} {t p c : Gwei}
    (h : weighJustificationAndFinalization s t p c = .ok s') : Pres s s' := by
  revert s' h
  show Ok (weighJustificationAndFinalization s t p c) (Pres s)
  unfold weighJustificationAndFinalization
  repeat pstep

macro_rules | `(tactic| pres_of $h) => `(tactic|
    with_reducible exact weighJustificationAndFinalization_pres $h)

theorem processJustificationAndFinalization_pres (cfg : Config) {s s' : BeaconState P f}
    (h : processJustificationAndFinalization cfg s = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processJustificationAndFinalization cfg s) (Pres s)
  unfold processJustificationAndFinalization
  repeat pstep

theorem processInactivityUpdates_pres (cfg : Config) {s s' : BeaconState P f}
    (h : processInactivityUpdates cfg s = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processInactivityUpdates cfg s) (Pres s)
  unfold processInactivityUpdates
  repeat pstep

theorem processRewardsAndPenalties_pres (cfg : Config) {s s' : BeaconState P f}
    (h : processRewardsAndPenalties cfg s = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processRewardsAndPenalties cfg s) (Pres s)
  unfold processRewardsAndPenalties
  repeat pstep

theorem processSlashings_pres (cfg : Config) {s s' : BeaconState P f}
    (h : processSlashings cfg s = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processSlashings cfg s) (Pres s)
  unfold processSlashings
  repeat pstep

theorem processPendingDeposits_pres (ctx : Ctx) {s s' : BeaconState P f}
    (h : processPendingDeposits ctx s = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processPendingDeposits ctx s) (Pres s)
  unfold processPendingDeposits
  repeat pstep

/-- A validator array relation: indices persist, credentials and the exit invariant are kept. -/
def ArrRel (A B : Array Validator) : Prop :=
  A.size ≤ B.size ∧ ∀ (j : Nat) (v' : Validator), B[j]? = some v' →
    ∃ v, A[j]? = some v ∧ CredKeep v v' ∧ (ExitOk v → ExitOk v')

theorem ArrRel.refl (A : Array Validator) : ArrRel A A :=
  ⟨le_refl _, fun _ v' h => ⟨v', h, CredKeep.refl _, id⟩⟩

theorem ArrRel.trans {A B C : Array Validator} (h1 : ArrRel A B) (h2 : ArrRel B C) : ArrRel A C := by
  refine ⟨le_trans h1.1 h2.1, fun j w hw => ?_⟩
  obtain ⟨v, hv, hk, hx⟩ := h2.2 j w hw
  obtain ⟨u, hu, hk', hx'⟩ := h1.2 j v hv
  exact ⟨u, hu, hk'.trans hk, fun h => hx (hx' h)⟩

theorem arrRel_set_eb {V V' : SszList Validator P.VALIDATOR_REGISTRY_LIMIT} {i : Nat} {v : Validator}
    {eb : Gwei} {site site' : String} (hg : V.get i site' = .ok v)
    (hs : V.set i { v with effective_balance := eb } site = .ok V') : ArrRel V.toArray V'.toArray := by
  obtain ⟨hi, hVe⟩ := set_ok hs
  have hv := get_ok hg
  refine ⟨le_of_eq (by rw [hVe, Array.size_set]), fun j w hw => ?_⟩
  rw [hVe, Array.getElem?_set] at hw
  by_cases hj : i = j
  · subst hj
    simp only [↓reduceIte] at hw
    cases hw
    exact ⟨v, hv, credKeep_of_wc rfl, id⟩
  · simp only [hj, ↓reduceIte] at hw
    exact ⟨w, hw, CredKeep.refl _, id⟩

theorem pres_of_arrRel {s : BeaconState P f} {V : SszList Validator P.VALIDATOR_REGISTRY_LIMIT}
    (h : ArrRel s.validators.toArray V.toArray) : Pres s { s with validators := V } :=
  pres_of_valRel ⟨h.1, fun j v' hv' => .inl (h.2 j v' hv')⟩ (pendingStep_same rfl)

theorem processEffectiveBalanceUpdates_pres (cfg : Config) {s s' : BeaconState P f}
    (h : processEffectiveBalanceUpdates cfg s = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processEffectiveBalanceUpdates cfg s) (Pres s)
  unfold processEffectiveBalanceUpdates
  repeat (first | ok_head | (with_reducible apply ok_bind; intro _ _))
  refine ok_pure (pres_of_arrRel ?_)
  refine list_forIn_rel
    (fun V V' : SszList Validator P.VALIDATOR_REGISTRY_LIMIT => ArrRel V.toArray V'.toArray)
    (fun _ => ArrRel.refl _) (fun _ _ _ => ArrRel.trans) _ ?_ _ _ _ (by assumption)
  intro i V r hb
  simp only [bind, Except.bind, pure, Except.pure] at hb
  repeat' split at hb
  all_goals first
    | (cases hb; exact ArrRel.refl _)
    | (cases hb; exact arrRel_set_eb (by assumption) (by assumption))
    | cases hb

/-! ## Slots -/

theorem processSlot_pres {s s' : BeaconState P f} (h : processSlot s = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processSlot s) (Pres s)
  unfold processSlot
  repeat pstep

macro_rules | `(tactic| pres_of $h) => `(tactic| with_reducible exact processSlot_pres $h)
macro_rules | `(tactic| pres_of $h) => do
  let hE := Lean.mkIdent `hE
  `(tactic| exact $hE _ _ $h)

theorem processSlotsWith_pres {pe : BeaconState P f → M (BeaconState P f)}
    (hE : ∀ a b, pe a = .ok b → Pres a b) {s s' : BeaconState P f} {slot : Slot}
    (h : processSlotsWith pe s slot = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processSlotsWith pe s slot) (Pres s)
  unfold processSlotsWith
  repeat pstep


/-! ## `process_epoch`, `process_slots` and `state_transition` (Electra and later) -/

theorem processEpoch_pres (ctx : Ctx) (hf : f.atLeast .electra = true) {s s' : BeaconState P f}
    (h : processEpoch ctx s = .ok s') : Pres s s' := by
  unfold processEpoch at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h⟩ := bind_eq_ok_iff.mp h
  dsimp only at h
  rw [ite_eq_left_of_eq_true _ _ (eq_true hf)] at h
  obtain ⟨s7a, h7a, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s7, h7, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s8, h8, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s9, h9, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s10, h10, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s11, h11, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s12, h12, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s13, h13, h⟩ := bind_eq_ok_iff.mp h
  refine (processJustificationAndFinalization_pres _ h1).trans <|
    (processInactivityUpdates_pres _ h2).trans <| (processRewardsAndPenalties_pres _ h3).trans <|
    (processRegistryUpdates_pres _ hf h4).trans <| (processSlashings_pres _ h5).trans <|
    (processEth1DataReset_pres _ h6).trans <| (processPendingDeposits_pres _ h7a).trans <|
    (processPendingConsolidations_pres _ h7).trans <|
    (processEffectiveBalanceUpdates_pres _ h8).trans <| (processSlashingsReset_pres _ h9).trans <|
    (processRandaoMixesReset_pres _ h10).trans <|
    (processHistoricalSummariesUpdate_pres _ h11).trans <|
    (processParticipationFlagUpdates_pres _ h12).trans <|
    (processSyncCommitteeUpdates_pres _ h13).trans ?_
  split at h
  · exact processProposerLookahead_pres _ h
  · cases h; exact Pres.refl _

theorem processSlots_pres (ctx : Ctx) (hf : f.atLeast .electra = true) {s s' : BeaconState P f}
    {slot : Slot} (h : processSlots ctx s slot = .ok s') : Pres s s' :=
  processSlotsWith_pres (fun _ _ hab => processEpoch_pres ctx hf hab) h

macro_rules | `(tactic| pres_of $h) => do
  let hE := Lean.mkIdent `hE
  `(tactic| exact processSlotsWith_pres $hE $h)
macro_rules | `(tactic| pres_of $h) => do
  let hB := Lean.mkIdent `hB
  `(tactic| exact $hB _ _ _ $h)

theorem stateTransitionWith_pres {pe : BeaconState P f → M (BeaconState P f)}
    {pb : BeaconState P f → BeaconBlock P f → M (BeaconState P f)}
    (hE : ∀ a b, pe a = .ok b → Pres a b) (hB : ∀ a blk b, pb a blk = .ok b → Pres a b)
    {bls : Bool} {s s' : BeaconState P f} {sb : SignedBeaconBlock P f} {vr : Bool}
    (h : stateTransitionWith pe pb bls s sb vr = .ok s') : Pres s s' := by
  revert s' h
  show Ok (stateTransitionWith pe pb bls s sb vr) (Pres s)
  unfold stateTransitionWith
  repeat pstep

theorem stateTransition_pres (ctx : Ctx) (hf : f.atLeast .electra = true) {s s' : BeaconState P f}
    {sb : SignedBeaconBlock P f} {vr : Bool} (h : stateTransition ctx s sb vr = .ok s') :
    Pres s s' :=
  stateTransitionWith_pres (fun _ _ hab => processEpoch_pres ctx hf hab)
    (fun _ _ _ hab => processBlock_pres ctx hab) h

/-! ## The joint step -/

open Jaune in
theorem jointStep_electra_pres {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .electra}
    {s' : JointState P} (h : jointStep cfg ccfg bls ⟨.electra, beacon, exec⟩ ⟨.electra, sb⟩ = .ok s') :
    Pres beacon s'.beacon := by
  obtain ⟨_, req, b', e', _, _, hst, rfl⟩ := jointStep_electra_ok_iff.mp h
  exact stateTransition_pres _ (by decide) hst

open Jaune in
theorem jointStep_fulu_pres {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .fulu} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
    {s' : JointState P} (h : jointStep cfg ccfg bls ⟨.fulu, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok s') :
    Pres beacon s'.beacon := by
  obtain ⟨req, b', e', _, _, hst, rfl⟩ := jointStep_fulu_ok_iff.mp h
  exact stateTransition_pres _ (by decide) hst

open Jaune in
theorem jointStep_cross_pres {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
    {s' : JointState P} (h : jointStep cfg ccfg bls ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok s') :
    Pres beacon s'.beacon := by
  obtain ⟨_, _, req, fslot, b1, b2, b', e', _, hb1, hb2, _, _, hb', rfl⟩ :=
    jointStep_cross_ok_iff.mp h
  have p1 : Pres beacon b1 := by
    split at hb1
    · exact processSlots_pres _ (by decide) hb1
    · cases hb1; exact Pres.refl _
  have p3 : Pres b2 b' := by
    split at hb'
    · revert hb'
      generalize b' = x
      revert x
      show Ok _ (Pres b2)
      repeat pstep
    · exact stateTransition_pres _ (by decide) hb'
  exact p1.trans ((upgradeToFulu_pres _ hb2).trans p3)

open Jaune in
/-- One successful joint step preserves `Pres` between the beacon states (Electra/Electra and
Fulu/Fulu via `state_transition`; Electra→Fulu via `process_slots`, `upgrade_to_fulu` and the
block). -/
theorem jointStep_pres {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s s' : JointState P}
    {b : AnySignedBlock P} (h : jointStep cfg ccfg bls s b = .ok s') : Pres s.beacon s'.beacon := by
  obtain ⟨fs, beacon, exec⟩ := s
  obtain ⟨fb, sb⟩ := b
  cases fs <;> cases fb
  all_goals first
    | exact jointStep_electra_pres h
    | exact jointStep_fulu_pres h
    | exact jointStep_cross_pres h
    | (unfold jointStep at h; cases h)

open Jaune in
theorem jointStep_anchorInv {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s s' : JointState P}
    {b : AnySignedBlock P} (h : jointStep cfg ccfg bls s b = .ok s') (hI : AnchorInv s.beacon) :
    AnchorInv s'.beacon :=
  (jointStep_pres h).anchor hI

open Jaune in
theorem jointStep_addrStable {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P} (h : jointStep cfg ccfg bls s b = .ok s') :
    AddrStable s.beacon s'.beacon :=
  (jointStep_pres h).addr

open Jaune in
/-- States reachable from `s₀` by successful joint steps. -/
inductive JointReach (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (s₀ : JointState P) :
    JointState P → Prop
  | refl : JointReach cfg ccfg bls s₀ s₀
  | step {s s' : JointState P} (b : AnySignedBlock P) : JointReach cfg ccfg bls s₀ s →
      jointStep cfg ccfg bls s b = .ok s' → JointReach cfg ccfg bls s₀ s'

open Jaune in
theorem JointReach.pres {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s₀ s : JointState P}
    (h : JointReach cfg ccfg bls s₀ s) : Pres s₀.beacon s.beacon := by
  induction h with
  | refl => exact Pres.refl _
  | step _ _ hs ih => exact ih.trans (jointStep_pres hs)

open Jaune in
/-- **Run-level anchor invariant.** If the anchor's beacon state satisfies `AnchorInv`, so does the
beacon state after every successful joint step along any run from it (each prefix of a run is a
`JointReach`). -/
theorem JointReach.anchorInv {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (h : JointReach cfg ccfg bls s₀ s) (h0 : AnchorInv s₀.beacon) :
    AnchorInv s.beacon :=
  h.pres.anchor h0

open Jaune in
/-- **Run-level address stability.** -/
theorem JointReach.addrStable {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (h : JointReach cfg ccfg bls s₀ s) : AddrStable s₀.beacon s.beacon :=
  h.pres.addr

end JauneConsensus.Facts
