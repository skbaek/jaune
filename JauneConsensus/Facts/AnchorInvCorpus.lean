import JauneConsensus.Facts.AnchorInvComposite
import JauneConsensus.Facts.PendingConsolidations

/-!
# Corpus anchor invariants and sub-step frame generator (`protocol-contract-corpus-v1`, G1b)

Extends `AnchorInv` (`PendingPartialsCompounding ∧ ExitImpliesWithdrawable`) with the two
load-bearing anchor invariants required by the cross-layer `S9` corpus (`C-S9` and `D-S9`):

* `BalancesMatchValidators`: `st.balances.toArray.size = st.validators.toArray.size`;
* `PendingConsolidationsDistinct`: every entry `pc` in `st.pending_consolidations` satisfies
  `pc.source_index ≠ pc.target_index`.

To avoid duplicating case-splits across both preservation and frame lemmas, `CommonSubstep`
bundles `BalancesMatchValidators` preservation together with exact preservation of `slot`,
`latest_block_header`, `latest_execution_payload_header`, `pending_consolidations`, and
`pending_deposits` across all non-queue consensus mutators. Queue, header, slot, epoch, upgrade,
`jointTransitionAt` (both `atSlot = false` and `atSlot = true`), `jointStep`, and `JointReach`
preservation theorems then compose cleanly on top.

Nothing here edits a spec definition.
-/

namespace JauneConsensus.Facts

open JauneConsensus

variable {P : Preset} {f : CFork}

/-! ## Anchor invariant predicates -/

/-- The balance list has one entry per registered validator. -/
def BalancesMatchValidators (st : BeaconState P f) : Prop :=
  st.balances.toArray.size = st.validators.toArray.size

/-- Total view of `pending_consolidations` as a `List PendingConsolidation` (empty before Electra). -/
def pendingConsolidationsList (st : BeaconState P f) : List PendingConsolidation :=
  match st.pendingConsolidations with
  | .ok l => l.toArray.toList
  | .error _ => []

theorem pendingConsolidationsList_eq_get (h : f.atLeast .electra = true) (st : BeaconState P f) :
    pendingConsolidationsList st = (Gated.get h st.pending_consolidations).toArray.toList := by
  unfold pendingConsolidationsList BeaconState.pendingConsolidations
  rw [gated_read_get h]

theorem pendingConsolidationsList_congr {s s' : BeaconState P f}
    (h : s'.pending_consolidations = s.pending_consolidations) :
    pendingConsolidationsList s' = pendingConsolidationsList s := by
  unfold pendingConsolidationsList BeaconState.pendingConsolidations
  rw [h]

/-- Every queued pending consolidation has distinct source and target validator indices. -/
def PendingConsolidationsDistinct (st : BeaconState P f) : Prop :=
  ∀ pc ∈ pendingConsolidationsList st, pc.source_index ≠ pc.target_index

theorem pendingConsolidationsDistinct_iff (st : BeaconState P f) :
    PendingConsolidationsDistinct st ↔
      ∀ l, st.pendingConsolidations = .ok l →
        ∀ pc ∈ l.toArray.toList, pc.source_index ≠ pc.target_index := by
  unfold PendingConsolidationsDistinct pendingConsolidationsList
  cases h : st.pendingConsolidations with
  | error e =>
    simp
  | ok l =>
    simp only [List.mem_iff_get]
    constructor
    · intro hd l' hl'
      cases hl'
      simpa [List.mem_iff_get] using hd
    · intro hd
      simpa [List.mem_iff_get] using hd l rfl

/-- Full composite anchor invariant for the `protocol-contract-corpus-v1` cross-layer `S9` rows. -/
def CorpusAnchorInv (st : BeaconState P f) : Prop :=
  AnchorInv st ∧ BalancesMatchValidators st ∧ PendingConsolidationsDistinct st

/-- Cross-fork preservation of `BalancesMatchValidators` and `PendingConsolidationsDistinct`. -/
structure CorpusPres {f1 f2 : CFork} (s : BeaconState P f1) (s' : BeaconState P f2) : Prop where
  bmv : BalancesMatchValidators s → BalancesMatchValidators s'
  pcd : PendingConsolidationsDistinct s → PendingConsolidationsDistinct s'

theorem CorpusPres.refl (s : BeaconState P f) : CorpusPres s s := ⟨id, id⟩

theorem CorpusPres.trans {f1 f2 f3 : CFork} {a : BeaconState P f1} {b : BeaconState P f2}
    {c : BeaconState P f3} (h1 : CorpusPres a b) (h2 : CorpusPres b c) : CorpusPres a c :=
  ⟨fun h => h2.bmv (h1.bmv h), fun h => h2.pcd (h1.pcd h)⟩

/-! ## `CommonSubstep`: shared preservation and frame relation for non-queue mutators -/

/-- A consensus sub-step that preserves `BalancesMatchValidators` and leaves `slot`,
`latest_block_header`, `latest_execution_payload_header`, `pending_consolidations`, and
`pending_deposits` untouched. -/
structure CommonSubstep (s s' : BeaconState P f) : Prop where
  bmv : BalancesMatchValidators s → BalancesMatchValidators s'
  slot_eq : s'.slot = s.slot
  lbh_eq : s'.latest_block_header = s.latest_block_header
  lep_eq : s'.latest_execution_payload_header = s.latest_execution_payload_header
  pc_eq : s'.pending_consolidations = s.pending_consolidations
  pd_eq : s'.pending_deposits = s.pending_deposits

theorem CommonSubstep.refl (s : BeaconState P f) : CommonSubstep s s :=
  ⟨id, rfl, rfl, rfl, rfl, rfl⟩

theorem CommonSubstep.trans {a b c : BeaconState P f}
    (h1 : CommonSubstep a b) (h2 : CommonSubstep b c) : CommonSubstep a c :=
  ⟨fun h => h2.bmv (h1.bmv h),
   h2.slot_eq.trans h1.slot_eq,
   h2.lbh_eq.trans h1.lbh_eq,
   h2.lep_eq.trans h1.lep_eq,
   h2.pc_eq.trans h1.pc_eq,
   h2.pd_eq.trans h1.pd_eq⟩

theorem CommonSubstep.pcd {s s' : BeaconState P f} (h : CommonSubstep s s') :
    PendingConsolidationsDistinct s → PendingConsolidationsDistinct s' := by
  unfold PendingConsolidationsDistinct
  rw [pendingConsolidationsList_congr h.pc_eq]
  exact id

theorem CommonSubstep.corpusPres {s s' : BeaconState P f} (h : CommonSubstep s s') :
    CorpusPres s s' :=
  ⟨h.bmv, h.pcd⟩

theorem commonSubstep_of_sizes {s s' : BeaconState P f}
    (hv : s'.validators.toArray.size = s.validators.toArray.size)
    (hb : s'.balances.toArray.size = s.balances.toArray.size)
    (hsl : s'.slot = s.slot)
    (hlbh : s'.latest_block_header = s.latest_block_header)
    (hlep : s'.latest_execution_payload_header = s.latest_execution_payload_header)
    (hpc : s'.pending_consolidations = s.pending_consolidations)
    (hpd : s'.pending_deposits = s.pending_deposits) :
    CommonSubstep s s' :=
  ⟨fun h => by unfold BalancesMatchValidators at h ⊢; omega, hsl, hlbh, hlep, hpc, hpd⟩

theorem commonSubstep_frame {s s' : BeaconState P f}
    (hv : s'.validators = s.validators)
    (hb : s'.balances = s.balances)
    (hsl : s'.slot = s.slot)
    (hlbh : s'.latest_block_header = s.latest_block_header)
    (hlep : s'.latest_execution_payload_header = s.latest_execution_payload_header)
    (hpc : s'.pending_consolidations = s.pending_consolidations)
    (hpd : s'.pending_deposits = s.pending_deposits) :
    CommonSubstep s s' :=
  commonSubstep_of_sizes (by rw [hv]) (by rw [hb]) hsl hlbh hlep hpc hpd

theorem commonSubstep_set_val {T X : BeaconState P f}
    {V : SszList Validator P.VALIDATOR_REGISTRY_LIMIT} {i : Nat} {v' : Validator} {site : String}
    (hX : X.validators = V) (hb : X.balances = T.balances)
    (hsl : X.slot = T.slot) (hlbh : X.latest_block_header = T.latest_block_header)
    (hlep : X.latest_execution_payload_header = T.latest_execution_payload_header)
    (hpc : X.pending_consolidations = T.pending_consolidations)
    (hpd : X.pending_deposits = T.pending_deposits)
    (hV : T.validators.set i v' site = .ok V) : CommonSubstep T X := by
  obtain ⟨_, hVe⟩ := set_ok hV
  exact commonSubstep_of_sizes (by rw [hX, hVe, Array.size_set]) (by rw [hb]) hsl hlbh hlep hpc hpd

theorem commonSubstep_set_bal {T X : BeaconState P f}
    {B : SszList Gwei P.VALIDATOR_REGISTRY_LIMIT} {i : Nat} {b' : Gwei} {site : String}
    (hv : X.validators = T.validators) (hX : X.balances = B)
    (hsl : X.slot = T.slot) (hlbh : X.latest_block_header = T.latest_block_header)
    (hlep : X.latest_execution_payload_header = T.latest_execution_payload_header)
    (hpc : X.pending_consolidations = T.pending_consolidations)
    (hpd : X.pending_deposits = T.pending_deposits)
    (hB : T.balances.set i b' site = .ok B) : CommonSubstep T X := by
  obtain ⟨_, hBe⟩ := set_ok hB
  exact commonSubstep_of_sizes (by rw [hv]) (by rw [hX, hBe, Array.size_set]) hsl hlbh hlep hpc hpd

theorem modify_size_eq {α : Type} {n : Nat} {xs ys : SszList α n} {i : Nat} {g : α → M α}
    {site : String} (h : xs.modify i g site = .ok ys) : ys.toArray.size = xs.toArray.size := by
  unfold SszList.modify at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, heq⟩ := set_ok h
  rw [heq, Array.size_set]

theorem commonSubstep_modify_val {T X : BeaconState P f}
    {V : SszList Validator P.VALIDATOR_REGISTRY_LIMIT} {i : Nat}
    {g : Validator → M Validator} {site : String}
    (hX : X.validators = V) (hb : X.balances = T.balances)
    (hsl : X.slot = T.slot) (hlbh : X.latest_block_header = T.latest_block_header)
    (hlep : X.latest_execution_payload_header = T.latest_execution_payload_header)
    (hpc : X.pending_consolidations = T.pending_consolidations)
    (hpd : X.pending_deposits = T.pending_deposits)
    (hV : T.validators.modify i g site = .ok V) : CommonSubstep T X :=
  commonSubstep_of_sizes (by rw [hX, modify_size_eq hV]) (by rw [hb]) hsl hlbh hlep hpc hpd

theorem commonSubstep_modify_bal {T X : BeaconState P f}
    {B : SszList Gwei P.VALIDATOR_REGISTRY_LIMIT} {i : Nat}
    {g : Gwei → M Gwei} {site : String}
    (hv : X.validators = T.validators) (hX : X.balances = B)
    (hsl : X.slot = T.slot) (hlbh : X.latest_block_header = T.latest_block_header)
    (hlep : X.latest_execution_payload_header = T.latest_execution_payload_header)
    (hpc : X.pending_consolidations = T.pending_consolidations)
    (hpd : X.pending_deposits = T.pending_deposits)
    (hB : T.balances.modify i g site = .ok B) : CommonSubstep T X :=
  commonSubstep_of_sizes (by rw [hv]) (by rw [hX, modify_size_eq hB]) hsl hlbh hlep hpc hpd

theorem commonSubstep_ite {s a b : BeaconState P f} {c : Prop} [Decidable c]
    (h1 : CommonSubstep s a) (h2 : CommonSubstep s b) :
    CommonSubstep s (if c then a else b) := by
  split
  · exact h1
  · exact h2

theorem okT_csub {γ : Type} {s s1 : BeaconState P f} {g : γ → BeaconState P f} {c : M γ}
    (hp : CommonSubstep s s1) (h : Ok c (fun r => CommonSubstep s1 (g r))) :
    Ok c (fun r => CommonSubstep s (g r)) :=
  fun a ha => hp.trans (h a ha)

theorem list_forIn_csub_proj {α β : Type} (π : β → BeaconState P f) {xs : List α}
    {init out : β} {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, Ok (body a b) (fun r => CommonSubstep (π b) (π r.value)))
    (h : forIn xs init body = .ok out) : CommonSubstep (π init) (π out) :=
  list_forIn_rel (fun a b => CommonSubstep (π a) (π b)) (fun _ => CommonSubstep.refl _)
    (fun _ _ _ h1 h2 => h1.trans h2) body (fun a b r hr => hb a b r hr) xs init out h

theorem array_forIn_csub_proj {α β : Type} (π : β → BeaconState P f) {xs : Array α}
    {init out : β} {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, Ok (body a b) (fun r => CommonSubstep (π b) (π r.value)))
    (h : forIn xs init body = .ok out) : CommonSubstep (π init) (π out) := by
  rw [← Array.forIn_toList] at h
  exact list_forIn_csub_proj π hb h

theorem range_forIn_csub_proj {β : Type} (π : β → BeaconState P f)
    {xs : Std.Legacy.Range} {init out : β} {body : Nat → β → M (ForInStep β)}
    (hb : ∀ a b, Ok (body a b) (fun r => CommonSubstep (π b) (π r.value)))
    (h : forIn xs init body = .ok out) : CommonSubstep (π init) (π out) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact list_forIn_csub_proj π hb h

theorem foldlM_csub {α : Type} {step : BeaconState P f → α → M (BeaconState P f)}
    (hstep : ∀ s a s', step s a = .ok s' → CommonSubstep s s') :
    ∀ (xs : List α) {s s' : BeaconState P f},
      List.foldlM step s xs = .ok s' → CommonSubstep s s' := by
  intro xs
  induction xs with
  | nil => intro s s' h; cases h; exact CommonSubstep.refl _
  | cons x xs ih =>
    intro s s' h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, h1, h2⟩ := bind_eq_ok_iff.mp h
    exact (hstep s x mid h1).trans (ih h2)

theorem array_foldlM_csub {α : Type} {step : BeaconState P f → α → M (BeaconState P f)}
    (hstep : ∀ s a s', step s a = .ok s' → CommonSubstep s s')
    {xs : Array α} {s s' : BeaconState P f}
    (h : Array.foldlM step s xs = .ok s') : CommonSubstep s s' := by
  rw [← Array.foldlM_toList] at h
  exact foldlM_csub hstep xs.toList h

/-! ## Join-point VCG for `CommonSubstep` -/

section Meta
open Lean Meta Elab Tactic

private def okPartsC? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity ``Ok 3 then some (e.getArg! 0, e.getArg! 1, e.getArg! 2) else none

private def csubParts (α Q : Expr) : MetaM (Expr × Expr) :=
  withLocalDeclD `r α fun r => do
    let qr := (mkApp Q r).headBeta
    unless qr.isAppOfArity ``CommonSubstep 4 do throwError "post-condition is not `CommonSubstep _ _`"
    let A := qr.getArg! 2
    if A.containsFVar r.fvarId! then throwError "post-condition base depends on the result"
    pure (A, ← mkLambdaFVars #[r] (qr.getArg! 3))

private def mkPostC (α σ g : Expr) : MetaM Expr := do
  let post ← withLocalDeclD `r α fun r => do
    mkLambdaFVars #[r] (← mkAppM ``CommonSubstep #[σ, (mkApp g r).headBeta])
  pure post.eta

private def isJpNameC (n : Name) : Bool := n.eraseMacroScopes == `__do_jp

private def findStateC : Nat → Expr → Expr → MetaM (Option Expr)
  | 0, _, _ => pure none
  | fuel + 1, x, T => do
    let T ← whnfR T
    if T.getAppFn.isConstOf ``BeaconState then return some x
    if T.isAppOfArity ``Prod 2 then
      if let some e ← findStateC fuel (← mkAppM ``Prod.fst #[x]) (T.getArg! 0) then return some e
      return ← findStateC fuel (← mkAppM ``Prod.snd #[x]) (T.getArg! 1)
    return none

elab "jp_intro_c" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (α, c, Q) := okPartsC? t | throwError "jp_intro_c: goal is not `Ok _ _`"
  let .letE n ty v b _ := c.headBeta | throwError "jp_intro_c: no `have` at the head"
  unless isJpNameC n do throwError "jp_intro_c: not a join point"
  let (A, gf) ← csubParts α Q
  let stTy ← inferType A
  let mkH (jp : Expr) : MetaM Expr := forallTelescope ty fun ys _ => do
    let mut σ := A
    for y in ys do
      if let some stExpr ← findStateC 8 y (← inferType y) then
        if ← isDefEq (← inferType stExpr) stTy then σ := stExpr
    let post ← mkPostC α σ gf
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

elab "jp_call_c" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (α, c, Q) := okPartsC? t | throwError "jp_call_c: goal is not `Ok _ _`"
  let c := c.headBeta
  let fn := c.getAppFn
  unless fn.isFVar do throwError "jp_call_c: not a call of a local"
  let (A, _) ← csubParts α Q
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isForall do continue
    let r : Option MVarId ← try
        let (mvs, _, body) ← forallMetaTelescope ty
        let some (_, c', post) := okPartsC? body | throwError "not Ok"
        unless c'.getAppFn == fn do throwError "other head"
        unless ← isDefEq c' c do throwError "args differ"
        let post ← instantiateMVars post
        let (σ, _) ← csubParts α post
        let hp ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``CommonSubstep #[A, σ]) `jp_csub
        let pf ← mkAppM ``okT_csub #[hp, mkAppN d.toExpr mvs]
        unless ← isDefEq (← inferType pf) t do throwError "type differs"
        g.assign (← instantiateMVars pf)
        pure (some hp.mvarId!)
      catch _ => pure none
    if let some hpG := r then
      replaceMainGoal [hpG]
      return
  throwError "jp_call_c: no join-point hypothesis applies"

elab "loop_csub " h:ident : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (α, c, Q) := okPartsC? t | throwError "loop_csub: goal is not `Ok _ _`"
  let d ← getLocalDeclFromUserName h.getId
  let ht ← instantiateMVars d.type
  let some (_, lhs, rhs) := ht.eq? | throwError "loop_csub: not an equation"
  unless lhs.getAppFn.isConstOf ``ForIn.forIn && lhs.getAppNumArgs ≥ 3 do
    throwError "loop_csub: not a forIn"
  let n := lhs.getAppNumArgs
  let xs := lhs.getArg! (n - 3)
  let init := lhs.getArg! (n - 2)
  let body := lhs.getArg! (n - 1)
  let ρ ← whnfR (← inferType xs)
  let lem ← if ρ.isAppOf ``List then pure ``list_forIn_csub_proj
    else if ρ.isAppOf ``Array then pure ``array_forIn_csub_proj
    else if ρ.isConstOf ``Std.Legacy.Range then pure ``range_forIn_csub_proj
    else throwError "loop_csub: collection {ρ}"
  unless rhs.isAppOfArity ``Except.ok 3 do throwError "loop_csub: not `.ok`"
  let out := rhs.appArg!
  let β ← inferType init
  let π ← withLocalDeclD `x β fun x => do
    let some e ← findStateC 8 x β | throwError "loop_csub: no state in the accumulator"
    mkLambdaFVars #[x] e
  let (A, gf) ← csubParts α Q
  let stepTy ← mkAppM ``ForInStep #[β]
  let hbTy ← forallTelescope (← inferType body) fun as _ => do
    let #[_, b] := as | throwError "loop_csub: body arity"
    let post ← withLocalDeclD `r stepTy fun r => do
      mkLambdaFVars #[r] (← mkAppM ``CommonSubstep
        #[π.beta #[b], π.beta #[← mkAppM ``ForInStep.value #[r]]])
    mkForallFVars as (mkAppN t.getAppFn #[stepTy, (mkAppN body as).headBeta, post])
  let hb ← mkFreshExprSyntheticOpaqueMVar hbTy `loop_body
  let pf ← mkAppM lem #[π, hb, d.toExpr]
  let hp ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``CommonSubstep #[A, π.beta #[init]]) `loop_pre
  let rest ← mkFreshExprSyntheticOpaqueMVar
    (mkAppN t.getAppFn #[α, c, ← mkPostC α (π.beta #[out]) gf]) `loop_rest
  let full ← mkAppM ``okT_csub #[← mkAppM ``CommonSubstep.trans #[hp, pf], rest]
  unless ← isDefEq (← inferType full) t do throwError "loop_csub: type mismatch"
  g.assign full
  let (_, hbG) ← hb.mvarId!.introN 2
  replaceMainGoal [hp.mvarId!, hbG, rest.mvarId!]

end Meta

syntax "csub_of " ident : tactic

syntax "csub_close" : tactic
macro_rules | `(tactic| csub_close) => `(tactic| first
  | with_reducible exact CommonSubstep.refl _
  | exact commonSubstep_frame rfl rfl rfl rfl rfl rfl rfl
  | (apply commonSubstep_set_val; rfl; rfl; rfl; rfl; rfl; rfl; rfl; assumption)
  | (apply commonSubstep_set_bal; rfl; rfl; rfl; rfl; rfl; rfl; rfl; assumption)
  | (apply commonSubstep_modify_val; rfl; rfl; rfl; rfl; rfl; rfl; rfl; assumption)
  | (apply commonSubstep_modify_bal; rfl; rfl; rfl; rfl; rfl; rfl; rfl; assumption)
  | (refine commonSubstep_ite ?_ ?_ <;> csub_close)
  | exact commonSubstep_frame (by split <;> rfl) (by split <;> rfl) (by split <;> rfl)
      (by split <;> rfl) (by split <;> rfl) (by split <;> rfl) (by split <;> rfl))

syntax "cstep" : tactic
macro_rules | `(tactic| cstep) => `(tactic| first
  | jp_intro_c
  | (jp_call_c; csub_close)
  | ok_head
  | with_reducible exact ok_throw
  | with_reducible exact ok_throw_bind
  | with_reducible exact ok_pure (CommonSubstep.refl _)
  | exact ok_pure (commonSubstep_frame rfl rfl rfl rfl rfl rfl rfl)
  | (refine ok_pure ?_; try dsimp -zeta only [ForInStep.value]
     csub_close)
  | exact ok_of fun _ hh => by csub_of hh
  | (refine ok_of fun _ hh => ?_; have h2 := by csub_of hh
     exact CommonSubstep.trans (by csub_close) h2)
  | with_reducible apply ok_bind_ite
  | (with_reducible apply ok_bind; intro _ hx; loop_csub hx; csub_close)
  | (with_reducible apply ok_bind; intro _ hx
     first | (refine okT_csub (CommonSubstep.trans ?_ (by csub_of hx)) ?_; csub_close) | skip)
  | (with_reducible apply ok_ite <;> intro _)
  | (with_reducible apply ok_dite <;> intro _)
  | (set_option simprocs false in dsimp -zeta only)
  | (rename_i x _; is_small_inductive x; cases x; all_goals (set_option simprocs false in dsimp -zeta only))
  | split)

/-! ## Leaf mutators satisfying `CommonSubstep` -/

theorem increaseBalance_csub {s s' : BeaconState P f} {idx : ValidatorIndex} {d : Gwei}
    (h : increaseBalance s idx d = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (increaseBalance s idx d) (CommonSubstep s)
  unfold increaseBalance; repeat cstep

theorem decreaseBalance_csub {s s' : BeaconState P f} {idx : ValidatorIndex} {d : Gwei}
    (h : decreaseBalance s idx d = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (decreaseBalance s idx d) (CommonSubstep s)
  unfold decreaseBalance; repeat cstep

theorem exitChurn_csub (cfg : Config) {s : BeaconState P f} {b : Gwei} {r : BeaconState P f × Epoch}
    (h : computeExitEpochAndUpdateChurn cfg s b = .ok r) : CommonSubstep s r.1 := by
  revert r h
  show Ok (computeExitEpochAndUpdateChurn cfg s b) (fun r => CommonSubstep s r.1)
  unfold computeExitEpochAndUpdateChurn; repeat cstep

theorem consolidationChurn_csub (cfg : Config) {s : BeaconState P f} {b : Gwei}
    {r : BeaconState P f × Epoch}
    (h : computeConsolidationEpochAndUpdateChurn cfg s b = .ok r) : CommonSubstep s r.1 := by
  obtain ⟨_, _, hr⟩ := computeConsolidationEpoch_frame h
  rw [hr]
  exact commonSubstep_frame rfl rfl rfl rfl rfl rfl rfl

theorem setPendingPartialWithdrawals_csub {s s' : BeaconState P f}
    {l : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    (h : s.setPendingPartialWithdrawals l = .ok s') : CommonSubstep s s' := by
  unfold BeaconState.setPendingPartialWithdrawals at h
  obtain ⟨g, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact commonSubstep_frame rfl rfl rfl rfl rfl rfl rfl

theorem setProposerLookahead_csub {s s' : BeaconState P f}
    {l : SszVector ValidatorIndex ((P.MIN_SEED_LOOKAHEAD + 1) * P.SLOTS_PER_EPOCH)}
    (h : s.setProposerLookahead l = .ok s') : CommonSubstep s s' := by
  unfold BeaconState.setProposerLookahead at h
  obtain ⟨g, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact commonSubstep_frame rfl rfl rfl rfl rfl rfl rfl

theorem setDepositBalanceToConsume_csub {s s' : BeaconState P f} {x : Gwei}
    (h : s.setDepositBalanceToConsume x = .ok s') : CommonSubstep s s' := by
  unfold BeaconState.setDepositBalanceToConsume at h
  obtain ⟨g, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact commonSubstep_frame rfl rfl rfl rfl rfl rfl rfl

/-- `addValidatorToRegistry` pushes one validator and, whenever `BalancesMatchValidators s` holds,
also pushes one balance entry (`idx = s.validators.length = s.balances.length`), preserving
`BalancesMatchValidators` and all non-registry fields. -/
theorem addValidatorToRegistry_csub {s s' : BeaconState P f} {pk : BLSPubkey} {wc : Bytes32}
    {amt : U64} (h : addValidatorToRegistry s pk wc amt = .ok s') : CommonSubstep s s' := by
  unfold addValidatorToRegistry at h
  obtain ⟨idx, hidx, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨V, hV, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨B, hB, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  have hn : idx.toNat = s.validators.toArray.size := U64.toNat_ofNat? hidx
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  intro hbm
  unfold BalancesMatchValidators at hbm ⊢
  unfold setOrAppendList at hV hB
  have hcv : (idx.toNat == s.validators.length) = true := by
    simp only [SszList.length, hn, beq_self_eq_true]
  have hcb : (idx.toNat == s.balances.length) = true := by
    simp only [SszList.length, hbm, hn, beq_self_eq_true]
  rw [ite_eq_left hcv] at hV
  rw [ite_eq_left hcb] at hB
  show B.toArray.size = V.toArray.size
  rw [push_ok hV, push_ok hB, Array.size_push, Array.size_push, hbm]

macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact increaseBalance_csub $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact decreaseBalance_csub $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact exitChurn_csub _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact consolidationChurn_csub _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact setPendingPartialWithdrawals_csub $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact setProposerLookahead_csub $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact setDepositBalanceToConsume_csub $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact addValidatorToRegistry_csub $h)

theorem initiate_csub_tail (cfg : Config) {s T s' : BeaconState P f} {i : ValidatorIndex}
    {v : Validator} {q : Epoch} (hT : CommonSubstep s T)
    (h : (do let d ← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY
             let w ← U64.add? q d "initiate_validator_exit"
             let V ← T.validators.set i.toNat { v with exit_epoch := q, withdrawable_epoch := w }
               "initiate_validator_exit"
             pure { T with validators := V } : M (BeaconState P f)) = .ok s') :
    CommonSubstep s s' := by
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨V, hV, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact hT.trans (commonSubstep_set_val rfl rfl rfl rfl rfl rfl rfl hV)

theorem initiateValidatorExit_csub (cfg : Config) {s s' : BeaconState P f} {idx : ValidatorIndex}
    (h : initiateValidatorExit cfg s idx = .ok s') : CommonSubstep s s' := by
  unfold initiateValidatorExit at h
  obtain ⟨v, _, h⟩ := bind_eq_ok_iff.mp h
  dsimp only at h
  split at h
  · cases h; exact CommonSubstep.refl s
  · split at h
    · obtain ⟨⟨st1, q⟩, hq, h⟩ := bind_eq_ok_iff.mp h
      exact initiate_csub_tail cfg (v := v) (exitChurn_csub cfg hq) h
    · obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨⟨st1, q'⟩, hq', h⟩ := bind_eq_ok_iff.mp h
        cases hq'
        exact initiate_csub_tail cfg (v := v) (CommonSubstep.refl s) h
      · obtain ⟨⟨st1, q'⟩, hq', h⟩ := bind_eq_ok_iff.mp h
        cases hq'
        exact initiate_csub_tail cfg (v := v) (CommonSubstep.refl s) h

macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact initiateValidatorExit_csub _ $h)

theorem slashValidator_csub (cfg : Config) {s s' : BeaconState P f} {slashed : ValidatorIndex}
    {wb : Option ValidatorIndex} (h : slashValidator cfg s slashed wb = .ok s') :
    CommonSubstep s s' := by
  revert s' h; show Ok (slashValidator cfg s slashed wb) (CommonSubstep s)
  unfold slashValidator; repeat cstep

macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact slashValidator_csub _ $h)

theorem applyPendingDeposit_csub (ctx : Ctx) {d : PendingDeposit} {s s' : BeaconState P f}
    (h : applyPendingDeposit ctx s d = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (applyPendingDeposit ctx s d) (CommonSubstep s)
  unfold applyPendingDeposit; repeat cstep

macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact applyPendingDeposit_csub _ $h)

/-! ## Block operations satisfying `CommonSubstep` -/

theorem processBlsToExecutionChange_csub (ctx : Ctx) {s s' : BeaconState P f}
    {sac : SignedBLSToExecutionChange}
    (h : processBlsToExecutionChange ctx s sac = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processBlsToExecutionChange ctx s sac) (CommonSubstep s)
  unfold processBlsToExecutionChange; repeat cstep

theorem processVoluntaryExit_csub (ctx : Ctx) {s s' : BeaconState P f} {sve : SignedVoluntaryExit}
    (h : processVoluntaryExit ctx s sve = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processVoluntaryExit ctx s sve) (CommonSubstep s)
  unfold processVoluntaryExit; repeat cstep

theorem processProposerSlashing_csub (ctx : Ctx) {s s' : BeaconState P f} {ps : ProposerSlashing}
    (h : processProposerSlashing ctx s ps = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processProposerSlashing ctx s ps) (CommonSubstep s)
  unfold processProposerSlashing; repeat cstep

theorem processAttesterSlashing_csub (ctx : Ctx) {s s' : BeaconState P f}
    {as : AttesterSlashing P f}
    (h : processAttesterSlashing ctx s as = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processAttesterSlashing ctx s as) (CommonSubstep s)
  unfold processAttesterSlashing; repeat cstep

theorem processAttestation_csub (ctx : Ctx) {a : Attestation P f} {s s' : BeaconState P f}
    (h : processAttestation ctx s a = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processAttestation ctx s a) (CommonSubstep s)
  unfold processAttestation; repeat cstep

theorem processWithdrawalRequest_csub (cfg : Config) {s s' : BeaconState P f}
    {wr : WithdrawalRequest}
    (h : processWithdrawalRequest cfg s wr = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processWithdrawalRequest cfg s wr) (CommonSubstep s)
  unfold processWithdrawalRequest; repeat cstep

theorem foldWithdrawalRequests_csub (cfg : Config) {wrs : List WithdrawalRequest}
    {s s' : BeaconState P f}
    (h : foldWithdrawalRequests cfg s wrs = .ok s') : CommonSubstep s s' :=
  foldlM_csub (fun _ _ _ hw => processWithdrawalRequest_csub cfg hw) wrs h

theorem processWithdrawals_csub {s s' : BeaconState P f} {pl : ExecutionPayload P}
    (h : processWithdrawals s pl = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processWithdrawals s pl) (CommonSubstep s)
  unfold processWithdrawals; repeat cstep

theorem processRandao_csub (ctx : Ctx) {body : BeaconBlockBody P f} {s s' : BeaconState P f}
    (h : processRandao ctx s body = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processRandao ctx s body) (CommonSubstep s)
  unfold processRandao; repeat cstep

theorem processEth1Data_csub {body : BeaconBlockBody P f} {s s' : BeaconState P f}
    (h : processEth1Data s body = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processEth1Data s body) (CommonSubstep s)
  unfold processEth1Data; repeat cstep

theorem processSyncAggregate_csub (ctx : Ctx) {sa : SyncAggregate P} {s s' : BeaconState P f}
    (h : processSyncAggregate ctx s sa = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processSyncAggregate ctx s sa) (CommonSubstep s)
  unfold processSyncAggregate; repeat cstep

macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processBlsToExecutionChange_csub _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processVoluntaryExit_csub _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processProposerSlashing_csub _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processAttesterSlashing_csub _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processAttestation_csub _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processWithdrawalRequest_csub _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processWithdrawals_csub $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processRandao_csub _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processEth1Data_csub $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processSyncAggregate_csub _ $h)

/-! ## Epoch sub-steps satisfying `CommonSubstep` -/

theorem weighJustificationAndFinalization_csub {s s' : BeaconState P f} {t p c : Gwei}
    (h : weighJustificationAndFinalization s t p c = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (weighJustificationAndFinalization s t p c) (CommonSubstep s)
  unfold weighJustificationAndFinalization; repeat cstep

macro_rules | `(tactic| csub_of $h) => `(tactic|
    with_reducible exact weighJustificationAndFinalization_csub $h)

theorem processJustificationAndFinalization_csub (cfg : Config) {s s' : BeaconState P f}
    (h : processJustificationAndFinalization cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processJustificationAndFinalization cfg s) (CommonSubstep s)
  unfold processJustificationAndFinalization; repeat cstep

theorem processInactivityUpdates_csub (cfg : Config) {s s' : BeaconState P f}
    (h : processInactivityUpdates cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processInactivityUpdates cfg s) (CommonSubstep s)
  unfold processInactivityUpdates; repeat cstep

theorem processRewardsAndPenalties_csub (cfg : Config) {s s' : BeaconState P f}
    (h : processRewardsAndPenalties cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processRewardsAndPenalties cfg s) (CommonSubstep s)
  unfold processRewardsAndPenalties; repeat cstep

theorem processRegistryUpdatesElectra_csub (cfg : Config) {s s' : BeaconState P f}
    (h : processRegistryUpdatesElectra cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processRegistryUpdatesElectra cfg s) (CommonSubstep s)
  unfold processRegistryUpdatesElectra; repeat cstep

theorem processRegistryUpdates_csub (cfg : Config) (hf : f.atLeast .electra = true)
    {s s' : BeaconState P f} (h : processRegistryUpdates cfg s = .ok s') : CommonSubstep s s' := by
  unfold processRegistryUpdates at h
  rw [ite_eq_left hf] at h
  exact processRegistryUpdatesElectra_csub cfg h

theorem processSlashings_csub (cfg : Config) {s s' : BeaconState P f}
    (h : processSlashings cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processSlashings cfg s) (CommonSubstep s)
  unfold processSlashings; repeat cstep

theorem processEth1DataReset_csub (cfg : Config) {s s' : BeaconState P f}
    (h : processEth1DataReset cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processEth1DataReset cfg s) (CommonSubstep s)
  unfold processEth1DataReset; repeat cstep

theorem processEffectiveBalanceUpdates_csub (cfg : Config) {s s' : BeaconState P f}
    (h : processEffectiveBalanceUpdates cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h
  show Ok (processEffectiveBalanceUpdates cfg s) (CommonSubstep s)
  unfold processEffectiveBalanceUpdates
  repeat (first | ok_head | (with_reducible apply ok_bind; intro _ _))
  refine ok_pure (commonSubstep_of_sizes ?_ rfl rfl rfl rfl rfl rfl)
  refine list_forIn_rel
    (fun V V' : SszList Validator P.VALIDATOR_REGISTRY_LIMIT => V'.toArray.size = V.toArray.size)
    (fun _ => rfl) (fun _ _ _ h1 h2 => h2.trans h1) _ ?_ _ _ _ (by assumption)
  intro i V r hb
  simp only [bind, Except.bind, pure, Except.pure] at hb
  repeat' split at hb
  all_goals first
    | (cases hb; rfl)
    | (cases hb; dsimp only [ForInStep.value]; obtain ⟨_, hVe⟩ := set_ok (by assumption); rw [hVe, Array.size_set])
    | cases hb

theorem processSlashingsReset_csub (cfg : Config) {s s' : BeaconState P f}
    (h : processSlashingsReset cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processSlashingsReset cfg s) (CommonSubstep s)
  unfold processSlashingsReset; repeat cstep

theorem processRandaoMixesReset_csub (cfg : Config) {s s' : BeaconState P f}
    (h : processRandaoMixesReset cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processRandaoMixesReset cfg s) (CommonSubstep s)
  unfold processRandaoMixesReset; repeat cstep

theorem processHistoricalSummariesUpdate_csub (cfg : Config) {s s' : BeaconState P f}
    (h : processHistoricalSummariesUpdate cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processHistoricalSummariesUpdate cfg s) (CommonSubstep s)
  unfold processHistoricalSummariesUpdate; repeat cstep

theorem processParticipationFlagUpdates_csub (cfg : Config) {s s' : BeaconState P f}
    (h : processParticipationFlagUpdates cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processParticipationFlagUpdates cfg s) (CommonSubstep s)
  unfold processParticipationFlagUpdates; repeat cstep

theorem processSyncCommitteeUpdates_csub (ctx : Ctx) {s s' : BeaconState P f}
    (h : processSyncCommitteeUpdates ctx s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processSyncCommitteeUpdates ctx s) (CommonSubstep s)
  unfold processSyncCommitteeUpdates; repeat cstep

theorem processProposerLookahead_csub (cfg : Config) {s s' : BeaconState P f}
    (h : processProposerLookahead cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processProposerLookahead cfg s) (CommonSubstep s)
  unfold processProposerLookahead; repeat cstep

/-! ## Queue, header, slot, epoch, block, and upgrade preservation -/

/-- `applyDeposit` at Electra+ preserves `BalancesMatchValidators`, `slot`, `latest_block_header`,
`latest_execution_payload_header`, and `pending_consolidations`, and appends at most one
`GENESIS_SLOT` entry to `pending_deposits`. -/
theorem applyDeposit_cpres_and_frame (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {pk : BLSPubkey} {wc : Bytes32} {amt : U64} {sig : BLSSignature}
    (h : applyDeposit ctx s pk wc amt sig = .ok s') :
    CorpusPres s s' ∧
    s'.slot = s.slot ∧
    s'.latest_block_header = s.latest_block_header ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
    s'.pending_consolidations = s.pending_consolidations ∧
    ∃ extra, (Gated.get hf s'.pending_deposits).toArray.toList =
      (Gated.get hf s.pending_deposits).toArray.toList ++ extra ∧
      ∀ d ∈ extra, d.slot = GENESIS_SLOT := by
  unfold applyDeposit at h
  simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false] at h
  by_cases hany : (!s.validators.toArray.any (·.pubkey == pk)) = true
  · rw [ite_eq_left hany] at h
    obtain ⟨valid, _, h⟩ := bind_eq_ok_iff.mp h
    cases valid with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at h
      cases h
      exact ⟨CorpusPres.refl _, rfl, rfl, rfl, rfl, [], by simp, by intro _ hm; cases hm⟩
    | true =>
      simp only [ite_true] at h
      obtain ⟨s1, hadd, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨q', hq', h⟩ := bind_eq_ok_iff.mp h
      unfold BeaconState.setPendingDeposits at h
      obtain ⟨g, hg, h⟩ := bind_eq_ok_iff.mp h
      cases h
      have hc1 := addValidatorToRegistry_csub hadd
      have hq0 : q = Gated.get hf s.pending_deposits := by
        unfold BeaconState.pendingDeposits at hq
        rw [hc1.pd_eq, gated_read_get hf] at hq
        exact (Except.ok.inj hq).symm
      have hg1 : g = Gated.mk hf q' := by
        rw [gated_write_eq hf] at hg
        exact (Except.ok.inj hg).symm
      refine ⟨⟨hc1.bmv, hc1.pcd⟩, hc1.slot_eq, hc1.lbh_eq, hc1.lep_eq, hc1.pc_eq,
        [{ pubkey := pk, withdrawal_credentials := wc, amount := amt,
           signature := sig, slot := GENESIS_SLOT }], ?_, ?_⟩
      · show (Gated.get hf g).toArray.toList = _
        rw [hg1, Gated.get_mk, push_ok hq', hq0, Array.toList_push]
      · intro d hd; simp only [List.mem_singleton] at hd; subst hd; rfl
  · rw [ite_eq_right hany] at h
    obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨q', hq', h⟩ := bind_eq_ok_iff.mp h
    unfold BeaconState.setPendingDeposits at h
    obtain ⟨g, hg, h⟩ := bind_eq_ok_iff.mp h
    cases h
    have hq0 : q = Gated.get hf s.pending_deposits := by
      unfold BeaconState.pendingDeposits at hq
      rw [gated_read_get hf] at hq
      exact (Except.ok.inj hq).symm
    have hg1 : g = Gated.mk hf q' := by
      rw [gated_write_eq hf] at hg
      exact (Except.ok.inj hg).symm
    refine ⟨⟨id, id⟩, rfl, rfl, rfl, rfl,
      [{ pubkey := pk, withdrawal_credentials := wc, amount := amt,
         signature := sig, slot := GENESIS_SLOT }], ?_, ?_⟩
    · show (Gated.get hf g).toArray.toList = _
      rw [hg1, Gated.get_mk, push_ok hq', hq0, Array.toList_push]
    · intro d hd; simp only [List.mem_singleton] at hd; subst hd; rfl

theorem processDeposit_cpres_and_frame (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {d : Deposit}
    (h : processDeposit ctx s d = .ok s') :
    CorpusPres s s' ∧
    s'.slot = s.slot ∧
    s'.latest_block_header = s.latest_block_header ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
    s'.pending_consolidations = s.pending_consolidations ∧
    ∃ extra, (Gated.get hf s'.pending_deposits).toArray.toList =
      (Gated.get hf s.pending_deposits).toArray.toList ++ extra ∧
      ∀ x ∈ extra, x.slot = GENESIS_SLOT := by
  unfold processDeposit at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hc, hsl, hlbh, hlep, hpc, ex, hpd, hg⟩ := applyDeposit_cpres_and_frame hf ctx h
  exact ⟨⟨hc.bmv, hc.pcd⟩, hsl, hlbh, hlep, hpc, ex, hpd, hg⟩

theorem foldDeposits_cpres_and_frame (hf : f.atLeast .electra = true) (ctx : Ctx) :
    ∀ (ds : List Deposit) {s s' : BeaconState P f},
      List.foldlM (processDeposit ctx) s ds = .ok s' →
      CorpusPres s s' ∧
      s'.slot = s.slot ∧
      s'.latest_block_header = s.latest_block_header ∧
      s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
      s'.pending_consolidations = s.pending_consolidations ∧
      ∃ extra, (Gated.get hf s'.pending_deposits).toArray.toList =
        (Gated.get hf s.pending_deposits).toArray.toList ++ extra ∧
        ∀ x ∈ extra, x.slot = GENESIS_SLOT := by
  intro ds
  induction ds with
  | nil =>
    intro s s' h; cases h
    exact ⟨CorpusPres.refl _, rfl, rfl, rfl, rfl, [], by simp, by intro _ hm; cases hm⟩
  | cons d ds ih =>
    intro s s' h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, h1, h2⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hc1, hsl1, hlbh1, hlep1, hpc1, ex1, hpd1, hg1⟩ := processDeposit_cpres_and_frame hf ctx h1
    obtain ⟨hc2, hsl2, hlbh2, hlep2, hpc2, ex2, hpd2, hg2⟩ := ih h2
    refine ⟨hc1.trans hc2, hsl2.trans hsl1, hlbh2.trans hlbh1, hlep2.trans hlep1,
      hpc2.trans hpc1, ex1 ++ ex2, ?_, ?_⟩
    · rw [hpd2, hpd1, List.append_assoc]
    · intro x hx
      rcases List.mem_append.mp hx with hx1 | hx2
      · exact hg1 x hx1
      · exact hg2 x hx2

/-- `preDeposits` (all operations before `foldDepositRequests`) preserves `CorpusPres`, `slot`,
`latest_block_header`, `latest_execution_payload_header`, and `pending_consolidations`, and appends
only `GENESIS_SLOT` entries to `pending_deposits` (none at Fulu, where `deposits` must be empty). -/
theorem preDeposits_cpres_and_frame (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {body : BeaconBlockBody P f}
    (h : preDeposits ctx s body = .ok s') :
    CorpusPres s s' ∧
    s'.slot = s.slot ∧
    s'.latest_block_header = s.latest_block_header ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
    s'.pending_consolidations = s.pending_consolidations ∧
    (f.atLeast .fulu = true → s'.pending_deposits = s.pending_deposits) ∧
    ∃ extra, (Gated.get hf s'.pending_deposits).toArray.toList =
      (Gated.get hf s.pending_deposits).toArray.toList ++ extra ∧
      ∀ x ∈ extra, x.slot = GENESIS_SLOT := by
  unfold preDeposits at h
  have hbody : ∀ {s0 : BeaconState P f}
      (hreq0 : f.atLeast .fulu = true → body.deposits.toArray.toList = []),
      (do
        let mut st := s0
        for op in body.proposer_slashings.toArray do st ← processProposerSlashing ctx st op
        for op in body.attester_slashings.toArray do st ← processAttesterSlashing ctx st op
        for op in body.attestations.toArray do st ← processAttestation ctx st op
        for op in body.deposits.toArray do st ← processDeposit ctx st op
        for op in body.voluntary_exits.toArray do st ← processVoluntaryExit ctx st op
        for op in body.bls_to_execution_changes.toArray do st ← processBlsToExecutionChange ctx st op
        pure st) = .ok s' →
      CorpusPres s0 s' ∧
      s'.slot = s0.slot ∧
      s'.latest_block_header = s0.latest_block_header ∧
      s'.latest_execution_payload_header = s0.latest_execution_payload_header ∧
      s'.pending_consolidations = s0.pending_consolidations ∧
      (f.atLeast .fulu = true → s'.pending_deposits = s0.pending_deposits) ∧
      ∃ extra, (Gated.get hf s'.pending_deposits).toArray.toList =
        (Gated.get hf s0.pending_deposits).toArray.toList ++ extra ∧
        ∀ x ∈ extra, x.slot = GENESIS_SLOT := by
    intro s0 hreq0 hb
    simp only [forArr_yield] at hb
    obtain ⟨s1, h1, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨s2, h2, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨s3, h3, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨s4, h4, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨s5, h5, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨s6, h6, hpure⟩ := bind_eq_ok_iff.mp hb
    cases hpure
    have c1 := (foldlM_csub (fun _ _ _ hh => processProposerSlashing_csub ctx hh) _ h1).trans <|
      (foldlM_csub (fun _ _ _ hh => processAttesterSlashing_csub ctx hh) _ h2).trans <|
      foldlM_csub (fun _ _ _ hh => processAttestation_csub ctx hh) _ h3
    obtain ⟨cd, hsld, hlbhd, hlepd, hpcd, ex, hpdd, hgd⟩ := foldDeposits_cpres_and_frame hf ctx _ h4
    have c2 := (foldlM_csub (fun _ _ _ hh => processVoluntaryExit_csub ctx hh) _ h5).trans <|
      foldlM_csub (fun _ _ _ hh => processBlsToExecutionChange_csub ctx hh) _ h6
    refine ⟨c1.corpusPres.trans (cd.trans c2.corpusPres),
      c2.slot_eq.trans (hsld.trans c1.slot_eq),
      c2.lbh_eq.trans (hlbhd.trans c1.lbh_eq),
      c2.lep_eq.trans (hlepd.trans c1.lep_eq),
      c2.pc_eq.trans (hpcd.trans c1.pc_eq), ?_, ex, ?_, hgd⟩
    · intro hfu
      rw [hreq0 hfu] at h4
      cases h4
      exact c2.pd_eq.trans c1.pd_eq
    · rw [c2.pd_eq, hpdd, c1.pd_eq]
  by_cases hfu : f.atLeast .fulu = true
  · rw [ite_eq_left hfu] at h
    obtain ⟨_, hreq, h⟩ := bind_eq_ok_iff.mp h
    have hlen : body.deposits.toArray.toList = [] := by
      have hb0 : (body.deposits.length == 0) = true := require_eq_ok_iff.mp hreq
      have hsz : body.deposits.toArray.size = 0 := beq_iff_eq.mp hb0
      exact Array.toList_eq_nil_iff.mpr (Array.eq_empty_of_size_eq_zero hsz)
    exact hbody (fun _ => hlen) h
  · rw [ite_eq_right hfu] at h
    simp only [hf, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] at h
    obtain ⟨startIndex, _, h⟩ := bind_eq_ok_iff.mp h
    by_cases hlim : s.eth1_deposit_index <
        (if s.eth1_data.deposit_count < startIndex then s.eth1_data.deposit_count else startIndex)
    · rw [ite_eq_left hlim] at h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      exact hbody (fun hh => absurd hh hfu) h
    · rw [ite_eq_right hlim] at h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      exact hbody (fun hh => absurd hh hfu) h

theorem foldDepositRequests_corpusPres (hf : f.atLeast .electra = true)
    {drs : List DepositRequest} {s s' : BeaconState P f}
    (h : foldDepositRequests s drs = .ok s') : CorpusPres s s' := by
  obtain ⟨_, _, hfr⟩ := foldDepositRequests_spec hf drs h
  refine ⟨fun hbm => ?_, fun hpcd => ?_⟩
  · unfold BalancesMatchValidators at hbm ⊢
    rw [hfr]; exact hbm
  · unfold PendingConsolidationsDistinct at hpcd ⊢
    rw [pendingConsolidationsList_congr (by rw [hfr])]; exact hpcd

theorem foldConsolidationRequests_corpusPres (hf : f.atLeast .electra = true) (cfg : Config)
    {crs : List ConsolidationRequest} {s s' : BeaconState P f}
    (h : foldConsolidationRequests cfg s crs = .ok s') : CorpusPres s s' := by
  obtain ⟨outcomes, _, _, _, _, _, _, hvsz, hbsz, hdist, hpc, _, _⟩ :=
    foldConsolidationRequests_frames_and_queues hf cfg crs h
  refine ⟨fun hbm => ?_, fun hpcd => ?_⟩
  · unfold BalancesMatchValidators at hbm ⊢
    omega
  · unfold PendingConsolidationsDistinct at hpcd ⊢
    rw [pendingConsolidationsList_eq_get hf] at hpcd ⊢
    rw [hpc]
    intro pc hmem
    rcases List.mem_append.mp hmem with h1 | h2
    · exact hpcd pc h1
    · exact hdist pc h2

theorem processOperations_corpusPres (hf : f.atLeast .electra = true) (ctx : Ctx)
    {body : BeaconBlockBody P f} {s s' : BeaconState P f}
    (h : processOperations ctx s body = .ok s') : CorpusPres s s' := by
  rw [processOperations_split_all ctx s body hf] at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h4⟩ := bind_eq_ok_iff.mp h
  exact (preDeposits_cpres_and_frame hf ctx h1).1.trans <|
    (foldDepositRequests_corpusPres hf h2).trans <|
    (foldWithdrawalRequests_csub ctx.cfg h3).corpusPres.trans <|
    foldConsolidationRequests_corpusPres hf ctx.cfg h4

theorem processBlockHeader_corpusPres {blk : BeaconBlock P f} {s s' : BeaconState P f}
    (h : processBlockHeader s blk = .ok s') :
    CorpusPres s s' ∧
    s'.slot = s.slot ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
    s'.pending_consolidations = s.pending_consolidations ∧
    s'.pending_deposits = s.pending_deposits := by
  unfold processBlockHeader at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact ⟨⟨id, id⟩, rfl, rfl, rfl, rfl⟩

theorem processExecutionPayload_corpusPres (ctx : Ctx) {body : BeaconBlockBody P f}
    {s s' : BeaconState P f} (h : processExecutionPayload ctx s body = .ok s') :
    CorpusPres s s' ∧
    s'.slot = s.slot ∧
    s'.latest_block_header = s.latest_block_header ∧
    s'.pending_consolidations = s.pending_consolidations ∧
    s'.pending_deposits = s.pending_deposits := by
  unfold processExecutionPayload at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨⟨id, id⟩, rfl, rfl, rfl, rfl⟩)
    | cases h

theorem processBlock_corpusPres (hf : f.atLeast .electra = true) (ctx : Ctx)
    {blk : BeaconBlock P f} {s s' : BeaconState P f}
    (h : processBlock ctx s blk = .ok s') : CorpusPres s s' := by
  unfold processBlock processBlockWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h7⟩ := bind_eq_ok_iff.mp h
  exact (processBlockHeader_corpusPres h1).1.trans <|
    (processWithdrawals_csub h2).corpusPres.trans <|
    (processExecutionPayload_corpusPres ctx h3).1.trans <|
    (processRandao_csub ctx h4).corpusPres.trans <|
    (processEth1Data_csub h5).corpusPres.trans <|
    (processOperations_corpusPres hf ctx h6).trans <|
    (processSyncAggregate_csub ctx h7).corpusPres

/-- `processPendingDeposits` preserves `CorpusPres`, `slot`, `latest_block_header`,
`latest_execution_payload_header`, and `pending_consolidations`. -/
theorem processPendingDeposits_cpres_and_frame (ctx : Ctx)
    {s s' : BeaconState P f} (h : processPendingDeposits ctx s = .ok s') :
    CorpusPres s s' ∧
    s'.slot = s.slot ∧
    s'.latest_block_header = s.latest_block_header ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
    s'.pending_consolidations = s.pending_consolidations := by
  rw [processPendingDeposits_eq] at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pending, hpend, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out, hloop, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, applied, _, _, _, hfold, _, _, _⟩ := pendingDepositsLoop_fate _ _ _ hloop
  have hc_mid := foldlM_csub (fun _ _ _ ha => applyPendingDeposit_csub ctx ha) applied hfold
  obtain ⟨q, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨st1, hst1, h⟩ := bind_eq_ok_iff.mp h
  unfold BeaconState.setPendingDeposits at hst1
  obtain ⟨g, _, hst1⟩ := bind_eq_ok_iff.mp hst1
  cases hst1
  have hc_tail : CommonSubstep { out.2.2.2.2 with pending_deposits := g } s' := by
    split at h
    · obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      exact setDepositBalanceToConsume_csub h
    · exact setDepositBalanceToConsume_csub h
  have hc_set : CorpusPres out.2.2.2.2 { out.2.2.2.2 with pending_deposits := g } :=
    ⟨id, by unfold PendingConsolidationsDistinct; exact id⟩
  exact ⟨hc_mid.corpusPres.trans (hc_set.trans hc_tail.corpusPres),
    hc_tail.slot_eq.trans hc_mid.slot_eq,
    hc_tail.lbh_eq.trans hc_mid.lbh_eq,
    hc_tail.lep_eq.trans hc_mid.lep_eq,
    hc_tail.pc_eq.trans hc_mid.pc_eq⟩

/-- `processPendingConsolidations` preserves `CorpusPres`, `slot`, `latest_block_header`,
`latest_execution_payload_header`, and `pending_deposits`. -/
theorem processPendingConsolidations_cpres_and_frame (hf : f.atLeast .electra = true) (cfg : Config)
    {s s' : BeaconState P f} (h : processPendingConsolidations cfg s = .ok s') :
    CorpusPres s s' ∧
    s'.slot = s.slot ∧
    s'.latest_block_header = s.latest_block_header ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
    s'.pending_deposits = s.pending_deposits := by
  rw [processPendingConsolidations_eq] at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨nextEpoch, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pending, hpend, h⟩ := bind_eq_ok_iff.mp h
  have hpq : pending = Gated.get hf s.pending_consolidations := by
    unfold BeaconState.pendingConsolidations at hpend
    rw [gated_read_get hf] at hpend
    exact (Except.ok.inj hpend).symm
  subst hpq
  obtain ⟨out, hloop, h⟩ := bind_eq_ok_iff.mp h
  rw [pendingConsolidationsLoop_eq_forIn] at hloop
  have hc_loop : CommonSubstep s out.1 := by
    refine list_forIn_csub_proj Prod.fst (fun pc acc r hr => ?_) hloop
    obtain ⟨src, _, hsp⟩ := pendingConsolidationStep_spec hr
    rcases hsp with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, bal, mid, st', _, hdec, hinc, rfl⟩
    · exact CommonSubstep.refl _
    · exact CommonSubstep.refl _
    · exact (decreaseBalance_csub hdec).trans (increaseBalance_csub hinc)
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  unfold BeaconState.setPendingConsolidations at h
  obtain ⟨g, hg, h⟩ := bind_eq_ok_iff.mp h
  cases h
  have hgq : g = Gated.mk hf q := by
    rw [gated_write_eq hf] at hg; exact (Except.ok.inj hg).symm
  have hq_arr : q.toArray =
      (Gated.get hf s.pending_consolidations).toArray.extract out.2
        (Gated.get hf s.pending_consolidations).length := by
    unfold SszList.ofArray at hq
    split at hq
    · cases hq; rfl
    · cases hq
  refine ⟨⟨hc_loop.bmv, ?_⟩, hc_loop.slot_eq, hc_loop.lbh_eq, hc_loop.lep_eq, hc_loop.pd_eq⟩
  intro hpcd
  unfold PendingConsolidationsDistinct at hpcd ⊢
  rw [pendingConsolidationsList_eq_get hf] at hpcd ⊢
  show ∀ pc ∈ (Gated.get hf g).toArray.toList, pc.source_index ≠ pc.target_index
  rw [hgq, Gated.get_mk, hq_arr, Array.toList_extract]
  intro pc hmem
  exact hpcd pc (List.mem_of_mem_drop (List.mem_of_mem_take hmem))

theorem processEpoch_cpres_and_frame (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} (h : processEpoch ctx s = .ok s') :
    CorpusPres s s' ∧
    s'.slot = s.slot ∧
    s'.latest_block_header = s.latest_block_header ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header := by
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
  have c_pre : CommonSubstep s s6 :=
    (processJustificationAndFinalization_csub _ h1).trans <|
    (processInactivityUpdates_csub _ h2).trans <|
    (processRewardsAndPenalties_csub _ h3).trans <|
    (processRegistryUpdates_csub _ hf h4).trans <|
    (processSlashings_csub _ h5).trans <|
    processEth1DataReset_csub _ h6
  have c_dep := processPendingDeposits_cpres_and_frame ctx h7a
  have c_con := processPendingConsolidations_cpres_and_frame hf ctx.cfg h7
  have c_post13 : CommonSubstep s7 s13 :=
    (processEffectiveBalanceUpdates_csub _ h8).trans <|
    (processSlashingsReset_csub _ h9).trans <|
    (processRandaoMixesReset_csub _ h10).trans <|
    (processHistoricalSummariesUpdate_csub _ h11).trans <|
    (processParticipationFlagUpdates_csub _ h12).trans <|
    processSyncCommitteeUpdates_csub _ h13
  have c_end : CommonSubstep s13 s' := by
    split at h
    · exact processProposerLookahead_csub _ h
    · cases h; exact CommonSubstep.refl _
  have c_post := c_post13.trans c_end
  exact ⟨c_pre.corpusPres.trans (c_dep.1.trans (c_con.1.trans c_post.corpusPres)),
    c_post.slot_eq.trans (c_con.2.1.trans (c_dep.2.1.trans c_pre.slot_eq)),
    c_post.lbh_eq.trans (c_con.2.2.1.trans (c_dep.2.2.1.trans c_pre.lbh_eq)),
    c_post.lep_eq.trans (c_con.2.2.2.1.trans (c_dep.2.2.2.1.trans c_pre.lep_eq))⟩

theorem processSlot_cpres_and_frame {s s' : BeaconState P f} (h : processSlot s = .ok s') :
    CorpusPres s s' ∧
    s'.slot = s.slot ∧
    s'.validators = s.validators ∧
    s'.balances = s.balances ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
    s'.pending_consolidations = s.pending_consolidations ∧
    s'.pending_deposits = s.pending_deposits := by
  unfold processSlot at h
  generalize Ssz.hashTreeRoot s = prevStateRoot at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine ⟨⟨fun hbm => ?_, fun hpcd => ?_⟩,
    by split <;> rfl, by split <;> rfl, by split <;> rfl,
    by split <;> rfl, by split <;> rfl, by split <;> rfl⟩
  · unfold BalancesMatchValidators at hbm ⊢
    split <;> exact hbm
  · unfold PendingConsolidationsDistinct at hpcd ⊢
    split <;> exact hpcd

theorem processSlots_corpusPres (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {slot : Slot}
    (h : processSlots ctx s slot = .ok s') :
    CorpusPres s s' ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header := by
  unfold processSlots processSlotsWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨slotsPerEpoch, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s_out, h, hpure⟩ := bind_eq_ok_iff.mp h
  cases hpure
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact list_forIn_rel
    (fun a b => CorpusPres a b ∧ b.latest_execution_payload_header = a.latest_execution_payload_header)
    (fun _ => ⟨CorpusPres.refl _, rfl⟩)
    (fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩) _
    (fun _ st r hr => by
      obtain ⟨st1, hslot, hr⟩ := bind_eq_ok_iff.mp hr
      have hc1 := processSlot_cpres_and_frame hslot
      obtain ⟨next, _, hr⟩ := bind_eq_ok_iff.mp hr
      obtain ⟨rem, _, hr⟩ := bind_eq_ok_iff.mp hr
      simp only [] at hr
      split at hr
      · obtain ⟨st2, hep, hr⟩ := bind_eq_ok_iff.mp hr
        cases hr
        have hc2 := processEpoch_cpres_and_frame hf ctx hep
        exact ⟨hc1.1.trans ⟨hc2.1.bmv, hc2.1.pcd⟩, hc2.2.2.2.trans hc1.2.2.2.2.1⟩
      · cases hr
        exact ⟨⟨hc1.1.bmv, hc1.1.pcd⟩, hc1.2.2.2.2.1⟩)
    _ _ _ h

/-- `upgradeToFulu` copies `validators`, `balances`, `pending_consolidations`, `pending_deposits`,
`slot`, `latest_block_header`, and `latest_execution_payload_header` verbatim, preserving
`CorpusPres`. -/
theorem upgradeToFulu_cpres_and_frame (cfg : Config)
    {pre : BeaconState P .electra} {post : BeaconState P .fulu}
    (h : upgradeToFulu cfg pre = .ok post) :
    CorpusPres pre post ∧
    post.validators = pre.validators ∧
    post.balances = pre.balances ∧
    post.slot = pre.slot ∧
    post.latest_block_header = pre.latest_block_header ∧
    post.latest_execution_payload_header = pre.latest_execution_payload_header ∧
    pendingConsolidationsList post = pendingConsolidationsList pre ∧
    Gated.get rfl post.pending_consolidations =
      Gated.get rfl pre.pending_consolidations ∧
    Gated.get rfl post.pending_deposits =
      Gated.get rfl pre.pending_deposits := by
  unfold upgradeToFulu at h
  obtain ⟨epoch, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ver, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨drsi, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨dbtc, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ebtc, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨eee, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨cbtc, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ece, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pd, hpd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ppw, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pc, hpc, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨la, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pl, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  have hpc_eq : pc = Gated.get rfl pre.pending_consolidations := (Except.ok.inj hpc).symm
  have hpd_eq : pd = Gated.get rfl pre.pending_deposits := (Except.ok.inj hpd).symm
  refine ⟨⟨fun hbm => hbm, fun hpcd => ?_⟩, rfl, rfl, rfl, rfl, rfl, ?_, hpc_eq, hpd_eq⟩
  · unfold PendingConsolidationsDistinct at hpcd ⊢
    rw [pendingConsolidationsList_eq_get (f := .fulu) rfl]
    rw [pendingConsolidationsList_eq_get (f := .electra) rfl] at hpcd
    exact hpc_eq.symm ▸ hpcd
  · rw [pendingConsolidationsList_eq_get (f := .fulu) rfl,
        pendingConsolidationsList_eq_get (f := .electra) rfl]
    exact congrArg (fun x => x.toArray.toList) hpc_eq

theorem stateTransition_corpusPres (hf : f.atLeast .electra = true) (ctx : Ctx)
    {s s' : BeaconState P f} {sb : SignedBeaconBlock P f} {vr : Bool}
    (h : stateTransition ctx s sb vr = .ok s') : CorpusPres s s' := by
  unfold stateTransition stateTransitionWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  have c1 := (processSlots_corpusPres hf ctx h1).1
  cases vr with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
    cases h
    exact c1.trans (processBlock_corpusPres hf ctx h2)
  | true =>
    simp only [ite_true] at h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    cases h
    exact c1.trans (processBlock_corpusPres hf ctx h2)

/-! ## `jointTransitionAt` (both `atSlot = false` and `atSlot = true`), `jointStep`, `JointReach` -/

open Jaune in
/-- `jointTransitionAt` preserves `AnchorInv`, `BalancesMatchValidators`, and
`PendingConsolidationsDistinct` at Electra and Fulu — including when `atSlot = true` (Electra
ingress at the fork slot without `processSlots`). -/
theorem jointTransitionAt_corpusPres {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (hf : f.atLeast .electra = true)
    {beacon beacon' : BeaconState P f} {exec exec' : BlockChain}
    {sb : SignedBeaconBlock P f} {atSlot : Bool}
    (h : jointTransitionAt cfg ccfg bls beacon exec sb atSlot = .ok (beacon', exec')) :
    Pres beacon beacon' ∧ CorpusPres beacon beacon' := by
  obtain ⟨req, _, _, hb⟩ := jointTransitionAt_ok_iff.mp h
  by_cases hat : atSlot = true
  · rw [ite_eq_left hat] at hb
    obtain ⟨_, _, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨_, _, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨s, hproc, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨_, _, hb⟩ := bind_eq_ok_iff.mp hb
    cases hb
    exact ⟨processBlock_pres _ hproc, processBlock_corpusPres hf _ hproc⟩
  · rw [ite_eq_right hat] at hb
    exact ⟨stateTransition_pres _ hf hb, stateTransition_corpusPres hf _ hb⟩

open Jaune in
theorem jointTransitionAt_corpusAnchorInv {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (hf : f.atLeast .electra = true)
    {beacon beacon' : BeaconState P f} {exec exec' : BlockChain}
    {sb : SignedBeaconBlock P f} {atSlot : Bool}
    (h : jointTransitionAt cfg ccfg bls beacon exec sb atSlot = .ok (beacon', exec'))
    (hI : CorpusAnchorInv beacon) : CorpusAnchorInv beacon' := by
  obtain ⟨hp, hcp⟩ := jointTransitionAt_corpusPres hf h
  exact ⟨hp.anchor hI.1, hcp.bmv hI.2.1, hcp.pcd hI.2.2⟩

open Jaune in
theorem jointStep_electra_corpusPres {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .electra}
    {s' : JointState P}
    (h : jointStep cfg ccfg bls ⟨.electra, beacon, exec⟩ ⟨.electra, sb⟩ = .ok s') :
    CorpusPres beacon s'.beacon := by
  obtain ⟨_, req, b', e', _, _, hst, rfl⟩ := jointStep_electra_ok_iff.mp h
  exact stateTransition_corpusPres (by decide) _ hst

open Jaune in
theorem jointStep_fulu_corpusPres {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .fulu} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
    {s' : JointState P}
    (h : jointStep cfg ccfg bls ⟨.fulu, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok s') :
    CorpusPres beacon s'.beacon := by
  obtain ⟨req, b', e', _, _, hst, rfl⟩ := jointStep_fulu_ok_iff.mp h
  exact stateTransition_corpusPres (by decide) _ hst

open Jaune in
theorem jointStep_cross_corpusPres {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
    {s' : JointState P}
    (h : jointStep cfg ccfg bls ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok s') :
    CorpusPres beacon s'.beacon := by
  obtain ⟨_, _, req, fslot, b1, b2, b', e', _, hb1, hb2, _, _, hb', rfl⟩ :=
    jointStep_cross_ok_iff.mp h
  have c1 : CorpusPres beacon b1 := by
    split at hb1
    · exact (processSlots_corpusPres (by decide) _ hb1).1
    · cases hb1; exact CorpusPres.refl _
  have c2 : CorpusPres b1 b2 := (upgradeToFulu_cpres_and_frame ccfg hb2).1
  have c3 : CorpusPres b2 b' := by
    split at hb'
    · obtain ⟨_, _, hb'⟩ := bind_eq_ok_iff.mp hb'
      obtain ⟨_, _, hb'⟩ := bind_eq_ok_iff.mp hb'
      obtain ⟨s, hproc, hb'⟩ := bind_eq_ok_iff.mp hb'
      obtain ⟨_, _, hb'⟩ := bind_eq_ok_iff.mp hb'
      cases hb'
      exact processBlock_corpusPres (by decide) _ hproc
    · exact stateTransition_corpusPres (by decide) _ hb'
  exact c1.trans (c2.trans c3)

open Jaune in
/-- One successful `jointStep` preserves `CorpusPres` (`BalancesMatchValidators` and
`PendingConsolidationsDistinct`) across all three accepted fork pairs (Electra→Electra,
Fulu→Fulu, and Electra→Fulu crossing). -/
theorem jointStep_corpusPres {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') : CorpusPres s.beacon s'.beacon := by
  obtain ⟨fs, beacon, exec⟩ := s
  obtain ⟨fb, sb⟩ := b
  cases fs <;> cases fb
  all_goals first
    | exact jointStep_electra_corpusPres h
    | exact jointStep_fulu_corpusPres h
    | exact jointStep_cross_corpusPres h
    | (unfold jointStep at h; cases h)

open Jaune in
theorem jointStep_balancesMatchValidators {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') (hB : BalancesMatchValidators s.beacon) :
    BalancesMatchValidators s'.beacon :=
  (jointStep_corpusPres h).bmv hB

open Jaune in
theorem jointStep_pendingConsolidationsDistinct {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') (hD : PendingConsolidationsDistinct s.beacon) :
    PendingConsolidationsDistinct s'.beacon :=
  (jointStep_corpusPres h).pcd hD

open Jaune in
theorem jointStep_corpusAnchorInv {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') (hI : CorpusAnchorInv s.beacon) :
    CorpusAnchorInv s'.beacon :=
  ⟨jointStep_anchorInv h hI.1,
   jointStep_balancesMatchValidators h hI.2.1,
   jointStep_pendingConsolidationsDistinct h hI.2.2⟩

open Jaune in
theorem JointReach.corpusPres {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (h : JointReach cfg ccfg bls s₀ s) : CorpusPres s₀.beacon s.beacon := by
  induction h with
  | refl => exact CorpusPres.refl _
  | step _ _ hs ih => exact ih.trans (jointStep_corpusPres hs)

open Jaune in
theorem JointReach.balancesMatchValidators {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (h : JointReach cfg ccfg bls s₀ s)
    (h0 : BalancesMatchValidators s₀.beacon) : BalancesMatchValidators s.beacon :=
  h.corpusPres.bmv h0

open Jaune in
theorem JointReach.pendingConsolidationsDistinct {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (h : JointReach cfg ccfg bls s₀ s)
    (h0 : PendingConsolidationsDistinct s₀.beacon) : PendingConsolidationsDistinct s.beacon :=
  h.corpusPres.pcd h0

open Jaune in
theorem JointReach.corpusAnchorInv {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (h : JointReach cfg ccfg bls s₀ s)
    (h0 : CorpusAnchorInv s₀.beacon) : CorpusAnchorInv s.beacon :=
  ⟨h.anchorInv h0.1, h.balancesMatchValidators h0.2.1, h.pendingConsolidationsDistinct h0.2.2⟩

end JauneConsensus.Facts
