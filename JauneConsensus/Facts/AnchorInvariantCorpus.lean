import JauneConsensus.Facts.AnchorInvariantComposite
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

variable {P : Preset} {f : ConsensusFork}

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
    pendingConsolidationsList st = (ForkField.get h st.pending_consolidations).toArray.toList := by
  unfold pendingConsolidationsList BeaconState.pendingConsolidations
  rw [forkField_read_get h]

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
def CorpusAnchorInvariant (st : BeaconState P f) : Prop :=
  AnchorInvariant st ∧ BalancesMatchValidators st ∧ PendingConsolidationsDistinct st

/-- Cross-fork preservation of `BalancesMatchValidators` and `PendingConsolidationsDistinct`. -/
structure CorpusPreservation {f1 f2 : ConsensusFork} (s : BeaconState P f1) (s' : BeaconState P f2) : Prop where
  balancesMatchValidators : BalancesMatchValidators s → BalancesMatchValidators s'
  pendingConsolidationsDistinct : PendingConsolidationsDistinct s → PendingConsolidationsDistinct s'

theorem CorpusPreservation.refl (s : BeaconState P f) : CorpusPreservation s s := ⟨id, id⟩

theorem CorpusPreservation.trans {f1 f2 f3 : ConsensusFork} {a : BeaconState P f1} {b : BeaconState P f2}
    {c : BeaconState P f3} (h1 : CorpusPreservation a b) (h2 : CorpusPreservation b c) : CorpusPreservation a c :=
  ⟨fun h => h2.balancesMatchValidators (h1.balancesMatchValidators h), fun h => h2.pendingConsolidationsDistinct (h1.pendingConsolidationsDistinct h)⟩

/-! ## `CommonSubstep`: shared preservation and frame relation for non-queue mutators -/

/-- A consensus sub-step that preserves `BalancesMatchValidators` and leaves `slot`,
`latest_block_header`, `latest_execution_payload_header`, `pending_consolidations`, and
`pending_deposits` untouched. -/
structure CommonSubstep (s s' : BeaconState P f) : Prop where
  balancesMatchValidators : BalancesMatchValidators s → BalancesMatchValidators s'
  slot_eq : s'.slot = s.slot
  latestBlockHeader_eq : s'.latest_block_header = s.latest_block_header
  latestExecutionPayloadHeader_eq : s'.latest_execution_payload_header = s.latest_execution_payload_header
  pendingConsolidations_eq : s'.pending_consolidations = s.pending_consolidations
  pendingDeposits_eq : s'.pending_deposits = s.pending_deposits

theorem CommonSubstep.refl (s : BeaconState P f) : CommonSubstep s s :=
  ⟨id, rfl, rfl, rfl, rfl, rfl⟩

theorem CommonSubstep.trans {a b c : BeaconState P f}
    (h1 : CommonSubstep a b) (h2 : CommonSubstep b c) : CommonSubstep a c :=
  ⟨fun h => h2.balancesMatchValidators (h1.balancesMatchValidators h),
   h2.slot_eq.trans h1.slot_eq,
   h2.latestBlockHeader_eq.trans h1.latestBlockHeader_eq,
   h2.latestExecutionPayloadHeader_eq.trans h1.latestExecutionPayloadHeader_eq,
   h2.pendingConsolidations_eq.trans h1.pendingConsolidations_eq,
   h2.pendingDeposits_eq.trans h1.pendingDeposits_eq⟩

theorem CommonSubstep.pendingConsolidationsDistinct {s s' : BeaconState P f} (h : CommonSubstep s s') :
    PendingConsolidationsDistinct s → PendingConsolidationsDistinct s' := by
  unfold PendingConsolidationsDistinct
  rw [pendingConsolidationsList_congr h.pendingConsolidations_eq]
  exact id

theorem CommonSubstep.corpusPreservation {s s' : BeaconState P f} (h : CommonSubstep s s') :
    CorpusPreservation s s' :=
  ⟨h.balancesMatchValidators, h.pendingConsolidationsDistinct⟩

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

theorem commonSubstep_set_validators {T X : BeaconState P f}
    {V : Ssz.List Validator P.VALIDATOR_REGISTRY_LIMIT} {i : Nat} {v' : Validator} {site : String}
    (hX : X.validators = V) (hb : X.balances = T.balances)
    (hsl : X.slot = T.slot) (hlbh : X.latest_block_header = T.latest_block_header)
    (hlep : X.latest_execution_payload_header = T.latest_execution_payload_header)
    (hpc : X.pending_consolidations = T.pending_consolidations)
    (hpd : X.pending_deposits = T.pending_deposits)
    (hV : T.validators.set i v' site = .ok V) : CommonSubstep T X := by
  obtain ⟨_, hVe⟩ := set_ok hV
  exact commonSubstep_of_sizes (by rw [hX, hVe, Array.size_set]) (by rw [hb]) hsl hlbh hlep hpc hpd

theorem commonSubstep_set_balances {T X : BeaconState P f}
    {B : Ssz.List Gwei P.VALIDATOR_REGISTRY_LIMIT} {i : Nat} {b' : Gwei} {site : String}
    (hv : X.validators = T.validators) (hX : X.balances = B)
    (hsl : X.slot = T.slot) (hlbh : X.latest_block_header = T.latest_block_header)
    (hlep : X.latest_execution_payload_header = T.latest_execution_payload_header)
    (hpc : X.pending_consolidations = T.pending_consolidations)
    (hpd : X.pending_deposits = T.pending_deposits)
    (hB : T.balances.set i b' site = .ok B) : CommonSubstep T X := by
  obtain ⟨_, hBe⟩ := set_ok hB
  exact commonSubstep_of_sizes (by rw [hv]) (by rw [hX, hBe, Array.size_set]) hsl hlbh hlep hpc hpd

theorem modify_size_eq {α : Type} {n : Nat} {xs ys : Ssz.List α n} {i : Nat} {g : α → Fallible α}
    {site : String} (h : xs.modify i g site = .ok ys) : ys.toArray.size = xs.toArray.size := by
  unfold Ssz.List.modify at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, heq⟩ := set_ok h
  rw [heq, Array.size_set]

theorem commonSubstep_modify_validators {T X : BeaconState P f}
    {V : Ssz.List Validator P.VALIDATOR_REGISTRY_LIMIT} {i : Nat}
    {g : Validator → Fallible Validator} {site : String}
    (hX : X.validators = V) (hb : X.balances = T.balances)
    (hsl : X.slot = T.slot) (hlbh : X.latest_block_header = T.latest_block_header)
    (hlep : X.latest_execution_payload_header = T.latest_execution_payload_header)
    (hpc : X.pending_consolidations = T.pending_consolidations)
    (hpd : X.pending_deposits = T.pending_deposits)
    (hV : T.validators.modify i g site = .ok V) : CommonSubstep T X :=
  commonSubstep_of_sizes (by rw [hX, modify_size_eq hV]) (by rw [hb]) hsl hlbh hlep hpc hpd

theorem commonSubstep_modify_balances {T X : BeaconState P f}
    {B : Ssz.List Gwei P.VALIDATOR_REGISTRY_LIMIT} {i : Nat}
    {g : Gwei → Fallible Gwei} {site : String}
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

theorem ok_trans_commonSubstep {γ : Type} {s s1 : BeaconState P f} {g : γ → BeaconState P f} {c : Fallible γ}
    (hp : CommonSubstep s s1) (h : Ok c (fun r => CommonSubstep s1 (g r))) :
    Ok c (fun r => CommonSubstep s (g r)) :=
  fun a ha => hp.trans (h a ha)

theorem list_forIn_commonSubstep_projection {α β : Type} (π : β → BeaconState P f) {xs : List α}
    {init out : β} {body : α → β → Fallible (ForInStep β)}
    (hb : ∀ a b, Ok (body a b) (fun r => CommonSubstep (π b) (π r.value)))
    (h : forIn xs init body = .ok out) : CommonSubstep (π init) (π out) :=
  list_forIn_relation (fun a b => CommonSubstep (π a) (π b)) (fun _ => CommonSubstep.refl _)
    (fun _ _ _ h1 h2 => h1.trans h2) body (fun a b r hr => hb a b r hr) xs init out h

theorem array_forIn_commonSubstep_projection {α β : Type} (π : β → BeaconState P f) {xs : Array α}
    {init out : β} {body : α → β → Fallible (ForInStep β)}
    (hb : ∀ a b, Ok (body a b) (fun r => CommonSubstep (π b) (π r.value)))
    (h : forIn xs init body = .ok out) : CommonSubstep (π init) (π out) := by
  rw [← Array.forIn_toList] at h
  exact list_forIn_commonSubstep_projection π hb h

theorem range_forIn_commonSubstep_projection {β : Type} (π : β → BeaconState P f)
    {xs : Std.Legacy.Range} {init out : β} {body : Nat → β → Fallible (ForInStep β)}
    (hb : ∀ a b, Ok (body a b) (fun r => CommonSubstep (π b) (π r.value)))
    (h : forIn xs init body = .ok out) : CommonSubstep (π init) (π out) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact list_forIn_commonSubstep_projection π hb h

theorem foldlM_commonSubstep {α : Type} {step : BeaconState P f → α → Fallible (BeaconState P f)}
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

theorem array_foldlM_commonSubstep {α : Type} {step : BeaconState P f → α → Fallible (BeaconState P f)}
    (hstep : ∀ s a s', step s a = .ok s' → CommonSubstep s s')
    {xs : Array α} {s s' : BeaconState P f}
    (h : Array.foldlM step s xs = .ok s') : CommonSubstep s s' := by
  rw [← Array.foldlM_toList] at h
  exact foldlM_commonSubstep hstep xs.toList h

/-! ## Join-point VCG for `CommonSubstep` -/

section Meta
open Lean Meta Elab Tactic

private def okPartsCorpus? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity ``Ok 3 then some (e.getArg! 0, e.getArg! 1, e.getArg! 2) else none

private def commonSubstepParts (α Q : Expr) : MetaM (Expr × Expr) :=
  withLocalDeclD `r α fun r => do
    let qr := (mkApp Q r).headBeta
    unless qr.isAppOfArity ``CommonSubstep 4 do throwError "post-condition is not `CommonSubstep _ _`"
    let A := qr.getArg! 2
    if A.containsFVar r.fvarId! then throwError "post-condition base depends on the result"
    pure (A, ← mkLambdaFVars #[r] (qr.getArg! 3))

private def commonSubstepPostcondition (α σ g : Expr) : MetaM Expr := do
  let post ← withLocalDeclD `r α fun r => do
    mkLambdaFVars #[r] (← mkAppM ``CommonSubstep #[σ, (mkApp g r).headBeta])
  pure post.eta

private def isJoinPointNameCorpus (n : Name) : Bool := n.eraseMacroScopes == `__do_jp

private def findStateCorpus : Nat → Expr → Expr → MetaM (Option Expr)
  | 0, _, _ => pure none
  | fuel + 1, x, T => do
    let T ← whnfR T
    if T.getAppFn.isConstOf ``BeaconState then return some x
    if T.isAppOfArity ``Prod 2 then
      if let some e ← findStateCorpus fuel (← mkAppM ``Prod.fst #[x]) (T.getArg! 0) then return some e
      return ← findStateCorpus fuel (← mkAppM ``Prod.snd #[x]) (T.getArg! 1)
    return none

elab "jp_intro_c" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (α, c, Q) := okPartsCorpus? t | throwError "jp_intro_c: goal is not `Ok _ _`"
  let .letE n ty v b _ := c.headBeta | throwError "jp_intro_c: no `have` at the head"
  unless isJoinPointNameCorpus n do throwError "jp_intro_c: not a join point"
  let (A, gf) ← commonSubstepParts α Q
  let stTy ← inferType A
  let mkH (jp : Expr) : MetaM Expr := forallTelescope ty fun ys _ => do
    let mut σ := A
    for y in ys do
      if let some stExpr ← findStateCorpus 8 y (← inferType y) then
        if ← isDefEq (← inferType stExpr) stTy then σ := stExpr
    let post ← commonSubstepPostcondition α σ gf
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
  let some (α, c, Q) := okPartsCorpus? t | throwError "jp_call_c: goal is not `Ok _ _`"
  let c := c.headBeta
  let fn := c.getAppFn
  unless fn.isFVar do throwError "jp_call_c: not a call of a local"
  let (A, _) ← commonSubstepParts α Q
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isForall do continue
    let r : Option MVarId ← try
        let (mvs, _, body) ← forallMetaTelescope ty
        let some (_, c', post) := okPartsCorpus? body | throwError "not Ok"
        unless c'.getAppFn == fn do throwError "other head"
        unless ← isDefEq c' c do throwError "args differ"
        let post ← instantiateMVars post
        let (σ, _) ← commonSubstepParts α post
        let hp ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``CommonSubstep #[A, σ]) `jp_csub
        let pf ← mkAppM ``ok_trans_commonSubstep #[hp, mkAppN d.toExpr mvs]
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
  let some (α, c, Q) := okPartsCorpus? t | throwError "loop_csub: goal is not `Ok _ _`"
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
  let lem ← if ρ.isAppOf ``List then pure ``list_forIn_commonSubstep_projection
    else if ρ.isAppOf ``Array then pure ``array_forIn_commonSubstep_projection
    else if ρ.isConstOf ``Std.Legacy.Range then pure ``range_forIn_commonSubstep_projection
    else throwError "loop_csub: collection {ρ}"
  unless rhs.isAppOfArity ``Except.ok 3 do throwError "loop_csub: not `.ok`"
  let out := rhs.appArg!
  let β ← inferType init
  let π ← withLocalDeclD `x β fun x => do
    let some e ← findStateCorpus 8 x β | throwError "loop_csub: no state in the accumulator"
    mkLambdaFVars #[x] e
  let (A, gf) ← commonSubstepParts α Q
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
    (mkAppN t.getAppFn #[α, c, ← commonSubstepPostcondition α (π.beta #[out]) gf]) `loop_rest
  let full ← mkAppM ``ok_trans_commonSubstep #[← mkAppM ``CommonSubstep.trans #[hp, pf], rest]
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
  | (apply commonSubstep_set_validators; rfl; rfl; rfl; rfl; rfl; rfl; rfl; assumption)
  | (apply commonSubstep_set_balances; rfl; rfl; rfl; rfl; rfl; rfl; rfl; assumption)
  | (apply commonSubstep_modify_validators; rfl; rfl; rfl; rfl; rfl; rfl; rfl; assumption)
  | (apply commonSubstep_modify_balances; rfl; rfl; rfl; rfl; rfl; rfl; rfl; assumption)
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
     first | (refine ok_trans_commonSubstep (CommonSubstep.trans ?_ (by csub_of hx)) ?_; csub_close) | skip)
  | (with_reducible apply ok_ite <;> intro _)
  | (with_reducible apply ok_dite <;> intro _)
  | (set_option simprocs false in dsimp -zeta only)
  | (rename_i x _; is_small_inductive x; cases x; all_goals (set_option simprocs false in dsimp -zeta only))
  | split)

/-! ## Leaf mutators satisfying `CommonSubstep` -/

theorem increaseBalance_commonSubstep {s s' : BeaconState P f} {idx : ValidatorIndex} {d : Gwei}
    (h : increaseBalance s idx d = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (increaseBalance s idx d) (CommonSubstep s)
  unfold increaseBalance; repeat cstep

theorem decreaseBalance_commonSubstep {s s' : BeaconState P f} {idx : ValidatorIndex} {d : Gwei}
    (h : decreaseBalance s idx d = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (decreaseBalance s idx d) (CommonSubstep s)
  unfold decreaseBalance; repeat cstep

theorem exitChurn_commonSubstep (cfg : Config) {s : BeaconState P f} {b : Gwei} {r : BeaconState P f × Epoch}
    (h : computeExitEpochAndUpdateChurn cfg s b = .ok r) : CommonSubstep s r.1 := by
  revert r h
  show Ok (computeExitEpochAndUpdateChurn cfg s b) (fun r => CommonSubstep s r.1)
  unfold computeExitEpochAndUpdateChurn; repeat cstep

theorem consolidationChurn_commonSubstep (cfg : Config) {s : BeaconState P f} {b : Gwei}
    {r : BeaconState P f × Epoch}
    (h : computeConsolidationEpochAndUpdateChurn cfg s b = .ok r) : CommonSubstep s r.1 := by
  obtain ⟨_, _, hr⟩ := computeConsolidationEpoch_frame h
  rw [hr]
  exact commonSubstep_frame rfl rfl rfl rfl rfl rfl rfl

theorem setPendingPartialWithdrawals_commonSubstep {s s' : BeaconState P f}
    {l : Ssz.List PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    (h : s.setPendingPartialWithdrawals l = .ok s') : CommonSubstep s s' := by
  unfold BeaconState.setPendingPartialWithdrawals at h
  obtain ⟨g, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact commonSubstep_frame rfl rfl rfl rfl rfl rfl rfl

theorem setProposerLookahead_commonSubstep {s s' : BeaconState P f}
    {l : Ssz.Vector ValidatorIndex ((P.MIN_SEED_LOOKAHEAD + 1) * P.SLOTS_PER_EPOCH)}
    (h : s.setProposerLookahead l = .ok s') : CommonSubstep s s' := by
  unfold BeaconState.setProposerLookahead at h
  obtain ⟨g, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact commonSubstep_frame rfl rfl rfl rfl rfl rfl rfl

theorem setDepositBalanceToConsume_commonSubstep {s s' : BeaconState P f} {x : Gwei}
    (h : s.setDepositBalanceToConsume x = .ok s') : CommonSubstep s s' := by
  unfold BeaconState.setDepositBalanceToConsume at h
  obtain ⟨g, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact commonSubstep_frame rfl rfl rfl rfl rfl rfl rfl

/-- `addValidatorToRegistry` pushes one validator and, whenever `BalancesMatchValidators s` holds,
also pushes one balance entry (`idx = s.validators.length = s.balances.length`), preserving
`BalancesMatchValidators` and all non-registry fields. -/
theorem addValidatorToRegistry_commonSubstep {s s' : BeaconState P f} {pk : BLSPubkey} {wc : Bytes32}
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
    simp only [Ssz.List.length, hn, beq_self_eq_true]
  have hcb : (idx.toNat == s.balances.length) = true := by
    simp only [Ssz.List.length, hbm, hn, beq_self_eq_true]
  rw [ite_eq_left hcv] at hV
  rw [ite_eq_left hcb] at hB
  show B.toArray.size = V.toArray.size
  rw [push_ok hV, push_ok hB, Array.size_push, Array.size_push, hbm]

macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact increaseBalance_commonSubstep $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact decreaseBalance_commonSubstep $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact exitChurn_commonSubstep _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact consolidationChurn_commonSubstep _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact setPendingPartialWithdrawals_commonSubstep $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact setProposerLookahead_commonSubstep $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact setDepositBalanceToConsume_commonSubstep $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact addValidatorToRegistry_commonSubstep $h)

theorem initiate_commonSubstep_tail (cfg : Config) {s T s' : BeaconState P f} {i : ValidatorIndex}
    {v : Validator} {q : Epoch} (hT : CommonSubstep s T)
    (h : (do let d ← u64Checked cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY
             let w ← U64.add? q d "initiate_validator_exit"
             let V ← T.validators.set i.toNat { v with exit_epoch := q, withdrawable_epoch := w }
               "initiate_validator_exit"
             pure { T with validators := V } : Fallible (BeaconState P f)) = .ok s') :
    CommonSubstep s s' := by
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨V, hV, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact hT.trans (commonSubstep_set_validators rfl rfl rfl rfl rfl rfl rfl hV)

theorem initiateValidatorExit_commonSubstep (cfg : Config) {s s' : BeaconState P f} {idx : ValidatorIndex}
    (h : initiateValidatorExit cfg s idx = .ok s') : CommonSubstep s s' := by
  unfold initiateValidatorExit at h
  obtain ⟨v, _, h⟩ := bind_eq_ok_iff.mp h
  dsimp only at h
  split at h
  · cases h; exact CommonSubstep.refl s
  · split at h
    · obtain ⟨⟨st1, q⟩, hq, h⟩ := bind_eq_ok_iff.mp h
      exact initiate_commonSubstep_tail cfg (v := v) (exitChurn_commonSubstep cfg hq) h
    · obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨⟨st1, q'⟩, hq', h⟩ := bind_eq_ok_iff.mp h
        cases hq'
        exact initiate_commonSubstep_tail cfg (v := v) (CommonSubstep.refl s) h
      · obtain ⟨⟨st1, q'⟩, hq', h⟩ := bind_eq_ok_iff.mp h
        cases hq'
        exact initiate_commonSubstep_tail cfg (v := v) (CommonSubstep.refl s) h

macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact initiateValidatorExit_commonSubstep _ $h)

theorem slashValidator_commonSubstep (cfg : Config) {s s' : BeaconState P f} {slashed : ValidatorIndex}
    {wb : Option ValidatorIndex} (h : slashValidator cfg s slashed wb = .ok s') :
    CommonSubstep s s' := by
  revert s' h; show Ok (slashValidator cfg s slashed wb) (CommonSubstep s)
  unfold slashValidator; repeat cstep

macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact slashValidator_commonSubstep _ $h)

theorem applyPendingDeposit_commonSubstep (ctx : Context) {d : PendingDeposit} {s s' : BeaconState P f}
    (h : applyPendingDeposit ctx s d = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (applyPendingDeposit ctx s d) (CommonSubstep s)
  unfold applyPendingDeposit; repeat cstep

macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact applyPendingDeposit_commonSubstep _ $h)

/-! ## Block operations satisfying `CommonSubstep` -/

theorem processBlsToExecutionChange_commonSubstep (ctx : Context) {s s' : BeaconState P f}
    {sac : SignedBLSToExecutionChange}
    (h : processBlsToExecutionChange ctx s sac = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processBlsToExecutionChange ctx s sac) (CommonSubstep s)
  unfold processBlsToExecutionChange; repeat cstep

theorem processVoluntaryExit_commonSubstep (ctx : Context) {s s' : BeaconState P f} {sve : SignedVoluntaryExit}
    (h : processVoluntaryExit ctx s sve = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processVoluntaryExit ctx s sve) (CommonSubstep s)
  unfold processVoluntaryExit; repeat cstep

theorem processProposerSlashing_commonSubstep (ctx : Context) {s s' : BeaconState P f} {ps : ProposerSlashing}
    (h : processProposerSlashing ctx s ps = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processProposerSlashing ctx s ps) (CommonSubstep s)
  unfold processProposerSlashing; repeat cstep

theorem processAttesterSlashing_commonSubstep (ctx : Context) {s s' : BeaconState P f}
    {as : AttesterSlashing P f}
    (h : processAttesterSlashing ctx s as = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processAttesterSlashing ctx s as) (CommonSubstep s)
  unfold processAttesterSlashing; repeat cstep

theorem processAttestation_commonSubstep (ctx : Context) {a : Attestation P f} {s s' : BeaconState P f}
    (h : processAttestation ctx s a = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processAttestation ctx s a) (CommonSubstep s)
  unfold processAttestation; repeat cstep

theorem processWithdrawalRequest_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    {wr : WithdrawalRequest}
    (h : processWithdrawalRequest cfg s wr = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processWithdrawalRequest cfg s wr) (CommonSubstep s)
  unfold processWithdrawalRequest; repeat cstep

theorem foldWithdrawalRequests_commonSubstep (cfg : Config) {wrs : List WithdrawalRequest}
    {s s' : BeaconState P f}
    (h : foldWithdrawalRequests cfg s wrs = .ok s') : CommonSubstep s s' :=
  foldlM_commonSubstep (fun _ _ _ hw => processWithdrawalRequest_commonSubstep cfg hw) wrs h

theorem processWithdrawals_commonSubstep {s s' : BeaconState P f} {pl : ExecutionPayload P}
    (h : processWithdrawals s pl = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processWithdrawals s pl) (CommonSubstep s)
  unfold processWithdrawals; repeat cstep

theorem processRandao_commonSubstep (ctx : Context) {body : BeaconBlockBody P f} {s s' : BeaconState P f}
    (h : processRandao ctx s body = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processRandao ctx s body) (CommonSubstep s)
  unfold processRandao; repeat cstep

theorem processEth1Data_commonSubstep {body : BeaconBlockBody P f} {s s' : BeaconState P f}
    (h : processEth1Data s body = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processEth1Data s body) (CommonSubstep s)
  unfold processEth1Data; repeat cstep

theorem processSyncAggregate_commonSubstep (ctx : Context) {sa : SyncAggregate P} {s s' : BeaconState P f}
    (h : processSyncAggregate ctx s sa = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processSyncAggregate ctx s sa) (CommonSubstep s)
  unfold processSyncAggregate; repeat cstep

macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processBlsToExecutionChange_commonSubstep _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processVoluntaryExit_commonSubstep _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processProposerSlashing_commonSubstep _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processAttesterSlashing_commonSubstep _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processAttestation_commonSubstep _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processWithdrawalRequest_commonSubstep _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processWithdrawals_commonSubstep $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processRandao_commonSubstep _ $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processEth1Data_commonSubstep $h)
macro_rules | `(tactic| csub_of $h) => `(tactic| with_reducible exact processSyncAggregate_commonSubstep _ $h)

/-! ## Epoch sub-steps satisfying `CommonSubstep` -/

theorem weighJustificationAndFinalization_commonSubstep {s s' : BeaconState P f} {t p c : Gwei}
    (h : weighJustificationAndFinalization s t p c = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (weighJustificationAndFinalization s t p c) (CommonSubstep s)
  unfold weighJustificationAndFinalization; repeat cstep

macro_rules | `(tactic| csub_of $h) => `(tactic|
    with_reducible exact weighJustificationAndFinalization_commonSubstep $h)

theorem processJustificationAndFinalization_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    (h : processJustificationAndFinalization cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processJustificationAndFinalization cfg s) (CommonSubstep s)
  unfold processJustificationAndFinalization; repeat cstep

theorem processInactivityUpdates_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    (h : processInactivityUpdates cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processInactivityUpdates cfg s) (CommonSubstep s)
  unfold processInactivityUpdates; repeat cstep

theorem processRewardsAndPenalties_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    (h : processRewardsAndPenalties cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processRewardsAndPenalties cfg s) (CommonSubstep s)
  unfold processRewardsAndPenalties; repeat cstep

theorem processRegistryUpdatesElectra_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    (h : processRegistryUpdatesElectra cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processRegistryUpdatesElectra cfg s) (CommonSubstep s)
  unfold processRegistryUpdatesElectra; repeat cstep

theorem processRegistryUpdates_commonSubstep (cfg : Config) (hf : f.atLeast .electra = true)
    {s s' : BeaconState P f} (h : processRegistryUpdates cfg s = .ok s') : CommonSubstep s s' := by
  unfold processRegistryUpdates at h
  rw [ite_eq_left hf] at h
  exact processRegistryUpdatesElectra_commonSubstep cfg h

theorem processSlashings_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    (h : processSlashings cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processSlashings cfg s) (CommonSubstep s)
  unfold processSlashings; repeat cstep

theorem processEth1DataReset_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    (h : processEth1DataReset cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processEth1DataReset cfg s) (CommonSubstep s)
  unfold processEth1DataReset; repeat cstep

theorem processEffectiveBalanceUpdates_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    (h : processEffectiveBalanceUpdates cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h
  show Ok (processEffectiveBalanceUpdates cfg s) (CommonSubstep s)
  unfold processEffectiveBalanceUpdates
  repeat (first | ok_head | (with_reducible apply ok_bind; intro _ _))
  refine ok_pure (commonSubstep_of_sizes ?_ rfl rfl rfl rfl rfl rfl)
  refine list_forIn_relation
    (fun V V' : Ssz.List Validator P.VALIDATOR_REGISTRY_LIMIT => V'.toArray.size = V.toArray.size)
    (fun _ => rfl) (fun _ _ _ h1 h2 => h2.trans h1) _ ?_ _ _ _ (by assumption)
  intro i V r hb
  simp only [bind, Except.bind, pure, Except.pure] at hb
  repeat' split at hb
  all_goals first
    | (cases hb; rfl)
    | (cases hb; dsimp only [ForInStep.value]; obtain ⟨_, hVe⟩ := set_ok (by assumption); rw [hVe, Array.size_set])
    | cases hb

theorem processSlashingsReset_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    (h : processSlashingsReset cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processSlashingsReset cfg s) (CommonSubstep s)
  unfold processSlashingsReset; repeat cstep

theorem processRandaoMixesReset_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    (h : processRandaoMixesReset cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processRandaoMixesReset cfg s) (CommonSubstep s)
  unfold processRandaoMixesReset; repeat cstep

theorem processHistoricalSummariesUpdate_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    (h : processHistoricalSummariesUpdate cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processHistoricalSummariesUpdate cfg s) (CommonSubstep s)
  unfold processHistoricalSummariesUpdate; repeat cstep

theorem processParticipationFlagUpdates_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    (h : processParticipationFlagUpdates cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processParticipationFlagUpdates cfg s) (CommonSubstep s)
  unfold processParticipationFlagUpdates; repeat cstep

theorem processSyncCommitteeUpdates_commonSubstep (ctx : Context) {s s' : BeaconState P f}
    (h : processSyncCommitteeUpdates ctx s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processSyncCommitteeUpdates ctx s) (CommonSubstep s)
  unfold processSyncCommitteeUpdates; repeat cstep

theorem processProposerLookahead_commonSubstep (cfg : Config) {s s' : BeaconState P f}
    (h : processProposerLookahead cfg s = .ok s') : CommonSubstep s s' := by
  revert s' h; show Ok (processProposerLookahead cfg s) (CommonSubstep s)
  unfold processProposerLookahead; repeat cstep

/-! ## Queue, header, slot, epoch, block, and upgrade preservation -/

/-- `applyDeposit` at Electra+ preserves `BalancesMatchValidators`, `slot`, `latest_block_header`,
`latest_execution_payload_header`, and `pending_consolidations`, and appends at most one
`GENESIS_SLOT` entry to `pending_deposits`. -/
theorem applyDeposit_corpusPreservation_and_frame (hf : f.atLeast .electra = true) (ctx : Context)
    {s s' : BeaconState P f} {pk : BLSPubkey} {wc : Bytes32} {amt : U64} {sig : BLSSignature}
    (h : applyDeposit ctx s pk wc amt sig = .ok s') :
    CorpusPreservation s s' ∧
    s'.slot = s.slot ∧
    s'.latest_block_header = s.latest_block_header ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
    s'.pending_consolidations = s.pending_consolidations ∧
    ∃ extra, (ForkField.get hf s'.pending_deposits).toArray.toList =
      (ForkField.get hf s.pending_deposits).toArray.toList ++ extra ∧
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
      exact ⟨CorpusPreservation.refl _, rfl, rfl, rfl, rfl, [], by simp, by intro _ hm; cases hm⟩
    | true =>
      simp only [ite_true] at h
      obtain ⟨s1, hadd, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨q', hq', h⟩ := bind_eq_ok_iff.mp h
      unfold BeaconState.setPendingDeposits at h
      obtain ⟨g, hg, h⟩ := bind_eq_ok_iff.mp h
      cases h
      have hc1 := addValidatorToRegistry_commonSubstep hadd
      have hq0 : q = ForkField.get hf s.pending_deposits := by
        unfold BeaconState.pendingDeposits at hq
        rw [hc1.pendingDeposits_eq, forkField_read_get hf] at hq
        exact (Except.ok.inj hq).symm
      have hg1 : g = ForkField.mk hf q' := by
        rw [forkField_write_eq hf] at hg
        exact (Except.ok.inj hg).symm
      refine ⟨⟨hc1.balancesMatchValidators, hc1.pendingConsolidationsDistinct⟩, hc1.slot_eq, hc1.latestBlockHeader_eq, hc1.latestExecutionPayloadHeader_eq, hc1.pendingConsolidations_eq,
        [{ pubkey := pk, withdrawal_credentials := wc, amount := amt,
           signature := sig, slot := GENESIS_SLOT }], ?_, ?_⟩
      · show (ForkField.get hf g).toArray.toList = _
        rw [hg1, ForkField.get_mk, push_ok hq', hq0, Array.toList_push]
      · intro d hd; simp only [List.mem_singleton] at hd; subst hd; rfl
  · rw [ite_eq_right hany] at h
    obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨q', hq', h⟩ := bind_eq_ok_iff.mp h
    unfold BeaconState.setPendingDeposits at h
    obtain ⟨g, hg, h⟩ := bind_eq_ok_iff.mp h
    cases h
    have hq0 : q = ForkField.get hf s.pending_deposits := by
      unfold BeaconState.pendingDeposits at hq
      rw [forkField_read_get hf] at hq
      exact (Except.ok.inj hq).symm
    have hg1 : g = ForkField.mk hf q' := by
      rw [forkField_write_eq hf] at hg
      exact (Except.ok.inj hg).symm
    refine ⟨⟨id, id⟩, rfl, rfl, rfl, rfl,
      [{ pubkey := pk, withdrawal_credentials := wc, amount := amt,
         signature := sig, slot := GENESIS_SLOT }], ?_, ?_⟩
    · show (ForkField.get hf g).toArray.toList = _
      rw [hg1, ForkField.get_mk, push_ok hq', hq0, Array.toList_push]
    · intro d hd; simp only [List.mem_singleton] at hd; subst hd; rfl

theorem processDeposit_corpusPreservation_and_frame (hf : f.atLeast .electra = true) (ctx : Context)
    {s s' : BeaconState P f} {d : Deposit}
    (h : processDeposit ctx s d = .ok s') :
    CorpusPreservation s s' ∧
    s'.slot = s.slot ∧
    s'.latest_block_header = s.latest_block_header ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
    s'.pending_consolidations = s.pending_consolidations ∧
    ∃ extra, (ForkField.get hf s'.pending_deposits).toArray.toList =
      (ForkField.get hf s.pending_deposits).toArray.toList ++ extra ∧
      ∀ x ∈ extra, x.slot = GENESIS_SLOT := by
  unfold processDeposit at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hc, hsl, hlbh, hlep, hpc, ex, hpd, hg⟩ := applyDeposit_corpusPreservation_and_frame hf ctx h
  exact ⟨⟨hc.balancesMatchValidators, hc.pendingConsolidationsDistinct⟩, hsl, hlbh, hlep, hpc, ex, hpd, hg⟩

theorem foldDeposits_corpusPreservation_and_frame (hf : f.atLeast .electra = true) (ctx : Context) :
    ∀ (ds : List Deposit) {s s' : BeaconState P f},
      List.foldlM (processDeposit ctx) s ds = .ok s' →
      CorpusPreservation s s' ∧
      s'.slot = s.slot ∧
      s'.latest_block_header = s.latest_block_header ∧
      s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
      s'.pending_consolidations = s.pending_consolidations ∧
      ∃ extra, (ForkField.get hf s'.pending_deposits).toArray.toList =
        (ForkField.get hf s.pending_deposits).toArray.toList ++ extra ∧
        ∀ x ∈ extra, x.slot = GENESIS_SLOT := by
  intro ds
  induction ds with
  | nil =>
    intro s s' h; cases h
    exact ⟨CorpusPreservation.refl _, rfl, rfl, rfl, rfl, [], by simp, by intro _ hm; cases hm⟩
  | cons d ds ih =>
    intro s s' h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, h1, h2⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hc1, hsl1, hlbh1, hlep1, hpc1, ex1, hpd1, hg1⟩ := processDeposit_corpusPreservation_and_frame hf ctx h1
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
theorem preDeposits_corpusPreservation_and_frame (hf : f.atLeast .electra = true) (ctx : Context)
    {s s' : BeaconState P f} {body : BeaconBlockBody P f}
    (h : preDeposits ctx s body = .ok s') :
    CorpusPreservation s s' ∧
    s'.slot = s.slot ∧
    s'.latest_block_header = s.latest_block_header ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
    s'.pending_consolidations = s.pending_consolidations ∧
    (f.atLeast .fulu = true → s'.pending_deposits = s.pending_deposits) ∧
    ∃ extra, (ForkField.get hf s'.pending_deposits).toArray.toList =
      (ForkField.get hf s.pending_deposits).toArray.toList ++ extra ∧
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
      CorpusPreservation s0 s' ∧
      s'.slot = s0.slot ∧
      s'.latest_block_header = s0.latest_block_header ∧
      s'.latest_execution_payload_header = s0.latest_execution_payload_header ∧
      s'.pending_consolidations = s0.pending_consolidations ∧
      (f.atLeast .fulu = true → s'.pending_deposits = s0.pending_deposits) ∧
      ∃ extra, (ForkField.get hf s'.pending_deposits).toArray.toList =
        (ForkField.get hf s0.pending_deposits).toArray.toList ++ extra ∧
        ∀ x ∈ extra, x.slot = GENESIS_SLOT := by
    intro s0 hreq0 hb
    simp only [forArray_yield] at hb
    obtain ⟨s1, h1, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨s2, h2, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨s3, h3, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨s4, h4, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨s5, h5, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨s6, h6, hpure⟩ := bind_eq_ok_iff.mp hb
    cases hpure
    have c1 := (foldlM_commonSubstep (fun _ _ _ hh => processProposerSlashing_commonSubstep ctx hh) _ h1).trans <|
      (foldlM_commonSubstep (fun _ _ _ hh => processAttesterSlashing_commonSubstep ctx hh) _ h2).trans <|
      foldlM_commonSubstep (fun _ _ _ hh => processAttestation_commonSubstep ctx hh) _ h3
    obtain ⟨cd, hsld, hlbhd, hlepd, hpcd, ex, hpdd, hgd⟩ := foldDeposits_corpusPreservation_and_frame hf ctx _ h4
    have c2 := (foldlM_commonSubstep (fun _ _ _ hh => processVoluntaryExit_commonSubstep ctx hh) _ h5).trans <|
      foldlM_commonSubstep (fun _ _ _ hh => processBlsToExecutionChange_commonSubstep ctx hh) _ h6
    refine ⟨c1.corpusPreservation.trans (cd.trans c2.corpusPreservation),
      c2.slot_eq.trans (hsld.trans c1.slot_eq),
      c2.latestBlockHeader_eq.trans (hlbhd.trans c1.latestBlockHeader_eq),
      c2.latestExecutionPayloadHeader_eq.trans (hlepd.trans c1.latestExecutionPayloadHeader_eq),
      c2.pendingConsolidations_eq.trans (hpcd.trans c1.pendingConsolidations_eq), ?_, ex, ?_, hgd⟩
    · intro hfu
      rw [hreq0 hfu] at h4
      cases h4
      exact c2.pendingDeposits_eq.trans c1.pendingDeposits_eq
    · rw [c2.pendingDeposits_eq, hpdd, c1.pendingDeposits_eq]
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

theorem foldDepositRequests_corpusPreservation (hf : f.atLeast .electra = true)
    {drs : List DepositRequest} {s s' : BeaconState P f}
    (h : foldDepositRequests s drs = .ok s') : CorpusPreservation s s' := by
  obtain ⟨_, _, hfr⟩ := foldDepositRequests_spec hf drs h
  refine ⟨fun hbm => ?_, fun hpcd => ?_⟩
  · unfold BalancesMatchValidators at hbm ⊢
    rw [hfr]; exact hbm
  · unfold PendingConsolidationsDistinct at hpcd ⊢
    rw [pendingConsolidationsList_congr (by rw [hfr])]; exact hpcd

theorem foldConsolidationRequests_corpusPreservation (hf : f.atLeast .electra = true) (cfg : Config)
    {crs : List ConsolidationRequest} {s s' : BeaconState P f}
    (h : foldConsolidationRequests cfg s crs = .ok s') : CorpusPreservation s s' := by
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

theorem processOperations_corpusPreservation (hf : f.atLeast .electra = true) (ctx : Context)
    {body : BeaconBlockBody P f} {s s' : BeaconState P f}
    (h : processOperations ctx s body = .ok s') : CorpusPreservation s s' := by
  rw [processOperations_split_all ctx s body hf] at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h4⟩ := bind_eq_ok_iff.mp h
  exact (preDeposits_corpusPreservation_and_frame hf ctx h1).1.trans <|
    (foldDepositRequests_corpusPreservation hf h2).trans <|
    (foldWithdrawalRequests_commonSubstep ctx.config h3).corpusPreservation.trans <|
    foldConsolidationRequests_corpusPreservation hf ctx.config h4

theorem processBlockHeader_corpusPreservation {blk : BeaconBlock P f} {s s' : BeaconState P f}
    (h : processBlockHeader s blk = .ok s') :
    CorpusPreservation s s' ∧
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

theorem processExecutionPayload_corpusPreservation (ctx : Context) {body : BeaconBlockBody P f}
    {s s' : BeaconState P f} (h : processExecutionPayload ctx s body = .ok s') :
    CorpusPreservation s s' ∧
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

theorem processBlock_corpusPreservation (hf : f.atLeast .electra = true) (ctx : Context)
    {blk : BeaconBlock P f} {s s' : BeaconState P f}
    (h : processBlock ctx s blk = .ok s') : CorpusPreservation s s' := by
  unfold processBlock processBlockWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s6, h6, h7⟩ := bind_eq_ok_iff.mp h
  exact (processBlockHeader_corpusPreservation h1).1.trans <|
    (processWithdrawals_commonSubstep h2).corpusPreservation.trans <|
    (processExecutionPayload_corpusPreservation ctx h3).1.trans <|
    (processRandao_commonSubstep ctx h4).corpusPreservation.trans <|
    (processEth1Data_commonSubstep h5).corpusPreservation.trans <|
    (processOperations_corpusPreservation hf ctx h6).trans <|
    (processSyncAggregate_commonSubstep ctx h7).corpusPreservation

/-- `processPendingDeposits` preserves `CorpusPres`, `slot`, `latest_block_header`,
`latest_execution_payload_header`, and `pending_consolidations`. -/
theorem processPendingDeposits_corpusPreservation_and_frame (ctx : Context)
    {s s' : BeaconState P f} (h : processPendingDeposits ctx s = .ok s') :
    CorpusPreservation s s' ∧
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
  have hc_mid := foldlM_commonSubstep (fun _ _ _ ha => applyPendingDeposit_commonSubstep ctx ha) applied hfold
  obtain ⟨q, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨st1, hst1, h⟩ := bind_eq_ok_iff.mp h
  unfold BeaconState.setPendingDeposits at hst1
  obtain ⟨g, _, hst1⟩ := bind_eq_ok_iff.mp hst1
  cases hst1
  have hc_tail : CommonSubstep { out.2.2.2.2 with pending_deposits := g } s' := by
    split at h
    · obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      exact setDepositBalanceToConsume_commonSubstep h
    · exact setDepositBalanceToConsume_commonSubstep h
  have hc_set : CorpusPreservation out.2.2.2.2 { out.2.2.2.2 with pending_deposits := g } :=
    ⟨id, by unfold PendingConsolidationsDistinct; exact id⟩
  exact ⟨hc_mid.corpusPreservation.trans (hc_set.trans hc_tail.corpusPreservation),
    hc_tail.slot_eq.trans hc_mid.slot_eq,
    hc_tail.latestBlockHeader_eq.trans hc_mid.latestBlockHeader_eq,
    hc_tail.latestExecutionPayloadHeader_eq.trans hc_mid.latestExecutionPayloadHeader_eq,
    hc_tail.pendingConsolidations_eq.trans hc_mid.pendingConsolidations_eq⟩

/-- `processPendingConsolidations` preserves `CorpusPres`, `slot`, `latest_block_header`,
`latest_execution_payload_header`, and `pending_deposits`. -/
theorem processPendingConsolidations_corpusPreservation_and_frame (hf : f.atLeast .electra = true) (cfg : Config)
    {s s' : BeaconState P f} (h : processPendingConsolidations cfg s = .ok s') :
    CorpusPreservation s s' ∧
    s'.slot = s.slot ∧
    s'.latest_block_header = s.latest_block_header ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header ∧
    s'.pending_deposits = s.pending_deposits := by
  rw [processPendingConsolidations_eq] at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨nextEpoch, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pending, hpend, h⟩ := bind_eq_ok_iff.mp h
  have hpq : pending = ForkField.get hf s.pending_consolidations := by
    unfold BeaconState.pendingConsolidations at hpend
    rw [forkField_read_get hf] at hpend
    exact (Except.ok.inj hpend).symm
  subst hpq
  obtain ⟨out, hloop, h⟩ := bind_eq_ok_iff.mp h
  rw [pendingConsolidationsLoop_eq_forIn] at hloop
  have hc_loop : CommonSubstep s out.1 := by
    refine list_forIn_commonSubstep_projection Prod.fst (fun pc acc r hr => ?_) hloop
    obtain ⟨src, _, hsp⟩ := pendingConsolidationStep_spec hr
    rcases hsp with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, bal, mid, st', _, hdec, hinc, rfl⟩
    · exact CommonSubstep.refl _
    · exact CommonSubstep.refl _
    · exact (decreaseBalance_commonSubstep hdec).trans (increaseBalance_commonSubstep hinc)
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  unfold BeaconState.setPendingConsolidations at h
  obtain ⟨g, hg, h⟩ := bind_eq_ok_iff.mp h
  cases h
  have hgq : g = ForkField.mk hf q := by
    rw [forkField_write_eq hf] at hg; exact (Except.ok.inj hg).symm
  have hq_arr : q.toArray =
      (ForkField.get hf s.pending_consolidations).toArray.extract out.2
        (ForkField.get hf s.pending_consolidations).length := by
    unfold Ssz.List.ofArray at hq
    split at hq
    · cases hq; rfl
    · cases hq
  refine ⟨⟨hc_loop.balancesMatchValidators, ?_⟩, hc_loop.slot_eq, hc_loop.latestBlockHeader_eq, hc_loop.latestExecutionPayloadHeader_eq, hc_loop.pendingDeposits_eq⟩
  intro hpcd
  unfold PendingConsolidationsDistinct at hpcd ⊢
  rw [pendingConsolidationsList_eq_get hf] at hpcd ⊢
  show ∀ pc ∈ (ForkField.get hf g).toArray.toList, pc.source_index ≠ pc.target_index
  rw [hgq, ForkField.get_mk, hq_arr, Array.toList_extract]
  intro pc hmem
  exact hpcd pc (List.mem_of_mem_drop (List.mem_of_mem_take hmem))

theorem processEpoch_corpusPreservation_and_frame (hf : f.atLeast .electra = true) (ctx : Context)
    {s s' : BeaconState P f} (h : processEpoch ctx s = .ok s') :
    CorpusPreservation s s' ∧
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
    (processJustificationAndFinalization_commonSubstep _ h1).trans <|
    (processInactivityUpdates_commonSubstep _ h2).trans <|
    (processRewardsAndPenalties_commonSubstep _ h3).trans <|
    (processRegistryUpdates_commonSubstep _ hf h4).trans <|
    (processSlashings_commonSubstep _ h5).trans <|
    processEth1DataReset_commonSubstep _ h6
  have c_dep := processPendingDeposits_corpusPreservation_and_frame ctx h7a
  have c_con := processPendingConsolidations_corpusPreservation_and_frame hf ctx.config h7
  have c_post13 : CommonSubstep s7 s13 :=
    (processEffectiveBalanceUpdates_commonSubstep _ h8).trans <|
    (processSlashingsReset_commonSubstep _ h9).trans <|
    (processRandaoMixesReset_commonSubstep _ h10).trans <|
    (processHistoricalSummariesUpdate_commonSubstep _ h11).trans <|
    (processParticipationFlagUpdates_commonSubstep _ h12).trans <|
    processSyncCommitteeUpdates_commonSubstep _ h13
  have c_end : CommonSubstep s13 s' := by
    split at h
    · exact processProposerLookahead_commonSubstep _ h
    · cases h; exact CommonSubstep.refl _
  have c_post := c_post13.trans c_end
  exact ⟨c_pre.corpusPreservation.trans (c_dep.1.trans (c_con.1.trans c_post.corpusPreservation)),
    c_post.slot_eq.trans (c_con.2.1.trans (c_dep.2.1.trans c_pre.slot_eq)),
    c_post.latestBlockHeader_eq.trans (c_con.2.2.1.trans (c_dep.2.2.1.trans c_pre.latestBlockHeader_eq)),
    c_post.latestExecutionPayloadHeader_eq.trans (c_con.2.2.2.1.trans (c_dep.2.2.2.1.trans c_pre.latestExecutionPayloadHeader_eq))⟩

theorem processSlot_corpusPreservation_and_frame {s s' : BeaconState P f} (h : processSlot s = .ok s') :
    CorpusPreservation s s' ∧
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

theorem processSlots_corpusPreservation (hf : f.atLeast .electra = true) (ctx : Context)
    {s s' : BeaconState P f} {slot : Slot}
    (h : processSlots ctx s slot = .ok s') :
    CorpusPreservation s s' ∧
    s'.latest_execution_payload_header = s.latest_execution_payload_header := by
  unfold processSlots processSlotsWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨slotsPerEpoch, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s_out, h, hpure⟩ := bind_eq_ok_iff.mp h
  cases hpure
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact list_forIn_relation
    (fun a b => CorpusPreservation a b ∧ b.latest_execution_payload_header = a.latest_execution_payload_header)
    (fun _ => ⟨CorpusPreservation.refl _, rfl⟩)
    (fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩) _
    (fun _ st r hr => by
      obtain ⟨st1, hslot, hr⟩ := bind_eq_ok_iff.mp hr
      have hc1 := processSlot_corpusPreservation_and_frame hslot
      obtain ⟨next, _, hr⟩ := bind_eq_ok_iff.mp hr
      obtain ⟨rem, _, hr⟩ := bind_eq_ok_iff.mp hr
      simp only [] at hr
      split at hr
      · obtain ⟨st2, hep, hr⟩ := bind_eq_ok_iff.mp hr
        cases hr
        have hc2 := processEpoch_corpusPreservation_and_frame hf ctx hep
        exact ⟨hc1.1.trans ⟨hc2.1.balancesMatchValidators, hc2.1.pendingConsolidationsDistinct⟩, hc2.2.2.2.trans hc1.2.2.2.2.1⟩
      · cases hr
        exact ⟨⟨hc1.1.balancesMatchValidators, hc1.1.pendingConsolidationsDistinct⟩, hc1.2.2.2.2.1⟩)
    _ _ _ h

/-- `upgradeToFulu` copies `validators`, `balances`, `pending_consolidations`, `pending_deposits`,
`slot`, `latest_block_header`, and `latest_execution_payload_header` verbatim, preserving
`CorpusPres`. -/
theorem upgradeToFulu_corpusPreservation_and_frame (cfg : Config)
    {pre : BeaconState P .electra} {post : BeaconState P .fulu}
    (h : upgradeToFulu cfg pre = .ok post) :
    CorpusPreservation pre post ∧
    post.validators = pre.validators ∧
    post.balances = pre.balances ∧
    post.slot = pre.slot ∧
    post.latest_block_header = pre.latest_block_header ∧
    post.latest_execution_payload_header = pre.latest_execution_payload_header ∧
    pendingConsolidationsList post = pendingConsolidationsList pre ∧
    ForkField.get rfl post.pending_consolidations =
      ForkField.get rfl pre.pending_consolidations ∧
    ForkField.get rfl post.pending_deposits =
      ForkField.get rfl pre.pending_deposits := by
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
  have hpc_eq : pc = ForkField.get rfl pre.pending_consolidations := (Except.ok.inj hpc).symm
  have hpd_eq : pd = ForkField.get rfl pre.pending_deposits := (Except.ok.inj hpd).symm
  refine ⟨⟨fun hbm => hbm, fun hpcd => ?_⟩, rfl, rfl, rfl, rfl, rfl, ?_, hpc_eq, hpd_eq⟩
  · unfold PendingConsolidationsDistinct at hpcd ⊢
    rw [pendingConsolidationsList_eq_get (f := .fulu) rfl]
    rw [pendingConsolidationsList_eq_get (f := .electra) rfl] at hpcd
    exact hpc_eq.symm ▸ hpcd
  · rw [pendingConsolidationsList_eq_get (f := .fulu) rfl,
        pendingConsolidationsList_eq_get (f := .electra) rfl]
    exact congrArg (fun x => x.toArray.toList) hpc_eq

theorem stateTransition_corpusPreservation (hf : f.atLeast .electra = true) (ctx : Context)
    {s s' : BeaconState P f} {sb : SignedBeaconBlock P f} {vr : Bool}
    (h : stateTransition ctx s sb vr = .ok s') : CorpusPreservation s s' := by
  unfold stateTransition stateTransitionWith at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  have c1 := (processSlots_corpusPreservation hf ctx h1).1
  cases vr with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
    cases h
    exact c1.trans (processBlock_corpusPreservation hf ctx h2)
  | true =>
    simp only [ite_true] at h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨s2, h2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    cases h
    exact c1.trans (processBlock_corpusPreservation hf ctx h2)

/-! ## `jointTransitionAt` (both `atSlot = false` and `atSlot = true`), `jointStep`, `JointReach` -/

open Jaune in
/-- `jointTransitionAt` preserves `AnchorInv`, `BalancesMatchValidators`, and
`PendingConsolidationsDistinct` at Electra and Fulu — including when `atSlot = true` (Electra
ingress at the fork slot without `processSlots`). -/
theorem jointTransitionAt_corpusPreservation {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (hf : f.atLeast .electra = true)
    {beacon beacon' : BeaconState P f} {exec exec' : BlockChain}
    {sb : SignedBeaconBlock P f} {atSlot : Bool}
    (h : jointTransitionAt cfg ccfg bls beacon exec sb atSlot = .ok (beacon', exec')) :
    Preservation beacon beacon' ∧ CorpusPreservation beacon beacon' := by
  obtain ⟨req, _, _, hb⟩ := jointTransitionAt_ok_iff.mp h
  by_cases hat : atSlot = true
  · rw [ite_eq_left hat] at hb
    obtain ⟨_, _, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨_, _, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨s, hproc, hb⟩ := bind_eq_ok_iff.mp hb
    obtain ⟨_, _, hb⟩ := bind_eq_ok_iff.mp hb
    cases hb
    exact ⟨processBlock_preservation _ hproc, processBlock_corpusPreservation hf _ hproc⟩
  · rw [ite_eq_right hat] at hb
    exact ⟨stateTransition_preservation _ hf hb, stateTransition_corpusPreservation hf _ hb⟩

open Jaune in
theorem jointTransitionAt_corpusAnchorInvariant {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (hf : f.atLeast .electra = true)
    {beacon beacon' : BeaconState P f} {exec exec' : BlockChain}
    {sb : SignedBeaconBlock P f} {atSlot : Bool}
    (h : jointTransitionAt cfg ccfg bls beacon exec sb atSlot = .ok (beacon', exec'))
    (hI : CorpusAnchorInvariant beacon) : CorpusAnchorInvariant beacon' := by
  obtain ⟨hp, hcp⟩ := jointTransitionAt_corpusPreservation hf h
  exact ⟨hp.anchor hI.1, hcp.balancesMatchValidators hI.2.1, hcp.pendingConsolidationsDistinct hI.2.2⟩

open Jaune in
theorem jointStep_electra_corpusPreservation {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .electra}
    {s' : JointState P}
    (h : jointStep cfg ccfg bls ⟨.electra, beacon, exec⟩ ⟨.electra, sb⟩ = .ok s') :
    CorpusPreservation beacon s'.beacon := by
  obtain ⟨_, req, b', e', _, _, hst, rfl⟩ := jointStep_electra_ok_iff.mp h
  exact stateTransition_corpusPreservation (by decide) _ hst

open Jaune in
theorem jointStep_fulu_corpusPreservation {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .fulu} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
    {s' : JointState P}
    (h : jointStep cfg ccfg bls ⟨.fulu, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok s') :
    CorpusPreservation beacon s'.beacon := by
  obtain ⟨req, b', e', _, _, hst, rfl⟩ := jointStep_fulu_ok_iff.mp h
  exact stateTransition_corpusPreservation (by decide) _ hst

open Jaune in
theorem jointStep_cross_corpusPreservation {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
    {s' : JointState P}
    (h : jointStep cfg ccfg bls ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok s') :
    CorpusPreservation beacon s'.beacon := by
  obtain ⟨_, _, req, fslot, b1, b2, b', e', _, hb1, hb2, _, _, hb', rfl⟩ :=
    jointStep_cross_ok_iff.mp h
  have c1 : CorpusPreservation beacon b1 := by
    split at hb1
    · exact (processSlots_corpusPreservation (by decide) _ hb1).1
    · cases hb1; exact CorpusPreservation.refl _
  have c2 : CorpusPreservation b1 b2 := (upgradeToFulu_corpusPreservation_and_frame ccfg hb2).1
  have c3 : CorpusPreservation b2 b' := by
    split at hb'
    · obtain ⟨_, _, hb'⟩ := bind_eq_ok_iff.mp hb'
      obtain ⟨_, _, hb'⟩ := bind_eq_ok_iff.mp hb'
      obtain ⟨s, hproc, hb'⟩ := bind_eq_ok_iff.mp hb'
      obtain ⟨_, _, hb'⟩ := bind_eq_ok_iff.mp hb'
      cases hb'
      exact processBlock_corpusPreservation (by decide) _ hproc
    · exact stateTransition_corpusPreservation (by decide) _ hb'
  exact c1.trans (c2.trans c3)

open Jaune in
/-- One successful `jointStep` preserves `CorpusPres` (`BalancesMatchValidators` and
`PendingConsolidationsDistinct`) across all three accepted fork pairs (Electra→Electra,
Fulu→Fulu, and Electra→Fulu crossing). -/
theorem jointStep_corpusPreservation {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') : CorpusPreservation s.beacon s'.beacon := by
  obtain ⟨fs, beacon, exec⟩ := s
  obtain ⟨fb, sb⟩ := b
  cases fs <;> cases fb
  all_goals first
    | exact jointStep_electra_corpusPreservation h
    | exact jointStep_fulu_corpusPreservation h
    | exact jointStep_cross_corpusPreservation h
    | (unfold jointStep at h; cases h)

open Jaune in
theorem jointStep_balancesMatchValidators {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') (hB : BalancesMatchValidators s.beacon) :
    BalancesMatchValidators s'.beacon :=
  (jointStep_corpusPreservation h).balancesMatchValidators hB

open Jaune in
theorem jointStep_pendingConsolidationsDistinct {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') (hD : PendingConsolidationsDistinct s.beacon) :
    PendingConsolidationsDistinct s'.beacon :=
  (jointStep_corpusPreservation h).pendingConsolidationsDistinct hD

open Jaune in
theorem jointStep_corpusAnchorInvariant {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') (hI : CorpusAnchorInvariant s.beacon) :
    CorpusAnchorInvariant s'.beacon :=
  ⟨jointStep_anchorInvariant h hI.1,
   jointStep_balancesMatchValidators h hI.2.1,
   jointStep_pendingConsolidationsDistinct h hI.2.2⟩

open Jaune in
theorem JointReach.corpusPreservation {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (h : JointReach cfg ccfg bls s₀ s) : CorpusPreservation s₀.beacon s.beacon := by
  induction h with
  | refl => exact CorpusPreservation.refl _
  | step _ _ hs ih => exact ih.trans (jointStep_corpusPreservation hs)

open Jaune in
theorem JointReach.balancesMatchValidators {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (h : JointReach cfg ccfg bls s₀ s)
    (h0 : BalancesMatchValidators s₀.beacon) : BalancesMatchValidators s.beacon :=
  h.corpusPreservation.balancesMatchValidators h0

open Jaune in
theorem JointReach.pendingConsolidationsDistinct {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (h : JointReach cfg ccfg bls s₀ s)
    (h0 : PendingConsolidationsDistinct s₀.beacon) : PendingConsolidationsDistinct s.beacon :=
  h.corpusPreservation.pendingConsolidationsDistinct h0

open Jaune in
theorem JointReach.corpusAnchorInvariant {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (h : JointReach cfg ccfg bls s₀ s)
    (h0 : CorpusAnchorInvariant s₀.beacon) : CorpusAnchorInvariant s.beacon :=
  ⟨h.anchorInvariant h0.1, h.balancesMatchValidators h0.2.1, h.pendingConsolidationsDistinct h0.2.2⟩

end JauneConsensus.Facts
