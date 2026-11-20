import Jaune.Run.CheckedTransaction
import Jaune.MessageCall.CheckedCanonical
import Jaune.Run.Prefix
import Jaune.GasFacts

/-!
# What a Checked block transition establishes (goal `jaune-shape-and-names-v1`, G2b)

The native counterparts of `Jaune.Run.BlockFacts` and of the run-layer half of
`Jaune.Run.Canonical`, stated over the Checked run layer and proved without the waiting
interpreter.

* `stateTransitionCoreE_mapError`, `_header`, `_preserves_chainId` and `_eq_ok`: the error
  embedding commutes with the transition, and a success validated the header, kept the chain
  identity, appended the block and carries the header's state root.
* Canonicality: native preparation keeps the entry world canonical and the transaction record
  unchanged, so a settled top-level message (`TopLevel.runNative_canonical`, over
  `Frame.runTop_canonical`), a signed transaction, the system calls, every body operation, the
  importer, `applyBody` and the block transition leave a canonical state.
-/

namespace Jaune.Checked

open Jaune

/-! ### The block transition -/

private theorem except_mapError_id {ε α : Type} (r : Except ε α) : r.mapError id = r := by
  cases r <;> rfl

private theorem except_mapError_bind {ε ε' α β : Type}
    (g : ε → ε') (r : Except ε α) (k : α → Except ε β) :
    (r.bind k).mapError g = (r.mapError g).bind (fun a => (k a).mapError g) := by
  cases r <;> rfl

private theorem except_mapError_comp {ε ε' ε'' α : Type}
    (g : ε → ε') (g' : ε' → ε'') (r : Except ε α) :
    (r.mapError g).mapError g' = r.mapError (g' ∘ g) := by
  cases r <;> rfl

/-- Embedding the transition's error type commutes with the whole algorithm, including
failures. -/
theorem stateTransitionCoreE_mapError {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except TransitionError Unit) :
    stateTransitionCoreE embed f ch block
      (fun u => (checkOmmers u).mapError embed) =
      (stateTransitionCoreE id f ch block checkOmmers).mapError embed := by
  simp only [stateTransitionCoreE, except_mapError_id, Function.id_comp, bind,
    except_mapError_bind, except_mapError_comp]
  rfl

/-- A successful transition validated the header. -/
theorem stateTransitionCoreE_header {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (h : stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    validateHeader f.ruleSet ch block.header = .ok () := by
  unfold stateTransitionCoreE at h
  obtain ⟨u, hu, _⟩ := Except.bind_eq_ok h
  cases u
  exact Except.mapError_eq_ok_iff.mp hu

/-- A successful transition keeps the chain identity. -/
theorem stateTransitionCoreE_preserves_chainId {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (h : stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    ch'.chainId = ch.chainId := by
  unfold stateTransitionCoreE at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases h
  rfl

/-- Success inversion: the header was valid, the block was appended and the new state's root
is the header's. -/
theorem stateTransitionCoreE_eq_ok {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (h : stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    validateHeader f.ruleSet ch block.header = .ok () ∧
      ch'.blocks = appendBlock ch.blocks block ∧
      ch'.state.root = block.header.stateRoot := by
  unfold stateTransitionCoreE at h
  obtain ⟨u1, hvh, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨q, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨u3, hchk, h⟩ := Except.bind_eq_ok h
  cases u1
  cases u3
  cases h
  exact ⟨Except.mapError_eq_ok_iff.mp hvh, rfl,
    Block.check_stateRoot (Except.mapError_eq_ok_iff.mp hchk)⟩

/-! ### Preparation keeps the entry world canonical and the transaction record -/

theorem Frame.State.liftMachine_ok_world {ε : Type} {core : Machine → Except (ε × Machine) Machine}
    {s t : Frame.State} (h : s.liftMachine core = .ok t) : t.world = s.world := by
  unfold Frame.State.liftMachine at h
  split at h <;> cases h
  rfl

theorem TopLevel.preparationCharge_ok_world {core : Machine → Except (ExceptionalHalt × Machine) Machine}
    {s t : Frame.State} (h : TopLevel.preparationCharge (s.liftMachine core) = .ok t) :
    t.world = s.world :=
  Frame.State.liftMachine_ok_world (Except.mapError_eq_ok_iff.mp h)

theorem Frame.State.writeDelegation_canonical {s : Frame.State} (h : s.world.Canonical)
    (authority target : Address) : (s.writeDelegation authority target).world.Canonical := by
  unfold Frame.State.writeDelegation
  dsimp only [Frame.State.withWorld, World.clearStorageWritesIfEmpty]
  exact ⟨State.Canonical.incrNonce (State.Canonical.setCode h.1 _ _) _, h.2⟩

namespace TopLevel

theorem authorizationStep_canonical {auth : Authorization} {input out : Input} {refund r : U256}
    (h : input.checkpoint.world.Canonical) (hs : authorizationStep auth input refund = .ok (out, r)) :
    out.checkpoint.world.Canonical ∧ out.message = input.message := by
  unfold authorizationStep at hs
  try dsimp only at hs
  by_cases hchain : (auth.chainId != input.message.context.block.chainId.toU256 && auth.chainId != 0) = true
  · simp only [hchain, ↓reduceIte] at hs
    cases hs; exact ⟨h, rfl⟩
  · simp only [hchain, Bool.false_eq_true, ↓reduceIte] at hs
    by_cases hnonce : auth.nonce = UInt64.max
    · simp only [hnonce, ↓reduceIte] at hs
      cases hs; exact ⟨h, rfl⟩
    · simp only [hnonce, ↓reduceIte] at hs
      split at hs
      · cases hs; exact ⟨h, rfl⟩
      · cases hs
      ·
        split at hs
        · cases hs; exact ⟨h, rfl⟩
        split at hs
        · cases hs; exact ⟨h, rfl⟩
        · cases hs
          exact ⟨Frame.State.writeDelegation_canonical h _ _, rfl⟩

theorem authorizationLoop_canonical :
    ∀ (auths : List Authorization) {input out : Input} {refund r : U256},
      input.checkpoint.world.Canonical → authorizationLoop auths input refund = .ok (out, r) →
        out.checkpoint.world.Canonical ∧ out.message = input.message
  | [], _, _, _, _, h, hs => by cases hs; exact ⟨h, rfl⟩
  | auth :: rest, input, out, refund, r, h, hs => by
    unfold authorizationLoop at hs
    obtain ⟨⟨mid, r'⟩, hm, hs⟩ := Except.bind_eq_ok hs
    have ⟨hc, he⟩ := authorizationStep_canonical h hm
    have ⟨hc', he'⟩ := authorizationLoop_canonical rest hc hs
    exact ⟨hc', he'.trans he⟩

theorem applyAuthorizations_canonical {input out : Input} {refund : Nat}
    (h : input.checkpoint.world.Canonical) (hs : applyAuthorizations input = .ok (out, refund)) :
    out.checkpoint.world.Canonical ∧ out.message.context.tx = input.message.context.tx := by
  unfold applyAuthorizations at hs
  split at hs
  · cases hs; exact ⟨h, rfl⟩
  · obtain ⟨⟨authorized, r⟩, ha, hs⟩ := Except.bind_eq_ok hs
    have ⟨hc, he⟩ := authorizationLoop_canonical _ h ha
    dsimp only at hs
    split at hs
    · cases hs
    · cases hs
      exact ⟨hc, by rw [← he]⟩

theorem resolveCodeDelegation_canonical {input : Input} (h : input.checkpoint.world.Canonical) :
    (resolveCodeDelegation input).checkpoint.world.Canonical ∧
      (resolveCodeDelegation input).message.context.tx = input.message.context.tx := by
  unfold resolveCodeDelegation
  dsimp only
  split
  · exact ⟨h, rfl⟩
  · exact ⟨h, rfl⟩

theorem prepareWithoutStateGas_canonical {input : Input} {message : Message} {s : Frame.State}
    {refund : Nat} (h : input.checkpoint.world.Canonical)
    (hp : prepareWithoutStateGas input = .ok (.frame message s refund)) :
    s.world.Canonical ∧ message.context.tx = input.message.context.tx := by
  unfold prepareWithoutStateGas at hp
  split at hp
  · split at hp
    · cases hp
    · cases hp; exact ⟨h, rfl⟩
  · obtain ⟨⟨authorized, r⟩, ha, hp⟩ := Except.bind_eq_ok hp
    cases hp
    have ⟨hc, he⟩ := applyAuthorizations_canonical h ha
    have ⟨hc', he'⟩ := resolveCodeDelegation_canonical hc
    exact ⟨hc', he'.trans he⟩

theorem chargeNewAuthority_canonical {rules : StateGasRules} {authority : Address} {s t : Frame.State}
    (h : s.world.Canonical) (hs : chargeNewAuthority rules authority s = .ok t) : t.world.Canonical := by
  unfold chargeNewAuthority at hs
  split at hs
  · rw [preparationCharge_ok_world hs]; exact h
  · cases hs; exact h

theorem chargeAuthorityWrite_canonical {rules : StateGasRules} {authority : Address} {s t : Frame.State}
    {paid paid' : AdrSet} (h : s.world.Canonical)
    (hs : chargeAuthorityWrite rules authority s paid = .ok (t, paid')) : t.world.Canonical := by
  unfold chargeAuthorityWrite at hs
  split at hs
  · cases hs; exact h
  · obtain ⟨u, hu, hs⟩ := Except.bind_eq_ok hs
    cases hs
    rw [preparationCharge_ok_world hu]; exact h

theorem chargeAuthorizationBase_canonical {rules : StateGasRules} {original : State}
    {authority target : Address} {s t : Frame.State} {set set' : AdrSet} (h : s.world.Canonical)
    (hs : chargeAuthorizationBase rules original authority target s set = .ok (t, set')) :
    t.world.Canonical := by
  unfold chargeAuthorizationBase at hs
  split at hs
  · cases hs; exact h
  · dsimp only at hs
    split at hs
    · obtain ⟨u, hu, hs⟩ := Except.bind_eq_ok hs
      cases hs
      rw [preparationCharge_ok_world hu]; exact h
    · obtain ⟨u, hu, hs⟩ := Except.bind_eq_ok hs
      cases hs
      cases hu; exact h

theorem applyValidatedAuthorization_canonical {rules : StateGasRules} {context : CallContext}
    {authority target : Address} {s : Frame.State} {paid set : AdrSet} {out}
    (h : s.world.Canonical)
    (hs : applyValidatedAuthorization rules context authority target s paid set = .ok out) :
    out.1.world.Canonical := by
  unfold applyValidatedAuthorization at hs
  obtain ⟨s1, h1, hs⟩ := Except.bind_eq_ok hs
  obtain ⟨⟨s2, paid2⟩, h2, hs⟩ := Except.bind_eq_ok hs
  obtain ⟨⟨s3, set3⟩, h3, hs⟩ := Except.bind_eq_ok hs
  cases hs
  exact Frame.State.writeDelegation_canonical (chargeAuthorizationBase_canonical
    (chargeAuthorityWrite_canonical (chargeNewAuthority_canonical h h1) h2) h3) _ _

theorem amsterdamAuthorizationStep_canonical {rules : StateGasRules} {context : CallContext}
    {auth : Authorization} {s : Frame.State} {paid set : AdrSet} {out}
    (h : s.world.Canonical)
    (hs : amsterdamAuthorizationStep rules context auth s paid set = .ok out) :
    out.1.world.Canonical := by
  unfold amsterdamAuthorizationStep at hs
  split at hs
  · cases hs; exact h
  split at hs
  · cases hs; exact h
  split at hs
  · cases hs; exact h
  · cases hs
  · dsimp only at hs
    split at hs
    · cases hs; exact h
    split at hs
    · cases hs; exact h
    · exact applyValidatedAuthorization_canonical (by exact h) hs

theorem amsterdamAuthorizationLoop_canonical {rules : StateGasRules} {context : CallContext} :
    ∀ (auths : List Authorization) {s : Frame.State} {paid set : AdrSet} {out},
      s.world.Canonical → amsterdamAuthorizationLoop rules context auths s paid set = .ok out →
        out.1.world.Canonical
  | [], _, _, _, _, h, hs => by cases hs; exact h
  | auth :: rest, s, paid, set, out, h, hs => by
    unfold amsterdamAuthorizationLoop at hs
    obtain ⟨⟨mid, paid', set'⟩, hm, hs⟩ := Except.bind_eq_ok hs
    exact amsterdamAuthorizationLoop_canonical rest (amsterdamAuthorizationStep_canonical h hm) hs

theorem applyAmsterdamAuthorizations_canonical {rules : StateGasRules} {input : Input} {s : Frame.State}
    (h : input.checkpoint.world.Canonical) (hs : applyAmsterdamAuthorizations rules input = .ok s) :
    s.world.Canonical := by
  unfold applyAmsterdamAuthorizations at hs
  obtain ⟨⟨t, _, _⟩, ht, hs⟩ := Except.bind_eq_ok hs
  cases hs
  exact amsterdamAuthorizationLoop_canonical _ h ht

theorem resolveAmsterdamCall_canonical {message out : Message} {s t : Frame.State}
    (h : s.world.Canonical) (hs : resolveAmsterdamCall message s = .ok (out, t)) :
    t.world.Canonical ∧ out.context.tx = message.context.tx := by
  unfold resolveAmsterdamCall at hs
  obtain ⟨u, hu, hs⟩ := Except.bind_eq_ok hs
  cases hs
  have hw : u.world.Canonical := by rw [preparationCharge_ok_world hu]; exact h
  refine ⟨?_, rfl⟩
  split <;> exact hw

theorem dispatchAmsterdam_canonical {rules : StateGasRules} {message out : Message} {s t : Frame.State}
    (h : s.world.Canonical) (hs : dispatchAmsterdam rules message s = .ok (out, t)) :
    t.world.Canonical ∧ out.context.tx = message.context.tx := by
  unfold dispatchAmsterdam at hs
  dsimp only at hs
  split at hs
  · split at hs
    · cases hs
    · split at hs
      · obtain ⟨u, hu, hs⟩ := Except.bind_eq_ok hs
        cases hs
        rw [preparationCharge_ok_world hu]; exact ⟨h, rfl⟩
      · obtain ⟨u, hu, hs⟩ := Except.bind_eq_ok hs
        cases hs
        cases hu; exact ⟨h, rfl⟩
  · split at hs
    · obtain ⟨u, hu, hs⟩ := Except.bind_eq_ok hs
      have hw : u.world.Canonical := by rw [preparationCharge_ok_world hu]; exact h
      exact resolveAmsterdamCall_canonical hw hs
    · obtain ⟨u, hu, hs⟩ := Except.bind_eq_ok hs
      cases hu
      exact resolveAmsterdamCall_canonical (by exact h) hs

theorem prepareAmsterdamFrame_canonical {rules : StateGasRules} {input : Input} {message : Message}
    {s : Frame.State} (h : input.checkpoint.world.Canonical)
    (hs : prepareAmsterdamFrame rules input = .ok (message, s)) :
    s.world.Canonical ∧ message.context.tx = input.message.context.tx := by
  unfold prepareAmsterdamFrame at hs
  dsimp only at hs
  split at hs
  · obtain ⟨u, hu, hs⟩ := Except.bind_eq_ok hs
    cases hu
    exact dispatchAmsterdam_canonical (by exact h) hs
  · obtain ⟨u, hu, hs⟩ := Except.bind_eq_ok hs
    have hw := applyAmsterdamAuthorizations_canonical h hu
    exact dispatchAmsterdam_canonical (by exact hw) hs

/-- Native preparation keeps the entry world canonical and the transaction record unchanged. -/
theorem prepareNative_canonical {input : Input} {message : Message} {s : Frame.State} {refund : Nat}
    (h : input.checkpoint.world.Canonical)
    (hp : prepareNative input = .ok (.frame message s refund)) :
    s.world.Canonical ∧ message.context.tx = input.message.context.tx := by
  unfold prepareNative at hp
  split at hp
  · exact prepareWithoutStateGas_canonical h hp
  · split at hp
    · cases hp
      exact prepareAmsterdamFrame_canonical h (by assumption)
    · cases hp
    · cases hp

/-- **A settled top-level message leaves a canonical state**, for a refusal, a failed frame and a
successful one, over `Frame.runTop_canonical`. -/
theorem runNative_canonical {input : Input} (h : input.checkpoint.world.Canonical)
    (ho : State.Canonical input.message.context.tx.originalState) {run : Run}
    (hr : runNative input = .ok run) : (run.settlement input).state.Canonical := by
  unfold runNative at hr
  obtain ⟨prepared, hp, hr⟩ := Except.bind_eq_ok hr
  cases prepared with
  | refused reason =>
    cases hr
    cases reason <;> exact h.1
  | frame message s refund =>
    have ⟨hs, htx⟩ := prepareNative_canonical h hp
    change (Frame.runTopWithRoot ⟨message, s⟩).map (Run.frame ⟨message, s⟩ refund) = .ok run at hr
    cases accepted : Frame.runTopWithRoot ⟨message, s⟩ with
    | error => rw [accepted] at hr; cases hr
    | ok top =>
      rw [accepted] at hr
      cases hr
      have result := congrArg (Except.map Frame.TopRun.result) accepted
      change Frame.runTop ⟨message, s⟩ = .ok top.result at result
      have hf : Frame.Canonical ⟨message, s⟩ := ⟨hs, by rw [show message.context.tx.originalState =
        input.message.context.tx.originalState from congrArg TransactionContext.originalState htx]; exact ho⟩
      have hw := Frame.runTop_canonical hf result
      unfold Run.settlement
      dsimp only
      cases hres : top.result <;> rw [hres] at hw <;>
        (split <;> exact hw.1)

end TopLevel

/-! ### The transaction and the system calls -/

/-- Native preparation over a canonical transaction-start state yields a canonical entry. -/
theorem Transaction.prepare_canonical {block : BlockContext} {state : State}
    {admitted : Transaction.Admitted} {tx : Jaune.Transaction} {prepared : Transaction.Prepared}
    (h : state.Canonical) (hp : prepare block state admitted tx = .ok prepared) :
    prepared.input.checkpoint.world.Canonical ∧
      State.Canonical prepared.input.message.context.tx.originalState := by
  unfold prepare at hp
  obtain ⟨st, hst, hp⟩ := Except.bind_eq_ok hp
  have hstc : st.Canonical :=
    State.Canonical.subBal (State.Canonical.incrNonce h _) (Option.toExcept_eq_ok hst)
  cases target : tx.type.to? <;> simp only [target, pure, Except.pure] at hp <;> cases hp <;>
    exact ⟨⟨hstc, TransientStorage.canonical_empty⟩, h⟩

/-- Settlement keeps the settled message's state canonical: fee credits, then the self-destructs
and the sweep, which only erase accounts. -/
theorem Transaction.settleRun_canonical {admitted : Transaction.Admitted}
    {prepared : Transaction.Prepared} {tx : Jaune.Transaction} {index : Nat} {run : TopLevel.Run}
    (h : (run.settlement prepared.input).state.Canonical) {p}
    (hp : settleRun admitted prepared tx index run = .ok p) : State.Canonical p.1.state := by
  unfold settleRun at hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact State.Canonical.sweepTouchedAccounts (State.Canonical.settleSelfdestructs
    (State.Canonical.addBal (State.Canonical.addBal h _ _) _ _) _ _) _ _

/-- **A successful signed transaction leaves a canonical state.** -/
theorem Transaction.run_canonical {block : BlockContext} {state : State} (h : state.Canonical)
    {bout : BlockOutput} {tx : Jaune.Transaction} {index : Nat} {p}
    (hp : Transaction.run block state bout tx index = .ok p) : State.Canonical p.1.state := by
  unfold Transaction.run at hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨prepared, hprepared, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨run, hrun, hp⟩ := Except.bind_eq_ok hp
  have ⟨hc, ho⟩ := Transaction.prepare_canonical h hprepared
  exact Transaction.settleRun_canonical
    (TopLevel.runNative_canonical hc ho (Except.mapError_eq_ok_iff.mp hrun)) hp

/-- A protocol system call on a canonical state leaves a canonical state. -/
theorem processSystemRun_canonical {block : BlockContext} {state : State} (h : state.Canonical)
    {target : Address} {code : ByteArray} {data : Bytes} {run : SystemRun}
    (hp : processSystemRun block state target code data = .ok run) : run.settlement.state.Canonical := by
  unfold processSystemRun at hp
  obtain ⟨message, hm, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact TopLevel.runNative_canonical ⟨h, TransientStorage.canonical_empty⟩ h hm

theorem processCheckedSystemRun_canonical {block : BlockContext} {state : State} (h : state.Canonical)
    {target : Address} {data : Bytes} {run : SystemRun}
    (hp : processCheckedSystemRun block state target data = .ok run) : run.settlement.state.Canonical := by
  unfold processCheckedSystemRun at hp
  dsimp only at hp
  split at hp
  · obtain ⟨u, hu, hp⟩ := Except.bind_eq_ok hp
    nomatch hu
  · obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    split at hp
    · nomatch hp
    · cases hp
      exact processSystemRun_canonical h (Except.mapError_eq_ok_iff.mp hq)

/-- The request producers on a canonical state leave a canonical state. -/
theorem processCheckedSystemTransaction_canonical {block : BlockContext} {state : State}
    (h : state.Canonical) {target : Address} {data : Bytes} {settlement : TopLevel.Settlement}
    (hp : processCheckedSystemTransaction block state target data = .ok settlement) :
    settlement.state.Canonical := by
  unfold processCheckedSystemTransaction at hp
  cases hr : processCheckedSystemRun block state target data with
  | error => rw [hr] at hp; cases hp
  | ok run =>
    rw [hr] at hp
    cases hp
    exact processCheckedSystemRun_canonical h hr

/-! ### The body -/

/-- **One body operation keeps the prefix's state canonical.** -/
theorem Body.stepRun_canonical {block : BlockContext} {p : Jaune.Body.Prefix}
    (hp : p.state.Canonical) {op : BodyOp} {r : OpRun} {q : Jaune.Body.Prefix}
    (hs : Body.stepRun block p op = .ok (r, q)) : q.state.Canonical := by
  cases op with
  | systemCall address data index =>
    simp only [Body.stepRun, Body.stepWith] at hs
    obtain ⟨d, _, hs⟩ := Except.bind_eq_ok hs
    obtain ⟨run, hrun, hs⟩ := Except.bind_eq_ok hs
    cases hs
    exact processSystemRun_canonical hp (Except.mapError_eq_ok_iff.mp hrun)
  | transaction tx index =>
    simp only [Body.stepRun, Body.stepWith] at hs
    obtain ⟨⟨run, bout⟩, ht, hs⟩ := Except.bind_eq_ok hs
    cases hs
    exact Transaction.run_canonical hp ht
  | withdrawals ws index =>
    simp only [Body.stepRun, Body.stepWith] at hs
    cases hs
    exact processWithdrawalsState_canonical hp ws
  | depositRequests =>
    simp only [Body.stepRun, Body.stepWith] at hs
    obtain ⟨_, _, hs⟩ := Except.bind_eq_ok hs
    cases hs
    exact hp
  | requestCall type address index =>
    simp only [Body.stepRun, Body.stepWith] at hs
    obtain ⟨run, hrun, hs⟩ := Except.bind_eq_ok hs
    cases hs
    exact processCheckedSystemRun_canonical hp hrun
  | rewards coinbase minerReward credits =>
    simp only [Body.stepRun, Body.stepWith] at hs
    cases hs
    exact State.Canonical.creditAll (State.Canonical.addBal hp _ _) credits
  | buildAccessList =>
    simp only [Body.stepRun, Body.stepWith] at hs
    cases hs
    exact hp
  | checkAccessListLimit =>
    simp only [Body.stepRun, Body.stepWith] at hs
    obtain ⟨_, _, hs⟩ := Except.bind_eq_ok hs
    cases hs
    exact hp

/-- The streaming step keeps the prefix's state canonical. -/
theorem Body.step_canonical {block : BlockContext} {p : Jaune.Body.Prefix}
    (hp : p.state.Canonical) {op : BodyOp} {q : Jaune.Body.Prefix}
    (hs : Body.step block p op = .ok q) : q.state.Canonical := by
  rw [← Body.stepRun_prefix] at hs
  cases hr : Body.stepRun block p op with
  | error => rw [hr] at hs; cases hs
  | ok pair =>
    rw [hr] at hs
    cases hs
    exact Body.stepRun_canonical hp hr

/-- A recorded run of operations keeps the prefix's state canonical. -/
theorem Body.run_canonical (block : BlockContext) :
    ∀ (ops : List BodyOp) {p : Jaune.Body.Prefix}, p.state.Canonical →
      ∀ {rs : List OpRun} {q : Jaune.Body.Prefix}, Body.run block p ops = .ok (rs, q) →
        q.state.Canonical
  | [], _, hp, _, _, hr => by cases hr; exact hp
  | op :: ops, p, hp, rs, q, hr => by
    simp only [Body.run] at hr
    obtain ⟨⟨r, p'⟩, hs, hr⟩ := Except.bind_eq_ok hr
    obtain ⟨⟨rs', q'⟩, hr', hr⟩ := Except.bind_eq_ok hr
    cases hr
    exact Body.run_canonical block ops (Body.stepRun_canonical hp hs) hr'

/-- The streaming fold keeps the prefix's state canonical. -/
theorem Body.fold_canonical (block : BlockContext) :
    ∀ (ops : List BodyOp) {p : Jaune.Body.Prefix}, p.state.Canonical →
      ∀ {q : Jaune.Body.Prefix}, ops.foldlM (Body.step block) p = .ok q → q.state.Canonical
  | [], _, hp, _, hf => by cases hf; exact hp
  | op :: ops, p, hp, q, hf => by
    rw [List.foldlM_cons] at hf
    obtain ⟨p', hs, hf⟩ := Except.bind_eq_ok hf
    exact Body.fold_canonical block ops (Body.step_canonical hp hs) hf

/-- The importer's body over a canonical prestate leaves a canonical state. -/
theorem Body.importer_canonical {block : BlockContext} {state : State} (h : state.Canonical)
    {txs : List (Bytes ⊕ Jaune.Transaction)} {ommers : List Header} {wds : List Withdrawal}
    {q : Jaune.Body.Prefix} (hp : Body.importer block state txs ommers wds = .ok q) :
    q.state.Canonical := by
  unfold Body.importer at hp
  obtain ⟨decoded, _, hp⟩ := Except.bind_eq_ok hp
  exact Body.fold_canonical block _ h hp

/-- **A successful block body leaves a canonical state.** -/
theorem applyBody_canonical {block : BlockContext} {state : State} (h : state.Canonical)
    {txs : List (Bytes ⊕ Jaune.Transaction)} {ommers : List Header} {wds : List Withdrawal} {p}
    (hp : applyBody block state txs ommers wds = .ok p) : State.Canonical p.1 := by
  unfold applyBody at hp
  cases hq : Body.importer block state txs ommers wds with
  | error e => rw [hq] at hp; cases hp
  | ok q =>
    rw [hq] at hp
    cases hp
    exact Body.importer_canonical h hq

/-- **Canonicality depends on the common execution body**, not on the ommer check or the error
carrier. -/
theorem stateTransitionCoreE_canonical {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch : BlockChain} (h : ch.Canonical) {block : Block} {ch'}
    {checkOmmers : Unit → Except ε Unit}
    (hp : stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    ch'.Canonical := by
  unfold stateTransitionCoreE at hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact Body.importer_canonical (state := ch.state) h (Except.mapError_eq_ok_iff.mp hq)

end Jaune.Checked
