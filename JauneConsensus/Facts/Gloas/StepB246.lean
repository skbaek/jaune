import JauneConsensus.Facts.JointGloas
import JauneConsensus.Facts.Gloas.InvariantsGen

/-!
# The per-step consensus layer of B2, B4 and B6 (goal `eip8282-gloas-cross-layer-v1`, RBS)

Lemmas over ONE successful Gloas→Gloas joint step
`jointStepG cfg ccfg bls (.gloas preB preExec preParent) (.gloas b) env? = .ok (.gloas postB postExec postParent)`,
which the run-level theorems of statements.md B2, B4 and B6 compose.

* `GStepView`: the step opened (`gloasStep_ok_iff`): the **post-slots state** `postSlots`, the
  execution-side settlement `o : ParentSettle P` keyed on `parentFull postSlots b.message`, the
  post-block state, and the step's end. `gloasStep_view` gives one; `GStepView.unique` says it is
  unique, so "the step's settlement" is well defined (`GStepView.settle`).
* `GStepView.processBlock`: the block transition runs Gloas `process_block` on `postSlots`, so
  the BF1 traces are read **at `postSlots`**, not at the step's pre-state.
* **B2/B4 consensus half** (`gloasStep_builderDeposit_applied`, `gloasStep_builderExit_applied`):
  a builder deposit (exit) request at position `k` of the block's `parent_execution_requests` is
  only possible when the step settles its parent FULL over a delivered payload `env`; the
  child's requests are then `env`'s by value, the built-upon chain becomes the payload's `post`,
  and request `k` runs from `tr[k]` to `tr[k+1]` of the trace read at `postSlots`, with exactly one
  classification outcome and `tr[k+1] = apply…Outcome tr[k] r o`.
* **non-FULL settles nothing** (`GStepView.requests_of_not_full`): an EMPTY or `.landed`
  settlement has the empty requests by value, so no builder request runs.
* **B6 per step** (`GStepView.full_iff`, `GStepView.postParent_cases`): a step applies requests
  only by settling FULL the payload its pre-state holds as `.delivered`, and its post-state holds
  only the block's own payload (`.withheld`, or `.delivered` with the block's own envelope).
* **B6 control (i)**: `settleParent'`, the mutant that treats a delivered payload's requests as
  applied at delivery; on a delivered payload with requests it refuses the child that carries
  them, where `settleParent` applies them at the settling step (`settleParent_applies_at_settle`,
  `settleParent'_refuses_at_settle`, `settleParent'_accepts_empty`).
-/

namespace JauneConsensus.Facts.Gloas

open Jaune JauneConsensus JauneConsensus.Facts

variable {P : Preset}

/-! ## The step, opened -/

/-- Whether a settlement is FULL over a delivered payload. -/
def _root_.JauneConsensus.ParentSettle.isFull : ParentSettle P → Bool
  | .full .. => true
  | _ => false

/-- A successful Gloas→Gloas joint step, opened: the post-slots state `postSlots` (the state
Gloas `process_block` receives), the execution-side settlement `settle`, the post-block state,
and the step's end. -/
structure GStepView (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    (preB : Gloas.BeaconState P) (preExec : BlockChain) (preParent : ParentPayload P)
    (b : Gloas.SignedBeaconBlock P) (env? : Option (Gloas.SignedExecutionPayloadEnvelope P))
    (postB : Gloas.BeaconState P) (postExec : BlockChain) (postParent : ParentPayload P) where
  postSlots : Gloas.BeaconState P
  settle : ParentSettle P
  slots : Gloas.processSlots (gloasCtx ccfg bls) preB b.message.slot = .ok postSlots
  settled : settleParent preParent preExec (parentFull postSlots b.message)
    b.message.body.parent_execution_requests = .ok (postExec, settle)
  block : gloasBlockTransition (gloasCtx ccfg bls) postSlots b = .ok postB
  stepEnd : (env? = none ∧ postParent = .withheld) ∨
    ∃ e req postE, env? = some e ∧ verifyEnvelopeG cfg ccfg bls postB postExec e = .ok (req, postE) ∧
      postParent = .delivered e req postE

section View

variable {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
  {preB : Gloas.BeaconState P} {preExec : BlockChain} {preParent : ParentPayload P}
  {b : Gloas.SignedBeaconBlock P} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
  {postB : Gloas.BeaconState P} {postExec : BlockChain} {postParent : ParentPayload P}

/-- Every successful Gloas→Gloas joint step has a view. -/
theorem gloasStep_view
    (h : jointStepG cfg ccfg bls (.gloas preB preExec preParent) (.gloas b) env? =
      .ok (.gloas postB postExec postParent)) :
    Nonempty (GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent) := by
  obtain ⟨postSlots, post, exec', o, h0, hs, hp, hd⟩ := jointStepG_gloas_ok_iff.mp h
  rcases gloasDeliverOpt_ok_iff.mp hd with ⟨hn, he⟩ | ⟨e, req, postE, he, hv, hs'⟩
  · cases he
    exact ⟨⟨postSlots, o, h0, hs, hp, Or.inl ⟨hn, rfl⟩⟩⟩
  · cases hs'
    exact ⟨⟨postSlots, o, h0, hs, hp, Or.inr ⟨e, req, postE, he, hv, rfl⟩⟩⟩

/-- The view is unique: the post-slots state and the settlement are functions of the step. -/
theorem GStepView.unique
    (V W : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent) :
    V.postSlots = W.postSlots ∧ V.settle = W.settle := by
  have h1 : V.postSlots = W.postSlots := Except.ok.inj (V.slots.symm.trans W.slots)
  refine ⟨h1, ?_⟩
  have h2 := V.settled
  rw [h1, W.settled] at h2
  exact (Prod.mk.inj (Except.ok.inj h2)).2.symm

/-- The block transition after the slots runs Gloas `process_block` on the post-slots state. -/
theorem GStepView.processBlock
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent) :
    Gloas.processBlock (gloasCtx ccfg bls) V.postSlots b.message = .ok postB :=
  Inv.applySignedBlockWith_ok V.block

/-- The settlement, by cases (`settleParent_ok_iff` at the step). -/
theorem GStepView.settle_cases
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent) :
    (parentFull V.postSlots b.message = true ∧ ∃ env req post, preParent = .delivered env req post ∧
        b.message.body.parent_execution_requests = env.message.execution_requests ∧
        postExec = post ∧ V.settle = .full env req post) ∨
      (parentFull V.postSlots b.message = true ∧ preParent = .landed ∧
        b.message.body.parent_execution_requests = Gloas.ExecutionRequests.empty ∧
        postExec = preExec ∧ V.settle = .landed) ∨
      (parentFull V.postSlots b.message = false ∧
        b.message.body.parent_execution_requests = Gloas.ExecutionRequests.empty ∧
        postExec = preExec ∧ V.settle = .empty) :=
  settleParent_ok_iff.mp V.settled

/-- **B6 per step, settle side.** The step settles FULL exactly when its pre-state holds a
delivered payload and the block builds on it; the settlement then names that payload, the
child's requests are the envelope's by value, and the built-upon chain becomes its `post`. -/
theorem GStepView.full_iff
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    {env : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P}
    {post : BlockChain} :
    V.settle = .full env req post ↔
      parentFull V.postSlots b.message = true ∧ preParent = .delivered env req post ∧
        b.message.body.parent_execution_requests = env.message.execution_requests ∧
        postExec = post := by
  constructor
  · intro hs
    rcases V.settle_cases with ⟨hf, env', req', post', hp, hr, he, hs'⟩ | ⟨_, _, _, _, hs'⟩ |
        ⟨_, _, _, hs'⟩
    · rw [hs] at hs'; cases hs'; exact ⟨hf, hp, hr, he⟩
    · rw [hs] at hs'; cases hs'
    · rw [hs] at hs'; cases hs'
  · rintro ⟨hf, rfl, hr, rfl⟩
    have := V.settled
    rw [hf, settleParent_ok_iff] at this
    rcases this with ⟨_, env', req', post', hp, _, he, hs⟩ | ⟨_, hp, _⟩ | ⟨hf', _⟩
    · cases hp; exact hs
    · cases hp
    · cases hf'

/-- **Non-FULL settles nothing.** An EMPTY or `.landed` settlement has the empty requests by
value: the block carries no builder deposit and no builder exit request. -/
theorem GStepView.requests_of_not_full
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    (hnf : V.settle.isFull = false) :
    b.message.body.parent_execution_requests = Gloas.ExecutionRequests.empty ∧
      blockBuilderDeposits b = [] ∧ blockBuilderExits b = [] := by
  have hE : b.message.body.parent_execution_requests = Gloas.ExecutionRequests.empty := by
    rcases V.settle_cases with ⟨_, _, _, _, _, _, _, hs⟩ | ⟨_, _, hr, _, _⟩ | ⟨_, hr, _, _⟩
    · rw [hs] at hnf; cases hnf
    · exact hr
    · exact hr
  refine ⟨hE, ?_, ?_⟩
  · simp only [blockBuilderDeposits, hE]; rfl
  · simp only [blockBuilderExits, hE]; rfl

/-- **B6 per step, end side.** After the step the joint state holds only the block's own payload:
`.withheld`, or `.delivered` with the block's own envelope, verified against the post-block state
and the chain after the settlement. -/
theorem GStepView.postParent_cases
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent) :
    (env? = none ∧ postParent = .withheld) ∨
      ∃ e req postE, env? = some e ∧ verifyEnvelopeG cfg ccfg bls postB postExec e = .ok (req, postE) ∧
        postParent = .delivered e req postE :=
  V.stepEnd

/-! ## The parent settlement inside `process_block`, through the traces -/

/-- At a FULL step, the parent settlement inside `process_block` (at `postSlots`) factors through
the two traces read at `postSlots`. -/
theorem GStepView.traces
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent) :
    ∃ trD trE, builderDepositTrace ccfg bls V.postSlots b = .ok trD ∧
      builderExitTrace ccfg bls V.postSlots b = .ok trE ∧ trE[0]? = trD.getLast? := by
  obtain ⟨s1, h1⟩ := processBlock_parent V.processBlock
  obtain ⟨trD, trE, hd, he, h0, -⟩ := processParentExecutionPayload_traces (b := b) h1
  exact ⟨trD, trE, hd, he, h0⟩

end View

/-! ## B2/B4: each builder request, at its mid-list state -/

section Requests

variable {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
  {preB : Gloas.BeaconState P} {preExec : BlockChain} {preParent : ParentPayload P}
  {b : Gloas.SignedBeaconBlock P} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
  {postB : Gloas.BeaconState P} {postExec : BlockChain} {postParent : ParentPayload P}

/-- A block with a builder request settles FULL over a delivered payload. -/
theorem GStepView.full_of_requests
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    (hne : blockBuilderDeposits b ≠ [] ∨ blockBuilderExits b ≠ []) :
    ∃ env req post, V.settle = .full env req post := by
  cases hs : V.settle with
  | full env req post => exact ⟨env, req, post, rfl⟩
  | empty =>
    have := V.requests_of_not_full (by rw [hs]; rfl)
    rcases hne with h | h
    · exact absurd this.2.1 h
    · exact absurd this.2.2 h
  | landed =>
    have := V.requests_of_not_full (by rw [hs]; rfl)
    rcases hne with h | h
    · exact absurd this.2.1 h
    · exact absurd this.2.2 h

/-- **B2 consensus half, per step.** The builder deposit request at position `k` of the block's
`parent_execution_requests` (the delivered parent payload's, by value) is applied at deposit trace
position `k` of the trace read at the post-slots state: it has exactly one classification
outcome at `tr[k]`, and `tr[k+1]` is that outcome's effect. The step settles FULL over the
delivered payload `env`, and its built-upon chain is the payload's `post`. -/
theorem GStepView.builderDeposit_applied
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    {k : Nat} {r : Gloas.BuilderDepositRequest} (hr : (blockBuilderDeposits b)[k]? = some r) :
    ∃ (env : Gloas.SignedExecutionPayloadEnvelope P) (req : Gloas.NewPayloadRequest P)
      (post : BlockChain) (tr : List (Gloas.BeaconState P)) (m m' : Gloas.BeaconState P)
      (o : BuilderDepositOutcome),
      V.settle = .full env req post ∧ preParent = .delivered env req post ∧
      b.message.body.parent_execution_requests = env.message.execution_requests ∧
      postExec = post ∧
      (env.message.execution_requests.builder_deposits.toArray.toList)[k]? = some r ∧
      builderDepositTrace ccfg bls V.postSlots b = .ok tr ∧ tr[k]? = some m ∧
      classifyBuilderDeposit ccfg bls m r = .ok o ∧
      (∀ o', classifyBuilderDeposit ccfg bls m r = .ok o' → o' = o) ∧
      tr[k + 1]? = some m' ∧ applyBuilderDepositOutcome ccfg m r o = .ok m' := by
  obtain ⟨env, req, post, hs⟩ := V.full_of_requests (Or.inl (by
    intro h; rw [h] at hr; simp at hr))
  obtain ⟨-, hp, hreq, he⟩ := V.full_iff.mp hs
  obtain ⟨tr, -, htr, -, -⟩ := V.traces
  obtain ⟨m, m', hm, hm', hstep⟩ := builderDepositTrace_step htr hr
  rw [processBuilderDepositRequest_eq] at hstep
  obtain ⟨o, hc, ha⟩ := bind_eq_ok_iff.mp hstep
  refine ⟨env, req, post, tr, m, m', o, hs, hp, hreq, he, ?_, htr, hm, hc,
    fun o' h' => by rw [hc] at h'; cases h'; rfl, hm', ha⟩
  rw [← hreq]; exact hr

/-- **B4 consensus half, per step.** The builder exit request at position `k` is applied at exit
trace position `k` of the trace read at the post-slots state, with exactly one classification
outcome; the step settles FULL over the delivered payload `env`. -/
theorem GStepView.builderExit_applied
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    {k : Nat} {r : Gloas.BuilderExitRequest} (hr : (blockBuilderExits b)[k]? = some r) :
    ∃ (env : Gloas.SignedExecutionPayloadEnvelope P) (req : Gloas.NewPayloadRequest P)
      (post : BlockChain) (tr : List (Gloas.BeaconState P)) (m m' : Gloas.BeaconState P)
      (o : BuilderExitOutcome),
      V.settle = .full env req post ∧ preParent = .delivered env req post ∧
      b.message.body.parent_execution_requests = env.message.execution_requests ∧
      postExec = post ∧
      (env.message.execution_requests.builder_exits.toArray.toList)[k]? = some r ∧
      builderExitTrace ccfg bls V.postSlots b = .ok tr ∧ tr[k]? = some m ∧
      classifyBuilderExit ccfg m r = .ok o ∧
      (∀ o', classifyBuilderExit ccfg m r = .ok o' → o' = o) ∧
      tr[k + 1]? = some m' ∧ applyBuilderExitOutcome ccfg m r o = .ok m' := by
  obtain ⟨env, req, post, hs⟩ := V.full_of_requests (Or.inr (by
    intro h; rw [h] at hr; simp at hr))
  obtain ⟨-, hp, hreq, he⟩ := V.full_iff.mp hs
  obtain ⟨-, tr, -, htr, -⟩ := V.traces
  obtain ⟨m, m', hm, hm', hstep⟩ := builderExitTrace_step htr hr
  rw [processBuilderExitRequest_eq] at hstep
  obtain ⟨o, hc, ha⟩ := bind_eq_ok_iff.mp hstep
  refine ⟨env, req, post, tr, m, m', o, hs, hp, hreq, he, ?_, htr, hm, hc,
    fun o' h' => by rw [hc] at h'; cases h'; rfl, hm', ha⟩
  rw [← hreq]; exact hr

/-- **B2 headline, per step.** Over the raw step hypothesis: the deposit request at position `k`
of the block is applied at deposit trace position `k` of the trace read at the post-slots state,
with one outcome, by a step whose settlement is FULL over the delivered payload `env`. -/
theorem gloasStep_builderDeposit_applied
    (h : jointStepG cfg ccfg bls (.gloas preB preExec preParent) (.gloas b) env? =
      .ok (.gloas postB postExec postParent))
    {k : Nat} {r : Gloas.BuilderDepositRequest} (hr : (blockBuilderDeposits b)[k]? = some r) :
    ∃ (postSlots : Gloas.BeaconState P) (env : Gloas.SignedExecutionPayloadEnvelope P)
      (req : Gloas.NewPayloadRequest P) (post : BlockChain) (tr : List (Gloas.BeaconState P))
      (m m' : Gloas.BeaconState P) (o : BuilderDepositOutcome),
      Gloas.processSlots (gloasCtx ccfg bls) preB b.message.slot = .ok postSlots ∧
      settleParent preParent preExec (parentFull postSlots b.message)
        b.message.body.parent_execution_requests = .ok (postExec, .full env req post) ∧
      preParent = .delivered env req post ∧
      b.message.body.parent_execution_requests = env.message.execution_requests ∧
      postExec = post ∧
      builderDepositTrace ccfg bls postSlots b = .ok tr ∧ tr[k]? = some m ∧
      classifyBuilderDeposit ccfg bls m r = .ok o ∧
      (∀ o', classifyBuilderDeposit ccfg bls m r = .ok o' → o' = o) ∧
      tr[k + 1]? = some m' ∧ applyBuilderDepositOutcome ccfg m r o = .ok m' := by
  obtain ⟨V⟩ := gloasStep_view h
  obtain ⟨env, req, post, tr, m, m', o, hs, hp, hreq, he, -, htr, hm, hc, hu, hm', ha⟩ :=
    V.builderDeposit_applied hr
  exact ⟨V.postSlots, env, req, post, tr, m, m', o, V.slots, hs ▸ V.settled, hp, hreq, he, htr, hm,
    hc, hu, hm', ha⟩

/-- **B4 headline, per step.** As `gloasStep_builderDeposit_applied`, for builder exits. -/
theorem gloasStep_builderExit_applied
    (h : jointStepG cfg ccfg bls (.gloas preB preExec preParent) (.gloas b) env? =
      .ok (.gloas postB postExec postParent))
    {k : Nat} {r : Gloas.BuilderExitRequest} (hr : (blockBuilderExits b)[k]? = some r) :
    ∃ (postSlots : Gloas.BeaconState P) (env : Gloas.SignedExecutionPayloadEnvelope P)
      (req : Gloas.NewPayloadRequest P) (post : BlockChain) (tr : List (Gloas.BeaconState P))
      (m m' : Gloas.BeaconState P) (o : BuilderExitOutcome),
      Gloas.processSlots (gloasCtx ccfg bls) preB b.message.slot = .ok postSlots ∧
      settleParent preParent preExec (parentFull postSlots b.message)
        b.message.body.parent_execution_requests = .ok (postExec, .full env req post) ∧
      preParent = .delivered env req post ∧
      b.message.body.parent_execution_requests = env.message.execution_requests ∧
      postExec = post ∧
      builderExitTrace ccfg bls postSlots b = .ok tr ∧ tr[k]? = some m ∧
      classifyBuilderExit ccfg m r = .ok o ∧
      (∀ o', classifyBuilderExit ccfg m r = .ok o' → o' = o) ∧
      tr[k + 1]? = some m' ∧ applyBuilderExitOutcome ccfg m r o = .ok m' := by
  obtain ⟨V⟩ := gloasStep_view h
  obtain ⟨env, req, post, tr, m, m', o, hs, hp, hreq, he, -, htr, hm, hc, hu, hm', ha⟩ :=
    V.builderExit_applied hr
  exact ⟨V.postSlots, env, req, post, tr, m, m', o, V.slots, hs ▸ V.settled, hp, hreq, he, htr, hm,
    hc, hu, hm', ha⟩

/-- **Non-FULL headline, per step.** A settlement that is not FULL (EMPTY, or `.landed`) applies
no builder request: the block's requests are empty by value (at a step, take the view's
`postSlots`/`settle`, `GStepView.requests_of_not_full`). -/
theorem settleParent_no_requests_of_not_full
    {postSlots : Gloas.BeaconState P} {o : ParentSettle P}
    (hs : settleParent preParent preExec (parentFull postSlots b.message)
      b.message.body.parent_execution_requests = .ok (postExec, o))
    (hnf : o.isFull = false) :
    b.message.body.parent_execution_requests = Gloas.ExecutionRequests.empty ∧
      blockBuilderDeposits b = [] ∧ blockBuilderExits b = [] := by
  have hE : b.message.body.parent_execution_requests = Gloas.ExecutionRequests.empty := by
    rcases settleParent_ok_iff.mp hs with ⟨_, _, _, _, _, _, _, rfl⟩ | ⟨_, _, hr, _, _⟩ |
        ⟨_, hr, _, _⟩
    · cases hnf
    · exact hr
    · exact hr
  refine ⟨hE, ?_, ?_⟩
  · simp only [blockBuilderDeposits, hE]; rfl
  · simp only [blockBuilderExits, hE]; rfl

end Requests

/-! ## B6 control (i): applying the requests at delivery -/

/-- The mutant of `settleParent` that treats a delivered payload's requests as already applied at
delivery (statements.md §0.3, B6 (i)): FULL over `.delivered` then requires the child to carry
empty requests, like a `.landed` parent. -/
def settleParent' (parent : ParentPayload P) (exec : BlockChain) (full : Bool)
    (childRequests : Gloas.ExecutionRequests) :
    Except SettleReject (BlockChain × ParentSettle P) :=
  if full then
    match parent with
    | .delivered _ _ post =>
      if childRequests = Gloas.ExecutionRequests.empty then .ok (post, .landed)
      else .error .requestsMismatch
    | .landed =>
      if childRequests = Gloas.ExecutionRequests.empty then .ok (exec, .landed)
      else .error .landedRequestsNonEmpty
    | .withheld => .error .fullOfWithheld
  else
    if childRequests = Gloas.ExecutionRequests.empty then .ok (exec, .empty)
    else .error .emptyRequestsNonEmpty

/-- The real settlement applies a delivered payload's requests at the settling step: the child
carrying them is accepted, as a FULL settlement of that payload. -/
theorem settleParent_applies_at_settle {exec : BlockChain}
    {env : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P}
    {post : BlockChain} :
    settleParent (.delivered env req post) exec true env.message.execution_requests =
      .ok (post, .full env req post) := by
  simp [settleParent]

/-- The mutant refuses, at the settling step, the child that carries a delivered payload's
(non-empty) requests: under it the requests would not be applied at the settling step. -/
theorem settleParent'_refuses_at_settle {exec : BlockChain}
    {env : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P}
    {post : BlockChain} (hne : env.message.execution_requests ≠ Gloas.ExecutionRequests.empty) :
    settleParent' (.delivered env req post) exec true env.message.execution_requests =
      .error .requestsMismatch := by
  simp [settleParent', hne]

/-- The mutant accepts the empty child of a delivered payload with requests (applying nothing at
the settling step), which the real settlement refuses. -/
theorem settleParent'_accepts_empty {exec : BlockChain}
    {env : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P}
    {post : BlockChain} (hne : env.message.execution_requests ≠ Gloas.ExecutionRequests.empty) :
    settleParent' (.delivered env req post) exec true Gloas.ExecutionRequests.empty =
      .ok (post, .landed) ∧
    settleParent (.delivered env req post) exec true Gloas.ExecutionRequests.empty =
      .error .requestsMismatch := by
  refine ⟨by simp [settleParent'], ?_⟩
  exact settleParent_refuses_other_requests (Ne.symm hne)

end JauneConsensus.Facts.Gloas
