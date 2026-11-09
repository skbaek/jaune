import JauneConsensus.JointGloas
import JauneConsensus.Facts.Gloas.BuilderAuth
import JauneConsensus.Facts.Joint

/-!
# Facts about the Gloas side of the joint step (goal `eip8282-gloas-cross-layer-v1`, G2)

* `engineVerdictG_ok_iff`: the Gloas engine accepts exactly when each check passes, in the
  definition's order (the `engineVerdict_ok_iff` shape), and `consensusFork?_eq_gloas_iff` says
  the only execution fork paired with Gloas is Amsterdam.
* `verifyEnvelopeG_ok_iff`: the envelope seam succeeds exactly when U6's named conjuncts
  (`EnvelopeChecksB`) hold with the engine `envelopeEngine`, the withdrawals match as lists, and
  the engine's verdict on the request is the returned chain; `deliver_ok_iff` lifts it to the
  envelope arm. `verifyEnvelopeG_engine_calls_agree` says the check's `Bool` engine call and the
  second call are on the same request and agree; `verifyEnvelopeG_requests` says the body run
  produced exactly the envelope's requests as a list.
* Rejections: withdrawals root (U6's `…B_rejects_of_withdrawalsRoot_ne`), withdrawals as lists,
  requests root (U6's `…B_rejects_of_requestsRoot_ne`), and a second envelope.
* BLS: `verifyExecutionPayloadEnvelopeB_bls_indep` (and its `verifyEnvelopeG`/`deliver` lifts):
  when the signature verifies, the switch makes no difference.
* `settleParent_ok_iff` and the two refusals; `processParentExecutionPayload_ok_iff` shows the
  beacon-side settlement inside Gloas `processBlock` branches on the same `parentFull` test.
* `gloasBlockArm_ok_iff`, `gloasDeliverOpt_ok_iff` (`gloasDeliverOpt_some`: the step hands
  `deliver` the `.withheld` state, the only one `deliver_ok_iff` accepts), `gloasStepWith_ok_iff`
  and its `none`/`some` forms, and `gloasBlockArm_refuses_full_of_withheld`.
* U5's instance: `gloasStep_ok_iff` names the post-slots state `postSlots` (the state Gloas
  `process_block` receives, `gloasBlockTransition_processBlock`, where the BF1 traces are read);
  `processSlots_then_gloasBlockTransition` is `Gloas.stateTransition`.
* `jointStepG`: `jointStepG_pre_ok_iff`, `jointStepG_cross_ok_iff`, `jointStepG_gloas_ok_iff`,
  and the refusals `jointStepG_refuses_*` / `jointStepG_cross_refuses_*`.
* The crossing's builders: `upgradeToGloas_builders` (every builder at `FAR_FUTURE_EPOCH`, no
  pending builder withdrawal, read off `onboard_builders_from_pending_deposits`) and
  `jointStepG_crossing_builders`.
-/

namespace JauneConsensus

open Jaune

variable {P : Preset}

/-! ## Small lemmas -/

/-- A `guardE` followed by a continuation succeeds iff the condition holds and the
continuation succeeds. -/
theorem guardE_bind_ok_iff {ε β : Type} {c : Bool} {e : ε} {k : Unit → Except ε β} {b : β} :
    (guardE c e >>= k) = .ok b ↔ c = true ∧ k () = .ok b := by
  cases c <;> simp [guardE, bind, Except.bind]

/-- The transition verdict is `.ok post` iff the configured transition succeeded with `post`. -/
theorem transitionVerdict_ok_iff {r : Except RulesLookupError (Except TransitionError BlockChain)}
    {post : BlockChain} : transitionVerdict r = .ok post ↔ r = .ok (.ok post) := by
  rcases r with e | e | p <;> simp [transitionVerdict]

/-- A `guardE` succeeds iff its condition holds. -/
theorem guardE_eq_ok_iff {ε : Type} {c : Bool} {e : ε} {u : Unit} :
    guardE c e = .ok u ↔ c = true := by
  cases c <;> simp [guardE]

private theorem pure_eq_ok_iff {ε α : Type} {a b : α} :
    (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

private theorem unit_exists_iff {p : Unit → Prop} : (∃ u : Unit, p u) ↔ p () :=
  ⟨fun ⟨(), h⟩ => h, fun h => ⟨(), h⟩⟩

private theorem require_ok_iff {c : Bool} {site : String} {u : Unit} :
    require c site = .ok u ↔ c = true := by
  cases c
  · simp [require]
  · exact iff_of_true rfl rfl

/-- The only execution fork paired with Gloas is Amsterdam. -/
theorem consensusFork?_eq_gloas_iff {f : Jaune.Fork} :
    f.consensusFork? = some .gloas ↔ f = .amsterdam := by
  cases f <;> simp [Jaune.Fork.consensusFork?]

/-! ## The engine -/

/-- The Gloas engine accepts a payload exactly when every check passes, in the definition's
order. -/
theorem engineVerdictG_ok_iff {cfg : ChainConfig} {exec : BlockChain}
    {req : Gloas.NewPayloadRequest P} {post : BlockChain} :
    engineVerdictG cfg exec req = .ok post ↔
      req.execution_payload.txBytes.any List.isEmpty = false ∧
      (payloadToBlockG req).header.hash = req.execution_payload.block_hash ∧
      blobVersionedHashesOf req.execution_payload.txBytes =
        .ok req.versioned_hashes.toArray.toList ∧
      cfg.checkChainId exec = .ok () ∧
      ∃ f, cfg.forkAt (payloadToBlockG req).header.number
            (payloadToBlockG req).header.timestamp = .ok f ∧
        f.consensusFork? = some .gloas ∧
        checkBlockRlpSize f.ruleSet.block (payloadToBlockG req).toBLT.toBytes.length = .ok () ∧
        stateTransitionScheduledE cfg f exec (payloadToBlockG req) = .ok (.ok post) ∧
        ∃ st bout, applyBody (initBenv f exec (payloadToBlockG req).header)
            (payloadToBlockG req).txs (payloadToBlockG req).ommers (payloadToBlockG req).wds =
            .ok (st, bout) ∧
          bout.requests = Gloas.getExecutionRequestsList req.execution_requests ∧
          req.execution_payload.balBytes = bout.blockAccessList.encode := by
  unfold engineVerdictG
  simp only [Except.bind_eq_ok_iff, guardE_eq_ok_iff, Except.mapError_eq_ok_iff,
    transitionVerdict_ok_iff, decide_eq_true_eq, pure_eq_ok_iff, Prod.exists, unit_exists_iff,
    Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2, _, hb, rfl, hc, f, hf, hp, hs, _, ht, st, bout, hbody, hr, hbal, rfl⟩
    exact ⟨h1, h2, hb, hc, f, hf, hp, hs, ht, st, bout, hbody, hr, hbal⟩
  · rintro ⟨h1, h2, hb, hc, f, hf, hp, hs, ht, st, bout, hbody, hr, hbal⟩
    exact ⟨h1, h2, _, hb, rfl, hc, f, hf, hp, hs, _, ht, st, bout, hbody, hr, hbal, rfl⟩

/-- An accepted Gloas payload runs on Amsterdam, and its body run produces the request's
requests, as the list `get_execution_requests_list`, and the payload's block access list. -/
theorem engineVerdictG_requests {cfg : ChainConfig} {exec : BlockChain}
    {req : Gloas.NewPayloadRequest P} {post : BlockChain}
    (h : engineVerdictG cfg exec req = .ok post) :
    ∃ st bout, applyBody (initBenv .amsterdam exec (payloadToBlockG req).header)
        (payloadToBlockG req).txs (payloadToBlockG req).ommers (payloadToBlockG req).wds =
        .ok (st, bout) ∧
      bout.requests = Gloas.getExecutionRequestsList req.execution_requests ∧
      req.execution_payload.balBytes = bout.blockAccessList.encode := by
  obtain ⟨_, _, _, _, f, _, hpair, _, _, st, bout, hbody, hr, hbal⟩ :=
    engineVerdictG_ok_iff.mp h
  rw [consensusFork?_eq_gloas_iff] at hpair
  subst hpair
  exact ⟨st, bout, hbody, hr, hbal⟩

/-- The `Bool` engine U6's check calls accepts exactly when the verdict is a chain. -/
theorem envelopeEngine_eq_true_iff {cfg : ChainConfig} {exec : BlockChain}
    {req : Gloas.NewPayloadRequest P} :
    envelopeEngine cfg exec req = true ↔ ∃ post, engineVerdictG cfg exec req = .ok post := by
  unfold envelopeEngine
  cases engineVerdictG cfg exec req <;> simp [Except.isOk, Except.toBool]

/-! ## The envelope seam -/

/-- The request `envelopeNewPayloadRequest` builds carries the envelope's requests. -/
theorem envelopeNewPayloadRequest_execution_requests {state : Gloas.BeaconState P}
    {e : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P}
    (h : Gloas.envelopeNewPayloadRequest state e = .ok req) :
    req.execution_requests = e.message.execution_requests := by
  unfold Gloas.envelopeNewPayloadRequest at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases h
  rfl

/-- The seam succeeds exactly when U6's named conjuncts hold with the engine
`envelopeEngine cfg exec`, the withdrawals match as lists, the request is the envelope's, and
the engine's verdict on it is the returned chain. -/
theorem verifyEnvelopeG_ok_iff {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {state : Gloas.BeaconState P} {exec : BlockChain} {e : Gloas.SignedExecutionPayloadEnvelope P}
    {req : Gloas.NewPayloadRequest P} {post : BlockChain} :
    verifyEnvelopeG cfg ccfg bls state exec e = .ok (req, post) ↔
      Gloas.EnvelopeChecksB bls ccfg (envelopeEngine cfg exec) state e ∧
      Gloas.WithdrawalsMatchExpected state e ∧
      Gloas.envelopeNewPayloadRequest state e = .ok req ∧
      engineVerdictG cfg exec req = .ok post := by
  constructor
  · intro h
    unfold verifyEnvelopeG at h
    obtain ⟨u, hv, h⟩ := Except.bind_eq_ok h
    obtain ⟨u2, hw, h⟩ := Except.bind_eq_ok h
    obtain ⟨r, hr, h⟩ := Except.bind_eq_ok h
    cases u
    have hw' : Gloas.WithdrawalsMatchExpected state e := of_decide_eq_true (require_ok_iff.mp hw)
    cases he : engineVerdictG cfg exec r with
    | error x =>
      rw [he] at h
      cases h
    | ok p =>
      rw [he] at h
      cases h
      exact ⟨Gloas.verifyExecutionPayloadEnvelopeB_ok_iff.mp hv, hw', hr, he⟩
  · rintro ⟨hc, hw, hr, he⟩
    unfold verifyEnvelopeG
    rw [Gloas.verifyExecutionPayloadEnvelopeB_ok_iff.mpr hc]
    simp only [require, decide_eq_true hw, hr, he, ite_true, bind, Except.bind, pure, Except.pure]

/-- The two engine calls agree: the request the check hands its `Bool` engine is the request the
second call runs, the `Bool` call accepted it, and the second call's chain is `post`. -/
theorem verifyEnvelopeG_engine_calls_agree {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {state : Gloas.BeaconState P} {exec : BlockChain} {e : Gloas.SignedExecutionPayloadEnvelope P}
    {req : Gloas.NewPayloadRequest P} {post : BlockChain}
    (h : verifyEnvelopeG cfg ccfg bls state exec e = .ok (req, post))
    {r : Gloas.NewPayloadRequest P} (hr : Gloas.envelopeNewPayloadRequest state e = .ok r) :
    r = req ∧ envelopeEngine cfg exec r = true ∧ engineVerdictG cfg exec r = .ok post := by
  obtain ⟨hc, _, hreq, he⟩ := verifyEnvelopeG_ok_iff.mp h
  have hrr : r = req := by
    rw [hr] at hreq
    cases hreq
    rfl
  subst hrr
  obtain ⟨r', hr', hb⟩ := hc.engine
  rw [hr] at hr'
  cases hr'
  exact ⟨rfl, hb, he⟩

/-- On an accepted envelope the request is the envelope's, and the body run on Amsterdam
produced the envelope's requests as the list `get_execution_requests_list`. -/
theorem verifyEnvelopeG_requests {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {state : Gloas.BeaconState P} {exec : BlockChain} {e : Gloas.SignedExecutionPayloadEnvelope P}
    {req : Gloas.NewPayloadRequest P} {post : BlockChain}
    (h : verifyEnvelopeG cfg ccfg bls state exec e = .ok (req, post)) :
    req.execution_requests = e.message.execution_requests ∧
      ∃ st bout, applyBody (initBenv .amsterdam exec (payloadToBlockG req).header)
          (payloadToBlockG req).txs (payloadToBlockG req).ommers (payloadToBlockG req).wds =
          .ok (st, bout) ∧
        bout.requests = Gloas.getExecutionRequestsList e.message.execution_requests := by
  obtain ⟨_, _, hreq, he⟩ := verifyEnvelopeG_ok_iff.mp h
  have hx := envelopeNewPayloadRequest_execution_requests hreq
  obtain ⟨st, bout, hbody, hr, _⟩ := engineVerdictG_requests he
  exact ⟨hx, st, bout, hbody, hx ▸ hr⟩

/-- An envelope whose withdrawals root differs from `payload_expected_withdrawals`' is rejected
(U6's root-form rejection). -/
theorem verifyEnvelopeG_rejects_of_withdrawalsRoot_ne {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {state : Gloas.BeaconState P} {exec : BlockChain}
    {e : Gloas.SignedExecutionPayloadEnvelope P}
    (hne : Ssz.hashTreeRoot e.message.payload.withdrawals ≠
      Ssz.hashTreeRoot state.payload_expected_withdrawals)
    (r : Gloas.NewPayloadRequest P × BlockChain) :
    verifyEnvelopeG cfg ccfg bls state exec e ≠ .ok r := fun h =>
  Gloas.verifyExecutionPayloadEnvelopeB_rejects_of_withdrawalsRoot_ne hne
    (Gloas.verifyExecutionPayloadEnvelopeB_ok_iff.mpr (verifyEnvelopeG_ok_iff.mp h).1)

/-- An envelope whose withdrawals differ, as lists, from `payload_expected_withdrawals` is
rejected (the list form, with no hash). -/
theorem verifyEnvelopeG_rejects_of_withdrawals_ne {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {state : Gloas.BeaconState P} {exec : BlockChain}
    {e : Gloas.SignedExecutionPayloadEnvelope P}
    (hne : ¬ Gloas.WithdrawalsMatchExpected state e)
    (r : Gloas.NewPayloadRequest P × BlockChain) :
    verifyEnvelopeG cfg ccfg bls state exec e ≠ .ok r := fun h =>
  hne (verifyEnvelopeG_ok_iff.mp h).2.1

/-- An envelope whose requests root differs from the committed bid's is rejected (U6's
rejection). -/
theorem verifyEnvelopeG_rejects_of_requestsRoot_ne {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {state : Gloas.BeaconState P} {exec : BlockChain}
    {e : Gloas.SignedExecutionPayloadEnvelope P}
    (hne : Ssz.hashTreeRoot e.message.execution_requests ≠
      state.latest_execution_payload_bid.execution_requests_root)
    (r : Gloas.NewPayloadRequest P × BlockChain) :
    verifyEnvelopeG cfg ccfg bls state exec e ≠ .ok r := fun h =>
  Gloas.verifyExecutionPayloadEnvelopeB_rejects_of_requestsRoot_ne hne
    (Gloas.verifyExecutionPayloadEnvelopeB_ok_iff.mpr (verifyEnvelopeG_ok_iff.mp h).1)

/-! ## The BLS switch -/

/-- When the envelope signature verifies with real BLS, U6's check is the same function of the
rest under either setting of the switch. -/
theorem verifyExecutionPayloadEnvelopeB_bls_indep {bls : Bool} {cfg : Config}
    {engine : Gloas.NewPayloadRequest P → Bool} {state : Gloas.BeaconState P}
    {e : Gloas.SignedExecutionPayloadEnvelope P}
    (hsig : Gloas.verifyExecutionPayloadEnvelopeSignatureB true state e = .ok true) :
    Gloas.verifyExecutionPayloadEnvelopeB bls cfg engine state e =
      Gloas.verifyExecutionPayloadEnvelopeB true cfg engine state e := by
  cases bls
  · have hlook : ∃ pk d, Gloas.builderSigningPubkey state e.message.builder_index = .ok pk ∧
        Gloas.getDomain state Gloas.DOMAIN_BEACON_BUILDER = .ok d := by
      unfold Gloas.verifyExecutionPayloadEnvelopeSignatureB at hsig
      obtain ⟨pk, hpk, h⟩ := Except.bind_eq_ok hsig
      obtain ⟨d, hd, _⟩ := Except.bind_eq_ok h
      exact ⟨pk, d, hpk, hd⟩
    obtain ⟨pk, d, hpk, hd⟩ := hlook
    have hf := Gloas.verifyExecutionPayloadEnvelopeSignatureB_false hpk hd
    unfold Gloas.verifyExecutionPayloadEnvelopeB
    rw [hf, hsig]
  · rfl

/-- `verifyEnvelopeG` does not depend on the switch when the signature verifies. -/
theorem verifyEnvelopeG_bls_indep {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {state : Gloas.BeaconState P} {exec : BlockChain} {e : Gloas.SignedExecutionPayloadEnvelope P}
    (hsig : Gloas.verifyExecutionPayloadEnvelopeSignatureB true state e = .ok true) :
    verifyEnvelopeG cfg ccfg bls state exec e = verifyEnvelopeG cfg ccfg true state exec e := by
  unfold verifyEnvelopeG
  rw [verifyExecutionPayloadEnvelopeB_bls_indep hsig]

/-! ## The envelope arm -/

/-- The envelope arm succeeds exactly on a Gloas state whose latest block's payload is
`.withheld`, when the seam accepts; it records the envelope, the request and the engine's chain,
and moves nothing else. -/
theorem deliver_ok_iff {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s s' : GJointState P}
    {e : Gloas.SignedExecutionPayloadEnvelope P} :
    deliver cfg ccfg bls s e = .ok s' ↔
      ∃ beacon exec req post, s = .gloas beacon exec .withheld ∧
        verifyEnvelopeG cfg ccfg bls beacon exec e = .ok (req, post) ∧
        s' = .gloas beacon exec (.delivered e req post) := by
  cases s with
  | pre j =>
    simp only [deliver, reduceCtorEq, false_and, exists_false]
  | gloas beacon exec parent =>
    cases parent with
    | withheld =>
      constructor
      · intro h
        unfold deliver at h
        obtain ⟨⟨req, post⟩, hv, h⟩ := Except.bind_eq_ok h
        cases h
        exact ⟨beacon, exec, req, post, rfl, hv, rfl⟩
      · rintro ⟨b, x, req, post, hs, hv, rfl⟩
        cases hs
        unfold deliver
        simp only [hv, bind, Except.bind, pure, Except.pure]
    | landed =>
      simp only [deliver, reduceCtorEq, GJointState.gloas.injEq, false_and, and_false,
        exists_false]
    | delivered env req post =>
      simp only [deliver, reduceCtorEq, GJointState.gloas.injEq, false_and, and_false,
        exists_false]

/-- A second envelope for the same block is refused. -/
theorem deliver_refuses_delivered {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain}
    {env e : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P}
    {post : BlockChain} (s' : GJointState P) :
    deliver cfg ccfg bls (.gloas beacon exec (.delivered env req post)) e ≠ .ok s' := by
  intro h
  obtain ⟨_, _, _, _, hs, _, _⟩ := deliver_ok_iff.mp h
  cases hs

/-- An envelope for a `.landed` parent (the state `upgrade_to_gloas` leaves, whose payload is
already the head) is refused. -/
theorem deliver_refuses_landed {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain}
    {e : Gloas.SignedExecutionPayloadEnvelope P} (s' : GJointState P) :
    deliver cfg ccfg bls (.gloas beacon exec .landed) e ≠ .ok s' := by
  intro h
  obtain ⟨_, _, _, _, hs, _, _⟩ := deliver_ok_iff.mp h
  cases hs

/-- The envelope arm rejects withdrawals that differ, as lists, from the expected ones. -/
theorem deliver_rejects_of_withdrawals_ne {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain} {parent : ParentPayload P}
    {e : Gloas.SignedExecutionPayloadEnvelope P}
    (hne : ¬ Gloas.WithdrawalsMatchExpected beacon e) (s' : GJointState P) :
    deliver cfg ccfg bls (.gloas beacon exec parent) e ≠ .ok s' := by
  intro h
  obtain ⟨_, _, _, _, hs, hv, _⟩ := deliver_ok_iff.mp h
  cases hs
  exact verifyEnvelopeG_rejects_of_withdrawals_ne hne _ hv

/-- The envelope arm rejects a withdrawals root that differs from the expected one (U6). -/
theorem deliver_rejects_of_withdrawalsRoot_ne {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain} {parent : ParentPayload P}
    {e : Gloas.SignedExecutionPayloadEnvelope P}
    (hne : Ssz.hashTreeRoot e.message.payload.withdrawals ≠
      Ssz.hashTreeRoot beacon.payload_expected_withdrawals) (s' : GJointState P) :
    deliver cfg ccfg bls (.gloas beacon exec parent) e ≠ .ok s' := by
  intro h
  obtain ⟨_, _, _, _, hs, hv, _⟩ := deliver_ok_iff.mp h
  cases hs
  exact verifyEnvelopeG_rejects_of_withdrawalsRoot_ne hne _ hv

/-- The envelope arm rejects requests whose root is not the committed bid's (U6). -/
theorem deliver_rejects_of_requestsRoot_ne {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain} {parent : ParentPayload P}
    {e : Gloas.SignedExecutionPayloadEnvelope P}
    (hne : Ssz.hashTreeRoot e.message.execution_requests ≠
      beacon.latest_execution_payload_bid.execution_requests_root) (s' : GJointState P) :
    deliver cfg ccfg bls (.gloas beacon exec parent) e ≠ .ok s' := by
  intro h
  obtain ⟨_, _, _, _, hs, hv, _⟩ := deliver_ok_iff.mp h
  cases hs
  exact verifyEnvelopeG_rejects_of_requestsRoot_ne hne _ hv

/-- The envelope arm does not depend on the switch when the signature verifies. -/
theorem deliver_bls_indep {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain} {parent : ParentPayload P}
    {e : Gloas.SignedExecutionPayloadEnvelope P}
    (hsig : Gloas.verifyExecutionPayloadEnvelopeSignatureB true beacon e = .ok true) :
    deliver cfg ccfg bls (.gloas beacon exec parent) e =
      deliver cfg ccfg true (.gloas beacon exec parent) e := by
  cases parent <;> simp only [deliver, verifyEnvelopeG_bls_indep hsig]

/-! ## Parent settlement -/

/-- Requests are determined by their five lists. -/
theorem ExecutionRequests.lists_eq_lists_iff {r r' : Gloas.ExecutionRequests} :
    r.lists = r'.lists ↔ r = r' :=
  ⟨Gloas.ExecutionRequests.eq_of_lists_eq, fun h => h ▸ rfl⟩

/-- Empty lists, by value, are `ExecutionRequests.empty()`. -/
theorem ExecutionRequests.lists_eq_empty_iff {r : Gloas.ExecutionRequests} :
    r.lists = emptyRequestLists ↔ r = Gloas.ExecutionRequests.empty :=
  ExecutionRequests.lists_eq_lists_iff (r' := Gloas.ExecutionRequests.empty)

/-- The settlement succeeds exactly in three cases: FULL over a delivered payload whose requests
the child carries by value (the chain becomes the payload's `post`); FULL over a landed payload
with empty requests by value; EMPTY with empty requests by value (the chain stays). -/
theorem settleParent_ok_iff {parent : ParentPayload P} {exec exec' : BlockChain} {full : Bool}
    {reqs : Gloas.ExecutionRequests} {o : ParentSettle P} :
    settleParent parent exec full reqs = .ok (exec', o) ↔
      (full = true ∧ ∃ env req post, parent = .delivered env req post ∧
          reqs = env.message.execution_requests ∧ exec' = post ∧ o = .full env req post) ∨
      (full = true ∧ parent = .landed ∧ reqs = Gloas.ExecutionRequests.empty ∧
          exec' = exec ∧ o = .landed) ∨
      (full = false ∧ reqs = Gloas.ExecutionRequests.empty ∧ exec' = exec ∧ o = .empty) := by
  constructor
  · intro hs
    cases full <;> cases parent <;> simp only [settleParent, Bool.false_eq_true, ite_true,
      ite_false] at hs <;> (try split at hs) <;> cases hs <;> simp_all
  · rintro (⟨rfl, env, req, post, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩) <;> simp [settleParent]

/-- An EMPTY settlement's by-value check implies the beacon side's
`requests == ExecutionRequests.empty()` (`processParentExecutionPayload`), so wrapping Gloas
`processBlock` never refuses what the settlement accepted on that count. -/
theorem settleParent_empty_beq {parent : ParentPayload P} {exec : BlockChain}
    {reqs : Gloas.ExecutionRequests} {r : BlockChain × ParentSettle P}
    (h : settleParent parent exec false reqs = .ok r) :
    (reqs == Gloas.ExecutionRequests.empty) = true := by
  obtain ⟨exec', o⟩ := r
  rcases settleParent_ok_iff.mp h with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨_, rfl, _⟩
  · cases hf
  · cases hf
  · rfl

/-- FULL settlement of a withheld payload is refused. -/
theorem settleParent_refuses_full_of_withheld {exec : BlockChain}
    {reqs : Gloas.ExecutionRequests} :
    settleParent (P := P) .withheld exec true reqs = .error .fullOfWithheld := rfl

/-- FULL settlement of a delivered payload with any other requests is refused. -/
theorem settleParent_refuses_other_requests {exec : BlockChain}
    {env : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P}
    {post : BlockChain} {reqs : Gloas.ExecutionRequests}
    (hne : reqs ≠ env.message.execution_requests) :
    settleParent (.delivered env req post) exec true reqs = .error .requestsMismatch := by
  simp [settleParent, hne]

/-- The beacon-side settlement inside Gloas `processBlock` branches on `parentFull`: EMPTY
checks the requests are `ExecutionRequests.empty()` and leaves the state; FULL checks the
requests root against the parent bid and applies the requests. -/
theorem processParentExecutionPayload_ok_iff {ctx : Ctx} {state st' : Gloas.BeaconState P}
    {block : Gloas.BeaconBlock P} :
    Gloas.processParentExecutionPayload ctx state block = .ok st' ↔
      (parentFull state block = false ∧
        (block.body.parent_execution_requests == Gloas.ExecutionRequests.empty) = true ∧
        st' = state) ∨
      (parentFull state block = true ∧
        (Ssz.hashTreeRoot block.body.parent_execution_requests ==
          state.latest_execution_payload_bid.execution_requests_root) = true ∧
        Gloas.applyParentExecutionPayload ctx state block.body.parent_execution_requests =
          .ok st') := by
  unfold Gloas.processParentExecutionPayload parentFull
  cases hf : (block.body.signed_execution_payload_bid.message.parent_block_hash ==
      state.latest_execution_payload_bid.block_hash)
  · simp only [bne, hf, Bool.not_false, ite_true, Except.bind_eq_ok_iff, require_ok_iff,
      unit_exists_iff, pure_eq_ok_iff, true_and, Bool.false_eq_true, false_and, or_false]
    exact and_congr_right fun _ => eq_comm
  · simp only [bne, hf, Bool.not_true, Bool.false_eq_true, ite_false, Except.bind_eq_ok_iff,
      require_ok_iff, unit_exists_iff, true_and, Bool.true_eq_false, false_and, false_or]

/-! ## The Gloas block arm -/

/-- The block arm succeeds exactly when `processSlots` reaches the block's slot, the
execution-side settlement at that state succeeds, and the rest of the block transition does. -/
theorem gloasBlockArm_ok_iff
    {processSlots : GloasSlotsFn P} {blockTransition : GloasBlockFn P}
    {beacon post : Gloas.BeaconState P} {exec exec' : BlockChain} {parent : ParentPayload P}
    {b : Gloas.SignedBeaconBlock P} {o : ParentSettle P} :
    gloasBlockArm processSlots blockTransition beacon exec parent b = .ok (post, exec', o) ↔
      ∃ st0, processSlots beacon b.message.slot = .ok st0 ∧
        settleParent parent exec (parentFull st0 b.message)
          b.message.body.parent_execution_requests = .ok (exec', o) ∧
        blockTransition st0 b = .ok post := by
  unfold gloasBlockArm
  simp only [Except.bind_eq_ok_iff, Except.mapError_eq_ok_iff, pure_eq_ok_iff, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨st0, h0, x, o', hs, p, hp, rfl, rfl, rfl⟩
    exact ⟨st0, h0, hs, hp⟩
  · rintro ⟨st0, h0, hs, hp⟩
    exact ⟨st0, h0, exec', o, hs, post, hp, rfl, rfl, rfl⟩

/-- A FULL child of a withheld payload is refused, whatever the block transition does. -/
theorem gloasBlockArm_refuses_full_of_withheld
    {processSlots : GloasSlotsFn P} {blockTransition : GloasBlockFn P}
    {beacon st0 : Gloas.BeaconState P} {exec : BlockChain} {b : Gloas.SignedBeaconBlock P}
    (h0 : processSlots beacon b.message.slot = .ok st0) (hfull : parentFull st0 b.message = true)
    (r : Gloas.BeaconState P × BlockChain × ParentSettle P) :
    gloasBlockArm processSlots blockTransition beacon exec .withheld b ≠ .ok r := by
  obtain ⟨post, exec', o⟩ := r
  rw [Ne, gloasBlockArm_ok_iff]
  rintro ⟨st0', h0', hs, _⟩
  rw [h0] at h0'
  cases h0'
  rw [hfull, settleParent_refuses_full_of_withheld] at hs
  cases hs

/-- The end of a Gloas step: with no envelope the block's payload is `.withheld`; with one, the
envelope is checked against the post-block state and the chain after the settlement, and
recorded as delivered. -/
theorem gloasDeliverOpt_ok_iff {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {post : Gloas.BeaconState P} {exec : BlockChain}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} {s' : GJointState P} :
    gloasDeliverOpt cfg ccfg bls post exec env? = .ok s' ↔
      (env? = none ∧ s' = .gloas post exec .withheld) ∨
      (∃ e req postE, env? = some e ∧ verifyEnvelopeG cfg ccfg bls post exec e = .ok (req, postE) ∧
        s' = .gloas post exec (.delivered e req postE)) := by
  cases env? with
  | none =>
    simp only [gloasDeliverOpt, pure_eq_ok_iff, true_and, reduceCtorEq, false_and,
      exists_false, or_false]
    exact eq_comm
  | some e =>
    simp only [gloasDeliverOpt, deliver_ok_iff, reduceCtorEq, false_and, false_or,
      Option.some.injEq]
    constructor
    · rintro ⟨_, _, req, postE, hs, hv, rfl⟩
      cases hs
      exact ⟨e, req, postE, rfl, hv, rfl⟩
    · rintro ⟨_, req, postE, rfl, hv, rfl⟩
      exact ⟨post, exec, req, postE, rfl, hv, rfl⟩

/-- The step hands `deliver` the `.withheld` state: an envelope is only ever checked for the
block just added, never against a `.landed` or `.delivered` parent. -/
theorem gloasDeliverOpt_some {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {post : Gloas.BeaconState P} {exec : BlockChain} {e : Gloas.SignedExecutionPayloadEnvelope P} :
    gloasDeliverOpt cfg ccfg bls post exec (some e) =
      deliver cfg ccfg bls (.gloas post exec .withheld) e := rfl

/-- The Gloas→Gloas step succeeds exactly when the block arm does and its end does. -/
theorem gloasStepWith_ok_iff
    {processSlots : GloasSlotsFn P} {blockTransition : GloasBlockFn P}
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {beacon : Gloas.BeaconState P}
    {exec : BlockChain} {parent : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} {s' : GJointState P} :
    gloasStepWith processSlots blockTransition cfg ccfg bls beacon exec parent b env? = .ok s' ↔
      ∃ post exec' o,
        gloasBlockArm processSlots blockTransition beacon exec parent b = .ok (post, exec', o) ∧
        gloasDeliverOpt cfg ccfg bls post exec' env? = .ok s' := by
  unfold gloasStepWith
  simp only [Except.bind_eq_ok_iff, Prod.exists]

/-- Without an envelope, the step is the block arm, and the block's payload is withheld. -/
theorem gloasStepWith_none_ok_iff
    {processSlots : GloasSlotsFn P} {blockTransition : GloasBlockFn P}
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {beacon : Gloas.BeaconState P}
    {exec : BlockChain} {parent : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {s' : GJointState P} :
    gloasStepWith processSlots blockTransition cfg ccfg bls beacon exec parent b none = .ok s' ↔
      ∃ post exec' o,
        gloasBlockArm processSlots blockTransition beacon exec parent b = .ok (post, exec', o) ∧
        s' = .gloas post exec' .withheld := by
  simp only [gloasStepWith_ok_iff, gloasDeliverOpt_ok_iff, true_and, reduceCtorEq, false_and,
    exists_false, or_false]

/-- With the block's envelope, the step is the block arm, then the envelope checked against the
post-block state and the chain after the settlement, recorded as delivered. -/
theorem gloasStepWith_some_ok_iff
    {processSlots : GloasSlotsFn P} {blockTransition : GloasBlockFn P}
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {beacon : Gloas.BeaconState P}
    {exec : BlockChain} {parent : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {e : Gloas.SignedExecutionPayloadEnvelope P} {s' : GJointState P} :
    gloasStepWith processSlots blockTransition cfg ccfg bls beacon exec parent b (some e) =
        .ok s' ↔
      ∃ post exec' o req postE,
        gloasBlockArm processSlots blockTransition beacon exec parent b = .ok (post, exec', o) ∧
        verifyEnvelopeG cfg ccfg bls post exec' e = .ok (req, postE) ∧
        s' = .gloas post exec' (.delivered e req postE) := by
  simp only [gloasStepWith_ok_iff, gloasDeliverOpt_ok_iff, reduceCtorEq, false_and, false_or,
    Option.some.injEq]
  constructor
  · rintro ⟨post, exec', o, h, _, req, postE, rfl, hv, rfl⟩
    exact ⟨post, exec', o, req, postE, h, hv, rfl⟩
  · rintro ⟨post, exec', o, req, postE, h, hv, rfl⟩
    exact ⟨post, exec', o, h, e, req, postE, rfl, hv, rfl⟩

/-! ## The block arm instantiated with U5 -/

/-- `process_slots` followed by `gloasBlockTransition` is U5's Gloas `state_transition`
(`Gloas.stateTransition_eq`). -/
theorem processSlots_then_gloasBlockTransition (ctx : Ctx) (state : Gloas.BeaconState P)
    (b : Gloas.SignedBeaconBlock P) :
    (do
      let st ← Gloas.processSlots ctx state b.message.slot
      gloasBlockTransition ctx st b : M (Gloas.BeaconState P)) =
      Gloas.stateTransition ctx state b :=
  (Gloas.stateTransition_eq ctx state b true).symm

/-- The Gloas→Gloas step with U5's functions succeeds exactly when Gloas `process_slots` reaches
the block's slot with the **post-slots state** `postSlots` (the state Gloas `process_block`
receives, at which the BF1 traces `builderDepositTrace`/`builderExitTrace` are read), the
execution-side settlement keyed on the FULL test at `postSlots` succeeds, the rest of
`state_transition` from `postSlots` gives `post`, and the step's end (the envelope, or
`.withheld`) succeeds. -/
theorem gloasStep_ok_iff {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain} {parent : ParentPayload P}
    {b : Gloas.SignedBeaconBlock P} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    {s' : GJointState P} :
    gloasStep cfg ccfg bls beacon exec parent b env? = .ok s' ↔
      ∃ postSlots post exec' o,
        Gloas.processSlots (gloasCtx ccfg bls) beacon b.message.slot = .ok postSlots ∧
        settleParent parent exec (parentFull postSlots b.message)
          b.message.body.parent_execution_requests = .ok (exec', o) ∧
        gloasBlockTransition (gloasCtx ccfg bls) postSlots b = .ok post ∧
        gloasDeliverOpt cfg ccfg bls post exec' env? = .ok s' := by
  unfold gloasStep
  rw [gloasStepWith_ok_iff]
  constructor
  · rintro ⟨post, exec', o, h, hd⟩
    obtain ⟨st0, h0, hs, hp⟩ := gloasBlockArm_ok_iff.mp h
    exact ⟨st0, post, exec', o, h0, hs, hp, hd⟩
  · rintro ⟨st0, post, exec', o, h0, hs, hp, hd⟩
    exact ⟨post, exec', o, gloasBlockArm_ok_iff.mpr ⟨st0, h0, hs, hp⟩, hd⟩

/-- The block transition after the slots runs Gloas `process_block` on the post-slots state (so
`processParentExecutionPayload` and the BF1 traces are read there). -/
theorem gloasBlockTransition_processBlock {ctx : Ctx} {st post : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} (h : gloasBlockTransition ctx st b = .ok post) :
    ∃ s, Gloas.processBlock ctx st b.message = .ok s := by
  unfold gloasBlockTransition Gloas.applySignedBlockWith at h
  simp only [ite_true] at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨s, hs, _⟩ := Except.bind_eq_ok h
  exact ⟨s, hs⟩

/-! ## The joint step -/

/-- A pre-Gloas pair is the Electra/Fulu `jointStep`, with no envelope and the block before the
Gloas fork slot. -/
theorem jointStepG_pre_ok_iff {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s : JointState P}
    {b : AnySignedBlock P} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    {s' : GJointState P} :
    jointStepG cfg ccfg bls (.pre s) (.pre b) env? = .ok s' ↔
      env? = none ∧ b.2.message.slot.toNat < gloasForkSlot (P := P) ccfg ∧
      ∃ j, jointStep cfg ccfg bls s b = .ok j ∧ s' = .pre j := by
  simp only [jointStepG, Except.bind_eq_ok_iff, require_ok_iff, unit_exists_iff,
    decide_eq_true_eq, Option.isNone_iff_eq_none, pure_eq_ok_iff]
  constructor
  · rintro ⟨h1, h2, j, hj, rfl⟩
    exact ⟨h1, h2, j, hj, rfl⟩
  · rintro ⟨h1, h2, j, hj, rfl⟩
    exact ⟨h1, h2, j, hj, rfl⟩

/-- A Gloas state and block take the Gloas arm. -/
theorem jointStepG_gloas_eq {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain} {parent : ParentPayload P}
    {b : Gloas.SignedBeaconBlock P} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} :
    jointStepG cfg ccfg bls (.gloas beacon exec parent) (.gloas b) env? =
      gloasStep cfg ccfg bls beacon exec parent b env? := rfl

/-- The Gloas arm of the joint step: `gloasStep_ok_iff`, with the post-slots state named. -/
theorem jointStepG_gloas_ok_iff {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain} {parent : ParentPayload P}
    {b : Gloas.SignedBeaconBlock P} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    {s' : GJointState P} :
    jointStepG cfg ccfg bls (.gloas beacon exec parent) (.gloas b) env? = .ok s' ↔
      ∃ postSlots post exec' o,
        Gloas.processSlots (gloasCtx ccfg bls) beacon b.message.slot = .ok postSlots ∧
        settleParent parent exec (parentFull postSlots b.message)
          b.message.body.parent_execution_requests = .ok (exec', o) ∧
        gloasBlockTransition (gloasCtx ccfg bls) postSlots b = .ok post ∧
        gloasDeliverOpt cfg ccfg bls post exec' env? = .ok s' := by
  rw [jointStepG_gloas_eq, gloasStep_ok_iff]

/-- Settling a `.landed` parent as `.landed` is exactly FULL with empty requests by value. -/
theorem settleParent_landed_iff {exec exec' : BlockChain} {full : Bool}
    {reqs : Gloas.ExecutionRequests} :
    settleParent (P := P) .landed exec full reqs = .ok (exec', .landed) ↔
      full = true ∧ reqs = Gloas.ExecutionRequests.empty ∧ exec' = exec := by
  rw [settleParent_ok_iff]
  constructor
  · rintro (⟨_, _, _, _, h, _⟩ | ⟨hf, _, hr, he, _⟩ | ⟨_, _, _, h⟩)
    · cases h
    · exact ⟨hf, hr, he⟩
    · cases h
  · rintro ⟨hf, hr, he⟩
    exact Or.inr (Or.inl ⟨hf, rfl, hr, he, rfl⟩)

/-- The crossing: a Fulu state strictly before the Gloas fork slot and a Gloas block at or after
it; `Gloas.crossFromFulu` gives `upgraded`; the crossing's slots function gives the post-slots
state `postSlots` (no slots at the fork slot); the parent settlement is FULL over the `.landed`
synthetic bid with empty requests by value, so the built-upon chain does not move; the rest of
`state_transition` gives `post`; then the step's end. -/
theorem jointStepG_cross_ok_iff {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .fulu} {exec : BlockChain} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} {s' : GJointState P} :
    jointStepG cfg ccfg bls (.pre ⟨.fulu, beacon, exec⟩) (.gloas b) env? = .ok s' ↔
      beacon.slot.toNat < gloasForkSlot (P := P) ccfg ∧
      gloasForkSlot (P := P) ccfg ≤ b.message.slot.toNat ∧
      ∃ upgraded postSlots post,
        Gloas.crossFromFulu (gloasCtx ccfg bls) beacon = .ok upgraded ∧
        crossingSlots (gloasCtx ccfg bls) upgraded b.message.slot = .ok postSlots ∧
        parentFull postSlots b.message = true ∧
        b.message.body.parent_execution_requests = Gloas.ExecutionRequests.empty ∧
        gloasBlockTransition (gloasCtx ccfg bls) postSlots b = .ok post ∧
        gloasDeliverOpt cfg ccfg bls post exec env? = .ok s' := by
  change crossingStep cfg ccfg bls beacon exec b env? = .ok s' ↔ _
  unfold crossingStep
  simp only [Except.bind_eq_ok_iff, require_ok_iff, unit_exists_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, upgraded, hup, ⟨post, exec', o⟩, harm, h⟩
    cases o with
    | landed =>
      obtain ⟨st0, h0, hs, hp⟩ := gloasBlockArm_ok_iff.mp harm
      obtain ⟨hf, hr, rfl⟩ := settleParent_landed_iff.mp hs
      exact ⟨h1, h2, upgraded, st0, post, hup, h0, hf, hr, hp, h⟩
    | empty => cases h
    | full _ _ _ => cases h
  · rintro ⟨h1, h2, upgraded, st0, post, hup, h0, hf, hr, hp, h⟩
    refine ⟨⟨h1, h2⟩, upgraded, hup, ⟨post, exec, .landed⟩, ?_, h⟩
    exact gloasBlockArm_ok_iff.mpr ⟨st0, h0, settleParent_landed_iff.mpr ⟨hf, hr, rfl⟩, hp⟩

/-! ## Refusals (Gloas pairs with Amsterdam only; every other pairing fails closed) -/

/-- A pre-Gloas block on a Gloas state is refused. -/
theorem jointStepG_refuses_gloas_pre {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain} {parent : ParentPayload P}
    {b : AnySignedBlock P} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} :
    jointStepG cfg ccfg bls (.gloas beacon exec parent) (.pre b) env? =
      .error (.assert "joint step: a pre-Gloas block on a Gloas state") := rfl

/-- A Gloas block on a pre-Gloas state of a fork other than Fulu is refused. -/
theorem jointStepG_refuses_cross_of_ne_fulu {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s : JointState P} (hf : s.fork ≠ .fulu) {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} :
    jointStepG cfg ccfg bls (.pre s) (.gloas b) env? =
      .error (.assert "joint step: a Gloas block crossing from a state other than Fulu") := by
  obtain ⟨f, beacon, exec⟩ := s
  cases f
  · rfl
  · rfl
  · exact absurd rfl hf
  · rfl

/-- An envelope with a pre-Gloas block is refused. -/
theorem jointStepG_refuses_pre_envelope {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s : JointState P} {b : AnySignedBlock P} {e : Gloas.SignedExecutionPayloadEnvelope P} :
    jointStepG cfg ccfg bls (.pre s) (.pre b) (some e) =
      .error (.assert "joint step: an envelope with a pre-Gloas block") := rfl

/-- A pre-Gloas block at or after the Gloas fork slot is refused. -/
theorem jointStepG_refuses_pre_at_gloas_fork {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s : JointState P} {b : AnySignedBlock P}
    (hslot : gloasForkSlot (P := P) ccfg ≤ b.2.message.slot.toNat) :
    jointStepG cfg ccfg bls (.pre s) (.pre b) none =
      .error (.assert "joint step: a pre-Gloas block at or after the Gloas fork slot") := by
  have : decide (b.2.message.slot.toNat < gloasForkSlot (P := P) ccfg) = false :=
    decide_eq_false (Nat.not_lt.mpr hslot)
  simp only [jointStepG, Option.isNone_none, require, this, ite_true, bind, Except.bind,
    Bool.false_eq_true, ite_false]
  rfl

/-- Any other pre-Gloas pair is refused, as by `jointStep` (`jointStep_refuses`). -/
theorem jointStepG_refuses_pre {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s : JointState P} {b : AnySignedBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (hpair : (s.fork, b.1) ≠ (.electra, .electra) ∧ (s.fork, b.1) ≠ (.fulu, .fulu) ∧
      (s.fork, b.1) ≠ (.electra, .fulu)) (s' : GJointState P) :
    jointStepG cfg ccfg bls (.pre s) (.pre b) env? ≠ .ok s' := by
  intro h
  obtain ⟨_, _, j, hj, _⟩ := jointStepG_pre_ok_iff.mp h
  obtain ⟨e, he⟩ := jointStep_refuses (cfg := cfg) (ccfg := ccfg) (bls := bls) hpair
  rw [he] at hj
  cases hj

/-- The crossing refuses an EMPTY first settlement (design.md §2.4: the first Gloas block's
bid must extend the synthetic bid's block hash). -/
theorem jointStepG_cross_refuses_empty {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .fulu} {exec : BlockChain} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} {upgraded postSlots : Gloas.BeaconState P}
    (hup : Gloas.crossFromFulu (gloasCtx ccfg bls) beacon = .ok upgraded)
    (h0 : crossingSlots (gloasCtx ccfg bls) upgraded b.message.slot = .ok postSlots)
    (hempty : parentFull postSlots b.message = false) (s' : GJointState P) :
    jointStepG cfg ccfg bls (.pre ⟨.fulu, beacon, exec⟩) (.gloas b) env? ≠ .ok s' := by
  intro h
  obtain ⟨_, _, u, st0, _, hu, h0', hf, _⟩ := jointStepG_cross_ok_iff.mp h
  rw [hup] at hu
  cases hu
  rw [h0] at h0'
  cases h0'
  rw [hempty] at hf
  cases hf

/-- The crossing refuses a first Gloas block whose `parent_execution_requests` are not empty by
value (SF-7). -/
theorem jointStepG_cross_refuses_requests {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .fulu} {exec : BlockChain} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (hne : b.message.body.parent_execution_requests ≠ Gloas.ExecutionRequests.empty)
    (s' : GJointState P) :
    jointStepG cfg ccfg bls (.pre ⟨.fulu, beacon, exec⟩) (.gloas b) env? ≠ .ok s' := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, hr, _⟩ := jointStepG_cross_ok_iff.mp h
  exact hne hr

/-- A FULL child of a withheld payload is refused by the joint step (the model of
`is_payload_verified`, FC:1058-1061). -/
theorem jointStepG_refuses_full_of_withheld {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon postSlots : Gloas.BeaconState P} {exec : BlockChain} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (h0 : Gloas.processSlots (gloasCtx ccfg bls) beacon b.message.slot = .ok postSlots)
    (hfull : parentFull postSlots b.message = true) (s' : GJointState P) :
    jointStepG cfg ccfg bls (.gloas beacon exec .withheld) (.gloas b) env? ≠ .ok s' := by
  intro h
  obtain ⟨st0, _, _, _, h0', hs, _⟩ := jointStepG_gloas_ok_iff.mp h
  rw [h0] at h0'
  cases h0'
  rw [hfull, settleParent_refuses_full_of_withheld] at hs
  cases hs

/-- A FULL child of a delivered payload whose `parent_execution_requests` are not the envelope's
`execution_requests` (as values) is refused by the joint step. -/
theorem jointStepG_refuses_other_requests {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon postSlots : Gloas.BeaconState P} {exec : BlockChain} {b : Gloas.SignedBeaconBlock P}
    {env : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P}
    {postE : BlockChain} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (h0 : Gloas.processSlots (gloasCtx ccfg bls) beacon b.message.slot = .ok postSlots)
    (hfull : parentFull postSlots b.message = true)
    (hne : b.message.body.parent_execution_requests ≠ env.message.execution_requests)
    (s' : GJointState P) :
    jointStepG cfg ccfg bls (.gloas beacon exec (.delivered env req postE)) (.gloas b) env? ≠
      .ok s' := by
  intro h
  obtain ⟨st0, _, _, _, h0', hs, _⟩ := jointStepG_gloas_ok_iff.mp h
  rw [h0] at h0'
  cases h0'
  rw [hfull, settleParent_refuses_other_requests hne] at hs
  cases hs

/-! ## The crossing's builders (`statements.md` `crossing_builders`, the Jaune half) -/

/-- Every builder record of `s` has `withdrawable_epoch = FAR_FUTURE_EPOCH`. -/
def BuildersFar (s : Gloas.BeaconState P) : Prop :=
  ∀ (i : Nat) (x : Gloas.Builder), s.builders.toArray[i]? = some x → x.withdrawable_epoch = FAR_FUTURE_EPOCH

/-- `add_builder_to_registry` writes a record at `FAR_FUTURE_EPOCH` and touches no pending
builder withdrawal. -/
theorem addBuilderToRegistry_buildersFar {state post : Gloas.BeaconState P} {pk : BLSPubkey}
    {ver : U8} {addr : ExecutionAddress} {amt : Gwei} {slot : Slot} (hf : BuildersFar state)
    (h : Gloas.addBuilderToRegistry state pk ver addr amt slot = .ok post) :
    BuildersFar post ∧ post.builder_pending_withdrawals = state.builder_pending_withdrawals := by
  unfold Gloas.addBuilderToRegistry at h
  obtain ⟨idx, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨ep, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨bs, hbs, h⟩ := Except.bind_eq_ok h
  cases h
  obtain ⟨_, hnew, hold⟩ := Facts.Gloas.pl_setOrAppend_ok hbs
  refine ⟨fun i x hx => ?_, rfl⟩
  by_cases hi : i = idx.toNat
  · subst hi
    rw [hnew] at hx
    cases hx
    rfl
  · rw [hold i hi] at hx
    exact hf i x hx

/-- One onboarding iteration keeps every builder at `FAR_FUTURE_EPOCH` (a registration writes
`FAR_FUTURE_EPOCH`, a top-up changes only the balance) and touches no pending builder
withdrawal. -/
theorem onboardBuilderDeposit_buildersFar {ctx : Ctx} {V : Array BLSPubkey}
    {acc acc' : Gloas.BeaconState P × Array PendingDeposit} {d : PendingDeposit}
    (hf : BuildersFar acc.1) (h : Gloas.onboardBuilderDeposit ctx V acc d = .ok acc') :
    BuildersFar acc'.1 ∧ acc'.1.builder_pending_withdrawals = acc.1.builder_pending_withdrawals := by
  obtain ⟨st, pd⟩ := acc
  unfold Gloas.onboardBuilderDeposit at h
  dsimp only at h hf
  split at h
  · cases h
    exact ⟨hf, rfl⟩
  · split at h
    · split at h
      · cases h
        exact ⟨hf, rfl⟩
      · obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
        split at h
        · cases h
          exact ⟨hf, rfl⟩
        · obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
          split at h
          · cases h
            exact ⟨hf, rfl⟩
          · obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
            obtain ⟨st', hadd, h⟩ := Except.bind_eq_ok h
            cases h
            exact addBuilderToRegistry_buildersFar hf hadd
    · rename_i bi _
      obtain ⟨bld, hget, h⟩ := Except.bind_eq_ok h
      obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
      obtain ⟨bs, hset, h⟩ := Except.bind_eq_ok h
      cases h
      refine ⟨fun i x hx => ?_, rfl⟩
      obtain ⟨_, hnew, hold⟩ := Facts.Gloas.pl_set_ok hset
      by_cases hi : i = bi
      · subst hi
        rw [hnew] at hx
        cases hx
        exact hf _ bld (Facts.Gloas.pl_get_ok.mp hget)
      · rw [hold i hi] at hx
        exact hf i x hx

/-- The onboarding loop keeps every builder at `FAR_FUTURE_EPOCH` and touches no pending
builder withdrawal. -/
theorem foldlM_onboardBuilderDeposit_buildersFar {ctx : Ctx} {V : Array BLSPubkey} :
    ∀ (l : List PendingDeposit) (acc acc' : Gloas.BeaconState P × Array PendingDeposit),
      BuildersFar acc.1 → l.foldlM (Gloas.onboardBuilderDeposit ctx V) acc = .ok acc' →
      BuildersFar acc'.1 ∧
        acc'.1.builder_pending_withdrawals = acc.1.builder_pending_withdrawals
  | [], acc, acc', hf, h => by
    cases h
    exact ⟨hf, rfl⟩
  | d :: l, acc, acc', hf, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨a1, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨f1, w1⟩ := onboardBuilderDeposit_buildersFar hf h1
    obtain ⟨f2, w2⟩ := foldlM_onboardBuilderDeposit_buildersFar l a1 acc' f1 h
    exact ⟨f2, w2.trans w1⟩

/-- `onboard_builders_from_pending_deposits` keeps every builder at `FAR_FUTURE_EPOCH` and
touches no pending builder withdrawal. -/
theorem onboardBuildersFromPendingDeposits_buildersFar {ctx : Ctx}
    {state post : Gloas.BeaconState P} (hf : BuildersFar state)
    (h : Gloas.onboardBuildersFromPendingDeposits ctx state = .ok post) :
    BuildersFar post ∧ post.builder_pending_withdrawals = state.builder_pending_withdrawals := by
  unfold Gloas.onboardBuildersFromPendingDeposits at h
  obtain ⟨⟨st, pd⟩, hfold, h⟩ := Except.bind_eq_ok h
  cases h
  rw [← Array.foldlM_toList] at hfold
  exact foldlM_onboardBuilderDeposit_buildersFar _ (state, #[]) (st, pd) hf hfold

/-- The state `upgrade_to_gloas` builds before onboarding has no builders and no pending
builder withdrawals (fork.md:194, 204). -/
theorem upgradedState_builders {cfg : Config} {pre : BeaconState P .fulu}
    {post : Gloas.BeaconState P} (h : Gloas.upgradedState cfg pre = .ok post) :
    post.builders = ProgressiveListS.empty ∧
      post.builder_pending_withdrawals = ProgressiveListS.empty := by
  unfold Gloas.upgradedState at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases h
  exact ⟨rfl, rfl⟩

/-- `upgrade_to_gloas` leaves every builder at `FAR_FUTURE_EPOCH` and no pending builder
withdrawal: the builders are exactly those `onboard_builders_from_pending_deposits` registers,
each written at `FAR_FUTURE_EPOCH` and only topped up after. -/
theorem upgradeToGloas_builders {ctx : Ctx} {pre : BeaconState P .fulu}
    {post : Gloas.BeaconState P} (h : Gloas.upgradeToGloas ctx pre = .ok post) :
    BuildersFar post ∧ post.builder_pending_withdrawals = ProgressiveListS.empty := by
  unfold Gloas.upgradeToGloas at h
  obtain ⟨p0, h0, h⟩ := Except.bind_eq_ok h
  obtain ⟨w, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨hb, hw⟩ := upgradedState_builders h0
  have hf : BuildersFar { p0 with ptc_window := w } := by
    intro i x hx
    simp only [hb, ProgressiveListS.empty] at hx
    simp at hx
  obtain ⟨f, w'⟩ := onboardBuildersFromPendingDeposits_buildersFar hf h
  exact ⟨f, w'.trans hw⟩

/-- `crossFromFulu` ends in `upgrade_to_gloas` of the Fulu state at the fork slot. -/
theorem crossFromFulu_upgrade {ctx : Ctx} {pre : BeaconState P .fulu}
    {post : Gloas.BeaconState P} (h : Gloas.crossFromFulu ctx pre = .ok post) :
    ∃ atFork, Gloas.upgradeToGloas ctx atFork = .ok post := by
  unfold Gloas.crossFromFulu at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  split at h
  · obtain ⟨atFork, _, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    exact ⟨atFork, h⟩
  · obtain ⟨atFork, _, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    exact ⟨atFork, h⟩

/-- **The crossing's builders.** A successful crossing step upgrades the Fulu state by
`upgrade_to_gloas` (inside `Gloas.crossFromFulu`) to `upgraded`, whose builders are each at
`FAR_FUTURE_EPOCH` and whose `builder_pending_withdrawals` is empty, and the step's Gloas block
arm runs from `upgraded`: its post-slots state `postSlots`, then the block transition to
`post`, then the step's end. -/
theorem jointStepG_crossing_builders {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .fulu} {exec : BlockChain} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} {s' : GJointState P}
    (h : jointStepG cfg ccfg bls (.pre ⟨.fulu, beacon, exec⟩) (.gloas b) env? = .ok s') :
    ∃ atFork upgraded postSlots post,
      Gloas.crossFromFulu (gloasCtx ccfg bls) beacon = .ok upgraded ∧
      Gloas.upgradeToGloas (gloasCtx ccfg bls) atFork = .ok upgraded ∧
      BuildersFar upgraded ∧
      upgraded.builder_pending_withdrawals = ProgressiveListS.empty ∧
      crossingSlots (gloasCtx ccfg bls) upgraded b.message.slot = .ok postSlots ∧
      gloasBlockTransition (gloasCtx ccfg bls) postSlots b = .ok post ∧
      gloasDeliverOpt cfg ccfg bls post exec env? = .ok s' := by
  obtain ⟨_, _, upgraded, postSlots, post, hup, h0, _, _, hp, hd⟩ :=
    jointStepG_cross_ok_iff.mp h
  obtain ⟨atFork, hat⟩ := crossFromFulu_upgrade hup
  obtain ⟨hf, hw⟩ := upgradeToGloas_builders hat
  exact ⟨atFork, upgraded, postSlots, post, hup, hat, hf, hw, h0, hp, hd⟩

end JauneConsensus
