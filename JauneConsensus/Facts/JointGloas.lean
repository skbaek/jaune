import JauneConsensus.JointGloas

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
* `gloasBlockArm_ok_iff`, `gloasStepWith_none_ok_iff`, `gloasStepWith_some_ok_iff`, and
  `gloasBlockArm_refuses_full_of_withheld`.
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

/-- The envelope arm succeeds exactly on a Gloas state whose latest block has no envelope yet,
when the seam accepts; it records the envelope, the request and the engine's chain, and moves
nothing else. -/
theorem deliver_ok_iff {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s s' : GJointState P}
    {e : Gloas.SignedExecutionPayloadEnvelope P} :
    deliver cfg ccfg bls s e = .ok s' ↔
      ∃ beacon exec parent req post, s = .gloas beacon exec parent ∧
        parent.awaitsEnvelope = true ∧
        verifyEnvelopeG cfg ccfg bls beacon exec e = .ok (req, post) ∧
        s' = .gloas beacon exec (.delivered e req post) := by
  cases s with
  | pre j =>
    simp only [deliver, reduceCtorEq, false_and, exists_false]
  | gloas beacon exec parent =>
    constructor
    · intro h
      unfold deliver at h
      obtain ⟨u, hreq, h⟩ := Except.bind_eq_ok h
      obtain ⟨⟨req, post⟩, hv, h⟩ := Except.bind_eq_ok h
      cases h
      exact ⟨beacon, exec, parent, req, post, rfl, require_ok_iff.mp hreq, hv, rfl⟩
    · rintro ⟨b, x, p, req, post, hs, hp, hv, rfl⟩
      cases hs
      unfold deliver
      simp only [require, hp, ite_true, hv, bind, Except.bind, pure, Except.pure]

/-- A second envelope for the same block is refused. -/
theorem deliver_refuses_delivered {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain}
    {env e : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P}
    {post : BlockChain} (s' : GJointState P) :
    deliver cfg ccfg bls (.gloas beacon exec (.delivered env req post)) e ≠ .ok s' := by
  intro h
  obtain ⟨_, _, _, _, _, hs, hp, _, _⟩ := deliver_ok_iff.mp h
  cases hs
  cases hp

/-- The envelope arm rejects withdrawals that differ, as lists, from the expected ones. -/
theorem deliver_rejects_of_withdrawals_ne {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain} {parent : ParentPayload P}
    {e : Gloas.SignedExecutionPayloadEnvelope P}
    (hne : ¬ Gloas.WithdrawalsMatchExpected beacon e) (s' : GJointState P) :
    deliver cfg ccfg bls (.gloas beacon exec parent) e ≠ .ok s' := by
  intro h
  obtain ⟨_, _, _, _, _, hs, _, hv, _⟩ := deliver_ok_iff.mp h
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
  obtain ⟨_, _, _, _, _, hs, _, hv, _⟩ := deliver_ok_iff.mp h
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
  obtain ⟨_, _, _, _, _, hs, _, hv, _⟩ := deliver_ok_iff.mp h
  cases hs
  exact verifyEnvelopeG_rejects_of_requestsRoot_ne hne _ hv

/-- The envelope arm does not depend on the switch when the signature verifies. -/
theorem deliver_bls_indep {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain} {parent : ParentPayload P}
    {e : Gloas.SignedExecutionPayloadEnvelope P}
    (hsig : Gloas.verifyExecutionPayloadEnvelopeSignatureB true beacon e = .ok true) :
    deliver cfg ccfg bls (.gloas beacon exec parent) e =
      deliver cfg ccfg true (.gloas beacon exec parent) e := by
  simp only [deliver, verifyEnvelopeG_bls_indep hsig]

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
  unfold gloasStepWith
  simp only [Except.bind_eq_ok_iff, pure_eq_ok_iff, Prod.exists]
  constructor
  · rintro ⟨post, exec', o, h, rfl⟩
    exact ⟨post, exec', o, h, rfl⟩
  · rintro ⟨post, exec', o, h, rfl⟩
    exact ⟨post, exec', o, h, rfl⟩

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
  unfold gloasStepWith
  simp only [Except.bind_eq_ok_iff, Prod.exists, deliver_ok_iff]
  constructor
  · rintro ⟨post, exec', o, h, _, _, _, req, postE, hs, _, hv, rfl⟩
    cases hs
    exact ⟨post, exec', o, req, postE, h, hv, rfl⟩
  · rintro ⟨post, exec', o, req, postE, h, hv, rfl⟩
    exact ⟨post, exec', o, h, post, exec', .withheld, req, postE, rfl, rfl, hv, rfl⟩

end JauneConsensus
