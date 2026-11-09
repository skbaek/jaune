import JauneConsensus.Joint

/-!
# Characterizations of the joint step (goal `eip7002-cross-layer-v1`, unit W1a)

`engineVerdict_ok_iff` states each engine check as a conjunct in the definition's
order; `jointTransitionAt_ok_iff` splits the joint transition into the payload
request, the engine verdict, and the beacon side; the `jointStep` theorems add
each accepted fork pair's slot requirements.
-/

namespace JauneConsensus

open Jaune

variable {P : Preset}

/-- Reading a fork-gated field when the fork fact is known. -/
private theorem Gated.read_get {c : Bool} (h : c = true) (x : Gated c α) (site : String) :
    Gated.read x site = .ok (Gated.get h x) := by
  cases c with
  | true => rfl
  | false => cases h

/-- A `!=` check that passes is an equality. -/
private theorem bne_eq_false_eq {α : Type} [BEq α] [LawfulBEq α] {a b : α} :
    (a != b) = false ↔ a = b := by
  simp [bne, beq_iff_eq]

/-- A `¬(· = true)` hypothesis gives the `= false` form. -/
private theorem eq_false_of_not_true {b : Bool} (h : ¬(b = true)) : b = false := by
  cases hb : b with
  | true => simp [hb] at h
  | false => rfl

/-- A `require true` is a silent success. -/
private theorem require_true {site : String} : require true site = .ok () := rfl

/-- Collapsing a bind over `.ok`. -/
private theorem bind_ok {ε α β} {x : α} {k : α → Except ε β} :
    ((.ok x : Except ε α) >>= k) = k x := rfl

/-- Collapsing a `mapError` over `.ok`. -/
private theorem mapError_ok' {ε δ α} {f : ε → δ} {a : α} :
    (Except.ok a).mapError f = .ok a := rfl

/-- `ofBlock` reads the body's execution requests, which exist at Electra and later. -/
theorem NewPayloadRequest.ofBlock_ok {f : CFork} {h : f.atLeast .electra = true}
    (block : BeaconBlock P f) :
    NewPayloadRequest.ofBlock block = .ok
      { executionPayload := block.body.execution_payload
        versionedHashes :=
          block.body.blob_kzg_commitments.toArray.toList.map fun c =>
            kzgCommitmentToVersionedHash c.toArray.toList
        parentBeaconBlockRoot := block.parent_root
        executionRequests := getExecutionRequestsList (Gated.get h block.body.execution_requests) } := by
  unfold NewPayloadRequest.ofBlock
  rw [Gated.read_get h]
  rfl

/-- The engine accepts a payload exactly when every check passes, in the
definition's order. -/
theorem engineVerdict_ok_iff {cfg : ChainConfig} {cf : CFork} {exec : BlockChain}
    {req : NewPayloadRequest P} {post : BlockChain} :
    engineVerdict cfg cf exec req = .ok post ↔
      req.executionPayload.txBytes.any List.isEmpty = false ∧
      (payloadToBlock req).header.hash = req.executionPayload.block_hash ∧
      blobVersionedHashesOf req.executionPayload.txBytes = .ok req.versionedHashes ∧
      cfg.checkChainId exec = .ok () ∧
      ∃ f, cfg.forkAt (payloadToBlock req).header.number
            (payloadToBlock req).header.timestamp = .ok f ∧
        f.consensusFork? = some cf ∧
        checkBlockRlpSize f.ruleSet.block (payloadToBlock req).toBLT.toBytes.length = .ok () ∧
        stateTransitionScheduledE cfg f exec (payloadToBlock req) = .ok (.ok post) ∧
        ∃ st bout, applyBody (initBenv f exec (payloadToBlock req).header)
            (payloadToBlock req).txs (payloadToBlock req).ommers (payloadToBlock req).wds =
            .ok (st, bout) ∧
          bout.requests = req.executionRequests := by
  constructor
  · intro h
    unfold engineVerdict at h
    by_cases hc1 : req.executionPayload.txBytes.any List.isEmpty = true
    · rw [ite_eq_left hc1] at h
      obtain ⟨a, ha, _⟩ := Except.bind_eq_ok h
      cases ha
    · rw [ite_eq_right hc1] at h
      have he1 : req.executionPayload.txBytes.any List.isEmpty = false :=
        eq_false_of_not_true hc1
      by_cases hc2 : ((payloadToBlock req).header.hash != req.executionPayload.block_hash) = true
      · rw [ite_eq_left hc2] at h
        obtain ⟨a, ha, _⟩ := Except.bind_eq_ok h
        cases ha
      · rw [ite_eq_right hc2] at h
        have he2 : (payloadToBlock req).header.hash = req.executionPayload.block_hash :=
          bne_eq_false_eq.mp (eq_false_of_not_true hc2)
        obtain ⟨hashes, hhashes, h⟩ := Except.bind_eq_ok h
        have hhashes' : blobVersionedHashesOf req.executionPayload.txBytes = .ok hashes :=
          Except.mapError_eq_ok_iff.mp hhashes
        by_cases hc3 : (hashes != req.versionedHashes) = true
        · rw [ite_eq_left hc3] at h
          obtain ⟨a, ha, _⟩ := Except.bind_eq_ok h
          cases ha
        · rw [ite_eq_right hc3] at h
          have he3 : hashes = req.versionedHashes :=
            bne_eq_false_eq.mp (eq_false_of_not_true hc3)
          subst he3
          obtain ⟨_, hchain, h⟩ := Except.bind_eq_ok h
          have hchain' : cfg.checkChainId exec = .ok () :=
            Except.mapError_eq_ok_iff.mp hchain
          obtain ⟨f, hfork, h⟩ := Except.bind_eq_ok h
          have hfork' : cfg.forkAt (payloadToBlock req).header.number
              (payloadToBlock req).header.timestamp = .ok f :=
            Except.mapError_eq_ok_iff.mp hfork
          by_cases hc4 : (f.consensusFork? != some cf) = true
          · rw [ite_eq_left hc4] at h
            obtain ⟨a, ha, _⟩ := Except.bind_eq_ok h
            cases ha
          · rw [ite_eq_right hc4] at h
            have he4 : f.consensusFork? = some cf :=
              bne_eq_false_eq.mp (eq_false_of_not_true hc4)
            obtain ⟨_, hsize, h⟩ := Except.bind_eq_ok h
            have hsize' : checkBlockRlpSize f.ruleSet.block
                (payloadToBlock req).toBLT.toBytes.length = .ok () :=
              Except.mapError_eq_ok_iff.mp hsize
            cases hs : stateTransitionScheduledE cfg f exec (payloadToBlock req) with
            | error e =>
              simp only [hs] at h
              obtain ⟨a, ha, _⟩ := Except.bind_eq_ok h
              cases ha
            | ok r =>
              cases r with
              | error e =>
                simp only [hs] at h
                obtain ⟨a, ha, _⟩ := Except.bind_eq_ok h
                cases ha
              | ok post' =>
                simp only [hs, pure_bind] at h
                obtain ⟨p, hp, h⟩ := Except.bind_eq_ok h
                have hbody : applyBody (initBenv f exec (payloadToBlock req).header)
                    (payloadToBlock req).txs (payloadToBlock req).ommers
                    (payloadToBlock req).wds = .ok p :=
                  Except.mapError_eq_ok_iff.mp hp
                obtain ⟨st, bout⟩ := p
                dsimp only at h
                by_cases hc5 : (bout.requests != req.executionRequests) = true
                · rw [ite_eq_left hc5] at h
                  obtain ⟨a, ha, _⟩ := Except.bind_eq_ok h
                  cases ha
                · rw [ite_eq_right hc5] at h
                  have he5 : bout.requests = req.executionRequests :=
                    bne_eq_false_eq.mp (eq_false_of_not_true hc5)
                  have h' : Except.ok post' = Except.ok post := h
                  cases h'
                  exact ⟨he1, he2, hhashes', hchain', f, hfork', he4, hsize',
                    hs, st, bout, hbody, he5⟩
  · rintro ⟨hempty, hhash, hhashes, hchain, f, hfork, hpair, hsize, hst, st, bout, hbody, hreq⟩
    have n1 : ¬(req.executionPayload.txBytes.any List.isEmpty = true) := by simp [hempty]
    have n2 : ¬(((payloadToBlock req).header.hash != req.executionPayload.block_hash) = true) := by
      simp [hhash]
    have n3 : ¬((req.versionedHashes != req.versionedHashes) = true) := by simp
    have n4 : ¬((f.consensusFork? != some cf) = true) := by simp [hpair]
    have n5 : ¬((bout.requests != req.executionRequests) = true) := by simp [hreq]
    unfold engineVerdict
    rw [ite_eq_right n1]
    rw [ite_eq_right n2]
    simp only [hhashes, mapError_ok', bind_ok]
    rw [ite_eq_right n3]
    simp only [hchain, mapError_ok', bind_ok]
    simp only [hfork, mapError_ok', bind_ok]
    rw [ite_eq_right n4]
    simp only [hsize, mapError_ok', bind_ok]
    simp only [hst, pure_bind]
    simp only [hbody, mapError_ok', bind_ok]
    rw [ite_eq_right n5]
    rfl

/-- An accepted payload's body run produces the payload's own requests. -/
theorem engineVerdict_requests {cfg : ChainConfig} {cf : CFork} {exec : BlockChain}
    {req : NewPayloadRequest P} {post : BlockChain}
    (h : engineVerdict cfg cf exec req = .ok post) :
    ∃ f p, applyBody (initBenv f exec (payloadToBlock req).header)
      (payloadToBlock req).txs (payloadToBlock req).ommers (payloadToBlock req).wds = .ok p ∧
      p.2.requests = req.executionRequests := by
  rw [engineVerdict_ok_iff] at h
  obtain ⟨_, _, _, _, f, _, _, _, _, st, bout, hbody, hreq⟩ := h
  exact ⟨f, (st, bout), hbody, hreq⟩

/-- If the body runs to different requests at the resolved fork, the engine refuses. -/
theorem engineVerdict_rejects_of_requests_ne {cfg : ChainConfig} {cf : CFork} {exec : BlockChain}
    {req : NewPayloadRequest P} {f : Jaune.Fork} {st : State} {bout : BlockOutput}
    (hfork : cfg.forkAt (payloadToBlock req).header.number
      (payloadToBlock req).header.timestamp = .ok f)
    (hbody : applyBody (initBenv f exec (payloadToBlock req).header) (payloadToBlock req).txs
      (payloadToBlock req).ommers (payloadToBlock req).wds = .ok (st, bout))
    (hne : bout.requests ≠ req.executionRequests) :
    ∃ e, engineVerdict cfg cf exec req = .error e := by
  cases hverdict : engineVerdict cfg cf exec req with
  | ok post' =>
    rw [engineVerdict_ok_iff] at hverdict
    obtain ⟨_, _, _, _, f', hfork', _, _, _, st', bout', hbody', hreq'⟩ := hverdict
    have hff : f' = f := by
      rw [hfork] at hfork'
      simpa using hfork'.symm
    cases hff
    rw [hbody] at hbody'
    have hpair2 : (st, bout) = (st', bout') := by simpa using hbody'
    have hb2 : bout = bout' := congrArg Prod.snd hpair2
    rw [hb2] at hne
    exact absurd hreq' hne
  | error e => exact ⟨e, rfl⟩

/-- The converted block carries the payload's withdrawals. -/
theorem payloadToBlock_wds (req : NewPayloadRequest P) :
    (payloadToBlock req).wds = req.executionPayload.executionWithdrawals := rfl

/-- A joint transition succeeds exactly when the payload request builds, the
engine accepts it, and the beacon side (with a passing engine verdict) succeeds. -/
theorem jointTransitionAt_ok_iff {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {f : CFork}
    {beacon : BeaconState P f} {exec : BlockChain} {sb : SignedBeaconBlock P f} {atSlot : Bool}
    {beacon' : BeaconState P f} {exec' : BlockChain} :
    jointTransitionAt cfg ccfg bls beacon exec sb atSlot = .ok (beacon', exec') ↔
      ∃ req, NewPayloadRequest.ofBlock sb.message = .ok req ∧
        engineVerdict cfg f exec req = .ok exec' ∧
        ((if atSlot then
            (do require (← verifyBlockSignature bls beacon sb)
                  "state_transition: verify_block_signature"
                let s ← processBlock { cfg := ccfg, blsActive := bls } beacon sb.message
                require (B256.beq sb.message.state_root (Ssz.hashTreeRoot s))
                  "state_transition: block.state_root"
                pure s)
          else stateTransition { cfg := ccfg, blsActive := bls } beacon sb) = .ok beacon') := by
  constructor
  · intro h
    unfold jointTransitionAt at h
    obtain ⟨req, hreq, h⟩ := Except.bind_eq_ok h
    cases hv : engineVerdict cfg f exec req with
    | error e =>
      simp only [hv, Except.isOk, Except.toBool] at h
      by_cases hat : atSlot = true
      · rw [ite_eq_left hat] at h
        obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
        obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
        obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
        obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
        obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
        cases h
      · rw [ite_eq_right hat] at h
        obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
        cases h
    | ok exec'v =>
      simp only [hv, Except.isOk, Except.toBool] at h
      by_cases hat : atSlot = true
      · rw [ite_eq_left hat] at h
        obtain ⟨sigv, hsig, h⟩ := Except.bind_eq_ok h
        obtain ⟨_, hsigreq, h⟩ := Except.bind_eq_ok h
        have hsigv : sigv = true := require_eq_ok_iff.mp hsigreq
        obtain ⟨s, hproc, h⟩ := Except.bind_eq_ok h
        obtain ⟨_, hbeqreq, h⟩ := Except.bind_eq_ok h
        have hbeqv : B256.beq sb.message.state_root (Ssz.hashTreeRoot s) = true :=
          require_eq_ok_iff.mp hbeqreq
        obtain ⟨bv, hbv, h⟩ := Except.bind_eq_ok h
        have hbv' : Except.ok s = Except.ok bv := hbv
        cases hbv'
        have hpair : Except.ok (s, exec'v) = Except.ok (beacon', exec') := h
        cases hpair
        rw [ite_eq_left hat]
        exact ⟨req, hreq, hv, by
          simp only [hsig, hsigv, hproc, hbeqv, require_true, bind_ok]
          rfl⟩
      · rw [ite_eq_right hat] at h
        obtain ⟨beaconv, hst', h⟩ := Except.bind_eq_ok h
        have hpair : Except.ok (beaconv, exec'v) = Except.ok (beacon', exec') := h
        cases hpair
        rw [ite_eq_right hat]
        exact ⟨req, hreq, hv, hst'⟩
  · rintro ⟨req, hreq, hverdict, hT⟩
    simp only [jointTransitionAt, hreq, bind_ok]
    by_cases hat : atSlot = true
    · rw [ite_eq_left hat] at hT ⊢
      obtain ⟨sigv, hsig, hT⟩ := Except.bind_eq_ok hT
      obtain ⟨_, hsigreq, hT⟩ := Except.bind_eq_ok hT
      have hsigv : sigv = true := require_eq_ok_iff.mp hsigreq
      obtain ⟨s, hproc, hT⟩ := Except.bind_eq_ok hT
      obtain ⟨_, hbeqreq, hT⟩ := Except.bind_eq_ok hT
      have hbeqv : B256.beq sb.message.state_root (Ssz.hashTreeRoot s) = true :=
        require_eq_ok_iff.mp hbeqreq
      have hs_eq : s = beacon' := by
        have h' : Except.ok s = Except.ok beacon' := hT
        cases h'
        rfl
      cases hs_eq
      simp only [hsig, hsigv, hproc, hbeqv, hverdict, require_true, bind_ok, pure_bind,
        Except.isOk, Except.toBool]
      rfl
    · rw [ite_eq_right hat] at hT ⊢
      simp only [hverdict, Except.isOk, Except.toBool]
      simp only [hT, bind_ok]
      rfl

/-- A joint Electra step is a below-the-fork-slot block with an accepted payload. -/
theorem jointStep_electra_ok_iff {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .electra}
    {s' : JointState P} :
    jointStep cfg ccfg bls ⟨.electra, beacon, exec⟩ ⟨.electra, sb⟩ = .ok s' ↔
      sb.message.slot.toNat < fuluForkSlot (P := P) ccfg ∧
      ∃ req beacon' exec', NewPayloadRequest.ofBlock sb.message = .ok req ∧
        engineVerdict cfg .electra exec req = .ok exec' ∧
        stateTransition { cfg := ccfg, blsActive := bls } beacon sb = .ok beacon' ∧
        s' = ⟨.electra, beacon', exec'⟩ := by
  constructor
  · intro h
    simp only [jointStep] at h
    obtain ⟨_, hslotreq, h⟩ := Except.bind_eq_ok h
    have hslot : sb.message.slot.toNat < fuluForkSlot (P := P) ccfg :=
      of_decide_eq_true (require_eq_ok_iff.mp hslotreq)
    obtain ⟨p, hjt, h⟩ := Except.bind_eq_ok h
    obtain ⟨beacon', exec'⟩ := p
    dsimp only at h
    have hs' : Except.ok (⟨.electra, beacon', exec'⟩ : JointState P) = Except.ok s' := h
    cases hs'
    rw [jointTransitionAt_ok_iff] at hjt
    obtain ⟨req, hreq, hverdict, hbeacon⟩ := hjt
    rw [ite_eq_right (by decide)] at hbeacon
    exact ⟨hslot, req, beacon', exec', hreq, hverdict, hbeacon, rfl⟩
  · rintro ⟨hslot, req, beacon', exec', hreq, hverdict, hbeacon, rfl⟩
    have hdec : decide (sb.message.slot.toNat < fuluForkSlot (P := P) ccfg) = true :=
      decide_eq_true hslot
    have hreq0 : require (decide (sb.message.slot.toNat < fuluForkSlot (P := P) ccfg))
        "joint step: an Electra block at or after the Fulu fork slot" = .ok () := by
      rw [require_eq_ok_iff]; exact hdec
    have hjt : jointTransitionAt cfg ccfg bls beacon exec sb = .ok (beacon', exec') := by
      rw [jointTransitionAt_ok_iff]
      refine ⟨req, hreq, hverdict, ?_⟩
      rw [ite_eq_right (by decide)]
      exact hbeacon
    simp only [jointStep, hreq0, bind_ok, hjt, bind_ok]
    rfl

/-- A joint Fulu step is a block with an accepted payload. -/
theorem jointStep_fulu_ok_iff {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .fulu} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
    {s' : JointState P} :
    jointStep cfg ccfg bls ⟨.fulu, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok s' ↔
      ∃ req beacon' exec', NewPayloadRequest.ofBlock sb.message = .ok req ∧
        engineVerdict cfg .fulu exec req = .ok exec' ∧
        stateTransition { cfg := ccfg, blsActive := bls } beacon sb = .ok beacon' ∧
        s' = ⟨.fulu, beacon', exec'⟩ := by
  constructor
  · intro h
    simp only [jointStep] at h
    obtain ⟨p, hjt, h⟩ := Except.bind_eq_ok h
    obtain ⟨beacon', exec'⟩ := p
    dsimp only at h
    have hs' : Except.ok (⟨.fulu, beacon', exec'⟩ : JointState P) = Except.ok s' := h
    cases hs'
    rw [jointTransitionAt_ok_iff] at hjt
    obtain ⟨req, hreq, hverdict, hbeacon⟩ := hjt
    rw [ite_eq_right (by decide)] at hbeacon
    exact ⟨req, beacon', exec', hreq, hverdict, hbeacon, rfl⟩
  · rintro ⟨req, beacon', exec', hreq, hverdict, hbeacon, rfl⟩
    have hjt : jointTransitionAt cfg ccfg bls beacon exec sb = .ok (beacon', exec') := by
      rw [jointTransitionAt_ok_iff]
      refine ⟨req, hreq, hverdict, ?_⟩
      rw [ite_eq_right (by decide)]
      exact hbeacon
    simp only [jointStep, hjt, bind_ok]
    rfl

/-- A joint crossing step upgrades a below-the-fork-slot Electra state to Fulu
and applies a Fulu block with an accepted payload. -/
theorem jointStep_cross_ok_iff {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
    {s' : JointState P} :
    jointStep cfg ccfg bls ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok s' ↔
      beacon.slot.toNat ≤ fuluForkSlot (P := P) ccfg ∧
        fuluForkSlot (P := P) ccfg ≤ sb.message.slot.toNat ∧
        ∃ req forkSlot beacon1 beacon2 beacon' exec',
        U64.ofNat? (fuluForkSlot (P := P) ccfg) "joint step: Fulu fork slot" = .ok forkSlot ∧
        ((if beacon.slot < forkSlot then
            processSlots { cfg := ccfg, blsActive := bls } beacon forkSlot
          else pure beacon) = .ok beacon1) ∧
        upgradeToFulu ccfg beacon1 = .ok beacon2 ∧
        NewPayloadRequest.ofBlock sb.message = .ok req ∧
        engineVerdict cfg .fulu exec req = .ok exec' ∧
        ((if sb.message.slot == beacon2.slot then
            (do require (← verifyBlockSignature bls beacon2 sb)
                  "state_transition: verify_block_signature"
                let s ← processBlock { cfg := ccfg, blsActive := bls } beacon2 sb.message
                require (B256.beq sb.message.state_root (Ssz.hashTreeRoot s))
                  "state_transition: block.state_root"
                pure s)
          else stateTransition { cfg := ccfg, blsActive := bls } beacon2 sb) = .ok beacon') ∧
        s' = ⟨.fulu, beacon', exec'⟩ := by
  constructor
  · intro h
    simp only [jointStep] at h
    obtain ⟨_, hslotreq, h⟩ := Except.bind_eq_ok h
    have hslot : beacon.slot.toNat ≤ fuluForkSlot (P := P) ccfg ∧
        fuluForkSlot (P := P) ccfg ≤ sb.message.slot.toNat :=
      of_decide_eq_true (require_eq_ok_iff.mp hslotreq)
    obtain ⟨forkSlot, hforkSlot, h⟩ := Except.bind_eq_ok h
    by_cases hlt : beacon.slot < forkSlot
    · rw [ite_eq_left hlt] at h
      obtain ⟨beacon1, hps, h⟩ := Except.bind_eq_ok h
      obtain ⟨beacon2, hup, h⟩ := Except.bind_eq_ok h
      obtain ⟨p, hjt, h⟩ := Except.bind_eq_ok h
      obtain ⟨beacon', exec'⟩ := p
      dsimp only at h
      have hs' : Except.ok (⟨.fulu, beacon', exec'⟩ : JointState P) = Except.ok s' := h
      cases hs'
      rw [jointTransitionAt_ok_iff] at hjt
      obtain ⟨req, hreq, hverdict, hbeacon⟩ := hjt
      have hps_if : ((if beacon.slot < forkSlot then
          processSlots { cfg := ccfg, blsActive := bls } beacon forkSlot
        else pure beacon) = .ok beacon1) := by
        rw [ite_eq_left hlt]; exact hps
      exact ⟨hslot.1, hslot.2, req, forkSlot, beacon1, beacon2, beacon', exec', hforkSlot,
        hps_if, hup, hreq, hverdict, hbeacon, rfl⟩
    · rw [ite_eq_right hlt] at h
      obtain ⟨beacon1, hps, h⟩ := Except.bind_eq_ok h
      obtain ⟨beacon2, hup, h⟩ := Except.bind_eq_ok h
      obtain ⟨p, hjt, h⟩ := Except.bind_eq_ok h
      obtain ⟨beacon', exec'⟩ := p
      dsimp only at h
      have hs' : Except.ok (⟨.fulu, beacon', exec'⟩ : JointState P) = Except.ok s' := h
      cases hs'
      rw [jointTransitionAt_ok_iff] at hjt
      obtain ⟨req, hreq, hverdict, hbeacon⟩ := hjt
      have hps_if : ((if beacon.slot < forkSlot then
          processSlots { cfg := ccfg, blsActive := bls } beacon forkSlot
        else pure beacon) = .ok beacon1) := by
        rw [ite_eq_right hlt]; exact hps
      exact ⟨hslot.1, hslot.2, req, forkSlot, beacon1, beacon2, beacon', exec', hforkSlot,
        hps_if, hup, hreq, hverdict, hbeacon, rfl⟩
  · rintro ⟨hslot1, hslot2, req, forkSlot, beacon1, beacon2, beacon', exec', hforkSlot, hps,
      hup, hreq, hverdict, hbeacon, rfl⟩
    have hdec : decide (beacon.slot.toNat ≤ fuluForkSlot (P := P) ccfg ∧
        fuluForkSlot (P := P) ccfg ≤ sb.message.slot.toNat) = true :=
      decide_eq_true ⟨hslot1, hslot2⟩
    have hreq0 : require (decide (beacon.slot.toNat ≤ fuluForkSlot (P := P) ccfg ∧
        fuluForkSlot (P := P) ccfg ≤ sb.message.slot.toNat))
        "joint step: a Fulu block crossing from an Electra state" = .ok () := by
      rw [require_eq_ok_iff]; exact hdec
    have hjt : jointTransitionAt cfg ccfg bls beacon2 exec sb
        (sb.message.slot == beacon2.slot) = .ok (beacon', exec') := by
      rw [jointTransitionAt_ok_iff]
      exact ⟨req, hreq, hverdict, hbeacon⟩
    simp only [jointStep, hreq0, bind_ok, hforkSlot, bind_ok]
    by_cases hlt : beacon.slot < forkSlot
    · rw [ite_eq_left hlt] at hps ⊢
      simp only [hps, bind_ok, hup, bind_ok, hjt, bind_ok]
      rfl
    · rw [ite_eq_right hlt] at hps ⊢
      simp only [hps, bind_ok, hup, bind_ok, hjt, bind_ok]
      rfl

/-- Any other fork pair is refused. -/
theorem jointStep_refuses {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s : JointState P}
    {b : AnySignedBlock P}
    (hpair : (s.fork, b.1) ≠ (.electra, .electra) ∧ (s.fork, b.1) ≠ (.fulu, .fulu) ∧
      (s.fork, b.1) ≠ (.electra, .fulu)) :
    ∃ e, jointStep cfg ccfg bls s b = .error e := by
  obtain ⟨f, beacon, exec⟩ := s
  obtain ⟨g, sb⟩ := b
  cases f <;> cases g
  · simp only [jointStep]
    exact ⟨_, rfl⟩
  · simp only [jointStep]
    exact ⟨_, rfl⟩
  · simp only [jointStep]
    exact ⟨_, rfl⟩
  · simp only [jointStep]
    exact ⟨_, rfl⟩
  · simp only [jointStep]
    exact ⟨_, rfl⟩
  · exact absurd rfl hpair.1
  · exact absurd rfl hpair.2.2
  · simp only [jointStep]
    exact ⟨_, rfl⟩
  · simp only [jointStep]
    exact ⟨_, rfl⟩
  · simp only [jointStep]
    exact ⟨_, rfl⟩
  · exact absurd rfl hpair.2.1
  · simp only [jointStep]
    exact ⟨_, rfl⟩
  · simp only [jointStep]
    exact ⟨_, rfl⟩
  · simp only [jointStep]
    exact ⟨_, rfl⟩
  · simp only [jointStep]
    exact ⟨_, rfl⟩
  · simp only [jointStep]
    exact ⟨_, rfl⟩

end JauneConsensus
