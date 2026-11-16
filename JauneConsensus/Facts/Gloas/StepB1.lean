import JauneConsensus.Facts.Gloas.StepB3
import JauneConsensus.Facts.Gloas.FinalizedNotAhead
import JauneConsensus.Facts.Gloas.StepB5

/-!
# B1 over one Gloas joint step (goal `eip8282-gloas-cross-layer-v1`, MBS)

The per-step half of statements.md B1 (rev 3.1, `bls = true`), over ONE Gloas joint step at its
post-slots state `postSlots` (`GStepView`, WSL's `StepB246.lean`); the traces are BF1's, read at `postSlots`.

* **Creation provenance** (`processBlock_builderCreated_trace`, `GStepView.registration`): a
  builder record created at the step (`BuilderCreated postSlots post i`; equivalently from the
  pre-step state, whose builders `postSlots` keeps) was created by the builder deposit request at
  deposit-trace position `k`, classified `register i req.amount` at `trD[k]` under the real BLS
  (`bls = true`), with a `0xB0` prefix, a signature verifying under `DOMAIN_BUILDER_DEPOSIT`, and
  the fresh record at `trD[k+1]` with `execution_address = credentials[12:]`.
* **Same-payload register then top-up** (in `GStepView.registration`): after the remaining
  deposits of the payload, builder `i` is the fresh record with balance
  `req.amount + Σ later 0xB0 top-ups for its pubkey`.
* **The fork clause** (`jointStepG_crossing_onboarding`): at the crossing step the builders are
  exactly `upgrade_to_gloas`'s onboarding (`upgraded.builders`), all at `FAR_FUTURE_EPOCH`, and no
  record is created by the first block.
-/

namespace JauneConsensus.Facts.Gloas

open Jaune JauneConsensus JauneConsensus.Facts

variable {P : Preset}

/-! ## Trace arithmetic -/

/-- If a function of a list's first and last elements differs, it differs across some
consecutive pair. -/
theorem exists_step_ne {α β : Type} (g : α → β) :
    ∀ (tr : List α) (a z : α), tr[0]? = some a → tr.getLast? = some z → g a ≠ g z →
      ∃ k x y, tr[k]? = some x ∧ tr[k + 1]? = some y ∧ g x ≠ g y
  | [], a, z, h0, _, _ => by simp at h0
  | [x], a, z, h0, hl, hne => by
    simp at h0 hl; subst h0; subst hl; exact absurd rfl hne
  | x :: y :: rest, a, z, h0, hl, hne => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst h0
    by_cases hxy : g x = g y
    · have hl' : (y :: rest).getLast? = some z := by
        rw [List.getLast?_cons_cons] at hl; exact hl
      obtain ⟨k, u, v, hu, hv, huv⟩ :=
        exists_step_ne g (y :: rest) y z rfl hl' (by rw [← hxy]; exact hne)
      exact ⟨k + 1, u, v, by simpa using hu, by simpa using hv, huv⟩
    · exact ⟨0, x, y, rfl, rfl, hxy⟩

/-- The last state of a nonempty trace is its last element. -/
theorem getLast?_of_traceLast {σ : Type} {tr : List σ} (h : tr ≠ []) (d : σ) :
    tr.getLast? = some (traceLast d tr) := by
  cases tr with
  | nil => exact absurd rfl h
  | cons x xs => simp [traceLast, List.getLast?_cons]

/-- The suffix of a scan from its `k`-th state folds to the scan's last state. -/
theorem scanM_ok_drop {σ α : Type} {f : σ → α → M σ} :
    ∀ (xs : List α) {s : σ} {tr : List σ} (k : Nat) {m : σ}, scanM f s xs = .ok tr →
      tr[k]? = some m → (xs.drop k).foldlM f m = .ok (traceLast s tr)
  | xs, s, tr, 0, m, h, hk => by
    rw [scanM_ok_head h] at hk; cases hk
    simpa using scanM_ok_foldlM h
  | [], s, tr, k + 1, m, h, hk => by
    simp only [scanM, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp at hk
  | a :: xs, s, tr, k + 1, m, h, hk => by
    simp only [scanM, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i s' hs'
      split at h
      · cases h
      · rename_i rest hrest
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [List.getElem?_cons_succ] at hk
        have := scanM_ok_drop xs k hrest hk
        simp only [List.drop_succ_cons]
        rw [this]
        have hne := scanM_ok_ne_nil hrest
        congr 1
        cases rest with
        | nil => exact absurd rfl hne
        | cons x xs' => simp [traceLast, List.getLast?_cons]

/-! ## Exits keep pubkeys -/

/-- A builder exit request keeps every slot's pubkey (it writes only `withdrawable_epoch`). -/
theorem exitReq_pubkeys {cfg : Config} {m m' : Gloas.BeaconState P}
    {r : Gloas.BuilderExitRequest} (h : Gloas.processBuilderExitRequest cfg m r = .ok m') (j : Nat) :
    (m'.builders.toArray[j]?).map (·.pubkey) = (m.builders.toArray[j]?).map (·.pubkey) := by
  rcases (Inv.exitReq_cases h).2 with heq | ⟨i, b, w, hb, hb', _, _, _, _, hoth⟩
  · rw [heq]
  · by_cases hji : j = i
    · subst hji; rw [hb, hb']; rfl
    · rw [hoth j hji]

/-! ## B1: where a created record comes from -/

/-- **B1 provenance at `process_block`.** If `process_block` creates a builder record at `i`
(`BuilderCreated st post i`), then some builder deposit request at deposit-trace position `k`
created it between `trD[k]` and `trD[k+1]`: the exit loop, the suffix and the rest of the block
keep every pubkey, so the pubkey at `i` changed inside the deposit loop, at some request. -/
theorem processBlock_builderCreated_trace {ctx : Ctx} {st post : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} (h : Gloas.processBlock ctx st b.message = .ok post) {i : Nat}
    (hcr : BuilderCreated st post i) :
    ∃ trD k r m m', builderDepositTrace ctx.cfg ctx.blsActive st b = .ok trD ∧
      (blockBuilderDeposits b)[k]? = some r ∧ trD[k]? = some m ∧ trD[k + 1]? = some m' ∧
      Gloas.processBuilderDepositRequest ctx m r = .ok m' ∧ BuilderCreated m m' i := by
  obtain ⟨mid, hmid, -, hmap⟩ := processBlock_after_parent ctx st b.message post h
  have hpkpost : (post.builders.toArray[i]?).map (·.pubkey) =
      (mid.builders.toArray[i]?).map (·.pubkey) := by
    have := congrArg (Option.map Prod.fst) (hmap i)
    simpa [Option.map_map, Function.comp_def] using this
  have hne : (st.builders.toArray[i]?).map (·.pubkey) ≠ (mid.builders.toArray[i]?).map (·.pubkey) := by
    rw [← hpkpost]; exact hcr.2
  obtain ⟨trD, trE, hD, hE, -, hEmpty, hFull⟩ := processParentExecutionPayload_traces hmid
  cases hflag : (b.message.body.signed_execution_payload_bid.message.parent_block_hash !=
      st.latest_execution_payload_bid.block_hash)
  case true =>
    obtain ⟨rfl, -, -⟩ := hEmpty hflag
    exact absurd rfl hne
  case false =>
  have hsuf := hFull hflag
  obtain ⟨s0, h0, hsD⟩ := builderDepositTrace_scan hD
  rw [← Gloas.processBuilderDepositRequest_ctx] at hsD
  obtain ⟨trD', hD', hsE, -⟩ := builderExitTrace_ok hE
  rw [hD] at hD'; cases hD'
  have hneD := scanM_ok_ne_nil hsD
  have hneE := scanM_ok_ne_nil hsE
  -- the exit loop keeps the pubkeys
  have hE0 : trE[0]? = some (traceLast st trD) := scanM_ok_head hsE
  have hpkE : ∀ (k : Nat) (x : Gloas.BeaconState P), trE[k]? = some x →
      ∀ j : Nat, (x.builders.toArray[j]?).map (fun c : Gloas.Builder => c.pubkey) =
        ((traceLast st trD).builders.toArray[j]?).map (fun c : Gloas.Builder => c.pubkey) :=
    scanM_inv (fun x : Gloas.BeaconState P => ∀ j : Nat,
        (x.builders.toArray[j]?).map (fun c : Gloas.Builder => c.pubkey) =
        ((traceLast st trD).builders.toArray[j]?).map (fun c : Gloas.Builder => c.pubkey))
      (fun x _ y hI hy j => (exitReq_pubkeys hy j).trans (hI j)) _ (fun _ => rfl) hsE
  have hmidb : mid.builders = (traceLast st trE).builders := by
    rw [applyParentSuffix_builders hsuf]
  have hlastE : trE[trE.length - 1]? = some (traceLast st trE) := by
    rw [← List.getLast?_eq_getElem?]; exact getLast?_of_traceLast hneE st
  have hmidpk : (mid.builders.toArray[i]?).map (·.pubkey) =
      ((traceLast st trD).builders.toArray[i]?).map (·.pubkey) := by
    rw [hmidb]; exact hpkE _ _ hlastE i
  have hs0 : s0.builders = st.builders := builderDepositTrace_head_builders hD h0
  have hne' : (s0.builders.toArray[i]?).map (fun c : Gloas.Builder => c.pubkey) ≠
      ((traceLast st trD).builders.toArray[i]?).map (fun c : Gloas.Builder => c.pubkey) := by
    rw [hs0, ← hmidpk]; exact hne
  obtain ⟨k, m, m', hm, hm', hmm⟩ :=
    exists_step_ne (fun x : Gloas.BeaconState P =>
        (x.builders.toArray[i]?).map (fun c : Gloas.Builder => c.pubkey))
      trD s0 (traceLast st trD) h0 (getLast?_of_traceLast hneD st) hne'
  have hk : k < (blockBuilderDeposits b).length := by
    have hl := scanM_ok_length hsD
    have := (List.getElem?_eq_some_iff.mp hm').1
    omega
  obtain ⟨r, hr⟩ : ∃ r, (blockBuilderDeposits b)[k]? = some r :=
    ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨m1, m1', hm1, hm1', hcall⟩ := scanM_ok_step hsD k r hr
  rw [hm] at hm1; cases hm1
  rw [hm'] at hm1'; cases hm1'
  refine ⟨trD, k, r, m, m', hD, hr, hm, hm', hcall, ?_, hmm⟩
  -- the record at `i` exists after the call: the registry never shrinks
  obtain ⟨_, hsz, _⟩ := processBuilderDepositRequest_at hcall i
  cases hc' : m'.builders.toArray[i]? with
  | some _ => rfl
  | none =>
    exfalso
    apply hmm
    simp only [hc', Option.map_none]
    cases hc : m.builders.toArray[i]? with
    | none => rfl
    | some _ =>
      have := (Array.getElem?_eq_some_iff.mp hc).1
      have : i < m'.builders.toArray.size := by omega
      rw [Array.getElem?_eq_getElem this] at hc'
      cases hc'

/-- **B1 main, per step (`bls = true`).** At a successful Gloas step with `bls = true`, post-slots
state `postSlots` and post-state `post`, a builder record created at `i`
(`BuilderCreated postSlots post i`) was created by the builder deposit request `req` at
deposit-trace position `k` of the block's `parent_execution_requests`:

* at the deposit-trace state `trD[k]`, `req` is classified `register i req.amount` (a new pubkey
  with a valid signature) under the real BLS;
* its credentials carry the `0xB0` prefix, and its signature verifies (`blsVerify true`) over the
  deposit message under `DOMAIN_BUILDER_DEPOSIT` (`builderDepositDomain`, CL:2276-2284);
* `trD[k+1]` holds at `i` the fresh record (`freshBuilder`: `version = 0`,
  `execution_address = credentials[12:]`, `balance = req.amount`, `deposit_epoch` the epoch of
  `trD[k]`'s slot, `withdrawable_epoch = FAR_FUTURE_EPOCH`);
* **register then top-up**: after the remaining deposits (the last deposit-trace state), builder
  `i` is that record with balance `req.amount + Σ amounts of the later 0xB0 deposits for its
  pubkey`. Needs `2 ≤ SLOTS_PER_EPOCH`. -/
theorem GStepView.registration (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    {cfg : ChainConfig} {ccfg : Config}
    {preB postB : Gloas.BeaconState P} {preExec postExec : BlockChain}
    {preParent postParent : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (V : GStepView cfg ccfg true preB preExec preParent b env? postB postExec postParent)
    {i : Nat} (created : BuilderCreated V.postSlots postB i) :
    ∃ (k : Nat) (req : Gloas.BuilderDepositRequest) (trD : List (Gloas.BeaconState P))
      (m m' : Gloas.BeaconState P) (dom : Domain) (addr : ExecutionAddress) (e : Epoch) (bal : U64),
      (blockBuilderDeposits b)[k]? = some req ∧
      builderDepositTrace ccfg true V.postSlots b = .ok trD ∧ trD[k]? = some m ∧ trD[k + 1]? = some m' ∧
      Gloas.processBuilderDepositRequest (gloasCtx ccfg true) m req = .ok m' ∧
      classifyBuilderDeposit ccfg true m req = .ok (.register i req.amount) ∧
      req.withdrawal_credentials.toBytes.head? = some 0xB0 ∧
      builderDepositDomain ccfg = some dom ∧
      blsVerify true req.pubkey (computeSigningRoot (builderDepositMessage req) dom) req.signature = true ∧
      Jaune.Bytes.toAdr? (req.withdrawal_credentials.toBytes.drop 12) = some addr ∧
      computeEpochAtSlot P m.slot = .ok e ∧
      m'.builders.toArray[i]? = some (freshBuilder req.pubkey addr req.amount e) ∧
      (traceLast V.postSlots trD).builders.toArray[i]? =
        some { freshBuilder req.pubkey addr req.amount e with balance := bal } ∧
      bal.toNat = req.amount.toNat + ((((blockBuilderDeposits b).drop (k + 1)).filter
        (fun r' => r'.pubkey == req.pubkey &&
          Gloas.isBuilderWithdrawalCredential r'.withdrawal_credentials)).map
          (·.amount.toNat)).sum := by
  have hpb := V.processBlock
  obtain ⟨trD, k, req, m, m', hD, hr, hm, hm', hcall, hcr⟩ :=
    processBlock_builderCreated_trace hpb created
  obtain ⟨hpre, -, ⟨dom, hdom, hv⟩, hcl, addr, e, haddr, he, hat⟩ :=
    processBuilderDepositRequest_created (ctx := gloasCtx ccfg true) rfl hcall hcr
  obtain ⟨s0, -, hsD⟩ := builderDepositTrace_scan hD
  rw [← Gloas.processBuilderDepositRequest_ctx] at hsD
  have hrest := scanM_ok_drop _ (k + 1) hsD hm'
  have hfirst : trD[0]? = some s0 := scanM_ok_head hsD
  obtain ⟨addr', e', bal, haddr', he', hat1, hat2, hbal⟩ :=
    register_then_topUp hspe (ctx := gloasCtx ccfg true) hcl hcall hrest
  rw [haddr] at haddr'; cases haddr'
  rw [he] at he'; cases he'
  have htl : traceLast s0 trD = traceLast V.postSlots trD :=
    traceLast_ne_nil (scanM_ok_ne_nil hsD) s0 V.postSlots
  rw [htl] at hat2
  exact ⟨k, req, trD, m, m', dom, addr, e, bal, hr, hD, hm, hm', hcall, hcl, hpre, hdom, hv, haddr,
    he, hat, hat2, hbal⟩

/-! ## B1 at the crossing: the onboarding -/

/-- **B1's fork clause, per step.** At a successful crossing step, the builders of the post-slots
state are exactly `upgrade_to_gloas`'s (`upgraded.builders`, the onboarding of
`onboard_builders_from_pending_deposits`), every builder of the post-state is at
`FAR_FUTURE_EPOCH` with the pubkey of the same slot of `upgraded`, the registry keeps its length,
and the first block creates no record: every builder record after the crossing is one of the
onboarding's. -/
theorem jointStepG_crossing_onboarding {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .fulu} {exec : BlockChain} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} {s' : GJointState P}
    (h : jointStepG cfg ccfg bls (.pre ⟨.fulu, beacon, exec⟩) (.gloas b) env? = .ok s') :
    ∃ (atFork : BeaconState P .fulu) (upgraded postSlots post : Gloas.BeaconState P)
      (parent' : ParentPayload P),
      Gloas.upgradeToGloas (gloasCtx ccfg bls) atFork = .ok upgraded ∧
      Gloas.crossFromFulu (gloasCtx ccfg bls) beacon = .ok upgraded ∧
      s' = .gloas post exec parent' ∧
      postSlots.builders = upgraded.builders ∧ BuildersFar upgraded ∧ BuildersFar post ∧
      post.builders.toArray.size = upgraded.builders.toArray.size ∧
      (∀ j : Nat, (post.builders.toArray[j]?).map (fun c : Gloas.Builder => c.pubkey) =
        (upgraded.builders.toArray[j]?).map (fun c : Gloas.Builder => c.pubkey)) ∧
      (∀ i, ¬ BuilderCreated postSlots post i) := by
  obtain ⟨upgraded, postSlots, post, parent', hup, _, _, hs, hbs, _, _, _, hfp, hpk, _, hnc⟩ :=
    jointStepG_crossing_noExit h
  obtain ⟨atFork, hat⟩ := crossFromFulu_upgrade hup
  obtain ⟨hfar, _⟩ := upgradeToGloas_builders hat
  refine ⟨atFork, upgraded, postSlots, post, parent', hat, hup, hs, hbs, hfar, hfp,
    by rw [hpk.1, hbs], fun j => ?_, hnc⟩
  have := congrArg (Option.map Prod.fst) (hpk.2 j)
  simp only [Option.map_map, Function.comp_def] at this
  rw [← hbs]; exact this

/-! ## B1's post-state clause (G3d, under FinalizedNotAhead) -/

section PostState

open Inv

/-- The parent prefix (the payment settlement and the validator request loops) keeps the triple
`I3`, from G3-05, G3-03, G3-04, G3-08 and LatestBidBuilderActive (the prefix half of
`parent_I3`). -/
theorem prefix_I3 {ctx : Ctx} {s a : Gloas.BeaconState P} {r : Gloas.ExecutionRequests}
    (hA : LatestBidBuilderActive s)
    (ha : Gloas.applyParentPrefix ctx s r = .ok a)
    (g5 : PendingCovered s) (g3 : PendingRefsInRange s) (g4 : ExitedHaveNoPending s)
    (g8 : LatestBidCoherence s) : I3 a := by
  obtain ⟨x, fx, hx⟩ := applyParentPrefix_split ha
  have px : I3 x := by
    rcases hx with ⟨idx, hset⟩ | ⟨hv, rfl, hc1, hc2⟩ | rfl
    · obtain ⟨hb, hr, hp⟩ := settle_refs_pend hset
      refine ⟨fun i c hc => ?_, hr g3, x04_of hb (fun i => (hp i).le) g4⟩
      rw [hb] at hc; rw [hp]; exact pendLe_of_covered g5 i c hc
    · obtain ⟨b, hb, hfar⟩ := hA hv
      have hnone : bidIndex s = none := by
        simp only [bidIndex, g8.1, hc1, hc2, ↓reduceIte]
      have hnl : ¬ BidLive s := by
        rintro ⟨_, _, hk, _⟩; rw [hnone] at hk; cases hk
      refine ⟨fun i c hc => ?_, refs_transfer (s := s) (s' := directAppend s) (le_refl _)
        (fun w hw => ?_) (fun j p hj hne => Or.inl ⟨p, hj, hne, rfl⟩) g3, fun i c hc hne => ?_⟩
      · change s.builders.toArray[i]? = some c at hc
        rw [directAppend_pend]
        have := g5 i c hc
        rw [expo_of_not_live hnl] at this
        exact this
      · simp only [directAppend, ProgressiveListS.push, Array.toList_push, List.mem_append,
          List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact Or.inl hw
        · exact Or.inr (Array.getElem?_eq_some_iff.mp hb).1
      · change s.builders.toArray[i]? = some c at hc
        rw [directAppend_pend]
        have h0 := g4 i c hc hne
        by_cases hi : s.latest_execution_payload_bid.builder_index.toNat = i
        · subst hi; rw [hb] at hc; cases hc; exact absurd hfar hne
        · have : wAmt i (bidWithdrawal s.latest_execution_payload_bid) = 0 := by
            unfold wAmt bidWithdrawal; rw [if_neg hi]
          omega
    · exact ⟨pendLe_of_covered g5, g3, g4⟩
  exact ⟨pendLe_of_eqs fx.1 fx.2.2.1 fx.2.1 px.1, refs_of_inv fx px.2.1,
    x04_of_eqs fx.1 fx.2.2.1 fx.2.1 px.2.2⟩

/-- **The exit loop keeps a not-yet-active builder.** If builder `i` is `R` at the start of an exit
loop and the finalized checkpoint is not after `R.deposit_epoch`, no request of the loop
initiates `i`'s exit (`is_active_builder` needs `deposit_epoch < finalized_checkpoint.epoch`, and
no request moves the checkpoint), so every state of the loop has `R` at `i`, with the start's
finalized checkpoint, slot and builder withdrawals. -/
theorem exitLoop_keeps {cfg : Config} {i : Nat} {R : Gloas.Builder}
    (rs : List Gloas.BuilderExitRequest) {x0 : Gloas.BeaconState P} {tr : List (Gloas.BeaconState P)}
    (h : scanM (Gloas.processBuilderExitRequest cfg) x0 rs = .ok tr)
    (hR : x0.builders.toArray[i]? = some R)
    (hfin : x0.finalized_checkpoint.epoch.toNat ≤ R.deposit_epoch.toNat) :
    ∀ (k : Nat) (x : Gloas.BeaconState P), tr[k]? = some x →
      x.builders.toArray[i]? = some R ∧ FinSlot x0 x ∧
        x.builder_pending_withdrawals = x0.builder_pending_withdrawals := by
  refine scanM_inv (fun x : Gloas.BeaconState P => x.builders.toArray[i]? = some R ∧ FinSlot x0 x ∧
      x.builder_pending_withdrawals = x0.builder_pending_withdrawals)
    (fun x a y ⟨hx, hfx, hwx⟩ hy => ?_) rs ⟨hR, finSlot.refl _, rfl⟩ h
  refine ⟨?_, finSlot.trans hfx (processBuilderExitRequest_fs _ _ _ _ hy),
    ((processBuilderExitRequest_frame hy).2.2.2.2.1).trans hwx⟩
  have h0 := hy
  rw [processBuilderExitRequest_eq] at h0
  obtain ⟨o, hco, -⟩ := bind_eq_ok_iff.mp h0
  obtain ⟨hign, hini⟩ := classifyBuilderExit_effect hco hy
  by_cases ho : ∃ j, o = .initiate j
  · obtain ⟨j, rfl⟩ := ho
    obtain ⟨b, e, w, hb, -, -, -, -, hoth, -⟩ := hini j rfl
    by_cases hij : i = j
    · subst hij
      exfalso
      rcases classifyBuilderExit_inv hco with ⟨-, hc⟩ | ⟨i', b0, bi, -, hb0, -, hcase⟩
      · cases hc
      · rcases hcase with ⟨-, hc⟩ | ⟨-, -, hc⟩ | ⟨⟨hlt, -⟩, -, p, -, hp⟩
        · cases hc
        · cases hc
        · rcases hp with ⟨-, hc⟩ | ⟨-, hc⟩
          · cases hc
          · cases hc
            rw [hx] at hb0; cases hb0
            have hlt' : R.deposit_epoch.toNat < x.finalized_checkpoint.epoch.toNat := hlt
            rw [hfx.1] at hlt'
            omega
    · rw [hoth i hij]; exact hx
  · rw [hign (fun j hj => ho ⟨j, hj⟩)]; exact hx

/-- **A builder that is not exiting and has nothing pending is routed nothing** by the expected
withdrawals: the builder-withdrawal phase routes it its `pendW` prefix (`0`), the validator phases
route no builder (N7's `validatorsBound`), and the builders sweep pays only withdrawable
builders. -/
theorem expected_routed_fresh (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {s2 : Gloas.BeaconState P}
    {ex : Gloas.ExpectedWithdrawals} (hex : Gloas.getExpectedWithdrawals s2 = .ok ex)
    {i : Nat} {R : Gloas.Builder}
    (hR : s2.builders.toArray[i]? = some R) (hfar : R.withdrawable_epoch = FAR_FUTURE_EPOCH)
    (hp : pendW s2.builder_pending_withdrawals.toArray.toList i = 0)
    (hrefs : ∀ w ∈ s2.builder_pending_withdrawals.toArray.toList, w.builder_index.toNat < 2 ^ 40)
    (hvb : s2.validators.toArray.size ≤ 2 ^ 40) (hbb : s2.builders.toArray.size ≤ 2 ^ 40)
    {bi : U64} (hbiN : bi.toNat = i) : routedSum bi ex.withdrawals.toList = 0 := by
  obtain ⟨bw, pw, sw, vw, p2, p3, p4, i1, i2, i3, i4, n2, n3, n4, e1, e2, e3, e4, hws⟩ :=
    getExpectedWithdrawals_parts hex
  have hi : i < 2 ^ 40 := lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hR).1 hbb
  have r1 : routedSum bi bw.toList = 0 := by
    obtain ⟨-, hr⟩ := routed_builderWithdrawals e1 hrefs (bi := bi) (by omega)
    rw [hr, hbiN]
    have := pendW_take_drop s2.builder_pending_withdrawals.toArray.toList bw.size i
    omega
  have r2 := routedSum_validatorPhase (getPendingPartialWithdrawals_inRange _ _ _ _ e2) hvb bi
  have r4 := routedSum_validatorPhase (getValidatorsSweepWithdrawals_inRange _ _ _ _ e4) hvb bi
  have r3 : routedSum bi sw.toList = 0 := by
    refine routedSum_zero (fun w hw hRt => ?_)
    obtain ⟨k, hk, hkw⟩ := List.mem_iff_getElem.mp hw
    have hk' : k < sw.size := by simpa using hk
    have hkw' : sw[k] = w := by rw [← hkw]; simp
    obtain ⟨bj, b', ep, he, hcv, hb', hwe, -⟩ := getBuildersSweepWithdrawals_provenance e3 k hk'
    rw [hkw'] at hcv
    have hbj : bj.toNat < 2 ^ 40 := lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hb').1 hbb
    have hij := routes_inj hRt hcv (by omega) hbj
    rw [← hij, hbiN, hR] at hb'
    cases hb'
    have hwe' : R.withdrawable_epoch.toNat ≤ ep.toNat := hwe
    have hel := epoch_lt_far hspe s2
    rw [← getCurrentEpoch_toNat he] at hel
    rw [hfar] at hwe'
    omega
  rw [hws, routedSum_append, routedSum_append, routedSum_append, r1, r2, r3, r4]

/-- **`process_withdrawals` keeps a builder that is not exiting and has nothing pending**,
balance included (`expected_routed_fresh`). -/
theorem withdrawals_keep_fresh (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {s2 s3 : Gloas.BeaconState P}
    (h : Gloas.processWithdrawals s2 = .ok s3) {i : Nat} {R : Gloas.Builder}
    (hR : s2.builders.toArray[i]? = some R) (hfar : R.withdrawable_epoch = FAR_FUTURE_EPOCH)
    (hp : pendW s2.builder_pending_withdrawals.toArray.toList i = 0)
    (hrefs : ∀ w ∈ s2.builder_pending_withdrawals.toArray.toList, w.builder_index.toNat < 2 ^ 40)
    (hvb : s2.validators.toArray.size ≤ 2 ^ 40) (hbb : s2.builders.toArray.size ≤ 2 ^ 40) :
    s3.builders.toArray[i]? = some R := by
  rcases processWithdrawals_cases h with rfl | ⟨ex, t, hex, ht, hb3, -, -⟩
  · exact hR
  have hi : i < 2 ^ 40 := lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hR).1 hbb
  obtain ⟨bi, hbi⟩ := (U64.ofNat?_ok_iff (site := "BuilderIndex")).mpr (by omega : i < 2 ^ 64)
  have hbiN : bi.toNat = i := U64.toNat_ofNat? hbi
  have hr0 := expected_routed_fresh hspe hex hR hfar hp hrefs hvb hbb hbiN
  obtain ⟨b', hb', hbe, hbal⟩ := applyWithdrawals_builder_balance ht (by
    show s2.builders.toArray.size ≤ 2 ^ 40; omega) (bi := bi) (by rw [hbiN]; exact hR)
    (by rw [hr0]; omega)
  rw [hr0] at hbal
  rw [hb3, ← hbiN, hb', hbe]
  have : b'.balance = R.balance := U64.ext_toNat (by omega)
  rw [this]

/-- **A freshly registered builder survives the rest of its step** (any `bls`; G3d). At a Gloas
step whose pre-state satisfies FinalizedNotAhead (with the G3 invariants and the N7 bounds), let the
deposit request at deposit-trace position `k` (state `m = trD[k]`) be classified `register i a`,
and let builder `i` be `R` at the end of the deposit loop, with `withdrawable_epoch = FAR` and
`deposit_epoch` the epoch of `m`'s slot. Then `i` is `R` at the step's post-state, and the step's
withdrawals route nothing to `i`.

Why: `R` is not active (`deposit_epoch` is the current epoch, and FinalizedNotAhead keeps the
finalized checkpoint at or before it), so no exit request of the payload initiates its exit; it has
nothing pending (`pend = 0` at its registration, by G3-03 for an appended slot and G3-04 for a
reused one, and the later phases before the withdrawals add no pending withdrawal); and it is not
withdrawable, so the builders sweep skips it. -/
theorem GStepView.fresh_survives (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {preB postB : Gloas.BeaconState P} {preExec postExec : BlockChain}
    {preParent postParent : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    (fna : FinalizedNotAhead preB)
    (g5 : PendingCovered preB) (g3 : PendingRefsInRange preB) (g4 : ExitedHaveNoPending preB)
    (g7 : NoLiveWeightOnLatestBid preB) (g8 : LatestBidCoherence preB) (fe : FutureEmpty preB)
    (hA : LatestBidBuilderActive preB)
    (validatorsBound : postB.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : postB.builders.toArray.size ≤ 2 ^ 40)
    {trD : List (Gloas.BeaconState P)} (hD : builderDepositTrace ccfg bls V.postSlots b = .ok trD)
    {k i : Nat} {m : Gloas.BeaconState P} {req : Gloas.BuilderDepositRequest} {a : U64}
    (hm : trD[k]? = some m) (hr : (blockBuilderDeposits b)[k]? = some req)
    (hcl : classifyBuilderDeposit ccfg bls m req = .ok (.register i a))
    {R : Gloas.Builder} {e : Epoch} (he : computeEpochAtSlot P m.slot = .ok e)
    (hat2 : (traceLast V.postSlots trD).builders.toArray[i]? = some R)
    (hfar : R.withdrawable_epoch = FAR_FUTURE_EPOCH) (hdep : R.deposit_epoch = e) :
    postB.builders.toArray[i]? = some R ∧
      ∃ ws : List Withdrawal, stepWithdrawals ccfg bls V.postSlots b.message = .ok ws ∧
        ∀ bi : U64, bi.toNat = i → routedSum bi ws = 0 := by
  set S := V.postSlots with hS
  -- the post-slots state
  have fnaS := processSlots_finalizedNotAhead V.slots fna
  have hs := processSlots_pendingCovered quorumPositive (by omega) V.slots ⟨g5, g7, fe⟩
  have g3' := processSlots_pendingRefsInRange quorumPositive V.slots g3
  have g4' := processSlots_exitedHaveNoPending quorumPositive V.slots g4
  have g8' := processSlots_latestBidCoherence V.slots g8
  have hA' := processSlots_latestBidBuilderActive V.slots hA
  -- the deposit trace starts at the parent prefix
  rcases builderDepositTrace_ok hD with ⟨hnil, -, -⟩ | ⟨s0, h0pre, hsD⟩
  · rw [hnil] at hr; simp at hr
  have f0 : FinSlot S s0 := applyParentPrefix_fs _ _ _ _ h0pre
  have i0 : I3 s0 := prefix_I3 hA' h0pre hs.1 g3' g4' g8'
  have trI := scanM_inv (fun x : Gloas.BeaconState P => FinSlot S x ∧ I3 x ∧
      x.builder_pending_withdrawals = s0.builder_pending_withdrawals)
    (fun x a y ⟨hfx, hIx, hwx⟩ hy => ⟨finSlot.trans hfx (processBuilderDepositRequest_fs _ _ _ _ hy),
      depReq_I3 hspe hy hIx, ((processBuilderDepositRequest_frame hy).2.2.2.2.1).trans hwx⟩)
    _ ⟨f0, i0, rfl⟩ hsD
  obtain ⟨fm, Im, wm⟩ := trI k m hm
  -- the fresh slot has nothing pending at its registration
  have hpm : pend m i = 0 := by
    rcases classifyBuilderDeposit_inv hcl with ⟨-, hc⟩ | ⟨-, _, _, _, _, hc⟩ |
        ⟨-, -, -, -, ⟨-, hc⟩ | ⟨-, -, idx, -, hidx, hc⟩⟩
    · cases hc
    · cases hc
    · cases hc
    · cases hc
      obtain ⟨ep, hep, hcase⟩ := getIndexForNewBuilder_spec hidx
      rcases hcase with hsz | ⟨b0, hb0, hwe, -⟩
      · exact pend_zero_of_ge Im.2.1 (by omega)
      · refine Im.2.2 _ b0 hb0 ?_
        intro hf
        have hwe' : b0.withdrawable_epoch.toNat ≤ ep.toNat := hwe
        rw [hf, getCurrentEpoch_toNat hep] at hwe'
        have := epoch_lt_far hspe m
        omega
  have hpWm : pendW m.builder_pending_withdrawals.toArray.toList i = 0 := by
    unfold pend at hpm; omega
  -- the last deposit-trace state
  have hneD := scanM_ok_ne_nil hsD
  have hlastD : trD[trD.length - 1]? = some (traceLast S trD) := by
    rw [← List.getLast?_eq_getElem?]; exact getLast?_of_traceLast hneD S
  obtain ⟨fL, -, wL⟩ := trI _ _ hlastD
  -- the deposit epoch is the current one, at or after the finalized checkpoint
  have hfin : (traceLast S trD).finalized_checkpoint.epoch.toNat ≤ R.deposit_epoch.toNat := by
    rw [hdep, computeEpochAtSlot_toNat he, fm.2, fL.1]
    exact fnaS
  -- the block, phase by phase
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    processBlock_phases V.processBlock
  obtain ⟨trD', trE, hD', hE, -, hEmpty, hFull⟩ := processParentExecutionPayload_traces h1
  change builderDepositTrace ccfg bls S b = _ at hD'
  rw [hD] at hD'; cases hD'
  obtain ⟨trD', hD', hsE, -⟩ := builderExitTrace_ok hE
  change builderDepositTrace ccfg bls S b = _ at hD'
  rw [hD] at hD'; cases hD'
  have exK := exitLoop_keeps _ hsE hat2 hfin
  have hneE := scanM_ok_ne_nil hsE
  have hlastE : trE[trE.length - 1]? = some (traceLast S trE) := by
    rw [← List.getLast?_eq_getElem?]; exact getLast?_of_traceLast hneE S
  obtain ⟨hRE, -, wE⟩ := exK _ _ hlastE
  -- the parent settlement is FULL (the block carries a builder deposit)
  cases hflag : (b.message.body.signed_execution_payload_bid.message.parent_block_hash !=
      S.latest_execution_payload_bid.block_hash)
  case true =>
    obtain ⟨-, htr, -⟩ := hEmpty hflag
    have hl := builderDepositTrace_length hD
    rw [htr] at hl
    have : (blockBuilderDeposits b).length = 0 := by simpa using hl
    rw [List.length_eq_zero_iff.mp this] at hr; simp at hr
  case false =>
  have hsuf := hFull hflag
  obtain ⟨hb1, -, hw1, -⟩ := applyParentSuffix_post hsuf
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have e2b : s2.builders = s1.builders := by rw [hm2]
  have e2w : s2.builder_pending_withdrawals = s1.builder_pending_withdrawals := by rw [hm2]
  have hR2 : s2.builders.toArray[i]? = some R := by rw [e2b, hb1]; exact hRE
  have hw2 : s2.builder_pending_withdrawals = m.builder_pending_withdrawals := by
    rw [e2w, hw1, wE, wL, wm]
  -- the refs of the withdrawals state, from `parent_I3`
  obtain ⟨-, r1, -⟩ := parent_I3 hspe hA' h1 hs.1 g3' g4' g8'
  have w3 := processWithdrawals_wFrame _ _ h3
  have b4 := processExecutionPayloadBid_post h4
  have c := afterBid_core h5 h6 h7 h8
  have hpost : postB.builders = s3.builders := by rw [c.1, b4.2.2.2.2.1]
  have bb2 : s2.builders.toArray.size ≤ 2 ^ 40 := by
    have : postB.builders.toArray.size = s2.builders.toArray.size := by
      rw [hpost]; exact w3.2.2.2.2.2.1
    omega
  have vb2 : s2.validators.toArray.size ≤ 2 ^ 40 := by
    have va : postB.validators.toArray.size = s3.validators.toArray.size :=
      afterWithdrawals_vlen h4 h5 h6 h7 h8
    have vb' : s3.validators.toArray.size = s2.validators.toArray.size :=
      processWithdrawals_vlen _ _ h3
    omega
  have hrefs : ∀ w ∈ s2.builder_pending_withdrawals.toArray.toList,
      w.builder_index.toNat < 2 ^ 40 := fun w hw => by
    rw [e2w] at hw
    have := r1.1 w hw
    rw [← e2b] at this
    omega
  have hp2 : pendW s2.builder_pending_withdrawals.toArray.toList i = 0 := by rw [hw2]; exact hpWm
  refine ⟨by rw [hpost]; exact withdrawals_keep_fresh hspe h3 hR2 hfar hp2 hrefs vb2 bb2, ?_⟩
  have hsw : stepWithdrawals ccfg bls V.postSlots b.message =
      (if s2.latest_block_hash != s2.latest_execution_payload_bid.block_hash then pure []
        else do let ex ← Gloas.getExpectedWithdrawals s2; pure ex.withdrawals.toList) := by
    simp only [stepWithdrawals, h1, h2, bind, Except.bind]
  cases hc : (s2.latest_block_hash != s2.latest_execution_payload_bid.block_hash)
  · obtain ⟨ex, -, hex, -⟩ := processWithdrawals_full hc h3
    refine ⟨ex.withdrawals.toList, by rw [hsw, hc]; simp [hex, bind, Except.bind, pure,
      Except.pure], fun bi hbi => expected_routed_fresh hspe hex hR2 hfar hp2 hrefs vb2 bb2 hbi⟩
  · exact ⟨[], by rw [hsw, hc]; rfl, fun _ _ => by simp [routedSum]⟩

/-- **B1 main with its post-state clause, per step (`bls = true`; G3d).** `GStepView.registration`
together with the frozen post-state clause of statements.md B1: under FinalizedNotAhead at the
step's pre-state (with the G3 invariants and the N7 bounds that the step's withdrawals need), the
builder freshly registered at `i` is, at the step's post-state `postB`, the fresh record
(`freshBuilder`: `version = 0`, `execution_address = credentials[12:]`, `deposit_epoch` the epoch of
`trD[k]`'s slot, `withdrawable_epoch = FAR_FUTURE_EPOCH`) with balance `bal`, where
`bal = req.amount + Σ amounts of the later 0xB0 deposits for its pubkey`; and the step's
withdrawals route nothing to it (`GStepView.fresh_survives`). -/
theorem GStepView.registration_post (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    {cfg : ChainConfig} {ccfg : Config}
    {preB postB : Gloas.BeaconState P} {preExec postExec : BlockChain}
    {preParent postParent : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (V : GStepView cfg ccfg true preB preExec preParent b env? postB postExec postParent)
    (fna : FinalizedNotAhead preB)
    (g5 : PendingCovered preB) (g3 : PendingRefsInRange preB) (g4 : ExitedHaveNoPending preB)
    (g7 : NoLiveWeightOnLatestBid preB) (g8 : LatestBidCoherence preB) (fe : FutureEmpty preB)
    (hA : LatestBidBuilderActive preB)
    (validatorsBound : postB.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : postB.builders.toArray.size ≤ 2 ^ 40)
    {i : Nat} (created : BuilderCreated V.postSlots postB i) :
    ∃ (k : Nat) (req : Gloas.BuilderDepositRequest) (trD : List (Gloas.BeaconState P))
      (m m' : Gloas.BeaconState P) (dom : Domain) (addr : ExecutionAddress) (e : Epoch) (bal : U64),
      (blockBuilderDeposits b)[k]? = some req ∧
      builderDepositTrace ccfg true V.postSlots b = .ok trD ∧ trD[k]? = some m ∧ trD[k + 1]? = some m' ∧
      Gloas.processBuilderDepositRequest (gloasCtx ccfg true) m req = .ok m' ∧
      classifyBuilderDeposit ccfg true m req = .ok (.register i req.amount) ∧
      req.withdrawal_credentials.toBytes.head? = some 0xB0 ∧
      builderDepositDomain ccfg = some dom ∧
      blsVerify true req.pubkey (computeSigningRoot (builderDepositMessage req) dom) req.signature = true ∧
      Jaune.Bytes.toAdr? (req.withdrawal_credentials.toBytes.drop 12) = some addr ∧
      computeEpochAtSlot P m.slot = .ok e ∧
      m'.builders.toArray[i]? = some (freshBuilder req.pubkey addr req.amount e) ∧
      (traceLast V.postSlots trD).builders.toArray[i]? =
        some { freshBuilder req.pubkey addr req.amount e with balance := bal } ∧
      postB.builders.toArray[i]? =
        some { freshBuilder req.pubkey addr req.amount e with balance := bal } ∧
      bal.toNat = req.amount.toNat + ((((blockBuilderDeposits b).drop (k + 1)).filter
        (fun r' => r'.pubkey == req.pubkey &&
          Gloas.isBuilderWithdrawalCredential r'.withdrawal_credentials)).map
          (·.amount.toNat)).sum ∧
      ∃ ws : List Withdrawal, stepWithdrawals ccfg true V.postSlots b.message = .ok ws ∧
        ∀ bi : U64, bi.toNat = i → routedSum bi ws = 0 := by
  obtain ⟨k, req, trD, m, m', dom, addr, e, bal, hr, hD, hm, hm', hcall, hcl, hpre, hdom, hv, haddr,
    he, hat, hat2, hbal⟩ := V.registration hspe created
  obtain ⟨H1, H2⟩ := V.fresh_survives hspe quorumPositive fna g5 g3 g4 g7 g8 fe hA validatorsBound
    buildersBound hD hm hr hcl he hat2 rfl rfl
  exact ⟨k, req, trD, m, m', dom, addr, e, bal, hr, hD, hm, hm', hcall, hcl, hpre, hdom, hv, haddr,
    he, hat, hat2, H1, hbal, H2⟩

end PostState

end JauneConsensus.Facts.Gloas
