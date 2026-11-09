import JauneConsensus.Facts.Gloas.StepB3

/-!
# B1 over one Gloas joint step (goal `eip8282-gloas-cross-layer-v1`, MBS)

The per-step half of statements.md B1 (rev 3.1, `bls = true`), over ONE Gloas joint step at its
post-slots state `postSlots` (`gloasStep_ok_iff`); the traces are BF1's, read at `postSlots`.

* **Creation provenance** (`processBlock_builderCreated_trace`, `gloasStep_registration`): a
  builder record created at the step (`BuilderCreated postSlots post i`; equivalently from the
  pre-step state, whose builders `postSlots` keeps) was created by the builder deposit request at
  deposit-trace position `k`, classified `register i req.amount` at `trD[k]` under the real BLS
  (`bls = true`), with a `0xB0` prefix, a signature verifying under `DOMAIN_BUILDER_DEPOSIT`, and
  the fresh record at `trD[k+1]` with `execution_address = credentials[12:]`.
* **Same-payload register then top-up** (in `gloasStep_registration`): after the remaining
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
theorem gloasStep_registration (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    {cfg : ChainConfig} {ccfg : Config}
    {beacon postSlots post : Gloas.BeaconState P} {exec exec' : BlockChain}
    {parent parent' : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (h : gloasStep cfg ccfg true beacon exec parent b env? = .ok (.gloas post exec' parent'))
    (hps : Gloas.processSlots (gloasCtx ccfg true) beacon b.message.slot = .ok postSlots)
    {i : Nat} (created : BuilderCreated postSlots post i) :
    ∃ (k : Nat) (req : Gloas.BuilderDepositRequest) (trD : List (Gloas.BeaconState P))
      (m m' : Gloas.BeaconState P) (dom : Domain) (addr : ExecutionAddress) (e : Epoch) (bal : U64),
      (blockBuilderDeposits b)[k]? = some req ∧
      builderDepositTrace ccfg true postSlots b = .ok trD ∧ trD[k]? = some m ∧ trD[k + 1]? = some m' ∧
      Gloas.processBuilderDepositRequest (gloasCtx ccfg true) m req = .ok m' ∧
      classifyBuilderDeposit ccfg true m req = .ok (.register i req.amount) ∧
      req.withdrawal_credentials.toBytes.head? = some 0xB0 ∧
      builderDepositDomain ccfg = some dom ∧
      blsVerify true req.pubkey (computeSigningRoot (builderDepositMessage req) dom) req.signature = true ∧
      Jaune.Bytes.toAdr? (req.withdrawal_credentials.toBytes.drop 12) = some addr ∧
      computeEpochAtSlot P m.slot = .ok e ∧
      m'.builders.toArray[i]? = some (freshBuilder req.pubkey addr req.amount e) ∧
      (traceLast postSlots trD).builders.toArray[i]? =
        some { freshBuilder req.pubkey addr req.amount e with balance := bal } ∧
      bal.toNat = req.amount.toNat + ((((blockBuilderDeposits b).drop (k + 1)).filter
        (fun r' => r'.pubkey == req.pubkey &&
          Gloas.isBuilderWithdrawalCredential r'.withdrawal_credentials)).map
          (·.amount.toNat)).sum := by
  have hpb := gloasStep_processBlock h hps
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
  have htl : traceLast s0 trD = traceLast postSlots trD :=
    traceLast_ne_nil (scanM_ok_ne_nil hsD) s0 postSlots
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

end JauneConsensus.Facts.Gloas
