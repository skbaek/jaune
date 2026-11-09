import JauneConsensus.Facts.JointGloas
import JauneConsensus.Facts.Gloas.TraceLink
import JauneConsensus.Facts.Gloas.InvariantsCoverBlock

/-!
# B3 over one Gloas joint step (goal `eip8282-gloas-cross-layer-v1`, MBS)

The per-step half of statements.md B3 (rev 3.1), over ONE Gloas joint step: `gloasStep`
(`= jointStepG` on a Gloas state and block) or the crossing `jointStepG` from Fulu, read at the
step's post-slots state `postSlots` (`gloasStep_ok_iff`, `jointStepG_cross_ok_iff`).

* **The step's shape** (`gloasStep_processBlock`, `gloasStep_post`): the post-state of a Gloas step
  is Gloas `process_block` of the block at `postSlots`; `processSlots_builders`: `process_slots`
  keeps the builder registry, so `postSlots.builders` is the pre-step state's.
* **The writers at the step** (`gloasStep_withdrawableEpoch_writers`): every change of a builder's
  `withdrawable_epoch` at a Gloas step is an exit at exit-trace position `k` classified
  `initiate i`, a top-up reset at deposit-trace position `k`, or a fresh record.
* **Every exit at a Gloas step consumes a request** (`gloasStep_exitInitiated`): an initiated exit
  (`ExitInitiated`, from the pre-step state or from `postSlots`) is the builder exit request at
  exit-trace position `k`, classified `initiate i` at `trE[k]`, its call running
  `trE[k] → trE[k+1]`.
* **The crossing step initiates no exit** (`jointStepG_crossing_noExit`, G2b obligation O-a): the
  upgraded state's builders are all at `FAR_FUTURE_EPOCH` (`upgradeToGloas_builders`), the first
  block's requests are empty by value, so the crossing changes no builder's pubkey or
  `withdrawable_epoch`: no exit, no reset, no fresh record.
* **Pre-Gloas steps have no builders** (`jointStepG_pre_noBuilders`): a pre-crossing joint state
  is a `JointState` (Electra/Fulu), whose beacon state has no builder registry; the step stays
  pre-crossing.
-/

namespace JauneConsensus.Facts.Gloas

open Jaune JauneConsensus JauneConsensus.Facts

variable {P : Preset}

/-! ## The shape of one Gloas step -/

/-- The block transition after the slots is Gloas `process_block` (the block signature and state
root checks write nothing). -/
theorem gloasBlockTransition_eq_processBlock {ctx : Ctx} {st post : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} (h : gloasBlockTransition ctx st b = .ok post) :
    Gloas.processBlock ctx st b.message = .ok post := by
  unfold gloasBlockTransition Gloas.applySignedBlockWith at h
  simp only [ite_true] at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s, hs, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact hs

/-- The step's end (the envelope, or `.withheld`) keeps the beacon state and the chain. -/
theorem gloasDeliverOpt_beacon {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {post : Gloas.BeaconState P} {exec : BlockChain}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} {s' : GJointState P}
    (h : gloasDeliverOpt cfg ccfg bls post exec env? = .ok s') :
    ∃ parent', s' = .gloas post exec parent' := by
  cases env? with
  | none => cases h; exact ⟨_, rfl⟩
  | some e =>
    simp only [gloasDeliverOpt, deliver] at h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    cases h
    exact ⟨_, rfl⟩

/-- **A Gloas step at its post-slots state.** If the step succeeds with Gloas post-state `post`,
and `process_slots` takes the pre-step state to `postSlots` (the state the block is processed at),
then `post` is Gloas `process_block` of the block at `postSlots`. -/
theorem gloasStep_processBlock {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon postSlots post : Gloas.BeaconState P} {exec exec' : BlockChain}
    {parent parent' : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (h : gloasStep cfg ccfg bls beacon exec parent b env? = .ok (.gloas post exec' parent'))
    (hps : Gloas.processSlots (gloasCtx ccfg bls) beacon b.message.slot = .ok postSlots) :
    Gloas.processBlock (gloasCtx ccfg bls) postSlots b.message = .ok post := by
  obtain ⟨ps, post0, exec0, o, h0, _, hbt, hd⟩ := gloasStep_ok_iff.mp h
  rw [hps] at h0
  cases h0
  obtain ⟨_, hs⟩ := gloasDeliverOpt_beacon hd
  cases hs
  exact gloasBlockTransition_eq_processBlock hbt

/-- A successful Gloas step has a post-slots state, and its post-state is a Gloas state that is
`process_block` of the block there. -/
theorem gloasStep_post {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : Gloas.BeaconState P} {exec : BlockChain} {parent : ParentPayload P}
    {b : Gloas.SignedBeaconBlock P} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    {s' : GJointState P} (h : gloasStep cfg ccfg bls beacon exec parent b env? = .ok s') :
    ∃ postSlots post exec' parent',
      Gloas.processSlots (gloasCtx ccfg bls) beacon b.message.slot = .ok postSlots ∧
      Gloas.processBlock (gloasCtx ccfg bls) postSlots b.message = .ok post ∧
      s' = .gloas post exec' parent' := by
  obtain ⟨ps, post0, exec0, o, h0, _, hbt, hd⟩ := gloasStep_ok_iff.mp h
  obtain ⟨parent', hs⟩ := gloasDeliverOpt_beacon hd
  exact ⟨ps, post0, exec0, parent', h0, gloasBlockTransition_eq_processBlock hbt, hs⟩

/-- `process_slots` keeps the builder registry (`process_epoch` writes the builder queues only,
`processBuilderPendingPayments_frame`). -/
theorem processSlots_builders {ctx : Ctx} {s s' : Gloas.BeaconState P} {slot : U64}
    (h : Gloas.processSlots ctx s slot = .ok s') : s'.builders = s.builders := by
  refine Inv.processSlots_ind (fun x => x.builders = s.builders) ?_ h rfl
  intro st st1 st2 next hI hf _ hcase
  show st2.builders = s.builders
  rcases hcase with ⟨rfl, _⟩ | ⟨_, he⟩
  · exact hf.1.trans hI
  · obtain ⟨a, c, fa, hp, fc⟩ := Inv.processEpoch_phases he
    rw [fc.1, (processBuilderPendingPayments_frame hp).1, fa.1, hf.1, hI]

/-- The crossing's slots function keeps the builder registry. -/
theorem crossingSlots_builders {ctx : Ctx} {s s' : Gloas.BeaconState P} {slot : U64}
    (h : crossingSlots ctx s slot = .ok s') : s'.builders = s.builders := by
  unfold crossingSlots at h
  split at h
  · cases h; rfl
  · exact processSlots_builders h

/-! ## Scans keep invariants -/

/-- An invariant of each call holds at every state of a scan. -/
theorem scanM_inv {σ α : Type} {f : σ → α → M σ} (I : σ → Prop)
    (hstep : ∀ x a y, I x → f x a = .ok y → I y) :
    ∀ (xs : List α) {s : σ} {tr : List σ}, I s → scanM f s xs = .ok tr →
      ∀ (k : Nat) (m : σ), tr[k]? = some m → I m
  | [], s, tr, hs, h, k, m, hk => by
    simp only [scanM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases k with
    | zero => simp at hk; rw [← hk]; exact hs
    | succ k => simp at hk
  | a :: xs, s, tr, hs, h, k, m, hk => by
    simp only [scanM, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i s' hs'
      split at h
      · cases h
      · rename_i rest hrest
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        cases k with
        | zero => simp at hk; rw [← hk]; exact hs
        | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          exact scanM_inv I hstep xs (hstep s a s' hs hs') hrest k m hk

/-! ## B3: the writers at a Gloas step -/

/-- **B3, the `withdrawable_epoch` writers at a Gloas step.** At a successful Gloas step with
post-slots state `postSlots` and post-state `post`, if builder `i`'s `withdrawable_epoch` changes
(from `postSlots`, whose builders are the pre-step state's, `processSlots_builders`), then the
change is an exit initiated (`ExitInitiated`) by the builder exit request at exit-trace position
`k`, classified `initiate i` at `trE[k]`; or a reset top-up by the builder deposit request at
deposit-trace position `k`; or a fresh record (`BuilderCreated`). The traces are read at
`postSlots`. Needs `2 ≤ SLOTS_PER_EPOCH` (`ValidJointG.slotsPerEpoch`). -/
theorem gloasStep_withdrawableEpoch_writers (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon postSlots post : Gloas.BeaconState P} {exec exec' : BlockChain}
    {parent parent' : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (h : gloasStep cfg ccfg bls beacon exec parent b env? = .ok (.gloas post exec' parent'))
    (hps : Gloas.processSlots (gloasCtx ccfg bls) beacon b.message.slot = .ok postSlots)
    {i : Nat} {x x' : Gloas.Builder} (hx : postSlots.builders.toArray[i]? = some x)
    (hx' : post.builders.toArray[i]? = some x') (hne : x.withdrawable_epoch ≠ x'.withdrawable_epoch) :
    ∃ trD trE, builderDepositTrace ccfg bls postSlots b = .ok trD ∧
      builderExitTrace ccfg bls postSlots b = .ok trE ∧
      ((ExitInitiated postSlots post i ∧
          ∃ k e m m', (blockBuilderExits b)[k]? = some e ∧ trE[k]? = some m ∧
            trE[k + 1]? = some m' ∧ Gloas.processBuilderExitRequest ccfg m e = .ok m' ∧
            classifyBuilderExit ccfg m e = .ok (.initiate i)) ∨
        (∃ k r m m', (blockBuilderDeposits b)[k]? = some r ∧ trD[k]? = some m ∧
            trD[k + 1]? = some m' ∧
            Gloas.processBuilderDepositRequest (gloasCtx ccfg bls) m r = .ok m' ∧
            classifyBuilderDeposit ccfg bls m r = .ok (.topUp i r.amount true)) ∨
        BuilderCreated postSlots post i) :=
  withdrawableEpoch_writers_trace hspe (gloasStep_processBlock h hps) hx hx' hne

/-- Along the builder-deposit loop, a builder slot holding a record at `FAR_FUTURE_EPOCH` keeps
holding one (a top-up keeps `withdrawable_epoch` unless it is a reset, which needs it off
`FAR_FUTURE_EPOCH`; a registration writes `FAR_FUTURE_EPOCH`). -/
theorem depReq_keeps_far {ctx : Ctx} {m m' : Gloas.BeaconState P}
    {r : Gloas.BuilderDepositRequest} (h : Gloas.processBuilderDepositRequest ctx m r = .ok m')
    {i : Nat} (hI : ∃ c, m.builders.toArray[i]? = some c ∧ c.withdrawable_epoch = FAR_FUTURE_EPOCH) :
    ∃ c, m'.builders.toArray[i]? = some c ∧ c.withdrawable_epoch = FAR_FUTURE_EPOCH := by
  obtain ⟨c, hc, hfar⟩ := hI
  obtain ⟨_, _, hat⟩ := processBuilderDepositRequest_at h i
  rcases hat with heq | ⟨c0, c', reset, hc0, hc', _, _, _, hnr, hr⟩ |
      ⟨addr, e, _, _, hat', _, _⟩
  · exact ⟨c, by rw [heq]; exact hc, hfar⟩
  · rw [hc] at hc0; cases hc0
    cases reset with
    | false => exact ⟨c', hc', (hnr rfl).trans hfar⟩
    | true => exact absurd hfar (hr.mp rfl).1
  · exact ⟨_, hat', rfl⟩

/-- **B3 at a Gloas step: every exit consumes a request.** At a successful Gloas step with
post-slots state `postSlots` and post-state `post`, if builder `i`'s exit is initiated
(`ExitInitiated postSlots post i`: the same incarnation leaves `FAR_FUTURE_EPOCH`), then it was
initiated by the builder exit request `e` at exit-trace position `k` of the block's
`parent_execution_requests`, classified `initiate i` at the exit-trace state `trE[k]` (so it
passed the first-match, activity, source-address and pending-balance checks,
`classifyBuilderExit_meaning`), its call running `trE[k] → trE[k+1]`. Needs
`2 ≤ SLOTS_PER_EPOCH`. -/
theorem gloasStep_exitInitiated (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon postSlots post : Gloas.BeaconState P} {exec exec' : BlockChain}
    {parent parent' : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (h : gloasStep cfg ccfg bls beacon exec parent b env? = .ok (.gloas post exec' parent'))
    (hps : Gloas.processSlots (gloasCtx ccfg bls) beacon b.message.slot = .ok postSlots)
    {i : Nat} (hin : ExitInitiated postSlots post i) :
    ∃ (k : Nat) (e : Gloas.BuilderExitRequest) (trE : List (Gloas.BeaconState P))
      (m m' : Gloas.BeaconState P),
      (blockBuilderExits b)[k]? = some e ∧ builderExitTrace ccfg bls postSlots b = .ok trE ∧
      trE[k]? = some m ∧ trE[k + 1]? = some m' ∧
      Gloas.processBuilderExitRequest ccfg m e = .ok m' ∧
      classifyBuilderExit ccfg m e = .ok (.initiate i) := by
  obtain ⟨x, x', hx, hx', hpk, hfar, hnfar⟩ := hin
  have hne : x.withdrawable_epoch ≠ x'.withdrawable_epoch := by rw [hfar]; exact Ne.symm hnfar
  obtain ⟨trD, trE, hD, hE, hcase⟩ := gloasStep_withdrawableEpoch_writers hspe h hps hx hx' hne
  rcases hcase with ⟨_, k, e, m, m', he, hm, hm', hcall, hcl⟩ | ⟨k, r, m, m', _, hm, _, _, hcl⟩ | hcr
  · exact ⟨k, e, trE, m, m', he, hE, hm, hm', hcall, hcl⟩
  · -- a reset top-up needs builder `i` off `FAR_FUTURE_EPOCH`, but the loop keeps it there
    exfalso
    obtain ⟨s0, h0, hs⟩ := builderDepositTrace_scan hD
    have hI0 : ∃ c, s0.builders.toArray[i]? = some c ∧ c.withdrawable_epoch = FAR_FUTURE_EPOCH :=
      ⟨x, by rw [builderDepositTrace_head_builders hD h0]; exact hx, hfar⟩
    obtain ⟨c, hc, hcf⟩ := scanM_inv _ (fun _ _ _ hI hy => depReq_keeps_far hy hI) _ hI0 hs k m hm
    obtain ⟨_, htop, _⟩ := classifyBuilderDeposit_meaning hcl
    obtain ⟨_, _, _, c0, hc0, hreset⟩ := (htop i r.amount true).mp rfl
    rw [hc] at hc0; cases hc0
    exact (hreset.mp rfl).1 hcf
  · exact absurd (by rw [hx, hx']; simp [hpk]) hcr.2

/-! ## B3 at the crossing: no exit (O-a) -/

/-- With no builder requests, the parent settlement keeps the builder registry. -/
theorem processParentExecutionPayload_builders_of_empty {ctx : Ctx} {st mid : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} (hd : blockBuilderDeposits b = [])
    (he : blockBuilderExits b = [])
    (h : Gloas.processParentExecutionPayload ctx st b.message = .ok mid) :
    mid.builders = st.builders := by
  rcases Inv.processParentExecutionPayload_cases h with ⟨rfl, _⟩ | ⟨_, a, d, e, ha, hdd, hee, hs⟩
  · rfl
  · simp only [blockBuilderDeposits] at hd
    simp only [blockBuilderExits] at he
    rw [hd] at hdd
    rw [he] at hee
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hdd hee
    subst hdd hee
    rw [(Inv.applyParentSuffix_post hs).1, applyParentPrefix_builders ha]

/-- With no builder requests, `process_block` keeps every builder's pubkey and
`withdrawable_epoch` (and the registry's length). -/
theorem processBlock_pkWe_of_empty {ctx : Ctx} {st post : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} (hd : blockBuilderDeposits b = [])
    (he : blockBuilderExits b = []) (h : Gloas.processBlock ctx st b.message = .ok post) :
    BuildersPkWe st post := by
  obtain ⟨mid, hmid, hpk⟩ := processBlock_after_parent ctx st b.message post h
  have hb := processParentExecutionPayload_builders_of_empty hd he hmid
  exact pkWe.trans (pkWe_of_eq hb) hpk

/-- **B3 at the crossing step (G2b obligation O-a): the crossing initiates no exit.** A successful
crossing step from a Fulu state upgrades it (`Gloas.crossFromFulu`, ending in
`upgrade_to_gloas`) to `upgraded`, whose builders are all at `FAR_FUTURE_EPOCH`
(`upgradeToGloas_builders`); the crossing's slots keep them (`postSlots`); the first Gloas block's
`parent_execution_requests` are empty by value (`jointStepG_cross_ok_iff`), so `process_block`
keeps every builder's pubkey and `withdrawable_epoch`. Hence, from `postSlots` to the post-state:
no exit is initiated (`ExitInitiated`), no record is created (`BuilderCreated`), every builder of
the post-state is at `FAR_FUTURE_EPOCH`, and no `withdrawable_epoch` changes (so no reset). -/
theorem jointStepG_crossing_noExit {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .fulu} {exec : BlockChain} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} {s' : GJointState P}
    (h : jointStepG cfg ccfg bls (.pre ⟨.fulu, beacon, exec⟩) (.gloas b) env? = .ok s') :
    ∃ (upgraded postSlots post : Gloas.BeaconState P) (parent' : ParentPayload P),
      Gloas.crossFromFulu (gloasCtx ccfg bls) beacon = .ok upgraded ∧
      crossingSlots (gloasCtx ccfg bls) upgraded b.message.slot = .ok postSlots ∧
      Gloas.processBlock (gloasCtx ccfg bls) postSlots b.message = .ok post ∧
      s' = .gloas post exec parent' ∧
      postSlots.builders = upgraded.builders ∧
      blockBuilderDeposits b = [] ∧ blockBuilderExits b = [] ∧
      BuildersFar postSlots ∧ BuildersFar post ∧ BuildersPkWe postSlots post ∧
      (∀ i, ¬ ExitInitiated postSlots post i) ∧ (∀ i, ¬ BuilderCreated postSlots post i) := by
  obtain ⟨_, _, upgraded, postSlots, post, hup, h0, _, hr, hbt, hd⟩ := jointStepG_cross_ok_iff.mp h
  obtain ⟨atFork, hat⟩ := crossFromFulu_upgrade hup
  obtain ⟨hfar, _⟩ := upgradeToGloas_builders hat
  have hbs := crossingSlots_builders h0
  have hpb := gloasBlockTransition_eq_processBlock hbt
  obtain ⟨parent', hs⟩ := gloasDeliverOpt_beacon hd
  have hdl : blockBuilderDeposits b = [] := by
    simp only [blockBuilderDeposits, hr]; rfl
  have hel : blockBuilderExits b = [] := by
    simp only [blockBuilderExits, hr]; rfl
  have hpk := processBlock_pkWe_of_empty hdl hel hpb
  have hfs : BuildersFar postSlots := fun i x hx => hfar i x (by rw [← hbs]; exact hx)
  have hfp : BuildersFar post := by
    intro i x hx
    have := hpk.2 i
    rw [hx] at this
    cases hc : postSlots.builders.toArray[i]? with
    | none => rw [hc] at this; cases this
    | some c =>
      rw [hc] at this
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      rw [this.2]; exact hfs i c hc
  refine ⟨upgraded, postSlots, post, parent', hup, h0, hpb, hs, hbs, hdl, hel, hfs, hfp, hpk,
    fun i ⟨x, x', hx, hx', _, _, hn⟩ => hn (hfp i x' hx'), fun i hcr => ?_⟩
  apply hcr.2
  have := hpk.2 i
  cases hc : postSlots.builders.toArray[i]? <;> cases hc' : post.builders.toArray[i]? <;>
    rw [hc, hc'] at this <;> simp_all

/-! ## Pre-Gloas steps -/

/-- **Pre-Gloas steps have no builders.** A successful joint step from a pre-crossing state with
a pre-Gloas block stays pre-crossing: its states are `JointState`s (Electra/Fulu), which carry no
builder registry, so no builder record is created and no exit is initiated there. -/
theorem jointStepG_pre_noBuilders {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s : JointState P} {b : AnySignedBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} {s' : GJointState P}
    (h : jointStepG cfg ccfg bls (.pre s) (.pre b) env? = .ok s') :
    ∃ j : JointState P, s' = .pre j := by
  obtain ⟨_, _, j, _, hj⟩ := jointStepG_pre_ok_iff.mp h
  exact ⟨j, hj⟩

end JauneConsensus.Facts.Gloas
