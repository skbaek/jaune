import JauneConsensus.Facts.Gloas.StepB1
import JauneConsensus.Facts.Gloas.StepB5

/-!
# B7 over one Gloas joint step (goal `eip8282-gloas-cross-layer-v1`, MBS)

The per-step half of statements.md B7 (rev 3.1, any `bls`), over ONE Gloas joint step at its
post-slots state `postSlots`.

* **Separation** (`GStepView.builderRequests_frame`, `GStepView.builderWriters`): the builder
  request loops leave validators, validator balances, `pending_deposits` and the builder queues
  unchanged (every state of both BF1 traces agrees on them with the first); and the only phases of
  the step that touch the builder registry are those two loops and `process_withdrawals`, which
  touches only builder balances; `process_slots` (with `process_pending_deposits`), the validator
  request loops, the header, the bid and the operations (voluntary exits, BLS changes, slashings)
  keep it.
* **Conservation** (`GStepView.builder_total_noRegister`): at a step that registers no fresh
  record, total builder balance at the post-state plus the builder debits of `apply_withdrawals`
  (`builderDebits`: WSL's `routedSum` per registry slot) equals total builder balance at the
  pre-step state plus the deposits credited along the deposit trace (`builderCredits`: WSL's
  `creditedAt` per slot). It is the sum over the registry of WSL's per-builder B5(i) equation
  `GStepView.builder_balance_equation` (consumed, not re-proved), with its hypotheses (G3 at the
  pre-state, N7 at the post-state); a step that registers is B1's (`GStepView.registration`).
-/

namespace JauneConsensus.Facts.Gloas

open Jaune JauneConsensus JauneConsensus.Facts

variable {P : Preset}

/-! ## The builder phases of one Gloas block -/

/-- **The builder writers of a Gloas block.** `process_block` at `st` runs the parent settlement
(`s1`: its builders are those at the end of the exit trace; an EMPTY parent leaves `st`), the
header (`s2`: builders and builder queues kept), `process_withdrawals` (`s3`: only builder balances
change, `BuildersPkWe` and `WFrame`), then the bid and the operations, which keep the builders. -/
theorem processBlock_builderPhases {ctx : Ctx} {st post : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} (h : Gloas.processBlock ctx st b.message = .ok post) :
    ∃ (trD trE : List (Gloas.BeaconState P)) (s1 s2 s3 : Gloas.BeaconState P),
      builderDepositTrace ctx.cfg ctx.blsActive st b = .ok trD ∧
      builderExitTrace ctx.cfg ctx.blsActive st b = .ok trE ∧
      Gloas.processParentExecutionPayload ctx st b.message = .ok s1 ∧
      s1.builders = (traceLast st trE).builders ∧
      s2 = { s1 with latest_block_header := s2.latest_block_header } ∧
      Gloas.processWithdrawals s2 = .ok s3 ∧ BuildersPkWe s2 s3 ∧ Inv.WFrame s2 s3 ∧
      post.builders = s3.builders := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := Inv.processBlock_phases h
  obtain ⟨trD, trE, hD, hE, hE0, hEmpty, hFull⟩ := processParentExecutionPayload_traces h1
  have hs1 : s1.builders = (traceLast st trE).builders := by
    cases hflag : (b.message.body.signed_execution_payload_bid.message.parent_block_hash !=
        st.latest_execution_payload_bid.block_hash)
    · rw [applyParentSuffix_builders (hFull hflag)]
    · obtain ⟨rfl, -, rfl⟩ := hEmpty hflag; rfl
  obtain ⟨_, _, hm2⟩ := Inv.processBlockHeader_post h2
  have b4 := Inv.processExecutionPayloadBid_post h4
  have c := Inv.afterBid_core h5 h6 h7 h8
  exact ⟨trD, trE, s1, s2, s3, hD, hE, h1, hs1, hm2, h3, processWithdrawals_pkWe _ _ h3,
    Inv.processWithdrawals_wFrame _ _ h3, c.1.trans b4.2.2.2.2.1⟩

/-! ## B7 separation, per step -/

/-- The fields a builder request leaves alone: validators, validator balances, `pending_deposits`
and the two builder queues. -/
def BuilderRequestFrame (s s' : Gloas.BeaconState P) : Prop :=
  s'.validators = s.validators ∧ s'.balances = s.balances ∧
    s'.pending_deposits = s.pending_deposits ∧
    s'.builder_pending_payments = s.builder_pending_payments ∧
    s'.builder_pending_withdrawals = s.builder_pending_withdrawals

theorem BuilderRequestFrame.trans {a b c : Gloas.BeaconState P} (h₁ : BuilderRequestFrame a b)
    (h₂ : BuilderRequestFrame b c) : BuilderRequestFrame a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
    h₂.2.2.2.2.trans h₁.2.2.2.2⟩

/-- **B7 separation, the builder requests, per step.** At a successful Gloas step with post-slots
state `postSlots`, every state of the deposit trace and of the exit trace (read at `postSlots`)
has the validators, validator balances, `pending_deposits` and builder queues of the first
deposit-trace state `s0`: the builder deposit and exit requests write the builder registry only
(`processBuilderDepositRequest_frame`, `processBuilderExitRequest_frame`). -/
theorem GStepView.builderRequests_frame {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {preB postB : Gloas.BeaconState P} {preExec postExec : BlockChain}
    {preParent postParent : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent) :
    ∃ (trD trE : List (Gloas.BeaconState P)) (s0 : Gloas.BeaconState P),
      builderDepositTrace ccfg bls V.postSlots b = .ok trD ∧
      builderExitTrace ccfg bls V.postSlots b = .ok trE ∧ trD[0]? = some s0 ∧
      s0.builders = V.postSlots.builders ∧
      (∀ (k : Nat) (m : Gloas.BeaconState P), trD[k]? = some m → BuilderRequestFrame s0 m) ∧
      (∀ (k : Nat) (m : Gloas.BeaconState P), trE[k]? = some m → BuilderRequestFrame s0 m) := by
  have hpb := V.processBlock
  obtain ⟨s1, h1⟩ := processBlock_parent hpb
  obtain ⟨trD, trE, hD, hE, -, -, -⟩ := processParentExecutionPayload_traces h1
  obtain ⟨s0, h0, hsD⟩ := builderDepositTrace_scan hD
  have frD := scanM_inv (BuilderRequestFrame s0)
    (fun _ _ _ hI hy => by
      obtain ⟨a, b, c, d, e, -⟩ := processBuilderDepositRequest_frame hy
      exact hI.trans ⟨a, b, c, d, e⟩) _
    ⟨rfl, rfl, rfl, rfl, rfl⟩ hsD
  obtain ⟨trD', hD', hsE, -⟩ := builderExitTrace_ok hE
  rw [hD] at hD'; cases hD'
  have hlast : BuilderRequestFrame s0 (traceLast V.postSlots trD) := by
    refine frD (trD.length - 1) _ ?_
    rw [← List.getLast?_eq_getElem?]
    exact getLast?_of_traceLast (scanM_ok_ne_nil hsD) V.postSlots
  have frE := scanM_inv (BuilderRequestFrame s0)
    (fun _ _ _ hI hy => by
      obtain ⟨a, b, c, d, e, -⟩ := processBuilderExitRequest_frame hy
      exact hI.trans ⟨a, b, c, d, e⟩) _ hlast hsE
  exact ⟨trD, trE, s0, hD, hE, h0, builderDepositTrace_head_builders hD h0, frD, frE⟩

/-- **B7 separation, the validator paths, per step.** At a successful Gloas step with post-slots
state `postSlots` and post-state `post`: `process_slots` (its epochs, `process_pending_deposits`
included) keeps the builder registry; the parent settlement's validator request loops (and its
payment settlement) start the deposit trace with `postSlots`'s builders; after the exit trace the
suffix, the header, the bid and the operations (voluntary exits, BLS changes, slashings) keep the
builders; and `process_withdrawals`, the one other builder writer, keeps every builder's pubkey,
`withdrawable_epoch`, identity and the registry's length (`BuildersPkWe`, `WFrame`): only builder
balances. -/
theorem GStepView.builderWriters {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {preB postB : Gloas.BeaconState P} {preExec postExec : BlockChain}
    {preParent postParent : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent) :
    V.postSlots.builders = preB.builders ∧
    ∃ (trD trE : List (Gloas.BeaconState P)) (s0 s1 s2 s3 : Gloas.BeaconState P),
      builderDepositTrace ccfg bls V.postSlots b = .ok trD ∧
      builderExitTrace ccfg bls V.postSlots b = .ok trE ∧
      trD[0]? = some s0 ∧ s0.builders = V.postSlots.builders ∧
      Gloas.processParentExecutionPayload (gloasCtx ccfg bls) V.postSlots b.message = .ok s1 ∧
      s1.builders = (traceLast V.postSlots trE).builders ∧ s2.builders = s1.builders ∧
      Gloas.processWithdrawals s2 = .ok s3 ∧ BuildersPkWe s2 s3 ∧ Inv.WFrame s2 s3 ∧
      postB.builders = s3.builders := by
  refine ⟨Inv.processSlots_identityStable V.slots, ?_⟩
  obtain ⟨trD, trE, s1, s2, s3, hD, hE, h1, hs1, hm2, h3, hpk, hwf, hpost⟩ :=
    processBlock_builderPhases (V.processBlock)
  obtain ⟨s0, h0, -⟩ := builderDepositTrace_scan hD
  exact ⟨trD, trE, s0, s1, s2, s3, hD, hE, h0, builderDepositTrace_head_builders hD h0, h1, hs1,
    by rw [hm2], h3, hpk, hwf, hpost⟩

/-- The step's withdrawals (`stepWithdrawals`) are defined whenever its `process_block` succeeds. -/
theorem stepWithdrawals_ok {ccfg : Config} {bls : Bool} {st post : Gloas.BeaconState P}
    {blk : Gloas.BeaconBlock P} (h : Gloas.processBlock (gloasCtx ccfg bls) st blk = .ok post) :
    ∃ ws, stepWithdrawals ccfg bls st blk = .ok ws := by
  obtain ⟨s1, s2, s3, -, -, -, -, h1, h2, h3, -⟩ := Inv.processBlock_phases h
  unfold stepWithdrawals
  simp only [h1, h2, bind, Except.bind]
  cases hc : (s2.latest_block_hash != s2.latest_execution_payload_bid.block_hash)
  · obtain ⟨ex, -, hex, -⟩ := processWithdrawals_full hc h3
    simp only [Bool.false_eq_true, ↓reduceIte, hex]
    exact ⟨_, rfl⟩
  · exact ⟨[], rfl⟩

/-! ## Conservation: summing WSL's per-builder equation -/

/-- Pointwise balance equations sum: if each slot `i` of `l'` and `l` satisfies
`g l'[i] + r i = g l[i] + c i`, the totals do. -/
theorem sum_map_pointwise {β : Type} (g : β → Nat) :
    ∀ (l l' : List β) (r c : Nat → Nat), l'.length = l.length →
      (∀ i x x', l[i]? = some x → l'[i]? = some x' → g x' + r i = g x + c i) →
      (l'.map g).sum + ((List.range l.length).map r).sum =
        (l.map g).sum + ((List.range l.length).map c).sum
  | [], [], _, _, _, _ => by simp
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | x :: xs, x' :: xs', r, c, hl, hp => by
    have h0 := hp 0 x x' rfl rfl
    have ih := sum_map_pointwise g xs xs' (fun i => r (i + 1)) (fun i => c (i + 1))
      (by simpa using hl) (fun i y y' hy hy' => hp (i + 1) y y' (by simpa using hy)
        (by simpa using hy'))
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.range_succ_eq_map,
      List.map_map, Function.comp_def, Nat.succ_eq_add_one] at ih ⊢
    omega

/-- The withdrawals a step routes to builder slot `i` (`routedSum` at the slot's index; `0` past
`2^64`, where no builder lies). -/
def routedAt (ws : List Withdrawal) (i : Nat) : Nat :=
  match U64.ofNat? i "BuilderIndex" with
  | .ok bi => routedSum bi ws
  | .error _ => 0

/-- **B7 conservation's debit term**: the builder debits of the step's `apply_withdrawals`, the
amounts routed to each builder slot of a registry of `n` slots. -/
def builderDebits (ws : List Withdrawal) (n : Nat) : Nat :=
  ((List.range n).map (routedAt ws)).sum

/-- **B7 conservation's credit term**: the builder deposits credited along the deposit trace
(WSL's `creditedAt`, the top-ups of each slot), over a registry of `n` slots. -/
def builderCredits (ccfg : Config) (bls : Bool) (trD : List (Gloas.BeaconState P))
    (rs : List Gloas.BuilderDepositRequest) (n : Nat) : Nat :=
  ((List.range n).map (fun i => creditedAt ccfg bls i trD rs)).sum

/-- No request of a deposit trace registers a fresh record anywhere. -/
def NoRegister (ccfg : Config) (bls : Bool) (tr : List (Gloas.BeaconState P))
    (rs : List Gloas.BuilderDepositRequest) : Prop :=
  ∀ i, NoRegisterAt ccfg bls i tr rs

/-- Without a registration, the deposit loop keeps the registry's length (a top-up or an ignored
request writes no slot past the end). -/
theorem depositLoop_size {ccfg : Config} {bls : Bool} :
    ∀ (rs : List Gloas.BuilderDepositRequest) (s : Gloas.BeaconState P)
      (tr : List (Gloas.BeaconState P)),
      scanM (Gloas.processBuilderDepositRequest { cfg := ccfg, blsActive := bls }) s rs = .ok tr →
      NoRegister ccfg bls tr rs →
      (traceLast s tr).builders.toArray.size = s.builders.toArray.size
  | [], s, tr, h, _ => by
    simp only [scanM, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | r :: rs, s, tr, h, hno => by
    obtain ⟨s', rest, h1, h2, rfl⟩ := scanM_cons_ok h
    have h1' := h1
    rw [processBuilderDepositRequest_eq] at h1'
    obtain ⟨o, hc, -⟩ := bind_eq_ok_iff.mp h1'
    obtain ⟨hpre, hbad, htop, -⟩ :=
      classifyBuilderDeposit_effect (ctx := { cfg := ccfg, blsActive := bls }) hc h1
    have hsz : s'.builders.toArray.size = s.builders.toArray.size := by
      cases o with
      | ignoredPrefix => rw [hpre rfl]
      | ignoredBadSignature => rw [hbad rfl]
      | topUp j a reset => exact (htop j a reset rfl).choose_spec.choose_spec.2.2.1
      | register j a =>
        have := (hno j)
        simp only [NoRegisterAt] at this
        exact absurd hc (this.1 a)
    have hno' : NoRegister ccfg bls rest rs := fun i => by
      have := hno i; simp only [NoRegisterAt] at this; exact this.2
    rw [traceLast_scan_cons h2, depositLoop_size rs s' rest h2 hno', hsz]

/-- Without a registration, a Gloas step keeps the builder registry's length. -/
theorem GStepView.size_noRegister {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {preB postB : Gloas.BeaconState P} {preExec postExec : BlockChain}
    {preParent postParent : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    {trD : List (Gloas.BeaconState P)} (hD : builderDepositTrace ccfg bls V.postSlots b = .ok trD)
    (hno : NoRegister ccfg bls trD (blockBuilderDeposits b)) :
    postB.builders.toArray.size = preB.builders.toArray.size := by
  obtain ⟨trD', trE, s1, s2, s3, hD', hE, -, hs1, hm2, -, hpk, -, hpost⟩ :=
    processBlock_builderPhases V.processBlock
  change builderDepositTrace ccfg bls V.postSlots b = _ at hD'
  change builderExitTrace ccfg bls V.postSlots b = _ at hE
  rw [hD] at hD'; cases hD'
  obtain ⟨s0, h0, hsD⟩ := builderDepositTrace_scan hD
  obtain ⟨trD', hD', hsE, -⟩ := builderExitTrace_ok hE
  rw [hD] at hD'; cases hD'
  have hdl := depositLoop_size _ _ _ hsD hno
  rw [traceLast_ne_nil (scanM_ok_ne_nil hsD) s0 V.postSlots] at hdl
  have hel : (traceLast V.postSlots trE).builders.toArray.size =
      (traceLast V.postSlots trD).builders.toArray.size := by
    have hpk := scanM_inv (fun x : Gloas.BeaconState P =>
        x.builders.toArray.size = (traceLast V.postSlots trD).builders.toArray.size)
      (fun _ _ _ hI hy => by
        rcases (Inv.exitReq_cases hy).2 with heq | ⟨_, _, _, _, _, _, _, _, hsz, _⟩
        · rw [heq]; exact hI
        · exact hsz.trans hI) _ rfl hsE
    refine hpk (trE.length - 1) _ ?_
    rw [← List.getLast?_eq_getElem?]
    exact getLast?_of_traceLast (scanM_ok_ne_nil hsE) V.postSlots
  rw [hpost, hpk.1, hm2]
  show s1.builders.toArray.size = _
  rw [hs1, hel, hdl, builderDepositTrace_head_builders hD h0,
    Inv.processSlots_identityStable V.slots]

/-- **B7 conservation, per step** (any `bls`). At a successful Gloas step at which no builder
deposit registers a fresh record, total builder balance at the post-state plus the builder debits
of the step's `apply_withdrawals` (`builderDebits` of `stepWithdrawals`, the withdrawals its
`process_withdrawals` applies: `[]` on an early return) equals total builder balance at the
pre-step state plus the builder deposits credited along the deposit trace (`builderCredits`); the
bid, the settlement and the exits are balance-neutral. It is the sum over the registry of WSL's
`GStepView.builder_balance_equation` (B5(i) per step); its hypotheses are that lemma's: the G3
invariants at the pre-state, the N7 bounds at the post-state, quorum positivity and
`2 ≤ SLOTS_PER_EPOCH`. A step that registers a fresh record is B1's (`GStepView.registration`). -/
theorem GStepView.builder_total_noRegister {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {preB postB : Gloas.BeaconState P} {preExec postExec : BlockChain}
    {preParent postParent : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH)
    (g5 : Inv.PendingCovered preB) (g3 : Inv.PendingRefsInRange preB)
    (g4 : Inv.ExitedHaveNoPending preB) (g7 : Inv.NoLiveWeightOnLatestBid preB)
    (g8 : Inv.LatestBidCoherence preB) (fe : Inv.FutureEmpty preB)
    (hA : Inv.LatestBidBuilderActive preB)
    (validatorsBound : postB.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : postB.builders.toArray.size ≤ 2 ^ 40)
    {trD : List (Gloas.BeaconState P)} (hD : builderDepositTrace ccfg bls V.postSlots b = .ok trD)
    (hno : NoRegister ccfg bls trD (blockBuilderDeposits b)) :
    ∃ ws : List Withdrawal, stepWithdrawals ccfg bls V.postSlots b.message = .ok ws ∧
      totalBuilderBalance postB + builderDebits ws preB.builders.toArray.size =
        totalBuilderBalance preB +
          builderCredits ccfg bls trD (blockBuilderDeposits b) preB.builders.toArray.size := by
  have hsz := V.size_noRegister hD hno
  obtain ⟨ws, hws⟩ := stepWithdrawals_ok (ccfg := ccfg) (bls := bls) V.processBlock
  refine ⟨ws, hws, ?_⟩
  unfold totalBuilderBalance builderDebits builderCredits
  have := sum_map_pointwise (fun c : Gloas.Builder => c.balance.toNat) preB.builders.toArray.toList
    postB.builders.toArray.toList (routedAt ws) (fun i => creditedAt ccfg bls i trD
      (blockBuilderDeposits b)) (by simpa using hsz) (fun i x x' hx hx' => by
      simp only [Array.getElem?_toList] at hx hx'
      have hi : i < 2 ^ 64 := by
        have := (Array.getElem?_eq_some_iff.mp hx').1; omega
      obtain ⟨bi, hbi⟩ := (U64.ofNat?_ok_iff (site := "BuilderIndex")).mpr hi
      have hbiN : bi.toNat = i := U64.toNat_ofNat? hbi
      obtain ⟨ws', bb', hws', hbb', -, heq, -⟩ := V.builder_balance_equation quorumPositive
        slotsPerEpoch g5 g3 g4 g7 g8 fe hA validatorsBound buildersBound (bi := bi)
        (by rw [hbiN]; exact hx) hD (by rw [hbiN]; exact hno i)
      rw [hws] at hws'; cases hws'
      rw [hbiN, hx'] at hbb'; cases hbb'
      simp only [routedAt, hbi]
      rw [hbiN] at heq
      exact heq)
  simpa using this

end JauneConsensus.Facts.Gloas
