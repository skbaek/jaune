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

/-! ## Conservation with registrations (G3d) -/

/-- Builder slot `i`'s balance in `ℕ`, `0` past the registry's end. -/
def balOf (x : Gloas.BeaconState P) (i : Nat) : Nat :=
  match x.builders.toArray[i]? with
  | some c => c.balance.toNat
  | none => 0

/-- What one builder deposit outcome credits to slot `i`: a top-up's or a registration's amount. -/
def depositCreditAll (i : Nat) : BuilderDepositOutcome → Nat
  | .topUp j a _ => if j = i then a.toNat else 0
  | .register j a => if j = i then a.toNat else 0
  | _ => 0

/-- The deposits credited to slot `i` along a deposit trace, registrations included
(statements.md's `creditedDepositsAt`, `creditedAt` plus a fresh record's own amount). -/
def creditedAllAt (ccfg : Config) (bls : Bool) (i : Nat) :
    List (Gloas.BeaconState P) → List Gloas.BuilderDepositRequest → Nat
  | m :: tr, r :: rs =>
    (match classifyBuilderDeposit ccfg bls m r with
      | .ok o => depositCreditAll i o
      | .error _ => 0) + creditedAllAt ccfg bls i tr rs
  | _, _ => 0

/-- **B7 conservation's credit term with registrations**: the deposits credited along the deposit
trace, top-ups and fresh records' amounts, over the first `n` registry slots. -/
def builderCreditsAll (ccfg : Config) (bls : Bool) (trD : List (Gloas.BeaconState P))
    (rs : List Gloas.BuilderDepositRequest) (n : Nat) : Nat :=
  ((List.range n).map (fun i => creditedAllAt ccfg bls i trD rs)).sum

/-- Without a registration at `i`, the two credit terms agree. -/
theorem creditedAllAt_of_noRegister {ccfg : Config} {bls : Bool} {i : Nat} :
    ∀ (tr : List (Gloas.BeaconState P)) (rs : List Gloas.BuilderDepositRequest),
      NoRegisterAt ccfg bls i tr rs → creditedAllAt ccfg bls i tr rs = creditedAt ccfg bls i tr rs
  | [], _, _ => by simp [creditedAllAt, creditedAt]
  | _ :: _, [], _ => by simp [creditedAllAt, creditedAt]
  | m :: tr, r :: rs, h => by
    simp only [NoRegisterAt] at h
    simp only [creditedAllAt, creditedAt, creditedAllAt_of_noRegister tr rs h.2]
    congr 1
    cases hc : classifyBuilderDeposit ccfg bls m r with
    | error _ => rfl
    | ok o =>
      cases o with
      | register j a =>
        by_cases hj : j = i
        · subst hj; exact absurd hc (h.1 a)
        · simp [depositCreditAll, depositCredit, hj]
      | topUp j a reset => rfl
      | ignoredPrefix => rfl
      | ignoredBadSignature => rfl

/-- A registration lands on an empty slot: past the registry's end, or a reusable record, whose
balance is `0`. -/
theorem balOf_register {ccfg : Config} {bls : Bool} {m : Gloas.BeaconState P}
    {r : Gloas.BuilderDepositRequest} {i : Nat} {a : U64}
    (hc : classifyBuilderDeposit ccfg bls m r = .ok (.register i a)) : balOf m i = 0 := by
  rcases classifyBuilderDeposit_inv hc with ⟨-, h⟩ | ⟨-, _, _, _, _, h⟩ |
      ⟨-, -, -, -, ⟨-, h⟩ | ⟨-, -, idx, -, hidx, h⟩⟩
  · cases h
  · cases h
  · cases h
  · cases h
    obtain ⟨_, _, hcase⟩ := getIndexForNewBuilder_spec hidx
    rcases hcase with hsz | ⟨b0, hb0, _, hz⟩
    · unfold balOf; rw [Array.getElem?_eq_none (by omega)]
    · unfold balOf; rw [hb0]; simp only [hz]; rfl

/-- **The builder-deposit loop credits every slot its deposits** (top-ups and a fresh record's
amount), in `ℕ`: a registration lands on a slot of balance `0` (`balOf_register`). -/
theorem depositLoop_balAll {ccfg : Config} {bls : Bool} {i : Nat} :
    ∀ (rs : List Gloas.BuilderDepositRequest) (s : Gloas.BeaconState P) (tr : List (Gloas.BeaconState P)),
      scanM (Gloas.processBuilderDepositRequest { cfg := ccfg, blsActive := bls }) s rs = .ok tr →
      balOf (traceLast s tr) i = balOf s i + creditedAllAt ccfg bls i tr rs
  | [], s, tr, h => by
    simp only [scanM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [creditedAllAt, traceLast]
  | r :: rs, s, tr, h => by
    obtain ⟨s', rest, h1, h2, rfl⟩ := scanM_cons_ok h
    have h1' := h1
    rw [processBuilderDepositRequest_eq] at h1'
    obtain ⟨o, hc, -⟩ := bind_eq_ok_iff.mp h1'
    obtain ⟨hpre, hbad, htop, hreg⟩ :=
      classifyBuilderDeposit_effect (ctx := { cfg := ccfg, blsActive := bls }) hc h1
    have step : balOf s' i = balOf s i + depositCreditAll i o := by
      cases o with
      | ignoredPrefix => rw [hpre rfl]; simp [depositCreditAll]
      | ignoredBadSignature => rw [hbad rfl]; simp [depositCreditAll]
      | topUp j a reset =>
        obtain ⟨c, c', hc0, hc', -, hoth, -, -, -, -, hbal, -⟩ := htop j a reset rfl
        by_cases hji : j = i
        · subst hji
          unfold balOf; rw [hc0, hc']; simp [depositCreditAll, hbal]
        · unfold balOf; rw [hoth i (Ne.symm hji)]; simp [depositCreditAll, hji]
      | register j a =>
        obtain ⟨addr, e, -, -, hat, -, hoth, -⟩ := hreg j a rfl
        by_cases hji : j = i
        · subst hji
          have h0 := balOf_register hc
          unfold balOf at h0 ⊢; rw [hat]
          simp [depositCreditAll, freshBuilder]
          omega
        · unfold balOf; rw [hoth i (Ne.symm hji)]; simp [depositCreditAll, hji]
    have ih := depositLoop_balAll (i := i) rs s' rest h2
    rw [traceLast_scan_cons h2, ih, step]
    simp only [creditedAllAt, hc]
    omega

/-- Without a registration at `i`, the deposit loop keeps slot `i` empty. -/
theorem depositLoop_absent {ccfg : Config} {bls : Bool} {i : Nat} :
    ∀ (rs : List Gloas.BuilderDepositRequest) (s : Gloas.BeaconState P) (tr : List (Gloas.BeaconState P)),
      scanM (Gloas.processBuilderDepositRequest { cfg := ccfg, blsActive := bls }) s rs = .ok tr →
      NoRegisterAt ccfg bls i tr rs → s.builders.toArray[i]? = none →
      (traceLast s tr).builders.toArray[i]? = none
  | [], s, tr, h, _, hn => by
    simp only [scanM, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hn
  | r :: rs, s, tr, h, hno, hn => by
    obtain ⟨s', rest, h1, h2, rfl⟩ := scanM_cons_ok h
    have h1' := h1
    rw [processBuilderDepositRequest_eq] at h1'
    obtain ⟨o, hc, -⟩ := bind_eq_ok_iff.mp h1'
    obtain ⟨hpre, hbad, htop, hreg⟩ :=
      classifyBuilderDeposit_effect (ctx := { cfg := ccfg, blsActive := bls }) hc h1
    simp only [NoRegisterAt] at hno
    have hn' : s'.builders.toArray[i]? = none := by
      cases o with
      | ignoredPrefix => rw [hpre rfl]; exact hn
      | ignoredBadSignature => rw [hbad rfl]; exact hn
      | topUp j a reset =>
        obtain ⟨c, c', hc0, -, -, hoth, -⟩ := htop j a reset rfl
        have hji : j ≠ i := fun hji => by rw [hji, hn] at hc0; cases hc0
        rw [hoth i (Ne.symm hji)]; exact hn
      | register j a =>
        obtain ⟨-, -, -, -, -, -, hoth, -⟩ := hreg j a rfl
        have hji : j ≠ i := fun hji => hno.1 a (by rw [hc, hji])
        rw [hoth i (Ne.symm hji)]; exact hn
    rw [traceLast_scan_cons h2]
    exact depositLoop_absent rs s' rest h2 hno.2 hn'

/-- A request that is not `NoRegisterAt i` registers `i` at some trace position. -/
theorem exists_register_of_not {ccfg : Config} {bls : Bool} {i : Nat} :
    ∀ (tr : List (Gloas.BeaconState P)) (rs : List Gloas.BuilderDepositRequest),
      ¬ NoRegisterAt ccfg bls i tr rs →
      ∃ (k : Nat) (m : Gloas.BeaconState P) (r : Gloas.BuilderDepositRequest) (a : U64),
        tr[k]? = some m ∧ rs[k]? = some r ∧
        classifyBuilderDeposit ccfg bls m r = .ok (.register i a)
  | [], _, h => absurd trivial h
  | _ :: _, [], h => absurd trivial h
  | m :: tr, r :: rs, h => by
    simp only [NoRegisterAt, not_and_or] at h
    rcases h with h | h
    · simp only [not_forall, not_not] at h
      obtain ⟨a, ha⟩ := h
      exact ⟨0, m, r, a, rfl, rfl, ha⟩
    · obtain ⟨k, m', r', a, h1, h2, h3⟩ := exists_register_of_not tr rs h
      exact ⟨k + 1, m', r', a, h1, h2, h3⟩

/-- A list's mapped sum is the sum over any number of positions covering it, `0` past its end. -/
theorem sum_map_eq_range {β : Type} (g : β → Nat) :
    ∀ (l : List β) (n : Nat), l.length ≤ n →
      (l.map g).sum = ((List.range n).map (fun i => match l[i]? with
        | some c => g c
        | none => 0)).sum
  | [], n, _ => by
    simp
  | c :: l, 0, h => by simp at h
  | c :: l, n + 1, h => by
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      List.getElem?_cons_zero, List.getElem?_cons_succ]
    rw [sum_map_eq_range g l n (by simpa using h)]

/-- A registry total is the sum of `balOf` over any number of slots covering the registry. -/
theorem total_eq_sum_balOf (x : Gloas.BeaconState P) (n : Nat)
    (hn : x.builders.toArray.size ≤ n) :
    totalBuilderBalance x = ((List.range n).map (balOf x)).sum := by
  unfold totalBuilderBalance
  rw [sum_map_eq_range (fun c : Gloas.Builder => c.balance.toNat) _ n (by simpa using hn)]
  congr 1
  apply List.map_congr_left
  intro j _
  rcases h : x.builders.toArray[j]? with _ | c <;> simp [balOf, h]

/-- Pointwise balance equations over the first `N` slots sum. -/
theorem sum_range_pointwise (f r p c : Nat → Nat) :
    ∀ N : Nat, (∀ i, i < N → f i + r i = p i + c i) →
      ((List.range N).map f).sum + ((List.range N).map r).sum =
        ((List.range N).map p).sum + ((List.range N).map c).sum
  | 0, _ => by simp
  | n + 1, h => by
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    have ih := sum_range_pointwise f r p c n (fun i hi => h i (by omega))
    have hn := h n (by omega)
    omega

/-- The step's registry never shrinks, and a slot that no request registers and that is empty at
the pre-state is empty at the post-state. -/
theorem GStepView.registry_shape {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {preB postB : Gloas.BeaconState P} {preExec postExec : BlockChain}
    {preParent postParent : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    {trD : List (Gloas.BeaconState P)} (hD : builderDepositTrace ccfg bls V.postSlots b = .ok trD) :
    preB.builders.toArray.size ≤ postB.builders.toArray.size ∧
      ∀ i, NoRegisterAt ccfg bls i trD (blockBuilderDeposits b) →
        preB.builders.toArray[i]? = none → postB.builders.toArray[i]? = none := by
  obtain ⟨trD', trE, s1, s2, s3, hD', hE, -, hs1, hm2, -, hpk, -, hpost⟩ :=
    processBlock_builderPhases V.processBlock
  change builderDepositTrace ccfg bls V.postSlots b = _ at hD'
  change builderExitTrace ccfg bls V.postSlots b = _ at hE
  rw [hD] at hD'; cases hD'
  obtain ⟨s0, h0, hsD⟩ := builderDepositTrace_scan hD
  obtain ⟨trD', hD', hsE, -⟩ := builderExitTrace_ok hE
  rw [hD] at hD'; cases hD'
  have hb0 : s0.builders = preB.builders := by
    rw [builderDepositTrace_head_builders hD h0, Inv.processSlots_identityStable V.slots]
  have htl : traceLast s0 trD = traceLast V.postSlots trD :=
    traceLast_ne_nil (scanM_ok_ne_nil hsD) s0 V.postSlots
  have hlastD : trD[trD.length - 1]? = some (traceLast s0 trD) := by
    rw [← List.getLast?_eq_getElem?]; exact getLast?_of_traceLast (scanM_ok_ne_nil hsD) s0
  have hlastE : trE[trE.length - 1]? = some (traceLast V.postSlots trE) := by
    rw [← List.getLast?_eq_getElem?]; exact getLast?_of_traceLast (scanM_ok_ne_nil hsE) V.postSlots
  have hpost' : postB.builders.toArray.size = (traceLast V.postSlots trE).builders.toArray.size := by
    rw [hpost, hpk.1, hm2]; show s1.builders.toArray.size = _; rw [hs1]
  refine ⟨?_, fun i hno hn => ?_⟩
  · have szD := scanM_inv (fun x : Gloas.BeaconState P =>
        s0.builders.toArray.size ≤ x.builders.toArray.size)
      (fun x a y hI hy => by
        rcases (Inv.depReq_cases hy).2 with heq | ⟨_, _, _, _, _, hsz, _⟩ | ⟨_, _, _, _, _, _, _, _, hsz, _⟩
        · rw [heq]; exact hI
        · omega
        · omega) _ (le_refl _) hsD _ _ hlastD
    have szE := scanM_inv (fun x : Gloas.BeaconState P =>
        (traceLast V.postSlots trD).builders.toArray.size ≤ x.builders.toArray.size)
      (fun x a y hI hy => by
        rcases (Inv.exitReq_cases hy).2 with heq | ⟨_, _, _, _, _, _, _, _, hsz, _⟩
        · rw [heq]; exact hI
        · omega) _ (le_refl _) hsE _ _ hlastE
    rw [htl] at szD
    rw [← hb0, hpost']; omega
  · have hnD := depositLoop_absent _ _ _ hsD hno (by rw [hb0]; exact hn)
    rw [htl] at hnD
    have hnE := scanM_inv (fun x : Gloas.BeaconState P => x.builders.toArray[i]? = none)
      (fun x a y hI hy => by
        rcases (Inv.exitReq_cases hy).2 with heq | ⟨j, c, _, hc, _, _, _, _, _, hoth⟩
        · rw [heq]; exact hI
        · have hji : j ≠ i := fun hji => by rw [hji, hI] at hc; cases hc
          rw [hoth i (Ne.symm hji)]; exact hI) _ hnD hsE _ _ hlastE
    have : (traceLast V.postSlots trE).builders.toArray.size ≤ i := by
      by_contra hlt
      rw [Array.getElem?_eq_getElem (by omega)] at hnE; cases hnE
    exact Array.getElem?_eq_none (by omega)

/-- **B7 conservation, per step, with registrations** (any `bls`; G3d). At a successful Gloas
step whose pre-state satisfies FinalizedNotAhead (with the G3 invariants and the N7 bounds), total
builder balance at the post-state plus the builder debits of the step's `apply_withdrawals`
(`builderDebits` of `stepWithdrawals`) equals total builder balance at the pre-state plus the
builder deposits credited along the deposit trace, top-ups and the fresh records' own amounts
(`builderCreditsAll`), all over the post-state's registry. A slot that no request registers is
WSL's per-builder B5(i) equation (`GStepView.builder_balance_equation`); a freshly registered
slot's post-state balance is its deposit-loop balance (`depositLoop_balAll`), which no exit and no
withdrawal touches (`GStepView.fresh_survives`, under FinalizedNotAhead); a registration lands on
an empty slot (`balOf_register`). -/
theorem GStepView.builder_total {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {preB postB : Gloas.BeaconState P} {preExec postExec : BlockChain}
    {preParent postParent : ParentPayload P} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (V : GStepView cfg ccfg bls preB preExec preParent b env? postB postExec postParent)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH)
    (fna : Inv.FinalizedNotAhead preB)
    (g5 : Inv.PendingCovered preB) (g3 : Inv.PendingRefsInRange preB)
    (g4 : Inv.ExitedHaveNoPending preB) (g7 : Inv.NoLiveWeightOnLatestBid preB)
    (g8 : Inv.LatestBidCoherence preB) (fe : Inv.FutureEmpty preB)
    (hA : Inv.LatestBidBuilderActive preB)
    (validatorsBound : postB.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : postB.builders.toArray.size ≤ 2 ^ 40)
    {trD : List (Gloas.BeaconState P)} (hD : builderDepositTrace ccfg bls V.postSlots b = .ok trD) :
    ∃ ws : List Withdrawal, stepWithdrawals ccfg bls V.postSlots b.message = .ok ws ∧
      totalBuilderBalance postB + builderDebits ws postB.builders.toArray.size =
        totalBuilderBalance preB +
          builderCreditsAll ccfg bls trD (blockBuilderDeposits b) postB.builders.toArray.size := by
  obtain ⟨hsize, habs⟩ := V.registry_shape hD
  obtain ⟨ws, hws⟩ := stepWithdrawals_ok (ccfg := ccfg) (bls := bls) V.processBlock
  refine ⟨ws, hws, ?_⟩
  obtain ⟨s0, h0, hsD⟩ := builderDepositTrace_scan hD
  have hb0 : s0.builders = preB.builders := by
    rw [builderDepositTrace_head_builders hD h0, Inv.processSlots_identityStable V.slots]
  have htl : traceLast s0 trD = traceLast V.postSlots trD :=
    traceLast_ne_nil (scanM_ok_ne_nil hsD) s0 V.postSlots
  rw [total_eq_sum_balOf postB _ (le_refl _), total_eq_sum_balOf preB _ hsize]
  unfold builderDebits builderCreditsAll
  refine sum_range_pointwise _ _ _ _ _ (fun i hi => ?_)
  have hi64 : i < 2 ^ 64 := by omega
  obtain ⟨bi, hbi⟩ := (U64.ofNat?_ok_iff (site := "BuilderIndex")).mpr hi64
  have hbiN : bi.toNat = i := U64.toNat_ofNat? hbi
  have hrt : routedAt ws i = routedSum bi ws := by simp only [routedAt, hbi]
  rw [hrt]
  by_cases hno : NoRegisterAt ccfg bls i trD (blockBuilderDeposits b)
  · rw [creditedAllAt_of_noRegister _ _ hno]
    cases hpre : preB.builders.toArray[i]? with
    | none =>
      have := habs i hno hpre
      rw [Array.getElem?_eq_none_iff] at this
      omega
    | some bb =>
      obtain ⟨ws', bb', hws', hbb', -, heq, -⟩ := V.builder_balance_equation quorumPositive
        slotsPerEpoch g5 g3 g4 g7 g8 fe hA validatorsBound buildersBound (bi := bi)
        (by rw [hbiN]; exact hpre) hD (by rw [hbiN]; exact hno)
      rw [hws] at hws'; cases hws'
      rw [hbiN] at hbb' heq
      simp only [balOf, hbb', hpre]
      exact heq
  · obtain ⟨k, m, r, a, hm, hr, hcl⟩ := exists_register_of_not _ _ hno
    obtain ⟨m1, m1', hm1, hm1', hcall⟩ := scanM_ok_step hsD k r hr
    rw [hm] at hm1; cases hm1
    have hrest := scanM_ok_drop _ (k + 1) hsD hm1'
    obtain ⟨addr, e, bal, -, he, -, hat2, -⟩ :=
      register_then_topUp slotsPerEpoch (ctx := { cfg := ccfg, blsActive := bls }) hcl hcall hrest
    rw [htl] at hat2
    obtain ⟨hpostR, ws', hws', hz⟩ := V.fresh_survives slotsPerEpoch quorumPositive fna g5 g3 g4 g7
      g8 fe hA validatorsBound buildersBound hD hm hr hcl he hat2 rfl rfl
    rw [hws] at hws'; cases hws'
    have hbal := depositLoop_balAll (i := i) _ _ _ hsD
    rw [htl] at hbal
    have h1 : balOf (traceLast V.postSlots trD) i = bal.toNat := by simp [balOf, hat2]
    have h2 : balOf s0 i = balOf preB i := by simp only [balOf, hb0]
    have h3 : balOf postB i = bal.toNat := by simp [balOf, hpostR]
    rw [h3, hz bi hbiN]
    omega

end JauneConsensus.Facts.Gloas
