import JauneConsensus.Facts.Gloas.BuilderTraces
import JauneConsensus.Facts.Gloas.BuilderFrames

/-!
# Builder request traces and foldlM prefixes (goal `eip8282-gloas-cross-layer-v1`, LINK)

Two forms of the per-request evaluation points of the builder loops of
`apply_parent_execution_payload`:

* the traces of `BuilderTraces.lean` (`builderDepositTrace`, `builderExitTrace`, built with
  `scanM`): request `k` runs from `tr[k]` to `tr[k+1]`;
* the foldlM-prefix forms of `BuilderFrames.lean` (`TopUpResetIn`, `ExitInitiateIn`): request `r`
  in `pre ++ r :: post` runs from `pre.foldlM … s0`.

They are the same points: the state after the first `k` requests of a scan is its `k`-th element
(`scanM_ok_prefix`). The link lemmas below are bidirectional:

* `topUpResetIn_iff_scan`, `exitInitiateIn_iff_scan`: for any successful scan from `s0`;
* `topUpResetIn_iff_trace`, `exitInitiateIn_iff_trace`: at the block's traces, whose first
  states are the `s0`/`s1` the prefix forms start from.
-/

namespace JauneConsensus.Facts.Gloas

open JauneConsensus JauneConsensus.Facts

variable {P : Preset}

/-! ## Scans and fold prefixes -/

/-- The state a scan reaches after a prefix of its list is the fold of that prefix. -/
theorem scanM_ok_prefix {σ α : Type} {f : σ → α → M σ} :
    ∀ (pre rest : List α) {s : σ} {tr : List σ}, scanM f s (pre ++ rest) = .ok tr →
      ∃ st, pre.foldlM f s = .ok st ∧ tr[pre.length]? = some st
  | [], rest, s, tr, h => ⟨s, rfl, scanM_ok_head h⟩
  | a :: pre, rest, s, tr, h => by
    simp only [List.cons_append, scanM, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i s' hs'
      split at h
      · cases h
      · rename_i rest' hrest
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨st, h1, h2⟩ := scanM_ok_prefix pre rest hrest
        refine ⟨st, ?_, by simpa using h2⟩
        rw [List.foldlM_cons, hs']
        exact h1

/-- A successful scan ends at the fold of the whole list. -/
theorem scanM_ok_foldlM {σ α : Type} {f : σ → α → M σ} {s : σ} {xs : List α} {tr : List σ}
    (h : scanM f s xs = .ok tr) : xs.foldlM f s = .ok (traceLast s tr) := by
  obtain ⟨st, h1, h2⟩ := scanM_ok_prefix xs [] (by simpa using h)
  have hlen := scanM_ok_length h
  have hne := scanM_ok_ne_nil h
  rw [h1]
  congr 1
  have : tr.getLast? = some st := by
    rw [List.getLast?_eq_getElem?, hlen]; simpa using h2
  simp [traceLast, this]

/-- A prefix-form statement about request `r` (reached by folding `pre`) is a statement about
the consecutive scan states `tr[k] → tr[k+1]` with `k = pre.length`, and back. -/
theorem prefix_iff_scan {σ α : Type} {f : σ → α → M σ} {s0 : σ} {xs : List α} {tr : List σ}
    (h : scanM f s0 xs = .ok tr) (Q : σ → α → Prop) :
    (∃ pre r post st, xs = pre ++ r :: post ∧ pre.foldlM f s0 = .ok st ∧ Q st r) ↔
      ∃ k r m m', xs[k]? = some r ∧ tr[k]? = some m ∧ tr[k + 1]? = some m' ∧ f m r = .ok m' ∧
        Q m r := by
  constructor
  · rintro ⟨pre, r, post, st, rfl, hf, hq⟩
    obtain ⟨st', hf', hk⟩ := scanM_ok_prefix pre (r :: post) h
    rw [hf] at hf'; cases hf'
    have hr : (pre ++ r :: post)[pre.length]? = some r := by simp
    obtain ⟨m, m', hm, hm', hstep⟩ := scanM_ok_step h pre.length r hr
    rw [hk] at hm; cases hm
    exact ⟨pre.length, r, st, m', hr, hk, hm', hstep, hq⟩
  · rintro ⟨k, r, m, m', hr, hm, -, -, hq⟩
    have hk : k < xs.length := (List.getElem?_eq_some_iff.mp hr).1
    have hsplit : xs = xs.take k ++ r :: xs.drop (k + 1) := by
      conv => lhs; rw [← List.take_append_drop k xs]
      rw [List.drop_eq_getElem_cons hk]
      congr 2
      exact (List.getElem?_eq_some_iff.mp hr).2
    obtain ⟨st, hf, hst⟩ := scanM_ok_prefix (xs.take k) (r :: xs.drop (k + 1)) (hsplit ▸ h)
    have hlen : (xs.take k).length = k := by simp; omega
    rw [hlen, hm] at hst; cases hst
    exact ⟨xs.take k, r, xs.drop (k + 1), m, hsplit, hf, hq⟩

/-! ## The link, for any scan -/

/-- `TopUpResetIn` over a scan of the deposit loop: some request `k` is classified a reset top-up
of builder `i` at `tr[k]`, and its call runs `tr[k] → tr[k+1]`. -/
theorem topUpResetIn_iff_scan {ctx : Ctx} {s0 : Gloas.BeaconState P}
    {rs : List Gloas.BuilderDepositRequest} {tr : List (Gloas.BeaconState P)}
    (h : scanM (Gloas.processBuilderDepositRequest ctx) s0 rs = .ok tr) (i : Nat) :
    TopUpResetIn ctx s0 rs i ↔
      ∃ k r m m', rs[k]? = some r ∧ tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
        Gloas.processBuilderDepositRequest ctx m r = .ok m' ∧
        classifyBuilderDeposit ctx.cfg ctx.blsActive m r = .ok (.topUp i r.amount true) :=
  prefix_iff_scan h (fun m r => classifyBuilderDeposit ctx.cfg ctx.blsActive m r = .ok (.topUp i r.amount true))

/-- `ExitInitiateIn` over a scan of the exit loop: some request `k` is classified `initiate i` at
`tr[k]`, and its call runs `tr[k] → tr[k+1]`. -/
theorem exitInitiateIn_iff_scan {cfg : Config} {s1 : Gloas.BeaconState P}
    {es : List Gloas.BuilderExitRequest} {tr : List (Gloas.BeaconState P)}
    (h : scanM (Gloas.processBuilderExitRequest cfg) s1 es = .ok tr) (i : Nat) :
    ExitInitiateIn cfg s1 es i ↔
      ∃ k e m m', es[k]? = some e ∧ tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
        Gloas.processBuilderExitRequest cfg m e = .ok m' ∧
        classifyBuilderExit cfg m e = .ok (.initiate i) :=
  prefix_iff_scan h (fun m e => classifyBuilderExit cfg m e = .ok (.initiate i))

/-! ## The block's traces are scans from their first states -/

/-- The deposit trace is the scan of the block's builder deposits from its first state (for an
EMPTY parent, the empty scan from `st`). -/
theorem builderDepositTrace_scan {ccfg : Config} {bls : Bool} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} {tr : List (Gloas.BeaconState P)}
    (h : builderDepositTrace ccfg bls st b = .ok tr) :
    ∃ s0, tr[0]? = some s0 ∧
      scanM (Gloas.processBuilderDepositRequest { cfg := ccfg, blsActive := bls }) s0
        (blockBuilderDeposits b) = .ok tr := by
  rcases builderDepositTrace_ok h with ⟨hd, -, rfl⟩ | ⟨s0, -, hs⟩
  · exact ⟨st, rfl, by rw [hd]; rfl⟩
  · exact ⟨s0, scanM_ok_head hs, hs⟩

/-- The exit trace is the scan of the block's builder exits from its first state. -/
theorem builderExitTrace_scan {ccfg : Config} {bls : Bool} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} {tr : List (Gloas.BeaconState P)}
    (h : builderExitTrace ccfg bls st b = .ok tr) :
    ∃ s1, tr[0]? = some s1 ∧
      scanM (Gloas.processBuilderExitRequest ccfg) s1 (blockBuilderExits b) = .ok tr := by
  obtain ⟨trD, _, hs, _⟩ := builderExitTrace_ok h
  exact ⟨_, scanM_ok_head hs, hs⟩

/-! ## The link at the block's traces -/

/-- **LINK, deposits.** At the block's deposit trace `trD` (first state `s0`, the state the
builder-deposit loop starts from), `TopUpResetIn` over the block's builder deposits holds iff some
request `k` is classified a reset top-up of builder `i` at `trD[k]`, its call running
`trD[k] → trD[k+1]`. -/
theorem topUpResetIn_iff_trace {ctx : Ctx} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} {trD : List (Gloas.BeaconState P)} {s0 : Gloas.BeaconState P}
    (hD : builderDepositTrace ctx.cfg ctx.blsActive st b = .ok trD) (h0 : trD[0]? = some s0)
    (i : Nat) :
    TopUpResetIn ctx s0 (blockBuilderDeposits b) i ↔
      ∃ k r m m', (blockBuilderDeposits b)[k]? = some r ∧ trD[k]? = some m ∧
        trD[k + 1]? = some m' ∧
        Gloas.processBuilderDepositRequest ctx m r = .ok m' ∧
        classifyBuilderDeposit ctx.cfg ctx.blsActive m r = .ok (.topUp i r.amount true) := by
  obtain ⟨s0', h0', hs⟩ := builderDepositTrace_scan hD
  rw [h0] at h0'; cases h0'
  rw [← Gloas.processBuilderDepositRequest_ctx] at hs
  exact topUpResetIn_iff_scan hs i

/-- **LINK, exits.** At the block's exit trace `trE` (first state `s1`, the last deposit-trace
state, where the builder-exit loop starts), `ExitInitiateIn` over the block's builder exits holds
iff some request `k` is classified `initiate i` at `trE[k]`, its call running `trE[k] → trE[k+1]`. -/
theorem exitInitiateIn_iff_trace {ccfg : Config} {bls : Bool} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} {trE : List (Gloas.BeaconState P)} {s1 : Gloas.BeaconState P}
    (hE : builderExitTrace ccfg bls st b = .ok trE) (h1 : trE[0]? = some s1) (i : Nat) :
    ExitInitiateIn ccfg s1 (blockBuilderExits b) i ↔
      ∃ k e m m', (blockBuilderExits b)[k]? = some e ∧ trE[k]? = some m ∧
        trE[k + 1]? = some m' ∧
        Gloas.processBuilderExitRequest ccfg m e = .ok m' ∧
        classifyBuilderExit ccfg m e = .ok (.initiate i) := by
  obtain ⟨s1', h1', hs⟩ := builderExitTrace_scan hE
  rw [h1] at h1'; cases h1'
  exact exitInitiateIn_iff_scan hs i


/-! ## The loops start from the block's pre-state builders -/

/-- The validator request loops of `apply_parent_execution_payload` (before the builder loops). -/
def validatorRequestLoops (ctx : Ctx) (requests : Gloas.ExecutionRequests)
    (state : Gloas.BeaconState P) : M (Gloas.BeaconState P) := do
  let mut state := state
  for op in requests.deposits.toArray do state := Gloas.processDepositRequest state op
  for op in requests.withdrawals.toArray do state ← Gloas.processWithdrawalRequest ctx.cfg state op
  for op in requests.consolidations.toArray do
    state ← Gloas.processConsolidationRequest ctx.cfg state op
  pure state

theorem applyParentPrefix_eq_settleThen (ctx : Ctx) (st : Gloas.BeaconState P)
    (requests : Gloas.ExecutionRequests) :
    Gloas.applyParentPrefix ctx st requests =
      settleThen ctx st requests (validatorRequestLoops ctx requests) := by
  rfl

theorem validatorRequestLoops_builders {ctx : Ctx} {requests : Gloas.ExecutionRequests}
    {x s0 : Gloas.BeaconState P} (h : validatorRequestLoops ctx requests x = .ok s0) :
    s0.builders = x.builders := by
  unfold validatorRequestLoops at h
  dsimp only at h
  obtain ⟨d, hd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have fd : BuilderFrame x d :=
    StepRel.forIn_array_rel builderFrame id (fun _ _ => by gvcg) _ _ hd
  have fw : BuilderFrame d w :=
    StepRel.forIn_array_rel builderFrame id (fun _ _ => by gvcg) _ _ hw
  have fc : BuilderFrame w c :=
    StepRel.forIn_array_rel builderFrame id (fun _ _ => by gvcg) _ _ hc
  exact fc.1.trans (fw.1.trans fd.1)

/-- The state the builder-deposit loop starts from has the pre-state's builders. -/
theorem applyParentPrefix_builders {ctx : Ctx} {st s0 : Gloas.BeaconState P}
    {requests : Gloas.ExecutionRequests} (h : Gloas.applyParentPrefix ctx st requests = .ok s0) :
    s0.builders = st.builders := by
  rw [applyParentPrefix_eq_settleThen] at h
  obtain ⟨x, hx, h⟩ := settleThen_ok h
  exact (validatorRequestLoops_builders h).trans hx

/-- The first deposit-trace state has the pre-state's builders. -/
theorem builderDepositTrace_head_builders {ccfg : Config} {bls : Bool} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} {tr : List (Gloas.BeaconState P)} {s0 : Gloas.BeaconState P}
    (h : builderDepositTrace ccfg bls st b = .ok tr) (h0 : tr[0]? = some s0) :
    s0.builders = st.builders := by
  rcases builderDepositTrace_ok h with ⟨-, -, rfl⟩ | ⟨s0', hp, hs⟩
  · simp at h0; rw [h0]
  · rw [scanM_ok_head hs] at h0; cases h0
    exact applyParentPrefix_builders hp

theorem traceLast_ne_nil {σ : Type} {tr : List σ} (h : tr ≠ []) (d d' : σ) :
    traceLast d tr = traceLast d' tr := by
  cases tr with
  | nil => exact absurd rfl h
  | cons x xs => exact traceLast_cons d d' x xs

theorem applyParentSuffix_builders {st0 s s' : Gloas.BeaconState P}
    (h : Gloas.applyParentSuffix st0 s = .ok s') : s'.builders = s.builders := by
  unfold Gloas.applyParentSuffix at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h; rfl

/-! ## B3 writers at the block's traces -/

/-- **B3, `withdrawableEpoch_writers` at the traces.** `withdrawableEpoch_writers` with its
existential loop states pinned to the block's traces and its prefix forms read through
`topUpResetIn_iff_trace`/`exitInitiateIn_iff_trace`: if `process_block` changes builder `i`'s
`withdrawable_epoch`, then the exit was initiated (`ExitInitiated`) by a builder exit request `k`
classified `initiate i` at the exit-trace state `trE[k]`, or a builder deposit request `k` is a
reset top-up of `i` at the deposit-trace state `trD[k]`, or `i` holds a fresh record
(`BuilderCreated`). Needs `2 <= SLOTS_PER_EPOCH`. -/
theorem withdrawableEpoch_writers_trace (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {ctx : Ctx}
    {pre post : Gloas.BeaconState P} {blk : Gloas.SignedBeaconBlock P}
    (h : Gloas.processBlock ctx pre blk.message = .ok post)
    {i : Nat} {b b' : Gloas.Builder} (hb : pre.builders.toArray[i]? = some b)
    (hb' : post.builders.toArray[i]? = some b') (hne : b.withdrawable_epoch ≠ b'.withdrawable_epoch) :
    ∃ trD trE, builderDepositTrace ctx.cfg ctx.blsActive pre blk = .ok trD ∧
      builderExitTrace ctx.cfg ctx.blsActive pre blk = .ok trE ∧
      ((ExitInitiated pre post i ∧
          ∃ k e m m', (blockBuilderExits blk)[k]? = some e ∧ trE[k]? = some m ∧
            trE[k + 1]? = some m' ∧ Gloas.processBuilderExitRequest ctx.cfg m e = .ok m' ∧
            classifyBuilderExit ctx.cfg m e = .ok (.initiate i)) ∨
        (∃ k r m m', (blockBuilderDeposits blk)[k]? = some r ∧ trD[k]? = some m ∧
            trD[k + 1]? = some m' ∧ Gloas.processBuilderDepositRequest ctx m r = .ok m' ∧
            classifyBuilderDeposit ctx.cfg ctx.blsActive m r = .ok (.topUp i r.amount true)) ∨
        BuilderCreated pre post i) := by
  obtain ⟨mid, hmid, -, hmap⟩ := processBlock_after_parent ctx pre blk.message post h
  have hm := hmap i
  rw [hb'] at hm
  obtain ⟨trD, trE, hD, hE, -, hEmpty, hFull⟩ := processParentExecutionPayload_traces hmid
  refine ⟨trD, trE, hD, hE, ?_⟩
  cases hc : mid.builders.toArray[i]? with
  | none => rw [hc] at hm; simp at hm
  | some cm =>
  rw [hc] at hm
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨hpk, hwe⟩ := hm
  cases hflag : (blk.message.body.signed_execution_payload_bid.message.parent_block_hash !=
      pre.latest_execution_payload_bid.block_hash)
  case true =>
    obtain ⟨rfl, -, -⟩ := hEmpty hflag
    rw [hb] at hc; cases hc
    exact absurd hwe.symm hne
  case false =>
  have hsuf := hFull hflag
  -- the deposit loop, from the first deposit-trace state
  obtain ⟨s0, h0, hsD⟩ := builderDepositTrace_scan hD
  rw [← Gloas.processBuilderDepositRequest_ctx] at hsD
  have hb0 : s0.builders.toArray[i]? = some b := by
    rw [builderDepositTrace_head_builders hD h0]; exact hb
  obtain ⟨_, c, hc1, hcase⟩ := builderDeposits_slot hspe (scanM_ok_foldlM hsD) hb0
  -- the exit loop, from the last deposit-trace state
  obtain ⟨trD', hD', hsE, -⟩ := builderExitTrace_ok hE
  rw [hD] at hD'; cases hD'
  have hneD := scanM_ok_ne_nil hsD
  rw [traceLast_ne_nil hneD pre s0] at hsE
  obtain ⟨_, c', hc', hpk', hcase'⟩ := builderExits_slot (scanM_ok_foldlM hsE) hc1
  have hneE := scanM_ok_ne_nil hsE
  have hmidb : mid.builders = (traceLast (traceLast s0 trD) trE).builders := by
    rw [applyParentSuffix_builders hsuf, traceLast_ne_nil hneE pre]
  rw [hmidb, hc'] at hc; cases hc
  have hTop := topUpResetIn_iff_scan hsD i
  have hExit := exitInitiateIn_iff_scan hsE i
  rcases hcase with ⟨hp, hw⟩ | hR | ⟨hp, _⟩
  · rcases hcase' with hw' | ⟨hfar, hex⟩
    · exact absurd (hw.symm.trans (hw'.symm.trans hwe.symm)) hne
    · refine Or.inl ⟨⟨b, b', hb, hb', (hpk'.trans hp).symm.trans hpk.symm, hw ▸ hfar, ?_⟩,
        hExit.mp hex⟩
      intro hf
      exact hne (by rw [hf, ← hfar, hw])
  · exact Or.inr (Or.inl (hTop.mp hR))
  · refine Or.inr (Or.inr ⟨by rw [hb']; rfl, ?_⟩)
    rw [hb, hb']
    intro heq
    simp only [Option.map_some, Option.some.injEq] at heq
    exact hp (hpk'.symm.trans (hpk.symm.trans heq.symm))

end JauneConsensus.Facts.Gloas
