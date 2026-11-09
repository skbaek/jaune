import JauneConsensus.Facts.Gloas.Step
import JauneConsensus.GloasBlock

/-!
# Builder request traces (goal `eip8282-gloas-cross-layer-v1`, BF1)

The mid-list states of the builder-deposit and builder-exit loops of
`apply_parent_execution_payload` (`GloasBlock.lean`, `applyParentExecutionPayload`;
`specs/gloas/beacon-chain.md:1776`), the per-request evaluation points of statements.md B1-B4.

* `scanM f s xs`: the states `s, f s x₀, …` of a monadic left fold, in order;
* `applyParentPrefix`: `applyParentExecutionPayload` up to (and including) the consolidation
  loop, `applyParentSuffix`: its tail after the builder-exit loop;
* `builderDepositTrace ccfg bls st b` and `builderExitTrace ccfg bls st b`: the traces of the two
  builder loops, run from the state `processBlock` receives (`st`), with the same calls as
  `processParentExecutionPayload` (an EMPTY parent carries no requests, so both traces are
  `[st]`);
* the factoring: `applyParentExecutionPayload_eq` (the function is prefix, deposit loop, exit
  loop, suffix), `forIn_eq_scanM` (a loop is the last element of its trace), the step lemmas
  `builderDepositTrace_step`/`builderExitTrace_step` (`tr[k] → tr[k+1]` is one request call), and
  `processParentExecutionPayload_traces` (a successful parent settlement ends at the last
  exit-trace state, after the suffix).
-/

namespace JauneConsensus.Facts.Gloas

open JauneConsensus JauneConsensus.Facts

variable {P : Preset}

/-! ## Monadic scans -/

/-- The states of a monadic left fold: `[s, f s x₀, f (f s x₀) x₁, …]`. -/
def scanM {σ α : Type} (f : σ → α → M σ) : σ → List α → M (List σ)
  | s, [] => pure [s]
  | s, a :: as => do
    let s' ← f s a
    let rest ← scanM f s' as
    pure (s :: rest)

theorem scanM_ok_length {σ α : Type} {f : σ → α → M σ} :
    ∀ {xs : List α} {s : σ} {tr : List σ}, scanM f s xs = .ok tr → tr.length = xs.length + 1
  | [], s, tr, h => by simp only [scanM, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | a :: as, s, tr, h => by
    simp only [scanM, bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i rest hrest
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [scanM_ok_length hrest]

theorem scanM_ok_head {σ α : Type} {f : σ → α → M σ} :
    ∀ {xs : List α} {s : σ} {tr : List σ}, scanM f s xs = .ok tr → tr[0]? = some s
  | [], s, tr, h => by simp only [scanM, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | a :: as, s, tr, h => by
    simp only [scanM, bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; rfl

/-- Each consecutive pair of a trace is one call of `f` on the matching element. -/
theorem scanM_ok_step {σ α : Type} {f : σ → α → M σ} :
    ∀ {xs : List α} {s : σ} {tr : List σ}, scanM f s xs = .ok tr →
      ∀ k (a : α), xs[k]? = some a → ∃ m m', tr[k]? = some m ∧ tr[k + 1]? = some m' ∧ f m a = .ok m'
  | [], s, tr, h, k, a, hk => by simp at hk
  | x :: as, s, tr, h, k, a, hk => by
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
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          exact ⟨s, s', rfl, by simpa using scanM_ok_head hrest, hs'⟩
        | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          obtain ⟨m, m', h1, h2, h3⟩ := scanM_ok_step hrest k a hk
          exact ⟨m, m', by simpa using h1, by simpa using h2, h3⟩

/-- The last state of a trace, `d` for an empty list (traces are never empty,
`scanM_ok_ne_nil`). -/
def traceLast {σ : Type} (d : σ) (tr : List σ) : σ := tr.getLast?.elim d id

theorem traceLast_cons {σ : Type} (d d' x : σ) (xs : List σ) :
    traceLast d (x :: xs) = traceLast d' (x :: xs) := by
  simp [traceLast, List.getLast?_cons]

/-- A trace is always nonempty. -/
theorem scanM_ok_ne_nil {σ α : Type} {f : σ → α → M σ} {xs : List α} {s : σ} {tr : List σ}
    (h : scanM f s xs = .ok tr) : tr ≠ [] := by
  intro hnil; have := scanM_ok_length h; simp [hnil] at this

/-- A `for` loop whose body is one call of `f` is the last state of the scan. -/
theorem forIn_eq_scanM {σ α : Type} (f : σ → α → M σ) :
    ∀ (xs : List α) (s : σ),
      forIn xs s (fun a s => do let s' ← f s a; pure (ForInStep.yield s')) =
        (scanM f s xs).map (fun tr => traceLast s tr)
  | [], s => rfl
  | a :: as, s => by
    have ih := forIn_eq_scanM f as
    rw [List.forIn_cons]
    cases hf : f s a with
    | error e => simp [hf, scanM, bind, Except.bind, Except.map]
    | ok s' =>
      simp only [hf, scanM, bind, Except.bind, pure, Except.pure]
      have := ih s'
      simp only [bind, Except.bind, pure, Except.pure] at this
      rw [this]
      cases hs : scanM f s' as with
      | error e => rfl
      | ok rest =>
        have hne := scanM_ok_ne_nil hs
        cases rest with
        | nil => exact absurd rfl hne
        | cons r rs => simp [Except.map, traceLast, List.getLast?_cons]

end JauneConsensus.Facts.Gloas

namespace JauneConsensus.Gloas

open JauneConsensus.Facts.Gloas

variable {P : Preset}

/-! ## `applyParentExecutionPayload`, split at the builder loops -/

/-- `apply_parent_execution_payload` up to the builder-deposit loop: the four caps, the parent's
builder payment, and the deposit, withdrawal and consolidation request loops (a verbatim copy of
the body's first part). -/
def applyParentPrefix (ctx : Ctx) (state : BeaconState P) (requests : ExecutionRequests) :
    M (BeaconState P) := do
  let site := "apply_parent_execution_payload"
  let parentBid := state.latest_execution_payload_bid
  let parentSlot := state.latest_block_header.slot
  let parentEpoch ← computeEpochAtSlot P parentSlot
  require (requests.withdrawals.length ≤ P.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD)
    s!"{site}: len(requests.withdrawals) <= MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD"
  require (requests.consolidations.length ≤ P.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD)
    s!"{site}: len(requests.consolidations) <= MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD"
  require (requests.builder_deposits.length ≤ P.MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD)
    s!"{site}: len(requests.builder_deposits) <= MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD"
  require (requests.builder_exits.length ≤ P.MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD)
    s!"{site}: len(requests.builder_exits) <= MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD"
  let spe ← c64 P.SLOTS_PER_EPOCH
  let mut state := state
  if parentEpoch == (← getCurrentEpoch state) then
    let paymentIndex ← spe.add? (← parentSlot.mod? spe site) site
    state ← settleBuilderPayment state paymentIndex
  else if parentEpoch == (← getPreviousEpoch state) then
    let paymentIndex ← parentSlot.mod? spe site
    state ← settleBuilderPayment state paymentIndex
  else if U64.zero < parentBid.value then
    let w : BuilderPendingWithdrawal :=
      { fee_recipient := parentBid.fee_recipient, amount := parentBid.value,
        builder_index := parentBid.builder_index }
    state := { state with builder_pending_withdrawals := state.builder_pending_withdrawals.push w }
  for op in requests.deposits.toArray do state := processDepositRequest state op
  for op in requests.withdrawals.toArray do state ← processWithdrawalRequest ctx.cfg state op
  for op in requests.consolidations.toArray do state ← processConsolidationRequest ctx.cfg state op
  pure state

/-- `apply_parent_execution_payload` after the builder-exit loop: payload availability and the
latest block hash, read from the original state `st0`. -/
def applyParentSuffix (st0 state : BeaconState P) : M (BeaconState P) := do
  let site := "apply_parent_execution_payload"
  let parentBid := st0.latest_execution_payload_bid
  let parentSlot := st0.latest_block_header.slot
  let i ← parentSlot.mod? (← c64 P.SLOTS_PER_HISTORICAL_ROOT) site
  pure { state with
    execution_payload_availability := ← state.execution_payload_availability.set i.toNat true site
    latest_block_hash := parentBid.block_hash }

private theorem ite_bind_M {α β : Type} (c : Prop) [Decidable c] (x y : M α) (f : α → M β) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

/-- The factoring of `apply_parent_execution_payload` at the builder loops. -/
theorem applyParentExecutionPayload_eq (ctx : Ctx) (st : BeaconState P)
    (requests : ExecutionRequests) :
    applyParentExecutionPayload ctx st requests = (do
      let s ← applyParentPrefix ctx st requests
      let s ← forIn requests.builder_deposits.toArray.toList s
        (fun op s => do let s' ← processBuilderDepositRequest ctx s op; pure (ForInStep.yield s'))
      let s ← forIn requests.builder_exits.toArray.toList s
        (fun op s => do let s' ← processBuilderExitRequest ctx.cfg s op; pure (ForInStep.yield s'))
      applyParentSuffix st s) := by
  simp only [applyParentExecutionPayload, applyParentPrefix, applyParentSuffix, bind_assoc,
    Array.forIn_toList, ite_bind_M, pure_bind]


/-- An EMPTY parent's `requests == ExecutionRequests.empty` check leaves no builder requests
(the derived `BEq` compares array sizes first, so no lawfulness of the element `BEq` is needed). -/
theorem builderLists_of_beq_empty {r : ExecutionRequests} (h : (r == ExecutionRequests.empty) = true) :
    r.builder_deposits.toArray = #[] ∧ r.builder_exits.toArray = #[] := by
  rcases r with ⟨d, w, c, ⟨bd⟩, ⟨be⟩⟩
  simp only [ExecutionRequests.empty, ProgressiveListS.empty] at h
  conv at h => lhs; whnf
  generalize (d == _) = x at h
  cases x
  · cases h
  · dsimp only at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨-, -, hbd, hbe⟩ := h
    change (bd.isEqv #[] (· == ·)) = true at hbd
    change (be.isEqv #[] (· == ·)) = true at hbe
    exact ⟨Array.size_eq_zero_iff.mp (Array.isEqv_iff_rel.mp hbd).1,
      Array.size_eq_zero_iff.mp (Array.isEqv_iff_rel.mp hbe).1⟩

end JauneConsensus.Gloas

namespace JauneConsensus.Gloas

variable {P : Preset}

/-- `process_builder_deposit_request` reads only the configuration and the BLS switch of its
context. -/
theorem processBuilderDepositRequest_ctx (ctx : Ctx) :
    processBuilderDepositRequest (P := P) ctx =
      processBuilderDepositRequest { cfg := ctx.cfg, blsActive := ctx.blsActive } := rfl

/-- `applyParentPrefix` reads only the configuration of its context. -/
theorem applyParentPrefix_ctx (ctx : Ctx) :
    applyParentPrefix (P := P) ctx = applyParentPrefix { cfg := ctx.cfg, blsActive := ctx.blsActive } :=
  rfl

end JauneConsensus.Gloas

namespace JauneConsensus.Facts.Gloas

open JauneConsensus JauneConsensus.Facts

variable {P : Preset}

/-! ## The traces -/

/-- The builder deposit requests a block applies (its parent's, `parent_execution_requests`). -/
abbrev blockBuilderDeposits (b : Gloas.SignedBeaconBlock P) : List Gloas.BuilderDepositRequest :=
  b.message.body.parent_execution_requests.builder_deposits.toArray.toList

/-- The builder exit requests a block applies. -/
abbrev blockBuilderExits (b : Gloas.SignedBeaconBlock P) : List Gloas.BuilderExitRequest :=
  b.message.body.parent_execution_requests.builder_exits.toArray.toList

/-- The mid-list states of the builder-deposit loop of `processBlock`'s parent settlement, run
from the state `processBlock` receives: for a FULL parent, the state after the payment settlement
and the deposit, withdrawal and consolidation request loops, then the state after each builder
deposit request (length `#builder_deposits + 1`); for an EMPTY parent, `[st]` (the requests must
then be empty). The calls and checks are those of `processParentExecutionPayload`, except that
the FULL parent's `hash_tree_root(requests) == parent_bid.execution_requests_root` commitment
check is not repeated (the trace is read at a step that succeeded, which made it). -/
def builderDepositTrace (ccfg : Config) (bls : Bool) (st : Gloas.BeaconState P)
    (b : Gloas.SignedBeaconBlock P) : M (List (Gloas.BeaconState P)) := do
  let ctx : Ctx := { cfg := ccfg, blsActive := bls }
  let requests := b.message.body.parent_execution_requests
  if b.message.body.signed_execution_payload_bid.message.parent_block_hash !=
      st.latest_execution_payload_bid.block_hash then
    require (requests == Gloas.ExecutionRequests.empty)
      "process_parent_execution_payload: requests == ExecutionRequests.empty()"
    pure [st]
  else
    let s0 ← Gloas.applyParentPrefix ctx st requests
    scanM (Gloas.processBuilderDepositRequest ctx) s0 (blockBuilderDeposits b)

/-- The mid-list states of the builder-exit loop: from the last builder-deposit trace state, the
state after each builder exit request (length `#builder_exits + 1`). -/
def builderExitTrace (ccfg : Config) (bls : Bool) (st : Gloas.BeaconState P)
    (b : Gloas.SignedBeaconBlock P) : M (List (Gloas.BeaconState P)) := do
  let trD ← builderDepositTrace ccfg bls st b
  scanM (Gloas.processBuilderExitRequest ccfg) (traceLast st trD) (blockBuilderExits b)

/-! ## Shape of the traces -/

private theorem bne_true_iff {α : Type} [BEq α] {a b : α} : (a != b) = true ↔ ¬ (a == b) = true := by
  simp [bne]

theorem builderDepositTrace_ok {ccfg : Config} {bls : Bool} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} {tr : List (Gloas.BeaconState P)}
    (h : builderDepositTrace ccfg bls st b = .ok tr) :
    (blockBuilderDeposits b = [] ∧ blockBuilderExits b = [] ∧ tr = [st]) ∨
      ∃ s0, Gloas.applyParentPrefix { cfg := ccfg, blsActive := bls } st
          b.message.body.parent_execution_requests = .ok s0 ∧
        scanM (Gloas.processBuilderDepositRequest { cfg := ccfg, blsActive := bls }) s0
          (blockBuilderDeposits b) = .ok tr := by
  unfold builderDepositTrace at h
  dsimp only at h
  by_cases hE : (b.message.body.signed_execution_payload_bid.message.parent_block_hash !=
      st.latest_execution_payload_bid.block_hash) = true
  · simp only [hE, ↓reduceIte] at h
    left
    simp only [require] at h
    by_cases hq : (b.message.body.parent_execution_requests == Gloas.ExecutionRequests.empty) = true
    · simp only [hq, ↓reduceIte] at h
      have := Gloas.builderLists_of_beq_empty hq
      simp only [blockBuilderDeposits, blockBuilderExits, this.1, this.2, Array.toList_empty]
      simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
      exact ⟨trivial, trivial, h.symm⟩
    · simp only [hq] at h; cases h
  · simp only [hE] at h
    right
    simp only [bind, Except.bind] at h
    cases hs0 : Gloas.applyParentPrefix { cfg := ccfg, blsActive := bls } st
        b.message.body.parent_execution_requests with
    | error e => rw [hs0] at h; cases h
    | ok s0 => rw [hs0] at h; exact ⟨s0, rfl, h⟩

/-- The deposit trace has one state per builder deposit request, plus the first. -/
theorem builderDepositTrace_length {ccfg : Config} {bls : Bool} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} {tr : List (Gloas.BeaconState P)}
    (h : builderDepositTrace ccfg bls st b = .ok tr) :
    tr.length = (blockBuilderDeposits b).length + 1 := by
  rcases builderDepositTrace_ok h with ⟨hd, -, rfl⟩ | ⟨s0, -, hs⟩
  · simp [hd]
  · exact scanM_ok_length hs

/-- Each step of the deposit trace is one `process_builder_deposit_request` call on the request
at that position. -/
theorem builderDepositTrace_step {ccfg : Config} {bls : Bool} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} {tr : List (Gloas.BeaconState P)}
    (h : builderDepositTrace ccfg bls st b = .ok tr) {k : Nat} {r : Gloas.BuilderDepositRequest}
    (hr : (blockBuilderDeposits b)[k]? = some r) :
    ∃ m m', tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
      Gloas.processBuilderDepositRequest { cfg := ccfg, blsActive := bls } m r = .ok m' := by
  rcases builderDepositTrace_ok h with ⟨hd, -, rfl⟩ | ⟨s0, -, hs⟩
  · simp [hd] at hr
  · exact scanM_ok_step hs k r hr

/-- The exit trace starts at the deposit trace's last state. -/
theorem builderExitTrace_ok {ccfg : Config} {bls : Bool} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} {tr : List (Gloas.BeaconState P)}
    (h : builderExitTrace ccfg bls st b = .ok tr) :
    ∃ trD, builderDepositTrace ccfg bls st b = .ok trD ∧
      scanM (Gloas.processBuilderExitRequest ccfg) (traceLast st trD) (blockBuilderExits b) = .ok tr ∧
      tr[0]? = trD.getLast? := by
  unfold builderExitTrace at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i trD hD
    refine ⟨trD, hD, h, ?_⟩
    rw [scanM_ok_head h]
    have hne : trD ≠ [] := by
      intro hnil; have := builderDepositTrace_length hD; simp [hnil] at this
    simp [traceLast, List.getLast?_eq_some_getLast hne]

/-- The exit trace has one state per builder exit request, plus the first. -/
theorem builderExitTrace_length {ccfg : Config} {bls : Bool} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} {tr : List (Gloas.BeaconState P)}
    (h : builderExitTrace ccfg bls st b = .ok tr) :
    tr.length = (blockBuilderExits b).length + 1 := by
  obtain ⟨_, _, hs, _⟩ := builderExitTrace_ok h
  exact scanM_ok_length hs

/-- Each step of the exit trace is one `process_builder_exit_request` call on the request at
that position. -/
theorem builderExitTrace_step {ccfg : Config} {bls : Bool} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} {tr : List (Gloas.BeaconState P)}
    (h : builderExitTrace ccfg bls st b = .ok tr) {k : Nat} {r : Gloas.BuilderExitRequest}
    (hr : (blockBuilderExits b)[k]? = some r) :
    ∃ m m', tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
      Gloas.processBuilderExitRequest ccfg m r = .ok m' := by
  obtain ⟨_, _, hs, _⟩ := builderExitTrace_ok h
  exact scanM_ok_step hs k r hr

/-! ## The factoring of the parent settlement through the traces -/

theorem builderDepositTrace_empty {ccfg : Config} {bls : Bool} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P}
    (hE : (b.message.body.signed_execution_payload_bid.message.parent_block_hash !=
      st.latest_execution_payload_bid.block_hash) = true)
    (hq : (b.message.body.parent_execution_requests == Gloas.ExecutionRequests.empty) = true) :
    builderDepositTrace ccfg bls st b = .ok [st] := by
  unfold builderDepositTrace
  dsimp only
  simp only [hE, ↓reduceIte, require, hq]
  rfl

theorem builderDepositTrace_full {ccfg : Config} {bls : Bool} {st : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P}
    (hE : ¬ (b.message.body.signed_execution_payload_bid.message.parent_block_hash !=
      st.latest_execution_payload_bid.block_hash) = true) :
    builderDepositTrace ccfg bls st b =
      (Gloas.applyParentPrefix { cfg := ccfg, blsActive := bls } st
          b.message.body.parent_execution_requests >>= fun s0 =>
        scanM (Gloas.processBuilderDepositRequest { cfg := ccfg, blsActive := bls }) s0
          (blockBuilderDeposits b)) := by
  unfold builderDepositTrace
  dsimp only
  simp only [hE, Bool.false_eq_true, ↓reduceIte]

/-- `processBlock` settles the parent first. -/
theorem processBlock_parent {ctx : Ctx} {st s' : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    (h : Gloas.processBlock ctx st blk = .ok s') :
    ∃ s1, Gloas.processParentExecutionPayload ctx st blk = .ok s1 := by
  unfold Gloas.processBlock at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · exact ⟨_, ‹_›⟩

/-- The parent settlement factors through the two traces: an EMPTY parent leaves the state and
both traces are `[st]`; a FULL parent's settlement is the suffix applied to the last exit-trace
state, and the exit trace starts at the last deposit-trace state. With the step lemmas
(`builderDepositTrace_step`, `builderExitTrace_step`) this is: the loops' results are the last
trace elements, and each step `tr[k] → tr[k+1]` is one request call. -/
theorem processParentExecutionPayload_traces {ctx : Ctx} {st s' : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P}
    (h : Gloas.processParentExecutionPayload ctx st b.message = .ok s') :
    ∃ trD trE, builderDepositTrace ctx.cfg ctx.blsActive st b = .ok trD ∧
      builderExitTrace ctx.cfg ctx.blsActive st b = .ok trE ∧
      trE[0]? = trD.getLast? ∧
      ((b.message.body.signed_execution_payload_bid.message.parent_block_hash !=
          st.latest_execution_payload_bid.block_hash) = true → s' = st ∧ trD = [st] ∧ trE = [st]) ∧
      ((b.message.body.signed_execution_payload_bid.message.parent_block_hash !=
          st.latest_execution_payload_bid.block_hash) = false →
        Gloas.applyParentSuffix st (traceLast st trE) = .ok s') := by
  unfold Gloas.processParentExecutionPayload at h
  dsimp only at h
  by_cases hE : (b.message.body.signed_execution_payload_bid.message.parent_block_hash !=
      st.latest_execution_payload_bid.block_hash) = true
  · simp only [hE, ↓reduceIte, require] at h
    by_cases hq : (b.message.body.parent_execution_requests == Gloas.ExecutionRequests.empty) = true
    · simp only [hq, ↓reduceIte, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hl := Gloas.builderLists_of_beq_empty hq
      have hd : builderDepositTrace ctx.cfg ctx.blsActive st b = .ok [st] :=
        builderDepositTrace_empty hE hq
      have he : builderExitTrace ctx.cfg ctx.blsActive st b = .ok [st] := by
        simp [builderExitTrace, traceLast, hd, blockBuilderExits, hl.2, scanM, bind, Except.bind, pure,
          Except.pure]
      exact ⟨[st], [st], hd, he, rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun h' => by simp [hE] at h'⟩
    · simp only [hq, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at h
      cases h
  · simp only [hE, Bool.false_eq_true, ↓reduceIte, require] at h
    split at h
    · rename_i hq
      simp only [bind, Except.bind, pure, Except.pure] at h
      rw [Gloas.applyParentExecutionPayload_eq, Gloas.applyParentPrefix_ctx,
        Gloas.processBuilderDepositRequest_ctx] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨s0, h0, s1, h1, s2, h2, h3⟩ := h
      rw [forIn_eq_scanM] at h1 h2
      cases hs1 : scanM (Gloas.processBuilderDepositRequest { cfg := ctx.cfg, blsActive := ctx.blsActive })
          s0 (blockBuilderDeposits b) with
      | error e => rw [hs1] at h1; cases h1
      | ok trD =>
        rw [hs1] at h1
        simp only [Except.map, Except.ok.injEq] at h1
        have hd : builderDepositTrace ctx.cfg ctx.blsActive st b = .ok trD := by
          rw [builderDepositTrace_full hE, h0]
          exact hs1
        have hne := scanM_ok_ne_nil hs1
        have hlast : traceLast st trD = s1 := by
          rw [← h1]; cases trD with
          | nil => exact absurd rfl hne
          | cons x xs => simp [traceLast, List.getLast?_cons]
        cases hs2 : scanM (Gloas.processBuilderExitRequest ctx.cfg) s1 (blockBuilderExits b) with
        | error e => rw [hs2] at h2; cases h2
        | ok trE =>
          rw [hs2] at h2
          simp only [Except.map, Except.ok.injEq] at h2
          have he : builderExitTrace ctx.cfg ctx.blsActive st b = .ok trE := by
            simp only [builderExitTrace, hd, bind, Except.bind, hlast]
            exact hs2
          have hneE := scanM_ok_ne_nil hs2
          have hlastE : traceLast st trE = s2 := by
            rw [← h2]; cases trE with
            | nil => exact absurd rfl hneE
            | cons x xs => simp [traceLast, List.getLast?_cons]
          obtain ⟨trD', hd', _, h0E⟩ := builderExitTrace_ok he
          rw [hd] at hd'; cases hd'
          exact ⟨trD, trE, hd, he, h0E, fun h' => absurd h' hE, fun _ => hlastE ▸ h3⟩
    · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      cases h

end JauneConsensus.Facts.Gloas
