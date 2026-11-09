import JauneConsensus.Block

/-!
# Facts: the mid-block state of each withdrawal request (W2c)

Definitions and lemmas about `processBlockWith` and `processOperations` (Electra and Fulu) that
name the state at which the k-th execution-layer withdrawal request is processed. Nothing here
edits a spec definition: `preRequests`, `foldWithdrawalRequests`, `postRequests` and
`withdrawalRequestTrace` are new, and each is built from the same calls as the spec.
-/

namespace JauneConsensus.Facts

open JauneConsensus

variable {P : Preset} {f : CFork}

/-- The operations of `process_operations` that precede the withdrawal-requests loop, in spec order:
the deposit-count check, the slashings, attestations, deposits, voluntary exits and
`bls_to_execution_change`s, and the deposit requests. -/
def preRequests (ctx : Ctx) (state : BeaconState P f) (body : BeaconBlockBody P f) :
    M (BeaconState P f) := do
  let site := "process_operations"
  let startIndex ← if f.atLeast .electra then state.depositRequestsStartIndex
    else pure U64.max  -- Capella to Deneb: the eth1 deposit count alone bounds deposits
  let limit := if state.eth1_data.deposit_count < startIndex then state.eth1_data.deposit_count
    else startIndex
  if !(f.atLeast .electra) then
    -- `eth1_data.deposit_count - eth1_deposit_index` is typed `uint64` and raises on underflow.
    let _ ← U64.sub? state.eth1_data.deposit_count state.eth1_deposit_index site
  if state.eth1_deposit_index < limit then
    let remaining ← U64.sub? limit state.eth1_deposit_index site
    require (body.deposits.length == min P.MAX_DEPOSITS remaining.toNat) s!"{site}: deposit count"
  else
    require (body.deposits.length == 0) s!"{site}: no deposits"
  let mut state := state
  for op in body.proposer_slashings.toArray do state ← processProposerSlashing ctx state op
  for op in body.attester_slashings.toArray do state ← processAttesterSlashing ctx state op
  for op in body.attestations.toArray do state ← processAttestation ctx state op
  for op in body.deposits.toArray do state ← processDeposit ctx state op
  for op in body.voluntary_exits.toArray do state ← processVoluntaryExit ctx state op
  for op in body.bls_to_execution_changes.toArray do state ← processBlsToExecutionChange ctx state op
  if f.atLeast .electra then
    let requests ← Gated.read body.execution_requests "execution_requests"
    for op in requests.deposits.toArray do state ← processDepositRequest state op
  pure state

/-- The withdrawal-requests loop of `process_operations` (Electra): the left fold of
`process_withdrawal_request` over the requests, in order. -/
def foldWithdrawalRequests (cfg : Config) (st : BeaconState P f) (reqs : List WithdrawalRequest) :
    M (BeaconState P f) :=
  List.foldlM (fun s wr => processWithdrawalRequest cfg s wr) st reqs

/-- The states of the withdrawal-requests fold: the state before each request, then the final
state. Its length is `reqs.length + 1`, and its last element is the fold's result. -/
def withdrawalRequestTrace (cfg : Config) :
    BeaconState P f → List WithdrawalRequest → M (List (BeaconState P f))
  | st, [] => pure [st]
  | st, wr :: rest => do
    let st' ← processWithdrawalRequest cfg st wr
    let tr ← withdrawalRequestTrace cfg st' rest
    pure (st :: tr)

/-- The consolidation-requests loop of `process_operations` (Electra), which follows the
withdrawal requests. -/
def postRequests (ctx : Ctx) (state : BeaconState P f) (body : BeaconBlockBody P f) :
    M (BeaconState P f) := do
  let mut state := state
  if f.atLeast .electra then
    let requests ← Gated.read body.execution_requests "execution_requests"
    for op in requests.consolidations.toArray do state ← processConsolidationRequest ctx.cfg state op
  pure state

/-! ## Loop lemmas -/

/-- The fold a `for` loop unfolds to, with each step wrapped as a yield, returns the plain fold. -/
theorem foldlM_yield_value {α β : Type} (g : β → α → M β) (L : List α) :
    ∀ init : β, ForInStep.value <$> L.foldlM (fun b a => match b with
        | .yield b => do let b' ← g b a; pure (ForInStep.yield b')
        | .done b => pure (ForInStep.done b)) (ForInStep.yield init) = L.foldlM g init := by
  induction L with
  | nil => intro init; rfl
  | cons a L ih =>
    intro init
    simp only [List.foldlM_cons]
    cases hg : g init a with
    | error e => rfl
    | ok b => exact ih b

/-- A `for` loop whose body always yields is the left fold of its body over the list. -/
theorem forArr_yield {α β : Type} (xs : Array α) (g : β → α → M β) (init : β) :
    forIn xs init (fun a b => do let b' ← g b a; pure (ForInStep.yield b')) =
      xs.toList.foldlM g init := by
  rw [Array.forIn_eq_foldlM, ← Array.foldlM_toList]
  exact foldlM_yield_value g xs.toList init

/-- A gated read under the fork fact succeeds with the gated value. -/
theorem gated_read_get {c : Bool} (h : c = true) {α : Type} (x : Gated c α) (site : String) :
    Gated.read x site = .ok (Gated.get h x) := by
  subst h
  rfl

/-- A bind on `Except.ok` reduces. -/
theorem ok_bind' {α β : Type} (a : α) (f : α → M β) : (Except.ok a : M α) >>= f = f a := rfl

/-- The split of `process_operations` at its withdrawal-requests loop (Electra and Fulu). -/
theorem processOperations_split (ctx : Ctx) (st : BeaconState P f) (body : BeaconBlockBody P f)
    (h : f.atLeast .electra = true) :
    processOperations ctx st body =
      preRequests ctx st body >>= fun s =>
        foldWithdrawalRequests ctx.cfg s (Gated.get h body.execution_requests).withdrawals.toArray.toList
          >>= fun s' => postRequests ctx s' body := by
  unfold processOperations preRequests foldWithdrawalRequests postRequests
  simp only [h, gated_read_get h, forArr_yield, pure_bind, bind_assoc, Bool.not_true,
    Bool.false_eq_true, ite_true, ite_false]
  cases hx : st.depositRequestsStartIndex with
  | error e => rfl
  | ok x =>
    rw [show (Except.ok x : M U64) = pure x from rfl]
    simp only [pure_bind]
    split_ifs <;> simp only [bind_assoc, pure_bind, ok_bind']

/-! ## The trace of the withdrawal-requests fold -/

/-- The trace is well formed on success: `reqs.length + 1` states, the first is the input, and the
`k`-th request takes the `k`-th state to the `(k+1)`-th. -/
theorem withdrawalRequestTrace_spec (cfg : Config) :
    ∀ (reqs : List WithdrawalRequest) (st : BeaconState P f) (tr : List (BeaconState P f)),
      withdrawalRequestTrace cfg st reqs = .ok tr →
      tr.length = reqs.length + 1 ∧ tr.head? = some st ∧
      ∀ (k : Nat) (wr : WithdrawalRequest) (a b : BeaconState P f),
        reqs[k]? = some wr → tr[k]? = some a → tr[k + 1]? = some b →
        processWithdrawalRequest cfg a wr = .ok b
  | [], st, tr, h => by
    have htr : tr = [st] := by
      simp only [withdrawalRequestTrace] at h
      exact (Except.ok.inj h).symm
    subst htr
    refine ⟨rfl, rfl, ?_⟩
    intro k wr a b hk
    simp at hk
  | wr :: rest, st, tr, h => by
    simp only [withdrawalRequestTrace] at h
    cases hp : processWithdrawalRequest cfg st wr with
    | error e =>
      rw [hp] at h
      change Except.error e = Except.ok tr at h
      cases h
    | ok st' =>
      rw [hp] at h
      change (withdrawalRequestTrace cfg st' rest >>= fun tr' => pure (st :: tr')) =
        Except.ok tr at h
      cases hr : withdrawalRequestTrace cfg st' rest with
      | error e =>
        rw [hr] at h
        change Except.error e = Except.ok tr at h
        cases h
      | ok tr' =>
        rw [hr] at h
        change Except.ok (st :: tr') = Except.ok tr at h
        have htr : tr = st :: tr' := (Except.ok.inj h).symm
        subst htr
        obtain ⟨hlen, hhead, hstep⟩ := withdrawalRequestTrace_spec cfg rest st' tr' hr
        refine ⟨by simp [hlen], by simp, ?_⟩
        intro k w a b hk ha hb
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk ha
          subst hk ha
          have hb' : tr'.head? = some b := by rw [List.head?_eq_getElem?]; exact hb
          rw [hhead] at hb'
          have hbs : st' = b := Option.some.inj hb'
          subst hbs
          exact hp
        | succ j =>
          simp only [List.getElem?_cons_succ] at hk ha hb
          exact hstep j w a b hk ha hb
termination_by reqs => reqs.length

/-- The fold is the last state of the trace. -/
theorem foldWithdrawalRequests_eq_trace_last (cfg : Config) (st : BeaconState P f)
    (reqs : List WithdrawalRequest) (tr : List (BeaconState P f)) (hne : tr ≠ [])
    (h : withdrawalRequestTrace cfg st reqs = .ok tr) :
    foldWithdrawalRequests cfg st reqs = .ok (tr.getLast hne) := by
  induction reqs generalizing st tr with
  | nil =>
    have htr : tr = [st] := by
      simp only [withdrawalRequestTrace] at h
      exact (Except.ok.inj h).symm
    subst htr
    rfl
  | cons wr rest ih =>
    simp only [withdrawalRequestTrace] at h
    cases hp : processWithdrawalRequest cfg st wr with
    | error e =>
      rw [hp] at h
      change Except.error e = Except.ok tr at h
      cases h
    | ok st' =>
      rw [hp] at h
      change (withdrawalRequestTrace cfg st' rest >>= fun tr' => pure (st :: tr')) =
        Except.ok tr at h
      cases hr : withdrawalRequestTrace cfg st' rest with
      | error e =>
        rw [hr] at h
        change Except.error e = Except.ok tr at h
        cases h
      | ok tr' =>
        rw [hr] at h
        change Except.ok (st :: tr') = Except.ok tr at h
        have htr : tr = st :: tr' := (Except.ok.inj h).symm
        subst htr
        have hne' : tr' ≠ [] := by
          intro e
          have := (withdrawalRequestTrace_spec cfg rest st' tr' hr).1
          simp [e] at this
        have key := ih st' tr' hne' hr
        have hlast : (st :: tr').getLast hne = tr'.getLast hne' := by
          simp [List.getLast_cons hne']
        rw [hlast]
        change (processWithdrawalRequest cfg st wr >>= fun s =>
          List.foldlM (fun s wr => processWithdrawalRequest cfg s wr) s rest) = _
        rw [hp]
        exact key


/-! ## The block -/

/-- The state after `process_withdrawals`: the header step, then the withdrawals step. -/
def blockAfterWithdrawals (state : BeaconState P f) (block : BeaconBlock P f) :
    M (BeaconState P f) := do
  let state ← processBlockHeader state block
  processWithdrawals state block.body.execution_payload

/-- The state handed to `process_operations`: the header, withdrawals, execution payload, RANDAO
and eth1 steps of `process_block`, in order. -/
def blockBeforeOps (ctx : Ctx) (state : BeaconState P f) (block : BeaconBlock P f) :
    M (BeaconState P f) := do
  let state ← blockAfterWithdrawals state block
  let state ← processExecutionPayload ctx state block.body
  let state ← processRandao ctx state block.body
  processEth1Data state block.body

/-- The steps of `process_block` from the execution payload on: the operations and the sync
aggregate. -/
def blockRest (ctx : Ctx) (state : BeaconState P f) (block : BeaconBlock P f) :
    M (BeaconState P f) := do
  let state ← processExecutionPayload ctx state block.body
  let state ← processRandao ctx state block.body
  let state ← processEth1Data state block.body
  let state ← processOperations ctx state block.body
  processSyncAggregate ctx state block.body.sync_aggregate

/-- `process_block` is the withdrawals state followed by the rest of the steps. -/
theorem processBlockWith_eq_afterWithdrawals (ctx : Ctx) (state : BeaconState P f)
    (block : BeaconBlock P f) :
    processBlockWith ctx state block =
      blockAfterWithdrawals state block >>= fun s => blockRest ctx s block := by
  unfold processBlockWith blockAfterWithdrawals blockRest
  simp only [bind_assoc]

/-- `process_block` exposes the state handed to `process_operations`. -/
theorem processBlockWith_split (ctx : Ctx) (state : BeaconState P f) (block : BeaconBlock P f) :
    processBlockWith ctx state block =
      blockBeforeOps ctx state block >>= fun s =>
        processOperations ctx s block.body >>= fun s' =>
          processSyncAggregate ctx s' block.body.sync_aggregate := by
  unfold processBlockWith blockBeforeOps blockAfterWithdrawals
  simp only [bind_assoc]


/-! ## Order sensitivity of the withdrawal requests (the P2 control)

The control is abstract. It states the two ignore facts that decide the order dependence, with the
intermediate state's reads as plain hypotheses, and it does not compute the constructor of the
`WithdrawalIgnoreReason` that fires (that enumeration is W2a's). Constructor names in the spec
comment: `fullExitPendingBalance` (a full exit with pending balance), `alreadyExiting` (a
validator whose `exit_epoch` is already set). -/

/-- A full exit for a validator with a positive pending balance changes nothing (on every path
that succeeds): it is ignored with `fullExitPendingBalance`. -/
theorem fullExit_ignored_of_pending (cfg : Config) (s : BeaconState P f) (wf : WithdrawalRequest)
    (hfull : wf.amount = FULL_EXIT_REQUEST_AMOUNT) (idx : ValidatorIndex)
    (hidx : validatorIndexOf s wf.validator_pubkey = .ok (some idx))
    (hpos : getPendingBalanceToWithdraw s idx ≠ .ok U64.zero) :
    ∀ r, processWithdrawalRequest cfg s wf = .ok r → r = s := by
  intro r hr
  unfold processWithdrawalRequest at hr
  simp only [hfull, FULL_EXIT_REQUEST_AMOUNT, beq_self_eq_true, Bool.not_true, Bool.and_false,
    hidx] at hr
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hr
  cases hpb : getPendingBalanceToWithdraw s idx with
  | error e =>
    simp only [hpb] at hr
    repeat' split at hr
    all_goals simp_all
  | ok p =>
    have hp0 : p ≠ U64.zero := fun h0 => hpos (by rw [hpb, h0])
    simp only [hpb] at hr
    repeat' split at hr
    all_goals simp_all


/-- A partial withdrawal for a validator whose `exit_epoch` is already set changes nothing (on every
path that succeeds): it is ignored with `alreadyExiting`. -/
theorem partial_ignored_of_exiting (cfg : Config) (s : BeaconState P f) (wp : WithdrawalRequest)
    (hwp : wp.amount ≠ FULL_EXIT_REQUEST_AMOUNT) (idx : ValidatorIndex)
    (hidx : validatorIndexOf s wp.validator_pubkey = .ok (some idx))
    (v : Validator) (hv : s.validators.get idx.toNat "process_withdrawal_request" = .ok v)
    (hexit : v.exit_epoch ≠ FAR_FUTURE_EPOCH) :
    ∀ r, processWithdrawalRequest cfg s wp = .ok r → r = s := by
  intro r hr
  have hfalse : (wp.amount == FULL_EXIT_REQUEST_AMOUNT) = false := by
    simpa [beq_iff_eq] using hwp
  unfold processWithdrawalRequest at hr
  simp only [hfalse, hidx] at hr
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hr
  repeat' split at hr
  all_goals simp_all

/-- The P2 order control, abstract form. Folding `[partial V, full exit V]` from `s` and folding
`[full exit V, partial V]` from `s` yield the two intermediate states `s1` and `s2` respectively,
so they differ whenever `s1 ≠ s2`. The hypotheses are the two ignore facts and the intermediate
reads. `hne` is an assumption, not derived here: that the partial's append (`s1`) and the full
exit's exit epoch (`s2`) make the intermediate states differ. -/
theorem order_control (cfg : Config) (s s1 s2 : BeaconState P f)
    (wp wf : WithdrawalRequest) (idx : ValidatorIndex)
    (hwp : wp.amount ≠ FULL_EXIT_REQUEST_AMOUNT) (hwf : wf.amount = FULL_EXIT_REQUEST_AMOUNT)
    (h1 : processWithdrawalRequest cfg s wp = .ok s1)
    (h1step : ∃ r, processWithdrawalRequest cfg s1 wf = .ok r)
    (h1idx : validatorIndexOf s1 wf.validator_pubkey = .ok (some idx))
    (h1pos : getPendingBalanceToWithdraw s1 idx ≠ .ok U64.zero)
    (h2 : processWithdrawalRequest cfg s wf = .ok s2)
    (h2step : ∃ r, processWithdrawalRequest cfg s2 wp = .ok r)
    (h2idx : validatorIndexOf s2 wp.validator_pubkey = .ok (some idx))
    (v2 : Validator) (hv2 : s2.validators.get idx.toNat "process_withdrawal_request" = .ok v2)
    (h2exit : v2.exit_epoch ≠ FAR_FUTURE_EPOCH)
    (hne : s1 ≠ s2) :
    foldWithdrawalRequests cfg s [wp, wf] ≠ foldWithdrawalRequests cfg s [wf, wp] := by
  obtain ⟨r1, hr1⟩ := h1step
  obtain ⟨r2, hr2⟩ := h2step
  have e1 : foldWithdrawalRequests cfg s [wp, wf] = .ok s1 := by
    have hr1s : r1 = s1 := fullExit_ignored_of_pending cfg s1 wf hwf idx h1idx h1pos r1 hr1
    unfold foldWithdrawalRequests
    simp only [List.foldlM_cons, h1, ok_bind', hr1, hr1s]
    rfl
  have e2 : foldWithdrawalRequests cfg s [wf, wp] = .ok s2 := by
    have hr2s : r2 = s2 := partial_ignored_of_exiting cfg s2 wp hwp idx h2idx v2 hv2 h2exit r2 hr2
    unfold foldWithdrawalRequests
    simp only [List.foldlM_cons, h2, ok_bind', hr2, hr2s]
    rfl
  rw [e1, e2]
  intro heq
  exact hne (Except.ok.inj heq)

end JauneConsensus.Facts
