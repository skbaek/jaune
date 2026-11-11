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
  if f.atLeast .fulu then
    require (body.deposits.length == 0) s!"{site}: no deposits (Fulu)"
  else
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
  cases hfu : f.atLeast .fulu
  · simp only [Bool.false_eq_true, ite_false]
    cases hx : st.depositRequestsStartIndex with
    | error e => rfl
    | ok x =>
      rw [show (Except.ok x : M U64) = pure x from rfl]
      simp only [pure_bind]
      split_ifs <;> simp only [bind_assoc, pure_bind, ok_bind']
  · simp only [ite_true, bind_assoc, pure_bind, ok_bind']

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

/-! ## Deposit-requests and consolidation-requests splits and traces (G1b) -/

/-- The operations of `process_operations` that precede the deposit-requests loop, in spec order:
the deposit-count check, the slashings, attestations, Eth1 bridge `deposits`, voluntary exits and
`bls_to_execution_change`s. -/
def preDeposits (ctx : Ctx) (state : BeaconState P f) (body : BeaconBlockBody P f) :
    M (BeaconState P f) := do
  let site := "process_operations"
  if f.atLeast .fulu then
    require (body.deposits.length == 0) s!"{site}: no deposits (Fulu)"
  else
    let startIndex ← if f.atLeast .electra then state.depositRequestsStartIndex
      else pure U64.max
    let limit := if state.eth1_data.deposit_count < startIndex then state.eth1_data.deposit_count
      else startIndex
    if !(f.atLeast .electra) then
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
  pure state

/-- The deposit-requests loop of `process_operations` (Electra and Fulu): the left fold of
`process_deposit_request` over the requests, in order. -/
def foldDepositRequests (state : BeaconState P f) (drs : List DepositRequest) :
    M (BeaconState P f) :=
  List.foldlM (fun s dr => processDepositRequest s dr) state drs

/-- The states of the deposit-requests fold: the state before each request, then the final state.
Its length is `drs.length + 1`, and its last element is the fold's result. -/
def depositRequestTrace :
    BeaconState P f → List DepositRequest → M (List (BeaconState P f))
  | st, [] => pure [st]
  | st, dr :: rest => do
    let st' ← processDepositRequest st dr
    let tr ← depositRequestTrace st' rest
    pure (st :: tr)

/-- The operations of `process_operations` up to and including the deposit-requests loop
(`preDeposits >>= foldDepositRequests`), i.e. the state handed to `foldWithdrawalRequests`. -/
def postDeposits (ctx : Ctx) (state : BeaconState P f) (body : BeaconBlockBody P f) :
    M (BeaconState P f) :=
  preRequests ctx state body

/-- The operations of `process_operations` that precede the consolidation-requests loop (Electra and
Fulu): `preRequests` followed by `foldWithdrawalRequests`. -/
def preConsolidations (ctx : Ctx) (state : BeaconState P f) (body : BeaconBlockBody P f) :
    M (BeaconState P f) := do
  let s ← preRequests ctx state body
  if f.atLeast .electra then
    let requests ← Gated.read body.execution_requests "execution_requests"
    foldWithdrawalRequests ctx.cfg s requests.withdrawals.toArray.toList
  else
    pure s

/-- The consolidation-requests loop of `process_operations` (Electra and Fulu): the left fold of
`process_consolidation_request` over the requests, in order. -/
def foldConsolidationRequests (cfg : Config) (st : BeaconState P f)
    (reqs : List ConsolidationRequest) : M (BeaconState P f) :=
  List.foldlM (fun s cr => processConsolidationRequest cfg s cr) st reqs

/-- The states of the consolidation-requests fold: the state before each request, then the final
state. Its length is `reqs.length + 1`, and its last element is the fold's result. -/
def consolidationRequestTrace (cfg : Config) :
    BeaconState P f → List ConsolidationRequest → M (List (BeaconState P f))
  | st, [] => pure [st]
  | st, cr :: rest => do
    let st' ← processConsolidationRequest cfg st cr
    let tr ← consolidationRequestTrace cfg st' rest
    pure (st :: tr)

/-- Generic trace specification for any monadic step fold. -/
theorem stepTrace_spec {α β : Type} (step : β → α → M β)
    (trace : β → List α → M (List β))
    (hnil : ∀ st, trace st [] = pure [st])
    (hcons : ∀ st x rest, trace st (x :: rest) = (do
      let st' ← step st x
      let tr ← trace st' rest
      pure (st :: tr))) :
    ∀ (reqs : List α) (st : β) (tr : List β),
      trace st reqs = .ok tr →
      tr.length = reqs.length + 1 ∧ tr.head? = some st ∧
      ∀ (k : Nat) (req : α) (a b : β),
        reqs[k]? = some req → tr[k]? = some a → tr[k + 1]? = some b →
        step a req = .ok b
  | [], st, tr, h => by
    rw [hnil] at h
    have htr : tr = [st] := (Except.ok.inj h).symm
    subst htr
    refine ⟨rfl, rfl, fun k _ _ _ hk => by simp at hk⟩
  | req :: rest, st, tr, h => by
    rw [hcons] at h
    cases hp : step st req with
    | error e =>
      rw [hp] at h
      change Except.error e = Except.ok tr at h
      cases h
    | ok st' =>
      rw [hp] at h
      change (trace st' rest >>= fun tr' => pure (st :: tr')) = Except.ok tr at h
      cases hr : trace st' rest with
      | error e =>
        rw [hr] at h
        change Except.error e = Except.ok tr at h
        cases h
      | ok tr' =>
        rw [hr] at h
        have htr : tr = st :: tr' := (Except.ok.inj h).symm
        subst htr
        obtain ⟨hlen, hhead, hstep⟩ := stepTrace_spec step trace hnil hcons rest st' tr' hr
        refine ⟨by simp [hlen], by simp, ?_⟩
        intro k r a b hk ha hb
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk ha
          subst hk ha
          have hb' : tr'.head? = some b := by rw [List.head?_eq_getElem?]; exact hb
          rw [hhead] at hb'
          cases hb'
          exact hp
        | succ j =>
          simp only [List.getElem?_cons_succ] at hk ha hb
          exact hstep j r a b hk ha hb
termination_by reqs => reqs.length

/-- Generic equivalence between a `List.foldlM` and the last element of its step trace. -/
theorem foldlM_eq_stepTrace_last {α β : Type} (step : β → α → M β)
    (trace : β → List α → M (List β))
    (hnil : ∀ st, trace st [] = pure [st])
    (hcons : ∀ st x rest, trace st (x :: rest) = (do
      let st' ← step st x
      let tr ← trace st' rest
      pure (st :: tr))) :
    ∀ (reqs : List α) (st : β) (tr : List β) (hne : tr ≠ []),
      trace st reqs = .ok tr →
      List.foldlM step st reqs = .ok (tr.getLast hne) := by
  intro reqs
  induction reqs with
  | nil =>
    intro st tr hne h
    rw [hnil] at h
    have htr : tr = [st] := (Except.ok.inj h).symm
    subst htr
    rfl
  | cons req rest ih =>
    intro st tr hne h
    rw [hcons] at h
    cases hp : step st req with
    | error e =>
      rw [hp] at h
      change Except.error e = Except.ok tr at h
      cases h
    | ok st' =>
      rw [hp] at h
      change (trace st' rest >>= fun tr' => pure (st :: tr')) = Except.ok tr at h
      cases hr : trace st' rest with
      | error e =>
        rw [hr] at h
        change Except.error e = Except.ok tr at h
        cases h
      | ok tr' =>
        rw [hr] at h
        have htr : tr = st :: tr' := (Except.ok.inj h).symm
        subst htr
        have hne' : tr' ≠ [] := by
          intro e
          have := (stepTrace_spec step trace hnil hcons rest st' tr' hr).1
          simp [e] at this
        have key := ih st' tr' hne' hr
        rw [List.getLast_cons hne', List.foldlM_cons, hp]
        exact key

/-- Conversly, every successful `List.foldlM` produces a step trace ending at its result. -/
theorem stepTrace_of_foldlM {α β : Type} (step : β → α → M β)
    (trace : β → List α → M (List β))
    (hnil : ∀ st, trace st [] = pure [st])
    (hcons : ∀ st x rest, trace st (x :: rest) = (do
      let st' ← step st x
      let tr ← trace st' rest
      pure (st :: tr))) :
    ∀ (reqs : List α) (st out : β),
      List.foldlM step st reqs = .ok out →
      ∃ (tr : List β) (hne : tr ≠ []), trace st reqs = .ok tr ∧ tr.getLast hne = out := by
  intro reqs
  induction reqs with
  | nil =>
    intro st out h
    cases h
    exact ⟨[st], List.cons_ne_nil _ _, hnil st, rfl⟩
  | cons req rest ih =>
    intro st out h
    rw [List.foldlM_cons] at h
    cases hp : step st req with
    | error e => rw [hp] at h; cases h
    | ok st' =>
      rw [hp] at h
      obtain ⟨tr', hne', htr', hlast⟩ := ih st' out h
      refine ⟨st :: tr', List.cons_ne_nil _ _, ?_, ?_⟩
      · rw [hcons, hp, ok_bind', htr']; rfl
      · rw [List.getLast_cons hne']; exact hlast

/-- `preRequests` splits into `preDeposits` followed by `foldDepositRequests` (Electra and Fulu). -/
theorem preRequests_eq_preDeposits_fold (ctx : Ctx) (st : BeaconState P f)
    (body : BeaconBlockBody P f) (h : f.atLeast .electra = true) :
    preRequests ctx st body =
      preDeposits ctx st body >>= fun s =>
        foldDepositRequests s (Gated.get h body.execution_requests).deposits.toArray.toList := by
  unfold preRequests preDeposits foldDepositRequests
  simp only [h, gated_read_get h, forArr_yield, pure_bind, Bool.not_true,
    Bool.false_eq_true, ite_true, ite_false]
  cases hfu : f.atLeast .fulu
  · simp only [Bool.false_eq_true, ite_false]
    cases hx : st.depositRequestsStartIndex with
    | error e => rfl
    | ok x =>
      rw [show (Except.ok x : M U64) = pure x from rfl]
      simp only [pure_bind]
      split_ifs <;> simp only [bind_assoc, ok_bind', bind_pure]
  · simp only [ite_true, bind_assoc, ok_bind', bind_pure]

/-- `postRequests` is `foldConsolidationRequests` (Electra and Fulu). -/
theorem postRequests_eq_foldConsolidationRequests (ctx : Ctx) (st : BeaconState P f)
    (body : BeaconBlockBody P f) (h : f.atLeast .electra = true) :
    postRequests ctx st body =
      foldConsolidationRequests ctx.cfg st
        (Gated.get h body.execution_requests).consolidations.toArray.toList := by
  unfold postRequests foldConsolidationRequests
  simp only [h, gated_read_get h, forArr_yield, ite_true, ok_bind', bind_pure]

/-- `preConsolidations` under Electra/Fulu is `preRequests >>= foldWithdrawalRequests`. -/
theorem preConsolidations_eq (ctx : Ctx) (st : BeaconState P f) (body : BeaconBlockBody P f)
    (h : f.atLeast .electra = true) :
    preConsolidations ctx st body =
      preRequests ctx st body >>= fun s =>
        foldWithdrawalRequests ctx.cfg s
          (Gated.get h body.execution_requests).withdrawals.toArray.toList := by
  unfold preConsolidations
  simp only [h, gated_read_get h, ite_true, ok_bind']

/-- Split of `process_operations` at its consolidation-requests loop (Electra and Fulu). -/
theorem processOperations_split_consolidations (ctx : Ctx) (st : BeaconState P f)
    (body : BeaconBlockBody P f) (h : f.atLeast .electra = true) :
    processOperations ctx st body =
      preConsolidations ctx st body >>= fun s =>
        foldConsolidationRequests ctx.cfg s
          (Gated.get h body.execution_requests).consolidations.toArray.toList := by
  rw [processOperations_split ctx st body h, preConsolidations_eq ctx st body h, bind_assoc]
  apply bind_congr; intro s
  apply bind_congr; intro s'
  exact postRequests_eq_foldConsolidationRequests ctx s' body h

/-- Full four-stage split of `process_operations` across all three execution-request loops
(Electra and Fulu): `preDeposits`, `foldDepositRequests`, `foldWithdrawalRequests`, and
`foldConsolidationRequests`. -/
theorem processOperations_split_all (ctx : Ctx) (st : BeaconState P f)
    (body : BeaconBlockBody P f) (h : f.atLeast .electra = true) :
    processOperations ctx st body =
      preDeposits ctx st body >>= fun s1 =>
        foldDepositRequests s1
          (Gated.get h body.execution_requests).deposits.toArray.toList >>= fun s2 =>
          foldWithdrawalRequests ctx.cfg s2
            (Gated.get h body.execution_requests).withdrawals.toArray.toList >>= fun s3 =>
            foldConsolidationRequests ctx.cfg s3
              (Gated.get h body.execution_requests).consolidations.toArray.toList := by
  rw [processOperations_split ctx st body h, preRequests_eq_preDeposits_fold ctx st body h,
    bind_assoc]
  apply bind_congr; intro s1
  apply bind_congr; intro s2
  apply bind_congr; intro s3
  exact postRequests_eq_foldConsolidationRequests ctx s3 body h

/-- Specification of `depositRequestTrace`: length `drs.length + 1`, head `st`, and each consecutive
pair stepped by `processDepositRequest`. -/
theorem depositRequestTrace_spec :
    ∀ (drs : List DepositRequest) (st : BeaconState P f) (tr : List (BeaconState P f)),
      depositRequestTrace st drs = .ok tr →
      tr.length = drs.length + 1 ∧ tr.head? = some st ∧
      ∀ (k : Nat) (dr : DepositRequest) (a b : BeaconState P f),
        drs[k]? = some dr → tr[k]? = some a → tr[k + 1]? = some b →
        processDepositRequest a dr = .ok b :=
  stepTrace_spec (fun s dr => processDepositRequest s dr) depositRequestTrace
    (fun _ => rfl) (fun _ _ _ => rfl)

/-- `foldDepositRequests` produces the last state of `depositRequestTrace`. -/
theorem foldDepositRequests_eq_trace_last (st : BeaconState P f) (drs : List DepositRequest)
    (tr : List (BeaconState P f)) (hne : tr ≠ []) (h : depositRequestTrace st drs = .ok tr) :
    foldDepositRequests st drs = .ok (tr.getLast hne) :=
  foldlM_eq_stepTrace_last (fun s dr => processDepositRequest s dr) depositRequestTrace
    (fun _ => rfl) (fun _ _ _ => rfl) drs st tr hne h

/-- Every successful `foldDepositRequests` yields a `depositRequestTrace` ending at its output. -/
theorem depositRequestTrace_of_fold {st out : BeaconState P f} {drs : List DepositRequest}
    (h : foldDepositRequests st drs = .ok out) :
    ∃ (tr : List (BeaconState P f)) (hne : tr ≠ []),
      depositRequestTrace st drs = .ok tr ∧ tr.getLast hne = out :=
  stepTrace_of_foldlM (fun s dr => processDepositRequest s dr) depositRequestTrace
    (fun _ => rfl) (fun _ _ _ => rfl) drs st out h

/-- Specification of `consolidationRequestTrace`: length `reqs.length + 1`, head `st`, and each
consecutive pair stepped by `processConsolidationRequest`. -/
theorem consolidationRequestTrace_spec (cfg : Config) :
    ∀ (reqs : List ConsolidationRequest) (st : BeaconState P f) (tr : List (BeaconState P f)),
      consolidationRequestTrace cfg st reqs = .ok tr →
      tr.length = reqs.length + 1 ∧ tr.head? = some st ∧
      ∀ (k : Nat) (cr : ConsolidationRequest) (a b : BeaconState P f),
        reqs[k]? = some cr → tr[k]? = some a → tr[k + 1]? = some b →
        processConsolidationRequest cfg a cr = .ok b :=
  stepTrace_spec (fun s cr => processConsolidationRequest cfg s cr) (consolidationRequestTrace cfg)
    (fun _ => rfl) (fun _ _ _ => rfl)

/-- `foldConsolidationRequests` produces the last state of `consolidationRequestTrace`. -/
theorem foldConsolidationRequests_eq_trace_last (cfg : Config) (st : BeaconState P f)
    (reqs : List ConsolidationRequest) (tr : List (BeaconState P f)) (hne : tr ≠ [])
    (h : consolidationRequestTrace cfg st reqs = .ok tr) :
    foldConsolidationRequests cfg st reqs = .ok (tr.getLast hne) :=
  foldlM_eq_stepTrace_last (fun s cr => processConsolidationRequest cfg s cr)
    (consolidationRequestTrace cfg) (fun _ => rfl) (fun _ _ _ => rfl) reqs st tr hne h

/-- Every successful `foldConsolidationRequests` yields a `consolidationRequestTrace` ending at its
output. -/
theorem consolidationRequestTrace_of_fold (cfg : Config) {st out : BeaconState P f}
    {reqs : List ConsolidationRequest}
    (h : foldConsolidationRequests cfg st reqs = .ok out) :
    ∃ (tr : List (BeaconState P f)) (hne : tr ≠ []),
      consolidationRequestTrace cfg st reqs = .ok tr ∧ tr.getLast hne = out :=
  stepTrace_of_foldlM (fun s cr => processConsolidationRequest cfg s cr)
    (consolidationRequestTrace cfg) (fun _ => rfl) (fun _ _ _ => rfl) reqs st out h


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
