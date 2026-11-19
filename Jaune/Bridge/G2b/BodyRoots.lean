import Jaune.Bridge.G2b.RunRoots
import Jaune.Run.BodyFacts

namespace Jaune.Staging

/-- A message's run, together with its actual top-level code entry, if any. -/
def MessageRoots (msg : Msg) (run : MessageRun) (roots : List Root) : Prop :=
  Message.run msg = .ok run ∧ roots = run.enteredRoot.toList

theorem exists_messageRoots {msg : Msg} {run : MessageRun}
    (h : Message.run msg = .ok run) : ∃ roots, MessageRoots msg run roots :=
  ⟨_, h, rfl⟩

theorem MessageRoots.atMostOne {msg run roots} (h : MessageRoots msg run roots) :
    roots.length ≤ 1 := by
  obtain ⟨_, rfl⟩ := h
  cases run.enteredRoot <;> simp

/-- Expose the sender and the root of the very message that contributed the final receipt. -/
def TransactionRoots (benv : Benv) (input : BlockOutput) (tx : Transaction) (index : Nat)
    (state : State) (output : BlockOutput) (sender : Address) (roots : List Root) : Prop :=
  ∃ run, B2.Transaction.run benv input tx index = .ok (run, output) ∧ run.state = state ∧
    run.sender = sender ∧ roots = run.message.enteredRoot.toList

theorem exists_transactionRoots {benv input tx index state output}
    (h : (fun pair => (pair.1.state, pair.2)) <$> B2.Transaction.run benv input tx index =
      .ok (state, output)) :
    ∃ sender roots, TransactionRoots benv input tx index state output sender roots := by
  cases hr : B2.Transaction.run benv input tx index with
  | error err => simp [hr, Functor.map, Except.map] at h
  | ok pair =>
    obtain ⟨run, next⟩ := pair
    simp only [hr, Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, run, hr, rfl, rfl, rfl⟩

/-- Each phase records its complete prefix, including state, receipts and gas meters. -/
structure BodyPhase where
  records : List OpRun
  final : Body.Prefix

def BodyPhase.roots (phase : BodyPhase) : List Root := phase.records.filterMap OpRun.messageRoot

def BodyPhase.frames (phase : BodyPhase) : List Exec.Frame := phase.roots.flatMap Root.frames

def BodyPhase.Ran (phase : BodyPhase) (benv : Benv) (start : Body.Prefix) (ops : List BodyOp) : Prop :=
  Body.run benv start ops = .ok (phase.records, phase.final)

def PreRoots (benv : Benv) (phase : BodyPhase) : Prop :=
  phase.Ran benv (.init benv.state) (Body.preOps benv)

/-- The receipt-derived deposit request and the configured request calls in schedule order. -/
def Body.requestOps (benv : Benv) (index : Nat) : List BodyOp :=
  if benv.stat.rules.header.requestsHash then
    .depositRequests :: benv.stat.rules.requests.map fun ⟨kind, address⟩ => .requestCall kind address index
  else []

def Body.withdrawalOps (benv : Benv) (index : Nat) (withdrawals : List Withdrawal) : List BodyOp :=
  if benv.stat.rules.header.withdrawalsRoot then [.withdrawals withdrawals index] else []

def Body.finishOps (benv : Benv) (ommers : List Header) : List BodyOp :=
  (match benv.stat.rules.proofOfWork with
   | none => []
   | some pow =>
     [.rewards benv.stat.coinbase (pow.blockReward + ommers.length * (pow.blockReward / 32))
       (ommers.map fun ommer =>
         (ommer.coinbase, (8 + ommer.number - benv.stat.number) * pow.blockReward / 8))]) ++
  [.buildAccessList, .checkAccessListLimit]

theorem Body.postOps_phases (benv : Benv) (n : Nat) (ommers : List Header) (wds : List Withdrawal) :
    Body.postOps benv n ommers wds =
      Body.withdrawalOps benv (n + 1) wds ++
      (Body.requestOps benv (n + 1) ++ Body.finishOps benv ommers) := by
  simp only [Body.postOps, Body.withdrawalOps, Body.requestOps, Body.finishOps, List.append_assoc]
  rfl

def RequestRoots (benv : Benv) (index : Nat) (start : Body.Prefix) (phase : BodyPhase) : Prop :=
  phase.Ran benv start (Body.requestOps benv index)

structure BodyRun where
  decoded : List Transaction
  pre : BodyPhase
  transactions : BodyPhase
  withdrawals : BodyPhase
  requests : BodyPhase
  finish : BodyPhase

def BodyRun.records (run : BodyRun) : List OpRun :=
  run.pre.records ++ run.transactions.records ++ run.withdrawals.records ++
    run.requests.records ++ run.finish.records

def BodyRun.roots (run : BodyRun) : List Root := run.records.filterMap OpRun.messageRoot

def BodyRun.frames (run : BodyRun) : List Exec.Frame := run.roots.flatMap Root.frames

/-- Each phase starts at the previous phase's actual final prefix, over every fork. -/
structure BodyRoots (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
    (wds : List Withdrawal) (state : State) (output : BlockOutput) (run : BodyRun) : Prop where
  decoded : txs.mapM (Jaune.decodeTransaction benv.stat.rules) = .ok run.decoded
  pre : PreRoots benv run.pre
  transactions : run.transactions.Ran benv run.pre.final (Body.transactionOps run.decoded)
  withdrawals : run.withdrawals.Ran benv run.transactions.final
    (Body.withdrawalOps benv (run.decoded.length + 1) wds)
  requests : RequestRoots benv (run.decoded.length + 1) run.withdrawals.final run.requests
  finish : run.finish.Ran benv run.requests.final (Body.finishOps benv ommers)
  output_eq : run.finish.final.output = (state, output)

/-- Split a successful run at an arbitrary operation boundary. -/
theorem Body.run_split {benv p q xs ys records}
    (h : Body.run benv p (xs ++ ys) = .ok (records, q)) :
    ∃ left right : BodyPhase, left.Ran benv p xs ∧ right.Ran benv left.final ys ∧
      records = left.records ++ right.records ∧ right.final = q := by
  rw [Body.run_append] at h
  obtain ⟨⟨l, mid⟩, hl, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨r, last⟩, hr, h⟩ := Except.bind_eq_ok h
  cases h
  exact ⟨⟨l, mid⟩, ⟨r, q⟩, hl, hr, rfl, rfl⟩

theorem BodyPhase.exists_of_fold {benv start ops final}
    (accepted : Body.fold benv start ops = .ok final) :
    ∃ phase : BodyPhase, phase.Ran benv start ops ∧ phase.final = final := by
  rw [Body.fold_eq_run] at accepted
  cases hr : Body.run benv start ops with
  | error e => rw [hr] at accepted; cases accepted
  | ok pair =>
    obtain ⟨records, last⟩ := pair
    rw [hr] at accepted
    exact ⟨⟨records, last⟩, hr, Except.ok.inj accepted⟩

theorem exists_preRoots {benv final}
    (h : Body.fold benv (.init benv.state) (Body.preOps benv) = .ok final) :
    ∃ phase, PreRoots benv phase ∧ phase.final = final := BodyPhase.exists_of_fold h

theorem exists_requestRoots {benv index start final}
    (h : Body.fold benv start (Body.requestOps benv index) = .ok final) :
    ∃ phase, RequestRoots benv index start phase ∧ phase.final = final := BodyPhase.exists_of_fold h

/-- Phase boundaries partition the original operation records, preserving their order. -/
theorem BodyRoots.of_run {benv txs decoded ommers wds records final}
    (hd : txs.mapM (Jaune.decodeTransaction benv.stat.rules) = .ok decoded)
    (hr : Body.run benv (.init benv.state) (Body.ops benv decoded ommers wds) = .ok (records, final)) :
    ∃ run, BodyRoots benv txs ommers wds final.state final.toBlockOutput run ∧
      run.records = records ∧ run.finish.final = final := by
  rw [Body.ops, Body.postOps_phases, List.append_assoc] at hr
  obtain ⟨pre, following, hp, hf, hrecords, hfinal⟩ := Body.run_split hr
  obtain ⟨transactions, post, ht, hpost, htRecords, hpFinal⟩ := Body.run_split hf
  obtain ⟨withdrawals, remaining, hw, hremaining, hwRecords, hwFinal⟩ := Body.run_split hpost
  obtain ⟨requests, finish, hq, hfinish, hqRecords, hfFinal⟩ := Body.run_split hremaining
  have last : finish.final = final := hfFinal.trans (hwFinal.trans (hpFinal.trans hfinal))
  exact ⟨⟨decoded, pre, transactions, withdrawals, requests, finish⟩,
    ⟨hd, hp, ht, hw, hq, hfinish, congrArg Body.Prefix.output last⟩,
    by simp only [BodyRun.records, hrecords, htRecords, hwRecords, hqRecords, List.append_assoc],
    last⟩

/-- Recover all five phase boundaries and their code entries from the actual importer. -/
theorem exists_bodyRoots {benv txs ommers wds state out}
    (accepted : applyBody benv txs ommers wds = .ok (state, out)) :
    ∃ run, BodyRoots benv txs ommers wds state out run := by
  unfold applyBody Body.importer at accepted
  cases hd : txs.mapM (Jaune.decodeTransaction benv.stat.rules) with
  | error err => rw [hd] at accepted; cases accepted
  | ok decoded =>
    rw [hd] at accepted
    simp only [bind, Except.bind, Body.fold_eq_run] at accepted
    cases hr : Body.run benv (.init benv.state) (Body.ops benv decoded ommers wds) with
    | error err => rw [hr] at accepted; cases accepted
    | ok pair =>
      obtain ⟨records, final⟩ := pair
      rw [hr] at accepted
      have result : final.output = (state, out) := Except.ok.inj accepted
      obtain ⟨run, phases, _, _⟩ := BodyRoots.of_run hd hr
      cases result
      exact ⟨run, phases⟩

/-- The block and its reconstructed body contain the same roots and the same retained frames. -/
theorem BlockRun.exists_bodyRoots {fork parent block run}
    (h : BlockRun.run fork parent block = .ok run) :
    ∃ body, BodyRoots run.benv block.transactions block.ommers block.withdrawals
      run.final.state run.final.toBlockOutput body ∧ body.roots = run.roots ∧ body.frames = run.frames := by
  unfold BlockRun.run at h
  obtain ⟨txs, hd, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨ops, final⟩, hr, h⟩ := Except.bind_eq_ok h
  cases h
  obtain ⟨body, roots, records, _⟩ := BodyRoots.of_run hd hr
  exact ⟨body, roots, congrArg (List.filterMap OpRun.messageRoot) records,
    congrArg (fun xs => (xs.filterMap OpRun.messageRoot).flatMap Root.frames) records⟩

end Jaune.Staging
