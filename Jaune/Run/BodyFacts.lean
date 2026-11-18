import Jaune.Run.Body
import Jaune.Run.BodyFactsRlp

/-!
# Theorems of the body run (goal `jaune-shape-and-names-v1`, W2 cut F)

Plain theorems about the staged body (`Jaune.Run.Body`); no old side.

* **The runner is the run.** `Body.fold_eq_run`: the fold the importer and the transition tool
  use keeps exactly the run's last prefix. `Body.run_append` and `Body.fold_append` split a run.
* **What each step writes.** `B2.processTransaction_output` gives the block output a transaction
  leaves: its gas settlement, the transaction and receipt entered under the index's key
  (`rlpKey`), the receipt's logs appended, and the access list. Every other operation leaves the
  gas counters, the tries, the receipt keys and the logs alone (`Body.step_frame`).
* **Functions of the run.** After a run of transactions at consecutive indices, the transaction
  trie is the fold of their inserts, the receipt keys are their keys, and the logs are the
  receipts' logs in order (`Body.fold_transactions_receipts`).
* **Receipts so far.** `Body.Prefix.Receipts q n rcpts`: the receipt keys are those of
  `0, …, n-1` and each is bound to its receipt (`rlpKey_injective` keeps earlier entries). The
  importer reaches the deposit step with it (`Body.importer_depositRequests`; t8n's driver in
  `Jaune.Run.BodyFactsT8n`), and under it the deposit requests are the deposit logs
  of the receipts in index order (`parseDepositRequests_of_receipts`).
* **Legacy gas accounting.** Under a legacy schedule every step keeps
  `BlockOutput.LegacyGasAccounting`, hence the importer's body
  (`Staging.applyBody_legacyGasAccounting`, the restatement of `applyBody_legacyGasAccounting`).
* **Prefix summaries.** `Body.Prefix.Summary` is what later steps read of a prefix: the state,
  the execution, state, sender and blob gas used so far, and the receipts so far. Every operation
  but the access-list build and its limit check reads only the summary, and the summary after it
  is a function of the summary before it (`Body.step_summary`, `Body.run_summary`).
-/

namespace Jaune.Staging

open Jaune

/-! ### The runner is the run -/

/-- The fold the runners use keeps exactly the run's last prefix. -/
theorem Body.fold_eq_run (benv : Benv) :
    ∀ (p : Body.Prefix) (ops : List BodyOp),
      Body.fold benv p ops = Prod.snd <$> Body.run benv p ops
  | p, [] => rfl
  | p, op :: ops => by
    simp only [Body.fold, Body.run]
    cases Body.step benv p op with
    | error e => rfl
    | ok r =>
      obtain ⟨r, q⟩ := r
      simp only [bind, Except.bind]
      rw [Body.fold_eq_run benv q ops]
      cases Body.run benv q ops with
      | error e => rfl
      | ok s => rfl

/-- A run over two lists is the run over the first, then the run over the second from where the
first ended. -/
theorem Body.run_append (benv : Benv) :
    ∀ (p : Body.Prefix) (xs ys : List BodyOp),
      Body.run benv p (xs ++ ys) = (do
        let (r, q) ← Body.run benv p xs
        let (s, q') ← Body.run benv q ys
        pure (r ++ s, q'))
  | p, [], ys => by
    simp only [List.nil_append, Body.run]
    cases h : Body.run benv p ys with
    | error e => simp [h, bind, Except.bind, pure, Except.pure]
    | ok s => simp [h, bind, Except.bind, pure, Except.pure]
  | p, op :: xs, ys => by
    simp only [List.cons_append, Body.run]
    cases Body.step benv p op with
    | error e => rfl
    | ok r =>
      obtain ⟨r, q⟩ := r
      simp only [bind, Except.bind]
      rw [Body.run_append benv q xs ys]
      cases Body.run benv q xs with
      | error e => rfl
      | ok s =>
        obtain ⟨s, q'⟩ := s
        cases h : Body.run benv q' ys with
        | error e => simp [h, bind, Except.bind, pure, Except.pure]
        | ok t => simp [h, bind, Except.bind, pure, Except.pure]

/-- Folding a list in pieces. -/
theorem Body.fold_append (benv : Benv) :
    ∀ (p : Body.Prefix) (xs ys : List BodyOp),
      Body.fold benv p (xs ++ ys) = Body.fold benv p xs >>= fun q => Body.fold benv q ys
  | p, [], ys => rfl
  | p, op :: xs, ys => by
    simp only [List.cons_append, Body.fold]
    cases Body.step benv p op with
    | error e => rfl
    | ok r => exact Body.fold_append benv r.2 xs ys

/-! ### What a transaction writes -/

/-- The block output a transaction leaves: the gas settlement, the transaction and its receipt
entered under `rlpKey index`, the receipt key appended, the receipt's logs appended, and an access
list. Under a legacy schedule the settlement's execution and sender counters agree and its state
counter is zero. -/
theorem B2.processTransaction_output {benv : Benv} {bout : BlockOutput} {tx : Transaction}
    {index : Nat} {q : State × BlockOutput}
    (h : B2.processTransaction benv bout tx index = .ok q) :
    ∃ (settlement : TransactionGasSettlement) (txBlobGasUsed : Nat)
      (receipt : Fin 5 × Receipt),
      q.2 = { bout.withGasSettlement settlement txBlobGasUsed with
        transactionsTrie := bout.transactionsTrie.insert (rlpKey index) tx
        receiptKeys := bout.receiptKeys ++ [rlpKey index]
        receiptsTrie := bout.receiptsTrie.insert (rlpKey index) receipt
        blockLogs := bout.blockLogs ++ receipt.2.logs
        blockAccessListBuilder := q.2.blockAccessListBuilder } ∧
      (benv.stat.rules.stateGas = none →
        settlement.executionGasUsed = settlement.gasUsed ∧ settlement.stateGasUsed = 0) := by
  unfold B2.processTransaction at h
  obtain ⟨checked, hc, h⟩ := Except.bind_eq_ok h
  obtain ⟨prepared, hp, h⟩ := Except.bind_eq_ok h
  obtain ⟨run, _, h⟩ := Except.bind_eq_ok h
  have hcb : checked.bout =
      {bout with transactionsTrie := bout.transactionsTrie.insert (rlpKey index) tx} ∧
      checked.benv.stat.rules = benv.stat.rules := by
    unfold Transaction.check at hc
    obtain ⟨_, hb, hc⟩ := Except.bind_eq_ok hc
    cases hb
    obtain ⟨_, _, hc⟩ := Except.bind_eq_ok hc
    obtain ⟨⟨_, _⟩, _, hc⟩ := Except.bind_eq_ok hc
    obtain ⟨⟨_, _, _, _⟩, _, hc⟩ := Except.bind_eq_ok hc
    cases hc
    exact ⟨rfl, rfl⟩
  have hpb : prepared.bout = checked.bout ∧ prepared.benv = checked.benv := by
    unfold Transaction.prepare at hp
    obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
    obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
    cases hp
    exact ⟨rfl, rfl⟩
  unfold B2.Transaction.settle at h
  obtain ⟨refundCounter, _, h⟩ := Except.bind_eq_ok h
  cases h
  refine ⟨settleTransactionGas prepared.benv.stat.rules tx.gasLimit prepared.calldataFloorGasCost
      run.gasLeft run.stateGasLeft refundCounter run.stateGasUsed, prepared.txBlobGasUsed,
    makeReceipt tx run.error
      (prepared.bout.withGasSettlement (settleTransactionGas prepared.benv.stat.rules tx.gasLimit
        prepared.calldataFloorGasCost run.gasLeft run.stateGasLeft refundCounter run.stateGasUsed)
        prepared.txBlobGasUsed).cumulativeGasUsed run.logs, ?_, ?_⟩
  · rw [hpb.1, hcb.1]
    rfl
  · intro hnone
    rw [hpb.2, hcb.2]
    exact settleTransactionGas_none_invariants hnone _ _ _ _ _ _

/-! ### What the other operations leave alone -/

/-- Every operation but a transaction leaves the gas counters, the transaction and receipt tries,
the receipt keys and the logs as they were. -/
theorem Body.step_frame {benv : Benv} {p q : Body.Prefix} {op : BodyOp} {r : OpRun}
    (hop : ∀ tx i, op ≠ .transaction tx i) (h : Body.step benv p op = .ok (r, q)) :
    q.executionGasUsed = p.executionGasUsed ∧ q.stateGasUsed = p.stateGasUsed ∧
      q.cumulativeGasUsed = p.cumulativeGasUsed ∧ q.blobGasUsed = p.blobGasUsed ∧
      q.transactionsTrie = p.transactionsTrie ∧ q.receiptsTrie = p.receiptsTrie ∧
      q.receiptKeys = p.receiptKeys ∧ q.logs = p.logs := by
  cases op with
  | transaction tx i => exact absurd rfl (hop tx i)
  | systemCall address data index =>
    simp only [Body.step] at h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | withdrawals ws index =>
    simp only [Body.step] at h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | depositRequests =>
    simp only [Body.step] at h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | requestCall type address index =>
    simp only [Body.step] at h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | rewards coinbase minerReward credits =>
    simp only [Body.step] at h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | buildAccessList =>
    simp only [Body.step] at h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | checkAccessListLimit =>
    simp only [Body.step] at h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A transaction step, read through `B2.processTransaction_output`. -/
theorem Body.step_transaction_output {benv : Benv} {p q : Body.Prefix} {tx : Transaction}
    {index : Nat} {r : OpRun} (h : Body.step benv p (.transaction tx index) = .ok (r, q)) :
    ∃ (settlement : TransactionGasSettlement) (txBlobGasUsed : Nat)
      (receipt : Fin 5 × Receipt),
      q.toBlockOutput = { p.toBlockOutput.withGasSettlement settlement txBlobGasUsed with
        transactionsTrie := p.transactionsTrie.insert (rlpKey index) tx
        receiptKeys := p.receiptKeys ++ [rlpKey index]
        receiptsTrie := p.receiptsTrie.insert (rlpKey index) receipt
        blockLogs := p.logs ++ receipt.2.logs
        blockAccessListBuilder := q.accessList } ∧
      (benv.stat.rules.stateGas = none →
        settlement.executionGasUsed = settlement.gasUsed ∧ settlement.stateGasUsed = 0) ∧
      r = .transaction index tx := by
  simp only [Body.step] at h
  obtain ⟨⟨state, bout⟩, ht, h⟩ := Except.bind_eq_ok h
  cases h
  obtain ⟨settlement, txBlobGasUsed, receipt, hq, hs⟩ := B2.processTransaction_output ht
  exact ⟨settlement, txBlobGasUsed, receipt, hq, hs, rfl⟩

/-! ### Receipts so far, deposit requests and the legacy relation -/

theorem forIn_filter_mapM {ε α β : Type} (C : α → Prop) [DecidablePred C]
    (E : α → Except ε (List β)) (F : α → List β → Except ε (ForInStep (List β)))
    (hF : ∀ x s, F x s = if C x then (fun r => ForInStep.yield (s ++ r)) <$> E x
      else pure (ForInStep.yield s)) :
    ∀ (l : List α) (a : List β),
      forIn l a F = (fun rs => a ++ rs.flatten) <$> (l.filter C).mapM E
  | [], a => by simp [pure, Except.pure, Functor.map, Except.map]
  | x :: l, a => by
    rw [List.forIn_cons, hF]
    by_cases hc : C x
    · simp only [hc, ↓reduceIte, decide_true, List.filter_cons_of_pos, List.mapM_cons]
      cases E x with
      | error e => rfl
      | ok r =>
        simp only [Functor.map, Except.map, bind, Except.bind]
        rw [forIn_filter_mapM C E F hF l (a ++ r)]
        cases (l.filter C).mapM E with
        | error e => rfl
        | ok rs => simp [pure, Except.pure, List.append_assoc]
    · simp only [hc, ↓reduceIte, decide_false, Bool.false_eq_true, not_false_eq_true,
        List.filter_cons_of_neg, pure, Except.pure, bind, Except.bind]
      exact forIn_filter_mapM C E F hF l a

theorem forIn_lookup_flatMap {ε α β κ : Type} [Ord κ] (C : α → Prop) [DecidablePred C]
    (E : α → Except ε (List β)) (logs : ν → List α) (trie : Std.TreeMap κ ν compare) (err : ε)
    (G : κ → List β → Except ε (ForInStep (List β)))
    (hG : ∀ k s, G k s = (trie[k]?.toExcept err) >>= fun v =>
      (fun rs => ForInStep.yield (s ++ rs.flatten)) <$> ((logs v).filter C).mapM E) :
    ∀ (l : List (κ × ν)) (a : List β), (∀ x ∈ l, trie[x.1]? = some x.2) →
      forIn (l.map Prod.fst) a G =
        (fun rs => a ++ rs.flatten) <$> ((l.flatMap (fun x => logs x.2)).filter C).mapM E
  | [], a, _ => by simp [pure, Except.pure, Functor.map, Except.map]
  | x :: l, a, hl => by
    rw [List.map_cons, List.forIn_cons, hG, hl x (List.mem_cons_self ..)]
    simp only [Option.toExcept, List.flatMap_cons, List.filter_append, List.mapM_append, bind,
      Except.bind, Functor.map, Except.map]
    cases hm : ((logs x.2).filter C).mapM E with
    | error e => rfl
    | ok rs =>
      simp only []
      rw [forIn_lookup_flatMap C E logs trie err G hG l (a ++ rs.flatten)
        (fun y hy => hl y (List.mem_cons_of_mem _ hy))]
      simp only [Functor.map, Except.map]
      cases ((l.flatMap (fun x => logs x.2)).filter C).mapM E with
      | error e => rfl
      | ok ts => simp [pure, Except.pure, List.append_assoc]


/-- **The receipts so far.** The prefix holds the receipts of the transactions at
`0, 1, …, n-1`, in order: its receipt keys are those indices' keys, and each is bound to its
receipt. -/
structure Body.Prefix.Receipts (q : Body.Prefix) (n : Nat) (rcpts : List (Fin 5 × Receipt)) :
    Prop where
  keys : q.receiptKeys = (List.range n).map rlpKey
  length : rcpts.length = n
  get : ∀ (i : Nat) (h : i < rcpts.length), q.receiptsTrie[rlpKey i]? = some rcpts[i]

theorem Body.Prefix.receipts_init (s : State) : (Body.Prefix.init s).Receipts 0 [] :=
  ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem Body.Prefix.Receipts.of_eq {p q : Body.Prefix} {n : Nat} {rcpts : List (Fin 5 × Receipt)}
    (hp : p.Receipts n rcpts) (hk : q.receiptKeys = p.receiptKeys)
    (ht : q.receiptsTrie = p.receiptsTrie) : q.Receipts n rcpts :=
  ⟨hk ▸ hp.keys, hp.length, fun i h => ht ▸ hp.get i h⟩

/-- A transaction at the next index adds its receipt at that index, appends its logs and enters
the transaction under the same key. -/
theorem Body.Prefix.Receipts.step_transaction {benv : Benv} {p q : Body.Prefix} {tx : Transaction}
    {n : Nat} {rcpts : List (Fin 5 × Receipt)} {r : OpRun} (hp : p.Receipts n rcpts)
    (h : Body.step benv p (.transaction tx n) = .ok (r, q)) :
    ∃ receipt, q.Receipts (n + 1) (rcpts ++ [receipt]) ∧ q.logs = p.logs ++ receipt.2.logs ∧
      q.transactionsTrie = p.transactionsTrie.insert (rlpKey n) tx := by
  obtain ⟨_, _, receipt, hq, -, -⟩ := Body.step_transaction_output h
  have hk : q.receiptKeys = p.receiptKeys ++ [rlpKey n] := congrArg BlockOutput.receiptKeys hq
  have ht : q.receiptsTrie = p.receiptsTrie.insert (rlpKey n) receipt :=
    congrArg BlockOutput.receiptsTrie hq
  refine ⟨receipt, ⟨?_, ?_, ?_⟩, congrArg BlockOutput.blockLogs hq,
    congrArg BlockOutput.transactionsTrie hq⟩
  · rw [hk, hp.keys, List.range_succ, List.map_append]
    rfl
  · simp [hp.length]
  · intro i hi
    rw [ht]
    simp only [Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq]
    have hlen := hp.length
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hin : i = n
    · subst hin
      simp only [↓reduceIte]
      rw [List.getElem_append_right (by omega)]
      simp [hlen]
    · have hne : rlpKey n ≠ rlpKey i := fun e => hin (rlpKey_injective e).symm
      simp only [hne, ↓reduceIte]
      rw [List.getElem_append_left (by omega)]
      exact hp.get i (by omega)

/-- A deposit log: emitted by the deposit contract, with the deposit event's signature as its
first topic. -/
abbrev IsDepositLog (log : Log) : Prop :=
  log.address = depositContractAddress ∧ log.topics[0]? = some depositEventSignatureHash

/-- **Deposit requests read the receipts so far.** Over a prefix holding the receipts of
`0, …, n-1`, the deposit requests are the deposit logs of those receipts, in index order and
each receipt's log order, each extracted (a malformed one is a block error), and concatenated.
"Receipt not found" is unreachable. -/
theorem parseDepositRequests_of_receipts {q : Body.Prefix} {n : Nat}
    {rcpts : List (Fin 5 × Receipt)} (h : q.Receipts n rcpts) :
    parseDepositRequests q.toBlockOutput =
      List.flatten <$> ((rcpts.flatMap (·.2.logs)).filter (fun log => decide (IsDepositLog log))).mapM
        (fun log => Except.mapError TransitionError.block (extractDepositData log.data)) := by
  have hl : (((List.range n).map rlpKey).zip rcpts).map Prod.fst = (List.range n).map rlpKey := by
    rw [List.map_fst_zip]; simp [h.length]
  have hr : (((List.range n).map rlpKey).zip rcpts).map Prod.snd = rcpts := by
    rw [List.map_snd_zip]; simp [h.length]
  have hmem : ∀ x ∈ ((List.range n).map rlpKey).zip rcpts, q.receiptsTrie[x.1]? = some x.2 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
    exact h.get i (by simp at hi; omega)
  unfold parseDepositRequests
  simp only [Body.Prefix.toBlockOutput]
  rw [h.keys, ← hl]
  rw [forIn_lookup_flatMap IsDepositLog
    (fun log => Except.mapError TransitionError.block (extractDepositData log.data))
    (fun v : Fin 5 × Receipt => v.2.logs) q.receiptsTrie
    (TransitionError.internal (.invariant (.text "receipt not found"))) _ ?_ _ [] hmem]
  · have : (((List.range n).map rlpKey).zip rcpts).flatMap (fun x => x.2.2.logs) =
        rcpts.flatMap (·.2.logs) := by
      conv_rhs => rw [← hr]
      rw [List.flatMap_map]
    rw [this]
    cases ((rcpts.flatMap (·.2.logs)).filter (fun log => decide (IsDepositLog log))).mapM
      (fun log => Except.mapError TransitionError.block (extractDepositData log.data)) <;> rfl
  · intro k s
    simp only [bind]
    congr 1
    funext v
    rw [forIn_filter_mapM IsDepositLog _ _ ?_ v.2.logs s]
    · cases ((v.2.logs).filter (fun log => decide (IsDepositLog log))).mapM
        (fun log => Except.mapError TransitionError.block (extractDepositData log.data)) <;> rfl
    · intro x s
      by_cases hc : IsDepositLog x
      · simp only [IsDepositLog] at hc
        simp only [IsDepositLog, hc, and_self, ↓reduceIte]
        cases Except.mapError TransitionError.block (extractDepositData x.data) <;> rfl
      · simp only [IsDepositLog] at hc
        simp only [IsDepositLog, hc, ↓reduceIte]


/-- Operations other than transactions keep the receipts so far. -/
theorem Body.fold_receipts_of_noTransaction (benv : Benv) :
    ∀ (ops : List BodyOp) (p q : Body.Prefix) (n : Nat) (rcpts : List (Fin 5 × Receipt)),
      (∀ op ∈ ops, ∀ tx i, op ≠ .transaction tx i) → p.Receipts n rcpts →
      Body.fold benv p ops = .ok q → q.Receipts n rcpts
  | [], p, q, n, rcpts, _, hp, h => by cases h; exact hp
  | op :: ops, p, q, n, rcpts, hops, hp, h => by
    simp only [Body.fold] at h
    obtain ⟨⟨r, p'⟩, hs, h⟩ := Except.bind_eq_ok h
    have hf := Body.step_frame (hops op (List.mem_cons_self ..)) hs
    exact Body.fold_receipts_of_noTransaction benv ops p' q n rcpts
      (fun op' h' => hops op' (List.mem_cons_of_mem _ h'))
      (hp.of_eq hf.2.2.2.2.2.2.1 hf.2.2.2.2.2.1) h

/-- Transactions at the next indices, in order, add their receipts in order. -/
theorem Body.fold_transactions_receipts (benv : Benv) :
    ∀ (l : List (Nat × Transaction)) (p q : Body.Prefix) (n : Nat)
      (rcpts : List (Fin 5 × Receipt)),
      l.map Prod.fst = List.range' n l.length → p.Receipts n rcpts →
      Body.fold benv p (l.map fun x => .transaction x.2 x.1) = .ok q →
      ∃ rs, rs.length = l.length ∧ q.Receipts (n + l.length) (rcpts ++ rs) ∧
        q.logs = p.logs ++ rs.flatMap (·.2.logs) ∧
        q.transactionsTrie = l.foldl (fun t x => t.insert (rlpKey x.1) x.2) p.transactionsTrie
  | [], p, q, n, rcpts, _, hp, h => by cases h; exact ⟨[], rfl, by simpa using hp, by simp, rfl⟩
  | ⟨i, tx⟩ :: l, p, q, n, rcpts, hl, hp, h => by
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl
    obtain ⟨rfl, hl⟩ := hl
    simp only [List.map_cons, Body.fold] at h
    obtain ⟨⟨r, p'⟩, hs, h⟩ := Except.bind_eq_ok h
    obtain ⟨receipt, hp', hlog, htx⟩ := hp.step_transaction hs
    obtain ⟨rs, hrs, hq, hlog', htx'⟩ :=
      Body.fold_transactions_receipts benv l p' q (i + 1) _ hl hp' h
    refine ⟨receipt :: rs, by simp [hrs], ?_, ?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm 1] using hq
    · rw [hlog', hlog]
      simp
    · rw [htx', htx]
      rfl

theorem putIndex_aux_fst {ξ : Type} : ∀ (k : Nat) (xs : List ξ),
    (List.putIndex.aux k xs).map Prod.fst = List.range' k (List.putIndex.aux k xs).length
  | _, [] => rfl
  | k, _ :: xs => by
    simp only [List.putIndex.aux, List.map_cons, List.length_cons, List.range'_succ]
    rw [putIndex_aux_fst (k + 1) xs]

theorem length_putIndex_aux {ξ : Type} : ∀ (k : Nat) (xs : List ξ),
    (List.putIndex.aux k xs).length = xs.length
  | _, [] => rfl
  | k, _ :: xs => by simp [List.putIndex.aux, length_putIndex_aux (k + 1) xs]

theorem length_putIndex {ξ : Type} (xs : List ξ) : xs.putIndex.length = xs.length :=
  length_putIndex_aux 0 xs

/-- **The importer reaches the deposit step with the receipts so far.** After the pre-execution
system calls, the transactions and the withdrawals (the operations `Body.ops` runs before
`.depositRequests`), the prefix holds the receipts of all `decoded.length` transactions, and
the deposit requests are their deposit logs. -/
theorem Body.importer_depositRequests (benv : Benv) (decoded : List Transaction)
    (wds : List Withdrawal) {q : Body.Prefix}
    (h : Body.fold benv (Body.Prefix.init benv.state)
      (Body.preOps benv ++ Body.transactionOps decoded ++
        (if benv.stat.rules.header.withdrawalsRoot then [.withdrawals wds (decoded.length + 1)]
          else [])) = .ok q) :
    ∃ rcpts : List (Fin 5 × Receipt), rcpts.length = decoded.length ∧
      q.Receipts decoded.length rcpts ∧
      parseDepositRequests q.toBlockOutput =
        List.flatten <$>
          ((rcpts.flatMap (·.2.logs)).filter (fun log => decide (IsDepositLog log))).mapM
            (fun log => Except.mapError TransitionError.block (extractDepositData log.data)) := by
  rw [Body.fold_append, Body.fold_append] at h
  obtain ⟨p2, h12, h3⟩ := Except.bind_eq_ok h
  obtain ⟨p1, h1, h2⟩ := Except.bind_eq_ok h12
  have hpre : ∀ op ∈ Body.preOps benv, ∀ tx i, op ≠ .transaction tx i := by
    intro op hop tx i e
    subst e
    unfold Body.preOps at hop
    simp only [List.mem_append] at hop
    rcases hop with hop | hop <;> split at hop <;> simp at hop
  have r1 := Body.fold_receipts_of_noTransaction benv _ _ _ 0 [] hpre
    (Body.Prefix.receipts_init benv.state) h1
  have hops : Body.transactionOps decoded =
      (List.putIndex.aux 0 decoded).map fun x => BodyOp.transaction x.2 x.1 := by
    unfold Body.transactionOps List.putIndex
    exact List.map_congr_left (fun x _ => rfl)
  rw [hops] at h2
  obtain ⟨rs, hrs, r2, -, -⟩ := Body.fold_transactions_receipts benv _ _ _ 0 [] (putIndex_aux_fst 0 decoded)
    r1 h2
  rw [length_putIndex_aux] at hrs r2
  simp only [Nat.zero_add, List.nil_append] at r2
  have r3 := Body.fold_receipts_of_noTransaction benv _ _ _ _ _
    (by intro op hop tx i e; subst e; split at hop <;> simp at hop) r2 h3
  exact ⟨rs, hrs, r3, parseDepositRequests_of_receipts r3⟩

/-! ### Legacy gas accounting -/

/-- Under a legacy schedule every operation keeps the legacy relation between the counters. -/
theorem Body.step_legacyGasAccounting {benv : Benv} {p q : Body.Prefix} {op : BodyOp} {r : OpRun}
    (hnone : benv.stat.rules.stateGas = none) (hp : p.toBlockOutput.LegacyGasAccounting)
    (h : Body.step benv p op = .ok (r, q)) : q.toBlockOutput.LegacyGasAccounting := by
  by_cases hop : ∃ tx i, op = .transaction tx i
  · obtain ⟨tx, i, rfl⟩ := hop
    obtain ⟨_, txBlobGasUsed, _, hq, hs, -⟩ := Body.step_transaction_output h
    rw [hq]
    exact BlockOutput.LegacyGasAccounting.withGasSettlement hp (hs hnone) txBlobGasUsed
  · obtain ⟨h1, h2, h3, -⟩ := Body.step_frame (fun tx i e => hop ⟨tx, i, e⟩) h
    unfold BlockOutput.LegacyGasAccounting at hp ⊢
    simp only [Body.Prefix.toBlockOutput] at hp ⊢
    rw [h1, h2, h3]
    exact hp

theorem Body.fold_legacyGasAccounting {benv : Benv} (hnone : benv.stat.rules.stateGas = none) :
    ∀ (ops : List BodyOp) (p q : Body.Prefix), p.toBlockOutput.LegacyGasAccounting →
      Body.fold benv p ops = .ok q → q.toBlockOutput.LegacyGasAccounting
  | [], p, q, hp, h => by cases h; exact hp
  | op :: ops, p, q, hp, h => by
    simp only [Body.fold] at h
    obtain ⟨⟨r, p'⟩, hs, h⟩ := Except.bind_eq_ok h
    exact Body.fold_legacyGasAccounting hnone ops p' q (Body.step_legacyGasAccounting hnone hp hs) h

theorem Body.importer_legacyGasAccounting {benv : Benv} (hnone : benv.stat.rules.stateGas = none)
    {txs : List (Bytes ⊕ Transaction)} {ommers : List Header} {wds : List Withdrawal}
    {q : Body.Prefix} (h : Body.importer benv txs ommers wds = .ok q) :
    q.toBlockOutput.LegacyGasAccounting := by
  unfold Body.importer at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  exact Body.fold_legacyGasAccounting hnone _ (Body.Prefix.init benv.state) _
    BlockOutput.init_legacyGasAccounting h

/-- **`applyBody_legacyGasAccounting` over the staged body.** A successful legacy block body
keeps the legacy block-counter relation: every step does. -/
theorem applyBody_legacyGasAccounting {benv : Benv} (hnone : benv.stat.rules.stateGas = none)
    {txs : List (Bytes ⊕ Transaction)} {ommers : List Header} {wds : List Withdrawal} {p}
    (hp : Staging.applyBody benv txs ommers wds = .ok p) : p.2.LegacyGasAccounting := by
  unfold Staging.applyBody at hp
  cases h : Body.importer benv txs ommers wds with
  | error e => simp [h, Functor.map, Except.map] at hp
  | ok q =>
    simp only [h, Functor.map, Except.map, Except.ok.injEq] at hp
    rw [← hp]
    exact Body.importer_legacyGasAccounting hnone h

/-! ### Prefix summaries -/

theorem checkTransaction_congr {benv : Benv} {b b' : BlockOutput} (tx : Transaction)
    (hg : b.blockGasUsed = b'.blockGasUsed) (hs : b.blockStateGasUsed = b'.blockStateGasUsed)
    (hb : b.blobGasUsed = b'.blobGasUsed) :
    checkTransaction benv b tx = checkTransaction benv b' tx := by
  unfold checkTransaction checkTransactionGasLimits
  rw [hg, hs, hb]

/-- The receipts so far as later steps read them: each receipt key with what the receipt trie
binds it to. -/
def receiptsRead (keys : List Bytes) (trie : Std.TreeMap Bytes (Fin 5 × Receipt) compare) :
    List (Bytes × Option (Fin 5 × Receipt)) :=
  keys.map fun k => (k, trie[k]?)

theorem receiptsRead_insert (keys : List Bytes) (trie : Std.TreeMap Bytes (Fin 5 × Receipt) compare)
    (key : Bytes) (r : Fin 5 × Receipt) :
    receiptsRead (keys ++ [key]) (trie.insert key r) =
      (receiptsRead keys trie).map (fun x => (x.1, if key = x.1 then some r else x.2)) ++
        [(key, some r)] := by
  simp [receiptsRead, Std.TreeMap.getElem?_insert]

/-- What later steps read of a block output, beside the state: the four gas counters and the
receipts so far. -/
def outputSummary (b : BlockOutput) :
    Nat × Nat × Nat × Nat × List (Bytes × Option (Fin 5 × Receipt)) :=
  (b.blockGasUsed, b.blockStateGasUsed, b.cumulativeGasUsed, b.blobGasUsed,
    receiptsRead b.receiptKeys b.receiptsTrie)

theorem Except.ok_bind' {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

theorem B2.processTransaction_summary {benv : Benv} {b b' : BlockOutput} (tx : Transaction)
    (index : Nat) (h : outputSummary b = outputSummary b') :
    (fun q => (q.1, outputSummary q.2)) <$> B2.processTransaction benv b tx index =
      (fun q => (q.1, outputSummary q.2)) <$> B2.processTransaction benv b' tx index := by
  simp only [outputSummary, Prod.mk.injEq] at h
  obtain ⟨hg, hs, hc, hb, hk⟩ := h
  unfold B2.processTransaction Transaction.check Transaction.prepare B2.Transaction.settle
  simp only [map_bind, bind_assoc, Except.ok_bind', pure_bind]
  rw [checkTransaction_congr (b := {b with
    transactionsTrie := b.transactionsTrie.insert (Rlp.Item.bytes (Nat.toBytes index)).toBytes tx})
    (b' := {b' with
    transactionsTrie := b'.transactionsTrie.insert (Rlp.Item.bytes (Nat.toBytes index)).toBytes tx})
    tx hg hs hb]
  refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => bind_congr fun _ =>
    bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => ?_
  simp only [Functor.map, Except.map, outputSummary, BlockOutput.withGasSettlement,
    receiptsRead_insert, hg, hs, hc, hb, hk]

/-- **A prefix's summary**: what later steps read of it — the state, the execution, state,
sender and blob gas used so far, and the receipts so far (each receipt key with its receipt). -/
abbrev Body.Prefix.Summary : Type :=
  State × Nat × Nat × Nat × Nat × List (Bytes × Option (Fin 5 × Receipt))

/-- The summary of a prefix. -/
def Body.Prefix.summary (p : Body.Prefix) : Body.Prefix.Summary :=
  (p.state, outputSummary p.toBlockOutput)

theorem forIn_congr_mem {m : Type → Type} [Monad m] {α β : Type} (f g : α → β → m (ForInStep β)) :
    ∀ (l : List α) (b : β), (∀ a ∈ l, ∀ s, f a s = g a s) → forIn l b f = forIn l b g
  | [], b, _ => rfl
  | a :: l, b, h => by
    simp only [List.forIn_cons, h a (List.mem_cons_self ..)]
    congr 1
    funext r
    cases r with
    | done c => rfl
    | yield c => exact forIn_congr_mem f g l c (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem receiptsRead_eq {t t' : Std.TreeMap Bytes (Fin 5 × Receipt) compare} :
    ∀ (ks ks' : List Bytes), receiptsRead ks t = receiptsRead ks' t' →
      ks = ks' ∧ ∀ k ∈ ks, t[k]? = t'[k]?
  | [], [], _ => ⟨rfl, fun _ h => absurd h (List.not_mem_nil)⟩
  | [], _ :: _, h => by simp [receiptsRead] at h
  | _ :: _, [], h => by simp [receiptsRead] at h
  | k :: ks, k' :: ks', h => by
    simp only [receiptsRead, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, hv⟩, h⟩ := h
    obtain ⟨rfl, ih⟩ := receiptsRead_eq ks ks' h
    refine ⟨rfl, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · exact ih x hx

/-- The deposit parse reads only the receipts so far. -/
theorem parseDepositRequests_congr {b b' : BlockOutput}
    (h : receiptsRead b.receiptKeys b.receiptsTrie = receiptsRead b'.receiptKeys b'.receiptsTrie) :
    parseDepositRequests b = parseDepositRequests b' := by
  obtain ⟨hks, hlk⟩ := receiptsRead_eq _ _ h
  unfold parseDepositRequests
  simp only []
  rw [← hks]
  congr 1
  apply forIn_congr_mem
  intro k hk s
  rw [hlk k hk]


/-- **Later steps read only the summary.** Every operation but the access-list build and its
limit check (which read the access list, a function of the run) succeeds or fails alike from two
prefixes with the same summary, with the same record, and leaves prefixes with the same summary. -/
theorem Body.step_summary (benv : Benv) {p p' : Body.Prefix} {op : BodyOp}
    (h1 : op ≠ .buildAccessList) (h2 : op ≠ .checkAccessListLimit)
    (hs : p.summary = p'.summary) :
    (fun x => (x.1, x.2.summary)) <$> Body.step benv p op =
      (fun x => (x.1, x.2.summary)) <$> Body.step benv p' op := by
  have hsum : outputSummary p.toBlockOutput = outputSummary p'.toBlockOutput :=
    congrArg Prod.snd hs
  have hst : p.state = p'.state := congrArg Prod.fst hs
  simp only [Body.Prefix.summary, outputSummary, Body.Prefix.toBlockOutput, Prod.mk.injEq] at hs
  obtain ⟨-, hg, hsg, hc, hb, hk⟩ := hs
  cases op with
  | buildAccessList => exact absurd rfl h1
  | checkAccessListLimit => exact absurd rfl h2
  | transaction tx index =>
    have key := B2.processTransaction_summary (benv := benv.withState p'.state) tx index hsum
    simp only [Body.step, hst]
    revert key
    cases B2.processTransaction (benv.withState p'.state) p.toBlockOutput tx index <;>
      cases B2.processTransaction (benv.withState p'.state) p'.toBlockOutput tx index <;>
      intro key <;>
      simp_all [Functor.map, Except.map, bind, Except.bind, pure, Except.pure, Body.Prefix.summary]
  | systemCall address data index =>
    simp only [Body.step, hst]
    cases data with
    | error e => rfl
    | ok d =>
      simp only [bind, Except.bind]
      cases (processUncheckedSystemTransaction (benv.withState p'.state) address d).mapError
        (fun e => TransitionError.vm e.toEvmError) with
      | error e => rfl
      | ok run =>
        simp only [Functor.map, Except.map, pure, Except.pure, Body.Prefix.summary, outputSummary,
          Body.Prefix.toBlockOutput, hg, hsg, hc, hb, hk]
  | withdrawals ws index =>
    simp only [Body.step, hst, Functor.map, Except.map, pure, Except.pure, Body.Prefix.summary,
      outputSummary, Body.Prefix.toBlockOutput, hg, hsg, hc, hb, hk]
  | depositRequests =>
    have hd : parseDepositRequests p.toBlockOutput = parseDepositRequests p'.toBlockOutput :=
      parseDepositRequests_congr hk
    simp only [Body.step, hd]
    cases parseDepositRequests p'.toBlockOutput with
    | error e => rfl
    | ok d =>
      simp only [bind, Except.bind, Functor.map, Except.map, pure, Except.pure, Body.Prefix.summary,
        outputSummary, Body.Prefix.toBlockOutput, hst, hg, hsg, hc, hb, hk]
  | requestCall type address index =>
    simp only [Body.step, hst]
    cases processCheckedSystemTransaction (benv.withState p'.state) address [] with
    | error e => rfl
    | ok run =>
      simp only [bind, Except.bind, Functor.map, Except.map, pure, Except.pure, Body.Prefix.summary,
        outputSummary, Body.Prefix.toBlockOutput, hg, hsg, hc, hb, hk]
  | rewards coinbase minerReward credits =>
    simp only [Body.step, hst, Functor.map, Except.map, pure, Except.pure, Body.Prefix.summary,
      outputSummary, Body.Prefix.toBlockOutput, hg, hsg, hc, hb, hk]


/-- **A run reads only its starting summary.** A run without the access-list build and its limit
check gives the same records and the same final summary from two prefixes with the same
summary. -/
theorem Body.run_summary (benv : Benv) :
    ∀ (ops : List BodyOp) (p p' : Body.Prefix),
      (∀ op ∈ ops, op ≠ .buildAccessList ∧ op ≠ .checkAccessListLimit) →
      p.summary = p'.summary →
      (fun x => (x.1, x.2.summary)) <$> Body.run benv p ops =
        (fun x => (x.1, x.2.summary)) <$> Body.run benv p' ops
  | [], p, p', _, hs => by
    simp only [Body.run, Functor.map, Except.map, pure, Except.pure, hs]
  | op :: ops, p, p', hops, hs => by
    have key := Body.step_summary benv (hops op (List.mem_cons_self ..)).1
      (hops op (List.mem_cons_self ..)).2 hs
    have ih := fun q q' => Body.run_summary benv ops q q'
      (fun op' h' => hops op' (List.mem_cons_of_mem _ h'))
    simp only [Body.run]
    revert key
    cases Body.step benv p op with
    | error e =>
      cases Body.step benv p' op with
      | error e' => intro key; simpa [Functor.map, Except.map, bind, Except.bind] using key
      | ok y => intro key; simp [Functor.map, Except.map] at key
    | ok x =>
      cases Body.step benv p' op with
      | error e' => intro key; simp [Functor.map, Except.map] at key
      | ok y =>
        intro key
        obtain ⟨r, q⟩ := x
        obtain ⟨r', q'⟩ := y
        simp only [Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq] at key
        obtain ⟨rfl, hq⟩ := key
        have := ih q q' hq
        simp only [bind, Except.bind]
        revert this
        cases Body.run benv q ops <;> cases Body.run benv q' ops <;> intro this <;>
          simp_all [Functor.map, Except.map, pure, Except.pure]

end Jaune.Staging
