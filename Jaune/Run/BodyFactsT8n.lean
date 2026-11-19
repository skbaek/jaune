import Jaune.T8n
import Jaune.Run.BodyFacts
import Jaune.Bridge.G2b.CheckedTop

/-!
# The transition tool's driver keeps the receipts so far (goal `jaune-shape-and-names-v1`, W2 cut F)

t8n's tolerant transaction loop runs each accepted transaction at the accepted count, so it keeps
`Body.Prefix.Receipts` with the accepted transactions' receipts; its deposit step therefore reads
the receipts so far (`parseDepositRequests_of_receipts`). Adapter class: it is a theorem
about the adapter's own driver.
-/

namespace Jaune.T8n

open Jaune

private theorem checkedStep_observe (benv : Benv) :
    Checked.Body.step benv = fun p op => (Body.step benv p op).map Prod.snd :=
  funext fun p => funext fun op => Checked.Body.step_observe benv p op

/-- The Checked fold keeps exactly the prefixes, rejections and accepted transactions of
the waiting body step. -/
theorem foldTransactions_observe (benv : Benv) :
    foldTransactions benv =
      foldTransactionsWith (fun p op => (Body.step benv p op).map Prod.snd) := by
  rw [foldTransactions, checkedStep_observe]

/-- State-test mode has the same outcome and error after selecting its single transaction. -/
theorem runStateTest_observe (benv : Benv) (txs : List (TransactionParse Transaction)) :
    runStateTest benv txs = (do
      let selected := match txs with | [] => [] | tx :: _ => [⟨0, tx⟩]
      let ⟨p, rej, inc⟩ ← foldTransactionsWith
        (fun p op => (Body.step benv p op).map Prod.snd) selected (Body.Prefix.init benv.state) [] []
      .ok ⟨p.state, p.toBlockOutput, rej, none, inc⟩) := by
  simp only [runStateTest, foldTransactions_observe]
  cases txs <;> rfl

/-- The complete blockchain-mode outcome agrees, including a returned block exception
with its prefix and the built access list. -/
theorem runBlockchain_observe (benv : Benv) (txs : List (TransactionParse Transaction))
    (wds : List Withdrawal) (reward : Option Nat) (ommers : List T8nOmmer) :
    runBlockchain benv txs wds reward ommers =
      runBlockchainWith (fun p op => (Body.step benv p op).map Prod.snd) benv txs wds reward ommers := by
  rw [runBlockchain, checkedStep_observe]

/-- The tolerant loop keeps the receipts so far, one receipt per accepted transaction. -/
theorem foldTransactions_receipts (benv : Benv) :
    ∀ (l : List (Nat × TransactionParse Transaction)) (p : Body.Prefix) (rej : List Rejection)
      (inc : List Transaction) (rcpts : List (Fin 5 × Receipt)) (q : Body.Prefix)
      (rej' : List Rejection) (inc' : List Transaction),
      p.Receipts inc.length rcpts → foldTransactions benv l p rej inc = .ok ⟨q, rej', inc'⟩ →
      ∃ rs, q.Receipts inc'.length (rcpts ++ rs)
  | [], p, rej, inc, rcpts, q, rej', inc', hp, h => by
    simp only [foldTransactionsWith, foldTransactions, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨[], by simpa using hp⟩
  | ⟨i, .error e⟩ :: rest, p, rej, inc, rcpts, q, rej', inc', hp, h => by
    rw [foldTransactions, foldTransactionsWith, ← foldTransactions] at h
    exact foldTransactions_receipts benv rest p _ inc rcpts q rej' inc' hp h
  | ⟨i, .ok tx⟩ :: rest, p, rej, inc, rcpts, q, rej', inc', hp, h => by
    rw [foldTransactions_observe, foldTransactionsWith] at h
    cases hs : Body.step benv p (.transaction tx inc.length) with
    | ok result =>
      rcases result with ⟨r, p'⟩
      simp only [hs, Except.map] at h
      obtain ⟨receipt, hp', -, -⟩ := hp.step_transaction hs
      have hp'' : p'.Receipts (inc ++ [tx]).length (rcpts ++ [receipt]) := by simpa using hp'
      obtain ⟨rs, hq⟩ := foldTransactions_receipts benv rest p' rej (inc ++ [tx]) _ q rej' inc' hp''
        (by rw [foldTransactions_observe]; exact h)
      exact ⟨receipt :: rs, by simpa using hq⟩
    | error error =>
      simp only [hs, Except.map] at h
      split at h
      · cases h
      · exact foldTransactions_receipts benv rest p _ inc rcpts q rej' inc' hp
          (by rw [foldTransactions_observe]; exact h)

end Jaune.T8n
