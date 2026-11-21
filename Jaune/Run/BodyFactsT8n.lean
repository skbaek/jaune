import Jaune.T8n
import Jaune.FrameRun.Facts

/-!
# The transition tool's driver keeps the receipts so far (goal `jaune-shape-and-names-v1`, W2 cut F)

t8n's tolerant transaction loop runs each accepted transaction at the accepted count, so it keeps
`Body.Prefix.Receipts` with the accepted transactions' receipts; its deposit step therefore reads
the receipts so far (`parseDepositRequests_of_receipts`). Adapter class: it is a theorem
about the adapter's own driver.
-/

namespace Jaune.T8n

open Jaune

/-- The tolerant loop keeps the receipts so far, one receipt per accepted transaction. -/
theorem foldTransactions_receipts (block : BlockContext) :
    ∀ (l : List (Nat × TransactionParse Transaction)) (p : Body.Prefix) (rej : List Rejection)
      (inc : List Transaction) (rcpts : List (Fin 5 × Receipt)) (q : Body.Prefix)
      (rej' : List Rejection) (inc' : List Transaction),
      p.Receipts inc.length rcpts → foldTransactions block l p rej inc = .ok ⟨q, rej', inc'⟩ →
      ∃ rs, q.Receipts inc'.length (rcpts ++ rs)
  | [], p, rej, inc, rcpts, q, rej', inc', hp, h => by
    simp only [foldTransactionsWith, foldTransactions, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨[], by simpa using hp⟩
  | ⟨i, .error e⟩ :: rest, p, rej, inc, rcpts, q, rej', inc', hp, h => by
    rw [foldTransactions, foldTransactionsWith, ← foldTransactions] at h
    exact foldTransactions_receipts block rest p _ inc rcpts q rej' inc' hp h
  | ⟨i, .ok tx⟩ :: rest, p, rej, inc, rcpts, q, rej', inc', hp, h => by
    rw [foldTransactions, foldTransactionsWith] at h
    cases hs : Body.step block p (.transaction tx inc.length) with
    | ok p' =>
      simp only [hs] at h
      obtain ⟨receipt, hp', -, -⟩ := Body.Prefix.Receipts.step_transaction hp hs
      have hp'' : p'.Receipts (inc ++ [tx]).length (rcpts ++ [receipt]) := by simpa using hp'
      obtain ⟨rs, hq⟩ := foldTransactions_receipts block rest p' rej (inc ++ [tx]) _ q rej' inc' hp''
        (by rw [foldTransactions]; exact h)
      exact ⟨receipt :: rs, by simpa using hq⟩
    | error error =>
      simp only [hs] at h
      split at h
      · cases h
      · exact foldTransactions_receipts block rest p _ inc rcpts q rej' inc' hp
          (by rw [foldTransactions]; exact h)

end Jaune.T8n
