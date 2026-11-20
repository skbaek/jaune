import Jaune.Run.Prefix
import Jaune.Run.BodyFactsRlp

/-!
# Facts about a block body's prefix (goal `jaune-shape-and-names-v1`, G2b N4-0)

The receipts and summary of a prefix and the congruences the body facts use. Extracted unchanged
from `Jaune.Run.BodyFacts`.
-/

section
open Jaune
namespace Jaune
/-- **The receipts so far.** The prefix holds the receipts of the transactions at
`0, 1, …, n-1`, in order: its receipt keys are those indices' keys, and each is bound to its
receipt. -/
structure Body.Prefix.Receipts (q : Body.Prefix) (n : Nat) (rcpts : List (Fin 5 × Receipt)) :
    Prop where
  keys : q.receiptKeys = (List.range n).map rlpKey
  length : rcpts.length = n
  get : ∀ (i : Nat) (h : i < rcpts.length), q.receiptsTrie[rlpKey i]? = some rcpts[i]
end Jaune
end

section
open Jaune
namespace Jaune
theorem Body.Prefix.receipts_init (s : State) : (Body.Prefix.init s).Receipts 0 [] :=
  ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
end Jaune
end

section
open Jaune
namespace Jaune
theorem Body.Prefix.Receipts.of_eq {p q : Body.Prefix} {n : Nat} {rcpts : List (Fin 5 × Receipt)}
    (hp : p.Receipts n rcpts) (hk : q.receiptKeys = p.receiptKeys)
    (ht : q.receiptsTrie = p.receiptsTrie) : q.Receipts n rcpts :=
  ⟨hk ▸ hp.keys, hp.length, fun i h => ht ▸ hp.get i h⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- The receipts so far as later steps read them: each receipt key with what the receipt trie
binds it to. -/
def receiptsRead (keys : List Bytes) (trie : Std.TreeMap Bytes (Fin 5 × Receipt) compare) :
    List (Bytes × Option (Fin 5 × Receipt)) :=
  keys.map fun k => (k, trie[k]?)
end Jaune
end

section
open Jaune
namespace Jaune
theorem receiptsRead_insert (keys : List Bytes) (trie : Std.TreeMap Bytes (Fin 5 × Receipt) compare)
    (key : Bytes) (r : Fin 5 × Receipt) :
    receiptsRead (keys ++ [key]) (trie.insert key r) =
      (receiptsRead keys trie).map (fun x => (x.1, if key = x.1 then some r else x.2)) ++
        [(key, some r)] := by
  simp [receiptsRead, Std.TreeMap.getElem?_insert]
end Jaune
end

section
open Jaune
namespace Jaune
/-- What later steps read of a block output, beside the state: the four gas counters and the
receipts so far. -/
def outputSummary (b : BlockOutput) :
    Nat × Nat × Nat × Nat × List (Bytes × Option (Fin 5 × Receipt)) :=
  (b.blockGasUsed, b.blockStateGasUsed, b.cumulativeGasUsed, b.blobGasUsed,
    receiptsRead b.receiptKeys b.receiptsTrie)
end Jaune
end

section
open Jaune
namespace Jaune
theorem Except.ok_bind' {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
end Jaune
end

section
open Jaune
namespace Jaune
/-- **A prefix's summary**: what later steps read of it — the state, the execution, state,
sender and blob gas used so far, and the receipts so far (each receipt key with its receipt). -/
abbrev Body.Prefix.Summary : Type :=
  State × Nat × Nat × Nat × Nat × List (Bytes × Option (Fin 5 × Receipt))
end Jaune
end

section
open Jaune
namespace Jaune
/-- The summary of a prefix. -/
def Body.Prefix.summary (p : Body.Prefix) : Body.Prefix.Summary :=
  (p.state, outputSummary p.toBlockOutput)
end Jaune
end

section
open Jaune
namespace Jaune
theorem forIn_congr_mem {m : Type → Type} [Monad m] {α β : Type} (f g : α → β → m (ForInStep β)) :
    ∀ (l : List α) (b : β), (∀ a ∈ l, ∀ s, f a s = g a s) → forIn l b f = forIn l b g
  | [], b, _ => rfl
  | a :: l, b, h => by
    simp only [List.forIn_cons, h a (List.mem_cons_self ..)]
    congr 1
    funext r
    cases r with
    | done c => rfl
    | yield c => exact Jaune.forIn_congr_mem f g l c (fun x hx => h x (List.mem_cons_of_mem _ hx))
end Jaune
end

section
open Jaune
namespace Jaune
theorem receiptsRead_eq {t t' : Std.TreeMap Bytes (Fin 5 × Receipt) compare} :
    ∀ (ks ks' : List Bytes), receiptsRead ks t = receiptsRead ks' t' →
      ks = ks' ∧ ∀ k ∈ ks, t[k]? = t'[k]?
  | [], [], _ => ⟨rfl, fun _ h => absurd h (List.not_mem_nil)⟩
  | [], _ :: _, h => by simp [receiptsRead] at h
  | _ :: _, [], h => by simp [receiptsRead] at h
  | k :: ks, k' :: ks', h => by
    simp only [receiptsRead, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, hv⟩, h⟩ := h
    obtain ⟨rfl, ih⟩ := Jaune.receiptsRead_eq ks ks' h
    refine ⟨rfl, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · exact ih x hx
end Jaune
end

section
open Jaune
namespace Jaune
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
end Jaune
end
