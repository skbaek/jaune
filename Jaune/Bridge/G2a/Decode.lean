import Batteries.Tactic.OpenPrivate
import Jaune.Transaction
import Jaune.Run.Decode
import Jaune.Bridge.G2a.Old.Body

/-!
# W2-T: the difference theorem for decision 16 (goal `jaune-shape-and-names-v1`, gate G2a, bridge)

Old side = `Bytes.toExceptTransaction`, `decodeTransaction`, `applyBody` and `stateTransitionCoreE`
at `ba15f397` (`Jaune.Transaction`), unedited. New side = the staged decoders of `Jaune.Run.Decode`.

Decision 16 is a behaviour change, so the bridge is a **difference theorem**, not an equality. The
two decoders agree on every slot except exactly the slots `UnknownTypeSlot` names: typed bytes
whose first byte `x` is no transaction type. There the old result is the internal error
`oldUnknownTypeError x` and the new one the rejection `Staging.transactionTypeNotSupported x`. The
statement is lifted through the body's decode (`List.mapM`), `applyBody` and the block transition:
each agrees with the old one unless the run reaches the decode and the first slot that fails to
decode is an unknown-type slot, and then the old result is the internal error and the new one the
rejection, for that slot's byte.

`applyBodyDecoding` and `stateTransitionCoreEDecoding` are `applyBody` and `stateTransitionCoreE`
with the slot decoder as a parameter (the old ones are these at `decodeTransaction`, by `rfl`).
They exist only to state the lift: the staged body run (W2-3) takes today's `decodeTransaction`,
and the switch commit composes it with the staged decoder. This module is deleted with the old side
after the gate's tag.
-/

open private dec from Jaune.Transaction.Parts

namespace Jaune.Bridge.G2a

open Jaune

/-! ### The difference set -/

/-- The bytes the envelope decoders read as a transaction type. -/
def IsTransactionType (x : UInt8) : Prop := x = 0x01 ∨ x = 0x02 ∨ x = 0x03 ∨ x = 0x04

instance (x : UInt8) : Decidable (IsTransactionType x) := by
  unfold IsTransactionType; infer_instance

/-- A slot the old decoder fails as an internal error: typed bytes whose first byte `x` is no
transaction type. -/
def UnknownTypeSlot (slot : Bytes ⊕ Transaction) (x : UInt8) : Prop :=
  ∃ xs, slot = .inl (x :: xs) ∧ ¬ IsTransactionType x

/-- The old decoder's result on an unknown-type slot. -/
def oldUnknownTypeError (x : UInt8) : TransitionError :=
  .internal <| .invariant <| .text s!"type-{x} txs do not exist, decoding failed"

theorem oldUnknownTypeError_ne (x y : UInt8) :
    oldUnknownTypeError x ≠ Staging.transactionTypeNotSupported y := by
  simp [oldUnknownTypeError, Staging.transactionTypeNotSupported]

/-- The old error is on the outer failure channel (an `ImportFailure`, never a candidate
verdict); the new one is the candidate's block rejection. -/
theorem oldUnknownTypeError_split (x : UInt8) :
    (oldUnknownTypeError x).split =
      .inl (.internal (.invariant (.text s!"type-{x} txs do not exist, decoding failed"))) := rfl

theorem transactionTypeNotSupported_split (x : UInt8) :
    (Staging.transactionTypeNotSupported x).split =
      .inr (.transaction (.typePreFork x.toNat
        (.text s!"type-{x} transactions do not exist (EIP-2718), the block is invalid"))) := rfl

/-! ### A predicate carried through `Except` binds -/

/-- Every error of `r` satisfies `P` and every value satisfies `Q`. -/
def Holds {ε α : Type} (P : ε → Prop) (Q : α → Prop) (r : Except ε α) : Prop :=
  (∀ e, r = .error e → P e) ∧ (∀ a, r = .ok a → Q a)

theorem Holds.bind {ε α β : Type} {P : ε → Prop} {Q : β → Prop} {m : Except ε α}
    {f : α → Except ε β} (hm : ∀ e, m = .error e → P e) (hf : ∀ a, Holds P Q (f a)) :
    Holds P Q (m >>= f) := by
  rcases m with e | a
  · exact ⟨fun e' h => (by cases h; exact hm e rfl), fun _ h => (by cases h)⟩
  · exact hf a

theorem Holds.ite {ε α : Type} {P : ε → Prop} {Q : α → Prop} {c : Prop} [Decidable c]
    {t f : Except ε α} (ht : c → Holds P Q t) (hf : ¬ c → Holds P Q f) :
    Holds P Q (if c then t else f) := by
  by_cases h : c
  · simp only [h, ite_true]; exact ht h
  · simp only [h, ite_false]; exact hf h

theorem Holds.error {ε α : Type} {P : ε → Prop} {Q : α → Prop} {e : ε} (h : P e) :
    Holds P Q (.error e) :=
  ⟨fun _ h' => (by cases h'; exact h), fun _ h' => (by cases h')⟩

theorem Holds.ok {ε α : Type} {P : ε → Prop} {Q : α → Prop} {a : α} (h : Q a) :
    Holds P Q (.ok a) :=
  ⟨fun _ h' => (by cases h'), fun _ h' => (by cases h'; exact h)⟩

/-! ### What the old envelope decoder fails with on a transaction-type byte -/

/-- The reasons the envelope decoder gives for a transaction-type slot: a strict-decode reason or
one of the two mandatory-receiver reasons. Never internal, never `typePreFork`. -/
def EnvelopeReason : TransitionError → Prop
  | .decode _ => True
  | .transaction (.type3ContractCreation _) => True
  | .transaction (.type4ContractCreation _) => True
  | _ => False

theorem dec_fails {α : Type} (m : Except DecodeError α) :
    ∀ e, dec m = .error e → EnvelopeReason e := by
  intro e h
  rcases m with d | a
  · cases h; trivial
  · cases h

/-- A typed transaction is not legacy. -/
def IsTyped (tx : Transaction) : Prop := tx.type.index ≠ 0

theorem toExceptTransaction_holds {x : UInt8} (xs : Bytes) (hx : IsTransactionType x) :
    Holds EnvelopeReason IsTyped (Bytes.toExceptTransaction (x :: xs)) := by
  unfold Bytes.toExceptTransaction
  dsimp only
  split
  all_goals
    repeat' (first
      | exact dec_fails _
      | exact Holds.error trivial
      | exact Holds.ok (by simp [IsTyped, TransactionType.index])
      | (refine Holds.bind ?_ ?_)
      | (refine Holds.ite ?_ ?_)
      | (intro))
  all_goals
    exfalso
    rcases hx with rfl | rfl | rfl | rfl <;> simp_all

/-! ### The slot decoders -/

theorem toExceptTransaction_unknown {x : UInt8} (xs : Bytes) (hx : ¬ IsTransactionType x) :
    Bytes.toExceptTransaction (x :: xs) = .error (oldUnknownTypeError x) := by
  unfold Bytes.toExceptTransaction
  dsimp only
  split <;> first | rfl | (exfalso; simp_all [IsTransactionType])

theorem isTransactionType_iff (x : UInt8) :
    Staging.isTransactionType x = true ↔ IsTransactionType x := by
  simp [Staging.isTransactionType, IsTransactionType, or_assoc]

theorem staged_toExceptTransaction_unknown {x : UInt8} (xs : Bytes) (hx : ¬ IsTransactionType x) :
    Staging.Bytes.toExceptTransaction (x :: xs) = .error (Staging.transactionTypeNotSupported x) := by
  simp only [Staging.Bytes.toExceptTransaction, (isTransactionType_iff x).not.mpr hx,
    Bool.false_eq_true, ite_false]

theorem staged_toExceptTransaction_eq {x : UInt8} (xs : Bytes) (hx : IsTransactionType x) :
    Staging.Bytes.toExceptTransaction (x :: xs) = Bytes.toExceptTransaction (x :: xs) := by
  simp only [Staging.Bytes.toExceptTransaction, (isTransactionType_iff x).mpr hx, ite_true]

/-- Off the difference set the staged envelope decoder is the old one. -/
theorem staged_toExceptTransaction_eq_of_not_unknown (xs : Bytes)
    (h : ∀ x, ¬ UnknownTypeSlot (.inl xs) x) :
    Staging.Bytes.toExceptTransaction xs = Bytes.toExceptTransaction xs := by
  rcases xs with _ | ⟨x, xs⟩
  · rfl
  · by_cases hx : IsTransactionType x
    · exact staged_toExceptTransaction_eq xs hx
    · exact absurd ⟨xs, rfl, hx⟩ (h x)

theorem decodeTransaction_eq_of_not_unknown (rules : ForkRules) (slot : Bytes ⊕ Transaction)
    (h : ∀ x, ¬ UnknownTypeSlot slot x) :
    Staging.decodeTransaction rules slot = decodeTransaction rules slot := by
  rcases slot with xs | tx
  · simp only [Staging.decodeTransaction, decodeTransaction,
      staged_toExceptTransaction_eq_of_not_unknown xs h]
  · rfl

theorem decodeTransaction_of_unknown {rules : ForkRules} {slot : Bytes ⊕ Transaction} {x : UInt8}
    (h : UnknownTypeSlot slot x) :
    decodeTransaction rules slot = .error (oldUnknownTypeError x) ∧
      Staging.decodeTransaction rules slot = .error (Staging.transactionTypeNotSupported x) := by
  obtain ⟨xs, rfl, hx⟩ := h
  simp only [decodeTransaction, Staging.decodeTransaction, toExceptTransaction_unknown xs hx,
    staged_toExceptTransaction_unknown xs hx]
  exact ⟨rfl, rfl⟩

/-- The errors of the old slot decoder off the difference set: an envelope reason, or the
admission reason `typePreFork` for a typed transaction's own (non-zero) type number. -/
theorem decodeTransaction_error_of_not_unknown {rules : ForkRules} {slot : Bytes ⊕ Transaction}
    (h : ∀ x, ¬ UnknownTypeSlot slot x) {e : TransitionError}
    (he : decodeTransaction rules slot = .error e) :
    EnvelopeReason e ∨ ∃ n d, n ≠ 0 ∧ n ≤ 4 ∧ e = .transaction (.typePreFork n d) := by
  rcases slot with (_ | ⟨x, xs⟩) | tx
  · left
    simp only [decodeTransaction, Bytes.toExceptTransaction, bind, Except.bind] at he
    cases he; trivial
  · have hx : IsTransactionType x := by
      by_contra hx; exact h x ⟨xs, rfl, hx⟩
    have hh := toExceptTransaction_holds xs hx
    simp only [decodeTransaction, bind, Except.bind] at he
    split at he
    · rename_i e' he'
      cases he; exact .inl (hh.1 _ he')
    · rename_i tx htx
      have hty := hh.2 tx htx
      split at he
      · rename_i e2 he2
        cases he
        unfold checkTransactionTypeAdmitted at he2
        split at he2
        · cases he2
        · cases he2
          refine .inr ⟨_, _, hty, ?_, rfl⟩
          cases tx.type <;> simp [TransactionType.index]
      · cases he
  · cases he

/-- **Difference theorem, slot.** The staged slot decoder equals the old one off the difference
set; on it, the old result is the internal error and the new one the rejection, for the slot's
first byte. -/
theorem decodeTransaction_difference (rules : ForkRules) (slot : Bytes ⊕ Transaction) :
    (Staging.decodeTransaction rules slot = decodeTransaction rules slot ∧
        ∀ x, ¬ UnknownTypeSlot slot x) ∨
      ∃ x, UnknownTypeSlot slot x ∧
        decodeTransaction rules slot = .error (oldUnknownTypeError x) ∧
        Staging.decodeTransaction rules slot = .error (Staging.transactionTypeNotSupported x) := by
  by_cases h : ∃ x, UnknownTypeSlot slot x
  · obtain ⟨x, hx⟩ := h
    exact .inr ⟨x, hx, decodeTransaction_of_unknown hx⟩
  · push Not at h
    exact .inl ⟨decodeTransaction_eq_of_not_unknown rules slot h, h⟩

/-- The old slot decoder returns the internal error exactly on the difference set (and there for
the slot's first byte, `decodeTransaction_of_unknown`). -/
theorem decodeTransaction_eq_oldUnknownTypeError_iff (rules : ForkRules)
    (slot : Bytes ⊕ Transaction) :
    (∃ x, decodeTransaction rules slot = .error (oldUnknownTypeError x)) ↔
      ∃ x, UnknownTypeSlot slot x := by
  constructor
  · rintro ⟨x, he⟩
    by_contra h
    push Not at h
    rcases decodeTransaction_error_of_not_unknown h he with he' | ⟨_, _, _, _, he'⟩
    · simp [oldUnknownTypeError, EnvelopeReason] at he'
    · simp [oldUnknownTypeError] at he'
  · rintro ⟨x, h⟩
    exact ⟨x, (decodeTransaction_of_unknown h).1⟩

/-- The staged slot decoder returns the rejection for `x` exactly on the slots with first byte
`x` in the difference set, for every byte `x` that is no transaction type. -/
theorem decodeTransaction_eq_transactionTypeNotSupported_iff (rules : ForkRules)
    (slot : Bytes ⊕ Transaction) {x : UInt8} (hx : ¬ IsTransactionType x) :
    Staging.decodeTransaction rules slot = .error (Staging.transactionTypeNotSupported x) ↔
      UnknownTypeSlot slot x := by
  constructor
  · intro he
    by_cases h : ∃ y, UnknownTypeSlot slot y
    · obtain ⟨y, hy⟩ := h
      rw [(decodeTransaction_of_unknown (rules := rules) hy).2] at he
      simp only [Except.error.injEq, Staging.transactionTypeNotSupported,
        TransitionError.transaction.injEq, TransactionValidationError.typePreFork.injEq] at he
      have : y = x := UInt8.toNat_inj.mp he.1
      exact this ▸ hy
    · push Not at h
      rw [decodeTransaction_eq_of_not_unknown rules slot h] at he
      rcases decodeTransaction_error_of_not_unknown h he with he' | ⟨n, d, hn0, hn4, he'⟩
      · simp [Staging.transactionTypeNotSupported, EnvelopeReason] at he'
      · simp only [Staging.transactionTypeNotSupported, TransitionError.transaction.injEq,
          TransactionValidationError.typePreFork.injEq] at he'
        exfalso
        apply hx
        have hn : x.toNat = n := he'.1
        unfold IsTransactionType
        rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl | rfl
        · exact .inl (UInt8.toNat_inj.mp hn)
        · exact .inr (.inl (UInt8.toNat_inj.mp hn))
        · exact .inr (.inr (.inl (UInt8.toNat_inj.mp hn)))
        · exact .inr (.inr (.inr (UInt8.toNat_inj.mp hn)))
  · intro h
    exact (decodeTransaction_of_unknown h).2

/-! ### The body's decode -/

/-- The run's decode differs: the first slot that fails to decode (every earlier slot decodes) is
an unknown-type slot with first byte `x`. -/
def DecodeDiffers (rules : ForkRules) (txs : List (Bytes ⊕ Transaction)) (x : UInt8) : Prop :=
  ∃ pre slot post, txs = pre ++ slot :: post ∧ UnknownTypeSlot slot x ∧
    ∀ s ∈ pre, ∃ tx, decodeTransaction rules s = .ok tx

/-- **Difference theorem, the whole list.** -/
theorem mapM_decodeTransaction_difference (rules : ForkRules) (txs : List (Bytes ⊕ Transaction)) :
    (txs.mapM (Staging.decodeTransaction rules) = txs.mapM (decodeTransaction rules) ∧
        ∀ x, ¬ DecodeDiffers rules txs x) ∨
      ∃ x, DecodeDiffers rules txs x ∧
        txs.mapM (decodeTransaction rules) = .error (oldUnknownTypeError x) ∧
        txs.mapM (Staging.decodeTransaction rules) =
          .error (Staging.transactionTypeNotSupported x) := by
  induction txs with
  | nil =>
    refine .inl ⟨rfl, ?_⟩
    rintro x ⟨pre, slot, post, h, -, -⟩
    simp at h
  | cons s rest ih =>
    rcases decodeTransaction_difference rules s with ⟨hs, hnot⟩ | ⟨x, hx, hold, hnew⟩
    · cases hd : decodeTransaction rules s with
      | error e =>
        refine .inl ⟨by simp [List.mapM_cons, hs, hd, bind, Except.bind], ?_⟩
        rintro y ⟨pre, slot, post, h, hu, hpre⟩
        rcases pre with _ | ⟨p, pre⟩
        · simp only [List.nil_append, List.cons.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact hnot y hu
        · simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, -⟩ := h
          obtain ⟨tx, htx⟩ := hpre _ List.mem_cons_self
          rw [hd] at htx; cases htx
      | ok tx =>
        rcases ih with ⟨hr, hrn⟩ | ⟨x, hx, hold, hnew⟩
        · refine .inl ⟨by simp [List.mapM_cons, hs, hd, hr, bind, Except.bind], ?_⟩
          rintro y ⟨pre, slot, post, h, hu, hpre⟩
          rcases pre with _ | ⟨p, pre⟩
          · simp only [List.nil_append, List.cons.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact hnot y hu
          · simp only [List.cons_append, List.cons.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact hrn y ⟨pre, slot, post, rfl, hu, fun t ht => hpre t (by simp [ht])⟩
        · refine .inr ⟨x, ?_, ?_, ?_⟩
          · obtain ⟨pre, slot, post, hrest, hu, hpre⟩ := hx
            refine ⟨s :: pre, slot, post, by simp [hrest], hu, ?_⟩
            intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact ⟨tx, hd⟩
            · exact hpre t ht
          · simp [List.mapM_cons, hd, hold, bind, Except.bind]
          · simp [List.mapM_cons, hs, hd, hnew, bind, Except.bind]
    · refine .inr ⟨x, ⟨[], s, rest, rfl, hx, by simp⟩, ?_, ?_⟩
      · simp [List.mapM_cons, hold, bind, Except.bind]
      · simp [List.mapM_cons, hnew, bind, Except.bind]

/-! ### `applyBody` -/

/-- `applyBody` with its slot decoder as a parameter: the old `applyBody` is this at
`decodeTransaction` (`applyBody_eq_decoding`); the new side of the lift is this at
`Staging.decodeTransaction`. -/
def applyBodyDecoding
    (decode : ForkRules → Bytes ⊕ Transaction → Except TransitionError Transaction)
    (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
    (wds : List Withdrawal) :
    Except TransitionError (State × BlockOutput) := do
  let rules := benv.stat.rules
  let ⟨stBeacon, bal⟩ ← beaconRootsCall rules benv
  let benvBeacon : Benv := benv.withState stBeacon
  let ⟨stHistory, bal⟩ ← historyStorageCall rules benvBeacon bal
  let benvHistory := benvBeacon.withState stHistory
  let ⟨benvTxs, boutTxs⟩ ←
    applyTransactions (← txs.mapM (decode benvHistory.stat.rules)).putIndex benvHistory {BlockOutput.init with blockAccessListBuilder := bal}
  let ⟨stWds, boutWds⟩ := withdrawalsPass rules benvTxs boutTxs wds
  let ⟨stReq, boutReq⟩ ← requestsPass rules (benvTxs.withState stWds) boutWds
  let stRewards := match rules.proofOfWork with
    | none => stReq
    | some pow => payRewards pow benv.stat.number benv.stat.coinbase ommers stReq
  let list := match rules.blockAccessListRules with
    | none => []
    | some _ => boutReq.blockAccessListBuilder.build
  checkBlockAccessListGasLimit rules benv.stat.blockGasLimit list
  .ok ⟨stRewards, {boutReq with blockAccessList := list}⟩

theorem applyBody_eq_decoding (benv : Benv) (txs : List (Bytes ⊕ Transaction))
    (ommers : List Header) (wds : List Withdrawal) :
    applyBody benv txs ommers wds = applyBodyDecoding decodeTransaction benv txs ommers wds := rfl

/-- The body run's result differs: both pre-execution system calls succeed, and the decode
differs (`DecodeDiffers`) for byte `x`. -/
def BodyDiffers (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (x : UInt8) : Prop :=
  ∃ stBeacon bal stHistory bal',
    beaconRootsCall benv.stat.rules benv = .ok (stBeacon, bal) ∧
    historyStorageCall benv.stat.rules (benv.withState stBeacon) bal = .ok (stHistory, bal') ∧
    DecodeDiffers benv.stat.rules txs x

/-- **Difference theorem, `applyBody`.** The body run with the staged decoder equals `applyBody`
unless `BodyDiffers`; then `applyBody` fails with the internal error and the staged run with the
rejection, for the first failing slot's byte. -/
theorem applyBody_difference (benv : Benv) (txs : List (Bytes ⊕ Transaction))
    (ommers : List Header) (wds : List Withdrawal) :
    (applyBodyDecoding Staging.decodeTransaction benv txs ommers wds =
          applyBody benv txs ommers wds ∧ ∀ x, ¬ BodyDiffers benv txs x) ∨
      ∃ x, BodyDiffers benv txs x ∧
        applyBody benv txs ommers wds = .error (oldUnknownTypeError x) ∧
        applyBodyDecoding Staging.decodeTransaction benv txs ommers wds =
          .error (Staging.transactionTypeNotSupported x) := by
  rw [applyBody_eq_decoding]
  unfold applyBodyDecoding
  cases hb : beaconRootsCall benv.stat.rules benv with
  | error e =>
    refine .inl ⟨by simp [hb, bind, Except.bind], ?_⟩
    rintro x ⟨_, _, _, _, h1, -⟩
    rw [hb] at h1; cases h1
  | ok p =>
    obtain ⟨stB, bal⟩ := p
    cases hh : historyStorageCall benv.stat.rules (benv.withState stB) bal with
    | error e =>
      refine .inl ⟨by simp [hb, hh, bind, Except.bind], ?_⟩
      rintro x ⟨_, _, _, _, h1, h2, -⟩
      rw [hb] at h1; cases h1
      rw [hh] at h2; cases h2
    | ok q =>
      obtain ⟨stH, bal'⟩ := q
      have hr : ((benv.withState stB).withState stH).stat.rules = benv.stat.rules := rfl
      rcases mapM_decodeTransaction_difference benv.stat.rules txs with
        ⟨hm, hmn⟩ | ⟨x, hx, hold, hnew⟩
      · refine .inl ⟨by simp only [hb, hh, hr, hm, bind, Except.bind], ?_⟩
        rintro x ⟨_, _, _, _, h1, h2, h3⟩
        rw [hb] at h1; cases h1
        rw [hh] at h2; cases h2
        exact hmn x h3
      · refine .inr ⟨x, ⟨_, _, _, _, hb, hh, hx⟩, ?_, ?_⟩
        · simp only [hb, hh, hr, hold, bind, Except.bind]
        · simp only [hb, hh, hr, hnew, bind, Except.bind]

/-! ### The block transition -/

/-- `stateTransitionCoreE` over `applyBodyDecoding decode`. -/
def stateTransitionCoreEDecoding
    (decode : ForkRules → Bytes ⊕ Transaction → Except TransitionError Transaction)
    {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except ε Unit) : Except ε BlockChain := do
  let rules := f.ruleSet
  Except.mapError embed (validateHeader rules ch block.header)
  checkOmmers ()
  let benv : Benv := initBlockEnvironment f ch block.header
  let ⟨st, bout⟩ ← Except.mapError embed
    (applyBodyDecoding decode benv block.transactions block.ommers block.withdrawals)
  let blockStateRoot : U256 := st.root
  let transactionsRoot : U256 := getTransactionsRoot bout
  let receiptRoot : U256 := getReceiptRoot bout
  let blockLogsBloom : Bytes := logsBloom bout.blockLogs
  let withdrawalsRoot : U256 := getWithdrawalsRoot bout
  let requestsHash :=
    if rules.header.requestsHash then some (computeRequestsHash bout.requests) else none
  Except.mapError (embed ∘ TransitionError.block) <|
    stateTransitionChecks bout block.header
      transactionsRoot blockStateRoot receiptRoot
      blockLogsBloom withdrawalsRoot requestsHash
  Except.mapError (embed ∘ TransitionError.block) <|
    blockAccessListCheck rules bout block.header
  .ok ⟨appendBlock ch.blocks block, st, ch.chainId⟩

theorem stateTransitionCoreE_eq_decoding {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) :
    stateTransitionCoreE embed f ch block checkOmmers =
      stateTransitionCoreEDecoding decodeTransaction embed f ch block checkOmmers := rfl

/-- The transition's result differs: the header validates, the ommer check passes and the body
differs (`BodyDiffers`) for byte `x`. -/
def TransitionDiffers {ε : Type} (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except ε Unit) (x : UInt8) : Prop :=
  validateHeader f.ruleSet ch block.header = .ok () ∧ checkOmmers () = .ok () ∧
    BodyDiffers (initBlockEnvironment f ch block.header) block.transactions x

/-- **Difference theorem, block transition.** For every error embedding (the importer's
`TransitionError.split` routes the old error to the outer failure channel and the new one to the
candidate's rejection: `oldUnknownTypeError_split`, `transactionTypeNotSupported_split`). -/
theorem stateTransitionCoreE_difference {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) :
    (stateTransitionCoreEDecoding Staging.decodeTransaction embed f ch block checkOmmers =
          stateTransitionCoreE embed f ch block checkOmmers ∧
        ∀ x, ¬ TransitionDiffers f ch block checkOmmers x) ∨
      ∃ x, TransitionDiffers f ch block checkOmmers x ∧
        stateTransitionCoreE embed f ch block checkOmmers = .error (embed (oldUnknownTypeError x)) ∧
        stateTransitionCoreEDecoding Staging.decodeTransaction embed f ch block checkOmmers =
          .error (embed (Staging.transactionTypeNotSupported x)) := by
  rw [stateTransitionCoreE_eq_decoding]
  unfold stateTransitionCoreEDecoding
  cases hv : validateHeader f.ruleSet ch block.header with
  | error e =>
    refine .inl ⟨by simp [hv, bind, Except.bind, Except.mapError], ?_⟩
    rintro x ⟨h1, -⟩; rw [hv] at h1; cases h1
  | ok u =>
    cases ho : checkOmmers () with
    | error e =>
      refine .inl ⟨by simp [hv, bind, Except.bind, Except.mapError], ?_⟩
      rintro x ⟨-, h2, -⟩; rw [ho] at h2; cases h2
    | ok u' =>
      rcases applyBody_difference (initBlockEnvironment f ch block.header) block.transactions block.ommers
          block.withdrawals with ⟨hb, hbn⟩ | ⟨x, hx, hold, hnew⟩
      · refine .inl ⟨?_, ?_⟩
        · rw [applyBody_eq_decoding] at hb
          simp only [hv, hb, bind, Except.bind, Except.mapError]
        · rintro x ⟨-, -, h3⟩; exact hbn x h3
      · refine .inr ⟨x, ⟨by cases u; exact hv, by cases u'; exact ho, hx⟩, ?_, ?_⟩
        · rw [applyBody_eq_decoding] at hold
          simp only [hv, hold, bind, Except.bind, Except.mapError]
        · simp only [hv, hnew, bind, Except.bind, Except.mapError]

end Jaune.Bridge.G2a
