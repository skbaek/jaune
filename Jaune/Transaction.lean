import Jaune.Transaction.Parts
import Jaune.Run.Canonical
-- `List.IsChain` itself is Batteries; its infix/suffix closure lemmas, which
-- the retained-history predicate below reasons with, are Mathlib's.
import Mathlib.Data.List.Chain

namespace Jaune

open Jaune

/-!
# Transaction, block, and chain processing

This module provides transaction, block, and chain-level operations. The
transaction and block runners in `Jaune.Run` compose the top-level message
driver with admission, settlement, and commitment checks.
-/

-- The single boundary shared by all four system transactions (beacon roots,
-- history storage, withdrawal requests, consolidation requests), so each takes
-- its own input state as the original state.

--------------- RETAINED HISTORY ---------------

-- P0.2's history half. `getLast256BlockHashes` recomputes only the tip's own
-- header hash and reads every other entry out of a retained block's
-- `parentHash` field, so the ancestry `BLOCKHASH` reports is only as
-- trustworthy as those fields. The predicates below say exactly what has to
-- hold of a snapshot's retained suffix for the lookup to be correct, and the
-- theorems after them prove it is -- for a full window, for an early chain,
-- and at the truncated boundary.

/-- Two adjacent retained blocks: consecutive numbering and an authenticated
parent-hash link. This carries clauses (1) and (2) of the design report's
`RetainedHistoryValid`; clause (2) is what makes the `BLOCKHASH` window
provable at all, because every entry below the tip *is* one of these fields. -/
def Block.Links (prev next : Block) : Prop :=
  next.header.number = prev.header.number + 1 ∧
  next.header.parentHash = prev.header.hash

instance (prev next : Block) : Decidable (Block.Links prev next) := by
  unfold Block.Links; infer_instance

/-- The retained window a snapshot's execution actually reads, oldest-first:
the 255 newest blocks. `appendBlock` keeps exactly that many, so for a chain
built by state transitions this is the whole block list. -/
def BlockChain.retained (chain : BlockChain) : List Block :=
  (chain.blocks.reverse.take 255).reverse

/-- A snapshot's retained history is valid when its blocks are consecutively
numbered and hash-linked, their headers are wire-representable, and it covers
enough ancestry for the `BLOCKHASH` window: either 255 blocks are retained, or
the chain still begins at block zero. The last clause is the design report's
"retention of at least `min 255 n`" written in terms of the oldest retained
header, which is the form the window proof consumes. -/
def BlockChain.RetainedHistoryValid (chain : BlockChain) : Prop :=
  chain.blocks.IsChain Block.Links ∧
  (∀ b ∈ chain.blocks, b.header.WireWellFormed) ∧
  (255 ≤ chain.blocks.length ∨ ∀ b ∈ chain.blocks.head?, b.header.number = 0)

instance (chain : BlockChain) : Decidable (chain.RetainedHistoryValid) := by
  unfold BlockChain.RetainedHistoryValid; infer_instance

/-- The shape of the hash list, stated once so no later proof has to unfold
the `match`: the retained blocks' `parentHash` fields, oldest-first, followed
by the tip's own recomputed header hash. -/
theorem getLast256BlockHashes_eq {chain : BlockChain} {b : Block} {bs : List Block}
    (hN : chain.blocks.reverse.take 255 = b :: bs) :
    BlockChain.recentBlockHashes chain
      = chain.retained.map (fun x => x.header.parentHash) ++ [b.header.hash] := by
  unfold BlockChain.recentBlockHashes BlockChain.retained
  rw [hN]
  simp [Header.hash, List.map_reverse]

/-- Below the tip, every entry is a retained block's `parentHash` field. -/
theorem getLast256BlockHashes_getD_lt {chain : BlockChain} {b : Block}
    {bs : List Block} (hN : chain.blocks.reverse.take 255 = b :: bs) {j : Nat}
    (hj : j < chain.retained.length) :
    (BlockChain.recentBlockHashes chain).getD j 0
      = chain.retained[j].header.parentHash := by
  rw [getLast256BlockHashes_eq hN, List.getD,
    List.getElem?_append_left (by simpa using hj),
    List.getElem?_eq_getElem (by simpa using hj)]
  simp

/-- The last entry is the tip's own recomputed header hash. -/
theorem getLast256BlockHashes_getD_last {chain : BlockChain} {b : Block}
    {bs : List Block} (hN : chain.blocks.reverse.take 255 = b :: bs) :
    (BlockChain.recentBlockHashes chain).getD chain.retained.length 0 = b.header.hash := by
  rw [getLast256BlockHashes_eq hN, List.getD,
    List.getElem?_append_right (by simp)]
  simp

/-- Consecutive numbering in closed form: the `i`th retained block sits `i`
above the oldest one. -/
theorem Block.isChain_number {l : List Block} (h : l.IsChain Block.Links) :
    ∀ {i : Nat} (hi : i < l.length) (h0 : 0 < l.length),
      l[i].header.number = l[0].header.number + i := by
  intro i
  induction i with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro hi h0
    have hlink := (List.isChain_iff_getElem.mp h) n (by omega)
    rw [hlink.1, ih (by omega) h0]
    omega

/-- The authenticated link: every retained block's `parentHash` is the true
header hash of the block below it. -/
theorem Block.isChain_parentHash {l : List Block} (h : l.IsChain Block.Links)
    {i : Nat} (hi : i + 1 < l.length) :
    l[i + 1].header.parentHash = l[i].header.hash :=
  ((List.isChain_iff_getElem.mp h) i hi).2

/-- Consecutive numbering makes the height a key: a retained history holds at
most one block per height. -/
theorem Block.isChain_number_inj {l : List Block} (h : l.IsChain Block.Links)
    {x y : Block} (hx : x ∈ l) (hy : y ∈ l)
    (hn : x.header.number = y.header.number) : x = y := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  have h0 : 0 < l.length := by omega
  have hxi := Block.isChain_number h hi h0
  have hyj := Block.isChain_number h hj h0
  have hij : i = j := by omega
  subst hij; rfl

/-- A newest-first window, read back oldest-first, is a suffix. -/
theorem Block.take_reverse_suffix (l : List Block) (n : Nat) :
    (l.reverse.take n).reverse <:+ l := by
  have h : l.reverse.take n <+: l.reverse := List.take_prefix _ _
  simpa using List.reverse_prefix.mp (by simpa using h)

/-- The retained window is a suffix of the block list. -/
theorem BlockChain.retained_suffix (chain : BlockChain) :
    chain.retained <:+ chain.blocks :=
  Block.take_reverse_suffix _ _

/-- A nonempty list's newest-first window is headed by its last element. -/
theorem Block.take_reverse_eq_cons {l : List Block} {x : Block} {n : Nat}
    (hn : 0 < n) (h : l.getLast? = some x) :
    ∃ bs, l.reverse.take n = x :: bs := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hr : l.reverse.head? = some x := by
    rw [List.head?_reverse]; exact h
  match hl : l.reverse with
  | [] => rw [hl] at hr; simp at hr
  | y :: ys =>
    rw [hl] at hr
    simp only [List.head?_cons, Option.some.injEq] at hr
    subst hr
    exact ⟨ys.take m, rfl⟩

/-- A nonempty chain's retained window is headed, newest-first, by its tip. -/
theorem BlockChain.take_reverse_eq_cons {chain : BlockChain} {tip : Block}
    (h : chain.blocks.getLast? = some tip) :
    ∃ bs, chain.blocks.reverse.take 255 = tip :: bs :=
  Block.take_reverse_eq_cons (by omega) h

theorem BlockChain.retained_length (chain : BlockChain) :
    chain.retained.length = min 255 chain.blocks.length := by
  unfold BlockChain.retained
  simp

/-- Below the retention bound nothing is dropped, so the oldest retained block
is the chain's own first block. -/
theorem BlockChain.retained_eq_blocks {chain : BlockChain}
    (h : chain.blocks.length ≤ 255) : chain.retained = chain.blocks := by
  unfold BlockChain.retained
  rw [List.take_of_length_le (by simpa using h)]
  simp

/-- The `BLOCKHASH` window theorem.

For a snapshot with valid retained history and a child block being executed at
`number = tip.number + 1`, every height the opcode admits --
`blockNumber < number ≤ blockNumber + 256` -- resolves to an authenticated
ancestry hash: either the true header keccak of a retained block at exactly
that height, or, one step below the oldest retained block, that block's own
`parentHash`. The second case is what makes the list reach 256 entries from
255 retained blocks; it is the only entry whose subject the snapshot no longer
carries, and it is authenticated by the retained header that names it.

Both truncated and early-chain windows are covered: with 255 blocks retained
the window's lower end is exactly the oldest retained block's parent, and
below the retention bound the chain still starts at block zero, so no admitted
height falls off the list and the index never truncates. -/
theorem getLast256BlockHashes_window {chain : BlockChain}
    (hv : chain.RetainedHistoryValid) {tip : Block}
    (htip : chain.blocks.getLast? = some tip) {number blockNumber : Nat}
    (hnum : number = tip.header.number + 1)
    (hlo : blockNumber < number) (hhi : number ≤ blockNumber + 256) :
    (∃ b ∈ chain.retained, b.header.number = blockNumber ∧
        (BlockChain.recentBlockHashes chain).getD
          ((BlockChain.recentBlockHashes chain).length - (number - blockNumber)) 0
            = b.header.hash) ∨
      (∃ oldest ∈ chain.retained.head?, blockNumber + 1 = oldest.header.number ∧
        (BlockChain.recentBlockHashes chain).getD
          ((BlockChain.recentBlockHashes chain).length - (number - blockNumber)) 0
            = oldest.header.parentHash) := by
  obtain ⟨bs, hN⟩ := BlockChain.take_reverse_eq_cons htip
  have hEq := getLast256BlockHashes_eq hN
  have hRdef : chain.retained = (tip :: bs).reverse := by
    unfold BlockChain.retained; rw [hN]
  have hm : chain.retained.length = bs.length + 1 := by rw [hRdef]; simp
  have h0 : 0 < chain.retained.length := by omega
  have hchain : chain.retained.IsChain Block.Links :=
    hv.1.suffix chain.retained_suffix
  have hlast? : chain.retained.getLast? = some tip := by
    rw [hRdef, List.getLast?_reverse]; rfl
  have hlast : chain.retained[chain.retained.length - 1] = tip := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast?
    exact Option.some.inj hlast?
  have htipnum : tip.header.number
      = chain.retained[0].header.number + (chain.retained.length - 1) := by
    have hnum0 :=
      Block.isChain_number hchain (i := chain.retained.length - 1) (by omega) h0
    rw [hlast] at hnum0
    exact hnum0
  have hhead : chain.retained.head? = some chain.retained[0] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
  have hlen1 : (BlockChain.recentBlockHashes chain).length = chain.retained.length + 1 := by
    rw [getLast256BlockHashes_eq hN]; simp
  -- Coverage: no admitted height falls below the oldest retained block's own
  -- parent. With a full window that is the arithmetic of 255 retained blocks;
  -- below it, the chain still starts at block zero.
  have hcov : chain.retained[0].header.number ≤ blockNumber + 1 := by
    rcases Nat.lt_or_ge chain.blocks.length 255 with hlen | hlen
    · have hret : chain.retained = chain.blocks :=
        chain.retained_eq_blocks (by omega)
      have hzero := hv.2.2.resolve_left (by omega) chain.retained[0]
        (by rw [← hret]; exact hhead)
      omega
    · have h255 : chain.retained.length = 255 := by
        rw [chain.retained_length]; omega
      omega
  rcases Nat.lt_or_ge blockNumber chain.retained[0].header.number with hc | hc
  · -- The truncated boundary: the entry is the oldest retained block's own
    -- authenticated `parentHash`, and it is the only such entry.
    right
    refine ⟨chain.retained[0], hhead, by omega, ?_⟩
    have hidx : (BlockChain.recentBlockHashes chain).length - (number - blockNumber) = 0 := by
      omega
    rw [hidx, getLast256BlockHashes_getD_lt hN h0]
  · -- A height the window still retains a block for.
    left
    obtain ⟨k, hk⟩ : ∃ k, blockNumber = chain.retained[0].header.number + k :=
      ⟨blockNumber - chain.retained[0].header.number, by omega⟩
    have hidx : (BlockChain.recentBlockHashes chain).length - (number - blockNumber)
        = k + 1 := by omega
    rcases Nat.lt_or_ge (k + 1) chain.retained.length with hlt | hge
    · refine ⟨chain.retained[k], List.getElem_mem (by omega), ?_, ?_⟩
      · have := Block.isChain_number hchain (i := k) (by omega) h0
        omega
      · rw [hidx, getLast256BlockHashes_getD_lt hN hlt,
          Block.isChain_parentHash hchain hlt]
    · have hkeq : k + 1 = chain.retained.length := by omega
      refine ⟨tip, hlast ▸ List.getElem_mem (by omega), by omega, ?_⟩
      rw [hidx, hkeq, getLast256BlockHashes_getD_last hN]

/-- The consumer form of the window theorem: whenever the requested height is
one the retained history still holds a block for, `BLOCKHASH` returns that
block's true header keccak -- never a stale, defaulted, or off-by-one entry. -/
theorem getLast256BlockHashes_of_mem_retained {chain : BlockChain}
    (hv : chain.RetainedHistoryValid) {tip b : Block}
    (htip : chain.blocks.getLast? = some tip) (hb : b ∈ chain.retained)
    {number : Nat} (hnum : number = tip.header.number + 1)
    (hlo : b.header.number < number) (hhi : number ≤ b.header.number + 256) :
    (BlockChain.recentBlockHashes chain).getD
      ((BlockChain.recentBlockHashes chain).length - (number - b.header.number)) 0
        = b.header.hash := by
  have hchain : chain.retained.IsChain Block.Links :=
    hv.1.suffix chain.retained_suffix
  rcases getLast256BlockHashes_window hv htip hnum hlo hhi with
    ⟨b', hb', hnum', hval⟩ | ⟨oldest, hold, hnum', _⟩
  · rw [hval, Block.isChain_number_inj hchain hb' hb hnum']
  · -- The boundary entry names a height *below* every retained block, so it
    -- cannot be the height of one.
    exfalso
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have h0 : 0 < chain.retained.length := by omega
    have hhead : chain.retained.head? = some chain.retained[0] := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
    rw [hhead, Option.mem_def, Option.some.injEq] at hold
    subst hold
    have := Block.isChain_number hchain hi h0
    omega

def stateTransitionOmmersCheck (ommers : List Header) :
    Except BlockValidationError Unit := do
  if ¬ommers.isEmpty then do
    .error <| .ommersOverParis <| .text
      s!"block body contains {ommers.length} ommer(s), \
         which is impossible after Paris"

/-- The hash a header's `ommersHash` commits to: the keccak of the RLP list
of the ommer headers. `emptyOmmerHash` is its value on the empty list. -/
def ommersListHash (ommers : List Header) : Hash32 :=
  (Rlp.Item.list (ommers.map Header.toRlpItem)).toBytes.keccak

private def ommersFail (msg : String) : Except TransitionError Unit :=
  .error <| .block <| .invalidOmmers <| .text msg

/-- Number and retained canonical parent checks precede ommer rule lookup.
The full header check below authenticates the parent's exact hash. -/
def ommerParent (chain : BlockChain) (header ommer : Header) :
    Except TransitionError Block := do
  if ommer.number < 1 ∨ ommer.number ≥ header.number then
    .error <| .block <| .invalidOmmers <| .text
      s!"ommer number = {ommer.number} is not between 1 and \
      block number = {header.number}"
  (chain.blocks.find? (·.header.number + 1 = ommer.number)).toExcept
    (TransitionError.block <| .invalidOmmers <| .text
      s!"ommer number = {ommer.number} has no retained parent")

/-- Validate an ommer against its retained parent, preserving the existing
ommer diagnostic and internal-error channels. A block-rejection reason of the
ommer's own header is returned as the cause of `invalidOmmerHeader`, not
rendered here (3.2). -/
def validateOmmerWithParent (rules : ForkRules) (chain : BlockChain)
    (ommer : Header) (parent : Block) : Except TransitionError Unit :=
  match validateHeader rules { chain with blocks := [parent] } ommer with
  | .ok () => .ok ()
  | .error (.block e) => .error <| .block <| .invalidOmmerHeader e
  | .error e => .error e

/-- Static ommer validation: the caller's explicit rules govern every header. -/
def validateOmmerHeader (rules : ForkRules) (chain : BlockChain)
    (header ommer : Header) : Except TransitionError Unit := do
  let parent ← ommerParent chain header ommer
  validateOmmerWithParent rules chain ommer parent

private def validateOmmerHeadersTyped {ε : Type}
    (check : Header → Except ε Unit) : List Header → Except ε Unit
  | [] => .ok ()
  | o :: os => do check o; validateOmmerHeadersTyped check os

/-- The containing block's list restrictions, after individual headers pass. -/
def validateOmmerList (chain : BlockChain) (header : Header)
    (ommers : List Header) : Except TransitionError Unit := do
  if ommers.length > 2 then
    ommersFail s!"block body contains {ommers.length} ommers, more than 2"
  let hashes := ommers.map Header.hash
  if hashes.eraseDups.length ≠ hashes.length then
    ommersFail "an ommer is listed twice"
  let recent := (chain.blocks.reverse.take (maxOmmerDepth + 1)).map (·.header)
  let recentHashes := recent.map Header.hash
  let recentOmmerHashes :=
    ((chain.blocks.reverse.take (maxOmmerDepth + 1)).flatMap (·.ommers)).map Header.hash
  let blockHash := header.hash
  for ommer in ommers do
    let ommerHash := ommer.hash
    if ommerHash = blockHash then
      ommersFail s!"ommer {ommerHash} is the block itself"
    if recentHashes.contains ommerHash then
      ommersFail s!"ommer {ommerHash} is a recent canonical block"
    if recentOmmerHashes.contains ommerHash then
      ommersFail s!"ommer {ommerHash} is already an ommer of a recent block"
    let age := header.number - ommer.number
    if age < 1 ∨ age > maxOmmerDepth then
      ommersFail s!"ommer {ommerHash} is {age} blocks old, \
        outside 1 to {maxOmmerDepth}"
    if ¬ recentHashes.contains ommer.parentHash then
      ommersFail s!"ommer {ommerHash} has a parent outside the recent canonical blocks"
    if ommer.parentHash = header.parentHash then
      ommersFail s!"ommer {ommerHash} is a sibling of the block"

/-- One ommer algorithm with a typed per-header resolver. Hash validation
precedes header lookup; list eligibility follows it. -/
def validateOmmersWith {ε : Type} (embed : TransitionError → ε)
    (check : Header → Except ε Unit) (chain : BlockChain) (header : Header)
    (ommers : List Header) : Except ε Unit := do
  if ommersListHash ommers ≠ header.ommersHash then
    Except.mapError embed <| ommersFail
      s!"ommers hash = {header.ommersHash} ≠ \
      hash of the ommer list = {ommersListHash ommers}"
  validateOmmerHeadersTyped check ommers
  Except.mapError embed (validateOmmerList chain header ommers)

/-- Static EELS-ordered ommer validation. Every header uses the explicit rules
while count, uniqueness, ancestry and age remain containing-block checks. -/
def validateOmmers (rules : ForkRules) (chain : BlockChain) (header : Header)
    (ommers : List Header) : Except TransitionError Unit :=
  validateOmmersWith id (validateOmmerHeader rules chain header) chain header ommers

/-- The block's ommers against its rules: after Paris the list must be empty
(`stateTransitionOmmersCheck`, unchanged); before it, `validateOmmers`. -/
def checkBlockOmmers (rules : ForkRules) (chain : BlockChain) (header : Header)
    (ommers : List Header) : Except TransitionError Unit :=
  match rules.proofOfWork with
  | none => Except.mapError TransitionError.block (stateTransitionOmmersCheck ommers)
  | some _ => validateOmmers rules chain header ommers

/-- Retention, measured: the 254 newest blocks kept, oldest-first, then the
new one. -/
theorem appendBlock_eq (blks : List Block) (blk : Block) :
    appendBlock blks blk = (blks.reverse.take 254).reverse ++ [blk] := by
  unfold appendBlock
  simp

theorem appendBlock_getLast? (blks : List Block) (blk : Block) :
    (appendBlock blks blk).getLast? = some blk := by
  rw [appendBlock_eq]
  simp

theorem appendBlock_ne_nil (blks : List Block) (blk : Block) :
    appendBlock blks blk ≠ [] := by
  rw [appendBlock_eq]
  simp

/-- Retained-history validity is preserved by an append that links to the tip.

This is the whole reason the checked transition never has to re-derive
ancestry: the child's `validateHeader` already established both halves of
`Block.Links` against the parent header, and the canonical envelope already
established the child header's wire well-formedness. -/
theorem BlockChain.retainedHistoryValid_appendBlock {chain chain' : BlockChain}
    {tip blk : Block}
    (hv : chain.RetainedHistoryValid) (htip : chain.blocks.getLast? = some tip)
    (hlink : Block.Links tip blk) (hwire : blk.header.WireWellFormed)
    (hb : chain'.blocks = appendBlock chain.blocks blk) :
    chain'.RetainedHistoryValid := by
  have hsuf : (chain.blocks.reverse.take 254).reverse <:+ chain.blocks :=
    Block.take_reverse_suffix _ _
  have hblocks : chain'.blocks = (chain.blocks.reverse.take 254).reverse ++ [blk] := by
    rw [hb, appendBlock_eq]
  obtain ⟨kept, hkept⟩ := Block.take_reverse_eq_cons (n := 254) (by omega) htip
  have hkeptlast : ((chain.blocks.reverse.take 254).reverse).getLast? = some tip := by
    rw [List.getLast?_reverse, hkept]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hblocks]
    refine (hv.1.suffix hsuf).append (List.IsChain.singleton _) ?_
    intro x hx y hy
    rw [hkeptlast, Option.mem_def, Option.some.injEq] at hx
    rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hx; subst hy
    exact hlink
  · rw [hblocks]
    intro b hb
    rcases List.mem_append.mp hb with h | h
    · exact hv.2.1 b (hsuf.subset h)
    · rw [List.mem_singleton.mp h]; exact hwire
  · -- Coverage: either the append filled the window, or the chain still
    -- begins where it began.
    rcases Nat.lt_or_ge chain.blocks.length 254 with hlen | hlen
    · right
      have hne : chain.blocks ≠ [] := by
        intro h; rw [h] at htip; simp at htip
      obtain ⟨x, xs, hcb⟩ : ∃ x xs, chain.blocks = x :: xs := by
        cases hc : chain.blocks with
        | nil => exact absurd hc hne
        | cons y ys => exact ⟨y, ys, rfl⟩
      have hall : (chain.blocks.reverse.take 254).reverse = chain.blocks := by
        rw [List.take_of_length_le (by simpa using Nat.le_of_lt hlen)]
        simp
      have hzero := hv.2.2.resolve_left (by omega)
      rw [hblocks, hall, hcb]
      intro b hb
      simp only [List.cons_append, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hb
      subst hb
      exact hzero _ (by rw [hcb]; rfl)
    · left
      rw [hblocks]
      simp only [List.length_append, List.length_reverse, List.length_take,
        List.length_cons, List.length_nil]
      omega

theorem transition_mapError_id {α : Type} (r : Except TransitionError α) :
    r.mapError id = r := by
  cases r <;> rfl

theorem transition_mapError_bind {ε ε' α β : Type}
    (g : ε → ε') (r : Except ε α) (k : α → Except ε β) :
    (r.bind k).mapError g = (r.mapError g).bind (fun a => (k a).mapError g) := by
  cases r <;> rfl

theorem transition_mapError_comp {ε ε' ε'' α : Type}
    (g : ε → ε') (g' : ε' → ε'') (r : Except ε α) :
    (r.mapError g).mapError g' = r.mapError (g' ∘ g) := by
  cases r <;> rfl

private theorem validateOmmerHeadersTyped_mapError {ε : Type}
    (embed : TransitionError → ε) (check : Header → Except TransitionError Unit)
    (ommers : List Header) :
    validateOmmerHeadersTyped (fun o => (check o).mapError embed) ommers =
      (validateOmmerHeadersTyped check ommers).mapError embed := by
  induction ommers with
  | nil => rfl
  | cons o os ih =>
    simp only [validateOmmerHeadersTyped, bind, transition_mapError_bind, ih]

private theorem validateOmmersWith_mapError {ε : Type}
    (embed : TransitionError → ε) (check : Header → Except TransitionError Unit)
    (chain : BlockChain) (header : Header) (ommers : List Header) :
    validateOmmersWith embed (fun o => (check o).mapError embed) chain header ommers =
      (validateOmmersWith id check chain header ommers).mapError embed := by
  unfold validateOmmersWith
  split <;> simp only [bind, transition_mapError_bind, transition_mapError_id,
    validateOmmerHeadersTyped_mapError]

/-- The static transition uses one explicitly named fork for both the block
and every ommer. It does not consult an activation schedule. -/
def stateTransitionTyped (f : Fork) (ch : BlockChain) (block : Block) :
  Except TransitionError BlockChain :=
  stateTransitionCoreTyped id f ch block
    (fun _ => checkBlockOmmers f.ruleSet ch block.header block.ommers)

/-- Scheduled ommer validation uses the ommer's own number and timestamp,
then validates against its actual retained parent. Lookup failures and candidate
failures remain distinct constructors. -/
def validateOmmerHeaderScheduledTyped (cfg : ChainConfig) (chain : BlockChain)
    (header ommer : Header) : Except (RulesLookupError ⊕ TransitionError) Unit := do
  let parent ← (ommerParent chain header ommer).mapError Sum.inr
  let f ← (cfg.forkAt ommer.number ommer.timestamp).mapError Sum.inl
  if f.ruleSet.proofOfWork.isNone then
    .error <| .inr <| .block <| .invalidOmmers <| .text
      "ommer's own scheduled fork does not permit proof of work"
  (validateOmmerWithParent f.ruleSet chain ommer parent).mapError Sum.inr

/-- Containing rules still decide whether ommers are allowed at all; after
Paris no resolver is consulted. The list's other restrictions are shared. -/
def checkBlockOmmersScheduledTyped (cfg : ChainConfig) (rules : ForkRules)
    (chain : BlockChain) (header : Header) (ommers : List Header) :
    Except (RulesLookupError ⊕ TransitionError) Unit :=
  match rules.proofOfWork with
  | none => (stateTransitionOmmersCheck ommers).mapError (Sum.inr ∘ TransitionError.block)
  | some _ => validateOmmersWith Sum.inr
      (validateOmmerHeaderScheduledTyped cfg chain header) chain header ommers

private def splitScheduled {α : Type} :
    Except (RulesLookupError ⊕ TransitionError) α →
      Except RulesLookupError (Except TransitionError α)
  | .error (.inl e) => .error e
  | .error (.inr e) => .ok (.error e)
  | .ok a => .ok (.ok a)

/-- A configured transition after the containing fork has been selected. Chain
identity and containing-fork lookup belong to the caller; every ommer lookup
stays on the outer typed channel. -/
def stateTransitionScheduledTyped (cfg : ChainConfig) (f : Fork)
    (ch : BlockChain) (block : Block) :
    Except RulesLookupError (Except TransitionError BlockChain) :=
  splitScheduled <| stateTransitionCoreTyped Sum.inr f ch block
    (fun _ => checkBlockOmmersScheduledTyped cfg f.ruleSet ch block.header block.ommers)

private theorem validateOmmerHeaderScheduledTyped_single (chainId : UInt64) (f : Fork)
    (chain : BlockChain) (header ommer : Header) (hp : f.ruleSet.proofOfWork.isNone = false) :
    validateOmmerHeaderScheduledTyped (ChainConfig.single chainId f) chain header ommer =
      (validateOmmerHeader f.ruleSet chain header ommer).mapError Sum.inr := by
  simp only [validateOmmerHeaderScheduledTyped, validateOmmerHeader, bind,
    ChainConfig.single_forkAt, Except.mapError, Except.bind,
    hp, Bool.false_eq_true, ↓reduceIte]
  cases ommerParent chain header ommer <;> rfl

private theorem checkBlockOmmersScheduledTyped_single (chainId : UInt64) (f : Fork)
    (chain : BlockChain) (header : Header) (ommers : List Header) :
    checkBlockOmmersScheduledTyped (ChainConfig.single chainId f) f.ruleSet chain header ommers =
      (checkBlockOmmers f.ruleSet chain header ommers).mapError Sum.inr := by
  unfold checkBlockOmmersScheduledTyped checkBlockOmmers
  cases hp : f.ruleSet.proofOfWork with
  | none => simp only [transition_mapError_comp]
  | some p =>
    simp only [validateOmmers]
    have hh : validateOmmerHeaderScheduledTyped (ChainConfig.single chainId f) chain header =
        (fun o => (validateOmmerHeader f.ruleSet chain header o).mapError Sum.inr) := by
      funext o
      exact validateOmmerHeaderScheduledTyped_single chainId f chain header o (by simp [hp])
    rw [hh, validateOmmersWith_mapError]

/-- All results, including every transition error, agree with the static core
under a constant schedule. No ommer lookup can fail on that schedule. -/
theorem stateTransitionScheduledTyped_single (chainId : UInt64) (f : Fork)
    (ch : BlockChain) (block : Block) :
    stateTransitionScheduledTyped (ChainConfig.single chainId f) f ch block =
      .ok (stateTransitionTyped f ch block) := by
  unfold stateTransitionScheduledTyped stateTransitionTyped
  simp only [checkBlockOmmersScheduledTyped_single]
  rw [stateTransitionCoreTyped_mapError]
  cases stateTransitionCoreTyped id f ch block
    (fun _ => checkBlockOmmers f.ruleSet ch block.header block.ommers) <;> rfl

/-- With no proof-of-work ommers, configured and static cores agree on all
results for any schedule: the containing list prohibition runs first. -/
theorem stateTransitionScheduledTyped_of_pow_none (cfg : ChainConfig) (f : Fork)
    (ch : BlockChain) (block : Block) (hp : f.ruleSet.proofOfWork = none) :
    stateTransitionScheduledTyped cfg f ch block = .ok (stateTransitionTyped f ch block) := by
  unfold stateTransitionScheduledTyped stateTransitionTyped
  have ho : checkBlockOmmersScheduledTyped cfg f.ruleSet ch block.header block.ommers =
      (checkBlockOmmers f.ruleSet ch block.header block.ommers).mapError Sum.inr := by
    simp only [checkBlockOmmersScheduledTyped, checkBlockOmmers, hp, transition_mapError_comp]
  simp only [ho]
  rw [stateTransitionCoreTyped_mapError]
  cases stateTransitionCoreTyped id f ch block
    (fun _ => checkBlockOmmers f.ruleSet ch block.header block.ommers) <;> rfl

theorem stateTransitionScheduledTyped_eq_ok_iff {cfg : ChainConfig} {f : Fork}
    {ch ch' : BlockChain} {block : Block} :
    stateTransitionScheduledTyped cfg f ch block = .ok (.ok ch') ↔
      stateTransitionCoreTyped Sum.inr f ch block
        (fun _ => checkBlockOmmersScheduledTyped cfg f.ruleSet ch block.header block.ommers)
        = .ok ch' := by
  unfold stateTransitionScheduledTyped
  cases stateTransitionCoreTyped Sum.inr f ch block
      (fun _ => checkBlockOmmersScheduledTyped cfg f.ruleSet ch block.header block.ommers) with
  | error e => cases e <;> simp [splitScheduled]
  | ok a => simp [splitScheduled]

/-- Legacy renderer adapter over `stateTransitionE`, byte-identical on every
input, and the entry point for static fixture suites, which state their fork
rather than deriving it.

Named `stateTransitionWith` and taking a `ForkRules` until goal
`jaune-forks-by-construction-v1`. Once a machine carries a `Fork`, the
rules-taking adapter and this one had the same domain, so the duplicate layer
was retired into this name rather than kept as a synonym; there is no longer a
rules-taking entry point that could be handed a record no fork realises. The
`UnsupportedForkError` vocabulary remains where `Fork.rules` renders an
absent record. Earlier historical waves used that route for pre-Berlin
forks; this candidate resolves their records too. -/
def stateTransitionAt (f : Fork) (ch : BlockChain) (block : Block) :
  Except String BlockChain :=
  (stateTransitionTyped f ch block).mapError TransitionError.render

/-- The adapter adds rendering and nothing else. -/
theorem stateTransitionAt_eq_ok_iff {f : Fork} {ch ch' : BlockChain}
    {block : Block} :
    stateTransitionAt f ch block = .ok ch'
      ↔ stateTransitionTyped f ch block = .ok ch' :=
  Except.mapError_eq_ok_iff

/-- Whether a configuration's declared chain identity agrees with a snapshot's.

P0.1: a configuration can be a perfectly valid, perfectly usable schedule and
still name a different chain than the snapshot it is handed. This is separate
from `ChainConfig.validate`, which never inspects `chainId` at all, and it is
the outer context channel, not a verdict about any candidate block -- a
contradictory caller context is not evidence that a block is invalid.
Declared here, downstream of `Jaune/Fork.lean`, because this is the first
module where `BlockChain` exists alongside `ChainConfig` (design report §6).
Neither configured entry point below may proceed past a mismatch: this check
runs first in both, and it never repairs a mismatch by preferring one side. -/
def ChainConfig.checkChainId (cfg : ChainConfig) (chain : BlockChain) :
    Except ChainContextError Unit :=
  if cfg.chainId = chain.chainId then
    .ok ()
  else
    .error (.chainIdMismatch cfg.chainId chain.chainId)

/-- The block state transition on a configured chain, deriving the active fork
from the block's number and timestamp and the chain's activation schedule.

Checks the configuration against the snapshot's chain identity before doing
anything else -- P0.1's fix -- then proceeds exactly as before. -/
def stateTransitionUsing (cfg : ChainConfig) (ch : BlockChain) (block : Block) :
    Except String BlockChain := do
  Except.mapError ChainContextError.render (cfg.checkChainId ch)
  let f ← Except.mapError RulesLookupError.render
    (cfg.forkAt block.header.number block.header.timestamp)
  match stateTransitionScheduledTyped cfg f ch block with
  | .error e => .error e.render
  | .ok r => r.mapError TransitionError.render

theorem stateTransitionUsing_run {cfg : ChainConfig} {ch ch' : BlockChain}
    {block : Block} (h : stateTransitionUsing cfg ch block = .ok ch') :
    ∃ f, cfg.forkAt block.header.number block.header.timestamp = .ok f ∧
      stateTransitionScheduledTyped cfg f ch block = .ok (.ok ch') := by
  unfold stateTransitionUsing at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨f, hf, h⟩ := Except.bind_eq_ok h
  refine ⟨f, Except.mapError_eq_ok_iff.mp hf, ?_⟩
  cases hs : stateTransitionScheduledTyped cfg f ch block with
  | error e => rw [hs] at h; cases h
  | ok r =>
    rw [hs] at h
    have hr : r = .ok ch' := Except.mapError_eq_ok_iff.mp h
    rw [hr]

/-- The Prague state transition.

Retained with its original name, type, and behaviour. Prague is permanent
supported protocol, not scaffolding, and downstream proofs state their results
about this name. -/
def stateTransition (ch : BlockChain) (block : Block) :
  Except String BlockChain :=
  stateTransitionAt .prague ch block

def Rlp.Item.toExceptWithdrawal : Rlp.Item → Except DecodeError Withdrawal
  | .list [
      .bytes globalIndex,
      .bytes validatorIndex,
      .bytes recipient,
      .bytes amount
    ] => do
    -- Check every untrusted field before constructing the withdrawal. In
    -- particular, `Bytes.toUInt64` truncates modulo 2^64, so it may only see the
    -- byte string returned by the at-most-eight-byte decoder.
    let globalIndex ← globalIndex.toRlpUInt64 "withdrawal globalIndex"
    let validatorIndex ← validatorIndex.toRlpUInt64 "withdrawal validatorIndex"
    let recipient ← recipient.toRlpAddress "withdrawal recipient"
    -- EIP-4895: `amount` is a 64-bit Gwei scalar on the wire, even though the
    -- `Withdrawal` field stores it as 256 bits for balance arithmetic.
    let amount ← amount.toRlpUInt64 "withdrawal amount"
    .ok {
      index := globalIndex,
      validatorIndex := validatorIndex,
      address := recipient,
      amount := amount.toNat.toU256
    }
  | _ =>
    .error <| DecodeError.structure "withdrawal"
      "expected a list of four byte-string fields"

/-- Strict withdrawal-decoder soundness: the amount a decoded withdrawal
carries always fits its 64-bit wire type, even though the field is 256 bits
wide. -/
theorem Rlp.Item.toExceptWithdrawal_wireWellFormed {blt : Rlp.Item} {w : Withdrawal}
    (h : blt.toExceptWithdrawal = .ok w) : w.WireWellFormed := by
  unfold Rlp.Item.toExceptWithdrawal at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    exact UInt64.toNat_toU256_high _
  · exact absurd h (by simp)

/-- Strict legacy-transaction-decoder soundness. A *list*-shaped transaction
item is the legacy route, so what it yields is both wire-well-formed and of
legacy type -- which is exactly `TxEntry.WireWellFormed` on the decoded side of
a block body's transaction slot. The typed route never reaches this decoder,
and never produces a `.zero` transaction. -/
theorem Rlp.Item.toExceptLegacyTransaction_wireWellFormed {bs : List Rlp.Item} {tx : Transaction}
    (h : Rlp.Item.toExceptLegacyTransaction bs = .ok tx) :
    Transaction.WireWellFormed tx ∧ tx.type.isLegacy = true := by
  unfold Rlp.Item.toExceptLegacyTransaction at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩ <;>
      first
        | exact Bytes.toRlpNat_lt_two_pow_256 (by assumption)
        | exact Bytes.toRlpU256_eq_ok (by assumption)
  · exact absurd h (by simp)

def Rlp.Item.toExceptBlock : Rlp.Item → Except DecodeError Block
  | Rlp.Item.list [
      HeaderBLT,
      .list TxBLTs,
      .list OmmerBLTs,
      .list WithdrawalBLTs
    ] => do
    let header ← HeaderBLT.toExceptHeader
    let aux : Rlp.Item → Except DecodeError (Bytes ⊕ Transaction)
      | .list ls => Rlp.Item.toExceptLegacyTransaction ls <&> .inr
      | .bytes xs => .ok <| .inl xs
    let txs ← List.mapM aux TxBLTs
    let ommers ← List.mapM Rlp.Item.toExceptHeader OmmerBLTs
    let withdrawals ← List.mapM Rlp.Item.toExceptWithdrawal WithdrawalBLTs
    .ok {
      header := header,
      transactions := txs,
      ommers := ommers,
      withdrawals := withdrawals
    }
  | .list [_, .list _, .list _] =>
    .error <| .withdrawalsNotRead <|
      .text "post-Shanghai block body omits the withdrawals list"
  | _ =>
    .error <| DecodeError.structure "block"
      "expected [header, transactions, ommers, withdrawals] lists"

/-- Strict block-decoder soundness: a decoded block is structurally canonical
componentwise. Note what this deliberately does *not* say about a byte-string
transaction slot -- it stays opaque here, and is decoded at the existing point
inside `applyBody`, so the staged typed-transaction rule (design report §7) is
preserved and no error precedence moves. -/
theorem Rlp.Item.toExceptBlock_rlpCanonical {blt : Rlp.Item} {b : Block}
    (h : blt.toExceptBlock = .ok b) : b.RlpCanonical := by
  unfold Rlp.Item.toExceptBlock at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨Rlp.Item.toExceptHeader_wireWellFormed (by assumption), ?_, ?_, ?_⟩
    · intro o ho
      obtain ⟨blt', hblt'⟩ := List.mapM_except_eq_ok_mem (by assumption) o ho
      exact Rlp.Item.toExceptHeader_wireWellFormed hblt'
    · intro w hw
      obtain ⟨blt', hblt'⟩ := List.mapM_except_eq_ok_mem (by assumption) w hw
      exact Rlp.Item.toExceptWithdrawal_wireWellFormed hblt'
    · intro e he
      obtain ⟨blt', hblt'⟩ := List.mapM_except_eq_ok_mem (by assumption) e he
      cases blt' with
      | bytes ys =>
        simp only [Except.ok.injEq] at hblt'
        subst hblt'
        trivial
      | list ls =>
        obtain ⟨tx, htx, he'⟩ := Except.bind_eq_ok hblt'
        simp only [Except.ok.injEq] at he'
        subst he'
        exact Rlp.Item.toExceptLegacyTransaction_wireWellFormed htx
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-
rlpToBlock is equivalent to json_to_block from execution-specs.
why does it accept the RLP bytes as input, and not the whole JSON?
the justification is that json_to_block expects the RLP bytes to be
always available, and always uses *only* the RLP bytes to obtain the
block, ignoring everything else in the JSON (the code path that deals
with nonexistent RLP bytes exists, but is unreachable). its return
type also omits the RLP bytes, since this is identical to the input.
-/
def rlpToBlockTyped (rlp : Bytes) : Except DecodeError (Block × Hash32) := do
  let block_blt ← (Bytes.toRlpItem? rlp).toExcept <|
    DecodeError.structure "block RLP" "cannot decode the outer RLP item"
  let block ← block_blt.toExceptBlock
  let canonicalRlp := block.toRlpItem.toBytes
  if rlp ≠ canonicalRlp then
    .error <| .roundTrip <|
      .text "decoded block does not re-encode byte-for-byte"
  .ok ⟨block, (Header.toRlpItem block.header).toBytes.keccak⟩

/-- Legacy renderer adapter over `rlpToBlockE`, byte-identical on every input.
Retained by name and type because Blanc's protected
`addBlockToChain_preserves_solvent` quantifies over exactly this equation, and
the canonical envelope's evidence field is stated with it. -/
def rlpToBlock (rlp : Bytes) : Except String (Block × U256) :=
  (rlpToBlockTyped rlp).mapError DecodeError.render

/-- The adapter adds rendering and nothing else: success is the typed core's
success. This is the bridge every string-level client inverts through. -/
theorem rlpToBlock_eq_ok_iff {rlp : Bytes} {p : Block × Hash32} :
    rlpToBlock rlp = .ok p ↔ rlpToBlockTyped rlp = .ok p :=
  Except.mapError_eq_ok_iff

---------------- FORK-RELATIVE WIRE DECODER ---------------

/-- The fork-relative wire encoding of a block body: the withdrawals element
rides along from Shanghai, so a pre-Shanghai body encodes three elements, not
four. `Block.toBLT` stays the canonical four-element encoding the proven
paths hash and compare through; this is the shape the fork's own fixtures
carry. Under Shanghai rules and later it is `Block.toBLT`, definitionally. -/
def Block.toRlpItemAt (rules : ForkRules) (b : Block) : Rlp.Item :=
  if rules.header.withdrawalsRoot then b.toRlpItem
  else .list [Header.toRlpItem b.header, .list (b.transactions.map BytesOrTransactionToRlpItem),
    .list (b.ommers.map Header.toRlpItem)]

/-- The fork-relative strict body decoder: a three-element body decodes with
no withdrawals exactly when the rules do not carry them, and is the
`withdrawalsNotRead` error `BLT.toExBlock` reports when they do. A
four-element body decodes through `BLT.toExBlock` under every fork, so the
post-Shanghai shape and every error it reports are shared, not duplicated. -/
def Rlp.Item.toExceptBlockAt (rules : ForkRules) : Rlp.Item → Except DecodeError Block
  | .list [HeaderBLT, .list TxBLTs, .list OmmerBLTs] =>
    if rules.header.withdrawalsRoot then
      .error (.withdrawalsNotRead (.text
        "post-Shanghai block body omits the withdrawals list"))
    else Rlp.Item.toExceptBlock
      (.list [HeaderBLT, .list TxBLTs, .list OmmerBLTs, .list []])
  | blt => blt.toExceptBlock

/-- The fork-relative strict block decoder: `rlpToBlockE` on the fork's own
wire shape. The round trip compares against the fork-relative encoding, so a
pre-Shanghai three-element body re-encodes to itself; under Shanghai rules
and later the comparison -- and every success and failure -- is
`rlpToBlockE`'s. `rlpToBlockE` itself is untouched: the proven envelope keeps
its equation. -/
def rlpToBlockTypedAt (rules : ForkRules) (rlp : Bytes) :
    Except DecodeError (Block × Hash32) := do
  let block_blt ← (Bytes.toRlpItem? rlp).toExcept <|
    DecodeError.structure "block RLP" "cannot decode the outer RLP item"
  let block ← block_blt.toExceptBlockAt rules
  let canonicalRlp := (block.toRlpItemAt rules).toBytes
  if rlp ≠ canonicalRlp then
    .error <| .roundTrip <|
      .text "decoded block does not re-encode byte-for-byte"
  .ok ⟨block, (Header.toRlpItem block.header).toBytes.keccak⟩

--------------- THE CANONICAL OUTER-BLOCK ENVELOPE ---------------

/-- The hash `rlpToBlock` returns is always the keccak of the decoded header's
canonical encoding. It is therefore *derivable* from the decoded block and was
never independent evidence, which is why the import core below takes an
envelope instead of a separate hash argument. -/
theorem rlpToBlock_headerHash {raw : Bytes} {block : Block} {hash : Hash32}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) :
    hash = (Header.toRlpItem block.header).toBytes.keccak := by
  rw [rlpToBlock_eq_ok_iff] at h
  unfold rlpToBlockTyped at h
  repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, herr, _⟩ := Except.bind_eq_ok h
    exact absurd herr (by simp)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- A successful strict decode proves the decoded block re-encodes to exactly
the bytes supplied -- P0.3's first acceptance criterion. -/
theorem rlpToBlock_canonical {raw : Bytes} {block : Block} {hash : Hash32}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) : block.toRlpItem.toBytes = raw := by
  rw [rlpToBlock_eq_ok_iff] at h
  unfold rlpToBlockTyped at h
  repeat obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, herr, _⟩ := Except.bind_eq_ok h
    exact absurd herr (by simp)
  · rename_i hne
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact (not_not.mp hne).symm

/-- A successful strict decode is structurally sound. -/
theorem rlpToBlock_rlpCanonical {raw : Bytes} {block : Block} {hash : Hash32}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) : block.RlpCanonical := by
  rw [rlpToBlock_eq_ok_iff] at h
  unfold rlpToBlockTyped at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨b, hb, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, herr, _⟩ := Except.bind_eq_ok h
    exact absurd herr (by simp)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact Rlp.Item.toExceptBlock_rlpCanonical hb

/-- A canonical outer block: the bytes a peer supplied, the block the strict
decoder produced from them, and the two pieces of evidence that make the pair
trustworthy -- that the block *is* the strict decoder's image of those bytes,
and that it re-encodes to them byte for byte.

The constructor is private. The only ways to obtain one are the strict decoder
(`CanonicalBlock.ofRlp?`) and the evidence-taking smart constructor
(`CanonicalBlock.ofDecode`), which demands the decoder equation itself, so a
caller cannot fabricate the evidence fields. Eliminators are exported:
`raw`, `block`, `headerHash`, `rawSize`, and the theorems below.

`raw` is retained rather than reconstructed because EIP-7934 depends on the
*supplied* size; re-encoding is evidence of canonicality, never a substitute
for the size observation (fixed decision 4). -/
structure CanonicalBlock : Type where
  private mk ::
  /-- The original RLP bytes. -/
  raw : Bytes
  /-- The block the strict decoder produced from `raw`. -/
  block : Block
  /-- Strict-decoder-image evidence. -/
  decoded :
    rlpToBlock raw = .ok ⟨block, (Header.toRlpItem block.header).toBytes.keccak⟩
  /-- Exact re-encoding evidence. -/
  canonical : block.toRlpItem.toBytes = raw

/-- The checked smart constructor: an envelope may only be built from the
strict decoder's own equation. -/
def CanonicalBlock.ofDecode {raw : Bytes} {block : Block} {hash : Hash32}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) : CanonicalBlock :=
  { raw := raw
    block := block
    decoded := by rw [rlpToBlock_headerHash h] at h; exact h
    canonical := rlpToBlock_canonical h }

/-- Strict decode of untrusted bytes into the envelope. The diagnostic on the
failure side is exactly the one `rlpToBlock` produces; this constructor adds no
second decoder and no second vocabulary. -/
def CanonicalBlock.ofRlp? (raw : Bytes) : Option CanonicalBlock :=
  match h : rlpToBlock raw with
  | .ok ⟨_, _⟩ => some (CanonicalBlock.ofDecode h)
  | .error _ => none

/-- The block header hash, *derived* from the envelope. -/
def CanonicalBlock.headerHash (cb : CanonicalBlock) : Hash32 :=
  (Header.toRlpItem cb.block.header).toBytes.keccak

/-- The authoritative original RLP size, the one EIP-7934 observes. -/
def CanonicalBlock.rawSize (cb : CanonicalBlock) : Nat := cb.raw.length

/-- Envelope inversion for downstream proofs: an envelope is exactly a
successful `rlpToBlock`. Stated so a client never has to unfold the structure
or the decoder. -/
theorem CanonicalBlock.rlpToBlock_eq (cb : CanonicalBlock) :
    rlpToBlock cb.raw = .ok ⟨cb.block, cb.headerHash⟩ := cb.decoded

/-- Structural soundness of the envelope. -/
theorem CanonicalBlock.rlpCanonical (cb : CanonicalBlock) :
    cb.block.RlpCanonical :=
  rlpToBlock_rlpCanonical cb.decoded

/-- The envelope's re-encoding, as an eliminator. -/
theorem CanonicalBlock.toBytes_eq (cb : CanonicalBlock) :
    cb.block.toRlpItem.toBytes = cb.raw := cb.canonical

theorem CanonicalBlock.rawSize_eq (cb : CanonicalBlock) :
    cb.rawSize = cb.raw.length := rfl

/-- Introduction: strict decode succeeds exactly when an envelope exists, and
the envelope it yields carries those very bytes and that very block. -/
theorem CanonicalBlock.ofRlp?_eq_some {raw : Bytes} {block : Block} {hash : Hash32}
    (h : rlpToBlock raw = .ok ⟨block, hash⟩) :
    ∃ cb : CanonicalBlock,
      CanonicalBlock.ofRlp? raw = some cb ∧ cb.raw = raw ∧ cb.block = block := by
  unfold CanonicalBlock.ofRlp?
  split
  · rename_i f s hb
    rw [h] at hb
    simp only [Except.ok.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨_, rfl, rfl, rfl⟩
  · rename_i err herr
    rw [h] at herr
    exact absurd herr (by simp)

theorem CanonicalBlock.ofRlp?_eq_none {raw : Bytes} {err : String}
    (h : rlpToBlock raw = .error err) : CanonicalBlock.ofRlp? raw = none := by
  unfold CanonicalBlock.ofRlp?
  split
  · rename_i b hb
    rw [h] at hb
    exact absurd hb (by simp)
  · rfl

--------------- CHECKED SEMANTIC CONSTRUCTORS ---------------

-- The open `Header`/`Tx`/`Withdrawal`/`Block` records stay exactly as they
-- are, for proofs and for negative construction. What follows is the *checked*
-- ingress beside them: one wrapper per record, each with a private
-- constructor and a decidable admission test, so a hand-built value is
-- certified against the very predicate the strict decoder establishes -- never
-- trimmed, normalised, or defaulted into shape (fixed decision 1).

/-- A header certified wire-well-formed. -/
structure CheckedHeader : Type where
  private mk ::
  val : Header
  wireWellFormed : val.WireWellFormed

/-- Certify a hand-built header, or refuse it. -/
def CheckedHeader.ofHeader? (h : Header) : Option CheckedHeader :=
  if hw : h.WireWellFormed then some ⟨h, hw⟩ else none

/-- Certification from the strict decoder, with no second test. -/
def CheckedHeader.ofDecode {blt : Rlp.Item} {h : Header}
    (hd : blt.toExceptHeader = .ok h) : CheckedHeader :=
  ⟨h, Rlp.Item.toExceptHeader_wireWellFormed hd⟩

/-- A withdrawal certified wire-well-formed. -/
structure CheckedWithdrawal : Type where
  private mk ::
  val : Withdrawal
  wireWellFormed : val.WireWellFormed

def CheckedWithdrawal.ofWithdrawal? (w : Withdrawal) : Option CheckedWithdrawal :=
  if hw : w.WireWellFormed then some ⟨w, hw⟩ else none

def CheckedWithdrawal.ofDecode {blt : Rlp.Item} {w : Withdrawal}
    (hd : blt.toExceptWithdrawal = .ok w) : CheckedWithdrawal :=
  ⟨w, Rlp.Item.toExceptWithdrawal_wireWellFormed hd⟩

/-- A certified block-body transaction slot.

Its decoded side carries a wire-well-formed *legacy* transaction; its opaque
side carries typed envelope bytes, which stay undecoded until the existing
decode point inside `applyBody`, so no error precedence moves. There is no
third shape: a decoded *typed* transaction can never be a slot, because a
typed transaction's canonical block encoding is its envelope byte followed by
its payload rather than the legacy list. Admitting one is precisely the
`.inr Tx` trust bypass P0.3 removes; `Tx.toTypedEnvelope?` is the way a
hand-built typed transaction becomes a slot. -/
structure BlockTransactionSlot : Type where
  private mk ::
  entry : Bytes ⊕ Transaction
  wellFormed : TransactionEntry.WireWellFormed entry

/-- The opaque typed slot. Nothing is decoded here. -/
def BlockTransactionSlot.ofTypedBytes (bs : Bytes) : BlockTransactionSlot := ⟨.inl bs, trivial⟩

/-- The decoded legacy slot, from the strict decoder's own equation. -/
def BlockTransactionSlot.ofLegacyDecode {ls : List Rlp.Item} {tx : Transaction}
    (h : Rlp.Item.toExceptLegacyTransaction ls = .ok tx) : BlockTransactionSlot :=
  ⟨.inr tx, Rlp.Item.toExceptLegacyTransaction_wireWellFormed h⟩

/-- The raw compatibility constructor: it carries no evidence, so it validates
once, here, rather than leaving a slot to be trusted later. -/
def BlockTransactionSlot.ofEntry? (e : Bytes ⊕ Transaction) : Option BlockTransactionSlot :=
  if h : TransactionEntry.WireWellFormed e then some ⟨e, h⟩ else none

/-- The envelope byte a typed transaction is carried under; `none` for legacy,
which has no envelope. -/
def TransactionType.envelopeByte : TransactionType → Option UInt8
  | .legacy _ _ => none
  | .eip2930 _ _ _ _ => some 0x01
  | .eip1559 _ _ _ _ _ => some 0x02
  | .eip4844 _ _ _ _ _ _ _ => some 0x03
  | .eip7702 _ _ _ _ _ _ => some 0x04

/-- A hand-built typed transaction's route into a block body: its envelope
byte followed by its payload. Placing the same record directly as a decoded
slot would re-encode it through the legacy list, corrupting both the
transactions trie and the signing hash -- which is why that route does not
exist. Legacy transactions have no envelope and are refused here; they enter
as decoded slots through `TxEnvelope.ofEntry?`. -/
def Transaction.toTypedEnvelope? (tx : Transaction) : Option BlockTransactionSlot :=
  tx.type.envelopeByte.map fun b => BlockTransactionSlot.ofTypedBytes (b :: tx.toRlpItem.toBytes)

/-- A block certified structurally canonical componentwise. -/
structure CheckedBlock : Type where
  private mk ::
  val : Block
  rlpCanonical : val.RlpCanonical

def CheckedBlock.ofBlock? (b : Block) : Option CheckedBlock :=
  if h : b.RlpCanonical then some ⟨b, h⟩ else none

/-- Assemble a block from already-certified parts. No admission test is needed
because every part carries its own. -/
def CheckedBlock.ofParts (header : CheckedHeader) (txs : List BlockTransactionSlot)
    (ommers : List CheckedHeader) (wds : List CheckedWithdrawal) : CheckedBlock :=
  { val :=
      { header := header.val
        transactions := txs.map BlockTransactionSlot.entry
        ommers := ommers.map CheckedHeader.val
        withdrawals := wds.map CheckedWithdrawal.val }
    rlpCanonical := by
      refine ⟨header.wireWellFormed, ?_, ?_, ?_⟩
      · intro o ho
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp ho
        exact c.wireWellFormed
      · intro w hw
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hw
        exact c.wireWellFormed
      · intro e he
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp he
        exact c.wellFormed }

/-- Every canonical outer block is a checked block. -/
def CanonicalBlock.toChecked (cb : CanonicalBlock) : CheckedBlock :=
  ⟨cb.block, cb.rlpCanonical⟩

theorem CanonicalBlock.toChecked_val (cb : CanonicalBlock) :
    cb.toChecked.val = cb.block := rfl

/-- P0.3's trust bypass, discharged rather than relocated.

`decodeTx rules (.inr tx) = .ok tx` still holds -- revalidating a
decoder-produced legacy transaction late in `applyBody` is exactly what the
plan forbids -- but
on the checked path it is no longer an *assumption*. Every decoded slot of a
canonical outer block is a wire-well-formed legacy transaction, so what
`decodeTx` returns there is certified, and the ingress side can no longer be
handed an uncertified `.inr Tx` at all. -/
theorem CanonicalBlock.decodeTransaction_inr {cb : CanonicalBlock} {tx : Transaction}
    (rules : ForkRules)
    (h : Sum.inr tx ∈ cb.block.transactions) :
    decodeTransaction rules (.inr tx) = .ok tx ∧
      Transaction.WireWellFormed tx ∧ tx.type.isLegacy = true :=
  ⟨rfl, cb.rlpCanonical.2.2.2 _ h⟩

--------------- THE CHECKED CHAIN SNAPSHOT ---------------

-- P0.2. A `BlockChain` is a freely constructible triple, so nothing stops a
-- caller pairing a real tip with an unrelated world. The tip header's
-- `stateRoot` is the authenticated identity of the prestate every child
-- executes from, and `initBlockEnvironment` reads `chain.state` directly, so without that
-- link "the state transition from this chain tip" is not a statement about
-- anything. What follows is the checked snapshot the expensive checks are
-- paid for once, and the proof-carrying constructors that carry the witness
-- forward instead of recomputing it (fixed decision 2).

/-- The snapshot's world commits to its own tip header. -/
def BlockChain.TipStateAgrees (chain : BlockChain) : Prop :=
  ∀ tip ∈ chain.blocks.getLast?, chain.state.root = tip.header.stateRoot

instance (chain : BlockChain) : Decidable chain.TipStateAgrees := by
  unfold BlockChain.TipStateAgrees; infer_instance

/-- Everything an executable snapshot must satisfy, in the order the checker
tests it (design report §5): nonempty history, canonical execution state,
valid retained ancestry, and only then the tip/root comparison that costs a
trie root. The conjunction is right-nested in exactly that order, so the
derived decision procedure short-circuits in it -- and because nonemptiness
comes first, tip/root agreement is never vacuously true on an empty chain. -/
def BlockChain.ValidContext (chain : BlockChain) : Prop :=
  chain.blocks ≠ [] ∧ chain.Canonical ∧
    chain.RetainedHistoryValid ∧ chain.TipStateAgrees

instance (chain : BlockChain) : Decidable chain.ValidContext := by
  unfold BlockChain.ValidContext; infer_instance

/-- A chain snapshot that is safe to execute from, with its tip named
explicitly.

The explicit `tip` and `tip_is_last` are what keep every consumer total: no
partial projection, no defaulting lookup, no `Fin` arithmetic, and
nonemptiness comes free. The constructor is private; the only routes in are
`BlockChain.check` (which pays for the checks), `CheckedBlockChain.ofEvidence`
(which demands them as proofs), and the transition/genesis constructors built
on it. -/
structure CheckedBlockChain : Type where
  private mk ::
  /-- The snapshot itself. -/
  val : BlockChain
  /-- Its tip block, named rather than projected. -/
  tip : Block
  /-- The tip really is the last block. -/
  tip_is_last : val.blocks.getLast? = some tip
  /-- Its retained ancestry supports `BLOCKHASH`. -/
  retainedHistory : val.RetainedHistoryValid
  /-- Its world carries no noncanonical entry. -/
  canonicalState : val.state.Canonical
  /-- Its world is the one the tip header commits to. -/
  tipStateRoot : val.state.root = tip.header.stateRoot

/-- The proof-carrying constructor. Nothing is computed here: every field is
evidence, so a caller that already holds the witness -- a successful checked
transition, for instance -- pays no trie root to package its result. -/
def CheckedBlockChain.ofEvidence (chain : BlockChain) (tip : Block)
    (htip : chain.blocks.getLast? = some tip)
    (hhist : chain.RetainedHistoryValid) (hcanon : chain.state.Canonical)
    (hroot : chain.state.root = tip.header.stateRoot) : CheckedBlockChain :=
  ⟨chain, tip, htip, hhist, hcanon, hroot⟩

theorem CheckedBlockChain.ofEvidence_val {chain : BlockChain} {tip : Block}
    {htip hhist hcanon hroot} :
    (CheckedBlockChain.ofEvidence chain tip htip hhist hcanon hroot).val
      = chain := rfl

theorem CheckedBlockChain.ofEvidence_tip {chain : BlockChain} {tip : Block}
    {htip hhist hcanon hroot} :
    (CheckedBlockChain.ofEvidence chain tip htip hhist hcanon hroot).tip
      = tip := rfl

/-- Package a snapshot whose context has already been decided. -/
def CheckedBlockChain.ofValidContext {chain : BlockChain}
    (h : chain.ValidContext) : CheckedBlockChain :=
  CheckedBlockChain.ofEvidence chain (chain.blocks.getLast h.1)
    (List.getLast?_eq_some_getLast h.1) h.2.2.1 h.2.1
    (h.2.2.2 _ (List.getLast?_eq_some_getLast h.1))

/-- The defensive checker, in the frozen order: nonempty history, canonical
state, valid retained ancestry, then the state root computed once and compared
with the tip's. A snapshot that fails any of them yields no checked value at
all, so there is nothing for a caller to ignore. -/
def BlockChain.check (chain : BlockChain) : Option CheckedBlockChain :=
  if h : chain.ValidContext then
    some (CheckedBlockChain.ofValidContext h)
  else
    none

theorem BlockChain.check_isSome_iff {chain : BlockChain} :
    chain.check.isSome = true ↔ chain.ValidContext := by
  unfold BlockChain.check
  split <;> simp_all

theorem BlockChain.check_eq_none {chain : BlockChain} (h : ¬ chain.ValidContext) :
    chain.check = none := by
  unfold BlockChain.check
  split
  · exact absurd (by assumption) h
  · rfl

/-- Every checked snapshot satisfies the context its checker tests for; the
two routes in agree on what they mean. -/
theorem CheckedBlockChain.validContext (cc : CheckedBlockChain) :
    cc.val.ValidContext := by
  refine ⟨?_, cc.canonicalState, cc.retainedHistory, ?_⟩
  · intro h
    have ht := cc.tip_is_last
    rw [h] at ht
    simp at ht
  · intro t ht
    rw [cc.tip_is_last, Option.mem_def, Option.some.injEq] at ht
    rw [← ht]
    exact cc.tipStateRoot

theorem CheckedBlockChain.check_val (cc : CheckedBlockChain) :
    cc.val.check.isSome = true :=
  BlockChain.check_isSome_iff.mpr cc.validContext

/-- The snapshot's key: the hash of the tip header it is proved to end with.
Total, because the tip is a field rather than a lookup -- which is what lets
`ChainStore` derive every key instead of accepting one. -/
def CheckedBlockChain.tipHash (cc : CheckedBlockChain) : Hash32 :=
  cc.tip.header.hash

/-- The snapshot's committed state root, read from the tip header rather than
rebuilt from the world -- the same trade `tipHash` makes, for the same reason:
`tipStateRoot` is already the proof that the two agree, so recomputing
`val.state.root` here would rebuild the whole trie to learn something the
structure carries. -/
def CheckedBlockChain.stateRoot (cc : CheckedBlockChain) : Hash32 :=
  cc.tip.header.stateRoot

/-- The field read is the trie rebuild. This is `tipStateRoot` under the
accessor's name, and it is what licenses a consumer to compare against
`stateRoot` where it would otherwise have called `State.root`. -/
theorem CheckedBlockChain.stateRoot_eq (cc : CheckedBlockChain) :
    cc.stateRoot = cc.val.state.root := cc.tipStateRoot.symm

/-- Genesis: the only route from a canonical genesis envelope and a parsed
prestate to a checked snapshot. It demands what `Main.lean` never checked --
that the prestate is canonical and that its root is the one the genesis header
commits to -- and it demands that genesis be block zero, which is what makes
the retained-history coverage clause true of the chain it starts. -/
def CheckedBlockChain.ofGenesis (cb : CanonicalBlock) (state : State)
    (chainId : UInt64) (hnum : cb.block.header.number = 0)
    (hcanon : state.Canonical) (hroot : state.root = cb.block.header.stateRoot) :
    CheckedBlockChain :=
  CheckedBlockChain.ofEvidence ⟨[cb.block], state, chainId⟩ cb.block rfl
    ⟨List.IsChain.singleton _,
      by
        intro b hb
        rw [List.mem_singleton.mp hb]
        exact cb.rlpCanonical.1,
      Or.inr (by
        intro b hb
        rw [Option.mem_def, List.head?_cons, Option.some.injEq] at hb
        rw [← hb]
        exact hnum)⟩
    hcanon hroot

theorem CheckedBlockChain.ofGenesis_val {cb : CanonicalBlock} {state : State}
    {chainId : UInt64} {hnum hcanon hroot} :
    (CheckedBlockChain.ofGenesis cb state chainId hnum hcanon hroot).val
      = ⟨[cb.block], state, chainId⟩ := rfl

theorem CheckedBlockChain.ofGenesis_tip {cb : CanonicalBlock} {state : State}
    {chainId : UInt64} {hnum hcanon hroot} :
    (CheckedBlockChain.ofGenesis cb state chainId hnum hcanon hroot).tip
      = cb.block := rfl

/-- The decidable form, for a caller that does not want to case on the three
conditions itself. The proof-taking `ofGenesis` above is what the fixture
runner uses, so that the prestate's root is computed exactly once. -/
def CheckedBlockChain.ofGenesis? (cb : CanonicalBlock) (state : State)
    (chainId : UInt64) : Option CheckedBlockChain :=
  if h : cb.block.header.number = 0 ∧ state.Canonical ∧
      state.root = cb.block.header.stateRoot then
    some (CheckedBlockChain.ofGenesis cb state chainId h.1 h.2.1 h.2.2)
  else
    none

theorem CheckedBlockChain.ofGenesis?_eq_some {cb : CanonicalBlock} {state : State}
    {chainId : UInt64} {cc : CheckedBlockChain}
    (h : CheckedBlockChain.ofGenesis? cb state chainId = some cc) :
    cc.val = ⟨[cb.block], state, chainId⟩ ∧ cc.tip = cb.block := by
  unfold CheckedBlockChain.ofGenesis? at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

--------------- THE CONFIGURED CHAIN ---------------

/-- A configured chain: a validated schedule, a checked snapshot, and the
evidence that they name the same chain.

P0.1 item 4. The three facts a configured entry point would otherwise recheck
on every call -- schedule usability, snapshot integrity, chain-ID agreement --
are established once, here, before any candidate bytes exist. The raw
configured wrappers keep checking on every call, because they carry no
proof. -/
structure ConfiguredChain : Type where
  private mk ::
  config : ChainConfig
  chain : CheckedBlockChain
  validSchedule : config.Valid
  chainId_eq : config.chainId = chain.val.chainId

/-- The checked constructor: the only route to a configured chain. -/
def ConfiguredChain.of? (cfg : ChainConfig) (cc : CheckedBlockChain) :
    Option ConfiguredChain :=
  if h : cfg.Valid ∧ cfg.chainId = cc.val.chainId then
    some ⟨cfg, cc, h.1, h.2⟩
  else
    none

theorem ConfiguredChain.of?_eq_some {cfg : ChainConfig} {cc : CheckedBlockChain}
    {pc : ConfiguredChain} (h : ConfiguredChain.of? cfg cc = some pc) :
    pc.config = cfg ∧ pc.chain = cc := by
  unfold ConfiguredChain.of? at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

/-- A configured chain never disagrees with itself: the chain-ID check the raw
configured entry points perform is redundant on this path, by construction. -/
theorem ConfiguredChain.checkChainId_eq_ok (pc : ConfiguredChain) :
    pc.config.checkChainId pc.chain.val = .ok () := by
  unfold ChainConfig.checkChainId
  rw [ite_eq_left pc.chainId_eq]

/-- Check EIP-7934 against the authoritative original RLP byte length.

This deliberately takes evidence, not a decoded `Block`: re-encoding would
discard the distinction between the bytes a peer supplied and a reconstructed
canonical value. The block-import path performs its existing strict decode and
byte-for-byte canonical round trip before treating this as a consensus
rejection. -/
def checkBlockRlpSize (limits : BlockLimits) (rawSize : Nat) :
    Except BlockValidationError Unit :=
  match limits.maxRlpSize with
  | none => .ok ()
  | some maxRlpSize =>
    if rawSize > maxRlpSize then
      .error <| .blockRlpSizeExceeded <| .text
        s!"original block RLP is {rawSize} bytes > \
           maximum = {maxRlpSize}"
    else
      .ok ()

/-- Import an envelope using its original wire length. The transition function supplies
the fork semantics and keeps lookup failures outside consensus rejections. -/
def importCore
    (transition : BlockChain → Block → Except ImportFailure (Except TransitionError BlockChain))
    (limits : BlockLimits) (chain : BlockChain) (candidate : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) := do
  match checkBlockRlpSize limits candidate.rawSize with
  | .error error => return .inr (.block error)
  | .ok () =>
    match ← transition chain candidate.block with
    | .ok next => return .inl next
    | .error error =>
      match error.split with
      | .inl failure => throw failure
      | .inr rejection => return .inr rejection

private theorem importCore_eq_ok_inl
    {transition : BlockChain → Block → Except ImportFailure (Except TransitionError BlockChain)}
    {limits : BlockLimits} {chain next : BlockChain} {candidate : CanonicalBlock}
    (h : importCore transition limits chain candidate = .ok (.inl next)) :
    checkBlockRlpSize limits candidate.rawSize = .ok () ∧
      transition chain candidate.block = .ok (.ok next) := by
  cases hs : checkBlockRlpSize limits candidate.rawSize with
  | error e => simp [importCore, hs, pure, Except.pure] at h
  | ok u =>
    cases u
    refine ⟨rfl, ?_⟩
    cases ht : transition chain candidate.block with
    | error e => simp [importCore, hs, ht, bind, Except.bind] at h
    | ok result =>
      cases result with
      | ok out =>
        simpa [importCore, hs, ht, bind, Except.bind, pure, Except.pure] using h
      | error e =>
        cases he : e.split <;>
          simp [importCore, hs, ht, bind, Except.bind, pure, Except.pure, he] at h

/-- Block import from a canonical outer-block envelope, under an explicit rule
set. This is the checked import core; every public import path below is a
named raw compatibility wrapper that validates its bytes and then calls it.

Both quantities the previous three-argument shape received as *independent*
parameters are now derived from the envelope: the header hash is
`cb.headerHash`, computed from the decoded header, and the EIP-7934 size is
`cb.rawSize`, the length of the bytes the peer actually supplied. That shape's
first act was to reject a block whose recomputed header hash differed from the
supplied one, a comparison that was tautological at every call site (design
report §3.4); with the envelope there is nothing left to compare, so the check
is *removed* rather than preserved as a no-op.

Check precedence is unchanged. Strict decode and the byte-for-byte round trip
are harness prerequisites, discharged before an envelope can exist at all;
among consensus checks EIP-7934 is first, before `stateTransitionAt` reaches
header validation, exactly as EELS. The two failure channels are unchanged:
`.error` is a harness-level failure, `.inr` is a block this chain rejects. -/
def addBlockToChainCanonicalTyped (f : Fork) (chain : BlockChain)
    (cb : CanonicalBlock) : Except ImportFailure (ImportOutcome BlockChain) :=
  importCore (fun ch block => .ok (stateTransitionTyped f ch block)) f.ruleSet.block chain cb

/-- Canonical-envelope configured import after the containing fork lookup.
Size rejection precedes the shared transition. Ommer lookup failures are
operational import failures and can never become scored block rejections. -/
def addBlockToChainScheduledCanonicalTyped (cfg : ChainConfig) (f : Fork)
    (chain : BlockChain) (cb : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) :=
  (importCore (fun ch block => (stateTransitionScheduledTyped cfg f ch block).mapError ImportFailure.ofLookup)
    f.ruleSet.block chain cb)

/-- A scheduled ommer lookup failure stays operational at the import boundary. -/
theorem addBlockToChainScheduledCanonicalTyped_lookup_error {cfg : ChainConfig} {f : Fork}
    {chain : BlockChain} {cb : CanonicalBlock} {e : RulesLookupError}
    (hsize : checkBlockRlpSize f.ruleSet.block cb.rawSize = .ok ())
    (hlookup : stateTransitionScheduledTyped cfg f chain cb.block = .error e) :
    addBlockToChainScheduledCanonicalTyped cfg f chain cb = .error (ImportFailure.ofLookup e) := by
  simp [addBlockToChainScheduledCanonicalTyped, importCore, hsize, hlookup, Except.mapError, bind, Except.bind]

theorem addBlockToChainScheduledCanonicalTyped_eq_ok_inl {cfg : ChainConfig} {f : Fork}
    {chain chain' : BlockChain} {cb : CanonicalBlock}
    (h : addBlockToChainScheduledCanonicalTyped cfg f chain cb = .ok (.inl chain')) :
    checkBlockRlpSize f.ruleSet.block cb.rawSize = .ok () ∧
      stateTransitionScheduledTyped cfg f chain cb.block = .ok (.ok chain') := by
  obtain ⟨hs, ht⟩ := importCore_eq_ok_inl h
  refine ⟨hs, ?_⟩
  cases hrun : stateTransitionScheduledTyped cfg f chain cb.block with
  | error e => simp [hrun, Except.mapError] at ht
  | ok result => simpa [hrun, Except.mapError] using ht

/-- Collapse a typed import result onto the legacy stringly channels: the
operational failure renders on the outer `.error`, the candidate rejection on
the inner `.inr`. This is the single renderer every legacy import adapter
goes through. -/
def ImportOutcome.renderLegacy :
    Except ImportFailure (ImportOutcome BlockChain) →
    Except String (BlockChain ⊕ String)
  | .error failure => .error failure.render
  | .ok (.inl chain) => .ok (.inl chain)
  | .ok (.inr rejection) => .ok (.inr rejection.render)

/-- Legacy renderer adapter over the canonical-envelope import core. -/
def addBlockToChainCanonical (f : Fork) (chain : BlockChain)
    (cb : CanonicalBlock) :
    Except String (BlockChain ⊕ String) :=
  ImportOutcome.renderLegacy (addBlockToChainCanonicalTyped f chain cb)

/-- Block import from raw bytes under an explicit rule set: the typed core of
the raw compatibility wrapper. It carries no evidence, so it validates on
every call (fixed decision 2) -- strict decode plus the exact round trip --
and hands the checked core an envelope built from that decode alone.

Channel decision, per the Step-1 producer/channel matrix: every strict decode
failure of the candidate bytes is a *candidate rejection* (`.inr .decode`),
because the audited fixture ordering scores each of the seven decode reasons
as a block exception. The legacy wrapper's old habit of reporting them on the
outer channel was the accidental nesting design report §8 names, and is
deliberately not preserved. `RawImportFailure.strictDecode` therefore retains
no producer on this path; it remains the declared ingress channel for a
future decoder whose failures are *not* candidate verdicts. -/
def addBlockToChainAtTyped (f : Fork) (chain : BlockChain)
    (blockRlp : Bytes) : Except ImportFailure (ImportOutcome BlockChain) :=
  match h : rlpToBlockTyped blockRlp with
  | .error reason => .ok (.inr (.decode reason))
  | .ok ⟨_, _⟩ =>
    addBlockToChainCanonicalTyped f chain
      (CanonicalBlock.ofDecode (rlpToBlock_eq_ok_iff.mpr h))

/-- Legacy renderer adapter over `addBlockToChainAtE`. Retained by type:
Blanc's protected `addBlockToChain_preserves_solvent` is its Prague instance.
Same rendered diagnostics; the decode-failure channel moved from the outer
`.error` to the inner `.inr` deliberately (see the core's docstring and the
Step-10 report).

Named `addBlockToChainWith` and taking a `ForkRules` until goal
`jaune-forks-by-construction-v1`; with a machine carrying a `Fork` the
rules-taking adapter and the fork-taking one had the same domain, and the
duplicate layer was retired into this name. Its `.support` channel remains
for an absent rule record. Earlier historical waves used that route for
pre-Berlin forks; this candidate resolves their records too. -/
def addBlockToChainAt (f : Fork) (chain : BlockChain) (blockRlp : Bytes) :
    Except String (BlockChain ⊕ String) :=
  ImportOutcome.renderLegacy (addBlockToChainAtTyped f chain blockRlp)

/-- Typed block import on a configured chain, deriving the active fork from
the block's own timestamp and the chain's activation schedule.

Checks schedule usability and chain identity before touching the candidate
bytes at all -- P0.1 and P0.5's frozen ordering (design report §3.3): a
contradictory or unusable configuration is a context failure regardless of
what the caller supplied as a block, so it must not depend on decoding
succeeding first. The era a decoded timestamp falls in is checked after
decode, inside `cfg.forkAt` below, because no number or timestamp exists before
decode. -/
def addBlockToChainUsingTyped (cfg : ChainConfig) (chain : BlockChain)
    (blockRlp : Bytes) : Except ImportFailure (ImportOutcome BlockChain) := do
  Except.mapError ImportFailure.context cfg.validate
  Except.mapError ImportFailure.context (cfg.checkChainId chain)
  match h : rlpToBlockTyped blockRlp with
  | .error reason => .ok (.inr (.decode reason))
  | .ok ⟨block, _⟩ =>
    let fork ←
      Except.mapError ImportFailure.ofLookup
        (cfg.forkAt block.header.number block.header.timestamp)
    addBlockToChainScheduledCanonicalTyped cfg fork chain
      (CanonicalBlock.ofDecode (rlpToBlock_eq_ok_iff.mpr h))

/-- Legacy renderer adapter over `addBlockToChainUsingE`. -/
def addBlockToChainUsing (cfg : ChainConfig) (chain : BlockChain)
    (blockRlp : Bytes) : Except String (BlockChain ⊕ String) :=
  ImportOutcome.renderLegacy (addBlockToChainUsingTyped cfg chain blockRlp)

/-- Prague block import.

Retained with its original name, type, and behaviour; downstream proofs state
their results about this name. -/
def addBlockToChain (chain : BlockChain) (blockRlp : Bytes) :
  Except String (BlockChain ⊕ String) :=
  addBlockToChainAt .prague chain blockRlp

--------------- IMPORT BRIDGE AND INVERSION LEMMAS ---------------

-- Stated entirely over `rlpToBlock`, `checkBlockRlpSize` and
-- `stateTransitionAt`. A downstream proof client -- Blanc, in practice --
-- can invert an import with these and never unfold `CanonicalBlock`,
-- `addBlockToChainCanonical`, or the raw wrapper's dependent match.

/-- A raw import whose bytes do not strictly decode *rejects the candidate*
with exactly the decoder's own diagnostic. Before Step 10 the same diagnostic
rode the outer harness channel -- the accidental nesting design report §8
records -- so the channel here is a deliberate move, and the rendered message
is unchanged. -/
theorem addBlockToChainAt_decode_error {f : Fork} {chain : BlockChain}
    {blockRlp : Bytes} {err : String} (h : rlpToBlock blockRlp = .error err) :
    addBlockToChainAt f chain blockRlp = .ok (.inr err) := by
  unfold rlpToBlock at h
  rw [Except.mapError_eq_error_iff] at h
  obtain ⟨reason, hre, rfl⟩ := h
  unfold addBlockToChainAt addBlockToChainAtTyped
  split
  · rename_i e he
    rw [hre] at he
    cases he
    rfl
  · rename_i b hs hb
    rw [hre] at hb
    exact absurd hb (by simp)

/-- A raw import whose bytes strictly decode is the checked core on the
envelope that decode produces. This is the bridge: the wrapper adds
validation, and nothing else. -/
theorem addBlockToChainAt_eq_canonical {f : Fork} {chain : BlockChain}
    {blockRlp : Bytes} {block : Block} {hash : Hash32}
    (h : rlpToBlock blockRlp = .ok ⟨block, hash⟩) :
    addBlockToChainAt f chain blockRlp
      = addBlockToChainCanonical f chain (CanonicalBlock.ofDecode h) := by
  have hE := rlpToBlock_eq_ok_iff.mp h
  unfold addBlockToChainAt addBlockToChainAtTyped
  split
  · rename_i e he
    rw [hE] at he
    exact absurd he (by simp)
  · rename_i f sh hb
    rw [hE] at hb
    simp only [Except.ok.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rfl

/-- Inversion of the typed canonical-envelope import core. -/
theorem addBlockToChainCanonicalTyped_eq_ok_inl {f : Fork}
    {chain chain' : BlockChain} {cb : CanonicalBlock}
    (h : addBlockToChainCanonicalTyped f chain cb = .ok (.inl chain')) :
    checkBlockRlpSize f.ruleSet.block cb.rawSize = .ok () ∧
      stateTransitionTyped f chain cb.block = .ok chain' := by
  obtain ⟨hs, ht⟩ := importCore_eq_ok_inl h
  exact ⟨hs, Except.ok.inj ht⟩

/-- Full inversion of a successful raw import: strict decode, then EIP-7934
against the *supplied* byte length, then the transition -- in that order.
Stated over the legacy names, so a downstream stringly client (Blanc) can
invert an import without unfolding the typed core. -/
theorem addBlockToChainAt_eq_ok_inl {f : Fork}
    {chain chain' : BlockChain} {blockRlp : Bytes}
    (h : addBlockToChainAt f chain blockRlp = .ok (.inl chain')) :
    ∃ block hash,
      rlpToBlock blockRlp = .ok ⟨block, hash⟩ ∧
      checkBlockRlpSize f.ruleSet.block blockRlp.length = .ok () ∧
      stateTransitionAt f chain block = .ok chain' := by
  unfold addBlockToChainAt at h
  cases hE : addBlockToChainAtTyped f chain blockRlp with
  | error failure =>
    rw [hE] at h; exact absurd h (by simp [ImportOutcome.renderLegacy])
  | ok outcome =>
    rw [hE] at h
    cases outcome with
    | inr r => exact absurd h (by simp [ImportOutcome.renderLegacy])
    | inl ch =>
      simp only [ImportOutcome.renderLegacy, Except.ok.injEq, Sum.inl.injEq] at h
      subst h
      unfold addBlockToChainAtTyped at hE
      split at hE
      · exact absurd hE (by simp)
      · rename_i block hash hd
        obtain ⟨hsize, hst⟩ := addBlockToChainCanonicalTyped_eq_ok_inl hE
        exact ⟨block, hash, rlpToBlock_eq_ok_iff.mpr hd, hsize,
          stateTransitionAt_eq_ok_iff.mpr hst⟩

-- P0.1 acceptance evidence: configured success cannot happen across
-- contradictory chain identities, and a successful configured transition
-- preserves the identity it started with.

theorem stateTransitionUsing_success_chainId_eq
    {cfg : ChainConfig} {ch : BlockChain} {block : Block} {ch' : BlockChain}
    (h : stateTransitionUsing cfg ch block = .ok ch') :
    cfg.chainId = ch.chainId := by
  by_contra hne
  simp [stateTransitionUsing, ChainConfig.checkChainId, hne, Except.mapError,
    Bind.bind, Except.bind] at h

/-- Every successful `stateTransitionAt` copies the input snapshot's chain
identity into its output unconditionally -- the shared fact both configured
entry points' preservation theorems reduce to. -/
theorem stateTransitionAt_preserves_chainId
    {f : Fork} {ch : BlockChain} {block : Block} {ch' : BlockChain}
    (h : stateTransitionAt f ch block = .ok ch') :
    ch'.chainId = ch.chainId := by
  rw [stateTransitionAt_eq_ok_iff] at h
  unfold stateTransitionTyped at h
  exact stateTransitionCoreTyped_preserves_chainId h

theorem stateTransitionUsing_preserves_chainId
    {cfg : ChainConfig} {ch : BlockChain} {block : Block} {ch' : BlockChain}
    (h : stateTransitionUsing cfg ch block = .ok ch') :
    ch'.chainId = ch.chainId := by
  obtain ⟨f, _, hs⟩ := stateTransitionUsing_run h
  exact stateTransitionCoreTyped_preserves_chainId (stateTransitionScheduledTyped_eq_ok_iff.mp hs)

/-- A same-ID configured transition is exactly the rule-selected core: the
identity check Step 2 adds is a no-op whenever the caller's IDs already agree,
so no previously-agreeing caller observes any behavioral change. -/
theorem stateTransitionUsing_eq_of_chainId_eq
    {cfg : ChainConfig} {ch : BlockChain} {block : Block}
    (heq : cfg.chainId = ch.chainId) :
    stateTransitionUsing cfg ch block
      = (Except.mapError RulesLookupError.render
          (cfg.forkAt block.header.number block.header.timestamp)).bind
          (fun f =>
            match stateTransitionScheduledTyped cfg f ch block with
            | .error e => .error e.render
            | .ok r => r.mapError TransitionError.render) := by
  unfold stateTransitionUsing ChainConfig.checkChainId
  simp [heq, Except.mapError, Bind.bind, Except.bind]

theorem addBlockToChainUsing_success_chainId_eq
    {cfg : ChainConfig} {chain : BlockChain} {blockRlp : Bytes} {chain' : BlockChain}
    (h : addBlockToChainUsing cfg chain blockRlp = .ok (.inl chain')) :
    cfg.chainId = chain.chainId := by
  unfold addBlockToChainUsing addBlockToChainUsingTyped at h
  by_contra hne
  cases hv : cfg.validate with
  | error e =>
    rw [hv] at h
    simp [Except.mapError, Bind.bind, Except.bind,
      ImportOutcome.renderLegacy] at h
  | ok u =>
    cases u
    rw [hv] at h
    simp [ChainConfig.checkChainId, hne, Except.mapError, Bind.bind,
      Except.bind, ImportOutcome.renderLegacy] at h

theorem addBlockToChainUsing_preserves_chainId
    {cfg : ChainConfig} {chain : BlockChain} {blockRlp : Bytes} {chain' : BlockChain}
    (h : addBlockToChainUsing cfg chain blockRlp = .ok (.inl chain')) :
    chain'.chainId = chain.chainId := by
  unfold addBlockToChainUsing at h
  cases hE : addBlockToChainUsingTyped cfg chain blockRlp with
  | error f => rw [hE] at h; simp [ImportOutcome.renderLegacy] at h
  | ok outcome =>
    rw [hE] at h
    cases outcome with
    | inr r => simp [ImportOutcome.renderLegacy] at h
    | inl ch =>
      simp only [ImportOutcome.renderLegacy, Except.ok.injEq, Sum.inl.injEq] at h
      subst h
      unfold addBlockToChainUsingTyped at hE
      obtain ⟨_, _, hE⟩ := Except.bind_eq_ok hE
      obtain ⟨_, _, hE⟩ := Except.bind_eq_ok hE
      split at hE
      · simp at hE
      · obtain ⟨rules, _, hE⟩ := Except.bind_eq_ok hE
        obtain ⟨_, hst⟩ := addBlockToChainScheduledCanonicalTyped_eq_ok_inl hE
        exact stateTransitionCoreTyped_preserves_chainId
          (stateTransitionScheduledTyped_eq_ok_iff.mp hst)

--------------- CANONICALITY THROUGH EXECUTION (P0.4, STEP 4) ---------------

-- Checkpoint 3: canonicality through message-call processing, transaction
-- processing, system transactions, withdrawals, the block body, and the raw
-- successful block transition. Every lemma states the success channel; the
-- error channel at this layer carries no state.

/-! ### The prepared top-level state -/

/-- **Raw successful block transition preserves canonicality.** The output
chain's execution state is the body's final state, and its original state is
the input chain's. -/
theorem stateTransitionAt_canonical {f : Fork} {ch : BlockChain}
    (h : ch.Canonical) {block : Block} {ch'}
    (hp : stateTransitionAt f ch block = .ok ch') : ch'.Canonical := by
  rw [stateTransitionAt_eq_ok_iff] at hp
  unfold stateTransitionTyped at hp
  exact stateTransitionCoreTyped_canonical h hp

theorem stateTransition_canonical {ch : BlockChain} (h : ch.Canonical)
    {block : Block} {ch'} (hp : stateTransition ch block = .ok ch') :
    ch'.Canonical :=
  stateTransitionAt_canonical (f := .prague) h hp

/-- Configured successful transition preserves canonicality. -/
theorem stateTransitionUsing_canonical {cfg : ChainConfig} {ch : BlockChain}
    (h : ch.Canonical) {block : Block} {ch'}
    (hp : stateTransitionUsing cfg ch block = .ok ch') : ch'.Canonical := by
  obtain ⟨f, _, hs⟩ := stateTransitionUsing_run hp
  exact stateTransitionCoreTyped_canonical h (stateTransitionScheduledTyped_eq_ok_iff.mp hs)

--------------- THE CHECKED TRANSITION (P0.2, STEP 6) ---------------

-- What the raw transition already establishes, read back out of it. Nothing
-- here re-executes or recomputes anything: `validateHeader` has already
-- compared the child's parent hash and number against the parent header, and
-- `stateTransitionChecks` has already compared the computed post-state root
-- against the child header's. Those two comparisons are exactly the halves of
-- a checked snapshot's witness the transition does not otherwise carry, so
-- the checked core constructs its output from them rather than paying for a
-- second trie root.

-- `validateHeader` is a `do` block of guards, so its elaboration is a nest of
-- join points under `have`-bound continuations. Zeta-expanding all of them at
-- once duplicates each continuation twice per level, and the resulting term is
-- large enough to exhaust `simp`'s step budget -- which is a limit that may
-- not be raised. Peeling one binder at a time keeps the shared term small.
/-- Header validation establishes both halves of `Block.Links` against the
chain's tip. -/
theorem validateHeader_links {rules : ForkRules} {chain : BlockChain}
    {header : Header} {tip : Block} (htip : chain.blocks.getLast? = some tip)
    (h : validateHeader rules chain header = .ok ()) :
    header.parentHash = tip.header.hash ∧
      header.number = tip.header.number + 1 := by
  unfold validateHeader at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨parent, hpar, h⟩ := Except.bind_eq_ok h
  rw [htip] at hpar
  simp only [Option.toExcept, Except.ok.injEq] at hpar
  subst hpar
  dsimp only at h
  by_cases hph : header.parentHash = tip.header.hash
  · rw [ite_eq_right (by simpa [Header.hash] using hph)] at h
    refine ⟨hph, ?_⟩
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    obtain ⟨bf, hbf, h⟩ := Except.bind_eq_ok h
    by_cases h1 : (header.excessBlobGas.any
        (· != calcExcessBlobGas rules.blob tip.header)) = true
    · rw [ite_eq_left h1] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    rw [ite_eq_right h1] at h
    by_cases h2 : header.gasUsed > header.gasLimit
    · rw [ite_eq_left h2] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    rw [ite_eq_right h2] at h
    by_cases h3 : bf ≠ header.baseFeePerGas
    · rw [ite_eq_left h3] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    rw [ite_eq_right h3] at h
    by_cases h4 : header.timestamp ≤ tip.header.timestamp
    · rw [ite_eq_left h4] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    rw [ite_eq_right h4] at h
    by_cases h5 : header.number ≠ tip.header.number + 1
    · rw [ite_eq_left h5] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    · simpa using h5
  · exfalso
    rw [ite_eq_left (by simpa [Header.hash] using hph)] at h
    by_cases hz : header.parentHash = 0
    · rw [ite_eq_left hz] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)
    · rw [ite_eq_right hz] at h
      obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
      exact absurd hb (by simp)

/-- A successful first fee-bearing header passed the complete gas-limit
check against the elastic limit of its actual retained parent. -/
theorem validateHeader_firstFee_gasLimit {rules : ForkRules} {chain : BlockChain}
    {header : Header} {parent : Block}
    (htip : chain.blocks.getLast? = some parent)
    (h : validateHeader rules chain header = .ok ())
    (hb : header.baseFeePerGas.isSome = true) (hp : parent.header.baseFeePerGas = none) :
    checkGasLimit header.gasLimit (elasticityMultiplier * parent.header.gasLimit) = .ok () := by
  have hph := (validateHeader_links htip h).1
  unfold validateHeader at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨p, hpar, h⟩ := Except.bind_eq_ok h
  rw [htip] at hpar
  simp only [Option.toExcept, Except.ok.injEq] at hpar
  subst hpar
  dsimp only at h
  rw [ite_eq_right (by simpa only [Header.hash, not_not] using hph)] at h
  obtain ⟨u, hgas, _⟩ := Except.bind_eq_ok h
  cases u
  have hg := Except.mapError_eq_ok_iff.mp hgas
  simpa only [checkFirstFeeGasLimit, hb, hp, Option.isNone_none, Bool.and_self,
    ↓reduceIte] using hg

/-- The block checks establish the computed post-state root against the child
header's own -- which is exactly the tip/root agreement the resulting snapshot
needs, already paid for. -/
theorem stateTransitionChecks_stateRoot {bout : BlockOutput} {header : Header}
    {transactionsRoot blockStateRoot receiptRoot : Hash32} {blockLogsBloom : Bytes}
    {withdrawalsRoot : Hash32} {requestsHash : Option Hash32}
    (h : stateTransitionChecks bout header transactionsRoot blockStateRoot
      receiptRoot blockLogsBloom withdrawalsRoot requestsHash = .ok ()) :
    blockStateRoot = header.stateRoot := by
  unfold stateTransitionChecks at h
  dsimp only at h
  by_cases h1 : max bout.blockGasUsed bout.blockStateGasUsed ≠ header.gasUsed
  · rw [ite_eq_left h1] at h
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
    exact absurd hb (by simp)
  rw [ite_eq_right h1] at h
  by_cases h2 : transactionsRoot ≠ header.transactionsRoot
  · rw [ite_eq_left h2] at h
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
    exact absurd hb (by simp)
  rw [ite_eq_right h2] at h
  by_cases h3 : blockStateRoot ≠ header.stateRoot
  · rw [ite_eq_left h3] at h
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok h
    exact absurd hb (by simp)
  · simpa using h3

/-- The checked output witness is derived from checks already performed by
the common algorithm, with no second root computation. -/
theorem BlockChain.validContext_of_scheduled {cfg : ChainConfig} {f : Fork}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionScheduledTyped cfg f cc.val cb.block = .ok (.ok ch')) :
    ch'.blocks.getLast? = some cb.block ∧ ch'.RetainedHistoryValid ∧
      ch'.state.Canonical ∧ ch'.state.root = cb.block.header.stateRoot := by
  have hc := stateTransitionScheduledTyped_eq_ok_iff.mp h
  obtain ⟨hvh, hblocks, hroot⟩ := stateTransitionCoreTyped_eq_ok hc
  obtain ⟨hph, hnum⟩ := validateHeader_links cc.tip_is_last hvh
  refine ⟨?_, ?_, stateTransitionCoreTyped_canonical cc.canonicalState hc, hroot⟩
  · rw [hblocks]; exact appendBlock_getLast? _ _
  · exact BlockChain.retainedHistoryValid_appendBlock cc.retainedHistory
      cc.tip_is_last ⟨hnum, hph⟩ cb.rlpCanonical.1 hblocks

/-- Inversion of a successful raw transition: header validation passed, the
result's blocks are the parent's with this block appended, and its state is
the one the child header commits to. -/
theorem stateTransitionAt_eq_ok {f : Fork} {ch ch' : BlockChain}
    {block : Block} (h : stateTransitionAt f ch block = .ok ch') :
    validateHeader f.ruleSet ch block.header = .ok () ∧
      ch'.blocks = appendBlock ch.blocks block ∧
      ch'.state.root = block.header.stateRoot := by
  rw [stateTransitionAt_eq_ok_iff] at h
  unfold stateTransitionTyped at h
  exact stateTransitionCoreTyped_eq_ok h

/-- The whole output witness of a successful transition from a checked
snapshot, assembled from what the transition already established: `Step 4`'s
canonicality preservation, header validation's parent link, the checked
envelope's wire well-formedness, and the block checks' own state-root
comparison. No root is recomputed. -/
theorem BlockChain.validContext_of_transition {f : Fork}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionAt f cc.val cb.block = .ok ch') :
    ch'.blocks.getLast? = some cb.block ∧ ch'.RetainedHistoryValid ∧
      ch'.state.Canonical ∧ ch'.state.root = cb.block.header.stateRoot := by
  obtain ⟨hvh, hblocks, hroot⟩ := stateTransitionAt_eq_ok h
  obtain ⟨hph, hnum⟩ := validateHeader_links cc.tip_is_last hvh
  refine ⟨?_, ?_, stateTransitionAt_canonical (f := f) cc.canonicalState h, hroot⟩
  · rw [hblocks]; exact appendBlock_getLast? _ _
  · exact BlockChain.retainedHistoryValid_appendBlock cc.retainedHistory
      cc.tip_is_last ⟨hnum, hph⟩ cb.rlpCanonical.1 hblocks

--------------- CHECKED TRANSITION AND IMPORT CORES ---------------

/-- The checked transition core: it accepts only a checked snapshot and a
canonical envelope, and it is definitionally the typed core on their values,
so every result about `stateTransitionE` transfers by `rfl`. Its output
witness is `CheckedBlockChain.ofTransition` below. -/
def stateTransitionChecked (f : Fork) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    Except TransitionError BlockChain :=
  stateTransitionTyped f cc.val cb.block

theorem stateTransitionChecked_eq (f : Fork) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    stateTransitionChecked f cc cb
      = stateTransitionTyped f cc.val cb.block := rfl

/-- The checked output of a successful checked transition.

This is the P0.2 fast path: the returned snapshot's four facts are proofs, not
computations, so a repeated client pays exactly one state-root computation --
the one `stateTransitionChecks` already performed on the child -- and never a
second one on the parent. -/
def CheckedBlockChain.ofTransition {f : Fork} {cc : CheckedBlockChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionChecked f cc cb = .ok ch') : CheckedBlockChain :=
  CheckedBlockChain.ofEvidence ch' cb.block
    (BlockChain.validContext_of_transition
      (stateTransitionAt_eq_ok_iff.mpr h)).1
    (BlockChain.validContext_of_transition
      (stateTransitionAt_eq_ok_iff.mpr h)).2.1
    (BlockChain.validContext_of_transition
      (stateTransitionAt_eq_ok_iff.mpr h)).2.2.1
    (BlockChain.validContext_of_transition
      (stateTransitionAt_eq_ok_iff.mpr h)).2.2.2

theorem CheckedBlockChain.ofTransition_val {f : Fork}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionChecked f cc cb = .ok ch') :
    (CheckedBlockChain.ofTransition h).val = ch' := rfl

theorem CheckedBlockChain.ofTransition_tip {f : Fork}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : stateTransitionChecked f cc cb = .ok ch') :
    (CheckedBlockChain.ofTransition h).tip = cb.block := rfl

/-- Inversion of the legacy canonical-envelope import adapter, stated over the
legacy transition name for stringly clients. -/
theorem addBlockToChainCanonical_eq_ok_inl {f : Fork}
    {chain chain' : BlockChain} {cb : CanonicalBlock}
    (h : addBlockToChainCanonical f chain cb = .ok (.inl chain')) :
    checkBlockRlpSize f.ruleSet.block cb.rawSize = .ok () ∧
      stateTransitionAt f chain cb.block = .ok chain' := by
  unfold addBlockToChainCanonical at h
  cases hE : addBlockToChainCanonicalTyped f chain cb with
  | error f => rw [hE] at h; exact absurd h (by simp [ImportOutcome.renderLegacy])
  | ok outcome =>
    rw [hE] at h
    cases outcome with
    | inr r => exact absurd h (by simp [ImportOutcome.renderLegacy])
    | inl ch =>
      simp only [ImportOutcome.renderLegacy, Except.ok.injEq, Sum.inl.injEq] at h
      subst h
      obtain ⟨hsize, hst⟩ := addBlockToChainCanonicalTyped_eq_ok_inl hE
      exact ⟨hsize, stateTransitionAt_eq_ok_iff.mpr hst⟩

/-- The checked import core: a checked snapshot in, and on the accepting
channel a snapshot whose witness is `CheckedBlockChain.ofImport`. The
validation order is the frozen one, unchanged -- this is the typed canonical
core with a checked input type, and it is the two-level shape P0.7 prescribes:
`Except ImportFailure (CheckedBlockChain-producing outcome ⊕ BlockRejection)`. -/
def addBlockToChainChecked (f : Fork) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) :=
  addBlockToChainCanonicalTyped f cc.val cb

/-- The checked output of a successful checked import. -/
def CheckedBlockChain.ofImport {f : Fork} {cc : CheckedBlockChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : addBlockToChainChecked f cc cb = .ok (.inl ch')) : CheckedBlockChain :=
  CheckedBlockChain.ofTransition
    (f := f) (cc := cc) (cb := cb)
    (addBlockToChainCanonicalTyped_eq_ok_inl h).2

theorem CheckedBlockChain.ofImport_val {f : Fork} {cc : CheckedBlockChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : addBlockToChainChecked f cc cb = .ok (.inl ch')) :
    (CheckedBlockChain.ofImport h).val = ch' := rfl

theorem CheckedBlockChain.ofImport_tip {f : Fork} {cc : CheckedBlockChain}
    {cb : CanonicalBlock} {ch' : BlockChain}
    (h : addBlockToChainChecked f cc cb = .ok (.inl ch')) :
    (CheckedBlockChain.ofImport h).tip = cb.block := rfl

--------------- CONFIGURED CHECKED ENTRY POINTS ---------------

/-- The configured checked transition. The chain-ID check the raw configured
entry point performs is discharged by the pair's own witness rather than
repeated, and the snapshot is not rechecked at all; what remains is the rule
lookup, which is the only part that depends on the candidate's timestamp. -/
def stateTransitionConfigured (pc : ConfiguredChain) (cb : CanonicalBlock) :
    Except RulesLookupError (Except TransitionError BlockChain) := do
  let f ← pc.config.forkAt cb.block.header.number cb.block.header.timestamp
  stateTransitionScheduledTyped pc.config f pc.chain.val cb.block

/-- The configured checked path agrees with the raw configured entry point on
every input, through the renderer: what it drops is exactly the check its
witness already carries. Replaces the pre-Step-10 same-carrier equation. -/
theorem stateTransitionConfigured_eq (pc : ConfiguredChain) (cb : CanonicalBlock) :
    (match stateTransitionConfigured pc cb with
      | .error e => .error e.render
      | .ok r => r.mapError TransitionError.render)
      = stateTransitionUsing pc.config pc.chain.val cb.block := by
  unfold stateTransitionConfigured stateTransitionUsing
  rw [pc.checkChainId_eq_ok]
  simp only [bind, Except.bind, Except.mapError]
  cases hr : pc.config.forkAt cb.block.header.number cb.block.header.timestamp <;> simp

theorem ConfiguredChain.validContext_of_transition {pc : ConfiguredChain}
    {cb : CanonicalBlock} {r : Except TransitionError BlockChain} {ch' : BlockChain}
    (h : stateTransitionConfigured pc cb = .ok r) (hr : r = .ok ch') :
    ch'.blocks.getLast? = some cb.block ∧ ch'.RetainedHistoryValid ∧
      ch'.state.Canonical ∧ ch'.state.root = cb.block.header.stateRoot := by
  obtain ⟨f, _, hst⟩ := Except.bind_eq_ok h
  rw [hr] at hst
  exact BlockChain.validContext_of_scheduled (cc := pc.chain) hst

/-- The checked output of a successful configured checked transition. -/
def CheckedBlockChain.ofConfiguredTransition {pc : ConfiguredChain}
    {cb : CanonicalBlock} {r : Except TransitionError BlockChain} {ch' : BlockChain}
    (h : stateTransitionConfigured pc cb = .ok r) (hr : r = .ok ch') :
    CheckedBlockChain :=
  CheckedBlockChain.ofEvidence ch' cb.block
    (ConfiguredChain.validContext_of_transition h hr).1
    (ConfiguredChain.validContext_of_transition h hr).2.1
    (ConfiguredChain.validContext_of_transition h hr).2.2.1
    (ConfiguredChain.validContext_of_transition h hr).2.2.2

/-- Checked configured import with its already-selected containing fork.
The caller retains the schedule for individual ommer validation. -/
def addBlockToChainScheduledChecked (cfg : ChainConfig) (f : Fork)
    (cc : CheckedBlockChain) (cb : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) :=
  addBlockToChainScheduledCanonicalTyped cfg f cc.val cb

/-- Build the scheduled import's output witness from its successful checks. -/
def CheckedBlockChain.ofScheduledImport {cfg : ChainConfig} {f : Fork}
    {cc : CheckedBlockChain} {cb : CanonicalBlock} {ch' : BlockChain}
    (h : addBlockToChainScheduledChecked cfg f cc cb = .ok (.inl ch')) :
    CheckedBlockChain :=
  CheckedBlockChain.ofEvidence ch' cb.block
    (BlockChain.validContext_of_scheduled
      (addBlockToChainScheduledCanonicalTyped_eq_ok_inl h).2).1
    (BlockChain.validContext_of_scheduled
      (addBlockToChainScheduledCanonicalTyped_eq_ok_inl h).2).2.1
    (BlockChain.validContext_of_scheduled
      (addBlockToChainScheduledCanonicalTyped_eq_ok_inl h).2).2.2.1
    (BlockChain.validContext_of_scheduled
      (addBlockToChainScheduledCanonicalTyped_eq_ok_inl h).2).2.2.2

--------------- CHECKED/RAW BRIDGES (FOR STEP 11) ---------------

-- Stated so a downstream proof client can move between the raw names its
-- theorems are written about and the checked ones, without unfolding either
-- structure.

theorem addBlockToChainChecked_eq_raw (f : Fork) (cc : CheckedBlockChain)
    (cb : CanonicalBlock) :
    addBlockToChainChecked f cc cb
      = addBlockToChainCanonicalTyped f cc.val cb := rfl

/-- A raw typed import of bytes into a checked snapshot's value is the checked
import of the envelope those bytes decode to. -/
theorem addBlockToChainAtTyped_eq_checked {f : Fork} {cc : CheckedBlockChain}
    {blockRlp : Bytes} {block : Block} {hash : Hash32}
    (h : rlpToBlock blockRlp = .ok ⟨block, hash⟩) :
    addBlockToChainAtTyped f cc.val blockRlp
      = addBlockToChainChecked f cc (CanonicalBlock.ofDecode h) := by
  have hE := rlpToBlock_eq_ok_iff.mp h
  unfold addBlockToChainAtTyped addBlockToChainChecked
  split
  · rename_i e he
    rw [hE] at he
    exact absurd he (by simp)
  · rename_i f sh hb
    rw [hE] at hb
    simp only [Except.ok.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rfl

/-- Any snapshot a checked value carries passes the checker, so a raw client
that checks first and a checked client that never rechecks agree on which
snapshots are executable. -/
theorem BlockChain.check_eq_some_of_checked (cc : CheckedBlockChain) :
    cc.val.check.isSome = true := cc.check_val

namespace ChainConfig

/-- The proof-of-work mint of one block under rules `pow`: what `payRewards` credits. -/
def rewardTotal (pow : ProofOfWorkRules) (number : Nat) (ommers : List Header) : Nat :=
  (pow.blockReward + ommers.length * (pow.blockReward / 32)) +
    (ommers.map fun o => (8 + o.number - number) * pow.blockReward / 8).sum

/-- The mint the configured schedule's fork pays for `block` (0 from Paris on). -/
def rewardAt (cfg : ChainConfig) (block : Block) : Nat :=
  match cfg.forkAt block.header.number block.header.timestamp with
  | .ok f => match f.ruleSet.proofOfWork with
    | some pow => rewardTotal pow block.header.number block.ommers
    | none => 0
  | .error _ => 0

theorem rewardAt_eq_zero {cfg : ChainConfig} {block : Block} {f : Fork}
    (h : cfg.forkAt block.header.number block.header.timestamp = .ok f)
    (hpos : f.ruleSet.proofOfWork = none) : cfg.rewardAt block = 0 := by
  simp only [rewardAt, h, hpos]

theorem single_prague_rewardAt (chainId : UInt64) (block : Block) :
    (single chainId .prague).rewardAt block = 0 := rfl

end ChainConfig

private theorem checkHeaderFieldPresence_eq {name : String} {present defined : Bool}
    (h : checkHeaderFieldPresence name present defined = .ok ()) : present = defined := by
  unfold checkHeaderFieldPresence at h
  split at h
  · cases h
  · rename_i heq
    exact not_not.mp heq

theorem checkHeaderShape_baseFee {rules : ForkRules} {header : Header}
    (h : checkHeaderShape rules header = .ok ()) :
    header.baseFeePerGas.isSome = rules.header.baseFee := by
  unfold checkHeaderShape at h
  obtain ⟨u, hb, _⟩ := Except.bind_eq_ok h
  cases u
  exact checkHeaderFieldPresence_eq hb

theorem checkHeaderShape_blobGas {rules : ForkRules} {header : Header}
    (h : checkHeaderShape rules header = .ok ()) :
    header.excessBlobGas.isSome = rules.header.blobGas ∧
      header.blobGasUsed.isSome = rules.header.blobGas := by
  unfold checkHeaderShape at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨u, hu, h⟩ := Except.bind_eq_ok h
  obtain ⟨v, hv, _⟩ := Except.bind_eq_ok h
  cases u
  cases v
  exact ⟨checkHeaderFieldPresence_eq hv, checkHeaderFieldPresence_eq hu⟩

/-- The first London block carries the initial fee when its parent carries no fee. -/
theorem expectedBaseFee_first {header parent : Header}
    (hb : header.baseFeePerGas.isSome = true) (hp : parent.baseFeePerGas = none) :
    expectedBaseFee header parent = .ok (some initialBaseFee) := by
  cases hh : header.baseFeePerGas with
  | none => simp only [hh, Option.isSome_none, Bool.false_eq_true] at hb
  | some fee => simp only [expectedBaseFee, hh, hp]

theorem parent_baseFee_none_iff {rules₀ : ForkRules} {parent : Header}
    (hp : checkHeaderShape rules₀ parent = .ok ()) :
    parent.baseFeePerGas = none ↔ rules₀.header.baseFee = false := by
  have hshape := checkHeaderShape_baseFee hp
  rw [← hshape]
  cases parent.baseFeePerGas <;> simp only [Option.isSome_none, Option.isSome_some,
    reduceCtorEq]

/-- Every configured step of a single-fork schedule is that fork's fixed-fork step. -/
theorem stateTransitionUsing_single {chainId : UInt64} {f : Fork} {ch : BlockChain}
    {block : Block} (hid : chainId = ch.chainId) :
    stateTransitionUsing (ChainConfig.single chainId f) ch block =
      stateTransitionAt f ch block := by
  rw [stateTransitionUsing_eq_of_chainId_eq hid, ChainConfig.single_forkAt]
  simp only [Except.mapError, Except.bind, stateTransitionScheduledTyped_single,
    stateTransitionAt]

/-- A successful step leaves the new block as the chain's last block. -/
theorem stateTransitionTyped_getLast {f : Fork} {ch ch' : BlockChain} {block : Block}
    (h : stateTransitionTyped f ch block = .ok ch') :
    ch'.blocks.getLast? = some block := by
  have hb := (stateTransitionAt_eq_ok (stateTransitionAt_eq_ok_iff.mpr h)).2.1
  rw [hb, appendBlock_getLast?]

/-- Header-shape coherence of the chain head with its scheduled fork. -/
def ChainConfig.ShapeCoherent (cfg : ChainConfig) (ch : BlockChain) : Prop :=
  ∀ b, ch.blocks.getLast? = some b →
    ∃ f, cfg.forkAt b.header.number b.header.timestamp = .ok f ∧
      checkHeaderShape f.ruleSet b.header = .ok ()

theorem stateTransitionUsing_shapeCoherent {cfg : ChainConfig} {ch ch' : BlockChain}
    {block : Block} (h : stateTransitionUsing cfg ch block = .ok ch') :
    cfg.ShapeCoherent ch' := by
  obtain ⟨f, hf, hrun⟩ := stateTransitionUsing_run h
  intro b hb
  have hc := stateTransitionScheduledTyped_eq_ok_iff.mp hrun
  have hblocks := (stateTransitionCoreTyped_eq_ok hc).2.1
  rw [hblocks, appendBlock_getLast?] at hb
  cases hb
  refine ⟨f, hf, ?_⟩
  have hv := stateTransitionCoreTyped_header hc
  unfold validateHeader at hv
  obtain ⟨u, hshape, _⟩ := Except.bind_eq_ok hv
  cases u
  exact hshape

/-- Successful header validation advances number and timestamp independently
of how the caller selected the rules. -/
theorem validateHeader_succ {rules : ForkRules} {ch : BlockChain} {header : Header}
    (h : validateHeader rules ch header = .ok ()) :
    ∃ parent, ch.blocks.getLast? = some parent ∧
      header.number = parent.header.number + 1 ∧
      parent.header.timestamp < header.timestamp := by
  have hv := h
  have hv0 := hv
  unfold validateHeader at hv
  obtain ⟨_, _, hv⟩ := Except.bind_eq_ok hv
  obtain ⟨parent, hpar, hv⟩ := Except.bind_eq_ok hv
  have hlast : ch.blocks.getLast? = some parent := by
    cases hh : ch.blocks.getLast? with
    | none => simp only [hh, Option.toExcept, reduceCtorEq] at hpar
    | some p =>
      simpa only [hh, Option.toExcept, Except.ok.injEq, Option.some.injEq] using hpar
  obtain ⟨hph, hnum⟩ := validateHeader_links hlast hv0
  refine ⟨parent, hlast, hnum, ?_⟩
  dsimp only at hv
  rw [ite_eq_right (by simpa only [Header.hash, not_not] using hph)] at hv
  obtain ⟨_, _, hv⟩ := Except.bind_eq_ok hv
  obtain ⟨bf, _, hv⟩ := Except.bind_eq_ok hv
  by_cases h1 : (header.excessBlobGas.any
      (· != calcExcessBlobGas rules.blob parent.header)) = true
  · rw [ite_eq_left h1] at hv
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok hv
    cases hb
  rw [ite_eq_right h1] at hv
  by_cases h2 : header.gasUsed > header.gasLimit
  · rw [ite_eq_left h2] at hv
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok hv
    cases hb
  rw [ite_eq_right h2] at hv
  by_cases h3 : bf ≠ header.baseFeePerGas
  · rw [ite_eq_left h3] at hv
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok hv
    cases hb
  rw [ite_eq_right h3] at hv
  by_cases h4 : header.timestamp ≤ parent.header.timestamp
  · rw [ite_eq_left h4] at hv
    obtain ⟨_, hb, _⟩ := Except.bind_eq_ok hv
    cases hb
  · omega

/-- A successful block step extends the chain by one block number and a later timestamp. -/
theorem stateTransitionTyped_header_succ {f : Fork} {ch ch' : BlockChain} {block : Block}
    (h : stateTransitionTyped f ch block = .ok ch') :
    ∃ parent, ch.blocks.getLast? = some parent ∧
      block.header.number = parent.header.number + 1 ∧
      parent.header.timestamp < block.header.timestamp := by
  exact validateHeader_succ (stateTransitionCoreTyped_header h)

/-- The configured fork is no earlier than the parent's scheduled fork. -/
theorem stateTransitionUsing_fork_mono {cfg : ChainConfig} {ch ch' : BlockChain}
    {block parent : Block} {f₀ : Fork}
    (hlast : ch.blocks.getLast? = some parent)
    (h₀ : cfg.forkAt parent.header.number parent.header.timestamp = .ok f₀)
    (h : stateTransitionUsing cfg ch block = .ok ch') :
    ∃ f, cfg.forkAt block.header.number block.header.timestamp = .ok f ∧
      f₀.index ≤ f.index ∧
      stateTransitionScheduledTyped cfg f ch block = .ok (.ok ch') := by
  obtain ⟨f, hf, hrun⟩ := stateTransitionUsing_run h
  obtain ⟨tip, htip, hnum, htime⟩ := validateHeader_succ
    (stateTransitionCoreTyped_header (stateTransitionScheduledTyped_eq_ok_iff.mp hrun))
  rw [hlast] at htip
  cases htip
  exact ⟨f, hf, ChainConfig.forkAt_index_mono (by omega) (by omega) h₀ hf, hrun⟩

/-- On a selected proof-of-stake fork, the original static-success conclusion
is valid for any schedule; no uniformity premise is added to the frozen theorem. -/
theorem stateTransitionUsing_fork_mono_static_of_pow_none
    {cfg : ChainConfig} {ch ch' : BlockChain} {block parent : Block} {f₀ : Fork}
    (hlast : ch.blocks.getLast? = some parent)
    (h₀ : cfg.forkAt parent.header.number parent.header.timestamp = .ok f₀)
    (h : stateTransitionUsing cfg ch block = .ok ch') :
    ∃ f, cfg.forkAt block.header.number block.header.timestamp = .ok f ∧
      f₀.index ≤ f.index ∧
      (f.ruleSet.proofOfWork = none → stateTransitionTyped f ch block = .ok ch') := by
  obtain ⟨f, hf, hm, hs⟩ := stateTransitionUsing_fork_mono hlast h₀ h
  refine ⟨f, hf, hm, ?_⟩
  intro hp
  rw [stateTransitionScheduledTyped_of_pow_none cfg f ch block hp] at hs
  exact Except.ok.inj hs

/-- Schedule shape coherence identifies the fee activation by rule flags,
including schedules which skip forks. The actual parent and successful shared
validation supply the elastic gas-limit bound, with no hardcoded height. -/
theorem stateTransitionScheduledTyped_firstFee_gasLimit
    {cfg : ChainConfig} {f f₀ : Fork} {ch ch' : BlockChain} {block parent : Block}
    (hshape : cfg.ShapeCoherent ch) (hlast : ch.blocks.getLast? = some parent)
    (h₀ : cfg.forkAt parent.header.number parent.header.timestamp = .ok f₀)
    (hfee₀ : f₀.ruleSet.header.baseFee = false) (hfee : f.ruleSet.header.baseFee = true)
    (h : stateTransitionScheduledTyped cfg f ch block = .ok (.ok ch')) :
    checkGasLimit block.header.gasLimit
      (elasticityMultiplier * parent.header.gasLimit) = .ok () := by
  obtain ⟨fp, hfp, hp⟩ := hshape parent hlast
  rw [h₀] at hfp
  cases hfp
  have hv := stateTransitionCoreTyped_header (stateTransitionScheduledTyped_eq_ok_iff.mp h)
  have hc : checkHeaderShape f.ruleSet block.header = .ok () := by
    unfold validateHeader at hv
    obtain ⟨u, hu, _⟩ := Except.bind_eq_ok hv
    cases u
    exact hu
  exact validateHeader_firstFee_gasLimit hlast hv
    ((checkHeaderShape_baseFee hc).trans hfee)
    ((parent_baseFee_none_iff hp).mpr hfee₀)

end Jaune
