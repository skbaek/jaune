import Jaune.ChainStore

/-!
Fixture-only parent-relative terminal-total-difficulty routing. This exact
fixture label is outside protocol fork schedules and the public fork catalogue.
Checked execution, error identities and final fixture assertions stay in their
existing layers; this module adds only an immutable branch ledger.
-/

namespace Jaune

open Jaune

/-- Fixture syntax, distinct from protocol fork/schedule syntax. -/
inductive FixtureNetwork : Type
  | scheduled (spec : NetworkSpec)
  | arrowGlacierParisTTD
  deriving DecidableEq, Repr

namespace FixtureNetwork

def ofString? (label : String) : Option FixtureNetwork :=
  if label = "ArrowGlacierToParisAtDiffC0000" then some .arrowGlacierParisTTD
  else .scheduled <$> NetworkSpec.ofString? label

def toString : FixtureNetwork → String
  | .scheduled spec => spec.toString
  | .arrowGlacierParisTTD => "ArrowGlacierToParisAtDiffC0000"

instance : ToString FixtureNetwork := ⟨toString⟩

def forks : FixtureNetwork → List Fork
  | .scheduled spec => spec.forks
  | .arrowGlacierParisTTD => [.arrowGlacier, .paris]

def genesisFork : FixtureNetwork → Fork
  | .scheduled (.static f) => f
  | .scheduled (.transition t) => t.before
  | .arrowGlacierParisTTD => .arrowGlacier

end FixtureNetwork

namespace FixtureTTD

/-- The threshold of the one supported fixture label, not mainnet fork data. -/
def threshold : Nat := 786432

inductive Phase : Type
  | preTerminal
  | terminalPow
  | pos
  deriving DecidableEq, Repr

/-- One complete branch record. TD and phase cannot drift from a second map. -/
structure Entry : Type where
  chain : CheckedBlockChain
  td : Nat
  phase : Phase

private def phaseFork : Phase → Fork
  | .preTerminal => .arrowGlacier
  | .terminalPow | .pos => .paris

/-- Only original low-TD PoW genesis is an admitted anchor for this label. -/
def GenesisAdmitted (g : CheckedBlockChain) : Prop :=
  g.tip.header.number = 0 ∧ 0 < g.tip.header.difficulty ∧ g.tip.header.difficulty < threshold

private def genesisEntry (g : CheckedBlockChain) : Entry :=
  ⟨g, g.tip.header.difficulty, .preTerminal⟩

/-- Recurrence reads only the selected parent's total and the checked child. -/
private def nextEntry (parent : Entry) (child : CheckedBlockChain) : Entry :=
  match parent.phase with
  | .preTerminal =>
    let td := parent.td + child.tip.header.difficulty
    ⟨child, td, if threshold ≤ td then .terminalPow else .preTerminal⟩
  | .terminalPow | .pos => ⟨child, parent.td, .pos⟩

/-- Proof-only provenance. Every step names the actual accepted static checked
import, including its parent, canonical envelope and selected fork. -/
inductive Origin (genesis : CheckedBlockChain) : Entry → Prop
  | genesis (h : GenesisAdmitted genesis) : Origin genesis (genesisEntry genesis)
  | step {parent : Entry} {cb : CanonicalBlock} {child : BlockChain}
      (previous : Origin genesis parent)
      (imported : addBlockToChainChecked (phaseFork parent.phase) parent.chain cb =
        .ok (.inl child)) :
      Origin genesis (nextEntry parent (CheckedBlockChain.ofImport imported))

private theorem nextEntry_phase_bounds (parent : Entry) (child : CheckedBlockChain)
    (h : match parent.phase with
      | .preTerminal => parent.td < threshold
      | .terminalPow | .pos => threshold ≤ parent.td) :
    match (nextEntry parent child).phase with
    | .preTerminal => (nextEntry parent child).td < threshold
    | .terminalPow | .pos => threshold ≤ (nextEntry parent child).td := by
  cases hp : parent.phase with
  | preTerminal =>
    simp only [nextEntry, hp]
    by_cases ht : threshold ≤ parent.td + child.tip.header.difficulty
    · simp only [ite_eq_left ht]; exact ht
    · simp only [ite_eq_right ht]; omega
  | terminalPow => simpa only [nextEntry, hp] using h
  | pos => simpa only [nextEntry, hp] using h

/-- Phase bounds follow the admitted origin; high TD alone is no origin. -/
theorem origin_phase_bounds {g : CheckedBlockChain} {entry : Entry}
    (h : Origin g entry) :
    match entry.phase with
    | .preTerminal => entry.td < threshold
    | .terminalPow | .pos => threshold ≤ entry.td := by
  induction h with
  | genesis h => exact h.2.2
  | @step parent cb child previous imported ih =>
    exact nextEntry_phase_bounds parent _ ih

/-- The child snapshot is exactly the checked import's witness. -/
private theorem nextEntry_chain (parent : Entry) (child : CheckedBlockChain) :
    (nextEntry parent child).chain = child := by
  cases hp : parent.phase <;> simp [nextEntry, hp]

private theorem nextEntry_pre (parent : Entry) (child : CheckedBlockChain)
    (h : parent.phase = .preTerminal) :
    (nextEntry parent child).td = parent.td + child.tip.header.difficulty ∧
    ((nextEntry parent child).phase = .terminalPow ↔
      threshold ≤ parent.td + child.tip.header.difficulty) := by
  simp [nextEntry, h]

private theorem nextEntry_post (parent : Entry) (child : CheckedBlockChain)
    (h : parent.phase ≠ .preTerminal) :
    (nextEntry parent child).td = parent.td ∧
      (nextEntry parent child).phase = .pos := by
  cases hp : parent.phase <;> simp_all [nextEntry]

private theorem nextEntry_terminal (parent : Entry) (child : CheckedBlockChain)
    (h : (nextEntry parent child).phase = .terminalPow) :
    parent.phase = .preTerminal ∧
      threshold ≤ parent.td + child.tip.header.difficulty := by
  cases hp : parent.phase <;> simp_all [nextEntry]

/-- The pre-terminal child has exactly the threshold-selected phase. -/
theorem step_preTerminal (parent : Entry) (child : CheckedBlockChain)
    (h : parent.phase = .preTerminal) :
    (nextEntry parent child).td = parent.td + child.tip.header.difficulty ∧
    ((nextEntry parent child).phase = .terminalPow ↔
      threshold ≤ parent.td + child.tip.header.difficulty) ∧
    ((nextEntry parent child).phase = .preTerminal ↔
      parent.td + child.tip.header.difficulty < threshold) ∧
    phaseFork parent.phase = .arrowGlacier := by
  obtain ⟨htd, hterminal⟩ := nextEntry_pre parent child h
  refine ⟨htd, hterminal, ?_, ?_⟩
  · simp [nextEntry, h]
  · simp [phaseFork, h]

/-- Terminal PoW and PoS parents select Paris, retain TD and remain PoS. -/
theorem step_postTerminal (parent : Entry) (child : CheckedBlockChain)
    (h : parent.phase ≠ .preTerminal) :
    (nextEntry parent child).td = parent.td ∧
    (nextEntry parent child).phase = .pos ∧ phaseFork parent.phase = .paris := by
  obtain ⟨htd, hphase⟩ := nextEntry_post parent child h
  refine ⟨htd, hphase, ?_⟩
  cases hp : parent.phase <;> simp_all [phaseFork]

/-- A terminal entry records an actual accepted Arrow Glacier crossing from
an origin-proven parent below the threshold. -/
theorem origin_terminal_crossing {g : CheckedBlockChain} {entry : Entry}
    (h : Origin g entry) (phase : entry.phase = .terminalPow) :
    ∃ (parent : Entry) (cb : CanonicalBlock) (child : BlockChain)
      (accepted : addBlockToChainChecked (phaseFork parent.phase) parent.chain cb =
        .ok (.inl child)),
      Origin g parent ∧ parent.phase = .preTerminal ∧ parent.td < threshold ∧
      threshold ≤ parent.td + cb.block.header.difficulty ∧
      entry = nextEntry parent (CheckedBlockChain.ofImport accepted) := by
  cases h with
  | genesis hg => cases phase
  | @step parent cb child previous imported =>
    obtain ⟨hp, ht⟩ := nextEntry_terminal parent _ phase
    have hb := origin_phase_bounds previous
    rw [hp] at hb
    exact ⟨parent, cb, child, imported, previous, hp, hb, ht, rfl⟩

/-- A PoS descendant must reach a real terminal PoW ancestor through accepted
Paris imports. This is proof-only lineage, not a second runtime ledger. -/
inductive ParisLineage (g : CheckedBlockChain) : Entry → Prop
  | terminal {entry : Entry} (origin : Origin g entry)
      (phase : entry.phase = .terminalPow) : ParisLineage g entry
  | step {parent : Entry} {cb : CanonicalBlock} {child : BlockChain}
      (previous : ParisLineage g parent) (post : parent.phase ≠ .preTerminal)
      (imported : addBlockToChainChecked (phaseFork parent.phase) parent.chain cb =
        .ok (.inl child)) :
      ParisLineage g (nextEntry parent (CheckedBlockChain.ofImport imported))

/-- No post-terminal origin can be manufactured by merely setting TD high. -/
theorem origin_paris_lineage {g : CheckedBlockChain} {entry : Entry}
    (h : Origin g entry) : entry.phase ≠ .preTerminal → ParisLineage g entry := by
  induction h with
  | genesis hg => simp [genesisEntry]
  | @step parent cb child previous imported ih =>
    intro post
    by_cases hp : parent.phase = .preTerminal
    · have terminal : (nextEntry parent (CheckedBlockChain.ofImport imported)).phase =
          .terminalPow := by
        simp only [nextEntry, hp] at post ⊢
        split <;> simp_all
      exact .terminal (.step previous imported) terminal
    · exact .step (ih hp) hp imported

/-- Static checked import preserves chain identity without a second check. -/
private theorem import_chainId {parent : Entry} {cb : CanonicalBlock} {child : BlockChain}
    (h : addBlockToChainChecked (phaseFork parent.phase) parent.chain cb =
      .ok (.inl child)) :
    (CheckedBlockChain.ofImport h).val.chainId = parent.chain.val.chainId := by
  exact stateTransitionAt_preserves_chainId
    (stateTransitionAt_eq_ok_iff.mpr (addBlockToChainCanonicalE_eq_ok_inl h).2)

theorem origin_chainId {g : CheckedBlockChain} {entry : Entry}
    (h : Origin g entry) : entry.chain.val.chainId = g.val.chainId := by
  induction h with
  | genesis hg => rfl
  | @step parent cb child previous imported ih =>
    rw [nextEntry_chain]
    exact (import_chainId imported).trans ih

/-- Computational structural equality, kept local to fixture ingress. -/
private def headerDecidableEq : DecidableEq Header := by
  intro a b
  cases a
  cases b
  simp only [Header.mk.injEq]
  infer_instance

/-- Only genesis and successful checked imports can populate this ledger. -/
structure Store : Type where
  private mk ::
  private entries : Std.TreeMap B256 Entry compare
  private valid : ∃ g, GenesisAdmitted g ∧
    ∀ key entry, entries[key]? = some entry →
      key = entry.chain.tipHash ∧ Origin g entry

namespace Store

def find? (store : Store) (key : B256) : Option Entry := store.entries[key]?

def init (genesis : CheckedBlockChain) (h : GenesisAdmitted genesis) : Store :=
  ⟨(∅ : Std.TreeMap B256 Entry compare).insert genesis.tipHash (genesisEntry genesis), by
    refine ⟨genesis, h, ?_⟩
    intro key entry he
    rw [Std.TreeMap.getElem?_insert] at he
    split at he
    · have hk : genesis.tipHash = key := Std.compare_eq_iff_eq.mp ‹_›
      cases Option.some.inj he
      exact ⟨hk.symm, .genesis h⟩
    · simp at he⟩

/-- Every visible entry retains admitted-genesis import provenance. -/
theorem find_origin (store : Store) (h : store.find? key = some entry) :
    ∃ g, GenesisAdmitted g ∧ Origin g entry := by
  obtain ⟨g, hg, hv⟩ := store.valid
  exact ⟨g, hg, (hv key entry h).2⟩

theorem find_key (store : Store) (h : store.find? key = some entry) :
    key = entry.chain.tipHash := by
  obtain ⟨g, hg, hv⟩ := store.valid
  exact (hv key entry h).1

theorem find_phase_bounds (store : Store) (h : store.find? key = some entry) :
    match entry.phase with
    | .preTerminal => entry.td < threshold
    | .terminalPow | .pos => threshold ≤ entry.td := by
  obtain ⟨g, _, ho⟩ := store.find_origin h
  exact origin_phase_bounds ho

private def insertAccepted (store : Store) {key : B256} {parent : Entry}
    (found : store.find? key = some parent) {cb : CanonicalBlock} {child : BlockChain}
    (imported : addBlockToChainChecked (phaseFork parent.phase) parent.chain cb =
      .ok (.inl child)) : Store :=
  let entry := nextEntry parent (CheckedBlockChain.ofImport imported)
  ⟨store.entries.insert entry.chain.tipHash entry, by
    obtain ⟨g, hg, hv⟩ := store.valid
    refine ⟨g, hg, ?_⟩
    intro hash value he
    rw [Std.TreeMap.getElem?_insert] at he
    split at he
    · have hk : entry.chain.tipHash = hash := Std.compare_eq_iff_eq.mp ‹_›
      cases Option.some.inj he
      exact ⟨hk.symm, .step (hv key parent found).2 imported⟩
    · exact hv hash value he⟩

private theorem insertAccepted_lookup (store : Store) {key : B256} {parent : Entry}
    (found : store.find? key = some parent) {cb : CanonicalBlock} {child : BlockChain}
    (imported : addBlockToChainChecked (phaseFork parent.phase) parent.chain cb =
      .ok (.inl child)) (hash : B256) :
    (Store.insertAccepted store found imported).find? hash =
      if (nextEntry parent (CheckedBlockChain.ofImport imported)).chain.tipHash = hash
      then some (nextEntry parent (CheckedBlockChain.ofImport imported))
      else store.find? hash := by
  simp only [insertAccepted, find?, Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq]

/-- The original branch anchor is stored with its actual difficulty. -/
theorem init_entry (genesis : CheckedBlockChain) (h : GenesisAdmitted genesis) :
    (init genesis h).find? genesis.tipHash = some (genesisEntry genesis) := by
  simp [init, find?]

/-- Installing the same complete entry twice changes no observable lookup.
This deliberately says nothing about the balancing-tree representation. -/
private theorem overwrite_lookup (entries : Std.TreeMap B256 Entry compare)
    (entry : Entry) (hash : B256) :
    ((entries.insert entry.chain.tipHash entry).insert entry.chain.tipHash entry)[hash]? =
      (entries.insert entry.chain.tipHash entry)[hash]? := by
  simp only [Std.TreeMap.getElem?_insert]
  split <;> rfl

/-- Final lookup retains the existing operational miss, never a scorable verdict. -/
def findLast (store : Store) (hash : B256) : Except ImportFailure CheckedBlockChain :=
  ((store.find? hash).map Entry.chain).toExcept
    (.harness (.text s!"lastblockhash = {hash} names no imported snapshot"))

end Store

/-- The same supplied genesis anchors every entry, rather than a separate
existential anchor being chosen independently for each lookup. -/
def Valid (genesis : CheckedBlockChain) (store : Store) : Prop :=
  GenesisAdmitted genesis ∧ ∀ key entry, store.find? key = some entry →
    key = entry.chain.tipHash ∧ Origin genesis entry

theorem Store.valid_exists (store : Store) : ∃ genesis, Valid genesis store :=
  store.valid

theorem Store.init_valid (genesis : CheckedBlockChain) (h : GenesisAdmitted genesis) :
    Valid genesis (Store.init genesis h) := by
  refine ⟨h, ?_⟩
  intro key entry he
  change ((∅ : Std.TreeMap B256 Entry compare).insert
    genesis.tipHash (genesisEntry genesis))[key]? = some entry at he
  rw [Std.TreeMap.getElem?_insert] at he
  split at he
  · have hk : genesis.tipHash = key := Std.compare_eq_iff_eq.mp ‹_›
    cases Option.some.inj he
    exact ⟨hk.symm, .genesis h⟩
  · simp at he

/-- The header read before parent selection comes from the original bytes. -/
def StructuralHeader (raw : Bytes) (header : Header) : Prop :=
  ∃ headerBlt tail, Bytes.toBLT? raw = some (.list (headerBlt :: tail)) ∧
    headerBlt.toExHeader = .ok header

/-- Acceptance binds original-byte decoding, parent lookup, selected rules,
canonical normalization and the actual checked import in one erased witness. -/
inductive Faithful (store : Store) (raw : Bytes) : CheckedBlockChain → Store → Prop
  | imported {header : Header} {parent : Entry} {rules : ForkRules}
      {block canon : Block} {hash canonHash : B256} {chain : BlockChain}
      (structural : StructuralHeader raw header)
      (found : store.find? header.parentHash = some parent)
      (selected : (phaseFork parent.phase).rules = .ok rules)
      (decoded : rlpToBlockEAt rules raw = .ok (block, hash))
      (sameHeader : block.header = header)
      (normalized : rlpToBlock block.toBLT.toBytes = .ok (canon, canonHash))
      (sameNormalized : canon.header = block.header)
      (accepted : addBlockToChainChecked (phaseFork parent.phase) parent.chain
        (CanonicalBlock.ofDecode normalized) = .ok (.inl chain)) :
      Faithful store raw (CheckedBlockChain.ofImport accepted)
        (Store.insertAccepted store found accepted)

/-- No caller can construct an accepted child independently of its atomic next ledger. -/
structure Accepted (store : Store) (raw : Bytes) : Type where
  private mk ::
  child : CheckedBlockChain
  next : Store
  faithful : Faithful store raw child next

private def missingParent (hash : B256) : BlockRejection :=
  if hash = 0 then .block (.unknownParentZero (.text
    "parent hash is the all-zero hash, which names no block"))
  else .block (.unknownParent (.text s!"parent hash = {hash} names no imported snapshot"))

/-- The only body/import producer. Parent selection precedes fork-relative body
checks. Full structural equality guards fail closed if normalization could ever
change the header that selected the parent; they never switch parent or fork. -/
private def importBody (store : Store) (raw : Bytes) (header : Header)
    (parent : Entry) (structural : StructuralHeader raw header)
    (found : store.find? header.parentHash = some parent) :
    Except ImportFailure (ImportOutcome (Accepted store raw)) :=
  letI := headerDecidableEq
  match selected : (phaseFork parent.phase).rules with
  | .error reason => .error (.support reason)
  | .ok rules =>
    match decoded : rlpToBlockEAt rules raw with
    | .error reason => .ok (.inr (.decode reason))
    | .ok (block, _) =>
      if sameHeader : block.header = header then
        match normalized : rlpToBlock block.toBLT.toBytes with
        | .error _ => .error (.internal (.assertion (.text
          "normalised fixture block does not strictly re-decode")))
        | .ok (canon, _) =>
          if sameNormalized : canon.header = block.header then
            match accepted : addBlockToChainChecked (phaseFork parent.phase) parent.chain
                (CanonicalBlock.ofDecode normalized) with
            | .error failure => .error failure
            | .ok (.inr reason) => .ok (.inr reason)
            | .ok (.inl _) =>
              .ok (.inl ⟨CheckedBlockChain.ofImport accepted,
                Store.insertAccepted store found accepted,
                .imported structural found selected decoded sameHeader normalized sameNormalized accepted⟩)
          else .error (.internal (.assertion (.text
            "normalised fixture block changed the selected header")))
      else .error (.internal (.assertion (.text
        "strict fixture body decode changed the selected header")))

/-- Structural header decode, exact parent lookup, phase-selected body decode,
then the existing static checked importer. Existing typed channels are retained. -/
def evaluate (store : Store) (raw : Bytes) :
    Except ImportFailure (ImportOutcome (Accepted store raw)) :=
  match outer : Bytes.toBLT? raw with
  | none => .ok (.inr (.decode
      (DecodeError.structure "block RLP" "cannot decode the outer RLP item")))
  | some (.list (headerBlt :: tail)) =>
    match decodedHeader : headerBlt.toExHeader with
    | .error reason => .ok (.inr (.decode reason))
    | .ok header =>
      match found : store.find? header.parentHash with
      | none => .ok (.inr (missingParent header.parentHash))
      | some parent => importBody store raw header parent
          ⟨headerBlt, tail, outer, decodedHeader⟩ found
  | some _ => .ok (.inr (.decode (DecodeError.structure "block"
      "expected [header, transactions, ommers, withdrawals] lists")))

/-- Acceptance certifies original-body decoding and checked import under the
same phase-selected fork, with the selected header retained at the child tip. -/
theorem accepted_selected_decode_import {store : Store} {raw : Bytes}
    (result : Accepted store raw) :
    ∃ (header : Header) (parent : Entry) (rules : ForkRules)
      (block canon : Block) (hash canonHash : B256) (chain : BlockChain)
      (normalized : rlpToBlock block.toBLT.toBytes = .ok (canon, canonHash))
      (accepted : addBlockToChainChecked (phaseFork parent.phase) parent.chain
        (CanonicalBlock.ofDecode normalized) = .ok (.inl chain)),
      StructuralHeader raw header ∧ store.find? header.parentHash = some parent ∧
      (phaseFork parent.phase).rules = .ok rules ∧
      rlpToBlockEAt rules raw = .ok (block, hash) ∧
      block.header = header ∧ canon.header = header ∧
      result.child = CheckedBlockChain.ofImport accepted ∧
      result.child.tip = canon := by
  obtain ⟨child, next, faithful⟩ := result
  cases faithful with
  | @imported header parent rules block canon hash canonHash chain structural found
      selected decoded sameHeader normalized sameNormalized accepted =>
    exact ⟨header, parent, rules, block, canon, hash, canonHash, chain,
      normalized, accepted, structural, found, selected, decoded, sameHeader,
      sameNormalized.trans sameHeader, rfl, rfl⟩

/-- The atomic next Store preserves any supplied valid genesis anchor. -/
theorem accepted_preserves_valid {genesis : CheckedBlockChain} {store : Store}
    {raw : Bytes} (result : Accepted store raw) (valid : Valid genesis store) :
    Valid genesis result.next := by
  obtain ⟨child, next, faithful⟩ := result
  cases faithful with
  | @imported header parent rules block canon hash canonHash chain structural found
      selected decoded sameHeader normalized sameNormalized accepted =>
    refine ⟨valid.1, ?_⟩
    intro key entry he
    change (store.entries.insert
      (nextEntry parent (CheckedBlockChain.ofImport accepted)).chain.tipHash
      (nextEntry parent (CheckedBlockChain.ofImport accepted)))[key]? = some entry at he
    rw [Std.TreeMap.getElem?_insert] at he
    split at he
    · have hk : (nextEntry parent (CheckedBlockChain.ofImport accepted)).chain.tipHash =
          key := Std.compare_eq_iff_eq.mp ‹_›
      cases Option.some.inj he
      exact ⟨hk.symm, .step (valid.2 _ _ found).2 accepted⟩
    · exact valid.2 key entry he

theorem evaluate_preserves_valid {genesis : CheckedBlockChain} {store : Store}
    {raw : Bytes} {result : Accepted store raw} (valid : Valid genesis store)
    (_evaluated : evaluate store raw = .ok (.inl result)) :
    Valid genesis result.next := accepted_preserves_valid result valid

/-- Every accepted update derives the complete child entry solely from the
selected parent, preserves all other keys, and never adds difficulty after TTD. -/
theorem accepted_recurrence {store : Store} {raw : Bytes}
    (result : Accepted store raw) :
    ∃ parent : Entry,
      store.find? result.child.tip.header.parentHash = some parent ∧
      result.next.find? result.child.tipHash = some (nextEntry parent result.child) ∧
      (∀ hash, hash ≠ result.child.tipHash →
        result.next.find? hash = store.find? hash) ∧
      (parent.phase = .preTerminal →
        (nextEntry parent result.child).td = parent.td + result.child.tip.header.difficulty ∧
        ((nextEntry parent result.child).phase = .terminalPow ↔
          threshold ≤ parent.td + result.child.tip.header.difficulty)) ∧
      (parent.phase ≠ .preTerminal →
        (nextEntry parent result.child).td = parent.td ∧
        (nextEntry parent result.child).phase = .pos) := by
  obtain ⟨child, next, faithful⟩ := result
  cases faithful with
  | @imported header parent rules block canon hash canonHash chain structural found
      selected decoded sameHeader normalized sameNormalized accepted =>
    refine ⟨parent, ?_, ?_, ?_, nextEntry_pre parent _, nextEntry_post parent _⟩
    · change store.find? canon.header.parentHash = some parent
      rw [sameNormalized, sameHeader]
      exact found
    · rw [Store.insertAccepted_lookup, nextEntry_chain]
      simp
    · intro key hk
      rw [Store.insertAccepted_lookup, nextEntry_chain]
      exact ite_eq_right (Ne.symm hk)

/-- Reinstalling exactly the accepted complete entry is lookup-idempotent.
It does not re-evaluate a candidate against a potentially changed parent. -/
theorem accepted_overwrite_lookup {store : Store} {raw : Bytes}
    (result : Accepted store raw) (hash : B256) :
    ∃ entry : Entry, result.next.find? result.child.tipHash = some entry ∧
      entry.chain = result.child ∧
      (result.next.entries.insert result.child.tipHash entry)[hash]? =
        result.next.find? hash := by
  obtain ⟨child, next, faithful⟩ := result
  cases faithful with
  | @imported header parent rules block canon blockHash canonHash chain structural found
      selected decoded sameHeader normalized sameNormalized accepted =>
    let entry := nextEntry parent (CheckedBlockChain.ofImport accepted)
    refine ⟨entry, ?_, nextEntry_chain _ _, ?_⟩
    · rw [Store.insertAccepted_lookup, nextEntry_chain]
      simp [entry]
    · change ((store.entries.insert entry.chain.tipHash entry).insert
        (CheckedBlockChain.ofImport accepted).tipHash entry)[hash]? =
          (store.entries.insert entry.chain.tipHash entry)[hash]?
      rw [← nextEntry_chain parent (CheckedBlockChain.ofImport accepted)]
      exact Store.overwrite_lookup store.entries entry hash

/-- Apply only the admitted original-genesis contract after shared fixture
canonicality/hash/prestate validation has built the checked snapshot. -/
def init (genesis : CheckedBlockChain) : Except ImportFailure Store :=
  letI : Decidable (GenesisAdmitted genesis) := by
    unfold GenesisAdmitted
    infer_instance
  if h : GenesisAdmitted genesis then .ok (Store.init genesis h)
  else .error (.harness (.text
    "TTD fixture genesis requires number zero and nonzero difficulty below 786432"))

/-- Successful initialization certifies this exact supplied genesis and entry. -/
theorem init_valid {genesis : CheckedBlockChain} {store : Store}
    (initialized : init genesis = .ok store) :
    Valid genesis store ∧
      store.find? genesis.tipHash = some (genesisEntry genesis) := by
  unfold init at initialized
  split at initialized
  · cases Except.ok.inj initialized
    exact ⟨Store.init_valid _ _, Store.init_entry _ _⟩
  · simp at initialized

/-- Failure or rejection cannot mutate any part of the ledger. -/
def adopt (store : Store) {raw : Bytes} :
    Except ImportFailure (ImportOutcome (Accepted store raw)) → Store
  | .ok (.inl accepted) => accepted.next
  | .ok (.inr _) | .error _ => store

theorem adopt_error (store : Store) (raw : Bytes) (failure : ImportFailure) :
    adopt store (raw := raw) (.error failure) = store := rfl

theorem adopt_rejected (store : Store) (raw : Bytes) (reason : BlockRejection) :
    adopt store (raw := raw) (.ok (.inr reason)) = store := rfl

end FixtureTTD
end Jaune
