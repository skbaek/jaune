-- ChainStore.lean : the parent-hash-indexed store of immutable `BlockChain`
-- snapshots used by the fixture runner.
--
-- Like `FixtureException`, this module is fixture-runner infrastructure, not
-- EVM semantics: it is imported by `Main.lean` only, and deliberately not from
-- the `Jaune` library root, so that no proof client depends on it.
--
-- The old runner treats a fixture's blocks as one linear chain, so block N is
-- always evaluated against the chain left by block N-1, whatever parent block
-- N actually names. That cannot represent competing branches: in
-- `UncleFromSideChain` a block must extend a sibling of the current tip, and
-- under the linear model it is judged against the wrong prestate. This store
-- fixes the model: every successfully imported block leaves behind an
-- immutable `BlockChain` snapshot indexed by the hash of its tip header, and a
-- decoded block is evaluated against the snapshot named by its own
-- `header.parentHash`. Keeping whole snapshots is cheap for these persistent
-- Lean values and avoids ever reconstructing state at a fork point.
--
-- Invariants:
--   * every key is the keccak of its snapshot's tip block header
--     (`BlockChain.tipHash?`), so lookup by `parentHash` or by the fixture's
--     `lastblockhash` is exact;
--   * a rejected block inserts nothing (`addResult` on an `.error` is the
--     identity), so failed candidates cannot disturb any branch;
--   * parentage is decided by `header.parentHash` alone -- the fixture's
--     advisory `chainname` may appear in diagnostics but never in lookups.
--
-- The store is keyed with the existing `Ord B256` order via `Std.TreeMap`;
-- deliberately no `Hashable B256` instance is introduced for the harness.

import Jaune.FixtureException

/-- The hash of a chain's tip block header: the key under which this snapshot
is (or would be) stored. `none` only for a chain with no blocks at all, which
the runner never constructs (genesis is always block zero). -/
def BlockChain.tipHash? (chain : BlockChain) : Option B256 :=
  chain.blocks.getLast?.map fun b => (Header.toBLT b.header).toBytes.keccak

/-- Immutable `BlockChain` snapshots indexed by the hash of their tip block
header. -/
structure ChainStore : Type where
  snapshots : Std.TreeMap B256 BlockChain compare

namespace ChainStore

/-- Initialize the store with the genesis snapshot under its hash. The caller
passes the hash it has already verified against the fixture's declared genesis
header hash and the recomputed keccak; the store trusts that verification. -/
def init (genesisHash : B256) (genesis : BlockChain) : ChainStore :=
  ⟨Std.TreeMap.empty.insert genesisHash genesis⟩

/-- The snapshot stored under `hash`, if any. -/
def find? (store : ChainStore) (hash : B256) : Option BlockChain :=
  store.snapshots.get? hash

/-- The number of stored snapshots. -/
def size (store : ChainStore) : Nat :=
  store.snapshots.size

/-- Insert a successfully imported child snapshot under its tip hash. Inserting
the same hash twice replaces the snapshot, which is harmless: equal tip hashes
mean equal tip headers, and a re-imported block reproduces the same snapshot. -/
def insert (store : ChainStore) (tipHash : B256) (chain : BlockChain) : ChainStore :=
  ⟨store.snapshots.insert tipHash chain⟩

/-- The parent snapshot a decoded block must be evaluated against: the one
stored under the block's own `header.parentHash`.

A miss is an explicit unknown-parent failure carrying the exact Step 6/9
producer tag, so the runner can score it against the fixture's expected
identities: the all-zero parent hash names no block at all
(`BlockException.UNKNOWN_PARENT_ZERO`), while any other missing hash names a
block this store has not imported (`BlockException.UNKNOWN_PARENT`). -/
def findParent (store : ChainStore) (parentHash : B256) : Except String BlockChain :=
  match store.find? parentHash with
  | some chain => .ok chain
  | none =>
    if parentHash = 0 then
      .error
        s!"{unknownParentZeroTag} : parent hash is the all-zero hash, \
           which names no block"
    else
      .error
        s!"{unknownParentTag} : parent hash = {parentHash} names no \
           imported snapshot"

/-- Fold one block-evaluation outcome into the store. A successful import
inserts the child snapshot under its tip hash; a rejected block inserts
nothing, so the store -- and therefore every existing branch -- is unchanged by
construction. The error is passed through untouched for the caller to classify
against the fixture's expected identities. -/
def addResult (store : ChainStore) :
  Except String (B256 × BlockChain) → ChainStore
  | .ok ⟨tipHash, chain⟩ => store.insert tipHash chain
  | .error _ => store

/-- The final snapshot named by the fixture's `lastblockhash`, whose tip hash
and post-state root the runner must always check. A miss here is a runner-level
failure, not a consensus rejection: it deliberately carries no canonical
exception tag, so it can never be scored as an expected block exception. -/
def findLast (store : ChainStore) (lastBlockHash : B256) : Except String BlockChain :=
  (store.find? lastBlockHash).toExcept
    s!"ERROR : lastblockhash = {lastBlockHash} names no imported snapshot"

end ChainStore

----------------- CHAIN STORE REGRESSION CHECKS ------------------

-- A pure synthetic fork scenario: the snapshots are built directly from
-- hand-made headers rather than by running state transitions, because what is
-- under test is the store's parentage model, not the EVM. The shape is the one
-- `UncleFromSideChain` needs: genesis has children A1 and B1, A2 extends A1,
-- B2 extends B1, and a candidate B3 is rejected.
--
--        genesis ── A1 ── A2
--              └─── B1 ── B2   (candidate B3 rejected)

/-- A minimal header whose identity is pinned by its parent hash, height, and a
one-byte `extraData` tag; everything else is zero. Distinct tags give distinct
keccak hashes, which is all the store looks at. -/
private def synthHeader (parentHash : B256) (number : Nat) (tag : Bytes) : Header :=
  { parentHash := parentHash
    ommersHash := 0
    coinbase := 0
    stateRoot := 0
    txsRoot := 0
    receiptRoot := 0
    bloom := []
    difficulty := 0
    number := number
    gasLimit := 0
    gasUsed := 0
    timestamp := 0
    extraData := tag
    prevRandao := 0
    nonce := 0
    baseFeePerGas := 0
    withdrawalsRoot := 0
    blobGasUsed := 0
    excessBlobGas := 0
    parentBeaconBlockRoot := 0
    requestsHash := none }

private def synthBlock (parentHash : B256) (number : Nat) (tag : Bytes) : Block :=
  { header := synthHeader parentHash number tag, txs := [], ommers := [], wds := [] }

private def synthHash (b : Block) : B256 :=
  (Header.toBLT b.header).toBytes.keccak

private def chainOf (blocks : List Block) : BlockChain :=
  { blocks := blocks, state := .empty, chainId := 1 }

/-- The tag trail of a snapshot: enough to tell every synthetic snapshot from
every other one in a decidable `#guard`. -/
private def tagsOf (chain : BlockChain) : List Bytes :=
  chain.blocks.map (fun b => b.header.extraData)

private def gB : Block := synthBlock 0 0 [0x60]
private def gH : B256 := synthHash gB
private def a1B : Block := synthBlock gH 1 [0xA1]
private def a1H : B256 := synthHash a1B
private def b1B : Block := synthBlock gH 1 [0xB1]
private def b1H : B256 := synthHash b1B
private def a2B : Block := synthBlock a1H 2 [0xA2]
private def a2H : B256 := synthHash a2B
private def b2B : Block := synthBlock b1H 2 [0xB2]
private def b2H : B256 := synthHash b2B
private def b3B : Block := synthBlock b2H 3 [0xB3]
private def b3H : B256 := synthHash b3B

-- The synthetic hashes are pairwise distinct, so the two branches and the
-- rejected candidate cannot collide in the store.
#guard ([gH, a1H, b1H, a2H, b2H, b3H].eraseDups).length = 6

private def gC : BlockChain := chainOf [gB]
private def a1C : BlockChain := chainOf [gB, a1B]
private def b1C : BlockChain := chainOf [gB, b1B]
private def a2C : BlockChain := chainOf [gB, a1B, a2B]
private def b2C : BlockChain := chainOf [gB, b1B, b2B]

private def store0 : ChainStore := .init gH gC
private def store1 : ChainStore := (store0.insert a1H a1C).insert b1H b1C
private def store2 : ChainStore := (store1.insert a2H a2C).insert b2H b2C

/-- The snapshot under `hash`, read as its tag trail. -/
private def findTags (store : ChainStore) (hash : B256) : Option (List Bytes) :=
  (store.find? hash).map tagsOf

/-- `r` is a rejection whose error classifies to exactly the canonical identity
`e`. -/
private def rejectsAs (r : Except String BlockChain) (e : FixtureException) : Bool :=
  match r with
  | .error msg => FixtureException.classify msg == some e
  | .ok _ => false

-- Initialization: exactly the genesis snapshot, stored under its verified hash.
#guard store0.size = 1
#guard findTags store0 gH == some [[0x60]]

-- Both of genesis's children find genesis -- not "the current tip" -- as their
-- parent, and each fork block finds its own branch's snapshot.
#guard (store2.findParent gH).toOption.map tagsOf == some [[0x60]]
#guard (store2.findParent a1H).toOption.map tagsOf == some [[0x60], [0xA1]]
#guard (store2.findParent b1H).toOption.map tagsOf == some [[0x60], [0xB1]]

-- Looking up A2 and B2 yields different snapshots: the branches stay separate.
#guard findTags store2 a2H == some [[0x60], [0xA1], [0xA2]]
#guard findTags store2 b2H == some [[0x60], [0xB1], [0xB2]]
#guard findTags store2 a2H != findTags store2 b2H

-- The key invariant: every stored snapshot sits under the keccak of its own
-- tip header.
#guard [gH, a1H, b1H, a2H, b2H].all fun h =>
  ((store2.find? h).bind BlockChain.tipHash?) == some h

-- Rejecting candidate B3 leaves the store -- and in particular B2's branch --
-- unchanged: nothing appears under B3's hash, no snapshot is disturbed, and
-- the count is what it was.
private def store3 : ChainStore :=
  store2.addResult (.error s!"{intrinsicGasTooLowTag} : synthetic rejection of B3")

#guard store3.size = store2.size
#guard (store3.find? b3H).isNone
#guard findTags store3 b2H == findTags store2 b2H
#guard findTags store3 b2H == some [[0x60], [0xB1], [0xB2]]
#guard findTags store3 a2H == findTags store2 a2H

-- Had B3 been valid, the same fold would have added exactly its snapshot.
private def store3' : ChainStore :=
  store2.addResult (.ok ⟨b3H, chainOf [gB, b1B, b2B, b3B]⟩)

#guard store3'.size = store2.size + 1
#guard findTags store3' b3H == some [[0x60], [0xB1], [0xB2], [0xB3]]
#guard findTags store3' b2H == findTags store2 b2H

-- Unknown parents fail explicitly with the exact Step 6/9 identities: the
-- all-zero hash is its own reason, and any other missing hash is
-- `UNKNOWN_PARENT`. Both are failures, never silent fallbacks to some tip.
#guard rejectsAs (store2.findParent 0) .blockUnknownParentZero
#guard rejectsAs (store2.findParent b3H) .blockUnknownParent
#guard (store2.findParent 0).toOption.isNone
#guard (store2.findParent b3H).toOption.isNone

-- Final lookup by the fixture's `lastblockhash`: an imported hash yields its
-- exact snapshot; a missing one is a runner-level failure that classifies to
-- no canonical identity, so it can never satisfy an expected exception.
#guard (store2.findLast b2H).toOption.map tagsOf == some [[0x60], [0xB1], [0xB2]]
#guard (store2.findLast a2H).toOption.map tagsOf == some [[0x60], [0xA1], [0xA2]]
#guard (store2.findLast b3H).toOption.isNone
#guard
  match store2.findLast b3H with
  | .error msg => (FixtureException.classify msg).isNone
  | .ok _ => false

-- Re-inserting an existing hash replaces rather than duplicates.
#guard ((store2.insert a2H a2C).size) = store2.size
#guard findTags (store2.insert a2H a2C) a2H == findTags store2 a2H
