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
-- The snapshots are *checked* ones: nonempty, state-canonical, with hash-linked
-- retained history and a world their tip header commits to. That integrity is
-- established once, at genesis ingress, and carried by proof through every
-- import, so no snapshot in this store ever costs a second state-root
-- computation (P0.2).
--
-- Invariants:
--   * every key is the keccak of its snapshot's tip block header, so lookup by
--     `parentHash` or by the fixture's `lastblockhash` is exact. Since Step 6
--     this is structural rather than documentary: the store holds
--     `CheckedBlockChain` values, whose tip is a field, and `init`/`insert`
--     derive the key from that tip instead of accepting one
--     (`CheckedBlockChain.tipHash?_val`);
--   * a rejected block inserts nothing (`addResult` on an `.error` is the
--     identity), so failed candidates cannot disturb any branch;
--   * parentage is decided by `header.parentHash` alone -- the fixture's
--     advisory `chainname` may appear in diagnostics but never in lookups.
--
-- The store is keyed with the existing `Ord B256` order via `Std.TreeMap`;
-- deliberately no `Hashable B256` instance is introduced for the harness.

import Jaune.FixtureException

namespace Jaune

open Jaune

/-- The hash of a chain's tip block header: the key under which this snapshot
is (or would be) stored. `none` only for a chain with no blocks at all, which
a checked snapshot can never be. -/
def BlockChain.tipHash? (chain : BlockChain) : Option Hash32 :=
  chain.blocks.getLast?.map fun b => (Header.toRlpItem b.header).toBytes.keccak

/-- Invariant 1, now structural: a checked snapshot's derived key is the
keccak of the tip header it is proved to end with. -/
theorem CheckedBlockChain.tipHash?_val (cc : CheckedBlockChain) :
    cc.val.tipHash? = some cc.tipHash := by
  unfold BlockChain.tipHash? CheckedBlockChain.tipHash
  rw [cc.tip_is_last]
  rfl

/-- Immutable checked snapshots indexed by the hash of their tip block
header. -/
structure ChainStore : Type where
  snapshots : Std.TreeMap Hash32 CheckedBlockChain compare

namespace ChainStore

/-- Initialize the store with the genesis snapshot under its own derived key.

P0.2 item 5: there is no caller-supplied key any more. The genesis snapshot is
a `CheckedBlockChain`, so its tip -- and therefore its key -- is a field of the
value being stored, and no verification is delegated to the caller. -/
def init (genesis : CheckedBlockChain) : ChainStore :=
  ⟨Std.TreeMap.empty.insert genesis.tipHash genesis⟩

/-- The snapshot stored under `hash`, if any. -/
def find? (store : ChainStore) (hash : Hash32) : Option CheckedBlockChain :=
  store.snapshots.get? hash

/-- The number of stored snapshots. -/
def size (store : ChainStore) : Nat :=
  store.snapshots.size

/-- Insert a successfully imported child snapshot under its own derived tip
hash. Inserting the same hash twice replaces the snapshot, which is harmless:
equal tip hashes mean equal tip headers, and a re-imported block reproduces the
same snapshot. -/
def insert (store : ChainStore) (chain : CheckedBlockChain) : ChainStore :=
  ⟨store.snapshots.insert chain.tipHash chain⟩

/-- The parent snapshot a decoded block must be evaluated against: the one
stored under the block's own `header.parentHash`.

A miss is an explicit typed unknown-parent rejection, so the runner can score
it against the fixture's expected identities by constructor: the all-zero
parent hash names no block at all (`BlockException.UNKNOWN_PARENT_ZERO`),
while any other missing hash names a block this store has not imported
(`BlockException.UNKNOWN_PARENT`). The rendered diagnostics are byte-for-byte
the Step 6/9 ones. -/
def findParent (store : ChainStore) (parentHash : Hash32) :
    Except BlockValidationError CheckedBlockChain :=
  match store.find? parentHash with
  | some chain => .ok chain
  | none =>
    if parentHash = 0 then
      .error <| .unknownParentZero <| .text
        s!"parent hash is the all-zero hash, \
           which names no block"
    else
      .error <| .unknownParent <| .text
        s!"parent hash = {parentHash} names no \
           imported snapshot"

/-- Fold one block-evaluation outcome into the store. A successful import
inserts the child snapshot under its tip hash; a rejected block inserts
nothing, so the store -- and therefore every existing branch -- is unchanged by
construction. The rejection reason is not consumed here: the caller scores it
against the fixture's expected identities by constructor. -/
def addResult (store : ChainStore) :
  ImportOutcome CheckedBlockChain → ChainStore
  | .inl chain => store.insert chain
  | .inr _ => store

/-- The final snapshot named by the fixture's `lastblockhash`, whose tip hash
and post-state root the runner must always check. A miss here is a
harness-level operational failure, not a consensus rejection: `ImportFailure`
has no fixture identity by type, so it can never be scored as an expected
block exception. The render is byte-for-byte the old `ERROR : ...` line. -/
def findLast (store : ChainStore) (lastBlockHash : Hash32) :
    Except ImportFailure CheckedBlockChain :=
  (store.find? lastBlockHash).toExcept
    (.harness (.text s!"lastblockhash = {lastBlockHash} names no imported snapshot"))

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
one-byte `extraData` tag; everything else is the neutral value.

Two fields are no longer free: the bloom is the 256-byte string every
wire-representable header carries, and the state root is the root of the empty
world these synthetic snapshots pair with. That is P0.2 item 7 -- the fixtures
satisfy the checked predicate for real, rather than the production store
gaining a bypass for them. -/
private def syntheticHeader (parentHash : Hash32) (number : Nat) (tag : Bytes) : Header :=
  { parentHash := parentHash
    ommersHash := 0
    coinbase := 0
    stateRoot := State.root (Std.TreeMap.empty : State)
    transactionsRoot := 0
    receiptsRoot := 0
    logsBloom := List.replicate 256 (0 : UInt8)
    difficulty := 0
    number := number
    gasLimit := 0
    gasUsed := 0
    timestamp := 0
    extraData := tag
    prevRandao := 0
    nonce := 0
    baseFeePerGas := some 0
    withdrawalsRoot := some 0
    blobGasUsed := some 0
    excessBlobGas := some 0
    parentBeaconBlockRoot := some 0
    requestsHash := none
    blockAccessListHash := none
    slotNumber := none }

private def syntheticBlock (parentHash : Hash32) (number : Nat) (tag : Bytes) : Block :=
  { header := syntheticHeader parentHash number tag, transactions := [], ommers := [], withdrawals := [] }

private def syntheticBlockHash (b : Block) : Hash32 :=
  (Header.toRlpItem b.header).toBytes.keccak

private def chainOf (blocks : List Block) : BlockChain :=
  { blocks := blocks, state := .empty, chainId := 1 }

/-- The checked snapshot of a synthetic chain. Every one of these passes the
real checker: consecutive numbering, hash-linked headers, wire-representable
headers, a canonical (empty) world, and a tip whose declared state root is
that world's. -/
private def checkedOf (blocks : List Block) : Option CheckedBlockChain :=
  (chainOf blocks).check

/-- The tag trail of a snapshot: enough to tell every synthetic snapshot from
every other one in a decidable `#guard`. -/
private def tagsOf (chain : BlockChain) : List Bytes :=
  chain.blocks.map (fun b => b.header.extraData)

private def genesisBlock : Block := syntheticBlock 0 0 [0x60]
private def genesisHash : Hash32 := syntheticBlockHash genesisBlock
private def shortBranchBlock1 : Block := syntheticBlock genesisHash 1 [0xA1]
private def shortBranchHash1 : Hash32 := syntheticBlockHash shortBranchBlock1
private def longBranchBlock1 : Block := syntheticBlock genesisHash 1 [0xB1]
private def longBranchHash1 : Hash32 := syntheticBlockHash longBranchBlock1
private def shortBranchBlock2 : Block := syntheticBlock shortBranchHash1 2 [0xA2]
private def shortBranchHash2 : Hash32 := syntheticBlockHash shortBranchBlock2
private def longBranchBlock2 : Block := syntheticBlock longBranchHash1 2 [0xB2]
private def longBranchHash2 : Hash32 := syntheticBlockHash longBranchBlock2
private def longBranchBlock3 : Block := syntheticBlock longBranchHash2 3 [0xB3]
private def longBranchHash3 : Hash32 := syntheticBlockHash longBranchBlock3

-- The synthetic hashes are pairwise distinct, so the two branches and the
-- rejected candidate cannot collide in the store.
#guard ([genesisHash, shortBranchHash1, longBranchHash1, shortBranchHash2, longBranchHash2, longBranchHash3].eraseDups).length = 6

-- Every synthetic snapshot is built through the real checker. There is no
-- test-only constructor and no production bypass: if one of these chains
-- failed retained-history validity or tip/root agreement, `checkedOf` would
-- return `none` and the guards below would fail rather than skip.
private def genesisChain : Option CheckedBlockChain := checkedOf [genesisBlock]
private def shortBranchChain1 : Option CheckedBlockChain := checkedOf [genesisBlock, shortBranchBlock1]
private def longBranchChain1 : Option CheckedBlockChain := checkedOf [genesisBlock, longBranchBlock1]
private def shortBranchChain2 : Option CheckedBlockChain := checkedOf [genesisBlock, shortBranchBlock1, shortBranchBlock2]
private def longBranchChain2 : Option CheckedBlockChain := checkedOf [genesisBlock, longBranchBlock1, longBranchBlock2]
private def longBranchChain3 : Option CheckedBlockChain := checkedOf [genesisBlock, longBranchBlock1, longBranchBlock2, longBranchBlock3]

#guard [genesisChain, shortBranchChain1, longBranchChain1, shortBranchChain2, longBranchChain2, longBranchChain3].all Option.isSome
-- The checker refuses a synthetic chain whose numbering or links are broken,
-- so the guards above are evidence rather than coincidence.
#guard (checkedOf [genesisBlock, shortBranchBlock2]).isNone
#guard (checkedOf [shortBranchBlock1]).isNone

/-- Every key is derived from the snapshot being stored. -/
private def store0? : Option ChainStore := genesisChain.map ChainStore.init

private def store2? : Option ChainStore := do
  let g ← genesisChain
  let a1 ← shortBranchChain1
  let b1 ← longBranchChain1
  let a2 ← shortBranchChain2
  let b2 ← longBranchChain2
  pure (((((ChainStore.init g).insert a1).insert b1).insert a2).insert b2)

/-- The snapshot under `hash`, read as its tag trail. -/
private def findTags (store : ChainStore) (hash : Hash32) : Option (List Bytes) :=
  (store.find? hash).map (fun cc => tagsOf cc.val)

private def findTags? (store? : Option ChainStore) (hash : Hash32) :
    Option (List Bytes) :=
  store?.bind (fun store => findTags store hash)

/-- `r` is a rejection whose typed reason classifies to exactly the canonical
identity `e`. -/
private def rejectsAs (r : Except BlockValidationError CheckedBlockChain)
    (e : FixtureException) : Bool :=
  match r with
  | .error reason => FixtureException.ofBlockValidationError reason == some e
  | .ok _ => false

-- Initialization: exactly the genesis snapshot, under the key the snapshot
-- itself determines. No hash is supplied.
#guard store0?.map ChainStore.size == some 1
#guard findTags? store0? genesisHash == some [[0x60]]

-- Both of genesis's children find genesis -- not "the current tip" -- as their
-- parent, and each fork block finds its own branch's snapshot.
#guard store2?.map (fun s => (s.findParent genesisHash).toOption.map (fun cc => tagsOf cc.val))
  == some (some [[0x60]])
#guard store2?.map (fun s => (s.findParent shortBranchHash1).toOption.map (fun cc => tagsOf cc.val))
  == some (some [[0x60], [0xA1]])
#guard store2?.map (fun s => (s.findParent longBranchHash1).toOption.map (fun cc => tagsOf cc.val))
  == some (some [[0x60], [0xB1]])

-- Looking up A2 and B2 yields different snapshots: the branches stay separate.
#guard findTags? store2? shortBranchHash2 == some [[0x60], [0xA1], [0xA2]]
#guard findTags? store2? longBranchHash2 == some [[0x60], [0xB1], [0xB2]]
#guard findTags? store2? shortBranchHash2 != findTags? store2? longBranchHash2

-- The key invariant, now structural: every stored snapshot sits under the
-- keccak of its own tip header, because that is the only key `insert` can use.
#guard store2?.map (fun s => [genesisHash, shortBranchHash1, longBranchHash1, shortBranchHash2, longBranchHash2].all fun h =>
  ((s.find? h).map CheckedBlockChain.tipHash) == some h) == some true
#guard store2?.map (fun s => [genesisHash, shortBranchHash1, longBranchHash1, shortBranchHash2, longBranchHash2].all fun h =>
  ((s.find? h).bind (fun cc => cc.val.tipHash?)) == some h) == some true

-- Rejecting candidate B3 leaves the store -- and in particular B2's branch --
-- unchanged: nothing appears under B3's hash, no snapshot is disturbed, and
-- the count is what it was.
private def store3? : Option ChainStore :=
  store2?.map (fun s =>
    s.addResult (.inr (.transaction
      (.intrinsicGasTooLow (.text "synthetic rejection of B3")))))

#guard store3?.map ChainStore.size == store2?.map ChainStore.size
#guard store3?.map (fun s => (s.find? longBranchHash3).isNone) == some true
#guard findTags? store3? longBranchHash2 == findTags? store2? longBranchHash2
#guard findTags? store3? longBranchHash2 == some [[0x60], [0xB1], [0xB2]]
#guard findTags? store3? shortBranchHash2 == findTags? store2? shortBranchHash2

-- Had B3 been valid, the same fold would have added exactly its snapshot --
-- under the key its own checked tip determines.
private def store3'? : Option ChainStore := do
  let s ← store2?
  let b3 ← longBranchChain3
  pure (s.addResult (.inl b3))

#guard store3'?.map ChainStore.size
  == store2?.map (fun s => ChainStore.size s + 1)
#guard findTags? store3'? longBranchHash3 == some [[0x60], [0xB1], [0xB2], [0xB3]]
#guard findTags? store3'? longBranchHash2 == findTags? store2? longBranchHash2

-- Unknown parents fail explicitly with the exact Step 6/9 identities: the
-- all-zero hash is its own reason, and any other missing hash is
-- `UNKNOWN_PARENT`. Both are failures, never silent fallbacks to some tip.
#guard store2?.map (fun s => rejectsAs (s.findParent 0) .blockUnknownParentZero)
  == some true
#guard store2?.map (fun s => rejectsAs (s.findParent longBranchHash3) .blockUnknownParent)
  == some true
#guard store2?.map (fun s => (s.findParent 0).toOption.isNone) == some true
#guard store2?.map (fun s => (s.findParent longBranchHash3).toOption.isNone) == some true

-- Final lookup by the fixture's `lastblockhash`: an imported hash yields its
-- exact snapshot; a missing one is a runner-level failure that classifies to
-- no canonical identity, so it can never satisfy an expected exception.
#guard store2?.map (fun s => (s.findLast longBranchHash2).toOption.map (fun cc => tagsOf cc.val))
  == some (some [[0x60], [0xB1], [0xB2]])
#guard store2?.map (fun s => (s.findLast shortBranchHash2).toOption.map (fun cc => tagsOf cc.val))
  == some (some [[0x60], [0xA1], [0xA2]])
#guard store2?.map (fun s => (s.findLast longBranchHash3).toOption.isNone) == some true
-- A `findLast` miss is an `ImportFailure`, which has no classification arm at
-- all; the guard pins the constructor and its byte-identical render.
#guard store2?.map (fun s =>
  match s.findLast longBranchHash3 with
  | .error (.harness _) => true
  | _ => false) == some true
#guard store2?.map (fun s =>
  match s.findLast longBranchHash3 with
  | .error f => f.render ==
      s!"ERROR : lastblockhash = {longBranchHash3} names no imported snapshot"
  | .ok _ => false) == some true

-- Re-inserting an existing snapshot replaces rather than duplicates.
#guard (do let s ← store2?; let a2 ← shortBranchChain2; pure (s.insert a2).size)
  == store2?.map ChainStore.size
#guard (do let s ← store2?; let a2 ← shortBranchChain2; pure (findTags (s.insert a2) shortBranchHash2))
  == some (findTags? store2? shortBranchHash2)

end Jaune
