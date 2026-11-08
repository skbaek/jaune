import JauneConsensus.ForkChoice

/-!
# Optimistic sync

`sync/optimistic.md` at `v1.6.1`: the `OptimisticStore`, its helpers (`is_optimistic`,
`latest_verified_ancestor`, `is_execution_block`, `is_optimistic_candidate_block`), and the
mechanisms the `sync` vectors exercise:

* "How to optimistically import blocks": `verify_and_notify_new_payload` returns `True` for a
  `VALID` or `NOT_VALIDATED` engine response and `False` for `INVALIDATED`, so an `INVALIDATED`
  block is not imported (`on_block` rejects it in `process_execution_payload`); a
  `NOT_VALIDATED` block is imported only when it is an optimistic candidate.
* The status transitions: `NOT_VALIDATED -> VALID` carries every ancestor to `VALID`;
  `NOT_VALIDATED -> INVALIDATED` carries every descendant to `INVALIDATED`; both leave
  `optimistic_roots`.
* "How to apply `latestValidHash` when payload status is `INVALID`".
* The head: LMD-GHOST over the fork-choice store with `INVALIDATED` blocks removed from the
  block tree (`getHeadExcluding`), as the pyspec test helper `get_opt_head_block_root`
  (`tests/core/pyspec/eth2spec/test/helpers/optimistic_sync.py`) computes it.

The execution engine's responses (`PayloadStatusV1`) are inputs.
-/

namespace JauneConsensus

open Jaune (Bytes B256)

variable {P : Preset} {f : CFork}

/-- `SAFE_SLOTS_TO_IMPORT_OPTIMISTICALLY` (`sync/optimistic.md`, "Constants"). -/
def SAFE_SLOTS_TO_IMPORT_OPTIMISTICALLY : Nat := 128

/-- The `status` of an engine API `PayloadStatusV1`. -/
inductive PayloadStatusKind
  | valid | invalid | syncing | accepted | invalidBlockHash
  deriving DecidableEq, Repr

/-- The alias `NOT_VALIDATED`: `SYNCING` or `ACCEPTED`. -/
def PayloadStatusKind.isNotValidated : PayloadStatusKind → Bool
  | .syncing | .accepted => true
  | _ => false

/-- The alias `INVALIDATED`: `INVALID` or `INVALID_BLOCK_HASH`. -/
def PayloadStatusKind.isInvalidated : PayloadStatusKind → Bool
  | .invalid | .invalidBlockHash => true
  | _ => false

/-- An engine API `PayloadStatusV1` (`validation_error` is diagnostic only and not kept). -/
structure PayloadStatusV1 where
  status : PayloadStatusKind
  latestValidHash : Option Hash32
  deriving DecidableEq, Repr

/-- `OptimisticStore` (`sync/optimistic.md`), with the set of blocks designated `INVALIDATED`
the consensus engine "MUST track". -/
structure OptimisticStore (P : Preset) (f : CFork) where
  optimistic_roots : Std.TreeSet Root compare
  head_block_root : Root
  blocks : RootMap (BeaconBlock P f)
  block_states : RootMap (BeaconState P f)
  invalidated : Std.TreeSet Root compare

/-- The optimistic store at an anchor, as the pyspec test helper `get_optimistic_store` builds
it: no optimistic roots, the anchor as head. -/
def getOptimisticStore (anchorState : BeaconState P f) (anchorBlock : BeaconBlock P f) :
    M (OptimisticStore P f) := do
  require (anchorBlock.state_root == Ssz.hashTreeRoot anchorState) "get_optimistic_store"
  let anchorRoot : Root := Ssz.hashTreeRoot anchorBlock
  pure { optimistic_roots := ∅, head_block_root := anchorRoot,
         blocks := (∅ : RootMap _).insert anchorRoot anchorBlock,
         block_states := (∅ : RootMap _).insert anchorRoot anchorState, invalidated := ∅ }

/-- `is_optimistic(opt_store, block)`. -/
def isOptimistic (optStore : OptimisticStore P f) (block : BeaconBlock P f) : Bool :=
  optStore.optimistic_roots.contains (Ssz.hashTreeRoot block)

/-- `latest_verified_ancestor(opt_store, block)`, its `while True` bounded by the number of
stored blocks plus one. -/
def latestVerifiedAncestor (optStore : OptimisticStore P f) (block : BeaconBlock P f) :
    M (BeaconBlock P f) := do
  let mut block := block
  for _ in [0:optStore.blocks.size + 1] do
    if !isOptimistic optStore block || block.parent_root == zeroRoot then return block
    block ← lookup optStore.blocks block.parent_root "latest_verified_ancestor: opt_store.blocks"
  throw (.assert "latest_verified_ancestor: walk longer than the store")

/-- `block.body.execution_payload == ExecutionPayload()`: every field at its SSZ default. -/
def ExecutionPayload.isDefault (p : ExecutionPayload P) : Bool :=
  p.parent_hash == zeroRoot && p.fee_recipient.toNat == 0 && p.state_root == zeroRoot &&
  p.receipts_root == zeroRoot && p.logs_bloom.toArray.all (· == 0) && p.prev_randao == zeroRoot &&
  p.block_number == U64.zero && p.gas_limit == U64.zero && p.gas_used == U64.zero &&
  p.timestamp == U64.zero && p.extra_data.toArray.isEmpty && p.base_fee_per_gas.toNat == 0 &&
  p.block_hash == zeroRoot && p.transactions.toArray.isEmpty && p.withdrawals.toArray.isEmpty &&
  p.blob_gas_used == U64.zero && p.excess_blob_gas == U64.zero

/-- `is_execution_block(block)`. -/
def isExecutionBlock (block : BeaconBlock P f) : Bool :=
  !block.body.execution_payload.isDefault

/-- `is_optimistic_candidate_block(opt_store, current_slot, block)`. -/
def isOptimisticCandidateBlock (optStore : OptimisticStore P f) (currentSlot : Slot)
    (block : BeaconBlock P f) : M Bool := do
  let parent ← lookup optStore.blocks block.parent_root
    "is_optimistic_candidate_block: opt_store.blocks[block.parent_root]"
  if isExecutionBlock parent then return true
  if (← block.slot.add? (← c64 SAFE_SLOTS_TO_IMPORT_OPTIMISTICALLY) "is_optimistic_candidate_block")
      ≤ currentSlot then return true
  return false

/-- The verdict `verify_and_notify_new_payload` returns for an engine response: `True` for
`VALID` and `NOT_VALIDATED`, `False` for `INVALIDATED`. -/
def PayloadStatusKind.newPayloadVerdict (s : PayloadStatusKind) : Bool := !s.isInvalidated

/-- The ancestors of `root` in the fork-choice block tree, `root` excluded, nearest first. -/
def ancestorsOf (blocks : RootMap (BeaconBlock P f)) (root : Root) : List Root := Id.run do
  let mut out := #[]
  let mut cur := root
  for _ in [0:blocks.size + 1] do
    match blocks.get? cur with
    | none => break
    | some b =>
      if blocks.contains b.parent_root then
        out := out.push b.parent_root
        cur := b.parent_root
      else break
  pure out.toList

/-- `root` and every stored descendant of it. -/
def withDescendants (blocks : RootMap (BeaconBlock P f)) (root : Root) : List Root :=
  root :: (blocks.toList.filterMap fun (r, _) =>
    if (ancestorsOf blocks r).contains root then some r else none)

/-- Transition `roots` to `INVALIDATED`: they leave `optimistic_roots`. -/
def OptimisticStore.invalidate (optStore : OptimisticStore P f) (roots : List Root) :
    OptimisticStore P f :=
  roots.foldl (fun s r =>
    { s with
      invalidated := s.invalidated.insert r
      optimistic_roots := s.optimistic_roots.erase r }) optStore

/-- `invalidBlock` for an `INVALID` response with `latestValidHash` to a block that was not
imported, by the table of "How to apply `latestValidHash` when payload status is `INVALID`": the
chain containing the block is the block followed by its stored ancestors. `none` means the block
in question itself, which is not in the store. -/
def invalidBlockOf (blocks : RootMap (BeaconBlock P f)) (block : BeaconBlock P f)
    (latestValidHash : Option Hash32) : Option Root := Id.run do
  let chain : List (Option Root × BeaconBlock P f) :=
    (none, block) :: ((block.parent_root :: ancestorsOf blocks block.parent_root).filterMap
      fun r => (blocks.get? r).map fun b => (some r, b))
  match latestValidHash with
  | none => pure none
  | some h =>
    if h == zeroRoot then
      -- the first (oldest) block with a non-default payload in the chain
      match (chain.reverse.find? fun (_, b) => isExecutionBlock b) with
      | some (r, _) => pure r
      | none => pure none
    else
      -- the child, within the chain, of the block whose payload has `block_hash == h`;
      -- when there is none, as if `latestValidHash` were `null`
      let rec go : List (Option Root × BeaconBlock P f) → Option Root
        | c :: p :: rest =>
          if p.2.body.execution_payload.block_hash == h then c.1 else go (p :: rest)
        | _ => none
      pure (go chain)

/-- Import `signedBlock` optimistically given the engine's response `status` to its payload.
Returns the stores and whether the block was imported. -/
def onBlockOptimistic (ctx : Ctx) (oracle : DataOracle P) (store : Store P f)
    (optStore : OptimisticStore P f) (status : PayloadStatusV1)
    (signedBlock : SignedBeaconBlock P f) : M (Store P f × OptimisticStore P f × Bool) := do
  let block := signedBlock.message
  let blockRoot : Root := Ssz.hashTreeRoot block
  -- The parent of the block MUST NOT have an `INVALIDATED` execution payload.
  if optStore.invalidated.contains block.parent_root then return (store, optStore, false)
  if status.status.isNotValidated then
    let currentSlot ← getCurrentSlot ctx.cfg store
    if !(← isOptimisticCandidateBlock optStore currentSlot block) then
      return (store, optStore, false)
  match onBlock { ctx with executionValid := status.status.newPayloadVerdict } oracle store signedBlock with
  | .ok store' =>
    let state ← lookup store'.block_states blockRoot "on_block_optimistic: block_states"
    let optStore := { optStore with
      blocks := optStore.blocks.insert blockRoot block
      block_states := optStore.block_states.insert blockRoot state }
    let optStore :=
      if status.status.isNotValidated then
        { optStore with optimistic_roots := optStore.optimistic_roots.insert blockRoot }
      else if status.status == .valid then
        -- NOT_VALIDATED -> VALID carries every ancestor to VALID
        (ancestorsOf store'.blocks blockRoot).foldl
          (fun s r => { s with optimistic_roots := s.optimistic_roots.erase r }) optStore
      else optStore
    pure (store', optStore, true)
  | .error _ =>
    if status.status == .invalid then
      match invalidBlockOf store.blocks block status.latestValidHash with
      | some r => pure (store, optStore.invalidate (withDescendants store.blocks r), false)
      | none => pure (store, optStore, false)
    else pure (store, optStore, false)

/-- The optimistic node's head: `get_head` with `INVALIDATED` blocks removed from the tree. -/
def getOptimisticHead (cfg : Config) (store : Store P f) (optStore : OptimisticStore P f) :
    M Root :=
  getHeadExcluding cfg store (fun r => optStore.invalidated.contains r)

end JauneConsensus
