import JauneConsensus.Block

/-!
# The execution engine, instantiated with Jaune

`verify_and_notify_new_payload` (`specs/electra/beacon-chain.md`, "Execution engine"), with
the engine's execution side given by Jaune's own block transition instead of the mocked
verdict `Ctx.executionValid`. This is the seam between the two layers (goal
`eip7002-cross-layer-v1`, O1). The vector harness keeps the mocked verdict; nothing here
changes `processBlock` or any existing definition.

The engine is the specs' definitional composition, not a model of the Engine API:

* `get_execution_requests_list` turns the block body's `ExecutionRequests` into the list
  `[type ++ ssz_serialize(requests)]` of its non-empty request types;
* the payload converts to a Jaune `Block` (`payloadToBlock`) whose header carries the PoS
  constants, the transactions and withdrawals roots, the parent beacon root and
  `requestsHash := computeRequestsHash list`;
* `is_valid_block_hash`: the converted header hashes to `payload.block_hash`;
* `is_valid_versioned_hashes`: the blob transactions' versioned hashes, in order, are the
  commitments' versioned hashes;
* `notify_new_payload`: the converted block is within EIP-7934's size limit (checked by Jaune's
  block import, outside the block transition, on the block's canonical RLP), is valid on the
  paired execution chain, and the
  requests Jaune's execution produces are `list` itself. The specs state this as validity of
  the payload *and* of the execution requests with respect to the execution state; Engine API
  clients check it through the requests hash, which agrees except on a SHA-256 collision, and
  the Engine API is out of scope here.

The execution side is entered exactly as Blanc's configured histories enter it
(`ChainConfig.checkChainId`, `ChainConfig.forkAt`, `stateTransitionScheduledE`, and
`applyBody` for the produced requests), so each accepted payload is one configured block
transition with its body run.
-/

namespace JauneConsensus

open Jaune

variable {P : Preset}

/-! ## `get_execution_requests_list` -/

/-- `get_execution_requests_list(execution_requests)` (Electra): for each request type whose
list is non-empty, in type order, the type byte followed by the list's SSZ serialization. -/
def getExecutionRequestsList (r : ExecutionRequests P) : ExecutionRequestsList :=
  [(depositRequestType, Ssz.serialize r.deposits),
   (withdrawalRequestType, Ssz.serialize r.withdrawals),
   (consolidationRequestType, Ssz.serialize r.consolidations)].filterMap fun (t, data) =>
    if data.isEmpty then none else some (t :: data)

/-! ## `NewPayloadRequest` -/

/-- `NewPayloadRequest` (Electra), with its `execution_requests` already turned into the list
`get_execution_requests_list` returns: that list is the only form in which the engine reads
them. -/
structure NewPayloadRequest (P : Preset) where
  executionPayload : ExecutionPayload P
  versionedHashes : List B256
  parentBeaconBlockRoot : Root
  executionRequests : ExecutionRequestsList

/-! ## Payload to execution block -/

/-- A consensus `Withdrawal` as Jaune's execution `Withdrawal`. The execution layer carries the
amount in Gwei as a word and multiplies it by `10^9` when crediting. -/
def Withdrawal.toExecution (w : JauneConsensus.Withdrawal) : Jaune.Withdrawal :=
  { globalIndex := w.index.toWord, validatorIndex := w.validator_index.toWord,
    recipient := w.address, amount := w.amount.toNat.toB256 }

/-- The trie key of the `i`-th entry of a block's transactions or withdrawals: `rlp(i)`. -/
def blockTrieKey (i : Nat) : Bytes := (BLT.bytes i.toBytes).toBytes

/-- The transactions root of a payload: the trie of its opaque transactions, keyed by
`rlp(index)`. A transaction's payload bytes are its EIP-2718 encoding (the legacy RLP list, or
the type byte followed by the typed payload), which is what the trie commits to. -/
def transactionsRootOf (txs : List Bytes) : B256 :=
  trie <| Std.TreeMap.ofList (txs.putIndex.map fun (i, tx) => ((blockTrieKey i).toNibbles, tx)) _

/-- The withdrawals root of a list of execution withdrawals, keyed by `rlp(index)`. -/
def withdrawalsRootOf (wds : List Jaune.Withdrawal) : B256 :=
  trie <| Std.TreeMap.ofList
    (wds.putIndex.map fun (i, wd) => ((blockTrieKey i).toNibbles, wd.toBLT.toBytes)) _

/-- The payload's transactions as byte strings. -/
def ExecutionPayload.txBytes (payload : ExecutionPayload P) : List Bytes :=
  payload.transactions.toArray.toList.map (·.toArray.toList)

/-- The payload's withdrawals as execution withdrawals. -/
def ExecutionPayload.executionWithdrawals (payload : ExecutionPayload P) : List Jaune.Withdrawal :=
  payload.withdrawals.toArray.toList.map Withdrawal.toExecution

/-- The execution header a payload stands for (Prague/Osaka shape): the payload's fields, the
proof-of-stake constants (`ommersHash` of no ommers, difficulty 0, nonce 0, `mixHash` =
`prev_randao`), the transactions and withdrawals roots, the parent beacon root, and the
EIP-7685 commitment to `list`. -/
def payloadHeader (payload : ExecutionPayload P) (parentBeaconRoot : Root)
    (list : ExecutionRequestsList) : Header :=
  { parentHash := payload.parent_hash
    ommersHash := emptyOmmerHash
    coinbase := payload.fee_recipient
    stateRoot := payload.state_root
    txsRoot := transactionsRootOf payload.txBytes
    receiptRoot := payload.receipts_root
    bloom := payload.logs_bloom.toArray.toList
    difficulty := 0
    number := payload.block_number.toNat
    gasLimit := payload.gas_limit.toNat
    gasUsed := payload.gas_used.toNat
    timestamp := payload.timestamp.toNat
    extraData := payload.extra_data.toArray.toList
    prevRandao := payload.prev_randao
    nonce := 0
    baseFeePerGas := some payload.base_fee_per_gas.toNat
    withdrawalsRoot := some (withdrawalsRootOf payload.executionWithdrawals)
    blobGasUsed := some payload.blob_gas_used.toNat
    excessBlobGas := some payload.excess_blob_gas.toNat
    parentBeaconBlockRoot := some parentBeaconRoot
    requestsHash := some (computeRequestsHash list)
    blockAccessListHash := none
    slotNumber := none }

/-! ## Payload transactions -/

/-- The legacy reading of one opaque payload transaction. A payload transaction is its EIP-2718
encoding: a legacy transaction is its RLP list (first byte `≥ 0xc0`), anything else is a typed
envelope. `none` for an envelope (or the empty string); for a legacy-shaped string, the strict
legacy decode Jaune's block decoder applies to a list-shaped body item (`BLT.toExBlock` through
`BLT.toExLegacyTx`), after reading the string as one RLP item. -/
def legacyPayloadTx? (bs : Bytes) : Option (Except Jaune.DecodeError Tx) :=
  match bs with
  | b :: _ =>
    if 0xc0 ≤ b then
      some <| match Bytes.toBLT? bs with
        | some (.list ls) => BLT.toExLegacyTx ls
        | _ => .error <| Jaune.DecodeError.structure "legacy transaction"
            "expected one well-formed RLP list"
    else none
  | [] => none

/-- One payload transaction as a block-body slot, the shape `BLT.toExBlock` gives a decoded
fixture block: a legacy transaction that decodes is `.inr` (decoded now, as the block decoder
does); everything else stays undecoded bytes `.inl`, which the transition decodes as a typed
envelope (`decodeTx`). A legacy-shaped string that does not decode stays `.inl`, and the engine
has already refused it at `blobVersionedHashesOf` (`EngineReject.transactionDecode`), before any
block is run. -/
def payloadTx (bs : Bytes) : Bytes ⊕ Tx :=
  match legacyPayloadTx? bs with
  | some (.ok tx) => .inr tx
  | _ => .inl bs

/-- One payload transaction decoded as the execution layer decodes it: a legacy RLP list through
the strict legacy decoder, a typed envelope through `Bytes.toExTx`. -/
def payloadTxDecode (bs : Bytes) : Except TransitionError Tx :=
  match legacyPayloadTx? bs with
  | some r => r.mapError .decode
  | none => bs.toExTx

/-- The execution block a payload stands for: its header, its transactions as block-body slots
(`payloadTx`: legacy transactions decoded, typed envelopes as undecoded bytes decoded by the
transition itself), no ommers, and its withdrawals. -/
def payloadToBlock (req : NewPayloadRequest P) : Block :=
  { header := payloadHeader req.executionPayload req.parentBeaconBlockRoot req.executionRequests
    txs := req.executionPayload.txBytes.map payloadTx
    ommers := []
    wds := req.executionPayload.executionWithdrawals }

/-! ## The engine -/

/-- Why the engine refused a payload. Each constructor is one check of
`verify_and_notify_new_payload`; the execution-side ones carry Jaune's typed reason. -/
inductive EngineReject where
  /-- `b"" in execution_payload.transactions`. -/
  | emptyTransaction
  /-- `is_valid_block_hash`. -/
  | blockHash
  /-- `is_valid_versioned_hashes`: a transaction does not decode. -/
  | transactionDecode (e : TransitionError)
  /-- `is_valid_versioned_hashes`: the hashes differ. -/
  | versionedHashes
  /-- The execution chain's identity is not the configuration's. -/
  | chainContext (e : ChainContextError)
  /-- The configuration selects no execution fork for the block. -/
  | forkLookup (e : RulesLookupError)
  /-- The selected execution fork is not paired with the block's consensus fork. -/
  | unpairedFork (f : Jaune.Fork)
  /-- `notify_new_payload`: EIP-7934, the block's RLP exceeds the fork's size limit. -/
  | blockSize (e : BlockValidationError)
  /-- `notify_new_payload`: the block is not valid on the execution chain. -/
  | transition (e : TransitionError)
  /-- `notify_new_payload`: the block's body does not run (the same run the transition makes). -/
  | body (e : TransitionError)
  /-- `notify_new_payload`: the execution layer's requests are not the block's. -/
  | requestsMismatch

/-- The versioned hashes of a payload's blob transactions, in transaction order, each
transaction's in its own order. Every transaction is decoded (`payloadTxDecode`), so one that
does not decode refuses the payload; a legacy transaction decodes and carries none. -/
def blobVersionedHashesOf (txs : List Bytes) : Except TransitionError (List B256) := do
  let txs ← txs.mapM payloadTxDecode
  pure <| txs.flatMap fun tx => match tx.type with
    | .three _ _ _ _ _ _ hashes => hashes
    | _ => []

/-- `verify_and_notify_new_payload`, with the engine's execution state the execution chain
`exec` under configuration `cfg`, for a block of consensus fork `cf`. On success it returns the
execution chain after the payload's block. -/
def engineVerdict (cfg : ChainConfig) (cf : CFork) (exec : BlockChain)
    (req : NewPayloadRequest P) : Except EngineReject BlockChain := do
  let payload := req.executionPayload
  if payload.txBytes.any List.isEmpty then throw .emptyTransaction
  let blk := payloadToBlock req
  if blk.header.hash != payload.block_hash then throw .blockHash
  let hashes ← (blobVersionedHashesOf payload.txBytes).mapError .transactionDecode
  if hashes != req.versionedHashes then throw .versionedHashes
  (cfg.checkChainId exec).mapError .chainContext
  let f ← (cfg.forkAt blk.header.number blk.header.timestamp).mapError .forkLookup
  if f.consensusFork? != some cf then throw (.unpairedFork f)
  (checkBlockRlpSize f.ruleSet.block blk.toBLT.toBytes.length).mapError .blockSize
  let post ← match stateTransitionScheduledE cfg f exec blk with
    | .error e => throw (.forkLookup e)
    | .ok (.error e) => throw (.transition e)
    | .ok (.ok post) => pure post
  let (_, bout) ← (applyBody (initBenv f exec blk.header) blk.txs blk.ommers blk.wds).mapError .body
  if bout.requests != req.executionRequests then throw .requestsMismatch
  pure post

/-- The `NewPayloadRequest` that `process_execution_payload` builds for `block` (Electra and
later): the payload, the commitments' versioned hashes, the block's parent root, and the
body's execution requests as a list. The spec reads the parent root from
`state.latest_block_header.parent_root`, which `process_block_header` has just set to
`block.parent_root`. -/
def NewPayloadRequest.ofBlock {f : CFork} (block : BeaconBlock P f) : M (NewPayloadRequest P) := do
  let requests ← Gated.read block.body.execution_requests "NewPayloadRequest: execution_requests"
  pure { executionPayload := block.body.execution_payload
         versionedHashes := block.body.blob_kzg_commitments.toArray.toList.map fun c =>
           kzgCommitmentToVersionedHash c.toArray.toList
         parentBeaconBlockRoot := block.parent_root
         executionRequests := getExecutionRequestsList requests }

/-! ## A legacy transaction in the seam

A closed payload carrying one legacy (RLP-list) transaction: the engine's decode accepts it and
contributes no versioned hash, and the converted block carries it decoded (`.inr`), as Jaune's
block decoder does for a fixture block. -/

/-- A legacy transaction's EIP-2718 bytes: the RLP list of nonce 0, gas price 1, gas 21000,
recipient `0x11…11`, value 0, empty data, `v = 27`, `r = 1`, `s = 1`. -/
def legacyTxExample : Bytes :=
  [0xdf, 0x80, 0x01, 0x82, 0x52, 0x08, 0x94] ++ List.replicate 20 0x11 ++
    [0x80, 0x80, 0x1b, 0x01, 0x01]

/-- A mainnet-preset request whose payload carries `legacyTxExample` and nothing else. -/
def legacyPayloadExample : NewPayloadRequest Preset.mainnet :=
  { executionPayload :=
      { parent_hash := zeroRoot, fee_recipient := (0 : Jaune.Adr), state_root := zeroRoot,
        receipts_root := zeroRoot, logs_bloom := ⟨Array.replicate 256 0, Array.size_replicate⟩,
        prev_randao := zeroRoot, block_number := U64.zero, gas_limit := U64.zero,
        gas_used := U64.zero, timestamp := U64.zero, extra_data := ⟨#[], Nat.zero_le _⟩,
        base_fee_per_gas := UIntN.zero, block_hash := zeroRoot,
        transactions := ⟨#[⟨legacyTxExample.toArray, by decide⟩], by decide⟩,
        withdrawals := ⟨#[], Nat.zero_le _⟩, blob_gas_used := U64.zero,
        excess_blob_gas := U64.zero }
    versionedHashes := []
    parentBeaconBlockRoot := zeroRoot
    executionRequests := [] }

#guard blobVersionedHashesOf legacyPayloadExample.executionPayload.txBytes matches .ok []
#guard (payloadToBlock legacyPayloadExample).txs matches [.inr _]

end JauneConsensus
