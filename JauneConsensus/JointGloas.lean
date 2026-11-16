import JauneConsensus.Joint
import JauneConsensus.GloasEnvelope
import JauneConsensus.GloasBlock
import JauneConsensus.GloasTransition

/-!
# The Gloas side of the joint execution–consensus step (goal `eip8282-gloas-cross-layer-v1`, G2)

Under ePBS (EIP-7732) a Gloas block carries only a bid; its payload arrives later in a signed
envelope, and the payload's execution requests are applied by the *next* block, which settles
its parent FULL or EMPTY. This module is the joint model of that, in the frozen design's terms
(Plans `evidence/eip8282-gloas-cross-layer-v1/recon/design.md` §1.2, §2, §3, rev 3):

* `ParentPayload` is what the joint state knows of the payload of the latest block's bid:
  `.landed` (already the execution head, its requests applied), `.withheld` (no envelope), or
  `.delivered env req post` (verified by the engine, `post` its chain, but not yet built upon);
* `GJointState` is the sum of the pre-crossing `JointState` and a Gloas state carrying the
  **built-upon** execution chain and the parent payload; `GBlock` is the matching block sum;
* `engineVerdictG` is Jaune's Amsterdam engine on a Gloas `NewPayloadRequest`: the
  `engineVerdict` checks, with the header's block-access-list hash and slot number filled in,
  the five-list requests compared as the list `Gloas.getExecutionRequestsList`, the BAL compared
  as bytes, and Gloas paired with Amsterdam only;
* `verifyEnvelopeG` is U6's BLS-switched `verifyExecutionPayloadEnvelopeB` with the engine
  `envelopeEngine` (the verdict as a `Bool`), then the list form of the withdrawals check, then
  the engine once more for the chain after the payload; `deliver` records `.delivered`;
* `settleParent` is the execution-side bookkeeping of `process_parent_execution_payload`, keyed
  on the same FULL test (`parentFull`): FULL on `.delivered env` requires the child's
  `parent_execution_requests` to *be* the envelope's (five lists, by value) and installs `post`;
  FULL on `.landed` requires empty requests by value; FULL on `.withheld` is refused; EMPTY
  requires empty requests by value and drops a delivered payload;
* `gloasBlockArm` and `gloasStepWith` are the Gloas→Gloas arm of the step, parametric in
  `processSlots` and in the post-slots block transition; `gloasStep` instantiates them with U5's
  `Gloas.processSlots` and `Gloas.applySignedBlockWith (Gloas.processBlock ctx)`. The beacon-side parent settlement is *inside* Gloas `processBlock`
  (`processParentExecutionPayload` is its first call), so the arm wraps the block transition
  and adds only the execution-side bookkeeping; `Facts/JointGloas.lean` proves the two read the
  same FULL test at the same state;
* `crossingStep` is the Fulu → Gloas crossing (`Gloas.crossFromFulu`, then the block arm over a
  `.landed` parent, FULL required), and `jointStepG` the whole step over `GJointState`/`GBlock`,
  delegating pre-Gloas pairs to `jointStep` and refusing every pairing other than these.

Nothing here changes a pre-Gloas definition.
-/

namespace JauneConsensus

open Jaune

variable {P : Preset}

/-! ## Joint state and blocks -/

/-- What a Gloas joint state knows of the payload of its latest block's bid. -/
inductive ParentPayload (P : Preset) where
  /-- The latest bid's payload is already the execution head and its requests were applied (the
  state `upgrade_to_gloas` leaves). -/
  | landed
  /-- No envelope was delivered for the latest block. -/
  | withheld
  /-- A verified envelope, not yet built upon: `req` is the request the engine accepted and `post`
  the engine's chain after the payload; the joint state's `exec` is **not** advanced. -/
  | delivered (env : Gloas.SignedExecutionPayloadEnvelope P) (req : Gloas.NewPayloadRequest P)
      (post : BlockChain)

/-- The joint state: pre-crossing (the Electra/Fulu `JointState`), or a Gloas beacon state with
the built-upon execution chain and the status of its latest block's payload. -/
inductive GJointState (P : Preset) where
  | pre (s : JointState P)
  | gloas (beacon : Gloas.BeaconState P) (exec : BlockChain) (parent : ParentPayload P)

/-- The built-upon execution chain of either arm. -/
def GJointState.exec : GJointState P → BlockChain
  | .pre s => s.exec
  | .gloas _ exec _ => exec

/-- The Gloas beacon state, if any. -/
def GJointState.gloas? : GJointState P → Option (Gloas.BeaconState P)
  | .pre _ => none
  | .gloas beacon _ _ => some beacon

/-- A joint block: pre-crossing, or Gloas. -/
inductive GBlock (P : Preset) where
  | pre (b : AnySignedBlock P)
  | gloas (b : Gloas.SignedBeaconBlock P)

/-! ## The Gloas payload as an execution block (design.md §3) -/

/-- The payload's transactions as byte strings. -/
def Gloas.ExecutionPayload.txBytes (payload : Gloas.ExecutionPayload P) : List Bytes :=
  payload.transactions.toArray.toList.map (·.bytes.toArray.toList)

/-- The payload's withdrawals as execution withdrawals. -/
def Gloas.ExecutionPayload.executionWithdrawals (payload : Gloas.ExecutionPayload P) :
    List Jaune.Withdrawal :=
  payload.withdrawals.toArray.toList.map Withdrawal.toExecution

/-- The payload's EIP-7928 block access list, as the bytes of its RLP encoding. -/
def Gloas.ExecutionPayload.balBytes (payload : Gloas.ExecutionPayload P) : Bytes :=
  payload.block_access_list.bytes.toArray.toList

/-- The Amsterdam execution header a Gloas payload stands for: `payloadHeader`'s fields, with
`blockAccessListHash := keccak(block_access_list)` (EIP-7928) and `slotNumber := slot_number`
(EIP-7843), which `payloadHeader` leaves `none`. -/
def payloadHeaderG (payload : Gloas.ExecutionPayload P) (parentBeaconRoot : Root)
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
    blockAccessListHash := some payload.balBytes.keccak
    slotNumber := some payload.slot_number.toWord }

/-- The execution block a Gloas `NewPayloadRequest` stands for: the header with the requests as
the list `Gloas.getExecutionRequestsList` (types `0x00`–`0x04`), the transactions through
`payloadTx` (a legacy RLP-list transaction decoded, a typed envelope kept as bytes), no ommers,
the withdrawals. -/
def payloadToBlockG (req : Gloas.NewPayloadRequest P) : Block :=
  { header := payloadHeaderG req.execution_payload req.parent_beacon_block_root
      (Gloas.getExecutionRequestsList req.execution_requests)
    txs := req.execution_payload.txBytes.map payloadTx
    ommers := []
    wds := req.execution_payload.executionWithdrawals }

/-! ## The engine on a Gloas payload -/

/-- Why the Gloas engine refused a payload: one of `engineVerdict`'s reasons, or the block access
list the body run builds differs, as bytes, from the payload's. -/
inductive EngineRejectG where
  | engine (e : EngineReject)
  | blockAccessList

/-- A check that fails with `e`. -/
def guardE {ε : Type} (c : Bool) (e : ε) : Except ε Unit :=
  if c then .ok () else .error e

/-- The configured block transition's verdict as an engine verdict. -/
def transitionVerdict :
    Except RulesLookupError (Except TransitionError BlockChain) → Except EngineReject BlockChain
  | .error e => .error (.forkLookup e)
  | .ok (.error e) => .error (.transition e)
  | .ok (.ok post) => .ok post

/-- `verify_and_notify_new_payload` for a Gloas `NewPayloadRequest`, with the engine's execution
state the chain `exec` under `cfg`: `engineVerdict`'s checks in its order (no empty
transaction, block hash, versioned hashes, chain identity, a fork paired with Gloas, EIP-7934
size, the block transition, the body run producing exactly the request list), then the body
run's block access list equal to the payload's as bytes. On success, the chain after the
payload's block. -/
def engineVerdictG (cfg : ChainConfig) (exec : BlockChain) (req : Gloas.NewPayloadRequest P) :
    Except EngineRejectG BlockChain := do
  let payload := req.execution_payload
  let blk := payloadToBlockG req
  guardE (!payload.txBytes.any List.isEmpty) (.engine .emptyTransaction)
  guardE (decide (blk.header.hash = payload.block_hash)) (.engine .blockHash)
  let hashes ← (blobVersionedHashesOf payload.txBytes).mapError
    (fun e => .engine (.transactionDecode e))
  guardE (decide (hashes = req.versioned_hashes.toArray.toList)) (.engine .versionedHashes)
  (cfg.checkChainId exec).mapError (fun e => .engine (.chainContext e))
  let f ← (cfg.forkAt blk.header.number blk.header.timestamp).mapError
    (fun e => .engine (.forkLookup e))
  guardE (decide (f.consensusFork? = some .gloas)) (.engine (.unpairedFork f))
  (checkBlockRlpSize f.ruleSet.block blk.toBLT.toBytes.length).mapError
    (fun e => .engine (.blockSize e))
  let post ← (transitionVerdict (stateTransitionScheduledE cfg f exec blk)).mapError .engine
  let out ← (applyBody (initBenv f exec blk.header) blk.txs blk.ommers blk.wds).mapError
    (fun e => .engine (.body e))
  guardE (decide (out.2.requests = Gloas.getExecutionRequestsList req.execution_requests))
    (.engine .requestsMismatch)
  guardE (decide (payload.balBytes = out.2.blockAccessList.encode)) .blockAccessList
  pure post

/-- The engine U6's envelope check takes: the Gloas verdict as a `Bool`. -/
def envelopeEngine (cfg : ChainConfig) (exec : BlockChain) : Gloas.NewPayloadRequest P → Bool :=
  fun req => (engineVerdictG cfg exec req).isOk

/-! ## The envelope arm -/

instance {state : Gloas.BeaconState P} {signedEnvelope : Gloas.SignedExecutionPayloadEnvelope P} :
    Decidable (Gloas.WithdrawalsMatchExpected state signedEnvelope) :=
  inferInstanceAs (Decidable (_ = _))

/-- The seam: U6's `verify_execution_payload_envelope` under the BLS switch `bls`, with the
engine `envelopeEngine cfg exec`; then the payload's withdrawals equal to
`payload_expected_withdrawals` as lists; then the engine once more on the same request, for
the chain after the payload. Returns the request and that chain. -/
def verifyEnvelopeG (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (state : Gloas.BeaconState P)
    (exec : BlockChain) (signedEnvelope : Gloas.SignedExecutionPayloadEnvelope P) :
    M (Gloas.NewPayloadRequest P × BlockChain) := do
  Gloas.verifyExecutionPayloadEnvelopeB bls ccfg (envelopeEngine cfg exec) state signedEnvelope
  require (decide (Gloas.WithdrawalsMatchExpected state signedEnvelope))
    "joint step: envelope withdrawals == payload_expected_withdrawals (lists)"
  let req ← Gloas.envelopeNewPayloadRequest state signedEnvelope
  match engineVerdictG cfg exec req with
  | .ok post => pure (req, post)
  | .error _ => throw (.assert "joint step: execution engine")

/-- The envelope arm: a Gloas joint state whose latest block's payload is `.withheld` (the
state the block arm leaves) takes the signed envelope `signedEnvelope`, checked by
`verifyEnvelopeG` against the state and the built-upon chain, and records it as `.delivered`.
The beacon state and `exec` do not move. A `.landed` or `.delivered` parent is refused: an
envelope is only ever for the block just added. -/
def deliver (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (s : GJointState P)
    (signedEnvelope : Gloas.SignedExecutionPayloadEnvelope P) : M (GJointState P) :=
  match s with
  | .pre _ => throw (.assert "joint step: an envelope for a pre-Gloas state")
  | .gloas beacon exec .withheld => do
    let (req, post) ← verifyEnvelopeG cfg ccfg bls beacon exec signedEnvelope
    pure (.gloas beacon exec (.delivered signedEnvelope req post))
  | .gloas _ _ _ =>
    throw (.assert "joint step: an envelope for a block whose payload is not withheld")

/-! ## Parent settlement -/

/-- `process_parent_execution_payload`'s FULL test: the block's bid builds on the parent bid's
block hash. -/
def parentFull (state : Gloas.BeaconState P) (block : Gloas.BeaconBlock P) : Bool :=
  block.body.signed_execution_payload_bid.message.parent_block_hash ==
    state.latest_execution_payload_bid.block_hash

/-- The five empty request lists. -/
def emptyRequestLists :
    List DepositRequest × List WithdrawalRequest × List ConsolidationRequest ×
      List Gloas.BuilderDepositRequest × List Gloas.BuilderExitRequest :=
  ([], [], [], [], [])

/-- How a step settled its parent's payload. -/
inductive ParentSettle (P : Preset) where
  /-- EMPTY: nothing applied; a delivered payload, if any, is orphaned. -/
  | empty
  /-- FULL over a `.landed` parent: the payload already is the head; nothing new is built upon. -/
  | landed
  /-- FULL over a delivered payload: it is built upon, and `post` becomes the chain. -/
  | full (env : Gloas.SignedExecutionPayloadEnvelope P) (req : Gloas.NewPayloadRequest P)
      (post : BlockChain)

/-- Why a parent settlement was refused. -/
inductive SettleReject where
  /-- FULL over a parent whose envelope was withheld (the model of `is_payload_verified`). -/
  | fullOfWithheld
  /-- FULL over a delivered payload, with requests that are not the envelope's. -/
  | requestsMismatch
  /-- FULL over a landed payload, with non-empty requests. -/
  | landedRequestsNonEmpty
  /-- EMPTY, with non-empty requests. -/
  | emptyRequestsNonEmpty

/-- The assert site naming a settlement refusal. -/
def SettleReject.site : SettleReject → String
  | .fullOfWithheld => "joint step: FULL settlement of a withheld payload"
  | .requestsMismatch => "joint step: parent_execution_requests != envelope's execution_requests"
  | .landedRequestsNonEmpty => "joint step: FULL settlement of a landed payload with requests"
  | .emptyRequestsNonEmpty => "joint step: EMPTY settlement with requests"

/-- The execution-side settlement of the parent payload, given the FULL test `full` and the
child's `parent_execution_requests`: the built-upon chain after it, and how it settled. Requests
are compared as values (equal containers are equal five lists,
`ExecutionRequests.lists_eq_lists_iff`), never only by `hash_tree_root`. -/
def settleParent (parent : ParentPayload P) (exec : BlockChain) (full : Bool)
    (childRequests : Gloas.ExecutionRequests) :
    Except SettleReject (BlockChain × ParentSettle P) :=
  if full then
    match parent with
    | .delivered env req post =>
      if childRequests = env.message.execution_requests then
        .ok (post, .full env req post)
      else .error .requestsMismatch
    | .landed =>
      if childRequests = Gloas.ExecutionRequests.empty then .ok (exec, .landed)
      else .error .landedRequestsNonEmpty
    | .withheld => .error .fullOfWithheld
  else
    if childRequests = Gloas.ExecutionRequests.empty then .ok (exec, .empty)
    else .error .emptyRequestsNonEmpty

/-! ## The Gloas block arm (parametric in the slots and block functions) -/

/-- The shape of Gloas `process_slots(state, slot)` (U5: `Gloas.processSlots`). -/
abbrev GloasSlotsFn (P : Preset) := Gloas.BeaconState P → Slot → M (Gloas.BeaconState P)

/-- The shape of the rest of Gloas `state_transition` after `process_slots`: the block signature,
`process_block` and the state-root check (U5: `Gloas.applySignedBlockWith`). -/
abbrev GloasBlockFn (P : Preset) :=
  Gloas.BeaconState P → Gloas.SignedBeaconBlock P → M (Gloas.BeaconState P)

/-- The Gloas→Gloas block arm: `processSlots` to the block's slot (`st0`), the execution-side
settlement keyed on the FULL test at `st0`, then `blockTransition st0 b`, the rest of
`state_transition` (the block signature, `process_block`, which settles the parent on the beacon
side, and the state root). Parametric in both: `gloasStep` instantiates them with U5's
`Gloas.processSlots` and `gloasBlockTransition`, `crossingStep` with `crossingSlots`. -/
def gloasBlockArm (processSlots : GloasSlotsFn P)
    (blockTransition : GloasBlockFn P)
    (beacon : Gloas.BeaconState P) (exec : BlockChain) (parent : ParentPayload P)
    (b : Gloas.SignedBeaconBlock P) : M (Gloas.BeaconState P × BlockChain × ParentSettle P) := do
  let st0 ← processSlots beacon b.message.slot
  let settled ← (settleParent parent exec (parentFull st0 b.message)
    b.message.body.parent_execution_requests).mapError fun r => .assert r.site
  let post ← blockTransition st0 b
  pure (post, settled.1, settled.2)

/-- The end of a Gloas step: the block's own envelope if one is given (`deliver`, always on the
`.withheld` state the block arm leaves), else the block's payload stays `.withheld`. -/
def gloasDeliverOpt (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (post : Gloas.BeaconState P)
    (exec : BlockChain) (env? : Option (Gloas.SignedExecutionPayloadEnvelope P)) :
    M (GJointState P) :=
  match env? with
  | none => pure (.gloas post exec .withheld)
  | some e => deliver cfg ccfg bls (.gloas post exec .withheld) e

/-- The Gloas→Gloas step: the block arm, then the block's own envelope if one is given
(`deliver`), else the block's payload is `.withheld`. -/
def gloasStepWith (processSlots : GloasSlotsFn P)
    (blockTransition : GloasBlockFn P)
    (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (beacon : Gloas.BeaconState P)
    (exec : BlockChain) (parent : ParentPayload P) (b : Gloas.SignedBeaconBlock P)
    (env? : Option (Gloas.SignedExecutionPayloadEnvelope P)) : M (GJointState P) := do
  let r ← gloasBlockArm processSlots blockTransition beacon exec parent b
  gloasDeliverOpt cfg ccfg bls r.1 r.2.1 env?

/-! ## The block arm instantiated with U5 -/

/-- The Gloas processing context of a joint step: the configuration and the BLS switch (the
Gloas `process_block` does not read the mocked `executionValid`). -/
def gloasCtx (ccfg : Config) (bls : Bool) : Ctx := { cfg := ccfg, blsActive := bls }

/-- The rest of Gloas `state_transition` after `process_slots` (U5's `applySignedBlockWith` over
the Gloas `process_block`): the block signature, `process_block` and the state root.
`Gloas.stateTransition_eq` shows `process_slots` followed by this is `Gloas.stateTransition`. -/
def gloasBlockTransition (ctx : Ctx) : GloasBlockFn P :=
  fun st b => Gloas.applySignedBlockWith (Gloas.processBlock ctx) ctx.blsActive st b

/-- The Gloas→Gloas step with U5's `Gloas.processSlots` and post-slots transition. -/
def gloasStep (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (beacon : Gloas.BeaconState P)
    (exec : BlockChain) (parent : ParentPayload P) (b : Gloas.SignedBeaconBlock P)
    (env? : Option (Gloas.SignedExecutionPayloadEnvelope P)) : M (GJointState P) :=
  gloasStepWith (Gloas.processSlots (gloasCtx ccfg bls)) (gloasBlockTransition (gloasCtx ccfg bls))
    cfg ccfg bls beacon exec parent b env?

/-! ## The Fulu → Gloas crossing (design.md §2.4) -/

/-- The first slot of `GLOAS_FORK_EPOCH`, as a natural number (the configured epoch may be the
far-future sentinel, whose slot does not fit a `Slot`). -/
def gloasForkSlot (ccfg : Config) : Nat := ccfg.GLOAS_FORK_EPOCH * P.SLOTS_PER_EPOCH

/-- The slots function of the crossing's block arm: none when the block is at the upgraded
state's slot (the fork slot: `Gloas.processBlockAtSlot`, as the generators' `do_fork` applies
the block), else Gloas `process_slots`. -/
def crossingSlots (ctx : Ctx) : GloasSlotsFn P := fun st slot =>
  if slot == st.slot then pure st else Gloas.processSlots ctx st slot

/-- The crossing step: a Fulu joint state strictly before the Gloas fork slot and a Gloas block
at or after it (G2-3). `Gloas.crossFromFulu` runs the Fulu `process_slots` to the fork slot and
`upgrade_to_gloas`; then the Gloas block arm runs over the parent `.landed` (the synthetic
self-build bid `upgrade_to_gloas` leaves is the execution head, its requests applied in the last
Fulu block). The settlement must be FULL with empty requests (design.md §2.4, derived facts 1–2):
an EMPTY settlement is refused here by name. -/
def crossingStep (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    (beacon : BeaconState P .fulu) (exec : BlockChain) (b : Gloas.SignedBeaconBlock P)
    (env? : Option (Gloas.SignedExecutionPayloadEnvelope P)) : M (GJointState P) := do
  require (decide (beacon.slot.toNat < gloasForkSlot (P := P) ccfg ∧
      gloasForkSlot (P := P) ccfg ≤ b.message.slot.toNat))
    "joint step: a Gloas block crossing from a Fulu state"
  let ctx := gloasCtx ccfg bls
  let upgraded ← Gloas.crossFromFulu ctx beacon
  let r ← gloasBlockArm (crossingSlots ctx) (gloasBlockTransition ctx) upgraded exec .landed b
  match r.2.2 with
  | .landed => gloasDeliverOpt cfg ccfg bls r.1 r.2.1 env?
  | _ => throw (.assert "joint step: the first Gloas block settles its landed parent FULL")

/-! ## The joint step -/

/-- One joint step over the sum state (design.md §2.1):

* a pre-Gloas state and block: the Electra/Fulu `jointStep`, with no envelope and the block
  before the Gloas fork slot;
* a Fulu state and a Gloas block: the crossing (`crossingStep`);
* a Gloas state and block: the Gloas arm (`gloasStep`);
* every other pairing is refused by name (Gloas pairs with Amsterdam only; a pre-Gloas block on a
  Gloas state, or a Gloas block on an Electra state, fails closed). -/
def jointStepG (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (s : GJointState P) (b : GBlock P)
    (env? : Option (Gloas.SignedExecutionPayloadEnvelope P)) : M (GJointState P) :=
  match s, b with
  | .pre s, .pre b => do
    require env?.isNone "joint step: an envelope with a pre-Gloas block"
    require (decide (b.2.message.slot.toNat < gloasForkSlot (P := P) ccfg))
      "joint step: a pre-Gloas block at or after the Gloas fork slot"
    pure (.pre (← jointStep cfg ccfg bls s b))
  | .pre ⟨.fulu, beacon, exec⟩, .gloas b => crossingStep cfg ccfg bls beacon exec b env?
  | .pre _, .gloas _ =>
    throw (.assert "joint step: a Gloas block crossing from a state other than Fulu")
  | .gloas beacon exec parent, .gloas b => gloasStep cfg ccfg bls beacon exec parent b env?
  | .gloas .., .pre _ => throw (.assert "joint step: a pre-Gloas block on a Gloas state")

end JauneConsensus
