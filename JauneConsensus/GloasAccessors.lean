import JauneConsensus.ContainersGloas
import JauneConsensus.Signing
import JauneConsensus.Block

/-!
# Gloas accessors (goal `eip8282-gloas-cross-layer-v1`, unit U6)

The small Gloas helpers of `ethereum/consensus-specs` `v1.7.0-beta.4` (`specs/gloas/beacon-chain.md`)
over `JauneConsensus.Gloas.BeaconState P`, starting with what `verify_execution_payload_envelope`
(`specs/gloas/fork-choice.md`) and `verify_execution_payload_envelope_signature` read. Later
Gloas units (epoch processing, block processing) extend this module.

The Gloas `BeaconState` is a separate structure (`ContainersGloas.lean`), so the fork-indexed
accessors of `Accessors.lean` and `Signing.lean` do not apply to it directly. Each helper here is
the Gloas-state wrapper of an existing fork-independent function:

* `getDomain` is `getDomainAt` (`Signing.lean`) at `compute_epoch_at_slot(state.slot)`;
* `computeTimeAtSlot` is `computeTimeAtSlotOf` (`Block.lean`, the `v1.7.0-beta.4` millisecond form);
* `blobVersionedHashes` maps `kzgCommitmentToVersionedHash` (`Helpers.lean`).

Every read is checked: an index out of range is `Reject.index`, a list past its limit is
`Reject.limit`, and `uint64` arithmetic goes through `UInt.lean`.
-/

namespace JauneConsensus.Gloas

open Jaune

variable {P : Preset}

/-! ## Constants (`specs/gloas/beacon-chain.md`) -/

/-- `DOMAIN_BEACON_BUILDER = DomainType('0x0B000000')` ("Domain types"). -/
def DOMAIN_BEACON_BUILDER : DomainType := #v[0x0B, 0x00, 0x00, 0x00]

/-- `BUILDER_INDEX_SELF_BUILD = BuilderIndex(UINT64_MAX)` ("Misc"). -/
def BUILDER_INDEX_SELF_BUILD : BuilderIndex := UINT64_MAX

/-- `BUILDER_INDEX_FLAG = uint64(2**40)` ("Misc"). -/
def BUILDER_INDEX_FLAG : U64 := U64.lit (2 ^ 40)

/-- `BUILDER_DEPOSIT_REQUEST_TYPE = Bytes1('0x03')` (EIP-8282). -/
def builderDepositRequestType : UInt8 := 0x03
/-- `BUILDER_EXIT_REQUEST_TYPE = Bytes1('0x04')` (EIP-8282). -/
def builderExitRequestType : UInt8 := 0x04

/-! ## Epochs, domains, time -/

/-- `get_current_epoch(state)`. -/
def getCurrentEpoch (state : BeaconState P) : M Epoch := computeEpochAtSlot P state.slot

/-- `get_domain(state, domain_type, epoch=None)`: `epoch` defaults to the current epoch; the
fork version is the state's `fork.previous_version` before `fork.epoch`, its
`current_version` from then on. -/
def getDomain (state : BeaconState P) (domainType : DomainType) (epoch : Option Epoch := none) :
    M Domain := do
  let e ← match epoch with
    | some e => pure e
    | none => getCurrentEpoch state
  pure (getDomainAt state.fork state.genesis_validators_root domainType e)

/-- `compute_time_at_slot(state.genesis_time, slot)` (the `v1.7.0-beta.4` millisecond form,
which raises on `uint64` overflow). -/
def computeTimeAtSlot (cfg : Config) (state : BeaconState P) (slot : Slot) : M U64 :=
  computeTimeAtSlotOf cfg state.genesis_time slot

/-! ## Registry lookups -/

/-- `state.validators[validator_index].pubkey` (`IndexError` when out of range). -/
def validatorPubkey (state : BeaconState P) (validatorIndex : ValidatorIndex) : M BLSPubkey := do
  let v ← getAt state.validators.toArray validatorIndex.toNat "state.validators[validator_index]"
  pure v.pubkey

/-- `state.builders[builder_index].pubkey` (`IndexError` when out of range). -/
def builderPubkey (state : BeaconState P) (builderIndex : BuilderIndex) : M BLSPubkey := do
  let b ← getAt state.builders.toArray builderIndex.toNat "state.builders[builder_index]"
  pure b.pubkey

/-- The key a builder-signed object (envelope or bid) of `builder_index` is verified against
(`verify_execution_payload_envelope_signature`): for `BUILDER_INDEX_SELF_BUILD`, the pubkey of
the latest block header's proposer; otherwise the builder's own pubkey. -/
def builderSigningPubkey (state : BeaconState P) (builderIndex : BuilderIndex) : M BLSPubkey :=
  if builderIndex == BUILDER_INDEX_SELF_BUILD then
    validatorPubkey state state.latest_block_header.proposer_index
  else
    builderPubkey state builderIndex

/-! ## Roots -/

/-- `hash_tree_root(state)`. -/
def stateRoot (state : BeaconState P) : Root := Ssz.hashTreeRoot state

/-- `header = state.latest_block_header.copy(); header.state_root = hash_tree_root(state)`. -/
def latestBlockHeaderWithStateRoot (state : BeaconState P) : BeaconBlockHeader :=
  { state.latest_block_header with state_root := stateRoot state }

/-- `hash_tree_root(header)` of `latestBlockHeaderWithStateRoot`: the root of the block whose
post-state `state` is. -/
def latestBlockRoot (state : BeaconState P) : Root :=
  Ssz.hashTreeRoot (latestBlockHeaderWithStateRoot state)

/-! ## Blob versioned hashes -/

/-- `versioned_hashes = VersionedHashes(); for commitment in commitments:
versioned_hashes.append(kzg_commitment_to_versioned_hash(commitment))`. `VersionedHashes` is
`List[VersionedHash, MAX_BLOB_COMMITMENTS_PER_BLOCK]`, so an append past the limit raises
(`Reject.limit`); the commitments themselves are a `ProgressiveList` with no limit. -/
def blobVersionedHashes (commitments : ProgressiveListR KZGCommitment) :
    M (SszList Bytes32 P.MAX_BLOB_COMMITMENTS_PER_BLOCK) :=
  let hashes := commitments.toArray.map fun c => kzgCommitmentToVersionedHash c.toArray.toList
  if h : hashes.size ≤ P.MAX_BLOB_COMMITMENTS_PER_BLOCK then pure ⟨hashes, h⟩
  else throw (.limit "VersionedHashes.append" P.MAX_BLOB_COMMITMENTS_PER_BLOCK hashes.size)

/-! ## Execution requests as lists -/

/-- `get_execution_requests_list(execution_requests)` (Gloas, EIP-8282 adds types `0x03` and
`0x04`): for each request type whose list is non-empty, in type order, the type byte followed by
the list's SSZ serialization. This is the list form in which the execution layer reads the
envelope's requests. -/
def getExecutionRequestsList (r : ExecutionRequests) : ExecutionRequestsList :=
  [(depositRequestType, Ssz.serialize r.deposits),
   (withdrawalRequestType, Ssz.serialize r.withdrawals),
   (consolidationRequestType, Ssz.serialize r.consolidations),
   (builderDepositRequestType, Ssz.serialize r.builder_deposits),
   (builderExitRequestType, Ssz.serialize r.builder_exits)].filterMap fun (t, data) =>
    if data.isEmpty then none else some (t :: data)

/-- The five request lists of an `ExecutionRequests`, as plain lists, in field order. -/
def ExecutionRequests.lists (r : ExecutionRequests) :
    List DepositRequest × List WithdrawalRequest × List ConsolidationRequest ×
      List BuilderDepositRequest × List BuilderExitRequest :=
  (r.deposits.toArray.toList, r.withdrawals.toArray.toList, r.consolidations.toArray.toList,
   r.builder_deposits.toArray.toList, r.builder_exits.toArray.toList)

/-- A progressive list is determined by its elements. -/
theorem ProgressiveListS.eq_of_toList_eq {s : Spine} {α : Type} {a b : ProgressiveListS s α}
    (h : a.toArray.toList = b.toArray.toList) : a = b := by
  cases a; cases b
  simp only at h
  rw [Array.toList_inj.mp h]

/-- Equal elements give equal `hash_tree_root`s (the easy direction; the converse would need
`hash_tree_root` to be injective, which is the SSZ collision caveat and is not provable). -/
theorem ProgressiveListS.hashTreeRoot_eq_of_toList_eq {s : Spine} {α : Type} [Ssz α]
    {a b : ProgressiveListS s α} (h : a.toArray.toList = b.toArray.toList) :
    Ssz.hashTreeRoot a = Ssz.hashTreeRoot b := by
  rw [ProgressiveListS.eq_of_toList_eq h]

/-- Requests with the same five lists are the same container. -/
theorem ExecutionRequests.eq_of_lists_eq {r r' : ExecutionRequests} (h : r.lists = r'.lists) :
    r = r' := by
  cases r; cases r'
  simp only [ExecutionRequests.lists, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [ProgressiveListS.eq_of_toList_eq h1, ProgressiveListS.eq_of_toList_eq h2,
    ProgressiveListS.eq_of_toList_eq h3, ProgressiveListS.eq_of_toList_eq h4,
    ProgressiveListS.eq_of_toList_eq h5]

/-- Requests with the same five lists have the same `hash_tree_root` (the easy direction; the
converse is the SSZ collision caveat). -/
theorem ExecutionRequests.hashTreeRoot_eq_of_lists_eq {r r' : ExecutionRequests}
    (h : r.lists = r'.lists) : Ssz.hashTreeRoot r = Ssz.hashTreeRoot r' := by
  rw [ExecutionRequests.eq_of_lists_eq h]

/-- Requests with the same five lists have the same `get_execution_requests_list`. -/
theorem getExecutionRequestsList_eq_of_lists_eq {r r' : ExecutionRequests}
    (h : r.lists = r'.lists) : getExecutionRequestsList r = getExecutionRequestsList r' := by
  rw [ExecutionRequests.eq_of_lists_eq h]

end JauneConsensus.Gloas
