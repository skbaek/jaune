import JauneConsensus.Accessors
import JauneConsensus.Crypto.Boundary

/-!
# Signature domains and signing roots

The domain types and the domain/signing-root functions of `ethereum/consensus-specs` `v1.6.1`
(`specs/phase0/beacon-chain.md`, "Domain types", `compute_fork_data_root`, `compute_domain`,
`compute_signing_root`, `get_domain`; the domain types added in `specs/altair/beacon-chain.md`
and `specs/capella/beacon-chain.md`), each mirroring its pyspec function.

`get_domain` takes the state's `fork`, `genesis_validators_root` and current epoch rather than
the whole state, so it is independent of the fork index of `BeaconState`; `getDomainAt` is the
form callers with a state use.
-/

namespace JauneConsensus

open Jaune

/-- `DomainType`: four bytes. -/
abbrev DomainType := Bytes

/-! ## Domain types

`DOMAIN_BEACON_PROPOSER` and `DOMAIN_BEACON_ATTESTER` are in `Accessors.lean` (`get_seed` needs
them); the others are here. -/

/-- `DOMAIN_RANDAO = DomainType('0x02000000')` (`specs/phase0/beacon-chain.md`) -/
def DOMAIN_RANDAO : DomainType := [0x02, 0x00, 0x00, 0x00]
/-- `DOMAIN_DEPOSIT = DomainType('0x03000000')` -/
def DOMAIN_DEPOSIT : DomainType := [0x03, 0x00, 0x00, 0x00]
/-- `DOMAIN_VOLUNTARY_EXIT = DomainType('0x04000000')` -/
def DOMAIN_VOLUNTARY_EXIT : DomainType := [0x04, 0x00, 0x00, 0x00]
/-- `DOMAIN_SELECTION_PROOF = DomainType('0x05000000')` -/
def DOMAIN_SELECTION_PROOF : DomainType := [0x05, 0x00, 0x00, 0x00]
/-- `DOMAIN_AGGREGATE_AND_PROOF = DomainType('0x06000000')` -/
def DOMAIN_AGGREGATE_AND_PROOF : DomainType := [0x06, 0x00, 0x00, 0x00]
/-- `DOMAIN_APPLICATION_MASK = DomainType('0x00000001')` -/
def DOMAIN_APPLICATION_MASK : DomainType := [0x00, 0x00, 0x00, 0x01]
/-- `DOMAIN_SYNC_COMMITTEE = DomainType('0x07000000')` (`specs/altair/beacon-chain.md`) -/
def DOMAIN_SYNC_COMMITTEE : DomainType := [0x07, 0x00, 0x00, 0x00]
/-- `DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF = DomainType('0x08000000')` -/
def DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF : DomainType := [0x08, 0x00, 0x00, 0x00]
/-- `DOMAIN_CONTRIBUTION_AND_PROOF = DomainType('0x09000000')` -/
def DOMAIN_CONTRIBUTION_AND_PROOF : DomainType := [0x09, 0x00, 0x00, 0x00]
/-- `DOMAIN_BLS_TO_EXECUTION_CHANGE = DomainType('0x0A000000')` (`specs/capella/beacon-chain.md`) -/
def DOMAIN_BLS_TO_EXECUTION_CHANGE : DomainType := [0x0A, 0x00, 0x00, 0x00]

/-! ## Versions -/

/-- `Version(bytes)`: a four-byte value (a config `*_FORK_VERSION`). Rejects any other length,
as the SSZ type would. -/
def versionOf (bs : Bytes) : M Version :=
  if h : bs.toArray.size = 4 then pure ⟨bs.toArray, h⟩
  else throw (.assert s!"Version: {bs.length} bytes")

/-! ## Domains and signing roots (`specs/phase0/beacon-chain.md`) -/

/-- `compute_fork_data_root(current_version, genesis_validators_root)`. -/
def computeForkDataRoot (currentVersion : Version) (genesisValidatorsRoot : Root) : Root :=
  Ssz.hashTreeRoot (ForkData.mk currentVersion genesisValidatorsRoot)

/-- `compute_domain(domain_type, fork_version, genesis_validators_root)`: the defaults
(`GENESIS_FORK_VERSION`, the zero root) are the callers' explicit arguments
(`computeDomainDefault`). `Domain(domain_type + fork_data_root[:28])`. -/
def computeDomain (domainType : DomainType) (forkVersion : Version) (genesisValidatorsRoot : Root) :
    Domain :=
  let forkDataRoot := computeForkDataRoot forkVersion genesisValidatorsRoot
  B256.ofBytes (domainType ++ forkDataRoot.toBytes.take 28)

/-- `compute_domain(domain_type)` with the defaults: `GENESIS_FORK_VERSION` and `Root()`. -/
def computeDomainDefault (cfg : Config) (domainType : DomainType) : M Domain := do
  pure (computeDomain domainType (← versionOf cfg.GENESIS_FORK_VERSION) (0 : B256))

/-- `compute_signing_root(ssz_object, domain)`. -/
def computeSigningRoot {α : Type} [Ssz α] (sszObject : α) (domain : Domain) : Root :=
  Ssz.hashTreeRoot (SigningData.mk (Ssz.hashTreeRoot sszObject) domain)

/-- `compute_signing_root` for an object whose root is already known (`hash_tree_root(x)` of a
`Root` is the root itself, so this is the same function on `Root`). -/
def computeSigningRootOfRoot (objectRoot : Root) (domain : Domain) : Root :=
  Ssz.hashTreeRoot (SigningData.mk objectRoot domain)

/-- `get_domain(state, domain_type, epoch)` with `epoch` given; `fork` and
`genesis_validators_root` are the state's. -/
def getDomainAt (fork : Fork) (genesisValidatorsRoot : Root) (domainType : DomainType)
    (epoch : Epoch) : Domain :=
  let forkVersion := if epoch < fork.epoch then fork.previous_version else fork.current_version
  computeDomain domainType forkVersion genesisValidatorsRoot

/-- `get_domain(state, domain_type, epoch=None)` for any fork's `BeaconState`: `epoch` defaults
to `get_current_epoch(state) = compute_epoch_at_slot(state.slot)`. -/
def getDomain {P : Preset} {f : CFork} (state : BeaconState P f) (domainType : DomainType)
    (epoch : Option Epoch := none) : M Domain := do
  let e ← match epoch with
    | some e => pure e
    | none => computeEpochAtSlot P state.slot
  pure (getDomainAt state.fork state.genesis_validators_root domainType e)

/-! ## The BLS switch

pyspec's `bls_active` flag (`eth2spec/utils/bls.py`) turns only the verification predicates
into `True` (`Verify`, `AggregateVerify`, `FastAggregateVerify`); aggregation and key
aggregation always compute. The vectors record the setting per case (`bls_setting`). -/

/-- `bls.Verify(pubkey, message, signature)` under the switch. -/
def blsVerify (active : Bool) (pubkey : BLSPubkey) (message : Root) (signature : BLSSignature) :
    Bool :=
  !active || verify pubkey.toArray.toList message.toBytes signature.toArray.toList

/-- `bls.FastAggregateVerify(pubkeys, message, signature)` under the switch. -/
def blsFastAggregateVerify (active : Bool) (pubkeys : List BLSPubkey) (message : Root)
    (signature : BLSSignature) : Bool :=
  !active || fastAggregateVerify (pubkeys.map (·.toArray.toList)) message.toBytes
    signature.toArray.toList

/-- `eth_fast_aggregate_verify(pubkeys, message, signature)` (`specs/altair/bls.md`) under the
switch. -/
def blsEthFastAggregateVerify (active : Bool) (pubkeys : List BLSPubkey) (message : Root)
    (signature : BLSSignature) : Bool :=
  !active || ethFastAggregateVerify (pubkeys.map (·.toArray.toList)) message.toBytes
    signature.toArray.toList

-- `compute_signing_root` of a `Root` equals its `ByRoot` form.
#guard computeSigningRoot (7 : B256) (9 : B256) == computeSigningRootOfRoot 7 9

end JauneConsensus
