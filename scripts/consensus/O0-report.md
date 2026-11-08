# O0 recon and design: Electra and Fulu consensus layer

Goal: `jaune-consensus-electra-fulu-v1`, outcome O0. Branch `claude/consensus-electra-fulu-v1` from Jaune `main` 99c0585.
Date: 2026-11-09 (WSL host). No consensus Lean was written. No Lean build was run.

Sources read: `ethereum/consensus-specs` at tag `v1.6.1` (tag commit `5fa6edcca8ab4cf548653e6680b17b9d3e04d225`,
verified by `git rev-parse v1.6.1^{commit}`), its `specs/`, `tests/formats/`, `presets/`, `configs/` and the pyspec test
utilities; RFC 9380 by citation; Jaune at 99c0585; Blanc's lakefile and manifest, read only. No other model source was read.

Location note. The brief named `docs/consensus/`. Jaune's `docs/` is served by GitHub Pages (`.nojekyll`, `has_pages`
true), so files there are published when `main` moves. Publication is a user decision, so these files live in
`scripts/consensus/` instead. Moving them is a one-line change if the master prefers otherwise.

## (a) Vector inventory

Files:
- `scripts/consensus-vectors.json`: the provenance pin. Release tag, tag commit, publication time, licence, and per
  tarball name, URL, size and SHA-256.
- `scripts/consensus-vector-inventory.py`: the inventory script. It streams each tarball (no extraction), checks size and
  SHA-256 against the pin, and counts cases by preset, fork, runner, handler and suite. A case is the directory
  `tests/<preset>/<fork>/<runner>/<handler>/<suite>/<case>` of any regular file under it. It refuses members with `..`,
  members outside the expected depth and members outside the tarball's preset.
- `scripts/consensus/inventory-v1.6.1.json` and `scripts/consensus/inventory-v1.6.1.md`: its output.

Pinned digests. They equal the asset digests the GitHub releases API reports for the tag.

| tarball | bytes | SHA-256 |
|---|---:|---|
| general.tar.gz | 169,552,849 | `87898ba7a3fa16bc66b08c88b4ccab008833a517a7602cf421c6ce79734e07e9` |
| minimal.tar.gz | 467,646,726 | `e1d0c9dc3d09fb74a98b324c40b2587a17dc555e6149d3f9741601fffcf43901` |
| mainnet.tar.gz | 678,708,605 | `8401c58700c461154db2050c2a982af7aca259bd016c2184ec39c454edf6f1c5` |

Scope rule used by the script: every `general` case; every `minimal` and `mainnet` case whose fork is `electra` or `fulu`;
plus `phase0/shuffling` on both presets, because O1 names shuffling and its only cases sit under `phase0`.

| preset | all cases | in-scope cases | files |
|---|---:|---:|---:|
| general | 5,509 | 5,509 | 10,925 |
| minimal | 60,959 | 16,126 | 202,311 |
| mainnet | 7,421 | 2,340 | 41,147 |
| total | 73,889 | 23,975 | |

In-scope cases by runner (minimal / mainnet, Electra + Fulu):

| runner | minimal | mainnet |
|---|---:|---:|
| ssz_static | 14,145 | 575 |
| operations | 756 | 684 |
| epoch_processing | 312 | 282 |
| sanity | 223 | 199 |
| fork_choice | 124 | 62 |
| transition | 66 | 54 |
| rewards | 68 | 68 |
| fork | 44 | 40 |
| random | 32 | 32 |
| light_client | 20 | 8 |
| networking (Fulu only) | 16 | 16 |
| finality | 10 | 10 |
| merkle_proof | 8 | 8 |
| sync | 2 | 2 |
| shuffling (phase0) | 300 | 300 |

General preset: `ssz_generic` 5,145 (phase0 directory); `kzg` 262 (Deneb, EIP-4844) and 82 (Fulu, EIP-7594); `bls` 20
(Altair directory: `eth_aggregate_pubkeys` 8, `eth_fast_aggregate_verify` 12). Handler and suite counts are in the
generated Markdown.

Findings that bear on the goal text:
1. **No `genesis` cases exist for Electra or Fulu.** The only genesis cases are `minimal/phase0` (10). O2 lists `genesis`
   among its suites. Nothing can be cut, since nothing exists, but O2's genesis evidence cannot come from vectors.
2. **`shuffling` exists only under `phase0`** (300 per preset). The script counts it in scope, as O1 requires.
3. **The general `bls` runner has only the two `eth_*` handlers (20 cases).** The core ciphersuite handlers (`sign`,
   `verify`, `aggregate`, `aggregate_verify`, `fast_aggregate_verify`) are documented in `tests/formats/bls/` but are not
   in this release's tarball. Signature coverage therefore comes mainly from the `bls_setting: 1` cases in operations,
   sanity, random, transition and epoch processing (428 cases in scope).
4. **`ssz_generic` includes progressive types** (`basic_progressive_list`, `progressive_bitlist`,
   `progressive_containers`, `compatible_unions`: 2,636 cases, plus the two progressive structs inside `containers`). Electra and Fulu do
   not use them. The objective says "every general-preset case those forks use", while O1's acceptance says all
   `ssz_generic`. I recommend implementing them (about 2 agent-days) so no exclusion question arises.
5. Per-case `config.yaml` overrides occur only in 10 minimal light-client cases. Config must still be a runtime value.
6. Case format is `.ssz_snappy` plus YAML everywhere. The harness needs a Snappy block decoder and a YAML reader.

Negative controls (run 2026-11-09, scratch copies in `/home/agent/consensus-spec-tests-v1.6.1/negctl/`):
- One case removed (`tests/general/fulu/kzg/recover_cells_and_kzg_proofs/kzg-mainnet/recover_cells_and_kzg_proofs_case_invalid_cell_3/`),
  pinned run: `FAIL: .../general.tar.gz: size 178563191 != pinned 169552849`, exit 1.
- Same tree, `--unpinned --expect scripts/consensus/inventory-v1.6.1.json`:
  `count mismatch general/fulu/kzg/recover_cells_and_kzg_proofs: got 17 recorded 18`, general 5,508 cases, exit 1.
- One byte changed at offset 1,000,000 of a same-size copy: `FAIL: ... sha256 e2902b6e... != pinned 87898ba7...`, exit 1.
- Original tarballs with `--expect`: `inventory matches`, exit 0.

## (b) Runners: what each exercises and what the model needs

| runner | exercises | model needs |
|---|---|---|
| ssz_generic | SSZ codec and `hash_tree_root` on generic types; invalid encodings must fail to decode | SSZ core, progressive types, compatible unions; YAML value reader for `value.yaml` |
| ssz_static | every Electra/Fulu container: serialize round trip and root | all containers (56 Electra, 59 Fulu, including legacy `PendingAttestation`, `HistoricalBatch`, `Eth1Block`, `PowBlock`) |
| bls | `eth_aggregate_pubkeys`, `eth_fast_aggregate_verify` | G1/G2 decompression, KeyValidate, aggregation, FastAggregateVerify, hash-to-curve, pairing check |
| kzg (4844) | blob commitment, proofs, verification, batch verification, Fiat-Shamir challenge | Lagrange-form KZG over the pinned setup, roots of unity, bit reversal, G1 MSM, pairing check |
| kzg (7594) | cells, cell proofs, batch cell verification and its challenge, recovery | FFT and coset FFT, coefficient-form polynomials, multi-proofs, recovery via vanishing polynomial |
| shuffling | `compute_shuffled_index` over every index | the swap-or-not shuffle on SHA-256 |
| operations | each block operation in isolation, 13 handlers; no post state means reject | block processing pieces, mocked `execution.yml` engine verdict for `execution_payload` |
| epoch_processing | each epoch sub-step from a pre-state; Fulu adds `proposer_lookahead` | every `process_*` epoch sub-step |
| rewards | Altair-style deltas: source, target, head, inactivity penalty | `get_flag_index_deltas`, `get_inactivity_penalty_deltas` |
| sanity | `blocks`: full `state_transition` with signatures and state root check; `slots`: `process_slots` | the whole transition. One mainnet case runs 8,192 slots (`historical_accumulator`) |
| finality, random | block sequences, same format as sanity blocks | as sanity; all 64 random cases are `bls_setting: 1` |
| fork | `upgrade_to_electra` from a Deneb state, `upgrade_to_fulu` from an Electra state | Deneb `BeaconState` decoding plus the upgrade functions |
| transition | block sequences across the fork epoch, pre-fork blocks under the old fork | the full Deneb transition for Electra cases (see (c)), Electra for Fulu cases |
| fork_choice | store steps: `on_tick`, `on_block`, `on_attestation`, `on_attester_slashing`, checks on head, checkpoints, boost, weights, `get_proposer_head`, `should_override_forkchoice_update` | Store, LMD-GHOST, proposer boost, reorg helpers; Fulu data availability from column sidecars (17 Fulu cases carry `columns`) |
| sync | optimistic sync, fork-choice format plus `on_payload_info` statuses | optimistic sync store and payload-status mock |
| light_client | `single_merkle_proof`, `sync`, `update_ranking`, `data_collection` | LC containers, LC sync protocol, full-node LC data collection, fork digests across the blob schedule (Fulu digests change at each BPO epoch) |
| merkle_proof | `BeaconBlockBody` inclusion proof | generalized indices and `compute_merkle_proof` |
| networking | `get_custody_groups`, `compute_columns_for_custody_group` | the two DAS-core helpers on `uint256` node ids |

`bls_setting` (meta.yaml): 0 means BLS may be on or off, 1 means required, 2 means must be off. In scope, 12 cases are
`2`. Pyspec's off switch makes only the verify predicates return true; `AggregatePKs` and `Sign` return stubs, but the
vectors were generated with BLS on, so sync-committee aggregate keys must always be computed for real. The model
therefore separates a verify switch from point arithmetic.

## (c) Deneb pieces Electra's `fork` and `transition` vectors need

`fork` (46 Electra cases): only decoding the Deneb `BeaconState` (with its Deneb field types, notably the Deneb
`ExecutionPayloadHeader`, `Validator`, `SyncCommittee`, `HistoricalSummary`) and `upgrade_to_electra`. The upgrade uses
Deneb `get_current_epoch` and the Electra helpers `compute_activation_exit_epoch`, `get_activation_exit_churn_limit`,
`get_consolidation_churn_limit`, `has_compounding_withdrawal_credential` and `queue_excess_active_balance`.

`transition` (60 Electra cases): the full Deneb state transition, not just the state type.
- 12 of 33 minimal cases (and 11 of 27 on mainnet) carry `fork_block`, so up to 95 Deneb `SignedBeaconBlock`s (mainnet)
  are processed before the fork. Every case processes Deneb slots and epochs before `fork_epoch` (up to epoch 66 on minimal).
- Pre-fork blocks include attestations, deposits, proposer and attester slashings, voluntary exits and BLS-to-execution
  changes, several with `bls_setting: 1`.

So the Deneb side needs:
- Deneb containers: `BeaconState`, `BeaconBlock`, `BeaconBlockBody` (no `execution_requests`), `SignedBeaconBlock`,
  `Attestation` (no `committee_bits`; per-committee bitlist limit), `IndexedAttestation` and `AttesterSlashing` (Deneb
  limits), Deneb preset limits `MAX_ATTESTATIONS` and `MAX_ATTESTER_SLASHINGS`.
- The Deneb versions of every function Electra modified: `compute_proposer_index`, `is_eligible_for_activation_queue`,
  `is_fully_withdrawable_validator`, `is_partially_withdrawable_validator`, `get_attesting_indices`,
  `get_next_sync_committee_indices`, `initiate_validator_exit`, `slash_validator`, `process_epoch`,
  `process_registry_updates`, `process_slashings`, `process_effective_balance_updates`, `get_expected_withdrawals`,
  `process_withdrawals`, `process_execution_payload`, `process_operations`, `process_attestation`,
  `get_validator_from_deposit`, `add_validator_to_registry`, `apply_deposit`, `process_deposit`,
  `process_voluntary_exit`, plus `get_validator_churn_limit` and `get_validator_activation_churn_limit` (EIP-7514).
- Everything else is shared and written once: slots, header, RANDAO, eth1 data, sync aggregate, BLS-to-execution
  change, proposer slashing, attester slashing logic, justification and finality, inactivity, rewards, resets,
  historical summaries, participation flags, sync committee updates.
- Config: Deneb and Capella fork versions (EIP-7044 exit domain uses `CAPELLA_FORK_VERSION`).

Estimate for the Deneb side: 4 to 7 agent-days on top of Electra, mostly the 22 function variants and their containers.

## (d) Design

### Placement and library targets

- Blanc requires Jaune by a pinned Git revision and `needs := #[@jaune/Assurance]`. Lake builds no default target of a
  dependency, but it does build `Assurance` in full, and `Assurance` includes `JauneUnionAxioms`.
- `scripts/check-assurance-manifest.py` (`check_union_coverage`) requires `JauneUnionAxioms` to import every module under
  `Jaune/`. A consensus module under `Jaune/` would therefore be built by Blanc. **So the consensus layer must live
  outside `Jaune/`.**
- Recommendation: a new source tree `JauneConsensus/` with module prefix `JauneConsensus.*`, a library
  `lean_lib «JauneConsensus»` (default target in Jaune only), an executable `lean_exe «jaune-consensus»` for the runner,
  and a separate assurance library `ConsensusAssurance` holding its own union-axiom module. Blanc's `needs` stays as is,
  so Blanc's build does not grow.
- Jaune's hygiene and integrity gates currently scope `Jaune/` and the `Jaune.lean` closure. They extend to
  `JauneConsensus/` by adding a scope, with no allowlist rows.
- Jaune CI builds default targets. Adding the library grows Jaune's CI time, not Blanc's. Whether CI also runs the
  consensus smoke tier is a master decision (Blanc's out-of-root lesson applies: an unbuilt module passes locally and rots).

Module layout:

```
JauneConsensus/
  Fork.lean          consensus fork axis, pairing with Jaune.Fork (O7)
  Preset.lean        Preset record (minimal, mainnet), generated from presets/*.yaml
  Config.lean        runtime Config record, generated from configs/*.yaml; BLOB_SCHEDULE
  Error.lean         Reject (typed rejection), the M monad
  UInt.lean          checked uint64 and uint256 arithmetic
  SSZ/Basic.lean     uintN, boolean, bitvector, bitlist, vector, list, container codecs
  SSZ/Merkle.lean    merkleize with a zero-hash table, mix_in_length, hash_tree_root on Bytes.sha256
  SSZ/Progressive.lean  progressive list, bitlist, container, compatible union (ssz_generic only)
  SSZ/Proof.lean     generalized indices, compute_merkle_proof, is_valid_merkle_branch
  Crypto/HashToCurve.lean  expand_message_xmd, hash_to_field, hash_to_curve G2 (RFC 9380)
  Crypto/BLSSig.lean       ciphersuite, eth_* helpers
  Crypto/Codec.lean        G1 and G2 compression and decompression, subgroup checks
  Crypto/MSM.lean          projective G1, bucket MSM
  Crypto/KZG.lean          EIP-4844
  Crypto/KZGCells.lean     EIP-7594
  Crypto/TrustedSetup.lean generated from presets/*/trusted_setups/trusted_setup_4096.json, digest pinned
  Shuffle.lean
  Containers.lean, State.lean
  Helpers.lean       math, predicates, accessors, mutators
  Block.lean, Epoch.lean, Transition.lean (state_transition, process_slots, upgrades)
  Genesis.lean, ForkChoice.lean, Sync.lean, LightClient.lean, DAS.lean
JauneConsensus.lean  library root
ConsensusMain.lean   runner (Snappy, YAML reader, case discovery, verdicts)
```

### Fork axis and pairing with Jaune's `Fork` (O7)

- `inductive CFork | deneb | electra | fulu | gloas` with an order. Deneb exists only as the pre-fork side.
- `CFork.executionForks : CFork → List Jaune.Fork`: `deneb ↦ [cancun]`, `electra ↦ [prague]`,
  `fulu ↦ [osaka, bpo1, bpo2]`, `gloas ↦ [amsterdam]`. Its inverse `Jaune.Fork.consensusFork? : Fork → Option CFork`
  is total, `none` before Cancun. Both live in `JauneConsensus/Fork.lean`, since the consensus layer imports the
  execution layer and not the reverse.
- `CFork.rules? : CFork → Option ForkData` is the single resolver, as `Fork.rules?` is on the execution side. Gloas returns
  `none`, so the runner refuses it by name and never falls back to Fulu.
- BPO1 and BPO2 are not consensus forks. They are `BLOB_SCHEDULE` entries read by `get_blob_parameters`. The pairing is
  checkable data: Electra's `MAX_BLOBS_PER_BLOCK_ELECTRA` 9 times `GAS_PER_BLOB` 131,072 equals `pragueBlobSchedule.max`
  and `osakaBlobSchedule.max`; the mainnet schedule's 15 and 21 equal `bpo1BlobSchedule.max` and `bpo2BlobSchedule.max`
  over 131,072. These become `#guard`s or `decide` theorems against the declarations in `Jaune/Fork.lean`.
- Request type bytes: consensus `WITHDRAWAL_REQUEST_TYPE` and `CONSOLIDATION_REQUEST_TYPE` equal the type bytes in
  `pragueRequests` (`ForkRules.requests`).
- `get_execution_requests_list` returns `List Bytes`, the exact input type of `computeRequestsHash` in
  `Jaune/Transaction.lean`. A later seam goal can state equality with no conversion.
- Shared types: `Jaune.Bytes`, `Jaune.B256` for roots, `Jaune.Adr` for execution addresses, `Bytes.sha256`, and the BLS
  types `BLSP`, `BLSP2`, `BLSF`, `BLSF2` from `Jaune/BLS.lean`. No second SHA-256, Keccak or BLS12-381.
- The printer for the pairing is `lake exe jaune-consensus --forks`, a sibling of `jaune --rules`.

### State representation

- Containers are Lean structures indexed by preset and fork: `BeaconState (P : Preset) (f : CFork)`.
- List and vector limits come from `P` in the field types (`SszList α n := {xs : Array α // xs.size ≤ n}`). A push past
  the limit is a typed rejection, as remerkleable raises.
- Fork-gated fields use `Gated (f.atLeast .electra) α`, where `Gated true α = α` and `Gated false α = Unit`. Fulu's
  `proposer_lookahead` is gated the same way. For a concrete fork the gate reduces by `rfl`, so Electra and Fulu theorems
  see plain fields.
- One definition per pyspec function. Where pyspec overrides per fork, the definition branches on `f` and cites both
  spec sections. Numeric differences between forks are data in `ForkData`, following Jaune's `ForkRules` doctrine.
- Collections are `Array` for O(1) reads and in-place updates when unshared.
- Alternatives considered: (1) one superset record per fork plus a well-formedness predicate: simpler types, weaker
  guarantees, Deneb code could read Electra fields; (2) separate structures per fork: forces duplicate definitions of
  shared functions, which the goal forbids.

### Failure model (O5)

- `abbrev M := Except Reject`. `Reject` is an inductive: `assert (site : String)`, `index`, `overflow`, `underflow`,
  `divByZero`, `limit`, `decode (why)`, `crypto (why)`. Every pyspec `assert`, index error and arithmetic error maps to
  one of these.
- `U64` is a structure over `UInt64` with no `HAdd`, `HSub` or `HMul` instances. Arithmetic is `U64.add? : U64 → U64 → M U64`
  and so on, so wrapping cannot be written. Reasoning lemmas state `toNat` results when no rejection occurs.
- Where pyspec computes in Python `int` (after `int(...)` or on literal arithmetic not typed `uint64`), the model uses
  `Nat`. Each such site cites the spec line. This is a fidelity point to check per function, because remerkleable
  checks only typed operands.
- Reads are `get? : SszList α n → Nat → M α`. There are no `[i]!`, `getD` or default reads in the spec layer.
- Integrity gate extension: reject `[`…`]!`, `getD`, `get!`, `.getLast!`, `Inhabited`-default reads, and `+`, `-`, `*`
  on `UInt64` in `JauneConsensus/` outside `UInt.lean`. Negative control: plant one, see red, revert, see green.

### SSZ

- A type class `Ssz α` with `fixedSize? : Option Nat`, `serialize : α → Bytes`, `deserialize : Bytes → M α` and
  `hashTreeRoot : α → B256`. Containers get instances from a field-list macro so each container is declared once.
- Decoding enforces every pyspec rule: offset monotonicity, first offset equals fixed part size, no trailing bytes,
  bitlist delimiter bit present, boolean in {0, 1}, list length within limit.
- Merkleization uses a 64-entry zero-hash table, so a list with limit 2^40 never materializes padding.
- Snappy decoding and YAML reading belong to the harness, not the semantics.
- Cost risk: `process_slot` hashes the whole state each slot. A mainnet `BeaconState` root is about 86,000 compressions
  (`randao_mixes` alone is 65,536 leaves). One mainnet sanity case runs 8,192 slots. Plan: plain values first, measure,
  then if needed an incremental root cache for the four history vectors (`block_roots`, `state_roots`, `randao_mixes`,
  `slashings`) as a data structure with a proved invariant (`cachedRoot v = hashTreeRoot v.toList`). That is a
  representation with a theorem, like Jaune's SHA-256 kernel and FIPS transcription, not memoization of an oracle.

### BLS signatures

Ciphersuite `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`, minimal-pubkey-size variant (G1 keys, G2 signatures).
- Extend, by importing, these existing declarations in `Jaune/BLS.lean`: `optimizedSwuG2`, `isoMapG2`, `blsSgn0F2`,
  `blsPairing`, `blsMillerLoop`, `blsG1Generator`, `blsG2Generator`, `blsCurveOrder`, and `BLSConst.hEffG2`. Reuse
  `Bytes.sha256` (Jaune/Hash.lean, proved equal to FIPS 180-4 by `Bytes.sha256_eq_fips`).
- New: `expandMessageXmd` (RFC 9380 section 5.3.1), `hashToFieldFp2` (count 2, L = 64), `hashToG2 =
  clear_cofactor(map(u0) + map(u1))`. `blsMapFp2ToG2` already clears the cofactor per point, so it must not be used
  twice; the new code calls `isoMapG2 ∘ optimizedSwuG2` and clears once.
- New: G2 decompression and G1/G2 compression (ZCash flag bits), G2 subgroup check, `KeyValidate`, `Verify`,
  `AggregateVerify`, `FastAggregateVerify`, `Aggregate`, `AggregatePKs`, `eth_aggregate_pubkeys`,
  `eth_fast_aggregate_verify`, and a `pairingCheck : List (BLSP × BLSP2) → Bool` (product of Miller loops, one final
  exponentiation), the shape `verifyKzgProofImpl` already uses.
- `decompressG1` exists in `Jaune/Precompiles.lean` with an execution-layer error type. Reuse it by wrapping, and hoist it
  into `Jaune/BLS.lean` with a neutral error only when the master accepts touching the execution surface.
- Acceptance before the vectors: RFC 9380 appendix K.1 (`expand_message_xmd` SHA-256) and appendix J.10.1
  (`BLS12381G2_XMD:SHA-256_SSWU_RO_`) test vectors as `#guard`s, transcribed from the RFC.

### KZG

- EIP-4844 from `specs/deneb/polynomial-commitments.md`; EIP-7594 from `specs/fulu/polynomial-commitments-sampling.md`.
- The trusted setup is `presets/{minimal,mainnet}/trusted_setups/trusted_setup_4096.json` (identical files, SHA-256
  `f8e44a31ebf0a6d0734dcb301b0716e2c77f3ae18ed0cab0870fbcc2ca55616f`; 4,096 G1 monomial, 4,096 G1 Lagrange, 65 G2
  monomial points). A registered generator writes `TrustedSetup.lean` and records that digest; a gate checks it.
  The existing `BLSConst.kzgSetupG2Monomial1` must equal entry 1 of the G2 list, checked by `#guard`.
- `verifyKzgProofImpl` is reused for EIP-4844 point verification.
- `g1_lincomb` is the hot spot: 4,096-term MSMs in commitments and proofs, and 128 of them per
  `compute_cells_and_kzg_proofs`. Plan: projective G1 and a bucket (Pippenger) MSM, tested equal to the naive sum.

### Shuffling

`compute_shuffled_index` exactly as pyspec, on `Bytes.sha256`. The whole-list shuffle stays out of the semantics.

### Harness and runner (O6)

- `jaune-consensus` reads the extracted tree. It refuses to start unless the tree matches the pinned tarballs: the
  inventory script gains a mode that writes a per-file digest manifest from the verified tarball, and the runner checks
  the tree against it.
- Selection by preset, fork, runner, handler. It refuses an empty selection and any count that differs from
  `inventory-v1.6.1.json`. Verdicts are strict all-PASS. Every case runs; none is skipped.
- Snappy block decoder in pure Lean, total by input-length fuel. YAML reader in pure Lean for the subset the vectors use
  (block and flow mappings and sequences, plain and quoted scalars); anything else fails closed.
- BLS policy: `bls_setting` 1 always verifies, 2 never verifies. For 0, both are conformant; the smoke tier runs it off,
  the full tier on if runtime allows.
- Caching lives only in the harness. Since pure Lean cannot memoize without `unsafe` or `implemented_by`, harness
  caching is limited to per-process reuse of closed constants (decompressed setup points) and running a suite in one
  process.
- Tiers: smoke (one case per handler, fixed rule over the inventory) for CI; full for closure. Catalogue rows in
  `scripts/GATES.md` with measured times. Controls per O6: removed case, wrong digest, corrupted post root.

### Performance, honestly

- Measured before (Jaune `scripts/report-ec-pairing-decision.md`, July 2026, macOS, Lean 4.23, compiled `-O2`): one full
  BLS12-381 pairing 920 ms median; Miller loop alone 55 ms. Final exponentiation is about 94 percent, done as a generic
  power by `(p^12 - 1) / r` on list-represented Fp12. No new measurement was taken: this worktree has no `.lake`, and a
  cold Jaune build to time one pairing costs more than it informs at O0. W2's first unit measures on this host.
- At that speed one signature check costs about 1 s. With BLS on for every non-`2` case, the in-scope blocks would need
  hours. With the policy above only the 428 `bls_setting: 1` cases need it.
- The fix is in the primitive, not a cache: split the final exponentiation into easy part (Frobenius, conjugation) and
  hard part, then if needed a fixed-shape Fp2/Fp6/Fp12 tower. Expected 3x from the split, 10x or more with the tower.
  This would serve the execution layer's EIP-2537 lane too; any change to `Jaune/BLS.lean` reruns the EC and BLS gates.
- Hash-to-curve costs two SWU maps, one cofactor multiplication by `hEffG2` (636 bits) and Fp2 square roots. Expect tens
  of milliseconds per message.
- KZG cells: with a bucket MSM, roughly 0.5 s per 4,096-term MSM, so about 1 minute per `compute_cells_and_kzg_proofs`
  or recovery case (29 such cases). Naive affine MSM would take tens of minutes per case.
- State roots: about 0.1 to 0.3 s per mainnet state root with the current SHA-256 kernel (estimate). The 8,192-slot case
  would take roughly 15 to 40 minutes without the incremental root cache.

## (e) Estimate and order

| stream | content | agent-days |
|---|---|---:|
| W1 | SSZ core, progressive types, proofs; ssz_generic | 5 to 8 |
| W2 | BLS ciphersuite and hash-to-curve; final exponentiation speedup; MSM; KZG 4844; KZG cells; shuffle; setup generator | 14 to 22 |
| W3 | presets and config generators, containers and state for Deneb, Electra, Fulu; ssz_static | 4 to 7 |
| W4 | harness: Snappy, YAML, provenance, counts, tiers, gates and controls | 6 to 9 |
| W5 | Electra transition: helpers, operations, epoch, rewards; sanity, finality, random | 14 to 22 |
| W6 | Fulu diff, upgrades, Deneb pre-fork side; fork, transition | 6 to 10 |
| W7 | fork choice, Deneb and Fulu data availability, optimistic sync | 8 to 14 |
| W8 | light client (sync, ranking, data collection), merkle proof, networking | 7 to 12 |
| W9 | fork pairing and shared types | 1 to 2 |
| W10 | integration, catalogue, TRUSTED.md, report; O5 gate extension | 4 to 7 |
| contingency | incremental state root cache, BLS tower | 3 to 8 |
| **total** | | **72 to 121** |

This is above the goal's one-to-two-month judgement. The main drivers are the Deneb transition (c), light-client data
collection, and the KZG and pairing performance work. With three parallel workers the critical path is
W4/W1 → W3 → W5 → W6 → W7, about 45 to 70 agent-days long, so about 6 to 10 weeks elapsed.

Proposed order with three workers:
- **Worker A (W1 then W3):** first unit `JauneConsensus/SSZ/Basic.lean` and `SSZ/Merkle.lean`: uintN, boolean,
  bitvector, bitlist, basic vector and list codecs with every decode check, zero-hash merkleization on `Bytes.sha256`,
  `#guard`s from hand-picked vectors. Target: ssz_generic `uints`, `boolean`, `bitvector`, `bitlist`, `basic_vector`
  (1,808 cases) once W4's reader lands.
- **Worker B (W2):** first unit `Crypto/HashToCurve.lean` plus `Crypto/Codec.lean`: `expandMessageXmd`, hash-to-field,
  hash-to-G2 reusing `optimizedSwuG2`/`isoMapG2`/`hEffG2`, G2 decompression, `pairingCheck`, with RFC 9380 K.1 and J.10.1
  `#guard`s; measure one pairing and one hash-to-curve on this host. Then `eth_*` bls (20 cases), shuffling, final
  exponentiation, MSM, KZG 4844, KZG cells.
- **Worker C (W4 then W9, then W5 epoch processing):** first unit the harness skeleton: `jaune-consensus` executable,
  pure-Lean Snappy decoder, YAML subset reader, extracted-tree manifest check, selection with empty and count refusals
  against `inventory-v1.6.1.json`, shuffling runner as the first end-to-end suite. Then `JauneConsensus/Fork.lean` (W9):
  `CFork`, pairing with `Jaune.Fork`, Gloas refusal, blob-schedule and request-type ties.
- After `ssz_static` is green, W5 splits: operations (A) and epoch processing plus rewards (C); W2's worker moves to W6.

## Decisions for the record

Master-level (recommendations):
1. Consensus tree outside `Jaune/` with its own library and assurance library (forced by `check_union_coverage` and
   Blanc's `needs`).
2. Fork-indexed containers with gated fields; preset limits in types.
3. `U64` without arithmetic instances; `Except Reject` everywhere.
4. Pure-Lean Snappy and YAML in the harness, rather than a Python preprocessor (PyYAML is present but unpinned).
5. `bls_setting: 0` off in smoke, on in full if runtime allows.
6. Implement the progressive SSZ types and count them in scope.
7. Fix BLS speed in the primitive (final exponentiation), not by caching.

Possibly reserved for the user:
1. O2 names `genesis`, but the release has no Electra or Fulu genesis cases. Either O2's text changes, or genesis is
   implemented without vector evidence.
2. Whether an incremental Merkle root cache inside the state representation is consistent with §5 "caches live only in
   the harness". I read §5 as forbidding oracle memoization, not a data structure with a proved invariant.
3. Supplementary core BLS vectors from outside this release would raise a licence question, so they are not proposed
   unless the user wants them.
4. Publication: these files sit outside `docs/` to avoid GitHub Pages.
