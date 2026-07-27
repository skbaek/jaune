# Step 5 report — complete static Osaka execution

Date: 2026-07-27 (Asia/Seoul). Plan: `~/plans/migration.md`, Step 5.

## Authoritative inputs

The executable reference is the same immutable revision used by Step 4:

| what | value |
|---|---|
| fixture release | `tests@v20.0.1` |
| execution-specs commit | `87aba1a38a476b31f819a2390eb481527e6dc683` |
| diffed trees | `src/ethereum/forks/prague` → `src/ethereum/forks/osaka` |
| final EIPs reviewed | EIP-7594, EIP-7825, EIP-7918, EIP-7934 |

The EELS trees were read from the pinned Git object database with
`git show 87aba1a3:…`; the independently pinned legacy generator checkout was
not moved. Final EIPs fix the rules and boundaries, while this pinned EELS diff
fixes executable ordering for the fixture release.

## Audited Prague-to-Osaka delta table

Every behavioural difference in the pinned EELS fork-module diff is mapped to
code and evidence, or to a bounded reason for not changing ELeVM.

| source / EIP | executable delta | ELeVM code | focused evidence | disposition |
|---|---|---|---|---|
| EIP-7823 | bound each MODEXP length header at 1024 | `ForkRules.modexp`, `modexpLengthsInBounds` | authoritative vectors; `eip7823_modexp_upper_bounds` 3/3 files | Step 4, done |
| EIP-7883 | Osaka MODEXP gas schedule | `ForkRules.modexp`, `modexpGascost` | authoritative vectors; `eip7883_modexp_gas_increase` 13/13 | Step 4, done |
| EIP-7939 | CLZ opcode at 0x1E, LOW gas | `ForkRules.op`, `Rinst.runCore` | boundary guards; `eip7939_count_leading_zeros` 14/14 | Step 4, done |
| EIP-7951 | P256VERIFY at 0x100, 6900 gas | `ForkRules.precompiles`, `executeP256Verify` | 782 upstream vectors; `eip7951_p256verify_precompiles` 14/14 | Step 4, done |
| EIP-7825 | reject transaction gas limits greater than `2^24` | `TransactionLimits.maxGas`, `checkTransactionGasCap`, `validateTransaction` | below/at/above guards; subtree 11/11 files, 37 cases | Step 5, done |
| EIP-7594 | reject type-3 transactions with more than six blobs | `TransactionLimits.maxBlobCount`, `checkTransactionBlobCount`, `checkTransactionBlobData` | 5/6/7 guards; subtree 2/2 files, 10 cases | Step 5, done |
| EIP-7918 | reserve-price branch in child excess-blob-gas calculation, `BLOB_BASE_COST = 2^13` | `BlobSchedule.reserveBaseCost`, `calculateExcessBlobGas` | equality/branch/target guards; subtree 2/2 files, 86 cases | Step 5, done |
| EIP-7934 | reject original block RLP above `10 MiB - 2 MiB = 8,388,608` bytes before header validation | `BlockLimits.maxRlpSize`, `checkBlockRlpSize`, private `addBlockToChainCore` raw-length argument | below/at/above guards; subtree 4/4 files, 10 cases | Step 5, done |
| EIP-7892 | express Osaka blob target/max as counts 6/9 times `2^17` | `osakaBlobSchedule` | schedule equality guards | Step 4 data, done; BPO changes are Step 6 |
| EIP-7607 / fork identity | Osaka identity and activation schedule | static `.osaka` rules and suite are complete; named mainnet `ChainConfig` remains Step 6 | full static Osaka suite here; activation boundaries in Step 6 | split by plan |
| EIP-7935 | default 60M block-gas-limit notice | no consensus formula change; EELS changes a `Header.gas_limit` docstring | file-by-file diff | proposer/configuration default, out of scope |
| EIP-7642 | `eth/69` history expiry / receipts protocol | no EVM, transition, or block-import rule in the pinned diff | file-by-file diff | networking, out of scope |
| EIP-7910 | `eth_config` JSON-RPC method | no ELeVM RPC subsystem or executable fork-module delta | no blockchain-test semantic row | RPC, out of scope |
| remaining EELS files | fork-qualified links, comment deletion, formatting | none | file-by-file diff | non-behavioural |

No unmapped execution rule remains in the pinned Prague-to-Osaka diff.

## What changed

### Central rule data

`Elevm/Fork.lean` adds two named subordinate records and extends the existing
blob schedule:

- `TransactionLimits.maxGas` and `.maxBlobCount`;
- `BlockLimits.maxRlpSize`;
- `BlobSchedule.reserveBaseCost`.

They are fields of `ForkRules`. Prague carries `none` for every new rule, while
Osaka carries `2^24`, `6`, `8,388,608`, and `2^13`. No use site compares fork
identities and no sentinel encodes an inactive rule.

### EIP-7825 transaction gas cap

`checkTransactionGasCap` uses a strict `>` boundary. `validateTransaction`
retains Prague's established nonce-before-initcode diagnostic precedence when
`maxGas = none`; Osaka follows EELS ordering: intrinsic/floor gas, initcode,
gas cap, nonce. `transactionGasLimitExceededTag` maps strictly to
`TransactionException.GAS_LIMIT_EXCEEDS_MAXIMUM` without changing legacy tags.

### EIP-7594 per-transaction blob count

`checkTransactionBlobCount` runs after the zero-blob check and before
version-byte and blob-fee checks. A distinct producer tag preserves precise
internal provenance while both historical and Osaka over-count tags map to the
canonical fixture exception `TYPE_3_TX_BLOB_COUNT_EXCEEDED`.

### EIP-7918 blob reserve price

`calculateExcessBlobGas` keeps the below-target zero branch first. Prague then
uses its original `parent excess + used - target` formula. Osaka compares
`reserveBaseCost * parent.baseFeePerGas` strictly against
`gasPerBlob * calculate_blob_gas_price blob parent.excessBlobGas`; only the
strictly greater branch applies the reserve adjustment. Both fees come from
the parent header and schedule data comes from the child rules, matching EELS.

### EIP-7934 original RLP size

The public `addBlockToChain*` signatures are unchanged. The private decoded
core receives `blockRlp.length` from both explicit and configured import paths.
Strict RLP decode/round-trip and independent header-hash evidence remain
harness prerequisites; the original byte length is then the first consensus
check, before `stateTransitionWith` reaches header validation. No shorter
re-encoding substitutes for the authoritative input size.

### Harness and strict exceptions

`FixtureException.lean` adds only the exact upstream enum mappings needed for
the new transaction and block failures. `check-mainnet.sh --suite osaka` is now
an active all-PASS gate; BPO1, BPO2, transitions, and the union suite remain
strictly inactive until their owning steps. No expected-failure baseline or
generated manifest changed.

## Boundary and focused evidence

All guards elaborate in the project build.

| rule | explicit guard points | focused current fixture result |
|---|---|---|
| EIP-7825 | `2^24 - 1`, `2^24`, `2^24 + 1`; Prague remains uncapped | 11/11 files, 37 cases; 4.29s harness / 10.04s real |
| EIP-7594 | 5, 6, 7 blobs; Prague remains uncapped | 2/2 files, 10 cases; 1.15s / 6.40s real |
| EIP-7918 | reserve equality at base fee 16, strict branch at 17, below target, just above target, Prague classic branch | 2/2 files, 86 cases; 1.55s / 6.20s real |
| EIP-7934 | 8,388,607, 8,388,608, 8,388,609 bytes; Prague remains uncapped | 4/4 files, 10 cases; 18.60s / 23.00s real |

Step-4 Osaka subtrees were rerun after the integrated Step-5 semantics:
EIP-7823 3/3 files (0.20s), EIP-7883 13/13 (1.21s), EIP-7939 14/14
(3.44s), and EIP-7951 14/14 (11.01s). Transition-labelled fixtures remain
owned by Step 6.

## Verification

All ELeVM semantic gates used the executable built from
`c2a4a20d630dd6d8aef2d14429f40541a8e84c8b`; its SHA-256 was
`22d70676e66dad447dd44ee7a122d5e87f9f1d13c61610e10fecbf286a25443d`.
Commit `598046f` only activates the already-green suite selector.

| gate | verdict | measured time |
|---|---|---:|
| Lean MCP project build, including all `#guard`s | OK | — |
| LSP diagnostics: `Fork.lean`, `Execution.lean`, `FixtureException.lean` | clean | — |
| `python3 -m unittest discover -s scripts/tests` | 102 tests OK; manifest exact | 13.220s (13.33s real) |
| `scripts/check-u256.sh` | 21,593/21,593 PASS | 0.23s real |
| `scripts/check-vectors.sh` | 44/44 files PASS; controls 5/5 | 465.77s real |
| `scripts/check.sh --patch --no-build` | 10/10 PASS | 0.56s real |
| `scripts/check.sh --rlp4 --no-build` | 4/4 PASS | 0.14s real |
| `scripts/check.sh --depth --no-build` | 67/67 match baseline | 12.11s real |
| `scripts/check.sh --smoke --no-build` | 174/174 match baseline (173 PASS / 1 expected FAIL) | 91.17s real |
| `scripts/check.sh --bls --no-build` | 29/29 match baseline | 147.73s real |
| `check-mainnet.sh --suite smoke --no-build` | 16/16 PASS | 0.50s harness / 6.10s real |
| `check-mainnet.sh --suite prague --no-build` | 2,573/2,573 PASS | 17,852.95s harness / 18,800.02s real |
| `check-mainnet.sh --suite osaka --no-build` | 2,514/2,514 PASS, 17,323 cases | **495.82s harness / 500.45s real** |

The Prague timing output is recorded verbatim. It showed an exceptional
wall/CPU gap (`18,800.02s real`, `750.25s user`), so it is evidence of a green
verdict, not a stable performance measurement. The one-time full Osaka run was
within the plan's ten-minute threshold. Legacy FULL remains the user-owned
closure gate and was not substituted by smoke.

## Blanc integration

Blanc policy pins semantic ELeVM checkpoints rather than documentation-only
tips, so `lakefile.lean`, `lake-manifest.json`, and
`.lake/packages/elevm/HEAD` all consume
`c2a4a20d630dd6d8aef2d14429f40541a8e84c8b`.

Generic proofs were repaired for the new `validateTransaction` rule split, the
new successful blob-count bind, and the raw-RLP check in block import. No
fork-specific theorem copy was added. The Lean MCP build completed all 907
jobs; `scripts/check.sh --no-build` audited all four protected theorems in
1.20s. Independent `lean_verify` checks reported exactly
`[propext, Classical.choice, Quot.sound]`, with no warnings, for:

- `weth_inv_solvent`;
- `stateTransition_inv_solvent`;
- `chain_inv_solvent`;
- `addBlockToChain_inv_solvent`.

## Unexpected findings

The pinned EELS diff includes EIP-7594's six-blob per-transaction execution
rule in addition to the three rules anticipated by the plan. It is not
networking-only: static Osaka has invalid-block fixtures for it. The rule was
therefore implemented and committed as its own bounded semantic concern.

The only verification anomaly was the Prague wall/CPU timing gap recorded
above; the strict classification remained 2,573/2,573 PASS.

## Scope check

- Prague wrappers and public transition/block-import signatures are unchanged.
- Current Prague is 2,573/2,573 PASS and every required legacy short baseline
  matches; no Prague failure or classification was accepted.
- No expected-failure baseline, generated manifest, fixture, or exclusion was
  edited. Osaka has no expected-failure allowance.
- `Hash.fB64`, `B64.rdnc`, legacy bootstrap code, and the frozen FULL corpus are
  untouched.
- BPO1/BPO2 identities, schedule activation, and transition suites remain Step
  6; no Osaka rule was copied into them.
- No `sorry`, `admit`, new axiom, `ofReduceBool`, or `ofReduceNat` was added.

## Commit ledger

| repo | branch | commit | purpose | pushed |
|---|---|---|---|---|
| ELeVM | `codex/migration` | `feb7128` | reviewed authoritative delta table | yes |
| ELeVM | `codex/migration` | `1bfbfc0` | EIP-7825 transaction gas cap | yes |
| ELeVM | `codex/migration` | `0196ace` | EIP-7918 reserve-price formula | yes |
| ELeVM | `codex/migration` | `f4dbe2e` | EIP-7594 per-transaction blob count | yes |
| ELeVM | `codex/migration` | `c2a4a20` | EIP-7934 original-RLP block limit | yes |
| ELeVM | `codex/migration` | `598046f` | activate the full static Osaka suite | yes |
| Blanc | `codex/migration` | `a66fd9d` | pin `c2a4a20`; generic proof repair and audit | yes |

## Recovery state and next handoff

The independent green semantic checkpoint is ELeVM `c2a4a20`; the pushed
static-suite checkpoint is `598046f`; Blanc's pushed proof checkpoint is
`a66fd9d`. Step 6 should start from these commits, resolve the authoritative
BPO1/BPO2 schedule, and add configured activation/transition semantics without
copying the now-complete static Osaka execution rules.

No human decision is pending for Step 5.
