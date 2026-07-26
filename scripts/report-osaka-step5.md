# Step 5 report — static Osaka transaction and block rules

Date: 2026-07-27 (Asia/Seoul). Plan: `~/plans/migration.md`, Step 5.

## Authoritative inputs

The executable reference is the same immutable revision used by Step 4:

| what | value |
|---|---|
| fixture release | `tests@v20.0.1` |
| execution-specs commit | `87aba1a38a476b31f819a2390eb481527e6dc683` |
| diffed trees | `src/ethereum/forks/prague` → `src/ethereum/forks/osaka` |
| EIP status checked | EIP-7594, 7825, 7918, 7934: Final |

The EELS trees are read from the pinned Git object database with
`git show 87aba1a3:…`; the legacy generator checkout remains at its independent
pin. Final EIPs explain the rule and its boundary, while this pinned EELS diff
fixes executable ordering for the fixture release.

## Reviewed Prague-to-Osaka delta table

This table accounts for every behavioural difference in the pinned EELS diff.
It is the Step-5 pre-implementation checkpoint; later sections record the
actual definitions, guards, fixtures, and commits as each row lands.

| source / EIP | executable delta | ELeVM destination | focused evidence | status |
|---|---|---|---|---|
| EIP-7823 | bound each MODEXP length header at 1024 | `ForkRules.modexp`, `modexpLengthsInBounds` | authoritative MODEXP vectors and `eip7823_modexp_upper_bounds` | Step 4, done |
| EIP-7883 | Osaka MODEXP gas schedule | `ForkRules.modexp`, `modexpGascost` | authoritative MODEXP vectors and `eip7883_modexp_gas_increase` | Step 4, done |
| EIP-7939 | CLZ opcode at 0x1E, LOW gas | `ForkRules.op`, `Rinst.runCore` | boundary guards and `eip7939_count_leading_zeros` | Step 4, done |
| EIP-7951 | P256VERIFY at 0x100, 6900 gas | `ForkRules.precompiles`, `executeP256Verify` | 782 upstream vectors and `eip7951_p256verify_precompiles` | Step 4, done |
| EIP-7825 | reject a transaction whose gas limit is greater than `2^24` | transaction-limit rule data; `validateTransaction` after intrinsic/initcode validation and before nonce overflow, matching EELS | just-below/at/above guards; `eip7825_transaction_gas_limit_cap` | Step 5, planned |
| EIP-7594 | reject a blob transaction with more than six blobs | transaction-limit rule data; `checkTransactionBlobData` after the zero-blob check and before version-byte/fee checks, matching EELS | 5/6/7-blob guards; `eip7594_peerdas/max_blob_per_tx` | Step 5, planned |
| EIP-7918 | reserve-price branch in the child's excess-blob-gas calculation, with `BLOB_BASE_COST = 2^13`; use the current child schedule's target/max/update fraction and the parent header's base fees | blob rule data; `calculateExcessBlobGas` | branch/equality and target-boundary guards; `eip7918_blob_reserve_price` | Step 5, planned |
| EIP-7934 | reject original RLP block bytes longer than `10 MiB - 2 MiB = 8,388,608` bytes, before header validation | block-limit rule data; raw byte length carried by the block-import path without replacing canonical decode, round-trip, or header-hash checks | just-below/at/above guards; `eip7934_block_rlp_limit` | Step 5, planned |
| EIP-7892 | express Osaka blob limits as target/max blob counts 6/9 times `2^17` | `osakaBlobSchedule` | existing schedule equality guards | Step 4 data, done; BPO changes are Step 6 |
| EIP-7607 / fork identity | Osaka identity and activation schedule | static `.osaka` is implemented; named mainnet `ChainConfig` belongs to Step 6 | static Osaka suite here; activation boundary fixtures in Step 6 | split by plan |
| EIP-7935 | default 60M block gas-limit notice | no consensus formula change: a proposer/configuration default is not an execution-validity rule | EELS changes only the `Header.gas_limit` docstring | out of scope |
| EIP-7642 | `eth/69` history expiry / receipts protocol | no block-import, state-transition, or EVM rule in the pinned Prague/Osaka code diff | EELS fork-module diff has no executable implementation | networking, out of scope |
| EIP-7910 | `eth_config` JSON-RPC method | no ELeVM RPC subsystem and no executable fork-module delta | no current `blockchain_tests` semantic row | RPC, out of scope |
| remaining EELS files | fork-qualified doc links, comment deletion, and formatting | none | reviewed file-by-file diff | non-behavioural |

### Check-order contract

The order is part of the implementation:

1. `validateTransaction`: intrinsic/calldata-floor gas, initcode size,
   transaction gas cap, nonce maximum.
2. Blob transaction checks inside `checkTransaction`: aggregate block gas/blob
   availability, chain ID/sender/fee calculation, zero blobs, per-transaction
   blob count, blob-version bytes, blob fee, then the pre-existing receiver,
   authorization, and account checks.
3. Block import: strict RLP decoding and canonical byte round trip remain
   harness-level prerequisites. The authoritative original byte length is then
   checked as the first consensus validity rule, before header validation.

The EIP-7934 EELS function calls `rlp.encode(block)` because its `state_transition`
API is handed only a decoded object. ELeVM's public fixture/block-import API is
handed the original bytes. Using those bytes is strictly stronger evidence and
avoids accepting an oversized noncanonical input by measuring a shorter
re-encoding; canonical decoding and the existing header-hash check remain
independent and unchanged.

## What changed

Delta-table checkpoint only. No production semantics changed in this first
commit.

## Verification

The checkpoint is documentation-only. Repository status/diff and the pinned
EELS tree diff were reviewed before commit. Semantic verification is recorded
below as the implementation lands.

## Evidence

The pinned static Osaka manifest contains 2,514 files / 17,323 cases. The four
Step-5 focused static subtrees contain:

| subtree | files | Osaka cases |
|---|---:|---:|
| `eip7825_transaction_gas_limit_cap` | 11 | 37 |
| `eip7918_blob_reserve_price` | 2 | 86 |
| `eip7934_block_rlp_limit` | 4 | 10 |
| `eip7594_peerdas/max_blob_per_tx` | 2 | 10 |

Transition-labelled files under the same EIP directories remain Step 6.

## Unexpected findings

The EELS diff contains the EIP-7594 six-blob per-transaction execution rule in
addition to the three rules anticipated by the Step-5 checklist. It is not
networking-only: the final EIP requires enforcement during block processing
and the static Osaka fixture lane has invalid-block cases for it.

## Scope check

Prague wrappers, legacy baselines, generated manifests, `Hash.fB64` /
`B64.rdnc`, and Blanc are untouched by the delta-table checkpoint. No source
definition, proof, fixture classification, expected-failure baseline, or
generated artifact changed.

## Commit ledger

Populated at each autonomous checkpoint.

## Recovery state

Starting independently green commits:

- ELeVM `codex/migration`: `e1f9eda` (pushed Step-4 report tip).
- Blanc `codex/migration`: `9e66c9c` (pushed Step-4 proof-integration tip).

Both trees were clean at Step-5 start.

## Autonomous decisions

The planned rule-data split is `TransactionLimits`, the existing
`BlobSchedule`, and `BlockLimits`, all fields of `ForkRules`. This keeps
activation data central without coupling transaction or block limits to opcode
rules. The EIP-7934 check uses the exact input `B8L.length`; it does not add raw
bytes to the public `Block` structure and therefore does not redesign the
Step-2 API.

## Human decisions pending

None at the delta-table checkpoint. A new major subsystem, ambiguous
fixture/spec mismatch, Prague regression, or public API redesign remains a stop
condition.

## Next handoff

Implement EIP-7825 from this reviewed table, then EIP-7918, then EIP-7934 plus
the bounded EIP-7594 remaining row. Static Osaka is activated only after the
whole exact suite is green.
