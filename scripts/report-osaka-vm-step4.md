# Step 4 report — the Osaka VM delta

Date: 2026-07-27 (Asia/Seoul). Plan: `~/plans/migration.md`, Step 4.

## Executable reference

The Prague-to-Osaka diff was taken from the EELS revision the fixture release
resolves to, which `scripts/sources.json` already pins as
`current_mainnet.release_commit`:

| what | value |
|---|---|
| fixture release | `tests@v20.0.1` |
| execution-specs commit | `87aba1a38a476b31f819a2390eb481527e6dc683` |
| diffed trees | `src/ethereum/forks/prague` → `src/ethereum/forks/osaka` |

Note for later steps: at that revision EELS has moved the fork modules under
`src/ethereum/forks/`, whereas the separately pinned legacy checkout
(`4198b9c5…`) still has them at `src/ethereum/<fork>`. Read the Osaka sources
out of the object database (`git show 87aba1a3:…`); do not check the legacy
working tree out to that revision, since the generators enforce its pin.

## The delta table

Every execution-layer change in that diff, and where it lands.

| EIP | change | step | status |
|---|---|---|---|
| 7823 | `MODEXP` base/exponent/modulus length headers bounded at 1024 | 4 | done |
| 7883 | `MODEXP` repricing: flat complexity 16 at ≤ 32 bytes, `2 * words²` above, doubled exponent-length weight, no `GQUADDIVISOR`, floor 500 | 4 | done |
| 7939 | `CLZ` (0x1E), `LOW` gas, pushes `256 - bit_length(x)` | 4 | done |
| 7951 | `P256VERIFY` at 0x100, flat 6900 gas | 4 | done |
| 7825 | `TX_MAX_GAS_LIMIT = 16_777_216` in `validate_transaction` | 5 | not implemented |
| 7918 | blob base-fee reserve price in `calculate_excess_blob_gas`, using the new `BLOB_BASE_COST = 2^13` and the blob-count schedule | 5 | not implemented |
| 7934 | `MAX_RLP_BLOCK_SIZE = 10_485_760 - 2_097_152`, checked on the block's own RLP before header validation | 5 | not implemented |
| 7594 | `BLOB_COUNT_LIMIT = 6` per blob transaction (`BlobCountExceededError`) | 5 | not implemented |
| 7892 | blob schedule restated as counts (`TARGET = 6`, `MAX = 9`, `× 2^17`) | 4 | data only; evaluates to Prague's numbers |
| 7607, 7935, 7642, 7910 | fork identity, default gas-limit notice, networking, RPC | — | out of scope (not execution rules) |

Non-EIP differences in the diff are docstring cross-references, comment
removals in `sstore`, and formatting; none change behaviour.

### Unexpected finding: EIP-7594's per-transaction blob count limit

The plan's Step-5 checklist anticipates EIP-7825, EIP-7918, and EIP-7934. The
EELS diff also adds a **per-transaction blob count limit** of 6 in
`check_transaction`, raising `BlobCountExceededError`. It is a real
execution-layer rejection reason with its own fixture subtree
(`for_osaka/osaka/eip7594_peerdas/max_blob_per_tx`), so Step 5's delta table
must carry it. This is exactly the case the plan anticipated when it said the
checklist is not authority.

### Note on Osaka's blob schedule

`MAX_BLOB_GAS_PER_BLOCK` and `BLOB_TARGET_GAS_PER_BLOCK` are no longer written
as literals at Osaka; they are `BLOB_SCHEDULE_MAX * PER_BLOB` and
`BLOB_SCHEDULE_TARGET * PER_BLOB` with counts 9 and 6. Those evaluate to
1179648 and 786432, i.e. Prague's values. `osakaBlobSchedule` states the
products rather than copying Prague's numbers, and a `#guard` checks the
equality. BPO1/BPO2 vary the counts, which is Step 6.

## What changed

`Elevm/Fork.lean`
- `ModexpRules` (`maxLength`, `flatComplexity`, `complexityCoeff`,
  `iterationCoeff`, `gasDivisor`, `minGas`) and `OpcodeRules` (`clz`), both
  carried by `ForkRules`.
- `pragueModexpRules`, `pragueOpcodeRules`; `osakaBlobSchedule`,
  `osakaModexpRules`, `osakaOpcodeRules`, `osakaPrecompiles`, `osakaRules`.
- `Fork.osaka.rules?` now resolves.

`Elevm/Types.lean`
- `Rinst.clz`, its `toString`, and `B8.toRinst 0x1e`.

`Elevm/Execution.lean`
- `modexpComplexity`/`modexpIterations`/`modexpGascost` take `ModexpRules`;
  `modexpLengthsInBounds` and the `modexpInputLimitTag` exceptional halt.
- `B64.leadingZeros`, `B256.leadingZeros`, and the `Rinst.runCore` `.clz` case.
- `gasP256Verify`, `executeP256Verify`, and `precompileRun`'s 0x100 case.
- `prepareMessage` derives EIP-2929's pre-warmed access list from
  `rules.precompiles` instead of a literal `[1 … 17]`.

`Elevm/EC.lean`
- `secp256r1`: curve constants, base point, and `verify`.

`Main.lean`
- `--vectors` takes `--network`; the runner refuses a file whose address is not
  a precompile under that fork.

Scripts and docs: `check-vectors.sh` gains an Osaka group and a per-file fork;
`check-mainnet.sh` gains `--dir`; `SOURCES.md` pins the two new vector files;
`README.md` and `report-fork-architecture.md` record Osaka's partial state.

Two vector files added, both from go-ethereum
`ca1f2e4d38f4e94676981bb9251239a5d490b004`:
`modexp_eip7883.json` (45 cases, SHA-256 `b66970a3…1719983`) and
`p256Verify.json` (782 cases, SHA-256 `72be7195…8c214d`).

No files deleted.

## Design decisions

**MODEXP as rule data, not a branch.** Both schedules are the same formula over
six numbers. `flatComplexity`/`maxLength` are `Option`, so Prague's absence of
a rule is stated rather than encoded as a sentinel.

**CLZ is gated at execution, not at decode.** `B8.toRinst` maps 0x1E at every
fork; `Rinst.runCore` checks `rules.op.clz` before the operand pop and returns
`InvalidOpcode` when the opcode is undefined. This is observationally identical
to EELS, where the byte is absent from the fork's opcode map: an invalid
instruction consumes the frame whatever the stack and gas hold, which the
guards pin for the empty-stack and zero-gas cases. Gating at decode instead
would have made `ByteArray.getInst` — and therefore Blanc's `Rinst.At`,
`Ninst.At`, `Jinst.At`, and `Linst.At` predicates — fork-dependent, which is a
much larger downstream change for no behavioural difference.

**P256VERIFY uses the generic affine ladder.** secp256r1 has `a ≠ 0`, so the
Jacobian formulas in `EC.lean` (the `shortw-jacobian-0` family, used by
BN128/BLS and secp256k1) do not apply to it. `EllipticCurve.mulBy` already
dispatches `a ≠ 0` to the affine ladder, so no new curve formula was written.
One verification costs about 26 ms. Adding a general-`a` Jacobian doubling
would be a performance change to shared curve code, which the plan lists as a
non-goal.

**The base point is checked, not trusted.** `#guard`s assert the generator is
on the curve, that multiplying it by the stated group order reaches infinity,
and that `a = p - 3`; a transcription error in any of the six literals would
have to survive all three, plus 782 upstream vectors.

## Verification

All results below are on `bc20ef9` unless noted; the binary was rebuilt before
each block.

| gate | verdict | wall time |
|---|---|---|
| `lake build` (all `#guard`s) | OK | — |
| `python3 -m unittest discover -s scripts/tests` | 102 tests OK | 13 s |
| `scripts/check-u256.sh` | 21593/21593 PASS | < 1 s |
| `scripts/check-vectors.sh` | 44/44 files PASS, controls 5/5 | 7 m 56 s |
| ↳ `modexp_eip2565.json` (Prague) | 47/47 PASS | — |
| ↳ `modexp_eip7883.json` (Osaka) | 45/45 PASS | — |
| ↳ `p256Verify.json` (Osaka) | 782/782 PASS | 20 s |
| `scripts/check.sh --patch --no-build` | 10/10 PASS | < 1 s |
| `scripts/check.sh --rlp4 --no-build` | 4/4 PASS | < 1 s |
| `scripts/check.sh --depth --no-build` | 67/67 match baseline | 2 s |
| `scripts/check.sh --smoke --no-build` | 174 match baseline (173 PASS / 1 FAIL) | 92 s |
| `scripts/check.sh --bls --no-build` | 29/29 match baseline | 2 m 27 s |
| `check-mainnet.sh --suite smoke --no-build` | 16/16 PASS | 0.5 s |
| `check-mainnet.sh --suite prague --no-build` | 2573/2573 PASS | 11 m 59 s |
| `--suite osaka --dir …/eip7823_modexp_upper_bounds` | 3/3 PASS | 0.3 s |
| `--suite osaka --dir …/eip7883_modexp_gas_increase` | 13/13 PASS | 1.3 s |
| `--suite osaka --dir …/eip7939_count_leading_zeros` | 14/14 PASS | 3.5 s |
| `--suite osaka --dir …/eip7951_p256verify_precompiles` | 14/14 PASS | 11.0 s |

Legacy FULL (~30 min) remains user-owned and was not re-run in this step; its
last verdict is on the Step-1 commit. No legacy classification changed in any
gate that was run, and no expected-FAIL baseline was touched.

### Cross-fork checks

- `modexp_eip7883.json` under Prague: 0/45 — the whole file fails, as it must.
- `modexp_eip2565.json` under Osaka: 0/47 — likewise.
- `p256Verify.json` under Prague: refused, because 0x100 is not a precompile
  under Prague rules.
- `CLZ` under Prague: `InvalidOpcode` with a populated stack, an empty stack,
  and zero gas alike.

### Informational: the Step-5 subtrees

Run for information only, not as gates. Each is red on exactly the rule Step 5
owns, which is the intended boundary:

| subtree | first failure |
|---|---|
| `eip7825_transaction_gas_limit_cap` | `tx_gas_limit_cap_exceeded.json` |
| `eip7918_blob_reserve_price` | `reserve_price_boundary.json` |
| `eip7934_block_rlp_limit` | `block_at_rlp_size_limit_boundary.json` |
| `eip7594_peerdas` | `invalid_max_blobs_per_tx.json` |

## Harness change

`check-mainnet.sh --dir REL --suite SUITE` restricts a suite to one subtree of
the pinned archive. It is not a way to reach an inactive suite as a whole:
entries still come from the generated manifest, every one must PASS, and a
selection that is empty, escapes the fixture root, or does not account for
every `.json` on disk under the subtree is an error. `--suite osaka` without
`--dir` remains refused, so nothing reports Osaka as conformant before Step 5.

## Scope check

- Prague behaviour is unchanged: 2573/2573 current Prague cases, all legacy
  baselines matching, 47/47 Prague MODEXP vectors, and no change to Prague's
  precompile set or pre-warmed access list (`praguePrecompiles` is exactly the
  literal `[1 … 17]` the old code inlined).
- `Hash.fB64` and the `B64.rdnc` decision are untouched.
- Strict manifests are unchanged; `scripts/mainnet/manifests.json` was not
  regenerated and still verifies against the archive.
- The Step-2 fork API is unchanged: no entry point was renamed or resignatured,
  and rules still reach execution only through `BenvStat.rules`.
- No `sorry`, `admit`, new axiom, or `ofReduce*` was introduced.

## Commit ledger

| repo | branch | hash | purpose | pre-commit gates | pushed |
|---|---|---|---|---|---|
| elevm | `codex/migration` | `c61ff3b` | MODEXP bounds and repricing; Osaka rules resolve | build, u256, vectors 43/43, patch, rlp4, depth, smoke, current smoke, both MODEXP subtrees, python tests | yes |
| elevm | `codex/migration` | `28a35b6` | CLZ | build, CLZ subtree 14/14, u256, smoke, depth, patch, rlp4, current smoke | yes |
| elevm | `codex/migration` | `bc20ef9` | P256VERIFY; access list from rules | build, vectors 44/44, all four subtrees, current prague 2573/2573, current smoke, u256, smoke, bls, depth, patch, rlp4 | yes |

## Next handoff

Blanc pins the pushed ELeVM commit that carries `Rinst.clz`. Step 5 starts from
the delta table above, whose remaining rows are EIP-7825, EIP-7918, EIP-7934,
and the EIP-7594 blob count limit.
