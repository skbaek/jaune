# Flatten the interpreter recursion and thin Blanc shadows — closure report

**Plan:** `~/plans/flatten.md` (Steps 1–4).
**Closure date:** 2026-07-28 (Asia/Seoul).
**Candidate branches:** `elevm` `codex/flatten` at
`fed6c71fe95361d4bcf328bc64f7e132cc453775` (documentation tip; semantic core
`1d67748023623ffef3d24ba9cdbc2095586da30b`) and `blanc` `codex/flatten` at
`39ed4a3c67db237fb41030b625d1b9492e5f3c34`.

## Final state

ELeVM has one recursive interpreter driver, `exec : Evm → Nat → Fueled
(String × Devm) Devm`.  `Frame`, `FrameEntry`, `Resume`, `XStep`, and `Step`
make all frame-local work non-recursive and fuel-free.  `runFrame`,
`executeCode`, `processMessage`, and `processCreateMessage` are non-recursive
wrappers; `genericCreate.step`, `genericCall.step`, `Xinst.step`, `Ninst.step`,
and `Evm.step` contain the old local semantic branches.

The old eight-way mutual interpreter block is deleted.  The only `mutual` left
in `Elevm/Execution.lean` is unrelated type-level code; there is no mutual
recursive interpreter.  The public call/create boundary remains unchanged:
`msg.gas + 50` is still seeded and exhaustion still becomes exactly
`"RecursionLimit"`.

Blanc is pinned to the pushed semantic ELeVM commit
`1d67748023623ffef3d24ba9cdbc2095586da30b`.  The revision agrees in
`lakefile.lean`, `lake-manifest.json`, and the real (not symlinked) managed
checkout.  `Blanc/Semantics.lean` has one six-constructor `Exec` derivation
relation, driver-level adequacy/monotonicity, and thin wrappers for the former
mirrors.  The former per-function `Saturation` record and bind-walking macros
are absent.  The detailed Step-3 implementation and its statement deltas are
recorded in `scripts/report-flatten-step3.md`.

## Refactor delta table

| Old region | Final home |
|---|---|
| `executeCode` initialization and precompile split | `executeCode.enter` |
| `processMessage` transfer/rollback | `Frame.enter`, `processMessage.settle` |
| create preprocessing, deposit and exceptional halt | `Frame.ofCreate`, `processCreateMessage.settle` |
| CREATE/CREATE2 construction and collision exits | `createMsg`, `genericCreate.step` |
| CALL-family depth exit and child construction | `callMsg`, `genericCall.step` |
| six `Xinst.run` branches | `Xinst.step` |
| PUSH/REG/X dispatch and PC advance | `Ninst.step` |
| decode/JUMP/LAST and frame continuation | `Evm.step`, `exec` |
| child incorporation/output copy | `Resume.run` |
| public message execution | `runFrame` and public wrappers |

No semantic branch was omitted; only dead debug commentary and the now-dead
fuel plumbing were removed.

## Fuel and interface accounting

`exec` is the sole driver.  It consumes one unit per instruction, as the old
`exec` did.  The old recursive wrapper tower additionally consumed five units
on a CALL-family child entry and six on a CREATE-family child entry; the new
frame-local entry is fuel-free.  Thus consumption is equal within a frame and
strictly lower at every child entry, so the unchanged `gas + 50` boundary is
not weakened.

Instruction semantics (`Rinst`, `Jinst`, `Linst`, decoding, precompiles, gas
constants, `Footprint`, and `liftMach*`) were not changed.  Error strings and
the two error payload layers remain unchanged.  No `stateTransition*` or
`addBlockToChain*` signature changed.

## Step-3 confirmation

The prior Step-3 report accurately describes the current checkout:

- Blanc is clean at pushed `39ed4a3`; all three ELeVM pin locations resolve to
  `1d67748`; ELeVM is clean at pushed `fed6c71`.
- Lean LSP diagnostics are empty for `Blanc/Semantics.lean`, `Common.lean`,
  `Solvent.lean`, `Weth.lean`, `Basic.lean`, and `Elevm/Execution.lean`.
- `lake build` succeeds for Blanc (907 jobs), and its audit reports all four
  protected theorems with exactly `[propext, Classical.choice, Quot.sound]`.
- The Step-3 metric delta remains: Semantics −613 lines, Common −1,108,
  Solvent −690, for −2,411 lines across the affected surface; 24 bind-walking
  macros and the old `Saturation` record are gone.

## Candidate verification (this closure)

All commands below were run against the stated candidate tips.  Script times
are their reported elapsed times where available; other times are observed
wall times or intentionally omitted when the script has no aggregate timer.

| Gate | Verdict |
|---|---|
| ELeVM `lake build` | PASS, 1,760 jobs (about 8 s wall) |
| U256 | PASS, 21,593/21,593 (about 0.3 s) |
| vectors | PASS, 44/44 files; controls 5/5; inner vectors 782/782 |
| PATCH | PASS, 10/10 (0.45 s) |
| RLP4 | PASS, 4/4 (0.02 s) |
| DEPTH | PASS, 67/67 classifications (13.08 s) |
| legacy smoke | PASS, baseline 173 PASS / 1 expected FAIL (about 114 s) |
| BLS | PASS, 29/29 (about 106 s) |
| current smoke | PASS, 16/16 (0.53 s) |
| current Prague | PASS, 2,573/2,573 (714.88 s) |
| current Osaka | PASS, 2,514/2,514 (493.47 s) |
| current transitions | PASS, 13/13 files, 109 cases (15.16 s) |
| Blanc `lake build` | PASS, 907 jobs (about 7 s wall) |
| Blanc exact axiom audit | PASS, 4/4 protected theorems |
| legacy FULL (user-run) | PASS, baseline 2,978 PASS / 5 expected FAIL (2,983 files; 1,807.12 s summed per-file) |
| current mainnet FULL (user-run) | PASS, 5,100/5,100 manifest files; terminal timing not retained |

The four-family evidence sweep was repeated three times on the final binary;
all selected fixtures passed.  Best summed per-file seconds were
`vmArithmeticTest` 1.54, `stMemoryTest` 4.60, `stSStoreTest` 2.85, and
`stCallCodes` 2.41 (aggregate **11.40 s**).  This is evidence only, not a
performance target or a correctness gate.

## Protected results

The statements of `weth_inv_solvent`, `stateTransition_inv_solvent`,
`chain_inv_solvent`, and `addBlockToChain_inv_solvent` are unchanged.  The
closure audit confirms each uses exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`, `ofReduce*`, or
new axiom.

## Commit ledger

| Repository | Commit | Purpose | Status |
|---|---|---|---|
| ELeVM | `3d5c626` | Step-1 design and term-surface pilot | pushed history |
| ELeVM | `f2d2cdd` | flattened core alongside old authority | pushed history |
| ELeVM | `1d67748` | Step-2 swap: one driver, old mutual block deleted | pushed semantic pin |
| Blanc | `7e2eab3` | pin bump (diagnostic) | pushed |
| Blanc | `0086a49`, `614ef3c`, `70d4595`, `30fce1c` | Step-3 diagnostic/recovery checkpoints | pushed, explicitly diagnostic |
| Blanc | `39ed4a3` | thin wrappers; Common/Solvent green | pushed green tip |
| ELeVM | `fed6c71` | records final Step-3 report | pushed documentation tip |
| ELeVM | `78a83dc` | Step-4 short-gate closure evidence | pushed |
| ELeVM | this update's commit | records user-run FULL verdicts | pending commit/push |

## Deliberate deviations and deferred work

No scope or semantic deviation occurred.  Blanc has the two documented,
driver-forced statement-shape changes: `Xlot` now stores `Option (Evm ×
Execution)`, and child derivations are indexed by `evm'.pc` rather than
literal zero; `Frame.enter_run_pc` bridges the latter.

The enabled follow-up is the termination/fuel-sufficiency theorem: prove
`gas + 50` cannot exhaust by one induction over `exec`, with per-step gas and
frame-entry side conditions.  It remains out of scope here.

## User-owned closure gates and merge handoff

The two required final gates were run sequentially by the user on the exact candidate with Lean LSP workers stopped:

```sh
cd ~/elevm
scripts/check.sh --full --no-build
scripts/check-mainnet.sh --suite full --no-build
```

Both passed: the legacy run matched its baseline (2,978 PASS / 5 expected FAIL across 2,983 files), and current mainnet FULL passed all 5,100 manifest files.  The technical closure gates are therefore complete.  This report does not merge,
rebase, or squash either branch.  After both verdicts are recorded, the exact
proposed merge tips are ELeVM `fed6c71` plus this documentation commit and
Blanc `39ed4a3`; Blanc deliberately continues to pin the immutable semantic
commit `1d67748`, not a documentation-only ELeVM commit.
