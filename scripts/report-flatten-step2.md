# Flatten the interpreter recursion — Step 2 report

**Plan:** `~/plans/flatten.md`, Step 2 ("Flatten ELeVM behind the unchanged
boundary").
**Date:** 2026-07-28 (Asia/Seoul).
**Repository/branch:** `elevm`, `codex/flatten`.
**Starting design checkpoint:** `3d5c626fe8bfdfbbe148ade0fccc62d5270db498`.

## What changed

`Elevm/Execution.lean` now implements the Step-1 design:

- `Frame`, `FrameEntry`, `Resume`, `XStep`, and `Step` make frame entry,
  frame settlement, child suspension, and one-instruction outcomes explicit.
- `createMsg` is the CREATE-family named record barrier parallel to the
  existing `callMsg`.
- `executeCode.enter`, `Frame.enter`, `Frame.settle`,
  `processMessage.settle`, and `processCreateMessage.settle` absorb the old
  fueled wrapper tower without recursion.
- `genericCreate.step`, `genericCall.step`, `Xinst.step`, `Ninst.step`, and
  `Evm.step` are fuel-free, non-recursive transcriptions of the old semantic
  branches.
- `Resume.run` is the named, defunctionalized return path for the two actual
  post-child shapes: CREATE/CREATE2 and
  CALL/CALLCODE/DELEGATECALL/STATICCALL.
- `exec` is the **only recursive interpreter definition**. It burns one fuel
  unit per instruction and has the three planned recursive sites: same-frame
  continuation, child execution, and post-child parent continuation.
- `runFrame`, `executeCode`, `processMessage`, and
  `processCreateMessage` are non-recursive wrappers.
- The eight-way mutual block and the fueled bodies of `genericCreate`,
  `genericCall`, `Xinst.run`, and `Ninst.run` are deleted.
- Seven executable guards cover an arithmetic loop, nested CALL, CREATE
  collision, normal/bypassed precompile dispatch, depth-zero short-circuit,
  OOG, and REVERT output.

The final Step-2 diff from the design checkpoint is confined to
`Elevm/Execution.lean`: 462 insertions, 368 deletions. The pure intermediates
inside the new barriers use the pilot-selected plain-`let` convention; only
fallible operations bind.

## Refactor delta-table state

Every row of the Step-1 delta table is implemented:

| old semantic region | final home |
|---|---|
| `executeCode` initialization / precompile split | `executeCode.enter` |
| `processMessage` transfer and rollback | `Frame.enter`, `processMessage.settle` |
| create-message preprocessing / code deposit / exceptional halt | `Frame.ofCreate`, `processCreateMessage.settle` |
| CREATE/CREATE2 child construction and collision exits | `createMsg`, `genericCreate.step` |
| CALL-family depth exit and child construction | `genericCall.step`, unchanged `callMsg` |
| six `Xinst.run` cases, including static-write and balance exits | `Xinst.step` |
| PUSH/REG/X dispatch and PC advance | `Ninst.step` |
| decode/JUMP/LAST and continuation | `Evm.step`, `exec` |
| child incorporation / output copying | `Resume.run` |
| public message execution | `runFrame` plus the three public wrappers |

No semantic branch was omitted. The only deleted content beyond fueled
plumbing is the old dead debug commentary identified by the design note.

## Fuel and error accounting

Driver count is one. Within a frame, old and new execution both burn one unit
per instruction. The new code removes the old wrapper burns at child entry:
five units are saved on CALL-family entry and six on CREATE-family entry.
Thus fuel consumption can only decrease, exactly as argued in the Step-1
design note.

The two frozen error layers remain:

- `Execution = Except (String × Devm) Devm` inside a frame;
- `Except (String × State × AdrSet × Tra) Devm` between frames.

Their only named crossings are `Frame.settle` through the unchanged
`executeCode.handleError`, and `Resume.run` through the unchanged
`liftToExecution`. No error identity changed. The `Fueled` namespace remains
for Blanc's Step-3 transition, as fixed by the Step-1 design; the interpreter
has no remaining `Fueled.ok`, `Fueled.error`, or `Fueled.assert` call sites.

## Verification

All commands ran from `~/elevm`. LSP diagnostics on the touched region and
whole file were clean before checkpoint 1, after the swap, and again after the
long gates. A live `lean_goal` query after the swap confirmed the file remained
fully parsed. Long fixture tiers were run only after stopping the two active
Lean LSP workers; LSP was restarted and rechecked afterward.

### Checkpoint 1 — new core alongside the old authority

| command | verdict |
|---|---|
| `lake build` | PASS, 1760 jobs; all seven new `#guard`s elaborated |
| `scripts/check-u256.sh` | PASS, 21,593/21,593 |
| `scripts/check.sh --depth --no-build` | PASS, 67/67 classifications |
| `scripts/check.sh --smoke --no-build` | PASS, baseline 173 PASS / 1 expected FAIL |
| `scripts/check-mainnet.sh --suite smoke --no-build` | PASS, 16/16 |

### Checkpoint 2 — flattened authority, mutual block deleted

| command | verdict / script timing where reported |
|---|---|
| `lake build` | PASS, 1760 jobs (about 6 s observed wall time) |
| `scripts/check-u256.sh` | PASS, 21,593/21,593 |
| `scripts/check-vectors.sh` | PASS, 44/44 files; controls 5/5; inner vectors 782/782 |
| `scripts/check.sh --patch --no-build` | PASS, 10/10 |
| `scripts/check.sh --rlp4 --no-build` | PASS, 4/4 |
| `scripts/check.sh --depth --no-build` | PASS, 67/67 classifications unchanged |
| `scripts/check.sh --smoke --no-build` | PASS, baseline 173 PASS / 1 expected FAIL |
| `scripts/check.sh --bls --no-build` | PASS, 29/29 |
| `scripts/check-mainnet.sh --suite smoke --no-build` | PASS, 16/16 in 0.53 s |
| `scripts/check-mainnet.sh --suite prague --no-build` | PASS, 2,573/2,573 in 729.08 s |
| `scripts/check-mainnet.sh --suite osaka --no-build` | PASS, 2,514/2,514 in 498.67 s |
| `scripts/check-mainnet.sh --suite transitions --no-build` | PASS, 13/13 manifest files (109 cases) in 15.32 s |

The legacy FULL and current `--suite full` gates remain user-owned Step-4
closure gates and were not run. The optional four-family performance sweep is
also deferred to Step 4; it is evidence, not a Step-2 semantic gate.

## Scope and invariant audit

- `Rinst.runCore`/`Rinst.run`, `Jinst.runCore`/`Jinst.run`, `Linst.run`,
  precompiles, decode, gas constants, `Footprint`, and `liftMach*` are
  untouched.
- The `processMessageCall.create`/`.call` compatibility region is
  **byte-identical** to `3d5c626`: `msg.gas + 50` and
  `"RecursionLimit"` are unchanged.
- `callMsg`, `incorporateChild*`, `chargeGas`, and every named helper reused by
  the design are unchanged.
- All error strings are frozen.
- No `stateTransition*` or `addBlockToChain*` signature changed.
- No `sorry`, `admit`, `ofReduce*`, new axiom, or unrelated edit entered.
- Blanc was not modified.

## Unexpected findings

No semantic divergence occurred, so no focused-diagnosis stop condition was
triggered. In the final legacy smoke run,
`static_Call50000_sha256.json` reported 144.18 s despite LSP workers being
stopped; its classification matched the baseline. Timing is evidence only and
this isolated host variance does not affect the gate verdict.

## Commit ledger

| checkpoint | commit | purpose | pre-commit gates | pushed | diagnostic |
|---|---|---|---|---|---|
| Step 1 | `3d5c626fe8bfdfbbe148ade0fccc62d5270db498` | design note and pilot | build, U256, pilot elaboration | not by Step 1 | no |
| Step 2 core-added | `f2d2cddf3c1eb29e6e823e2c73a5d9afb2aa70d7` | new flattened core alongside legacy authority | build, guards, U256, DEPTH, legacy/current smoke | no | no |
| Step 2 swap-and-delete | this report's commit; exact hash recorded in handoff | flattened authority, old mutual block deleted | complete checkpoint-2 battery above | required after commit | no |

## Recovery state and decisions

The green recovery point for the swap is
`f2d2cddf3c1eb29e6e823e2c73a5d9afb2aa70d7`. If Step 3 needs to inspect
the old executable side by side with the flattened core, that commit contains
both and has the required smoke/depth evidence.

Autonomous decisions were limited to the fixed design: two resume shapes for
six call-type instructions, retention of the tiny `Fueled` namespace for the
Blanc transition, and retention of the two error payload layers because
unifying them would violate the frozen instruction interface.

## Human decisions pending and next handoff

No human decision is required for Step 2. The user-owned legacy FULL and
current full verdicts, and eventual merge approval, remain pending for Step 4.

Step 3 should pin Blanc to the pushed 40-character hash of the
swap-and-delete commit reported in the handoff, then perform only the Blanc
relation/proof rewrite.
