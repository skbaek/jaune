# Step 3 — retype the interpreter and delete the RecursionLimit observable

**Plan:** `~/plans/sufficient.md`, Step 3
**Repository:** `~/elevm`, branch `codex/sufficient`
**Step-2 tip:** `911a114`
**Step-3 tips:** `25a0521` (rename) · `0a94e41` (retype, **pushed — Blanc's pin
target**)
**Date:** 2026-07-29 (Asia/Seoul)

## Result

The public API is total. Fuel is an implementation detail of `execCore`.

```lean
def execCore : Evm → Nat → Fueled (String × Devm) Devm   -- the old `exec`
def sufficientLim (gas : Nat) : Nat := gas + 1
def exec (evm : Evm) : Except (String × Devm) Devm

def runFrame            (frame : Frame) : Except (String × State × AdrSet × Tra) Devm
def executeCode         (msg : Msg)     : Except (String × State × AdrSet × Tra) Devm
def processMessage      (msg : Msg)     : Except (String × State × AdrSet × Tra) Devm
def processCreateMessage (msg : Msg)    : Except (String × State × AdrSet × Tra) Devm
```

`exec` runs `execCore` at `sufficientLim evm.dyna.gasLeft` and discharges the
`Option` with Step 2's witness. **The additive constant is 1**, the proved one,
with no slack.

Axiom set of every declaration added or retyped here — the *definitions*
included, since `exec` carries a proof — is exactly
`[propext, Classical.choice, Quot.sound]`. That is already the protected set in
Blanc, so Step 4 inherits no new axiom.

## What changed

### `Elevm/Execution.lean` (4,948 → 4,889 lines)

- `exec` renamed to `execCore`; its `.spawn` self-recursion, the two `#guard`s
  that call it, and one prose comment renamed with it. Definition otherwise
  byte-identical.
- The four frame wrappers **removed** (they moved, retyped, to
  `Elevm/Sufficiency.lean`), together with `flattenGuardSummary` and the three
  `#guard`s that exercised them.
- Retained here: the guards that pin `execCore` and the frame-local functions —
  `flattenGuardArithmeticLoop` (the check that fuel really can run out when it
  is *not* seeded from the frame's gas), `flattenGuardCreateCollision`,
  `flattenGuardPrecompileDispatch`, `flattenGuardDepthZero`,
  `flattenGuardOog`.

### `Elevm/Sufficiency.lean` (2,791 → 3,055 lines)

Renames of the Step-2 statements, which all mention the driver:

| Step 2 | Step 3 |
|---|---|
| `exec_settledGasLe` | `execCore_settledGasLe` |
| `exec_run_isSome` | `execCore_run_isSome` |
| `exec_ne_exhausted` | `execCore_ne_exhausted` |
| `exec_succ_ne_exhausted` | `execCore_succ_ne_exhausted` |

New material:

- `sufficientLim`, `execCore_run_sufficientLim_isSome`, `exec`.
- Bridge equations, so no downstream proof manipulates `Option.get`:
  - `execCore_run_sufficientLim : (execCore evm (sufficientLim evm.dyna.gasLeft)).run = some (exec evm)`
  - `execCore_run_mono : lim ≤ lim' → (execCore evm lim).run = some raw → (execCore evm lim').run = some raw`
  - `execCore_run_of_lt : evm.dyna.gasLeft < lim → (execCore evm lim).run = some (exec evm)`
  - `exec_eq_of_run : evm.dyna.gasLeft < lim → (execCore evm lim).run = some raw → exec evm = raw`
- The four total wrappers, plus `runFrame_of_done` and `runFrame_of_run`.
- Nine `#guard`s over the total entry points (below).

### `Elevm/Transaction.lean` (1,969 → 1,959 lines)

`processMessageCall.create` and `.call` now read

```lean
let evm ← Except.bimap Prod.fst id (processCreateMessage msg)
let evm ← Except.bimap Prod.fst id (processMessage msgPc)
```

Both `"RecursionLimit"` sites are gone, along with the `Fueled.toExcept` calls
and the `msg.gas + 50` seeding that carried them.

## Why the change of seeding is neutral *by proof*

The consumers used to seed `gas + 50`; the total `exec` seeds `gas + 1`. That is
a change of argument to `execCore`, so "it is obviously the same" is not good
enough. `execCore_run_mono` closes it: more fuel never changes a result the
driver already reached. Since the frame's gas bounds both budgets from below
(`Frame.enter_run_gasLeft` gives the child exactly `frame.inner.gas`), both
seedings land on the same `some raw`, hence the same result.

This was not required by the plan. It is ~45 lines and it converts the step's
central claim from *empirically confirmed by 5,087 mainnet fixtures* to
*proved*, so it was worth taking.

## The `#guard`s over the total entry points

Mirroring the flatten arc's seven representative states through the fuel-free
API. Pinned gas figures are canaries: this arc must not move a gas charge, so a
change in any of them is a failure signal, not a number to rebase.

| State | Route | Assertion |
|---|---|---|
| arithmetic loop | `exec (initEvm msg)` and `processMessage msg` | `OutOfGasError`; settled frame carries `error = some "OutOfGasError"`, `gasLeft = 0` |
| nested CALL | `runFrame (Frame.ofCall …)` = `processMessage …` | stack head 1, `gasLeft = 97379` |
| CREATE collision | `processMessage …` executing `CREATE` at an address that already carries code | no error, stack head 0, `gasLeft = 1062` |
| precompile, both paths | `processMessage …` with `disablePrecompiles` false / true | `gasLeft = 7000` (ecrecover charged 3,000) / `10000` |
| depth-zero short-circuit | `processMessage {… with depth := 0}` | stack head 0 (the same parent gets 1 at depth 8) |
| OOG halt | `exec (initEvm msg)` | `OutOfGasError` |
| REVERT with output | `runFrame (Frame.ofCall …)` | `error = some "Revert"`, 32 bytes out, last byte `0x2A`, `gasLeft = 982` |

The headline is the first: the state that *exhausted* `execCore` at fuel 20 now
runs to a definite result through `exec`. Both forms are kept — the exhausting
one in `Elevm/Execution.lean`, the terminating one here — so the guard set
records both sides of what the arc changed.

The CREATE-collision guard is now routed through a real frame rather than a
direct `genericCreate.step` call, and it incidentally documents that the
collision exit does **not** restore `createGas`: `100000 - 9 - 32000 = 67991`
in, `except64th 67991 = 66929` reserved and consumed, `1062` left. The
readiness audit's list of "exits that restore `createGas` exactly" includes
collision; that is inaccurate against `Elevm/Execution.lean:3967-3973`, where
only the depth-0 / insufficient-balance / max-nonce exit at `:3962` refunds.
Nothing in Step 2's proof depended on the distinction, and no code changed.

## Evidence

### Gate verdicts on `0a94e41`

| Gate | Result | Baseline |
|---|---|---|
| LSP diagnostics, 3 touched files | clean | — |
| `lake build` | PASS, 1,764 jobs, 13.6 s | 1,764 / 11.35 s at Step-2 tip |
| `#guard`s | all pass (build-time) | — |
| `scripts/check-u256.sh` | 21,593 / 21,593 PASS | matches |
| `scripts/check.sh --patch` | 10 / 10 | matches |
| `scripts/check.sh --rlp4` | 4 / 4 | matches |
| `scripts/check.sh --depth` | 67 / 67 (67 PASS, 0 FAIL) | matches |
| `scripts/check.sh --smoke` | 174 files, 173 PASS / 1 expected FAIL | matches |
| `scripts/check.sh --bls` | 29 / 29 | matches |
| `scripts/check-vectors.sh` | 44 / 44 files, controls 5 / 5, 782 / 782 | matches |
| `scripts/check-mainnet.sh --suite smoke` | 16 / 16 | matches |
| `scripts/check-mainnet.sh --suite transitions` | 13 / 13 files, 15.12 s | matches |
| `scripts/check-mainnet.sh --suite prague` | 2,573 / 2,573 in 727.29 s | 2,573; 714.88 s |
| `scripts/check-mainnet.sh --suite osaka` | 2,514 / 2,514 in 489.57 s | 2,514; 493.47 s |

No classification changed anywhere. Prague and Osaka were the once-per-
checkpoint authorized runs.

### Size and elaboration cost

| | Step-2 tip `911a114` | Step-3 tip `0a94e41` | Δ |
|---|---:|---:|---:|
| `Elevm/Execution.lean` | 4,948 | 4,889 | −59 |
| `Elevm/Sufficiency.lean` | 2,791 | 3,055 | +264 |
| `Elevm/Transaction.lean` | 1,969 | 1,959 | −10 |
| `lake build` jobs | 1,764 | 1,764 | 0 |
| `Elevm.Sufficiency` elaboration | 4.7 s | 7.9 s | +3.2 s |
| `Fueled` mentions, Execution | 30 | 21 | −9 |
| `Fueled` mentions, Transaction | 2 | 0 | −2 |

### Four-family sweep

Three runs on the final binary; all selected fixtures passed.

| Family | Best (s) | Flatten baseline (s) |
|---|---:|---:|
| `vmArithmeticTest` | 1.54 | 1.54 |
| `stMemoryTest` | 4.60 | 4.60 |
| `stSStoreTest` | 2.89 | 2.85 |
| `stCallCodes` | 2.40 | 2.41 |
| **aggregate** | **11.45** | **11.40** |

+0.4 %, inside run-to-run spread (11.45 / 11.46 / 11.49). Evidence only.

## Unexpected findings

1. **Host swap exhaustion mid-Prague.** Swap reached 11.8 GB of 12.3 GB with
   ~75 MB of free pages, from fifteen idle Lean LSP workers accumulated across
   sessions. Killing the workers freed ~2.9 GB and throughput recovered to
   ~7 files/s. The final Prague wall time (727.29 s against a 714.88 s
   baseline) is unaffected. This is the hazard `~/plans/sufficient.md` warns
   about under *Execution environment assumption*; the mitigation is to reap
   LSP workers before, not during, a long tier.
2. **The readiness audit's `createGas` refund list is inaccurate** for the
   collision exit. Documented above; no impact on the proof or on the code.

## Scope check

- Instruction semantics untouched. `git diff 911a114..0a94e41` touches exactly
  `Elevm/Execution.lean`, `Elevm/Sufficiency.lean`, `Elevm/Transaction.lean`.
- Gas charge timing unchanged; no charge moved, renamed, or reordered.
- Gas constants, fork rules, decode, precompiles, `Footprint`/`liftMach*`
  untouched.
- No baseline rebased.
- `"RecursionLimit"` occurs zero times in ELeVM source. It never appeared in an
  error-tag list, in `isExceptionalHalt`, or in a fixture-exception mapping —
  `Elevm/FixtureException.lean` has no reference — so the deletion cannot move
  a classification, and none moved.
- `Fueled` survives, unchanged, with its full namespace. `execCore` survives,
  public, behaviorally identical.
- No `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `ofReduceNat`,
  `maxHeartbeats`, or `maxRecDepth` anywhere in `Elevm/`.
- No Blanc file touched.

## Commit ledger

| Repo | Branch | Hash | Purpose | Pre-commit gates | Push | Diagnostic? |
|---|---|---|---|---|---|---|
| elevm | `codex/sufficient` | `25a0521` | rename `exec` → `execCore` | build, U256, DEPTH | yes (with next) | no |
| elevm | `codex/sufficient` | `0a94e41` | `sufficientLim`, total `exec`, retyped wrappers, rewired consumers, `"RecursionLimit"` deleted, bridge lemmas, `#guard`s | full battery incl. Prague + Osaka | **yes** | no |

Recovery points: `911a114` (Step-2 tip), then `25a0521`.

## Autonomous decisions

1. **Proved `execCore_run_mono`.** Not requested. It makes the seeding change
   neutral by proof rather than by fixture, and it hands Step 4 the
   fuel-irrelevance lemma its `∃ lim, ∀ lim' > lim, …` statements are really
   about.
2. **Moved the wrappers into `Elevm/Sufficiency.lean`** rather than keeping
   them in `Elevm/Execution.lean` and forward-declaring. They consume the total
   `exec`, so this is forced by the module order the Step-1 split established.
3. **Moved rather than restated the three wrapper `#guard`s**, and added a
   fresh mirrored set over the total API, so both the fueled and the total
   behavior stay pinned.
4. **Pinned exact gas figures in the new guards.** They are canaries for the
   frozen charge timing; a change should fail loudly.
5. **Reaped idle Lean LSP workers** mid-run to relieve swap. Non-destructive —
   the MCP respawns them on demand.

## Human decisions pending

None for Step 3. No stop condition triggered: no classification changed, the
retype needed no charge moved, and the constant stayed 1.

## Next handoff — Step 4

Pin Blanc's `codex/sufficient` to

```
0a94e419ac21ba42d04b8961107df50a0f1df2cd
```

all three locations agreeing, never a symlink. From `Elevm.Sufficiency`, Step 4
consumes:

- `exec`, `runFrame`, `executeCode`, `processMessage`, `processCreateMessage` —
  the retyped API Blanc's `Exec` relation, `Xlot`, `Xlot.Good`,
  `Saturates`/`exec_saturates`, adequacy bridge, and thin wrappers must be
  retargeted at;
- `execCore` plus the renamed Step-2 theorems, for proofs that still want to
  reason over the fueled definition;
- `execCore_run_of_lt` and `exec_eq_of_run` for Phase B: these are the levers
  that retire a `∃ lim, ∀ lim' > lim, …` statement, since any budget past the
  frame's gas already gives `exec`;
- `runFrame_of_done` / `runFrame_of_run` for frame-level case splits.

Blanc must import `Elevm.Sufficiency` (or `Elevm`) — `Elevm.Execution` alone no
longer provides the wrappers.
