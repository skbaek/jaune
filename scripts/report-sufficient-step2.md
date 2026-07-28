# Step 2 — the strict-decrease corpus and the sufficiency theorem

**Plan:** `~/plans/sufficient.md`, Step 2
**Repository:** `~/elevm`, branch `codex/sufficient`
**Step-1 base:** `5c5fe7a`
**Step-2 tip:** `17556bf` (not pushed; Step 3 produces the pin target)
**Date:** 2026-07-29 (Asia/Seoul)

## Result

```lean
theorem exec_run_isSome : ∀ (lim : Nat) (evm : Evm),
    evm.dyna.gasLeft < lim → ∃ raw : Execution, (exec evm lim).run = some raw

theorem exec_ne_exhausted (evm : Evm) (lim : Nat) (h : evm.dyna.gasLeft < lim) :
    exec evm lim ≠ Fueled.exhausted

theorem exec_succ_ne_exhausted (evm : Evm) :
    exec evm (evm.dyna.gasLeft + 1) ≠ Fueled.exhausted
```

**The additive constant is 1** — the tight bound the plan aimed for, with no
slack needed. Step 3 can define `sufficientLim gas := gas + 1` and discharge the
`Option` with `exec_succ_ne_exhausted`.

Axiom set of `exec_succ_ne_exhausted`, `exec_ne_exhausted`, `exec_run_isSome`
and `exec_settledGasLe`: exactly `[propext, Classical.choice, Quot.sound]`.

## What changed

Only `Elevm/Sufficiency.lean`. **No definition anywhere in ELeVM was touched:
Step 2 adds lemmas and proof-local definitions only.**

### The strict-decrease corpus (`.ok` branch)

Committed across `3ac154f` and `219ed70` (the interrupted session's work,
carried forward unchanged):

- `Rinst.runCore_gasLt` — all 69 constructors.
- `Jinst.runCore_gasLt` — all 3.
- `Xinst.step_gasDecreasing` — all 6, via `XStep.GasDecreasing`,
  `genericCall.step_gasDecreasing`, `genericCreate.step_gasDecreasing`,
  `calculateMsgCallGas_stipend_lt`, `call_charge_stipend_lt`, `except64th_le`.

### The gas non-increase corpus (`6215a8f`) — not anticipated by the plan

See *Unexpected findings*. New material:

- `resultGas` / `machResultGas` / `machMetaResultGas` and the peeling lemmas
  `gasLe_bind_snd`, `gasLe_bind_id`, `gasLe_bind_const`, `gasLe_bind`,
  `gasLe_bind_gen`.
- The `Mach` layer: `pop`, `popToNat`, `popToAdr`, `popN`, `push`, `chargeGas`,
  `pushItem`, `applyUnary`/`Binary`/`Ternary`, plus `liftMach`,
  `liftMachExecution`, `liftMachMetaExecution` transfer lemmas.
- `Rinst.runCore_gasLe` (69), `Jinst.runCore_gasLe` (3), `Linst.run_gasLe` (4),
  `Rinst.balanceCore_machMetaResultGas`.
- The tag route for `Xinst`: `NoRevertOut`, `MachNoRevert`, `noRevert_bind`,
  `XStep.NoRevert`, `xstepNoRevert`, `xstepNoRevert_bind`,
  `genericCall.step_noRevert`, `genericCreate.step_noRevert`,
  `Xinst.step_noRevert` (6).

### Settlement, the step obligation, and the driver (`17556bf`)

- `Execution.SettledGasLe` with its two discharge routes
  (`settledGasLe_of_gasLe`, `settledGasLe_of_noRevert`) and `.mono`.
- `processCreateMessage.chargeCodeGas_gasLe`, `processMessage.settle_ok_gasLe`,
  `processCreateMessage.settle_ok_gasLe`, `Frame.settleMsg_ok_gasLe`,
  `Frame.settle_gasLe`.
- `Frame.enter_run_gasLeft` (a `.run` child starts with exactly
  `frame.inner.gas`) and `Frame.enter_done_gasLe`.
- `Resume.run_gasLe` (the resume error branch; `Resume.run_ok_gasLeft` already
  covered the successful one).
- `Step.GasBound`, `Step.ofExecution_gasBound`, `Step.ofJump_gasBound`,
  `XStep.toStep_gasBound`, `Ninst.step_push_gasLt`, `Ninst.step_gasBound`,
  `Evm.step_gasBound`.
- `exec_settledGasLe` (driver monotonicity) and the three theorems above.

## Unexpected findings

### 1. The plan's monotonicity statement is too weak — the error branch is live

The plan specifies

> driver monotonicity (`execCore evm lim = some (.ok devm) → devm.gasLeft ≤
> evm.dyna.gasLeft`)

i.e. the successful branch only. That is not enough. In the driver's
`.spawn`/`.run` arm the child's **whole** result is handed to
`frame.settle`, and `executeCode.handleError` turns

```lean
.error ("Revert", d)   ↦   .ok (d.withError (some "Revert"))
```

into a *successful* frame result carrying `d.gasLeft` — live gas, which
`Resume.run` then adds back to the parent. Without a bound on that `d`, the
resumed parent's gas is unbounded and the induction does not close. The other
two error shapes are free: an exceptional halt is rewritten to zero gas, and any
remaining tag stays an `.error`, which `Resume.run` cannot turn into a resumed
parent. So the obligation is exactly

```lean
def Execution.SettledGasLe (n : Nat) (ex : Execution) : Prop :=
  ∀ d : Devm, executeCode.handleError ex = .ok d → d.gasLeft ≤ n
```

and monotonicity is stated over it. This is a gap in the plan, not in the
interpreter: no semantics are involved, only the shape of the theorem. It is the
single largest cost in Step 2 — roughly 900 of the 2,105 added lines.

### 2. Two routes to the same obligation, because `Xinst` resists the first

`SettledGasLe` is discharged two ways:

- **By gas bound** (`Rinst`, `Jinst`, `Linst`): prove `ex.gasLeft ≤ n` outright.
  A compositional `resultGas` device makes this cheap — its bind lemmas leave
  the tail as an *unconditional* obligation measured against the intermediate
  `Devm`, so a walk chains without threading equations through hypotheses.
  `Linst` genuinely needs this route: `Linst.run .rev` is the sole producer of
  `"Revert"` in the entire interpreter.
- **By tag** (`Xinst`): the compositional bound is *false locally* for the call
  family. A call that short-circuits at depth 0 evaluates
  `(evm1.withGasLeft (evm1.gasLeft + gas)).push 0`, so if that push overflows,
  the error carries **more** gas than the intermediate `Devm` it came from; the
  bound is recoverable only from the charge equation the device deliberately
  discards. Since every error an `Xinst` can raise is a stack or gas fault,
  `Xinst.step_noRevert` plus the existing `XStep.GasDecreasing` discharges
  `SettledGasLe` without any arithmetic. This is a real property of the code,
  and it fails loudly (rather than silently) if a new tag is ever introduced.

### 3. Confirmations

- No continuing step was found that fails to strictly decrease gas.
- No gas charge needed to move. Charge timing is byte-identical to `5c5fe7a`.
- The `except64th n = n` trap for `n < 64` is carried by the upfront
  `gasCreate`, exactly as the readiness audit predicted (`except64th_le`).

## Evidence

### Corpus census

| Family | Obligation | Constructors | Bespoke | Combinator-derived |
|---|---|---:|---:|---:|
| `Rinst` | strict `<` on `.ok` | 69 | 26 | 43 |
| `Rinst` | non-increase `≤` | 69 | 26 | 43 |
| `Jinst` | both | 3 | 3 | 0 |
| `Linst` | non-increase `≤` | 4 | 4 | 0 |
| `Xinst` | `GasDecreasing` | 6 | 6 | 0 |
| `Xinst` | `NoRevert` | 6 | 6 | 0 |

The plan asked this to be checked against Blanc's analogue: **48** bespoke
`_runCore_instructionFrame` lemmas against the same 69 constructors. Both
`Rinst` corpora here needed **26**, because the four `apply*`/`pushItem`
combinator lemmas close 43 constructors in a single `all_goals first` dispatch.

### Size and elaboration cost

| | Step-1 base `5c5fe7a` | Step-2 tip `17556bf` | Δ |
|---|---:|---:|---:|
| `Elevm/Sufficiency.lean` lines | 686 | 2,791 | +2,105 |
| top-level declarations in it | 65 | 188 | +123 |
| `lake build` jobs | 1,760 (arc start) | 1,764 | +4 |
| `lake build` wall | ~8 s (arc start) | 11.35 s | +3.4 s |
| `Elevm.Sufficiency` elaboration | — | 4.7 s | — |
| `Elevm.Sufficiency:c.o` | — | 3.9 s | — |

Per-slice line growth: Rinst `<` corpus +461, Jinst/Xinst/frame support +328,
non-increase corpus +882, settlement and driver +434.

### Gate verdicts on `17556bf`

| Gate | Result | Baseline |
|---|---|---|
| LSP diagnostics, whole file | clean | — |
| `lake build` | PASS, 1,764 jobs, 11.35 s | — |
| `scripts/check-u256.sh` | 21,593 / 21,593 PASS | matches |
| `scripts/check.sh --depth --no-build` | 67 / 67, 67 PASS 0 FAIL | matches |
| `scripts/check.sh --smoke --no-build` | 174 files, 173 PASS / 1 FAIL | matches |
| `scripts/check-mainnet.sh --suite smoke --no-build` | 16 / 16 | matches |

No fixture result changed, as expected: this step adds no executable code.

Source scan: no `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`,
`ofReduceNat`, `maxHeartbeats`, or `maxRecDepth` anywhere in the file.

## Scope check

- Instruction semantics untouched — `git diff 5c5fe7a..17556bf` touches
  `Elevm/Sufficiency.lean` and `scripts/handoff-sufficient-step2.md` only.
- Gas charge timing unchanged; no charge was moved or renamed.
- Gas constants, fork rules, decode, precompiles, `Footprint`/`liftMach*`
  untouched.
- No baseline rebased.
- `"RecursionLimit"` still occurs exactly twice, both in `Elevm/Transaction.lean`
  (Step 3 deletes them).
- `Fueled` still has 30 mentions in `Elevm/Execution.lean`; the driver keeps its
  name `exec` (Step 3 renames it to `execCore`).
- No Blanc file touched; `Devm.Burn` was neither imported nor imitated.

## Commit ledger

| Repo | Branch | Hash | Purpose | Pre-commit gates | Push | Diagnostic? |
|---|---|---|---|---|---|---|
| elevm | `codex/sufficient` | `3ac154f` | Rinst strict-decrease corpus | LSP, build, DEPTH | no | no |
| elevm | `codex/sufficient` | `219ed70` | Jinst/Xinst/frame support (interrupted session's checkpoint) | LSP only | no | no — green, but its build/U256/DEPTH were deferred and are confirmed green here |
| elevm | `codex/sufficient` | `6215a8f` | gas non-increase for the halting branch | LSP, build, U256, DEPTH | no | no |
| elevm | `codex/sufficient` | `17556bf` | settlement, monotonicity, sufficiency | LSP, build, U256, DEPTH, SMOKE, current smoke | no | no |

Nothing was pushed: per the plan, Step 3 produces Blanc's pin target. Recovery
points are each commit above; the pre-Step-2 recovery point is `5c5fe7a`.

## Autonomous decisions

1. **Added the non-increase corpus** rather than stopping at the plan's
   monotonicity statement. Reported above as a plan gap; proceeding was the only
   way to close the induction, and it changes no definition.
2. **Split the settlement obligation into two discharge routes.** Chosen over
   re-deriving the call family's stipend arithmetic a second time (~250 lines of
   duplicated `hstip` derivations) for the `Xinst` error branch.
3. **Stated monotonicity over `SettledGasLe`** rather than over raw gas, so the
   driver induction is indifferent to which route a family took.
4. **Left the driver named `exec`.** The rename to `execCore` is Step 3's.
5. **Marked `scripts/handoff-sufficient-step2.md` superseded** rather than
   deleting it, so the session boundary stays legible without misleading a
   future reader into redoing finished work.

## Human decisions pending

None for Step 2. The predeclared stop conditions did not trigger: no
non-decreasing continuing step, no charge needed moving, no instruction family
required more than two focused attempts, and the constant is ≥ 1 uniformly.

## Next handoff — Step 3

Step 3 consumes, from `Elevm/Sufficiency.lean`:

- `exec_succ_ne_exhausted : exec evm (evm.dyna.gasLeft + 1) ≠ Fueled.exhausted`
  — define `sufficientLim (gas : Nat) : Nat := gas + 1` and use this to
  discharge the `Option` in the total `exec`;
- `exec_ne_exhausted` for any other seeding a bridge lemma may want;
- `exec_settledGasLe` if a downstream proof needs the parent-facing gas bound.

Note for Step 3: renaming `exec` to `execCore` renames it in every statement in
`Elevm/Sufficiency.lean` too (`exec_run_isSome`, `exec_settledGasLe`,
`exec_ne_exhausted`, `exec_succ_ne_exhausted` and their proof bodies, which
`rw [exec]` the equation lemma).
