# Step 4 — repair Blanc and delete the fuel-threshold machinery

**Plan:** `~/plans/sufficient.md`, Step 4
**Repository:** `~/blanc`, branch `codex/sufficient` (new, from `main` = `39ed4a3`)
**ELeVM pin:** `0a94e419ac21ba42d04b8961107df50a0f1df2cd` (the Step-3 retype
commit), agreeing in `lakefile.lean`, `lake-manifest.json`, and the real
Lake-managed checkout — no symlink.
**Step-4 tips:** `7903b64` (pin bump, **diagnostic**) · `05eabae` (Phase A,
pushed) · `0a177f1` (Phase B, **pushed tip**)
**Date:** 2026-07-29 (Asia/Seoul)

## Result

Blanc is green over ELeVM's fuel-free API, and the fuel-threshold machinery is
gone. No Blanc statement mentions fuel any more: the adequacy bridge reads

```lean
lemma exec_iff_exec_eq (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution) :
    Nonempty (Exec pc sevm devm exn) ↔ exec ⟨pc, sevm, devm⟩ = exn
```

and the `∃ lim, ∀ lim' > lim, …` form has no remaining occurrence in the
library. The four protected solvency theorems are **byte-identical** to their
`39ed4a3` statements (verified by extraction and comparison, not by eye), with
axiom set exactly `[propext, Classical.choice, Quot.sound]`.

## What changed

### Phase A — repair to green (`05eabae`)

- **`Blanc/Semantics.lean`** imports `Elevm.Sufficiency` (the retyped wrappers
  no longer live in `Elevm.Execution`). Every reference to the fueled driver
  is `execCore`: `of_exec'`, `of_exec`, `exec_iff_exec_eq`, and (until Phase B
  removed them) `exec_saturates` and `Xlot.Good`.
- **The wrapper bridge is total.** `of_runFrame` / `of_processMessage` /
  `of_processCreateMessage` now consume `runFrame f = r` (etc.) and produce
  `xl.Filled` instead of `xl.Good lim`, via the new

  ```lean
  lemma Xlot.filled_exec (evm : Evm) : Xlot.Filled (.some ⟨evm, exec evm⟩)
  ```

  which is ELeVM's `execCore_run_sufficientLim` fed to `of_exec`. This is the
  arc's payoff in one line: the child slot of an entered frame *always*
  carries a closed derivation, because sufficiency discharged the threshold
  obligation once and for all. No consumer destructures a fuel bound any more.
- **`Blanc/Common.lean`** imports `Elevm.Transaction` (`processMessageCall`
  moved there in the Step-1 split). `processCreateMessage_eq` restated
  totally (`processCreateMessage msg = processCreateMessage.settle msg
  (processMessage (processCreateMessage.msg msg))`); the old `Fueled.mapResult`
  composition step in its proof disappears. `Xlot.balance_rel_of_good` became
  `Xlot.balance_rel_of_filled`; the `balance_noninc` family and the three
  `processMessageCall` proofs track the retyped consumers — the
  `Fueled.toExcept` layer is gone, so each site drops exactly one conversion
  call (`Fueled.eq_ok_of_toExcept_eq_ok h_pm` → `h_pm`) while the split
  skeletons survive unchanged.
- **`Blanc/Solvent.lean`**: `State.Inv.of_exec_precond` takes the `Exec`
  derivation directly and routes through `weth_inv_solvent`;
  `processMessage_inv_solvent`, `processCreateMessage_inv_solvent`,
  `processMessage_inv_noDel`, `processCreateMessage_inv_noDel`, and
  `executeCode_inv_noDel` lost their `lim` parameters; the two
  `processMessageCall` masters' create branches case-split a 2-way `Except`
  instead of the 3-way fueled option. `Exec.inv_noDel` (already Exec-level)
  now serves the slot-inversion directly — the old route converted
  `Good → fueled equation → Exec`; the new one starts at `Exec`.
- **`Blanc/Weth.lean`, `Blanc/Basic.lean`**: untouched.

### Phase B — reap the fruit (`0a177f1`)

Every deletion evidence-backed: reference counts were taken per declaration
across the whole library before deleting, and only zero-reference items were
removed.

- **Deleted (38 declarations):**
  - `Saturates` and `exec_saturates` — no references anywhere; superseded by
    ELeVM's `execCore_run_mono`, which is the same fact with a usable shape.
  - `Xlot.Good` — no references after Phase A.
  - 33 of the 36 `Fueled`-namespace lemmas in `Semantics.lean` (the
    `ok/error/exhausted` discrimination set, the `bind`/`mapResult` inversion
    set, `assert_eq`, `lift_bind_lift`, …). Survivors: `ext`,
    `exhausted_ne_ofExcept`, `ofExcept_inj` — exactly what the
    `execCore`-level induction behind the adequacy bridge needs.
  - `Fueled.mapResult_mapResult`, `Fueled.eq_ok_of_toExcept_eq_ok`
    (`Common.lean`) — both orphaned by Phase A.
- **Restated fuel-free (4 theorems):** `exec_iff_exec_eq` (above),
  `exec_inv_solvent`, `State.Inv.of_exec_transfer`, `exec_inv_noDel` — all
  now take plain equations about the total `exec`. The forward direction of
  the bridge lifts `of_exec'`'s threshold witness to
  `max (lim + 1) (gasLeft + 1)` and reads it off with ELeVM's
  `exec_eq_of_run`; the backward direction is `execCore_run_sufficientLim`
  into `of_exec`.
- `of_exec'` and `of_exec` survive **by design**: they are the induction over
  `execCore` that proves the bridge, and `execCore` reasoning is a declared
  non-goal to remove.

## Evidence

### Metrics

| | `39ed4a3` (before) | Phase A `05eabae` | Phase B `0a177f1` | Δ arc |
|---|---:|---:|---:|---:|
| `Semantics.lean` lines | 1,220 | 1,227 | 1,018 | −202 |
| `Common.lean` lines | 8,939 | 8,935 | 8,915 | −24 |
| `Solvent.lean` lines | 6,505 | 6,496 | 6,497 | −8 |
| `Fueled` mentions, Semantics | 104 | 100 | 20 | −84 |
| `Fueled` mentions, Common | 15 | 8 | 0 | −15 |
| `Fueled` mentions, Solvent | 14 | 3 | 0 | −14 |
| declarations deleted | — | 0 | 38 | 38 |

The 20 residual `Fueled` mentions in `Semantics.lean` are the `execCore`-level
adequacy induction (`of_exec'`, `of_exec`, `Xlot.filled_exec`, the bridge) and
the three surviving namespace lemmas — the residue the plan predicted, kept
because `execCore` stays public.

### Elaboration times (per-module, from the green builds)

| Module | Phase A | Phase B |
|---|---:|---:|
| `Blanc.Semantics` | 1.5 s | 1.2 s |
| `Blanc.Common` | 7.5 s | 7.5 s |
| `Blanc.Solvent` | 4.6 s | 4.6 s |

Total build: 909 jobs (baseline 907; +2 = ELeVM's new `Sufficiency` and
`Transaction` modules).

### Gate verdicts

| Gate | Phase A `05eabae` | Phase B `0a177f1` |
|---|---|---|
| `lake build` | PASS, 909 jobs | PASS, 909 jobs |
| `scripts/check.sh --no-build` | 4/4 OK, exact axiom sets | 4/4 OK, exact axiom sets |
| protected statements vs `39ed4a3` | untouched | **byte-identical** (extracted and compared) |
| `sorry`/`admit`/`ofReduce*`/`native_decide`/`maxHeartbeats`/`maxRecDepth`/new `axiom` | none | none |

The four protected theorems and the generic `…With/…Using` results
(`stateTransitionWith_inv_solvent`, `stateTransitionUsing_inv_solvent`,
`chainUsing_inv_solvent`, `addBlockToChainWith_inv_solvent`,
`addBlockToChainUsing_inv_solvent`) sit in the untouched region of
`Solvent.lean` (nothing below line ~5280 was edited in either phase).

## Unexpected findings

1. **The repair was smaller than budgeted.** The flatten arc's relational
   layer (`RunFrame`, `Exec`, the decode bridge, the effect masters) is
   fuel-free by construction, so the entire breakage surface was the fueled
   tail of `Semantics.lean` (24 errors, lines 963–1220) plus the handful of
   consumers enumerated above. Phase A reached green with a 114+/120− line
   diff and one iteration (two syntactic `rw` fixes in
   `executeCode_inv_noDel`, where an unreduced `match` blocked pattern
   matching — fixed with `show … from`-coerced equations).
2. **`State.Inv.of_exec_transfer` and `executeCode_inv_noDel` have no
   callers.** Both are API-surface counterparts kept deliberately (and now
   fuel-free); noted here so a later cleanup arc doesn't rediscover this.
3. **Lake did not move the package checkout on `lake update elevm`** — it
   fetched the new commits and rewrote the manifest but left the worktree at
   the old revision; the checkout was moved to the pinned revision explicitly
   (still Lake's own clone, never a symlink) and verified afterwards.

## Scope check

- Instruction semantics, gas charges, fork rules, decode, precompiles:
  untouched (no ELeVM source edit in this step; ELeVM is consumed at the
  pushed pin only).
- The step's whole diff touches exactly `lakefile.lean`, `lake-manifest.json`,
  `Blanc/Semantics.lean`, `Blanc/Common.lean`, `Blanc/Solvent.lean`.
- Protected statements byte-identical; axiom sets exact.
- Every deletion had zero references at deletion time (counted per
  declaration, including bare-name and dot-notation forms; no `open Fueled`
  exists anywhere).
- No baseline rebased. No fixture behavior involved — this step changes no
  executable ELeVM code.

## Commit ledger

| Repo | Branch | Hash | Purpose | Pre-commit gates | Push | Diagnostic? |
|---|---|---|---|---|---|---|
| blanc | `codex/sufficient` | `7903b64` | pin elevm `0a94e41`, breakage surveyed | pins agree; 24 errors contained in Semantics fueled tail, listed in message | yes | **yes — flagged, Semantics red** |
| blanc | `codex/sufficient` | `05eabae` | Phase A: repair to green over the retyped API | build 909 jobs; exact audit; safety greps | yes | no |
| blanc | `codex/sufficient` | `0a177f1` | Phase B: fuel-threshold machinery deleted | build 909 jobs; exact audit; safety greps; byte-compare of protected statements | **yes — tip** | no |

Recovery points: `39ed4a3` (Blanc main), `7903b64` (pin bumped), `05eabae`
(Phase A green — the fallback deliverable had Phase B stalled), `0a177f1`.
Trees clean at every commit; ELeVM untouched at `4a7648d` (tip) / `0a94e41`
(pin target).

## Autonomous decisions

1. **Phase A already moved the wrapper bridge from `Xlot.Good lim` to
   `Xlot.Filled`.** Under the total wrappers there is no non-arbitrary
   threshold left to state — any `Good`-shaped conclusion would have had to
   invent one — so the repair and the reap coincide for this predicate.
   `Xlot.Good` itself was kept through Phase A and deleted in Phase B with
   the zero-reference evidence, preserving the two-phase bookkeeping.
2. **`exec_inv_solvent`, `State.Inv.of_exec_transfer`, `exec_inv_noDel`,
   `executeCode_inv_noDel` were restated rather than deleted.** They are the
   executable-level API surface Blanc offers over the interpreter; deleting
   the uncalled ones would have shrunk the library's stated guarantees, which
   is not this step's mandate.
3. **The Step-2/Step-3 reusable devices were reused untouched** — no
   re-derivation: `Exec.inv_noDel`, the `FrameBody` route, and the effect
   masters all applied as-is; the only new derivation-level lemma in the whole
   step is `Xlot.filled_exec`.

## Human decisions pending

None from this step. No stop condition triggered: no protected statement or
axiom set changed, Phase A reached green on the first family pass, and Phase B
required no weakening of any statement.

## Next handoff — Step 5

Candidates for closure verification:

- ELeVM `codex/sufficient` tip `4a7648d` (semantic pin target `0a94e41`).
- Blanc `codex/sufficient` tip `0a177f1`, pinned to `0a94e41` in all three
  locations.

Step 5 re-runs the short-gate battery on both repositories, arranges the
user-owned legacy FULL and current `--suite full` runs, records the
four-family sweep on the final binary, and writes
`elevm/scripts/report-sufficient.md`. Nothing is merged without user
approval.
