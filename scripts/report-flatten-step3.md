# Flatten the interpreter recursion — Step 3 report

**Plan:** `~/plans/flatten.md`, Step 3 ("Rebuild Blanc's shadow layer as thin
wrappers").
**Dates:** started 2026-07-28, completed 2026-07-28 (Asia/Seoul).
**Repository/branch:** `blanc`, `codex/flatten`.
**Status:** **complete and green.** `lake build` succeeds on the whole library
and `scripts/check.sh --no-build` reports 4/4 protected theorems clean with the
exact axiom set. The step's exit criterion is met.

---

## 1. What changed

### 1.1 Pin

`Blanc` pins ELeVM at the Step-2 flattened-core commit
`1d67748023623ffef3d24ba9cdbc2095586da30b`. All three locations agree
(`lakefile.lean`, `lake-manifest.json`, and the managed checkout
`.lake/packages/elevm` HEAD); the checkout is a real directory, not a symlink.
The pin was set in the first Step-3 session and was not touched since.

### 1.2 `Blanc/Semantics.lean` — one relation plus thin wrappers

The hand-maintained relational shadow layer is one generic derivation relation
plus thin non-recursive wrappers, exactly as fixed by the Step-1 design note.

**The relation.** `Exec` keeps its name and index shape
`Nat → Sevm → Devm → Execution → Type`, as `weth_inv_solvent`'s statement
requires. Its eight constructors became six — `halt`, `cont`, `doneErr`,
`doneOk`, `runErr`, `runOk` — and every premise other than a sub-derivation is
an *equation about a non-recursive function* (`Evm.step`, `Frame.enter`,
`Resume.run`, `Frame.settle`).

**`Xlot`** is retyped from `Option (Sevm × Devm × Execution)` to
`Option (Evm × Execution)`, matching what the single driver suspends on. All
statements mentioning `Xlot` survive textually; proofs that destructured the old
triple take the pair instead. This is the statement change the design note
predicted, and it is the source of most of the downstream churn.

**The mirrors, as thin wrappers.** `RunFrame` is the generic frame relation;
`XStep.Run` and `Step.Run` are the generic step relations. On top of them:

| former mirror | new definition | statement preserved? |
|---|---|---|
| `ProcessMessage msg xl ex` | `RunFrame (Frame.ofCall msg) xl ex` | yes |
| `ProcessCreateMessage msg xl ex` | `RunFrame (Frame.ofCreate msg) xl ex` | yes |
| `ExecuteCode msg xl ex` | match on `executeCode.enter msg` | yes |
| `Xinst.Run sevm devm x xl ex` | `XStep.Run (Xinst.step sevm devm x) xl ex` | yes |
| `GenericCall …` (15 args) | `XStep.Run (genericCall.step …) xl ex` | yes |
| `GenericCreate …` | `XStep.Run (genericCreate.step …) xl ex` | yes |
| `Ninst.Run' pc sevm devm n xl ex` | `Step.Run (Ninst.step ⟨pc,sevm,devm⟩ n) xl ex` | yes |
| `Ninst.Run`, `Func.Run`, `Prog.Run`, `Jinst.Run`, `Linst.Run`, the `*.At` predicates, `Devm.Rel(s)`, `Devm.Burn`, `Devm.PopBurn`, `Except.Split`, `Except.SplitXl`, `ExistsEq` | unchanged | yes |

**Adequacy and monotonicity, once each.**

- `exec_saturates (lim) : ∀ evm, Saturates lim (exec evm)` — one induction on
  `lim`, quantified over `Evm`. This replaces the eight-field `Saturation`
  record and its 90-line `saturation` proof, both deleted.
- `of_exec`, `of_exec'`, `exec_iff_exec_eq` — **statements textually
  unchanged**; the proofs shrank to a six-way case analysis with no
  bind-walking.
- `of_processMessage` and `of_processCreateMessage` are retained as derived
  corollaries of a new `of_runFrame`, with **unchanged statements**.

**Deleted outright** (grep-confirmed absent): the `Saturation` record,
`saturation`, all 24 `macro_rules`/`syntax` declarations of the bind-walking
family (`eee_bind`, `efg_step_*`, `eq_split`, `eq_ite`, `bind_step_good`,
`okStep1`, `bind_step'`, …), and the collapsed adequacy chain
(`of_execute_code'`, `of_process_message'`, `of_process_create_message'`,
`of_generic_create'`, `of_generic_call'`, `Xinst.run_eq_of_run`,
`Ninst.run_of_run'`, `of_executeCode`, `of_genericCreate`, `of_genericCall`,
`Xinst.run_of_run_eq`, `Ninst.run_of_run_eq`).

**New bridging API** — this is what makes the downstream repair mechanical, and
it is the part of the step with the most leverage:

- *Decode bridge:* `Evm.step_invOp`, `Evm.step_next`, `Evm.step_jump`,
  `Evm.step_last`, `Evm.step_spawn_inv`.
- *Step-outcome inversion:* `Step.run_ofExecution`, `Step.ofExecution_cont`,
  `Step.ofExecution_ne_spawn`, `Step.ofExecution_ne_halt_ok`, `Step.ofJump_cont`,
  `Step.run_ofJump`, `XStep.toStep_spawn`, `XStep.run_toStep`,
  `Ninst.step_reg/_push/_exec`, `Ninst.step_cont_pc`, `Ninst.step_spawn_pc`,
  `Ninst.step_ne_halt_ok`, `Ninst.step_spawn_inv`, `Ninst.step_spawn_depth`.
- *Frame relations:* `RunFrame.of_done`, `RunFrame.of_run`, `RunFrame.some_inv`,
  `RunFrame.depth_eq`, `RunFrame.decompose`, `FrameBody`,
  `RunFrame.iff_settleMsg`, `ProcessMessage.iff_body`,
  `ProcessCreateMessage.iff_processMessage`, `Frame.enter_run_inv`,
  `executeCode.enter_inl`, `executeCode.enter_inr`, `ExecuteCode.some_inv`,
  `XStep.Run.some_inv`, `Step.Run.some_inv`.
- *Derivation inversion:* `Exec.halt_inv`, `Exec.last_inv`, `Exec.invOp_inv`.
- *Depth side conditions:* `genericCall.step_spawn_depth`,
  `genericCreate.step_spawn_depth`, `Xinst.step_spawn_depth`,
  `Step.spawn_depth_lt`, `Frame.enter_run_depth`.

**Depth induction is recovered.** `Common.lean`'s `Exec.strong_rec` needs a
strict decrease at every child derivation; `Step.spawn_depth_lt` (every spawn is
depth-guarded, and `callMsg`/`createMsg` set `depth := sevm.depth - 1`) plus
`Frame.enter_run_depth` (entering a frame preserves its depth) discharge it once.
This was the design note's main risk item and it is **resolved**.

### 1.3 `Blanc/Common.lean` — green

Three structural devices carry the whole file.

**(a) `Xinst.Shape` — the dispatch shape of a call-type instruction.** Everything
`Xinst.step` does before dispatching (popping operands, charging gas, extending
memory, recording accesses, resolving delegations) stays inside
`Devm.InstructionFrame`. `Xinst.Shape sevm devm s` records that once, as a
three-way disjunction: a childless outcome inside the instruction frame, or a
dispatch to `genericCreate.step`/`genericCall.step` at an instruction-frame-equal
machine, carrying additionally the child's caller/target relation and the
provenance of the child's code. `Xinst.step_shape` proves it compositionally with
seven small combinators (`shape_bind`, `shape_bindE`, `shape_assert`,
`shape_create`, `shape_call`, `shape_shortfall(')`, `Shape.trans_left`).

This replaces the six per-constructor bind walks that the old mirrors forced.
`Xinst.codePreserve_effectGen` (330 lines → 27) and `Xinst.balance_effectGen`
(330 lines → 18) are now three-case arguments over it, and it is reused three
more times in `Solvent.lean`.

**(b) `Evm.step_effect` + `Exec.effect`.** The four decode branches are
enumerated once, in `Evm.step_effect`; `Exec.effect` then only has to compose
steps, one case per driver outcome instead of one per mutual-block constructor.
`Xlot.Rel`, `Ninst.effectGen_reg/_exec`, `Xlot.rel_of_filled`,
`Xlot.invGetCode_of_rel`, `Xlot.rel_of_invGetCode` and the `Ninst.push_*` family
follow directly.

**(c) `Evm.step_spawn_child`.** The whole former six-lemma `prep_*` family
(≈ 850 lines) becomes `Frame.enter_run_{pc,code,currentTarget,getCode}` plus
`Xinst.step_spawn_getCode` / `Xinst.step_spawn_source`, packaged as one lemma:
a spawned child starts at `pc = 0`, on a machine with the parent's code map,
and — under the `Prog.At` side conditions — with the contract's code loaded.

`lift_core` is re-derived over the six constructors. Its predicate argument is
now derivation-free (`Nat → Sevm → Devm → Execution → Prop`; the only consumer
already ignored the derivation), and it performs the decode dispatch itself, so
`lift` and `lift_inv` keep their per-instruction-kind handler shapes and
`Solvent.lean`'s use site is unaffected apart from the `Xlot` retyping.

The balance masters (`ExecuteCode/ProcessMessage/ProcessCreateMessage.balance_effect`,
`GenericCall/GenericCreate.balanceEffect`) go through `ProcessMessage.iff_body` /
`ProcessCreateMessage.iff_processMessage` and new `Resume.*_balance` helpers.

`Common.lean`'s instruction frame-lemma corpus needed **no semantic rework**:
every change is a case-name/arity adaptation, an `Xlot` pair-vs-triple
adaptation, or a proof that got shorter.

### 1.4 `Blanc/Solvent.lean` — green

- The ten `Ninst.Hinv` instances go through the new `Ninst.run_push_eq` and
  `of_run_reg` step-outcome equations instead of unfolding `Ninst.Run'`.
- `of_executeCode_someCode` / `_cases` / `_noneCode` are rephrased against
  `executeCode.enter`; their `Xlot` payload becomes `⟨initEvm msg, ex'⟩`.
- `of_send_to_caller'` (the WETH `sendToCaller` line) walks `Xinst.step .call`
  directly: seven sequential pops with `rcases … : …` + `simp only`, then
  `split` through the delegation resolution, gas charge, static assertion and the
  two early exits; the frame settlement is inverted by `RunFrame.some_inv` +
  `Frame.enter_run_inv`, and the child message is re-abstracted so the 200-line
  tail is untouched.
- `Xinst.none_inv_precond` (110 → 12 lines), `Xinst.some_inv_precond`
  (212 → 28 lines) and `Xinst.inv_noDel_gen` (≈ 230 → 14 lines) collapse into
  three-case arguments over `Xinst.Shape`.
- The `GenericCall`/`GenericCreate` `none_inv_precond`, `some_inv_precond` and
  `inv_noDel` masters use the `repeat' split` dispatch pattern plus new
  `Resume.{call,create}_{state,noDel,run_error}` return-path helpers.
- The executable wrappers (`processMessage_inv_solvent`,
  `processCreateMessage_inv_solvent`, `executeCode_inv_noDel`,
  `processMessage_inv_noDel`, `processCreateMessage_inv_noDel`) go through
  `of_processMessage` and a new `processCreateMessage_eq`
  (`processCreateMessage msg lim = mapResult (processCreateMessage.settle msg)
  (processMessage (processCreateMessage.msg msg) lim)`) instead of unfolding the
  old `Fueled` bind chain.

### 1.5 `Blanc/Weth.lean` — unchanged

Zero references to any replaced name, as predicted; `git diff` against the
pre-step commit is empty.

---

## 2. Verification

All commands run from `~/blanc` on `codex/flatten` = `39ed4a3`.

| gate | verdict |
|---|---|
| pin agreement, all three locations | **PASS** — `1d67748…`; managed checkout is a real directory |
| `lake build` (whole library) | **PASS** — 907 jobs |
| `scripts/check.sh --no-build` (protected-theorem audit) | **PASS** — 4/4 clean |
| `weth_inv_solvent` | **PASS** — `[propext, Classical.choice, Quot.sound]` |
| `stateTransition_inv_solvent` | **PASS** — `[propext, Classical.choice, Quot.sound]` |
| `chain_inv_solvent` | **PASS** — `[propext, Classical.choice, Quot.sound]` |
| `addBlockToChain_inv_solvent` | **PASS** — `[propext, Classical.choice, Quot.sound]` |
| compiler warnings, all five `Blanc/*.lean` | **PASS** — zero |
| `grep` for `sorry` / `admit` / `ofReduce*` / `native_decide` / new `axiom` | **PASS** — none |
| protected theorem statements vs `36c4ec3` | **PASS** — `git diff` over the four statements and the generic `…With/…At/…Using` variants is empty |

ELeVM was **not modified** in this step; `~/elevm` `codex/flatten` is unchanged
at `13895ce` (semantic commit `1d67748`). No ELeVM fixture gate was re-run,
because no ELeVM source changed — those verdicts stand from Step 2 and are
re-confirmed in Step 4.

---

## 3. Metrics

### Line counts (pre-step `36c4ec3` → `39ed4a3`)

| file | before | after | delta |
|---|---:|---:|---|
| `Blanc/Semantics.lean` | 1,833 | 1,220 | −613 (−33 %) |
| `Blanc/Common.lean` | 10,047 | 8,939 | −1,108 (−11 %) |
| `Blanc/Solvent.lean` | 7,195 | 6,505 | −690 (−10 %) |
| `Blanc/Weth.lean` | 325 | 325 | 0 |
| `Blanc/Basic.lean` | 808 | 808 | 0 |
| **total** | **20,208** | **17,797** | **−2,411 (−12 %)** |

`git diff --stat` against `36c4ec3` over the three touched files: 3,002
insertions, 5,413 deletions.

The line-count figure understates the structural win: a substantial part of the
new text is bridging API that did not exist before (≈ 350 lines in
`Semantics.lean`, ≈ 400 in `Common.lean`) and which is precisely what makes the
consuming layers short.

### Structural counts

| metric | before | after |
|---|---:|---:|
| `Exec` constructors | 8 | 6 |
| per-function `Saturation` record | 8 fields + 90-line proof | one `exec_saturates` |
| bind-walking macros/syntax in `Semantics.lean` | 24 | 0 |
| adequacy lemmas | 12 | 3 (+2 retained corollaries) |
| `Fueled.` references in `Solvent.lean` | 36 | 14 |
| `Xinst.Run` references in `Solvent.lean` | 23 | 9 |
| `GenericCall` references in `Solvent.lean` | 22 | 12 |

Largest single collapses: `Xinst.codePreserve_effectGen` 330 → 27 lines,
`Xinst.balance_effectGen` 330 → 18, `Xinst.some_inv_precond` 212 → 28,
`Xinst.inv_noDel_gen` ≈ 230 → 14, the `prep_*` family ≈ 850 → ≈ 120.

### Elaboration time (`lake env lean`, user CPU, this host)

| file | before | after |
|---|---:|---:|
| `Blanc/Semantics.lean` | 5.19 s | 2.13 s (−59 %) |
| `Blanc/Solvent.lean` | 14.24 s | 13.30 s (−7 %) |
| `Blanc/Common.lean` | not measured pre-arc | 24.12 s |

The `Semantics.lean` and `Solvent.lean` baselines are the figures recorded
before the arc; `Common.lean` has no recorded baseline, so its after-figure is
reported without a comparison rather than against a guess. Whole-library
`lake build` from warm oleans is 6.5 s wall / 14.6 s user.

---

## 4. Scope and invariant audit

- ELeVM was **not modified**; no error string, gas constant, or ELeVM name was
  touched from Blanc.
- The four protected theorem statements are **textually unchanged**, as are the
  generic `…With/…At/…Using` variants; `Blanc/Weth.lean` is byte-identical.
- `Common.lean`'s instruction frame-lemma corpus needed **no semantic rework** —
  that stop condition did not trigger.
- No `sorry`, `admit`, `ofReduce*`, `native_decide`, or new axiom entered.
- Zero compiler warnings across the library.

### Statement changes that could not be preserved

Two, both forced by the driver's shape and both predicted by the design note:

1. **`Xlot` is `Option (Evm × Execution)`**, not `Option (Sevm × Devm ×
   Execution)`. Consumers that destructured the triple now take the pair, with
   `sevm_ ↦ evm_.sta` and `devm_ ↦ evm_.dyna`. Affected exported statements:
   `Xlot.Filled`, `Xlot.Good`, `Xlot.Rel`, `Xlot.InvGetCode`, `Xlot.InvNoDel`,
   `Xinst.{none,some}_inv_precond`, `GenericCall/GenericCreate.some_inv_precond`,
   and the `nextSome` handlers of `lift` and `lift_inv`.
2. **Child sub-derivations are indexed at `evm'.pc`, not at `0`.** The old
   mirrors hard-coded `Exec 0 sevm' devm' exn'`; the new relation carries
   `Exec evm'.pc evm'.sta evm'.dyna exn'`. `Frame.enter_run_pc` proves
   `evm'.pc = 0`, so the two are interderivable, but the *statements* of
   `lift`/`lift_inv`'s `nextSome` handlers and of
   `GenericCall/GenericCreate/Xinst.some_inv_precond` changed accordingly.

`lift_core`'s predicate argument also changed from `Exec.Pred` (which takes the
derivation) to a derivation-free `Nat → Sevm → Devm → Execution → Prop`. This is
internal: `lift_core` has exactly one caller (`lift`), which already instantiated
the predicate with one that ignores the derivation.

---

## 5. Stop conditions

None of the plan's four Step-3 stop conditions triggered:

- *a protected statement or axiom set would change* — no; `Exec`'s name and
  indices were preserved for exactly this reason, and the audit confirms it;
- *the depth-induction principle cannot be recovered* — recovered, §1.2;
- *`Common.lean`'s frame-lemma corpus needs semantic rework* — it does not;
- *two focused repair attempts fail on the same lemma family* — no family
  resisted two attempts.

---

## 6. Commit ledger

| repo | commit | purpose | gates | pushed | diagnostic |
|---|---|---|---|---|---|
| blanc | `7e2eab3` | pin bump to ELeVM `1d67748` | pins agree; breakage surveyed | yes | **yes (red)** |
| blanc | `0086a49` | Semantics.lean rebuilt as thin wrappers | `lake build Blanc.Semantics` PASS | yes | **yes (red downstream)** |
| blanc | `614ef3c` | bridging API + Func.Run layer + depth family | Semantics green | yes | **yes (red)** |
| blanc | `70d4595` | codePreserve family | Semantics green; Common 27 decls red | yes | **yes (red)** |
| blanc | `30fce1c` | Common.lean green (Shape, effect, prep, lift_core, balance) | `lake env lean Blanc/Common.lean` clean | no | **yes (Solvent red)** |
| blanc | `39ed4a3` | Solvent.lean green; protected theorems re-established | `lake build` PASS (907 jobs); `scripts/check.sh --no-build` 4/4 clean | **yes** | no |

Branch tip pushed: `blanc` `codex/flatten` = `39ed4a3`.
Recovery points: `36c4ec3` (pre-step) and `39ed4a3` (this green checkpoint).
Trees clean in both repositories.

---

## 7. Autonomous decisions

- **`lift_core`'s predicate made derivation-free.** The alternative was to
  synthesise an old-shaped eliminator over the new constructors. Since
  `lift_core` is internal to `Common.lean` and its only caller already discarded
  the derivation argument, the simpler interface was taken and the decode
  dispatch moved inside `lift_core` so that `lift`/`lift_inv` — which Solvent
  does consume — keep their per-instruction-kind handler shapes.
- **`Xinst.Shape` was strengthened twice** during the step (with the child's
  caller/target relation, then with its code provenance) once it became clear
  the same three-case argument could also discharge Solvent's `precond` and
  `noDel` families. Each strengthening is discharged constructor-by-constructor
  inside `Xinst.step_shape`.
- **Two diagnostic (red) commits** were made mid-step (`30fce1c` and the four
  inherited from the first session) to bound recovery; each is flagged above.
  The step ends green and pushed, as required.

---

## 8. Next handoff — Step 4

Nothing in this step is left open. Step 4 (closure) starts from:

- `~/elevm` `codex/flatten` = `13895ce`, semantic commit `1d67748` (unchanged
  here);
- `~/blanc` `codex/flatten` = `39ed4a3`, pinned to `1d67748`, all three pin
  locations agreeing.

Step 4 must re-run every short ELeVM gate on the exact candidates (build, U256,
vectors, PATCH, RLP4, DEPTH, SMOKE, BLS, current smoke/prague/osaka/transitions)
plus the Blanc build and audit recorded above, arrange the user-owned legacy
`check.sh --full` and `check-mainnet.sh --suite full` runs, and write
`elevm/scripts/report-flatten.md`.
