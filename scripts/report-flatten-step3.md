# Flatten the interpreter recursion — Step 3 report (INCOMPLETE)

**Plan:** `~/plans/flatten.md`, Step 3 ("Rebuild Blanc's shadow layer as thin
wrappers").
**Date:** 2026-07-28 (Asia/Seoul).
**Repository/branch:** `blanc`, `codex/flatten`.
**Status:** **incomplete — stopped at a flagged diagnostic checkpoint.**
`Blanc/Semantics.lean` is fully green and is the step's main deliverable;
`Blanc/Common.lean` is partially repaired and still red; `Blanc/Solvent.lean`
and `Blanc/Weth.lean` were not attempted. The step therefore does **not** meet
its own exit criterion ("the step must end green and pushed"), and the four
protected theorems have **not** been re-established. See §7 for the handoff.

---

## 1. What changed

### 1.1 Pin

`Blanc` now pins ELeVM at the Step-2 flattened-core commit
`1d67748023623ffef3d24ba9cdbc2095586da30b`. All three locations agree
(`lakefile.lean`, `lake-manifest.json`, and the managed checkout
`.lake/packages/elevm` HEAD); the checkout is a real directory, not a symlink.

### 1.2 `Blanc/Semantics.lean` — complete, green

The hand-maintained relational shadow layer is replaced by one generic
derivation relation plus thin non-recursive wrappers, exactly as fixed by the
Step-1 design note.

**The relation.** `Exec` keeps its name and its index shape
`Nat → Sevm → Devm → Execution → Type`, as `weth_inv_solvent`'s statement
requires. Its eight constructors become six — `halt`, `cont`, `doneErr`,
`doneOk`, `runErr`, `runOk` — and every premise other than a sub-derivation is
now an *equation about a non-recursive function* (`Evm.step`, `Frame.enter`,
`Resume.run`, `Frame.settle`).

**`Xlot`** is retyped from `Option (Sevm × Devm × Execution)` to
`Option (Evm × Execution)`, matching what the single driver actually suspends
on. All statements mentioning `Xlot` survive textually; proofs that destructure
the old triple need the pair instead (this is the statement change the design
note predicted, and it is the source of most of the downstream churn).

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
  unchanged**; only the proofs changed, and they shrank to a six-way case
  analysis with no bind-walking.
- `of_processMessage` and `of_processCreateMessage` are retained as derived
  corollaries of a new `of_runFrame`, with **unchanged statements** (they are
  consumed by `Common.lean`).

**Deleted outright** (grep-confirmed absent from `Semantics.lean`): the
`Saturation` record, `saturation`, the macros `eee_bind`, `efg_step_splitXl`,
`efg_step_exec`, `efg_end_exec`, `efg_step_exists`, `efg_step_early`,
`efg_step_ite`, `eq_split`, `eq_ite`, `bind_step_good`, `okStep1`,
`bind_step'`, and the collapsed adequacy chain `of_execute_code'`,
`of_process_message'`, `of_process_create_message'`, `of_generic_create'`,
`of_generic_call'`, `Xinst.run_eq_of_run`, `Ninst.run_of_run'`,
`of_executeCode`, `of_genericCreate`, `of_genericCall`,
`Xinst.run_of_run_eq`, `Ninst.run_of_run_eq`.

**New bridging API** (this is what makes the downstream repair mechanical, and
it is the part of the step with the most leverage):

- *Decode bridge:* `Evm.step_invOp`, `Evm.step_next`, `Evm.step_jump`,
  `Evm.step_last`, `Evm.step_spawn_inv`. Each `*.At` predicate pins the
  driver's step outcome.
- *Step-outcome inversion:* `Step.run_ofExecution`, `Step.ofExecution_cont`,
  `Step.ofExecution_ne_spawn`, `Step.ofExecution_ne_halt_ok`,
  `Step.ofJump_cont`, `Step.ofJump_ne_spawn`, `Step.ofJump_ne_halt_ok`,
  `XStep.toStep_spawn`, `Ninst.step_reg/_push/_exec` (explicit `rfl` forms),
  `Ninst.step_cont_pc`, `Ninst.step_spawn_pc`, `Ninst.step_ne_halt_ok`,
  `Ninst.step_spawn_inv`, `Ninst.step_spawn_depth`.
- *Frame relations:* `RunFrame.of_done`, `RunFrame.of_run`,
  `RunFrame.some_inv`, `RunFrame.depth_eq`, `RunFrame.decompose`, the new
  frame-independent `FrameBody`, `RunFrame.iff_settleMsg`,
  `ProcessMessage.iff_body`, `ProcessCreateMessage.iff_processMessage`,
  `executeCode.enter_inl`, `executeCode.enter_inr`, `ExecuteCode.some_inv`,
  `XStep.Run.some_inv`, `Step.Run.some_inv`.
- *Derivation inversion:* `Exec.halt_inv`, `Exec.last_inv`, `Exec.invOp_inv`.
- *Depth side conditions:* `genericCall.step_spawn_depth`,
  `genericCreate.step_spawn_depth`, `Xinst.step_spawn_depth`,
  `Step.spawn_depth_lt`, `Frame.enter_run_depth`.

**Depth induction is recovered.** `Common.lean`'s `Exec.strong_rec` needs a
strict decrease at every child derivation; `Step.spawn_depth_lt` (every spawn
is depth-guarded, and `callMsg`/`createMsg` set `depth := sevm.depth - 1`) plus
`Frame.enter_run_depth` (entering a frame preserves its depth) discharge it
once. This was the design note's main risk item and it is **resolved**.

### 1.3 `Blanc/Common.lean` — partially repaired, still red

Repaired and green:

- `Linst.run_of_at` — now a one-liner off `Exec.last_inv` (was 8 case tags).
- `Exec'.Prec` rewritten with five constructors over the new `Exec`
  (`cont`, `doneOk`, `runErrChild`, `runOkChild`, `runOkCont`), and
  `Exec'.lt.well_founded` rewritten as a six-case `Exec.rec`.
- `Rinst.run_of_at`, `Jinst.run_of_at`, `Ninst.run_of_at`, `push_of_pushAt` —
  the Func.Run-layer step-forward lemmas.
- The entire depth family (`ExecuteCode.depth_eq`, `ProcessMessage.depth_eq`,
  `ProcessCreateMessage.depth_eq`, `GenericCall.depth_lt`,
  `GenericCreate.depth_lt`, `Xinst.depth_lt`, `Ninst.depth_lt_of_run'_some`) —
  ~200 lines of bind-chain walking collapsed to 2–4 line proofs.
- `Xlot.InvGetCode` retyped; `ExecuteCode.codePreserve`,
  `ProcessMessage.codePreserve`, `ProcessCreateMessage.codePreserve`,
  `GenericCreate.codePreserve`; new helpers `createMsg_benv_state_getCode`
  and `Resume.create_getCode`.

`GenericCreate.codePreserve` establishes the **reusable pattern for the
remaining instruction-body walks**: unfold the step function, `simp only` the
`Except` plumbing, `repeat' split`, then close each branch with the existing
`getCode` lemmas. It produced exactly the seven expected branches (two
assertion failures, the balance/max-nonce/depth-zero early exit ×2 for the
push outcome, the address-collision early exit ×2, and the spawn).

**Still red — 27 declarations:**

| region | declarations |
|---|---|
| spawn-preparation facts | `Xinst.prep_codeFrame`, `Xinst.prep_inv_getCode`, `Ninst.prep_inv_getCode`, `Xinst.prep_codeSource`, `Xinst.prep_inv_code`, `Ninst.prep_inv_code` |
| remaining body walk | `GenericCall.codePreserve` |
| effect machinery | `Xlot.Rel`, `Ninst.effectGen_reg`, `Ninst.effectGen_exec`, `Exec.effect`, `Xlot.rel_of_filled`, `Xlot.invGetCode_of_rel`, `Xlot.rel_of_invGetCode`, `Xinst.codePreserve_effectGen`, `Ninst.push_instructionFrame_effectGen`, `Ninst.push_effectGen_of_instructionFrame` |
| the eliminator | `lift_core`, `lift`, `lift_inv` |
| leaves | `of_run_reg`, `of_run_push`, `Rinst.inv_stor`, `Xlot.InvNoDel` |
| balance masters | `ExecuteCode.balance_effect`, `ProcessMessage.balance_effect`, `ProcessCreateMessage.balance_effect` |

`Exec.effect` and `lift_core` are the two structural ones: both enumerate the
old eight `Exec` constructors and must be rewritten to the new six, the same
way `Exec'.lt.well_founded` already was. The rest are mechanical applications
of the two patterns already established (frame decomposition for the
message-level masters; `repeat' split` for the instruction bodies).

### 1.4 `Blanc/Solvent.lean`, `Blanc/Weth.lean` — not attempted

Untouched. Grep-measured consuming surface, for the continuation:
`Solvent.lean` has 25 `of_exec` lines, 4 `exec_iff_exec_eq`, 25 `Xlot`,
23 `Xinst.Run`, 22 `GenericCall`, 18 `Ninst.Run'`, 12 `Exec.`, and 36
`Fueled.` lines; `Weth.lean` has **zero** references to any of the replaced
names, so it should need at most incidental repair.

---

## 2. Verification

| gate | verdict |
|---|---|
| pin agreement, all three locations | **PASS** — `1d67748…`, managed checkout is a real directory |
| `lake build Blanc.Semantics` | **PASS** — 892 jobs |
| LSP diagnostics, `Blanc/Semantics.lean` | **PASS** — empty |
| `lake build` (whole library) | **FAIL** — `Blanc.Common` red (27 declarations) |
| `scripts/check.sh --no-build` (protected-theorem audit) | **NOT RUN** — requires a green build |
| `grep` for `sorry` / `admit` / `ofReduce*` / `native_decide` / new `axiom` | **PASS** — none in any `Blanc/*.lean` |

The protected theorems `weth_inv_solvent`, `stateTransition_inv_solvent`,
`chain_inv_solvent`, `addBlockToChain_inv_solvent` are **not re-established**
and their axiom sets are **unaudited** at this checkpoint. Their *statements*
are untouched (`Solvent.lean` was not edited), and `Exec`'s name and indices
were preserved precisely so that `weth_inv_solvent`'s statement survives, but
that is a design property, not a verified one, until the build is green.

---

## 3. Metrics (partial — before/after for the completed file only)

| metric | before (`36c4ec3`) | after | delta |
|---|---:|---:|---|
| `Blanc/Semantics.lean` lines | 1,833 | 1,184 | −649 (−35 %) |
| `Semantics.lean` elaboration (`lake env lean`, user CPU) | 5.19 s | 2.10 s | −60 % |
| `Exec` constructors | 8 | 6 | −2 |
| per-function `Saturation` record | 8 fields + 90-line proof | one `exec_saturates` | deleted |
| bind-walking macros deleted | — | 13 | `eee_bind`, `efg_step_*` (5), `eq_split`, `eq_ite`, `bind_step_good`, `okStep1`, `bind_step'`, `efg_end_exec`, `efg_step_exec` |
| adequacy lemmas collapsed | 12 | 3 (+2 retained corollaries) | −9 |

`Blanc/Solvent.lean` elaboration was measured before the change (14.24 s user)
but cannot be re-measured until the build is green, so no after-figure is
recorded.

The line-count figure understates the structural win and overstates nothing:
~350 of the 1,184 remaining lines are the *new* bridging API of §1.2, which did
not exist before and which is what makes the downstream layer short. The
replaced regions proper (mirrors + `Fueled` lemma library + adequacy chain,
old `:95-1164`) went from ~1,070 lines to ~430.

---

## 4. Scope and invariant audit

- ELeVM was **not modified** in this step; `~/elevm` `codex/flatten` is
  unchanged at `1d67748`.
- No `Solvent.lean` or `Weth.lean` edit, so no protected statement changed.
- `Common.lean`'s instruction frame-lemma corpus needed **no semantic rework**
  — the stop condition on that did not trigger. Every `Common.lean` change so
  far is either a case-name/arity adaptation to the new `Exec`, an `Xlot`
  pair-vs-triple adaptation, or a proof that got shorter.
- No `sorry`, `admit`, `ofReduce*`, `native_decide`, or new axiom entered.
- No error string, gas constant, or ELeVM name was touched.

---

## 5. Stop conditions

None of the plan's four Step-3 stop conditions triggered:

- *a protected statement or axiom set would change* — no; `Exec`'s name and
  indices were preserved exactly for this reason.
- *the depth-induction principle cannot be recovered* — recovered, see §1.2.
- *`Common.lean`'s frame-lemma corpus needs semantic rework* — it does not.
- *two focused repair attempts fail on the same lemma family* — no family
  resisted two attempts; every repair attempted so far succeeded.

The step stopped for **session capacity**, not for a semantic obstacle. The
remaining work is understood, bounded, and mechanical, but it is roughly
2–3× what was completed here.

---

## 6. Commit ledger

| repo | commit | purpose | gates | pushed | diagnostic |
|---|---|---|---|---|---|
| blanc | `7e2eab3` | pin bump to ELeVM `1d67748` | pins agree; breakage surveyed (80 errors, all in Semantics.lean) | yes | **yes (red)** |
| blanc | `0086a49` | Semantics.lean rebuilt as thin wrappers | `lake build Blanc.Semantics` PASS; LSP clean | yes | **yes** (downstream still red) |
| blanc | `614ef3c` | bridging API + Func.Run layer + depth family | Semantics green; Common partially repaired | yes | **yes (red)** |
| blanc | `70d4595` | codePreserve family + `GenericCreate.codePreserve` | Semantics green; Common 27 decls red | yes | **yes (red)** |

Branch tip pushed: `blanc` `codex/flatten` = `70d4595`.
Recovery points: `36c4ec3` (pre-step), and `0086a49` for a
Semantics-only-green state.

---

## 7. Handoff — what the continuation must do

1. **Finish `Common.lean` (27 declarations).** In this order, because of
   dependencies:
   - `Xinst.prep_codeFrame` / `prep_codeSource` / `prep_inv_getCode` /
     `prep_inv_code` and the two `Ninst.prep_*` — apply the
     `GenericCreate.codePreserve` pattern (§1.3) to `Xinst.step`, using
     `XStep.Run.some_inv` to get the spawn and `Frame`/`createMsg`/`callMsg`
     projections to read off the child's initial state. Statements change only
     by `(sevm_, devm_, exn_) ↦ (evm_, exn_)` with `sevm_ ↦ evm_.sta`,
     `devm_ ↦ evm_.dyna`.
   - `GenericCall.codePreserve` — same pattern as `GenericCreate`; expect a
     three-way split (depth-zero early exit, then the spawn) plus a
     `Resume.call_getCode` helper mirroring `Resume.create_getCode`.
   - `Exec.effect` and `lift_core`/`lift`/`lift_inv` — rewrite the eight-way
     constructor enumerations to the new six, exactly as
     `Exec'.lt.well_founded` was rewritten. `lift_core` is the largest single
     item (27 errors) and is where a derived old-shaped eliminator, if one is
     wanted at all, would pay for itself.
   - the `Xlot.Rel` / `effectGen` / `balance_effect` group — these are
     message-level and should go through `FrameBody` /
     `RunFrame.iff_settleMsg` / `ProcessCreateMessage.iff_processMessage`,
     the way the `codePreserve` family already does.
2. **Then `Solvent.lean`** (surface measured in §1.4) and **`Weth.lean`**
   (expected trivial).
3. **Then the exit gates:** `lake build` green, `scripts/check.sh --no-build`
   exact axiom audit (`[propext, Classical.choice, Quot.sound]`, no
   `sorryAx`/`ofReduce*`) on all four protected theorems plus the generic
   `…With/…At/…Using` variants, and the after-metrics for `Solvent.lean`
   elaboration.
4. **Then push a green checkpoint** and only then hand off to Step 4.

Nothing in Step 4 can begin until the protected-theorem audit passes: the
whole point of the arc's exit criterion is that those four statements and
their axiom sets are unchanged, and that is currently unverified.
