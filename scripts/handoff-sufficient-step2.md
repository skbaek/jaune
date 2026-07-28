# Step 2 sufficiency handoff — 2026-07-28

> **SUPERSEDED — Step 2 is complete.** Everything listed below as remaining was
> finished in commits `6215a8f` and `17556bf`. See
> `scripts/report-sufficient-step2.md` for the outcome, the corpus census, the
> gate verdicts, and the Step-3 handoff. This note is kept only as a record of
> the session boundary; do not work from its "Remaining Step 2 work" list.
>
> Two of its statements no longer apply in the current environment: the
> `~/elanc/.work-sufficient/Sufficiency.lean` mirror is unnecessary
> (`~/elevm` is directly writable), and the plan's `.ok`-only monotonicity
> statement turned out to be too weak — see the report's *Unexpected findings*.

## Request and governing plan

- User request: perform **Step 2** from `/Users/agent/plans/sufficient.md`.
- ELeVM repository: `/Users/agent/elevm`
- Branch: `codex/sufficient`
- Do not push during Step 2.
- Do not change instruction definitions, execution semantics, or charge timing.
- Continue using the `lean-inspector` and `lean-prover` skills and the
  `lean-lsp-mcp` tools. After every Lean edit, query `lean_goal` and
  `lean_diagnostic_messages`.

## Durable repository state

- Step 1 base commit: `5c5fe7a`
- Completed Rinst checkpoint commit:
  `3ac154f sufficiency: prove strict decrease for Rinst`
- The current working tree contains a **clean, uncommitted** continuation in:
  `/Users/agent/elevm/Elevm/Sufficiency.lean`
- A byte-for-byte editable mirror is kept at:
  `/Users/agent/elanc/.work-sufficient/Sufficiency.lean`
- Current Lean file length: 1475 lines.
- Full-file LSP diagnostics were clean when this note was written.
- No `sorry`, `admit`, new axiom, `ofReduceBool`, or raised resource limit was
  introduced.

## Completed and checked

### Rinst checkpoint (committed)

- Universal strict-decrease theorem for all 69 `Rinst` constructors:
  `Rinst.runCore_gasLt`.
- Includes arithmetic/bitwise combinator cases and bespoke walks for memory,
  storage, access lists, environmental instructions, logs, DUP/SWAP, etc.
- Required checkpoint gates passed:
  - LSP diagnostics: clean
  - `lake build`: PASS, `real 9.53`, `user 13.20`, `sys 3.73`
  - `scripts/check.sh --depth --no-build`: PASS, 67/67

### Uncommitted continuation (LSP clean)

- Universal `Jinst.runCore_gasLt` for all 3 jump instructions.
- `except64th_le`.
- `processCreateMessage.msg_gas`.
- `genericCreate.step_gasDecreasing`, including:
  - depth/balance/nonce refund path,
  - collision path,
  - spawn path,
  - exact `except64th` arithmetic.
- Strict-decrease proofs for all 6 `Xinst` constructors:
  - existing Step-1 CALL pilot,
  - CREATE,
  - CREATE2,
  - CALLCODE,
  - DELEGATECALL (`delcall`),
  - STATICCALL.
- Universal `Xinst.step_gasDecreasing`.
- Frame-support lemmas completed so far:
  - `executePrecomp_gasLe`
  - `executeCode.handleError_ok_gasLe`
  - `chargeGas_result_gasLe`

## Exact next proof target

Prove:

```lean
theorem processCreateMessage.chargeCodeGas_gasLe
    (rules : ForkRules) (devm : Devm) :
    (processCreateMessage.chargeCodeGas rules devm).gasLeft ≤ devm.gasLeft := by
  ...
```

One attempted proof was removed before this checkpoint so the file remains
LSP-clean. The failed tactic was `split` immediately after unfolding
`processCreateMessage.chargeCodeGas`; the goal has let-bound
`contractCode`/`contractCodeGas`, so `split` could not expose the match.

Recommended next attempt:

1. Generalize or case-split `devm.output` explicitly.
2. In the `0xEF :: _` branch, the result carries `devm` unchanged.
3. In the other branch, case-split
   `chargeGas (devm.output.length * gasCodeDeposit) devm`.
4. Reuse `chargeGas_result_gasLe`; both the max-code-size error and success
   carry the charged `Devm`.

A likely skeleton is:

```lean
  generalize hcode : devm.output = code
  cases code with
  | nil =>
      -- simplify chargeCodeGas with hcode, then case chargeGas
  | cons b bs =>
      by_cases hb : b = 0xEF
      · subst b
        -- simplify the invalid-prefix branch
      · -- simplify the non-prefix branch, case chargeGas, reuse
          -- chargeGas_result_gasLe
```

Use `lean_multi_attempt` after exposing the exact branch goal rather than
guessing a large `simp` set.

## Remaining Step 2 work

1. Finish settlement/frame/resume arithmetic:
   - `processCreateMessage.chargeCodeGas_gasLe`
   - `processMessage.settle` gas preservation
   - `processCreateMessage.settle` non-increase
   - `Frame.settle` non-increase
   - `Frame.enter`:
     - `.run` child begins with exactly `frame.inner.gas`
     - successful `.done` child has gas at most `frame.inner.gas`
   - both `Resume.run` branches, including the error path. The existing
     `Resume.run_ok_gasLeft` handles successful results.
2. Define/prove the step-level predicate and finish:
   - `Ninst.step` push branch
   - regular branch via `Rinst.runCore_gasLt`
   - exec branch via `Xinst.step_gasDecreasing`
   - `Evm.step` top-level strict-decrease/halting bound.
3. Prove raw driver monotonicity for the current driver name `exec`
   (Step 3 performs the rename to `execCore`).
4. Prove the sufficiency theorem by structural induction on `lim`.
   The expected final additive constant is **1**.
5. At the Jinst/Ninst/Xinst/frame family checkpoint run:
   - full-file LSP diagnostics
   - `lake build`
   - U256
   - DEPTH
   - then commit.
6. At the driver checkpoint run:
   - LSP diagnostics
   - `lake build`
   - U256
   - DEPTH
   - SMOKE
   - current smoke
   - then commit.
7. Write the Step-2 report with:
   - final constant,
   - bespoke vs combinator-derived count,
   - added line count,
   - build-time comparison,
   - gate results and commit ledger.

## Important proof facts already available

- `XStep.GasDecreasing n`
  - `.done ex`: every successful result has gas `< n`
  - `.spawn frame rsm`: `frame.inner.gas + rsm.parentGas < n`
- `Resume.parentGas`
- `Resume.run_ok_gasLeft`
- `genericCall.step_gasDecreasing`
- `genericCreate.step_gasDecreasing`
- `calculateMsgCallGas_stipend_lt`
- `call_charge_stipend_lt`
- `accessDelegation_gasLeft`
- `executePrecomp_gasLe`
- `executeCode.handleError_ok_gasLe`
- `chargeGas_result_gasLe`

## Workspace/editing procedure

The ELeVM repository is outside the current writable root. Continue editing
the mirror with `apply_patch`, then copy it to the repository:

```sh
cp /Users/agent/elanc/.work-sufficient/Sufficiency.lean \
  /Users/agent/elevm/Elevm/Sufficiency.lean
```

The `cp` escalation prefix was approved. After each copy, inspect the edited
line with `lean_goal` and the file/range with `lean_diagnostic_messages`.

Do not use `lean_run_code` in this environment: it returned unsound-looking
results during exploration. Actual-file LSP queries and `lean_multi_attempt`
were reliable.

## Current verification/status commands

At handoff:

```text
git branch: codex/sufficient
ahead of origin by: 1 commit
modified: Elevm/Sufficiency.lean
full-file LSP diagnostics: clean
```

The uncommitted Jinst/Xinst/frame-support continuation has **not** yet had a
fresh `lake build`, U256, or DEPTH run; do those before its family commit.
