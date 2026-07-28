# Sufficiency arc — Step 1 design report

**Plan:** `~/plans/sufficient.md`, Step 1 (design, module split, gas-decrease
infrastructure, pilot).
**Date:** 2026-07-28 (Asia/Seoul).
**Branch:** `codex/sufficient` in `~/elevm`, from `main` at
`7bdc10060a8f5491557cc400f00b604531caa3c8`.

## 0. Starting point re-verification and drift

Every fact in the plan's "Verified starting point" was re-checked before the
first edit. **No drift.**

| Fact | Plan | Observed |
| --- | --- | --- |
| ELeVM `main` | `7bdc100…`, clean | identical, clean |
| Blanc `main` | `39ed4a3…`, clean | identical, clean |
| Toolchain | `leanprover/lean4:v4.32.1` | identical in both repos |
| Blanc's ELeVM pin | `1d67748…` in all three locations | identical |
| `Elevm/Execution.lean` | 6,894 lines | 6,894 |
| `Fueled` mentions in `Execution.lean` | 32 | 32 |
| `abbrev Fueled` / namespace | `:1550` / `:1552-1601` | identical |
| driver `exec` | `:4172`, `termination_by lim` | identical |
| wrappers | `:4193 / :4200 / :4206 / :4210` | identical |
| consumers | `:4950 / :4983 / :5027` | identical |
| `"RecursionLimit"` sites | exactly 2, at `:4961` and `:5005` | identical |
| `Rinst` / `Jinst` / `Xinst` constructors | 69 / 3 / 6 | 69 / 3 / 6 |
| Blanc `Fueled` mentions | Semantics 104, Common 15, Solvent 14 | identical |
| `lake build` | 1,760 jobs | 1,760 jobs, 3.7 s (cached) |

## 1. The module split

### Decision: a clean three-way cut was available; the inline fallback was not needed.

```
Elevm/Execution.lean      1 – 4,948   the interpreter, through the frame
                                      wrappers and their #guards
Elevm/Sufficiency.lean    new         the corpus, the theorem, sufficientLim,
                                      and (from Step 3) the total definitions
Elevm/Transaction.lean    ex-4950 – 6894   processMessageCall onward: the
                                      transaction, block, and chain machinery
```

Dependency analysis behind the cut point:

* The only consumers of `exec`, `runFrame`, `executeCode`, `processMessage`, or
  `processCreateMessage` anywhere in the repository are the `flattenGuard*`
  checks at `:4237–4324` and `processMessageCall.create/.call` at `:4963`/`:5007`.
  Nothing outside `Execution.lean` referenced the driver, `Fueled`, or the
  wrappers at all.
* The guards stay with the driver. `processMessageCall.create` at the old
  `:4950` is therefore the *first* consumer, and the cut is placed exactly
  there.
* The plan permits declarations between `:4213` and `:4950` that do not depend
  on the driver to stay put, and they do: the `Test`/bloom/header/`recoverSender`/
  `setDelegation` block at `:4333–4949` has no driver dependency and was left in
  `Elevm/Execution.lean`. Keeping it there minimises the moved text and so the
  size of the reviewable diff.
* No `namespace`, `section`, `open`, `variable`, or `set_option` block spans the
  cut, so the tail is self-contained.

### Verification that the move is pure

Concatenating the new `Execution.lean` with `Transaction.lean` minus its
24-line prologue (module header plus the two restated `#guard` helpers of the
next subsection) is **byte-identical** to the pre-split file (`diff` reports no
difference). Reproduce with:

```bash
{ cat Elevm/Execution.lean; printf '\n'; tail -n +25 Elevm/Transaction.lean; } | diff - <(git show 7bdc100:Elevm/Execution.lean)
```

### The one deviation from strict text motion

`private` declarations do not cross module boundaries. Two `#guard` helpers —
`errOf` and `hasTag`, at `Execution.lean:1219` and `:1223` — are used by
`#guard`s on both sides of the cut (73 `hasTag` and 10 `errOf` uses in the moved
text). They are **restated privately** in `Elevm/Transaction.lean` rather than
being made public, so the library's public API is unchanged. The alternative —
dropping `private` — would have widened the public surface of a library Blanc
depends on, for two test helpers. The restatement carries a comment pointing at
its counterpart.

Import updates: `Elevm.lean` and `Main.lean` gain both new modules;
`Elevm/FixtureException.lean` now imports `Elevm.Transaction`.

## 2. The measure, the relation, and the obligations

### The measure and the relation

The relation is the **single field** `devm'.gasLeft < devm.gasLeft`, written
inline as an inequality rather than as a named relation, so that `omega` sees it
without an unfolding step.

It is deliberately not Blanc's `Devm.Burn`: that relation is non-strict
(`gasLeft ≥`) and bundles thirteen further field equalities. Neither property is
wanted here, and importing it would couple ELeVM to Blanc's proof architecture
backwards. Only its proof *shape* was a useful model.

One auxiliary definition is needed because the driver's `.spawn` branch consumes
a raw frame result in both branches:

```lean
def Execution.gasLeft : Execution → Nat
  | .ok devm  => devm.gasLeft
  | .error e  => e.2.gasLeft
```

### The obligations — and a reduction from four to two

The plan anticipated four obligations (per-step `.cont`, spawned-child,
resume-after-`.done`, resume-after-child). **They collapse to two.**

The three spawn-shaped obligations are all consequences of one arithmetic fact
about the spawning step, because the surrounding machinery is generic:

* `Frame.enter` hands the child exactly `frame.inner.gas` — the child's whole
  budget is a field of the frame, not something the driver computes;
* neither the child's own run nor `Frame.settle` can increase that budget
  (driver monotonicity plus settle monotonicity, both Step 2);
* `Resume.run` succeeds only by incorporating a child that succeeded, and always
  returns exactly `rsm.parentGas + child.gasLeft`. This is **proved** in Step 1
  as `Resume.run_ok_gasLeft`:

  ```lean
  theorem Resume.run_ok_gasLeft {rsm : Resume} {r} {devm' : Devm}
      (h : rsm.run r = .ok devm') :
      ∃ child : Devm, r = .ok child ∧
        devm'.gasLeft = rsm.parentGas + child.gasLeft
  ```

So the spawning instruction only has to establish that the parent's retained gas
plus the child's whole budget is below where the parent started. That is
captured by:

```lean
def XStep.GasDecreasing (n : Nat) : XStep → Prop
  | .done ex          => ∀ devm', ex = .ok devm' → devm'.gasLeft < n
  | .spawn frame rsm  => frame.inner.gas + rsm.parentGas < n

def Resume.parentGas : Resume → Nat
  | .create parent _  => parent.gasLeft
  | .call parent _ _  => parent.gasLeft
```

The two obligations Step 2 must discharge per instruction are therefore:

```lean
-- O1, continuing steps
theorem Evm.step_cont_gasLt {evm pc devm}
    (h : evm.step = .cont pc devm) : devm.gasLeft < evm.dyna.gasLeft

-- O2, spawning steps (the three former spawn obligations, unified)
theorem Evm.step_spawn_gas {evm frame rsm pc}
    (h : evm.step = .spawn frame rsm pc) :
    frame.inner.gas + rsm.parentGas < evm.dyna.gasLeft
```

plus the two generic bridges that turn O2 into what the driver's induction
needs (`Frame.enter_run_gas`, `Frame.settle_gasLe`) and the precompile-path
bound for `Frame.enter = .done`.

### Driver monotonicity

Stated over **both** branches of the raw result, because `Frame.settle` consumes
both and the `.error` payload's `Devm` is what a `Revert` carries back:

```lean
theorem exec_gasLe {evm lim raw}
    (h : (exec evm lim).run = some raw) : raw.gasLeft ≤ evm.dyna.gasLeft
```

The plan's `.ok`-only form is the special case; the general form is what the
resume-after-child step actually uses.

### The sufficiency statement and the constant

```lean
theorem execCore_ne_exhausted {evm : Evm} {lim : Nat}
    (h : evm.dyna.gasLeft < lim) : (execCore evm lim).run ≠ none

def sufficientLim (gas : Nat) : Nat := gas + 1
```

**The constant is 1.** Nothing found in Step 1 obstructs the tight bound. The
induction's base case is vacuous (`gasLeft < 0` is false), and every continuing
outcome strictly decreases `gasLeft`, so one unit of fuel per unit of gas plus
one is exactly enough. The pilot confirmed the two places the readiness audit
flagged as the risk — the `calculateMsgCallGas` stipend and the depth-0 refund —
need no slack. No fallback constant is required. This is recorded now so Step 3
can define `sufficientLim` without re-deriving it; if Step 2's remaining
families were to force slack, the report boundary is a documented larger
constant, not a stop condition.

### Charge timing

Untouched, and nothing in the pilot came close to needing it moved. The
`.call` proof in particular reads `devm.gasLeft` *after* the pops and *before*
the charge, exactly as `calculateMsgCallGas` requires, and the argument goes
through with the existing ordering. Plan invariant 4 holds.

## 3. The combinator layer

`Elevm/Sufficiency.lean` is 686 lines / 65 declarations, in six layers below
the pilot.

| Layer | Count | Content |
| --- | --- | --- |
| `Execution.gasLeft` | 3 | the definition and its two `@[simp]` equations |
| Gas-preserving updates | 23 | every `Devm → Devm` update other than `withGasLeft` (21) plus the two access-list inserts, all by `rfl`, all `@[simp]` |
| Charging | 3 | `chargeGas_gasLeft` (exact equation), `_gasLt`, `_gasLe` |
| Stack | 5 | `push`, `pop`, `popToNat`, `popToAdr`, `popN` |
| Footprint lifts | 3 | `liftMachExecution_ok`, `liftMachMetaExecution_ok`, `liftMachMetaWorldExecution_ok` |
| `Mach` core + instruction combinators | 11 | `Mach.{chargeGas,pop,push,pushItem,applyUnary,applyBinary,applyTernary}_gasLeft` and their `Devm`-level counterparts |

Two design choices are worth recording:

1. **`chargeGas_gasLeft` is an exact equation** (`devm'.gasLeft + c = devm.gasLeft`),
   not an inequality. The call and create families need to add the charge back
   to compare the child's budget with the parent's original gas, and an
   inequality would lose that.
2. **`Except.bind_eq_ok` replaces the `split`/`rename_i` idiom.**

   ```lean
   theorem Except.bind_eq_ok {e : Except ε α} {f : α → Except ε β} {b : β}
       (h : e >>= f = .ok b) : ∃ a, e = .ok a ∧ f a = .ok b
   ```

   Peeling one `bind` at a time never requires writing the scrutinee out, so an
   arbitrarily large cost expression — `calculateMsgCallGas` applied to a
   four-line `extra_gas` computation, in the `.call` case — never appears in the
   proof text. This is the single most important device for Step 2's cost, and
   it is why the seven-pop `.call` walk is six lines of `obtain`. Note that a
   `dsimp only at …` is needed after the `obtain`s to reduce the `(x, d).2`
   projections before `omega` will see them as the same atoms.

   There is no `applyTernary_def` in `Execution.lean` to match `applyUnary_def`
   and `applyBinary_def`; rather than add one, the `apply*` family is proved at
   the `Mach` level and lifted, which also gives `liftMachMetaWorldExecution_ok`
   for `Rinst.balanceCore` free of charge.

### `Rinst` coverage census (all 69 constructors classified)

| Shape | Count | Constructors | Step-2 cost |
| --- | --- | --- | --- |
| Bare `pushItem` | 19 | address, basefee, blobbasefee, origin, caller, callvalue, calldatasize, codesize, gasprice, retdatasize, selfbalance, chainid, number, timestamp, gaslimit, prevrandao, coinbase, msize, pc | one combinator application |
| Bare `applyBinary` | 20 | add, sub, mul, div, sdiv, mod, smod, lt, gt, slt, sgt, eq, and, or, xor, byte, shl, shr, sar, signextend | one combinator application |
| Bare `applyUnary` | 2 | iszero, not | one combinator application |
| Bare `applyTernary` | 2 | addmod, mulmod | one combinator application |
| **Combinator-derived subtotal** | **43** | | |
| `applyUnary` under a fork gate | 1 | clz | one `split`, then a combinator |
| Short walk (≤ 4 binds: pops → charge → push/write) | 17 | blobhash, calldataload, calldatacopy, codecopy, retdatacopy, mload, mstore, mstore8, gas, pop, kec, exp, swap, dup, tload, mcopy, blockhash | pilot pattern, ~10 lines each |
| Warm/cold `if` around the charge | 4 | extcodesize, extcodecopy, extcodehash, sload | pilot pattern, ~16 lines each |
| Bespoke | 4 | sstore, tstore, log, balance | individual attention |
| **Walk subtotal** | **26** | | |

**43 of 69 constructors are one combinator application; 22 more follow a pilot
pattern; only 4 need genuine bespoke work.**

The plan's estimate to check against was Blanc's 48 bespoke
`_runCore_instructionFrame` lemmas over the same 69 constructors. This corpus
lands at 26 walks and 4 bespoke — roughly half. Two caveats on the comparison:
Blanc's lemmas prove much more than a gas fact (13 field equalities each), and
they are stated against Blanc's mirror definitions rather than ELeVM's own, so
the numbers are not measuring the same work. The honest reading is that the
combinator layer removes 43 constructors from the grind entirely, which the
Blanc precedent did not.

`Jinst` (3) and `Xinst` (6) are individually walked; `Ninst.step`'s push branch
is a two-line `chargeGas` argument (`gBase`/`gVerylow`, both positive).

## 4. The call family, and the one lemma that carries it

The readiness audit's hardest case — the `except64th`/stipend accounting —
turned out to have a clean statement that needs **no hypothesis about the
parent's remaining gas at all**, and that holds in *both* branches of
`calculateMsgCallGas`:

```lean
theorem calculateMsgCallGas_stipend_lt
    {value gas gasLeft memoryCost extraGas cs : Nat}
    (hstip : (if value = 0 then 0 else cs) < extraGas + memoryCost) :
    (calculateMsgCallGas value gas gasLeft memoryCost extraGas cs).2 <
      (calculateMsgCallGas value gas gasLeft memoryCost extraGas cs).1 + memoryCost
```

*The stipend handed to the child is strictly less than the cost charged to the
parent.* Combined with `chargeGas_gasLeft` this immediately gives
`parent_after.gasLeft + stipend < parent_before.gasLeft`, which is exactly what
all three call outcomes need: the depth-0 refund, the insufficient-balance
refund, and the spawn (whose child budget *is* the stipend). Packaged as
`call_charge_stipend_lt`, it is a one-line instantiation per site.

The side condition is per-opcode and trivially checkable:

* `value = 0`: needs `0 < extra_gas + memory_cost`, supplied by
  `gasWarmAccess ≤ access_cost` (100 in the warm case, 2,600 cold);
* `value ≠ 0`: needs `gCallStipend < extra_gas`, supplied by
  `transferCost = gasCallValue = 9000 > 2300`.

`.delcall` and `.statcall` pass a literal `0` for `value`, so they only need the
first. Branch 1 of `calculateMsgCallGas` — the one the audit noted returns a
cost exceeding `gas_left` — needs no separate treatment: the lemma holds there
too, so the proof never has to argue that `chargeGas` fails.

**The `except64th n = n` trap for `n < 64` never arises.** The proof does not
mention `except64th` at all. What carries the CREATE case is the same shape: the
upfront `gasCreate = 32000` charge sits above the `createGas` that is later
refunded or handed to the child.

## 5. The pilot

Five representative obligations, chosen one per shape Step 2 will meet.

| Pilot | Shape it stands for | Result |
| --- | --- | --- |
| `Rinst.runCore_add_gasLt` | the `apply*` family (43 constructors) | 7 lines |
| `Rinst.runCore_mstore_gasLt` | memory-extending body (17 constructors) | 15 lines |
| `Rinst.runCore_extcodesize_gasLt` | warm/cold access, charge inside an `if` (4 constructors) | 22 lines |
| `Jinst.runCore_jumpdest_gasLt` | the smallest charge in the machine, `gJumpdest = 1` | 11 lines |
| `Xinst.step_call_gasDecreasing` | a call-type spawn *and* both its refund branches | 63 lines, on top of the 24-line `genericCall.step_gasDecreasing` and the 14-line `call_charge_stipend_lt`, both of which the other five `Xinst` constructors reuse |

All five went through with the intended combinators; none needed a definition
touched, a charge moved, or a constant weakened. Two findings worth carrying
into Step 2:

* **The elaborator pushes a `do` continuation into both arms of an `if`.** In
  `.extcodesize` the source reads `let devm ← if warm then chargeGas … else …`,
  but the elaborated term is `if warm then (do chargeGas …; push …) else (…)`.
  The walk must `split` *before* peeling the remaining binds, not after. All
  four warm/cold constructors share this.
* **`Xinst.step .call` needs no `match` on `accessDelegation`.** Its
  five-way destructuring `let` elaborates to projections, not a `match`, so the
  walk is uninterrupted; `accessDelegation_gasLeft` (proved here, `@[simp]`)
  discharges the projection.

### Sizing Step 2

Extrapolating from the pilot at the measured line counts: 43 combinator cases at
~7 lines, 17 short walks at ~15, 4 warm/cold at ~22, 1 fork-gated at ~10, 4
bespoke at ~40, `Jinst` 3 at ~12, `Xinst` 6 at ~50 (four call-type reusing
`call_charge_stipend_lt`, two create-type sharing a `gasCreate` argument),
`Ninst`/`Evm.step`/monotonicity/sufficiency at ~200 → **roughly 1,400–1,700
added lines**. At the measured elaboration rate for this module (686 lines in
1.45 s of content time) that is **~3–4 s of added elaboration**, which is the
figure to hold Step 2 against.

## 6. Verification

All commands from `~/elevm` on `codex/sufficient`.

| Gate | Result |
| --- | --- |
| `lake build` | **1,764 jobs PASS**, 8.2 s wall (was 1,760 jobs; +4 for the two new modules) |
| `scripts/check-u256.sh` | **21,593/21,593 PASS** |
| `scripts/check.sh --depth --no-build` | **67/67 match baseline** (67 PASS, 0 FAIL) — the recursion-stress gate, green at both commits |
| `scripts/check-mainnet.sh --suite smoke --no-build` | **16/16 PASS**, 0.50 s |
| `scripts/check-hygiene.sh` | **clean** — 2 allowlisted occurrences, no new ones |
| LSP diagnostics, `Elevm/Sufficiency.lean` | **no errors, no warnings** |
| `grep` for `sorry`/`admit`/`ofReduce`/`axiom`/`native_decide`/limit-raising | **none** in `Sufficiency.lean` |
| `#print axioms` on 8 representative results | all `[propext, Classical.choice, Quot.sound]` |

### Elaboration timings (user CPU, second of two runs)

| Module | Before | After |
| --- | --- | --- |
| `Elevm/Execution.lean` (whole, pre-split) | 5.93 s | — |
| `Elevm/Execution.lean` (post-split) | — | 4.66 s |
| `Elevm/Sufficiency.lean` | — | 2.08 s |
| `Elevm/Transaction.lean` | — | 1.76 s |
| import-only baseline (`import Elevm.Execution`, empty body) | — | 0.63 s |

Net of the 0.63 s import baseline each module pays, content time is 4.03 s +
1.45 s + 1.13 s = 6.61 s against the pre-split 5.93 s − 0.63 s = 5.30 s. The
whole 1.31 s increase is the new proof module; the split itself is free. Wall
`lake build` went 3.7 s → 8.2 s, but the pre-split figure was a fully cached
no-op run, so the two are not comparable; the comparable figure is the 1,764-job
count.

## 7. Scope check

* Instruction semantics: **untouched.** No definition in `Execution.lean` was
  edited; the file was truncated at a declaration boundary and nothing else.
* Gas charge timing: **unchanged**, and never came close to needing a change.
* Gas constants, fork rules, decode, precompiles, `Footprint`/`liftMach*`:
  **untouched.**
* Error strings: **unchanged.** `"RecursionLimit"` still occurs exactly twice,
  now at `Transaction.lean:36` and `:80`; its deletion is Step 3's.
* No baseline rebased. No `#guard` added, removed, or changed.
* Public API: unchanged. The only visibility question raised by the split
  (`errOf`/`hasTag`) was resolved by restating them privately, not by widening.
* Blanc: **not touched.** Its pin still resolves to `1d67748…`, an ancestor of
  this branch's base.

## 8. Commit ledger

| # | Repo | Branch | Hash | Purpose | Pre-commit gates | Push | Diagnostic |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | elevm | `codex/sufficient` | `c06fc4ec615590088a0d7b015595d336ba6e53b9` | pure text-motion module split | build 1,764, u256, depth, current smoke, hygiene | not yet | no |
| 2 | elevm | `codex/sufficient` | *(this commit)* | measure, combinator layer, pilot, design report | build 1,764, LSP clean, u256, depth, current smoke, hygiene, axiom audit | not yet | no |

Recovery points: the verified starting commit `7bdc100…`; then commit 1, which
is the recovery point for all Step-2 work.

## 9. Autonomous decisions

1. **Cut point at the first consumer, not at the wrappers.** The
   `Test`/header/`setDelegation` block at `:4333–4949` has no driver dependency
   and stayed in `Execution.lean`, which the plan permits and which halves the
   moved text.
2. **`Elevm/Sufficiency.lean` created in the split commit** as a documented
   placeholder, so the final three-module layout and its import edges land once
   rather than being rewired in the infrastructure commit.
3. **`errOf`/`hasTag` restated privately** rather than made public (§1).
4. **Four obligations reduced to two** (§2). This is a refinement of the plan's
   design, not a departure from it: the plan fixed the obligations "per-step
   `.cont`, spawned-child, resume-after-`.done`, resume-after-child", and all
   three spawn-shaped ones are now corollaries of one arithmetic fact plus
   generic `Frame`/`Resume` bridges. It reduces Step 2's per-instruction work
   from three obligations to one.
5. **`Except.bind_eq_ok` as the walking device** in place of the flatten arc's
   `split`/`repeat' split`/`rename_i` idiom (§3).
6. **`calculateMsgCallGas_stipend_lt` stated without a `gas_left` hypothesis**
   (§4), which makes branch 1 of that function need no separate argument.

## 10. Human decisions pending

None. No stop condition was reached: a clean module cut existed, every
instruction in the pilot slice strictly decreases gas, and the constant is 1
uniformly.

## 11. Next handoff — Step 2

Available to build on:

* `Elevm/Sufficiency.lean` with the five-layer combinator stack, the walking
  device, `Resume.run_ok_gasLeft`, `calculateMsgCallGas_stipend_lt`,
  `call_charge_stipend_lt`, `genericCall.step_gasDecreasing`, and
  `XStep.GasDecreasing`;
* the census in §3, which fixes the family boundaries to commit at:
  combinator cases → short walks → warm/cold → bespoke → `Jinst`/`Ninst` →
  `Xinst` (call family, then create family) → driver;
* the two obligations of §2, the monotonicity statement, and the constant 1.

Still to derive in Step 2 (deliberately not started here): the generic
`Frame.enter_run_gas` and `Frame.settle_gasLe` bridges, the precompile bound for
the `Frame.enter = .done` path (`executePrecomp` over ~20 precompiles), and the
create family's `gasCreate` argument.
