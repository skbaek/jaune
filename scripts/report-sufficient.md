# The sufficiency arc — closure report

**Plan:** `~/plans/sufficient.md` (all five steps)
**Repositories and candidates proposed for merge:**

- `~/elevm`, branch `codex/sufficient`, tip `c8fb8a3` (semantic tip `0a94e41`;
  commits after it are documentation only)
- `~/blanc`, branch `codex/sufficient`, tip `0a177f1`, pinned to ELeVM
  `0a94e419ac21ba42d04b8961107df50a0f1df2cd` in `lakefile.lean`,
  `lake-manifest.json`, and the real Lake-managed checkout

**Candidate binary:** `.lake/build/bin/elevm`, SHA-256
`885b93a905a3df7492ce1a1044ee9f5c28f0c87f60044bea5e2e7b362575040f`
(built at `c8fb8a3`; code identical to `0a94e41`).
**Date:** 2026-07-29 (Asia/Seoul)

## What the arc delivered

ELeVM's interpreter is total. Fuel is an implementation detail of `execCore`,
proved sufficient once, at the definition site:

```lean
def execCore : Evm → Nat → Fueled (String × Devm) Devm   -- the old `exec`, unchanged
def sufficientLim (gas : Nat) : Nat := gas + 1
theorem execCore_ne_exhausted (evm : Evm) (lim : Nat)
    (h : evm.dyna.gasLeft < lim) : execCore evm lim ≠ Fueled.exhausted
def exec (evm : Evm) : Except (String × Devm) Devm       -- total; fuel internal

def runFrame             (frame : Frame) : Except (String × State × AdrSet × Tra) Devm
def executeCode          (msg : Msg)     : Except (String × State × AdrSet × Tra) Devm
def processMessage       (msg : Msg)     : Except (String × State × AdrSet × Tra) Devm
def processCreateMessage (msg : Msg)     : Except (String × State × AdrSet × Tra) Devm
```

**The additive constant is 1 — the tight bound** — and the `"RecursionLimit"`
observable is deleted. Blanc consumes the retyped API with its adequacy bridge
restated fuel-free:

```lean
lemma exec_iff_exec_eq (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution) :
    Nonempty (Exec pc sevm devm exn) ↔ exec ⟨pc, sevm, devm⟩ = exn
```

No `∃ lim, ∀ lim' > lim, …` statement, `Xlot.Good` threshold, or
`Saturates` record survives anywhere in Blanc.

## Final module layout (ELeVM)

| Module | Lines at tip | Content |
|---|---:|---|
| `Elevm/Execution.lean` | 4,889 | the interpreter through `execCore` and the frame-local functions; guards that pin the fueled driver (including the one showing fuel *can* run out when not seeded from gas) |
| `Elevm/Sufficiency.lean` | 3,055 | the gas-decrease corpus, `execCore_settledGasLe`, `execCore_run_isSome`, the sufficiency theorems, `sufficientLim`, the total `exec`, the four total wrappers, bridge lemmas, guards over the total API |
| `Elevm/Transaction.lean` | 1,959 | `processMessageCall` and everything transaction- and block-level |

The Step-1 split was verified byte-identical to the pre-split file; the root
`Elevm.lean` exports all three.

## Corpus census (Step 2)

| Family | Obligation | Constructors | Bespoke | Combinator-derived |
|---|---|---:|---:|---:|
| `Rinst` | strict `<` on `.ok` | 69 | 26 | 43 |
| `Rinst` | non-increase `≤` | 69 | 26 | 43 |
| `Jinst` | both | 3 | 3 | 0 |
| `Linst` | non-increase `≤` | 4 | 4 | 0 |
| `Xinst` | `GasDecreasing` | 6 | 6 | 0 |
| `Xinst` | `NoRevert` | 6 | 6 | 0 |

Blanc's analogous corpus had needed 48 bespoke lemmas against the same 69
constructors; the combinator layer here closed 43 of them in one dispatch,
leaving 26. The plan's `.ok`-only monotonicity was found too weak
(`executeCode.handleError` turns a `Revert` into a successful frame result
carrying live gas); the real obligation, `Execution.SettledGasLe`, added the
non-increase corpus — a plan gap reported in Step 2, not a deviation.

## Blanc Phase A / Phase B metrics (Step 4)

| | `39ed4a3` (before) | Phase A `05eabae` | Phase B `0a177f1` | Δ arc |
|---|---:|---:|---:|---:|
| `Semantics.lean` lines | 1,220 | 1,227 | 1,018 | −202 |
| `Common.lean` lines | 8,939 | 8,935 | 8,915 | −24 |
| `Solvent.lean` lines | 6,505 | 6,496 | 6,497 | −8 |
| `Fueled` mentions Semantics / Common / Solvent | 104 / 15 / 14 | 100 / 8 / 3 | 20 / 0 / 0 | −113 |
| declarations deleted (all zero-reference at deletion) | — | 0 | 38 | 38 |
| `Blanc.Semantics` / `.Common` / `.Solvent` elaboration | — | 1.5 / 7.5 / 4.6 s | 1.2 / 7.5 / 4.6 s | — |

The 20 residual `Fueled` mentions are the `execCore`-level adequacy induction
(`of_exec'`, `of_exec`, `Xlot.filled_exec`) and the three surviving namespace
lemmas — kept by design, since `execCore` stays public.

## Protected results

The statements of `weth_inv_solvent`, `stateTransition_inv_solvent`,
`chain_inv_solvent`, and `addBlockToChain_inv_solvent` are **byte-identical**
to their `39ed4a3` forms (verified by mechanical extraction and comparison at
the Phase-B tip), and each uses exactly

```
[propext, Classical.choice, Quot.sound]
```

as do the generic `…With/…Using` results, which sit in an untouched region of
`Solvent.lean`. In ELeVM, every declaration the arc added — the *definitions*
included, since `exec` carries a proof — has the same exact axiom set.

## `"RecursionLimit"` and observability

- The string occurs **zero** times in ELeVM source at the candidate; it never
  appeared in an error-tag list, `isExceptionalHalt`, or any
  fixture-exception mapping, so its deletion cannot move a classification.
- The consumers' old `msg.gas + 50` seeding was replaced by
  `sufficientLim gas = gas + 1` **neutrally by proof**: `execCore_run_mono`
  shows more fuel never changes a reached result, so both seedings agree.
- No fixture classification changed at any checkpoint of the arc (Step 3 ran
  the full battery including the authorized Prague and Osaka; Step 5
  verdicts below).

## Gate verdicts on the exact candidates (Step 5)

ELeVM at `c8fb8a3` (code = `0a94e41`), binary
`885b93a9…5040f`; Blanc at `0a177f1`. Idle Lean LSP workers were reaped
before the fixture tiers.

| Gate | Result | Baseline |
|---|---|---|
| elevm `lake build` | PASS, 1,764 jobs (cached; full build 13.6 s at Step 3) | 1,764 |
| `scripts/check-u256.sh` | 21,593 / 21,593 PASS | matches |
| `scripts/check.sh --patch` | 10 / 10 PASS | matches |
| `scripts/check.sh --rlp4` | 4 / 4 PASS | matches |
| `scripts/check.sh --depth` | 67 / 67 (67 PASS, 0 FAIL) | matches |
| `scripts/check-mainnet.sh --suite smoke` | 16 / 16 in 0.49 s | matches |
| `scripts/check-mainnet.sh --suite transitions` | 13 / 13 files in 15.41 s | matches |
| `scripts/check.sh --smoke` | 174 files match baseline (173 PASS, 1 expected FAIL) | matches |
| `scripts/check.sh --bls` | 29 / 29 PASS | matches |
| `scripts/check-vectors.sh` | 44 / 44 files, 782 / 782, controls 5 / 5 | matches |
| `scripts/check-mainnet.sh --suite prague` | 2,573 / 2,573 PASS in 723.30 s | matches (714.88 / 727.29 s at prior checkpoints) |
| `scripts/check-mainnet.sh --suite osaka` | 2,514 / 2,514 PASS in 499.69 s | matches (493.47 / 489.57 s at prior checkpoints) |
| Blanc `lake build` | PASS, 909 jobs (baseline 907 + the two new ELeVM modules) | — |
| Blanc `scripts/check.sh` exact audit | PASS, 4/4 protected theorems, exact axiom sets | matches |

### Four-family sweep (evidence only)

Three runs on the candidate binary; every fixture in all four families passed
(19 / 71 / 28 / 79 files, 0 FAIL).

| Family | Best (s) | Step-3 best (s) | Flatten baseline (s) |
|---|---:|---:|---:|
| `vmArithmeticTest` | 1.55 | 1.54 | 1.54 |
| `stMemoryTest` | 4.59 | 4.60 | 4.60 |
| `stSStoreTest` | 2.93 | 2.89 | 2.85 |
| `stCallCodes` | 2.38 | 2.40 | 2.41 |
| **best run aggregate** | **11.48** | 11.45 | 11.40 |

Run aggregates 11.61 / 11.48 / 11.62 — +0.3 % against Step 3 and +0.7 %
against the flatten baseline, inside run-to-run spread. Evidence only, not a
gate.

### User-owned closure gates — **required before merge, not yet run**

| Gate | Owner | Status |
|---|---|---|
| `scripts/check.sh --full --no-build` (legacy FULL, ~30 min; baseline 2,978 PASS / 5 expected FAIL over 2,983 files) | user | **pending** |
| `scripts/check-mainnet.sh --suite full --no-build` (current FULL, hours; baseline 5,100/5,100 manifest files) | user | **pending** |

Run both on exactly `c8fb8a3` (or `0a94e41` — same code) with the binary hash
above, with no Lean LSP workers alive. Neither may be replaced by a smoke
suite.

## Commit ledger (whole arc)

| Repo | Branch | Hash | Purpose | Push | Diagnostic? |
|---|---|---|---|---|---|
| elevm | `codex/sufficient` | `c06fc4e` | Step 1: pure text-motion module split | yes | no |
| elevm | `codex/sufficient` | `5c5fe7a` | Step 1: measure, combinator layer, pilot, design report | yes | no |
| elevm | `codex/sufficient` | `3ac154f` | Step 2: Rinst strict-decrease corpus | yes | no |
| elevm | `codex/sufficient` | `219ed70` | Step 2: Jinst/Xinst/frame checkpoint (interrupted session) | yes | no — deferred gates confirmed green in Step 2 |
| elevm | `codex/sufficient` | `6215a8f` | Step 2: gas non-increase for the halting branch | yes | no |
| elevm | `codex/sufficient` | `17556bf` | Step 2: settlement, monotonicity, the sufficiency theorem | yes | no |
| elevm | `codex/sufficient` | `911a114` | Step 2 report | yes | no |
| elevm | `codex/sufficient` | `25a0521` | Step 3: rename `exec` → `execCore` | yes | no |
| elevm | `codex/sufficient` | `0a94e41` | Step 3: retype; `"RecursionLimit"` deleted — **Blanc's pin** | yes | no |
| elevm | `codex/sufficient` | `4a7648d` | Step 3 report | yes | no |
| elevm | `codex/sufficient` | `c8fb8a3` | Step 4 report | yes | no |
| blanc | `codex/sufficient` | `7903b64` | Step 4: pin bump | yes | **yes — flagged, Semantics red** |
| blanc | `codex/sufficient` | `05eabae` | Step 4 Phase A: repair to green | yes | no |
| blanc | `codex/sufficient` | `0a177f1` | Step 4 Phase B: fuel-threshold machinery deleted | yes | no |

Plus this report's own documentation commit(s). Trees are clean and both
branches are in sync with origin.

## Deviations from the plan

1. **Step 2 (reported then):** the plan's `.ok`-only driver monotonicity was
   insufficient; `Execution.SettledGasLe` and a non-increase corpus (~900
   lines) were required. A plan gap, not a semantic change.
2. **Step 3 (reported then):** the readiness audit's claim that
   `genericCreate.step` restores `createGas` on the *collision* exit is
   inaccurate (only the depth-0 / insufficient-balance / max-nonce exit
   refunds). No proof depended on it; no code changed.
3. **Step 4 (reported then):** Phase A already moved the wrapper bridge from
   `Xlot.Good lim` to `Xlot.Filled`, because under total wrappers no
   non-arbitrary threshold remains to state; `Xlot.Good` itself was deleted in
   Phase B with zero-reference evidence.
4. **`README.md` needed no update** — it does not describe the interpreter's
   signature or fuel.

## What remains open (by design)

- `Fueled` and `execCore` survive: `execCore` is public, structurally
  recursive, and behaviorally identical; it is the definition Blanc's
  adequacy induction reasons over. Only the *default* API is fuel-free.
- `State.Inv.of_exec_transfer` and `executeCode_inv_noDel` are caller-less
  API surface, now stated fuel-free; noted so a later cleanup does not
  rediscover them.
- Structured-error reform, footprint-factoring completion, and the
  representation / performance arcs remain separately scoped, as does the
  allocator arc gated behind the migration plan.

## Merge handoff

Nothing has been merged; neither branch may be merged into `main` without
explicit user approval. Proposed for merge after both user-owned FULL
verdicts are green:

- elevm `codex/sufficient` at its pushed tip (semantic code = `0a94e41`;
  every commit after it, this report included, is documentation only)
- blanc `codex/sufficient` @ `0a177f1` (pin `0a94e41` — the semantic commit;
  policy question of whether to track the docs tip is left to the user, and
  the pin as it stands is correct and immutable)

After the merge, move `~/plans/sufficient.md` to `~/plans/archive/`.
