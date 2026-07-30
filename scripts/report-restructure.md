# Restructure arc — closure report

Module split and root-namespace wrap for Jaune and Blanc. Plan:
`~/plans/restructure.md`. Executed 2026-07-31 (Asia/Seoul).

**Verdict: the arc is complete and green, with Step 4's `Solvent.lean` split
deferred at its predeclared feasibility stop.** Both `--full` closure gates
have final verdicts on the exact pushed candidates. Merge into the two `main`
branches remains user-owned and has not been performed.

Candidates proposed for integration:

| Repository | Branch | Commit |
| --- | --- | --- |
| Jaune | `codex/restructure` | `ad7f47ec4bd1fa3cd1c4a315174b7361f7960518` |
| Blanc | `codex/restructure` | `ecad8192c3ca91a82112c4f365501c9767412081` |

Blanc pins Jaune `ad7f47ec…` in `lakefile.lean`, both `lake-manifest.json`
revision fields, and the Lake-managed checkout at `.lake/packages/jaune`.
Both trees are clean and agree with their remote branch tips. Both repositories
use `leanprover/lean4:v4.32.1`.

Arc-wide diff against the pre-arc `main` tips (Jaune `5ffdd9ba`, Blanc
`12c2ccf6`): Jaune 20 files, +3,559/−3,461; Blanc 12 files, +2,765/−2,676.

---

## 1. Final module layout

### Jaune — the `Execution.lean` three-way split

`Jaune/Execution.lean` was 4,696 lines at the `blake2f.md` closure. It is now
three dependency-ordered modules:

| Module | Lines (post-split) | Lines (now, post-wrap) | Contents |
| --- | ---: | ---: | --- |
| `Jaune/Machine.lean` | 2,596 | 2,602 | machine/state records, the `Execution` abbreviation, `Block`, `BlockChain`, `Meta`, `Devm`, `Sevm`, `Evm`, `Benv`, `BenvStat`, `fakeExpAux`, `jumpable`, `getInst`, state/storage mutators, rollback |
| `Jaune/Precompiles.lean` | 814 | 820 | `PrecompResult` … `executePrecomp`, including the whole Blake2 block and its equivalence proofs |
| `Jaune/Execution.lean` | 1,290 | 1,296 | `MsgCallOutput`, the frame machinery, `Evm.step`, `execFueled`, header and executable-range checks, and the RLP tag helpers |

Import chain: `Jaune.Machine` ← `Jaune.Precompiles` ← `Jaune.Execution`, each
importing exactly its predecessor. `Jaune.lean` imports `Basic`, `Types`,
`Fork`, `Hash`, `EC`, `BLSConst`, `BLS`, **`Machine`, `Precompiles`**,
`Execution`, `Sufficiency`, `Transaction` — the two new modules inserted in
dependency order immediately before `Execution`.

`ChainStore` and `FixtureException` remain outside `Jaune.lean`'s import
closure, as required.

**Cut points, as verified and used.** The clean cut began at original
`Execution.lean:2661` (`PrecompResult`) and ended at 3472 (`executePrecomp`);
the first later consumer of that block was at 3738, which is what made the cut
clean.

**The one declaration that moved off its planned side of a boundary.** Private
`rlpTags`, `errOf`, and `hasTag`, together with their focused RLP `#guard`
checks, were planned for the earlier module but had to go to `Execution.lean`,
because the header-boundary checks there require `hasTag`. No definition or
check body changed.

**Guard preservation.** All 108 original `#guard` commands survive and are
rehomed: Machine 41, Precompiles 22, Execution 45. The pre-arc
`Execution.lean` contained exactly 108.

### Blanc — the `Common.lean` split

`Blanc/Common.lean` was 8,608 lines. It no longer exists; it is now three
dependency-ordered modules:

| Module | Lines | Role |
| --- | ---: | --- |
| `Blanc/CommonCore.lean` | 1,716 | compiler-correctness and hop layer through the pre-tactic cut |
| `Blanc/Tactics.lean` | 507 | `TacticM` machinery and the static quotation co-unit |
| `Blanc/CommonProofs.lean` | 6,449 | remaining proof layers, master instruction theorems, local proof macros |

`Blanc.Tactics` imports `Blanc.CommonCore`; `Blanc.CommonProofs` imports
`Blanc.Tactics`; `Blanc/Weth.lean` and `Blanc/Solvent.lean` import
`Blanc.CommonProofs`.

**Regions gathered into `Tactics`.** Original `Common.lean:1716-2022` moved as
the first tactic/lemma co-unit — `of_run_prepend`, `run_prepend_elim`,
`of_run_append`, `run_append_elim`, the Line/Func invariant API, and the
`func_execute*`, `line_inv`, and `func_inv` elaborators. `apply_univ` and the
original `6657-6837` TacticM section moved together. `Stack.Nth` moved
unchanged with `show_nth`, because that macro hygienically binds
`Stack.Nth.head` and `.tail`, making the inductive part of its static co-unit.

**What deliberately stayed downstream.** `show_prefix_zero`,
`show_prefix_one`, `show_prefix_two`, and `show_hinv_stor` remain at their
original relative positions in `CommonProofs`. Their hygienic quotations bind
proof declarations that are necessarily downstream of the main tactic layer;
moving them into `Tactics` produced exactly the surviving cycle the co-unit
rule warns about. Keeping each local macro with the proofs it invokes preserves
a three-module linear graph without editing a proof — which is what the plan's
stop condition requires.

### `Solvent.lean` — split not available, and why

`Blanc/Solvent.lean` (6,328 lines) is **unsplit**. This is the plan's
predeclared feasibility HALT, accepted by the user on 2026-07-31, and the
reason is semantic rather than structural:

- `State.Inv` (`Solvent.lean:3624` at the Step-4 checkpoint) contains
  `some (w.getCode wa).toList = Prog.compile weth`.
- `Msg.InvSolvent` (`:4750`) carries the same compiled-WETH requirement for
  active messages.
- `Benv.InvSolvent` (`:4760`) embeds `State.Inv`, so its lack of a direct
  `weth` token does not make it generic.
- The fork-parametric `stateTransitionWith_preserves_solvent` (`:6194`) and
  `addBlockToChainWith_preserves_solvent` (`:6284`) are interleaved with the
  protected Prague/WETH corollaries at `:6232`, `:6273`, and `:6320`.

**For the later arc that owns this:** the work is to parameterize the
code/program component of `State.Inv` and `Msg.InvSolvent`, and consequently
`Benv.InvSolvent`, then propagate that parameter through the full preservation
ladder. That is a semantic generalization of a protected invariant, which this
pure-refactor arc had no license to perform. No part of it was begun.

---

## 2. Namespace wrap inventory

### Files wrapped

- **Jaune — 15 files:** `Jaune.lean` and all 14 modules under `Jaune/`,
  wrapped `namespace Jaune … end Jaune` inside their imports. This includes
  `ChainStore.lean` and `FixtureException.lean`, which sit outside the root
  import closure.
- **Blanc — 8 files:** `Blanc.lean` and all seven modules under `Blanc/`.

### `open` statements added and retargeted

Five repository-local Jaune consumers gained `open Jaune` after their imports:
`Main.lean`, `scripts/bench-ec.lean`, `scripts/check-ec.lean`,
`scripts/bench-u256.lean`, and `scripts/flatten-pilot.lean`. All four scripts
elaborate clean under `lake env lean` at this candidate.

Blanc's modules open Jaune where they consume it — `Blanc/Semantics.lean`,
`Blanc/Weth.lean`, and `Blanc/Solvent.lean` take a bare `open Jaune`;
`Blanc/Basic.lean` takes `open Jaune Jaune.List Jaune.B256`; and
`CommonCore`/`Tactics`/`CommonProofs` each take
`open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat`.

`open Ninst` was **not** purely upstream: `Jaune.Ninst` supplies constructors
while `Blanc.Ninst` supplies local aliases, so its three consumers deliberately
use `open Jaune.Ninst Ninst`. `DispatchTree` is Blanc-owned.

New file boundaries do not export `open` state, so the Step-4 split repeated
the required `open Jaune.Ninst Ninst` and `open DispatchTree` commands in each
new module. No name or declaration body was rewritten to accommodate this.

### `_root_.` rewrites by target

Blanc's source carried **149** `_root_.` qualifications before the wrap. Each
was classified individually:

| Class | Count | Disposition |
| --- | ---: | --- |
| Jaune-owned | 107 | now `Jaune.` — 88 `State`, 4 `State.setBal`, 14 `destroyAccount`, 1 `addAccessedAddress` |
| Blanc-owned | 24 | now resolve under `Blanc` — 16 `Stack.*`, 6 `SumNof`, 2 `of_benvAfterTransfer{,_no}` |
| core Lean | 18 | `_root_.Eq`, left rooted |

**No remaining `_root_.` qualification names a Jaune declaration.** The current
inventory is 27, all core Lean: `_root_.Eq` ×18, `_root_.Nat` ×3,
`_root_.List` ×3, `_root_.ByteArray.toList.loop` ×3.

That is **27, not the 23 Step 3 recorded**, and the delta is honest rather than
drift: Step 4's split repeated the file-local opens across the new module
boundaries, and four of those repeated opens needed an explicit core root
(`_root_.List`/`_root_.Nat` in `Tactics` and `CommonProofs`). No new root
names a Jaune or Blanc declaration.

### String-built-name re-rooting decision

All 31 originally string-built targets — 4 Func, 4 Stack, 23 `Line.spx` names
— plus the two manually constructed Line names, proved to be **Blanc-owned**.
The decision was therefore to centralize the base: `Strings.toName []` now
starts at `` `Blanc ``, which avoids mixed-prefix call sites. The remaining
string-built Stack/Line targets go through `Blanc.String.apply`/`toExpr`, and
the six fixed Line/Func inversion targets use direct quotations such as
`q(@Line.nil_inv)`.

The apparent `Lean.Name.anonymous` hazard near the old `Common.lean:1715` was
local identifier construction, not a constant, and was left unchanged.

### Compiler-directed qualifications in Jaune

Three, all in `Basic.lean`: recursive calls now use `drop? n xs` and
`take? n xs`, and one ambiguous theorem reference is
`_root_.Nat.mul_le_mul_right`. No declaration was renamed or moved by the wrap.

---

## 3. Step 4: ran, partially

Step 4 **ran**. The `Common.lean` split landed green and pushed at
`ecad8192c3ca91a82112c4f365501c9767412081`. The `Solvent.lean` split was
**deferred** at the predeclared feasibility HALT documented in §1, from that
same checkpoint. The user accepted the deferral on 2026-07-31 and authorized
Step 5 closure from it.

---

## 4. The Blanc audit update, and the negative test

`scripts/AxiomCheck.lean` and `scripts/check.sh` were updated to the four
`Blanc.`-qualified protected theorem names. The expected axiom set and the
audit's matching logic are unchanged.

**The audit still bites.** A temporary copy of `scripts/check.sh` with the
first target replaced by `Blanc.nonexistent_protected_theorem` was run at this
candidate:

```text
FAIL — Blanc.nonexistent_protected_theorem: no axiom report found in Lean output
OK — Blanc.stateTransition_preserves_solvent: [propext, Classical.choice, Quot.sound]
OK — Blanc.chain_preserves_solvent: [propext, Classical.choice, Quot.sound]
OK — Blanc.addBlockToChain_preserves_solvent: [propext, Classical.choice, Quot.sound]
REGRESSION — axiom audit: only 3/4 top theorems have the exact expected axiom set
```

Exit 1. The temporary file was removed.

---

## 5. The four protected theorems

Statements are textually unchanged; only the declaring namespace moved. Each
depends on exactly `[propext, Classical.choice, Quot.sound]`, verified at this
candidate by `blanc/scripts/check.sh --no-build`.

```lean
theorem weth_preserves_solvent (wa : Adr) :
    ∀ sevm pre post,
      Exec 0 sevm pre (.ok post)  →
      (sevm.currentTarget = wa → some sevm.code.toList = Prog.compile weth) →
      Precond wa sevm pre →
      Postcond wa sevm post := by
```

```lean
theorem stateTransition_preserves_solvent (wa : Adr)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state :=
```

```lean
theorem chain_preserves_solvent (wa : Adr) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state := by
```

```lean
theorem addBlockToChain_preserves_solvent (wa : Adr)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChain ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state :=
```

Their qualified names are `Blanc.weth_preserves_solvent`,
`Blanc.stateTransition_preserves_solvent`, `Blanc.chain_preserves_solvent`,
and `Blanc.addBlockToChain_preserves_solvent`.

---

## 6. Gate verdicts on the exact candidates

Every gate below was run on Jaune `ad7f47ec…` and Blanc `ecad8192…` on
2026-07-31, **strictly one gate at a time** — see §9 for why that matters.
Fixture harnesses ran at `--jobs auto` (10 workers), so their timings are
reference-only by the `--jobs` contract.

| Gate | Verdict | Scale / time |
| --- | --- | --- |
| Jaune `lake build` | PASS | 1,768 jobs |
| `scripts/check-hygiene.sh` | PASS | 0 non-allowlisted occurrences |
| `python3 -m unittest discover -s scripts/tests` | PASS | 121 tests |
| `python3 scripts/env_doctor.py` | PASS | — |
| `gen_mainnet_manifest.py --check` | PASS | exact manifest identity |
| `gen-vector-shards.py --check` | PASS | 106/106 exact partition |
| `scripts/check-u256.sh` | PASS | 21,593/21,593 |
| `scripts/check.sh --patch` | PASS | 10/10 |
| `scripts/check.sh --rlp4` | PASS | 4/4 |
| `scripts/check.sh --depth` | PASS | 67/67 vs baseline, 8 s |
| `scripts/check.sh --smoke` | PASS | 174 vs baseline (173 PASS / 1 FAIL), 83 s |
| `scripts/check.sh --bls` | PASS | 29/29 vs target baseline, 77 s |
| `scripts/check-ec.sh` | PASS | 573/573 + differential oracle |
| `scripts/check-vectors.sh` | PASS | 51/51 files, 1,824 cases, 5/5 controls, 89.59 s |
| `check-mainnet.sh --suite smoke` | PASS | 16/16 |
| `check-mainnet.sh --suite transitions` | PASS | 13/13 files, 109 cases, 8.70 s |
| `check-mainnet.sh --suite prague` | PASS | 2,573/2,573, 172.23 s |
| `check-mainnet.sh --suite osaka` | PASS | 2,514/2,514, 142.67 s |
| **`check-mainnet.sh --suite full`** | **PASS** | **5,100/5,100, 308.93 s** |
| **`scripts/check.sh --full`** | **PASS** | **2,983 vs baseline (2,978 PASS / 5 FAIL), 499 s** |
| Blanc `lake build` | PASS | 913 jobs |
| Blanc `scripts/check.sh --no-build` | PASS | 4/4 exact axiom sets |
| Blanc negative audit | PASS (bites) | exit 1 at 3/4 |

Verbatim closure verdicts:

```text
OK — full: 2983 files match baseline (2978 PASS, 5 FAIL; --jobs 10, timings reference-only)
OK — full: 5100/5100 manifest files PASS in 308.93s (--jobs 10, timings reference-only)
```

### Identity evidence

The classification sets that had to match, and did:

- legacy `--full`: `scripts/report-full.txt` is exactly 2,983 lines over 2,983
  unique paths, and its STATUS and path columns are **byte-identical** to
  `scripts/baseline-full.txt` (`diff` of `cut -f1,3` is empty). The five
  baselined FAILs are unchanged: `GeneralStateTests/stEIP1559/intrinsicCancun`,
  `InvalidBlocks/bcEIP1559/intrinsicOrFailCancun`,
  `InvalidBlocks/bcStateTests/EmptyTransaction`,
  `InvalidBlocks/bcStateTests/UserTransactionGasLimitIsTooLowWhenZeroCost`, and
  `InvalidBlocks/bcStateTests/txCost-sec73`.
- current mainnet: prague 2,573, osaka 2,514, full 5,100 report lines — each
  matching its suite size exactly, all PASS.
- U256 21,593/21,593; vectors 1,824 declared cases across 51 files with 5/5
  controls; EC 573/573.
- protected axiom sets exactly `[propext, Classical.choice, Quot.sound]` ×4.

**The jaune binary's SHA-256 changed by construction** and is not a regression:
module boundaries and namespaces are compiler inputs, so a byte-identical
binary was never achievable. It is currently
`e34a82533b123be7ed35c21c6984575cc7e2f785ee736940591f8f1826087953`.
Classification identity, not binary identity, is this arc's invariant, and
classification identity holds everywhere above.

`lake build` job counts: Jaune 1,768 before and after — the split adds modules
but not compilation units at this granularity. Blanc 911 → **913**, exactly the
net two-module increase from one module becoming three.

---

## 7. Commit ledger

| Repository | Branch | Commit | Purpose | Pre-commit gates | Push | Diagnostic |
| --- | --- | --- | --- | --- | --- | :---: |
| Jaune | `codex/restructure` | `35cb4f0d532a964ac611ab62ec723635eaa89cdc` | Three-way `Execution.lean` split | build 1,768; LSP; hygiene; U256; DEPTH | pushed | no |
| Blanc | `codex/restructure` | `f93b0db8a75e75c6506e301a0b9e6f1ca39308ac` | Pin Jaune Step-1 candidate through Lake | build 911; protected audit 4/4 | pushed | no |
| Jaune | `codex/restructure` | `ad7f47ec4bd1fa3cd1c4a315174b7361f7960518` | Root namespace + local consumers | build 1,768; complete LSP; full Step-2 identity set | pushed | no |
| Blanc | `codex/restructure` | `9221c1c5a1cfbb4ea2b8429aa4b9e949609aeafb` | Jaune pin advance | three pins agree; **expected-red** 83-error census | pushed | **yes** |
| Blanc | `codex/restructure` | `11c1e794ae40e2f2400769fdbe8c1ceab8f5d3fc` | Blanc wrap, hazard repair, audit update | clean LSP; build 911; audit 4/4; negative audit; exact statements | pushed | no |
| Blanc | `codex/restructure` | `ecad8192c3ca91a82112c4f365501c9767412081` | `Common.lean` three-module split | clean LSP; build 913; tactic corpus; audit 4/4; four exact `lean_verify` scans | pushed | no |

`9221c1c5` is the one diagnostic commit: it advanced the pin through the normal
Lake flow and is **expected-red** by design, stopping in `Blanc.Basic` with 83
cascading diagnostics on 49 source lines, all downstream of the wrapped Jaune
names. Its green recovery point was `f93b0db8`. No history was rewritten and no
protected branch was merged.

---

## 8. Upstream-candidate inventory

Blanc declarations that state reusable facts about Jaune or core types with no
Blanc semantic concept in them. **Nothing was moved.** This is the worklist a
post-integrity arc will own; `integrity.md` will extend it. "Hits" counts
source-token occurrences including the declaration; "uses" excludes it.

| Candidate | Kind | Hits / uses | Protected cone |
| --- | --- | ---: | :---: |
| `Blanc.of_bind_eq_ok` | lemma | 150 / 149 | yes |
| `Blanc.B256.Nof` | definition | 17 / 16 | yes |
| `Blanc.of_bind_eq_some` | lemma | 16 / 15 | yes |
| `Blanc.B256.toNat_zero` | lemma | 11 / 10 | yes |
| `Blanc.B256.toNat_sub_eq_of_le` | theorem | 8 / 7 | yes |
| `Blanc.B256.toNat_add_eq_of_nof` | lemma | 7 / 6 | yes |
| `Blanc.Adr.toNat_lt_size` | lemma | 7 / 6 | yes |
| `Blanc.B256.zero_ne_one` | lemma | 5 / 4 | yes |
| `Blanc.Adr.max` | definition | 5 / 4 | yes |
| `Blanc.B128.and_eq_and_prod_and` | lemma | 4 / 3 | yes |
| `Blanc.B256.sub_self` | lemma | 4 / 3 | yes |
| `Blanc.B256.and_eq_and_prod_and` | lemma | 3 / 2 | yes |
| `Blanc.B128.zero_and` | lemma | 2 / 1 | yes |
| `Blanc.Nat.add_sub_mod_eq_sub` | lemma | 2 / 1 | yes |
| `Blanc.Adr.toNat_inj` | lemma | 2 / 1 | yes |
| `Blanc.adr_toNat_lt_size_local` | lemma | 2 / 1 | yes |
| `Blanc.of_pure_eq_some` | lemma | 2 / 1 | yes |
| `Blanc.B128.sub_self` | lemma | 2 / 1 | yes |
| `Blanc.B128.zero_eq` | lemma | 2 / 1 | no |
| `Blanc.B128.sub_zero` | lemma | 1 / 0 | no |
| `Blanc.B256.le_add_right` | lemma | 1 / 0 | no |
| `Blanc.Except.IsOk` | inductive/API | 2 / 0 external | no |

`Adr.max` and `B256.Nof` are definitions and `Except.IsOk` is API-bearing, so
moving any of the three would change Jaune's public API — that is a semantic
decision, not a relocation.

The `Blanc/Basic.lean` banner `-- B(2^n) lemmas (transfer to Jaune later) --`
was **carried forward, not silently prefixed**; it sits at `Blanc/Basic.lean:251`
in the wrapped file.

---

## 9. Unexpected findings and decisions

### The Step 5 HALT was a harness defect, not a classification drift

The first Step 5 attempt HALTed reporting that legacy `--full` classified all
2,983 fixtures as changed against the committed baseline. **That was a false
alarm, and no baseline was ever wrong.** Root cause: two `scripts/check.sh
--full` processes ran concurrently and both appended to
`scripts/report-full.txt`.

`check.sh:363` resolves the report path, `:366` truncates it, and `:435`
(parallel) / `:492` (sequential) append. Two writers truncate before either has
written a line, then both append. The surviving artifact had 5,966 lines over
2,983 unique paths, each appearing exactly twice; mapping each line back to its
baseline index splits it into exactly two increasing subsequences of 2,983.
Two comparison scratch directories from `mktemp -d` (`check.sh:550`, one per
invocation) survived, each holding the same doubled report.

The amplifier is `delete base[$2]` in the comparison at `check.sh:590-598`,
which exists so the `END` clause can report baseline files the report never
mentioned. It makes the lookup table single-use: the second occurrence of each
path finds nothing and scores `MISSING -> <status>`. Replaying that awk on the
preserved artifacts reproduces the HALT exactly — 2,978 `MISSING -> PASS` plus
5 `MISSING -> FAIL`. Comparing **either** run's copy alone against the baseline
yields zero changes. Both runs were green; the gate was green; only the report
file was corrupt.

Contention was the second symptom: the two runs summed 8,457.7 s and 8,205.8 s
of fixture time against a 1,145.8 s sequential baseline (~7.2x, where a single
`--jobs auto` run costs ~1.6x), with a `check-mainnet.sh --suite full` running
through most of the same window.

**Two defects are recorded, and neither was fixed here** — this arc has no
license to change the harness:

1. No `check.sh`/`check-mainnet.sh`/`check-vectors.sh` takes any lock on its
   report file, and all three write a fixed default path.
2. The comparison absorbs a duplicated report as a classification verdict.
   GATES.md already draws exactly this line for the wall-clock guard — *"no
   report or baseline can absorb the event"* — and a duplicated report is the
   same category of harness event.

Both are specified in `~/plans/concurrency-guard-proposal.md`, written
2026-07-31, which also records the 2026-07-31 artifact as a ready-made
regression fixture. The re-run reported in §6 ran every gate strictly
sequentially and produced a clean 2,983-line report.

### The plan's `bench-ec.lean:126` expectation was stale

The plan requires confirming that `scripts/bench-ec.lean:126` is "broken
exactly as before, unmasked". **It is not broken, and was not broken at this
arc's branch point.** Jaune commit `88b5746948affe4efd7b45e18ab1c22035eb9a11`
("fix: compare the EC benchmark address numerically, not as a string slice")
had already replaced the `String`/`String.Slice` comparison before the Step-1
checkpoint. At this candidate all four consumer scripts — `bench-ec.lean`,
`check-ec.lean`, `bench-u256.lean`, `flatten-pilot.lean` — elaborate clean
under `lake env lean`. This arc neither repaired nor altered that comparison;
it inherited it already fixed.

### Checkpoint granularity differed from the plan, twice

Step 2's two suggested internal commits were collapsed into one. In this
repository's actual Lake target graph `lake build` includes `Main.lean`, so a
library-only commit before adding `open Jaune` to the consumers would have been
deliberately red — and every committed recovery point must be green. Step 3
likewise consolidated its tactic-machinery and wrap checkpoints, because the
target declarations do not have their final prefix until the wrap exists.
Both changed granularity, not scope or semantics.

### The catalogue's Python test count is stale

`GATES.md` records the harness unit suite as 110 tests; it is **121**. Noticed
and left alone — correcting the catalogue is not this arc's business, and it is
listed below for `integrity.md`.

### Documentation corrected

`blanc/README.md` was stale in three ways and is fixed in this arc's docs
checkpoint: it linked `Blanc/Common.lean` (no longer exists), quoted an
obsolete Jaune pin `b4ce1537…`, and named the four audited theorems as
`weth_inv_solvent`/`stateTransition_inv_solvent`/`chain_inv_solvent`/
`addBlockToChain_inv_solvent`. **The `_inv_` names were already wrong before
this arc** — they are pre-existing staleness from the earlier rename arc, not
wrap fallout — but the same four lines had to change for the `Blanc.` prefix,
and leaving a knowingly-wrong name beside a corrected one would be worse than
fixing both. Recorded here rather than fixed silently.

`jaune/README.md` needed no change: its only usage example is the
`lake exe jaune` CLI, which the wrap does not affect.

Historical reports under `scripts/` were **not** rewritten. They record what
was true when written.

---

## 10. Defects noticed and deliberately not fixed

Handed to `~/plans/integrity.md`:

1. **The two harness defects in §9** — no report-file locking, and a
   duplicated report absorbed as a classification verdict. Owner:
   `~/plans/concurrency-guard-proposal.md`.
2. **The inherited `Jaune/Types.lean:462` unused-simp warning** — the sole
   diagnostic in both builds, present before this arc and untouched.
3. **`GATES.md` records 110 Python unit tests; the suite has 121.**
4. **The 16 zero-name-reference `@[simp]` lemmas in Jaune** — carried from the
   style arc, still unaddressed.
5. **The upstream-candidate inventory in §8** — 22 Blanc declarations that
   belong in Jaune, nothing moved.
6. **The `Solvent.lean` generic/WETH boundary** (§1) — the largest deferred
   item, requiring a semantic generalization of `Msg.InvSolvent` and
   `Benv.InvSolvent`.
7. **`~/plans` carries two uncommitted proposal files** —
   `t8n-proposal.md` and `restore-chain-using-proposal.md` — preserved and
   excluded by every step of this arc, as by the steps before it. They are the
   user's to commit or discard.

---

## 11. Scope check

No semantic change; no opcode behaviour, gas, error text, validation order, or
public API semantics moved. No baseline, exclusion list, manifest, timeout,
guard, or audit was weakened or rebased — the legacy baseline's STATUS and path
columns are byte-identical to the committed file. No unrelated defect was
repaired to make a gate pass. No `sorry`, `admit`, new axiom, `ofReduce*`,
protected-cone `bv_decide`, or raised elaboration limit was introduced. No
local-path Blanc dependency, no history rewrite, no force-push, and no
protected-branch merge.

---

## 12. Recovery state and merge handoff

Latest independently green **semantic** commits, both pushed, both trees clean:

- Jaune `codex/restructure` — `ad7f47ec4bd1fa3cd1c4a315174b7361f7960518`
- Blanc `codex/restructure` — `ecad8192c3ca91a82112c4f365501c9767412081`

Every gate verdict in §6 was measured on exactly those two commits.

**Two documentation-only commits sit on top of them** — this report in Jaune,
and the `blanc/README.md` correction described in §9 — so the branch tips
offered for merge are one commit ahead of each hash above while their semantic
content is identical to it. Neither touches a `.lean` source file, a baseline,
a manifest, or a pin. Per the plan's Step-5 checkpoint 3, **Blanc's pin stays
at the semantic Jaune commit `ad7f47ec…`**: a documentation-only Jaune commit
does not require a bump. The exact final tips are recorded in the arc ledger
`~/plans/state/restructure.json`.

There is no deliberate uncommitted source state in either repository.

**Pending human decision: the merge.** Both branches are proposed for
integration into their respective `main` branches. **Blanc must merge after
Jaune** so that its pin resolves to a commit reachable on Jaune `main`. No
merge, rebase, or squash was performed.

`~/plans/integrity.md` has been refreshed to the post-restructure layout,
names, and tips, and is ready for its Step 1. `~/plans/restructure.md` moves to
`~/plans/archive/` only after the user-approved merge.
