# Rename closure report — ELeVM → Jaune, 2026-07-29

Plan: `~/plans/rename.md`. Focus: identity only. No semantics, no proof, no
classification, and no baseline changed in this arc.

## Verdict

**Green.** Every gate is classification-exact against the `sufficient.md`
closure baselines. The grep audit is empty on every functional surface in
jaune, Blanc, elanc, the active plans, agent memory, and the site. Two
user-owned FULL gates remain outstanding, and both merges are the user's.

## Inventory

Name-variant occurrences in the pre-rename repository (`.lean .sh .py .md
.json .yml`): ELEVM 37 / ELeVM 96 / Elevm 156 / elevm 116 ≈ 405 across 45
tracked files outside `scripts/report-*.md`.

After the arc, occurrences outside the allowlist are **zero** in all of:

| surface | allowlist | audit |
|---|---|---|
| `~/jaune` | `scripts/report-*.md`, `scripts/handoff-sufficient-step2.md`, the oracle preimage | clean |
| `~/blanc` | `scripts/report-*.md` | clean |
| `~/elanc` | `docs/portability-plan.md`, `docs/portability-acceptance-2026-07-24.md` | clean |
| `~/plans` | `archive/`, `rename.md`, one quoted conversation title | clean |
| agent memory | `jaune-rename.md`, `rename-state.md` | clean |
| `~/pitch/jaune-blanc-site` | — | clean |
| `~/pitch/pitch.md` | entire file (historical) | untouched, 16 mentions |

## Commit ledger

| repo | branch | commit | content |
|---|---|---|---|
| jaune | `codex/rename` | `34d758d` | Lean surfaces: `Jaune/`, `Jaune.lean`, imports, lakefile, manifest |
| jaune | `codex/rename` | `b4ce153` | runners, CI, docs, README — **Blanc's pin target** |
| blanc | `codex/rename` | `08f999e` | require/manifest/checkout, 4 imports, README, canary |
| elanc | `codex/rename` | `1464bff` | agent config, setup guide, doctor + tests, versions.json |
| plans | `codex/rename` | `b819242` | active plans; `archive/` untouched |

Agent memory and the site are not version-controlled and were edited in place.

## Gate verdicts

All on the exact pushed candidates with clean trees, re-run at closure.

**jaune @ `b4ce153`**

| gate | result | baseline |
|---|---|---|
| `lake build` | 1,764 jobs | 1,764 |
| `check-hygiene.sh` | 2 allowlisted under `Jaune/` | — |
| `check-u256.sh` | 21,593/21,593 PASS | exact |
| `check.sh --patch` | 10/10 | exact |
| `check.sh --rlp4` | 4/4 | exact |
| `check.sh --depth` | 67/67 | exact |
| `check.sh --smoke` | 174 files, 173 PASS / 1 FAIL | exact |
| `check.sh --bls` | 29/29 | exact |
| `check-vectors.sh` | 44/44 files, controls 5/5 | exact |
| `check-mainnet.sh --suite smoke` | 16/16 | exact |
| `check-mainnet.sh --suite transitions` | 13/13 | exact |
| `check-mainnet.sh --suite prague` | 2,573/2,573 (757.33 s) | exact |
| `check-mainnet.sh --suite osaka` | 2,514/2,514 (581.30 s) | exact |
| `unittest discover -s scripts/tests` | 110 tests OK | — |

**blanc @ `08f999e`**

| gate | result |
|---|---|
| `lake build` | 909 jobs (baseline 909) |
| `scripts/check.sh --no-build` | 4/4 top theorems clean |

Axiom set for each of `weth_inv_solvent`, `stateTransition_inv_solvent`,
`chain_inv_solvent`, `addBlockToChain_inv_solvent`: exactly
`[propext, Classical.choice, Quot.sound]`. All four theorem statements are at
unchanged line numbers with unchanged text, and no Lean diff line in Blanc is
anything other than a name change.

**elanc @ `1464bff`**: `unittest discover -s scripts/tests` 22 tests OK. The
doctor resolves the renamed world — `jaune` directory, origin
`github.com/skbaek/jaune`, Blanc's pin `b4ce153` agreeing across lakefile,
manifest, and managed checkout, and the jaune env doctor located.

**Outstanding, user-owned.** Justified because the runner scripts themselves
changed in this arc:

- `scripts/check.sh --full --no-build` — baseline 2,978 PASS / 5 FAIL over 2,983
- `scripts/check-mainnet.sh --suite full --no-build` — baseline 5,100 files

## Redirect

`git ls-remote https://github.com/skbaek/elevm.git HEAD` resolves and returns
`429f2af`, the pre-rename `main` tip. **`skbaek/elevm` must never be
re-created**: GitHub's redirect for web, fetch/clone, and badges survives only
while the old slug stays unclaimed.

## Pin agreement

Blanc pins `skbaek/jaune @ b4ce1537941a44f35e0ea57afa0d0844a29c9f00` in all
three locations — `lakefile.lean`, `lake-manifest.json`, and the Lake-managed
checkout at `.lake/packages/jaune`, which is an ordinary directory and not a
symlink. The stale `.lake/packages/elevm` tree was removed.

## Deviations from the plan

1. **The oracle preimage is not renamed.** The ASCII string
   `elevm ec oracle step 1` is the keccak preimage of `benchSigHash`, so the
   committed secp256k1 vectors in `scripts/bench-ec.lean` and
   `scripts/check-ec.lean` only reproduce under the original bytes. Four
   occurrences, added to the allowlist.

2. **`scripts/handoff-sufficient-step2.md` is not renamed.** It is explicitly
   marked SUPERSEDED and quotes historical paths verbatim — the same category
   as `scripts/report-*.md`. Allowlist extended by one file.

3. **`baseline-bls.txt` contained two variants.** The plan calls any hit in a
   `baseline-*.txt` a stop condition. Both were in the `#` documentation
   header, no classification line was involved, and no module path appeared.
   Resolved with the user: the two comment lines were rewritten, and every
   classification line was verified byte-identical by diffing the file with
   comments stripped.

4. **A third environment variable.** `ELEVM_REPORT_DIR` → `JAUNE_REPORT_DIR`,
   renamed with its four readers under the same rule as the two the plan named.

5. **Surfaces the plan did not enumerate.** Blanc's
   `.github/workflows/canary.yml` is functional — it `ls-remote`s the
   repository URL and seds the lakefile pin — and `ELEVM_DEV` became
   `JAUNE_DEV`. Four active plans beyond `integrity.md` and `todo.md`
   (`big-step-planning.md`, `small-step-planning.md`, `jumpdest-proposal.md`,
   `lean-eval-proposal.md`) name runnable commands and were updated.

6. **Two elanc docs left as history**, per that repository's own rule at
   `docs/portability-plan.md:117` — *"Do not rewrite historical evidence merely
   for cosmetic path consistency."*

7. **Blanc's README quoted a stale pin.** It read `1facd137…` while the
   lakefile held `0a94e419…`; since the line was being rewritten anyway, it now
   quotes the real revision.

8. **A naming trap worth recording.** A mechanical `ELEVM → JAUNE` sweep
   violates the standard, which forbids `JAUNE` in prose. `JAUNE` is correct
   only in environment-variable names; the project in prose is `Jaune`; and
   lowercase `jaune` names only the executable, package, lake target, or a
   path. Both repositories needed a corrective second pass.

## Findings outside this arc

Neither is caused by the rename; both are tracked separately and are **not**
fixed on `codex/rename`.

1. **`scripts/check-ec.sh` could not link.** Lake's trace schema 2025-09-10
   (in force under `leanprover/lean4:v4.32.1`) records link inputs structurally
   under `trace["inputs"]["linkObjs"]` and passes the linker a response file,
   so parsing `.c.o` paths out of the log message raised `StopIteration`. The
   stale pre-rename `elevm.trace` has the identical shape, which dates the
   breakage to the toolchain migration. Fixed on branch `codex/fix-ec-trace`
   (`d3c4fe4`), where the gate reports **573/573 cases PASS** — the pinned EC
   values were still correct, so nothing had rotted while the gate was dark.
   `scripts/run-bench-u256.sh` already carried the correct parser.
   `scripts/run-bench-ec.sh` links after the fix but still fails earlier, in
   Lean elaboration: `scripts/bench-ec.lean:126` cannot synthesize
   `Decidable (got ≠ benchSigAdr.toSlice)`. That is API drift and is untouched.

2. **The elanc doctor fails on a stale toolchain pin.** `scripts/versions.json`
   records `leanprover/lean4:v4.23.0` while both Lean projects have been on
   `v4.32.1` since the migration. The same stale pin is on elanc `main`.

Minor: `~/jaune/.gitignore` covers `/.lake` and `/scripts/report-*.txt` but not
`__pycache__`, so running the Python unit suite leaves artifacts that a blanket
`git add -A` will stage.

## Handoff

Both tips are pushed and clean and are presented for user merge; **nothing was
merged**. After merge, `~/plans/rename.md` moves to `~/plans/archive/` and
`integrity.md` Step 1 may begin — its re-audit re-derives every declaration,
path, and module name under the new names, so it absorbs this rename at no
marginal cost.
