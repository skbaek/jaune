# blake2f arc closure report — unbox the BLAKE2b working vector

- **Plan:** `~/plans/blake2f.md` (two steps, executed in auto mode 2026-07-31)
- **Step reports:** `~/plans/reports/blake2f-step-1.md`,
  `~/plans/reports/blake2f-step-2.md`
- **Arc ledger:** `~/plans/state/blake2f.json`
- **Toolchain:** `leanprover/lean4:v4.32.1`
- **Focus:** Jaune only. Blanc was not edited, not repinned, and not gated on.

## Candidate

- **Jaune source candidate:** `d7dc10f14609c03e4373f37a7e692e171f21a967` on
  `codex/blake2f` — the last commit that changes Lean source.
- **Jaune branch tip proposed for merge:** the tip of `codex/blake2f`, which adds
  the harness change, the refreshed legacy baseline, and this report on top of
  the source candidate. Named exactly under *Merge handoff* below.
- **Blanc:** `main` at `12c2ccf68fb2d36a351556c8d67f652008e9be54`, untouched,
  still pinning Jaune `c9808a575bb97491f64b178630e5616c7cee5350`.

The branch is published exactly at its local tip. No history was rewritten,
nothing was force-pushed, and no merge into `main` was performed.

## What the arc did

`Blake2.g` ended in four `Array.set!` calls. `Array α` stores *boxed* elements
and `lean_box_uint64` is unconditionally a heap allocation, so a BLAKE2b round —
eight `Blake2.g` calls — cost **32 allocations and 32 frees**, in a loop that
does no other memory work. `Jaune/Hash.lean` had already solved exactly this for
keccak, one file away: `State1600` holds the 25 lanes as unboxed scalar fields
"so a round never touches the heap". This arc applies that technique to Blake2.

All Lean changes are in `Jaune/Execution.lean`, inside the existing Blake2 block.
No new module. Added:

| declaration | what it is |
|---|---|
| `Blake2.Vec` | a non-polymorphic structure with sixteen `UInt64` fields |
| `Blake2.Vec.toArray` | the bridge to `Array UInt64`; used once per compression and by the theorems, never inside a round |
| `Blake2.roundVec` | the flat round — a transliteration of `Blake2.round`: same eight mixes, same order, same literal word indices, each `Blake2.g` body inlined as scalar `let` bindings |
| `Blake2.roundsVec` | the flat rounds loop, mirroring `Blake2.rounds` including its `k - (n + 1)` round index and `blake2Sigma[r % blake2Sigma.size]!` lookup |
| `Blake2.roundVec_toArray` | round-level equivalence |
| `Blake2.roundsVec_toArray` | loop-level equivalence, by induction on the round count |

`bCompress` now builds the structure directly and calls the flat loop, bridging
back to an array once for its unchanged tail. `executeBlake2F` is textually
unchanged.

`Blake2.g`, `Blake2.round`, and `Blake2.rounds` are **retained as the reference**,
matching `Jaune/Hash.lean`'s convention — and here the convention is stronger: a
comment above the block states that they stay because the equivalence theorems
mention them, so they are a specification with a proof attached rather than dead
code needing an allowlist entry.

The vestigial seventeenth working word is gone. Design decision 6 was verified
before it was relied on: `bCompress` built a seventeen-element list, but
`Blake2.round` touches indices 0–15 and the tail reads `v[i]!`/`v[i+8]!` for
`i < 8`. Index 16 was written and never read. Dropping a *trailing* element leaves
indices 0–15 unchanged for every input.

**Emitted-code evidence.** `.lake/build/ir/Jaune/Execution.c` for
`lp_jaune_Blake2_roundVec` declares all sixteen words as `uint64_t` locals, reads
them with `lean_ctor_get_uint64`, tests `lean_is_exclusive`, and contains exactly
one `lean_alloc_ctor(0, 0, 128)` — on the reuse-fail path only. In the steady-state
loop the state object is exclusive and reused in place, so a round allocates
nothing.

## The two theorems and their axiom sets

```lean
theorem Blake2.roundVec_toArray  (m : Array UInt64) (s : Array Nat) (w : Blake2.Vec) :
    (Blake2.roundVec m s w).toArray = Blake2.round m s w.toArray

theorem Blake2.roundsVec_toArray (m : Array UInt64) (k n : Nat) (w : Blake2.Vec) :
    (Blake2.roundsVec m k n w).toArray = Blake2.rounds m k n w.toArray
```

The round-level proof is `cases w` and one `simp only`; the loop-level proof is
`induction n generalizing w`, `rfl` in the zero case and one `simp only` using
the induction hypothesis and the round-level theorem in the successor case.

**Axiom sets, recorded with `#print axioms` against the built file:**

| theorem | axioms |
|---|---|
| `Blake2.roundVec_toArray` | `propext`, `Quot.sound` |
| `Blake2.roundsVec_toArray` | `propext`, `Quot.sound` |

Both are exactly `[propext, Quot.sound]`, satisfying the plan's subset
requirement. Getting there took one deliberate adjustment, which is a genuine
finding and is worth carrying forward:

> The obvious `cases v; simp [flat round, bridge, Blake2.round, Blake2.g]` closes
> the round-level goal in about a second — but its axiom set is
> `[propext, Classical.choice, Quot.sound]`. `Classical.choice` enters through
> exactly two Mathlib lemmas, `Nat.ofNat_pos` and `Nat.one_lt_ofNat`, which the
> default simp set prefers for discharging the `0 < 16` and `1 < 16` side
> conditions of `getElem!_pos`. Squeezing with `simp?` and dropping those two from
> the resulting `simp only` set lets the core `Nat.reduceLT` simproc decide the
> same literal comparisons, removing `Classical.choice` at no cost. A source
> comment records this so a future editor does not "simplify" the explicit set
> back into a bare `simp` and silently widen the trusted base.

For context: `[propext, Classical.choice, Quot.sound]` is the set Blanc's own
protected-theorem audit requires *exactly*, so the wider set would not have been
anomalous by repository convention — the plan asked for the tighter one and the
tighter one was free.

**Negative control, performed and not committed.** Changing `b2R3` to `b2R2` in
the second rotation of the eighth mix of `Blake2.roundVec` makes
`Blake2.roundVec_toArray` fail with `unsolved goals`, leaving the full
sixteen-word array equation open. Reverted immediately; it appears in no commit.

No `sorry`, `admit`, new axiom, `native_decide`, `decide`, `ofReduce*`, or raised
elaboration limit was used anywhere in the arc. `rfl` and
`with_unfolding_all rfl` were tried and rejected — both exhaust the recursion
depth, and raising the limit is prohibited.

## Measurements, and the decision gate applied

Both instruments, sequential, on an idle host with no Lean LSP worker alive.
`planning.md` §5 requires comparable before/after measurements from the same
committed instrument on the same machine; both satisfy that.

### Instrument 1 — fixture level (authoritative)

Identical command before and after, same binary path, same host:

```
.lake/build/bin/jaune \
  <fixtures>/GeneralStateTests/stTimeConsuming/CALLBlake2f_MaxRounds.json \
  --network Prague
```

| | wall (s) | user (s) | sys (s) | ns/round | rc |
|---|---:|---:|---:|---:|---:|
| before (`d4a62ba5`, unmodified tree) | **753.24** | 747.62 | 3.57 | 175.4 | 0 |
| after (`d7dc10f1`) | **77.45** | 75.82 | 0.39 | 18.0 | 0 |

Round count 4,294,967,295. **Speedup 9.72×.** Runner stdout was captured both
times and diffed: byte-identical, twelve lines each.

This beats the plan's projected ~6.5×. The prototype the projection came from was
known to run ~1.28× slower per round than the real loop for an unidentified
reason, and the plan flagged the vestigial seventeenth element as a candidate;
removing it here may account for part of the gap. Note that the measured
18.0 ns/round is *below* the prototype's best fused-accumulator figure of
28.9 ns/round — which retrospectively strengthens fixed design decision 1. The
round-shape-preserving form, chosen because it keeps the one-second proof, is not
leaving meaningful performance on the table on this host.

### Instrument 2 — committed instrument (corroborating)

`scripts/run-bench-u256.sh`, the `blake2f-12` row, five runs each:

| | runs (ns/op) | median |
|---|---|---:|
| before | 5009, 5214, 5065, 5008, 5337 | **5065** |
| after | 3119, 3238, 3166, 3084, 3085 | **3119** |

**1.62×.** As the plan predicted, this row is only 12 rounds and is
setup-dominated — per iteration it pays list marshalling, `bCompress` entry and
exit, and the driver's fold — so the round-loop saving is diluted. It is a
corroborating signal, not the headline, and its magnitude is consistent with a
~10× round loop behind a fixed per-call cost.

### The predeclared decision gate

> **GO** if the measured fixture speedup is ≥ 2.0×; **HALT** if below.

Measured **9.72×**. **The gate is GO**, and the arc proceeded to closure. Had it
come in below 2.0×, the recorded response was to report and stop — not to reach
for the fused-accumulator form to make the number look better.

## The baseline refresh, and the harness mode that made it safe

### Why a new mode

`check.sh` compares the STATUS column only; TIME is "informational reference data
… never gate input". But TIME has a *functional* role: parallel dispatch is
longest-first, **seeded from the committed baseline's TIME column**. After this
arc that seed was actively wrong — Blake2 would still be dispatched first as a
711 s job while the real longest fixture waited behind it. And nothing prompts a
refresh on its own: DRIFT fires only when a file gets *slower* than 2x its
reference, so a ninefold speedup produces no signal at all.

The obstacle was that **`--rebase` performed no comparison**: it was
`cp "$REPORT" "$BASELINE"` then `exit 0`, placed above the comparison block.
Refreshing through it would have rested this arc's central safety claim on an
agent remembering to run a diff by hand, with the gate printing `OK` regardless.

One flag was serving two intentions that deserve different answers. They are now
two flags, both sequential-only and both refused for the `--patch`/`--rlp4`
target gates and the hand-maintained `--bls` baseline:

| flag | means | on a classification change |
|---|---|---|
| `--rebase` | "the classifications legitimately changed; accept them" | absorbs it, after printing `REBASE — <file>: <old> -> <new>` for each |
| `--refresh-times` | "the classifications are identical, the code got faster; refresh the reference times" | **writes nothing**, prints the differing files, exits nonzero |

`--rebase` keeps its semantics exactly; it is now self-documenting rather than
forbidden-by-convention. `--refresh-times` additionally re-derives the STATUS and
path columns from the bytes it is about to write and `cmp`s them against the
committed ones, so "timing-only" is enforced by the harness rather than asserted
by a commit message. Both are catalogued in `scripts/GATES.md`.

**Verified with a negative control, not by inspection**, on the `--depth` tier:

- positive — `OK — depth: 67 files STATUS-identical to baseline; TIME column
  refreshed`, with `cmp` of `cut -f1,3` before and after reporting identical and
  the TIME column moved on 66 of 67 lines;
- negative — one baseline line flipped `PASS` to `FAIL` in a scratch edit; the
  mode printed the differing file, **wrote nothing** (`shasum` unchanged across
  the run), and exited 1.

Both scratch edits were restored from git and appear in no commit. The harness
change was committed **alone and before any long run**, so it is reviewable
independently of the baseline it later wrote.

### The refresh

```
scripts/check.sh --full --refresh-times --no-build
OK — full: 2983 files STATUS-identical to baseline; TIME column refreshed
```

Sequential, `--no-build` after a successful `lake build jaune` at the same
commit, no Lean LSP worker alive, swap 100 MB of 1 GB used, one-minute load
average allowed to fall to 1.41 before launch.

| fixture | old reference | new reference | ratio |
|---|---:|---:|---:|
| `stTimeConsuming/CALLBlake2f_MaxRounds.json` | 711.44 s | **75.90 s** | 9.37x |
| `VMTests/vmPerformance/loopMul.json` | 390.17 s | **372.50 s** | 1.05x |
| sum of the TIME column | 3,337.9 s | **1,145.8 s** | 2.91x |

`loopMul` is now the corpus's longest fixture, 4.5x ahead of the second-longest
(`static_Call50000_sha256`, 83.39 s). No DRIFT line appeared. The refreshed
baseline was committed alone, as a timing-only change.

### What the refresh bought, measured

One `scripts/check.sh --full --jobs auto --no-build` run was taken after the
refresh, so the gate's new cost is measured rather than projected:

```
OK — full: 2983 files match baseline (2978 PASS, 5 FAIL; --jobs 10, timings reference-only)
WALL = 462 s
```

| | before the arc | after |
|---|---:|---:|
| sequential `--full` (sum of per-file time) | 3,337.9 s | **1,145.8 s** |
| parallel `--full` at `--jobs auto` | ~900 s | **462 s** |

The 2,978 PASS / 5 FAIL split is the corpus's five known legacy FAILs, unmoved.
`GATES.md` and `check.sh`'s header comment were corrected accordingly: they
stated that `CALLBlake2f_MaxRounds` was ~41% of the serial total and that the
parallel makespan was 99.6% that one fixture, which this arc falsified. The
shape of the claim survives — `--full` is still latency-bound by one indivisible
fixture that parallelism cannot touch — but the fixture is now `loopMul` at
372.5 s and 33% of the serial total.

## Verification — every gate, on the exact candidate

Cheap and medium tiers were run in Step 1 on `d7dc10f1` and the cheap battery was
re-run in Step 2 on the final commit. Both `--suite full` closure gates were run
in Step 2; neither was replaced by its smoke tier.

| gate | verdict |
|---|---|
| `lake build` | `Build completed successfully (1764 jobs).` |
| LSP diagnostics on `Jaune/Execution.lean` | empty at every severity |
| `scripts/check-hygiene.sh` | `OK — hygiene: all 0 occurrence(s) of {dbg_trace, sorry} under Jaune/ are allowlisted; no new ones` |
| `scripts/check-u256.sh` | `OK — u256: 21593/21593 PASS` |
| `scripts/check.sh --patch` | `OK — patch: 10/10 PASS` |
| `scripts/check.sh --rlp4` | `OK — rlp4: 4/4 PASS` |
| `scripts/check.sh --depth` | `OK — depth: 67 files match baseline (67 PASS, 0 FAIL)` |
| `python3 -m unittest discover -s scripts/tests` | `Ran 121 tests` / `OK` |
| `scripts/check-vectors.sh --jobs auto` | `OK — vectors: 51/51 files PASS; controls 5/5 PASS in 90.83s` |
| `scripts/check.sh --smoke` | `OK — smoke: 174 files match baseline (173 PASS, 1 FAIL)` |
| `scripts/check.sh --bls` | `OK — bls: 29 files match baseline (29 PASS, 0 FAIL)` |
| `scripts/check-ec.sh` | `OK — ec: 573/573 cases PASS` |
| `scripts/check-mainnet.sh --suite smoke` | `OK — smoke: 16/16 manifest files PASS` |
| `scripts/check-mainnet.sh --suite transitions` | `OK — transitions: 13/13 manifest files PASS in 8.33s` |
| **`scripts/check-mainnet.sh --suite full --jobs auto`** | `OK — full: 5100/5100 manifest files PASS in 248.89s` |
| **`scripts/check.sh --full --refresh-times` (sequential)** | `OK — full: 2983 files STATUS-identical to baseline; TIME column refreshed` |
| `scripts/check.sh --full --jobs auto` (post-refresh, makespan evidence) | `OK — full: 2983 files match baseline (2978 PASS, 5 FAIL)` in 462 s |

`scripts/vectors/blake2F.json` is the **primary correctness gate** for this
change — it is the only differential BLAKE2F oracle in the repository — and it
passed as one of `check-vectors.sh`'s five controls. The U256 differential oracle
does **not** cover BLAKE2F (its hash ops are `keccak` and `keccak_ba` only) and is
not cited as BLAKE2F evidence anywhere in this arc.

All ten `eip152_blake2` current-mainnet manifest files PASS, for both
`for_prague` and `for_osaka`.

**Identity.** No classification moved in any tier, in either direction. The five
known legacy FAILs are still FAIL and the `--smoke` tier's one known FAIL is
still FAIL. The refreshed baseline's STATUS and path columns are byte-identical
to the committed ones, checked both by the mode and independently by `cmp`.

## Blanc: neither edited nor repinned, and why that is correct

Blanc's exposure to this change is **zero, verified rather than assumed**. A grep
of `~/blanc/Blanc` for `executePrecomp`, `precompileRun`, `executeBlake2F`,
`bCompress`, and `Blake2` finds no reference to any Blake2 internal.
`executePrecomp` is unfolded in exactly three places, and each immediately treats
`precompileRun` as an opaque value:

- `Blanc/Common.lean:7136` — `unfold executePrecomp at h_ex`, then
  `generalize h_res : precompileRun evm adr = res`;
- `Blanc/Common.lean:7977` — `unfold executePrecomp …`, then
  `cases precompileRun evm a <;> rfl`;
- `Blanc/Solvent.lean:1788` — `unfold executePrecomp applyPrecompResult at h`,
  then `split at h`, never descending into the precompile body.

No Blanc proof can therefore see the difference between the array round and the
flat round, and `executeBlake2F`'s name, type, error strings
(`"InvalidParameter"`, `"bCompress failed"`), gas charge, and output bytes are
unchanged in any case. Repinning Blanc would have added a cross-repository
integration risk to an arc that has no cross-repository content, and would have
pre-empted `restructure.md` Step 3, which owns the pin bump. Blanc's pin still
resolves to the same immutable commit,
`c9808a575bb97491f64b178630e5616c7cee5350`.

## Defects noticed and deliberately left for `integrity.md`

Per the plan, defects found in passing are recorded, not fixed.

1. **`baseline-<tier>.txt` carries no provenance header.** The `--bls` baseline
   states the machine and date its times were recorded on; the tier baselines do
   not, even though `check.sh`'s own header says the TIME column is "recorded on
   the machine that ran `--rebase` (stated in each baseline's header)". Related
   observation: `GATES.md` gave sequential legacy `--full` as ~31.1 min while the
   *old* baseline's TIME column summed to 3,337.9 s (~55.6 min). Those cannot
   both describe the same machine, and with no header there is no way to tell
   which is which. Not resolvable inside this arc — it would need a sequential
   run of a tree that no longer exists on this branch.
2. **`check.sh` leaks `CMP_DIR`.** The comparison path creates it with
   `mktemp -d` and never removes it; the parallel path's `trap … EXIT` covers only
   `WORK`. One small temporary directory per comparison run. Pre-existing.
3. **A pre-existing `linter.unusedSimpArgs` warning** at `Jaune/Types.lean:458`
   (`toUInt32_toUInt64` unused in a `simp` list). Predates this branch, different
   file, left alone.

Nothing else was encountered in the Blake2 block or its surroundings that
warranted recording.

## Closure checklist

| item | status |
|---|---|
| Both equivalence theorems proved; axiom sets recorded and within `[propext, Quot.sound]`; negative control performed and not committed | done |
| Reference definitions retained, with a doc comment stating the theorem is why they stay | done |
| `executeBlake2F` and `bCompress` unchanged in name, type, error strings, gas charge, output bytes | done |
| No new module; all changes inside the existing Blake2 block of `Jaune/Execution.lean` | done |
| Blanc neither edited nor repinned; pin still resolves to the same immutable commit | done |
| Every gate in `GATES.md`'s cheap, medium, and long tiers green on the exact candidate, with both `--suite full` gates run | done |
| `check.sh --refresh-times` added and documented in `GATES.md`; negative control performed and not committed; `--rebase` prints its delta; harness change committed separately from the baseline it later writes | done |
| Legacy baseline refreshed through `--refresh-times`, verdict line quoted, refresh committed alone as timing-only | done |
| Fixture speedup measured on both instruments, sequential, idle host, LSP down; decision gate applied in writing | done |
| `scripts/report-blake2f.md` committed | this file |
| `restructure.md` and `integrity.md` refreshed, plan edits committed in `~/plans` | done |
| Exact merge candidate named; **user approval obtained before any merge into `main`** | **named below; approval pending** |
| After the approved merge, `~/plans/blake2f.md` moves to `~/plans/archive/` | pending the merge |

## Merge handoff

**Proposed for integration into Jaune `main`: the tip of `codex/blake2f`.** It is
pushed, its tree is clean, and every gate above is green on it. The exact
40-character hash is recorded in `~/plans/state/blake2f.json` and in
`~/plans/reports/blake2f-step-2.md`. Blanc needs no companion merge and no
repin.

**No merge has been performed or attempted, and the arc's launch was not treated
as approval for one.** This is the arc's single user-owned action.
