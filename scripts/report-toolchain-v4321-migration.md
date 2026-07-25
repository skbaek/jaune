# Toolchain migration re-baseline: Lean/mathlib v4.23.0 → v4.32.1

Date: 2026-07-25 (Asia/Seoul). Plan: `~/plans/migration.md` step 1. Sequencing
constraint: `~/plans/toolchain-migration-notes.md` (allocator/refcount arc must
not start until the profiles are re-taken on the new runtime).

**This report is evidence only. No allocator/refcount work is authorized by it,
and none was performed.**

## Boundary

- ELeVM `f9dda7d` (v4.23.0, pre-migration) → `aa8724a` (v4.32.1), branch
  `codex/migration`.
- Lean `leanprover/lean4:v4.32.1` (stable, published 2026-07-22); mathlib tag
  `v4.32.1`, rev `520045ab14e26149ee970e2e617ca04b09bde5d6`, whose own
  `lean-toolchain` names v4.32.1. Matched pair confirmed. v4.33.0-rc1 exists and
  is a pre-release; it is deliberately not the target.
- Machine, fixtures, and instruments identical across every row below. All
  v4.23.0 "same-machine" columns were measured on this host immediately before
  the migration, and they reproduce the committed `d9de9ab`-era reference values
  to within 1% (`keccak64` 1369 vs 1359 ns/op; four-family aggregate 11.80 vs
  11.73 s), so the reference numbers and this host are interchangeable.

## Codegen canary

`scripts/repro-lean423-uint64-cse.lean`, run with its two documented commands:

| toolchain | `lean -c` | `leanc -c -O2` | result |
|---|---|---|---|
| v4.23.0 | exit 0 | **fails** | `repro.c:83:10: incompatible integer to pointer conversion passing 'uint64_t' … to parameter of type 'lean_object *'` at `lean_inc(x_2)` |
| v4.32.1 | exit 0 | exit 0 | also links and runs; output `9223372036854775817 9223372039002259457` (verified correct); generated C has no `lean_inc` on an unboxed `uint64_t` |

**The v4.23 duplicated-UInt64-literal CSE bug is fixed on v4.32.1.**

`Elevm/Hash.lean`'s `fB64` nevertheless keeps reading round constants from
`B64.rdnc`, per the adopted decision record: the read costs nothing measurable
and is immune to regressions of the emitter path. Only its comment changed.

## Correctness gates (v4.32.1, commit `aa8724a`)

| gate | verdict | wall time |
|---|---|---|
| `lake build` (clean, `.lake/build` removed) | success, **zero warnings** | 27.5 s |
| `scripts/check-hygiene.sh` | OK, 2/2 occurrences allowlisted | <1 s |
| `scripts/check-u256.sh` | 21,593/21,593 PASS | 2.3 s |
| `scripts/check-vectors.sh` | 42/42 files PASS, controls 5/5 | 8 m 17 s |
| `check.sh --patch` | 10/10 PASS | 0.6 s |
| `check.sh --rlp4` | 4/4 PASS | 0.1 s |
| `check.sh --depth` | 67 files match baseline | 13.4 s |
| `check.sh --smoke` | 174 files match baseline (173 PASS / 1 expected FAIL) | 1 m 33 s |
| `check.sh --bls` | 29 files match baseline (29 PASS) | 2 m 31 s |
| Python tooling unit tests | 77/78 — see note | 13 s |
| legacy `check.sh --full` | **2,983 files match baseline (2,978 PASS / 5 expected FAIL)** | see note |

No classification changed anywhere. No baseline was rebased.

**Legacy FULL note — timing drift was a measurement artifact, not a regression.**
FULL was run to completion on this exact commit and its classification matches
the committed baseline exactly. It reported six informational per-file timing
DRIFT lines, the worst nominally 622×. Those are spurious. The run consumed
**1,838 s user CPU against the baseline's 1,794 s summed file time (+2.5%,
i.e. parity)** but took 3 h 01 m wall at 17% CPU: the host was swap-thrashing
(8,435 MB of 9,216 MB swap in use), largely because two Lean LSP worker
processes holding mathlib environments (~900 MB RSS each) were alive for the
whole run. Re-timed in isolation on the same binary, every flagged file is at or
better than baseline:

| file | during FULL | isolated | baseline |
|---|---:|---:|---:|
| `stStaticCall/StaticcallToPrecompileFromTransaction.json` | 1058.1 s | 1.25 s | 1.70 s |
| `stStackTests/stackOverflowM1PUSH.json` | 499.4 s | 0.31 s | 3.01 s |
| `stRandom2/randomStatetest476.json` | 973.5 s | 0.33 s | 4.27 s |

Operational lesson for future long gates on this host: do not run a multi-file
fixture tier concurrently with live Lean LSP servers, and treat per-file wall
times from a contended run as unusable. Whole-run user CPU versus the baseline's
summed file time is the robust cross-check.

**Python note.** `test_u256_explicit_path_with_spaces_is_deterministic` fails.
It reproduces identically on unmigrated `main` at `f9dda7d` (verified in a
pristine worktree), so it is a pre-existing test-fixture defect, not migration
drift: `make_checkout()` builds a synthetic execution-specs tree containing
`src/ethereum/crypto/kzg.py` but not `crypto/hash.py`, while
`gen-u256-vectors.py` imports `ethereum.crypto.hash`. Tracked separately; out of
scope here. Also note this suite must be run with the frozen oracle interpreter
(`~/execution-specs/venv/bin/python`, 3.11.9) — bare system `python3` masks the
real error with a "py-ecc is not installed" message.

**Post-Step 1 tooling follow-up — resolved.** The independently reviewed fix at
`b0f5f0bbad9a6a9935cfab5ee277dd1442f95e87` single-sources the generator
checkout layout, includes the required `src/ethereum/crypto/hash.py` module in
the synthetic oracle fixture, and makes missing declared sources fail during
the up-front layout check. The named recovery branch
`claude/objective-jackson-213da2` was pushed before merge. It was merged into
`codex/migration` by `f3679ea03858645edd0269c61ffb60fb834d41be` without
conflicts. On that merge candidate:

- `/Users/agent/execution-specs/venv/bin/python -m unittest discover -s scripts/tests`:
  **80/80 PASS** in 14.366 s (14.44 s wall);
- `scripts/check-hygiene.sh`: **PASS**, all 2 allowlisted occurrences and no new
  `dbg_trace`/`sorry` under `Elevm/` (0.03 s wall).

This follow-up changes Python tooling and tests only. It does not change Lean
source, the Step 1 binary, fixture classifications, protocol behavior, or
Blanc's immutable ELeVM pin.

## Performance: fixture level (the authoritative basis)

Summed per-file report seconds, `check.sh` instruments unchanged.

### Four ordinary families (best of 3 repetitions)

| family | v4.23 same-machine | `d9de9ab` reference | v4.32.1 | change |
|---|---:|---:|---:|---:|
| vmArithmeticTest | 1.74 | 1.61 | 1.54 | −11.5% |
| stMemoryTest | 4.64 | 4.65 | 4.62 | −0.4% |
| stSStoreTest | 2.98 | 2.97 | 2.93 | −1.7% |
| stCallCodes | 2.44 | 2.50 | 2.42 | −0.8% |
| **aggregate** | **11.80** | **11.73** | **11.51** | **−2.5%** |

### Larger tiers

| tier | v4.23 reference | v4.32.1 | change |
|---|---:|---:|---:|
| SMOKE (174 files) | 91.94 | 91.96 | +0.0% |
| BLS (29 files) | 189.82 | 150.63 | **−20.6%** |

**No fixture-level regression anywhere; BLS is materially faster.**

## Performance: U256 microbenchmark (`run-bench-u256.sh`, ns/op)

v4.32.1 column is the best of 4 runs; the spread column is that instrument's own
run-to-run variance on v4.32.1, which bounds how much any single-run delta means.
The v4.23 column is a single run (the v4.23 binary was not retained), so rows
inside the spread band are not distinguishable from noise.

| row | v4.23 same-machine | v4.32.1 (best of 4) | change | v4.32.1 spread |
|---|---:|---:|---:|---:|
| add | 135 | 156 | +15.6% | 1.3% |
| and | 92 | 107 | +16.3% | 5.6% |
| lt | 80 | 86 | +7.5% | 10.5% |
| mul | 1474 | 1449 | −1.7% | 6.4% |
| div-2^128 | 966 | 961 | −0.5% | 8.8% |
| div-3 | 927 | 962 | +3.8% | 4.9% |
| codec | 367 | 402 | +9.5% | 11.4% |
| sha256 | 1323 | 1252 | −5.4% | 2.5% |
| blake2f-12 | 4810 | 5089 | +5.8% | 1.0% |
| keccak64 | 1369 | 1420 | +3.7% | 3.4% |
| keccak512 | 11436 | 11403 | −0.3% | 4.3% |
| `exp` | — | — | not comparable | — |

`exp` is excluded on the instrument's own documented grounds (100 chained
iterations salted by a clock nonce; swings exceed 10× on identical binaries).

Reading: the three cheapest scalar rows (`add`, `and`, `lt`) and `codec` are
modestly slower per operation, the crypto and division rows are at parity or
better. None of this reaches the fixture level, where the same binary is at
parity-to-faster on every tier — so the microbench deltas are real but not
material to ELeVM's workloads. The instrument salts operands with a clock-derived
nonce by design, so `sink` values legitimately differ between runs and between
toolchains; that is not a correctness signal, and the 21,593-case differential
U256 oracle passes.

## Profile: does the allocator/refcount residual survive?

macOS `sample` main-thread call trees, 1 ms interval, self time from the
"Sort by top of stack" section, idle frames (`__ulock_wait`, `kevent`, …)
excluded to give busy self samples. Two sampleable workloads; short-lived
per-file processes remain unsampleable as in the keccak arc.

| workload | busy samples | v4.23's named trio | all alloc/refcount | of which Lean runtime | of which libsystem_malloc |
|---|---:|---:|---:|---:|---:|
| `buffer.json` (stMemoryTest, deep), 6 runs | 7,231 | 14.0% | **47.0%** | 16.4% | 30.5% |
| `divByZero.json` (vmArithmeticTest), 8 runs | 1,899 | 17.2% | **57.3%** | 17.7% | 39.6% |

"v4.23's named trio" is exactly the three symbols the keccak decision report
measured at ≈51–59% of busy self time: `mi_malloc_small`, `mi_free`,
`lean_dec_ref_cold`.

**Conclusion: the residual survives, but its composition moved.** Total
allocation/refcount self time is 47–57%, sitting inside the v4.23 band of
51–59%, so the allocator/refcount arc remains just as motivated as it was. What
changed is where that time is spent: the three symbols that used to carry the
whole 51–59% now carry only 14–17%, while 30–40% has moved into macOS's
`libsystem_malloc` xzone allocator (`_xzm_free`, `_xzm_xzone_malloc_tiny`,
`_xzm_xzone_malloc`, `_malloc_zone_malloc`). v4.32.1 evidently routes much more
allocation to the system allocator instead of serving it from Lean's bundled
mimalloc small-object path.

Consequence for the future arc, recorded here so it is not re-derived: the
FBIP/ownership slice is unaffected in its rationale, because it reduces
allocation *count* and therefore wins regardless of which allocator serves the
traffic. Any plan step that assumed the cost was specifically mimalloc's, or
that proposed tuning mimalloc, must be re-derived against this new composition.
The top non-allocator self-time entries are unchanged in character
(`List.reverseAux`, `List.lengthTR`, JSON parsing, `roundB64`).

## Instrument repair

`scripts/run-bench-u256.sh` could not run at all on v4.32.1: it recovered the
native dependency objects by scraping the linker command out of
`.lake/build/bin/elevm.trace`, and Lake 5.0 (trace schema `2025-09-10`) now
passes the linker a response file and records the objects structurally under
`inputs.linkObjs`. The parser now reads `inputs.linkObjs`, keeping the old log
scrape as a fallback. Behaviour of the benchmark itself is unchanged.

## Scope check

Prague semantics, the fork surface, every committed baseline, the strict vector
manifest, and `fB64`'s `B64.rdnc` read are all unchanged. `min` on `B256` still
resolves to the pre-existing `B256.min`; only the `min_def` proof obligation is
now discharged explicitly. No `sorry`, `admit`, new axiom, `ofReduce*`, or
raised limit was introduced.
