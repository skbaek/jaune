# Step 3: keccak arc re-profile and byte-layer GO/NO-GO

Date: 2026-07-25 (Asia/Seoul). Plan: `~/plans/keccak-bytelayer.md`
(bundling `~/plans/keccak-proposal.md` + narrow `~/plans/bytelayer-proposal.md`).
Machine, fixtures, and instruments identical across all rows; profiles are
macOS `sample` main-thread call trees; family times are `check.sh --dir`
summed per-file report times.

## Reviewed boundary

- Baseline: `85c7610` (pre-arc HEAD, clean) → step 1a `931155d` → step 1b
  `ea10058` → step 2 `d9de9ab`. Toolchain `leanprover/lean4:v4.23.0`.
- Public entry points `B8L.keccak`, `ByteArray.keccak`, `B256.keccak`
  unchanged in name and type; `Rinst.runCore` body untouched. Blanc exposure
  of the arc: **zero** (confirmed pre-arc: Blanc applies keccak opaquely,
  never unfolds it, no `native_decide`/`ofReduce*` anywhere in `Blanc/`).

## Results

### Committed benchmark instrument (`run-bench-u256.sh`, ns/op)

| row | 1a baseline | step 2 | factor |
|---|---:|---:|---:|
| keccak64 | 53,721 | 1,359 | **39.5×** |
| keccak512 | 226,370 | 11,648 | **19.4×** |
| sha256 (context, unchanged) | 1,325 | 1,349 | — |

keccak64 has reached parity with the Step-6-optimized SHA-256 row.

### Four ordinary families (summed per-file seconds)

| family | 1a baseline | 1b inline | step 2 | factor |
|---|---:|---:|---:|---:|
| vmArithmeticTest | 6.77 | 6.58 | 1.61 | 4.20× |
| stMemoryTest | 16.27 | 16.38 | 4.65 | 3.50× |
| stSStoreTest | 11.79 | 11.93 | 2.97 | 3.97× |
| stCallCodes | 4.33 | 4.34 | 2.50 | 1.73× |
| **aggregate** | **39.16** | **39.23** | **11.73** | **3.34×** |

Versus the pre-EC Step-1 reference (105.81 s): **9.02× cumulative**.
SMOKE summed file time: 491.13 s at EC closure (175 files) → 91.94 s now
(174 files; `loopMul`, a top-2 perf outlier, was retired from the manifest
by the user before this arc — part of that delta is the retired file).

### Correctness gates (every boundary)

u256 oracle 21,593/21,593 PASS at 1a, 1b, and 2 — includes the 80 new
boundary-length keccak vectors driving both `B8L.keccak` and
`ByteArray.keccak` (op `keccak_ba`); four-family classifications clean at
every step; SMOKE 174/174 baseline match at step 2. FULL is deferred to
nightly CI / user per plan.

### Post-step-2 inclusive profile shares (call-tree basis)

Parser validated against the pre-arc baseline profile: it reproduces
keccak = 82.2% inclusive on `buffer.json`, matching the EC-closure
"80–83%" record.

| workload | busy samples | keccak incl | permutation | keccak-internal residual | global list machinery |
|---|---:|---:|---:|---:|---:|
| buffer.json (deep) | 846 | 5.4% | 1.7% | 3.8% | 5.4% |
| vmArithmeticTest | 975 | 7.7% | 2.6% | 5.1% | 8.3% |
| stMemoryTest | 5,957 | 8.3% | 2.8% | 5.5% | 6.7% |
| stSStoreTest | 598 | 9.0% | 3.5% | 5.5% | 6.7% |
| stCallCodes | — | not sampleable: post-step-2 files run 0.03–0.05 s and `sample` cannot attach | | | |

"keccak-internal residual" = inclusive keccak minus the `fB64`/`roundB64`
permutation subtree: absorption, `B8s.toB64` lane assembly, list walking —
the portion a byte-layer reroute could recover. "Global list machinery" =
`lengthTR`/`splitToArray`/`sliceD`/`takeD`/`ekatD`/`reverseAux`/`appendTR`
everywhere, hash-fed or not — a strict upper bound on any B8L-related win.

## GO/NO-GO

Predeclared gate (plan step 3): byte-layer step 4 is GO iff the hash-path
marshalling residual is ≥ 15% inclusive in ≥ 2 of the 4 families.

Measured: 5.1%, 5.5%, 5.5% in the three measurable families (upper bounds
8.3%, 6.7%, 6.7% even crediting all list machinery). No family reaches
15%; the gate cannot pass regardless of the unmeasurable fourth (it would
need two). Even deleting the entire keccak-internal residual would yield at
most ~1.06× on these workloads.

**Decision: NO-GO.** Step 4 (ByteArray/`Array B8` reroute of memory-fed
keccak plus the Blanc `kec_runCore` frame-lemma repair and pin bump) is
cancelled. The keccak512 bench row does show ~55% marshalling at micro
scale on large inputs, but fixture-scale keccak inputs are dominated by
32/64-byte storage-key/address shapes where the absolute residual is small;
the fixture-level basis predeclared by the plan governs.

## Residual and follow-up

The post-step-2 busy profile is dominated by allocator/refcount traffic
(`mi_malloc_small`/`mi_free`/`lean_dec_ref_cold` ≈ 51–59% of busy self time
across families) distributed through the interpreter at large — the same
residual class the EC closure flagged after its own NO-GOs. That is not a
hash or byte-layer problem; it needs its own separately scoped arc
(allocation economy / representation choices), with its own baseline,
profile, and decision gate. No production change beyond step 2 is
warranted by this evidence.

## Deviations from plan

1. Step 1b expectation missed as measured: `@[inline] B64.rol` alone was
   flat (the Step-6 analogy did not transfer; cost sat in closure plumbing,
   ρπ read-after-`set!` copy-on-write, and per-write UInt64 boxing). The
   plan's "proceed regardless if green" clause applied.
2. Step 2 hit a Lean 4.23 codegen bug (duplicated `UInt64` literal CSE'd,
   then `lean_inc` emitted on an unboxed uint64 — invalid C). Worked around
   by reading round constants from `B64.rdnc`; documented in `Hash.lean`.
3. stCallCodes could not be re-profiled post-step-2 (process lifetimes below
   sampler attach latency); the decision is insensitive to it.
4. Step-3 family sampling used aggregated 1 s attach-loop samples across
   three sweep repetitions instead of single ≥10 s samples (post-step-2
   per-file runtimes made the plan's primary method impossible; the plan's
   "slowest members" fallback was extended to whole-family aggregation).

## Handoff

Remaining for closure (step 5, separate session): nightly-CI or user-run
FULL confirmation on `d9de9ab`+, then archive the plan. No Blanc action of
any kind is required by this arc.
