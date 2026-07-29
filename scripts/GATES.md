# Verification gates

Authoritative catalogue of the Jaune/Blanc verification gates: what exists, what
each one takes, what it proves, and which to reach for when. This file is the
single source of truth for gate usage — plans, agent instructions, and reports
should link here rather than restate it.

Audience is anyone driving these gates, human or agent, regardless of tool.

All commands are run from `~/jaune` unless stated otherwise.

## If you are an agent, start here

**For routine checks — "did my last edit break anything?" — pass `--jobs auto`.**
The two fixture harnesses (`check.sh`, `check-mainnet.sh`) run sequentially by
default and take roughly 2–4x longer that way. That default is deliberate and
correct for the scripts (see [The `--jobs` contract](#the---jobs-contract)), but
it is the wrong default for development work. Saving that time is the entire
reason parallel mode exists; use it.

Choose the gate by what you changed, cheapest falsifier first:

| you changed | run this first | then, before pushing |
|---|---|---|
| anything at all | `scripts/check-hygiene.sh` + `lake build` | — |
| U256/word/hash primitives | `scripts/check-u256.sh` | `scripts/check.sh --smoke --no-build --jobs auto` |
| EC / precompiles | `scripts/check-ec.sh`, `scripts/check.sh --bls --no-build --jobs auto` | `scripts/check-mainnet.sh --suite prague --no-build --jobs auto` |
| interpreter / gas / state | `scripts/check.sh --depth --no-build --jobs auto` | `scripts/check.sh --smoke --no-build --jobs auto` |
| fork / block validity | `scripts/check-mainnet.sh --suite transitions --no-build --jobs auto` | `scripts/check-mainnet.sh --suite osaka --no-build --jobs auto` |
| harness / generators | `python3 -m unittest discover -s scripts/tests` | `python3 scripts/env_doctor.py` |
| anything Blanc consumes | `cd ~/blanc && lake build && scripts/check.sh --no-build` | — |

**Use sequential (omit `--jobs`) when the timings themselves matter:** recording
a baseline with `--rebase`, investigating a performance regression, or producing
timing evidence for a report. A contended run's TIME column reflects scheduling,
not the fixture. Parallel mode enforces this — it refuses `--rebase` outright.

**Long gates are evidence obligations, not optional.** Gates expected to exceed
ten minutes are normally deferred to the user unless the task explicitly
authorizes them, but a deferred long gate needs a named owner and must pass
before merge. It never substitutes for the cheap gates above.

## The `--jobs` contract

`check.sh` and `check-mainnet.sh` accept `--jobs <n>|auto`; `auto` resolves to
the machine's logical-core count. **Sequential (`--jobs 1`) is the default and
its behaviour is untouched** — same guard, same ordering, same authoritative
timings. Sequential is cleaner in every respect except speed, so it stays the
script-level default; parallel is an explicit per-invocation choice.

What parallel mode changes:

- **Timings become reference-only.** `--rebase` is refused and the DRIFT
  comparison is skipped entirely rather than computed and suppressed. The gate
  itself is unaffected — it only ever compared STATUS.
- **The per-file guard rises 1800s → 2000s.** This is the sole thing a parallel
  run still decides for real; it remains a hang detector, never a performance
  budget. An explicit `JAUNE_TIMEOUT` still wins.
- **Dispatch becomes longest-first**, seeded from the committed baseline's TIME
  column. No fixture names are hardcoded; if the slowest fixture changes, the
  next sequential `--rebase` updates the order automatically.
- **`check-mainnet.sh` runs the whole selection instead of stopping at the first
  failure**, and reports every failure. It also writes
  `scripts/report-mainnet-<suite>.txt`, which the sequential path does not.

What it does not change: the report is reassembled in **sequential order**, not
completion order, so a report from either mode diffs cleanly against the same
baseline.

Only these two harnesses take `--jobs`. `check-u256.sh`, `check-vectors.sh`,
`check-ec.sh`, and `check-hygiene.sh` do not.

### What the job count is worth

It depends on which bound the suite is under, and the two corpora differ:

- **Legacy `--full` is latency-bound.** One indivisible fixture
  (`CALLBlake2f_MaxRounds`, a single Prague case) is ~41% of the serial total,
  and the parallel makespan is 99.6% that one fixture. It is therefore *flat* in
  the job count — 886s at 4 jobs, 899s at 8. Only making that fixture faster
  moves this number.
- **Current-mainnet suites are throughput-bound.** ~90% of their fixtures run
  under 0.15s, so process spawn dominates and the suite scales with cores:
  435s at 4 jobs, 328s at 8, 299s at 10.

Efficiency cores run this workload ~5x slower than performance cores, but you
cannot steer work away from them: there is no affinity API, and the scheduler
migrates rather than pins (at 8 concurrent, every worker inflates a uniform
~1.64x rather than some bimodally). Capping the pool at the P-core count only
idles cores, which is why `auto` takes all of them.

## Catalogue

Runtimes are order-of-magnitude, measured on a 10-core Apple M5. `--no-build` is
permitted only after a successful build at the same source commit with the same
executable inputs.

### Cheap — run these constantly

| gate | proves | scale | time |
|---|---|---|---|
| `scripts/check-hygiene.sh` | source/forbidden-token hygiene, allowlist in `hygiene-allow.txt` | — | sub-second |
| `lake build` | integration elaboration | ~1,760 jobs | ~8 s |
| `scripts/check-u256.sh` | differential word/hash oracle | 21,593 cases | sub-second |
| `scripts/check.sh --patch` | the ten historical FAIL files, fixed all-PASS target | 10 | sub-second |
| `scripts/check.sh --rlp4` | four invalid-RLP/header files, subset of `--patch` | 4 | sub-second |
| `scripts/check-mainnet.sh --suite smoke` | current-mainnet smoke | 16 | sub-second |
| `scripts/check.sh --depth` | fuel/call-depth stress set | 67 | ~13 s |
| `python3 -m unittest discover -s scripts/tests` | harness/generator unit tests | 110 tests | ~13 s |
| `scripts/check-mainnet.sh --suite transitions` | fork-transition validity | 13 files / 109 cases | ~8–15 s |

### Medium — before a commit or push candidate

| gate | proves | scale | time |
|---|---|---|---|
| `scripts/check.sh --smoke` | broad conformance vs baseline | 174 classifications | ~2 min |
| `scripts/check.sh --bls` | BLS12-381 + point-evaluation vs hand-authored target baseline | 29 | ~2 min |
| `scripts/check-ec.sh` | EC differential oracle (pinned, differential, identity cases) | — | compiles a Lean checker first |
| `scripts/check-vectors.sh` | generated vector conformance + controls | 44 files, 5 controls | ~8 min |
| `cd ~/blanc && lake build && scripts/check.sh --no-build` | downstream elaboration + protected-theorem/axiom audit | ~907 jobs | ~7 s build |

### Long sequentially — but mostly not long in parallel

| gate | proves | scale | sequential | `--jobs auto` |
|---|---|---|---|---|
| `scripts/check-mainnet.sh --suite osaka` | strict all-PASS | 2,514 | ~8 min | **~2.3 min** |
| `scripts/check-mainnet.sh --suite prague` | strict all-PASS | 2,573 | ~12 min | **~3.0 min** |
| `scripts/check-mainnet.sh --suite full` | strict all-PASS, whole manifest | 5,100 | ~20.8 min | **~5.0 min** |
| `scripts/check.sh --full` | every legacy fixture vs baseline | 2,983 | ~31.1 min | ~15.0 min |

Judge the ten-minute long-gate deferral threshold against the gate as you will
actually run it. With `--jobs auto` the three current-mainnet suites drop well
under it and should be run inline rather than deferred by reflex — the whole
manifest costs about five minutes. **Only `check.sh --full` stays genuinely
long**, because one indivisible fixture dominates it and parallelism cannot
touch that.

The two `--full` gates are the exact-candidate closure pair. **Neither may be
replaced by its smoke tier.**

### Environment and provenance

| command | purpose |
|---|---|
| `python3 scripts/env_doctor.py` | validate the configured legacy/EELS/oracle environment |
| `python3 scripts/env_doctor.py --mainnet-root "$HOME/eest-mainnet-v20.0.1" --mainnet-deep` | validate external fixture identities |
| `python3 scripts/gen_mainnet_manifest.py --fixtures-root "$HOME/eest-mainnet-v20.0.1/fixtures" --check` | exact current-manifest identity |

Python generators run under the frozen oracle venv
`~/execution-specs/venv/bin/python`. Generated vectors must come from
generators, never manual transcription.

## Pass criteria

Two different contracts, and confusing them is the most common misreading:

- **`check.sh` tiers are regression gates.** They pass iff every file's
  classification *equals the committed baseline's* — **not** iff every file
  passes. The legacy corpus has 5 known FAILs; a FAIL turning into a PASS is a
  gate failure exactly like the reverse. Baselines are
  `scripts/baseline-<tier>.txt`, reports are `scripts/report-<tier>.txt`
  (gitignored).
- **`check-mainnet.sh` suites and `check.sh --patch`/`--rlp4` are all-PASS
  targets.** Any non-PASS fails. They have no baseline to rebase.

`--bls` is a middle case: it compares against a committed baseline like a tier,
but that baseline is a hand-authored *target*, so `--rebase` is refused — edit
`scripts/baseline-bls.txt` directly, with a written justification for any
non-PASS entry.

Every gate's last line is a single unambiguous verdict, and every gate exits 0
if and only if it passed.

## Rules

- Never weaken or silently rebase a gate to make it green. A baseline,
  exclusion list, manifest, timeout, or golden error route that has to move in
  order to pass is a stop condition, not a step.
- The wall-clock guard is a hang detector, never a classifier. If it trips, the
  run reports a HARNESS ERROR and records no classification for that file — no
  report or baseline can absorb the event.
- Never run a long fixture tier while Lean LSP servers are alive. Two LSP
  workers holding mathlib environments sit at ~900 MB RSS each and can exhaust
  this host's ~9 GB of swap, inflating wall time several-fold and producing
  pure-artifact DRIFT lines. Classifications stay trustworthy under contention;
  timings do not.
