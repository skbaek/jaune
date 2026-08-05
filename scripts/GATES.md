# Verification gates

Authoritative catalogue of the Jaune/Blanc verification gates: what exists, what
each one takes, what it proves, and which to reach for when. This file is the
single source of truth for gate usage — plans, agent instructions, and reports
should link here rather than restate it.

Audience is anyone driving these gates, human or agent, regardless of tool.

All commands are run from `~/jaune` unless stated otherwise.

## If you are an agent, start here

**For routine checks — "did my last edit break anything?" — pass `--jobs auto`.**
Three harnesses take it — `check.sh`, `check-mainnet.sh`, `check-vectors.sh` —
and all three run sequentially by default, which costs roughly 2–5x. That default
is deliberate and correct for the scripts (see [The `--jobs`
contract](#the---jobs-contract)), but it is the wrong default for development
work. Saving that time is the entire reason parallel mode exists; use it.

Choose the gate by what you changed, cheapest falsifier first:

| you changed | run this first | then, before pushing |
|---|---|---|
| anything at all | `scripts/check-hygiene.sh` + `scripts/check-integrity.sh` + `lake build` | — |
| U256/word/hash primitives | `scripts/check-u256.sh` | `scripts/check.sh --smoke --no-build --jobs auto` |
| blob-fee arithmetic (fake exponential) | `scripts/check-fake-exp.sh` | `scripts/check-mainnet.sh --suite transitions --no-build --jobs auto` |
| EC / precompiles | `scripts/check-ec.sh`, `scripts/check.sh --bls --no-build --jobs auto` | `scripts/check-mainnet.sh --suite prague --no-build --jobs auto` |
| interpreter / gas / state | `scripts/check.sh --depth --no-build --jobs auto` | `scripts/check.sh --smoke --no-build --jobs auto` |
| fork / block validity | `scripts/check-mainnet.sh --suite transitions --no-build --jobs auto` | `scripts/check-mainnet.sh --suite osaka --no-build --jobs auto` |
| harness / generators | `python3 -m unittest discover -s scripts/tests` | `python3 scripts/env_doctor.py` |
| a module's imports, or an added `#guard` / heavy elaboration | `lake build` | `scripts/check-elab.sh` |
| anything Blanc consumes | `cd ~/blanc && lake build && scripts/check.sh --no-build` | `cd ~/blanc && scripts/check-elab.sh` |
| a Blanc module's imports, or an added Blanc contract | `cd ~/blanc && scripts/check-layering.sh` | `cd ~/blanc && lake build && scripts/check.sh --no-build` |
| a Blanc contract's compiled bytes, its fixtures, or either fixture generator | `cd ~/blanc && scripts/check-fmint.sh --no-build` + `scripts/check-weth.sh --no-build` | both `cd ~/blanc && scripts/check-*-coverage.sh` |

**Use sequential (omit `--jobs`) when the timings themselves matter:** writing a
baseline with `--rebase` or `--refresh-times`, investigating a performance
regression, or producing timing evidence for a report. A contended run's TIME
column reflects scheduling, not the fixture. Parallel mode enforces this — it
refuses both writing modes outright.

**Long gates are evidence obligations, not optional.** An action expected to
exceed 1,000 seconds — judged as you will actually run it, parallel mode
included — is deferred to the user unless the task explicitly authorizes it; a
deferred long gate needs a named owner and must pass before merge. Everything
under the threshold runs inline (use background execution when one command
would outlast a foreground tool call), and a deferred gate never substitutes
for the cheap gates above.

## The `--jobs` contract

`check.sh`, `check-mainnet.sh`, and `check-vectors.sh` accept `--jobs <n>|auto`;
`auto` resolves to the machine's logical-core count. **Sequential (`--jobs 1`) is
the default and its behaviour is untouched** — same guard, same ordering, same
authoritative timings. Sequential is cleaner in every respect except speed, so it
stays the script-level default; parallel is an explicit per-invocation choice.

What parallel mode changes:

- **Timings become reference-only.** `--rebase` and `--refresh-times` are both
  refused and the DRIFT comparison is skipped entirely rather than computed and
  suppressed. The gate itself is unaffected — it only ever compared STATUS.
  `check-vectors.sh` has no baseline to protect, so it just marks the verdict
  line.
- **The per-file guard rises 1800s → 2000s.** This is the sole thing a parallel
  run still decides for real; it remains a hang detector, never a performance
  budget. An explicit `JAUNE_TIMEOUT` still wins. `check-vectors.sh` differs: it
  has no guard at all sequentially, and applies a 3600s one only in parallel,
  because its sequential path streams each runner's output as it goes — a hang is
  visible there, but a parallel run assembles its output at the end, where a hang
  and slow progress look alike until the guard distinguishes them.
- **Dispatch becomes longest-first**, seeded from the committed baseline's TIME
  column. No fixture names are hardcoded; if the slowest fixture changes, the
  next sequential `--rebase` updates the order automatically.
  `check-vectors.sh` has no baseline, so it seeds from a small reference-time
  table (`get_weight`) naming only its files that are not near-instant; an
  unnamed file sorts last. A stale weight there costs makespan, never
  correctness.
- **`check-mainnet.sh` runs the whole selection instead of stopping at the first
  failure**, and reports every failure. It also writes
  `scripts/report-mainnet-<suite>.txt`, which the sequential path does not.

What it does not change: the report is reassembled in **sequential order**, not
completion order, so a report from either mode diffs cleanly against the same
baseline. For `check-vectors.sh` this holds for stdout as well as the report:
both modes emit the same bytes in the same manifest order, so two runs differ
only in the verdict line's wall time and its `--jobs` marker.

Only these three harnesses take `--jobs`. `check-u256.sh`, `check-fake-exp.sh`,
`check-ec.sh`, and `check-hygiene.sh` do not — the first three are
single-process oracles and the fourth is sub-second.

`check-elab.sh` does not take it either, for a different and more fundamental
reason: **its gate *is* the TIME column.** The three harnesses above can run
contended because a contended run still decides STATUS correctly and only their
reference times degrade. An elaboration-time gate has nothing left once the
timings are untrustworthy, so it always runs one file at a time and there is no
flag to change that. For the same reason it inspects running Lean language
servers before measuring and refuses when they are holding large environments —
the swap-exhaustion case recorded in the last rule on this page. It keys on
resident size rather than on presence, deliberately: `lean-lsp-mcp` is mandated
tooling, so an idle server (~40 MB, no file open) is the normal steady state and
must not block the gate, whereas one holding a mathlib environment (~900 MB)
must. `--force` overrides for investigation and may not be combined with
`--rebase`.

### What the job count is worth

It depends on which bound the suite is under, and the corpora differ:

- **Legacy `--full` is latency-bound.** Its makespan is set by the single
  longest indivisible fixture, not by the job count. That fixture is now
  `VMTests/vmPerformance/loopMul.json` at 372.5s sequential — 33% of the serial
  total and 4.5x the second-longest file. Measured 462s at `--jobs auto` (10)
  on 2026-07-31. Only making *that* fixture faster moves this number. ("Serial
  total" here and below means the sum of the per-file TIME column, 1,145.8s — a
  lower bound on sequential wall time, not a measured one; see the catalogue
  table's note.)

  Until 2026-07-31 the dominant fixture was `stTimeConsuming/CALLBlake2f_MaxRounds`
  at 711s (~41% of a 3,338s serial total), which held the makespan near 900s
  regardless of workers. Unboxing the BLAKE2b working vector took it to 75.9s
  (see `scripts/report-blake2f.md`), which is why the bound moved. The lesson
  generalizes: when one file caps this gate, the number only moves by making
  that file faster — and when it does, the committed TIME column must be
  refreshed or dispatch keeps scheduling the old order (see [Writing a
  `check.sh` baseline](#writing-a-checksh-baseline-two-verbs)).
- **The vector suite was latency-bound until its dominant file was sharded.**
  `blsPairing.json` alone was ~367s of a ~458s sequential total (80%), which set
  the makespan floor no matter how many workers ran: 382s at 10 jobs, a 1.2x
  saving. It is now run as eight balanced shards holding exactly its 106 cases
  (see `scripts/vectors/SOURCES.md`), which drops the gate to ~90s at
  `--jobs auto`. Measured makespan for that file's work alone: 367s unsharded,
  83s at 8 shards, 82s at 24, 78s at 53 — the machine's aggregate-throughput
  ceiling is ~78s, so 8 shards is within 7% of the floor and more shards buy
  almost nothing.
- **Current-mainnet suites are throughput-bound.** ~90% of their fixtures run
  under 0.15s, so process spawn dominates and the suite scales with cores:
  435s at 4 jobs, 328s at 8, 299s at 10.

The two latency-bound cases look alike and are not, so do not read the vector
suite's fix as a plan for `--full`. What carries over is the diagnostic question,
not the remedy: when one file caps a parallel gate, ask what is inside it.

`blsPairing.json` was a **batch** — one process holding 106 independent cases,
each a pure function of its own input. Batches split; the only cost is the
discipline of proving the parts still cover the whole.

`loopMul.json` — like `CALLBlake2f_MaxRounds.json` before it — is a **single
computation**: one block, one transaction, contiguous work with no independent
units inside it. No partition of it exists and sharding has nothing to offer
`--full`. Only making that computation faster moves that number.

That is exactly what happened to the previous holder of this position.
`CALLBlake2f_MaxRounds` was 711s of contiguous BLAKE2F rounds; replacing the
boxed `Array UInt64` working vector with a flat scalar structure made it 75.9s
and handed the bound to `loopMul`. Sharding was never the remedy for either.

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
| `scripts/check-integrity.sh` | no panic / raw bang op / stringly semantic carrier in `Jaune.lean`'s import closure (R4 also covers the runner boundary), allowlist in `integrity-allow.txt` | 58 rows, 0 pending | sub-second |
| `lake build` | integration elaboration | ~1,776 jobs | ~8 s |
| `scripts/check-u256.sh` | differential word/hash oracle | 21,593 cases | sub-second |
| `cd ~/blanc && scripts/check-layering.sh` | Blanc's contracts are siblings in the import hierarchy: no cross-contract import, no shared module importing a contract, no unclassified module (rule and rationale in Blanc's `README.md`) | 2 contracts, 15 modules, 13 non-root | sub-second |
| `cd ~/blanc && scripts/check-fmint.sh --no-build` | fmint fixture conformance, the manifest cross-check, and byte-equality of every fixture's fmint pre-state code against the committed `Blanc.fmintCode` literal | 11 fixtures, 188 assertions, 1257 bytes | sub-second |
| `cd ~/blanc && scripts/check-weth.sh --no-build` | WETH fixture conformance and the same byte-equality check against `Blanc.wethCode`; there is no WETH manifest, so no cross-check | 11 fixtures, 888 bytes | sub-second |
| `cd ~/blanc && scripts/check-fmint-coverage.sh` | every fmint selector is exercised by some fixture, against a declared unexercised-selector budget | 12 selectors, budget 0 | sub-second |
| `cd ~/blanc && scripts/check-weth-coverage.sh` | the same for WETH, plus the `deposit()` fallback on empty calldata | 10 selectors + fallback, budget 0 | sub-second |
| `scripts/check-fake-exp.sh` | fake-exponential differential oracle vs the pinned EELS `taylor_exponential` (blob base fee) | 240 cases | sub-second |
| `scripts/check.sh --patch` | the ten historical FAIL files, fixed all-PASS target | 10 | sub-second |
| `scripts/check.sh --rlp4` | four invalid-RLP/header files, subset of `--patch` | 4 | sub-second |
| `scripts/check-mainnet.sh --suite smoke` | current-mainnet smoke | 16 | sub-second |
| `scripts/check.sh --depth` | fuel/call-depth stress set | 67 | ~13 s |
| `python3 -m unittest discover -s scripts/tests` | harness/generator unit tests | 121 tests | ~13 s |
| `scripts/check-mainnet.sh --suite transitions` | fork-transition validity | 13 files / 109 cases | ~8–15 s |

### Medium — before a commit or push candidate

| gate | proves | scale | time |
|---|---|---|---|
| `scripts/check.sh --smoke` | broad conformance vs baseline | 174 classifications | ~2 min |
| `scripts/check.sh --bls` | BLS12-381 + point-evaluation vs hand-authored target baseline | 29 | ~2 min |
| `scripts/check-ec.sh` | EC differential oracle (pinned, differential, identity cases) | — | compiles a Lean checker first |
| `scripts/check-vectors.sh` | generated vector conformance + controls + declared-case-count coverage | 51 files, 1,824 cases, 5 controls | ~7.8 min; **~1.5 min at `--jobs auto`** |
| `scripts/check-elab.sh` | per-module elaboration time vs `scripts/baseline-elab.txt` | 17 modules, ~49 s of elaboration | ~70 s |
| `cd ~/blanc && scripts/check-elab.sh` | per-module Blanc elaboration time vs `~/blanc/scripts/baseline-elab.txt` | 15 modules, ~39 s of elaboration | ~40 s |
| `cd ~/blanc && lake build && scripts/check.sh --no-build` | downstream elaboration + protected-theorem/axiom audit | 922 jobs, 24 audited theorems | ~7 s build |

### Long sequentially — but mostly not long in parallel

| gate | proves | scale | sequential | `--jobs auto` |
|---|---|---|---|---|
| `scripts/check-mainnet.sh --suite osaka` | strict all-PASS | 2,514 | ~8 min | **~2.3 min** |
| `scripts/check-mainnet.sh --suite prague` | strict all-PASS | 2,573 | ~12 min | **~3.0 min** |
| `scripts/check-mainnet.sh --suite full` | strict all-PASS, whole manifest | 5,100 | ~20.8 min | **~5.0 min** |
| `scripts/check.sh --full` | every legacy fixture vs baseline | 2,983 | **≥ 19 min** | **7.7 min** |

**Read the two legacy `--full` cells differently — they have different
provenances.** The parallel cell is a measured wall time: 462 s at `--jobs auto`,
2026-07-31. The sequential cell is **not** a measured wall time; it is
1,145.8 s of *summed per-file fixture time* taken from the refreshed TIME
column, which is a **lower bound** on wall time — a sequential run also pays
2,983 process spawns plus harness overhead on top. Treat it as "at least 19
min". Before the BLAKE2b unboxing the corresponding figures were ≥ 3,338 s
summed and ~900 s measured.

Judge the 1,000-second deferral threshold against the gate as you will actually
run it. At `--jobs auto` every row above comes in under it — legacy `--full`
lands near ~460 s, latency-bound by one indivisible fixture that parallelism
cannot touch — so all four run inline rather than deferred by reflex.
**A sequential legacy `check.sh --full` remains above the threshold and still
requires explicit authorization**: its lower bound alone, 1,145.8 s, exceeds
1,000 s. A sequential run is still called for only when its per-file timings are
themselves the evidence.

**The BLAKE2b unboxing changed no deferral status.** The parallel run was already
under the threshold before it (~900 s) and the sequential run was already above
it; the arc made both faster without moving either across the line.

The two `--full` gates are the exact-candidate closure pair. **Neither may be
replaced by its smoke tier.**

### Environment and provenance

| command | purpose |
|---|---|
| `python3 scripts/env_doctor.py` | validate the configured legacy/EELS/oracle environment |
| `python3 scripts/env_doctor.py --mainnet-root "$HOME/eest-mainnet-v20.0.1" --mainnet-deep` | validate external fixture identities |
| `python3 scripts/gen_mainnet_manifest.py --fixtures-root "$HOME/eest-mainnet-v20.0.1/fixtures" --check` | exact current-manifest identity |
| `python3 scripts/gen-vector-shards.py --check` | the `blsPairing` shards are an exact partition of their source |

Python generators run under the frozen oracle venv
`~/execution-specs/venv/bin/python`. Generated vectors must come from
generators, never manual transcription.

## Pass criteria

Two different contracts, and confusing them is the most common misreading:

- **`check.sh` tiers are regression gates.** They pass iff every file's
  classification *equals the committed baseline's* — **not** iff every file
  passes. The legacy corpus has 5 known FAILs, all diagnosed and none a Jaune
  defect: two files have no case in the supported fork range, while the other
  three carry wrong expected exceptions and the frozen oracle agrees with
  Jaune. A FAIL turning into a PASS is a gate failure exactly like the reverse.
  Baselines are `scripts/baseline-<tier>.txt`, reports are
  `scripts/report-<tier>.txt` (gitignored).
- **`check-mainnet.sh` suites and `check.sh --patch`/`--rlp4` are all-PASS
  targets.** Any non-PASS fails. They have no baseline to rebase.
- **`check-vectors.sh` is an all-PASS target that also checks coverage.** Every
  manifest file must pass *and* must run the number of cases the manifest
  declares for it, cross-checked against the count the runner reports. A file
  that quietly lost cases would otherwise pass while testing less than it
  claims — the runner reports `n/n` for whatever it finds. A file with no
  declared count is a configuration error, not an unchecked file, which is what
  forces a newly added vector to state its size. The binary independently
  refuses a vector file holding no cases rather than reporting a vacuous `0/0`
  pass.

- **`scripts/check-elab.sh` is a per-module drift gate on elaboration time.** It
  measures each of our own modules (`Jaune/**/*.lean` plus `Jaune.lean` and
  `Main.lean`, discovered rather than listed) re-elaborating against built
  dependencies — the cost of opening the file in a session, and the cost sitting
  on `lake build`'s critical path. A module fails above **both** 2x its
  `scripts/baseline-elab.txt` time **and** that time plus 1.0 s; the absolute
  floor keeps a sub-second module from tripping on scheduler noise. A module
  that fails to elaborate at all fails the gate, and a source module with no
  baseline row is a configuration error, which is what forces a new module to
  state its cost. A module that got much *faster* prints `IMPROVED` rather than
  passing silently, because a stale over-generous baseline is how this gate
  would quietly stop gating; refresh with `--rebase`. Stale rows for deleted
  files are a warning, never a failure. This gate exists because no other one
  measures this axis: hygiene, integrity, and every conformance tier are silent
  about elaboration cost, and CI's only ceilings are coarse job timeouts, so a
  module drifting from 4 s to 60 s would land unnoticed.

  **It is a local gate, not a CI gate.** Its baseline is wall-clock time from
  one machine, which is machine-dependent in precisely the way `notimeout.md`
  objected to when it abolished TIMEOUT as a fixture classification — a slower
  runner would fail modules that are in no way worse. Keep it a pre-push check,
  or give CI a baseline measured on its own runner. The 2x factor and the 1.0 s
  floor absorb same-machine variance, not cross-machine variance.

- **`scripts/check-integrity.sh` is a shrink-only budget.** It inventories
  `panic`, raw bang operations, and stringly-typed semantic error carriers over
  the exact local module import closure of `Jaune.lean`, computed transitively
  rather than hardcoded, and every occurrence must match an exact row in
  `scripts/integrity-allow.txt`. A **new** occurrence fails. `PENDING` rows —
  known defects with an owning step — are counted against a declared
  `# pending-budget:` line that may only decrease, so a step cannot discharge
  one defect and quietly introduce another. Absence of `partial def`,
  `implemented_by`, and `dbg_trace` is asserted outright: the gate refuses an
  allowlist that carries a row for them at all. Use `--list` to regenerate the
  inventory and `--pending` to read the full pending set.

`--bls` is a middle case: it compares against a committed baseline like a tier,
but that baseline is a hand-authored *target*, so `--rebase` is refused — edit
`scripts/baseline-bls.txt` directly, with a written justification for any
non-PASS entry.

Every gate's last line is a single unambiguous verdict, and every gate exits 0
if and only if it passed.

## Writing a `check.sh` baseline: two verbs

A baseline line is `STATUS<TAB>TIME<TAB>path`, and the two columns have
different status: STATUS is the gate, TIME is reference data. So the two reasons
to rewrite a baseline get two different flags. Both are sequential-only, and
both are refused for the `--patch`/`--rlp4` target gates and for the
hand-maintained `--bls` baseline.

| flag | means | on a classification change |
|---|---|---|
| `--rebase` | "the classifications legitimately changed; accept them" | absorbs it, after printing a `REBASE — <file>: <old> -> <new>` line for each |
| `--refresh-times` | "the classifications are identical, the code got faster; refresh the reference times" | **writes nothing**, prints the differing files, exits nonzero |

`--rebase` is rare and consequential — it is the one operation that can make a
regression disappear, which is why it now prints the delta it absorbs instead of
a bare `OK`. `--refresh-times` is the safe, mechanical case: it runs the tier,
compares STATUS through the ordinary comparison, and only then writes a baseline
that keeps the committed STATUS and path columns and takes TIME from the new
run. It re-checks that property on the bytes it is about to write, so
"timing-only" is verified rather than asserted. A refusal from it is a finding —
report it; do not route around it with `--rebase`.

Refreshing TIME is not cosmetic. Parallel dispatch is longest-first, **seeded
from the committed baseline's TIME column**, so after an optimization that
changes which fixture is slowest, a stale TIME column schedules the wrong
fixture first and gives back part of the speedup. Note also that no DRIFT line
appears when a fixture gets *faster* — DRIFT fires only above 2× its reference —
so nothing else prompts the refresh.

Verdict lines:

```
OK — full: 2983 files STATUS-identical to baseline; TIME column refreshed
OK — depth: baseline rebased with 67 files, 1 classification change(s) absorbed (67 PASS, 0 FAIL)
```

## One run at a time

Two gate runs on one host are refused, not queued. Each report-writing harness
takes an exclusive lock on its report file, and the heavier ones additionally
take a single shared **heavy-gate lock**; a second run that would contend exits
2 with a `REFUSED` verdict naming the holder's PID, start time, and full command
line. It does not wait, does not fall back to another path, and writes nothing.
The mechanism is `scripts/gate-lock.sh` (`mkdir`, `kill -0`, one `EXIT` trap —
macOS has no `flock`), which also documents the 2026-07-31 incident that
motivated it.

| gate | report lock | heavy lock |
|---|---|---|
| `check.sh --smoke`, `--bls`, `--full`, or any `--jobs > 1` | yes | yes |
| `check.sh --depth`, `--patch`, `--rlp4`, `--dir` (sequential) | yes | no |
| `check-mainnet.sh --suite osaka`/`prague`/`full`, or any `--jobs > 1` | parallel only | yes |
| `check-mainnet.sh --suite smoke`/`transitions` (sequential) | — (writes none) | no |
| `check-vectors.sh` | yes | yes |
| `check-elab.sh` (Jaune or Blanc) | yes | yes |
| `cd ~/blanc && scripts/check-layering.sh` | — (writes none) | no |
| `cd ~/blanc && scripts/check-fmint.sh`, `check-weth.sh`, and both `check-*-coverage.sh` | — (write none) | no |

The cheap tiers stay outside the heavy lock deliberately: the check you run
while iterating must never be hostage to a 20-minute one. `check-hygiene.sh`,
`check-integrity.sh`, `check-u256.sh`, `check-fake-exp.sh` and `check-ec.sh`
take no lock at all — the first four are sub-second, and `check-ec.sh` is a
single-process oracle that writes its report in one `tee` rather than appending
per file.

Escape hatches, where one exists, are named in the refusal: `check.sh` and
`check-elab.sh` accept `--report <path>`, and a run writing elsewhere locks that
path instead. There is no flag that skips the heavy lock. A run killed with
`SIGKILL` leaves its lock behind; the next run finds the recorded PID dead,
announces a `RECLAIMED` line, and proceeds.

## Rules

- Never weaken or silently rebase a gate to make it green. A baseline,
  exclusion list, manifest, timeout, or golden error route that has to move in
  order to pass is a stop condition, not a step.
- The wall-clock guard is a hang detector, never a classifier. If it trips, the
  run reports a HARNESS ERROR and records no classification for that file — no
  report or baseline can absorb the event.
- **A report or baseline that repeats a path is a harness event, never a
  classification change** — the same rule, applied to the other input the
  comparison trusts. `check.sh` treats `path` as a primary key on its selection,
  its report, and its baseline, and rejects a violation on any of the three
  before comparing anything, `--rebase` included. It also refuses a report whose
  line count disagrees with the selection. Without those checks a doubled report
  scores one fabricated `MISSING -> <status>` per file, which is exactly how the
  2026-07-31 run reported 2,983 regressions against a baseline nobody had
  touched. `MISSING` itself still means what it always meant: a report path the
  baseline does not carry is a new fixture.
- Never run a long fixture tier while Lean LSP servers are alive. Two LSP
  workers holding mathlib environments sit at ~900 MB RSS each and can exhaust
  this host's ~9 GB of swap, inflating wall time several-fold and producing
  pure-artifact DRIFT lines. Classifications stay trustworthy under contention;
  timings do not.
