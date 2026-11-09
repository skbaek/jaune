# Verification gates

Authoritative catalogue of **Jaune's** verification gates: what exists, what
each one takes, what it proves, and which to reach for when. This file is the
single source of truth for Jaune gate usage — plans, agent instructions, and
reports should link here rather than restate it.

Audience is anyone driving these gates, human or agent, regardless of tool.

**Headline fact these gates produce.** Jaune passes 100% of the
blockchain-test fixtures of `execution-specs` `tests@v21.0.2` whose fork lies
in [Byzantium, BPO2]: 73,686/73,686 cases and 8,262/8,262 files, as the union
of `scripts/check-mainnet.sh --lane historical --suite hist-full` (39,212 cases /
3,550 files) and `scripts/check-mainnet.sh --suite full` (34,474 / 4,712), both
strict all-PASS with no expected-failure allowance. Neither is a CI gate.

All commands are run from the root of the Jaune checkout under test — the
goal's worktree during goal work, `~/jaune` otherwise — unless stated
otherwise.

**`check-legacy.sh` was named `check.sh` until 2026-08-05.** It was renamed
because the bare name said nothing about which corpus it runs, and the two
conformance harnesses read as unrelated when they are siblings:
`check-legacy.sh` drives the legacy corpus, `check-mainnet.sh` the current one.
Reports and commits from before that date name it `check.sh`; those are records
of what was run and were deliberately left alone. Nothing else took the name —
`check.sh` no longer exists in this repository, so an old command line fails
loudly rather than silently running something different. (Blanc has its own
unrelated `scripts/check.sh`, an axiom audit.)

**Blanc's gates are catalogued in its own repository, at
`~/blanc/scripts/GATES.md`.** A gate lives in the repository whose tree it
checks. Blanc consumes Jaune through an ordinary pinned Lake dependency, so
Blanc's gates appear here only where a *Jaune* change makes them the right
falsifier — see [Blanc's gates](#blancs-gates) below.

## If you are an agent, start here

**For routine checks — "did my last edit break anything?" — pass `--jobs auto`.**
Three harnesses take it — `check-legacy.sh`, `check-mainnet.sh`, `check-vectors.sh` —
and all three run sequentially by default, which costs roughly 2–5x. That default
is deliberate and correct for the scripts (see [The `--jobs`
contract](#the---jobs-contract)), but it is the wrong default for development
work. Saving that time is the entire reason parallel mode exists; use it.

Choose the gate by what you changed, cheapest falsifier first:

| you changed | run this first | then, before pushing |
|---|---|---|
| anything at all | `scripts/check-hygiene.sh` + `scripts/check-integrity.sh` + `scripts/check-canonical-opcode-names.sh` + `scripts/check-rule-data-reads.sh` + `lake build` | — |
| the canonical execution surface, its `#expect_axioms` rows or `Examples/` | `python3 scripts/check-consumer-boundary.py` + `python3 scripts/check-assurance-manifest.py` | `lake build` |
| U256/word/hash primitives | `scripts/check-u256.sh` | `scripts/check-legacy.sh --smoke --no-build --jobs auto` |
| blob-fee arithmetic (fake exponential) | `scripts/check-fake-exp.sh` | `scripts/check-mainnet.sh --suite transitions --no-build --jobs auto` |
| EC / precompiles | `scripts/check-ec.sh`, `scripts/check-legacy.sh --bls --no-build --jobs auto` | `scripts/check-mainnet.sh --suite prague --no-build --jobs auto` |
| interpreter / gas / state | `scripts/check-legacy.sh --depth --no-build --jobs auto` | `scripts/check-legacy.sh --smoke --no-build --jobs auto` |
| call frames, calldata lifetime, or anything under `genericCall` | `scripts/check-memory-probe.sh` | `scripts/check-legacy.sh --depth --no-build --jobs auto` |
| fork / block validity | `scripts/check-mainnet.sh --suite transitions --no-build --jobs auto` | `scripts/check-mainnet.sh --suite osaka --no-build --jobs auto` |
| a number a fork carries as rule data (`Jaune/Fork.lean`) | `scripts/check-fork-constants.sh` | `scripts/check-mainnet.sh --suite full --no-build --jobs auto` |
| the runner's CLI, its refusals or its case selection (`Main.lean`) | `scripts/check-cli.sh` + `scripts/check-mainnet.sh --suite smoke` | `scripts/check-legacy.sh --smoke --no-build --jobs auto` |
| the `t8n` frontend (`Jaune/T8n.lean`) or its corpus | `scripts/check-t8n.sh --red-test` | `scripts/check-mainnet.sh --suite smoke` |
| trace serialization or the standalone message/transaction runner | owned build of `jaune-trace`, then `python3 scripts/check-trace.py` | ordinary CLI controls; reference trace comparison under an explicit projection |
| harness / generators | `python3 scripts/check-legacy-baseline.py self-test` + `python3 -m unittest discover -s scripts/tests` | `python3 scripts/env_doctor.py` |
| a module's imports, or an added `#guard` / heavy elaboration | `lake build` | `scripts/check-elab.sh` |
| anything Blanc consumes | `lake build && scripts/check.sh --no-build` in the Blanc checkout carrying the candidate pin — its goal worktree during goal work, `~/blanc` otherwise | Blanc's full set — see [Blanc's gates](#blancs-gates) |

**Use sequential (omit `--jobs`) when the timings themselves matter:** refreshing
this host's ignored timing baseline with `--rebase` or `--refresh-times`,
investigating a performance regression, or producing timing evidence for a
report. A contended run's TIME column reflects scheduling, not the fixture.
Parallel mode enforces this — it refuses both writing modes outright.

**Long gates are evidence obligations, not optional.** An action expected to
exceed 1,000 seconds — judged as you will actually run it, parallel mode
included — is deferred to the user unless the task explicitly authorizes it; a
deferred long gate needs a named owner and must pass before merge. Everything
under the threshold runs inline (use background execution when one command
would outlast a foreground tool call), and a deferred gate never substitutes
for the cheap gates above.

## The `--jobs` contract

`check-legacy.sh`, `check-mainnet.sh`, and `check-vectors.sh` accept `--jobs <n>|auto`;
`auto` resolves to the smaller of effective CPU capacity and a memory budget.
The shared `scripts/fixture_jobs.py` selector reserves 1 GiB outside the worker
pool and provisions 2.4 GiB per worker. On Linux it takes the tightest remaining
allowance across host `MemAvailable` and every finite cgroup-v2 ancestor, and
caps CPU by affinity, cpuset, and finite quota; on macOS it counts only free and
inactive `vm_stat` pages. XNU already includes speculative pages in its free
count, and purgeable pages are not assumed disjoint, so neither is counted a
second time. An unreadable container boundary or other missing trustworthy
memory information conservatively resolves to one worker; an **unreadable**
boundary file is distinguished from an **absent** one, so a leaf whose own
`memory.max` is refused resolves to one worker rather than inheriting a
permissive readable ancestor's answer. A clean 6 or 8 GiB job therefore selects
no more than two.
**Sequential (`--jobs 1`) is the default and its behaviour is untouched** —
same guard, same ordering, same authoritative timings. A positive numeric value
is an explicit override and bypasses automatic sizing without changing its
meaning; invalid and zero values still fail loudly. On a memory-constrained
host, safer `auto` sizing can trade parallel throughput for headroom. Use a
numeric override only after separately measuring that worker count under the
same boundary; this policy does not imply an interpreter-runtime regression.

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
- **Dispatch becomes longest-first**, seeded from this checkout's ignored
  host-local timing baseline when it exists. No fixture names are hardcoded; a
  fresh clone preserves report order until its first complete sequential run
  creates the local weights.
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
`check-ec.sh`, `check-hygiene.sh`, and `check-canonical-opcode-names.sh` do not
— the first three are single-process oracles and the last two are sub-second.

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
  total and 4.5x the second-longest file. Measured 462s at `--jobs 10`
  on 2026-07-31. Only making *that* fixture faster moves this number. ("Serial
  total" here and below means the sum of the per-file TIME column, 1,145.8s — a
  lower bound on sequential wall time, not a measured one; see the catalogue
  table's note.)

  Until 2026-07-31 the dominant fixture was `stTimeConsuming/CALLBlake2f_MaxRounds`
  at 711s (~41% of a 3,338s serial total), which held the makespan near 900s
  regardless of workers. Unboxing the BLAKE2b working vector took it to 75.9s
  (see `scripts/report-blake2f.md`), which is why the bound moved. The lesson
  generalizes: when one file caps this gate, the number only moves by making
  that file faster — and when it does, the host-local timing baseline must be
  refreshed or dispatch keeps scheduling the old order (see [Writing a
  `check-legacy.sh` baseline](#writing-a-check-legacysh-baseline-two-verbs)).
- **The vector suite was latency-bound until its dominant file was sharded.**
  `blsPairing.json` alone was ~367s of a ~458s sequential total (80%), which set
  the makespan floor no matter how many workers ran: 382s at 10 jobs, a 1.2x
  saving. It is now run as eight balanced shards holding exactly its 106 cases
  (see `scripts/vectors/SOURCES.md`), which drops the gate to ~90s at
  `--jobs 10`. Measured makespan for that file's work alone: 367s unsharded,
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

Efficiency cores run this workload ~5x slower than performance cores, but the
OS scheduler migrates rather than pins (at 8 concurrent, every worker inflates
a uniform ~1.64x rather than some bimodally). The CPU side of `auto` therefore
uses all CPUs actually available to the job; the independent memory side is the
safety cap. Use an explicit numeric count when reproducing a historical timing.

## Catalogue

Runtimes are order-of-magnitude, measured on a 10-core Apple M5. A cell marked
"2026-09-21 catalogue" is the wall time of that row in the Lean 4.34 migration's
full catalogue run on this host (recorded outside this repository;
Jaune `194adff`, parallel rows at `--jobs auto`); a cell with no date is older.
`--no-build` is permitted only after a successful build at the same source commit
with the same executable inputs.

### Cheap — run these constantly

| gate | proves | scale | time |
|---|---|---|---|
| `scripts/check-hygiene.sh` | source hygiene (`dbg_trace`, `sorry`) **and the trust surface** (`axiom`, `opaque`, `@[extern]`, `@[implemented_by]`, `@[csimp]`, `partial def`, `unsafe`, `native_decide`) under `Jaune/` and the consensus tree `JauneConsensus/` (with its root `JauneConsensus.lean` and runner `ConsensusMain.lean`) **plus `MemoryProbe.lean`**, allowlist in `hygiene-allow.txt`. The three attribute checks cover declaration annotations and line-leading `attribute [...]` commands (including local/scoped attribute lists); this is a line-local lexical gate, not a Lean parser. `@[csimp]` is on this list because it is the attribute that makes the compiled binary run a different function from the elaborated definition, and every fixture gate measures the compiled binary | 10 patterns, 1 occurrence, 1 allowlist row (`Jaune.execFueled_eq_cached`, justified in `hygiene-allow.txt`) | sub-second |
| `scripts/check-integrity.sh` | no panic / raw bang op / stringly semantic carrier in `Jaune.lean`'s import closure and in the consensus layer (`JauneConsensus.lean`'s closure, every file under `JauneConsensus/`, and `ConsensusMain.lean`) (R4 also covers the runner boundary and `MemoryProbe.lean`; R1's absence rule covers `MemoryProbe.lean` too). R5, an absence rule with no allowlist, is the consensus spec layer's failure-fidelity check (goal `jaune-consensus-electra-fulu-v1`, O5): under `JauneConsensus/` minus `UInt.lean`, `Harness/` and `Crypto/`, no defaulted read (`getD`, `getLastD`, `headD`) and no raw `UInt64` (the type name, `toUInt64`, `.val`), so wrapping `+ - * / %`, shifts and truncating literals exist only behind `UInt.lean`'s checked operations. Controls (2026-11-09, reverted, restored bytes identical): planted `xs[0]!`, a `UInt64` `+`, `getD`, `.val` and `panic!` in `JauneConsensus/SSZ/Merkle.lean` each turn it red under R3/R5/R5/R5/R2. R6, also an absence rule with no allowlist, covers every file under `JauneConsensus/`: no nested action `(← ...)` in a branch of a term-level `if` (`:= if` / `← if`) unless the branch is its own `do` block, because Lean lifts the action before the `if` and an Electra-only field read in an Electra branch would run, and reject, at Deneb. Control (2026-11-09, reverted, restored bytes identical): removing the `do` from `get_expected_withdrawals`'s Electra branch in `JauneConsensus/Block.lean` turns it red under R6; allowlist in `integrity-allow.txt` | 57 rows, 0 pending | sub-second |
| `scripts/check-canonical-opcode-names.sh` | the eight retired constructor/API spellings and three abbreviated render strings are absent from live Lean source; syntax-qualified SELFDESTRUCT matching leaves ordinary destination locals alone | 8 symbol families, 3 render strings | sub-second |
| `python3 scripts/check-assurance-manifest.py` | that the [destination axiom audit](#destination-axiom-audit)'s `#expect_axioms` rows and `scripts/assurance-manifest.json` name the same declarations with the same expected sets, in both directions and without repeats, and that every public theorem/lemma and `Exec`-valued def of `Jaune/SymbolicPush.lean` and `Jaune/SymbolicArith.lean` has a row. Also that `scripts/JauneUnionAxioms.lean` imports every `Jaune/` module and `scripts/ConsensusUnionAxioms.lean` (library `ConsensusAssurance`, separate from the `Assurance` Blanc builds) every `JauneConsensus/` module; an orphan `JauneConsensus/Orphan.lean` turns it red. Source-only: whether each set is the declaration's actual closure is the build's verdict | 53 rows / 53 entries, 9 covered rules | sub-second |
| `scripts/check-rule-data-reads.sh` | that no interpreter site reads a repriced gas number from the global that shadows it instead of from the selected `rules.gas`. Inventories every live mention of `gasColdAccountAccess`, `gasCallValue` and `gasCreate` under `Jaune/` and in `Main.lean` against the shrink-only `scripts/rule-data-allow.txt`; a new occurrence anywhere fails until it is classified. It is structural rather than an evaluation guard on purpose (goal `jaune-forks-by-construction-v1`, D-F6): when this gate was introduced, every reachable `stateGas = none` machine ran `pragueGasSchedule`, so a global read could agree numerically and escape an evaluation guard. Historical forks now carry distinct schedules; this gate continues to enforce the selected-rule read boundary rather than relying on coincident literal values. **This gate is the whole of the replacement's site coverage.** The schedule-level rows beside `meteringGuardLegacySchedule` in `Jaune/Execution.lean` record two of the four quantities the retired `meteringGuardLegacyRules` rows priced (14,500 / 5,400), through `GasSchedule.accessCost`, `GasSchedule.accessDelegation` and `GasSchedule.delegationCost`. The CREATE (31,000) and SELFDESTRUCT (32,700) rows restated a literal and arithmetic over definitions, could not fail for anything an instruction site does, and were removed on 2026-09-23 (evidence-economy trim); those two quantities have no function-level control. Negative controls, both run in a disposable tree: replacing `gasRules.callValue` by `gasCallValue` in `Xinst.step`'s legacy CALL arm, and `sevm.benvStat.rules.gas.coldAccountAccess` by `gasColdAccountAccess` in `Linst.run`'s legacy SELFDESTRUCT arm (`Jaune/Machine.lean`), each leave the tree green with every `#guard` still passing and turn **this** gate red naming the new occurrence; reverting only the edit restores green | 3 shadowed globals, 15 occurrences / 14 allowlist rows | sub-second |
| `lake build` | integration elaboration. Its default targets are `Jaune`, `Examples`, `Assurance`, `jaune`, `jaune-memory-probe` and `jaune-trace`, so the bounded memory probe is elaborated by the ordinary build rather than only on request, and the ordinary build fails on any [destination axiom audit](#destination-axiom-audit) mismatch | 1,822 jobs (2026-10-11) | ~8 s |
| `scripts/check-cli.sh` | the runner's fixture-file refusals (wrong sibling tree, no cases, no supported network, and filters selecting nothing), undeclared-format pass-through and supported static/transition admissions, tested with synthetic inputs. The original Amsterdam refusal guards were rewritten as admission assertions rather than deleted; unknown labels still fail closed. The rule-data printer answers `--rules` for all 17 runnable rule sets, while the retired `--rules-partial` flag is refused. The t8n handshake verifies the 16 target-backed names against `sources.json`'s `conformance_target.fork_lane`, with Petersburg advertised as `ConstantinopleFix`; synthetic EIP-1283 `Constantinople` is fixture-only and has no t8n target name. `--info` states the advertised lane, its basis and resolved set without an obsolete pending-goal clause. Allocation boundaries and the shared expectation-field helper additionally check strict/diagnostic selection and complete/unreached provenance, and a second helper checks that `t8n` refuses a quantity too wide for its field | 72 checks; the helpers separately report 20 focused ingress invocations and 49 wide-input rows | Current WSL timing pending |
| `scripts/check-fork-constants.sh` | that each live rule-data field classified for comparison agrees with the pinned `execution-specs` module where that module exists, by comparing `scripts/amsterdam/constants.json` (written by `scripts/gen-fork-constants.py` from that revision) against `lake exe jaune --rules <fork>`. Also that the extraction was taken at the commit `sources.json` currently pins, and — the row that keeps the gate from shrinking — that the printer's field set is exactly the set the extraction's coverage table classifies, so a new `ForkRules` field must be classified before this can pass. The Amsterdam column is compared in full: `bal.itemCost` from `vm.gas.GasCosts.BLOCK_ACCESS_LIST_ITEM`, `op.slotnum`/`op.stackAccess` as source-presence facts on `vm.instructions.Ops`, the code limits from `vm.interpreter`, the four request `(type, address)` pairs in `process_general_purpose_requests` call order; no field of any fork is classified as owned by a later goal. One row is schedule data rather than rule data (programme D13, goal `jaune-amsterdam-currency-v1`): `mainnetActivation`, the pinned `FORK_CRITERIA` timestamp against `mainnetChainConfig`'s activation for the fork — `null` on both sides for Amsterdam while upstream keeps it `Unscheduled`, so the day the pin says `ByTimestamp` this gate turns red at `Amsterdam.mainnetActivation` and names the `mainnetAmsterdamTimestamp` to write (before that goal the criterion was only printed, under `--table`). Negative controls: one Amsterdam literal mutated in a disposable worktree turns this gate red at the named field (`Amsterdam.bal.itemCost: this build has 2001, 1562e2f8b5cb has 2000`, readiness control) and the gas-limit boundary fixture red; the D13 row's three-part control is recorded in goal D's work records. The mainnet schedule is compared for all 17 declared forks (goal `jaune-historical-forks-v1`, design §4): `lake exe jaune --mainnet-schedule` against the extraction's `mainnet_schedule` and each available EELS module's `FORK_CRITERIA` from Byzantium (`ByBlockNumber` as `{"block": n}`, `ByTimestamp` as the bare number, `Unscheduled` as `null`; synthetic EIP-1283 `Constantinople`, which has no EELS module or mainnet activation, must print `null`). Originally U10 inspected twelve then-refused forks through `lake exe jaune --rules-literal <fork>`, which prints `Fork.ruleSet` without resolving it; that refusal context is historical. Today all 17 declared rule sets resolve through `--rules`. Across them, 228 cells are explicitly classified dormant and skipped rather than compared. Synthetic Constantinople's cells are all dormant because there is no independent EELS module; its executable record is not an oracle comparison. Every emitted field still requires a coverage classification, so dormant/no-oracle cells cannot silently become claimed comparisons | 1,234 comparisons across 17 runnable forks, no refused forks, 228 dormant cells classified, plus 17 mainnet-schedule rows | sub-second |
| `scripts/check-t8n.sh` | the `t8n` transition-tool frontend against goldens generated from the pinned conformance target: `result`, `alloc` and `body` byte-identical per case, each case run twice for determinism, every golden's digest checked against `scripts/t8n/provenance.json`. The original Amsterdam half is the Appendix-F 15-by-2 scenario/mode matrix; ten additional authored cases cover storage-only creation/deletion across the five authored forks because the release skipped those upstream tests. Five further authored cases compare zero-value transaction, CALL and STATICCALL storage preservation against pinned EELS. All are compared byte-for-byte including the EIP-7928 `blockAccessList`/`blockAccessListHash` pair the tool now emits (the former target-only deviation entries are gone; the registry has no field exemptions and keeps four message-normalization rows, the `INTRINSIC_GAS_TOO_LOW` row carrying its owner and date). Twenty-two historical cases comprise eleven transfers, the Berlin SELFDESTRUCT case, seven per-fork ommer cases and three Muir difficulty cases (see the t8n README). All 76 registered cases conform; `scripts/t8n/expected-refusals.json` contains no refusal entries. Synthetic EIP-1283 Constantinople has no pinned-target golden. With no field exemptions registered, `--red-test` additionally corrupts one conforming case's `stateRoot` in a scratch copy and requires rejection, proving the comparison bites | 76 conforming cases, no registered refusals | Historical: 6.6 s on the smaller 2026-09-21 corpus; not a measurement of these cases |
| `scripts/check-jumpdest.sh` | the sampled half of the jumpdest claim. **Definitional identity** (`Jaune/Machine.lean`): at the v21 pin, `pinnedJumpDestsFrom` aliases the legacy forward walk (EELS #3618); `pinnedJumpDestsFrom_eq_legacy` is `rfl` and its equality has no sampled duplicate. **Sampled, not proved**: the bridge from either walk to Jaune's own `jumpable`/`noPushBefore` scan (`jumpable cd k ↔ k ∈ legacyJumpDestsFrom cd 0`), which this gate checks on nine 64 KiB pseudo-random blobs (fixed seeds, EIP-7954's raised ceiling), with per-phase timings forced before each clock read (`jaune --jumpdest-control <seed> 1 65536`). The seed list omits seven measured seeds on which `jumpable` does not finish inside 45 s at 64 KiB (a cost artifact — goal C's review ran them at 8 and 16 KiB and found agreement); re-implementing `jumpable` on the walk is packet P2, reserved to the owner. A falsifier for the sampled half, run as well as the theorem, never instead of it | 9 blobs × 65,536 bytes | ~7 s |
| `scripts/check-memory-probe.sh` | that a 1,000,000-byte call input driven through a 1,024-deep call path does not retain one calldata copy per frame, for **both** call families. Runs `jaune-memory-probe --staticcall 1024 1000000` and `--call 1024 1000000` and asserts each child's peak resident set against a fixed budget. **Peak mechanism:** `getrusage(RUSAGE_CHILDREN).ru_maxrss` (kibibytes on Linux, bytes on macOS, converted by `scripts/memory_probe_budget.py`), bounded by a sampling watchdog that kills a child crossing the budget — `/proc/<pid>/statm` on Linux, `ps -o rss=` elsewhere. **No cgroup, container, privilege, platform or memory-size dependency**: this is the portable form of the assertion, and it is what makes the regression enforceable on an ordinary developer machine rather than only on a 16 GB Linux host. The cgroup collector `scripts/measure-resource.py` remains the instrument for the Linux resource-acceptance rows, which do need Linux. Needs the built binary and no corpus, like `check-cli.sh`; takes no lock and writes nothing under the repository. Losing the property costs about 32 MB per live frame, so it crosses this budget by depth 8 — a mutant that removes the `@[csimp]` substitution turns this row red at the assertion and restores green when reverted | 2 points, 256 MiB asserted peak (measured ~104 MiB, ~2.5x margin) | ~0.3 s |
| `python3 scripts/check-legacy-exception-aliases.py` | that every row of `FixtureException.legacyAliases` -- the retesteth token (`TR_IntrinsicGas`, ...) the `legacytests` restoration tree expects, mapped to a canonical expectation -- is attested by upstream's own rename or the accepted definitional exception: re-derived from the same test, case and block in the later ethereum/tests tree under `execution-specs` (at Cancun, or the Cancun sibling of a case at another fork when that case has no same-fork pair), failing on a non-definitional row no agreeing pair attests, on a set-valued row one of whose members no pair names, on a contradicting pair of either kind, and on a row whose target the source's own vocabulary (its `toString` and `ofString?` arms) does not parse; a sibling pair that names a post-merge identity for a pre-Paris case, or the fee-market identity for a pre-London case, is explained by the fork difference and attests nothing (U11d, review U11a #1); the accepted `TR_RLP_WRONGVALUE` row is definitional because upstream never converted its block tests: its `DEFINITIONAL` listing requires the exact canonical value, an occurrence in the restoration tree, every occurrence's `hasBigInt` marker, and no upstream pair of either kind (U11c); the vocabulary check applies to this row too. Tokens with no row are noted, not failed (the runner refuses them at parse). Needs no build, takes no lock (goal U11a). Negative controls: moving `TR_NoFunds` to `INTRINSIC_GAS_TOO_LOW` turns it red at that row (U11a work record); dropping the pre-Paris explanation turns 16 rows red at their sibling pairs, and renaming one `toString` arm turns the three rows naming it red at the vocabulary check (U11d work record); moving `TR_RLP_WRONGVALUE`'s value, emptying its `DEFINITIONAL` entry, and flipping its marker each turn it red, with restored bytes identical (U11c work record). Integration controls exercise sibling contradictions despite same-fork agreement, unattested set members, vocabulary refusal including the definitional row, missing/changed definitional identity or marker, and newly appearing pairs | pair-attested rows plus the accepted definitional row | ~7 s |
| `scripts/check-u256.sh` | differential word/hash oracle | 21,593 cases | sub-second |
| `scripts/check-fake-exp.sh` | fake-exponential differential oracle vs the pinned EELS `taylor_exponential` (blob base fee) | 240 cases | sub-second |
| `scripts/check-legacy.sh --patch` | the ten historical FAIL files, fixed all-PASS target | 10 | sub-second |
| `scripts/check-legacy.sh --rlp4` | four invalid-RLP/header files, subset of `--patch` | 4 | sub-second |
| `scripts/check-mainnet.sh --suite smoke` | current-mainnet smoke | 16 | sub-second |
| `scripts/check-legacy.sh --depth` | fuel/call-depth stress set | 67 | ~13 s |
| `python3 scripts/check-legacy-baseline.py self-test` | tracked correctness / ignored timing separation, timing genesis/new-fixture extension, refresh refusal, rebase isolation, drift, duplicate rejection, and host-local dispatch weights | 11 controls | sub-second |
| `python3 -m unittest discover -s scripts/tests` | harness/generator unit tests. **This suite must stay lock-free**: it is a light row that runs while anything else on the host may hold the host-global heavy-gate lock, so no test here may shell out to a suite that takes it (`osaka`, `prague`, `full`, `amsterdam`, `amsterdam-full`, and the historical static suites) against the real `$HOME`; the heavy-suite dispatches, the synthetic `amsterdam-full` union, the synthetic historical lane and the synthetic legacy tier selection, run with `$HOME` pointed at a private directory, so the lock path `gate-lock.sh` derives from it is the test's own | harness, generator, reference, correction and clock tests; the suite reports the collected total | Historical: 16.2 s on 213 tests (2026-09-21 catalogue) |
| `scripts/check-mainnet.sh --lane amsterdam --suite amsterdam-smoke` | Amsterdam release smoke (16 lowest SHA-256 ranks of the static suite) | 16 files / 85 cases | Historical devnet corpus: 14.7 s wall, ~4 s of it fixtures (2026-09-21 catalogue); not a v21 measurement |
| `scripts/check-mainnet.sh --lane amsterdam --dir for_amsterdam/amsterdam/<subtree> --suite amsterdam` | one `eip*` subtree of the release corpus, all-PASS, count-checked against the manifest | manifest-selected subtree | 0.2 s – 110 s (`eip8037_*` is the slow one) |
| `scripts/check-mainnet.sh --suite transitions` | fork-transition validity | 16 files / 115 cases | Historical: 18.0 s on the 2026-09-21 corpus; not a v21 measurement |

### Medium — before a commit or push candidate

The standalone tracer also has a cheap native gate, `python3 scripts/check-trace.py`
(optional `--binary PATH`). It requires the built `jaune-trace` default target,
takes no lock and writes only a temporary directory. It checks instruction
observations, frame identity, nested/refunded rollback observations, zero-step
frames, unavailable exceptional gas cost, byte/instruction limits and CLI
refusals. Transaction controls additionally cover settled summary scope, typed
wire identity, authorization refunds, rejection metadata and real write failure. It does not duplicate the trace driver's execution-erasure theorem.
Usage and the message-versus-transaction boundary are in
[`TRACE_PRODUCTION.md`](TRACE_PRODUCTION.md).

| gate | proves | scale | time |
|---|---|---|---|
| `scripts/check-legacy.sh --smoke` | broad conformance vs baseline | 174 classifications | 79.9 s at `--jobs auto` (3 jobs, 2026-09-21 catalogue) |
| `scripts/check-legacy.sh --bls` | BLS12-381 + point-evaluation vs hand-authored target baseline. **Unique protection:** it is CI's only BLS12-381/point-evaluation conformance (the nightly job); the mainnet suites carry the same EIP-2537/EIP-4844 modules from a newer release but run only locally | 29 | 76.0 s at `--jobs auto` (3 jobs, 2026-09-21 catalogue); 171.9 s summed per-file, sequential, 2026-08-25 host-local report (pre-4.34) |
| `scripts/check-ec.sh` | EC differential oracle (pinned, differential, identity cases) | — | 11.6 s including compiling its Lean checker (2026-09-21 catalogue) |
| `scripts/check-vectors.sh` | generated vector conformance + controls + declared-case-count coverage | 53 files, 1,990 cases, 5 controls | ~7.8 min; **~1.5 min at `--jobs 10`**; 197.8 s at `--jobs auto` (2026-09-21 catalogue); `auto` is resource-dependent |
| `scripts/check-elab.sh` | per-module elaboration time vs the ignored host-local `scripts/baseline-elab.txt` (auto-initialized on first run) | 41 modules, discovered from the default targets | 170.898 s genesis on the readiness host (2026-10-11); no historical timing comparison |
| `lake build && scripts/check.sh --no-build` in the Blanc checkout carrying the candidate pin | that a Jaune change has not broken its downstream consumer: Blanc's integration elaboration and its axiom audit. **The cheapest Blanc-side falsifier after a pin bump** — the rest of Blanc's set is catalogued in Blanc's own file | count-free here; use Blanc's gate summaries | current Blanc catalogue |

### Long sequentially — but mostly not long in parallel

| gate | proves | scale | sequential | `--jobs auto` |
|---|---|---|---|---|
| `scripts/check-mainnet.sh --suite osaka` | strict all-PASS | 2,333 | ~8 min | **231.0 s** (2026-09-21 catalogue) |
| `scripts/check-mainnet.sh --suite prague` | strict all-PASS | 2,341 | ~12 min | **341.7 s** (2026-09-21 catalogue) |
| `scripts/check-mainnet.sh --suite full` | strict all-PASS, whole manifest; **supersedes `osaka`, `prague`, `bpo1`, `bpo2`, `transitions` and `smoke` in a closure bundle** | 4,712 | ~20.8 min | **618.9 s** (2026-09-21 catalogue) |
| `scripts/check-mainnet.sh --lane historical --suite hist-full` | strict all-PASS over every historical suite and `hist-transitions`; **supersedes its declared `component_suites` (the eight nonempty fork suites and `hist-transitions`) in a closure bundle** | 3,550 | not measured | not measured |
| `scripts/check-mainnet.sh --lane amsterdam --suite amsterdam` | strict all-PASS over the static Amsterdam corpus, zero exclusions inside `for_amsterdam` | 3,180 | not measured; run it parallel | **454.5 s** (2026-09-21 catalogue; 267 s at `--jobs 6`, 2026-09-06) |
| `scripts/check-mainnet.sh --lane amsterdam --suite amsterdam-full` | the union of `amsterdam` and `amsterdam-transitions`; strict all-PASS with the exact registered `bal-header-format-v1` correction; **supersedes both, and `amsterdam-smoke`, in a closure bundle** | 3,239 | not measured; run it parallel | **463.6 s** (2026-09-21 catalogue, a run RED on exactly DP-1's four files) |
| `scripts/check-legacy.sh --full` | every legacy fixture vs baseline; **supersedes `--smoke`, `--depth`, `--patch` and `--rlp4` in a closure bundle** | 2,983 | **≥ 19 min** | **501.3 s** at 4 jobs (2026-09-21 catalogue) |

The scales above describe `tests@v21.0.2`. Dated 2026-09-21 runtime cells
are historical: mainnet used `tests@v20.0.1` (5,100 files for `full`), while
Amsterdam used the former devnet release. They are not timings for v21.0.2.
Admission uses the expected runtime of the actual command and host.

**Read the two legacy `--full` cells differently — they have different
provenances.** The parallel cell is a measured wall time: 501.3 s at `--jobs auto`
(4 jobs), 2026-09-21; it was 462 s at 10 jobs on 2026-07-31. The sequential cell is **not** a measured wall time; it is
1,145.8 s of *summed per-file fixture time* from the catalogue host's historical
measurement, which is a **lower bound** on wall time — a sequential run also pays
2,983 process spawns plus harness overhead on top. Treat it as "at least 19
min". Before the BLAKE2b unboxing the corresponding figures were ≥ 3,338 s
summed and ~900 s measured.

Judge the 1,000-second deferral threshold against the gate as you will actually
run it. At `--jobs auto` every row above comes in under it — legacy `--full`
lands near ~460 s, latency-bound by one indivisible fixture that parallelism
cannot touch — so all of them run inline rather than deferred by reflex.
**A sequential legacy `check-legacy.sh --full` remains above the threshold and still
requires explicit authorization**: its lower bound alone, 1,145.8 s, exceeds
1,000 s. A sequential run is still called for only when its per-file timings are
themselves the evidence.

**The BLAKE2b unboxing changed no deferral status.** The parallel run was already
under the threshold before it (~900 s) and the sequential run was already above
it; the arc made both faster without moving either across the line.

The two `--full` gates are the exact-candidate closure pair. **Neither may be
replaced by its smoke tier.**

**In a closure bundle a superset replaces its components; it never runs beside
them.** When a candidate owes the whole catalogue (goal closure, a review
bundle, a toolchain migration), run `check-mainnet.sh --suite full`, not also
`--suite osaka`, `prague`, `bpo1`, `bpo2`, `transitions` or `smoke`; run
`--lane amsterdam --suite amsterdam-full`, not also `amsterdam`,
`amsterdam-transitions` or `amsterdam-smoke`; and run `check-legacy.sh --full`,
not also `--smoke`, `--depth`, `--patch` or `--rlp4`. Each superset runs every
file of its components under a pass rule at least as strict: `full` and
`amsterdam-full` are their manifests' declared unions (`component_suites`),
every `--smoke` and `--depth` baseline line is identical in
`baseline-full.txt`, and every `--patch`/`--rlp4` file is `PASS` there. Running
both bought ~1,155 s of repeated files and no protection in the 2026-09-21
catalogue. The legacy premise (baseline lines identical, patch/rlp4 files
`PASS`) was verified by inspection at `69fb6b6` and must be re-verified on any
`--rebase` of `baseline-full.txt`. The subsets stay available, and remain the
right tools, for iterating.

### Readiness measurements (2026-10-11)

WSL2 Linux, Lean 4.34.0, candidate `ea74b79` (semantic source `af9a705`),
14 GiB memory-high / 16 GiB maximum / zero-swap containment. These are measured
command wall times, including harness work; parallel fixture timings are
reference-only. Read-only archive verification overlapped the mainnet run.

| command | scale | wall seconds | raw verdict |
|---|---|---:|---|
| `check-mainnet.sh --suite full --no-build --jobs 6` | 4,968 files / 34,449 cases | 469.788 | PASS |
| `check-t8n.sh --red-test` | 49 cases + 3 controls | 10.283 | PASS |
| `check-jumpdest.sh` | 9 × 65,536-byte blobs | 7.194 | PASS |
| `check-memory-probe.sh` | both call families, 256 MiB budget | 0.461 | PASS |
| `python3 -m unittest discover -s scripts/tests` | 219 tests | 5.059 | PASS |
| `check-ec.sh` | differential oracle including checker compilation | 26.585 | PASS |

Pre-review semantic candidate `e8ce266` on the same host and containment, with
one heavy gate at a time. These historical measurements precede the zero-value
entry repair; they are not that repair's validation verdicts:

| command | scale | wall seconds | raw verdict |
|---|---|---:|---|
| `check-mainnet.sh --suite full --no-build --jobs 6` | 4,968 files / 34,449 cases | 428.241 | PASS |
| `check-mainnet.sh --lane amsterdam --suite amsterdam-full --no-build --jobs 6` | 3,354 files / 26,587 declared cases | 293.605 | RED, exactly four DP-1 findings |
| `check-legacy.sh --full --no-build --jobs 6` | 2,983 files | 666.775 | RED, exactly five owner-approved classification changes |
| `check-legacy.sh --bls --no-build --jobs 6` | 29 files | 66.158 | PASS |
| `check-vectors.sh --jobs 6` | 53 files / 1,990 cases / 5 controls | 93.044 | PASS |
| `check-elab.sh --no-build` after the owned warm full build | 41 modules | 170.898 | PASS, host-local baseline genesis only |

The host's single compilation owner supplies elab's warm-build precondition
through the owned wrapper immediately before the gate. No historical timing
comparison is claimed. The actual first discovered module was `Examples.lean`:
its cold first row was 5.560 s, and the required isolated repeat was 1.497 s.
The repeat is the accepted warm observation; the generated baseline's initial
row remains unchanged and must not be presented as a warm reference. No
baseline was copied, hand-edited or rebased.

### The Amsterdam lane

`check-mainnet.sh` takes `--lane (mainnet|amsterdam|historical)`. All three lanes now pin
`tests@v21.0.2`, EELS `e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e`, and default
to `~/eest-mainnet-v21.0.2`. The `t8n` conformance target is that same commit,
which carries ethereum/execution-specs#3849 and #3361; both
generators refuse a target checkout that does not descend from the lanes'
release (`conformance_target.fixture_release_commit` in `scripts/sources.json`). Their suite namespaces, generated manifests and
environment overrides remain separate. The manifest generator validates the
release index and every selected file's `content_sha256`; changed counts or
bytes fail `--check`. Empty or miscounted `--dir` selections fail before a run.

| suite | selection | files / cases | pass rule |
|---|---|---:|---|
| `amsterdam` | static `Amsterdam` under `for_amsterdam` | 3,180 / 26,349 | all-PASS, zero exclusions; heavy lock |
| `amsterdam-smoke` | 16 lowest SHA-256 ranks of `release_commit:path` in static | 16 / 85 | all-PASS; no lock |
| `amsterdam-transitions` | `BPO2ToAmsterdamAtTime15k`, rules selected per block timestamp | 59 / 193 | strict all-PASS with the registered correction below; zero exclusions; no lock when sequential |
| `amsterdam-full` | union of static and transitions | 3,239 / 26,542 | strict all-PASS with the registered correction below; heavy lock |

The official v21.0.2 archive is preserved unchanged. Its full run reports
3,237 PASS and two FAIL, the same two found in v21.0.1: under
`for_bpo2toamsterdamattime15k/amsterdam/eip7928_block_level_access_lists/fork_transition/`,
`invalid_post_fork_block_without_bal_hash_field.json` and
`invalid_pre_fork_block_with_bal_hash_field.json`. Their raw 22-field headers
are structurally invalid; the original raw expectations name `INVALID_BAL_HASH`
and `INVALID_BLOCK_HASH`, respectively. The earlier four-failure DP-1 result
also included the two slot-number files under `eip7843_slotnum`; the repair
now reports their expected `INCORRECT_BLOCK_FORMAT`. Those earlier results
remain historical, not current four-file failures.

The explicitly approved `bal-header-format-v1` package changes only the two
BAL raw expectations to `INCORRECT_BLOCK_FORMAT` plus generation metadata.
It preserves the raw block bytes, prestate/poststate, Engine payloads and
Engine expectations. The official base remains independently verified,
including both replaced paths. Upstream did not change these two tests in
v21.0.2 (the source is blob `e92eac80` at both releases), so the package was
re-derived against the new base through its registered packager, from the same
source patch. With that exact separate overlay, the strict `amsterdam-full` gate
passes all 26,542 cases (3,239 files), and the transition subset passes all 59. Registration/source provenance and archive/index hashes
are in `scripts/amsterdam/corrections/bal-header-format-v1/`; this is a local
registered correction, not a corrected official release. No exclusion or
exception alias was introduced. DP-2's `SYSTEM_CONTRACT_EMPTY` identity is
implemented and its deployment fixtures pass.

The lane's parser, suite derivation, admission and dispatch, empty selections
and manifest-drift controls are in `scripts/tests/test_amsterdam_lane.py`.
Suite names remain disjoint, so a mistyped lane does not silently select the
other lane's corpus. Historical devnet timings are retained in dated table
cells above and must not be presented as current-release measurements.

The explicit fixture-correction mechanism is active for Amsterdam through
the approved `bal-header-format-v1` registration in `scripts/sources.json`.
Without such an exact registration it is inactive. Its verifier
is `scripts/fixture_corrections.py`; its bounded packager is
`scripts/gen-amsterdam-fixture-correction.py`. Packaging accepted generated
bytes is distinct from authorizing their adoption. Registration preserves the
official base archive/index and verifies a separate correction archive, index,
source patch and portable generation receipt. Setup uses
`python3 scripts/fixture_corrections.py install --lane amsterdam --base-root PATH`;
missing or invalid setup is refused, with no fallback to old fixture bytes.
The extended doctor still deep-compares every official base file, including
paths with replacements. An active correction produces an explicitly composite
Amsterdam manifest; other lane manifests and logical selections retain their
existing identities. Both dispatch modes use the same verified mapping and
NUL-delimited argument transport. Each run retains its input receipt under
`.lake/fixture-input-receipts/` and checks it, source/index identities and
selected input hashes again before accepting a passing aggregate. The verdict
names an active correction's ID and archive/index digests. Small package,
semantic-delta, routing and post-run controls are in
`scripts/tests/test_fixture_corrections.py`. This mechanism changes neither the
recorded original-release results above nor the all-PASS rule; any further
correction adoption remains a separate reserved corpus/reference decision.
After adoption, the packager's `--check` accepts the unchanged active source
lock only when `--output` is the exact registered package directory and its
registration, package and base release match. It reproduces packaging from the
accepted `--experiment-receipt` and `--base-root` inputs; it does not rerun EELS.
Normal package installation/verification and fixture dispatch need only the
portable committed package and official base, not the experiment checkout or
its detailed private evidence. New proposal generation still requires an
inactive pointer.

### The historical lane (goal U10)

One suite per pre-Prague fork over the same v21 release, strict all-PASS,
plus the transition fixtures: `byzantium`, `constantinople`,
`constantinoplefix` (Petersburg's fixture label), `petersburg`, `istanbul`,
`muirglacier`, `berlin`, `london`, `arrowglacier`, `grayglacier`, `paris`,
`shanghai`, `cancun`, `hist-smoke` (drawn from Cancun), `hist-transitions`
(`ParisToShanghaiAtTime15k`, `ShanghaiToCancunAtTime15k`,
`CancunToPragueAtTime15k`, whose Prague endpoint the mainnet lane owns) and
the union `hist-full`, inventoried in `scripts/historical/manifests.json`.
No case in this lane declares a blob schedule, so none is required. All
17 declared forks now resolve. The historical EEST union is strict all-PASS:
39,212 cases in 3,550 files, including all 24 transition files. There are no
static EEST inputs for synthetic EIP-1283 `constantinople`, Muir Glacier,
Arrow Glacier or Gray Glacier; empty suites are refused, not vacuously green.
Petersburg's nonempty EEST suite is named `constantinoplefix`; use that label.
Lane controls are in `scripts/tests/test_historical_lane.py`.

Historical legacy tiers use the separate pinned `legacytests` restoration,
not the ordinary Prague corpus. Nine `--hist-<fork>` tiers have tracked
`baseline-hist-<fork>.txt` correctness baselines: Byzantium, Constantinople,
Petersburg, Istanbul, Berlin, London, Paris, Shanghai and Cancun. They compare
ordered selected file classifications with their exact per-tier baselines;
a matching gate can be green while containing recorded FAIL rows. Those
rows are fixture or reference artifacts, each reviewed per row in the
categories below, not Jaune defects found by the tier; strict EEST
conformance for those forks is the historical lane's 100%, above. The seven
new baselines were generated by the registered helper from accepted complete
reports under the owner's bounded naming/order authority; Shanghai/Cancun's
existing baselines remain unchanged. No blanket network-wide waiver follows.
Transition memberships retain their exact selected network labels; historical
tiers do not substitute for strict historical EEST conformance.

The reader selects exact `expectException`, `expectExceptionALL` or the
original case-network suffix and refuses conflicting/non-string applicable
fields. Foreign suffixes alone grant no expected-invalid permission. Aliases
and error scoring are unchanged. Each accepted FAIL retains its original
wire/predicate/final-state review and its qualifications: multiply-invalid
ordering is not a universal alias; seals are NoProof; synthetic Constantinople
has no independent EELS oracle; the accepted London activation-gas correction
and reconstructed TTD lineage are not general reference-equivalence claims.
Earlier dated U11 refusal and partial-run results remain historical evidence.

The bomb-only forks' finite evidence is `scripts/check-difficulty-vectors.sh`:
nine authored boundary vectors (below, at, and above each of the 9M, 10.7M
and 11.4M delays) compared against the pinned target's
`calculate_block_difficulty` per fork module. No theorem states that
function. Inputs are bound by parameter name, so a renamed parameter fails
loudly.

### Blanc's gates

Blanc is Jaune's downstream consumer, and its gates are catalogued in **its own
repository**: `~/blanc/scripts/GATES.md`. That file is authoritative for their
commands, scale, pass criteria, and lock behavior; do not restate them here.

What belongs in *this* file is the one selection rule that is a Jaune concern:

**After a change Blanc consumes — or any bump of Blanc's pinned Jaune
revision — the cheapest Blanc-side falsifier is**

```
cd <the Blanc checkout carrying the candidate pin> && lake build && scripts/check.sh --no-build
```

run in the Blanc goal worktree during goal work, in `~/blanc` otherwise,

**and a green result there is not a substitute for Blanc's full set**, which
that repository's catalogue defines and which the pin bump's own checkpoint
owes. Blanc pins Jaune by commit, so nothing in Blanc moves until someone moves
the pin: a red Jaune tree cannot silently break Blanc, and a green Blanc does
not vouch for Jaune.

### The consensus lane (goal `jaune-consensus-electra-fulu-v1`, in progress)

The consensus conformance runner is the `jaune-consensus` executable (`ConsensusMain.lean`,
harness under `JauneConsensus/Harness/`). It reads the extracted `ethereum/consensus-specs`
`v1.7.0-beta.4` vectors (default `$HOME/consensus-spec-tests-v1.7.0-beta.4/extracted`, override
with `--vectors`) and trusts them only as far as they match the committed, generated
`scripts/consensus-vectors.json` and `scripts/consensus/inventory-v1.7.0-beta.4.json`.
**Two-release split for the general preset** (master decision, goal
`eip8282-gloas-cross-layer-v1` W1-a, 2026-11-10): beta.4's `general.tar.gz` holds only the 20
altair `bls` cases, with no `ssz_generic` and no `kzg`, so the general-preset rows stay on the
`v1.6.1` general tarball, recorded as the second, general-only provenance entry `general` in
`scripts/consensus-vectors.json`; `--preset general` defaults to
`$HOME/consensus-spec-tests-v1.6.1/extracted`. No general row was dropped. The inventory also
records beta.4's `comptests` tarball (`minimal`-preset `fork_choice_compliance`, extracted to
`<root>/comptests/`), whose non-case members (`tests/core/`, `tests/formats/`,
`tests/generators/`, 576 files) are skipped and counted; `--preset comptests` runs it (the `fork_choice_compliance` row). Run from the
repository root after an owned build of `jaune-consensus`. It takes no lock and writes nothing;
the heaviest runner measured is `operations` at mainnet Gloas, about 600 MB peak RSS (599 MB;
`fork_choice` about 240 MB), and the whole lane run with about 21 runners concurrent peaked at
2.27 GiB (DRY discovery run at `0bcd72c4`, WSL, 2026-11-10). The `run` banner names the release
of the preset's own provenance entry: `--preset general` prints `v1.6.1` (the general-only entry).
Up to `0bcd72c4` it printed `v1.7.0-beta.4` although the general vectors were `v1.6.1`.

| gate | proves | scale | time |
|---|---|---|---|
| `.lake/build/bin/jaune-consensus run --preset general --runner ssz_generic` | each `valid` case decodes, equals `value.yaml`, re-encodes to `serialized` and has the `meta.yaml` root; each `invalid` case fails to decode (`Harness/SszGeneric.lean`), strict all-PASS, after the tree check below | 5,145 phase0 cases (2,708 valid, 2,437 invalid, 10 handlers) | 147.7 s (closure tier, both forks, BLS on, eight runners concurrent (WSL, 2026-11-09, binary 5c1992d)) |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner ssz_static` | each case's `serialized` decodes to the container at the case's preset and fork, re-encodes to itself, equals `value.yaml` and has the `roots.yaml` root (`Harness/SszStatic.lean`), strict all-PASS, after the tree check below. `F` is `electra`, `fulu` or `gloas`: Gloas is accepted for this container-only runner alone (`containerOnlyRunners`), with the Gloas containers of `JauneConsensus/ContainersGloas.lean` (EIP-7688 progressive containers and lists, on `eth-ssz-specs==0.1.0`'s right-leaning `merkleize_progressive`; `SSZ/Progressive.lean` keeps `v1.6.1`'s left-leaning one for `ssz_generic`). Control (2026-11-10): see the Gloas `ssz_static` paragraph below the table | `v1.7.0-beta.4`: minimal 6,765 + 7,380 + 8,979, mainnet 275 + 300 + 365 (Electra + Fulu + Gloas; Gloas 73 types) | minimal 22.3 s / 27.2 s / 14.9 s, mainnet 9.8 s / 9.5 s / 8.4 s (Electra / Fulu / Gloas, one process at a time, WSL, 2026-11-10) |
| `.lake/build/bin/jaune-consensus run --preset minimal --runner shuffling` / `--preset mainnet` | `compute_shuffled_index` for every index of every case, strict all-PASS, after the tree check below | 300 + 300 cases | 16.1 s / 145.3 s (WSL, 2026-11-09; 17.7 s / 155.6 s after the move to checked `U64`); 30.7 s / 270.7 s (beta.4, WSL, 2026-11-10, binary 5666b17f, 25 runners per preset concurrent, BLS on) |
| `.lake/build/bin/jaune-consensus run --preset general --runner bls` | `eth_aggregate_pubkeys`: `input` aggregates to `output` (`null` exactly where the model raises); `eth_fast_aggregate_verify`: the verification bit equals `output` (`Harness/Runner.lean`), strict all-PASS, after the tree check below | 20 cases (8 + 12) | 1.9 s (closure tier, both forks, BLS on, eight runners concurrent (WSL, 2026-11-09, binary 5c1992d)) |
| `.lake/build/bin/jaune-consensus scan --preset general`; `scan --preset P --fork F` for `F` in `phase0` (`shuffling`), `electra`, `fulu`; `scan --preset comptests --fork F` for `F` in `electra`, `fulu`; `scan --preset P --fork gloas --runner R` for `R` in `gloasRunners` (`ssz_static`, `epoch_processing`, `rewards`, `operations`, `networking`, `light_client`, `fork`, `sanity`, `random`, `finality`, `transition`) | the tree check over every in-scope suite of the selection, then the readers: every `.ssz_snappy` decodes, every `.yaml` is inside the accepted subset, and the 48 `ssz_generic/uints/valid` serializations decode to the little-endian encoding of their `value.yaml` (an independent oracle for the Snappy decoder). The bare `scan --preset minimal` / `mainnet` / `comptests` (and `--fork gloas` without an admitted runner) refuses (`gloas is declared ... fails closed`) until the Gloas `fork_choice`, `fast_confirmation` and `comptests` suites are admitted (the Mac's M4/M5); restore the bare form then | general 5,509; minimal `phase0` 300, Electra 7,969, Fulu 8,596, Gloas 10,186 over the eleven runners (`ssz_static` 8,979, `operations` 463, `networking` 311, `epoch_processing` 172, `sanity` 113, `rewards` 46, `fork` 37, `transition` 34, `random` 16, `light_client` 10, `finality` 5); mainnet `phase0` 300, Electra 1,188, Fulu 1,224, Gloas 1,484 (`ssz_static` 365, `operations` 421, `networking` 312, `epoch_processing` 154, `sanity` 98, `rewards` 46, `fork` 35, `transition` 28, `random` 16, `light_client` 4, `finality` 5); comptests Electra 1,472, Fulu 1,472 | general 15.2 s; minimal Electra 4.5 s, Fulu 4.5 s, `phase0` 0.2 s, Gloas 3.2 s summed over its runners; mainnet Electra 15.5 s, Fulu 14.3 s, `phase0` 0.2 s, Gloas 21.1 s summed; comptests 9.4 s / 8.9 s (WSL, 2026-11-10, binary `0bcd72c4`, one process at a time) |
| `.lake/build/bin/jaune-consensus --bench-hash-pair N` | times `N` pair hashes three ways (Jaune's `Bytes.sha256` on the 64-byte list, `hashPairKernel`, `hashPair` in `JauneConsensus/Crypto/Sha256Pair.lean`) over the same pseudo-random inputs and requires all three to agree on every input (a differential run beside the theorem `hashPair_eq`); exit 1 on any disagreement | 200,000 pairs | 0.4 s per variant; `hashPair` 1.6-1.7 µs/pair against 2.9-3.0 µs for `Bytes.sha256`, both including about 0.8-0.95 µs of benchmark overhead (output bytes and loop), so about 0.8 µs against 2.0-2.1 µs for the hash itself (WSL, 2026-11-09) |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner operations` | each `<handler>` operation on `pre` gives `post` byte for byte, or rejects when the case has no `post`, under the case's `config.yaml` over its preset base (`Harness/Operations.lean`), strict all-PASS, after the tree check below | minimal 395 + 371; mainnet 359 + 335 (Electra + Fulu) | minimal 43.1 s / 37.5 s, mainnet 350.3 s / 199.3 s (Electra / Fulu) (beta.4, WSL, 2026-11-10, binary 5666b17f, 25 runners per preset concurrent, BLS on); before beta.4: minimal 84.4 s, mainnet 640.0 s (closure tier, both forks, BLS on, eight runners concurrent (WSL, 2026-11-09, binary 5c1992d)) |
| `.lake/build/bin/jaune-consensus run --preset P --fork gloas --runner operations` | every Gloas `operations/<handler>` on `pre` gives `post` byte for byte, or rejects when the case has no `post`, under the case's `config.yaml` over its preset base (goal `eip8282-gloas-cross-layer-v1`, U4: `JauneConsensus/GloasWithdrawals.lean`, `GloasOperations.lean`, `GloasBlock.lean`; harness `Harness/Operations.lean`, Gloas arms). The Gloas-only handlers are `execution_payload_bid`, `parent_execution_payload` (input `block`), `payload_attestation` (each case ships a `config.yaml`, `GLOAS_FORK_EPOCH: 0`), `builder_deposit_request`, `builder_exit_request` and `voluntary_exit_churn` (`process_voluntary_exit`); `attestation` reads its `parent_slot` input from `meta.yaml`; `withdrawals` has no input file (`process_withdrawals(state)`). BLS on except where `bls_setting` is 2 (the closure tier's setting). Strict all-PASS, after the tree check below. Control (2026-11-10, reverted, restored bytes identical by SHA-256): removing the `execution_address != source_address` check from `process_builder_exit_request` fails exactly `builder_exit_request/process_builder_exit_request__wrong_source_address` on both presets (PASS 6 FAIL 1 of 7, `post state differs`, exit 1); restoring gives 7/7 | minimal 463, mainnet 421 | minimal 147.9 s, mainnet 155.4 s (WSL, 2026-11-10, binary fa5a3c1c, one runner at a time, BLS on) |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner epoch_processing` | each `process_<handler>` sub-step from `pre` gives `post` byte for byte, or rejects when the case has no `post` (`JauneConsensus/Epoch.lean`, `EpochAccessors.lean`); `JAUNE_CONSENSUS_EPOCH_FULL=1` adds the diagnostic `pre_epoch → post_epoch` check of the whole `process_epoch`, which every case passes except the two `effective_balance_hysteresis` generators that edit the state after yielding `pre_epoch` | minimal 157 + 157, mainnet 142 + 142 (Electra + Fulu) | minimal 8.5 s / 8.8 s, mainnet 108.3 s / 113.7 s (beta.4, WSL, 2026-11-10, binary 5666b17f, 25 runners per preset concurrent, BLS on); before beta.4 minimal 6.2 s / 6.3 s, mainnet 52.6 s / 56.6 s (WSL, 2026-11-09) |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner rewards` | from `pre`, `get_flag_index_deltas` for the source, target and head flags and `get_inactivity_penalty_deltas` return exactly the recorded `Deltas` (handlers `basic`, `leak`, `random` and, from beta.4, `inactivity_scores`) | 46 per preset and fork, 184 in all | minimal 0.3 s / 0.2 s, mainnet 22.1 s / 24.9 s (Electra / Fulu) (beta.4, WSL, 2026-11-10, binary 5666b17f, 25 runners per preset concurrent, BLS on); before beta.4 minimal 0.7 s, mainnet 5.7 s per fork |
| `.lake/build/bin/jaune-consensus run --preset P --fork gloas --runner epoch_processing` | goal `eip8282-gloas-cross-layer-v1`, U3: each Gloas `process_<handler>` sub-step (`JauneConsensus/GloasEpoch.lean`, over `Gloas.BeaconState`, transcribed from `v1.7.0-beta.4` with the Gloas overrides of `GloasOps.lean`/`GloasMutators.lean`/`GloasEpochAccessors.lean`) from `pre` gives `post` byte for byte, or rejects when the case has no `post`, under the case's `config.yaml` over its preset base when it has one (the `ptc_window` case), strict all-PASS, after the tree check below. Every Gloas handler, including the Gloas-only `builder_pending_payments`, `ptc_window` and `pending_deposits_churn` (a file of `process_pending_deposits` cases). Gloas is admitted for this runner by `gloasRunners` (`Harness/Discovery.lean`). `JAUNE_CONSENSUS_EPOCH_FULL=1` (diagnostic): every minimal case also passes `pre_epoch → post_epoch` through the Gloas `process_epoch`. Control: see the Gloas epoch paragraph below the table | minimal 172, mainnet 154 | minimal 5.4 s (15.7 s with the full-epoch diagnostic), mainnet 158.5 s (one process, WSL, 2026-11-10) |
| `.lake/build/bin/jaune-consensus run --preset P --fork gloas --runner rewards` | U3: from a Gloas `pre`, the Gloas `get_flag_index_deltas` (source, target, head) and `get_inactivity_penalty_deltas` (`GloasEpochAccessors.lean`) return exactly the recorded `Deltas`, strict all-PASS, after the tree check below | 46 per preset, 92 in all | minimal 0.8 s, mainnet 7.8 s (WSL, 2026-11-10) |
| `.lake/build/bin/jaune-consensus run --preset P --fork gloas --runner fork` | goal `eip8282-gloas-cross-layer-v1`, U5: `upgrade_to_gloas` (`JauneConsensus/GloasUpgrade.lean`, `Gloas.upgradeToGloas`, transcribed from `specs/gloas/fork.md` at `v1.7.0-beta.4`: the field copy, `initialize_ptc_window`, then `onboard_builders_from_pending_deposits`) on the Fulu `pre` gives the Gloas `post` byte for byte, strict all-PASS, after the tree check below. Pending deposit signatures are verified under the case's `bls_setting` (BLS on unless 2). Control: see the Gloas fork paragraph below the table | minimal 37, mainnet 35 | minimal 16.4 s, mainnet 129.1 s (WSL, 2026-11-10, binary 22c4e32f, 30 runners concurrent, BLS on) |
| `.lake/build/bin/jaune-consensus run --preset P --fork gloas --runner sanity` | U5: `slots`: the Gloas `process_slots` (`JauneConsensus/GloasTransition.lean`, `Gloas.processSlots`: the Gloas `process_slot` clears the next slot's `execution_payload_availability` bit) from `pre` gives `post`; `blocks`: the Gloas `state_transition` (`Gloas.stateTransition`, over U3's `process_epoch` and U4's `process_block`) for each block gives `post`, or rejects when the case has no `post`; the five payload-attestation cases apply their `config.yaml` (`GLOAS_FORK_EPOCH: 0`). The cases carry blocks only: a parent's payload is applied inside the child's `process_block` (`process_parent_execution_payload`), so no envelope or engine step runs. Strict all-PASS, after the tree check below | minimal 113, mainnet 98 (17 `slots` per preset, the rest `blocks`) | minimal 273.3 s, mainnet 1,904.4 s (WSL, 2026-11-10, binary 22c4e32f, 30 runners concurrent, BLS on) |
| `.lake/build/bin/jaune-consensus run --preset P --fork gloas --runner random` / `--runner finality` | U5: the Gloas `state_transition` over the `blocks` gives `post` (`finality`: with its finalized checkpoint); every `random` case applies its `config.yaml`. Strict all-PASS, after the tree check below | `random` 16 per preset, `finality` 5 per preset | random minimal 551.1 s, mainnet 1,073.3 s; finality minimal 155.7 s, mainnet 713.6 s (WSL, 2026-11-10, binary 22c4e32f, 30 runners concurrent, BLS on) |
| `.lake/build/bin/jaune-consensus run --preset P --fork gloas --runner transition --handler core` | U5: Fulu → Gloas. The Fulu blocks up to `fork_block` on the Fulu `state_transition`; then `Gloas.crossFromFulu` (the Fulu `process_slots` to the first slot of `fork_epoch`, then `upgrade_to_gloas`); then the Gloas blocks, the one at the fork slot without `process_slots` (`Gloas.processBlockAtSlot`, as the generators' `do_fork` applies it). The run's `GLOAS_FORK_EPOCH` is the case's `fork_epoch` (the generators' `post_spec` sets it where `get_ptc` reads it, in `test_payload_attestations.py`; no other Gloas rule reads it), so `transition_accepts_gloas_payload_attestations` passes and `transition_rejects_pre_gloas_payload_attestation` rejects. Strict all-PASS, after the tree check below | minimal 34, mainnet 28 | minimal 334.0 s, mainnet 1,425.5 s (WSL, 2026-11-10, binary 22c4e32f, 30 runners concurrent, BLS on) |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner fork` | the upgrade `pre` (Deneb for Electra, Electra for Fulu) gives `post` byte for byte, or rejects when the case has no `post` (`Harness/StateTransition.lean`), strict all-PASS, after the tree check below | minimal 24 + 20; mainnet 22 + 18 (Electra + Fulu) | minimal 0.3 s / 2.4 s, mainnet 24.3 s / 65.5 s (Electra / Fulu) (beta.4, WSL, 2026-11-10, binary 5666b17f, 25 runners per preset concurrent, BLS on); before beta.4: minimal 1.8 s, mainnet 56.8 s (closure tier, both forks, BLS on, eight runners concurrent (WSL, 2026-11-09, binary 5c1992d)) |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner sanity --handler slots` / `--handler blocks` | `slots`: `pre` advanced by the empty slots gives `post`; `blocks`: `pre` through `blocks` gives `post`, or rejects when the case has no `post` (`Harness/StateTransition.lean`), strict all-PASS, after the tree check below | minimal 118 + 103; mainnet 106 + 91 (Electra + Fulu; `--handler slots` 15 per fork and preset, the rest `--handler blocks`) | blocks minimal 167.6 s / 154.4 s, mainnet 360.3 s / 287.4 s; slots minimal 4.2 s / 4.0 s, mainnet 715.5 s / 959.0 s (Electra / Fulu) (beta.4, WSL, 2026-11-10, binary 5666b17f, 25 runners per preset concurrent, BLS on); before beta.4: minimal 428.7 s, mainnet 1,966.4 s, both suites (closure tier, both forks, BLS on, eight runners concurrent (WSL, 2026-11-09, binary 5c1992d)) |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner finality` | the finalized checkpoint after the `blocks` run equals `post` (`Harness/StateTransition.lean`), strict all-PASS, after the tree check below | 5 per fork and preset, 20 in all | minimal 99.1 s / 95.1 s, mainnet 531.9 s / 502.7 s (Electra / Fulu) (beta.4, WSL, 2026-11-10, binary 5666b17f, 25 runners per preset concurrent, BLS on); before beta.4: minimal 230.3 s, mainnet 1,007.6 s (closure tier, both forks, BLS on, eight runners concurrent (WSL, 2026-11-09, binary 5c1992d)) |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner random` | `pre` through the random `blocks` gives `post` (`Harness/StateTransition.lean`), strict all-PASS, after the tree check below | 16 per fork and preset, 64 in all | minimal 365.1 s / 298.3 s, mainnet 784.2 s / 669.3 s (Electra / Fulu) (beta.4, WSL, 2026-11-10, binary 5666b17f, 25 runners per preset concurrent, BLS on); before beta.4: minimal 1,014.4 s, mainnet 1,374.3 s (closure tier, both forks, BLS on, eight runners concurrent (WSL, 2026-11-09, binary 5c1992d)) |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner transition --handler core` | `pre` through the multi-fork `blocks` (with `fork_epoch`, `fork_block` and `post_fork` from `meta.yaml`) gives `post` (`Harness/StateTransition.lean`), strict all-PASS, after the tree check below. Control (2026-11-10, beta.4, reverted, restored `Block.lean` SHA-256 identical): letting Fulu's `process_deposit_request` set `deposit_requests_start_index` again (the Electra behaviour, removed in beta.4's `specs/fulu/beacon-chain.md`) fails exactly minimal Fulu `transition_with_deposit_request_right_after_fork` at `block.state_root`, while Fulu `operations` (371) and `sanity` blocks (88) stay green; restored, 31/31 | minimal 33 + 31; mainnet 27 + 25 (Electra + Fulu) | minimal 243.6 s / 190.7 s, mainnet 1,169.2 s / 1,037.8 s (Electra / Fulu) (beta.4, WSL, 2026-11-10, binary 5666b17f, 25 runners per preset concurrent, BLS on); before beta.4: minimal 752.1 s, mainnet 2,386.7 s (closure tier, both forks, BLS on, eight runners concurrent (WSL, 2026-11-09, binary 5c1992d)) |
| `JAUNE_CONSENSUS_FC_BLS=0 .lake/build/bin/jaune-consensus run --preset P --fork F --runner fork_choice` | the store from `get_forkchoice_store(anchor_state, anchor_block)` through every `steps.yaml` step (`JauneConsensus/ForkChoice.lean`, `Sync.lean`, `Harness/ForkChoiceCases.lean`; the `v1.7.0-beta.4` fork choice: millisecond store, `ForkChoiceNode`, `get_attestation_score`, idempotent `on_block` with `record_block_timeliness` and `update_proposer_boost_root`, `is_proposer_equivocation`, Fulu `get_proposer_head` without shuffling stability): `on_tick(seconds_to_milliseconds(tick))`, `on_block` with its block's attestations and attester slashings (Deneb blob and Fulu `column_` data availability as `retrieve_blobs_and_proofs` / `retrieve_column_sidecars` oracles), `on_attestation`, `on_attester_slashing`; `valid: false` steps must reject; every `checks` key compared (`head`, `time`, `genesis_time` in seconds, both checkpoints, `proposer_boost_root`, `get_proposer_head`; `should_override_forkchoice_update` left the format at beta.4). Every case is `bls_setting` 0 (absent), so BLS may be off; without the variable signatures are verified. Control (2026-11-09, at `v1.6.1`, reverted, `consensus-preset-generate.py --check` matches and 56/56 restored): minimal `PROPOSER_SCORE_BOOST` 40 to 0 in `Config.lean` fails 12 of 56 minimal Electra cases by name at a `head` check (the three `ex_ante` cases, `get_head/proposer_boost_correct_head`, `shorter_chain_but_heavier_weight`, `discard_equivocations_slashed_validator_censoring`, both `justification_withholding` cases, four `reorg` cases); 40 to 20 fails none, so the vectors fix the boost only coarsely | minimal 56 + 68, mainnet 26 + 38 (Electra + Fulu) | BLS off, beta.4: minimal 22.6 s / 79.7 s, mainnet 63.2 s / 105.6 s (Electra / Fulu; Mac working time, 2026-11-10, two runner processes concurrent); at `v1.6.1`: minimal 25.5 s / 72.1 s, mainnet 83.0 s / 114.0 s (WSL, 2026-11-09, peak RSS about 240 MB). The closure tier reruns these suites with signature checks on; see the closure row |
| `JAUNE_CONSENSUS_FC_BLS=0 .lake/build/bin/jaune-consensus run --preset P --fork F --runner sync` | optimistic sync: the store through every `steps.yaml` step and the `sync` engine responses, with the optimistic head compared (`Harness/ForkChoiceCases.lean`), strict all-PASS, after the tree check below | 1 per fork and preset, 4 in all | BLS off, beta.4: minimal 0.1 s / 0.1 s, mainnet 1.9 s / 3.2 s (Electra / Fulu; Mac working time, 2026-11-10); at `v1.6.1` minimal 0.2 s / 0.1 s, mainnet 3.3 s / 5.0 s (WSL, 2026-11-09). The closure tier reruns these suites with signature checks on; see the closure row |
| `.lake/build/bin/jaune-consensus run --preset minimal --fork F --runner fast_confirmation` | the fast confirmation rule (`JauneConsensus/FastConfirmation.lean`, `specs/phase0/fast-confirmation.md` with `specs/bellatrix/fast-confirmation.md` at `v1.7.0-beta.4`) over the fork-choice steps of `fast_confirmation/<handler>` (`Harness/ForkChoiceCases.lean`, `tests/formats/fast_confirmation/README.md`). The format has no step for the handler: the generator runs `on_fast_confirmation` and then yields a checks step carrying the seven fast-confirmation keys, so such a step runs `on_fast_confirmation` (store from `get_fast_confirmation_store`, refreshed from the fork-choice store) first and then compares all its keys: the fork-choice keys and `previous_epoch_observed_justified_checkpoint`, `current_epoch_observed_justified_checkpoint`, `previous_epoch_greatest_unrealized_checkpoint`, `previous_slot_head`, `current_slot_head`, `confirmed_root`, `safe_execution_block_hash`; a step carrying only some of them fails. Every case is `bls_setting` 2, so BLS is off (at beta.4 pyspec still aggregates pubkeys with BLS off; two `is_one_confirmed` cases cross the minimal sync-committee period and pin that). Strict all-PASS, after the tree check below. Control (2026-11-10, Mac, disposable worktree `eip8282-fc-mutation` at the `M2` commit, reverted, restored bytes identical to that commit, whose binary is this row's green run): `COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR` 5 to 1000 in `FastConfirmation.lean` fails 16 of 184 minimal Electra cases by name at `confirmed_root` (among them `basic/fast_confirm_with_low_participation`, `basic/fast_confirm_with_asynchrony_at_epoch_boundary`, `empty_slots/fcr_empty_slot_at_epoch_boundary`, `empty_slots/fcr_handles_multiple_consecutive_empty_slots`, `is_one_confirmed/is_one_confirmed_epoch_crossing_block`, `previous_epoch/fcr_previous_epoch_002`, `reconfirmation/reconfirmation_passes_with_empty_slots_prior_first_block`); 5 to 0 fails none, so the vectors fix the adjustment only coarsely | minimal 184 + 184 (Electra + Fulu; 10 handlers: `basic` 3, `current_epoch` 22, `empty_slots` 5, `ffg` 2, `is_one_confirmed` 19, `previous_epoch` 108, `reconfirmation` 3, `restart_gu` 6, `revert_finality` 8, `variables` 8) | 93.1 s / 72.1 s (Electra / Fulu; Mac working time, 2026-11-10, two runner processes concurrent) |
| `.lake/build/bin/jaune-consensus run --preset comptests --fork F --runner fork_choice_compliance` | the beta.4 `comptests` tarball's `minimal`-preset fork-choice compliance suites (`block_tree_test`, `block_weight_test`, `shuffling_test`, `block_cover_test`, `attester_slashing_test`, `invalid_message_test`), which have no `tests/formats` entry. Each case runs as the reference runner `tests/generators/compliance_runners/fork_choice/runner/test_run.py` at the tag does (`Harness/ForkChoiceCases.lean`): the fork-choice steps, with an assertion rejection from a valid block's own attestations or attester slashings suppressed, a `valid: false` step required to fail with an assertion or index error, a `valid: false` `attester_slashing` step refused, and the extra check `viable_for_head_roots_and_weights` (the leaves of `get_filtered_node_tree` with their `get_weight`, compared as a set). `--preset comptests` reads `<root>/comptests/tests/minimal/...` (`Harness/Manifest.lean`, `casePresetOf`); the cases run at the `minimal` preset. Every case is `bls_setting` 2, so BLS is off. Strict all-PASS, after the tree check below. Control (2026-11-10, Mac, disposable worktree `eip8282-fc-mutation` with this row's harness, reverted, restored bytes identical to the committed `ForkChoice.lean`): `filter_node_tree`'s `voting_source.epoch + 2 >= current_epoch` changed to `+ 1` fails 24 of 192 Electra `block_cover_test` cases by name at a `head` check (all from the seeds `block_cover_test_16_260123816`, `_16_630180874`, `_17_229295563`, `_17_893087626`, `_20_307303224`, `_20_470471564`, `_21_126221261`, `_21_617130625`) | 1,472 + 1,472 (Electra + Fulu; per fork 512 `block_tree`, 256 `block_weight`, 256 `shuffling`, 192 `block_cover`, 128 `attester_slashing`, 128 `invalid_message`) | 2,059.6 s / 1,753.7 s (Electra / Fulu; Mac working time, 2026-11-10, the two forks concurrent beside other runners) |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner light_client` | `single_merkle_proof`: `is_valid_merkle_branch` against `hash_tree_root(object)` and `compute_merkle_proof(object, leaf_index) == branch` (`JauneConsensus/LightClientFullNode.lean`); `sync`: the light-client store over the steps (`LightClient.lean`); `update_ranking`: no later update ranks better; `data_collection` (minimal only): the generator's full-node collection (`Harness/LightClientDataCollection.lean`, transcribed from `helpers/light_client_data_collection.py`) over the state transition, every served bootstrap, update, finality and optimistic update checked by fork digest, file name and exact bytes; from beta.4 the generator advances a stored finalized-checkpoint state in `_get_current_sync_committee_for_finalized_period`, and the harness models that advance and its Python aliasing with `states`. Beta.4's `sync` meta names the store by `store_fork_version`: `ELECTRA_FORK_VERSION` for an Electra or Fulu store, or `GLOAS_FORK_VERSION` for a Gloas store (goal `eip8282-gloas-cross-layer-v1`, U7b: `JauneConsensus/GloasLightClient.lean`, `GloasLightClientFullNode.lean`); each object's type follows its fork digest, and a Gloas store takes Electra-format data through `upgrade_lc_*_to_gloas`, so the three Gloas-store cases `gloas_store_with_legacy_data` (Electra and Fulu) and `gloas_fork` (Fulu, with an `upgrade_store` step) now run. Controls (2026-11-09, reverted, restored bytes identical): never taking a better update in `_create_lc_update` fails both `data_collection` cases at step 3 (`best_updates`); `FINALIZED_CHECKPOINT_FIELD_INDEX` 20 to 21 fails `finality_root_merkle_proof` and `data_collection` | minimal 11 + 12, mainnet 4 + 4 (Electra + Fulu), all pass | minimal 73.5 s / 70.5 s, mainnet 1.3 s / 1.3 s with the Gloas-store cases (WSL, 2026-11-10, binary d9e18f43, one runner at a time, BLS on); minimal 95.1 s / 93.8 s, mainnet 4.0 s / 4.5 s (beta.4, WSL, 2026-11-10, binary 5666b17f, 25 runners per preset concurrent, BLS on); before beta.4: minimal 68.8 s (66 s of it the two `data_collection` cases), mainnet 1.7 s (WSL, 2026-11-09) |
| `.lake/build/bin/jaune-consensus run --preset P --fork gloas --runner light_client` | goal `eip8282-gloas-cross-layer-v1`, U7b: the Gloas light client (`JauneConsensus/GloasLightClient.lean`: the Gloas generalized indices and `*_gindex_at_slot`, `get_lc_execution_root`, `is_valid_light_client_header`, and the Altair store over the Gloas containers; `GloasLightClientFullNode.lean`: progressive-container proof trees, `block_to_light_client_header`, the `create_light_client_*` functions and the six `upgrade_lc_*_to_gloas`; transcribed from `v1.7.0-beta.4` `specs/gloas/light-client/`). `single_merkle_proof`: `is_valid_merkle_branch` and `compute_merkle_proof(object, leaf_index) == branch` over the Gloas `BeaconState` (735, 2945, 2946) and `BeaconBlockBody` (2856) proof trees; `sync`: the Gloas store over the steps; `update_ranking`: no later update ranks better under the Gloas `is_better_update`. Admitted by `gloasRunners` (`Harness/Discovery.lean`); Gloas has no `merkle_proof` suite. `data_collection` (minimal only, U7c): the Gloas copy of the generator's full-node collection (`Harness/GloasLightClientDataCollection.lean`, transcribed from `helpers/light_client_data_collection.py` as the Electra/Fulu harness is) over U5's Gloas `state_transition` and `process_slots` (`GloasTransition.lean`) and the Gloas light-client functions above, with the Gloas `create_signed_genesis_block` (the genesis body's bid message is `state.latest_execution_payload_bid`); every served bootstrap, update, finality and optimistic update checked by the Gloas fork digest, file name and exact bytes. The case has `GLOAS_FORK_EPOCH: 0` and crosses no fork (an `initial_state` before `GLOAS_FORK_EPOCH` is refused); its digests change at each `BLOB_SCHEDULE` epoch. Strict all-PASS. Control: see the Gloas light-client paragraph below the table | minimal 10 (`single_merkle_proof` 4, `sync` 4, `update_ranking` 1, `data_collection` 1), mainnet 4 (`single_merkle_proof`); all pass | minimal 54.3 s (of it nearly all `data_collection`), mainnet 0.9 s (WSL, 2026-11-10, binary from aa16bb4c, one runner at a time, BLS on); before U7c, with `data_collection` failing closed: minimal 6.1 s, mainnet 1.7 s (binary d9e18f43) |
| `.lake/build/bin/jaune-consensus run --preset P --fork fulu --runner networking --handler get_custody_groups` / `--handler compute_columns_for_custody_group` | `get_custody_groups`: the custody groups for the inputs; `compute_columns_for_custody_group`: the columns for the group (`Harness/Networking.lean`), strict all-PASS, after the tree check below | minimal 11 + 5, mainnet 11 + 5 per fork (Fulu; from U7a also Gloas, same counts, PASS); the `gossip_*` handlers are the row below | minimal 0.1 s / 0.1 s, mainnet 0.2 s / 0.1 s (beta.4, WSL, 2026-11-10, binary 5666b17f, 25 runners per preset concurrent, BLS on); before beta.4: minimal 0.1 s, mainnet 0.0 s (closure tier, both forks, BLS on, eight runners concurrent (WSL, 2026-11-09, binary 5c1992d)) |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner networking --handler gossip_H` for `H` in `proposer_slashing`, `attester_slashing`, `voluntary_exit`, `bls_to_execution_change`, `sync_committee_message`, `sync_committee_contribution_and_proof` | goal `eip8282-gloas-cross-layer-v1`, U7a: the store-free gossip validators (`tests/formats/networking/gossip_validation.md`), `validate_<topic>_gossip` transcribed from `v1.7.0-beta.4` (`JauneConsensus/Gossip.lean` over the fork-indexed state, `GloasGossip.lean` over `Gloas.BeaconState` with the Gloas `is_valid_indexed_attestation`; shared helpers and `Seen` in `GossipCore.lean`). The driver (`Harness/GossipCases.lean`) parses `meta.yaml` strictly, checks every referenced file and the topic's message prefix (read from the vectors, `Harness/GossipTable.lean`), sets the store up from the anchor alone (the anchor block's `state_root` must be `hash_tree_root(state)`; a case with more blocks, block flags, `finalized_checkpoint` or preloaded headers is refused), runs the messages in sequence through one `Seen`, and requires each outcome and, when given, its `reason` to equal the vector's, under the case's `config.yaml` over its preset base. `F` is `electra`, `fulu` or `gloas` (`networking` is in `gloasRunners`). The other `gossip_*` handlers are Store-dependent (unit M6): the Electra and Fulu ones are the row below; the Gloas ones fail as `UNIMPLEMENTED` until their rows land in `gossipHandlers`. Control: see the gossip paragraph below the table | per fork, minimal 9 + 12 + 14 + 6 + 7 + 14 = 62, mainnet 63 (15 contribution cases); 375 in all (Electra, Fulu, Gloas) | minimal 0.4 to 3.8 s per handler, mainnet 1.2 to 7.3 s per handler (WSL, 2026-11-10; mainnet Fulu up to 42.7 s under host contention) |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner networking --handler gossip_H` for `H` in `beacon_block`, `beacon_attestation`, `beacon_aggregate_and_proof`, `blob_sidecar` (Electra), `data_column_sidecar`, `partial_data_column_sidecar` (Fulu) | goal `eip8282-gloas-cross-layer-v1`, M6: the Store-dependent gossip validators of Electra and Fulu, `validate_<topic>_gossip` transcribed from `v1.7.0-beta.4` in the spec's order with its reason strings (`JauneConsensus/GossipStore.lean`, over the fork-choice `Store` of `ForkChoice.lean`; `validate_partial_data_column_sidecar_gossip` keeps a header cached by its header part when its cell part then raises, as pyspec's in-place `Seen` does). The handler (`Harness/GossipStoreCases.lean`) sets the store up per the format's Condition: `get_forkchoice_store` from the anchor, each later block state-transitioned from its parent's post-state (signatures and state root checked) or, when `failed`/`pending`, recorded with no post-state; `payload_status` feeds `block_payload_statuses`; `finalized_checkpoint` (`root` or `block`) replaces the store's; `seen_partial_data_column_headers` preloads `Seen`. Outcomes and reasons strict, as in the row above. The Gloas handlers of these topics and the four Gloas-only topics fail as `UNIMPLEMENTED` until their rows land. Control: see the M6 gossip paragraph below the table | per preset, Electra 20 + 23 + 33 + 16 = 92, Fulu 23 + 23 + 33 + 17 + 24 = 120; 424 in all | minimal 3.2 to 11.7 s per handler, mainnet 5.5 to 14.3 s per handler (Mac working time, 2026-11-10, one runner at a time, BLS on); WSL remains the timing authority |
| `.lake/build/bin/jaune-consensus run --preset P --fork F --runner merkle_proof` | `single_merkle_proof`: `is_valid_merkle_branch` against `hash_tree_root(object)` and `compute_merkle_proof(object, leaf_index) == branch`, with the proof tree regenerated from the object (`Harness/LightClientCases.lean`). Control (2026-11-09, reverted, restored bytes identical): a length chunk of `len + 1` in the `blob_kzg_commitments` proof tree fails the 4 Electra `merkle_proof` cases per preset at the regeneration check | 4 per fork and preset, 16 in all | 0.7 s / 0.4 s (WSL, 2026-11-09); minimal 1.2 s / 0.8 s, mainnet 1.2 s / 1.1 s (beta.4, WSL, 2026-11-10, binary 5666b17f, 25 runners per preset concurrent, BLS on) |
| `.lake/build/bin/jaune-consensus run --preset general --runner kzg` | all twelve general-preset `kzg` handlers (Deneb EIP-4844: `blob_to_kzg_commitment`, `compute_challenge`, `compute_kzg_proof`, `compute_blob_kzg_proof`, `verify_kzg_proof`, `verify_blob_kzg_proof`, `verify_blob_kzg_proof_batch`; Fulu EIP-7594: `compute_cells`, `compute_cells_and_kzg_proofs`, `compute_verify_cell_kzg_proof_batch_challenge`, `verify_cell_kzg_proof_batch`, `recover_cells_and_kzg_proofs`): `data.yaml`'s `output` equals the model's (`null` exactly where the model raises), through the shared tree and count checks (`Harness/KzgCases.lean`). Control (2026-11-09, reverted, restored bytes identical): changing `FIAT_SHAMIR_PROTOCOL_DOMAIN` in `Crypto/KZG.lean` fails all 9 `compute_challenge` cases. The standalone `jaune-consensus-kzg-vectors` remains only as a differential tool (its `@spec` and `@jaune` pseudo-handlers run the spec-shaped cell paths and Jaune's execution-layer `verifyKzgProof`); it is not a catalogue gate | 344 cases (262 Deneb, 82 Fulu) | 152.2 s (2026-11-09, one process; the FK20 setup table is about 31 s of it) |
| `.lake/build/bin/jaune-consensus run --preset P [--fork F] --runner R --tier smoke` | the smoke tier for CI: the same tree and count checks as every tier, executing only the first case of each in-scope suite for any runner above | 1 case per suite | every runner, both forks, one process at a time, BLS on (WSL, 2026-11-09, binary 5c1992d): general 8.1 s, minimal 300.5 s, mainnet 447.2 s; `fork_choice` dominates (minimal 182.9 s, mainnet 257.6 s), every other runner under 80 s |
| the closure tier | every runner row above at full tier over the four presets (`general`, `minimal`, `mainnet`, `comptests`) and the three forks (Electra, Fulu, Gloas) where the inventory lists them, plus the scan, inventory, verify-tree and generator rows below, all strict all-PASS with no expected-failure allowance. **Closure rule:** `fork_choice` and `sync` run with signature checks on (`JAUNE_CONSENSUS_FC_BLS` unset), not `=0`; the per-runner rows above record the `=0` working times, this tier records the checks-on times | 41,504 in-scope cases (5,509 general + 27,328 minimal + 4,251 mainnet + 4,416 comptests), across Electra, Fulu and Gloas (plus `phase0` `shuffling`); of these the Gloas suites still pending are minimal `fork_choice` 92, mainnet `fork_choice` 55, minimal `fast_confirmation` 185 and comptests Gloas 1,472 (the Mac's M4/M5), and the nine store-dependent Gloas `gossip_*` handlers, 233 cases per preset (the Mac's M6), so the tier is not yet closable at Gloas (DRY discovery run at `0bcd72c4`, WSL, 2026-11-10: every other in-scope case PASS). History: before the beta.4 move and Gloas, 23,975 (5,509 general + 16,126 minimal + 2,340 mainnet) | BLS on (binary from 2406ef6, all exit 0): fork_choice minimal 56/56 in 1,498.5 s / 68/68 in 1,570.4 s, mainnet 25/25 in 451.4 s / 37/37 in 512.9 s; sync minimal 7.7 s / 5.4 s, mainnet 13.3 s / 13.6 s (Electra / Fulu; WSL, 2026-11-09). Full closure run at 5c1992d (WSL, 2026-11-09, BLS on, eight runners concurrent, all 33 runner rows PASS 23,975 of 23,975, all exit 0): fork_choice minimal 2,730.5 s, mainnet 869.0 s; sync minimal 17.8 s, mainnet 34.0 s (both forks per run); the longest row is minimal fork_choice, so the tier takes about 46 min of wall time at that concurrency. Every other runner's closure time is its row's time At `v1.7.0-beta.4` (Mac working time, 2026-11-10, BLS on, the four fork_choice runs and the sync runs concurrent beside two comptests runs, all exit 0): fork_choice minimal 56/56 in 1,582.4 s / 68/68 in 1,641.6 s, mainnet 26/26 in 490.8 s / 38/38 in 548.1 s; sync minimal 8.1 s / 8.1 s, mainnet 11.7 s / 14.0 s (Electra / Fulu); WSL remains the timing authority |
| `.lake/build/bin/jaune-consensus --forks`, `--fork-rules NAME` | the O7 pairing table; `--fork-rules electra` / `fulu` print the paired execution forks, max blobs and request types; `--fork-rules gloas` exits 0 and prints only its pairing, `gloas: execution [Amsterdam]`, read from `Jaune.Fork.consensusFork?` (`ConsensusMain.lean`, `gloasPairing`; `CFork.rules?` stays `none` at Gloas, so the runner refusals are unchanged); `--fork-rules heze`, `eip7805` and any unknown name exit 1 with a refusal (verified 2026-11-10) | — | sub-second |
| `.lake/build/bin/jaune-consensus recorded-pairs` / `recorded-pairs --negative-control` | the engine's payload conversion against recorded mainnet data (goal `eip7002-cross-layer-v1`, O4; `JauneConsensus/Harness/RecordedPairs.lean`). For each pair in `scripts/consensus/recorded-pairs/manifest.json`, after checking both raw files' SHA-256 against the manifest: (a) `payloadHeader payload parent_root (getExecutionRequestsList requests)` hashes to the payload's `block_hash`, (b) which is the recorded execution block's `hash`, and (c) `computeRequestsHash` of the requests list is its `requestsHash`; strict all-PASS. `--negative-control` flips one bit of the first withdrawal request's `validator_pubkey` in memory and passes only if every pair then fails (a) and (c), which is this row's bite evidence. Provenance (in the manifest): beacon blocks from one provider (publicnode; Lodestar serves no finalized block and no provider served SSZ), execution blocks parsed-identical across four JSON-RPC providers; every header-feeding payload field is pinned by that agreed block hash, and only the beacon block root rests on the single beacon provider. The beacon-state transition is not run | 3 Fulu pairs with EIP-7002 requests (slots 15601889, 15613807, 15613823): 5 withdrawals + 1 consolidation, 1 full exit + 1 deposit, 1 partial; the first has no deposits, the others no consolidations | interpreted (`#eval`, Mac, 2026-11-09): 3/3 PASS, negative control 3/3 failing as expected; about 1 s each, compiled binary, plain and `--negative-control` (WSL, 2026-11-09, integration e8f503d6) |
| `.lake/build/bin/jaune-consensus recorded-pairs-gloas` (default `--dir scripts/consensus/recorded-devnet8`) | the engine's Gloas conversion reproduces the devnet's recorded EL block hash and `requests_hash` (goal `eip8282-gloas-cross-layer-v1`, G4; `JauneConsensus/Harness/RecordedPairsGloas.lean`). Every file listed in the directory's `SHA256SUMS` (lines copied verbatim from the Plans snapshot) is checked before anything is decoded, and only listed files are read. For each `ssz/blk_<S>.ssz` (Gloas `SignedBeaconBlock`, mainnet preset) with `ssz/env_<S-1>.ssz` (`SignedExecutionPayloadEnvelope`) and `json/el_<block_hash>.json` (`eth_getBlockByHash`): block `S`'s `parent_root` is the envelope's `beacon_block_root` and its bid builds on the payload's `block_hash`; `parent_execution_requests` equals the envelope's `execution_requests` as the five lists; at least one EIP-8282 request is present; `payloadToBlockG` of the `Gloas.NewPayloadRequest` built from the envelope hashes to the payload's `block_hash` and the recorded `hash`, and its `requestsHash` and `blockAccessListHash` are the recorded ones; strict all-PASS. On a hash mismatch every header field is compared with the recorded block and the differing ones are named. **Control, every run:** one byte of the first builder request's `pubkey` is flipped and both the block-hash and the `requests_hash` checks must then fail, so the gate passes only if every mutant is rejected (bites by construction). The request's `versioned_hashes` come from the payload's blob transactions (the committing bid is in block `S-1`, not recorded); `payloadToBlockG` does not read them. A `note (not gated)` line reports where the engine's own `blobVersionedHashesOf` refuses a payload's transactions; since the seam decodes legacy (RLP-list) transactions (`payloadTx`/`payloadTxDecode`, `JauneConsensus/Engine.lean`, whose `#guard`s on a closed one-legacy-transaction payload are the unit's control), no pair prints one (pair 625741's two legacy transactions printed it before). Provenance: `scripts/consensus/recorded-devnet8/provenance.json` (URLs, `fetched_at`, `genesis_validators_root`, Gloas fork version/epoch, `chainId`, alpha.14 vs beta.4 relation). Nothing else is claimed: no beacon-state transition, no execution run, no signature check | 5 glamsterdam-devnet-8 pairs: beacon slots 635977, 629644, 625741 (builder deposits; 625741 repeats 629644's top-up bytes) and 614108, 614027 (builder exits); EL blocks 552829, 547182, 543667, 533294, 533221 | 0.6 s, compiled binary (WSL, 2026-11-10): 5/5 PASS, controls rejected 5/5, no note line after the legacy-transaction seam fix |
| `python3 -I scripts/consensus-vector-inventory.py --tarballs ~/consensus-spec-tests-v1.7.0-beta.4/tarballs [--general-tarballs ~/consensus-spec-tests-v1.6.1/tarballs] --expect scripts/consensus/inventory-v1.7.0-beta.4.json` | the four tarballs (beta.4 `minimal`, `mainnet`, `comptests`; `v1.6.1` `general`, the default `--general-tarballs`) match their pinned size and SHA-256, and regenerate the committed inventory exactly (counts, per-suite records, skipped `comptests` source members) | 4 tarballs, 1.9 GB; 41,504 in-scope cases (general 5,509, minimal 27,328, mainnet 4,251, comptests 4,416) | 68.0 s (WSL, 2026-11-10) |
| `python3 -I scripts/consensus-verify-tree.py --tarballs ~/consensus-spec-tests-v1.7.0-beta.4/tarballs --tree ~/consensus-spec-tests-v1.7.0-beta.4/extracted [--preset T] [--select FORK[/RUNNER[/HANDLER[/SUITE]]]]`, and for the general entry `--preset general --tarballs ~/consensus-spec-tests-v1.6.1/tarballs --tree ~/consensus-spec-tests-v1.6.1/extracted` | the extracted tree's **contents**: every in-scope file under the selection is a regular file with the size and SHA-256 of its member in the digest-checked tarball, and the tree holds no entry that is not a selected member. The tree holds one directory per tarball (`<root>/<tarball>/tests/<preset>/...`); the default `--preset` is every tarball of the pinned release. The runner checks names only; run this once per extraction | 630,557 files (minimal 150,032, mainnet 30,969, comptests 449,556) + 10,925 general | 80.6 s + 6.2 s (WSL, 2026-11-10) |
| `python3 -I scripts/consensus-preset-generate.py --check` | `JauneConsensus/Preset.lean`, `Config.lean` and `Harness/ConfigOverride.lean` are byte-identical to what the generator writes from the pinned pyspec checkout (`--specs`, default `~/consensus-specs-v1.7.0-beta.4`, refused unless at the tag commit): presets phase0 to Gloas, and every config variable a phase0 to Gloas spec file mentions (`GAS_LIMIT_SCHEDULE` as a list of records) | 3 files | sub-second |
| `python3 scripts/consensus-trusted-setup-generate.py --check` | `JauneConsensus/Crypto/TrustedSetup.lean` is byte-identical to what the generator writes from the pinned `trusted_setup_4096.json` (digest-checked against the pin) | 1 file | sub-second (0.07 s, WSL, 2026-11-09) |

**The tree check** runs on every selected suite in every tier (the smoke tier narrows only
which cases execute): case count against the suite record and the inventory count; SHA-256 of
the sorted case names; SHA-256 of the sorted `<case>/<file>` paths; the `bls_setting` histogram
read from each `meta.yaml`; the set of cases with a per-case `config.yaml`; and every file name
against the runner's known kinds (`runnerFileKinds`, including Fulu fork-choice
`column_0x<root>.ssz_snappy`); and, from `v1.7.0-beta.4` on, each case's `manifest.yaml`, whose
`preset`, `fork`, `runner`, `handler`, `suite` and `case` must equal the case's location (its
presence is pinned by the file-path digest). It refuses an empty selection, a suite missing from the tree or
present without a record, `--fork gloas` for every runner outside `gloasRunners` (through
`CFork.rules?`, which resolves Gloas to nothing; `ssz_static` only decodes, re-encodes and hashes
containers, and `epoch_processing`, `rewards`, `operations`, `fork`, `sanity`, `random`, `finality` and `transition` run the separate Gloas modules) and `--fork eip7805`. A `(runner, handler)` with no handler is a FAIL
(`UNIMPLEMENTED`), never a skip. `--tier smoke` executes the first case of each suite.

A case's `config.yaml` (10 minimal light-client cases) is applied over its preset's base
`Config` by the generated typed setters; `scan` applies every one and refuses a key that is not a
phase0 to Fulu config variable, a `PRESET_BASE` other than the case's preset, and a byte string of
the wrong width.

Negative controls (run 2026-11-09 in a disposable copy under
`~/consensus-spec-tests-v1.6.1/negctl/harness-w4`, restored bytes identical to the extracted
tree): one mutated expected mapping entry fails exactly that case (`index 0: computed 6, expected
9`, PASS 299 FAIL 1, exit 1); one removed case directory is refused (`299 cases on disk, manifest
300, inventory 300`); a renamed case at equal count is refused by the names digest; an extra case
is refused; one flipped `bls_setting` (1 to 2) is refused by the histogram; one removed Fulu
`column_` file is refused by the file-path digest; an unknown file name is refused by kind.
`consensus-verify-tree.py`: one changed byte in an extracted `mapping.yaml` is refused at that file
(SHA-256 mismatch), an extra file is refused, a missing file is refused, an empty selection is
refused. Config overrides: an added unknown key, `PRESET_BASE: 'mainnet'`, and a 3-byte
`GENESIS_FORK_VERSION` are each refused. Preset: `SHUFFLE_ROUND_COUNT` changed by hand in
`Preset.lean` fails `consensus-preset-generate.py --check`; minimal 10 to 11 fails the build at
the `Shuffle.lean` mapping guard; mainnet 90 to 89 fails 188 of 300 mainnet shuffling cases by
name (for example `shuffle_0x23bc..._10: index 0: computed 2, expected 3`); regenerating restores
the committed bytes and 300/300. Epoch: minimal `MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA` 64,000,000,000 to
32,000,000,000 in `Config.lean` fails `--check` and 6 of 155 minimal Electra `epoch_processing`
cases by name (`pending_deposits/process_pending_deposits_withdrawable_validator_not_churned` at
`deposit_balance_to_consume`; five `registry_updates` cases, among them `ejection` and
`ejection_past_churn_limit_min`, at `exit_balance_to_consume`); regenerating restores 155/155.
Gloas `ssz_static` (2026-11-10, reverted, restored bytes identical by SHA-256): changing the
Gloas `ExecutionRequests` layout from `active_fields(width=5)` to width 6 with a gap at 4
(`[1, 1, 1, 1, 0, 1]`, same fields, same serialization) in `JauneConsensus/ContainersGloas.lean`
fails 861 of 8,979 minimal Gloas cases, all at the root check (`hash_tree_root differs from
meta.yaml root`): every case of `ExecutionRequests` and of the six containers that hold it
(`ExecutionPayloadEnvelope`, `SignedExecutionPayloadEnvelope`, `NewPayloadRequest`,
`BeaconBlockBody`, `BeaconBlock`, `SignedBeaconBlock`), 123 each, for example
`ExecutionRequests/ssz_lengthy/case_0`; restoring gives 8,979/8,979. During the port, the
`v1.6.1` left-leaning `merkleize_progressive` failed all 141 smoke cases of the 21 Gloas types
with a progressive list or container at the root check, which is how the `eth-ssz-specs`
revision was found.

Gloas epoch (U3, 2026-11-10, reverted, restored bytes identical by SHA-256): replacing the Gloas
`get_exit_churn_limit` call in `Gloas.computeExitEpochAndUpdateChurn` (`JauneConsensus/GloasMutators.lean`,
reached from `Gloas.initiateValidatorExit`) with a local copy of Electra's
`get_activation_exit_churn_limit` (`CHURN_LIMIT_QUOTIENT`, capped at
`MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`) fails 8 of 172 minimal Gloas `epoch_processing` cases,
all `registry_updates`, by name: `ejection`, `ejection_past_churn_limit_min`,
`ejection_past_churn_limit_scaled` and the five `activation_queue_activation_and_ejection__*` cases
(at `exit_balance_to_consume`, `earliest_exit_epoch` or `validators`); restoring gives 172/172.
`pending_deposits_churn` does not distinguish the two, since deposits consume the activation churn,
not the exit churn.

Gossip (U7a, 2026-11-10, reverted, restored bytes identical by SHA-256): computing the
voluntary-exit signature domain from `GENESIS_FORK_VERSION` instead of `CAPELLA_FORK_VERSION` in
`Gossip.validateVoluntaryExitGossip` (`JauneConsensus/Gossip.lean`) fails 5 of 14 minimal Electra
and 5 of 14 minimal Fulu `gossip_voluntary_exit` cases by name (`valid`, `valid_at_clock_disparity`,
`valid_capella_signature`, `valid_previous_epoch`, `ignore_already_seen`, each `got reject (invalid
voluntary exit signature), expected valid`) and leaves Gloas 14/14; the same edit in
`Gloas.validateVoluntaryExitGossip` (`GloasGossip.lean`) fails the same 5 Gloas cases and leaves
Fulu 14/14; restoring gives 14/14 at each fork.

Gloas light client (U7b, 2026-11-10, reverted, restored bytes identical by SHA-256): changing
`CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS` from 2945 to 2944 in `JauneConsensus/GloasLightClient.lean`
(same branch depth, so every `#guard` still holds and the tree builds) fails all 4 minimal Gloas
`sync` cases by name (`advance_finality_without_sync_committee`, `light_client_sync`,
`light_client_sync_no_force_update`, `supply_sync_committee_from_past_update`, each
`initialize_light_client_store: sync committee branch`), PASS 5 FAIL 5 of 10 with the then open
`data_collection` case; restoring gives PASS 9 FAIL 1 (only `data_collection`). U7c (2026-11-10,
reverted, restored `GloasLightClientDataCollection.lean` SHA-256 identical): never taking a better
update in the Gloas `_create_lc_update` (`isBetter && false`) fails exactly minimal Gloas
`data_collection` at step 3 (`best_updates`: `expected exactly keys [period], found [period,
update]`), PASS 9 FAIL 1 of 10, mainnet 4/4; restoring gives 10/10. The
`single_merkle_proof` cases take the index from `proof.yaml` and are pinned instead by the
Gloas proof trees, whose `FINALIZED_CHECKPOINT_FIELD_INDEX` and
`SIGNED_EXECUTION_PAYLOAD_BID_FIELD_INDEX` are tied to the Gloas gindices by `#guard`.

Gloas fork (U5, 2026-11-10, reverted, restored `GloasUpgrade.lean` SHA-256 identical and the rebuilt
binary byte-identical to the candidate's): dropping the in-loop top-up of a known builder in
`Gloas.onboardBuilderDeposit` (`JauneConsensus/GloasUpgrade.lean`) fails exactly 3 Gloas `fork`
cases per preset by name, `fork_builder_deposit_followed_by_non_builder_credentials`,
`fork_multiple_deposits_same_builder` and `fork_valid_builder_deposit_followed_by_invalid_builder_deposit`
(minimal PASS 34 FAIL 3 of 37, mainnet PASS 32 FAIL 3 of 35, `post-state differs`, exit 1);
restoring gives 37/37. The other candidate control, running the builder onboarding before
`initialize_ptc_window`, fails no case (37/37): `compute_ptc` reads only the validator registry,
balances and RANDAO mixes, which onboarding does not touch, so the vectors do not pin that order.

Gossip (M6, 2026-11-10, Mac, reverted, restored bytes identical by SHA-256): changing
`BLOB_KZG_COMMITMENTS_GINDEX` from `16 + 11` to `16 + 10` in `JauneConsensus/GossipStore.lean` (the
generalized index of `BeaconBlockBody.blob_kzg_commitments` behind every sidecar inclusion proof)
fails, by name, 5 of 16 minimal Electra `gossip_blob_sidecar` cases (`valid`,
`valid_slot_within_clock_disparity`, `ignore_already_seen`, `reject_invalid_kzg_proof`,
`reject_wrong_proposer_index`, each `got reject (invalid blob sidecar inclusion proof)`), 5 of 17
minimal Fulu `gossip_data_column_sidecar` cases (the same five, `invalid sidecar inclusion
proof`) and 8 of 24 minimal Fulu `gossip_partial_data_column_sidecar` cases (among them
`valid_header_only`, `valid_header_and_cells`, `valid_cells_only_with_cached_header`,
`reject_prior_header_differs`, `reject_invalid_kzg_proofs`, `invalid header inclusion proof`),
and leaves `gossip_beacon_block` 20/20 (Electra) and 23/23 (Fulu); restoring gives 16/16,
17/17 and 24/24.

### Environment and provenance

| command | purpose |
|---|---|
| `python3 scripts/env_doctor.py` | validate the configured legacy/EELS/oracle environment |
| `python3 scripts/env_doctor.py --mainnet-root "$HOME/eest-mainnet-v21.0.2" --mainnet-deep` | validate external fixture identities |
| `python3 scripts/gen_mainnet_manifest.py --fixtures-root "$HOME/eest-mainnet-v21.0.2/fixtures" --check` | exact current-manifest identity |
| `python3 scripts/bootstrap_mainnet.py --lane amsterdam` | install the same tests@v21.0.2 release as mainnet (939,189,561-byte archive; separate suite manifest) |
| `python3 scripts/env_doctor.py --amsterdam-root "$HOME/eest-mainnet-v21.0.2" --amsterdam-deep` | validate that lane's archive digest, layout, release index, and every extracted file against the archive |
| `python3 scripts/gen_mainnet_manifest.py --lane amsterdam --fixtures-root "$HOME/eest-mainnet-v21.0.2/fixtures" --check` | exact Amsterdam-lane manifest identity |
| `python3 scripts/gen-fork-constants.py --check` | the committed fork-constant extraction still matches the pinned `execution-specs` revision. Needs that checkout and its venv; `scripts/check-fork-constants.sh` itself needs neither |
| `python3 scripts/gen-vector-shards.py --check` | the `blsPairing` shards are an exact partition of their source |
| `python3 scripts/gen-hash-precompile-vectors.py --check` | the committed `sha256.json`/`ripemd160.json` still match the pinned EELS oracle, and that oracle still matches the published FIPS 180-4 / RIPEMD-160 known answers |
| `python3 scripts/gen-t8n-goldens.py --check` | the committed `t8n` goldens still match the conformance target's current output. Needs that checkout and its venv; `scripts/check-t8n.sh` itself needs neither |
| `python3 scripts/t8n-acceptance.py --third <evm>` | three-way `t8n` agreement over the corpus: Jaune, the conformance target, and one further transition tool, compared field by field. Not a gate — it needs two external tools — and its registered divergences live in `scripts/t8n/acceptance-divergences.json` |

Python generators run under the frozen oracle venv
`~/execution-specs/venv/bin/python`. Generated vectors must come from
generators, never manual transcription.

## Pass criteria

Two different contracts, and confusing them is the most common misreading:

- **`check-legacy.sh` tiers are regression gates.** They pass iff every file's
  classification *equals the tracked correctness baseline's* — **not** iff every file
  passes. The legacy corpus has 5 known FAILs, all diagnosed and none a Jaune
  defect: two Cancun-only files have no case selected by the ordinary tier's
  `--network Prague` filter and fail closed on the empty selection (Cancun
  itself is supported), while the other three carry wrong expected exceptions
  and the frozen oracle agrees with
  Jaune. A FAIL turning into a PASS is a gate failure exactly like the reverse.
  Correctness baselines are tracked `STATUS<TAB>path` files at
  `scripts/baseline-<tier>.txt`. Reports and host-local timing baselines are
  gitignored as `scripts/report-<tier>.txt` and
  `scripts/baseline-<tier>-times.txt`.
  **Amsterdam-readiness owner amendment (2026-10-11):** the raw full gate now
  reports 2,973 PASS / 10 FAIL, exactly five PASS→FAIL changes against the
  unchanged baseline. The owner accepts only these five stale Prague files,
  all under `GeneralStateTests/`: `stCreate2/RevertInCreateInInitCreate2Paris.json`,
  `stCreate2/create2collisionStorageParis.json`,
  `stExtCodeHash/dynamicAccountOverwriteEmpty_Paris.json`,
  `stRevertTest/RevertInCreateInInit_Paris.json`, and
  `stSStoreTest/InitCollisionParis.json`. The ten original-input Prague replays
  agree with pinned EELS `e27f097`; their old header gas values disagree. Keep
  all fixture and baseline bytes unchanged and all files selected. The raw
  regression gate remains RED; qualified readiness acceptance requires exactly
  this delta and the retained ten-case replay. Any additional delta fails.
  The separate unmerged historical restoration `41404287` has no Prague cases
  and does not replace the active legacy root. This amendment does not change
  the harness's exit status, baseline comparison or general pass rule.
  The smoke and nightly CI aggregate implements this same qualification with
  `scripts/legacy_qualification.py`: it checks the entire raw report against
  the unchanged baseline and requires the exact two smoke/five full deltas,
  then replays all ten original-input cases against both the candidate binary
  and the manifest-pinned EELS target. Its verdict is **QUALIFIED**, with the
  raw **RED** exit retained, never an all-PASS legacy verdict. It verifies
  fixture Git blobs, preserves signed transaction fields, compares complete
  result/body/account-state JSON, and rejects stale or partial replay output.
  CI uploads the raw report and every replay input, output and command. A
  different classification delta, failed replay, changed baseline or missing
  evidence fails the aggregate; BLS remains an independent all-PASS check.
- **`check-mainnet.sh` suites and `check-legacy.sh --patch`/`--rlp4` are all-PASS
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
  measures each of our own modules re-elaborating against built dependencies:
  every Lean file the default `lake build` elaborates, namely
  `Jaune/**/*.lean` and `Examples/**/*.lean`, the root modules `Jaune.lean`,
  `Examples.lean`, `Main.lean`, `MemoryProbe.lean` and `TraceMain.lean`, and the
  modules of the default `Assurance` library (`scripts/AxiomAudit.lean`,
  `scripts/ExecutionAxioms.lean`, `scripts/UnionAxiomsControls.lean` and the
  fixtures `scripts/UnionAxiomsFixture/{Good,Bad,Dep,ViaDep}.lean`), whose `srcDir` and `roots` the gate reads
  from `lakefile.lean` (a configuration it cannot read is a setup failure).
  Trees are discovered rather than listed. The time measured is the cost of
  opening the file in a session, and the cost sitting on `lake build`'s
  critical path. A module fails above **both** 2x its
  `scripts/baseline-elab.txt` time **and** that time plus 1.0 s; the absolute
  floor keeps a sub-second module from tripping on scheduler noise. A module
  that fails to elaborate at all fails the gate, and a source module with no
  baseline row is initialized by its first green measurement on this host. A
  module that got much *faster* prints `IMPROVED` rather than
  passing silently, because a stale over-generous baseline is how this gate
  would quietly stop gating; refresh with `--rebase`. Stale rows for deleted
  files are a warning, never a failure. This gate exists because no other one
  measures this axis: hygiene, integrity, and every conformance tier are silent
  about elaboration cost, and CI's only ceilings are coarse job timeouts, so a
  module drifting from 4 s to 60 s would land unnoticed.

  **Do not pass it `--no-build`.** Every other gate treats that flag as a
  pure saving, and this one does not: the `lake build` it skips is also what
  pulls the dependency oleans into the page cache, and without it the
  *first* file measured — `Jaune.lean`, which sorts first — pays the cold
  read alone. Measured on one unchanged tree, 2026-08-10: `Jaune.lean` at
  3.075 s with `--no-build` and 1.290 s without, against a 1.230 s baseline.
  The first is a red gate and a fiction; the second is the number. Nothing
  else in the run moves, because by the second file the cache is warm.

  A separate census measured the same cold-first-row inflation in both Jaune
  and Blanc even when `lake build` had run. Therefore the first module of any
  sequential pass on a Lean-cold host is re-elaborated alone before its row is
  believed; the precondition reduces cold reads but does not prove that first
  measurement warm.

  **It is a local gate, not a CI gate.** Its ignored baseline is created in the
  Jaune checkout by the first uncontended green run. That genesis run performs
  no timing comparison; later runs compare only with the same host's history.
  CI continues to build and run correctness gates without consuming a timing
  baseline. The 2x factor and 1.0 s floor absorb same-machine variance.

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

- **`scripts/check-cli.sh` is an all-hold assertion gate on the runner's
  refusals, admissions, rule-data printer, handshake and field provenance.**
  Each assertion requires its expected exit status and output; synthetic
  fixtures and temporary files isolate the boundary, and any failed assertion
  fails the gate. The original four fixture-refusal messages could otherwise
  rot silently: corpus conformance exercises well-formed inputs, golden
  messages cover block-rejection reasons *inside* a run, and the Python tests
  cover bootstrap and generator scripts. The gate now also checks the expanded
  runnable rule sets and their distinct target-backed advertised projection.

  The allocation boundary checks also require `t8n` to retain an explicitly
  empty account at Berlin and Paris, with zero storage slots normalized, and
  the blockchain fixture loader to reject empty account fields from Paris on.
  These are distinct pinned upstream paths: t8n uses `MaterializedAlloc`, while
  the legacy blockchain loader uses `Load.json_to_state`. A storage-only
  account is empty for the latter policy, independently of its storage root.

  `scripts/check-t8n-wide-input.py`, called by this gate, edits one field of a
  signed corpus case per row and checks that `t8n` refuses a value too wide for
  its field rather than reducing it modulo the width. A value that fits, a field
  the fork never reads and a transaction `--state-test` never selects must all
  still run. No golden can pin this, since the pinned target ends the run with
  `OverflowError` on the refused inputs, so the corpus of `check-t8n.sh` stays
  refusal-free. Each row runs under a resident-memory budget, because the blob
  base fee can exhaust the host: see `scripts/t8n/README.md`.

  `scripts/check-expectation-fields.py`, called by this gate, checks the shared
  fixture-field reader through the built strict and diagnostic frontends.
  The reader selects only modern `expectException`, `expectExceptionALL`, or
  `expectException` plus the original case's exact network label. Applicable
  fields have no precedence: ambiguity (even equal values), a selected
  non-string, or unsupported `exceptions` is a format error. Foreign suffixes
  remain provenance only. Focused controls cover ALL/selected-network wiring,
  original transition-label selection, foreign-only isolation, ambiguity/type
  handling, and complete/unreached v2 field provenance. They require no corpus
  installation and do not duplicate `FixtureClosure.score_continue_iff`'s
  abstract continuation policy. Diagnostic reports are schema v2; prior v1
  receipts remain evidence of their original binary, not this changed runner.

  **It pins the guards, not the run beneath them.** The permissive half of the
  wrong-tree rule — a case declaring no `_info.fixture-format` is passed through
  — is checked as an A/B pair of files identical but for the `_info` block, and
  asserted only as far as *entering* the per-case run. No conformance tier can
  check that half at all: every case in both installed corpora carries the
  field, so none of them ever takes the pass-through branch. A hand-written
  fixture carries no valid genesis state root, so it cannot legitimately
  complete a run, and the gate deliberately does not assert what happens after
  that point. It needs the built binary and no corpus, so a bare runner can run
  it after a build; it never builds one itself.

`--bls` is a middle case: it compares against a tracked baseline like a tier,
but that baseline is a hand-authored *target*, so `--rebase` is refused — edit
`scripts/baseline-bls.txt` directly, with a written justification for any
non-PASS entry. `--refresh-times` remains safe because it writes only the
ignored host-local timing file.

Every gate's last line is a single unambiguous verdict, and every gate exits 0
if and only if it passed.

## Writing a `check-legacy.sh` baseline: two verbs

Portable correctness and host-specific timing use separate files. The tracked
baseline is `STATUS<TAB>path`; the ignored local timing file is
`TIME<TAB>path`. A fresh clone's first complete sequential run initializes the
timing file and makes no timing comparison. Both explicit write modes are
sequential-only and refused for the `--patch`/`--rlp4` target gates;
`--bls` refuses only `--rebase`.

| flag | means | on a classification change |
|---|---|---|
| `--rebase` | "the classifications legitimately changed; accept them" | absorbs it, after printing a `REBASE — <file>: <old> -> <new>` line for each |
| `--refresh-times` | "the classifications are identical, the code got faster; refresh this host's reference times" | **writes nothing**, prints the differing files, exits nonzero |

`--rebase` is rare and consequential — it is the one operation that can make a
regression disappear, which is why it now prints the delta it absorbs instead of
a bare `OK`. `--refresh-times` is the safe, mechanical case: it runs the tier,
compares STATUS through the ordinary comparison, and only then replaces the
ignored timing file. It never writes the tracked correctness baseline. A
refusal from it is a finding — report it; do not route around it with
`--rebase`.

Refreshing TIME is not cosmetic. Parallel dispatch is longest-first, **seeded
from the host-local timing file**, so after an optimization that
changes which fixture is slowest, a stale TIME column schedules the wrong
fixture first and gives back part of the speedup. Note also that no DRIFT line
appears when a fixture gets *faster* — DRIFT fires only above 2× its reference —
so nothing else prompts the refresh.

Verdict lines:

```
OK — full: 2983 files match correctness baseline; host-local times refreshed
OK — depth: correctness baseline rebased with 67 files, 1 classification change(s) absorbed (67 PASS, 0 FAIL)
```

## One run at a time

Two gate runs on one host are refused, not queued. Each report-writing harness
takes an exclusive lock on its report file, and the heavier ones additionally
take a single shared **heavy-gate lock**; a second run that would contend exits
2 with a `REFUSED` verdict naming the holder's PID, start time, and full command
line. It does not wait, does not fall back to another path, and writes nothing.
The heavy-gate lock is host-global — it lives at `~/.codex/locks/gate-heavy.lock`
and is shared across both this repository and Blanc, and across every checkout
or worktree of either, because they all contend for the same cores: one host,
one heavy gate. Before running a timing-authoritative gate, a session must
already hold the cross-session hard semaphore through
`python3 -m creme semaphore`; see `~/creme/docs/guides/execution.md` for the
protocol. The gate lock is the last line of defense, not the coordination
mechanism. The lock mechanism is `scripts/gate-lock.sh` (`mkdir`, `kill -0`,
one `EXIT` trap — macOS has no `flock`), which also documents the 2026-07-31
incident that motivated it.

| gate | report lock | heavy lock |
|---|---|---|
| `check-legacy.sh --smoke`, `--bls`, `--full`, or any `--jobs > 1` | yes | yes |
| `check-legacy.sh --depth`, `--patch`, `--rlp4`, `--dir` (sequential) | yes | no |
| `check-mainnet.sh --suite osaka`/`prague`/`full`, or any `--jobs > 1` | parallel only | yes |
| `check-mainnet.sh --suite smoke`/`transitions`/`bpo1`/`bpo2` (sequential) | — (writes none) | no |
| `check-vectors.sh` | yes | yes |
| `check-elab.sh` | yes | yes |

`check-memory-probe.sh` takes no lock either: each of its two points is one
short-lived process, it writes nothing under the repository unless `--json-dir`
names somewhere else, and its own watchdog bounds what it can consume. Its
budget is an assertion, not a tuning knob — raising `--budget-bytes` to make it
pass is weakening a gate.

`check-rule-data-reads.sh` takes no lock and needs nothing built: it reads
tracked Lean source and one committed allowlist, and writes nothing.

`check-fork-constants.sh` takes no lock and needs no corpus: it reads the
built binary and one committed JSON file, and writes nothing. A
`--lane amsterdam` run takes the heavy lock exactly as the mainnet lane does,
derived from the suite name: `--suite amsterdam` takes it, with or without a
`--dir` subtree (as `--suite prague --dir X` does on the mainnet lane);
`--suite amsterdam-smoke` does not; `--suite amsterdam-full` takes it as the
union of a heavy suite; `--suite amsterdam-transitions` does not when
sequential, exactly as the mainnet lane's `transitions`.

`check-t8n.sh` takes no lock either, for the same reason `check-cli.sh` does
not: it writes nothing under the repository. Each case runs in a `mktemp -d`
directory removed on exit, so two concurrent runs cannot see each other's
outputs, and the goldens it reads are never written by the gate.

The cheap tiers stay outside the heavy lock deliberately: the check you run
while iterating must never be hostage to a 20-minute one. `check-hygiene.sh`,
`check-integrity.sh`, `check-canonical-opcode-names.sh`, `check-cli.sh`,
`check-u256.sh`, `check-fake-exp.sh` and `check-ec.sh` take no lock at all — the
first six are sub-second, and `check-ec.sh` is a single-process oracle that
writes its report in one `tee` rather than appending per file. `check-cli.sh`
and `check-t8n.sh` additionally write nothing
under the repository at all: their scratch files live in a `mktemp -d`
directory removed on exit, so two concurrent runs cannot even see each other's
inputs.

Escape hatches, where one exists, are named in the refusal: `check-legacy.sh` and
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
  comparison trusts. `check-legacy.sh` treats `path` as a primary key on its selection,
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

### Destination axiom audit

The default `Assurance` library (`srcDir := "scripts"`) elaborates
`scripts/ExecutionAxioms.lean`: 53 `#expect_axioms` rows over the canonical
execution surface (`Jaune.Exec` and its constructors, adequacy, derivation,
settlement and chronology, frame spawn lemmas, `Jaune.SymbolicPush`,
`Jaune.SymbolicArith`, and the `Examples.Execution` and `Examples.Arithmetic`
observations), each pinned to exactly `Classical.choice`, `Quot.sound`,
`propext`. A row fails elaboration, and with it `lake build`, when
the declaration's axiom closure differs from its set in either direction; the
message names the row as `AXIOM mismatch for <name>: expected [...], actual [...]`.
Rows and sets are a user-reserved decision (`jaune-destination-axiom-pins-20260924`
approved the first 38): adding, removing or re-pinning one is never a routine
edit. The other 15 were added at the standard set together with the
declarations they audit (unit `jaune-c6-surface-20260924`), under that
unit's explicit authorization.

`scripts/assurance-manifest.json` gives every row its provenance: declaration,
expected set, origin (`carried` for the fifteen obligations Blanc pinned under
their former `Blanc.*` names, `destination` otherwise), the original check (the
Blanc `scripts/check.sh` row and `scripts/AxiomCheck.lean` line at a named
commit), the property enforced, the destination check, and the downstream check
retained. `python3 scripts/check-assurance-manifest.py` (CI, hygiene job) fails
when a row is deleted, an entry is deleted, a set differs, or a public rule of a
coverage module has no row; `scripts/tests/test_assurance_manifest.py` holds
those three omissions as controls.

The closure is computed by `Jaune.AxiomAudit.walkMany` in
`scripts/AxiomAudit.lean`, a from-scratch walk over each reachable constant's
type and value and each inductive's constructors, with one visited set per walk
and no cached per-constant result. It never calls `Lean.collectAxioms` or
`#print axioms` (lean4#15226). It is the single walker, with two entry points.
Per name: `walk` (a single root) serves `#expect_axioms` and the `#full_axioms`
report command (one `FULL-AXIOMS '<name>': [...]` line per name, each name in
its own task), each name with a fresh visited set. Union: `#union_axioms_of_modules
P [allowed,...]` roots one walk, with one shared visited set, at every kernel
constant (all kinds, private names and auxiliaries) recorded in the `constNames`
of every imported module named `P` or `P.…`, and logs one
`UNION-AXIOMS 'P': [...] roots=<n> modules=<m> visited=<v>` line. It fails
elaboration when no module matches (an empty population is never green), when
the walk reaches an absent constant, and when the union contains an axiom outside
the allowed list (default `propext, Classical.choice, Quot.sound`; `[]` allows
none); an axiom failure names, per offending axiom, up to 20 roots that reach it
with the chain from the root to the axiom (a linear reverse-graph search, not a
walk per root). All three commands fail elaboration when the walk reaches a
constant the environment does not contain. That module imports only `Lean` and
is a root of `Assurance` so a downstream package can import it; `Jaune.lean`
imports neither file. Like the other `scripts/*.lean` metaprograms, the walker,
`ExecutionAxioms.lean`, `UnionAxiomsControls.lean` and the four fixture modules
`scripts/UnionAxiomsFixture/{Good,Bad,Dep,ViaDep}.lean` are outside the hygiene and
integrity scopes. Controls of the per-name entry points (2026-09-24, disposable
tree, against this walker): injecting a non-standard axiom into one audited
declaration fails the owned build at exactly that row, a wrong expected set
fails its row, a row whose declaration references a constant absent from the
environment fails at that row, and restoring the bytes restores green.

The union entry point's controls are committed in the default `Assurance`
library (`scripts/UnionAxiomsControls.lean`, every `#guard_msgs` exact, so the
ordinary build fails at the control if a behaviour changes): a compliant
population passes with the exact union and root set; an explicit allowed list is
honoured and `[]` allows nothing; a population reaching a non-allowed axiom
fails naming the axiom, both root theorems and the chain; an empty population
fails closed, as does a name that is only a textual prefix of a module; and an
absent constant reached from a root fails and is located; axioms declared
outside the population are found across its boundary, through the constructor of
an inductive the population mentions and through a private theorem (a private
name is a root).

The default `Assurance` library also elaborates `scripts/JauneUnionAxioms.lean`:
one `#union_axioms_of_modules Jaune` walk over every kernel constant of all
`Jaune` modules, including the runner-side modules outside `Jaune.lean` and the
standalone tracer (`Trace`, `TraceJson`, `TraceTransaction`). The source-only
assurance-manifest gate requires every Jaune source module to be transitively
imported by this audit, so adding a module cannot silently omit it. The walk is
against the standard `propext, Classical.choice, Quot.sound`. It complements the
53 exact rows and never replaces them: a union says no declaration uses a
non-standard axiom, not which standard ones a pinned declaration uses. Blanc's
union covers only `Blanc.…` modules, so this is the only audit of the Jaune
constants Blanc does not reach. Before the standalone tracer was integrated, measured on WSL with Lean 4.35.0
(2026-10-15): `roots=12278 modules=29 visited=23337`, about 2 s. That historical
measurement does not cover the subsequently added tracing modules.

### Ambient execution examples

`Examples` is a default Lake library in the same package and revision as Jaune;
the ordinary owned default build elaborates `Examples.Execution` and
`Examples.Arithmetic`. The latter's `#guard_msgs` negative checks (a gas premise
one short, and the `ADD` rule applied to `DIV`) fail that build if either
negative case starts elaborating. It is outside
Jaune's production import closure. Hygiene scans every Lean file under both
source trees and their root modules. Integrity scans examples (including files
not imported by `Examples.lean`) under R1–R4; R1 also recursively scans Jaune,
so a nested module cannot escape the absence rule. Existing allowlists and
budgets apply unchanged. Missing example tree/root is a setup failure.

`python3 scripts/check-consumer-boundary.py` is a static CI check that the nine
canonical execution modules are reachable from `Jaune.lean`, every source under
`Examples/` is reachable from `Examples.lean`, and both libraries retain default
Lake registration. It rejects Blanc/Creme imports in either source tree and
example imports in the production closure. It scans actual source imports after
removing nested comments; unsupported import syntax fails explicitly. It does
not establish theorem types, axiom sets, or successful external installation.

The `external-consumer` CI job prepares a disposable package with
`python3 scripts/external-consumer.py prepare DIRECTORY --url URL --revision SHA`,
builds `Consumer`, then runs the copied verifier with `verify DIRECTORY`.
Preparation requires a fresh directory and a full commit ID. Verification checks
the exact Git URL/revision, installed HEAD, clean tracked source, matching
toolchain, Git-only dependency types, absence of Blanc/Creme packages and the
consumer olean. It does not compile; local builds use the normal host launcher.
CI deletes its sparse bootstrap checkout before building, so source must come
from the dependency. GitHub build-cache restoration is disabled; Mathlib cache
download is enabled. A local bare-mirror rehearsal is useful development evidence
but is not the CI HTTPS-install verdict. Hygiene and integrity also scan the
external smoke source before it is copied.
