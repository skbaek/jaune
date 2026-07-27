# Step 6 report — BPO schedules and supported fork transitions

Date: 2026-07-27 (Asia/Seoul). Plan: `~/plans/migration.md`, Step 6.

## Authoritative inputs

The BPO schedule was resolved from two independent sources that agree exactly.

| what | value |
|---|---|
| fixture release | `tests@v20.0.1` |
| execution-specs commit | `87aba1a38a476b31f819a2390eb481527e6dc683` |
| diffed trees | `src/ethereum/forks/osaka` → `.../bpo1` → `.../bpo2` |
| defining EIP | EIP-7892 (Blob Parameter Only Hardforks), cited by each BPO fork module |
| mainnet activations | each fork module's `FORK_CRITERIA` |
| second source | the `config.blobSchedule` every runnable fixture declares |

The EELS trees were read from the pinned object database with `git show
87aba1a3:…`; no checkout was moved.

### The delta is three numbers

The complete `osaka` → `bpo1` → `bpo2` module diff at the pinned revision,
outside docstrings, cross-reference paths, comment text, and import formatting,
is `vm/gas.py`:

| constant | Osaka | BPO1 | BPO2 |
|---|---:|---:|---:|
| `BLOB_SCHEDULE_TARGET` | 6 | 10 | 14 |
| `BLOB_SCHEDULE_MAX` | 9 | 15 | 21 |
| `BLOB_BASE_FEE_UPDATE_FRACTION` | 5007716 | 8346193 | 11684671 |
| `BLOB_BASE_COST` | 2^13 | 2^13 | 2^13 |

`PER_BLOB` stays `2^17`, so in the gas units `BlobSchedule` carries the targets
are 786,432 / 1,310,720 / 1,835,008 and the ceilings 1,179,648 / 1,966,080 /
2,752,512. Every other file differs only in prose. No BPO fork changes a
transaction limit, an opcode, a precompile, or a gas rule.

The same three numbers per fork are declared by the fixtures themselves, in
blob counts, in `config.blobSchedule`. Among the cases this build runs, BPO1 is
declared by 47 and BPO2 by 23, all agreeing. The generator records them
(`declared_blob_schedules` in the manifest) and fails closed if any two cases
disagree or if a runnable case declares none; the fixture runner checks its own
rule data against the declaration of every case it runs.

### Mainnet activation timestamps

| fork | timestamp | UTC | source |
|---|---:|---|---|
| Prague | 1746612311 | 2025-05-07 10:05:11 | `forks/prague/__init__.py` |
| Osaka | 1764798551 | 2025-12-03 21:49:11 | `forks/osaka/__init__.py` |
| BPO1 | 1765290071 | 2025-12-09 14:21:11 | `forks/bpo1/__init__.py` |
| BPO2 | 1767747671 | 2026-01-07 01:01:11 | `forks/bpo2/__init__.py` |

BPO3 is `Unscheduled` at this revision, which is consistent with the plan's
scope ending at BPO2.

## What changed

### Rule data (`Elevm/Fork.lean`)

`bpo1BlobSchedule`, `bpo2BlobSchedule`, `bpo1Rules`, `bpo2Rules`, and the two
new `Fork.rules?` cases. Each rule set is written as a record update of
`osakaRules`, and a guard undoes the update:

```
#guard { bpo1Rules with fork := .osaka, blob := osakaBlobSchedule } = osakaRules
```

That makes "blob parameter only" a property of the code rather than a claim
about it. No Osaka execution function was copied, and no use site compares fork
identities.

### Schedules and labels (`Elevm/Fork.lean`)

- `ForkTransition` and a strict parser for the `<before>To<after>AtTime<n>`
  fixture labels: exactly one `AtTime`, exactly one `To`, a decimal timestamp
  with the fixtures' optional `k` suffix, and both endpoints parseable by
  `Fork.ofString?`. `ForkTransition.chainConfig` builds the schedule; whether it
  is usable stays `ChainConfig.validate`'s answer.
- `NetworkSpec`, which is either a static fork or such a transition, with
  `toString`, `ofString?`, and `forks`.
- `mainnetChainConfig` and the four activation constants above. Prague is the
  schedule's floor rather than an activation, because the supported chain
  begins at Prague and a schedule may not name rules this build does not have;
  `mainnetPragueTimestamp` records the real activation and is guarded against
  the schedule.

### Fixture runner (`Main.lean`)

`--network` resolves to a `NetworkSpec`. A static label imports at
`addBlockToChainAt`; a transition label imports through
`addBlockToChainUsing`, so each block's own timestamp selects its rules. The
schedule is validated once, before any fixture is read. `--vectors` keeps the
static-only resolution.

`checkFixtureBlobSchedule` compares each case's declared blob schedule against
the rules the run will apply, for every fork the label can select.

### Harness and manifests

- `gen_mainnet_manifest.py` derives supported transitions by parsing labels —
  a transition is supported when both endpoints are forks this build
  implements, the same rule the Lean parser applies. Nothing is hand-listed.
- New `transitions` suite (per-file network labels) and `full` suite (the union,
  stated as its component suites so no file's case evidence is written twice).
- Exclusions now name the fork that put a label outside the supported chain.
- Manifest `schema_version` 2. The Prague, Osaka, and smoke file lists are
  byte-for-byte the same selections as before.
- `check-mainnet.sh` activates `--suite transitions` and `--suite full`, accepts
  the three supported transition labels, and allows `--dir` for transitions.

## The empty static BPO suites

**The pinned release publishes no fixture whose `network` is a bare `BPO1` or
`BPO2`.** Every BPO case in `blockchain_tests` is a transition case:

| label | files | cases |
|---|---:|---:|
| `PragueToOsakaAtTime15k` | 8 | 62 |
| `OsakaToBPO1AtTime15k` | 3 | 24 |
| `BPO1ToBPO2AtTime15k` | 2 | 23 |
| `BPO1` (static) | 0 | 0 |
| `BPO2` (static) | 0 | 0 |

The plan asks for `--suite bpo1` and `--suite bpo2` to be activated and green.
An all-PASS verdict over zero selected files is exactly the permissive oracle
design decision 8 forbids, so both suites remain refused — but for the accurate
reason, which the harness now states: the archive has no such fixture, and BPO
rules are exercised by `--suite transitions`. This is a fact about the fixture
release, not an unfinished step; it needs no code and blocks nothing, and it is
reported here rather than papered over.

BPO1 and BPO2 rules therefore rest on: the pinned EELS module diff; the
fixtures' own declared schedules, checked at both ends; the 47 BPO-transition
fixture cases run through the configured API; and explicit boundary guards.

## Boundary and focused evidence

All guards elaborate in the project build.

| what | guard points |
|---|---|
| BPO rule shape | undoing identity + blob schedule returns `osakaRules`, for both |
| blob numbers | target, ceiling, fraction, and the shared `2^13` reserve cost, per fork |
| schedule ordering | targets and ceilings strictly increase along Prague → BPO2 |
| `calculateExcessBlobGas` | same parent gives 1,966,080 / 1,441,792 / 917,504 at Osaka / BPO1 / BPO2 |
| below-target boundary | each fork's own target − 1, target, and target + one blob |
| reserve branch | identical at all three schedules, because EIP-7892 keeps every ratio at two thirds |
| activation, state transition | block at 199 vs 200 vs 299 vs 300 on a Prague→Osaka→BPO1→BPO2 schedule, judged end to end by `stateTransitionUsing` |
| multi-block sequence | one fixed expectation over timestamps [0, 99, 100, 199, 200, 299, 300, 400] is accepted exactly on the BPO1 segment |
| configured = explicit | `stateTransitionUsing` at 250 and 350 gives the same diagnostic, expected value included, as `stateTransitionAt .bpo1` / `.bpo2`, and a different one from `.osaka` |
| block import | the same agreement on the `.inr` channel, via a transition-derived schedule |
| mainnet schedule | validates; each recorded timestamp is a boundary (t−1 old, t new) |
| label parsing | 3 supported labels round-trip; 12 malformed or unsupported labels rejected |
| unusable schedules | backwards transition and activation-at-genesis rejected with `InvalidChainConfigError` |

Negative tests run against the built binary, not only the guards:

- a fixture whose declared BPO1 target is altered by one blob is rejected with
  `BPO1 blob target = 1310720, fixture declares 11 blobs = 1441792`;
- `--network CancunToPragueAtTime15k` is refused as an unknown label;
- `--network OsakaToPragueAtTime15k` is refused with `InvalidChainConfigError`;
- `--vectors … --network PragueToOsakaAtTime15k` is refused.

## Verification

ELeVM gates ran against the executable built from `394ee6f`; the Lean library
content is `a40871b`, which is what Blanc consumes.

| gate | verdict | measured time |
|---|---|---:|
| `lake build` (all `#guard`s elaborate) | OK | — |
| LSP diagnostics: `Fork.lean`, `Execution.lean`, `Main.lean` | clean | — |
| `scripts/check-hygiene.sh` | OK, no new occurrences | — |
| `python3 -m unittest discover -s scripts/tests` | 110 tests OK (was 102) | 12.82s |
| `gen_mainnet_manifest.py --check` | manifest exact | — |
| `scripts/check-u256.sh` | 21,593/21,593 PASS | 0.27s |
| `scripts/check-vectors.sh` | 44/44 files PASS; controls 5/5 | 477.27s |
| `scripts/check.sh --patch --no-build` | 10/10 PASS | 0.54s |
| `scripts/check.sh --rlp4 --no-build` | 4/4 PASS | 0.14s |
| `scripts/check.sh --depth --no-build` | 67/67 match baseline | 12.74s |
| `scripts/check.sh --smoke --no-build` | 174/174 match baseline (173 PASS / 1 expected FAIL) | 91.41s |
| `scripts/check.sh --bls --no-build` | 29/29 match baseline | 150.43s |
| `check-mainnet.sh --suite smoke --no-build` | 16/16 PASS | 0.49s harness / 6.61s real |
| `check-mainnet.sh --suite transitions --no-build` | **13/13 PASS, 109 cases** | 15.06s harness / 19.88s real |
| `check-mainnet.sh --suite osaka --no-build` | 2,514/2,514 PASS, 17,323 cases | 511.28s harness / 518.22s real |
| `check-mainnet.sh --suite bpo1 / --suite bpo2` | refused: no such fixture in the release | — |
| Blanc `lake build` | 907 jobs OK | 26.79s (first) / 6.63s |
| Blanc `scripts/check.sh --no-build` | 4/4 protected theorems clean | 1.29s |

Deferred long gates, both **user-owned at closure (Step 7)**:

- `check-mainnet.sh --suite prague --no-build` — 2,573 files; measured at
  18,800s real in Step 5, so far above the ten-minute agent-gate policy. It is
  a component of `--suite full`, which Step 7 must run in full anyway. Its code
  path is exercised here by current smoke (16 Prague files) and by the Osaka
  suite, which shares every line except the label; and the generator has
  verified that all 34,151 Prague case declarations equal the one recorded
  Prague blob schedule.
- `check-mainnet.sh --suite full --no-build` — 5,100 files, 34,005 cases.
- legacy `scripts/check.sh --full --no-build` — 2,983 files, ~30 minutes.

## Blanc integration

Blanc pins `a40871bc69df5159f6edc7fc7c3e928675b9f54d` in `lakefile.lean`,
`lake-manifest.json`, and the Lake-managed checkout, following the established
policy of pinning semantic checkpoints rather than harness or documentation
tips.

**No proof needed repair.** A BPO fork is rule data and nothing downstream
reads a blob schedule — the clearest possible evidence for the design decision.

The generalisation Step 6 asks for was then done as its own change:

- `stateTransitionWith_inv_solvent (rules : ForkRules)` and
  `addBlockToChainWith_inv_solvent (rules : ForkRules)` are the general
  theorems;
- `stateTransitionAt_inv_solvent`, `stateTransitionUsing_inv_solvent`,
  `addBlockToChainAt_inv_solvent`, and `addBlockToChainUsing_inv_solvent` are
  instances;
- `BlockChain.ReachUsing cfg` is reachability along a configured chain and
  `chainUsing_inv_solvent` covers a sequence crossing every activation in one
  induction; `Reach.toReachUsing` shows the existing relation is the
  Prague-only instance;
- `stateTransition_inv_solvent` and `addBlockToChain_inv_solvent` are now
  one-line `pragueRules` corollaries. Their statements are textually
  unchanged, as are `weth_inv_solvent`'s and `chain_inv_solvent`'s.

There is no per-fork copy of any top theorem. `lean_verify` reports exactly
`[propext, Classical.choice, Quot.sound]`, with no warnings, for all four
protected theorems and for the new generic ones.

## Unexpected findings

1. **No static BPO fixtures exist in the pinned release** (see above). This is
   the one place the step's outcome differs from the plan's expectation.
2. **Prague and Osaka share a blob schedule.** EIP-7892 restates Osaka's
   target and ceiling as blob counts without moving them, so the first
   observable blob-schedule boundary on the supported chain is Osaka → BPO1.
   The boundary guards are written to account for this rather than to hide it.
3. **The reserve-price branch is schedule-independent.** EIP-7892 keeps
   `(max − target) / max` at two thirds for Osaka, BPO1, and BPO2, so
   EIP-7918's branch returns the same value under all three. Only the ordinary
   target-subtraction branch discriminates, which is what the guards use.
4. **`UnsupportedForkError` is now unreachable** in this build, since every
   declared fork resolves. It is retained for the next declared fork.

## Scope check

- Prague wrappers and every public entry-point signature are unchanged; the
  four `rfl` examples still hold.
- Prague, Osaka, legacy, U256, vector, PATCH, RLP4, DEPTH, SMOKE, and BLS
  classifications are unchanged. No baseline was edited or rebased.
- No expected-failure allowance exists for any current-mainnet suite, and none
  was added.
- The Prague/Osaka/smoke manifest selections are identical to Step 5's; only
  the schema and the added suites differ.
- No Osaka execution function was copied. BPO forks are record updates.
- Mainnet timestamps appear only in `mainnetChainConfig`, never in `ForkRules`.
- `Hash.fB64`, `B64.rdnc`, legacy bootstrap code, and the frozen corpora are
  untouched.
- No `sorry`, `admit`, new axiom, `ofReduceBool`, or `ofReduceNat` was added;
  `check-hygiene.sh` reports no new occurrences.

## Commit ledger

| repo | branch | commit | purpose | pre-commit gates | pushed |
|---|---|---|---|---|---|
| ELeVM | `codex/migration` | `a40871b` | BPO1/BPO2 rule data, transition labels, mainnet schedule, boundary guards | build (all guards), LSP diagnostics | yes |
| ELeVM | `codex/migration` | `f2e275b` | fixture runner: configured transitions, declared-schedule check | build, 13/13 transition files, negative tests | yes |
| ELeVM | `codex/migration` | `394ee6f` | manifest/harness: transitions and full suites, exclusions, BPO refusal | 110 Python tests, manifest `--check`, transitions, osaka, smoke | yes |
| Blanc | `codex/migration` | `36c4ec3` | pin `a40871b`; generic solvency over rules and configured chains | build, axiom audit, `lean_verify` | yes |

## Recovery state

- ELeVM `codex/migration` tip `394ee6f`, clean, pushed. The independent green
  semantic checkpoint is `a40871b`.
- Blanc `codex/migration` tip `36c4ec3`, clean, pushed, pinned to `a40871b` in
  all three locations.
- No uncommitted work.

## Autonomous decisions

- **Pinned Blanc to `a40871b`, not the branch tip**, matching Step 5's policy of
  pinning the last commit that changes what Blanc consumes.
- **Supported transitions are derived, not listed.** Both the Lean parser and
  the generator decide support by parsing the label and checking its endpoints,
  so the two cannot drift apart and neither carries a hand-kept list.
- **The union suite names its components** instead of repeating their entries,
  which keeps one statement of each file's case evidence.
- **Added the fixture-declared blob-schedule cross-check.** Not required by the
  plan, but with no static BPO suite available it turns 34,005 current-mainnet
  cases into an oracle for exactly the data a BPO fork consists of. It is
  inert on fixture families that carry no `config` section, so the legacy lane
  is unaffected.
- **Deferred the current Prague suite to closure** under the plan's
  ten-minute agent-gate policy, rather than spending five hours re-running a
  suite Step 7 must run again as part of `--suite full`.

## Human decisions pending

None from this step. The three deferred long gates above are Step 7's, and the
merge decision remains the user's.

## Next handoff

Step 7 starts from ELeVM `394ee6f` and Blanc `36c4ec3`, with fixture release
`tests@v20.0.1` at `87aba1a3` and all supported static and transition suites
green except the deferred long runs.
