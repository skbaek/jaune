# Step 7 closure report — candidate verification and merge handoff

Date: 2026-07-27 (Asia/Seoul). Plan: `~/plans/migration.md`, Step 7.

## Candidate identity and status

This is a **documentation/evidence checkpoint, not a merge**.  The verified
candidate is ELeVM `ce9426a0e72b77362f117fdc0a6475b1a683fb48` on
`codex/migration` and Blanc `36c4ec37b656bafe457bcf99653bc4a1053071fa` on
`codex/migration`.  Both began this step clean and equal to their respective
`origin/codex/migration` tips.  ELeVM's last semantic checkpoint is
`a40871bc69df5159f6edc7fc7c3e928675b9f54d`; the later ELeVM commits add the
transition harness and documentation only.

The final two long conformance gates are deliberately **user-owned and still
pending**.  Consequently this report is not a green merge verdict.  It records
the exact commands and binary identity that the owner must use below; no
baseline, manifest, or exclusion was changed to avoid those gates.

## Locked inputs and provenance

| input | old | candidate |
|---|---|---|
| Lean | `leanprover/lean4:v4.23.0` | `leanprover/lean4:v4.32.1` |
| mathlib | `v4.23.0` | `v4.32.1` (manifest rev `520045ab14e26149ee970e2e617ca04b09bde5d6`) |
| legacy EELS checkout | — | `4198b9c5996713b268aed602739d5aa40e277694` |
| legacy ethereum/tests | — | `3129f16519013b265fa309208f49406b2ef57b13` |
| LegacyTests gitlink | — | `2339b9a7457c6e3d8e4271032b0e71c46c61dd29` |
| frozen EEST archive | — | `v5.4.0`, SHA-256 `92cf1b47ad12fb27163261fc3c1cea5df72439cab507983d06b56c94f8741909` |
| canonical current-mainnet lane | — | `tests@v20.0.1`, EELS `87aba1a38a476b31f819a2390eb481527e6dc683`, fixture archive SHA-256 `3586193db06d4d5745d5e90b3c3008c2255a4e19ccd8f11a3ce887aec8c0b17c` |

Both `lean-toolchain` files and both mathlib inputs/manifests name v4.32.1.
Blanc's `lakefile.lean`, `lake-manifest.json`, and normal Lake-managed
`.lake/packages/elevm` checkout all name exactly
`a40871bc69df5159f6edc7fc7c3e928675b9f54d`.  This deliberate semantic-pin
policy avoids repinning Blanc for ELeVM harness/report-only commits.

## Fork API and supported matrix

`Fork` contains Prague, Osaka, BPO1, and BPO2.  `ForkRules` centralises opcode,
precompile, MODEXP, transaction, block, and blob-schedule rules; `ChainConfig`
selects a fork from block context.  The one interpreter is reached through
`stateTransitionAt`/`addBlockToChainAt` for static fixtures and
`stateTransitionUsing`/`addBlockToChainUsing` for configured transitions.  The
unparameterised public wrappers remain Prague wrappers.

| current suite | files | cases | candidate result |
|---|---:|---:|---|
| smoke (Prague sample) | 16 | 28 | 16/16 PASS |
| Osaka | 2,514 | 17,323 | 2,514/2,514 PASS |
| transitions: Prague→Osaka, Osaka→BPO1, BPO1→BPO2 | 13 | 109 | 13/13 PASS |
| Prague | 2,573 | 16,573 | pending as a component of `full` |
| full union | 5,100 | 34,005 | user-owned pending |

The upstream release contains no bare static BPO1/BPO2 files.  Those selectors
refuse zero-case runs; their 47 BPO-transition cases are covered by the
transition suite.  Historical forks and transitions ending in BPO3/BPO4 are
machine-generated exclusions with a fork-specific reason in
`scripts/mainnet/manifests.json`; unknown labels and zero selections fail.

## EIP-to-code/test disposition

The full audited table is retained in `scripts/report-osaka-step5.md`.  Its
completed execution rows are EIP-7823/7883 (MODEXP), 7939 (CLZ), 7951
(P256VERIFY), 7825 (transaction gas cap), 7594 (per-transaction blob cap),
7918 (blob reserve price), 7934 (original RLP size), and 7892 (Osaka/BPO blob
schedule data).  EIP-7607 supplies fork identity; EIP-7935 is a proposer
default, while EIP-7642 and EIP-7910 are out-of-scope networking/RPC work.
The BPO-specific three-number schedule and activation evidence are in
`scripts/report-bpo-step6.md`.  No executable EELS Prague→Osaka delta remains
unmapped.

## Exact candidate verification

All commands below used the candidate binaries built by `lake build` at the
start of this checkpoint (ELeVM: 1,760 jobs; Blanc: 907 jobs).  The original
report command for manifest checking omitted its mandatory fixture-root
argument; the actual successful command was:

```
python3 scripts/gen_mainnet_manifest.py \
  --fixtures-root "$HOME/eest-mainnet-v20.0.1/fixtures" --check
```

| gate | verdict |
|---|---|
| Python unit tests | 110 tests OK (13.02 s) |
| manifest regeneration | exact match to the pinned fixture tree |
| hygiene | 2 allowlisted occurrences; no new `dbg_trace`/`sorry` |
| U256 oracle | 21,593/21,593 PASS |
| strict vectors | 44/44 files PASS, 5/5 controls; 782 P256 cases PASS |
| PATCH / RLP4 | 10/10 PASS / 4/4 PASS |
| DEPTH / frozen SMOKE / BLS | 67 PASS / 173 PASS + 1 expected FAIL / 29 PASS |
| current smoke | 16/16 PASS in 0.54 s |
| current Osaka | 2,514/2,514 PASS in 498.47 s |
| current transitions | 13/13 PASS in 15.62 s |
| ELeVM and Blanc LSP diagnostics | clean on `Fork.lean`, `Execution.lean`, `Main.lean`, and `Blanc/Solvent.lean` |
| Blanc build and audit | build succeeds; 4/4 protected theorems clean |

`lean_verify` with source scanning recorded, for each protected theorem,
exactly `[propext, Classical.choice, Quot.sound]` and no warning:
`weth_inv_solvent`, `stateTransition_inv_solvent`, `chain_inv_solvent`, and
`addBlockToChain_inv_solvent`.  Their declarations were compared with the
Step-0 Blanc revision `f0d4616f22bb7e6a192860cc701fa813d06843d9`; their
statements are unchanged.

## Required user-owned long gates

Run these serially, with no competing Lean-LSP-heavy workload, on the exact
candidate commit above; preserve their complete reports and final verdicts.

```
cd ~/elevm
git checkout ce9426a0e72b77362f117fdc0a6475b1a683fb48
lake build
scripts/check.sh --full --no-build
scripts/check-mainnet.sh --suite full --no-build
```

The first must match the frozen legacy baseline (2,983 files: 2,978 PASS and
5 expected FAIL); the second must PASS every manifested supported case and
reject no entry for being unknown or zero-selected.  A red result must be
returned to its owning semantic step with the first failing file as reproducer;
do not rebase a baseline or change an exclusion during closure.

## Retained performance decision

The Lean 4.32.1 canary fixes the v4.23 UInt64 CSE code-generation failure, but
`Hash.fB64` deliberately retains the `B64.rdnc` read.  The re-baseline found
no fixture-level regression (SMOKE parity and BLS 20.6% faster); allocator and
refcount work remains a separate future plan.  The before/after benchmark and
profile tables, including the conclusion that allocation/refcount cost remains
47–57% of busy samples, are retained verbatim in
`scripts/report-toolchain-v4321-migration.md`.

## Commit ledger and scope

The complete ordered ledger before this report-only commit is:

```
ELeVM: aa8724a 34a42fa b0f5f0b 24d0c5b f3679ea a291c79 377ef61 1d0e060
       839f442 78fea35 52f5107 306f4c8 6b23493 c61ff3b 28a35b6 bc20ef9
       e1f9eda feb7128 1bfbfc0 0196ace f4dbe2e c2a4a20 598046f f27b9af
       a40871b f2e275b 394ee6f ce9426a
Blanc: fd07b41 ae97841 46fc74f 92ebe94 18a08d9 78d9d02 50bec5d 0d8e2de
       9e66c9c a66fd9d 36c4ec3
```

The feature-level purpose and pre-commit gates are recorded in the Step-1,
Step-2, Step-4, Step-5, and Step-6 reports.  The latest independently green
semantic commits are ELeVM `a40871b` and Blanc `36c4ec3`; this ELeVM report
commit is documentation only.  All listed migration commits were pushed to
`origin/codex/migration`; none was merged, rebased, squashed, force-pushed, or
deleted.

No legacy baseline, bootstrap implementation, strict current manifest,
`Hash.fB64`, or unrelated allocator/refcount code changed in this checkpoint.
The old fixture lane remains a frozen regression corpus and v20.0.1 remains the
canonical current-mainnet source.  The only human decision pending is the two
long-gate verdicts followed by protected-branch integration approval.
