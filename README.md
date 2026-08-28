# Jaune

[![CI](https://github.com/skbaek/jaune/actions/workflows/ci.yml/badge.svg)](https://github.com/skbaek/jaune/actions/workflows/ci.yml)

**[skbaek.github.io/jaune](https://skbaek.github.io/jaune/)** — the guided
tour: claim, evidence, trust boundaries, roadmap.
**[Blanc](https://github.com/skbaek/blanc)**
([site](https://skbaek.github.io/blanc/)) — the sibling project: a contract
language that compiles through a verified compiler and proves its contracts
against these semantics. It is Jaune's end-to-end case study.

**Jaune** is an executable formal specification of the EVM in Lean 4. Its
strict current-mainnet lane passes **5,100/5,100 supported fixture files and
34,005/34,005 cases**, Prague through BPO2 including configured transitions,
against [execution-specs](https://github.com/ethereum/execution-specs)
`tests@v20.0.1`. Its semantics are demonstrated sufficient for real
verification: a WETH implementation's solvency is proven to be preserved over
every state reachable along a valid configured chain, including histories that
cross scheduled fork activations, through a verified compiler, with no `sorry`
and no `native_decide` in the trusted path. Jaune is MIT-licensed.

Jaune was originally written from the Yellow Paper, then rebuilt on a pinned
2025 execution-specs revision; later forks were implemented and checked
explicitly. The frozen legacy fixture corpus is retained as independently-filled
regression evidence; its five non-passing files are diagnosed, and none is a
defect in Jaune, as described under Verification status.

## Prerequisite

You need to have [elan](https://github.com/leanprover/elan) installed.

## Installation

```sh
lake exe cache get Mathlib/Data/Nat/Basic.lean Mathlib/Data/List/Lemmas.lean \
  Mathlib/Data/List/TakeDrop.lean Mathlib/Data/List/TakeWhile.lean \
  Mathlib/Data/UInt.lean Mathlib/Tactic/NormNum.lean \
  Mathlib/Data/List/Chain.lean
lake build
```

Jaune depends on mathlib. `lake exe cache get` downloads prebuilt artifacts;
without it `lake build` compiles mathlib from source, which takes hours rather
than the minute the build itself needs.

Those seven files are Jaune's entire mathlib import surface — the exact set
returned by `grep -rh '^import Mathlib' Jaune/ Jaune.lean Main.lean`. Naming
them fetches only the modules that surface transitively depends on, instead of
every artifact in mathlib, which is what a bare `lake exe cache get` does.
Expect a few hundred MB under `.lake/` rather than several GB, and a
correspondingly shorter first build. A bare `lake exe cache get` still works
and is the right choice if you intend to import more of mathlib yourself.

## Usage

`lake exe jaune /path/to/fixture.json`

Runs one blockchain-test fixture file. The fixture corpora are not in this
repository; install the pinned current-mainnet release first, and run fixtures
from its `blockchain_tests` directory:

```sh
python3 scripts/bootstrap_mainnet.py     # ~/eest-mainnet-v20.0.1
FIX=~/eest-mainnet-v20.0.1/fixtures/blockchain_tests
lake exe jaune $FIX/for_prague/ported_static/vmArithmeticTest/mul/mul.json
```

EEST fills one test into sibling trees — `blockchain_tests`,
`blockchain_tests_engine`, `blockchain_tests_engine_x`, `state_tests` and
`transaction_tests` — under a single file name. Only `blockchain_tests` is this
runner's; the rest describe a different consumer, and a file from one of them is
refused by name rather than run.

Every option is a filter: each one only narrows the set of cases that run, and
the selection is always narrowed to the networks this build supports. The run
fails if no case survives, so a green run never means "nothing was checked".

Given no `--network`, every supported case in the file runs under the rules its
own `network` label names. A file holding a mix of networks contributes its
supported part; one whose cases all predate Prague is reported as out of scope
rather than passing vacuously.

| option | means |
|---|---|
| `--network <label>` | run only cases at this network; not repeatable |
| `--name <case>` | run only these cases; repeatable |
| `--notName <case>` | skip these cases; repeatable |
| `--index <n>` | run only the case at this index |

`lake exe jaune --help` prints the supported network labels. It derives them
from the build rather than from a written list, so they cannot drift.

The runner takes exactly one file. Fixture *trees* are enumerated by
`scripts/check-legacy.sh --dir`, which records a classification per file against a
baseline — see [`scripts/GATES.md`](scripts/GATES.md). The alternate modes
`--vectors <address> <file>`, `--u256 <file>`, and `--fake-exp <file>` run the
pinned differential oracles and are likewise driven by those gates.

## The `t8n` transition tool

`lake exe jaune t8n` reads a pre-state (`alloc`), an environment (`env`) and a
transaction list (`txs`), executes one state transition outside any
block-validation context, and emits `result` and the post-state `alloc`. This
is the interface every transition tool in the ecosystem exposes, and it is how
a test framework, a differential campaign or a third-party cross-check drives
an implementation without bespoke integration.

```sh
lake exe jaune t8n \
  --input.alloc alloc.json --input.env env.json --input.txs txs.json \
  --output.result result.json --output.alloc out-alloc.json \
  --state.fork Prague --state.chainid 1
```

Inputs may be read from a single stdin document instead, by naming `stdin` as
any `--input.*` value; outputs may be written to `stdout` the same way.
Options accept `--flag value` and `--flag=value` alike. `--state-test` applies
exactly one transaction with no system operations.

**The supported lane is Prague, Osaka, BPO1 and BPO2** — the same forks the
fixture runner supports, and unsupported input fails closed. There is no
default fork and no fallback: an out-of-lane `--state.fork`, a missing one, an
unrecognised flag, an unrecognised input field, and the RLP-string form of
`txs` are each an explicit error with a non-zero exit. Tracing is not claimed,
so `--trace`, its variants and `--opcode.count` are refused rather than
ignored.

`lake exe jaune t8n --info` is the handshake: the version, the Lean toolchain,
the fork lane, the modes, and the corpus and oracle pins, all read from
[`scripts/sources.json`](scripts/sources.json) rather than restated.
`lake exe jaune t8n --forks` prints the lane alone, on one line, from any
working directory; `lake exe jaune -v` prints the banner a framework
identifies the binary by.

Conformance is gated. `scripts/check-t8n.sh` compares nine cases against
goldens generated from a pinned `execution-specs` revision, with every
normalization and declared difference explicit — see
[`scripts/t8n/README.md`](scripts/t8n/README.md) for the corpus, the
generator, and the registry of declared differences.

**Case study:** [What a full-output reader sees in
`t8n`](https://skbaek.github.io/jaune/t8n-case-study.html) records a pinned three-way
comparison with EELS and Geth: two transition-tool emission divergences, why
the ordinary fixture path did not expose them, their upstream filings, and the
exact boundaries: no consensus impact, and no known fixture-corpus impact.

## External test fixtures

The fixture suites use pinned data outside this repository. See
[`scripts/vectors/SOURCES.md`](scripts/vectors/SOURCES.md) for the safe
execution-specs/legacy-fixture and EEST bootstrap, frozen Python oracle,
environment doctor, path overrides, disk requirements, and long-test
requirements.

## Verification status

- **What you are trusting** — [`TRUSTED.md`](TRUSTED.md) states the trusted
  base exactly: the kernel and pins, the axioms, what is deliberately absent
  and which gate enforces each absence, the known exceptions, and where the
  line between testing and proof falls. Every figure in it names the command
  that regenerates it.
- **SHA-256 computes the published function, by theorem.**
  [`Jaune/SHA256Spec.lean`](Jaune/SHA256Spec.lean) transcribes NIST FIPS 180-4
  section by section, and `Jaune.Bytes.sha256_eq_fips` proves the optimized
  kernel equal to that transcription for every input, with the standard axioms
  and no `sorry`. It is the only hash here whose conformance rests on a theorem
  rather than on differential vectors and fixtures — and the reader still owes
  the transcription a read, which is the point of citing the standard at every
  declaration. [`TRUSTED.md`](TRUSTED.md) states exactly what the theorem does
  and does not claim.
- **Supported forks:** Prague, Osaka, BPO1, and BPO2, plus the transitions
  between them. Jaune's primary Prague evidence is the strict all-PASS
  current-mainnet lane over the separately installed `execution-specs`
  `tests@v20.0.1` release: 2,573/2,573 Prague fixtures and 5,100/5,100 across
  the whole manifest, with no expected-failure allowance. Its generated
  manifests activate Prague as a whole suite
  (`scripts/check-mainnet.sh --suite prague`, or the deterministic
  `--suite smoke`).
- **Static Osaka is supported.** Its complete execution delta is implemented:
  EIP-7823 and EIP-7883 (`MODEXP` bounds/repricing), EIP-7939 (`CLZ`), EIP-7951
  (`P256VERIFY`), EIP-7825 (transaction gas cap), EIP-7594 (six blobs per
  transaction), EIP-7918 (blob reserve price), and EIP-7934 (original block-RLP
  size). `scripts/check-mainnet.sh --suite osaka` is a strict all-PASS gate;
  the pinned manifest is 2,514/2,514 files (17,323 cases).
- **BPO1 and BPO2 are supported as rule data** (EIP-7892): each is Osaka with a
  different blob target, ceiling, and base-fee update fraction, and nothing
  else. A chain selects them from its own activation schedule, so a fixture
  labelled `OsakaToBPO1AtTime15k` runs through the configured block-import API
  and each block's timestamp chooses its rules.
  `scripts/check-mainnet.sh --suite transitions` is a strict all-PASS gate over
  the 13 files (109 cases) whose transition labels name two supported forks.
  The pinned release publishes no fixture whose network is a bare `BPO1` or
  `BPO2`, so `--suite bpo1` and `--suite bpo2` select nothing and are refused
  rather than reported as vacuously green.
- **Reference:** mirrors [execution-specs](https://github.com/ethereum/execution-specs)
  `mainnet` at commit
  [`4198…7694`](https://github.com/ethereum/execution-specs/tree/4198b9c5996713b268aed602739d5aa40e277694)
  (as of 2025-09-19).
- **Pinned fixture corpora** — never committed here; provisioned by
  `scripts/bootstrap_*.py`, with provenance in
  [`scripts/sources.json`](scripts/sources.json) and
  [`scripts/vectors/SOURCES.md`](scripts/vectors/SOURCES.md):
  - *legacy* — `ethereum/tests` @ `3129f16` (plus its `LegacyTests` @ `2339b9a`);
  - *EEST* — release `v5.4.0` (SHA-256 `92cf1b47…`).
  - *current mainnet* — `execution-specs` `tests@v20.0.1` @ `87aba1a`, asset
    SHA-256 `3586193d…`; installed separately at `~/eest-mainnet-v20.0.1`.
- **Gate catalogue** — [`scripts/GATES.md`](scripts/GATES.md) is the
  authoritative reference for every verification gate: exact commands, pass
  criteria, runtimes, and which gate to reach for when. Both fixture harnesses
  take `--jobs auto` to run in parallel, which roughly halves the legacy corpus
  and quarters the current-mainnet one.
- **Conformance tiers** ([`scripts/check-legacy.sh`](scripts/check-legacy.sh)), each compared
  against a committed baseline. The gate passes iff **every** file's PASS/FAIL
  matches its baseline — a regression gate, not an all-green one:

  | tier | files | committed baseline |
  |---|---|---|
  | `--depth` | 67 | all PASS |
  | `--smoke` | 174 | 173 PASS, 1 FAIL |
  | `--bls` | 29 | all PASS (hand-authored target) |
  | `--full` | 2983 | 2978 PASS, 5 FAIL (diagnosed; none a Jaune defect) |

  The frozen `ethereum/tests` corpus is retained as an independently-filled
  regression instrument. Its `--full` tier is the entire `BlockchainTests`
  corpus, dominated by the `GeneralStateTests/` subtree — which passes
  **2633 of 2634**. Its five baselined FAILs are diagnosed, and none is a
  defect in Jaune: two
  (`stEIP1559/intrinsicCancun.json`, `bcEIP1559/intrinsicOrFailCancun.json`)
  are the corpus's only two fixtures with no case in the supported fork
  range, refused under the fail-closed era policy above rather than reported
  as a vacuous pass; the other three, under `InvalidBlocks/bcStateTests/`,
  are multiply-invalid fixtures whose pipe-separated expected-exception
  alternatives reflect their fill generator's check ordering (evmone tests
  the fee cap before intrinsic gas) and omit the specification's: the frozen
  EELS oracle validates intrinsic gas first and reports exactly the identity
  Jaune reports, on all three (see the per-tier `scripts/baseline-*.txt`).

## Semantic integrity

Jaune closes the P0 semantic-integrity gaps identified in review — chain-ID
agreement, prestate/tip binding, wire-vs-freely-constructed transactions,
canonical state/structural representation, fail-closed era support before a
chain's earliest implemented fork, removal of non-fuel panic/partial paths,
and typed internal errors. See
[`scripts/report-integrity.md`](scripts/report-integrity.md) for the full
closure report.

- **Checked entry points are the recommended API.** `CheckedBlockChain` binds
  an executable snapshot to canonical state, validated hash-linked/
  consecutively numbered retained history (sufficient for `BLOCKHASH`), and
  tip-state-root agreement; `ConfiguredChain` additionally validates a
  `ChainConfig`'s activation schedule and its chain-ID agreement with the
  snapshot, once. Repeated transitions and imports reuse these witnesses
  instead of recomputing a trie root on every call.
  `CanonicalBlock.ofRlp? : Bytes → Option CanonicalBlock` is the checked wire
  ingress. `CanonicalBlock`'s constructor is private, so the only route to a
  value is the evidence-taking smart constructor `CanonicalBlock.ofDecode`,
  which demands the strict decoder's own equation; a successful decode
  therefore proves both the strict outer-block decoder image and the exact
  `block.toBLT.toBytes = raw` round trip, so a hand-built
  `Block`/`Header`/`Tx` cannot be certified through it.
- **Raw compatibility entry points remain** — `stateTransitionWith/At/Using`,
  `addBlockToChainWith/At/Using`, `stateTransition`, `addBlockToChain`,
  `rlpToBlock`, and friends — for existing callers and proof statements that
  name them by type. They validate configured chain-ID agreement and
  schedule usability up front, but a raw call does not itself recompute the
  checked-snapshot invariants above on every invocation; build and store a
  `CheckedBlockChain`/`ConfiguredChain` once and drive repeated execution
  from it instead.
- **Configured execution fails closed** before a chain's earliest
  implemented era rather than assuming every schedule's first activation
  sits at timestamp zero; the failing call reports which era is unsupported
  as a typed `SupportError`, not a silent default.
- **Core semantics uses typed errors, not strings.**
  `ChainContextError`, `DecodeError`, `EvmError`, `TxValidationError`,
  `BlockValidationError`, and `InternalError` are the internal
  discriminants that producers construct directly; `String` remains only at
  external parsing/rendering/fixture-compatibility boundaries.
  [`scripts/check-integrity.sh`](scripts/check-integrity.sh) enforces this
  as a shrink-only gate over panic, raw bang operations, and stringly-typed
  semantic carriers in `Jaune.lean`'s import closure — see
  [`scripts/GATES.md`](scripts/GATES.md).

## What CI checks, and what it does not

Three workflows run against this repository. What each one covers is worth
stating exactly, because the badge above reports only the first of them.

- **`ci.yml` (every push and pull request)** preserves the ordinary Lean build
  and separately runs the standard-library unit suite for the source manifest,
  read-only doctor, legacy/EEST/oracle bootstraps, malicious archive handling,
  and generator path/pin checks. These portability tests create only tiny
  synthetic Git repositories and fixture archives in their temporary workspace
  — they never download the EEST release or a complete legacy fixture corpus.
  A separate no-toolchain hygiene job
  ([`scripts/check-hygiene.sh`](scripts/check-hygiene.sh)) fails the build if
  any `dbg_trace` or `sorry` appears under `Jaune/` outside the justified
  allowlist ([`scripts/hygiene-allow.txt`](scripts/hygiene-allow.txt)).
  After the build, two gates that need nothing but the binary run in the same
  job: [`scripts/check-t8n.sh`](scripts/check-t8n.sh), which checks the `t8n`
  frontend byte-identical to goldens generated from the pinned conformance
  target and deterministic across two runs, and
  [`scripts/check-u256.sh`](scripts/check-u256.sh) over the word and hash
  primitives. Together they cost about a second.
- **`smoke.yml` (every push and pull request)** classifies 174 files of the
  frozen legacy corpus against [`scripts/baseline-smoke.txt`](scripts/baseline-smoke.txt).
- **`nightly.yml` (daily, 07:00 UTC)** provisions both corpora and runs the
  full legacy tier (2,983 classifications against
  [`scripts/baseline-full.txt`](scripts/baseline-full.txt)) and the EEST BLS
  tier.

**The current-mainnet suite is not a CI gate.** The headline result on this
page — 5,100/5,100 supported fixture files, 34,005/34,005 cases — is produced
by [`scripts/check-mainnet.sh`](scripts/check-mainnet.sh), which runs locally
against a corpus this repository does not vendor. So does
[`scripts/check-integrity.sh`](scripts/check-integrity.sh). A green badge
attests to the build, the hygiene gate, and the legacy tiers; it does not
attest to the current-mainnet number. [`scripts/GATES.md`](scripts/GATES.md) is
the authoritative catalogue of which gate checks what, and where each runs.

The workflows intentionally use maintained major-version action tags
(`actions/checkout@v6`, `actions/setup-python@v5`, and
`leanprover/lean-action@v1`) instead of immutable commit SHAs. Review the
corresponding official action release notes before a tag update, and keep that
policy consistent within Jaune.

## Contact

Jaune is maintained by one person, [skbaek](https://github.com/skbaek)
(<seulkeebaek@gmail.com>). There is no team behind it and no service-level
promise; expect a reply within about a week.

Four things are actively wanted, in descending order of how much they are
wanted:

1. **A divergence.** If Jaune disagrees with a client, with
   [execution-specs](https://github.com/ethereum/execution-specs), or with your
   own implementation on any input, that is the most useful thing you can send.
   Open an issue with the input, the fork, and the pins. It does not matter
   whether the divergence turns out to be Jaune's fault — it has already been
   both ways.
2. **A claim that outruns its proof**, here or on the site. See
   [`SECURITY.md`](SECURITY.md).
3. **A workflow this does not fit.** If you looked at the `t8n` frontend and it
   could not slot into your differential or testing setup, the specific reason
   is worth more than a feature request.
4. **Patches**, which are welcome but not the bottleneck. There is no
   `CONTRIBUTING.md` yet; open an issue first and the shape of the change can
   be settled there.

Issues on this repository are read. So is the mail.
