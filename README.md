# Jaune

[![CI](https://github.com/skbaek/jaune/actions/workflows/ci.yml/badge.svg)](https://github.com/skbaek/jaune/actions/workflows/ci.yml)

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

`lake build`

## Usage

`lake exe jaune /path/to/test`

## External test fixtures

The fixture suites use pinned data outside this repository. See
[`scripts/vectors/SOURCES.md`](scripts/vectors/SOURCES.md) for the safe
execution-specs/legacy-fixture and EEST bootstrap, frozen Python oracle,
environment doctor, path overrides, disk requirements, and long-test
requirements.

## Verification status

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
- **Conformance tiers** ([`scripts/check.sh`](scripts/check.sh)), each compared
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

## Portability checks in CI

CI preserves the ordinary Lean build and separately runs the standard-library
unit suite for the source manifest, read-only doctor, legacy/EEST/oracle
bootstraps, malicious archive handling, and generator path/pin checks. The
tests create only tiny synthetic Git repositories and fixture archives in their
temporary workspace; CI never downloads the EEST release or a complete legacy
fixture corpus. A separate no-toolchain hygiene job
([`scripts/check-hygiene.sh`](scripts/check-hygiene.sh)) fails the build if any
`dbg_trace` or `sorry` appears under `Jaune/` outside the justified allowlist
([`scripts/hygiene-allow.txt`](scripts/hygiene-allow.txt)).

The workflows intentionally use maintained major-version action tags
(`actions/checkout@v6`, `actions/setup-python@v5`, and
`leanprover/lean-action@v1`) instead of immutable commit SHAs. Review the
corresponding official action release notes before a tag update, and keep that
policy consistent within Jaune.
