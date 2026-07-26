# ELEVM

[![CI](https://github.com/skbaek/elevm/actions/workflows/ci.yml/badge.svg)](https://github.com/skbaek/elevm/actions/workflows/ci.yml)

Executable Lean EVM (ELEVM) is an implementation of the Ethereum Virtual Machine 
(EVM) in the Lean 4 theorem prover. ELEVM can run EVM state tests in the standard JSON 
format of [execution spec tests](https://github.com/ethereum/execution-spec-tests). 
It passes all general state tests used by the latest version[^1] of 
[execution-specs](https://github.com/ethereum/execution-specs) on the `mainnet` branch.

## Prerequisite

You need to have [elan](https://github.com/leanprover/elan) installed.

## Installation

`lake build`

## Usage

`lake exe elevm /path/to/test`

## External test fixtures

The fixture suites use pinned data outside this repository. See
[`scripts/vectors/SOURCES.md`](scripts/vectors/SOURCES.md) for the safe
execution-specs/legacy-fixture and EEST bootstrap, frozen Python oracle,
environment doctor, path overrides, disk requirements, and long-test
requirements.

## Verification status

- **Tested fork:** Prague. ELEVM's frozen legacy corpus remains a regression
  instrument. The canonical current-mainnet lane is the separately installed
  `execution-specs` `tests@v20.0.1` release; its strict generated manifests
  activate Prague as a whole suite (`scripts/check-mainnet.sh --suite prague`,
  or the deterministic `--suite smoke`) and inventory later forks and
  transitions.
- **Osaka is in progress and not claimed as supported.** Its VM-level delta is
  implemented — EIP-7823 and EIP-7883 (`MODEXP` input bounds and repricing),
  EIP-7939 (`CLZ`), and EIP-7951 (`P256VERIFY`) — and each of those EIPs' own
  fixture subtrees passes in full under
  `scripts/check-mainnet.sh --suite osaka --dir <subtree>`. The transaction,
  blob-fee, and block-validation delta is not implemented, so `--suite osaka`
  as a whole is deliberately refused rather than run and reported. BPO1 and
  BPO2 remain identities without rules.
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
- **Conformance tiers** ([`scripts/check.sh`](scripts/check.sh)), each compared
  against a committed baseline. The gate passes iff **every** file's PASS/FAIL
  matches its baseline — a regression gate, not an all-green one:

  | tier | files | committed baseline |
  |---|---|---|
  | `--depth` | 67 | all PASS |
  | `--smoke` | 175 | 174 PASS, 1 FAIL |
  | `--bls` | 29 | all PASS (hand-authored target) |
  | `--full` | 2983 | 2978 PASS, 5 FAIL |

  `--full` is the entire `BlockchainTests` corpus, dominated by the
  `GeneralStateTests/` subtree — which passes **2633 of 2634**. The five
  baselined FAILs are four under `InvalidBlocks/` (fixtures encoding invalid
  blocks) plus one Cancun-variant EIP-1559 case
  (`GeneralStateTests/stEIP1559/intrinsicCancun.json`); each is the committed
  expected classification (see the per-tier `scripts/baseline-*.txt`).

## Portability checks in CI

CI preserves the ordinary Lean build and separately runs the standard-library
unit suite for the source manifest, read-only doctor, legacy/EEST/oracle
bootstraps, malicious archive handling, and generator path/pin checks. The
tests create only tiny synthetic Git repositories and fixture archives in their
temporary workspace; CI never downloads the EEST release or a complete legacy
fixture corpus. A separate no-toolchain hygiene job
([`scripts/check-hygiene.sh`](scripts/check-hygiene.sh)) fails the build if any
`dbg_trace` or `sorry` appears under `Elevm/` outside the justified allowlist
([`scripts/hygiene-allow.txt`](scripts/hygiene-allow.txt)).

The workflows intentionally use maintained major-version action tags
(`actions/checkout@v6`, `actions/setup-python@v5`, and
`leanprover/lean-action@v1`) instead of immutable commit SHAs. Review the
corresponding official action release notes before a tag update, and keep that
policy consistent within ELEVM.

[^1]:As of 2025/09/19, commit [`4198...7694`](https://github.com/ethereum/execution-specs/tree/4198b9c5996713b268aed602739d5aa40e277694)
