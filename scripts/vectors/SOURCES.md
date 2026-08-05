# Pinned sources for compact MSM vectors and EEST fixtures

The external-source facts on this page (execution-specs, ethereum/tests,
LegacyTests, and EEST) are also recorded machine-readably in
[`scripts/sources.json`](../sources.json), the single manifest that later
bootstrap tooling and generators are expected to consume rather than
duplicating these literals. [`scripts/env_doctor.py`](../env_doctor.py) is a
read-only, Python-standard-library-only diagnostic that checks the current
checkouts, the EEST archive/extraction, and the Python oracle venv against
that manifest; it never downloads, clones, installs, or repairs anything.
Run it with `python3 scripts/env_doctor.py` (add `--json` for machine-readable
output); pass `--execution-specs`, `--eest-root`, or `--venv` to point it at
non-default locations, or `--manifest` to check against a different manifest
file entirely. Its `EEST_ROOT` override is a doctor-specific variable naming
the top-level EEST install directory (containing the archive and its
extracted `fixtures/` tree); it is distinct from `scripts/check-legacy.sh`'s
`JAUNE_FIXTURES`, which instead points directly at a tier's leaf fixture
directory.

The EEST checks come in two depths. The default *fast* check verifies the
archive's SHA-256 when the archive is present, the extracted top-level fixture
directories, the exact leaf directories the `--bls` tier consumes, and the
release provenance recorded in the tree's own `fixtures/.meta/fixtures.ini`.
Adding `--eest-deep` additionally streams the release archive and compares it
file-by-file against the extracted tree, hashing every fixture to detect any
changed, missing, or extra file. Deep mode reads far more data and is
correspondingly slower, but stays bounded in memory; it is intended for
occasional integrity audits rather than every run.

The repository CI exercises the manifest, doctor, bootstrap, archive-safety,
and generator argument/pin behavior only with tiny synthetic inputs. It never
downloads the EEST release, the full legacy corpus, or the frozen oracle
packages. Run the bootstrap and long fixture tiers locally only when their
network, disk, and runtime requirements above are available.

## Canonical current-mainnet lane

The current conformance source is
[`execution-specs` `tests@v20.0.1`](https://github.com/ethereum/execution-specs/releases/tag/tests%40v20.0.1),
resolved to commit `87aba1a38a476b31f819a2390eb481527e6dc683`. Its official
`fixtures.tar.gz` asset has SHA-256
`3586193db06d4d5745d5e90b3c3008c2255a4e19ccd8f11a3ce887aec8c0b17c`.
Install it separately from frozen EEST material:

```sh
python3 scripts/bootstrap_mainnet.py                 # ~/eest-mainnet-v20.0.1
python3 scripts/env_doctor.py --mainnet-root ~/eest-mainnet-v20.0.1 --mainnet-deep
```

The extracted tree occupies about 7.9 GB and the archive about 404 MB. Allow at
least 13 GB of free space in the destination filesystem for a fresh install
(archive plus tree plus transient staging). The download is a single public
GitHub release asset; exact transfer time depends on your connection. Of the
extracted trees only `blockchain_tests` (3.6 GB) is the runner's; the rest are
kept as shipped because the release is verified whole against the publisher's
manifest, and a pruned tree would no longer match it.

The asset is verified before extraction. Its `fixtures/.meta/index.json` is
also checked for the publisher's root hash, timestamp, and case count. Generate
or verify the exact suite/exclusion inventory with
`scripts/gen_mainnet_manifest.py`; never edit `scripts/mainnet/manifests.json`
by hand. `scripts/check-mainnet.sh --suite smoke` and `--suite prague` execute
only generated Prague entries with an explicit `--network Prague`; Osaka, BPO,
and transition labels remain inventoried and fail closed until their owning
migration steps activate them.

## Legacy fixture Git bootstrap

[`scripts/bootstrap_legacy.py`](../bootstrap_legacy.py) safely creates the
Git-backed sources used by the ordinary fixture tiers:

1. execution-specs, detached at the manifest commit;
2. the ignored, independent `tests/fixtures/ethereum_tests` checkout, detached
   at its manifest commit; and
3. only that checkout's required `LegacyTests` submodule, at the manifest
   gitlink commit.

Preview a fresh install without network or filesystem changes:

```sh
python3 scripts/bootstrap_legacy.py --dry-run
```

Install to the compatible default `~/execution-specs`, or select another
destination explicitly:

```sh
python3 scripts/bootstrap_legacy.py
python3 scripts/bootstrap_legacy.py --execution-specs "/path/with spaces/execution-specs"
EELS_ROOT="/another/path/execution-specs" python3 scripts/bootstrap_legacy.py
```

`--execution-specs` takes precedence over `EELS_ROOT`; otherwise the
manifest's home-relative default is used. The current known-good installation
occupies about 5.9 GB. Allow at least 7 GB of free space in the destination
filesystem and expect several gigabytes of public GitHub network transfer;
actual transfer size and duration depend on Git and server compression. The
bootstrap does not install Python packages or EEST fixtures.

The command builds a missing destination in a temporary sibling, verifies all
three repositories, and then places it atomically where the filesystem
supports an ordinary sibling rename. A fully correct existing installation is
an offline no-op. Any other existing target—empty, nonempty, partial, dirty,
at the wrong revision, or using an unexpected origin—is refused without
repair or overwrite.

After an interrupted process, the final destination is either absent or was
already fully placed. Inspect any sibling named
`.execution-specs.bootstrap-*` before removing it manually. For a refused
destination, inspect it and either move/remove it yourself only when certain
it is disposable, or choose a different `--execution-specs` path; the command
intentionally has no force/repair mode. Verify the finished environment with:

```sh
python3 scripts/env_doctor.py --legacy-only \
  --execution-specs "/path/to/execution-specs"
```

Omit `--legacy-only` to also diagnose the EEST and Python components handled
by later portability steps.

The test harness's existing `JAUNE_FIXTURES` override is unchanged and points
directly to `BlockchainTests`, not to the execution-specs root.

## EEST blockchain fixtures (`--bls` tier)

The `--bls` tier of `scripts/check-legacy.sh` runs EEST consensus fixtures that are
too large to vendor. They come from one pinned execution-spec-tests fixture
release, unpacked outside the repo at `~/eest-fixtures/fixtures/`:

| Release tag | File | SHA-256 |
| --- | --- | --- |
| [`v5.4.0`](https://github.com/ethereum/execution-spec-tests/releases/tag/v5.4.0) | `fixtures_stable.tar.gz` | `92cf1b47ad12fb27163261fc3c1cea5df72439cab507983d06b56c94f8741909` |

The tier reads `blockchain_tests/prague/eip2537_bls_12_381_precompiles/` and
the point-evaluation files under `blockchain_tests/cancun/eip4844_blobs/`
(their cases are regenerated per network; the tier selects the Prague ones).

### Safe EEST bootstrap

[`scripts/bootstrap_eest.py`](../bootstrap_eest.py) acquires this release
safely from the manifest's EEST fields. It installs into the top-level
`EEST_ROOT` directory (default `~/eest-fixtures`), which holds both the
release archive and its extracted `fixtures/` tree:

```sh
python3 scripts/bootstrap_eest.py --dry-run          # plan only, no changes
python3 scripts/bootstrap_eest.py                     # install to ~/eest-fixtures
python3 scripts/bootstrap_eest.py --eest-root "/data/eest fixtures"
```

`--eest-root` (or `$EEST_ROOT`) selects the install directory;
`--archive-cache` overrides where the archive is read from and stored
(default `<eest-root>/fixtures_stable.tar.gz`). Point `--archive-cache` at an
already-downloaded copy to install fully offline.

The command:

- reuses an already-present archive whose SHA-256 matches, with no network
  access; otherwise downloads once to a `*.part` file, verifies the checksum
  **before** extraction, and only then promotes it by an atomic rename;
- extracts through a member-by-member validator that refuses absolute paths,
  `..` traversal, symlinks, hardlinks, and device/special members, staging the
  tree in a temporary sibling and placing it atomically at
  `<eest-root>/fixtures`;
- verifies the extracted layout, `--bls` tier directories, and release
  provenance before placement;
- treats a fully correct existing installation as an offline no-op.

The extracted tree occupies about 4.1 GB and the archive about 250 MB. Allow
at least 9 GB of free space in the destination filesystem for a fresh install
(archive plus tree plus transient staging). The download is a single public
GitHub release asset; exact transfer time depends on your connection.

Any existing but non-matching state is refused, never repaired: a cached
archive with the wrong checksum, a partial or modified `fixtures/` tree, or a
tree with the wrong provenance all stop the command with recovery guidance.
The bootstrap never deletes, resets, or overwrites an existing fixture tree.
After an interruption the final `fixtures/` directory is either absent or was
already fully placed; inspect any leftover `.fixtures.bootstrap-*` staging
sibling or `fixtures_stable.tar.gz.part` file and remove it manually if you
are certain it is disposable. Verify a finished installation, including a full
integrity audit, with:

```sh
python3 scripts/env_doctor.py --eest-root ~/eest-fixtures --eest-deep
```

The four committed `*.head.json` files contain the first 32 entries of their
full upstream vectors. Regenerate them with the committed `jq '.[0:32]'`
commands in `scripts/check-vectors.sh`; do not hand-edit them.

## Frozen Python oracle environment

[`scripts/oracle/requirements.in`](../oracle/requirements.in) records the
complete 18-package runtime closure observed in the known-good oracle, and
[`scripts/oracle/requirements.lock`](../oracle/requirements.lock) is uv's
transitive lock with exact versions and package-distribution SHA-256 hashes.
The lock deliberately contains no editable or local-path
`ethereum-execution` entry. Both generators instead validate and import the
checkout pinned independently by `scripts/sources.json`.

Python **3.11.9 is exact** for this environment. A different patch release is
a failure rather than a warning because the oracle includes native extension
wheels and generated artifacts are accepted only from the interpreter/package
closure actually tested. This is stricter than execution-specs' general
`>=3.11` package metadata on purpose.

Create the environment after the execution-specs bootstrap:

```sh
EELS_ROOT="$HOME/execution-specs"
python3 scripts/bootstrap_oracle.py --execution-specs "$EELS_ROOT" --dry-run
python3 scripts/bootstrap_oracle.py --execution-specs "$EELS_ROOT"
python3 scripts/env_doctor.py --execution-specs "$EELS_ROOT" \
  --venv "$EELS_ROOT/venv"
```

`--execution-specs` takes precedence over `EELS_ROOT`, and `--venv` can select
a path containing spaces. The default venv remains
`<execution-specs>/venv`. A correct existing venv is a no-op. An existing venv
with the wrong interpreter, a missing/wrong/extra package, or a broken native
import is refused without mutation; inspect it and manually move/remove it
only if it is disposable, or choose another `--venv`.

The bootstrap builds a relocatable temporary sibling, syncs only the frozen
lock with required hashes, verifies it, and atomically places it. Inspect any
leftover `.venv.bootstrap-*` directory after interruption. Use `--offline` to
forbid all Python and package downloads; it succeeds only when uv already has
Python 3.11.9 and every locked artifact cached, and otherwise explains how to
prefill the cache or rerun with network access.

To audit or refresh the lock after an intentional source/version review:

```sh
uv pip compile --python 3.11.9 --python-version 3.11.9 --generate-hashes \
  scripts/oracle/requirements.in \
  --output-file scripts/oracle/requirements.lock
```

Any changed resolved version, changed generator bytes, local-path entry, or
need to loosen the execution-specs pin requires review rather than silently
updating the manifest's recorded lock hash.

## Interpreter for the unit-test suite

Most of `scripts/tests` is standard-library only, but two tests in
`test_generators.py` run the U256 generator and the pinned `keccak256` for
real, so they need the frozen oracle closure that `requirements.lock` pins for
generator execution. Run the suite with that interpreter to get full coverage:

```sh
"$EELS_ROOT/venv/bin/python" -m unittest discover -s scripts/tests
```

Plain `python3 -m unittest discover -s scripts/tests` is also green. The two
tests accept the interpreter running the suite when it already has the closure,
fall back to the manifest-default `<execution-specs>/venv/bin/python`, and
otherwise skip with a message naming that venv and `scripts/bootstrap_oracle.py`
instead of failing. `OK (skipped=2)` therefore means the oracle venv was not
discoverable, not that the generators are unverified — create the venv as
above and rerun for the full 80.

The remaining generator tests stay on whichever interpreter runs the suite on
purpose: they assert checkout-validation refusals, which happen before the
package gate and the pinned import and are interpreter-independent.

## BLS constants generator

`Jaune/BLSConst.lean` is generated from the following pinned local sources:

- execution-specs commit
  [`4198b9c5996713b268aed602739d5aa40e277694`](https://github.com/ethereum/execution-specs/tree/4198b9c5996713b268aed602739d5aa40e277694)
- `py-ecc` version `8.0.0`, installed in that checkout's venv

The generator does not clone repositories or install dependencies. Point it at
an existing checkout; it reads both pins from the shared manifest before
producing output:

```sh
EELS_ROOT="$HOME/execution-specs"
"$EELS_ROOT/venv/bin/python" scripts/gen-bls-consts.py \
  --execution-specs "$EELS_ROOT" --output Jaune/BLSConst.lean
```

`EELS_ROOT` may be used instead of the command-line option. To verify the
committed constants without replacing them:

```sh
"$EELS_ROOT/venv/bin/python" scripts/gen-bls-consts.py \
  --execution-specs "$EELS_ROOT" --output /tmp/BLSConst.lean
cmp /tmp/BLSConst.lean Jaune/BLSConst.lean
```

## U256 differential vectors

`scripts/gen-u256-vectors.py` uses only the standard library for its formulas,
but it now enforces the same manifest-pinned checkout and expected Prague
source layout as the BLS generator. The explicit path wins over `EELS_ROOT`;
neither script embeds a home-directory username.

Generate to a disposable output and compare without touching the committed
artifact:

```sh
"$EELS_ROOT/venv/bin/python" scripts/gen-u256-vectors.py \
  --execution-specs "$EELS_ROOT" --output /tmp/u256.json
cmp /tmp/u256.json scripts/vectors/u256.json
```

## EIP-2537 vectors

Source commit: [`c6842c8115013524f5955d410c24e1748a615d07`](https://github.com/ethereum/EIPs/tree/c6842c8115013524f5955d410c24e1748a615d07)

| Full source | SHA-256 | Committed sample |
| --- | --- | --- |
| [`msm_G1_bls.json`](https://raw.githubusercontent.com/ethereum/EIPs/c6842c8115013524f5955d410c24e1748a615d07/assets/eip-2537/msm_G1_bls.json) | `9473ca855509a10238388355093e092fab46d80753e72a64b8c1accba8364f65` | `msm_G1_bls.head.json` |
| [`msm_G2_bls.json`](https://raw.githubusercontent.com/ethereum/EIPs/c6842c8115013524f5955d410c24e1748a615d07/assets/eip-2537/msm_G2_bls.json) | `198411e8e72830245866ad94e2f743fa2499ffb928ca7c2bd10a18ed842368ef` | `msm_G2_bls.head.json` |

## go-ethereum vectors

These two vectors are also multi-megabyte, so they follow the same compact
sample policy rather than being committed in full.

Source commit: [`06b23b4293950d8c08b624b90f310d1e918048e8`](https://github.com/ethereum/go-ethereum/tree/06b23b4293950d8c08b624b90f310d1e918048e8)

| Full source | SHA-256 | Committed sample |
| --- | --- | --- |
| [`blsG1MultiExp.json`](https://raw.githubusercontent.com/ethereum/go-ethereum/06b23b4293950d8c08b624b90f310d1e918048e8/core/vm/testdata/precompiles/blsG1MultiExp.json) | `b2603f681b9695e6ceb3cc7562c3c922b6db709882c26e84050774c0db7ce33a` | `blsG1MultiExp.head.json` |
| [`blsG2MultiExp.json`](https://raw.githubusercontent.com/ethereum/go-ethereum/06b23b4293950d8c08b624b90f310d1e918048e8/core/vm/testdata/precompiles/blsG2MultiExp.json) | `f9b3fabe719b89883be935d7482805ac1fe734419e5ec77707dc262b0fdad926` | `blsG2MultiExp.head.json` |

## Sharded vectors

`blsPairing.json` is committed in full, but `scripts/check-vectors.sh` does not
run it directly: it runs the eight `blsPairing.shardN.json` files, which hold
exactly its 106 cases between them. The source stays committed so that the
partition remains checkable.

This is a *partition*, not a sample, and the distinction is the whole point. The
`.head.json` files above are truncations — they deliberately run fewer cases than
their source. The shards run every case the source has; sharding changes only how
many processes the work is spread across. It exists because one process is an
indivisible unit of latency: unsharded, this file alone was ~80% of that gate's
sequential wall time and no job count could split it.

Splitting is sound because a vector case is independent of every other case in
its file. `processVector` in `Main.lean` builds a fresh minimal EVM per case from
that case's own Input/Expected/Gas and evaluates a pure term, so a file's verdict
is exactly the conjunction of its cases' verdicts, and splitting a conjunction
across processes cannot change it.

Regenerate and verify with the committed generator, never by hand:

```bash
python3 scripts/gen-vector-shards.py            # rewrite the shards
python3 scripts/gen-vector-shards.py --check    # verify the committed ones
```

`--check` compares the shards against the source as a multiset of canonical case
encodings, so a dropped case, a duplicated case, an extra case, and two shards
sharing one case are all failures. Independently of the generator,
`scripts/check-vectors.sh` pins each shard's case count and cross-checks it
against the count the runner reports, so a shard that lost cases fails the gate
even if the generator is never run.

Shards are balanced by input length rather than cut into contiguous slices:
pairing cost scales with the number of pairs and the source is sorted ascending
by pair count, so contiguous slices would put every heavy case in the last shard
and roughly double the gate's makespan. Case order across shards is therefore not
the source's order, which the independence argument above makes irrelevant.

## Osaka precompile vectors

These are committed verbatim rather than sampled: each is in the same size
class as the already-vendored `modexp_eip2565.json` and BLS files.

Source commit: [`ca1f2e4d38f4e94676981bb9251239a5d490b004`](https://github.com/ethereum/go-ethereum/tree/ca1f2e4d38f4e94676981bb9251239a5d490b004)

| Source | SHA-256 | Committed file |
| --- | --- | --- |
| [`modexp_eip7883.json`](https://raw.githubusercontent.com/ethereum/go-ethereum/ca1f2e4d38f4e94676981bb9251239a5d490b004/core/vm/testdata/precompiles/modexp_eip7883.json) | `b66970a383617ebbd036460547e555967b1ce953e3d2a2f5969d5fdff1719983` | `modexp_eip7883.json` |
| [`p256Verify.json`](https://raw.githubusercontent.com/ethereum/go-ethereum/ca1f2e4d38f4e94676981bb9251239a5d490b004/core/vm/testdata/precompiles/p256Verify.json) | `72be71957c3e4292d874b3e2a6a2fc2142524433b01cb9a9552b9bb2528c214d` | `p256Verify.json` |

`p256Verify.json` is 782 cases, 567 accepting and 215 rejecting, and its case
names record that most of them are derived from Google's Wycheproof
`ecdsa_secp256r1_sha256` suites. It is the substantive oracle for the
`P256VERIFY` implementation, which is why it is vendored whole rather than
sampled.

Unlike every other vector file, these hold only under Osaka rules, so
`scripts/check-vectors.sh` runs each of them with an explicit `--network`. The
two MODEXP files are complementary rather than alternative — `modexp_eip2565`
is the Prague schedule and `modexp_eip7883` the Osaka one — and each fails
wholesale under the other fork. `jaune --vectors` additionally refuses a file
whose address is not a precompile under the requested fork, so a vector can
never be exercised under rules that do not activate its address.
