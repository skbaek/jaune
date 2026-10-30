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

## Historical, mainnet and Amsterdam release lanes

All three lanes use [`execution-specs` `tests@v21.0.1`](https://github.com/ethereum/execution-specs/releases/tag/tests%40v21.0.1),
commit `1562e2f8b5cb1efda7e0d7c517f2dfb5742c0a43`. The official `fixtures.tar.gz`
is 999,553,432 bytes, SHA-256
`b9b14391ed1a625e4ca9a058c055d0eacd98a42b76c7a6127c640cdc2d3c9439`.
They share the versioned install directory by default and retain separate
manifests, suite namespaces and environment overrides. The historical lane
reads the default (mainnet) install; it has no bootstrap lane of its own.
Together the historical and mainnet lanes pass 100% of the release's
blockchain-test fixtures in [Byzantium, BPO2]: 8,660/8,660 files and
73,345/73,345 cases.

```sh
python3 scripts/bootstrap_mainnet.py                 # ~/eest-mainnet-v21.0.1
python3 scripts/bootstrap_mainnet.py --lane amsterdam # same release/root
python3 scripts/env_doctor.py --mainnet-root ~/eest-mainnet-v21.0.1 --mainnet-deep
python3 scripts/env_doctor.py --amsterdam-root ~/eest-mainnet-v21.0.1 --amsterdam-deep
python3 scripts/gen_mainnet_manifest.py --fixtures-root ~/eest-mainnet-v21.0.1/fixtures --check
python3 scripts/gen_mainnet_manifest.py --lane historical --fixtures-root ~/eest-mainnet-v21.0.1/fixtures --check
python3 scripts/gen_mainnet_manifest.py --lane amsterdam --fixtures-root ~/eest-mainnet-v21.0.1/fixtures --check
```

Keep previous installations separate. Verification checks the archive digest,
safe extraction and every extracted member against the archive. The release
index records root hash
`0xc9f9db837189f64011d8195b97fcaaa43f7d2456ebcae95ed6429b4919cf3a68`
and 354,684 cases across all shipped fixture families. Only selected blockchain
fixtures run here; unsupported labels and non-blockchain families remain
inventoried. Never prune a verified release or hand-edit a generated manifest.

| lane / suite | files | cases |
|---|---:|---:|
| historical / byzantium | 113 | 2,659 |
| historical / constantinoplefix (Petersburg) | 151 | 2,856 |
| historical / istanbul | 158 | 3,016 |
| historical / berlin | 220 | 3,997 |
| historical / london | 220 | 4,277 |
| historical / paris | 224 | 4,299 |
| historical / shanghai | 258 | 4,544 |
| historical / cancun | 2,325 | 13,050 |
| historical / hist-transitions | 23 | 198 |
| historical / hist-smoke | 16 | 58 |
| historical / hist-full | 3,692 | 38,896 |
| mainnet / Prague | 2,506 | 16,790 |
| mainnet / Osaka | 2,449 | 17,550 |
| mainnet / transitions | 13 | 109 |
| mainnet / full | 4,968 | 34,449 |
| mainnet / smoke | 16 | 243 |
| Amsterdam / static | 3,296 | 26,398 |
| Amsterdam / transitions | 58 | 189 |
| Amsterdam / smoke | 16 | 346 |
| Amsterdam / full | 3,354 | 26,587 |

These are the generated inventories. Every historical and mainnet suite is
strict all-PASS. Amsterdam's transition/full gates pass with the registered
two-fixture correction `bal-header-format-v1`; the unmodified official archive
reports two BAL-header exception-name findings, structurally invalid headers
that Jaune also rejects under a different exception name (see
[`../GATES.md`](../GATES.md#the-amsterdam-lane)). Static BPO1/BPO2 suites are
empty and refused; their scheduled transitions are covered. Muir, Arrow and
Gray Glacier and synthetic EIP-1283 Constantinople have no fixtures in the
release; their empty historical suites are refused likewise. BPO3 and later
forks remain unsupported. A mistyped or empty `--dir` is refused, as is an
on-disk subtree count that differs from its manifest.

`conformance_target` uses the same release commit in a separate checkout at
`~/execution-specs-t8n-v21.0.1`; its registered wrapper is carried at `9fc6c99c1`.
An optional dedicated checkout may instead contain exactly the registered
`ommer-reward-summary-cli-v1` adapter. The semantic base remains unchanged.
`sources.json` registers its CLI path, pre/post Git blobs, mode, full-file
SHA-256 and patch SHA-256; no other changed path is permitted in that checkout.
The four existing Jaune-wrapper allowances remain a separate alternative.
The adapter removes reward summaries only from the copy passed to typed
`Environment` validation, retaining the original JSON for reward parsing.
It changes an executed oracle CLI path and is disclosed as such, rather than
being represented as an unmodified-base CLI. Generated cases record the
actual checkout HEAD and adapter identity beside their existing file digests.
Historical case entries and output files are not regenerated by registration.

Provision this optional reference only after its registration is approved:
`python3 scripts/bootstrap_conformance.py --root /dedicated/path --with-cli-adapter`.
Existing mismatching destinations are refused, never repaired. Build its own
venv with the same frozen test dependency sync as the base installation, and
select it explicitly with `JAUNE_T8N_TARGET=/dedicated/path`. Verify it with
`python3 scripts/conformance_reference.py --root /dedicated/path --require-cli-adapter`
or `python3 scripts/env_doctor.py --conformance-target /dedicated/path`.
The default path, base commit, fixture release pins, and frozen oracle are unchanged.

The constants extractor and t8n golden generator use the selected checkout. The frozen
`execution_specs` oracle at `4198b9c` is unchanged. The 76-case t8n corpus
includes ten authored storage-only creation/deletion cases across five of the
runnable forks (Prague, Osaka, BPO1, BPO2, Amsterdam). The release skipped those upstream cases; authored agreement
does not claim published release coverage of them.

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
above and rerun for the full suite (191 test functions under `scripts/tests/`
at goal `jaune-amsterdam-currency-v1`; "the full 80" here was the 2026-08
count).

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

## SHA-256 and RIPEMD-160 precompile vectors

`scripts/vectors/sha256.json` (81 cases, address `0x02`) and
`scripts/vectors/ripemd160.json` (85 cases, address `0x03`) are generated by
[`scripts/gen-hash-precompile-vectors.py`](../gen-hash-precompile-vectors.py),
not vendored from an upstream corpus and never hand-transcribed.

**Oracle.** Expectations are composed exactly as the manifest-pinned EELS
precompiles compose them, at execution-specs commit
[`4198b9c5996713b268aed602739d5aa40e277694`](https://github.com/ethereum/execution-specs/tree/4198b9c5996713b268aed602739d5aa40e277694):

| part of a case | source |
| --- | --- |
| SHA-256 output | `hashlib.sha256(data).digest()`, the whole body of `src/ethereum/prague/vm/precompiled_contracts/sha256.py` |
| RIPEMD-160 output | `left_pad_zero_bytes(hashlib.new("ripemd160", data).digest(), 32)`, the whole body of `src/ethereum/prague/vm/precompiled_contracts/ripemd160.py`; `left_pad_zero_bytes` is imported from `ethereum.utils.byte`, not reimplemented |
| `Gas` | `GAS_SHA256`/`GAS_SHA256_WORD`/`GAS_RIPEMD160`/`GAS_RIPEMD160_WORD` and `ceil32` imported from `ethereum.prague.vm.gas` and `ethereum.utils.numeric`, not transcribed |

`hashlib` resolves to the frozen oracle venv's OpenSSL 3.0.14 (Python 3.11.9);
`ripemd160` is present in that build's `hashlib.algorithms_available`, so no
substitute reference was needed. Nothing in either file derives from Jaune's own
output.

**Independent anchor.** The pin above fixes *which* code composes the oracle but
not whether the local OpenSSL computes the published functions. The generator
therefore carries `PUBLISHED_KATS`: twelve known-answer pairs transcribed from
the standards documents — FIPS 180-4's worked examples for SHA-256, and the test
suite published with RIPEMD-160 by its authors — asserted against the oracle
before any output is written. A mismatch refuses to write rather than
"correcting" the transcription from the oracle, which would destroy the anchor.

**Sweep.** Both files are generated over an identical input set, because both
hashes are Merkle-Damgard over a 64-byte block with an 8-byte trailing length
field and therefore branch at the same lengths. The sweep takes each seam base
and its two neighbours: the 55/56 padding seam mod 64 (where the length field no
longer fits beside the `0x80` byte and an extra compression block appears), the
63/64/65 block seam, and the 31/32/33 word seam where the precompile's `ceil32`
gas word count steps — 63 lengths from the empty input to 4096 bytes. Fourteen
all-zero and all-`0xff` cases at seam lengths cover the two degenerate messages
that a pseudorandom generator would never emit, and the published known answers
above are committed as cases in their own right.

Regenerate and verify with the generator, never by hand:

```sh
EELS_ROOT="$HOME/execution-specs"
"$EELS_ROOT/venv/bin/python" scripts/gen-hash-precompile-vectors.py
"$EELS_ROOT/venv/bin/python" scripts/gen-hash-precompile-vectors.py --check
```

`--check` regenerates both files in memory from the pinned oracle and compares
them byte for byte against the committed artifacts, so a hand-edited case, a
dropped case, and a stale regeneration are all failures. Independently of the
generator, `scripts/check-vectors.sh` pins each file's case count and
cross-checks it against the count the runner reports.

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

### Historical EIP-7610 restoration

`sources.json` now separately pins `legacy_restoration`, the owner-approved,
unmerged legacytests PR18 commit. Install it in its own versioned directory;
`JAUNE_LEGACY_RESTORATION_ROOT` overrides that directory. Clone the section's
`repo_url` without checkout into a fresh directory, fetch its exact `commit`,
and check out that commit detached. `python3 scripts/env_doctor.py --legacy-only`
checks its revision, origin and tracked cleanliness alongside the frozen sources.
An existing installation must not be reset or overwritten to install this pin.

The `legacy_tests_submodule` section continues to describe the original
`ethereum/tests` gitlink, preserving the frozen oracle installation. The separate
restoration contains Cancun/Constantinople historical cases, not Prague cases.
It is inventory evidence, not a replacement root for `check-legacy.sh --full`.
The Prague files at the `ethereum_tests` pin still encode EIP-7610 in five
families. The owner accepted exactly those five classification changes while
retaining the raw RED legacy verdict, all fixture/baseline bytes and a ten-case
original-input replay against pinned EELS. Any additional delta fails readiness
acceptance; this is not a clean legacy baseline.
No baseline entry or fixture byte is changed by selecting the restoration.
