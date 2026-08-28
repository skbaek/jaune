#!/usr/bin/env python3
"""Generate differential vectors for the SHA-256 (0x02) and RIPEMD-160 (0x03)
precompiles.

Why this is a separate generator from ``gen-u256-vectors.py``
------------------------------------------------------------

``gen-u256-vectors.py`` writes ``scripts/vectors/u256.json``, whose schema is a
``{"vectors": [{"op", "args", "expected"}]}`` envelope evaluated by the binary's
``--u256`` op dispatcher (``scripts/check-u256.sh``).  That is the wrong shape
for this job twice over: it is not dispatched by ``scripts/check-vectors.sh`` at
all, and it carries no precompile address, so it could never close the
``0x02``/``0x03`` matrix gap.  A precompile vector file is a bare JSON array of
``{"Name", "Input", "Expected", "Gas"}`` cases run by ``jaune --vectors <addr>``,
which exercises the real precompile entry point including its gas schedule.
Adding a ``sha256`` op to the U256 oracle would additionally require a new Lean
dispatcher case; emitting precompile-shaped files requires no Lean change at
all.  Hence a second generator producing files in the corpus's own precompile
schema.

The boundary-length sweep follows the keccak sweep in ``gen-u256-vectors.py``:
lengths chosen at the seams the implementation branches on rather than sampled
uniformly.  Both hashes here are Merkle-Damgard over a 64-byte block with an
8-byte trailing length field, so the seams are the same for both and the two
files are generated over an identical input set:

* the 55/56 seam mod 64, where the 8-byte length no longer fits beside the 0x80
  padding byte and an extra compression block appears;
* the 63/64/65 block seam mod 64;
* the 31/32/33 word seam mod 32, where the precompile's ``ceil32`` gas word
  count increments (this is a gas-schedule seam, not a hashing one, and the
  ``Gas`` field of every case is checked exactly);
* the empty input, single bytes, and several multi-block lengths.

Oracle independence
-------------------

Expectations never come from Jaune.  Each case's ``Expected`` is composed
exactly as the manifest-pinned EELS precompile composes it:

* ``ethereum/prague/vm/precompiled_contracts/sha256.py`` is
  ``hashlib.sha256(data).digest()``;
* ``ethereum/prague/vm/precompiled_contracts/ripemd160.py`` is
  ``left_pad_zero_bytes(hashlib.new("ripemd160", data).digest(), 32)``;

and each case's ``Gas`` is ``GAS_X + GAS_X_WORD * (ceil32(len(data)) // 32)``
with ``GAS_SHA256``, ``GAS_SHA256_WORD``, ``GAS_RIPEMD160``,
``GAS_RIPEMD160_WORD`` and ``ceil32`` *imported from the pinned checkout*, not
transcribed.  ``left_pad_zero_bytes`` is imported likewise.  The digest
primitives are the same ``hashlib`` calls those two EELS modules make, resolved
by the frozen oracle venv's OpenSSL.

That leaves one link unvalidated by the pin alone: whether the local OpenSSL
computes the published functions.  ``PUBLISHED_KATS`` below closes it with
known-answer pairs transcribed from the standards documents (FIPS 180-4's
examples for SHA-256, the RIPEMD-160 authors' published test suite), which are
asserted against the oracle before any output is produced.  If one of them ever
disagrees the generator refuses to write; the transcription is never "corrected"
from the oracle's output, because then it would stop being an independent
anchor.

Run under the frozen oracle venv:

    ~/execution-specs/venv/bin/python scripts/gen-hash-precompile-vectors.py
    ~/execution-specs/venv/bin/python scripts/gen-hash-precompile-vectors.py --check
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
from pathlib import Path

import generator_common

ROOT = Path(__file__).resolve().parents[1]
VECTORS = ROOT / "scripts" / "vectors"
SEED = 0x5A25_6202_6082_8000

# Merkle-Damgard seams shared by both hashes: a 64-byte compression block with
# an 8-byte big-endian (SHA-256) / little-endian (RIPEMD-160) length field.
PADDING_SEAMS = tuple(56 + 64 * k for k in range(6))    # 56 120 184 248 312 376
BLOCK_SEAMS = tuple(64 * k for k in range(1, 9))        # 64 .. 512
# The precompile gas word seam: cost steps at every 32 bytes, independently of
# the hashing seams above.
WORD_SEAMS = tuple(32 * k for k in range(1, 9))         # 32 .. 256
TINY = (0, 1, 2, 3)
MULTI_BLOCK = (1000, 1024, 1025, 2048, 4096)

# Fixed, non-random content at the seams that matter most: an all-zero input and
# an all-ones input are the two degenerate messages, and a generator whose only
# content is pseudorandom would never emit either.
PATTERN_LENGTHS = (32, 55, 56, 64, 119, 120, 128)

# Known answers transcribed from the standards documents, not from any
# implementation. SHA-256: FIPS 180-4 worked examples (one-block "abc",
# two-block 448-bit, and the 896-bit message). RIPEMD-160: the test suite
# published with the algorithm by Dobbertin, Bosselaers and Preneel.
PUBLISHED_KATS: dict[str, tuple[tuple[str, bytes, str], ...]] = {
    "sha256": (
        ("fips180-4_empty", b"",
         "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
        ("fips180-4_abc", b"abc",
         "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
        ("fips180-4_448bit",
         b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
         "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
        ("fips180-4_896bit",
         b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno"
         b"ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
         "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"),
    ),
    "ripemd160": (
        ("published_empty", b"", "9c1185a5c5e9fc54612808977ee8f548b2258d31"),
        ("published_a", b"a", "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"),
        ("published_abc", b"abc", "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"),
        ("published_message_digest", b"message digest",
         "5d0689ef49d2fae572b881b123a85ffa21595f36"),
        ("published_alphabet", b"abcdefghijklmnopqrstuvwxyz",
         "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"),
        ("published_448bit",
         b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
         "12a053384a9c0c88e405a06c27dcf49ada62eb2b"),
        ("published_alphanumeric",
         b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
         "b0e20b6e3116640286ed3a87a5713079b21f5189"),
        ("published_8x1234567890", b"1234567890" * 8,
         "9b752e45573d4b39f4dbd3323cab82bf63326bfb"),
    ),
}


def sweep_lengths() -> list[int]:
    seams = set(PADDING_SEAMS) | set(BLOCK_SEAMS) | set(WORD_SEAMS)
    lengths = set(TINY) | set(MULTI_BLOCK)
    for base in seams:
        for delta in (-1, 0, 1):
            if base + delta >= 0:
                lengths.add(base + delta)
    return sorted(lengths)


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    generator_common.add_source_arguments(parser)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=VECTORS,
        help=f"directory to write the two vector files into (default: {VECTORS})",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="regenerate in memory and compare against the committed files; "
        "write nothing",
    )
    return parser, parser.parse_args()


def build(source_root: Path) -> dict[str, list[dict]]:
    """Return {"sha256": cases, "ripemd160": cases}, expectations from EELS."""
    sys.path.insert(0, str(source_root))
    from ethereum.prague.vm.gas import (  # noqa: E402
        GAS_RIPEMD160,
        GAS_RIPEMD160_WORD,
        GAS_SHA256,
        GAS_SHA256_WORD,
    )
    from ethereum.utils.byte import left_pad_zero_bytes  # noqa: E402
    from ethereum.utils.numeric import ceil32  # noqa: E402
    from ethereum_types.numeric import Uint  # noqa: E402

    def word_count(data: bytes) -> int:
        return int(ceil32(Uint(len(data))) // Uint(32))

    # Bodies composed exactly as the pinned EELS precompile modules compose
    # them; see this module's docstring.
    def sha256_out(data: bytes) -> bytes:
        return hashlib.sha256(data).digest()

    def sha256_gas(data: bytes) -> int:
        return int(GAS_SHA256 + GAS_SHA256_WORD * Uint(word_count(data)))

    def ripemd160_out(data: bytes) -> bytes:
        return left_pad_zero_bytes(hashlib.new("ripemd160", data).digest(), 32)

    def ripemd160_gas(data: bytes) -> int:
        return int(GAS_RIPEMD160 + GAS_RIPEMD160_WORD * Uint(word_count(data)))

    algorithms = {
        "sha256": (sha256_out, sha256_gas, 32),
        "ripemd160": (ripemd160_out, ripemd160_gas, 32),
    }

    # Anchor the local OpenSSL against the published standards before writing.
    for name, kats in PUBLISHED_KATS.items():
        out = algorithms[name][0]
        for label, message, digest in kats:
            got = out(message)
            # RIPEMD-160's precompile output is the 20-byte digest left-padded
            # to 32; the published constant is the bare digest.
            got = got[-len(bytes.fromhex(digest)):]
            if got.hex() != digest:
                raise SystemExit(
                    f"RED — published known-answer mismatch for {name} "
                    f"{label}: oracle produced {got.hex()}, the standards "
                    f"document says {digest}. Refusing to write; do not "
                    f"'correct' the transcription from the oracle."
                )

    lengths = sweep_lengths()
    files: dict[str, list[dict]] = {}
    for name, (out, gas, width) in algorithms.items():
        rng = random.Random(SEED)
        cases: list[dict] = []

        def add(label: str, data: bytes) -> None:
            expected = out(data)
            assert len(expected) == width, (label, len(expected))
            cases.append({
                "Name": f"{name}_{label}",
                "Input": data.hex(),
                "Expected": expected.hex(),
                "Gas": gas(data),
            })

        for label, message, _ in PUBLISHED_KATS[name]:
            add(label, message)
        for n in lengths:
            add(f"len_{n}", bytes(rng.getrandbits(8) for _ in range(n)))
        for n in PATTERN_LENGTHS:
            add(f"zeros_{n}", bytes(n))
            add(f"ones_{n}", b"\xff" * n)
        files[name] = cases
    return files


def render(cases: list[dict]) -> str:
    return json.dumps(cases, indent=2) + "\n"


def main() -> int:
    parser, args = parse_args()
    manifest, _, source_root = generator_common.load_generator_source(
        parser, args.manifest, args.execution_specs
    )
    generator_common.require_known_packages(parser, manifest)
    files = build(source_root)

    failures = 0
    for name, cases in files.items():
        path = args.output_dir / f"{name}.json"
        text = render(cases)
        if args.check:
            if not path.exists():
                print(f"RED — missing vector file: {path}", file=sys.stderr)
                failures += 1
                continue
            if path.read_text() != text:
                print(
                    f"RED — {path.name} differs from what this generator "
                    f"produces from the pinned oracle",
                    file=sys.stderr,
                )
                failures += 1
                continue
            print(f"OK — {path.name}\t{len(cases)} cases match the pinned oracle")
        else:
            path.write_text(text)
            print(f"  wrote {path.name}\t{len(cases)} cases")
    if failures:
        raise SystemExit(
            f"RED — hash precompile vectors: {failures} file(s) do not match "
            f"the pinned oracle"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
