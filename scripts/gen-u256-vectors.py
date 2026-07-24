#!/usr/bin/env python3
"""Generate the Step-1 EVM-word differential oracle.

The formulas below were re-derived from the manifest-pinned Prague EELS sources:
``vm/instructions/{arithmetic,comparison,bitwise,keccak}.py`` and
``vm/gas.py``.  The generator validates that checkout before writing output.
"""
import argparse
import json
import random
import sys
from pathlib import Path

import generator_common

W = 256
MOD = 1 << W
MASK = MOD - 1
SEED = 0xE1E5_2026_0719
ROOT = Path(__file__).resolve().parents[1]

def h(x): return f"0x{x & MASK:064x}"
def signed(x): return x - MOD if x >= (1 << 255) else x
def word(x): return x & MASK
def sdiv(x, y):
    x, y = signed(x), signed(y)
    if y == 0: return 0
    if x == -(1 << 255) and y == -1: return 1 << 255
    return word((1 if x * y >= 0 else -1) * (abs(x) // abs(y)))
def smod(x, y):
    x, y = signed(x), signed(y)
    return 0 if y == 0 else word((1 if x >= 0 else -1) * (abs(x) % abs(y)))
def signextend(k, x):
    if k >= 32: return x
    bit = 8 * k + 7
    return x | (MASK ^ ((1 << (bit + 1)) - 1)) if x & (1 << bit) else x & ((1 << (bit + 1)) - 1)
def sar(k, x):
    return word(signed(x) >> k) if k < 256 else (MASK if signed(x) < 0 else 0)
def byte(k, x): return 0 if k >= 32 else (x >> (8 * (31 - k))) & 0xff
def bytecount(x): return (x.bit_length() + 7) // 8

def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    generator_common.add_source_arguments(parser)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "scripts" / "vectors" / "u256.json",
        help="output JSON path (default: scripts/vectors/u256.json)",
    )
    return parser, parser.parse_args()


def main():
    parser, args = parse_args()
    manifest, _, source_root = generator_common.load_generator_source(
        parser, args.manifest, args.execution_specs
    )
    revision = manifest["execution_specs"]["commit"]
    rng = random.Random(SEED)
    limb_edges = [v << shift for shift in (0, 64, 128, 192)
                  for v in ((1 << 64) - 1, 1 << 64, (1 << 64) + 1)]
    edges = [0, 1, 2, 255, 1 << 255, MASK] + limb_edges
    # Fixed-seed random cases complement the complete mandated edge inventory.
    words = [word(x) for x in edges] + [rng.getrandbits(W) for _ in range(8)]
    vs = []
    def add(op, args, expected): vs.append({"op": op, "args": [h(x) for x in args], "expected": h(expected)})
    for x in words:
        add("iszero", [x], int(x == 0)); add("not", [x], ~x)
        vs.append({"op": "bytecount", "args": [h(x)], "expected": bytecount(x)})
        vs.append({"op": "exp_gas", "args": [h(x)], "expected": 10 + 50 * bytecount(x)})
        for k in list(range(33)) + [63, 64, 127, 128, 255, 256, 257, MASK]:
            add("byte", [k, x], byte(k, x)); add("shl", [k, x], word(x << k) if k < W else 0)
            add("shr", [k, x], x >> k if k < W else 0); add("sar", [k, x], sar(k, x))
        for k in list(range(33)) + [MASK]: add("signextend", [k, x], signextend(k, x))
    for x in words:
      for y in words:
        add("add", [x,y], x+y); add("sub", [x,y], x-y); add("mul", [x,y], x*y)
        add("div", [x,y], 0 if y == 0 else x//y); add("mod", [x,y], 0 if y == 0 else x%y)
        add("sdiv", [x,y], sdiv(x,y)); add("smod", [x,y], smod(x,y))
        add("and", [x,y], x&y); add("or", [x,y], x|y); add("xor", [x,y], x^y)
        add("lt", [x,y], int(x < y)); add("gt", [x,y], int(x > y))
        add("slt", [x,y], int(signed(x) < signed(y))); add("sgt", [x,y], int(signed(x) > signed(y)))
        add("eq", [x,y], int(x == y)); add("exp", [x,y], pow(x,y,MOD))
        for z in [0, 1, 2, MASK]:
            add("addmod", [x,y,z], 0 if z == 0 else (x+y)%z)
            add("mulmod", [x,y,z], 0 if z == 0 else (x*y)%z)
    # Big-endian codec round trips: values exercise both conversion directions.
    for x in words:
        vs.append({"op":"codec", "args":[h(x)], "expected":h(x)})
    for n in [0, 1, 7, 8, 15, 16, 31, 32]:
        data = bytes(rng.getrandbits(8) for _ in range(n))
        vs.append({"op": "ofB8L", "args": ["0x" + data.hex()],
                   "expected": h(int.from_bytes(data, "big"))})
    # EELS keccak formula is keccak256(data); fixed byte strings cover 0/32/64 bytes.
    # These are the EELS keccak256 formula's standard Keccak-256 test vectors (not SHA3-256).
    for data, digest in [("", "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
                         ("00" * 32, "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563"),
                         ("00" * 64, "ad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5")]:
        vs.append({"op": "keccak", "args": ["0x" + data], "expected": "0x" + digest})
    # Boundary coverage for the Lean absorption drivers, which branch on the
    # 8-byte lane and the 136-byte keccak-256 rate: lane boundaries, the
    # 135/136/137 rate seam (the 0x01 and 0x80 padding bits share one byte at
    # length 135 mod 136), multi-block inputs, and fixed-seed random lengths.
    # Digests come from the manifest-pinned EELS keccak256 running inside the
    # frozen oracle venv.  Both Lean entry points must agree with it, so each
    # case is emitted twice: op "keccak" drives B8L.keccak and op "keccak_ba"
    # drives ByteArray.keccak.
    generator_common.require_known_packages(parser, manifest)
    sys.path.insert(0, str(source_root))
    from ethereum.crypto.hash import keccak256
    keccak_lengths = [1, 7, 8, 9, 16, 31, 32, 33, 55, 56, 63, 64, 65,
                      127, 128, 135, 136, 137, 168, 200, 255, 256, 271,
                      272, 273, 511, 512, 544, 1000, 1088]
    keccak_lengths += sorted(rng.randrange(0, 4096) for _ in range(10))
    for n in keccak_lengths:
        data = bytes(rng.getrandbits(8) for _ in range(n))
        arg = "0x" + data.hex()
        digest = "0x" + keccak256(data).hex()
        vs.append({"op": "keccak", "args": [arg], "expected": digest})
        vs.append({"op": "keccak_ba", "args": [arg], "expected": digest})
    out = {"header": {"eels_revision": revision, "seed": SEED,
                      "sources": ["arithmetic.py", "comparison.py", "bitwise.py", "keccak.py", "gas.py"]},
           "vectors": vs}
    path = args.output
    path.write_text(json.dumps(out, indent=2) + "\n")
    print(f"wrote {len(vs)} vectors to {path}")

if __name__ == "__main__": main()
