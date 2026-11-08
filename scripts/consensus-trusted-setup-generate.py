#!/usr/bin/env python3
"""Generate JauneConsensus/Crypto/TrustedSetup.lean from the pinned KZG setup.

Source: consensus-specs v1.6.1, presets/mainnet/trusted_setups/trusted_setup_4096.json
(the minimal preset's file is byte-identical). The generator refuses any file whose
SHA-256 differs from the pin below, checks the entry counts and encodings, and writes
the three point lists as compressed hex in Lean string literals (one point per line),
decoded at use. Output is deterministic.

    python3 scripts/consensus-trusted-setup-generate.py [--spec-root DIR] [--check]

--check regenerates in memory and fails unless the committed file is identical.
Transcribing or editing the output by hand is forbidden; regenerate instead.
"""

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path

PIN_SHA256 = "f8e44a31ebf0a6d0734dcb301b0716e2c77f3ae18ed0cab0870fbcc2ca55616f"
RELATIVE = Path("presets/mainnet/trusted_setups/trusted_setup_4096.json")
REPO = Path(__file__).resolve().parent.parent
DEFAULT_OUTPUT = REPO / "JauneConsensus/Crypto/TrustedSetup.lean"
EXPECT = {"g1_monomial": (4096, 48), "g1_lagrange": (4096, 48), "g2_monomial": (65, 96)}
LEAN_NAMES = {
    "g1_monomial": "kzgSetupG1MonomialHex",
    "g1_lagrange": "kzgSetupG1LagrangeHex",
    "g2_monomial": "kzgSetupG2MonomialHex",
}


def fail(msg):
    print(f"FAIL: {msg}", file=sys.stderr)
    sys.exit(1)


def render(data):
    out = [
        "-- GENERATED FILE — do not edit by hand.",
        "-- Produced by scripts/consensus-trusted-setup-generate.py from consensus-specs v1.6.1",
        f"-- {RELATIVE} (SHA-256 {PIN_SHA256}).",
        "-- Each string is the concatenation of the compressed points of one setup list, in",
        "-- file order, as lowercase hex without the 0x prefix; JauneConsensus/Crypto/KZG.lean",
        "-- decodes them at use.",
        "",
        "namespace JauneConsensus",
        "",
        f'/-- SHA-256 of the source file. -/\ndef kzgSetupSourceSha256 : String := "{PIN_SHA256}"',
        "",
    ]
    for key in ("g1_monomial", "g1_lagrange", "g2_monomial"):
        count, width = EXPECT[key]
        out.append(f"/-- `KZG_SETUP_{key.upper()}`: {count} compressed points of {width} bytes. -/")
        out.append(f"def {LEAN_NAMES[key]} : String :=")
        entries = [e[2:] for e in data[key]]
        lines = ['  "' + entries[0] + "\\"]
        for e in entries[1:-1]:
            lines.append("  " + e + "\\")
        lines.append("  " + entries[-1] + '"')
        if len(entries) == 1:
            lines = ['  "' + entries[0] + '"']
        out.extend(lines)
        out.append("")
    out.append("end JauneConsensus")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--spec-root", type=Path,
                    default=Path(os.environ.get("CONSENSUS_SPECS_ROOT", Path.home() / "consensus-specs-v1.6.1")))
    ap.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    src = args.spec_root / RELATIVE
    raw = src.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != PIN_SHA256:
        fail(f"{src}: sha256 {digest} != pinned {PIN_SHA256}")
    data = json.loads(raw)
    if sorted(data) != sorted(EXPECT):
        fail(f"unexpected keys {sorted(data)}")
    for key, (count, width) in EXPECT.items():
        entries = data[key]
        if len(entries) != count:
            fail(f"{key}: {len(entries)} entries, expected {count}")
        for e in entries:
            if not (isinstance(e, str) and e.startswith("0x") and len(e) == 2 + 2 * width
                    and all(c in "0123456789abcdef" for c in e[2:])):
                fail(f"{key}: malformed entry {e[:20]}...")
    text = render(data)
    if args.check:
        current = args.output.read_text() if args.output.exists() else None
        if current != text:
            fail(f"{args.output} differs from the generator output")
        print(f"OK: {args.output} matches the generator output (source sha256 {digest})")
        return
    args.output.write_text(text)
    print(f"wrote {args.output} (source sha256 {digest})")


if __name__ == "__main__":
    main()
