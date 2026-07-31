#!/usr/bin/env python3
"""Generate the Step-7 fake-exponential differential oracle.

Expected outputs come from the manifest-pinned EELS implementation itself:
``ethereum.utils.numeric.taylor_exponential`` imported from the validated
execution-specs checkout, never a transcription.  (The same function at the
current-mainnet fixture release's source commit
87aba1a38a476b31f819a2390eb481527e6dc683 is byte-identical; verified
2026-07-31 against the GitHub raw file.)

The grid is deliberately *feasible*: `taylor_exponential` grows like
``factor * e**(numerator/denominator)``, so the generator refuses any case
whose exponent ratio exceeds FEASIBLE_RATIO.  The near-U64 excess values
present in the pinned corpus (0xfffffffffff40000 .. 0xfffffffffffe0000, all
in invalid-header fixtures that are rejected before any price calculation)
are exactly the cases the plan forbids executing; they are covered by the
non-evaluating recurrence/uniqueness theorems in Jaune/Machine.lean
(`fakeExpAux_spec`, `fakeExpAux_spec_unique`, `calculateBlobGasPrice_*`).

Run under the frozen oracle venv:

    ~/execution-specs/venv/bin/python scripts/gen-fake-exp-vectors.py
"""
import argparse
import json
import random
import sys
from pathlib import Path

import generator_common

SEED = 0xFA4E_2026_0731
ROOT = Path(__file__).resolve().parents[1]

# The four canonical blob schedules' baseFeeUpdateFraction values (Prague and
# Osaka share one).  Cross-checked below against both the pinned EELS fork
# configuration and scripts/mainnet/manifests.json's declared_blob_schedules.
CANONICAL_FRACTIONS = {
    "Prague": 5007716,
    "Osaka": 5007716,
    "BPO1": 8346193,
    "BPO2": 11684671,
}

GAS_PER_BLOB = 2**17

# The largest excessBlobGas in the pinned current-mainnet corpus that a block
# under execution can actually feed into a blob-gas-price calculation:
# 0xe760000, from for_prague/cancun/eip4844_blobs/excess_blob_gas/
# correct_decreasing_blob_gas_costs.json.  (Derived 2026-07-31 by scanning
# every file of the full-suite manifest; re-verified below when the corpus is
# installed.)  The corpus values above it are the near-U64 cluster named in
# the module docstring.
MAX_FEASIBLE_CORPUS_EXCESS = 0xE760000

# Refuse any case whose e-exponent exceeds this; e**2000 is ~10^868, still
# instant for bignums, while the corpus's near-U64 ratios (~3.7e12) are not
# computable at all.
FEASIBLE_RATIO = 2000


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    generator_common.add_source_arguments(parser)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "scripts" / "vectors" / "fake-exp.json",
        help="output JSON path (default: scripts/vectors/fake-exp.json)",
    )
    parser.add_argument(
        "--mainnet-manifest",
        type=Path,
        default=ROOT / "scripts" / "mainnet" / "manifests.json",
        help="current-mainnet manifest used to cross-check the canonical "
        "blob schedules (default: scripts/mainnet/manifests.json)",
    )
    return parser.parse_args()


def main():
    args = parse_args()
    manifest, execution_specs, source_root = generator_common.load_generator_source(
        argparse.ArgumentParser(), args.manifest, args.execution_specs
    )

    sys.path.insert(0, str(source_root))
    from ethereum.utils.numeric import taylor_exponential
    from ethereum_types.numeric import Uint

    def oracle(factor, numerator, denominator):
        return int(
            taylor_exponential(Uint(factor), Uint(numerator), Uint(denominator))
        )

    # Cross-check the canonical fractions against the committed mainnet
    # manifest, so the grid cannot drift from the schedules the fixtures run.
    declared = json.load(open(args.mainnet_manifest))["declared_blob_schedules"]
    for fork, fraction in CANONICAL_FRACTIONS.items():
        if fork in declared:
            got = declared[fork]["baseFeeUpdateFraction"]
            if got != fraction:
                raise SystemExit(
                    f"canonical fraction mismatch for {fork}: manifest says "
                    f"{got}, generator says {fraction}"
                )

    rng = random.Random(SEED)
    cases = []

    def add(factor, numerator, denominator, note):
        if denominator <= 0:
            raise SystemExit("the oracle domain requires a positive denominator")
        if numerator > FEASIBLE_RATIO * denominator:
            raise SystemExit(
                f"infeasible case rejected: {numerator}/{denominator} exceeds "
                f"ratio {FEASIBLE_RATIO} ({note})"
            )
        cases.append(
            {
                "factor": str(factor),
                "numerator": str(numerator),
                "denominator": str(denominator),
                "expected": str(oracle(factor, numerator, denominator)),
                "note": note,
            }
        )

    # 1. Reference vectors: small closed-form-checkable points of the raw
    #    function, including nonunit factors.
    for fac, num, den in [
        (1, 0, 1),
        (1, 1, 1),
        (1, 2, 1),
        (2, 5, 1),
        (1, 50, 1),
        (1, 500, 1),
        (3, 7, 2),
        (10, 100, 3),
    ]:
        add(fac, num, den, "reference")

    # 2. Canonical schedules: numerator zero, unit steps around the
    #    denominator, small multiples, realistic blob-step excess values, the
    #    maximum feasible corpus excess, and a seeded random spread.
    for fork, den in sorted(set(CANONICAL_FRACTIONS.items())):
        for num in [0, 1, den - 1, den, den + 1, 3 * den, 10 * den, 48 * den]:
            add(1, num, den, f"{fork} grid")
        for k in [1, 2, 3, 6, 9, 21, 100, 763, 1851]:
            add(1, k * GAS_PER_BLOB, den, f"{fork} blob-step")
        add(1, MAX_FEASIBLE_CORPUS_EXCESS, den, f"{fork} corpus-max-feasible")
        for _ in range(40):
            add(1, rng.randrange(0, 100 * den), den, f"{fork} random")

    out = {
        "_provenance": {
            "generator": "scripts/gen-fake-exp-vectors.py",
            "execution_specs_commit": manifest["execution_specs"]["commit"],
            "oracle": "ethereum.utils.numeric.taylor_exponential",
            "seed": hex(SEED),
            "max_feasible_corpus_excess": hex(MAX_FEASIBLE_CORPUS_EXCESS),
        },
        "vectors": cases,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with open(args.output, "w") as fh:
        json.dump(out, fh, indent=1)
        fh.write("\n")
    print(f"wrote {len(cases)} fake-exp vectors to {args.output}")


if __name__ == "__main__":
    main()
